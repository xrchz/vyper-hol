(*
 * Simplify CFG Pass — Definitions
 *
 * Simplifies the control flow graph by:
 *   1. Removing unreachable blocks
 *   2. Collapsing block chains via DFS from entry:
 *      a. Merge B into A when A→B, A sole pred of B, B sole succ of A
 *      b. Bypass trivial jump blocks (single JMP, 1 pred, 1 succ)
 *   3. Batch label replacement for data segment consistency
 *   4. Fixing degenerate PHI nodes after predecessor removal
 *
 * TOP-LEVEL:
 *   remove_unreachable_blocks — remove blocks not reachable from entry
 *   fix_phi_inst              — fix a PHI after predecessor changes
 *   merge_blocks              — merge B into A
 *   merge_jump                — bypass trivial jump block
 *   collapse_dfs              — DFS collapse from entry (matches Python)
 *   simplify_cfg_fn           — full pass (iterated to fixpoint)
 *   simplify_cfg_ctx          — transform all functions in context
 *
 * Source: vyper/venom/passes/simplify_cfg.py
 *)

Theory simplifyCfgDefs
Ancestors
  cfgTransform venomWf venomExecSemantics

(* ===== Unreachable Block Removal ===== *)

(* Remove all blocks not reachable from entry. *)
Definition remove_unreachable_blocks_def:
  remove_unreachable_blocks func =
    case fn_entry_label func of
      NONE => func
    | SOME entry =>
        func with fn_blocks :=
          FILTER (λbb. reachable func bb.bb_label) func.fn_blocks
End

(* ===== PHI Fixup ===== *)

(* Remove PHI operands referencing labels not in the given predecessor set. *)
Definition filter_phi_ops_def:
  filter_phi_ops pred_labels [] = [] ∧
  filter_phi_ops pred_labels [x] = [x] ∧
  filter_phi_ops pred_labels (Label l :: val_op :: rest) =
    (if MEM l pred_labels
     then Label l :: val_op :: filter_phi_ops pred_labels rest
     else filter_phi_ops pred_labels rest) ∧
  filter_phi_ops pred_labels (x :: y :: rest) =
    x :: y :: filter_phi_ops pred_labels rest
End

(* Fix a single PHI instruction given actual predecessor labels:
   - 0 operands → NOP
   - 2 operands (1 predecessor) → ASSIGN
   - otherwise → keep as PHI with filtered operands *)
Definition fix_phi_inst_def:
  fix_phi_inst actual_preds inst =
    if inst.inst_opcode ≠ PHI then inst
    else
      let ops' = filter_phi_ops actual_preds inst.inst_operands in
      case ops' of
        [] => inst with <| inst_opcode := NOP;
                           inst_operands := [];
                           inst_outputs := [] |>
      | [_; val_op] =>
          inst with <| inst_opcode := ASSIGN;
                       inst_operands := [val_op] |>
      | _ => inst with inst_operands := ops'
End

(* Fix all PHIs in a block, then sort so PHIs remain at the top.
   Python does: bb.instructions.sort(key=lambda inst: inst.opcode != "phi")
   which puts PHIs (key=0) before non-PHIs (key=1), preserving relative order. *)
Definition fix_phis_in_block_def:
  fix_phis_in_block actual_preds bb =
    let insts' = MAP (fix_phi_inst actual_preds) bb.bb_instructions in
    let phis = FILTER (λi. i.inst_opcode = PHI) insts' in
    let non_phis = FILTER (λi. i.inst_opcode ≠ PHI) insts' in
    bb with bb_instructions := phis ++ non_phis
End

(* Fix PHIs in all blocks of a function. *)
Definition fix_all_phis_def:
  fix_all_phis func =
    func with fn_blocks :=
      MAP (λbb. fix_phis_in_block (pred_labels func bb.bb_label) bb)
      func.fn_blocks
End

(* ===== Block Merging (chain collapse) ===== *)

(* Can A and B be chain-merged?
   A has single successor B, B has single predecessor A, B has no PHIs, and
   they are distinct blocks.  The label guard excludes self-loop "merges",
   which neither decrease the block count nor yield valid replacement maps. *)
(* Python checks: len(cfg_out(bb)) == 1 and len(cfg_in(next_bb)) == 1.
   No JMP opcode check — any terminator with single successor triggers merge.
   no_phis: defensive (fix_all_phis should have eliminated PHIs already). *)
Definition can_merge_blocks_def:
  can_merge_blocks func a b ⇔
    a.bb_label ≠ b.bb_label ∧
    bb_succs a = [b.bb_label] ∧
    num_preds func b.bb_label = 1 ∧
    no_phis b
End

Theorem can_merge_blocks_distinct:
  can_merge_blocks func a b ==> a.bb_label <> b.bb_label
Proof
  simp[can_merge_blocks_def]
QED

(* Merge B into A: drop A's terminator, append B's instructions. *)
Definition merge_blocks_def:
  merge_blocks a b =
    a with bb_instructions :=
      FRONT a.bb_instructions ++ b.bb_instructions
End

(* ===== Trivial Jump Bypass ===== *)

(* Can a trivial jump block be bypassed?
   Python: len(cfg_in(next_bb)) == 1 and len(cfg_out(next_bb)) == 1
           and len(next_bb.instructions) == 1
   Context: called when len(cfg_out(a)) == 2 (from collapse_dfs). *)
Definition can_bypass_jump_def:
  can_bypass_jump func a b ⇔
    LENGTH b.bb_instructions = 1 ∧
    num_succs a = 2 ∧
    MEM b.bb_label (bb_succs a) ∧
    num_preds func b.bb_label = 1 ∧
    num_succs b = 1
End

(* PHI agreement check: for each PHI in target, if both a and b are
   predecessors, their operand values must agree.
   Python: the check at top of _merge_jump. *)
Definition phi_values_agree_def:
  phi_values_agree a_label b_label [] = T ∧
  phi_values_agree a_label b_label (inst::rest) =
    (if inst.inst_opcode ≠ PHI then T
     else
       let a_val = resolve_phi a_label inst.inst_operands in
       let b_val = resolve_phi b_label inst.inst_operands in
       (case (a_val, b_val) of
          (SOME va, SOME vb) =>
            if va ≠ vb then F
            else phi_values_agree a_label b_label rest
        | _ => phi_values_agree a_label b_label rest))
End

(* Update PHI in target after bypass: remove b's entry if a already present,
   else replace b's label with a's label. *)
Definition update_phi_bypass_def:
  update_phi_bypass a_label b_label inst =
    if inst.inst_opcode ≠ PHI then inst
    else
      let has_a = MEM (Label a_label) inst.inst_operands in
      if has_a then
        inst with inst_operands := remove_phi_label b_label inst.inst_operands
      else
        inst with inst_operands :=
          MAP (λop. case op of
                      Label l => if l = b_label then Label a_label else Label l
                    | _ => op) inst.inst_operands
End

(* Perform the jump bypass: update A's terminator, update target PHIs,
   remove b. Accumulates label replacement in label_map.
   Returns (updated_fn, updated_label_map) or NONE on failure. *)
Definition do_merge_jump_def:
  do_merge_jump func a b label_map =
    case bb_succs b of
      [target_lbl] =>
        (case lookup_block target_lbl func.fn_blocks of
           SOME target =>
             (* Update A's terminator: b → target *)
             let a' = a with bb_instructions :=
               MAP (λinst.
                 if ¬is_terminator inst.inst_opcode then inst
                 else subst_label_inst b.bb_label target_lbl inst)
               a.bb_instructions in
             (* Update target's PHIs *)
             let target' = target with bb_instructions :=
               MAP (update_phi_bypass a.bb_label b.bb_label)
                   target.bb_instructions in
             let func' = func with fn_blocks :=
               replace_block a.bb_label a'
                 (replace_block target_lbl target'
                   (remove_block b.bb_label func.fn_blocks)) in
             let label_map' = (b.bb_label, target_lbl) :: label_map in
             SOME (func', label_map')
         | NONE => NONE)
    | _ => NONE
End

(* ===== Successor PHI Label Update ===== *)

(* After merging B into A, update successor PHIs to reference A instead of B.
   Matches Python's _merge_blocks immediate PHI update. *)
Definition update_succ_phi_labels_def:
  update_succ_phi_labels old_lbl new_lbl bbs succs =
    FOLDL (λbs s.
      case lookup_block s bs of
        NONE => bs
      | SOME sbb =>
          let sbb' = sbb with bb_instructions :=
            MAP (λinst.
              if inst.inst_opcode ≠ PHI then inst
              else subst_label_inst old_lbl new_lbl inst)
            sbb.bb_instructions in
          replace_block s sbb' bs)
    bbs succs
End

(* ===== DFS Collapse ===== *)

(* Try to bypass one trivial jump successor.
   Returns (updated_fn, updated_label_map, success_flag). *)
Definition try_bypass_def:
  (try_bypass func label_map bb [] = (func, label_map, F)) ∧
  (try_bypass func label_map bb (next_lbl::rest) =
    case lookup_block next_lbl func.fn_blocks of
      SOME next_bb =>
        if can_bypass_jump func bb next_bb then
          let target_lbl = HD (bb_succs next_bb) in
          (case lookup_block target_lbl func.fn_blocks of
             SOME target =>
               if phi_values_agree bb.bb_label next_bb.bb_label
                    target.bb_instructions then
                 (case do_merge_jump func bb next_bb label_map of
                    SOME (func', lm') => (func', lm', T)
                  | NONE => try_bypass func label_map bb rest)
               else try_bypass func label_map bb rest
           | NONE => try_bypass func label_map bb rest)
        else try_bypass func label_map bb rest
    | NONE => try_bypass func label_map bb rest)
End

(* DFS collapse from a block. After a successful merge/bypass, re-process
   the same block (Python recurses on bb after merge). Tracks visited set.
   Returns (updated_fn, updated_label_map, updated_visited).
   collapse_dfs: process a single block
   collapse_dfs_succs: DFS into a list of successor blocks *)
Definition collapse_dfs_def:
  (collapse_dfs func label_map visited lbl =
    case lookup_block lbl func.fn_blocks of
      NONE => (func, label_map, visited)
    | SOME bb =>
        (* Try chain merge: single successor with single predecessor *)
        case bb_succs bb of
          [next_lbl] =>
            (case lookup_block next_lbl func.fn_blocks of
               SOME next_bb =>
                 if can_merge_blocks func bb next_bb then
                   let merged = merge_blocks bb next_bb in
                   let bbs' = replace_block lbl merged
                       (remove_block next_lbl func.fn_blocks) in
                   (* Immediate successor PHI update: next_lbl → lbl *)
                   let bbs'' = update_succ_phi_labels
                       next_lbl lbl bbs' (bb_succs merged) in
                   let func' = func with fn_blocks := bbs'' in
                   let label_map' = (next_bb.bb_label, lbl) :: label_map in
                   (* TERMINATION: merge removes next_lbl block,
                      fn_blocks count decreases *)
                   collapse_dfs func' label_map' visited lbl
                 else
                   (* No merge — mark visited, DFS into successor *)
                   if MEM lbl visited then (func, label_map, visited)
                   else
                     let visited' = lbl :: visited in
                     (* TERMINATION: lbl added to visited,
                        unvisited count decreases *)
                     collapse_dfs func label_map visited' next_lbl
             | NONE =>
                 if MEM lbl visited then (func, label_map, visited)
                 else (func, label_map, lbl :: visited))
        | succs =>
            (* Try bypass for 2-successor case *)
            let (func', lm', bypassed) =
              try_bypass func label_map bb succs in
            if bypassed then
              (* TERMINATION: bypass removes a block,
                 fn_blocks count decreases *)
              collapse_dfs func' lm' visited lbl
            else if MEM lbl visited then (func', lm', visited)
            else
              let visited' = lbl :: visited in
              (* TERMINATION: lbl added to visited,
                 unvisited count decreases *)
              collapse_dfs_succs func' lm' visited' succs) ∧
  (collapse_dfs_succs func label_map visited [] =
    (func, label_map, visited)) ∧
  (collapse_dfs_succs func label_map visited (s::rest) =
    let (func', lm', vis') = collapse_dfs func label_map visited s in
    (* TERMINATION: fn_blocks non-increasing, visited non-shrinking,
       succ list strictly shorter *)
    collapse_dfs_succs func' lm' vis' rest)
Termination
  WF_REL_TAC `inv_image ($< LEX $< LEX $<)
    (λx. case x of
       INL (func, lm, vis, lbl) =>
         (LENGTH func.fn_blocks,
          LENGTH (FILTER (λbb. ¬MEM bb.bb_label vis) func.fn_blocks),
          0)
     | INR (func, lm, vis, succs) =>
         (LENGTH func.fn_blocks,
          LENGTH (FILTER (λbb. ¬MEM bb.bb_label vis) func.fn_blocks),
          LENGTH succs))`
  >> cheat
End

(* ===== Full Pass ===== *)

(* One round, exposing the block-label replacement evidence generated by the
   collapse.  collapse_dfs conses new replacements, so reverse the log before
   returning it to put the entries in execution (and resolution) order. *)
Definition simplify_cfg_round_with_labels_def:
  simplify_cfg_round_with_labels func =
    case fn_entry_label func of
      NONE => (func, [])
    | SOME entry =>
        let func1 = remove_unreachable_blocks func in
        (* Fix PHIs before DFS — matches Python's remove_unreachable_blocks
           which calls fix_phi_instructions for all blocks *)
        let func1a = fix_all_phis func1 in
        let (func2, label_map, _) =
          collapse_dfs func1a [] [] entry in
        (* Only CFG operands are block labels.  In particular this must not
           rewrite INVOKE callee labels. *)
        let func3 = if label_map = [] then func2
                    else subst_block_labels_fn label_map func2 in
        (* Remove newly unreachable blocks + final PHI fix *)
        let func4 = remove_unreachable_blocks func3 in
        (fix_all_phis func4, REVERSE label_map)
End

Definition simplify_cfg_round_def:
  simplify_cfg_round func = FST (simplify_cfg_round_with_labels func)
End

(* Iterate rounds until fixpoint, retaining replacement evidence from every
   round in chronological order. *)
Definition simplify_cfg_iter_with_labels_def:
  simplify_cfg_iter_with_labels 0 func = (func, []) ∧
  simplify_cfg_iter_with_labels (SUC n) func =
    let (func', round_map) = simplify_cfg_round_with_labels func in
    if func'.fn_blocks = func.fn_blocks then (func, round_map)
    else
      let (result, later_map) = simplify_cfg_iter_with_labels n func' in
      (result, round_map ++ later_map)
End

Definition simplify_cfg_iter_def:
  simplify_cfg_iter n func = FST (simplify_cfg_iter_with_labels n func)
End

Definition simplify_cfg_fn_with_labels_def:
  simplify_cfg_fn_with_labels func =
    simplify_cfg_iter_with_labels (LENGTH func.fn_blocks) func
End

Definition simplify_cfg_fn_def:
  simplify_cfg_fn func = FST (simplify_cfg_fn_with_labels func)
End

Theorem simplify_cfg_fn_with_labels_fst:
  FST (simplify_cfg_fn_with_labels func) = simplify_cfg_fn func
Proof
  simp[simplify_cfg_fn_def]
QED

(* Transform all functions in context. *)
Definition simplify_cfg_ctx_def:
  simplify_cfg_ctx ctx =
    ctx with ctx_functions := MAP simplify_cfg_fn ctx.ctx_functions
End
