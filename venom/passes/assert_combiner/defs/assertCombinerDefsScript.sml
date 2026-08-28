(*
 * Assert Combiner Pass — Definitions
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 *
 * Ports vyper/venom/passes/assert_combiner.py to HOL4.
 *
 * Combines consecutive `assert iszero(x)` instructions into a single
 * assert using OR:
 *   assert iszero(a); assert iszero(b)  →  assert iszero(a | b)
 *
 * Two phases:
 *   1. Analysis: scan each block for mergeable assert pairs
 *   2. Transform: merge pairs using OR + ISZERO
 *
 * Merge conditions:
 *   - Both asserts use iszero (traced through assigns)
 *   - Same error_msg (modeled as: both are plain ASSERT)
 *   - No volatile/effectful instructions between them
 *
 * Uses DFG analysis (to trace iszero chains through assigns).
 *
 * TOP-LEVEL:
 *   ac_get_iszero_operand    — trace through assigns to find iszero input
 *   ac_is_safe_between       — check if instruction is safe between asserts
 *   ac_find_merge_pairs      — analysis: find mergeable assert pairs
 *   ac_apply_merge           — transform: merge a pair
 *   ac_transform_block       — block-level transform
 *   ac_transform_function    — function-level transform
 *
 * Source: vyper/venom/passes/assert_combiner.py
 *)

Theory assertCombinerDefs
Ancestors
  passSimulationDefs dfgDefs dfgAnalysisProps venomExecSemantics venomInst venomEffects
Libs
  pred_setTheory

(* ===== Volatile Detection ===== *)

(* An instruction is volatile if it has observable side effects that
   cannot be reordered. Matches Python IRInstruction.is_volatile.
   Defined here because is_volatile is not yet on main. *)
Definition ac_is_volatile_def:
  ac_is_volatile (opc : opcode) <=>
    MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2;
             SELFDESTRUCT; LOG; SSTORE; TSTORE;
             MSTORE; MCOPY; ISTORE;
             CALLDATACOPY; CODECOPY; RETURNDATACOPY; EXTCODECOPY;
             DLOADBYTES; ASSERT; ASSERT_UNREACHABLE]
End

(* ===== Analysis Helpers ===== *)

(* Check if an instruction is safe to appear between two asserts.
   Must not be a terminator, volatile, or have effects.
   ALLOCA excluded: it modifies vs_allocas (non-variable state),
   breaking execution_equiv in the deferred-abort case.
   PHI/PARAM/FMP_PARAM/OFFSET excluded: they can fail even when operands evaluate
   (PHI needs vs_prev_bb, PARAM/FMP_PARAM need an index in range,
    OFFSET needs the label map). *)
Definition ac_is_safe_between_def:
  ac_is_safe_between inst <=>
    ~is_terminator inst.inst_opcode /\
    ~ac_is_volatile inst.inst_opcode /\
    inst.inst_opcode <> ALLOCA /\
    inst.inst_opcode <> PHI /\
    inst.inst_opcode <> PARAM /\
    inst.inst_opcode <> FMP_PARAM /\
    inst.inst_opcode <> OFFSET /\
    write_effects inst.inst_opcode = {} /\
    read_effects inst.inst_opcode = {}
End

(* Trace an operand through ASSIGN chains to find an ISZERO instruction.
   Returns SOME (iszero's input operand) if found, NONE otherwise.
   Uses visited-set for termination (SSA def-use chains are acyclic). *)
Definition ac_get_iszero_operand_def:
  ac_get_iszero_operand dfg visited op =
    case op of
      Var v =>
        (case dfg_get_def dfg v of
           SOME inst =>
             if inst.inst_id IN visited then NONE
             else if inst.inst_opcode = ISZERO then
               (case inst.inst_operands of
                  [src] => SOME src
                | _ => NONE)
             else if inst.inst_opcode = ASSIGN then
               (case inst.inst_operands of
                  [src] => ac_get_iszero_operand dfg
                             (inst.inst_id INSERT visited) src
                | _ => NONE)
             else NONE
         | NONE => NONE)
    | _ => NONE
Termination
  WF_REL_TAC `inv_image $< (\(dfg,visited,_). CARD (dfg_def_ids dfg DIFF visited))`
  >> rpt strip_tac
  >> imp_res_tac dfg_get_def_implies_dfg_def_ids
  >> irule CARD_PSUBSET
  >> simp[FINITE_DIFF, dfg_def_ids_finite, PSUBSET_DEF, SUBSET_DEF, EXTENSION]
  >> qexists_tac `inst.inst_id` >> simp[]
End

(* ===== Merge Candidate ===== *)

Datatype:
  merge_candidate = <|
    mc_first_id  : num;        (* inst_id of first assert (to remove) *)
    mc_first_pred : operand;   (* iszero's input for first assert *)
    mc_second_id : num;        (* inst_id of second assert (to modify) *)
    mc_second_pred : operand   (* iszero's input for second assert *)
  |>
End

(* ===== Analysis: Find Merge Pairs ===== *)

(*
 * Scan a block's instructions to find pairs of asserts that can be merged.
 * Maintains a "pending" assert. When a second assert is found with a safe
 * gap, it forms a merge candidate.
 *
 * pending : SOME (inst_id, iszero_pred) of the current pending assert
 *)
Definition ac_scan_block_def:
  ac_scan_block dfg [] pending = [] /\
  ac_scan_block dfg (inst :: rest) pending =
    if inst.inst_opcode = ASSERT then
      case (inst.inst_operands,
            ac_get_iszero_operand dfg {} (HD inst.inst_operands)) of
        ([_], SOME pred) =>
          (case pending of
             SOME (prev_id, prev_pred) =>
               (* Found a merge pair *)
               let mc = <| mc_first_id := prev_id;
                           mc_first_pred := prev_pred;
                           mc_second_id := inst.inst_id;
                           mc_second_pred := pred |> in
               (* Chain: merged result becomes new pending *)
               mc :: ac_scan_block dfg rest (SOME (inst.inst_id, pred))
           | NONE =>
               ac_scan_block dfg rest (SOME (inst.inst_id, pred)))
      | _ =>
          (* Assert without iszero pattern — reset pending *)
          ac_scan_block dfg rest NONE
    else if ac_is_safe_between inst then
      (* Safe instruction — keep pending *)
      ac_scan_block dfg rest pending
    else
      (* Unsafe instruction — reset pending *)
      ac_scan_block dfg rest NONE
End

(* ===== Transform: Apply Merges ===== *)

(* Fresh variable names for OR and ISZERO outputs *)
Definition ac_or_var_def:
  ac_or_var (id:num) = STRCAT "ac_or_" (toString id)
End

Definition ac_iz_var_def:
  ac_iz_var (id:num) = STRCAT "ac_iz_" (toString id)
End

(*
 * Apply merge: given merge candidates, transform the instruction list.
 *
 * Uses FOLDL with a merged_preds map (id → actual merged predicate).
 * When instruction B is "second" of MC1 (merge with A):
 *   - The merged pred for B = Var or_v (the OR output)
 *   - If B is later "first" of MC2, we use merged_preds[B] instead of mc_first_pred
 *
 * IMPORTANT: Process "second" logic BEFORE "first" NOP, so that a
 * 3-assert chain A→B→C correctly records merged_preds[B] before B is NOP'd.
 * Otherwise pred_a would be lost when processing C.
 *)
Definition ac_apply_merge_step_def:
  ac_apply_merge_step candidates (merged_preds, acc) inst =
    (* Phase 1: "second" merge — compute OR/ISZERO, update merged_preds *)
    let (merged_preds1, pre_insts, merged_op) =
      case FIND (\mc. mc.mc_second_id = inst.inst_id) candidates of
        SOME mc =>
          let actual_first_pred =
            case ALOOKUP merged_preds mc.mc_first_id of
              SOME p => p
            | NONE => mc.mc_first_pred in
          if actual_first_pred = mc.mc_second_pred then
            (* Identical preds — no merge needed, but record for chaining *)
            ((mc.mc_second_id, actual_first_pred) :: merged_preds,
             [], NONE)
          else
            let id = inst.inst_id in
            let or_v = ac_or_var id in
            let iz_v = ac_iz_var id in
            let or_inst = <| inst_id := id; inst_opcode := OR;
                inst_operands := [actual_first_pred; mc.mc_second_pred];
                inst_outputs := [or_v] |> in
            let iz_inst = <| inst_id := id + 1; inst_opcode := ISZERO;
                inst_operands := [Var or_v];
                inst_outputs := [iz_v] |> in
            ((mc.mc_second_id, Var or_v) :: merged_preds,
             [or_inst; iz_inst], SOME iz_v)
      | NONE => (merged_preds, [], NONE) in
    (* Phase 2: if this is also a "first" assert — NOP it *)
    if EXISTS (\mc. mc.mc_first_id = inst.inst_id) candidates then
      let nop = inst with <| inst_opcode := NOP;
                              inst_operands := [];
                              inst_outputs := [] |> in
      (merged_preds1, acc ++ pre_insts ++ [nop])
    (* Phase 3: if it was only a "second" — emit merged assert *)
    else (case merged_op of
      SOME iz_v =>
        (merged_preds1, acc ++ pre_insts ++
          [inst with inst_operands := [Var iz_v]])
    | NONE =>
        (merged_preds1, acc ++ pre_insts ++ [inst]))
End

(* ===== Block and Function Transform ===== *)

Definition ac_transform_block_def:
  ac_transform_block dfg bb =
    let candidates = ac_scan_block dfg bb.bb_instructions NONE in
    bb with bb_instructions :=
      SND (FOLDL (ac_apply_merge_step candidates) ([], [])
                  bb.bb_instructions)
End

Definition ac_transform_function_def:
  ac_transform_function fn =
    let dfg = dfg_build_function fn in
    fn with fn_blocks :=
      MAP (ac_transform_block dfg) fn.fn_blocks
End

Definition ac_transform_context_def:
  ac_transform_context ctx =
    ctx with ctx_functions := MAP ac_transform_function ctx.ctx_functions
End

(* ===== Fresh Variable Tracking ===== *)

(* Fresh variables introduced by merging within a single block. *)
Definition ac_fresh_vars_block_def:
  ac_fresh_vars_block dfg bb =
    let candidates = ac_scan_block dfg bb.bb_instructions NONE in
    set (FLAT (MAP (\mc.
      [ac_or_var mc.mc_second_id; ac_iz_var mc.mc_second_id])
      candidates))
End

(* Fresh variables in a function. *)
Definition ac_fresh_vars_fn_def:
  ac_fresh_vars_fn fn =
    let dfg = dfg_build_function fn in
    BIGUNION (set (MAP (ac_fresh_vars_block dfg) fn.fn_blocks))
End
