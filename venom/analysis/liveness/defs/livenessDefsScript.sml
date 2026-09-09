(*
 * Liveness Analysis — Definitions
 *
 * Upstream: vyperlang/vyper@d21ee3ba9 (positional phi substitution)
 *
 * Backward liveness analysis via generic df_analyze framework.
 *
 * TOP-LEVEL:
 *   liveness_analyze      — run full liveness analysis on a function
 *   liveness_analyze_fuel — bounded liveness analysis for evaluator use
 *   live_vars_at          — query live variables before instruction idx
 *   input_vars_from       — live vars entering target from source (PHI-aware)
 *
 * Soundness statement helpers:
 *   cfg_exec_path         — valid execution path through CFG
 *   var_used_at           — variable read at position
 *   var_defined_at        — variable written at position
 *   used_before_defined   — used before redefined along path
 *   fn_all_vars           — all variable names in a function
 *)

Theory livenessDefs
Ancestors
  list finite_map pred_set
  venomInst cfgDefs dfAnalyzeDefs dfHelperDefs

(* ==========================================================================
   Transfer function: (live \ defs) ∪ uses
   ========================================================================== *)

Definition live_update_def:
  live_update defs uses live =
    let live' = FILTER (λv. ¬MEM v defs) live in
    live' ++ FILTER (λv. ¬MEM v live') uses
End

Definition liveness_transfer_def:
  liveness_transfer (bbs : basic_block list) (inst : instruction)
                    (live : string list) =
    live_update (inst_defs inst) (inst_uses inst) live
End

(* ==========================================================================
   PHI-aware edge transfer
   ========================================================================== *)

(* Collect PHI instructions from the start of a block *)
Definition collect_phis_def:
  collect_phis [] = [] ∧
  collect_phis (inst :: rest) =
    if inst.inst_opcode = PHI then inst :: collect_phis rest
    else []
End

(* Build output→phi_index map from a list of PHIs.
 * Each PHI output variable maps to its phi's index.
 * Also record the matching operand from src_label for each phi. *)
Definition build_phi_maps_def:
  build_phi_maps src_label phis =
    let indexed = MAPi (λi phi. (i, phi)) phis in
    FOLDL (λ(op_map, matching) (i, phi).
      let pairs = phi_pairs phi.inst_operands in
      let op_map' = FOLDL (λm v. m |+ (v, i)) op_map phi.inst_outputs in
      let src_var = FIND (λ(l,v). l = src_label) pairs in
      let matching' = case src_var of
                        SOME (_, v) => matching |+ (i, v)
                      | NONE => matching in
      (op_map', matching'))
    (FEMPTY : (string, num) fmap, FEMPTY : (num, string) fmap) indexed
End

(* Positional substitution: walk liveness, replace phi-related entries
 * with the source-matching operand (deduplicated by phi index).
 * Matches Python d21ee3ba9 fix. *)
Definition input_vars_from_def:
  input_vars_from src_label target_instrs base_liveness =
    let phis = collect_phis target_instrs in
    if NULL phis then base_liveness
    else
      let (op_map, matching) = build_phi_maps src_label phis in
      let (result, placed) = FOLDL (λ(acc, placed) v.
        case FLOOKUP op_map v of
          SOME phi_idx =>
            if MEM phi_idx placed then (acc, placed)
            else
              (case FLOOKUP matching phi_idx of
                 SOME src_v => (acc ++ [src_v], phi_idx :: placed)
               | NONE => (acc, placed))
        | NONE => (acc ++ [v], placed))
        ([], [] : num list) base_liveness in
      result
End

Definition liveness_edge_transfer_def:
  liveness_edge_transfer (bbs : basic_block list) succ_lbl cur_lbl
                         (live : string list) =
    case lookup_block succ_lbl bbs of
      NONE => live
    | SOME succ_bb =>
        input_vars_from cur_lbl succ_bb.bb_instructions live
End

(* ==========================================================================
   Top-level analysis (backward, set union lattice)
   ========================================================================== *)

Definition liveness_analyze_def:
  liveness_analyze fn =
    df_analyze Backward [] list_union liveness_transfer
              liveness_edge_transfer fn.fn_blocks NONE fn
End

Definition liveness_analyze_fuel_def:
  liveness_analyze_fuel fuel fn =
    df_analyze_fuel fuel Backward [] list_union liveness_transfer
                    liveness_edge_transfer fn.fn_blocks NONE fn
End

(* ==========================================================================
   Query API
   ========================================================================== *)

(* Live variables before instruction idx in block lbl.
   idx = LENGTH instrs gives the exit liveness (live-out). *)
Definition live_vars_at_def:
  live_vars_at st lbl idx = df_at [] st lbl idx
End

(* ==========================================================================
   Variable universe (for boundedness statement)
   ========================================================================== *)

Definition fn_all_vars_def:
  fn_all_vars bbs =
    FLAT (MAP (λbb.
      FLAT (MAP (λinst. inst_uses inst ++ inst_defs inst)
                bb.bb_instructions))
      bbs)
End

(* ==========================================================================
   Execution path and use/def at a point (for soundness statement)
   ========================================================================== *)

Definition cfg_exec_path_def:
  cfg_exec_path cfg ([] : (string # num) list) = T ∧
  cfg_exec_path cfg [(lbl, idx)] = T ∧
  cfg_exec_path cfg ((lbl1, idx1) :: (lbl2, idx2) :: rest) =
    (((lbl1 = lbl2 ∧ idx2 = idx1 + 1) ∨
      (MEM lbl2 (cfg_succs_of cfg lbl1) ∧ idx2 = 0)) ∧
     cfg_exec_path cfg ((lbl2, idx2) :: rest))
End

Definition var_used_at_def:
  var_used_at bbs lbl idx v =
    (∃bb inst.
      lookup_block lbl bbs = SOME bb ∧
      idx < LENGTH bb.bb_instructions ∧
      EL idx bb.bb_instructions = inst ∧
      MEM v (inst_uses inst))
End

Definition var_defined_at_def:
  var_defined_at bbs lbl idx v =
    (∃bb inst.
      lookup_block lbl bbs = SOME bb ∧
      idx < LENGTH bb.bb_instructions ∧
      EL idx bb.bb_instructions = inst ∧
      inst.inst_opcode ≠ PHI ∧
      MEM v (inst_defs inst))
End

Definition used_before_defined_def:
  used_before_defined bbs v positions =
    (∃k. k < LENGTH positions ∧
         var_used_at bbs (FST (EL k positions)) (SND (EL k positions)) v ∧
         ∀j. j < k ==>
             ¬var_defined_at bbs (FST (EL j positions))
                                 (SND (EL j positions)) v)
End

(* FMP lowering emits hidden parameters as ordinary def/use instructions. *)
Theorem fmp_hidden_param_defs_uses:
  (inst_uses (mk_inst id FMP_PARAM [Lit (n2w k)] [v]) = [] /\
   inst_defs (mk_inst id FMP_PARAM [Lit (n2w k)] [v]) = [v]) /\
  (inst_uses (mk_inst id RETPC_PARAM [Lit (n2w k)] [v]) = [] /\
   inst_defs (mk_inst id RETPC_PARAM [Lit (n2w k)] [v]) = [v])
Proof
  simp[mk_inst_def, inst_uses_def, inst_defs_def, operand_vars_def,
       operand_var_def]
QED

Theorem fmp_hidden_param_liveness_transfer:
  (liveness_transfer bbs
     (mk_inst id FMP_PARAM [Lit (n2w k)] [v]) live =
   FILTER (\x. x <> v) live) /\
  (liveness_transfer bbs
     (mk_inst id RETPC_PARAM [Lit (n2w k)] [v]) live =
   FILTER (\x. x <> v) live)
Proof
  simp[liveness_transfer_def, live_update_def, mk_inst_def,
       inst_uses_def, inst_defs_def, operand_vars_def, operand_var_def]
QED

Theorem fmp_lowered_generated_defs_uses:
  (inst_uses (mk_inst id INITIAL_FMP [] [v]) = [] /\
   inst_defs (mk_inst id INITIAL_FMP [] [v]) = [v]) /\
  (inst_uses (mk_inst id' BUMP [Var fmp; Lit (n2w k)] [out]) = [fmp] /\
   inst_defs (mk_inst id' BUMP [Var fmp; Lit (n2w k)] [out]) = [out])
Proof
  simp[mk_inst_def, inst_uses_def, inst_defs_def, operand_vars_def,
       operand_var_def]
QED
