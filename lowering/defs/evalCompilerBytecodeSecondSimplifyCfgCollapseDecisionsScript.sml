Theory evalCompilerBytecodeSecondSimplifyCfgCollapseDecisions
Ancestors evalCompilerBytecodeSecondSimplifyCfgInitialPhi
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val second_literal_edge_ths =
  map (REWRITE_RULE
    [evalCompilerBytecodeSecondSimplifyCfgResultTheory.second_simplify_cfg_operand_def])
    [second_simplify_cfg_dispatch_edge, second_simplify_cfg_fallback_edge]
val second_phi_fixed_blocks_th =
  SIMP_RULE (srw_ss ()) second_literal_edge_ths
    second_simplify_cfg_phi_fixed_blocks
val second_phi_fixed_blocks =
  fst (listSyntax.dest_list (rhs (concl second_phi_fixed_blocks_th)))
val _ =
  if length second_phi_fixed_blocks = 3 then ()
  else raise Fail "second PHI-fixed function changed fixture block count"
val second_entry_bb_tm = List.nth (second_phi_fixed_blocks, 0)
val second_dispatch_bb_tm = List.nth (second_phi_fixed_blocks, 1)
val second_fallback_bb_tm = List.nth (second_phi_fixed_blocks, 2)
val _ = map (assert_closed "second PHI-fixed block") second_phi_fixed_blocks

Definition second_simplify_cfg_entry_bb_def:
  second_simplify_cfg_entry_bb = ^second_entry_bb_tm
End

Definition second_simplify_cfg_dispatch_bb_def:
  second_simplify_cfg_dispatch_bb = ^second_dispatch_bb_tm
End

Definition second_simplify_cfg_fallback_bb_def:
  second_simplify_cfg_fallback_bb = ^second_fallback_bb_tm
End

val phi_fixed_def =
  evalCompilerBytecodeSecondSimplifyCfgInitialPhiTheory.second_simplify_cfg_phi_fixed_def
fun eval_phi_fixed tm =
  SIMP_CONV (srw_ss ()) [phi_fixed_def] tm

val second_entry_lookup_th = eval_phi_fixed
  ``lookup_block "__entry" second_simplify_cfg_phi_fixed.fn_blocks``
val second_dispatch_lookup_th = eval_phi_fixed
  ``lookup_block "@dispatch_1" second_simplify_cfg_phi_fixed.fn_blocks``
val second_fallback_lookup_th = eval_phi_fixed
  ``lookup_block "@fallback_0" second_simplify_cfg_phi_fixed.fn_blocks``
val second_entry_succs_th = computeLib.EVAL_CONV
  ``bb_succs second_simplify_cfg_entry_bb``
val second_dispatch_succs_th = computeLib.EVAL_CONV
  ``bb_succs second_simplify_cfg_dispatch_bb``
val second_fallback_succs_th = computeLib.EVAL_CONV
  ``bb_succs second_simplify_cfg_fallback_bb``
val _ =
  if aconv (rhs (concl second_entry_succs_th))
       ``["@fallback_0"; "@dispatch_1"]``
  then () else raise Fail "second entry successor order changed"
val _ =
  if aconv (rhs (concl second_dispatch_succs_th)) ``["@fallback_0"]``
  then () else raise Fail "second dispatch successor order changed"
val _ =
  if aconv (rhs (concl second_fallback_succs_th)) ``[] : string list``
  then () else raise Fail "second fallback successor order changed"

val second_fallback_preds_th = eval_phi_fixed
  ``num_preds second_simplify_cfg_phi_fixed "@fallback_0"``
val second_entry_try_bypass_th = eval_phi_fixed
  ``try_bypass second_simplify_cfg_phi_fixed []
      second_simplify_cfg_entry_bb ["@fallback_0"; "@dispatch_1"]``
val second_dispatch_merge_fallback_th = eval_phi_fixed
  ``can_merge_blocks second_simplify_cfg_phi_fixed
      second_simplify_cfg_dispatch_bb second_simplify_cfg_fallback_bb``

val second_closed_decision_ths =
  [second_entry_lookup_th, second_dispatch_lookup_th,
   second_fallback_lookup_th, second_entry_succs_th,
   second_dispatch_succs_th, second_fallback_succs_th,
   second_fallback_preds_th, second_entry_try_bypass_th,
   second_dispatch_merge_fallback_th]
val _ =
  map (assert_closed "second SimplifyCFG collapse decision" o concl)
    second_closed_decision_ths

Theorem exact_second_simplify_cfg_closed_decisions:
  ^(concl (LIST_CONJ second_closed_decision_ths))
Proof
  ACCEPT_TAC (LIST_CONJ second_closed_decision_ths)
QED

Theorem exact_second_entry_succs:
  bb_succs second_simplify_cfg_entry_bb =
    ["@fallback_0"; "@dispatch_1"]
Proof
  ACCEPT_TAC second_entry_succs_th
QED

val _ = export_theory()
