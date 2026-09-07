Theory evalCompilerBytecodeEmptyDeploySimplifyCfgRound
Ancestors evalCompilerBytecodeEmptyDeploySimplifyCfgCollapse
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

Theorem exact_empty_deploy_substitution_guard:
  (([] : (string # string) list) = [])
Proof
  simp[]
QED

Definition empty_deploy_simplify_cfg_substituted_def:
  empty_deploy_simplify_cfg_substituted =
    empty_deploy_simplify_cfg_phi_fixed
End

Theorem exact_empty_deploy_substitution:
  (if ([] : (string # string) list) = [] then
     empty_deploy_simplify_cfg_phi_fixed
   else subst_block_labels_fn [] empty_deploy_simplify_cfg_phi_fixed) =
  empty_deploy_simplify_cfg_substituted
Proof
  simp[empty_deploy_simplify_cfg_substituted_def]
QED

val substituted_blocks_th = computeLib.EVAL_CONV
  ``empty_deploy_simplify_cfg_substituted.fn_blocks``
val substituted_blocks =
  fst (listSyntax.dest_list (rhs (concl substituted_blocks_th)))
val _ =
  if length substituted_blocks = 1 then ()
  else raise Fail "deploy substitution changed the singleton block count"
val substituted_entry_th = computeLib.EVAL_CONV
  ``fn_entry_label empty_deploy_simplify_cfg_substituted``

Theorem exact_empty_deploy_substituted_blocks:
  ^(concl substituted_blocks_th)
Proof
  ACCEPT_TAC substituted_blocks_th
QED

Theorem exact_empty_deploy_substituted_entry:
  ^(concl substituted_entry_th)
Proof
  ACCEPT_TAC substituted_entry_th
QED

fun eval_substituted_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val reachable_tm = list_mk_comb
      (``reachable``,
       [``empty_deploy_simplify_cfg_substituted``, rhs (concl label_th)])
  in
    computeLib.EVAL_CONV reachable_tm
  end

val substituted_reachable_ths =
  map eval_substituted_reachable substituted_blocks
val final_remove_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     substituted_entry_th :: substituted_blocks_th ::
     substituted_reachable_ths)
    ``remove_unreachable_blocks empty_deploy_simplify_cfg_substituted``
val final_removed_tm = rhs (concl final_remove_th)

Definition empty_deploy_simplify_cfg_final_removed_def:
  empty_deploy_simplify_cfg_final_removed = ^final_removed_tm
End

Theorem exact_empty_deploy_final_remove_unreachable:
  remove_unreachable_blocks empty_deploy_simplify_cfg_substituted =
    empty_deploy_simplify_cfg_final_removed
Proof
  simp[empty_deploy_simplify_cfg_final_removed_def] >>
  ACCEPT_TAC final_remove_th
QED

val final_removed_blocks_th = computeLib.EVAL_CONV
  ``empty_deploy_simplify_cfg_final_removed.fn_blocks``
val final_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl final_removed_blocks_th)))

Theorem exact_empty_deploy_final_removed_blocks:
  ^(concl final_removed_blocks_th)
Proof
  ACCEPT_TAC final_removed_blocks_th
QED

fun eval_final_phi_repair bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val preds_tm = list_mk_comb
      (``pred_labels``,
       [``empty_deploy_simplify_cfg_final_removed``, rhs (concl label_th)])
    val preds_th = computeLib.EVAL_CONV preds_tm
    val repair_tm = list_mk_comb
      (``fix_phis_in_block``, [rhs (concl preds_th), bb])
    val repair_th = computeLib.EVAL_CONV repair_tm
  in
    [preds_th, repair_th]
  end

val final_phi_repair_ths =
  List.concat (map eval_final_phi_repair final_removed_blocks)
val final_fix_all_phis_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.fix_all_phis_def ::
     final_removed_blocks_th :: final_phi_repair_ths)
    ``fix_all_phis empty_deploy_simplify_cfg_final_removed``
val round1_fn_tm = rhs (concl final_fix_all_phis_th)

Definition empty_deploy_simplify_cfg_round1_fn_def:
  empty_deploy_simplify_cfg_round1_fn = ^round1_fn_tm
End

Theorem exact_empty_deploy_final_fix_all_phis:
  fix_all_phis empty_deploy_simplify_cfg_final_removed =
    empty_deploy_simplify_cfg_round1_fn
Proof
  simp[empty_deploy_simplify_cfg_round1_fn_def] >>
  ACCEPT_TAC final_fix_all_phis_th
QED

Theorem exact_empty_deploy_simplify_cfg_round_with_labels:
  simplify_cfg_round_with_labels empty_deploy_simplify_cfg_operand =
    (empty_deploy_simplify_cfg_round1_fn,
     ([] : (string # string) list))
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_round_with_labels_def,
       evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_operand_entry,
       evalCompilerBytecodeEmptyDeploySimplifyCfgInitialTheory.exact_empty_deploy_remove_unreachable,
       evalCompilerBytecodeEmptyDeploySimplifyCfgInitialTheory.exact_empty_deploy_fix_all_phis,
       evalCompilerBytecodeEmptyDeploySimplifyCfgCollapseTheory.exact_empty_deploy_collapse_dfs_components,
       exact_empty_deploy_substitution,
       exact_empty_deploy_final_remove_unreachable,
       exact_empty_deploy_final_fix_all_phis]
QED

val _ = export_theory()
