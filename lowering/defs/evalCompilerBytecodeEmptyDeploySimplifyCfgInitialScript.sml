Theory evalCompilerBytecodeEmptyDeploySimplifyCfgInitial
Ancestors evalCompilerBytecodeEmptyDeploySimplifyCfg
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

val deploy_blocks_th =
  evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_operand_blocks
val deploy_blocks =
  fst (listSyntax.dest_list (rhs (concl deploy_blocks_th)))
val _ =
  if length deploy_blocks = 1 then ()
  else raise Fail "deploy SimplifyCFG operand is not a singleton"
val deploy_entry_th =
  evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_operand_entry

fun eval_deploy_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val reachable_tm = list_mk_comb
      (``reachable``,
       [``empty_deploy_simplify_cfg_operand``, rhs (concl label_th)])
  in
    computeLib.EVAL_CONV reachable_tm
  end

val deploy_reachable_ths = map eval_deploy_reachable deploy_blocks

Theorem exact_empty_deploy_simplify_cfg_operand_reachability:
  ^(concl (LIST_CONJ deploy_reachable_ths))
Proof
  ACCEPT_TAC (LIST_CONJ deploy_reachable_ths)
QED

val deploy_remove_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     deploy_entry_th :: deploy_blocks_th :: deploy_reachable_ths)
    ``remove_unreachable_blocks empty_deploy_simplify_cfg_operand``
val deploy_removed_tm = rhs (concl deploy_remove_th)

Definition empty_deploy_simplify_cfg_removed_def:
  empty_deploy_simplify_cfg_removed = ^deploy_removed_tm
End

Theorem exact_empty_deploy_remove_unreachable:
  remove_unreachable_blocks empty_deploy_simplify_cfg_operand =
    empty_deploy_simplify_cfg_removed
Proof
  simp[empty_deploy_simplify_cfg_removed_def] >>
  ACCEPT_TAC deploy_remove_th
QED

val deploy_removed_blocks_th =
  computeLib.EVAL_CONV ``empty_deploy_simplify_cfg_removed.fn_blocks``
val deploy_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl deploy_removed_blocks_th)))
val _ =
  if length deploy_removed_blocks = 1 then ()
  else raise Fail "initial deploy cleanup changed the singleton block count"

Theorem exact_empty_deploy_simplify_cfg_removed_blocks:
  ^(concl deploy_removed_blocks_th)
Proof
  ACCEPT_TAC deploy_removed_blocks_th
QED

fun eval_deploy_phi_repair bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val preds_tm = list_mk_comb
      (``pred_labels``,
       [``empty_deploy_simplify_cfg_removed``, rhs (concl label_th)])
    val preds_th = computeLib.EVAL_CONV preds_tm
    val repair_tm = list_mk_comb
      (``fix_phis_in_block``, [rhs (concl preds_th), bb])
    val repair_th = computeLib.EVAL_CONV repair_tm
  in
    [preds_th, repair_th]
  end

val deploy_phi_repair_ths =
  List.concat (map eval_deploy_phi_repair deploy_removed_blocks)
val deploy_fix_all_phis_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.fix_all_phis_def ::
     deploy_removed_blocks_th :: deploy_phi_repair_ths)
    ``fix_all_phis empty_deploy_simplify_cfg_removed``
val deploy_phi_fixed_tm = rhs (concl deploy_fix_all_phis_th)

Definition empty_deploy_simplify_cfg_phi_fixed_def:
  empty_deploy_simplify_cfg_phi_fixed = ^deploy_phi_fixed_tm
End

Theorem exact_empty_deploy_fix_all_phis:
  fix_all_phis empty_deploy_simplify_cfg_removed =
    empty_deploy_simplify_cfg_phi_fixed
Proof
  simp[empty_deploy_simplify_cfg_phi_fixed_def] >>
  ACCEPT_TAC deploy_fix_all_phis_th
QED

val deploy_phi_fixed_blocks_th =
  computeLib.EVAL_CONV ``empty_deploy_simplify_cfg_phi_fixed.fn_blocks``

Theorem exact_empty_deploy_simplify_cfg_phi_fixed_blocks:
  ^(concl deploy_phi_fixed_blocks_th)
Proof
  ACCEPT_TAC deploy_phi_fixed_blocks_th
QED

val _ = export_theory()
