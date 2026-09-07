Theory evalCompilerBytecodeRound2Phi
Ancestors evalCompilerBytecodeRound2Remove

open HolKernel Parse boolLib bossLib

val round2_removed_blocks_th =
  computeLib.EVAL_CONV ``first_simplify_cfg_round2_removed.fn_blocks``
val round2_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl round2_removed_blocks_th)))

Theorem first_simplify_cfg_round2_removed_blocks:
  ^(concl round2_removed_blocks_th)
Proof
  ACCEPT_TAC round2_removed_blocks_th
QED

fun eval_round2_phi_repair bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val preds_tm =
      list_mk_comb (``pred_labels``,
        [``first_simplify_cfg_round2_removed``, label_tm])
    val preds_th = computeLib.EVAL_CONV preds_tm
    val repair_tm =
      list_mk_comb (``fix_phis_in_block``, [rhs (concl preds_th), bb])
    val repair_th = computeLib.EVAL_CONV repair_tm
  in
    [preds_th, repair_th]
  end

val round2_phi_repair_ths =
  List.concat (map eval_round2_phi_repair round2_removed_blocks)
val round2_fix_all_phis_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.fix_all_phis_def ::
     first_simplify_cfg_round2_removed_blocks :: round2_phi_repair_ths)
    ``fix_all_phis first_simplify_cfg_round2_removed``
val round2_phi_fixed_tm = rhs (concl round2_fix_all_phis_th)

Definition first_simplify_cfg_round2_phi_fixed_def:
  first_simplify_cfg_round2_phi_fixed = ^round2_phi_fixed_tm
End

Theorem exact_round2_fix_all_phis:
  fix_all_phis first_simplify_cfg_round2_removed =
    first_simplify_cfg_round2_phi_fixed
Proof
  simp[first_simplify_cfg_round2_phi_fixed_def] >>
  ACCEPT_TAC round2_fix_all_phis_th
QED

val _ = export_theory()
