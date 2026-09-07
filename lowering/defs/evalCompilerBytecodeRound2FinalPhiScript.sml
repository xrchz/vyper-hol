Theory evalCompilerBytecodeRound2FinalPhi
Ancestors evalCompilerBytecodeRound2FinalRemove

open HolKernel Parse boolLib bossLib

val round2_final_removed_blocks_th =
  computeLib.EVAL_CONV ``first_simplify_cfg_round2_final_removed.fn_blocks``
val round2_final_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl round2_final_removed_blocks_th)))

Theorem first_simplify_cfg_round2_final_removed_blocks:
  ^(concl round2_final_removed_blocks_th)
Proof
  ACCEPT_TAC round2_final_removed_blocks_th
QED

fun eval_round2_final_phi_repair bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val preds_tm =
      list_mk_comb (``pred_labels``,
        [``first_simplify_cfg_round2_final_removed``, label_tm])
    val preds_th = computeLib.EVAL_CONV preds_tm
    val repair_tm =
      list_mk_comb (``fix_phis_in_block``, [rhs (concl preds_th), bb])
    val repair_th = computeLib.EVAL_CONV repair_tm
  in
    [preds_th, repair_th]
  end

val round2_final_phi_repair_ths =
  List.concat (map eval_round2_final_phi_repair round2_final_removed_blocks)
val round2_final_fix_all_phis_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.fix_all_phis_def ::
     first_simplify_cfg_round2_final_removed_blocks ::
     round2_final_phi_repair_ths)
    ``fix_all_phis first_simplify_cfg_round2_final_removed``
val round2_fn_tm = rhs (concl round2_final_fix_all_phis_th)

Definition first_simplify_cfg_round2_fn_def:
  first_simplify_cfg_round2_fn = ^round2_fn_tm
End

Theorem exact_round2_final_fix_all_phis:
  fix_all_phis first_simplify_cfg_round2_final_removed =
    first_simplify_cfg_round2_fn
Proof
  simp[first_simplify_cfg_round2_fn_def] >>
  ACCEPT_TAC round2_final_fix_all_phis_th
QED

val round2_collapse_components_tm =
  rhs (concl
    evalCompilerBytecodeRound2CollapseTheory.exact_round2_collapse_dfs_components)
val (_, round2_collapse_tail_tm) =
  pairSyntax.dest_pair round2_collapse_components_tm
val (label_map2, _) = pairSyntax.dest_pair round2_collapse_tail_tm

Theorem exact_second_simplify_cfg_round_with_labels:
  simplify_cfg_round_with_labels first_simplify_cfg_round1_fn =
    (first_simplify_cfg_round2_fn, REVERSE ^label_map2)
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_round_with_labels_def,
       evalCompilerBytecodeRound2RemoveTheory.first_simplify_cfg_round1_fn_entry,
       evalCompilerBytecodeRound2RemoveTheory.exact_round2_remove_unreachable,
       evalCompilerBytecodeRound2PhiTheory.exact_round2_fix_all_phis,
       evalCompilerBytecodeRound2CollapseTheory.exact_round2_collapse_dfs_components,
       evalCompilerBytecodeRound2SubstTheory.exact_round2_substitution,
       evalCompilerBytecodeRound2FinalRemoveTheory.exact_round2_final_remove_unreachable,
       exact_round2_final_fix_all_phis]
QED

val _ = export_theory()
