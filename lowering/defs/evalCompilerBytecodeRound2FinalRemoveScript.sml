Theory evalCompilerBytecodeRound2FinalRemove
Ancestors evalCompilerBytecodeRound2Subst

open HolKernel Parse boolLib bossLib

val round2_substituted_blocks_th =
  computeLib.EVAL_CONV ``first_simplify_cfg_round2_substituted.fn_blocks``
val round2_substituted_blocks =
  fst (listSyntax.dest_list (rhs (concl round2_substituted_blocks_th)))

Theorem first_simplify_cfg_round2_substituted_blocks:
  ^(concl round2_substituted_blocks_th)
Proof
  ACCEPT_TAC round2_substituted_blocks_th
QED

val round2_substituted_entry_th =
  computeLib.EVAL_CONV
    ``fn_entry_label first_simplify_cfg_round2_substituted``

Theorem first_simplify_cfg_round2_substituted_entry:
  ^(concl round2_substituted_entry_th)
Proof
  ACCEPT_TAC round2_substituted_entry_th
QED

fun eval_round2_substituted_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val reachable_tm =
      list_mk_comb (``reachable``,
        [``first_simplify_cfg_round2_substituted``, rhs (concl label_th)])
  in
    computeLib.EVAL_CONV reachable_tm
  end

val round2_substituted_reachable_ths =
  map eval_round2_substituted_reachable round2_substituted_blocks

val round2_final_remove_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     first_simplify_cfg_round2_substituted_entry ::
     first_simplify_cfg_round2_substituted_blocks ::
     round2_substituted_reachable_ths)
    ``remove_unreachable_blocks first_simplify_cfg_round2_substituted``
val round2_final_removed_tm = rhs (concl round2_final_remove_th)

Definition first_simplify_cfg_round2_final_removed_def:
  first_simplify_cfg_round2_final_removed = ^round2_final_removed_tm
End

Theorem exact_round2_final_remove_unreachable:
  remove_unreachable_blocks first_simplify_cfg_round2_substituted =
    first_simplify_cfg_round2_final_removed
Proof
  simp[first_simplify_cfg_round2_final_removed_def] >>
  ACCEPT_TAC round2_final_remove_th
QED

val _ = export_theory()
