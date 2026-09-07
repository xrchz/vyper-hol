Theory evalCompilerBytecodeRound2Remove
Ancestors evalCompilerBytecodeSimplifyCfgProbe

open HolKernel Parse boolLib bossLib

val round2_blocks_th =
  computeLib.EVAL_CONV ``first_simplify_cfg_round1_fn.fn_blocks``
val round2_blocks =
  fst (listSyntax.dest_list (rhs (concl round2_blocks_th)))

Theorem first_simplify_cfg_round1_fn_blocks:
  ^(concl round2_blocks_th)
Proof
  ACCEPT_TAC round2_blocks_th
QED

val round2_entry_th =
  computeLib.EVAL_CONV ``fn_entry_label first_simplify_cfg_round1_fn``

Theorem first_simplify_cfg_round1_fn_entry:
  ^(concl round2_entry_th)
Proof
  ACCEPT_TAC round2_entry_th
QED

fun eval_round2_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val reachable_tm =
      list_mk_comb (``reachable``,
        [``first_simplify_cfg_round1_fn``, label_tm])
  in
    computeLib.EVAL_CONV reachable_tm
  end

val round2_reachable_ths = map eval_round2_reachable round2_blocks
val round2_remove_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     first_simplify_cfg_round1_fn_entry ::
     first_simplify_cfg_round1_fn_blocks :: round2_reachable_ths)
    ``remove_unreachable_blocks first_simplify_cfg_round1_fn``
val round2_removed_tm = rhs (concl round2_remove_th)

Definition first_simplify_cfg_round2_removed_def:
  first_simplify_cfg_round2_removed = ^round2_removed_tm
End

Theorem exact_round2_remove_unreachable:
  remove_unreachable_blocks first_simplify_cfg_round1_fn =
    first_simplify_cfg_round2_removed
Proof
  simp[first_simplify_cfg_round2_removed_def] >>
  ACCEPT_TAC round2_remove_th
QED

val _ = export_theory()
