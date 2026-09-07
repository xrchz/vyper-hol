Theory evalCompilerBytecodeSecondSimplifyCfgInitialRemove
Ancestors evalCompilerBytecodeSecondSimplifyCfgResult
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

val second_blocks_th =
  computeLib.EVAL_CONV ``second_simplify_cfg_operand.fn_blocks``
val second_blocks =
  fst (listSyntax.dest_list (rhs (concl second_blocks_th)))
val second_entry_th =
  computeLib.EVAL_CONV ``fn_entry_label second_simplify_cfg_operand``

Theorem second_simplify_cfg_operand_blocks:
  ^(concl second_blocks_th)
Proof
  ACCEPT_TAC second_blocks_th
QED

Theorem second_simplify_cfg_operand_entry:
  ^(concl second_entry_th)
Proof
  ACCEPT_TAC second_entry_th
QED

fun eval_second_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val reachable_tm =
      list_mk_comb (``reachable``, [``second_simplify_cfg_operand``, label_tm])
  in
    computeLib.EVAL_CONV reachable_tm
  end

val second_reachable_ths = map eval_second_reachable second_blocks

Theorem exact_second_simplify_cfg_operand_reachability:
  ^(concl (LIST_CONJ second_reachable_ths))
Proof
  ACCEPT_TAC (LIST_CONJ second_reachable_ths)
QED

val second_remove_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     second_entry_th :: second_blocks_th :: second_reachable_ths)
    ``remove_unreachable_blocks second_simplify_cfg_operand``
val second_removed_tm = rhs (concl second_remove_th)

Definition second_simplify_cfg_removed_def:
  second_simplify_cfg_removed = ^second_removed_tm
End

Theorem exact_second_remove_unreachable:
  remove_unreachable_blocks second_simplify_cfg_operand =
    second_simplify_cfg_removed
Proof
  simp[second_simplify_cfg_removed_def] >>
  ACCEPT_TAC second_remove_th
QED

val second_removed_blocks_th =
  computeLib.EVAL_CONV ``second_simplify_cfg_removed.fn_blocks``

Theorem second_simplify_cfg_removed_blocks:
  ^(concl second_removed_blocks_th)
Proof
  ACCEPT_TAC second_removed_blocks_th
QED

val _ = export_theory()
