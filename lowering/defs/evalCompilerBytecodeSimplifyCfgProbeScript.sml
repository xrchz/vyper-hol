Theory evalCompilerBytecodeSimplifyCfgProbe
Ancestors evalCompilerBytecodeStageProbe

open HolKernel Parse boolLib bossLib

Theorem imported_first_simplify_cfg_operation_unfold:
  !fn.
    simplify_cfg_fn_with_labels fn =
      simplify_cfg_iter_with_labels (LENGTH fn.fn_blocks) fn
Proof
  ACCEPT_TAC
    evalCompilerBytecodeStageProbeTheory.first_simplify_cfg_operation_unfold
QED


Theorem first_simplify_cfg_operand_block_count:
  LENGTH first_simplify_cfg_operand.fn_blocks = 3
Proof
  EVAL_TAC
QED

Theorem first_simplify_cfg_operand_entry:
  fn_entry_label first_simplify_cfg_operand = SOME "__entry"
Proof
  EVAL_TAC
QED

(* Evaluate reachability one retained candidate at a time.  Keeping these
   conversions separate prevents the recursive closure computation from being
   duplicated while FILTER is traversed. *)
val first_simplify_cfg_blocks_th =
  computeLib.EVAL_CONV ``first_simplify_cfg_operand.fn_blocks``
val first_simplify_cfg_blocks =
  fst (listSyntax.dest_list (rhs (concl first_simplify_cfg_blocks_th)))

fun eval_first_simplify_cfg_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val reachable_tm =
      list_mk_comb (``reachable``, [``first_simplify_cfg_operand``, label_tm])
  in
    computeLib.EVAL_CONV reachable_tm
  end

val first_simplify_cfg_reachable_ths =
  map eval_first_simplify_cfg_reachable first_simplify_cfg_blocks

val first_remove_unreachable_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     first_simplify_cfg_operand_entry ::
     first_simplify_cfg_blocks_th :: first_simplify_cfg_reachable_ths)
    ``remove_unreachable_blocks first_simplify_cfg_operand``

Theorem exact_first_remove_unreachable:
  ^(concl first_remove_unreachable_th)
Proof
  ACCEPT_TAC first_remove_unreachable_th
QED
val _ = export_theory()
