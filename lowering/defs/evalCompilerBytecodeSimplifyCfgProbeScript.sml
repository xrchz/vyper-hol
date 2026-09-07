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
val first_removed_tm = rhs (concl first_remove_unreachable_th)
Definition first_simplify_cfg_removed_def:
  first_simplify_cfg_removed = ^first_removed_tm
End

Theorem exact_first_remove_unreachable_named:
  remove_unreachable_blocks first_simplify_cfg_operand =
    first_simplify_cfg_removed
Proof
  simp[first_simplify_cfg_removed_def, exact_first_remove_unreachable]
QED

Theorem first_simplify_cfg_dispatch_edge:
  fn_succ first_simplify_cfg_operand "__entry" "@dispatch_1"
Proof
  simp[cfgTransformTheory.fn_succ_def,
       venomInstTheory.lookup_block_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, first_simplify_cfg_operand_def]
QED

Theorem first_simplify_cfg_fallback_edge:
  fn_succ first_simplify_cfg_operand "__entry" "@fallback_0"
Proof
  simp[cfgTransformTheory.fn_succ_def,
       venomInstTheory.lookup_block_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, first_simplify_cfg_operand_def]
QED

val first_literal_edge_ths =
  map (REWRITE_RULE [first_simplify_cfg_operand_def])
    [first_simplify_cfg_dispatch_edge, first_simplify_cfg_fallback_edge]
val first_removed_normal_th =
  SIMP_CONV (srw_ss ()) first_literal_edge_ths first_removed_tm
val first_removed_eq_operand_th =
  SIMP_RULE (srw_ss ()) [GSYM first_simplify_cfg_operand_def,
    GSYM first_simplify_cfg_blocks_th]
    (TRANS first_simplify_cfg_removed_def first_removed_normal_th)

Theorem first_simplify_cfg_removed_eq_operand:
  first_simplify_cfg_removed = first_simplify_cfg_operand
Proof
  once_rewrite_tac [first_removed_eq_operand_th] >>
  simp[venomInstTheory.ir_function_component_equality]
QED

val first_removed_blocks_eq_operand_th =
  CONV_RULE (DEPTH_CONV BETA_CONV)
    (AP_TERM ``\fn : ir_function. fn.fn_blocks``
      first_simplify_cfg_removed_eq_operand)
val first_removed_blocks_th =
  TRANS first_removed_blocks_eq_operand_th first_simplify_cfg_blocks_th
val first_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl first_removed_blocks_th)))

Theorem first_simplify_cfg_removed_blocks:
  ^(concl first_removed_blocks_th)
Proof
  ACCEPT_TAC first_removed_blocks_th
QED

val _ = export_theory()
