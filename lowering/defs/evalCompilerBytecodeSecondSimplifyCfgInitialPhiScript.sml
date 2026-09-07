Theory evalCompilerBytecodeSecondSimplifyCfgInitialPhi
Ancestors evalCompilerBytecodeSecondSimplifyCfgInitialRemove
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

Theorem second_simplify_cfg_dispatch_edge:
  fn_succ second_simplify_cfg_operand "__entry" "@dispatch_1"
Proof
  simp[cfgTransformTheory.fn_succ_def,
       venomInstTheory.lookup_block_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, evalCompilerBytecodeSecondSimplifyCfgResultTheory.second_simplify_cfg_operand_def]
QED

Theorem second_simplify_cfg_fallback_edge:
  fn_succ second_simplify_cfg_operand "__entry" "@fallback_0"
Proof
  simp[cfgTransformTheory.fn_succ_def,
       venomInstTheory.lookup_block_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.FIND_def,
       listTheory.INDEX_FIND_def, evalCompilerBytecodeSecondSimplifyCfgResultTheory.second_simplify_cfg_operand_def]
QED

val second_literal_edge_ths =
  map (REWRITE_RULE [evalCompilerBytecodeSecondSimplifyCfgResultTheory.second_simplify_cfg_operand_def])
    [second_simplify_cfg_dispatch_edge, second_simplify_cfg_fallback_edge]
val second_removed_blocks_th =
  SIMP_RULE (srw_ss ()) second_literal_edge_ths
    second_simplify_cfg_removed_blocks
val second_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl second_removed_blocks_th)))

fun eval_second_phi_repair bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val preds_tm =
      list_mk_comb
        (``pred_labels``, [``second_simplify_cfg_removed``, label_tm])
    val preds_th =
      SIMP_CONV (srw_ss ())
        [second_simplify_cfg_removed_def,
         cfgTransformTheory.pred_labels_def,
         cfgTransformTheory.block_preds_def,
         venomInstTheory.bb_succs_def,
         venomInstTheory.get_successors_def,
         venomInstTheory.is_terminator_def,
         venomStateTheory.get_label_def]
        preds_tm
    val repair_tm =
      list_mk_comb (``fix_phis_in_block``, [rhs (concl preds_th), bb])
    val repair_th = computeLib.EVAL_CONV repair_tm
  in
    [preds_th, repair_th]
  end

val second_phi_repair_ths =
  List.concat (map eval_second_phi_repair second_removed_blocks)

Theorem exact_second_initial_phi_repairs:
  ^(concl (LIST_CONJ second_phi_repair_ths))
Proof
  ACCEPT_TAC (LIST_CONJ second_phi_repair_ths)
QED

val second_fix_all_phis_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.fix_all_phis_def ::
     second_simplify_cfg_removed_blocks :: second_phi_repair_ths)
    ``fix_all_phis second_simplify_cfg_removed``
val second_phi_fixed_tm = rhs (concl second_fix_all_phis_th)

Definition second_simplify_cfg_phi_fixed_def:
  second_simplify_cfg_phi_fixed = ^second_phi_fixed_tm
End

Theorem exact_second_fix_all_phis:
  fix_all_phis second_simplify_cfg_removed = second_simplify_cfg_phi_fixed
Proof
  simp[second_simplify_cfg_phi_fixed_def] >>
  ACCEPT_TAC second_fix_all_phis_th
QED

val second_phi_fixed_blocks_th =
  computeLib.EVAL_CONV ``second_simplify_cfg_phi_fixed.fn_blocks``

Theorem second_simplify_cfg_phi_fixed_blocks:
  ^(concl second_phi_fixed_blocks_th)
Proof
  ACCEPT_TAC second_phi_fixed_blocks_th
QED

val _ = export_theory()
