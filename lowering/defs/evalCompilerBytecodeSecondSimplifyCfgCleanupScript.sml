Theory evalCompilerBytecodeSecondSimplifyCfgCleanup
Ancestors evalCompilerBytecodeSecondSimplifyCfgCollapseTraversal
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

val second_collapse_components =
  CONJUNCTS second_simplify_cfg_collapse_result_components
val second_collapsed_fn_th = List.nth (second_collapse_components, 0)
val second_collapse_label_map_th = List.nth (second_collapse_components, 1)

val second_substitution_tm =
  ``if FST (SND second_simplify_cfg_collapse_result) = [] then
      FST second_simplify_cfg_collapse_result
    else
      subst_block_labels_fn
        (FST (SND second_simplify_cfg_collapse_result))
        (FST second_simplify_cfg_collapse_result)``
val second_substitution_th =
  SIMP_CONV (srw_ss ()) second_collapse_components second_substitution_tm
val second_substituted_tm = rhs (concl second_substitution_th)

Definition second_simplify_cfg_substituted_def:
  second_simplify_cfg_substituted = ^second_substituted_tm
End

Theorem exact_second_substitution:
  (if FST (SND second_simplify_cfg_collapse_result) = [] then
      FST second_simplify_cfg_collapse_result
    else
      subst_block_labels_fn
        (FST (SND second_simplify_cfg_collapse_result))
        (FST second_simplify_cfg_collapse_result)) =
  second_simplify_cfg_substituted
Proof
  simp[second_simplify_cfg_substituted_def,
       second_simplify_cfg_collapse_result_components]
QED

Theorem second_simplify_cfg_substituted_eq_phi_fixed:
  second_simplify_cfg_substituted = second_simplify_cfg_phi_fixed
Proof
  simp[second_simplify_cfg_substituted_def]
QED

val second_literal_edge_ths =
  map
    (REWRITE_RULE
      [evalCompilerBytecodeSecondSimplifyCfgResultTheory.second_simplify_cfg_operand_def])
    [evalCompilerBytecodeSecondSimplifyCfgInitialPhiTheory.second_simplify_cfg_dispatch_edge,
     evalCompilerBytecodeSecondSimplifyCfgInitialPhiTheory.second_simplify_cfg_fallback_edge]
val second_phi_fixed_blocks_normal_th =
  SIMP_RULE (srw_ss ())
    second_literal_edge_ths
    evalCompilerBytecodeSecondSimplifyCfgInitialPhiTheory.second_simplify_cfg_phi_fixed_blocks
val second_substituted_blocks_th =
  REWRITE_RULE [GSYM second_simplify_cfg_substituted_eq_phi_fixed]
    second_phi_fixed_blocks_normal_th
val second_substituted_blocks =
  fst (listSyntax.dest_list (rhs (concl second_substituted_blocks_th)))

Theorem second_simplify_cfg_substituted_blocks:
  ^(concl second_substituted_blocks_th)
Proof
  ACCEPT_TAC second_substituted_blocks_th
QED

val second_phi_fixed_entry_th =
  computeLib.EVAL_CONV ``fn_entry_label second_simplify_cfg_phi_fixed``
val second_substituted_entry_th =
  REWRITE_RULE [GSYM second_simplify_cfg_substituted_eq_phi_fixed]
    second_phi_fixed_entry_th

Theorem second_simplify_cfg_substituted_entry:
  ^(concl second_substituted_entry_th)
Proof
  ACCEPT_TAC second_substituted_entry_th
QED

fun eval_second_substituted_reachable bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val reachable_tm =
      list_mk_comb
        (``reachable``, [``second_simplify_cfg_phi_fixed``, label_tm])
    val reachable_th = computeLib.EVAL_CONV reachable_tm
  in
    REWRITE_RULE [GSYM second_simplify_cfg_substituted_eq_phi_fixed]
      reachable_th
  end

val second_substituted_reachable_ths =
  map eval_second_substituted_reachable second_substituted_blocks

Theorem exact_second_simplify_cfg_substituted_reachability:
  ^(concl (LIST_CONJ second_substituted_reachable_ths))
Proof
  ACCEPT_TAC (LIST_CONJ second_substituted_reachable_ths)
QED

val second_final_remove_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.remove_unreachable_blocks_def ::
     second_substituted_entry_th :: second_substituted_blocks_th ::
     second_substituted_reachable_ths)
    ``remove_unreachable_blocks second_simplify_cfg_substituted``
val second_final_removed_tm = rhs (concl second_final_remove_th)

Definition second_simplify_cfg_final_removed_def:
  second_simplify_cfg_final_removed = ^second_final_removed_tm
End

Theorem exact_second_final_remove_unreachable:
  remove_unreachable_blocks second_simplify_cfg_substituted =
    second_simplify_cfg_final_removed
Proof
  ACCEPT_TAC
    (TRANS second_final_remove_th
      (SYM second_simplify_cfg_final_removed_def))
QED

val second_final_removed_blocks_th =
  computeLib.EVAL_CONV ``second_simplify_cfg_final_removed.fn_blocks``

Theorem second_simplify_cfg_final_removed_blocks:
  ^(concl second_final_removed_blocks_th)
Proof
  ACCEPT_TAC second_final_removed_blocks_th
QED

val _ = export_theory()
