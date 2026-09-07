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

Theorem second_simplify_cfg_substituted_dispatch_edge:
  fn_succ second_simplify_cfg_substituted "__entry" "@dispatch_1"
Proof
  simp[second_simplify_cfg_substituted_eq_phi_fixed,
       cfgTransformTheory.fn_succ_def,
       evalCompilerBytecodeSecondSimplifyCfgCollapseDecisionsTheory.exact_second_entry_lookup,
       GSYM evalCompilerBytecodeSecondSimplifyCfgCollapseDecisionsTheory.second_simplify_cfg_entry_bb_def,
       evalCompilerBytecodeSecondSimplifyCfgCollapseDecisionsTheory.exact_second_entry_succs]
QED

Theorem second_simplify_cfg_substituted_fallback_edge:
  fn_succ second_simplify_cfg_substituted "__entry" "@fallback_0"
Proof
  simp[second_simplify_cfg_substituted_eq_phi_fixed,
       cfgTransformTheory.fn_succ_def,
       evalCompilerBytecodeSecondSimplifyCfgCollapseDecisionsTheory.exact_second_entry_lookup,
       GSYM evalCompilerBytecodeSecondSimplifyCfgCollapseDecisionsTheory.second_simplify_cfg_entry_bb_def,
       evalCompilerBytecodeSecondSimplifyCfgCollapseDecisionsTheory.exact_second_entry_succs]
QED

Theorem second_simplify_cfg_substituted_entry_reachable:
  reachable second_simplify_cfg_substituted "__entry"
Proof
  simp[cfgTransformTheory.reachable_def,
       second_simplify_cfg_substituted_entry]
QED

Theorem second_simplify_cfg_substituted_dispatch_reachable:
  reachable second_simplify_cfg_substituted "@dispatch_1"
Proof
  simp[cfgTransformTheory.reachable_def,
       second_simplify_cfg_substituted_entry] >>
  metis_tac[relationTheory.RTC_SINGLE,
            second_simplify_cfg_substituted_dispatch_edge]
QED

Theorem second_simplify_cfg_substituted_fallback_reachable:
  reachable second_simplify_cfg_substituted "@fallback_0"
Proof
  simp[cfgTransformTheory.reachable_def,
       second_simplify_cfg_substituted_entry] >>
  metis_tac[relationTheory.RTC_SINGLE,
            second_simplify_cfg_substituted_fallback_edge]
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

val second_filter_pred =
  ``\bb : basic_block.
      reachable second_simplify_cfg_substituted bb.bb_label``

fun second_filter_guard_th (bb, reachable_th) =
  let
    val beta_th = BETA_CONV (mk_comb (second_filter_pred, bb))
    val label_th = RAND_CONV computeLib.EVAL_CONV (rhs (concl beta_th))
  in
    TRANS beta_th (TRANS label_th (EQT_INTRO reachable_th))
  end

val second_filter_guard_ths =
  ListPair.mapEq second_filter_guard_th
    (second_substituted_blocks,
     [second_simplify_cfg_substituted_entry_reachable,
      second_simplify_cfg_substituted_dispatch_reachable,
      second_simplify_cfg_substituted_fallback_reachable])

Theorem second_simplify_cfg_final_filter_all:
  FILTER
    (\bb. reachable second_simplify_cfg_substituted bb.bb_label)
    second_simplify_cfg_substituted.fn_blocks =
  second_simplify_cfg_substituted.fn_blocks
Proof
  pure_rewrite_tac [second_simplify_cfg_substituted_blocks] >>
  pure_rewrite_tac
    (listTheory.FILTER :: boolTheory.COND_CLAUSES ::
     second_filter_guard_ths) >>
  REFL_TAC
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
