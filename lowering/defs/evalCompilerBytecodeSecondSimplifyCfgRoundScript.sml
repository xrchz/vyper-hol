Theory evalCompilerBytecodeSecondSimplifyCfgRound
Ancestors evalCompilerBytecodeSecondSimplifyCfgCleanup
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

val second_final_removed_blocks_th =
  evalCompilerBytecodeSecondSimplifyCfgCleanupTheory.second_simplify_cfg_final_removed_blocks
val second_final_removed_blocks =
  fst (listSyntax.dest_list (rhs (concl second_final_removed_blocks_th)))

fun eval_second_final_phi_repair bb =
  let
    val label_th =
      computeLib.EVAL_CONV (mk_comb (``\bb : basic_block. bb.bb_label``, bb))
    val label_tm = rhs (concl label_th)
    val preds_tm =
      list_mk_comb
        (``pred_labels``, [``second_simplify_cfg_final_removed``, label_tm])
    val preds_th =
      SIMP_CONV (srw_ss ())
        [evalCompilerBytecodeSecondSimplifyCfgCleanupTheory.second_simplify_cfg_final_removed_def,
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

val second_final_phi_repair_ths =
  List.concat (map eval_second_final_phi_repair second_final_removed_blocks)

Theorem exact_second_final_phi_repairs:
  ^(concl (LIST_CONJ second_final_phi_repair_ths))
Proof
  ACCEPT_TAC (LIST_CONJ second_final_phi_repair_ths)
QED

val second_final_fix_all_phis_th =
  SIMP_CONV (srw_ss ())
    (simplifyCfgDefsTheory.fix_all_phis_def ::
     second_final_removed_blocks_th :: second_final_phi_repair_ths)
    ``fix_all_phis second_simplify_cfg_final_removed``
val second_round1_fn_tm = rhs (concl second_final_fix_all_phis_th)

Definition second_simplify_cfg_round1_fn_def:
  second_simplify_cfg_round1_fn = ^second_round1_fn_tm
End

Theorem exact_second_final_fix_all_phis:
  fix_all_phis second_simplify_cfg_final_removed =
    second_simplify_cfg_round1_fn
Proof
  ACCEPT_TAC
    (TRANS second_final_fix_all_phis_th
      (SYM second_simplify_cfg_round1_fn_def))
QED

Definition second_simplify_cfg_label_map_def:
  second_simplify_cfg_label_map =
    FST (SND second_simplify_cfg_collapse_result)
End

Theorem second_simplify_cfg_label_map_empty:
  second_simplify_cfg_label_map = ([] : (string # string) list)
Proof
  simp[second_simplify_cfg_label_map_def,
       evalCompilerBytecodeSecondSimplifyCfgCollapseTraversalTheory.second_simplify_cfg_collapse_result_components]
QED

Theorem exact_second_simplify_cfg_round_with_labels:
  simplify_cfg_round_with_labels second_simplify_cfg_operand =
    (second_simplify_cfg_round1_fn, REVERSE second_simplify_cfg_label_map)
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_round_with_labels_def,
       evalCompilerBytecodeSecondSimplifyCfgInitialRemoveTheory.second_simplify_cfg_operand_entry,
       evalCompilerBytecodeSecondSimplifyCfgInitialRemoveTheory.exact_second_remove_unreachable,
       evalCompilerBytecodeSecondSimplifyCfgInitialPhiTheory.exact_second_fix_all_phis,
       evalCompilerBytecodeSecondSimplifyCfgCollapseTraversalTheory.exact_second_collapse_dfs,
       evalCompilerBytecodeSecondSimplifyCfgCollapseTraversalTheory.second_simplify_cfg_collapse_result_def,
       second_simplify_cfg_label_map_def] >>
  pure_rewrite_tac [GSYM second_simplify_cfg_substituted_eq_phi_fixed] >>
  simp[exact_second_final_remove_unreachable,
       exact_second_final_fix_all_phis]
QED

val second_round_fixpoint_guard_th =
  computeLib.EVAL_CONV
    ``second_simplify_cfg_round1_fn.fn_blocks =
      second_simplify_cfg_operand.fn_blocks``

Theorem exact_second_round_fixpoint_guard:
  ^(concl second_round_fixpoint_guard_th)
Proof
  ACCEPT_TAC second_round_fixpoint_guard_th
QED

val second_iter_unfold_th =
  SIMP_RULE (srw_ss ()) []
    (Q.SPECL [`2`, `second_simplify_cfg_operand`]
      (cj 2 simplifyCfgDefsTheory.simplify_cfg_iter_with_labels_def))

Theorem exact_second_simplify_cfg_iter_with_labels:
  simplify_cfg_iter_with_labels
      (LENGTH second_simplify_cfg_operand.fn_blocks)
      second_simplify_cfg_operand =
    (second_simplify_cfg_operand, [])
Proof
  simp[evalCompilerBytecodeSecondSimplifyCfgResultTheory.second_simplify_cfg_operand_block_count,
       second_iter_unfold_th,
       exact_second_simplify_cfg_round_with_labels,
       second_simplify_cfg_label_map_empty,
       exact_second_round_fixpoint_guard]
QED

Theorem exact_second_simplify_cfg_fn_with_labels:
  simplify_cfg_fn_with_labels second_simplify_cfg_operand =
    (second_simplify_cfg_operand, [])
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def,
       exact_second_simplify_cfg_iter_with_labels]
QED

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head_arity c n t =
  if head_arity c n t then t else find_term (head_arity c n) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val after_second_make_ssa =
  evalCompilerBytecodeAfterSecondMakeSSATheory.exact_empty_runtime_after_second_make_ssa
val second_simplify_fold_tm =
  find_head_arity ``run_configured_fn_pass_fold`` 7
    (rhs (concl after_second_make_ssa))
val _ = assert_closed "second SimplifyCFG residual fold" second_simplify_fold_tm
val second_simplify_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    second_simplify_fold_tm
fun is_dispatch_case t =
  head_is ``option_CASE`` t andalso has_head ``execute_configured_fn_pass`` t
val second_simplify_unit_case_tm =
  find_term is_dispatch_case (rhs (concl second_simplify_fold_one))
val _ = assert_closed "second SimplifyCFG unit option case"
  second_simplify_unit_case_tm
val second_simplify_unit_case =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    second_simplify_unit_case_tm
val second_simplify_fold_exposed =
  PURE_REWRITE_RULE [second_simplify_unit_case] second_simplify_fold_one
val second_simplify_context_exposed =
  PURE_REWRITE_RULE [second_simplify_fold_exposed] after_second_make_ssa
val second_simplify_dispatch_tm =
  find_head_arity ``execute_configured_fn_pass`` 5
    (rhs (concl second_simplify_context_exposed))
val _ = assert_closed "second SimplifyCFG dispatcher"
  second_simplify_dispatch_tm
val second_simplify_dispatch_one =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_simplify_cfg
    second_simplify_dispatch_tm
val second_simplify_dispatch_named =
  REWRITE_RULE
    [GSYM evalCompilerBytecodeSecondSimplifyCfgResultTheory.second_simplify_cfg_operand_def]
    second_simplify_dispatch_one
val second_simplify_dispatch_result_th =
  REWRITE_RULE [exact_second_simplify_cfg_fn_with_labels]
    second_simplify_dispatch_named

Theorem exact_second_simplify_cfg_dispatch:
  ^(concl second_simplify_dispatch_result_th)
Proof
  ACCEPT_TAC second_simplify_dispatch_result_th
QED

val _ = export_theory()
