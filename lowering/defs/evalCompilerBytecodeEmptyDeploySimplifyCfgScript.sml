Theory evalCompilerBytecodeEmptyDeploySimplifyCfg
Ancestors evalCompilerBytecodeEmptyDeployPreWalk1
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)
fun rew_rec def tm =
  FIRST_CONV [REWR_CONV (cj 1 def), REWR_CONV (cj 2 def)] tm

val driver_first_stage_th =
  evalCompilerBytecodeEmptyDeployPreWalk1Theory.exact_empty_deploy_driver_first_stage_context
val first_stage_tm = find_head ``run_pipeline_stage``
  (rhs (concl driver_first_stage_th))
val first_stage_unfold =
  REWR_CONV (cj 1 venomPipelineRunnerTheory.run_pipeline_stage_def)
    first_stage_tm
val mapped_tm = rhs (concl first_stage_unfold)
val mapped_unfold =
  REWR_CONV venomPipelineRunnerTheory.run_mapped_functions_def mapped_tm
val first_named_tm = find_head ``run_named_fn_schedules``
  (rhs (concl mapped_unfold))
val first_named_one = computeLib.RESTR_EVAL_CONV
  [``run_configured_fn_passes``] first_named_tm
val first_configured_tm = find_head ``run_configured_fn_passes``
  (rhs (concl first_named_one))
val _ = assert_closed "deploy SimplifyCFG configured transaction" first_configured_tm
val first_configured_unfold =
  REWR_CONV venomFnScheduleRunnerTheory.run_configured_fn_passes_def
    first_configured_tm
val first_coverage_tm = find_head ``ir_supply_covers_unit``
  (rhs (concl first_configured_unfold))
val first_coverage_th = computeLib.EVAL_CONV first_coverage_tm
val _ =
  if aconv (rhs (concl first_coverage_th)) ``T`` then ()
  else raise Fail "deploy SimplifyCFG transaction lacks supply coverage"
val first_after_coverage =
  REWRITE_RULE [first_coverage_th] first_configured_unfold
val first_lookup_tm = find_head ``lookup_unique_function``
  (rhs (concl first_after_coverage))
val first_lookup_th = computeLib.EVAL_CONV first_lookup_tm
val first_transaction_prefix =
  SIMP_RULE (srw_ss ()) [first_lookup_th] first_after_coverage
val first_closed_fold_tm = find_head ``run_configured_fn_pass_fold``
  (rhs (concl first_transaction_prefix))
val _ = assert_closed "deploy SimplifyCFG closed fold" first_closed_fold_tm
val first_closed_fold_one =
  rew_rec venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def
    first_closed_fold_tm
val first_closed_dispatcher_tm = find_head ``execute_configured_fn_pass``
  (rhs (concl first_closed_fold_one))
val first_closed_dispatcher_unfold =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_simplify_cfg
    first_closed_dispatcher_tm
val first_simplify_cfg_tm = find_head ``simplify_cfg_fn_with_labels``
  (rhs (concl first_closed_dispatcher_unfold))
val _ = assert_closed "deploy concrete SimplifyCFG operation" first_simplify_cfg_tm

Theorem exact_empty_deploy_simplify_cfg_stage_context:
  ^(concl first_stage_unfold)
Proof
  ACCEPT_TAC first_stage_unfold
QED

Theorem exact_empty_deploy_simplify_cfg_mapped_context:
  ^(concl mapped_unfold)
Proof
  ACCEPT_TAC mapped_unfold
QED

Theorem exact_empty_deploy_simplify_cfg_named_context:
  ^(concl first_named_one)
Proof
  ACCEPT_TAC first_named_one
QED

Theorem exact_empty_deploy_simplify_cfg_transaction_prefix:
  ^(concl first_transaction_prefix)
Proof
  ACCEPT_TAC first_transaction_prefix
QED

Theorem exact_empty_deploy_simplify_cfg_fold_context:
  ^(concl first_closed_fold_one)
Proof
  ACCEPT_TAC first_closed_fold_one
QED

Theorem exact_empty_deploy_simplify_cfg_dispatcher_context:
  ^(concl first_closed_dispatcher_unfold)
Proof
  ACCEPT_TAC first_closed_dispatcher_unfold
QED

Theorem deploy_simplify_cfg_operation_unfold[local]:
  !fn.
    simplify_cfg_fn_with_labels fn =
      simplify_cfg_iter_with_labels (LENGTH fn.fn_blocks) fn
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def]
QED

val first_simplify_cfg_unfold =
  REWR_CONV deploy_simplify_cfg_operation_unfold first_simplify_cfg_tm
val first_iter_tm = rhs (concl first_simplify_cfg_unfold)
val first_iter_args = snd (strip_comb first_iter_tm)
val first_count_tm = hd first_iter_args
val first_operand_tm = List.nth (first_iter_args, 1)
val _ = assert_closed "deploy SimplifyCFG operand" first_operand_tm

Definition empty_deploy_simplify_cfg_operand_def:
  empty_deploy_simplify_cfg_operand = ^first_operand_tm
End

val first_count_th = computeLib.EVAL_CONV first_count_tm
val _ =
  if aconv (rhs (concl first_count_th)) ``1`` then ()
  else raise Fail "deploy SimplifyCFG operand does not have one block"
val counted_simplify_cfg =
  REWRITE_RULE [first_count_th] first_simplify_cfg_unfold
val named_counted_simplify_cfg =
  REWRITE_RULE [GSYM empty_deploy_simplify_cfg_operand_def]
    counted_simplify_cfg

Theorem exact_empty_deploy_simplify_cfg_named_count:
  ^(concl named_counted_simplify_cfg)
Proof
  ACCEPT_TAC named_counted_simplify_cfg
QED

val operand_blocks_tm = ``(^first_operand_tm).fn_blocks``
val operand_blocks_th = computeLib.EVAL_CONV operand_blocks_tm
val named_operand_blocks_th =
  REWRITE_RULE [GSYM empty_deploy_simplify_cfg_operand_def] operand_blocks_th

Theorem exact_empty_deploy_simplify_cfg_operand_blocks:
  ^(concl named_operand_blocks_th)
Proof
  ACCEPT_TAC named_operand_blocks_th
QED

val operand_count_tm = ``LENGTH (^first_operand_tm).fn_blocks``
val operand_count_th = computeLib.EVAL_CONV operand_count_tm
val named_operand_count_th =
  REWRITE_RULE [GSYM empty_deploy_simplify_cfg_operand_def] operand_count_th

Theorem exact_empty_deploy_simplify_cfg_operand_count:
  ^(concl named_operand_count_th)
Proof
  ACCEPT_TAC named_operand_count_th
QED

val operand_entry_tm = ``fn_entry_label ^first_operand_tm``
val operand_entry_th = computeLib.EVAL_CONV operand_entry_tm
val named_operand_entry_th =
  REWRITE_RULE [GSYM empty_deploy_simplify_cfg_operand_def] operand_entry_th

Theorem exact_empty_deploy_simplify_cfg_operand_entry:
  ^(concl named_operand_entry_th)
Proof
  ACCEPT_TAC named_operand_entry_th
QED

val _ = export_theory()
