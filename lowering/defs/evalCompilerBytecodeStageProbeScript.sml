Theory evalCompilerBytecodeStageProbe
Ancestors evalCompilerBytecodeDefs evalCompiler compileVyper
Libs evalCompilerBytecodeLib finite_mapLib computeLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

val tm = ``formal_o1_ir_no_asm_opt 100000 ([] : toplevel list)``
val outer = computeLib.RESTR_EVAL_CONV
  [``lower_vyper_runtime_unit``,
   ``checked_unit_pipeline_fuel_for_testing``,
   ``lower_vyper_deploy_unit``,
   ``run_venom_pipeline``,
   ``run_pipeline_stages``,
   ``run_callee_first``,
   ``codegen_assembly_fuel``] tm
fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t
val lower_tm = find_term (head_is ``lower_vyper_runtime_unit``)
  (rhs (concl outer))
val lower_raw = computeLib.EVAL_CONV lower_tm
val lower_th = SIMP_RULE (srw_ss())
  [finite_mapTheory.FEVERY_FEMPTY,
   venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM] lower_raw
val outer1 = REWRITE_RULE [lower_th] outer
val advance1 = CONV_RULE
  (RAND_CONV (computeLib.RESTR_EVAL_CONV
    [``checked_unit_pipeline_fuel_for_testing``, ``run_venom_pipeline``,
     ``run_pipeline_stages``, ``run_callee_first``, ``codegen_assembly_fuel``,
     ``lower_vyper_deploy_unit``])) outer1
val runtime_checked_tm = find_term
  (head_is ``checked_unit_pipeline_fuel_for_testing``)
  (rhs (concl advance1))
val runtime_checked_outer = computeLib.RESTR_EVAL_CONV
  [``run_venom_pipeline``, ``codegen_assembly_fuel``] runtime_checked_tm
val runtime_pipeline_tm = find_term (head_is ``run_venom_pipeline``)
  (rhs (concl runtime_checked_outer))
val runtime_pipeline_raw = computeLib.RESTR_EVAL_CONV
  [``run_pipeline_stages``, ``run_callee_first``] runtime_pipeline_tm
val runtime_pipeline_outer = SIMP_RULE (srw_ss())
  [finite_mapTheory.FEVERY_FEMPTY,
   venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
  runtime_pipeline_raw
fun rew_rec def tm = FIRST_CONV [REWR_CONV (cj 1 def), REWR_CONV (cj 2 def)] tm

val runtime_pre_tm = find_head ``run_pipeline_stages``
  (rhs (concl runtime_pipeline_outer))
val runtime_pre_one =
  rew_rec venomPipelineRunnerTheory.run_pipeline_stages_def runtime_pre_tm

Theorem exact_runtime_pre_one_context:
  ^(concl runtime_pre_one)
Proof
  ACCEPT_TAC runtime_pre_one
QED
val first_stage_tm = find_head ``run_pipeline_stage``
  (rhs (concl runtime_pre_one))
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
val _ =
  if null (free_vars first_configured_tm) then ()
  else raise Fail ("first configured call free variables: " ^
    String.concatWith ", " (map term_to_string (free_vars first_configured_tm)))
val first_configured_unfold =
  REWR_CONV venomFnScheduleRunnerTheory.run_configured_fn_passes_def
    first_configured_tm
val first_fold_tm = find_head ``run_configured_fn_pass_fold``
  (rhs (concl first_configured_unfold))
val first_fold_one =
  rew_rec venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def
    first_fold_tm
val first_dispatcher_tm = find_head ``execute_configured_fn_pass``
  (rhs (concl first_fold_one))
val first_dispatcher_unfold =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_simplify_cfg
    first_dispatcher_tm
val first_simplify_cfg_tm = find_head ``simplify_cfg_fn_with_labels``
  (rhs (concl first_dispatcher_unfold))

val _ =
  if head_is ``execute_configured_fn_pass`` first_dispatcher_tm andalso
     head_is ``simplify_cfg_fn_with_labels`` first_simplify_cfg_tm
  then ()
  else raise Fail "failed to isolate exact SimplifyCFG operation"


Theorem exact_first_simplify_cfg_named_context:
  ^(concl first_named_one)
Proof
  ACCEPT_TAC first_named_one
QED

Theorem exact_first_simplify_cfg_mapped_context:
  ^(concl mapped_unfold)
Proof
  ACCEPT_TAC mapped_unfold
QED

Theorem exact_first_simplify_cfg_stage_context:
  ^(concl first_stage_unfold)
Proof
  ACCEPT_TAC first_stage_unfold
QED
Theorem exact_first_simplify_cfg_dispatcher_context:
  ^(concl first_dispatcher_unfold)
Proof
  ACCEPT_TAC first_dispatcher_unfold
QED

Theorem exact_first_simplify_cfg_fold_context:
  ^(concl first_fold_one)
Proof
  ACCEPT_TAC first_fold_one
QED

Theorem first_simplify_cfg_operation_unfold:
  !fn.
    simplify_cfg_fn_with_labels fn =
      simplify_cfg_iter_with_labels (LENGTH fn.fn_blocks) fn
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def]
QED

val first_coverage_tm = find_head ``ir_supply_covers_unit``
  (rhs (concl first_configured_unfold))
val first_coverage_th = computeLib.EVAL_CONV first_coverage_tm
val _ =
  if aconv (rhs (concl first_coverage_th)) ``T`` then ()
  else raise Fail "first configured transaction lacks supply coverage"
val first_after_coverage =
  REWRITE_RULE [first_coverage_th] first_configured_unfold
val first_lookup_tm = find_head ``lookup_unique_function``
  (rhs (concl first_after_coverage))
val first_lookup_th = computeLib.EVAL_CONV first_lookup_tm
val first_transaction_prefix = SIMP_RULE (srw_ss())
  [first_lookup_th] first_after_coverage
val first_closed_fold_tm = find_head ``run_configured_fn_pass_fold``
  (rhs (concl first_transaction_prefix))
val _ =
  if null (free_vars first_closed_fold_tm) then ()
  else raise Fail ("first configured fold free variables: " ^
    String.concatWith ", " (map term_to_string (free_vars first_closed_fold_tm)))

Theorem exact_first_simplify_cfg_transaction_prefix:
  ^(concl first_transaction_prefix)
Proof
  ACCEPT_TAC first_transaction_prefix
QED

val first_closed_fold_one =
  rew_rec venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def
    first_closed_fold_tm
val first_closed_dispatcher_tm = find_head ``execute_configured_fn_pass``
  (rhs (concl first_closed_fold_one))
val first_closed_dispatcher_unfold =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_simplify_cfg
    first_closed_dispatcher_tm
val first_closed_simplify_cfg_tm = find_head ``simplify_cfg_fn_with_labels``
  (rhs (concl first_closed_dispatcher_unfold))
val _ =
  if null (free_vars first_closed_simplify_cfg_tm) then ()
  else raise Fail "concrete SimplifyCFG operation is not closed"
val first_closed_simplify_cfg_unfold =
  REWR_CONV first_simplify_cfg_operation_unfold first_closed_simplify_cfg_tm
val first_closed_iter_tm = rhs (concl first_closed_simplify_cfg_unfold)
val first_closed_iter_args = snd (strip_comb first_closed_iter_tm)
val first_closed_iter_count_tm = hd first_closed_iter_args
val first_simplify_cfg_operand_tm = List.nth (first_closed_iter_args, 1)
val _ =
  if null (free_vars first_simplify_cfg_operand_tm) then ()
  else raise Fail "first SimplifyCFG operand is not closed"

Definition first_simplify_cfg_operand_def:
  first_simplify_cfg_operand = ^first_simplify_cfg_operand_tm
End

val first_closed_iter_count_th =
  computeLib.EVAL_CONV first_closed_iter_count_tm
val first_closed_simplify_cfg_count =
  REWRITE_RULE [first_closed_iter_count_th] first_closed_simplify_cfg_unfold
val first_named_simplify_cfg_count =
  REWRITE_RULE [GSYM first_simplify_cfg_operand_def]
    first_closed_simplify_cfg_count

Theorem exact_first_simplify_cfg_named_count:
  ^(concl first_named_simplify_cfg_count)
Proof
  ACCEPT_TAC first_named_simplify_cfg_count
QED

val first_closed_iter_counted_tm =
  rhs (concl first_closed_simplify_cfg_count)
val first_closed_iter_num_def =
  CONV_RULE numLib.SUC_TO_NUMERAL_DEFN_CONV
    (cj 2 simplifyCfgDefsTheory.simplify_cfg_iter_with_labels_def)
val first_closed_iter_one =
  REWR_CONV (cj 1 first_closed_iter_num_def) first_closed_iter_counted_tm
val first_named_iter_one =
  REWRITE_RULE [GSYM first_simplify_cfg_operand_def] first_closed_iter_one

Theorem exact_first_simplify_cfg_named_iter_one:
  ^(concl first_named_iter_one)
Proof
  ACCEPT_TAC first_named_iter_one
QED

val _ = export_theory()
