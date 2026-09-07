Theory evalCompilerBytecodeSimplifyCfgResult
Ancestors evalCompilerBytecodeRound2Result

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t

val exact_first_simplify_cfg_literal =
  REWRITE_RULE
    [evalCompilerBytecodeStageProbeTheory.first_simplify_cfg_operand_def]
    evalCompilerBytecodeRound2ResultTheory.exact_first_simplify_cfg_fn_with_labels

val exact_first_closed_fold_direct =
  SIMP_RULE (srw_ss ())
    [venomPassDispatcherTheory.execute_configured_fn_pass_simplify_cfg,
     exact_first_simplify_cfg_literal]
    evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_closed_fold_context
val _ =
  if null (free_vars (concl exact_first_closed_fold_direct)) then ()
  else raise Fail "direct SimplifyCFG fold result is not closed"
val _ =
  if has_head ``simplify_cfg_fn_with_labels``
      (concl exact_first_closed_fold_direct)
  then raise Fail "SimplifyCFG remained under direct closed fold context"
  else ()

val exact_first_transaction_result =
  SIMP_RULE (srw_ss ()) [exact_first_closed_fold_direct]
    evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_transaction_prefix
val _ =
  if null (free_vars (concl exact_first_transaction_result)) then ()
  else raise Fail "exact first configured SimplifyCFG transaction is not closed"
val _ =
  if has_head ``simplify_cfg_fn_with_labels``
      (concl exact_first_transaction_result)
  then raise Fail "SimplifyCFG remained under exact configured transaction"
  else ()

Theorem exact_first_configured_simplify_cfg_transaction:
  ^(concl exact_first_transaction_result)
Proof
  ACCEPT_TAC exact_first_transaction_result
QED

val post_first_simplify_cfg_runtime_pre_one =
  SIMP_RULE (srw_ss ())
    [evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_stage_context,
     evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_mapped_context,
     evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_named_context,
     exact_first_configured_simplify_cfg_transaction]
    evalCompilerBytecodeStageProbeTheory.exact_runtime_pre_one_context
val _ =
  if aconv (concl post_first_simplify_cfg_runtime_pre_one)
      (concl evalCompilerBytecodeStageProbeTheory.exact_runtime_pre_one_context)
  then raise Fail "closed transaction rewrite did not reach runtime pre-walk equation"
  else ()
val _ =
  if null (free_vars (concl post_first_simplify_cfg_runtime_pre_one)) then ()
  else raise Fail "post-SimplifyCFG runtime pre-walk equation is not closed"
val _ =
  if has_head ``simplify_cfg_fn_with_labels``
      (concl post_first_simplify_cfg_runtime_pre_one)
  then raise Fail "first SimplifyCFG remained in runtime pre-walk equation"
  else ()
val _ =
  if has_head ``run_pipeline_stages``
      (concl post_first_simplify_cfg_runtime_pre_one)
  then ()
  else raise Fail "remaining pipeline missing after first SimplifyCFG transaction"

Theorem exact_post_first_simplify_cfg_runtime_pre_one:
  ^(concl post_first_simplify_cfg_runtime_pre_one)
Proof
  ACCEPT_TAC post_first_simplify_cfg_runtime_pre_one
QED

val first_stage_tail_fold_tm = find_head ``run_configured_fn_pass_fold``
  (rhs (concl post_first_simplify_cfg_runtime_pre_one))
val _ =
  if null (free_vars first_stage_tail_fold_tm) then ()
  else raise Fail "completed first-stage fold tail is not closed"
val first_stage_tail_fold_done =
  FIRST_CONV
    [REWR_CONV (cj 1 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def),
     REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)]
    first_stage_tail_fold_tm
val post_first_stage =
  SIMP_RULE (srw_ss ()) [first_stage_tail_fold_done]
    post_first_simplify_cfg_runtime_pre_one
val _ =
  if null (free_vars (concl post_first_stage)) then ()
  else raise Fail "post-first-stage runtime equation is not closed"
val _ =
  if has_head ``simplify_cfg_fn_with_labels`` (concl post_first_stage)
  then raise Fail "SimplifyCFG remained after completing first stage"
  else ()
val _ =
  if has_head ``run_pipeline_stages`` (concl post_first_stage) andalso
     has_head ``VP_DretDesugar`` (concl post_first_stage)
  then ()
  else raise Fail "post-first-stage boundary lacks remaining Dret pipeline"

Theorem exact_post_first_stage_runtime_pre_one:
  ^(concl post_first_stage)
Proof
  ACCEPT_TAC post_first_stage
QED

val exact_first_named_result =
  SIMP_RULE (srw_ss ()) [exact_first_configured_simplify_cfg_transaction]
    evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_named_context

Theorem exact_first_simplify_cfg_named_result:
  ^(concl exact_first_named_result)
Proof
  ACCEPT_TAC exact_first_named_result
QED

val exact_first_mapped_result =
  SIMP_RULE (srw_ss ()) [exact_first_simplify_cfg_named_result]
    evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_mapped_context

Theorem exact_first_simplify_cfg_mapped_result:
  ^(concl exact_first_mapped_result)
Proof
  ACCEPT_TAC exact_first_mapped_result
QED

val exact_first_stage_result =
  SIMP_RULE (srw_ss ()) [exact_first_simplify_cfg_mapped_result]
    evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_stage_context

Theorem exact_first_simplify_cfg_stage_result:
  ^(concl exact_first_stage_result)
Proof
  ACCEPT_TAC exact_first_stage_result
QED



val _ = export_theory()
