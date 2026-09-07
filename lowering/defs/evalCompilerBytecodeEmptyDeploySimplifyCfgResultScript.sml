Theory evalCompilerBytecodeEmptyDeploySimplifyCfgResult
Ancestors evalCompilerBytecodeEmptyDeploySimplifyCfgIter

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val exact_simplify_cfg_literal =
  REWRITE_RULE
    [evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.empty_deploy_simplify_cfg_operand_def]
    evalCompilerBytecodeEmptyDeploySimplifyCfgIterTheory.exact_empty_deploy_simplify_cfg_fn_with_labels

val exact_dispatcher_result =
  PURE_REWRITE_RULE [exact_simplify_cfg_literal]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_dispatcher_context
val _ =
  if has_head ``simplify_cfg_fn_with_labels`` (concl exact_dispatcher_result)
  then raise Fail "deploy SimplifyCFG dispatcher rewrite retained the function"
  else ()

val exact_fold_result =
  PURE_REWRITE_RULE [exact_dispatcher_result]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_fold_context
val _ = assert_closed "deploy SimplifyCFG fold result" (concl exact_fold_result)
val _ =
  if has_head ``simplify_cfg_fn_with_labels`` (concl exact_fold_result)
  then raise Fail "deploy SimplifyCFG fold rewrite retained the function"
  else ()

val exact_transaction_result =
  PURE_REWRITE_RULE [exact_fold_result]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_transaction_prefix
val _ = assert_closed "deploy SimplifyCFG transaction result"
  (concl exact_transaction_result)
val _ =
  if has_head ``simplify_cfg_fn_with_labels`` (concl exact_transaction_result)
  then raise Fail "deploy SimplifyCFG transaction rewrite retained the function"
  else ()

Theorem exact_empty_deploy_configured_simplify_cfg_transaction:
  ^(concl exact_transaction_result)
Proof
  ACCEPT_TAC exact_transaction_result
QED

val exact_named_result =
  PURE_REWRITE_RULE [exact_transaction_result]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_named_context
val exact_mapped_result =
  PURE_REWRITE_RULE [exact_named_result]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_mapped_context
val exact_stage_result =
  PURE_REWRITE_RULE [exact_mapped_result]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_stage_context
val post_simplify_cfg_deploy_pre_walk =
  PURE_REWRITE_RULE [exact_stage_result]
    evalCompilerBytecodeEmptyDeployPreWalk1Theory.exact_empty_deploy_driver_first_stage_context

val _ =
  if aconv (concl post_simplify_cfg_deploy_pre_walk)
       (concl evalCompilerBytecodeEmptyDeployPreWalk1Theory.exact_empty_deploy_driver_first_stage_context)
  then raise Fail "deploy SimplifyCFG reinsertion did not change the driver context"
  else ()
val _ = assert_closed "post-SimplifyCFG deploy pre-walk equation"
  (concl post_simplify_cfg_deploy_pre_walk)
val _ =
  if has_head ``simplify_cfg_fn_with_labels``
       (rhs (concl post_simplify_cfg_deploy_pre_walk)) orelse
     has_head ``simplify_cfg_iter_with_labels``
       (rhs (concl post_simplify_cfg_deploy_pre_walk))
  then raise Fail "post-SimplifyCFG deploy boundary retains SimplifyCFG"
  else ()
val _ =
  if has_head ``run_pipeline_stages``
       (rhs (concl post_simplify_cfg_deploy_pre_walk))
  then ()
  else raise Fail "post-SimplifyCFG deploy boundary lacks remaining pipeline"

Theorem exact_post_simplify_cfg_empty_deploy_pre_walk:
  ^(concl post_simplify_cfg_deploy_pre_walk)
Proof
  ACCEPT_TAC post_simplify_cfg_deploy_pre_walk
QED

val _ = export_theory()
