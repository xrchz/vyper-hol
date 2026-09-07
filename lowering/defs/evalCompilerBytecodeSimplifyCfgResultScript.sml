Theory evalCompilerBytecodeSimplifyCfgResult
Ancestors evalCompilerBytecodeRound2Result

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t

val exact_first_simplify_cfg_literal =
  REWRITE_RULE
    [evalCompilerBytecodeStageProbeTheory.first_simplify_cfg_operand_def]
    evalCompilerBytecodeRound2ResultTheory.exact_first_simplify_cfg_fn_with_labels

val exact_first_dispatcher_result =
  SIMP_RULE (srw_ss ()) [exact_first_simplify_cfg_literal]
    evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_dispatcher_context
val _ =
  if has_head ``simplify_cfg_fn_with_labels``
      (concl exact_first_dispatcher_result)
  then raise Fail "SimplifyCFG remained under dispatcher context"
  else ()

Theorem exact_first_simplify_cfg_dispatcher_result:
  ^(concl exact_first_dispatcher_result)
Proof
  ACCEPT_TAC exact_first_dispatcher_result
QED

val exact_first_fold_result =
  SIMP_RULE (srw_ss ()) [exact_first_simplify_cfg_dispatcher_result]
    evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_fold_context

Theorem exact_first_simplify_cfg_fold_result:
  ^(concl exact_first_fold_result)
Proof
  ACCEPT_TAC exact_first_fold_result
QED

val exact_first_transaction_result =
  SIMP_RULE (srw_ss ()) [exact_first_simplify_cfg_fold_result]
    evalCompilerBytecodeStageProbeTheory.exact_first_simplify_cfg_transaction_prefix

Theorem exact_first_configured_simplify_cfg_transaction:
  ^(concl exact_first_transaction_result)
Proof
  ACCEPT_TAC exact_first_transaction_result
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
