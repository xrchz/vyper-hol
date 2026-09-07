Theory evalCompilerBytecodeEmptyDeployPreWalkResult
Ancestors evalCompilerBytecodeEmptyDeployDretDesugar
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun find_head c t = if head_is c t then t else find_term (head_is c) t
fun find_head_arity c n t =
  if head_arity c n t then t else find_term (head_arity c n) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val direct_discard_boundary =
  evalCompilerBytecodeEmptyDeployDretDesugarTheory.exact_post_dret_closed_discard_runner_empty_deploy_boundary
val discard_runner_tm = rhs (concl direct_discard_boundary)
val _ = assert_closed "deploy DiscardAnalyses runner" discard_runner_tm
val (_, discard_runner_args) = strip_comb discard_runner_tm
val _ =
  if head_arity ``run_pipeline_stages`` 4 discard_runner_tm andalso
     aconv (List.nth (discard_runner_args, 1)) ``[PS_DiscardAnalyses]``
  then () else raise Fail "deploy residual runner is not direct singleton DiscardAnalyses"

val discard_runner_one =
  FIRST_CONV
    [REWR_CONV (cj 1 venomPipelineRunnerTheory.run_pipeline_stages_def),
     REWR_CONV (cj 2 venomPipelineRunnerTheory.run_pipeline_stages_def)]
    discard_runner_tm
val discard_stage_tm = find_head_arity ``run_pipeline_stage`` 4
  (rhs (concl discard_runner_one))
val _ = assert_closed "deploy DiscardAnalyses stage" discard_stage_tm
val exact_discard_stage = computeLib.EVAL_CONV discard_stage_tm
val discard_runner_after_stage =
  CONV_RULE (RAND_CONV (PURE_REWRITE_CONV [exact_discard_stage]))
    discard_runner_one
val discard_runner_to_tail = computeLib.RESTR_EVAL_CONV
  [``run_pipeline_stages``] (rhs (concl discard_runner_after_stage))
val discard_runner_tail_exposed =
  TRANS discard_runner_after_stage discard_runner_to_tail
val empty_tail_tm = rhs (concl discard_runner_tail_exposed)
val _ =
  if head_is ``run_pipeline_stages`` empty_tail_tm then ()
  else raise Fail "deploy DiscardAnalyses result did not expose the runner tail"
val (_, empty_tail_args) = strip_comb empty_tail_tm
val _ =
  if listSyntax.is_list (List.nth (empty_tail_args, 1)) andalso
     null (fst (listSyntax.dest_list (List.nth (empty_tail_args, 1))))
  then ()
  else raise Fail ("deploy runner tail is not empty: " ^ term_to_string empty_tail_tm)
val empty_tail_result =
  FIRST_CONV
    [REWR_CONV (cj 1 venomPipelineRunnerTheory.run_pipeline_stages_def),
     REWR_CONV (cj 2 venomPipelineRunnerTheory.run_pipeline_stages_def)]
    empty_tail_tm
val exact_pre_walk_literal =
  TRANS discard_runner_tail_exposed empty_tail_result
val exact_pre_walk_rhs = rhs (concl exact_pre_walk_literal)
val _ =
  if head_is ``SOME`` exact_pre_walk_rhs then ()
  else raise Fail "deploy pre-walk result is not literal SOME"
val (_, [pre_walk_pair_tm]) = strip_comb exact_pre_walk_rhs
val (pre_walk_unit_tm, pre_walk_supply_tm) = pairSyntax.dest_pair pre_walk_pair_tm
val _ = assert_closed "deploy pre-walk unit" pre_walk_unit_tm
val _ = assert_closed "deploy pre-walk supply" pre_walk_supply_tm

Definition empty_deploy_pre_walk_unit_def:
  empty_deploy_pre_walk_unit = ^pre_walk_unit_tm
End

Definition empty_deploy_pre_walk_supply_def:
  empty_deploy_pre_walk_supply = ^pre_walk_supply_tm
End

val named_pre_walk_result =
  CONV_RULE
    (RAND_CONV
      (PURE_REWRITE_CONV
        [GSYM empty_deploy_pre_walk_unit_def,
         GSYM empty_deploy_pre_walk_supply_def]))
    exact_pre_walk_literal
val _ =
  if aconv (lhs (concl named_pre_walk_result))
       (lhs (concl exact_pre_walk_literal))
  then () else raise Fail "naming deploy pre-walk payload changed the runner LHS"
val _ =
  if aconv (rhs (concl named_pre_walk_result))
       ``SOME (empty_deploy_pre_walk_unit, empty_deploy_pre_walk_supply)``
  then () else raise Fail "named deploy pre-walk result has the wrong RHS"

Theorem exact_empty_deploy_pre_walk_result:
  ^(concl named_pre_walk_result)
Proof
  ACCEPT_TAC named_pre_walk_result
QED


val exact_simplify_named =
  PURE_REWRITE_RULE
    [evalCompilerBytecodeEmptyDeploySimplifyCfgResultTheory.exact_empty_deploy_configured_simplify_cfg_transaction]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_named_context
val exact_simplify_mapped =
  PURE_REWRITE_RULE [exact_simplify_named]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_mapped_context
val exact_simplify_stage =
  PURE_REWRITE_RULE [exact_simplify_mapped]
    evalCompilerBytecodeEmptyDeploySimplifyCfgTheory.exact_empty_deploy_simplify_cfg_stage_context
val complete_after_simplify =
  PURE_REWRITE_RULE [exact_simplify_stage]
    evalCompilerBytecodeEmptyDeployPreWalk1Theory.exact_empty_deploy_complete_pre_walk_one_context
val complete_after_simplify_tail =
  computeLib.RESTR_EVAL_CONV [``run_pipeline_stages``]
    (rhs (concl complete_after_simplify))
val complete_dret_runner =
  TRANS complete_after_simplify complete_after_simplify_tail
val complete_after_dret =
  PURE_REWRITE_RULE
    [evalCompilerBytecodeEmptyDeployDretDesugarTheory.exact_post_dret_closed_discard_runner_empty_deploy_boundary]
    complete_dret_runner
val complete_pre_walk_raw =
  PURE_REWRITE_RULE [exact_empty_deploy_pre_walk_result]
    complete_after_dret
val complete_pre_walk_result =
  SIMP_RULE pure_ss [optionTheory.option_case_def, pairTheory.pair_case_def]
    complete_pre_walk_raw
val complete_pre_walk_lhs = lhs (concl complete_pre_walk_result)
val complete_pre_walk_rhs = rhs (concl complete_pre_walk_result)
val _ = assert_closed "complete deploy pre-walk runner" complete_pre_walk_lhs
val _ =
  if aconv complete_pre_walk_rhs
       ``SOME (empty_deploy_pre_walk_unit, empty_deploy_pre_walk_supply)``
  then ()
  else raise Fail ("complete deploy pre-walk result has wrong RHS: " ^
                   term_to_string complete_pre_walk_rhs)

Theorem exact_empty_deploy_complete_pre_walk_result:
  ^(concl complete_pre_walk_result)
Proof
  ACCEPT_TAC complete_pre_walk_result
QED
val _ = export_theory()
