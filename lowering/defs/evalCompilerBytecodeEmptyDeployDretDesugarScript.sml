Theory evalCompilerBytecodeEmptyDeployDretDesugar
Ancestors evalCompilerBytecodeEmptyDeploySimplifyCfgResult
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val post_simplify_cfg =
  evalCompilerBytecodeEmptyDeploySimplifyCfgResultTheory.exact_post_simplify_cfg_empty_deploy_pre_walk
val post_simplify_rhs = rhs (concl post_simplify_cfg)
val (_, outer_case_args) = strip_comb post_simplify_rhs
val pre_walk_scrutinee_tm = hd outer_case_args
val _ = assert_closed "deploy pre-walk scrutinee" pre_walk_scrutinee_tm
val pre_walk_to_dret_runner = computeLib.RESTR_EVAL_CONV
  [``run_pipeline_stages``] pre_walk_scrutinee_tm
val dret_runner_boundary =
  PURE_REWRITE_RULE [pre_walk_to_dret_runner] post_simplify_cfg
val dret_runner_tm = find_head ``run_pipeline_stages``
  (rhs (concl dret_runner_boundary))
val _ = assert_closed "deploy Dret runner" dret_runner_tm
val (_, dret_runner_args) = strip_comb dret_runner_tm
val _ =
  if aconv (List.nth (dret_runner_args, 1))
       ``[PS_MapFunctions (CFP_Simple VP_DretDesugar); PS_DiscardAnalyses]``
  then () else raise Fail "deploy Dret runner has the wrong remaining stages"

val dret_runner_one =
  REWR_CONV (cj 2 venomPipelineRunnerTheory.run_pipeline_stages_def)
    dret_runner_tm
val dret_stage_tm = find_head ``run_pipeline_stage``
  (rhs (concl dret_runner_one))
val _ = assert_closed "deploy Dret stage" dret_stage_tm
val exact_dret_stage = computeLib.EVAL_CONV dret_stage_tm
val dret_runner_after_stage =
  CONV_RULE (RAND_CONV (PURE_REWRITE_CONV [exact_dret_stage]))
    dret_runner_one
val dret_runner_tail = computeLib.RESTR_EVAL_CONV
  [``run_pipeline_stages``] (rhs (concl dret_runner_after_stage))
val exact_dret_runner = TRANS dret_runner_after_stage dret_runner_tail
val post_dret_boundary =
  PURE_REWRITE_RULE [exact_dret_runner] dret_runner_boundary

val _ = assert_closed "post-Dret deploy boundary" (concl post_dret_boundary)
val _ =
  if has_head ``VP_DretDesugar`` (rhs (concl post_dret_boundary))
  then raise Fail "DretDesugar remained after exact deploy stage evaluation"
  else ()
val _ =
  if has_head ``PS_DiscardAnalyses`` (rhs (concl post_dret_boundary)) andalso
     has_head ``run_pipeline_stages`` (rhs (concl post_dret_boundary))
  then ()
  else raise Fail "post-Dret deploy boundary lacks singleton DiscardAnalyses"

Theorem exact_post_dret_desugar_empty_deploy_boundary:
  ^(concl post_dret_boundary)
Proof
  ACCEPT_TAC post_dret_boundary
QED

val _ = export_theory()
