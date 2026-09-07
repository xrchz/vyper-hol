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

val normalized_dret_runner =
  SIMP_RULE (srw_ss ())
    [finite_mapTheory.FEVERY_FEMPTY,
     venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
    exact_dret_runner
val normalized_dret_rhs = rhs (concl normalized_dret_runner)
val normalized_dret_rhs_result = computeLib.RESTR_EVAL_CONV
  [``run_pipeline_stages``] normalized_dret_rhs
val closed_discard_runner_boundary =
  TRANS normalized_dret_runner normalized_dret_rhs_result
val closed_discard_runner_tm = rhs (concl closed_discard_runner_boundary)
val _ =
  if head_is ``run_pipeline_stages`` closed_discard_runner_tm then ()
  else raise Fail ("deploy post-Dret RHS is not a direct pipeline runner: " ^
    term_to_string closed_discard_runner_tm)
val (_, closed_discard_args) = strip_comb closed_discard_runner_tm
val _ =
  if length closed_discard_args = 4 then ()
  else raise Fail "deploy post-Dret runner is not fully applied at arity four"
val _ = assert_closed "direct deploy DiscardAnalyses runner"
  closed_discard_runner_tm
val _ =
  if aconv (List.nth (closed_discard_args, 1)) ``[PS_DiscardAnalyses]``
  then ()
  else raise Fail "direct deploy runner is not singleton DiscardAnalyses"
val _ =
  if has_head ``VP_DretDesugar`` closed_discard_runner_tm
  then raise Fail "DretDesugar remained in the direct deploy runner"
  else ()

Theorem exact_post_dret_desugar_empty_deploy_boundary:
  ^(concl post_dret_boundary)
Proof
  ACCEPT_TAC post_dret_boundary
QED

Theorem exact_post_dret_closed_discard_runner_empty_deploy_boundary:
  ^(concl closed_discard_runner_boundary)
Proof
  ACCEPT_TAC closed_discard_runner_boundary
QED

val _ = export_theory()
