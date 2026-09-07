Theory evalCompilerBytecodeSimplifyCfgResult
Ancestors evalCompilerBytecodeSimplifyCfgProbe

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t

val first_round_rhs = rhs (concl
  evalCompilerBytecodeSimplifyCfgProbeTheory.exact_first_simplify_cfg_round_with_labels)
val (_, first_round_map_tm) = pairSyntax.dest_pair first_round_rhs

val first_iter_unfold_th =
  SIMP_RULE (srw_ss ()) []
    (Q.SPECL [`2`, `first_simplify_cfg_operand`]
      (cj 2 simplifyCfgDefsTheory.simplify_cfg_iter_with_labels_def))

Theorem exact_first_simplify_cfg_fn_with_labels:
  simplify_cfg_fn_with_labels first_simplify_cfg_operand =
    (first_simplify_cfg_operand, ^first_round_map_tm)
Proof
  simp[simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def,
       evalCompilerBytecodeSimplifyCfgProbeTheory.first_simplify_cfg_operand_block_count,
       first_iter_unfold_th,
       evalCompilerBytecodeSimplifyCfgProbeTheory.exact_first_simplify_cfg_round_with_labels,
       evalCompilerBytecodeSimplifyCfgProbeTheory.exact_first_round_fixpoint_guard]
QED

val exact_first_simplify_cfg_literal =
  REWRITE_RULE
    [evalCompilerBytecodeStageProbeTheory.first_simplify_cfg_operand_def]
    exact_first_simplify_cfg_fn_with_labels

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

val post_first_stage_rhs = rhs (concl post_first_stage)
val (_, post_first_stage_case_args) = strip_comb post_first_stage_rhs
val post_first_stage_scrutinee = hd post_first_stage_case_args
val _ =
  if null (free_vars post_first_stage_scrutinee) then ()
  else raise Fail "post-first-stage outer scrutinee is not closed"
val post_first_stage_scrutinee_result =
  computeLib.EVAL_CONV post_first_stage_scrutinee
val closed_runner_boundary =
  SIMP_RULE (srw_ss ()) [post_first_stage_scrutinee_result] post_first_stage
val _ =
  if aconv (concl closed_runner_boundary) (concl post_first_stage) then
    raise Fail "closed outer stage case did not reduce"
  else ()
val _ =
  if null (free_vars (concl closed_runner_boundary)) then ()
  else raise Fail "closed runner boundary theorem is not closed"
val closed_runner_tm = find_head ``run_pipeline_stages``
  (rhs (concl closed_runner_boundary))
val _ =
  if null (free_vars closed_runner_tm) then ()
  else raise Fail "residual Dret pipeline runner is not independently closed"
val _ =
  if has_head ``VP_DretDesugar`` closed_runner_tm andalso
     not (has_head ``simplify_cfg_fn_with_labels`` closed_runner_tm)
  then ()
  else raise Fail "closed runner payload has the wrong remaining pipeline"

Theorem exact_post_first_stage_closed_runner_boundary:
  ^(concl closed_runner_boundary)
Proof
  ACCEPT_TAC closed_runner_boundary
QED

val dret_runner_one =
  FIRST_CONV
    [REWR_CONV (cj 1 venomPipelineRunnerTheory.run_pipeline_stages_def),
     REWR_CONV (cj 2 venomPipelineRunnerTheory.run_pipeline_stages_def)]
    closed_runner_tm
val dret_stage_tm = find_head ``run_pipeline_stage``
  (rhs (concl dret_runner_one))
val _ =
  if null (free_vars dret_stage_tm) then ()
  else raise Fail "Dret stage call is not closed"
val exact_dret_stage_result = computeLib.EVAL_CONV dret_stage_tm
val post_dret_runner = SIMP_RULE (srw_ss ()) [exact_dret_stage_result]
  dret_runner_one
val post_dret_boundary = SIMP_RULE (srw_ss ()) [post_dret_runner]
  closed_runner_boundary
val _ =
  if null (free_vars (concl post_dret_boundary)) then ()
  else raise Fail "post-Dret runtime boundary is not closed"
val _ =
  if has_head ``VP_DretDesugar`` (rhs (concl post_dret_boundary)) then
    raise Fail "DretDesugar remained after exact stage evaluation"
  else ()
val _ =
  if has_head ``PS_DiscardAnalyses`` (rhs (concl post_dret_boundary)) andalso
     has_head ``run_pipeline_stages`` (rhs (concl post_dret_boundary))
  then ()
  else raise Fail "post-Dret boundary lacks the later residual pipeline"

Theorem exact_post_dret_desugar_runtime_boundary:
  ^(concl post_dret_boundary)
Proof
  ACCEPT_TAC post_dret_boundary
QED

val post_dret_guard_normalized =
  SIMP_RULE (srw_ss ())
    [finite_mapTheory.FEVERY_FEMPTY,
     venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
    exact_post_dret_desugar_runtime_boundary

fun reduce_closed_outer_cases 0 th =
      raise Fail "post-Dret normalization exceeded the outer-case budget"
  | reduce_closed_outer_cases n th =
      let
        val r = rhs (concl th)
      in
        if head_is ``run_pipeline_stages`` r then th
        else
          let
            val (_, args) = strip_comb r
            val scrutinee = hd args
            val _ = if null (free_vars scrutinee) then ()
                    else raise Fail "post-Dret outer case scrutinee is not closed"
            val scrutinee_result = computeLib.EVAL_CONV scrutinee
            val th' = SIMP_RULE (srw_ss ()) [scrutinee_result] th
            val _ = if aconv (concl th') (concl th) then
                      raise Fail "post-Dret outer case did not reduce"
                    else ()
          in
            reduce_closed_outer_cases (n - 1) th'
          end
      end

val closed_discard_runner_boundary =
  reduce_closed_outer_cases 8 post_dret_guard_normalized
val closed_discard_runner_tm = rhs (concl closed_discard_runner_boundary)
val _ =
  if head_is ``run_pipeline_stages`` closed_discard_runner_tm then ()
  else raise Fail "post-Dret RHS is not a direct pipeline runner"
val _ =
  if null (free_vars closed_discard_runner_tm) then ()
  else raise Fail "direct post-Dret Discard runner is not closed"
val (_, discard_runner_args) = strip_comb closed_discard_runner_tm
val discard_stage_list_tm = List.nth (discard_runner_args, 1)
val _ =
  if aconv discard_stage_list_tm ``[PS_DiscardAnalyses]`` then ()
  else raise Fail "direct post-Dret runner is not singleton DiscardAnalyses"

Theorem exact_post_dret_closed_discard_runner_boundary:
  ^(concl closed_discard_runner_boundary)
Proof
  ACCEPT_TAC closed_discard_runner_boundary
QED

val discard_runner_one =
  REWR_CONV (cj 2 venomPipelineRunnerTheory.run_pipeline_stages_def)
    closed_discard_runner_tm
val discard_stage_tm = find_head ``run_pipeline_stage``
  (rhs (concl discard_runner_one))
val _ =
  if null (free_vars discard_stage_tm) then ()
  else raise Fail "DiscardAnalyses stage call is not closed"
val exact_discard_stage_result = computeLib.EVAL_CONV discard_stage_tm
val exact_discard_runner_result =
  CONV_RULE
    (RAND_CONV
      (SIMP_CONV (srw_ss ())
        [exact_discard_stage_result,
         venomPipelineRunnerTheory.run_pipeline_stages_def]))
    discard_runner_one
val _ =
  if aconv (lhs (concl exact_discard_runner_result)) closed_discard_runner_tm
  then ()
  else raise Fail "exact Discard runner equation has a mismatched LHS"
val exact_discard_runner_rhs = rhs (concl exact_discard_runner_result)
val _ =
  if head_is ``SOME`` exact_discard_runner_rhs then ()
  else raise Fail "exact Discard runner result is not literal SOME"
val _ =
  if has_head ``run_pipeline_stages`` exact_discard_runner_rhs orelse
     has_head ``run_pipeline_stage`` exact_discard_runner_rhs
  then raise Fail "exact Discard runner result retains a pipeline call"
  else ()

Theorem exact_post_dret_discard_runner_result:
  ^(concl exact_discard_runner_result)
Proof
  ACCEPT_TAC exact_discard_runner_result
QED

val _ =
  if aconv (lhs (concl exact_post_dret_discard_runner_result))
      (rhs (concl exact_post_dret_closed_discard_runner_boundary))
  then ()
  else raise Fail "Discard result no longer matches the normalized boundary"
val exact_pre_walk_literal =
  CONV_RULE (RAND_CONV (REWR_CONV exact_post_dret_discard_runner_result))
    exact_post_dret_closed_discard_runner_boundary
val exact_pre_walk_rhs = rhs (concl exact_pre_walk_literal)
val _ =
  if head_is ``SOME`` exact_pre_walk_rhs then ()
  else raise Fail "composed pre-walk boundary is not literal SOME"
val (_, [pre_walk_pair_tm]) = strip_comb exact_pre_walk_rhs
val (pre_walk_unit_tm, pre_walk_supply_tm) = pairSyntax.dest_pair pre_walk_pair_tm
val _ =
  if null (free_vars pre_walk_unit_tm) andalso
     null (free_vars pre_walk_supply_tm)
  then ()
  else raise Fail "pre-walk snapshot payload is not closed"

Definition empty_runtime_pre_walk_unit_def:
  empty_runtime_pre_walk_unit = ^pre_walk_unit_tm
End

Definition empty_runtime_pre_walk_supply_def:
  empty_runtime_pre_walk_supply = ^pre_walk_supply_tm
End

val named_pre_walk_result =
  CONV_RULE
    (RAND_CONV
      (PURE_REWRITE_CONV
        [GSYM empty_runtime_pre_walk_unit_def,
         GSYM empty_runtime_pre_walk_supply_def]))
    exact_pre_walk_literal
val _ =
  if aconv (lhs (concl named_pre_walk_result))
      (lhs (concl exact_pre_walk_literal))
  then ()
  else raise Fail "naming the pre-walk payload changed the exact LHS"
val _ =
  if aconv (rhs (concl named_pre_walk_result))
      ``SOME (empty_runtime_pre_walk_unit, empty_runtime_pre_walk_supply)``
  then ()
  else raise Fail "named pre-walk result has the wrong RHS"

Theorem exact_empty_runtime_pre_walk_result:
  ^(concl named_pre_walk_result)
Proof
  ACCEPT_TAC named_pre_walk_result
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
