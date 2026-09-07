Theory evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgResult
Ancestors evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgIter

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)
fun find_closed_head_arity c arity tm =
  find_term
    (fn t =>
      let val (h, args) = strip_comb t
      in same_const h c andalso length args = arity andalso null (free_vars t) end
      handle HOL_ERR _ => false)
    tm
fun is_dispatch_option_case t =
  head_is ``option_CASE`` t andalso
  can (find_term (fn u => head_is ``execute_configured_fn_pass`` u)) t

val exact_simplify_cfg_result =
  evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgIterTheory.exact_empty_deploy_post_fmp_simplify_cfg_fn_with_labels

val exact_dispatcher_rewritten =
  PURE_REWRITE_RULE [exact_simplify_cfg_result]
    evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.exact_empty_deploy_post_fmp_simplify_cfg_dispatcher_context
val exact_dispatcher_result =
  CONV_RULE
    (RAND_CONV
      (SIMP_CONV (srw_ss () ++ boolSimps.LET_ss)
        [evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgIterTheory.exact_empty_deploy_post_fmp_round_fixpoint_guard]))
    exact_dispatcher_rewritten
val _ =
  if has_head ``simplify_cfg_fn_with_labels`` (concl exact_dispatcher_result)
  then raise Fail "post-FMP deploy SimplifyCFG dispatcher rewrite retained the function"
  else ()

Theorem exact_empty_deploy_post_fmp_simplify_cfg_dispatch:
  ^(concl exact_dispatcher_result)
Proof
  ACCEPT_TAC exact_dispatcher_result
QED

val after_second_make_ssa =
  evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.exact_empty_deploy_after_second_make_ssa
val simplify_cfg_fold_tm =
  find_closed_head_arity ``run_configured_fn_pass_fold`` 7
    (rhs (concl after_second_make_ssa))
val simplify_cfg_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    simplify_cfg_fold_tm
val simplify_cfg_unit_case_tm =
  find_term is_dispatch_option_case (rhs (concl simplify_cfg_fold_one))
val _ = assert_closed "post-FMP deploy SimplifyCFG unit option case"
  simplify_cfg_unit_case_tm
val simplify_cfg_unit_case =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    simplify_cfg_unit_case_tm
val simplify_cfg_unit_case_dispatch_rewritten =
  CONV_RULE
    (RAND_CONV (REWRITE_CONV [exact_dispatcher_result]))
    simplify_cfg_unit_case
val simplify_cfg_unit_case_dispatch_reduced =
  CONV_RULE
    (RAND_CONV
      (computeLib.RESTR_EVAL_CONV
        [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]))
    simplify_cfg_unit_case_dispatch_rewritten
val simplify_cfg_fold_result =
  PURE_REWRITE_RULE [simplify_cfg_unit_case_dispatch_reduced]
    simplify_cfg_fold_one
val after_simplify_cfg =
  PURE_REWRITE_RULE [simplify_cfg_fold_result]
    after_second_make_ssa

val after_named_operand =
  PURE_REWRITE_RULE
    [GSYM evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.empty_deploy_post_fmp_simplify_cfg_operand_def]
    after_simplify_cfg
val after_dispatch =
  PURE_REWRITE_RULE [exact_dispatcher_result] after_named_operand
val residual_fold_tm =
  find_term (fn t => head_is ``run_configured_fn_pass_fold`` t)
    (rhs (concl after_dispatch))
fun contains_residual t =
  aconv t residual_fold_tm orelse
  (is_comb t andalso
   (contains_residual (rator t) orelse contains_residual (rand t))) orelse
  (is_abs t andalso contains_residual (body t))
fun residual_owner_path t =
  if aconv t residual_fold_tm then [t]
  else if is_comb t andalso contains_residual (rator t)
       then t :: residual_owner_path (rator t)
  else if is_comb t andalso contains_residual (rand t)
       then t :: residual_owner_path (rand t)
  else if is_abs t andalso contains_residual (body t)
       then t :: residual_owner_path (body t)
  else []
val scheduler_cases =
  List.filter (head_is ``option_CASE``)
    (residual_owner_path (rhs (concl after_dispatch)))
val scheduler_case_tm = List.last scheduler_cases
val _ = assert_closed "post-FMP SimplifyCFG scheduler case" scheduler_case_tm
val scheduler_case_ctor =
  REWR_CONV (cj 2 optionTheory.option_case_def) scheduler_case_tm
val scheduler_case_result =
  CONV_RULE (RAND_CONV (REDEPTH_CONV BETA_CONV)) scheduler_case_ctor
val _ = assert_closed "post-FMP SimplifyCFG scheduler equation"
  (concl scheduler_case_result)

Theorem exact_empty_deploy_post_fmp_simplify_cfg_scheduler_case:
  ^(concl scheduler_case_result)
Proof
  ACCEPT_TAC scheduler_case_result
QED

val after_simplify_cfg_closed =
  PURE_REWRITE_RULE [scheduler_case_result] after_dispatch
val next_fold_tm =
  find_closed_head_arity ``run_configured_fn_pass_fold`` 7
    (rhs (concl after_simplify_cfg_closed))
val (_, next_fold_args) = strip_comb next_fold_tm
val (next_passes, _) = listSyntax.dest_list (List.nth (next_fold_args, 2))
val _ =
  if not (null next_passes) andalso
     aconv (hd next_passes) ``CFP_Simple VP_SingleUseExpansion``
  then () else raise Fail
    "post-FMP deploy post-SimplifyCFG fold is not headed by SingleUseExpansion"
val _ = assert_closed "post-FMP deploy post-SimplifyCFG boundary"
  (concl after_simplify_cfg_closed)
val _ =
  if has_head ``simplify_cfg_fn_with_labels``
       (rhs (concl after_simplify_cfg_closed)) orelse
     has_head ``simplify_cfg_iter_with_labels``
       (rhs (concl after_simplify_cfg_closed))
  then raise Fail "post-FMP deploy boundary retains SimplifyCFG"
  else ()

Theorem exact_empty_deploy_after_post_fmp_simplify_cfg:
  ^(concl after_simplify_cfg_closed)
Proof
  ACCEPT_TAC after_simplify_cfg_closed
QED

val _ = export_theory()
