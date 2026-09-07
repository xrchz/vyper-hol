Theory evalCompilerBytecodeEmptyDeployPostFmpSingleUseExpansion
Ancestors evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgResult
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_closed_head_arity c n t =
  find_term
    (fn u => head_arity c n u andalso null (free_vars u))
    t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val incoming =
  evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgResultTheory.exact_empty_deploy_after_post_fmp_simplify_cfg
val fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl incoming))
val fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    fold_tm
fun is_unit_case t =
  head_is ``option_CASE`` t andalso
  has_head ``execute_configured_fn_pass`` t
val unit_case_tm = find_term is_unit_case (rhs (concl fold_one))
val _ = assert_closed "SingleUseExpansion unit option case" unit_case_tm
val unit_case = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  unit_case_tm
val fold_exposed = PURE_REWRITE_RULE [unit_case] fold_one
val context_exposed = PURE_REWRITE_RULE [fold_exposed] incoming
val dispatcher_tm = find_closed_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl context_exposed))
val dispatcher_result = computeLib.EVAL_CONV dispatcher_tm
fun is_result_case t =
  head_is ``option_CASE`` t andalso
  can (find_term (fn u => aconv u dispatcher_tm)) t
val result_case_tm = find_term is_result_case (rhs (concl context_exposed))
val _ = assert_closed "SingleUseExpansion result option case" result_case_tm
val result_case_rewritten = REWRITE_CONV [dispatcher_result] result_case_tm
val result_case_reduced = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  (rhs (concl result_case_rewritten))
val result_case = TRANS result_case_rewritten result_case_reduced
val after_single_use_expansion =
  PURE_REWRITE_RULE [result_case] context_exposed

val next_fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_single_use_expansion))
val (_, next_fold_args) = strip_comb next_fold_tm
val (next_passes, _) = listSyntax.dest_list (List.nth (next_fold_args, 2))
val _ =
  if not (null next_passes) andalso aconv (hd next_passes) ``CFP_Simple VP_DFT``
  then () else raise Fail "post-FMP deploy fold is not headed by DFT"
val _ = assert_closed "post-FMP deploy after SingleUseExpansion"
  (concl after_single_use_expansion)

Theorem exact_empty_deploy_after_post_fmp_single_use_expansion:
  ^(concl after_single_use_expansion)
Proof
  ACCEPT_TAC after_single_use_expansion
QED

val _ = export_theory()
