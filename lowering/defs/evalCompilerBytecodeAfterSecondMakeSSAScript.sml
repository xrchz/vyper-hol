Theory evalCompilerBytecodeAfterSecondMakeSSA
Ancestors evalCompilerBytecodeSecondMakeSSAResult
Libs computeLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head_arity c n t =
  if head_arity c n t then t else find_term (head_arity c n) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm ^
    " ; free vars: " ^
    String.concatWith ", " (map term_to_string (free_vars tm)))

val after_fmp =
  evalCompilerBytecodeWalkStageProbeTheory.exact_empty_runtime_after_fmp_lowering
val exact_make_ssa_result =
  evalCompilerBytecodeSecondMakeSSAResultTheory.exact_empty_runtime_second_make_ssa_result
val make_ssa_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_fmp))
val _ = assert_closed "second MakeSSA residual fold" make_ssa_fold_tm
val make_ssa_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    make_ssa_fold_tm
fun is_dispatch_case t =
  head_is ``option_CASE`` t andalso has_head ``execute_configured_fn_pass`` t
val make_ssa_unit_case_tm =
  find_term is_dispatch_case (rhs (concl make_ssa_fold_one))
val _ = assert_closed "second MakeSSA unit option case" make_ssa_unit_case_tm
val make_ssa_unit_case = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  make_ssa_unit_case_tm
val make_ssa_fold_exposed =
  PURE_REWRITE_RULE [make_ssa_unit_case] make_ssa_fold_one
val make_ssa_context_exposed =
  PURE_REWRITE_RULE [make_ssa_fold_exposed] after_fmp

val make_ssa_dispatch_tm = lhs (concl exact_make_ssa_result)
fun is_exact_dispatch_case t =
  head_is ``option_CASE`` t andalso
  can (find_term (fn u => aconv u make_ssa_dispatch_tm)) t
val make_ssa_dispatch_case_tm =
  find_term is_exact_dispatch_case (rhs (concl make_ssa_context_exposed))
val _ = assert_closed "second MakeSSA result option case" make_ssa_dispatch_case_tm
val after_make_ssa_case_rewritten =
  REWRITE_CONV [exact_make_ssa_result] make_ssa_dispatch_case_tm
val after_make_ssa_case_reduced = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  (rhs (concl after_make_ssa_case_rewritten))
val after_make_ssa_case =
  TRANS after_make_ssa_case_rewritten after_make_ssa_case_reduced
val after_second_make_ssa_context =
  PURE_REWRITE_RULE [after_make_ssa_case] make_ssa_context_exposed
val _ =
  if aconv (lhs (concl after_second_make_ssa_context))
       (lhs (concl after_fmp))
  then () else raise Fail "second MakeSSA recomposition changed the outer LHS"
val residual_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_second_make_ssa_context))
val _ = assert_closed "post-second-MakeSSA residual fold" residual_fold_tm
val (_, residual_fold_args) = strip_comb residual_fold_tm
val (residual_passes, _) =
  listSyntax.dest_list (List.nth (residual_fold_args, 2))
val _ =
  if not (null residual_passes) andalso
     aconv (hd residual_passes) ``CFP_Simple VP_SimplifyCFG``
  then () else raise Fail
    "post-second-MakeSSA residual fold is not headed by SimplifyCFG"

Theorem exact_empty_runtime_after_second_make_ssa:
  ^(concl after_second_make_ssa_context)
Proof
  ACCEPT_TAC after_second_make_ssa_context
QED

val _ = export_theory()
