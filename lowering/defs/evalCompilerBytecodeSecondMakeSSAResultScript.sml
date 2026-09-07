Theory evalCompilerBytecodeSecondMakeSSAResult
Ancestors evalCompilerBytecodeWalkStageProbe
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

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
val make_ssa_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_fmp))
val _ = assert_closed "second MakeSSA residual fold" make_ssa_fold_tm
val (_, make_ssa_fold_args) = strip_comb make_ssa_fold_tm
val (make_ssa_passes, _) =
  listSyntax.dest_list (List.nth (make_ssa_fold_args, 2))
val _ =
  if not (null make_ssa_passes) andalso
     aconv (hd make_ssa_passes) ``CFP_Simple VP_MakeSSA``
  then () else raise Fail "post-FMP residual fold is not headed by MakeSSA"

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
val second_dispatch_tm = find_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl make_ssa_context_exposed))
val _ = assert_closed "second MakeSSA dispatcher" second_dispatch_tm
val (_, second_dispatch_args) = strip_comb second_dispatch_tm
val _ =
  if aconv (List.nth (second_dispatch_args, 1))
       ``CFP_Simple VP_MakeSSA``
  then () else raise Fail "second configured dispatcher is not MakeSSA"

val second_dispatch_one =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_make_ssa
    second_dispatch_tm
val make_ssa_tm =
  if head_is ``make_ssa_current_fn`` (rhs (concl second_dispatch_one)) then
    rhs (concl second_dispatch_one)
  else find_term (head_is ``make_ssa_current_fn``)
    (rhs (concl second_dispatch_one))
val _ = assert_closed "second make_ssa_current_fn call" make_ssa_tm
val exact_make_ssa = computeLib.EVAL_CONV make_ssa_tm
val exact_second_dispatch_result =
  CONV_RULE
    (RAND_CONV (SIMP_CONV (srw_ss ()) [exact_make_ssa]))
    second_dispatch_one
val _ =
  if aconv (lhs (concl exact_second_dispatch_result)) second_dispatch_tm then ()
  else raise Fail "exact second MakeSSA result changed the dispatcher LHS"
val _ =
  if head_is ``SOME`` (rhs (concl exact_second_dispatch_result)) then ()
  else raise Fail ("exact second MakeSSA dispatcher result is not SOME: " ^
    term_to_string (rhs (concl exact_second_dispatch_result)))
val _ =
  if has_head ``make_ssa_current_fn`` (rhs (concl exact_second_dispatch_result))
  then raise Fail "exact second MakeSSA result retains make_ssa_current_fn"
  else ()

Theorem exact_empty_runtime_second_make_ssa_result:
  ^(concl exact_second_dispatch_result)
Proof
  ACCEPT_TAC exact_second_dispatch_result
QED

val _ = export_theory()
