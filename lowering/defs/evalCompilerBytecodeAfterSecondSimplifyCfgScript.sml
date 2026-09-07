Theory evalCompilerBytecodeAfterSecondSimplifyCfg
Ancestors evalCompilerBytecodeSecondSimplifyCfgRound
Libs computeLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head_arity c n t =
  if head_arity c n t then t
  else (find_term (head_arity c n) t
        handle HOL_ERR _ => raise Fail
          ("missing head/arity " ^ term_to_string c))
fun find_named label p t =
  find_term p t handle HOL_ERR _ => raise Fail label
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm ^
    " ; free vars: " ^
    String.concatWith ", " (map term_to_string (free_vars tm)))

val after_second_make_ssa =
  evalCompilerBytecodeAfterSecondMakeSSATheory.exact_empty_runtime_after_second_make_ssa
val exact_simplify_result =
  evalCompilerBytecodeSecondSimplifyCfgRoundTheory.exact_second_simplify_cfg_dispatch
val simplify_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_second_make_ssa))
val _ = assert_closed "second SimplifyCFG residual fold" simplify_fold_tm
val simplify_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    simplify_fold_tm
fun is_dispatch_case t =
  head_is ``option_CASE`` t andalso has_head ``execute_configured_fn_pass`` t
val simplify_unit_case_tm =
  find_named "missing dispatcher option case" is_dispatch_case
    (rhs (concl simplify_fold_one))
val _ = assert_closed "second SimplifyCFG unit option case" simplify_unit_case_tm
val simplify_unit_case = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  simplify_unit_case_tm
val simplify_fold_exposed =
  PURE_REWRITE_RULE [simplify_unit_case] simplify_fold_one
val simplify_context_exposed =
  PURE_REWRITE_RULE [simplify_fold_exposed] after_second_make_ssa

val simplify_dispatch_tm = lhs (concl exact_simplify_result)
fun is_exact_dispatch_case t =
  head_is ``option_CASE`` t andalso
  can (find_term (fn u => aconv u simplify_dispatch_tm)) t
val simplify_dispatch_case_tm =
  find_named "missing exact dispatcher option case" is_exact_dispatch_case
    (rhs (concl simplify_context_exposed))
val _ = assert_closed "second SimplifyCFG result option case"
  simplify_dispatch_case_tm
val after_simplify_case_rewritten =
  REWRITE_CONV [exact_simplify_result] simplify_dispatch_case_tm
val after_simplify_case_reduced = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  (rhs (concl after_simplify_case_rewritten))
val after_simplify_case =
  TRANS after_simplify_case_rewritten after_simplify_case_reduced
val after_second_simplify_cfg_context =
  PURE_REWRITE_RULE [after_simplify_case] simplify_context_exposed
val _ =
  if aconv (lhs (concl after_second_simplify_cfg_context))
       (lhs (concl after_second_make_ssa))
  then () else raise Fail "second SimplifyCFG recomposition changed the outer LHS"
val residual_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_second_simplify_cfg_context))
val _ = assert_closed "post-second-SimplifyCFG residual fold" residual_fold_tm
val (_, residual_fold_args) = strip_comb residual_fold_tm
val (residual_passes, _) =
  listSyntax.dest_list (List.nth (residual_fold_args, 2))
val _ =
  if not (null residual_passes) andalso
     aconv (hd residual_passes) ``CFP_Simple VP_SingleUseExpansion``
  then () else raise Fail
    "post-second-SimplifyCFG residual fold is not headed by SingleUseExpansion"

Theorem exact_empty_runtime_after_second_simplify_cfg:
  ^(concl after_second_simplify_cfg_context)
Proof
  ACCEPT_TAC after_second_simplify_cfg_context
QED

val _ = export_theory()
