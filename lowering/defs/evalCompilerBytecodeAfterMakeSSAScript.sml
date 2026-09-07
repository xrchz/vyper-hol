Theory evalCompilerBytecodeAfterMakeSSA
Ancestors evalCompilerBytecodeMakeSSAResult
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head_arity c n t =
  head_arity c n t orelse can (find_term (head_arity c n)) t
fun find_head_arity c n t =
  if head_arity c n t then t else find_term (head_arity c n) t

val first_fold_context_th =
  evalCompilerBytecodeCalleeFirstProbeTheory.exact_empty_runtime_callee_first_first_fold_context
val exact_make_ssa_result =
  evalCompilerBytecodeMakeSSAResultTheory.exact_empty_runtime_first_make_ssa_result
val first_dispatch_tm = lhs (concl exact_make_ssa_result)
fun is_first_dispatch_case t =
  head_is ``option_CASE`` t andalso
  can (find_term (fn u => aconv u first_dispatch_tm)) t
val first_dispatch_case_tm =
  find_term is_first_dispatch_case (rhs (concl first_fold_context_th))
val _ =
  if null (free_vars first_dispatch_case_tm) then ()
  else raise Fail "first MakeSSA result case is not closed"
val after_make_ssa_case_rewritten =
  REWRITE_CONV [exact_make_ssa_result] first_dispatch_case_tm
val after_make_ssa_case_reduced =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    (rhs (concl after_make_ssa_case_rewritten))
val after_make_ssa_case =
  TRANS after_make_ssa_case_rewritten after_make_ssa_case_reduced
val after_make_ssa_context =
  PURE_REWRITE_RULE [after_make_ssa_case] first_fold_context_th
val _ =
  if aconv (lhs (concl after_make_ssa_context))
       (lhs (concl first_fold_context_th))
  then ()
  else raise Fail "MakeSSA recomposition changed the callee-first LHS"
val residual_fold_tm =
  find_head_arity ``run_configured_fn_pass_fold`` 7
    (rhs (concl after_make_ssa_context))
val _ =
  if null (free_vars residual_fold_tm) then ()
  else raise Fail
    ("post-MakeSSA residual configured fold is not closed: " ^
     term_to_string residual_fold_tm ^ " ; free vars: " ^
     String.concatWith ", " (map term_to_string (free_vars residual_fold_tm)))
val (_, residual_fold_args) = strip_comb residual_fold_tm
val residual_passes_tm = List.nth (residual_fold_args, 2)
val (residual_passes, _) = listSyntax.dest_list residual_passes_tm
val _ =
  if not (null residual_passes) andalso
     aconv (hd residual_passes) ``CFP_Simple VP_LowerDload``
  then ()
  else raise Fail "post-MakeSSA residual fold is not headed by LowerDload"

Theorem exact_empty_runtime_after_make_ssa_to_lower_dload:
  ^(concl after_make_ssa_context)
Proof
  ACCEPT_TAC after_make_ssa_context
QED

val _ = export_theory()
