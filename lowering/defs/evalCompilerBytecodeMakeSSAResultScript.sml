Theory evalCompilerBytecodeMakeSSAResult
Ancestors evalCompilerBytecodeCalleeFirstProbe
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t
fun find_head_arity c n t =
  if head_arity c n t then t else find_term (head_arity c n) t

val first_fold_context_th =
  evalCompilerBytecodeCalleeFirstProbeTheory.exact_empty_runtime_callee_first_first_fold_context
val first_dispatch_tm =
  find_head_arity ``execute_configured_fn_pass`` 5
    (rhs (concl first_fold_context_th))
val _ =
  if null (free_vars first_dispatch_tm) then ()
  else raise Fail "first empty-runtime configured dispatcher is not closed"
val (_, first_dispatch_args) = strip_comb first_dispatch_tm
val first_pass_tm = List.nth (first_dispatch_args, 1)
val _ =
  if aconv first_pass_tm ``CFP_Simple VP_MakeSSA`` then ()
  else raise Fail "first empty-runtime configured dispatcher is not MakeSSA"

val first_dispatch_one =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_make_ssa
    first_dispatch_tm
val make_ssa_tm = find_head ``make_ssa_current_fn``
  (rhs (concl first_dispatch_one))
val _ =
  if null (free_vars make_ssa_tm) then ()
  else raise Fail "first empty-runtime make_ssa_current_fn call is not closed"
val exact_make_ssa = computeLib.EVAL_CONV make_ssa_tm
val exact_dispatch_result =
  CONV_RULE
    (RAND_CONV (SIMP_CONV (srw_ss ()) [exact_make_ssa]))
    first_dispatch_one
val _ =
  if aconv (lhs (concl exact_dispatch_result)) first_dispatch_tm then ()
  else raise Fail "exact MakeSSA result changed the dispatcher LHS"
val _ =
  if head_is ``SOME`` (rhs (concl exact_dispatch_result)) then ()
  else raise Fail "exact MakeSSA dispatcher result is not SOME"
val _ =
  if has_head ``make_ssa_current_fn`` (rhs (concl exact_dispatch_result))
  then raise Fail "exact MakeSSA dispatcher result retains make_ssa_current_fn"
  else ()

Theorem exact_empty_runtime_first_make_ssa_result:
  ^(concl exact_dispatch_result)
Proof
  ACCEPT_TAC exact_dispatch_result
QED

val _ = export_theory()
