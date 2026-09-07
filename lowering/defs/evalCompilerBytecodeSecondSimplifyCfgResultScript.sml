Theory evalCompilerBytecodeSecondSimplifyCfgResult
Ancestors evalCompilerBytecodeAfterSecondMakeSSA
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t
fun find_head_arity c n t =
  if head_arity c n t then t else find_term (head_arity c n) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm ^
    " ; free vars: " ^
    String.concatWith ", " (map term_to_string (free_vars tm)))

val after_make_ssa =
  evalCompilerBytecodeAfterSecondMakeSSATheory.exact_empty_runtime_after_second_make_ssa
val simplify_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_make_ssa))
val _ = assert_closed "second SimplifyCFG residual fold" simplify_fold_tm
val simplify_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    simplify_fold_tm
fun is_dispatch_case t =
  head_is ``option_CASE`` t andalso has_head ``execute_configured_fn_pass`` t
val simplify_unit_case_tm =
  find_term is_dispatch_case (rhs (concl simplify_fold_one))
val _ = assert_closed "second SimplifyCFG unit option case" simplify_unit_case_tm
val simplify_unit_case = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  simplify_unit_case_tm
val simplify_fold_exposed =
  PURE_REWRITE_RULE [simplify_unit_case] simplify_fold_one
val simplify_context_exposed =
  PURE_REWRITE_RULE [simplify_fold_exposed] after_make_ssa
val simplify_dispatch_tm = find_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl simplify_context_exposed))
val _ = assert_closed "second SimplifyCFG dispatcher" simplify_dispatch_tm
val (_, simplify_dispatch_args) = strip_comb simplify_dispatch_tm
val _ =
  if aconv (List.nth (simplify_dispatch_args, 1))
       ``CFP_Simple VP_SimplifyCFG``
  then () else raise Fail "second configured dispatcher is not SimplifyCFG"

val simplify_dispatch_one =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_simplify_cfg
    simplify_dispatch_tm
val simplify_operation_tm = find_head ``simplify_cfg_fn_with_labels``
  (rhs (concl simplify_dispatch_one))
val _ = assert_closed "second simplify_cfg_fn_with_labels call" simplify_operation_tm
val (_, [simplify_operand_tm]) = strip_comb simplify_operation_tm

Definition second_simplify_cfg_operand_def:
  second_simplify_cfg_operand = ^simplify_operand_tm
End

val simplify_operation_named =
  REWRITE_RULE [GSYM second_simplify_cfg_operand_def] simplify_dispatch_one
val second_block_count_th =
  computeLib.EVAL_CONV ``LENGTH second_simplify_cfg_operand.fn_blocks``

Theorem second_simplify_cfg_operand_block_count:
  ^(concl second_block_count_th)
Proof
  ACCEPT_TAC second_block_count_th
QED

val _ = export_theory()
