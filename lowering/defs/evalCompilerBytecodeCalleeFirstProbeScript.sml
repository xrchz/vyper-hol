Theory evalCompilerBytecodeCalleeFirstProbe
Ancestors evalCompilerBytecodeDriverBoundary
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t

val driver_boundary_th =
  evalCompilerBytecodeDriverBoundaryTheory.exact_empty_runtime_driver_to_callee_first
val callee_first_tm = find_head ``run_callee_first``
  (rhs (concl driver_boundary_th))
val _ =
  if null (free_vars callee_first_tm) then ()
  else raise Fail "empty runtime callee-first call is not closed"

val (_, callee_first_args) = strip_comb callee_first_tm
val callee_passes_tm = List.nth (callee_first_args, 1)
val callee_names_tm = List.nth (callee_first_args, 2)
val exact_walk_order_shape = computeLib.EVAL_CONV callee_names_tm
val _ =
  if aconv (rhs (concl exact_walk_order_shape)) ``["__entry"]`` then ()
  else raise Fail "empty runtime callee-first order is not singleton entry"
val exact_passes_shape =
  SIMP_CONV (srw_ss ())
    [venomPassScheduleTheory.o1_pipeline_spec_exact,
     venomPassScheduleTheory.o1_fn_passes_exact]
    callee_passes_tm
val exact_passes_rhs = rhs (concl exact_passes_shape)
val (exact_passes, _) = listSyntax.dest_list exact_passes_rhs
val _ =
  if length exact_passes = 9 andalso
     aconv (List.nth (exact_passes, 0)) ``CFP_Simple VP_MakeSSA`` andalso
     aconv (List.nth (exact_passes, 1)) ``CFP_Simple VP_LowerDload``
  then ()
  else raise Fail "empty runtime configured pass prefix is not MakeSSA/LowerDload"

val callee_one =
  REWR_CONV venomPipelineRunnerTheory.run_callee_first_def callee_first_tm
val callee_shaped =
  CONV_RULE
    (RAND_CONV
      (SIMP_CONV (srw_ss ()) [exact_walk_order_shape, exact_passes_shape]))
    callee_one
val named_runner_tm = rhs (concl callee_shaped)
val named_one =
  REWR_CONV (cj 2 venomPipelineRunnerTheory.run_named_fn_schedules_def)
    named_runner_tm
val configured_tm = find_head ``run_configured_fn_passes``
  (rhs (concl named_one))
val _ =
  if null (free_vars configured_tm) then ()
  else raise Fail "empty runtime configured transaction is not closed"

val configured_one =
  REWR_CONV venomFnScheduleRunnerTheory.run_configured_fn_passes_def
    configured_tm
val coverage_tm = find_head ``ir_supply_covers_unit``
  (rhs (concl configured_one))
val exact_coverage = computeLib.EVAL_CONV coverage_tm
val _ =
  if aconv (rhs (concl exact_coverage)) ``T`` then ()
  else raise Fail "empty runtime IR supply does not cover the walk unit"
val after_coverage = SIMP_RULE (srw_ss ()) [exact_coverage] configured_one

val lookup_tm = find_head ``lookup_unique_function``
  (rhs (concl after_coverage))
val exact_lookup = computeLib.EVAL_CONV lookup_tm
val _ =
  if head_is ``SOME`` (rhs (concl exact_lookup)) then ()
  else raise Fail "empty runtime entry function lookup did not return SOME"
val after_lookup = SIMP_RULE (srw_ss ()) [exact_lookup] after_coverage

val first_fold_tm = find_head ``run_configured_fn_pass_fold``
  (rhs (concl after_lookup))
val _ =
  if null (free_vars first_fold_tm) then ()
  else raise Fail "empty runtime first configured fold is not closed"
val (_, first_fold_args) = strip_comb first_fold_tm
val first_fold_passes_tm = List.nth (first_fold_args, 2)
val (first_fold_passes, _) = listSyntax.dest_list first_fold_passes_tm
val _ =
  if not (null first_fold_passes) andalso
     aconv (hd first_fold_passes) ``CFP_Simple VP_MakeSSA`` andalso
     length first_fold_passes > 1 andalso
     aconv (List.nth (first_fold_passes, 1)) ``CFP_Simple VP_LowerDload``
  then ()
  else raise Fail "closed configured fold does not start MakeSSA/LowerDload"

val first_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    first_fold_tm
val configured_first_context =
  SIMP_RULE (srw_ss ()) [first_fold_one] after_lookup
val named_first_context =
  SIMP_RULE (srw_ss ()) [configured_first_context] named_one
val callee_first_context =
  SIMP_RULE (srw_ss ()) [named_first_context] callee_shaped
val _ =
  if aconv (lhs (concl callee_first_context)) callee_first_tm then ()
  else raise Fail "first-fold context changed the callee-first LHS"
val _ =
  if has_head ``execute_configured_fn_pass``
       (rhs (concl callee_first_context))
  then ()
  else raise Fail "first-fold context does not expose the configured dispatcher"

Theorem exact_empty_runtime_callee_first_first_fold_context:
  ^(concl callee_first_context)
Proof
  ACCEPT_TAC callee_first_context
QED

val _ = export_theory()
