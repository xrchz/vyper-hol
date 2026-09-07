Theory evalCompilerBytecodeEmptyDeployGraphBoundary
Ancestors evalCompilerBytecodeEmptyDeployPreWalkResult
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
fun find_closed_head_arity c n t =
  let fun p u = head_arity c n u andalso null (free_vars u)
  in if p t then t else find_term p t end
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val frozen_fcg_tm =
  ``fcg_analyze empty_deploy_pre_walk_unit.cu_context``
val exact_frozen_fcg_literal = computeLib.EVAL_CONV frozen_fcg_tm
val frozen_fcg_value_tm = rhs (concl exact_frozen_fcg_literal)
val _ = assert_closed "empty deploy frozen call graph" frozen_fcg_value_tm

Definition empty_deploy_frozen_fcg_def:
  empty_deploy_frozen_fcg = ^frozen_fcg_value_tm
End

val exact_frozen_fcg =
  CONV_RULE
    (RAND_CONV (PURE_REWRITE_CONV [GSYM empty_deploy_frozen_fcg_def]))
    exact_frozen_fcg_literal

Theorem exact_empty_deploy_frozen_fcg:
  ^(concl exact_frozen_fcg)
Proof
  ACCEPT_TAC exact_frozen_fcg
QED

val exact_prune_flag =
  computeLib.EVAL_CONV ``o1_pipeline_spec.ps_prune_unreachable``
val _ =
  if aconv (rhs (concl exact_prune_flag)) ``T`` then ()
  else raise Fail "O1 prune-unreachable flag is not true"

Theorem exact_empty_deploy_o1_prune_unreachable_flag[local]:
  ^(concl exact_prune_flag)
Proof
  ACCEPT_TAC exact_prune_flag
QED

val prune_walk_unit_tm =
  ``prune_unit_fcg_unreachable empty_deploy_pre_walk_unit
      empty_deploy_frozen_fcg``
val exact_prune_walk_unit_literal = computeLib.EVAL_CONV prune_walk_unit_tm
val walk_unit_value_tm = rhs (concl exact_prune_walk_unit_literal)
val _ = assert_closed "empty deploy pruned walk unit" walk_unit_value_tm

Definition empty_deploy_walk_unit_def:
  empty_deploy_walk_unit = ^walk_unit_value_tm
End

val exact_prune_walk_unit =
  CONV_RULE
    (RAND_CONV (PURE_REWRITE_CONV [GSYM empty_deploy_walk_unit_def]))
    exact_prune_walk_unit_literal

Theorem exact_empty_deploy_prune_walk_unit:
  ^(concl exact_prune_walk_unit)
Proof
  ACCEPT_TAC exact_prune_walk_unit
QED

val exact_reachable_acyclic = computeLib.EVAL_CONV
  ``reachable_fcg_acyclic empty_deploy_pre_walk_unit.cu_context
      empty_deploy_frozen_fcg``
val _ =
  if aconv (rhs (concl exact_reachable_acyclic)) ``T`` then ()
  else raise Fail "empty deploy reachable call graph is not acyclic"

Theorem exact_empty_deploy_reachable_fcg_acyclic:
  ^(concl exact_reachable_acyclic)
Proof
  ACCEPT_TAC exact_reachable_acyclic
QED

val exact_entry = computeLib.EVAL_CONV
  ``empty_deploy_pre_walk_unit.cu_context.ctx_entry``
val entry_rhs = rhs (concl exact_entry)
val _ =
  if head_is ``SOME`` entry_rhs then ()
  else raise Fail "empty deploy pre-walk entry is absent"
val entry_tm = optionSyntax.dest_some entry_rhs
val _ = assert_closed "empty deploy entry" entry_tm

Theorem exact_empty_deploy_pre_walk_entry:
  ^(concl exact_entry)
Proof
  ACCEPT_TAC exact_entry
QED

val postorder_tm = ``fcg_postorder empty_deploy_frozen_fcg ^entry_tm``
val exact_postorder_literal = computeLib.EVAL_CONV postorder_tm
val postorder_value_tm = rhs (concl exact_postorder_literal)
val _ = assert_closed "empty deploy call-graph postorder" postorder_value_tm

Definition empty_deploy_walk_order_def:
  empty_deploy_walk_order = ^postorder_value_tm
End

val exact_postorder =
  CONV_RULE
    (RAND_CONV (PURE_REWRITE_CONV [GSYM empty_deploy_walk_order_def]))
    exact_postorder_literal

Theorem exact_empty_deploy_fcg_postorder:
  ^(concl exact_postorder)
Proof
  ACCEPT_TAC exact_postorder
QED

val driver_first_stage =
  evalCompilerBytecodeEmptyDeployPreWalk1Theory.exact_empty_deploy_driver_first_stage_context
val complete_runner_one =
  evalCompilerBytecodeEmptyDeployPreWalk1Theory.exact_empty_deploy_complete_pre_walk_one_context
val driver_with_complete_pre_walk =
  PURE_REWRITE_RULE [GSYM complete_runner_one] driver_first_stage
val complete_pre_walk_call = lhs (concl
  evalCompilerBytecodeEmptyDeployPreWalkResultTheory.exact_empty_deploy_complete_pre_walk_result)
val _ = assert_closed "complete deploy pre-walk call" complete_pre_walk_call
val _ =
  if can (find_term (aconv complete_pre_walk_call))
       (rhs (concl driver_with_complete_pre_walk))
  then ()
  else raise Fail "normalized deploy driver lacks the complete pre-walk call"
val driver_after_pre_walk =
  CONV_RULE
    (RAND_CONV
      (ONCE_DEPTH_CONV
        (REWR_CONV
          evalCompilerBytecodeEmptyDeployPreWalkResultTheory.exact_empty_deploy_complete_pre_walk_result)))
    driver_with_complete_pre_walk
val after_graph =
  SIMP_RULE (boss_ss ())
    [exact_empty_deploy_o1_prune_unreachable_flag,
     exact_empty_deploy_frozen_fcg,
     exact_empty_deploy_prune_walk_unit,
     exact_empty_deploy_reachable_fcg_acyclic,
     exact_empty_deploy_pre_walk_entry,
     exact_empty_deploy_fcg_postorder]
    driver_after_pre_walk

val _ =
  if aconv (lhs (concl after_graph)) (lhs (concl driver_first_stage))
  then () else raise Fail "graph normalization changed the deploy driver LHS"
val _ =
  if can (find_term (aconv complete_pre_walk_call)) (rhs (concl after_graph))
  then raise Fail "complete deploy pre-walk call remains after graph normalization"
  else ()
val callee_first_tm = find_closed_head_arity ``run_callee_first`` 5
  (rhs (concl after_graph))
val _ = assert_closed "empty deploy callee-first call" callee_first_tm
val _ =
  if null (free_vars (rhs (concl after_graph))) then ()
  else raise Fail "empty deploy graph boundary RHS is not closed"

Theorem exact_empty_deploy_driver_to_closed_callee_first:
  ^(concl after_graph)
Proof
  ACCEPT_TAC after_graph
QED

val (_, callee_first_args) = strip_comb callee_first_tm
val callee_passes_tm = List.nth (callee_first_args, 1)
val callee_names_tm = List.nth (callee_first_args, 2)
val exact_walk_order_shape = computeLib.EVAL_CONV callee_names_tm
val exact_passes_shape =
  SIMP_CONV (srw_ss ())
    [venomPassScheduleTheory.o1_pipeline_spec_exact,
     venomPassScheduleTheory.o1_fn_passes_exact]
    callee_passes_tm
val (exact_passes, _) = listSyntax.dest_list (rhs (concl exact_passes_shape))
val _ =
  if length exact_passes = 9 andalso
     aconv (hd exact_passes) ``CFP_Simple VP_MakeSSA``
  then ()
  else raise Fail "empty deploy configured pass list is not nine passes headed MakeSSA"

val callee_one =
  REWR_CONV venomPipelineRunnerTheory.run_callee_first_def callee_first_tm
val callee_shaped =
  CONV_RULE
    (RAND_CONV
      (SIMP_CONV (srw_ss ()) [exact_walk_order_shape, exact_passes_shape]))
    callee_one
val callee_to_first_fold_rhs =
  computeLib.RESTR_EVAL_CONV [``run_configured_fn_pass_fold``]
    (rhs (concl callee_shaped))
val callee_to_first_fold = TRANS callee_shaped callee_to_first_fold_rhs
val first_fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl callee_to_first_fold))
val _ = assert_closed "empty deploy first configured fold" first_fold_tm
val (_, first_fold_args) = strip_comb first_fold_tm
val first_fold_passes_tm = List.nth (first_fold_args, 2)
val (first_fold_passes, _) = listSyntax.dest_list first_fold_passes_tm
val _ =
  if length first_fold_passes = 9 andalso
     aconv (hd first_fold_passes) ``CFP_Simple VP_MakeSSA``
  then ()
  else raise Fail "empty deploy first fold is not nine passes headed MakeSSA"

val exact_driver_first_fold =
  PURE_REWRITE_RULE [callee_to_first_fold] after_graph
val _ =
  if null (free_vars (rhs (concl exact_driver_first_fold))) then ()
  else raise Fail "empty deploy first-fold driver context is not closed"

Theorem exact_empty_deploy_driver_first_make_ssa_fold:
  ^(concl exact_driver_first_fold)
Proof
  ACCEPT_TAC exact_driver_first_fold
QED

val first_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    first_fold_tm
val unit_with_current_fn_tm = find_head ``unit_with_current_fn``
  (rhs (concl first_fold_one))
val _ = assert_closed "empty deploy unit_with_current_fn call" unit_with_current_fn_tm
val exact_unit_with_current_fn = computeLib.EVAL_CONV unit_with_current_fn_tm
val _ =
  if head_is ``SOME`` (rhs (concl exact_unit_with_current_fn)) andalso
     null (free_vars (rhs (concl exact_unit_with_current_fn)))
  then ()
  else raise Fail "empty deploy current-function lookup did not return closed SOME"
fun is_dispatch_option_case t =
  head_is ``option_CASE`` t andalso has_head ``execute_configured_fn_pass`` t
val first_dispatch_case_tm =
  find_term is_dispatch_option_case (rhs (concl first_fold_one))
val _ = assert_closed "empty deploy enclosing first-dispatch option case"
  first_dispatch_case_tm
val exact_first_dispatch_case =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    first_dispatch_case_tm
val first_fold_observed =
  PURE_REWRITE_RULE [exact_first_dispatch_case] first_fold_one
val driver_first_dispatch =
  PURE_REWRITE_RULE [first_fold_observed] exact_driver_first_fold
val first_dispatch_tm = find_closed_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl driver_first_dispatch))
val (_, first_dispatch_args) = strip_comb first_dispatch_tm
val _ =
  if aconv (List.nth (first_dispatch_args, 1)) ``CFP_Simple VP_MakeSSA``
  then () else raise Fail "empty deploy first dispatcher is not MakeSSA"

val first_dispatch_one =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_make_ssa
    first_dispatch_tm
val make_ssa_tm = find_head ``make_ssa_current_fn``
  (rhs (concl first_dispatch_one))
val _ = assert_closed "empty deploy make_ssa_current_fn call" make_ssa_tm
val exact_make_ssa = computeLib.EVAL_CONV make_ssa_tm
val exact_first_dispatch_result =
  CONV_RULE
    (RAND_CONV (SIMP_CONV (srw_ss ()) [exact_make_ssa]))
    first_dispatch_one
val _ =
  if head_is ``SOME`` (rhs (concl exact_first_dispatch_result)) then ()
  else raise Fail "empty deploy exact MakeSSA dispatcher result is not SOME"

fun is_first_dispatch_case t =
  head_is ``option_CASE`` t andalso
  can (find_term (fn u => aconv u first_dispatch_tm)) t
val first_result_case_tm =
  find_term is_first_dispatch_case (rhs (concl driver_first_dispatch))
val _ = assert_closed "empty deploy first MakeSSA result case" first_result_case_tm
val after_make_ssa_case_rewritten =
  REWRITE_CONV [exact_first_dispatch_result] first_result_case_tm
val after_make_ssa_case_reduced =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    (rhs (concl after_make_ssa_case_rewritten))
val after_make_ssa_case =
  TRANS after_make_ssa_case_rewritten after_make_ssa_case_reduced
val after_make_ssa_context =
  PURE_REWRITE_RULE [after_make_ssa_case] driver_first_dispatch
val residual_fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_make_ssa_context))
val (_, residual_fold_args) = strip_comb residual_fold_tm
val residual_passes_tm = List.nth (residual_fold_args, 2)
val (residual_passes, _) = listSyntax.dest_list residual_passes_tm
val _ =
  if not (null residual_passes) andalso
     aconv (hd residual_passes) ``CFP_Simple VP_LowerDload``
  then () else raise Fail "empty deploy residual fold is not headed by LowerDload"
val _ =
  if aconv (lhs (concl after_make_ssa_context))
       (lhs (concl exact_driver_first_fold)) andalso
     null (free_vars (rhs (concl after_make_ssa_context)))
  then () else raise Fail "empty deploy post-MakeSSA driver boundary is malformed"

Theorem exact_empty_deploy_after_make_ssa_to_lower_dload:
  ^(concl after_make_ssa_context)
Proof
  ACCEPT_TAC after_make_ssa_context
QED

val _ = export_theory()
