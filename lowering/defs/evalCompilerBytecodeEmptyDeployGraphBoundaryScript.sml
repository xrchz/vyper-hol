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
val _ =
  if aconv (lhs (concl callee_to_first_fold)) callee_first_tm
  then () else raise Fail "standalone deploy callee-first LHS changed"
val _ = assert_closed "standalone deploy callee-first first-fold equation"
  (concl callee_to_first_fold)
val _ =
  if has_head ``run_configured_fn_pass_fold`` (rhs (concl callee_to_first_fold))
  then () else raise Fail "standalone deploy callee-first RHS lacks configured fold"
val _ =
  if has_head ``run_pipeline_stages`` (rhs (concl callee_to_first_fold))
  then raise Fail "standalone deploy callee-first RHS crossed into driver stages"
  else ()

Theorem exact_empty_deploy_callee_first_first_fold:
  ^(concl callee_to_first_fold)
Proof
  ACCEPT_TAC callee_to_first_fold
QED

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

val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

val lower_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    residual_fold_tm
val lower_unit_case_tm =
  find_term is_dispatch_option_case (rhs (concl lower_fold_one))
val _ = assert_closed "empty deploy LowerDload unit option case" lower_unit_case_tm
val lower_unit_case =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    lower_unit_case_tm
val lower_fold_exposed = PURE_REWRITE_RULE [lower_unit_case] lower_fold_one
val lower_context_exposed =
  PURE_REWRITE_RULE [lower_fold_exposed] after_make_ssa_context
val lower_dispatch_tm = find_closed_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl lower_context_exposed))
val (_, lower_dispatch_args) = strip_comb lower_dispatch_tm
val _ =
  if aconv (List.nth (lower_dispatch_args, 1))
       ``CFP_Simple VP_LowerDload``
  then () else raise Fail "empty deploy residual dispatcher is not LowerDload"
val exact_lower_dispatch = computeLib.EVAL_CONV lower_dispatch_tm
val _ =
  if head_is ``SOME`` (rhs (concl exact_lower_dispatch)) then ()
  else raise Fail "empty deploy LowerDload dispatcher result is not SOME"

val lower_dispatch_case_tm =
  find_term
    (fn t => head_is ``option_CASE`` t andalso
      can (find_term (fn u => aconv u lower_dispatch_tm)) t)
    (rhs (concl lower_context_exposed))
val _ = assert_closed "empty deploy LowerDload result option case"
  lower_dispatch_case_tm
val lower_dispatch_case_rewritten =
  REWRITE_CONV [exact_lower_dispatch] lower_dispatch_case_tm
val lower_dispatch_case_reduced =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    (rhs (concl lower_dispatch_case_rewritten))
val lower_dispatch_case =
  TRANS lower_dispatch_case_rewritten lower_dispatch_case_reduced
val after_lower_dload =
  PURE_REWRITE_RULE [lower_dispatch_case] lower_context_exposed
val concretize_fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_lower_dload))
val (_, concretize_fold_args) = strip_comb concretize_fold_tm
val (concretize_passes, _) =
  listSyntax.dest_list (List.nth (concretize_fold_args, 2))
val _ =
  if not (null concretize_passes) andalso
     aconv (hd concretize_passes) ``CFP_Simple VP_ConcretizeMemLoc``
  then () else raise Fail
    "empty deploy post-LowerDload fold is not headed by ConcretizeMemLoc"
val _ =
  if aconv (lhs (concl after_lower_dload))
       (lhs (concl after_make_ssa_context)) andalso
     null (free_vars (rhs (concl after_lower_dload)))
  then () else raise Fail "empty deploy post-LowerDload boundary is malformed"

Theorem exact_empty_deploy_lower_dload_dispatch:
  ^(concl exact_lower_dispatch)
Proof
  ACCEPT_TAC exact_lower_dispatch
QED

Theorem exact_empty_deploy_after_lower_dload:
  ^(concl after_lower_dload)
Proof
  ACCEPT_TAC after_lower_dload
QED

val concretize_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    concretize_fold_tm
val concretize_unit_case_tm =
  find_term is_dispatch_option_case (rhs (concl concretize_fold_one))
val _ = assert_closed "empty deploy ConcretizeMemLoc unit option case"
  concretize_unit_case_tm
val concretize_unit_case =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    concretize_unit_case_tm
val concretize_fold_exposed =
  PURE_REWRITE_RULE [concretize_unit_case] concretize_fold_one
val concretize_context_exposed =
  PURE_REWRITE_RULE [concretize_fold_exposed] after_lower_dload
val concretize_dispatch_tm =
  find_closed_head_arity ``execute_configured_fn_pass`` 5
    (rhs (concl concretize_context_exposed))
val (_, concretize_dispatch_args) = strip_comb concretize_dispatch_tm
val _ =
  if aconv (List.nth (concretize_dispatch_args, 1))
       ``CFP_Simple VP_ConcretizeMemLoc``
  then () else raise Fail
    "empty deploy residual dispatcher is not ConcretizeMemLoc"
val concretize_dispatch_unfold =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_concretize
    concretize_dispatch_tm
val concretize_function_tm = find_closed_head_arity ``concretize_function_eval`` 2
  (rhs (concl concretize_dispatch_unfold))
val (_, concretize_function_args) = strip_comb concretize_function_tm
val deploy_reserved_tm = List.nth (concretize_function_args, 0)
val deploy_fn_tm = List.nth (concretize_function_args, 1)
val complete_positions_tm =
  ``complete_alloc_positions (^deploy_fn_tm).fn_forced_alloc_positions
      ^deploy_reserved_tm ^deploy_fn_tm FEMPTY``
val _ = assert_closed "empty deploy complete allocation positions"
  complete_positions_tm
val exact_complete_positions_raw = computeLib.EVAL_CONV complete_positions_tm
val exact_complete_positions =
  CONV_RULE
    (RAND_CONV
      (SIMP_CONV (srw_ss ())
        [wordsTheory.dimword_def,
         concretizeMemLocDefsTheory.checked_first_fit_def,
         concretizeMemLocDefsTheory.checked_first_fit_scan_def,
         concretizeMemLocDefsTheory.sort_reserved_by_pos_def,
         concretizeMemLocDefsTheory.insert_reserved_by_pos_def,
         staticLayoutDefsTheory.reserved_intervals_wf_def,
         staticLayoutDefsTheory.reserved_interval_wf_def]))
    exact_complete_positions_raw
val complete_positions_rhs = rhs (concl exact_complete_positions)
val _ =
  if head_is ``SOME`` complete_positions_rhs andalso
     null (free_vars complete_positions_rhs)
  then () else raise Fail
    ("empty deploy allocation completion is not closed SOME: " ^
     term_to_string complete_positions_rhs)

Theorem exact_empty_deploy_complete_alloc_positions:
  ^(concl exact_complete_positions)
Proof
  ACCEPT_TAC exact_complete_positions
QED

val deploy_layout_tm =
  ``compute_function_layout_eval ^deploy_reserved_tm ^deploy_fn_tm``
val deploy_layout_one =
  REWR_CONV concretizeMemLocDefsTheory.compute_function_layout_eval_def
    deploy_layout_tm
val deploy_layout_after_positions =
  CONV_RULE (RAND_CONV (REWRITE_CONV [exact_complete_positions]))
    deploy_layout_one
val deploy_layout_simplified =
  CONV_RULE
    (RAND_CONV
      (SIMP_CONV (srw_ss ())
        [wordsTheory.w2n_n2w, wordsTheory.dimword_def,
         venomMemPropsTheory.dimindex_256,
         staticLayoutDefsTheory.mk_concretize_layout_def,
         staticLayoutDefsTheory.global_reserved_end_def,
         staticLayoutDefsTheory.allocation_eom_fold_def,
         staticLayoutDefsTheory.allocation_end_def]))
    deploy_layout_after_positions
val allocation_eom_tm =
  find_closed_head_arity ``allocation_eom_fold`` 3
    (rhs (concl deploy_layout_simplified))
val exact_allocation_eom_raw = computeLib.EVAL_CONV allocation_eom_tm
val exact_allocation_eom =
  CONV_RULE
    (RAND_CONV
      (SIMP_CONV (srw_ss ())
        [wordsTheory.w2n_n2w, wordsTheory.dimword_def,
         venomMemPropsTheory.dimindex_256]))
    exact_allocation_eom_raw
val _ =
  if head_is ``SOME`` (rhs (concl exact_allocation_eom)) then ()
  else raise Fail "empty deploy allocation eom is not literal SOME"
val deploy_layout_with_eom =
  PURE_REWRITE_RULE [exact_allocation_eom] deploy_layout_simplified
val exact_deploy_layout =
  CONV_RULE (RAND_CONV computeLib.EVAL_CONV) deploy_layout_with_eom
val deploy_layout_rhs = rhs (concl exact_deploy_layout)
val _ =
  if head_is ``SOME`` deploy_layout_rhs andalso
     null (free_vars deploy_layout_rhs) andalso
     not (has_head ``FLOOKUP`` deploy_layout_rhs)
  then () else raise Fail
    ("empty deploy static layout is not closed literal SOME: " ^
     term_to_string deploy_layout_rhs)

Theorem exact_empty_deploy_compute_function_layout:
  ^(concl exact_deploy_layout)
Proof
  ACCEPT_TAC exact_deploy_layout
QED

val concretize_function_unfold =
  REWR_CONV concretizeMemLocDefsTheory.concretize_function_eval_def
    concretize_function_tm
val concretize_function_with_layout_case =
  PURE_REWRITE_RULE [exact_deploy_layout] concretize_function_unfold
val concretize_function_with_layout =
  CONV_RULE
    (RAND_CONV
      (computeLib.RESTR_EVAL_CONV [``apply_concretize_layout``]))
    concretize_function_with_layout_case
val apply_layout_tm = find_closed_head_arity ``apply_concretize_layout`` 2
  (rhs (concl concretize_function_with_layout))
val exact_apply_layout = computeLib.EVAL_CONV apply_layout_tm
val concretize_function_result =
  PURE_REWRITE_RULE [exact_apply_layout] concretize_function_with_layout
val concretize_function_rhs = rhs (concl concretize_function_result)
val _ =
  if head_is ``SOME`` concretize_function_rhs andalso
     null (free_vars concretize_function_rhs) andalso
     not (has_head ``FLOOKUP`` concretize_function_rhs) andalso
     not (has_head ``ALLOCA`` concretize_function_rhs)
  then () else raise Fail
    ("empty deploy concretize function is not closed literal SOME: " ^
     term_to_string concretize_function_rhs)

Theorem exact_empty_deploy_concretize_function_eval:
  ^(concl concretize_function_result)
Proof
  ACCEPT_TAC concretize_function_result
QED

val concretize_dispatch_with_function =
  PURE_REWRITE_RULE [concretize_function_result] concretize_dispatch_unfold
val exact_concretize_dispatch =
  CONV_RULE
    (RAND_CONV
      (computeLib.RESTR_EVAL_CONV [``concretize_function_eval``]))
    concretize_dispatch_with_function
val exact_concretize_dispatch_rhs = rhs (concl exact_concretize_dispatch)
val _ =
  if head_is ``SOME`` exact_concretize_dispatch_rhs andalso
     null (free_vars exact_concretize_dispatch_rhs) andalso
     not (has_head ``concretize_function_eval`` exact_concretize_dispatch_rhs)
  then () else raise Fail
    "empty deploy ConcretizeMemLoc dispatcher result is not literal SOME"

Theorem exact_empty_deploy_concretize_dispatch:
  ^(concl exact_concretize_dispatch)
Proof
  ACCEPT_TAC exact_concretize_dispatch
QED

val concretize_dispatch_case_tm =
  find_term
    (fn t => head_is ``option_CASE`` t andalso
      can (find_term (fn u => aconv u concretize_dispatch_tm)) t)
    (rhs (concl concretize_context_exposed))
val _ = assert_closed "empty deploy ConcretizeMemLoc result option case"
  concretize_dispatch_case_tm
val concretize_dispatch_case_rewritten =
  REWRITE_CONV [exact_concretize_dispatch] concretize_dispatch_case_tm
val concretize_dispatch_case_reduced =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    (rhs (concl concretize_dispatch_case_rewritten))
val concretize_dispatch_case =
  TRANS concretize_dispatch_case_rewritten concretize_dispatch_case_reduced
val after_concretize =
  PURE_REWRITE_RULE [concretize_dispatch_case] concretize_context_exposed
val fmp_fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_concretize))
val (_, fmp_fold_args) = strip_comb fmp_fold_tm
val (fmp_passes, _) = listSyntax.dest_list (List.nth (fmp_fold_args, 2))
val _ =
  if not (null fmp_passes) andalso
     aconv (hd fmp_passes) ``CFP_Simple VP_FmpLowering``
  then () else raise Fail
    "empty deploy post-ConcretizeMemLoc fold is not headed by FmpLowering"
val _ =
  if aconv (lhs (concl after_concretize)) (lhs (concl after_lower_dload)) andalso
     null (free_vars (rhs (concl after_concretize)))
  then () else raise Fail
    "empty deploy post-ConcretizeMemLoc boundary is malformed"

Theorem exact_empty_deploy_after_concretize_to_fmp_lowering:
  ^(concl after_concretize)
Proof
  ACCEPT_TAC after_concretize
QED

val fmp_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    fmp_fold_tm
val fmp_unit_case_tm =
  find_term is_dispatch_option_case (rhs (concl fmp_fold_one))
val _ = assert_closed "empty deploy FmpLowering unit option case"
  fmp_unit_case_tm
val fmp_unit_case =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    fmp_unit_case_tm
val fmp_fold_exposed = PURE_REWRITE_RULE [fmp_unit_case] fmp_fold_one
val fmp_context_exposed = PURE_REWRITE_RULE [fmp_fold_exposed] after_concretize
val fmp_dispatch_tm = find_closed_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl fmp_context_exposed))
val (_, fmp_dispatch_args) = strip_comb fmp_dispatch_tm
val _ =
  if aconv (List.nth (fmp_dispatch_args, 1))
       ``CFP_Simple VP_FmpLowering``
  then () else raise Fail "empty deploy residual dispatcher is not FmpLowering"
val fmp_policy_tm = List.nth (fmp_dispatch_args, 0)
val fmp_unit_tm = List.nth (fmp_dispatch_args, 2)
val fmp_supply_tm = List.nth (fmp_dispatch_args, 3)
val fmp_function_tm = List.nth (fmp_dispatch_args, 4)
val fmp_dispatch_unfold =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_fmp
    fmp_dispatch_tm
val fmp_lower_tm = find_closed_head_arity ``fmp_lower_function`` 3
  (rhs (concl fmp_dispatch_unfold))
val (_, fmp_lower_args) = strip_comb fmp_lower_tm
val fmp_context_tm = List.nth (fmp_lower_args, 0)
val _ = assert_closed "empty deploy FMP policy" fmp_policy_tm
val _ = assert_closed "empty deploy FMP unit" fmp_unit_tm
val _ = assert_closed "empty deploy FMP context" fmp_context_tm
val _ = assert_closed "empty deploy FMP supply" fmp_supply_tm
val _ = assert_closed "empty deploy FMP function" fmp_function_tm

val fmp_analysis_tm = list_mk_comb (``analyze_fmp_context``, [fmp_context_tm])
val exact_fmp_analysis_raw = computeLib.EVAL_CONV fmp_analysis_tm
val fmp_analysis_rhs = rhs (concl exact_fmp_analysis_raw)
val (_, fmp_analysis_result_args) = strip_comb fmp_analysis_rhs
val _ =
  if head_is ``SOME`` fmp_analysis_rhs andalso
     length fmp_analysis_result_args = 1
  then () else raise Fail "empty deploy FMP analysis did not return SOME"
val fmp_infos_tm = hd fmp_analysis_result_args
val _ = assert_closed "empty deploy FMP analysis information" fmp_infos_tm

Definition empty_deploy_fmp_infos_def:
  empty_deploy_fmp_infos = ^fmp_infos_tm
End

val exact_fmp_analysis =
  REWRITE_RULE [GSYM empty_deploy_fmp_infos_def] exact_fmp_analysis_raw

Theorem exact_empty_deploy_fmp_analysis:
  ^(concl exact_fmp_analysis)
Proof
  ACCEPT_TAC exact_fmp_analysis
QED

Theorem exact_empty_deploy_fmp_info_valid:
  fmp_info_valid ^fmp_context_tm empty_deploy_fmp_infos
Proof
  irule fmpAnalysisPropsTheory.analyze_fmp_context_valid >>
  ACCEPT_TAC exact_empty_deploy_fmp_analysis
QED

val fmp_lower_input_tm = list_mk_comb
  (``fmp_lower_input``, [fmp_infos_tm, fmp_context_tm, fmp_function_tm])
val exact_fmp_lower_input_raw = computeLib.EVAL_CONV fmp_lower_input_tm
val exact_fmp_lower_input =
  REWRITE_RULE [GSYM empty_deploy_fmp_infos_def] exact_fmp_lower_input_raw

Theorem exact_empty_deploy_fmp_lower_input:
  ^(concl exact_fmp_lower_input)
Proof
  ACCEPT_TAC exact_fmp_lower_input
QED

val fmp_lookup_tm =
  ``FLOOKUP ^fmp_infos_tm (^fmp_function_tm).fn_name``
val exact_fmp_lookup_raw = computeLib.EVAL_CONV fmp_lookup_tm
val exact_fmp_lookup =
  REWRITE_RULE [GSYM empty_deploy_fmp_infos_def] exact_fmp_lookup_raw

Theorem exact_empty_deploy_fmp_bottom_lookup:
  ^(concl exact_fmp_lookup)
Proof
  ACCEPT_TAC exact_fmp_lookup
QED

Theorem empty_deploy_bb_well_formed_snoc[local]:
  is_terminator term.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
  EVERY (\i. i.inst_opcode <> PHI) (prefix ++ [term]) ==>
  bb_well_formed
    <| bb_label := lbl; bb_instructions := prefix ++ [term] |>
Proof
  rw[venomWfTheory.bb_well_formed_def] >>
  rpt strip_tac >> simp[]
  >- (Cases_on `i < LENGTH prefix`
      >- gvs[listTheory.EVERY_EL, listTheory.EL_APPEND_EQN]
      >> `i = LENGTH prefix` by decide_tac
      >> simp[listTheory.EL_APPEND_EQN])
  >> Cases_on `j < LENGTH prefix`
  >- gvs[listTheory.EVERY_EL, listTheory.EL_APPEND_EQN]
  >> `j = LENGTH prefix` by decide_tac
  >> gvs[listTheory.EL_APPEND_EQN]
QED

Theorem empty_deploy_fn_inst_wf_from_blocks[local]:
  (!bb. MEM bb fn.fn_blocks ==>
        EVERY inst_wf bb.bb_instructions) ==>
  fn_inst_wf fn
Proof
  rw[venomWfTheory.fn_inst_wf_def] >>
  first_x_assum drule >>
  simp[listTheory.EVERY_MEM]
QED

fun eval_fmp_closed label tm =
  let val _ = assert_closed label tm
  in computeLib.EVAL_CONV tm end

val fmp_blocks_th = eval_fmp_closed "deploy FMP function block projection"
  ``(^fmp_function_tm).fn_blocks``
val (fmp_blocks, _) = listSyntax.dest_list (rhs (concl fmp_blocks_th))
val _ = if length fmp_blocks = 1 then ()
        else raise Fail ("deploy FMP function block count: " ^
          Int.toString (length fmp_blocks))
val fmp_bb_tm = hd fmp_blocks
val fmp_bb_insts_th = eval_fmp_closed "deploy FMP block instructions"
  ``(^fmp_bb_tm).bb_instructions``
val (fmp_bb_insts, _) = listSyntax.dest_list (rhs (concl fmp_bb_insts_th))
val _ = if length fmp_bb_insts = 4 then ()
        else raise Fail ("deploy FMP block instruction count: " ^
          Int.toString (length fmp_bb_insts))
val fmp_bb_succs_th = eval_fmp_closed "deploy FMP block successors"
  ``bb_succs ^fmp_bb_tm``

Theorem empty_deploy_fmp_bb_snoc_shape[local]:
  ^fmp_bb_tm =
    <| bb_label := (^fmp_bb_tm).bb_label;
       bb_instructions := FRONT ((^fmp_bb_tm).bb_instructions) ++
                          [LAST ((^fmp_bb_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED

Theorem empty_deploy_fmp_bb_well_formed[local]:
  bb_well_formed ^fmp_bb_tm
Proof
  once_rewrite_tac[empty_deploy_fmp_bb_snoc_shape] >>
  irule empty_deploy_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem empty_deploy_fmp_bb_instructions_wf[local]:
  EVERY inst_wf (^fmp_bb_tm).bb_instructions
Proof
  EVAL_TAC >> simp[]
QED

Theorem exact_empty_deploy_fmp_function_well_formed:
  wf_function ^fmp_function_tm
Proof
  simp[venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def,
       venomWfTheory.fn_succs_closed_def,
       venomWfTheory.fn_inst_ids_distinct_def,
       venomInstTheory.fn_labels_def,
       empty_deploy_fmp_bb_well_formed,
       fmp_bb_succs_th]
QED

Theorem exact_empty_deploy_fmp_function_inst_wf:
  fn_inst_wf ^fmp_function_tm
Proof
  irule empty_deploy_fn_inst_wf_from_blocks >>
  rpt strip_tac >>
  gvs[fmp_blocks_th, empty_deploy_fmp_bb_instructions_wf]
QED
val fmp_reclaim_states_tm =
  ``fmp_reclaim_states ^fmp_function_tm``
val exact_fmp_reclaim_states_raw =
  eval_fmp_closed "empty-deploy FMP reclaim states" fmp_reclaim_states_tm
val fmp_reclaim_states_rhs = rhs (concl exact_fmp_reclaim_states_raw)
val (_, fmp_reclaim_states_result_args) = strip_comb fmp_reclaim_states_rhs
val _ =
  if head_is ``SOME`` fmp_reclaim_states_rhs andalso
     length fmp_reclaim_states_result_args = 1
  then () else raise Fail "empty-deploy FMP reclaim states did not return SOME"
val fmp_states_tm = hd fmp_reclaim_states_result_args
val _ = assert_closed "empty-deploy FMP reclaim-state payload" fmp_states_tm

Definition empty_deploy_fmp_states_def:
  empty_deploy_fmp_states = ^fmp_states_tm
End

val exact_fmp_reclaim_states =
  REWRITE_RULE [GSYM empty_deploy_fmp_states_def]
    exact_fmp_reclaim_states_raw

Theorem exact_empty_deploy_fmp_reclaim_states:
  ^(concl exact_fmp_reclaim_states)
Proof
  ACCEPT_TAC exact_fmp_reclaim_states
QED

val fmp_candidate_tm = list_mk_comb
  (``fmp_candidate_plan``,
   [fmp_infos_tm, fmp_context_tm, fmp_function_tm, fmp_states_tm])
val exact_fmp_candidate_raw =
  eval_fmp_closed "empty-deploy FMP candidate plan" fmp_candidate_tm
val _ =
  if fst (dest_const (rhs (concl exact_fmp_candidate_raw))) = "FEMPTY"
  then () else raise Fail
    ("empty-deploy FMP candidate result: " ^
     term_to_string (rhs (concl exact_fmp_candidate_raw)))
val exact_fmp_candidate =
  REWRITE_RULE [GSYM empty_deploy_fmp_infos_def,
                GSYM empty_deploy_fmp_states_def]
    exact_fmp_candidate_raw

Theorem exact_empty_deploy_fmp_candidate_empty:
  ^(concl exact_fmp_candidate)
Proof
  ACCEPT_TAC exact_fmp_candidate
QED

Theorem exact_empty_deploy_fmp_reclaim_result:
  analyze_fmp_reclaims empty_deploy_fmp_infos ^fmp_context_tm
    ^fmp_function_tm = SOME FEMPTY
Proof
  irule fmpReclaimPropsTheory.analyze_fmp_reclaims_ready >>
  simp[exact_empty_deploy_fmp_info_valid,
       exact_empty_deploy_fmp_function_well_formed,
       exact_empty_deploy_fmp_function_inst_wf,
       exact_empty_deploy_fmp_reclaim_states,
       exact_empty_deploy_fmp_candidate_empty,
       fmpReclaimDefsTheory.fmp_reclaim_plan_ok_def] >>
  EVAL_TAC
QED

Theorem exact_empty_deploy_fmp_reclaim_input:
  fmp_reclaim_input ^fmp_function_tm FEMPTY
Proof
  simp[fmpLowerDefsTheory.fmp_reclaim_input_def]
QED
val fmp_checked_seal_tm = list_mk_comb
  (``fmp_checked_seal``,
   [fmp_context_tm, fmp_function_tm, ``fmp_info_bottom``,
    ``(^fmp_function_tm).fn_blocks``])
val exact_fmp_checked_seal_raw =
  eval_fmp_closed "empty-deploy FMP checked seal" fmp_checked_seal_tm
val fmp_checked_seal_rhs = rhs (concl exact_fmp_checked_seal_raw)
val (_, fmp_checked_seal_result_args) = strip_comb fmp_checked_seal_rhs
val _ =
  if head_is ``SOME`` fmp_checked_seal_rhs andalso
     length fmp_checked_seal_result_args = 1
  then () else raise Fail "empty-deploy FMP checked seal did not return SOME"
val fmp_sealed_function_tm = hd fmp_checked_seal_result_args
val _ = assert_closed "empty-deploy sealed FMP function" fmp_sealed_function_tm

Definition empty_deploy_fmp_sealed_function_def:
  empty_deploy_fmp_sealed_function = ^fmp_sealed_function_tm
End

val exact_fmp_checked_seal =
  exact_fmp_checked_seal_raw
  |> SIMP_RULE (srw_ss ()) [fmpAnalysisDefsTheory.fmp_info_bottom_def]
  |> REWRITE_RULE [GSYM empty_deploy_fmp_sealed_function_def]

Theorem exact_empty_deploy_fmp_checked_seal:
  ^(concl exact_fmp_checked_seal)
Proof
  ACCEPT_TAC exact_fmp_checked_seal
QED



Theorem exact_empty_deploy_fmp_with_info:
  fmp_lower_function_with_info empty_deploy_fmp_infos ^fmp_context_tm
    ^fmp_supply_tm ^fmp_function_tm =
  SOME (empty_deploy_fmp_sealed_function,^fmp_supply_tm)
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_with_info_def,
       exact_empty_deploy_fmp_info_valid,
       exact_empty_deploy_fmp_lower_input,
       exact_empty_deploy_fmp_bottom_lookup,
       exact_empty_deploy_fmp_reclaim_result,
       exact_empty_deploy_fmp_reclaim_input,
       exact_empty_deploy_fmp_checked_seal,
       fmpAnalysisDefsTheory.fmp_info_bottom_def]
QED

val exact_fmp_with_info_normalized =
  SIMP_RULE (srw_ss ()) [] exact_empty_deploy_fmp_with_info

Theorem exact_empty_deploy_fmp_lower:
  fmp_lower_function ^fmp_context_tm ^fmp_supply_tm ^fmp_function_tm =
  SOME (empty_deploy_fmp_sealed_function,^fmp_supply_tm)
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       exact_empty_deploy_fmp_analysis,
       exact_fmp_with_info_normalized]
QED

val fmp_dispatch_with_lower =
  PURE_REWRITE_RULE [exact_empty_deploy_fmp_lower] fmp_dispatch_unfold
val exact_fmp_dispatch =
  CONV_RULE
    (RAND_CONV
      (computeLib.RESTR_EVAL_CONV [``fmp_lower_function``]))
    fmp_dispatch_with_lower
val exact_fmp_dispatch_rhs = rhs (concl exact_fmp_dispatch)
val _ =
  if head_is ``SOME`` exact_fmp_dispatch_rhs andalso
     null (free_vars exact_fmp_dispatch_rhs) andalso
     not (has_head ``fmp_lower_function`` exact_fmp_dispatch_rhs)
  then () else raise Fail
    "empty deploy FmpLowering dispatcher result is not literal SOME"

Theorem exact_empty_deploy_fmp_dispatch:
  ^(concl exact_fmp_dispatch)
Proof
  ACCEPT_TAC exact_fmp_dispatch
QED

val fmp_dispatch_case_tm =
  find_term
    (fn t => head_is ``option_CASE`` t andalso
      can (find_term (fn u => aconv u fmp_dispatch_tm)) t)
    (rhs (concl fmp_context_exposed))
val _ = assert_closed "empty deploy FmpLowering result option case"
  fmp_dispatch_case_tm
val fmp_dispatch_case_rewritten =
  REWRITE_CONV [exact_fmp_dispatch] fmp_dispatch_case_tm
val fmp_dispatch_case_reduced =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    (rhs (concl fmp_dispatch_case_rewritten))
val fmp_dispatch_case =
  TRANS fmp_dispatch_case_rewritten fmp_dispatch_case_reduced
val after_fmp_lowering =
  PURE_REWRITE_RULE [fmp_dispatch_case] fmp_context_exposed
val second_make_ssa_fold_tm =
  find_closed_head_arity ``run_configured_fn_pass_fold`` 7
    (rhs (concl after_fmp_lowering))
val (_, second_make_ssa_fold_args) = strip_comb second_make_ssa_fold_tm
val (second_make_ssa_passes, _) =
  listSyntax.dest_list (List.nth (second_make_ssa_fold_args, 2))
val _ =
  if not (null second_make_ssa_passes) andalso
     aconv (hd second_make_ssa_passes) ``CFP_Simple VP_MakeSSA``
  then () else raise Fail
    "empty deploy post-FmpLowering fold is not headed by MakeSSA"
val _ =
  if aconv (lhs (concl after_fmp_lowering))
       (lhs (concl after_concretize)) andalso
     null (free_vars (rhs (concl after_fmp_lowering))) andalso
     not (has_head ``fmp_lower_function`` (rhs (concl after_fmp_lowering)))
  then () else raise Fail
    "empty deploy post-FmpLowering boundary is malformed"

Theorem exact_empty_deploy_after_fmp_lowering:
  ^(concl after_fmp_lowering)
Proof
  ACCEPT_TAC after_fmp_lowering
QED

val second_make_ssa_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    second_make_ssa_fold_tm
val second_make_ssa_unit_case_tm =
  find_term is_dispatch_option_case (rhs (concl second_make_ssa_fold_one))
val _ = assert_closed "empty deploy second MakeSSA unit option case"
  second_make_ssa_unit_case_tm
val second_make_ssa_unit_case =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    second_make_ssa_unit_case_tm
val second_make_ssa_fold_exposed =
  PURE_REWRITE_RULE [second_make_ssa_unit_case] second_make_ssa_fold_one
val second_make_ssa_context_exposed =
  PURE_REWRITE_RULE [second_make_ssa_fold_exposed] after_fmp_lowering
val second_make_ssa_dispatch_tm =
  find_closed_head_arity ``execute_configured_fn_pass`` 5
    (rhs (concl second_make_ssa_context_exposed))
val (_, second_make_ssa_dispatch_args) = strip_comb second_make_ssa_dispatch_tm
val _ =
  if aconv (List.nth (second_make_ssa_dispatch_args, 1))
       ``CFP_Simple VP_MakeSSA``
  then () else raise Fail "empty deploy second dispatcher is not MakeSSA"
val second_make_ssa_dispatch_one =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_make_ssa
    second_make_ssa_dispatch_tm
val second_make_ssa_tm = find_closed_head_arity ``make_ssa_current_fn`` 2
  (rhs (concl second_make_ssa_dispatch_one))
val exact_second_make_ssa = computeLib.EVAL_CONV second_make_ssa_tm
val exact_second_make_ssa_dispatch =
  CONV_RULE
    (RAND_CONV (SIMP_CONV (srw_ss ()) [exact_second_make_ssa]))
    second_make_ssa_dispatch_one
val _ =
  if head_is ``SOME`` (rhs (concl exact_second_make_ssa_dispatch)) andalso
     null (free_vars (rhs (concl exact_second_make_ssa_dispatch)))
  then () else raise Fail
    "empty deploy exact second MakeSSA dispatcher result is not closed SOME"

Theorem exact_empty_deploy_second_make_ssa_dispatch:
  ^(concl exact_second_make_ssa_dispatch)
Proof
  ACCEPT_TAC exact_second_make_ssa_dispatch
QED

val second_make_ssa_dispatch_case_tm =
  find_term
    (fn t => head_is ``option_CASE`` t andalso
      can (find_term (fn u => aconv u second_make_ssa_dispatch_tm)) t)
    (rhs (concl second_make_ssa_context_exposed))
val _ = assert_closed "empty deploy second MakeSSA result option case"
  second_make_ssa_dispatch_case_tm
val second_make_ssa_dispatch_case_rewritten =
  REWRITE_CONV [exact_second_make_ssa_dispatch]
    second_make_ssa_dispatch_case_tm
val second_make_ssa_dispatch_case_reduced =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    (rhs (concl second_make_ssa_dispatch_case_rewritten))
val second_make_ssa_dispatch_case =
  TRANS second_make_ssa_dispatch_case_rewritten
    second_make_ssa_dispatch_case_reduced
val after_second_make_ssa =
  PURE_REWRITE_RULE [second_make_ssa_dispatch_case]
    second_make_ssa_context_exposed
val simplify_cfg_fold_tm =
  find_closed_head_arity ``run_configured_fn_pass_fold`` 7
    (rhs (concl after_second_make_ssa))
val (_, simplify_cfg_fold_args) = strip_comb simplify_cfg_fold_tm
val (simplify_cfg_passes, _) =
  listSyntax.dest_list (List.nth (simplify_cfg_fold_args, 2))
val _ =
  if not (null simplify_cfg_passes) andalso
     aconv (hd simplify_cfg_passes) ``CFP_Simple VP_SimplifyCFG``
  then () else raise Fail
    "empty deploy post-second-MakeSSA fold is not headed by SimplifyCFG"
val _ =
  if aconv (lhs (concl after_second_make_ssa))
       (lhs (concl after_fmp_lowering)) andalso
     null (free_vars (rhs (concl after_second_make_ssa)))
  then () else raise Fail
    "empty deploy post-second-MakeSSA boundary is malformed"

Theorem exact_empty_deploy_after_second_make_ssa:
  ^(concl after_second_make_ssa)
Proof
  ACCEPT_TAC after_second_make_ssa
QED

val simplify_cfg_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    simplify_cfg_fold_tm
val simplify_cfg_unit_case_tm =
  find_term is_dispatch_option_case (rhs (concl simplify_cfg_fold_one))
val _ = assert_closed "empty deploy configured SimplifyCFG unit option case"
  simplify_cfg_unit_case_tm
val simplify_cfg_unit_case =
  computeLib.RESTR_EVAL_CONV
    [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
    simplify_cfg_unit_case_tm
val simplify_cfg_fold_exposed =
  PURE_REWRITE_RULE [simplify_cfg_unit_case] simplify_cfg_fold_one
val simplify_cfg_context_exposed =
  PURE_REWRITE_RULE [simplify_cfg_fold_exposed] after_second_make_ssa
val simplify_cfg_dispatch_tm =
  find_closed_head_arity ``execute_configured_fn_pass`` 5
    (rhs (concl simplify_cfg_context_exposed))
val (_, simplify_cfg_dispatch_args) = strip_comb simplify_cfg_dispatch_tm
val _ =
  if aconv (List.nth (simplify_cfg_dispatch_args, 1))
       ``CFP_Simple VP_SimplifyCFG``
  then () else raise Fail "empty deploy configured dispatcher is not SimplifyCFG"
val simplify_cfg_dispatch_unfold =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_simplify_cfg
    simplify_cfg_dispatch_tm
val simplify_cfg_fn_tm =
  find_closed_head_arity ``simplify_cfg_fn_with_labels`` 1
    (rhs (concl simplify_cfg_dispatch_unfold))
val (_, simplify_cfg_fn_args) = strip_comb simplify_cfg_fn_tm
val simplify_cfg_operand_tm = hd simplify_cfg_fn_args
val _ = assert_closed "empty deploy post-FMP SimplifyCFG operand"
  simplify_cfg_operand_tm

Definition empty_deploy_post_fmp_simplify_cfg_operand_def:
  empty_deploy_post_fmp_simplify_cfg_operand = ^simplify_cfg_operand_tm
End

val simplify_cfg_dispatch_named =
  REWRITE_RULE [GSYM empty_deploy_post_fmp_simplify_cfg_operand_def]
    simplify_cfg_dispatch_unfold

Theorem exact_empty_deploy_post_fmp_simplify_cfg_dispatcher_context:
  ^(concl simplify_cfg_dispatch_named)
Proof
  ACCEPT_TAC simplify_cfg_dispatch_named
QED

val simplify_cfg_blocks_raw = computeLib.EVAL_CONV
  ``(^simplify_cfg_operand_tm).fn_blocks``
val simplify_cfg_blocks =
  REWRITE_RULE [GSYM empty_deploy_post_fmp_simplify_cfg_operand_def]
    simplify_cfg_blocks_raw
val (simplify_cfg_blocks_list, _) =
  listSyntax.dest_list (rhs (concl simplify_cfg_blocks))
val _ =
  if length simplify_cfg_blocks_list = 1 then ()
  else raise Fail "empty deploy post-FMP SimplifyCFG operand is not singleton"

Theorem exact_empty_deploy_post_fmp_simplify_cfg_blocks:
  ^(concl simplify_cfg_blocks)
Proof
  ACCEPT_TAC simplify_cfg_blocks
QED

val simplify_cfg_count_raw = computeLib.EVAL_CONV
  ``LENGTH (^simplify_cfg_operand_tm).fn_blocks``
val _ =
  if aconv (rhs (concl simplify_cfg_count_raw)) ``1`` then ()
  else raise Fail "empty deploy post-FMP SimplifyCFG operand count is not one"
val simplify_cfg_count =
  REWRITE_RULE [GSYM empty_deploy_post_fmp_simplify_cfg_operand_def]
    simplify_cfg_count_raw

Theorem exact_empty_deploy_post_fmp_simplify_cfg_block_count:
  ^(concl simplify_cfg_count)
Proof
  ACCEPT_TAC simplify_cfg_count
QED

val simplify_cfg_entry_raw = computeLib.EVAL_CONV
  ``fn_entry_label ^simplify_cfg_operand_tm``
val simplify_cfg_entry =
  REWRITE_RULE [GSYM empty_deploy_post_fmp_simplify_cfg_operand_def]
    simplify_cfg_entry_raw

Theorem exact_empty_deploy_post_fmp_simplify_cfg_entry:
  ^(concl simplify_cfg_entry)
Proof
  ACCEPT_TAC simplify_cfg_entry
QED

val _ = export_theory()
