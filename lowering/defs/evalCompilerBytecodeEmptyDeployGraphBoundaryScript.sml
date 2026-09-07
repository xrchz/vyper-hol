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
val _ = export_theory()
