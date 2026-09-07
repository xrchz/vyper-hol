Theory evalCompilerBytecodeWalkPrep
Ancestors evalCompilerBytecodeSimplifyCfgResult
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

val frozen_fcg_tm =
  ``fcg_analyze empty_runtime_pre_walk_unit.cu_context``
val exact_frozen_fcg_literal = computeLib.EVAL_CONV frozen_fcg_tm
val frozen_fcg_value_tm = rhs (concl exact_frozen_fcg_literal)
val _ =
  if null (free_vars frozen_fcg_value_tm) then ()
  else raise Fail "empty runtime frozen call graph is not closed"

Definition empty_runtime_frozen_fcg_def:
  empty_runtime_frozen_fcg = ^frozen_fcg_value_tm
End

val exact_frozen_fcg =
  CONV_RULE
    (RAND_CONV (PURE_REWRITE_CONV [GSYM empty_runtime_frozen_fcg_def]))
    exact_frozen_fcg_literal

Theorem exact_empty_runtime_frozen_fcg:
  ^(concl exact_frozen_fcg)
Proof
  ACCEPT_TAC exact_frozen_fcg
QED

val exact_prune_flag =
  computeLib.EVAL_CONV ``o1_pipeline_spec.ps_prune_unreachable``

val _ =
  if aconv (rhs (concl exact_prune_flag)) ``T`` then ()
  else raise Fail "O1 prune-unreachable flag is not true"

Theorem exact_o1_prune_unreachable_flag:
  ^(concl exact_prune_flag)
Proof
  ACCEPT_TAC exact_prune_flag
QED

val prune_walk_unit_tm =
  ``prune_unit_fcg_unreachable empty_runtime_pre_walk_unit
      empty_runtime_frozen_fcg``
val exact_prune_walk_unit_literal = computeLib.EVAL_CONV prune_walk_unit_tm
val walk_unit_value_tm = rhs (concl exact_prune_walk_unit_literal)
val _ =
  if null (free_vars walk_unit_value_tm) then ()
  else raise Fail "empty runtime pruned walk unit is not closed"

Definition empty_runtime_walk_unit_def:
  empty_runtime_walk_unit = ^walk_unit_value_tm
End

val exact_prune_walk_unit =
  CONV_RULE
    (RAND_CONV (PURE_REWRITE_CONV [GSYM empty_runtime_walk_unit_def]))
    exact_prune_walk_unit_literal

Theorem exact_empty_runtime_prune_walk_unit:
  ^(concl exact_prune_walk_unit)
Proof
  ACCEPT_TAC exact_prune_walk_unit
QED


val selected_walk_unit_tm =
  ``if o1_pipeline_spec.ps_prune_unreachable then
      prune_unit_fcg_unreachable empty_runtime_pre_walk_unit
        empty_runtime_frozen_fcg
    else empty_runtime_pre_walk_unit``
val exact_selected_walk_unit =
  SIMP_CONV (srw_ss ())
    [exact_o1_prune_unreachable_flag,
     exact_empty_runtime_prune_walk_unit]
    selected_walk_unit_tm
val _ =
  if aconv (rhs (concl exact_selected_walk_unit))
      ``empty_runtime_walk_unit``
  then ()
  else raise Fail "selected walk-unit result has the wrong RHS"

Theorem exact_empty_runtime_selected_walk_unit:
  ^(concl exact_selected_walk_unit)
Proof
  ACCEPT_TAC exact_selected_walk_unit
QED

val exact_reachable_acyclic = computeLib.EVAL_CONV
  ``reachable_fcg_acyclic empty_runtime_pre_walk_unit.cu_context
      empty_runtime_frozen_fcg``
val _ =
  if aconv (rhs (concl exact_reachable_acyclic)) ``T`` then ()
  else raise Fail "empty runtime reachable call graph is not acyclic"

Theorem exact_empty_runtime_reachable_fcg_acyclic:
  ^(concl exact_reachable_acyclic)
Proof
  ACCEPT_TAC exact_reachable_acyclic
QED

val exact_entry = computeLib.EVAL_CONV
  ``empty_runtime_pre_walk_unit.cu_context.ctx_entry``
val entry_rhs = rhs (concl exact_entry)
val _ =
  if head_is ``SOME`` entry_rhs then ()
  else raise Fail "empty runtime pre-walk entry is absent"
val (_, [entry_tm]) = strip_comb entry_rhs
val _ =
  if null (free_vars entry_tm) then ()
  else raise Fail "empty runtime entry is not closed"

Theorem exact_empty_runtime_pre_walk_entry:
  ^(concl exact_entry)
Proof
  ACCEPT_TAC exact_entry
QED

val postorder_tm = ``fcg_postorder empty_runtime_frozen_fcg ^entry_tm``
val exact_postorder_literal = computeLib.EVAL_CONV postorder_tm
val postorder_value_tm = rhs (concl exact_postorder_literal)
val _ =
  if null (free_vars postorder_value_tm) then ()
  else raise Fail "empty runtime call-graph postorder is not closed"

Definition empty_runtime_walk_order_def:
  empty_runtime_walk_order = ^postorder_value_tm
End

val exact_postorder =
  CONV_RULE
    (RAND_CONV (PURE_REWRITE_CONV [GSYM empty_runtime_walk_order_def]))
    exact_postorder_literal

Theorem exact_empty_runtime_fcg_postorder:
  ^(concl exact_postorder)
Proof
  ACCEPT_TAC exact_postorder
QED
val _ = export_theory()
