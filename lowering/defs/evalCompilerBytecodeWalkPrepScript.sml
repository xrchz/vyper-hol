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

fun first_unit_function label unit_tm =
  let
    val functions_th = computeLib.EVAL_CONV
      ``(^unit_tm).cu_context.ctx_functions``
    val (functions, _) = listSyntax.dest_list (rhs (concl functions_th))
  in
    if length functions = 1 then hd functions
    else raise Fail (label ^ " does not contain exactly one function")
  end

val pre_walk_function_tm = first_unit_function "pre-walk unit"
  ``empty_runtime_pre_walk_unit``
val selected_walk_function_tm = first_unit_function "selected walk unit"
  ``empty_runtime_walk_unit``
val _ =
  if null (free_vars selected_walk_function_tm) then ()
  else raise Fail "selected walk function is not closed"

Definition empty_runtime_walk_function_def:
  empty_runtime_walk_function = ^selected_walk_function_tm
End

fun eval_cfg_projection fn_tm =
  let
    fun normalize th =
      CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss ()) [])) th
    val labels = normalize (computeLib.EVAL_CONV
      ``MAP bb_label (^fn_tm).fn_blocks``)
    val succs = normalize (computeLib.EVAL_CONV
      ``MAP bb_succs (^fn_tm).fn_blocks``)
    val closed = normalize (computeLib.EVAL_CONV ``fn_succs_closed ^fn_tm``)
    val blocks = computeLib.EVAL_CONV ``LENGTH (^fn_tm).fn_blocks``
  in
    (labels, succs, closed, blocks)
  end

val (pre_walk_labels, pre_walk_succs, pre_walk_closed,
     pre_walk_block_count) = eval_cfg_projection pre_walk_function_tm
val (selected_walk_labels, selected_walk_succs, selected_walk_closed,
     selected_walk_block_count) = eval_cfg_projection selected_walk_function_tm
val _ =
  if aconv (rhs (concl pre_walk_block_count)) ``3`` andalso
     aconv (rhs (concl selected_walk_block_count)) ``3``
  then ()
  else raise Fail "corrected walk preparation did not preserve three CFG blocks"
val selected_walk_blocks_th = computeLib.EVAL_CONV
  ``(^selected_walk_function_tm).fn_blocks``
val (selected_walk_blocks, _) =
  listSyntax.dest_list (rhs (concl selected_walk_blocks_th))
val selected_walk_block_succs = map (fn bb => computeLib.EVAL_CONV
  ``bb_succs ^bb``) selected_walk_blocks
val _ =
  if length selected_walk_blocks = 3 then ()
  else raise Fail "selected walk function does not have three blocks"

Theorem exact_empty_runtime_walk_function:
  empty_runtime_walk_function = ^selected_walk_function_tm
Proof
  simp[empty_runtime_walk_function_def]
QED


Theorem empty_runtime_walk_function_succs_closed:
  fn_succs_closed empty_runtime_walk_function
Proof
  simp[empty_runtime_walk_function_def,
       venomWfTheory.fn_succs_closed_def,
       venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def,
       venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def,
       venomInstTheory.fn_labels_def,
       listTheory.nub_def] >>
  rpt strip_tac >>
  gvs[LIST_CONJ selected_walk_block_succs,
      venomInstTheory.is_terminator_def,
      venomStateTheory.get_label_def]
QED
Theorem exact_empty_runtime_walk_cfg_provenance:
  ^(concl pre_walk_labels) /\
  ^(concl pre_walk_succs) /\
  ^(concl pre_walk_closed) /\
  ^(concl pre_walk_block_count) /\
  ^(concl selected_walk_labels) /\
  ^(concl selected_walk_succs) /\
  ^(concl selected_walk_closed) /\
  ^(concl selected_walk_block_count)
Proof
  ACCEPT_TAC (LIST_CONJ
    [pre_walk_labels, pre_walk_succs, pre_walk_closed, pre_walk_block_count,
     selected_walk_labels, selected_walk_succs, selected_walk_closed,
     selected_walk_block_count])
QED
val _ = export_theory()
