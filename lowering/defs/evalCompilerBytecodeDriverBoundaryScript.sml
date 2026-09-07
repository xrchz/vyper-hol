Theory evalCompilerBytecodeDriverBoundary
Ancestors evalCompilerBytecodeWalkPrep
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t

val pre_runner_tm =
  lhs (concl evalCompilerBytecodeSimplifyCfgResultTheory.exact_empty_runtime_pre_walk_result)
val (_, pre_runner_args) = strip_comb pre_runner_tm
val runtime_rpolicy_tm = List.nth (pre_runner_args, 0)
val runtime_input_unit_tm = List.nth (pre_runner_args, 2)
val runtime_driver_tm =
  ``run_venom_pipeline (K T) (K T) (K T) ^runtime_rpolicy_tm
      o1_pipeline_spec ^runtime_input_unit_tm``
val runtime_driver_one =
  REWR_CONV venomPipelineDriverTheory.run_venom_pipeline_def runtime_driver_tm

Theorem runtime_unit_wf_intro[local]:
  ctx_wf unit.cu_context /\
  wf_invoke_targets unit.cu_context /\
  ctx_inst_ids_distinct unit.cu_context /\
  (!fn. MEM fn unit.cu_context.ctx_functions ==>
        wf_function fn /\ fn_inst_wf fn) /\
  unit_labels_wf unit ==>
  unit_wf unit
Proof
  rw[venomCompilerWfTheory.unit_wf_def,
     venomWfTheory.venom_wf_def]
QED

Theorem runtime_bb_well_formed_snoc[local]:
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

Theorem runtime_fn_inst_wf_from_blocks[local]:
  (!bb. MEM bb fn.fn_blocks ==>
        EVERY inst_wf bb.bb_instructions) ==>
  fn_inst_wf fn
Proof
  rw[venomWfTheory.fn_inst_wf_def] >>
  first_x_assum drule >>
  simp[listTheory.EVERY_MEM]
QED

fun eval_closed label tm =
  let
    val _ = if null (free_vars tm) then ()
            else raise Fail (label ^ " is not closed")
  in
    computeLib.EVAL_CONV tm
  end

val runtime_functions_th = eval_closed "runtime function projection"
  ``(^runtime_input_unit_tm).cu_context.ctx_functions``
val runtime_functions = fst (listSyntax.dest_list (rhs (concl runtime_functions_th)))
val _ = if length runtime_functions = 1 then ()
        else raise Fail "runtime context does not have exactly one function"
val runtime_fn_tm = hd runtime_functions

val runtime_blocks_th = eval_closed "runtime block projection"
  ``(^runtime_fn_tm).fn_blocks``
val runtime_blocks = fst (listSyntax.dest_list (rhs (concl runtime_blocks_th)))
val _ = if length runtime_blocks = 3 then ()
        else raise Fail "runtime function does not have exactly three blocks"
val runtime_bb0_tm = List.nth (runtime_blocks, 0)
val runtime_bb1_tm = List.nth (runtime_blocks, 1)
val runtime_bb2_tm = List.nth (runtime_blocks, 2)

fun block_instructions label bb =
  let
    val th = eval_closed label ``(^bb).bb_instructions``
    val insts = fst (listSyntax.dest_list (rhs (concl th)))
  in
    (th, insts)
  end
val (runtime_bb0_insts_th, runtime_bb0_insts) =
  block_instructions "runtime entry instruction projection" runtime_bb0_tm
val (runtime_bb1_insts_th, runtime_bb1_insts) =
  block_instructions "runtime dispatch instruction projection" runtime_bb1_tm
val (runtime_bb2_insts_th, runtime_bb2_insts) =
  block_instructions "runtime fallback instruction projection" runtime_bb2_tm
val _ =
  if map length [runtime_bb0_insts, runtime_bb1_insts, runtime_bb2_insts] =
       [4, 3, 1] andalso
     length (List.concat
       [runtime_bb0_insts, runtime_bb1_insts, runtime_bb2_insts]) = 8
  then ()
  else raise Fail "runtime block instruction cardinalities are not 4/3/1"

val runtime_bb0_succs_th = eval_closed "runtime entry successors"
  ``bb_succs ^runtime_bb0_tm``
val runtime_bb1_succs_th = eval_closed "runtime dispatch successors"
  ``bb_succs ^runtime_bb1_tm``
val runtime_bb2_succs_th = eval_closed "runtime fallback successors"
  ``bb_succs ^runtime_bb2_tm``
val runtime_data_segment_th = eval_closed "runtime data segment projection"
  ``(^runtime_input_unit_tm).cu_data_segment``
val _ =
  if null (fst (listSyntax.dest_list (rhs (concl runtime_data_segment_th)))) then ()
  else raise Fail "runtime data segment is not empty"

Theorem runtime_functions_shape[local]:
  ^(concl runtime_functions_th)
Proof
  ACCEPT_TAC runtime_functions_th
QED

Theorem runtime_blocks_shape[local]:
  ^(concl runtime_blocks_th)
Proof
  ACCEPT_TAC runtime_blocks_th
QED

Theorem runtime_bb0_instructions_shape[local]:
  ^(concl runtime_bb0_insts_th)
Proof
  ACCEPT_TAC runtime_bb0_insts_th
QED

Theorem runtime_bb1_instructions_shape[local]:
  ^(concl runtime_bb1_insts_th)
Proof
  ACCEPT_TAC runtime_bb1_insts_th
QED

Theorem runtime_bb2_instructions_shape[local]:
  ^(concl runtime_bb2_insts_th)
Proof
  ACCEPT_TAC runtime_bb2_insts_th
QED

Theorem runtime_bb0_succs_shape[local]:
  ^(concl runtime_bb0_succs_th)
Proof
  ACCEPT_TAC runtime_bb0_succs_th
QED

Theorem runtime_bb1_succs_shape[local]:
  ^(concl runtime_bb1_succs_th)
Proof
  ACCEPT_TAC runtime_bb1_succs_th
QED

Theorem runtime_bb2_succs_shape[local]:
  ^(concl runtime_bb2_succs_th)
Proof
  ACCEPT_TAC runtime_bb2_succs_th
QED

Theorem runtime_data_segment_shape[local]:
  ^(concl runtime_data_segment_th)
Proof
  ACCEPT_TAC runtime_data_segment_th
QED

Theorem runtime_bb0_snoc_shape[local]:
  ^runtime_bb0_tm =
    <| bb_label := (^runtime_bb0_tm).bb_label;
       bb_instructions := FRONT ((^runtime_bb0_tm).bb_instructions) ++
                          [LAST ((^runtime_bb0_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED

Theorem runtime_bb1_snoc_shape[local]:
  ^runtime_bb1_tm =
    <| bb_label := (^runtime_bb1_tm).bb_label;
       bb_instructions := FRONT ((^runtime_bb1_tm).bb_instructions) ++
                          [LAST ((^runtime_bb1_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED

Theorem runtime_bb2_snoc_shape[local]:
  ^runtime_bb2_tm =
    <| bb_label := (^runtime_bb2_tm).bb_label;
       bb_instructions := FRONT ((^runtime_bb2_tm).bb_instructions) ++
                          [LAST ((^runtime_bb2_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED

Theorem runtime_bb0_well_formed[local]:
  bb_well_formed ^runtime_bb0_tm
Proof
  once_rewrite_tac[runtime_bb0_snoc_shape] >>
  irule runtime_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem runtime_bb1_well_formed[local]:
  bb_well_formed ^runtime_bb1_tm
Proof
  once_rewrite_tac[runtime_bb1_snoc_shape] >>
  irule runtime_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem runtime_bb2_well_formed[local]:
  bb_well_formed ^runtime_bb2_tm
Proof
  once_rewrite_tac[runtime_bb2_snoc_shape] >>
  irule runtime_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem runtime_bb0_instructions_wf[local]:
  EVERY inst_wf (^runtime_bb0_tm).bb_instructions
Proof
  EVAL_TAC >> simp[]
QED

Theorem runtime_bb1_instructions_wf[local]:
  EVERY inst_wf (^runtime_bb1_tm).bb_instructions
Proof
  simp[venomWfTheory.inst_wf_def]
QED

Theorem runtime_bb2_instructions_wf[local]:
  EVERY inst_wf (^runtime_bb2_tm).bb_instructions
Proof
  EVAL_TAC >> simp[]
QED

Theorem runtime_function_well_formed[local]:
  wf_function ^runtime_fn_tm
Proof
  simp[venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def,
       venomWfTheory.fn_succs_closed_def,
       venomWfTheory.fn_inst_ids_distinct_def,
       venomInstTheory.fn_labels_def,
       runtime_bb0_well_formed,
       runtime_bb1_well_formed,
       runtime_bb2_well_formed,
       runtime_bb0_succs_shape,
       runtime_bb1_succs_shape,
       runtime_bb2_succs_shape] >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[runtime_bb0_well_formed,
          runtime_bb1_well_formed,
          runtime_bb2_well_formed])
  >> rpt strip_tac >>
  gvs[runtime_bb0_succs_shape,
      runtime_bb1_succs_shape,
      runtime_bb2_succs_shape]
QED

Theorem runtime_function_instructions_wf[local]:
  fn_inst_wf ^runtime_fn_tm
Proof
  irule runtime_fn_inst_wf_from_blocks >>
  simp[] >> rpt strip_tac >>
  gvs[runtime_bb0_instructions_wf,
      runtime_bb1_instructions_wf,
      runtime_bb2_instructions_wf]
QED

Theorem runtime_context_functions_wf[local]:
  !fn. MEM fn (^runtime_input_unit_tm).cu_context.ctx_functions ==>
        wf_function fn /\ fn_inst_wf fn
Proof
  simp[runtime_functions_shape,
       runtime_function_well_formed,
       runtime_function_instructions_wf]
QED


Theorem runtime_context_wf[local]:
  ctx_wf (^runtime_input_unit_tm).cu_context
Proof
  simp[venomWfTheory.ctx_wf_def,
       venomWfTheory.ctx_distinct_fn_names_def,
       venomWfTheory.ctx_has_entry_def,
       venomInstTheory.ctx_fn_names_def,
       runtime_functions_shape]
QED

Theorem runtime_invoke_targets_wf[local]:
  wf_invoke_targets (^runtime_input_unit_tm).cu_context
Proof
  rw[venomWfTheory.wf_invoke_targets_def] >> rpt strip_tac >>
  gvs[runtime_functions_shape,
      venomInstTheory.fn_insts_def,
      venomInstTheory.fn_insts_blocks_def,
      runtime_blocks_shape,
      runtime_bb0_instructions_shape,
      runtime_bb1_instructions_shape,
      runtime_bb2_instructions_shape]
QED

Theorem runtime_context_inst_ids_distinct[local]:
  ctx_inst_ids_distinct (^runtime_input_unit_tm).cu_context
Proof
  simp[venomWfTheory.ctx_inst_ids_distinct_def,
       runtime_functions_shape,
       runtime_blocks_shape,
       runtime_bb0_instructions_shape,
       runtime_bb1_instructions_shape,
       runtime_bb2_instructions_shape]
QED

Theorem runtime_unit_labels_wf[local]:
  unit_labels_wf ^runtime_input_unit_tm
Proof
  simp[venomCompilerWfTheory.unit_labels_wf_def,
       venomCompilerWfTheory.unit_label_namespace_def,
       venomCompilerWfTheory.unit_data_labels_consistent_def,
       venomCompilerWfTheory.unit_data_label_refs_def,
       venomInstTheory.fn_labels_def,
       runtime_functions_shape,
       runtime_blocks_shape,
       runtime_data_segment_shape]
QED

Theorem exact_empty_runtime_input_unit_wf:
  unit_wf ^runtime_input_unit_tm
Proof
  irule runtime_unit_wf_intro >>
  simp[runtime_context_wf,
       runtime_invoke_targets_wf,
       runtime_context_inst_ids_distinct,
       runtime_context_functions_wf,
       runtime_unit_labels_wf]
QED

val _ =
  if aconv (concl exact_empty_runtime_input_unit_wf)
       ``unit_wf ^runtime_input_unit_tm``
  then ()
  else raise Fail "exact runtime unit_wf guard has unexpected conclusion"

Theorem exact_empty_runtime_raw_static_inputs_wf:
  raw_static_inputs_wf (^runtime_input_unit_tm).cu_context
Proof
  simp[staticLayoutWfTheory.raw_static_inputs_wf_def,
       staticLayoutDefsTheory.reserved_intervals_wf_def,
       staticLayoutWfTheory.forced_positions_wf_def,
       runtime_context_inst_ids_distinct,
       runtime_functions_shape]
QED

val _ =
  if aconv (concl exact_empty_runtime_raw_static_inputs_wf)
       ``raw_static_inputs_wf (^runtime_input_unit_tm).cu_context``
  then ()
  else raise Fail "exact runtime raw-static guard has unexpected conclusion"

val runtime_spec_wf_th = eval_closed "runtime pipeline specification guard"
  ``pipeline_spec_wf ^runtime_rpolicy_tm o1_pipeline_spec``
val _ =
  if aconv (rhs (concl runtime_spec_wf_th)) ``T`` then ()
  else raise Fail "runtime pipeline specification is not well formed"

Theorem exact_empty_runtime_pipeline_spec_wf[local]:
  ^(concl runtime_spec_wf_th)
Proof
  ACCEPT_TAC runtime_spec_wf_th
QED

val runtime_outer_pre_walk_tm = find_head ``run_pipeline_stages``
  (rhs (concl runtime_driver_one))
val (_, runtime_outer_pre_walk_args) = strip_comb runtime_outer_pre_walk_tm
val runtime_initial_supply_tm = List.nth (runtime_outer_pre_walk_args, 3)
val runtime_initial_supply_th =
  eval_closed "runtime initial IR supply" runtime_initial_supply_tm
val (_, exact_pre_walk_args) = strip_comb pre_runner_tm
val exact_pre_walk_supply_tm = List.nth (exact_pre_walk_args, 3)
val _ =
  if aconv (rhs (concl runtime_initial_supply_th)) exact_pre_walk_supply_tm then ()
  else raise Fail "evaluated runtime initial supply does not match pre-walk boundary"

Theorem exact_empty_runtime_initial_supply[local]:
  ^(concl runtime_initial_supply_th)
Proof
  ACCEPT_TAC runtime_initial_supply_th
QED

val runtime_outer_pre_walk_shape =
  SIMP_CONV (srw_ss ())
    [venomPassScheduleTheory.o1_pipeline_spec_exact,
     exact_empty_runtime_initial_supply]
    runtime_outer_pre_walk_tm
val _ =
  if aconv (rhs (concl runtime_outer_pre_walk_shape)) pre_runner_tm then ()
  else raise Fail "normalized runtime pre-walk runner does not match exact boundary LHS"
val runtime_driver_normalized =
  CONV_RULE
    (RAND_CONV
      (ONCE_DEPTH_CONV (REWR_CONV runtime_outer_pre_walk_shape)))
    runtime_driver_one
val runtime_after_pre_walk =
  CONV_RULE
    (RAND_CONV
      (ONCE_DEPTH_CONV
        (REWR_CONV
          evalCompilerBytecodeSimplifyCfgResultTheory.exact_empty_runtime_pre_walk_result)))
    runtime_driver_normalized
val runtime_after_graph =
  SIMP_RULE (boss_ss ())
    [exact_empty_runtime_pipeline_spec_wf,
     exact_empty_runtime_input_unit_wf,
     exact_empty_runtime_raw_static_inputs_wf,
     exact_empty_runtime_frozen_fcg,
     exact_o1_prune_unreachable_flag,
     exact_empty_runtime_prune_walk_unit,
     exact_empty_runtime_reachable_fcg_acyclic,
     exact_empty_runtime_pre_walk_entry,
     exact_empty_runtime_fcg_postorder]
    runtime_after_pre_walk

val _ =
  if aconv (lhs (concl runtime_after_graph)) runtime_driver_tm then ()
  else raise Fail "callee-first boundary changed the runtime driver LHS"
val closed_callee_first_tm = find_head ``run_callee_first``
  (rhs (concl runtime_after_graph))
val _ =
  if null (free_vars closed_callee_first_tm) then ()
  else raise Fail
    ("runtime driver callee-first boundary is not closed: " ^
     term_to_string closed_callee_first_tm ^ " ; full RHS: " ^
     term_to_string (rhs (concl runtime_after_graph)))
val pre_walk_call_tm =
  lhs (concl
    evalCompilerBytecodeSimplifyCfgResultTheory.exact_empty_runtime_pre_walk_result)
val _ =
  if can (find_term (aconv pre_walk_call_tm))
      (rhs (concl runtime_after_graph))
  then raise Fail "runtime driver still contains the exact pre-walk stage call"
  else ()

Theorem exact_empty_runtime_driver_to_callee_first:
  ^(concl runtime_after_graph)
Proof
  ACCEPT_TAC runtime_after_graph
QED
val _ = export_theory()
