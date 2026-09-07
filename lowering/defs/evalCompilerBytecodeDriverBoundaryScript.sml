Theory evalCompilerBytecodeDriverBoundary
Ancestors evalCompilerBytecodeWalkPrep
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t

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

val _ = export_theory()
