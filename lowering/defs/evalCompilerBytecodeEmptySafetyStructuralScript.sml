Theory evalCompilerBytecodeEmptySafetyStructural
Ancestors evalCompilerBytecodeEmptyResult
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

Theorem final_bb_well_formed_snoc[local]:
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

Theorem final_fn_inst_wf_from_blocks[local]:
  (!bb. MEM bb fn.fn_blocks ==>
        EVERY inst_wf bb.bb_instructions) ==>
  fn_inst_wf fn
Proof
  rw[venomWfTheory.fn_inst_wf_def] >>
  first_x_assum drule >>
  simp[listTheory.EVERY_MEM]
QED

Theorem final_unit_wf_intro[local]:
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

fun block_shape block =
  ``^block = <| bb_label := (^block).bb_label;
                bb_instructions := FRONT ((^block).bb_instructions) ++
                                   [LAST ((^block).bb_instructions)] |>``

Theorem empty_runtime_final_block0_snoc[local]:
  ^(block_shape ``empty_runtime_final_block0``)
Proof
  EVAL_TAC
QED
Theorem empty_runtime_final_block1_snoc[local]:
  ^(block_shape ``empty_runtime_final_block1``)
Proof
  EVAL_TAC
QED
Theorem empty_runtime_final_block2_snoc[local]:
  ^(block_shape ``empty_runtime_final_block2``)
Proof
  EVAL_TAC
QED
Theorem empty_runtime_final_block3_snoc[local]:
  ^(block_shape ``empty_runtime_final_block3``)
Proof
  EVAL_TAC
QED

Theorem empty_runtime_final_block0_wf:
  bb_well_formed empty_runtime_final_block0
Proof
  once_rewrite_tac[empty_runtime_final_block0_snoc] >>
  irule final_bb_well_formed_snoc >> EVAL_TAC
QED
Theorem empty_runtime_final_block1_wf:
  bb_well_formed empty_runtime_final_block1
Proof
  once_rewrite_tac[empty_runtime_final_block1_snoc] >>
  irule final_bb_well_formed_snoc >> EVAL_TAC
QED
Theorem empty_runtime_final_block2_wf:
  bb_well_formed empty_runtime_final_block2
Proof
  once_rewrite_tac[empty_runtime_final_block2_snoc] >>
  irule final_bb_well_formed_snoc >> EVAL_TAC
QED
Theorem empty_runtime_final_block3_wf:
  bb_well_formed empty_runtime_final_block3
Proof
  once_rewrite_tac[empty_runtime_final_block3_snoc] >>
  irule final_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem eta_exists_eq_string[local]:
  !label : string. $? ($= label)
Proof
  gen_tac >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >>
  simp[]
QED

Theorem empty_runtime_final_block0_insts_wf[local]:
  EVERY inst_wf empty_runtime_final_block0.bb_instructions
Proof
  EVAL_TAC >> simp[]
QED
Theorem empty_runtime_final_block1_insts_wf[local]:
  EVERY inst_wf empty_runtime_final_block1.bb_instructions
Proof
  EVAL_TAC >> simp[venomWfTheory.inst_wf_def, eta_exists_eq_string]
QED
Theorem empty_runtime_final_block2_insts_wf[local]:
  EVERY inst_wf empty_runtime_final_block2.bb_instructions
Proof
  EVAL_TAC >> simp[]
QED
Theorem empty_runtime_final_block3_insts_wf[local]:
  EVERY inst_wf empty_runtime_final_block3.bb_instructions
Proof
  EVAL_TAC >> simp[eta_exists_eq_string]
QED

val block0_label = computeLib.EVAL_CONV ``empty_runtime_final_block0.bb_label``
val block1_label = computeLib.EVAL_CONV ``empty_runtime_final_block1.bb_label``
val block2_label = computeLib.EVAL_CONV ``empty_runtime_final_block2.bb_label``
val block3_label = computeLib.EVAL_CONV ``empty_runtime_final_block3.bb_label``
val block0_succs = computeLib.EVAL_CONV ``bb_succs empty_runtime_final_block0``
val block1_succs = computeLib.EVAL_CONV ``bb_succs empty_runtime_final_block1``
val block2_succs = computeLib.EVAL_CONV ``bb_succs empty_runtime_final_block2``
val block3_succs = computeLib.EVAL_CONV ``bb_succs empty_runtime_final_block3``
val final_fn_name = computeLib.EVAL_CONV ``empty_runtime_final_fn.fn_name``
Theorem empty_runtime_final_fn_wf:
  wf_function empty_runtime_final_fn
Proof
  simp[venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def,
       venomWfTheory.fn_succs_closed_def,
       venomWfTheory.fn_inst_ids_distinct_def,
       venomInstTheory.fn_labels_def,
       empty_runtime_final_blocks_exact,
       empty_runtime_final_block0_wf,
       empty_runtime_final_block1_wf,
       empty_runtime_final_block2_wf,
       empty_runtime_final_block3_wf,
       block0_label, block1_label, block2_label, block3_label,
       block0_succs, block1_succs, block2_succs, block3_succs] >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[empty_runtime_final_block0_wf,
          empty_runtime_final_block1_wf,
          empty_runtime_final_block2_wf,
          empty_runtime_final_block3_wf])
  >> rpt strip_tac >>
  gvs[block0_succs, block1_succs, block2_succs, block3_succs,
      empty_runtime_final_block0_instructions_exact,
      empty_runtime_final_block1_instructions_exact,
      empty_runtime_final_block2_instructions_exact,
      empty_runtime_final_block3_instructions_exact]
QED

Theorem empty_runtime_final_fn_inst_wf:
  fn_inst_wf empty_runtime_final_fn
Proof
  irule final_fn_inst_wf_from_blocks >>
  simp[empty_runtime_final_blocks_exact] >> rpt strip_tac >>
  gvs[empty_runtime_final_block0_insts_wf,
      empty_runtime_final_block1_insts_wf,
      empty_runtime_final_block2_insts_wf,
      empty_runtime_final_block3_insts_wf]
QED

Theorem empty_runtime_final_context_wf[local]:
  ctx_wf empty_runtime_final_unit.cu_context
Proof
  simp[venomWfTheory.ctx_wf_def,
       venomWfTheory.ctx_distinct_fn_names_def,
       venomWfTheory.ctx_has_entry_def,
       venomInstTheory.ctx_fn_names_def,
       empty_runtime_final_functions_exact,
       empty_runtime_final_context_entry_exact,
       final_fn_name]
QED

Theorem empty_runtime_final_invoke_targets_wf[local]:
  wf_invoke_targets empty_runtime_final_unit.cu_context
Proof
  rw[venomWfTheory.wf_invoke_targets_def] >> rpt strip_tac >>
  gvs[empty_runtime_final_functions_exact,
      venomInstTheory.fn_insts_def,
      venomInstTheory.fn_insts_blocks_def,
      empty_runtime_final_blocks_exact,
      empty_runtime_final_block0_instructions_exact,
      empty_runtime_final_block1_instructions_exact,
      empty_runtime_final_block2_instructions_exact,
      empty_runtime_final_block3_instructions_exact]
QED

Theorem empty_runtime_final_inst_ids_distinct[local]:
  ctx_inst_ids_distinct empty_runtime_final_unit.cu_context
Proof
  simp[venomWfTheory.ctx_inst_ids_distinct_def,
       empty_runtime_final_functions_exact,
       empty_runtime_final_blocks_exact,
       empty_runtime_final_block0_instructions_exact,
       empty_runtime_final_block1_instructions_exact,
       empty_runtime_final_block2_instructions_exact,
       empty_runtime_final_block3_instructions_exact]
QED

Theorem empty_runtime_final_labels_wf:
  unit_labels_wf empty_runtime_final_unit
Proof
  simp[venomCompilerWfTheory.unit_labels_wf_def,
       venomCompilerWfTheory.unit_label_namespace_def,
       venomCompilerWfTheory.unit_data_labels_consistent_def,
       venomCompilerWfTheory.unit_data_label_refs_def,
       venomInstTheory.fn_labels_def,
       empty_runtime_final_functions_exact,
       empty_runtime_final_blocks_exact,
       empty_runtime_final_data_segment_exact,
       block0_label, block1_label, block2_label, block3_label]
QED

Theorem empty_runtime_final_unit_wf:
  unit_wf empty_runtime_final_unit
Proof
  irule final_unit_wf_intro >>
  simp[empty_runtime_final_context_wf,
       empty_runtime_final_invoke_targets_wf,
       empty_runtime_final_inst_ids_distinct,
       empty_runtime_final_functions_exact,
       empty_runtime_final_fn_wf,
       empty_runtime_final_fn_inst_wf,
       empty_runtime_final_labels_wf]
QED

val _ = export_theory()
