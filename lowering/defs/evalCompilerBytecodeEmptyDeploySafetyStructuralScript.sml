Theory evalCompilerBytecodeEmptyDeploySafetyStructural
Ancestors evalCompilerBytecodeEmptyDeployStandaloneWalk
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val functions_th = computeLib.EVAL_CONV
  ``empty_deploy_final_compilation_unit.cu_context.ctx_functions``
val functions = fst (listSyntax.dest_list (rhs (concl functions_th)))
val _ = if length functions = 1 then ()
  else raise Fail "exact final deploy unit is not singleton-function"
val final_fn_tm = hd functions
val _ = assert_closed "exact final deploy function" final_fn_tm

Definition empty_deploy_final_fn_def:
  empty_deploy_final_fn = ^final_fn_tm
End

val functions_named =
  REWRITE_RULE [GSYM empty_deploy_final_fn_def] functions_th

Theorem empty_deploy_final_functions_exact:
  ^(concl functions_named)
Proof
  ACCEPT_TAC functions_named
QED

val blocks_th = computeLib.EVAL_CONV ``empty_deploy_final_fn.fn_blocks``
val blocks = fst (listSyntax.dest_list (rhs (concl blocks_th)))
val _ = if length blocks = 1 then ()
  else raise Fail "exact final deploy function is not singleton-block"
val block_tm = hd blocks
val _ = assert_closed "exact final deploy block" block_tm

Definition empty_deploy_final_block_def:
  empty_deploy_final_block = ^block_tm
End

val blocks_named = REWRITE_RULE [GSYM empty_deploy_final_block_def] blocks_th

Theorem empty_deploy_final_blocks_exact:
  ^(concl blocks_named)
Proof
  ACCEPT_TAC blocks_named
QED

fun eval_projection tm = computeLib.EVAL_CONV tm
val block_insts = eval_projection ``empty_deploy_final_block.bb_instructions``
val data_segment = eval_projection
  ``empty_deploy_final_compilation_unit.cu_data_segment``
val context_entry = eval_projection
  ``empty_deploy_final_compilation_unit.cu_context.ctx_entry``
val global_reserved = eval_projection
  ``empty_deploy_final_compilation_unit.cu_context.ctx_global_reserved``
val final_call_abi = eval_projection ``empty_deploy_final_fn.fn_call_abi``
val final_forced_positions = eval_projection
  ``empty_deploy_final_fn.fn_forced_alloc_positions``
val final_eom = eval_projection ``empty_deploy_final_fn.fn_eom``
val final_fmp_signature = eval_projection ``empty_deploy_final_fn.fn_fmp_signature``

val _ = List.app (assert_closed "exact final deploy projection" o rhs o concl)
  [block_insts, data_segment, context_entry, global_reserved,
   final_call_abi, final_forced_positions, final_eom, final_fmp_signature]

Theorem empty_deploy_final_block_instructions_exact:
  ^(concl block_insts)
Proof
  ACCEPT_TAC block_insts
QED

Theorem empty_deploy_final_data_segment_exact:
  ^(concl data_segment)
Proof
  ACCEPT_TAC data_segment
QED

Theorem empty_deploy_final_context_entry_exact:
  ^(concl context_entry)
Proof
  ACCEPT_TAC context_entry
QED

Theorem empty_deploy_final_global_reserved_exact:
  ^(concl global_reserved)
Proof
  ACCEPT_TAC global_reserved
QED

Theorem empty_deploy_final_call_abi_exact:
  ^(concl final_call_abi)
Proof
  ACCEPT_TAC final_call_abi
QED

Theorem empty_deploy_final_forced_positions_exact:
  ^(concl final_forced_positions)
Proof
  ACCEPT_TAC final_forced_positions
QED

Theorem empty_deploy_final_eom_exact:
  ^(concl final_eom)
Proof
  ACCEPT_TAC final_eom
QED

Theorem empty_deploy_final_fmp_signature_exact:
  ^(concl final_fmp_signature)
Proof
  ACCEPT_TAC final_fmp_signature
QED

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

Theorem empty_deploy_final_block_snoc[local]:
  empty_deploy_final_block =
    <| bb_label := empty_deploy_final_block.bb_label;
       bb_instructions := FRONT empty_deploy_final_block.bb_instructions ++
                          [LAST empty_deploy_final_block.bb_instructions] |>
Proof
  EVAL_TAC
QED

Theorem empty_deploy_final_block_wf:
  bb_well_formed empty_deploy_final_block
Proof
  once_rewrite_tac[empty_deploy_final_block_snoc] >>
  irule final_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem empty_deploy_final_block_insts_wf:
  EVERY inst_wf empty_deploy_final_block.bb_instructions
Proof
  EVAL_TAC >> simp[venomWfTheory.inst_wf_def]
QED


Theorem deploy_fn_inst_wf_from_blocks[local]:
  (!bb. MEM bb fn.fn_blocks ==>
        EVERY inst_wf bb.bb_instructions) ==>
  fn_inst_wf fn
Proof
  rw[venomWfTheory.fn_inst_wf_def] >>
  first_x_assum drule >>
  simp[listTheory.EVERY_MEM]
QED

val final_block_label = computeLib.EVAL_CONV
  ``empty_deploy_final_block.bb_label``
val final_block_succs = computeLib.EVAL_CONV
  ``bb_succs empty_deploy_final_block``

Theorem empty_deploy_final_fn_wf:
  wf_function empty_deploy_final_fn
Proof
  simp[venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def,
       venomWfTheory.fn_succs_closed_def,
       venomWfTheory.fn_inst_ids_distinct_def,
       venomInstTheory.fn_labels_def,
       empty_deploy_final_blocks_exact,
       empty_deploy_final_block_wf,
       final_block_label, final_block_succs] >>
  gvs[empty_deploy_final_block_instructions_exact]
QED

Theorem empty_deploy_final_fn_inst_wf:
  fn_inst_wf empty_deploy_final_fn
Proof
  irule deploy_fn_inst_wf_from_blocks >>
  simp[empty_deploy_final_blocks_exact] >> rpt strip_tac >>
  gvs[empty_deploy_final_block_insts_wf]
QED

val final_fn_name = computeLib.EVAL_CONV ``empty_deploy_final_fn.fn_name``

Theorem empty_deploy_final_context_wf[local]:
  ctx_wf empty_deploy_final_compilation_unit.cu_context
Proof
  simp[venomWfTheory.ctx_wf_def,
       venomWfTheory.ctx_distinct_fn_names_def,
       venomWfTheory.ctx_has_entry_def,
       venomInstTheory.ctx_fn_names_def,
       empty_deploy_final_functions_exact,
       empty_deploy_final_context_entry_exact,
       final_fn_name]
QED

Theorem empty_deploy_final_invoke_targets_wf[local]:
  wf_invoke_targets empty_deploy_final_compilation_unit.cu_context
Proof
  rw[venomWfTheory.wf_invoke_targets_def] >> rpt strip_tac >>
  gvs[empty_deploy_final_functions_exact,
      venomInstTheory.fn_insts_def,
      venomInstTheory.fn_insts_blocks_def,
      empty_deploy_final_blocks_exact,
      empty_deploy_final_block_instructions_exact]
QED

Theorem empty_deploy_final_inst_ids_distinct[local]:
  ctx_inst_ids_distinct empty_deploy_final_compilation_unit.cu_context
Proof
  simp[venomWfTheory.ctx_inst_ids_distinct_def,
       empty_deploy_final_functions_exact,
       empty_deploy_final_blocks_exact,
       empty_deploy_final_block_instructions_exact]
QED

Theorem empty_deploy_final_labels_wf:
  unit_labels_wf empty_deploy_final_compilation_unit
Proof
  simp[venomCompilerWfTheory.unit_labels_wf_def,
       venomCompilerWfTheory.unit_label_namespace_def,
       venomCompilerWfTheory.unit_data_labels_consistent_def,
       venomCompilerWfTheory.unit_data_label_refs_def,
       venomCompilerWfTheory.data_section_label_refs_def,
       venomCompilerWfTheory.data_item_label_refs_def,
       venomInstTheory.fn_labels_def,
       empty_deploy_final_functions_exact,
       empty_deploy_final_blocks_exact,
       empty_deploy_final_data_segment_exact,
       final_block_label]
QED

Theorem deploy_unit_wf_intro[local]:
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

Theorem empty_deploy_final_unit_wf:
  unit_wf empty_deploy_final_compilation_unit
Proof
  irule deploy_unit_wf_intro >>
  simp[empty_deploy_final_context_wf,
       empty_deploy_final_invoke_targets_wf,
       empty_deploy_final_inst_ids_distinct,
       empty_deploy_final_functions_exact,
       empty_deploy_final_fn_wf,
       empty_deploy_final_fn_inst_wf,
       empty_deploy_final_labels_wf]
QED
val _ = export_theory()
