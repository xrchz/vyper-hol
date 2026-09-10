structure compilerEvalLib :> compilerEvalLib = struct

open HolKernel
open asmIRTheory planExecTheory symbolResolveTheory

(* This layer contains context-plan orchestration plus the mechanical tail

     supplied/empty context plan -> stack_op list -> asm_inst list -> byte list.

   It does not yet compute a plan for a nonempty function. Keep the datatype
   and theorem inventories explicit: residual constants in
   test results should lead to a deliberate addition here rather than copying
   computeLib's global compset. *)
val final_codegen_types =
  [``:venomState$operand``, ``:asmIR$asm_inst``, ``:asmIR$stack_op``,
   ``:venomInst$data_item``, ``:venomInst$data_section``,
   ``:venomInst$instruction``, ``:venomInst$basic_block``,
   ``:venomInst$internal_call_abi``, ``:venomInst$fmp_signature``,
   ``:venomInst$ir_function``, ``:venomInst$venom_context``,
   ``:stackPlanTypes$spill_region``, ``:stackPlanTypes$context_plan``,
   ``:stackPlanTypes$context_plan_acc``,
   ``:venomPolicyTypes$evm_capability``,
   ``:venomCompilerTypes$resolved_compiler_policy``,
   ``:venomCompilerTypes$compilation_unit``,
   ``:'a list``, ``:'a option``, ``:'a # 'b``]

val final_codegen_defs =
  [encode_num_bytes_def,
   data_section_asm_def, data_segment_asm_def,
   swap_name_def, dup_name_def, exec_stack_op_def, execute_plan_def,
   stackPlanGenTheory.revert_postamble_def,
   stackPlanGenTheory.context_plan_ops_def,
   venomInstTheory.mk_inst_def,
   venomInstTheory.default_internal_call_abi_def,
   venomInstTheory.mk_raw_function_def,
   venomInstTheory.is_param_opcode_def,
   venomInstTheory.entry_block_def,
   venomInstTheory.fn_entry_label_def,
   callLayoutDefsTheory.param_inst_at_def,
   callLayoutDefsTheory.no_param_insts_def,
   callLayoutDefsTheory.canonical_after_fmp_def,
   callLayoutDefsTheory.canonical_entry_params_from_def,
   callLayoutDefsTheory.canonical_param_prefix_def,
   venomInstTheory.mk_venom_context_def,
   venomLayoutTheory.ceil32_def,
   staticLayoutDefsTheory.reserved_intervals_wf_def,
   staticLayoutDefsTheory.global_reserved_end_def,
   stackPlanGenTheory.collect_fn_eoms_def,
   stackPlanGenTheory.max_live_eom_def,
   stackPlanGenTheory.generate_context_regions_def,
   stackPlanGenTheory.finish_context_plan_def,
   stackPlanGenTheory.generate_context_plan_with_def,
   stackPlanTypesTheory.init_spill_alloc_def,
   stackPlanTypesTheory.init_plan_state_def,
   stackPlanTypesTheory.stack_op_in_spill_region_def,
   stackPlanTypesTheory.spill_plan_in_region_def,
   stackPlanGenTheory.generate_fn_plan_fuel_def,
   stackPlanGenTheory.generate_context_plan_fuel_def,
   venomPolicyTypesTheory.target_capabilities_wf_def,
   venomPolicyTypesTheory.prague_capabilities_def,
   venomTargetSafetyTheory.opcode_target_supported_def,
   venomTargetSafetyTheory.instruction_target_safe_def,
   venomTargetSafetyTheory.basic_block_target_safe_def,
   venomTargetSafetyTheory.function_target_safe_def,
   venomTargetSafetyTheory.context_target_safe_def,
   asmTargetSafetyTheory.asm_opcode_target_supported_def,
   asmTargetSafetyTheory.asm_inst_target_safe_def,
   asmTargetSafetyTheory.assembly_target_safe_def,
   codegenTheory.codegen_assembly_fuel_def,
   evm_opcode_table_def, evm_opcode_byte_def, symbol_size_def, pad_bytes_def,
   asm_inst_size_def, compute_label_offsets_def, encode_inst_def, assemble_def]

fun build_final_codegen_compset () =
  reduceLib.num_compset
  |> computeLib.copy
  |> listSimps.list_rws
  |> pairLib.add_pair_compset
  |> combinLib.add_combin_compset
  |> optionLib.OPTION_rws
  |> stringLib.add_string_compset
  |> wordsLib.add_words_compset false
  |> finite_mapLib.add_finite_map_compset
  |> alistLib.add_alist_compset
  |> computeLib.add_conv (``REPLICATE``, 2, listLib.REPLICATE_CONV)
  |> computeLib.extend_compset [computeLib.Tys final_codegen_types]
  |> computeLib.add_thms final_codegen_defs

val final_codegen_compset =
  build_final_codegen_compset () |> computeLib.seal

val final_codegen_conv = computeLib.CBV_CONV final_codegen_compset

end
