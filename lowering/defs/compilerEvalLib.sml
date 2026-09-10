structure compilerEvalLib :> compilerEvalLib = struct

open HolKernel
open asmIRTheory planExecTheory symbolResolveTheory

(* This layer contains context-plan orchestration plus the mechanical tail

     supplied/empty context plan -> stack_op list -> asm_inst list -> byte list.

   It does not yet compute a plan for a nonempty function. Keep the datatype
   and theorem inventories explicit: residual constants in
   test results should lead to a deliberate addition here rather than copying
   computeLib's global compset. *)
(* TODO: Replace the parser quotations below with terms constructed through
   the corresponding syntax libraries. Library behavior should not depend on
   the ambient parser grammar. *)
val final_codegen_types =
  [``:venomState$operand``, ``:asmIR$asm_inst``, ``:asmIR$stack_op``,
   ``:venomInst$data_item``, ``:venomInst$data_section``,
   ``:venomInst$opcode``, ``:venomInst$instruction``,
   ``:venomInst$basic_block``,
   ``:venomInst$internal_call_abi``, ``:venomInst$fmp_signature``,
   ``:venomInst$ir_function``, ``:venomInst$venom_context``,
   ``:stackPlanTypes$spill_alloc``, ``:stackPlanTypes$plan_state``,
   ``:stackPlanTypes$spill_region``, ``:stackPlanTypes$context_plan``,
   ``:stackPlanTypes$context_plan_acc``,
   ``:cfgDefs$cfg_analysis``, ``:dfgDefs$dfg_analysis``,
   ``:'a dfAnalyzeDefs$df_state``,
   ``:dfAnalyzeDefs$direction``,
   ``:venomPolicyTypes$evm_capability``,
   ``:venomCompilerTypes$resolved_compiler_policy``,
   ``:venomCompilerTypes$compilation_unit``,
   ``:'a list``, ``:'a option``, ``:'a # 'b``]

val final_codegen_defs =
  [alistTheory.fmap_to_alist_FEMPTY,
   encode_num_bytes_def,
   data_section_asm_def, data_segment_asm_def,
   swap_name_def, dup_name_def, exec_stack_op_def, execute_plan_def,
   asmIRTheory.venom_to_evm_name_def,
   venomStateTheory.get_label_def,
   stackPlanGenTheory.revert_postamble_def,
   stackPlanGenTheory.context_plan_ops_def,
   venomInstTheory.mk_inst_def,
   venomInstTheory.default_internal_call_abi_def,
   venomInstTheory.mk_raw_function_def,
   venomInstTheory.is_param_opcode_def,
   venomInstTheory.entry_block_def,
   venomInstTheory.fn_entry_label_def,
   venomInstTheory.get_successors_def,
   venomInstTheory.operand_var_def,
   venomInstTheory.operand_vars_def,
   venomInstTheory.inst_uses_def,
   venomInstTheory.inst_defs_def,
   venomInstTheory.bb_succs_def,
   venomInstTheory.lookup_block_def,
   venomInstTheory.fn_insts_blocks_def,
   venomInstTheory.fn_insts_def,
   venomInstTheory.is_terminator_def,
   venomInstTheory.is_raw_fmp_opcode_def,
   venomEffectsTheory.is_commutative_def,
   cfgTransformTheory.is_halting_opcode_def,
   cfgTransformTheory.bb_is_halting_def,
   asmIRTheory.get_non_label_operands_def,
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
   stackPlanTypesTheory.free_spill_slot_def,
   stackPlanTypesTheory.is_var_operand_def,
   stackModelTheory.stack_push_def,
   stackModelTheory.stack_pop_def,
   stackModelTheory.stack_peek_def,
   stackModelTheory.stack_poke_def,
   stackModelTheory.stack_swap_def,
   stackModelTheory.stack_dup_def,
   stackModelTheory.stack_find_def,
   stackModelTheory.stack_get_depth_def,
   stackModelTheory.stack_get_unfixed_depth_def,
   stackPlanOpsTheory.do_spill_tos_def,
   stackPlanOpsTheory.do_spill_at_def,
   stackPlanOpsTheory.do_restore_def,
   stackPlanOpsTheory.top_n_def,
   stackPlanOpsTheory.do_swap_def,
   stackPlanOpsTheory.do_dup_def,
   stackPlanOpsTheory.select_spill_candidate_def,
   stackPlanOpsTheory.reduce_depth_plan_def,
   stackPlanOpsTheory.reorder_one_def,
   stackPlanOpsTheory.reorder_plan_def,
   stackPlanOpsTheory.reorder_cost_def,
   stackPlanOpsTheory.popmany_plan_def,
   stackPlanOpsTheory.release_dead_spills_def,
   dfHelperDefsTheory.list_union_def,
   dfAnalyzeDefsTheory.df_at_def,
   dfAnalyzeDefsTheory.df_boundary_def,
   dfAnalyzeDefsTheory.df_fold_forward_def,
   dfAnalyzeDefsTheory.df_fold_backward_def,
   dfAnalyzeDefsTheory.df_fold_block_def,
   dfAnalyzeDefsTheory.df_joined_val_def,
   dfAnalyzeDefsTheory.df_process_block_def,
   dfAnalyzeDefsTheory.init_df_state_def,
   dfAnalyzeDefsTheory.df_populate_inst_def,
   dfAnalyzeDefsTheory.df_analyze_fuel_def,
   livenessDefsTheory.live_update_def,
   livenessDefsTheory.liveness_transfer_def,
   livenessDefsTheory.collect_phis_def,
   livenessDefsTheory.build_phi_maps_def,
   livenessDefsTheory.input_vars_from_def,
   livenessDefsTheory.liveness_edge_transfer_def,
   livenessDefsTheory.liveness_analyze_fuel_def,
   livenessDefsTheory.live_vars_at_def,
   dfgDefsTheory.dfg_empty_def,
   dfgDefsTheory.operand_var_def,
   dfgDefsTheory.operand_vars_def,
   dfgDefsTheory.dfg_add_use_def,
   dfgDefsTheory.dfg_add_uses_def,
   dfgDefsTheory.dfg_add_defs_def,
   dfgDefsTheory.dfg_set_inst_by_id_def,
   dfgDefsTheory.dfg_add_inst_def,
   dfgDefsTheory.dfg_build_insts_rev_def,
   dfgDefsTheory.dfg_build_insts_def,
   dfgDefsTheory.dfg_build_function_def,
   dfgDefsTheory.normalize_operand_def,
   dfgDefsTheory.operand_equiv_def,
   cfgDefsTheory.set_insert_def,
   cfgDefsTheory.fmap_lookup_list_def,
   cfgDefsTheory.cfg_succs_of_def,
   cfgDefsTheory.cfg_preds_of_def,
   cfgDefsTheory.init_succs_def,
   cfgDefsTheory.init_preds_def,
   cfgDefsTheory.build_succs_def,
   cfgDefsTheory.build_preds_def,
   cfgDefsTheory.dfs_post_walk_def,
   cfgDefsTheory.dfs_pre_walk_def,
   cfgDefsTheory.build_reachable_def,
   cfgDefsTheory.cfg_analyze_def,
   listTheory.nub_def,
   listTheory.REV_DEF,
   indexedListsTheory.MAPi_def,
   stackPlanGenTheory.emit_one_input_def,
   stackPlanGenTheory.emit_input_plan_def,
   stackPlanGenTheory.optimistic_swap_plan_def,
   stackPlanGenTheory.generate_phi_plan_def,
   stackPlanGenTheory.generate_offset_plan_def,
   stackPlanGenTheory.bump_round_word_def,
   stackPlanGenTheory.bump_emit_ops_def,
   stackPlanGenTheory.generate_emit_ops_def,
   stackPlanGenTheory.compute_operands_def,
   stackPlanGenTheory.generate_regular_inst_plan_def,
   stackPlanGenTheory.is_unlowered_fmp_opcode_def,
   stackPlanGenTheory.is_unlowered_internal_call_opcode_def,
   stackPlanGenTheory.is_pre_codegen_opcode_def,
   stackPlanGenTheory.generate_inst_plan_def,
   stackPlanGenTheory.get_params_def,
   stackPlanGenTheory.prepare_params_plan_def,
   stackPlanGenTheory.clean_stack_plan_def,
   stackPlanGenTheory.non_param_insts_def,
   stackPlanGenTheory.generate_block_plan_def,
   stackPlanGenTheory.generate_fn_plan_aux_fuel_def,
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

(* Numeral fuel did not match wl_iterate_fuel's SUC-pattern equations in this
   custom compset. Keep this workaround local and revisit whether standard
   computation rules can make it unnecessary. *)
val small_fuel_suc_thms =
  List.tabulate (32, fn n =>
    reduceLib.SUC_CONV
      (mk_comb (``SUC``, numSyntax.mk_numeral (Arbnum.fromInt n)))
    |> SYM)

fun build_final_codegen_compset () =
  reduceLib.num_compset
  |> computeLib.copy
  |> listSimps.list_rws
  |> pairLib.add_pair_compset
  |> combinLib.add_combin_compset
  |> pred_setLib.add_pred_set_compset
  |> optionLib.OPTION_rws
  |> stringLib.add_string_compset
  |> wordsLib.add_words_compset false
  |> finite_mapLib.add_finite_map_compset
  |> alistLib.add_alist_compset
  |> computeLib.add_conv (``REPLICATE``, 2, listLib.REPLICATE_CONV)
  |> computeLib.add_conv
       (``wl_iterate_fuel``, 6,
        Rewrite.REWRITE_CONV
          (small_fuel_suc_thms @
           [worklistDefsTheory.wl_iterate_fuel_def,
            worklistDefsTheory.wl_step_def]))
  |> computeLib.add_conv
       (``generate_fn_plan_aux_fuel``, 8,
        Rewrite.REWRITE_CONV
          (small_fuel_suc_thms @
           [stackPlanGenTheory.generate_fn_plan_aux_fuel_def]))
  |> computeLib.add_conv
       (``generate_succs_plan_fuel``, 10,
        Rewrite.REWRITE_CONV
          (small_fuel_suc_thms @
           [stackPlanGenTheory.generate_fn_plan_aux_fuel_def]))
  |> computeLib.extend_compset [computeLib.Tys final_codegen_types]
  |> computeLib.add_thms final_codegen_defs

val final_codegen_compset =
  build_final_codegen_compset () |> computeLib.seal

val final_codegen_conv = computeLib.CBV_CONV final_codegen_compset

end
