(*
 * Compiler Bytecode Evaluation Fixtures
 *
 * STATUS: Regression/evaluation support, not core lowering definitions.
 * Compares executable compiler output against bytecode fixture files using
 * EVAL_TAC and evalCompilerBytecodeLib.
 *)

Theory evalCompilerBytecode
Ancestors evalCompilerBytecodeDefs evalCompiler compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["bytecode"]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Definition empty_runtime_entry_raw_fn_def:
  empty_runtime_entry_raw_fn =
    <| fn_name := "__entry";
       fn_blocks :=
         [<| bb_label := "__entry";
             bb_instructions :=
               [mk_inst 0 CALLDATASIZE [] ["%0"];
                mk_inst 1 LT [Var "%0"; Lit 4w] ["%1"];
                mk_inst 2 ISZERO [Var "%1"] ["%2"];
                mk_inst 3 JNZ
                  [Var "%2"; Label "@dispatch_1"; Label "@fallback_0"] []] |>;
          <| bb_label := "@dispatch_1";
             bb_instructions :=
               [mk_inst 4 CALLDATALOAD [Lit 0w] ["%3"];
                mk_inst 5 SHR [Lit 224w; Var "%3"] ["%4"];
                mk_inst 6 JMP [Label "@fallback_0"] []] |>;
          <| bb_label := "@fallback_0";
             bb_instructions := [mk_inst 7 REVERT [Lit 0w; Lit 0w] []] |>];
       fn_call_abi := default_internal_call_abi;
       fn_noinline := F;
       fn_forced_alloc_positions := FEMPTY;
       fn_eom := NONE;
       fn_fmp_signature := NONE |>
End


val empty_runtime_entry_concretized_eval =
  EVAL ``concretize_function_eval [] empty_runtime_entry_raw_fn``
val empty_runtime_entry_concrete_value_eval =
  EVAL ``THE ^(rhs (concl empty_runtime_entry_concretized_eval))``
Definition empty_runtime_entry_fn_def:
  empty_runtime_entry_fn =
    ^(rhs (concl empty_runtime_entry_concrete_value_eval))
End
Theorem empty_runtime_entry_control_eval[local]:
  fn_entry_label empty_runtime_entry_fn = SOME "__entry" /\
  lookup_block "__entry" empty_runtime_entry_fn.fn_blocks =
    SOME (HD empty_runtime_entry_fn.fn_blocks) /\
  lookup_block "@dispatch_1" empty_runtime_entry_fn.fn_blocks =
    SOME (EL 1 empty_runtime_entry_fn.fn_blocks) /\
  lookup_block "@fallback_0" empty_runtime_entry_fn.fn_blocks =
    SOME (EL 2 empty_runtime_entry_fn.fn_blocks)
Proof
  EVAL_TAC
QED

val empty_runtime_entry_block_eval = EVAL ``HD empty_runtime_entry_fn.fn_blocks``
val empty_runtime_dispatch_block_eval = EVAL ``EL 1 empty_runtime_entry_fn.fn_blocks``
val empty_runtime_fallback_block_eval = EVAL ``EL 2 empty_runtime_entry_fn.fn_blocks``
val empty_runtime_live_eval = EVAL ``liveness_analyze empty_runtime_entry_fn``
val empty_runtime_dfg_eval = EVAL ``dfg_build_function empty_runtime_entry_fn``
val empty_runtime_cfg_eval = EVAL ``cfg_analyze empty_runtime_entry_fn``


Definition empty_runtime_entry_block_def:
  empty_runtime_entry_block = ^(rhs (concl empty_runtime_entry_block_eval))
End

Definition empty_runtime_dispatch_block_def:
  empty_runtime_dispatch_block = ^(rhs (concl empty_runtime_dispatch_block_eval))
End

Definition empty_runtime_fallback_block_def:
  empty_runtime_fallback_block = ^(rhs (concl empty_runtime_fallback_block_eval))
End
Definition empty_runtime_entry_live_def:
  empty_runtime_entry_live = ^(rhs (concl empty_runtime_live_eval))
End

Definition empty_runtime_entry_dfg_def:
  empty_runtime_entry_dfg = ^(rhs (concl empty_runtime_dfg_eval))
End

Definition empty_runtime_entry_cfg_def:
  empty_runtime_entry_cfg = ^(rhs (concl empty_runtime_cfg_eval))
End

val empty_runtime_entry_preds_eval =
  EVAL ``cfg_preds_of empty_runtime_entry_cfg "__entry"``
val empty_runtime_dispatch_preds_eval =
  EVAL ``cfg_preds_of empty_runtime_entry_cfg "@dispatch_1"``
val empty_runtime_fallback_preds_eval =
  EVAL ``cfg_preds_of empty_runtime_entry_cfg "@fallback_0"``

Theorem empty_runtime_block_lookup_eval[local]:
  lookup_block "__entry" empty_runtime_entry_fn.fn_blocks =
    SOME empty_runtime_entry_block /\
  lookup_block "@dispatch_1" empty_runtime_entry_fn.fn_blocks =
    SOME empty_runtime_dispatch_block /\
  lookup_block "@fallback_0" empty_runtime_entry_fn.fn_blocks =
    SOME empty_runtime_fallback_block
Proof
  EVAL_TAC
QED

Theorem empty_runtime_entry_live_eval[local]:
  liveness_analyze empty_runtime_entry_fn = empty_runtime_entry_live
Proof
  simp[empty_runtime_entry_live_def, empty_runtime_live_eval]
QED

Theorem empty_runtime_entry_dfg_eval[local]:
  dfg_build_function empty_runtime_entry_fn = empty_runtime_entry_dfg
Proof
  simp[empty_runtime_entry_dfg_def, empty_runtime_dfg_eval]
QED

Theorem empty_runtime_entry_cfg_eval[local]:
  cfg_analyze empty_runtime_entry_fn = empty_runtime_entry_cfg
Proof
  simp[empty_runtime_entry_cfg_def, empty_runtime_cfg_eval]
QED

Theorem empty_runtime_entry_cfg_control_eval[local]:
  cfg_succs_of empty_runtime_entry_cfg "__entry" =
    ["@fallback_0"; "@dispatch_1"] /\
  cfg_succs_of empty_runtime_entry_cfg "@dispatch_1" = ["@fallback_0"] /\
  cfg_succs_of empty_runtime_entry_cfg "@fallback_0" = []
Proof
  EVAL_TAC
QED

Theorem empty_runtime_entry_cfg_preds_eval[local]:
  cfg_preds_of empty_runtime_entry_cfg "__entry" =
    ^(rhs (concl empty_runtime_entry_preds_eval)) /\
  cfg_preds_of empty_runtime_entry_cfg "@dispatch_1" =
    ^(rhs (concl empty_runtime_dispatch_preds_eval)) /\
  cfg_preds_of empty_runtime_entry_cfg "@fallback_0" =
    ^(rhs (concl empty_runtime_fallback_preds_eval))
Proof
  simp[empty_runtime_entry_preds_eval, empty_runtime_dispatch_preds_eval,
       empty_runtime_fallback_preds_eval]
QED


val empty_runtime_entry_block_plan_eval = EVAL
  ``generate_block_plan empty_runtime_entry_live empty_runtime_entry_dfg
      empty_runtime_entry_cfg empty_runtime_entry_fn empty_runtime_entry_block
      (init_plan_state 0)``

Definition empty_runtime_entry_block_plan_result_def:
  empty_runtime_entry_block_plan_result =
    ^(rhs (concl empty_runtime_entry_block_plan_eval))
End

Theorem empty_runtime_entry_block_plan[local]:
  generate_block_plan empty_runtime_entry_live empty_runtime_entry_dfg
    empty_runtime_entry_cfg empty_runtime_entry_fn empty_runtime_entry_block
    (init_plan_state 0) = empty_runtime_entry_block_plan_result
Proof
  simp[empty_runtime_entry_block_plan_result_def,
       empty_runtime_entry_block_plan_eval]
QED

val empty_runtime_after_entry_eval =
  EVAL ``SND (THE empty_runtime_entry_block_plan_result)``
Definition empty_runtime_after_entry_def:
  empty_runtime_after_entry = ^(rhs (concl empty_runtime_after_entry_eval))
End

val empty_runtime_fallback_block_plan_eval = EVAL
  ``generate_block_plan empty_runtime_entry_live empty_runtime_entry_dfg
      empty_runtime_entry_cfg empty_runtime_entry_fn empty_runtime_fallback_block
      empty_runtime_after_entry``
Definition empty_runtime_fallback_block_plan_result_def:
  empty_runtime_fallback_block_plan_result =
    ^(rhs (concl empty_runtime_fallback_block_plan_eval))
End
Theorem empty_runtime_fallback_block_plan[local]:
  generate_block_plan empty_runtime_entry_live empty_runtime_entry_dfg
    empty_runtime_entry_cfg empty_runtime_entry_fn empty_runtime_fallback_block
    empty_runtime_after_entry = empty_runtime_fallback_block_plan_result
Proof
  simp[empty_runtime_fallback_block_plan_result_def,
       empty_runtime_fallback_block_plan_eval]
QED

val empty_runtime_after_fallback_eval =
  EVAL ``SND (THE empty_runtime_fallback_block_plan_result)``
Definition empty_runtime_after_fallback_def:
  empty_runtime_after_fallback = ^(rhs (concl empty_runtime_after_fallback_eval))
End

val empty_runtime_dispatch_block_plan_eval = EVAL
  ``generate_block_plan empty_runtime_entry_live empty_runtime_entry_dfg
      empty_runtime_entry_cfg empty_runtime_entry_fn empty_runtime_dispatch_block
      empty_runtime_after_fallback``
Definition empty_runtime_dispatch_block_plan_result_def:
  empty_runtime_dispatch_block_plan_result =
    ^(rhs (concl empty_runtime_dispatch_block_plan_eval))
End
Theorem empty_runtime_dispatch_block_plan[local]:
  generate_block_plan empty_runtime_entry_live empty_runtime_entry_dfg
    empty_runtime_entry_cfg empty_runtime_entry_fn empty_runtime_dispatch_block
    empty_runtime_after_fallback = empty_runtime_dispatch_block_plan_result
Proof
  simp[empty_runtime_dispatch_block_plan_result_def,
       empty_runtime_dispatch_block_plan_eval]
QED

val empty_runtime_aux_eval = EVAL
  ``generate_fn_plan_aux empty_runtime_entry_live empty_runtime_entry_dfg
      empty_runtime_entry_cfg empty_runtime_entry_fn ["__entry"] []
      (init_plan_state 0)``
Definition empty_runtime_aux_result_def:
  empty_runtime_aux_result = ^(rhs (concl empty_runtime_aux_eval))
End

Theorem empty_runtime_aux_plan[local]:
  generate_fn_plan_aux empty_runtime_entry_live empty_runtime_entry_dfg
    empty_runtime_entry_cfg empty_runtime_entry_fn ["__entry"] []
    (init_plan_state 0) = empty_runtime_aux_result
Proof
  simp[empty_runtime_aux_result_def, empty_runtime_aux_eval]
QED
(* Unit-shaped bounded O1 configuration used only by executable fixtures. *)

val empty_runtime_entry_plan_value_eval = EVAL
  ``case empty_runtime_aux_result of
      NONE => ARB
    | SOME (ops, labels, ps) => (ops, ps)``
Definition empty_runtime_entry_plan_def:
  empty_runtime_entry_plan = ^(rhs (concl empty_runtime_entry_plan_value_eval))
End

Theorem empty_runtime_entry_canonical[local]:
  canonical_param_prefix empty_runtime_entry_fn
Proof
  EVAL_TAC
QED

Definition empty_prague_rpolicy_def:
  empty_prague_rpolicy =
    <| rpol_target := prague_capabilities;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
End

val empty_runtime_lowering_eval =
  EVAL ``lower_vyper_runtime_unit ([] : toplevel list) empty_prague_rpolicy``
val empty_runtime_raw_unit_value_eval =
  EVAL ``THE (lower_vyper_runtime_unit ([] : toplevel list)
               empty_prague_rpolicy)``

Definition empty_runtime_raw_unit_def:
  empty_runtime_raw_unit = ^(rhs (concl empty_runtime_raw_unit_value_eval))
End

Theorem empty_runtime_lowering_exact:
  lower_vyper_runtime_unit ([] : toplevel list) empty_prague_rpolicy =
    SOME empty_runtime_raw_unit
Proof
  simp[empty_runtime_raw_unit_def, empty_runtime_lowering_eval,
       empty_runtime_raw_unit_value_eval,
       finite_mapTheory.FEVERY_FEMPTY,
       venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
QED


Theorem empty_runtime_raw_context_exact:
  empty_runtime_raw_unit.cu_context =
    <| ctx_functions := [empty_runtime_entry_raw_fn];
       ctx_entry := SOME "__entry";
       ctx_global_reserved := [] |>
Proof
  simp[empty_runtime_raw_unit_def, empty_runtime_raw_unit_value_eval,
       empty_runtime_entry_raw_fn_def, venomInstTheory.mk_inst_def,
       venomInstTheory.default_internal_call_abi_def,
       finite_mapTheory.FEVERY_FEMPTY,
       venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
QED
Definition empty_runtime_concrete_unit_def:
  empty_runtime_concrete_unit =
    empty_runtime_raw_unit with cu_context :=
      (empty_runtime_raw_unit.cu_context with
         ctx_functions := [empty_runtime_entry_fn])
End



Theorem empty_runtime_entry_concretize_eval[local]:
  concretize_function_eval [] empty_runtime_entry_raw_fn =
    SOME empty_runtime_entry_fn
Proof
  simp[empty_runtime_entry_fn_def, empty_runtime_entry_concretized_eval]
QED

Theorem empty_runtime_context_concretize_exact:
  concretize_context_eval empty_runtime_raw_unit.cu_context =
    SOME empty_runtime_concrete_unit.cu_context
Proof
  simp[empty_runtime_concrete_unit_def, empty_runtime_raw_context_exact,
       concretize_context_eval_def, empty_runtime_entry_concretize_eval]
QED
Theorem empty_runtime_init_counter_zero[local]:
  (init_plan_state 0 with ps_label_counter := 0) = init_plan_state 0
Proof
  EVAL_TAC
QED
Theorem empty_runtime_entry_plan_eval:
  generate_fn_plan empty_runtime_entry_fn 0 0 =
    SOME empty_runtime_entry_plan
Proof
  simp[stackPlanGenTheory.generate_fn_plan_def, empty_runtime_entry_canonical,
       empty_runtime_entry_live_eval, empty_runtime_entry_dfg_eval,
       empty_runtime_entry_cfg_eval, empty_runtime_entry_control_eval,
       empty_runtime_init_counter_zero, empty_runtime_aux_plan,
       empty_runtime_aux_result_def, empty_runtime_entry_plan_def,
       empty_runtime_entry_plan_value_eval]
QED


Theorem empty_runtime_entry_live_fuel_eval[local]:
  liveness_analyze_fuel 100000 empty_runtime_entry_fn =
    empty_runtime_entry_live
Proof
  EVAL_TAC
QED

Theorem empty_runtime_aux_fuel_eval[local]:
  !fuel.
  generate_fn_plan_aux_fuel
    (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC fuel))))))))))
    empty_runtime_entry_live empty_runtime_entry_dfg empty_runtime_entry_cfg
    empty_runtime_entry_fn ["__entry"] [] (init_plan_state 0) =
    empty_runtime_aux_result
Proof
  gen_tac >> EVAL_TAC
QED

Theorem empty_runtime_aux_fuel_100000_eval[local]:
  generate_fn_plan_aux_fuel 100000
    empty_runtime_entry_live empty_runtime_entry_dfg empty_runtime_entry_cfg
    empty_runtime_entry_fn ["__entry"] [] (init_plan_state 0) =
    empty_runtime_aux_result
Proof
  mp_tac (Q.SPEC `99990` empty_runtime_aux_fuel_eval) >> simp[]
QED

Theorem empty_runtime_entry_plan_fuel_eval:
  generate_fn_plan_fuel 100000 empty_runtime_entry_fn 0 0 =
    SOME empty_runtime_entry_plan
Proof
  simp[stackPlanGenTheory.generate_fn_plan_fuel_def,
       empty_runtime_entry_canonical, empty_runtime_entry_live_fuel_eval,
       empty_runtime_entry_dfg_eval, empty_runtime_entry_cfg_eval,
       empty_runtime_entry_control_eval, empty_runtime_init_counter_zero,
       empty_runtime_aux_fuel_100000_eval, empty_runtime_aux_result_def,
       empty_runtime_entry_plan_def, empty_runtime_entry_plan_value_eval]
QED
Theorem empty_bytecode_unit_pipeline_exact:
  bytecode_unit_pipeline_for_testing empty_prague_rpolicy
    empty_runtime_raw_unit =
  SOME <| po_unit := empty_runtime_concrete_unit;
          po_final_assembly := empty_prague_rpolicy.rpol_final_assembly |>
Proof
  simp[bytecode_unit_pipeline_for_testing_def,
       empty_runtime_context_concretize_exact,
       empty_runtime_concrete_unit_def]
QED

Theorem empty_runtime_raw_data_exact[local]:
  empty_runtime_raw_unit.cu_data_segment = []
Proof
  simp[empty_runtime_raw_unit_def, empty_runtime_raw_unit_value_eval,
       finite_mapTheory.FEVERY_FEMPTY,
       venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
QED

val empty_runtime_max_live_eom_eval = EVAL
  ``max_live_eom
      <| ctx_functions := [empty_runtime_entry_fn];
         ctx_entry := SOME "__entry";
         ctx_global_reserved := [] |>``
Theorem resolve_empty_prague_policy[local]:
  resolve_o1_policy (o1_policy prague_capabilities) =
    SOME empty_prague_rpolicy
Proof
  simp[venomPipelineDriverTheory.o1_policy_def,
       venomCompilerTypesTheory.resolve_o1_policy_def,
       empty_prague_rpolicy_def,
       venomPolicyTypesTheory.target_capabilities_wf_def,
       venomPolicyTypesTheory.prague_capabilities_def]
QED

Theorem empty_bytecode_matches_expected:
  compile_vyper_o1_fuel_for_testing 100000 ([] : toplevel list) =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "empty.hex")
Proof
  simp[compile_vyper_o1_fuel_for_testing_def,
       compileVyperTheory.compile_vyper_fuel_for_testing_def,
       resolve_empty_prague_policy, empty_runtime_lowering_exact,
       compileVyperTheory.checked_unit_pipeline_fuel_for_testing_def,
       empty_bytecode_unit_pipeline_exact,
       compileVyperTheory.finalize_codegen_fuel_for_testing_def,
       bytecode_identity_finalizer_for_testing_def] >>
  simp[codegenTheory.codegen_assembly_fuel_def,
       stackPlanGenTheory.generate_context_plan_fuel_def,
       stackPlanGenTheory.generate_context_plan_with_def,
       stackPlanGenTheory.generate_context_regions_def,
       empty_runtime_concrete_unit_def, empty_runtime_raw_context_exact,
       empty_runtime_raw_data_exact, empty_runtime_max_live_eom_eval,
       empty_runtime_entry_plan_fuel_eval] >>
  EVAL_TAC >>
  simp[finite_mapTheory.FEVERY_FEMPTY,
       venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM] >>
  EVAL_TAC >>
  FAIL_TAC "empty fixture after deploy evaluation"
QED



val noop_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 noop_program``
Theorem noop_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 noop_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "noop.hex")
Proof
  rewrite_tac[noop_compiler_eval] >> EVAL_TAC
QED

val return_uint_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 return_uint_program``
val return_arg_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 return_arg_program``
val local_uint_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 local_uint_program``
val add_arg_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 add_arg_program``
val two_external_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 two_external_program``

Theorem return_uint_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 return_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_uint.hex")
Proof
  rewrite_tac[return_uint_compiler_eval] >> EVAL_TAC
QED

Theorem return_arg_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 return_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "return_arg.hex")
Proof
  rewrite_tac[return_arg_compiler_eval] >> EVAL_TAC
QED

Theorem local_uint_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 local_uint_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "local_uint.hex")
Proof
  rewrite_tac[local_uint_compiler_eval] >> EVAL_TAC
QED

Theorem add_arg_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 add_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "add_arg.hex")
Proof
  rewrite_tac[add_arg_compiler_eval] >> EVAL_TAC
QED

Theorem two_external_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 two_external_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "two_external.hex")
Proof
  rewrite_tac[two_external_compiler_eval] >> EVAL_TAC
QED

val storage_read_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 storage_read_program``
val storage_write_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 storage_write_program``
val deploy_storage_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 deploy_storage_program``
val event_log_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 event_log_program``
val indexed_event_log_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 indexed_event_log_program``
val mixed_event_log_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 mixed_event_log_program``
val hashmap_read_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 hashmap_read_program``
val hashmap_write_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 hashmap_write_program``

Theorem storage_read_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 storage_read_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_read.hex")
Proof
  rewrite_tac[storage_read_compiler_eval] >> EVAL_TAC
QED

Theorem storage_write_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 storage_write_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "storage_write.hex")
Proof
  rewrite_tac[storage_write_compiler_eval] >> EVAL_TAC
QED

Theorem deploy_storage_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 deploy_storage_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "deploy_storage.hex")
Proof
  rewrite_tac[deploy_storage_compiler_eval] >> EVAL_TAC
QED

Theorem event_log_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "event_log.hex")
Proof
  rewrite_tac[event_log_compiler_eval] >> EVAL_TAC
QED

Theorem indexed_event_log_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 indexed_event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "indexed_event_log.hex")
Proof
  rewrite_tac[indexed_event_log_compiler_eval] >> EVAL_TAC
QED

Theorem mixed_event_log_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 mixed_event_log_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "mixed_event_log.hex")
Proof
  rewrite_tac[mixed_event_log_compiler_eval] >> EVAL_TAC
QED

Theorem hashmap_read_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 hashmap_read_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_read.hex")
Proof
  rewrite_tac[hashmap_read_compiler_eval] >> EVAL_TAC
QED

Theorem hashmap_write_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 hashmap_write_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "hashmap_write.hex")
Proof
  rewrite_tac[hashmap_write_compiler_eval] >> EVAL_TAC
QED

val if_bool_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 if_bool_program``
Theorem if_bool_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 if_bool_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_bool.hex")
Proof
  rewrite_tac[if_bool_compiler_eval] >> EVAL_TAC
QED

val if_join_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 if_join_program``
Theorem if_join_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 if_join_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "if_join.hex")
Proof
  rewrite_tac[if_join_compiler_eval] >> EVAL_TAC
QED

val for_pass_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 for_pass_program``
Theorem for_pass_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 for_pass_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_pass.hex")
Proof
  rewrite_tac[for_pass_compiler_eval] >> EVAL_TAC
QED

val for_accum_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 for_accum_program``
Theorem for_accum_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 for_accum_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_accum.hex")
Proof
  rewrite_tac[for_accum_compiler_eval] >> EVAL_TAC
QED

val for_continue_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval_with_fuels [100000]
  ``compile_vyper_o1_fuel_for_testing 100000 for_continue_program``
Theorem for_continue_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 for_continue_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_continue.hex")
Proof
  rewrite_tac[for_continue_compiler_eval] >> EVAL_TAC
QED

val for_break_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 for_break_program``
Theorem for_break_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 for_break_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "for_break.hex")
Proof
  rewrite_tac[for_break_compiler_eval] >> EVAL_TAC
QED


val internal_call_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval_with_fuels [100000]
  ``compile_vyper_o1_fuel_for_testing 100000 internal_call_program``
Theorem internal_call_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 internal_call_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call.hex")
Proof
  rewrite_tac[internal_call_compiler_eval] >> EVAL_TAC
QED

val internal_call_arg_compiler_eval = evalCompilerBytecodeLib.closed_compiler_eval
  ``compile_vyper_o1_fuel_for_testing 100000 internal_call_arg_program``
Theorem internal_call_arg_result_lengths:
  compile_vyper_o1_fuel_for_testing 100000 internal_call_arg_program =
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call_arg.hex")
Proof
  rewrite_tac[internal_call_arg_compiler_eval] >> EVAL_TAC
QED
