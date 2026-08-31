(*
 * TASK_018 focused raw frontend-shape validation.
 *
 * These are closed compiler evaluations only: they inspect emitted instruction
 * envelopes and call ABI metadata, without claiming source-level correctness.
 *)

Theory task018RawShape
Ancestors
  evalCompiler
  venomCompilerWf


Theorem task18_unit_wf_intro[local]:
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

Theorem task18_bb_well_formed_snoc[local]:
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

Definition task18_initial_state_def:
  task18_initial_state : compile_state =
    <| cs_next_var := 0;
       cs_next_label := 0;
       cs_next_id := 0;
       cs_current_bb := "entry";
       cs_current_insts := [];
       cs_blocks := [];
       cs_data_sections := [] |>
End

Definition task18_block_insts_def:
  task18_block_insts [] = [] /\
  task18_block_insts (b::bs) =
    b.bb_instructions ++ task18_block_insts bs
End

Definition task18_state_insts_def:
  task18_state_insts st =
    st.cs_current_insts ++ task18_block_insts st.cs_blocks
End

Definition task18_emitted_insts_def:
  task18_emitted_insts (m:compile_state -> 'a # compile_state) =
    task18_state_insts (SND (m task18_initial_state))
End

Definition task18_opcodes_def:
  task18_opcodes [] = [] /\
  task18_opcodes (i::is) = i.inst_opcode :: task18_opcodes is
End

Definition task18_emitted_opcodes_def:
  task18_emitted_opcodes m = task18_opcodes (task18_emitted_insts m)
End

Definition task18_all_dret_wf_def:
  task18_all_dret_wf insts =
    EVERY (\i. i.inst_opcode = DRET ==>
               i.inst_outputs = [] /\ IS_SOME (parse_dret_shape i)) insts
End

Definition task18_prague_cenv_def:
  task18_prague_cenv : compile_env =
    (ARB:compile_env) with
      <| ce_target := prague_capabilities;
         ce_struct_fields := FEMPTY;
         ce_vars := FEMPTY |>
End

Definition task18_no_mcopy_cenv_def:
  task18_no_mcopy_cenv : compile_env =
    task18_prague_cenv with ce_target := (\cap. cap <> CapMcopy)
End

Definition task18_bytes_type_def:
  task18_bytes_type = BaseT (BytesT (Dynamic 64))
End

Definition task18_ordinary_return_def:
  task18_ordinary_return =
    compile_internal_return task18_prague_cenv
      (SOME (Var "%value")) (Var "%return_pc") 1
      (BaseT (UintT 256)) (BaseT (UintT 256)) [] NONE
End

Theorem task18_ordinary_return_shape:
  task18_emitted_insts task18_ordinary_return =
    [mk_inst 0 RET [Var "%value"; Var "%return_pc"] []] /\
  task18_all_dret_wf (task18_emitted_insts task18_ordinary_return)
Proof
  EVAL_TAC
QED

Theorem task18_one_dynamic_representable[simp]:
  1 < dimword(:256)
Proof
  simp[wordsTheory.dimword_def]
QED

Definition task18_dynamic_return_def:
  task18_dynamic_return =
    compile_internal_return task18_prague_cenv
      (SOME (Var "%value")) (Var "%return_pc") 0
      task18_bytes_type task18_bytes_type [] (SOME (Var "%return_buf"))
End

Theorem task18_dynamic_return_shape:
  task18_emitted_opcodes task18_dynamic_return =
    [MLOAD; ADD; AND; ADD; DRET] /\
  LAST (task18_emitted_insts task18_dynamic_return) =
    mk_inst 4 DRET
      [Lit 1w; Var "%value"; Var "%3"; Var "%return_pc"] [] /\
  parse_dret_shape (LAST (task18_emitted_insts task18_dynamic_return)) =
    SOME (0,1) /\
  task18_all_dret_wf (task18_emitted_insts task18_dynamic_return)
Proof
  EVAL_TAC >>
  simp[task18_one_dynamic_representable,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       task18_block_insts_def, task18_opcodes_def,
       task18_all_dret_wf_def, dretShapeDefsTheory.parse_dret_shape_def,
       venomInstTheory.mk_inst_def]
QED

Definition task18_no_mcopy_return_def:
  task18_no_mcopy_return =
    compile_internal_return task18_no_mcopy_cenv
      (SOME (Var "%value")) (Var "%return_pc") 0
      task18_bytes_type task18_bytes_type [] (SOME (Var "%return_buf"))
End

Theorem task18_no_mcopy_return_shape:
  task18_emitted_insts task18_no_mcopy_return =
    [mk_inst 0 INVALID [] []] /\
  ~MEM MCOPY (task18_emitted_opcodes task18_no_mcopy_return) /\
  ~MEM DRET (task18_emitted_opcodes task18_no_mcopy_return) /\
  task18_all_dret_wf (task18_emitted_insts task18_no_mcopy_return)
Proof
  EVAL_TAC
QED

Definition task18_one_word_complex_type_def:
  task18_one_word_complex_type = TupleT [BaseT (UintT 256)]
End

Definition task18_tuple_cenv_def:
  task18_tuple_cenv : compile_env =
    task18_prague_cenv with
      <| ce_vars := FEMPTY |+ ("x", MemLoc 64 32);
         ce_var_type :=
           (\name. if name = "x" then SOME task18_one_word_complex_type
                   else NONE) |>
End

Definition task18_tuple_unpack_def:
  task18_tuple_unpack =
    compile_tuple_unpack task18_tuple_cenv
      (TupleT [task18_one_word_complex_type])
      [BaseTarget (NameTarget "x")] (Var "%source")
End

Theorem task18_one_word_tuple_unpack_shape:
  task18_emitted_opcodes task18_tuple_unpack =
    [ALLOCA; MCOPY; MLOAD; MSTORE] /\
  task18_emitted_insts task18_tuple_unpack =
    [mk_inst 0 ALLOCA [Lit 32w] ["%0"];
     mk_inst 1 MCOPY [Var "%0"; Var "%source"; Lit 32w] [];
     mk_inst 2 MLOAD [Var "%0"] ["%1"];
     mk_inst 3 MSTORE [Lit 64w; Var "%1"] []] /\
  task18_all_dret_wf (task18_emitted_insts task18_tuple_unpack)
Proof
  EVAL_TAC
QED

Theorem task18_nested_user_arity:
  MEM (mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"])
      nested_after_foo_mid_call_state.cs_current_insts /\
  MEM (mk_inst 42 INVOKE
        [Label "leaf"; nested_mid_y_value_operand] ["%26"])
      nested_after_mid_leaf_call_state.cs_current_insts /\
  case lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |> of
    NONE => F
  | SOME unit =>
      MAP (\fn. (fn.fn_name, fn.fn_call_abi, fn.fn_noinline,
                 fn.fn_eom, fn.fn_fmp_signature))
          unit.cu_context.ctx_functions =
        [("__entry", default_internal_call_abi, F, NONE, NONE);
         ("leaf",
          <| ica_has_memory_return_buffer := SOME F;
             ica_user_return_count := SOME 1 |>, F, NONE, NONE);
         ("mid",
          <| ica_has_memory_return_buffer := SOME F;
             ica_user_return_count := SOME 1 |>, F, NONE, NONE)]
Proof
  conj_tac
  >- EVAL_TAC
  >> conj_tac
  >- simp[nested_after_mid_leaf_call_state_def]
  >> mp_tac nested_internal_call_packaging
  >> Cases_on `lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |>`
  >> gvs[]
QED


Definition task18_nested_entry_blocks_def:
  task18_nested_entry_blocks =
    REVERSE nested_after_foo_body_state.cs_blocks ++
      [<| bb_label := nested_after_foo_body_state.cs_current_bb;
          bb_instructions := nested_after_foo_body_state.cs_current_insts |>;
       <| bb_label := nested_after_fallback_state.cs_current_bb;
          bb_instructions := nested_after_fallback_state.cs_current_insts |>]
End

Definition task18_nested_entry_block_def:
  task18_nested_entry_block = EL 0 task18_nested_entry_blocks
End

Definition task18_nested_dispatch_block_def:
  task18_nested_dispatch_block = EL 1 task18_nested_entry_blocks
End

Definition task18_nested_match_block_def:
  task18_nested_match_block = EL 2 task18_nested_entry_blocks
End

Definition task18_nested_next_block_def:
  task18_nested_next_block = EL 3 task18_nested_entry_blocks
End

Definition task18_nested_foo_block_def:
  task18_nested_foo_block = EL 4 task18_nested_entry_blocks
End

Definition task18_nested_fallback_block_def:
  task18_nested_fallback_block = EL 5 task18_nested_entry_blocks
End

Definition task18_nested_entry_fn_def:
  task18_nested_entry_fn =
    mk_raw_function "__entry" task18_nested_entry_blocks
End

Theorem task18_nested_entry_fn_blocks:
  task18_nested_entry_fn.fn_blocks =
    [task18_nested_entry_block; task18_nested_dispatch_block;
     task18_nested_match_block; task18_nested_next_block;
     task18_nested_foo_block; task18_nested_fallback_block]
Proof
  EVAL_TAC
QED


Theorem task18_nested_entry_block_wf:
  bb_well_formed task18_nested_entry_block
Proof
  pure_rewrite_tac[task18_nested_entry_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> `[mk_inst 0 CALLDATASIZE [] ["%0"];
       mk_inst 1 LT [Var "%0"; Lit 4w] ["%1"];
       mk_inst 2 ISZERO [Var "%1"] ["%2"];
       mk_inst 3 JNZ
         [Var "%2"; Label (fresh_label_output "dispatch" 1);
          Label nested_fallback_label] []] =
      [mk_inst 0 CALLDATASIZE [] ["%0"];
       mk_inst 1 LT [Var "%0"; Lit 4w] ["%1"];
       mk_inst 2 ISZERO [Var "%1"] ["%2"]] ++
      [mk_inst 3 JNZ
         [Var "%2"; Label (fresh_label_output "dispatch" 1);
          Label nested_fallback_label] []]` by simp[]
  >> pop_assum (fn th => pure_once_rewrite_tac[th])
  >> irule task18_bb_well_formed_snoc
  >> EVAL_TAC
QED
Theorem task18_nested_runtime_entry_member:
  case lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |> of
    NONE => F
  | SOME unit =>
      HD unit.cu_context.ctx_functions = task18_nested_entry_fn
Proof
  pure_rewrite_tac[compileVyperTheory.lower_vyper_runtime_unit_def,
                   vyperCompilerTheory.run_lowering_def]
  >> rewrite_tac[nested_internal_call_classify,
                 nested_internal_call_selectors]
  >> rewrite_tac[nested_external_target_packages,
                 nested_internal_target_packages]
  >> simp[nested_internal_call_classify,
       nested_internal_call_selectors,
       nested_external_package_eq,
       nested_leaf_package_eq,
       nested_mid_package_eq,
       compileVyperTheory.package_fallback_fn_def,
       compileVyperTheory.set_fallback_package_target_def,
       vyperCompilerTheory.lowering_policy_ok_def,
       venomPolicyTypesTheory.prague_capabilities_wf,
       venomPolicyTypesTheory.prague_capabilities_def,
       venomPolicyTypesTheory.target_capabilities_wf_def,
       nested_runtime_final_state_eq,
       nested_internal_call_extracted_context]
  >> pure_rewrite_tac[vyperCompilerTheory.extract_context_with_internals_def]
  >> simp[vyperCompilerTheory.internal_fn_descriptors_def,
          nested_leaf_package_def, nested_mid_package_def,
          nested_leaf_cenv_entry_facts, nested_mid_cenv_entry_facts]
  >> rewrite_tac[nested_internal_blocks_partition]
  >> simp[venomInstTheory.mk_venom_context_def,
          venomInstTheory.mk_raw_function_def,
          task18_nested_entry_fn_def,
          task18_nested_entry_blocks_def]
  >> IF_CASES_TAC
  >- simp[]
  >> mp_tac nested_internal_call_extracted_context
  >> pure_rewrite_tac[vyperCompilerTheory.extract_context_with_internals_def]
  >> simp[vyperCompilerTheory.internal_fn_descriptors_def,
          nested_leaf_package_def, nested_mid_package_def,
          nested_leaf_cenv_entry_facts, nested_mid_cenv_entry_facts]
  >> rewrite_tac[nested_internal_blocks_partition]
  >> simp[venomInstTheory.mk_venom_context_def,
          venomInstTheory.mk_raw_function_def]
QED
(* TASK_018 unsupported-shape inventory (and only this boundary):
   1. A top-level bytes/string dynamic return without CapMcopy emits INVALID
      before length computation, MCOPY-dependent behavior, or DRET.
   2. A nested ABI-dynamic return, or a bytes/string return with a non-
      bytestring source representation, emits INVALID; this port does not
      synthesize a malformed flattened dynamic envelope.
   3. Complex tuple staging without CapMcopy emits INVALID before allocation or
      MCOPY.  If pass 1 materializes a one-word complex source but the target
      requires multiple words, pass 2 emits INVALID rather than treating the
      materialized word as a pointer. *)

Definition task18_nested_dynamic_type_def:
  task18_nested_dynamic_type = TupleT [task18_bytes_type]
End

Definition task18_nested_dynamic_return_def:
  task18_nested_dynamic_return =
    compile_internal_return task18_prague_cenv
      (SOME (Var "%value")) (Var "%return_pc") 0
      task18_nested_dynamic_type task18_nested_dynamic_type []
      (SOME (Var "%return_buf"))
End

Definition task18_mismatched_dynamic_return_def:
  task18_mismatched_dynamic_return =
    compile_internal_return task18_prague_cenv
      (SOME (Var "%value")) (Var "%return_pc") 0
      task18_bytes_type (BaseT (UintT 256)) [] (SOME (Var "%return_buf"))
End

Theorem task18_unsupported_dynamic_shapes:
  task18_emitted_insts task18_nested_dynamic_return =
    [mk_inst 0 INVALID [] []] /\
  task18_emitted_insts task18_mismatched_dynamic_return =
    [mk_inst 0 INVALID [] []] /\
  ~MEM MCOPY (task18_emitted_opcodes task18_nested_dynamic_return) /\
  ~MEM DRET (task18_emitted_opcodes task18_nested_dynamic_return) /\
  task18_all_dret_wf (task18_emitted_insts task18_nested_dynamic_return)
Proof
  EVAL_TAC
QED

Definition task18_no_mcopy_tuple_unpack_def:
  task18_no_mcopy_tuple_unpack =
    compile_tuple_unpack task18_no_mcopy_cenv
      (TupleT [task18_one_word_complex_type])
      [BaseTarget (NameTarget "x")] (Var "%source")
End

Theorem task18_no_mcopy_tuple_fails_early:
  task18_emitted_insts task18_no_mcopy_tuple_unpack =
    [mk_inst 0 INVALID [] []] /\
  ~MEM ALLOCA (task18_emitted_opcodes task18_no_mcopy_tuple_unpack) /\
  ~MEM MCOPY (task18_emitted_opcodes task18_no_mcopy_tuple_unpack) /\
  task18_all_dret_wf (task18_emitted_insts task18_no_mcopy_tuple_unpack)
Proof
  EVAL_TAC
QED

Definition task18_two_word_complex_type_def:
  task18_two_word_complex_type =
    TupleT [BaseT (UintT 256); BaseT (UintT 256)]
End

Definition task18_incompatible_tuple_cenv_def:
  task18_incompatible_tuple_cenv : compile_env =
    task18_prague_cenv with
      <| ce_vars := FEMPTY |+ ("x", MemLoc 64 64);
         ce_var_type :=
           (\name. if name = "x" then SOME task18_two_word_complex_type
                   else NONE) |>
End

Definition task18_incompatible_tuple_unpack_def:
  task18_incompatible_tuple_unpack =
    compile_tuple_unpack task18_incompatible_tuple_cenv
      (TupleT [task18_one_word_complex_type])
      [BaseTarget (NameTarget "x")] (Var "%source")
End

Theorem task18_incompatible_one_word_tuple_fails:
  task18_emitted_opcodes task18_incompatible_tuple_unpack =
    [ALLOCA; MCOPY; MLOAD; INVALID] /\
  LAST (task18_emitted_insts task18_incompatible_tuple_unpack) =
    mk_inst 3 INVALID [] [] /\
  task18_all_dret_wf (task18_emitted_insts task18_incompatible_tuple_unpack)
Proof
  EVAL_TAC
QED

val _ = export_theory();
