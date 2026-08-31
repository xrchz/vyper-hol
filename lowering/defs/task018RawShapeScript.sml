(*
 * TASK_018 focused raw frontend-shape validation.
 *
 * These are closed compiler evaluations only: they inspect emitted instruction
 * envelopes and call ABI metadata, without claiming source-level correctness.
 *)

Theory task018RawShape
Ancestors
  evalCompiler

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

val _ = export_theory();
