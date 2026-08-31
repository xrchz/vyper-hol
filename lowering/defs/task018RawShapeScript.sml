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

Theorem task18_fn_inst_wf_from_blocks[local]:
  (!bb. MEM bb fn.fn_blocks ==>
        EVERY inst_wf bb.bb_instructions) ==>
  fn_inst_wf fn
Proof
  rw[venomWfTheory.fn_inst_wf_def] >>
  first_x_assum drule >>
  simp[listTheory.EVERY_MEM]
QED

Theorem task18_lower_runtime_integrity[local]:
  lower_vyper_runtime_unit tops rpolicy = SOME unit ==>
  ctx_distinct_fn_names unit.cu_context /\
  wf_invoke_targets unit.cu_context /\
  ctx_inst_ids_distinct unit.cu_context /\
  forced_alloc_inputs_check unit.cu_context
Proof
  simp[compileVyperTheory.lower_vyper_runtime_unit_def]
  >> pairarg_tac
  >> gvs[]
  >> metis_tac[vyperCompilerTheory.run_lowering_integrity,
               vyperCompilerTheory.run_lowering_static_integrity]
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

Theorem task18_nested_entry_block_inst_wf:
  EVERY inst_wf task18_nested_entry_block.bb_instructions
Proof
  pure_rewrite_tac[task18_nested_entry_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[venomWfTheory.inst_wf_def, venomInstTheory.mk_inst_def]
QED

Theorem task18_nested_dispatch_block_inst_wf:
  EVERY inst_wf task18_nested_dispatch_block.bb_instructions
Proof
  pure_rewrite_tac[task18_nested_dispatch_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[venomWfTheory.inst_wf_def, venomInstTheory.mk_inst_def]
QED

Theorem task18_nested_match_block_inst_wf:
  EVERY inst_wf task18_nested_match_block.bb_instructions
Proof
  pure_rewrite_tac[task18_nested_match_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[venomWfTheory.inst_wf_def, venomInstTheory.mk_inst_def]
QED

Theorem task18_nested_next_block_inst_wf:
  EVERY inst_wf task18_nested_next_block.bb_instructions
Proof
  pure_rewrite_tac[task18_nested_next_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[venomWfTheory.inst_wf_def, venomInstTheory.mk_inst_def]
QED

Theorem task18_nested_foo_block_inst_wf:
  EVERY inst_wf task18_nested_foo_block.bb_instructions
Proof
  pure_rewrite_tac[task18_nested_foo_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[venomWfTheory.inst_wf_def, venomInstTheory.mk_inst_def]
QED

Theorem task18_nested_fallback_block_inst_wf:
  EVERY inst_wf task18_nested_fallback_block.bb_instructions
Proof
  pure_rewrite_tac[task18_nested_fallback_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[venomWfTheory.inst_wf_def, venomInstTheory.mk_inst_def]
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

Theorem task18_nested_dispatch_block_wf:
  bb_well_formed task18_nested_dispatch_block
Proof
  pure_rewrite_tac[task18_nested_dispatch_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> `[mk_inst 4 CALLDATALOAD [Lit 0w] ["%3"];
       mk_inst 5 SHR [Lit 224w; Var "%3"] ["%4"];
       mk_inst 6 EQ [Var "%4"; Lit (n2w 801029432)] ["%5"];
       mk_inst 7 JNZ
         [Var "%5"; Label (fresh_label_output "match" 2);
          Label (fresh_label_output "next" 3)] []] =
      [mk_inst 4 CALLDATALOAD [Lit 0w] ["%3"];
       mk_inst 5 SHR [Lit 224w; Var "%3"] ["%4"];
       mk_inst 6 EQ [Var "%4"; Lit (n2w 801029432)] ["%5"]] ++
      [mk_inst 7 JNZ
         [Var "%5"; Label (fresh_label_output "match" 2);
          Label (fresh_label_output "next" 3)] []]` by simp[]
  >> pop_assum (fn th => pure_once_rewrite_tac[th])
  >> irule task18_bb_well_formed_snoc
  >> EVAL_TAC
QED

Theorem task18_nested_match_block_wf:
  bb_well_formed task18_nested_match_block
Proof
  pure_rewrite_tac[task18_nested_match_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> `[mk_inst 8 JMP [Label "fn_foo"] []] =
      [] ++ [mk_inst 8 JMP [Label "fn_foo"] []]` by simp[]
  >> pop_assum (fn th => pure_once_rewrite_tac[th])
  >> irule task18_bb_well_formed_snoc
  >> EVAL_TAC
QED

Theorem task18_nested_next_block_wf:
  bb_well_formed task18_nested_next_block
Proof
  pure_rewrite_tac[task18_nested_next_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> `[mk_inst 9 JMP [Label nested_fallback_label] []] =
      [] ++ [mk_inst 9 JMP [Label nested_fallback_label] []]` by simp[]
  >> pop_assum (fn th => pure_once_rewrite_tac[th])
  >> irule task18_bb_well_formed_snoc
  >> EVAL_TAC
QED

Theorem task18_nested_foo_block_wf:
  bb_well_formed task18_nested_foo_block
Proof
  pure_rewrite_tac[task18_nested_foo_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> `[mk_inst 10 CALLVALUE [] ["%6"];
       mk_inst 11 ISZERO [Var "%6"] ["%7"];
       mk_inst 12 ASSERT [Var "%7"] [];
       mk_inst 13 CALLDATASIZE [] ["%8"];
       mk_inst 14 LT [Var "%8"; Lit 36w] ["%9"];
       mk_inst 15 ISZERO [Var "%9"] ["%10"];
       mk_inst 16 ASSERT [Var "%10"] [];
       mk_inst 17 CALLDATASIZE [] ["%11"];
       mk_inst 18 CALLDATALOAD [Lit 4w] ["%12"];
       mk_inst 19 MSTORE [Lit 0w; Var "%12"] [];
       mk_inst 20 MLOAD [Lit 0w] ["%13"];
       mk_inst 21 ALLOCA [Lit 32w] ["%14"];
       mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"];
       mk_inst 23 MSTORE [Var "%14"; Var "%15"] [];
       mk_inst 24 MLOAD [Var "%14"] ["%16"];
       mk_inst 25 ALLOCA [Lit 32w] ["%17"];
       mk_inst 26 MSTORE [Var "%17"; nested_foo_mid_call_operand] [];
       mk_inst 27 RETURN [Var "%17"; Lit 32w] []] =
      [mk_inst 10 CALLVALUE [] ["%6"];
       mk_inst 11 ISZERO [Var "%6"] ["%7"];
       mk_inst 12 ASSERT [Var "%7"] [];
       mk_inst 13 CALLDATASIZE [] ["%8"];
       mk_inst 14 LT [Var "%8"; Lit 36w] ["%9"];
       mk_inst 15 ISZERO [Var "%9"] ["%10"];
       mk_inst 16 ASSERT [Var "%10"] [];
       mk_inst 17 CALLDATASIZE [] ["%11"];
       mk_inst 18 CALLDATALOAD [Lit 4w] ["%12"];
       mk_inst 19 MSTORE [Lit 0w; Var "%12"] [];
       mk_inst 20 MLOAD [Lit 0w] ["%13"];
       mk_inst 21 ALLOCA [Lit 32w] ["%14"];
       mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"];
       mk_inst 23 MSTORE [Var "%14"; Var "%15"] [];
       mk_inst 24 MLOAD [Var "%14"] ["%16"];
       mk_inst 25 ALLOCA [Lit 32w] ["%17"];
       mk_inst 26 MSTORE [Var "%17"; nested_foo_mid_call_operand] []] ++
      [mk_inst 27 RETURN [Var "%17"; Lit 32w] []]` by simp[]
  >> pop_assum (fn th => pure_once_rewrite_tac[th])
  >> irule task18_bb_well_formed_snoc
  >> EVAL_TAC
QED

Theorem task18_nested_fallback_block_wf:
  bb_well_formed task18_nested_fallback_block
Proof
  pure_rewrite_tac[task18_nested_fallback_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> `[mk_inst 28 REVERT [Lit 0w; Lit 0w] []] =
      [] ++ [mk_inst 28 REVERT [Lit 0w; Lit 0w] []]` by simp[]
  >> pop_assum (fn th => pure_once_rewrite_tac[th])
  >> irule task18_bb_well_formed_snoc
  >> EVAL_TAC
QED

Theorem task18_nested_entry_block_succs:
  bb_succs task18_nested_entry_block =
    ["@fallback_0"; "@dispatch_1"]
Proof
  pure_rewrite_tac[venomInstTheory.bb_succs_def,
                   task18_nested_entry_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> EVAL_TAC
QED

Theorem task18_nested_dispatch_block_succs:
  bb_succs task18_nested_dispatch_block =
    ["@next_3"; "@match_2"]
Proof
  pure_rewrite_tac[venomInstTheory.bb_succs_def,
                   task18_nested_dispatch_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> EVAL_TAC
QED

Theorem task18_nested_match_block_succs:
  bb_succs task18_nested_match_block = ["fn_foo"]
Proof
  pure_rewrite_tac[venomInstTheory.bb_succs_def,
                   task18_nested_match_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> EVAL_TAC
QED

Theorem task18_nested_next_block_succs:
  bb_succs task18_nested_next_block = ["@fallback_0"]
Proof
  pure_rewrite_tac[venomInstTheory.bb_succs_def,
                   task18_nested_next_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> EVAL_TAC
QED

Theorem task18_nested_foo_block_succs:
  bb_succs task18_nested_foo_block = []
Proof
  pure_rewrite_tac[venomInstTheory.bb_succs_def,
                   task18_nested_foo_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> EVAL_TAC
QED

Theorem task18_nested_fallback_block_succs:
  bb_succs task18_nested_fallback_block = []
Proof
  pure_rewrite_tac[venomInstTheory.bb_succs_def,
                   task18_nested_fallback_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> EVAL_TAC
QED


Theorem task18_nested_entry_fn_wf:
  wf_function task18_nested_entry_fn
Proof
  rewrite_tac[venomWfTheory.wf_function_def]
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> conj_tac
  >- (rewrite_tac[task18_nested_entry_fn_blocks]
      >> rpt strip_tac
      >> gvs[task18_nested_entry_block_wf,
             task18_nested_dispatch_block_wf,
             task18_nested_match_block_wf,
             task18_nested_next_block_wf,
             task18_nested_foo_block_wf,
             task18_nested_fallback_block_wf])
  >> conj_tac
  >- (rewrite_tac[venomWfTheory.fn_succs_closed_def,
                  task18_nested_entry_fn_blocks]
      >> rpt strip_tac
      >> gvs[task18_nested_entry_block_succs,
             task18_nested_dispatch_block_succs,
             task18_nested_match_block_succs,
             task18_nested_next_block_succs,
             task18_nested_foo_block_succs,
             task18_nested_fallback_block_succs]
      >> EVAL_TAC)
  >> EVAL_TAC
QED

Definition task18_nested_leaf_block_def:
  task18_nested_leaf_block =
    <| bb_label := nested_after_leaf_body_state.cs_current_bb;
       bb_instructions := nested_after_leaf_body_state.cs_current_insts |>
End

Definition task18_nested_leaf_fn_def:
  task18_nested_leaf_fn =
    mk_internal_function "leaf" [task18_nested_leaf_block] F 1
End

Definition task18_nested_mid_block_def:
  task18_nested_mid_block =
    <| bb_label := nested_after_mid_body_state.cs_current_bb;
       bb_instructions := nested_after_mid_body_state.cs_current_insts |>
End

Definition task18_nested_mid_fn_def:
  task18_nested_mid_fn =
    mk_internal_function "mid" [task18_nested_mid_block] F 1
End

Theorem task18_nested_leaf_block_exact:
  task18_nested_leaf_block =
    <| bb_label := "leaf";
       bb_instructions :=
         [mk_inst 29 PARAM [Lit 0w] ["%18"];
          mk_inst 30 MSTORE [Lit 0w; nested_leaf_z_operand] [];
          mk_inst 31 PARAM [Lit 1w] ["%19"];
          mk_inst 32 MSTORE [Lit 32w; nested_leaf_return_pc_operand] [];
          mk_inst 33 MLOAD [Lit 0w] ["%20"];
          mk_inst 34 MLOAD [Lit 32w] ["%21"]] ++
         [mk_inst 35 RET
            [nested_leaf_value_operand;
             nested_leaf_loaded_return_pc_operand] []] |>
Proof
  simp[task18_nested_leaf_block_def,
       nested_after_leaf_body_state_def,
       nested_after_leaf_entry_state_def]
QED

Theorem task18_nested_mid_block_exact:
  task18_nested_mid_block =
    <| bb_label := "mid";
       bb_instructions :=
         [mk_inst 36 PARAM [Lit 0w] ["%22"];
          mk_inst 37 MSTORE [Lit 0w; nested_mid_y_operand] [];
          mk_inst 38 PARAM [Lit 1w] ["%23"];
          mk_inst 39 MSTORE [Lit 32w; nested_mid_return_pc_operand] [];
          mk_inst 40 MLOAD [Lit 0w] ["%24"];
          mk_inst 41 ALLOCA [Lit 32w] ["%25"];
          mk_inst 42 INVOKE [Label "leaf"; nested_mid_y_value_operand] ["%26"];
          mk_inst 43 MSTORE [Var "%25"; Var "%26"] [];
          mk_inst 44 MLOAD [Var "%25"] ["%27"];
          mk_inst 45 MLOAD [Lit 32w] ["%28"]] ++
         [mk_inst 46 RET
            [nested_mid_leaf_call_operand;
             nested_mid_loaded_return_pc_operand] []] |>
Proof
  simp[task18_nested_mid_block_def,
       nested_after_mid_body_state_def,
       nested_after_mid_leaf_call_state_def,
       nested_after_mid_name_state_def,
       nested_after_mid_entry_state_def]
QED

Theorem task18_nested_leaf_block_inst_wf:
  EVERY inst_wf task18_nested_leaf_block.bb_instructions
Proof
  rewrite_tac[task18_nested_leaf_block_exact]
  >> simp[venomWfTheory.inst_wf_def,
          venomInstTheory.mk_inst_def,
          nested_leaf_z_operand_def,
          nested_leaf_return_pc_operand_def,
          nested_leaf_value_operand_def,
          nested_leaf_loaded_return_pc_operand_def]
QED

Theorem task18_nested_leaf_block_wf:
  bb_well_formed task18_nested_leaf_block
Proof
  rewrite_tac[task18_nested_leaf_block_exact]
  >> irule task18_bb_well_formed_snoc
  >> EVAL_TAC
QED

Theorem task18_nested_mid_block_inst_wf:
  EVERY inst_wf task18_nested_mid_block.bb_instructions
Proof
  rewrite_tac[task18_nested_mid_block_exact]
  >> simp[venomWfTheory.inst_wf_def,
          venomInstTheory.mk_inst_def,
          nested_mid_y_operand_def,
          nested_mid_return_pc_operand_def,
          nested_mid_y_value_operand_def,
          nested_mid_leaf_call_operand_def,
          nested_mid_loaded_return_pc_operand_def]
QED

Theorem task18_nested_entry_fn_inst_wf:
  fn_inst_wf task18_nested_entry_fn
Proof
  irule task18_fn_inst_wf_from_blocks
  >> rewrite_tac[task18_nested_entry_fn_blocks]
  >> rpt strip_tac
  >> gvs[task18_nested_entry_block_inst_wf,
         task18_nested_dispatch_block_inst_wf,
         task18_nested_match_block_inst_wf,
         task18_nested_next_block_inst_wf,
         task18_nested_foo_block_inst_wf,
         task18_nested_fallback_block_inst_wf]
QED

Theorem task18_nested_leaf_fn_inst_wf:
  fn_inst_wf task18_nested_leaf_fn
Proof
  irule task18_fn_inst_wf_from_blocks
  >> simp[task18_nested_leaf_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def,
          task18_nested_leaf_block_inst_wf]
QED

Theorem task18_nested_mid_fn_inst_wf:
  fn_inst_wf task18_nested_mid_fn
Proof
  irule task18_fn_inst_wf_from_blocks
  >> simp[task18_nested_mid_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def,
          task18_nested_mid_block_inst_wf]
QED

Theorem task18_nested_mid_block_wf:
  bb_well_formed task18_nested_mid_block
Proof
  rewrite_tac[task18_nested_mid_block_exact]
  >> irule task18_bb_well_formed_snoc
  >> EVAL_TAC
QED

Theorem task18_nested_leaf_block_succs:
  bb_succs task18_nested_leaf_block = []
Proof
  simp[task18_nested_leaf_block_def,
       nested_after_leaf_body_state_def,
       nested_after_leaf_entry_state_def,
       venomInstTheory.bb_succs_def]
  >> EVAL_TAC
QED

Theorem task18_nested_mid_block_succs:
  bb_succs task18_nested_mid_block = []
Proof
  simp[task18_nested_mid_block_def,
       nested_after_mid_body_state_def,
       nested_after_mid_leaf_call_state_def,
       nested_after_mid_name_state_def,
       nested_after_mid_entry_state_def,
       venomInstTheory.bb_succs_def]
  >> EVAL_TAC
QED

Theorem task18_nested_leaf_fn_ids:
  FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    task18_nested_leaf_fn.fn_blocks) = [29; 30; 31; 32; 33; 34; 35]
Proof
  simp[task18_nested_leaf_fn_def,
       vyperCompilerTheory.mk_internal_function_def,
       venomInstTheory.mk_raw_function_def,
       task18_nested_leaf_block_exact,
       venomInstTheory.mk_inst_def]
QED

Theorem task18_nested_mid_fn_ids:
  FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    task18_nested_mid_fn.fn_blocks) =
  [36; 37; 38; 39; 40; 41; 42; 43; 44; 45; 46]
Proof
  simp[task18_nested_mid_fn_def,
       vyperCompilerTheory.mk_internal_function_def,
       venomInstTheory.mk_raw_function_def,
       task18_nested_mid_block_exact,
       venomInstTheory.mk_inst_def]
QED

Theorem task18_nested_leaf_fn_wf:
  wf_function task18_nested_leaf_fn
Proof
  rewrite_tac[venomWfTheory.wf_function_def]
  >> conj_tac
  >- simp[task18_nested_leaf_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def,
          venomInstTheory.fn_labels_def,
          task18_nested_leaf_block_exact]
  >> conj_tac
  >- simp[venomWfTheory.fn_has_entry_def,
          task18_nested_leaf_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def]
  >> conj_tac
  >- simp[task18_nested_leaf_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def,
          task18_nested_leaf_block_wf]
  >> conj_tac
  >- simp[venomWfTheory.fn_succs_closed_def,
          task18_nested_leaf_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def,
          task18_nested_leaf_block_succs]
  >> simp[venomWfTheory.fn_inst_ids_distinct_def,
          task18_nested_leaf_fn_ids]
QED

Theorem task18_nested_mid_fn_wf:
  wf_function task18_nested_mid_fn
Proof
  rewrite_tac[venomWfTheory.wf_function_def]
  >> conj_tac
  >- simp[task18_nested_mid_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def,
          venomInstTheory.fn_labels_def,
          task18_nested_mid_block_exact]
  >> conj_tac
  >- simp[venomWfTheory.fn_has_entry_def,
          task18_nested_mid_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def]
  >> conj_tac
  >- simp[task18_nested_mid_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def,
          task18_nested_mid_block_wf]
  >> conj_tac
  >- simp[venomWfTheory.fn_succs_closed_def,
          task18_nested_mid_fn_def,
          vyperCompilerTheory.mk_internal_function_def,
          venomInstTheory.mk_raw_function_def,
          task18_nested_mid_block_succs]
  >> simp[venomWfTheory.fn_inst_ids_distinct_def,
          task18_nested_mid_fn_ids]
QED
Theorem task18_nested_entry_fn_labels:
  fn_labels task18_nested_entry_fn =
    ["__entry"; "@dispatch_1"; "@match_2"; "@next_3";
     "fn_foo"; "@fallback_0"]
Proof
  pure_rewrite_tac[venomInstTheory.fn_labels_def,
                   task18_nested_entry_fn_blocks,
                   task18_nested_entry_block_def,
                   task18_nested_dispatch_block_def,
                   task18_nested_match_block_def,
                   task18_nested_next_block_def,
                   task18_nested_foo_block_def,
                   task18_nested_fallback_block_def,
                   task18_nested_entry_blocks_def,
                   nested_after_fallback_state_def,
                   nested_after_foo_body_state_def,
                   nested_after_foo_mid_call_state_def,
                   nested_after_foo_name_state_def,
                   nested_after_foo_entry_state_def]
  >> simp[]
  >> EVAL_TAC
QED

Theorem task18_nested_leaf_fn_labels:
  fn_labels task18_nested_leaf_fn = ["leaf"]
Proof
  simp[venomInstTheory.fn_labels_def,
       task18_nested_leaf_fn_def,
       vyperCompilerTheory.mk_internal_function_def,
       venomInstTheory.mk_raw_function_def,
       task18_nested_leaf_block_exact]
QED

Theorem task18_nested_mid_fn_labels:
  fn_labels task18_nested_mid_fn = ["mid"]
Proof
  simp[venomInstTheory.fn_labels_def,
       task18_nested_mid_fn_def,
       vyperCompilerTheory.mk_internal_function_def,
       venomInstTheory.mk_raw_function_def,
       task18_nested_mid_block_exact]
QED

Theorem task18_nested_context_entry:
  (mk_venom_context
     [task18_nested_entry_fn; task18_nested_leaf_fn; task18_nested_mid_fn]
     (SOME "__entry")).ctx_entry = SOME "__entry"
Proof
  simp[venomInstTheory.mk_venom_context_def]
QED

Theorem task18_nested_unit_labels_wf:
  unit_labels_wf
    <| cu_context :=
         mk_venom_context
           [task18_nested_entry_fn; task18_nested_leaf_fn;
            task18_nested_mid_fn] (SOME "__entry");
       cu_data_segment := [] |>
Proof
  simp[venomCompilerWfTheory.unit_labels_wf_def,
       venomCompilerWfTheory.unit_label_namespace_def,
       venomCompilerWfTheory.unit_data_labels_consistent_def,
       venomCompilerWfTheory.unit_data_label_refs_def,
       venomInstTheory.mk_venom_context_def,
       task18_nested_entry_fn_labels,
       task18_nested_leaf_fn_labels,
       task18_nested_mid_fn_labels]
QED

Theorem task18_nested_runtime_entry_member:
  case lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |> of
    NONE => F
  | SOME unit =>
      unit.cu_context.ctx_entry = SOME "__entry" /\
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

Theorem task18_nested_data_sections_empty:
  nested_after_mid_body_state.cs_data_sections = []
Proof
  simp[nested_after_mid_body_state_def]
  >> simp[nested_after_mid_leaf_call_state_def]
  >> simp[nested_after_mid_name_state_def]
  >> simp[nested_after_mid_entry_state_def]
  >> simp[nested_after_leaf_body_state_def]
  >> simp[nested_after_leaf_entry_state_def]
  >> simp[nested_after_fallback_state_def]
  >> simp[nested_after_foo_body_state_def]
  >> simp[nested_after_foo_mid_call_state_def]
  >> simp[nested_after_foo_name_state_def]
  >> simp[nested_after_foo_entry_state_def]
  >> simp[nested_after_dispatch_state_def]
QED

Theorem task18_nested_runtime_functions:
  case lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |> of
    NONE => F
  | SOME unit =>
      unit.cu_data_segment = [] /\
      unit.cu_context.ctx_functions =
        [task18_nested_entry_fn;
         task18_nested_leaf_fn;
         task18_nested_mid_fn]
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
          task18_nested_entry_blocks_def,
          task18_nested_leaf_fn_def,
          task18_nested_leaf_block_def,
          task18_nested_mid_fn_def,
          task18_nested_mid_block_def,
          vyperCompilerTheory.mk_internal_function_def]
  >> IF_CASES_TAC
  >- simp[task18_nested_data_sections_empty]
  >> mp_tac nested_internal_call_extracted_context
  >> pure_rewrite_tac[vyperCompilerTheory.extract_context_with_internals_def]
  >> simp[vyperCompilerTheory.internal_fn_descriptors_def,
          nested_leaf_package_def, nested_mid_package_def,
          nested_leaf_cenv_entry_facts, nested_mid_cenv_entry_facts]
  >> rewrite_tac[nested_internal_blocks_partition]
  >> simp[venomInstTheory.mk_venom_context_def,
          venomInstTheory.mk_raw_function_def,
          vyperCompilerTheory.mk_internal_function_def,
          task18_nested_entry_fn_def,
          task18_nested_entry_blocks_def,
          task18_nested_leaf_fn_def,
          task18_nested_leaf_block_def,
          task18_nested_mid_fn_def,
          task18_nested_mid_block_def]
QED
Theorem task18_nested_functions_wf:
  EVERY (\fn. wf_function fn /\ fn_inst_wf fn)
    [task18_nested_entry_fn; task18_nested_leaf_fn; task18_nested_mid_fn]
Proof
  simp[task18_nested_entry_fn_wf,
       task18_nested_leaf_fn_wf,
       task18_nested_mid_fn_wf,
       task18_nested_entry_fn_inst_wf,
       task18_nested_leaf_fn_inst_wf,
       task18_nested_mid_fn_inst_wf]
QED

Theorem task18_nested_runtime_unit_wf:
  case lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |> of
    NONE => F
  | SOME unit => unit_wf unit
Proof
  Cases_on `lower_vyper_runtime_unit nested_internal_call_program
    <| rpol_target := prague_capabilities;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>`
  >- (mp_tac nested_internal_call_packaging >> simp[])
  >> mp_tac task18_nested_runtime_entry_member
  >> mp_tac task18_nested_runtime_functions
  >> mp_tac nested_internal_call_packaging
  >> simp[]
  >> rpt strip_tac
  >> drule task18_lower_runtime_integrity
  >> strip_tac
  >> `ctx_wf x.cu_context` by
       gvs[venomWfTheory.ctx_wf_def,
           venomWfTheory.ctx_has_entry_def,
           venomWfTheory.ctx_distinct_fn_names_def]
  >> `!fn. MEM fn x.cu_context.ctx_functions ==>
             wf_function fn /\ fn_inst_wf fn` by
       (qpat_assum `x.cu_context.ctx_functions = _`
          (fn th => rewrite_tac[th])
        >> rpt strip_tac
        >> gvs[task18_nested_entry_fn_wf,
               task18_nested_leaf_fn_wf,
               task18_nested_mid_fn_wf,
               task18_nested_entry_fn_inst_wf,
               task18_nested_leaf_fn_inst_wf,
               task18_nested_mid_fn_inst_wf])
  >> `unit_labels_wf x` by
       gvs[venomCompilerWfTheory.unit_labels_wf_def,
           venomCompilerWfTheory.unit_label_namespace_def,
           venomCompilerWfTheory.unit_data_labels_consistent_def,
           venomCompilerWfTheory.unit_data_label_refs_def,
           task18_nested_entry_fn_labels,
           task18_nested_leaf_fn_labels,
           task18_nested_mid_fn_labels]
  >> irule task18_unit_wf_intro
  >> simp[]
QED
Theorem task18_nested_runtime_prechecks:
  case lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |> of
    NONE => F
  | SOME unit =>
      unit_wf unit /\
      lowering_context_ok unit.cu_context /\
      unit.cu_context.ctx_global_reserved = [] /\
      EVERY function_forced_metadata_ok unit.cu_context.ctx_functions /\
      EVERY (\fn. fn.fn_forced_alloc_positions = FEMPTY)
        unit.cu_context.ctx_functions /\
      target_capabilities_wf prague_capabilities /\
      prague_capabilities CapMcopy
Proof
  Cases_on `lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |>`
  >- (mp_tac nested_internal_call_packaging >> simp[])
  >> mp_tac task18_nested_runtime_unit_wf
  >> mp_tac nested_internal_call_packaging
  >> simp[]
  >> rpt strip_tac
  >> drule task18_lower_runtime_integrity
  >> gvs[vyperCompilerTheory.lowering_context_ok_def,
         GSYM vyperCompilerTheory.wf_invoke_targets_check_eq,
         venomPolicyTypesTheory.prague_capabilities_wf,
         venomPolicyTypesTheory.prague_capabilities_def]
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

Definition task18_immutable_deploy_unit_def:
  task18_immutable_deploy_unit =
    THE (lower_vyper_deploy_unit immutable_multi_deploy_program
      <| rpol_target := prague_capabilities;
         rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>
      ([170w; 187w] : byte list))
End

Definition task18_immutable_deploy_fn_def:
  task18_immutable_deploy_fn =
    EL 0 task18_immutable_deploy_unit.cu_context.ctx_functions
End

Definition task18_immutable_helper_fn_def:
  task18_immutable_helper_fn =
    EL 1 task18_immutable_deploy_unit.cu_context.ctx_functions
End

Theorem task18_immutable_deploy_functions:
  lower_vyper_deploy_unit immutable_multi_deploy_program
      <| rpol_target := prague_capabilities;
         rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>
      ([170w; 187w] : byte list) = SOME task18_immutable_deploy_unit /\
  task18_immutable_deploy_unit.cu_context.ctx_functions =
    [task18_immutable_deploy_fn; task18_immutable_helper_fn]
Proof
  Cases_on `lower_vyper_deploy_unit immutable_multi_deploy_program
      <| rpol_target := prague_capabilities;
         rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>
      ([170w; 187w] : byte list)`
  >- (mp_tac immutable_multi_deploy_static_inputs >> simp[])
  >> `task18_immutable_deploy_unit = x` by
       simp[task18_immutable_deploy_unit_def]
  >> simp[]
  >> mp_tac immutable_multi_deploy_static_inputs
  >> simp[]
  >> strip_tac
  >> Cases_on `x.cu_context.ctx_functions`
  >> gvs[task18_immutable_deploy_fn_def,
         task18_immutable_helper_fn_def]
  >> qpat_x_assum `[h; fn] = _`
       (fn th => rewrite_tac[GSYM th])
  >> simp[]
QED

Definition task18_immutable_deploy_block_def:
  task18_immutable_deploy_block =
    <| bb_label := "__deploy";
       bb_instructions :=
         [mk_inst 0 CALLVALUE [] ["%0"];
          mk_inst 1 ISZERO [Var "%0"] ["%1"];
          mk_inst 2 ASSERT [Var "%1"] [];
          mk_inst 3 ALLOCA [Lit 32w] ["%2"];
          mk_inst 4 MLOAD [Lit 0w] ["%3"];
          mk_inst 5 ALLOCA [Lit 34w] ["%4"];
          mk_inst 6 ADD [Var "%4"; Lit 2w] ["%5"];
          mk_inst 7 MCOPY [Var "%5"; Var "%2"; Lit 32w] [];
          mk_inst 8 OFFSET [Lit 0w; Label "runtime_begin"] ["%6"];
          mk_inst 9 CODECOPY [Var "%4"; Var "%6"; Lit 2w] []] ++
         [mk_inst 10 RETURN [Var "%4"; Lit 34w] []] |>
End

Definition task18_immutable_helper_block_def:
  task18_immutable_helper_block =
    <| bb_label := "helper";
       bb_instructions :=
         [mk_inst 11 ALLOCA [Lit 32w] ["%7"];
          mk_inst 12 MLOAD [Lit 0w] ["%8"];
          mk_inst 13 PARAM [Lit 0w] ["%9"];
          mk_inst 14 MSTORE [Lit 0w; Var "%9"] [];
          mk_inst 15 INVALID [] []] |>
End

Theorem task18_immutable_deploy_projections:
  task18_immutable_deploy_fn.fn_blocks = [task18_immutable_deploy_block] /\
  task18_immutable_helper_fn.fn_blocks = [task18_immutable_helper_block] /\
  unit_data_label_refs task18_immutable_deploy_unit = []
Proof
  mp_tac immutable_multi_deploy_static_inputs
  >> EVAL_TAC
  >> IF_CASES_TAC
  >- (gvs[vyperCompilerTheory.invoke_target_ok_def]
      >> IF_CASES_TAC
      >- (gvs[]
          >> pure_rewrite_tac[
               vyperCompilerTheory.function_forced_metadata_ok_def,
               vyperCompilerTheory.forced_alloc_key_in_function_def,
               venomInstTheory.fn_insts_def]
          >> simp[finite_mapTheory.FEVERY_FEMPTY,
                  finite_mapTheory.FEVERY_FUPDATE,
                  finite_mapTheory.FLOOKUP_UPDATE,
                  venomInstTheory.fn_insts_blocks_def,
                  LEFT_AND_OVER_OR, EXISTS_OR_THM, DISJ_IMP_THM]
          >> simp[venomCompilerWfTheory.data_section_label_refs_def,
                  venomCompilerWfTheory.data_item_label_refs_def])
      >> gvs[vyperCompilerTheory.function_forced_metadata_ok_def,
             vyperCompilerTheory.forced_alloc_key_in_function_def,
             venomInstTheory.fn_insts_def,
             finite_mapTheory.FEVERY_FEMPTY,
             finite_mapTheory.FEVERY_FUPDATE,
             venomInstTheory.fn_insts_blocks_def])
  >> gvs[]
QED

Theorem task18_immutable_deploy_block_wf:
  bb_well_formed task18_immutable_deploy_block /\
  EVERY inst_wf task18_immutable_deploy_block.bb_instructions
Proof
  conj_tac
  >- (pure_rewrite_tac[task18_immutable_deploy_block_def]
      >> irule task18_bb_well_formed_snoc
      >> EVAL_TAC)
  >> simp[task18_immutable_deploy_block_def,
          venomWfTheory.inst_wf_def,
          venomInstTheory.mk_inst_def]
QED


Theorem task18_immutable_helper_block_wf:
  bb_well_formed task18_immutable_helper_block /\
  EVERY inst_wf task18_immutable_helper_block.bb_instructions
Proof
  conj_tac
  >- (pure_rewrite_tac[task18_immutable_helper_block_def]
      >> `[mk_inst 11 ALLOCA [Lit 32w] ["%7"];
           mk_inst 12 MLOAD [Lit 0w] ["%8"];
           mk_inst 13 PARAM [Lit 0w] ["%9"];
           mk_inst 14 MSTORE [Lit 0w; Var "%9"] [];
           mk_inst 15 INVALID [] []] =
          [mk_inst 11 ALLOCA [Lit 32w] ["%7"];
           mk_inst 12 MLOAD [Lit 0w] ["%8"];
           mk_inst 13 PARAM [Lit 0w] ["%9"];
           mk_inst 14 MSTORE [Lit 0w; Var "%9"] []] ++
          [mk_inst 15 INVALID [] []]` by simp[]
      >> pop_assum (fn th => pure_once_rewrite_tac[th])
      >> irule task18_bb_well_formed_snoc
      >> EVAL_TAC)
  >> simp[task18_immutable_helper_block_def,
          venomWfTheory.inst_wf_def,
          venomInstTheory.mk_inst_def]
QED

Theorem task18_immutable_deploy_block_succs:
  bb_succs task18_immutable_deploy_block = []
Proof
  simp[task18_immutable_deploy_block_def,
       venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def,
       venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def,
       venomInstTheory.mk_inst_def]
QED

Theorem task18_immutable_helper_block_succs:
  bb_succs task18_immutable_helper_block = []
Proof
  simp[task18_immutable_helper_block_def,
       venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def,
       venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def,
       venomInstTheory.mk_inst_def]
QED

Theorem task18_immutable_deploy_fn_ids:
  FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    task18_immutable_deploy_fn.fn_blocks) =
  [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10]
Proof
  simp[task18_immutable_deploy_projections,
       task18_immutable_deploy_block_def,
       venomInstTheory.mk_inst_def]
QED

Theorem task18_immutable_helper_fn_ids:
  FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
    task18_immutable_helper_fn.fn_blocks) = [11; 12; 13; 14; 15]
Proof
  simp[task18_immutable_deploy_projections,
       task18_immutable_helper_block_def,
       venomInstTheory.mk_inst_def]
QED

Theorem task18_immutable_deploy_fn_labels:
  fn_labels task18_immutable_deploy_fn = ["__deploy"]
Proof
  simp[venomInstTheory.fn_labels_def,
       task18_immutable_deploy_projections,
       task18_immutable_deploy_block_def]
QED

Theorem task18_immutable_helper_fn_labels:
  fn_labels task18_immutable_helper_fn = ["helper"]
Proof
  simp[venomInstTheory.fn_labels_def,
       task18_immutable_deploy_projections,
       task18_immutable_helper_block_def]
QED

Theorem task18_immutable_deploy_fn_inst_wf:
  fn_inst_wf task18_immutable_deploy_fn
Proof
  irule task18_fn_inst_wf_from_blocks
  >> simp[task18_immutable_deploy_projections,
          task18_immutable_deploy_block_wf]
QED

Theorem task18_immutable_helper_fn_inst_wf:
  fn_inst_wf task18_immutable_helper_fn
Proof
  irule task18_fn_inst_wf_from_blocks
  >> simp[task18_immutable_deploy_projections,
          task18_immutable_helper_block_wf]
QED

Theorem task18_immutable_deploy_fn_wf:
  wf_function task18_immutable_deploy_fn
Proof
  rewrite_tac[venomWfTheory.wf_function_def]
  >> simp[task18_immutable_deploy_fn_labels,
          venomWfTheory.fn_has_entry_def,
          task18_immutable_deploy_projections,
          task18_immutable_deploy_block_wf,
          venomWfTheory.fn_succs_closed_def,
          task18_immutable_deploy_block_succs,
          venomWfTheory.fn_inst_ids_distinct_def,
          task18_immutable_deploy_fn_ids]
QED

Theorem task18_immutable_helper_fn_wf:
  wf_function task18_immutable_helper_fn
Proof
  rewrite_tac[venomWfTheory.wf_function_def]
  >> simp[task18_immutable_helper_fn_labels,
          venomWfTheory.fn_has_entry_def,
          task18_immutable_deploy_projections,
          task18_immutable_helper_block_wf,
          venomWfTheory.fn_succs_closed_def,
          task18_immutable_helper_block_succs,
          venomWfTheory.fn_inst_ids_distinct_def,
          task18_immutable_helper_fn_ids]
QED

Theorem task18_run_deploy_entry[local]:
  run_deploy_lowering has_constructor rpolicy runtime_bytecode immutables_len
    constructor_args data_size ctor_internal_fns cenv (stmts : stmt list) is_payable
    is_nonreentrant nkey use_transient entry_label = SOME unit ==>
  unit.cu_context.ctx_entry = SOME entry_label
Proof
  simp[vyperCompilerTheory.run_deploy_lowering_def]
  >> pairarg_tac
  >> gvs[AllCaseEqs(),
         vyperCompilerTheory.extract_context_with_forced_internals_def,
         venomInstTheory.mk_venom_context_def,
         vyperCompilerTheory.install_immutable_reservation_def]
  >> rpt strip_tac
  >> gvs[]
QED

Theorem task18_lower_deploy_integrity[local]:
  lower_vyper_deploy_unit tops rpolicy bytes = SOME unit ==>
  ctx_distinct_fn_names unit.cu_context /\
  wf_invoke_targets unit.cu_context /\
  ctx_inst_ids_distinct unit.cu_context /\
  forced_alloc_inputs_check unit.cu_context /\
  unit.cu_context.ctx_entry = SOME "__deploy"
Proof
  simp[compileVyperTheory.lower_vyper_deploy_unit_def]
  >> pairarg_tac
  >> gvs[]
  >> Cases_on `ctor_fn`
  >> gvs[]
  >> pairarg_tac
  >> gvs[]
  >> metis_tac[vyperCompilerTheory.run_deploy_lowering_integrity,
               vyperCompilerTheory.run_deploy_lowering_static_integrity,
               task18_run_deploy_entry]
QED

Theorem task18_immutable_deploy_context_entry:
  task18_immutable_deploy_unit.cu_context.ctx_entry = SOME "__deploy"
Proof
  mp_tac task18_immutable_deploy_functions
  >> strip_tac
  >> drule task18_lower_deploy_integrity
  >> simp[]
QED

Theorem task18_immutable_deploy_unit_labels_wf:
  unit_labels_wf task18_immutable_deploy_unit
Proof
  simp[venomCompilerWfTheory.unit_labels_wf_def,
       venomCompilerWfTheory.unit_label_namespace_def,
       venomCompilerWfTheory.unit_data_labels_consistent_def,
       task18_immutable_deploy_functions,
       task18_immutable_deploy_fn_labels,
       task18_immutable_helper_fn_labels,
       task18_immutable_deploy_projections]
QED


Theorem task18_immutable_function_names:
  task18_immutable_deploy_fn.fn_name = "__deploy" /\
  task18_immutable_helper_fn.fn_name = "helper"
Proof
  mp_tac task18_immutable_deploy_functions
  >> strip_tac
  >> mp_tac immutable_multi_deploy_static_inputs
  >> simp[]
  >> strip_tac
  >> qpat_x_assum `task18_immutable_deploy_unit.cu_context.ctx_functions = _`
       (fn th => rewrite_tac[th])
  >> gvs[]
QED
Theorem task18_immutable_deploy_unit_wf:
  unit_wf task18_immutable_deploy_unit
Proof
  mp_tac task18_immutable_deploy_functions
  >> strip_tac
  >> drule task18_lower_deploy_integrity
  >> strip_tac
  >> `ctx_wf task18_immutable_deploy_unit.cu_context` by
       gvs[venomWfTheory.ctx_wf_def,
           venomWfTheory.ctx_has_entry_def,
           venomWfTheory.ctx_distinct_fn_names_def,
           task18_immutable_deploy_context_entry,
           task18_immutable_function_names,
           venomInstTheory.ctx_fn_names_def]
  >> `!fn. MEM fn task18_immutable_deploy_unit.cu_context.ctx_functions ==>
             wf_function fn /\ fn_inst_wf fn` by
       (qpat_assum `task18_immutable_deploy_unit.cu_context.ctx_functions = _`
          (fn th => rewrite_tac[th])
        >> rpt strip_tac
        >> gvs[task18_immutable_deploy_fn_wf,
               task18_immutable_helper_fn_wf,
               task18_immutable_deploy_fn_inst_wf,
               task18_immutable_helper_fn_inst_wf])
  >> irule task18_unit_wf_intro
  >> simp[task18_immutable_deploy_unit_labels_wf]
QED
val _ = export_theory();
