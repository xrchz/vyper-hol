(* Executable validation fixtures for target-checked DRET desugaring. *)
Theory dretDesugarProps
Ancestors
  dretDesugarProofs
Libs
  bossLib listTheory

Definition dret_test_supply_def:
  dret_test_supply =
    <| irs_next_inst := 101; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [100;42;7];
       irs_used_vars := ["formal_var_0";"src1";"size1";"ret1";
                         "src2";"size2";"ret2"];
       irs_used_labels := ["entry";"multi"] |>
End

Definition dret_test_block_def:
  dret_test_block label insts =
    <| bb_label := label; bb_instructions := insts |>
End

Definition dret_opcode_count_def:
  dret_opcode_count op fn =
    LENGTH (FILTER (\inst. inst.inst_opcode = op) (fn_insts fn))
End

Definition dret_output_vars_def:
  dret_output_vars fn = FLAT (MAP (\inst. inst.inst_outputs) (fn_insts fn))
End

Definition dret_multi_fn_def:
  dret_multi_fn = mk_raw_function "multi"
    [dret_test_block "entry"
      [mk_inst 100 GETFMP [] ["formal_var_0"];
       mk_inst 7 DRET [Lit 1w; Var "src1"; Var "size1"; Var "ret1"] [];
       mk_inst 42 DRET [Lit 1w; Var "src2"; Var "size2"; Var "ret2"] []]]
End

Definition dret_plain_fn_def:
  dret_plain_fn = mk_raw_function "plain"
    [dret_test_block "plain_entry" [mk_inst 3 STOP [] []]]
End

Definition dret_malformed_fn_def:
  dret_malformed_fn = mk_raw_function "malformed"
    [dret_test_block "malformed_entry" [mk_inst 4 DRET [] []]]
End

Definition dret_sealed_fn_def:
  dret_sealed_fn =
    dret_multi_fn with fn_fmp_signature :=
      SOME <| fms_has_fmp_param := T; fms_publishes := T |>
End

Theorem dret_no_dret_identity_eval:
  dret_desugar_function prague_capabilities dret_test_supply dret_plain_fn =
    SOME (dret_plain_fn,dret_test_supply)
Proof
  EVAL_TAC >> simp[]
QED

Theorem dret_malformed_rejected_eval:
  dret_desugar_function prague_capabilities dret_test_supply
    dret_malformed_fn = NONE
Proof
  EVAL_TAC >> simp[]
QED

Theorem dret_sealed_rejected_eval:
  dret_desugar_function prague_capabilities dret_test_supply
    dret_sealed_fn = NONE
Proof
  EVAL_TAC >> simp[] >>
  qexists `mk_inst 7 DRET [Lit 1w; Var "src1"; Var "size1"; Var "ret1"] []` >>
  simp[venomInstTheory.mk_inst_def]
QED

Theorem dret_missing_mcopy_rejected_eval:
  dret_desugar_function (\c. F) dret_test_supply dret_multi_fn = NONE
Proof
  EVAL_TAC >> simp[] >>
  qexists `mk_inst 7 DRET [Lit 1w; Var "src1"; Var "size1"; Var "ret1"] []` >>
  simp[venomInstTheory.mk_inst_def]
QED


Theorem dret_multi_fn_ready:
  ~no_dret dret_multi_fn /\ dret_desugar_input dret_multi_fn
Proof
  conj_tac
  >- (simp[dretDesugarDefsTheory.no_dret_def, dret_multi_fn_def,
           dret_test_block_def, venomInstTheory.mk_raw_function_def,
           venomInstTheory.mk_inst_def, venomInstTheory.fn_insts_def,
           venomInstTheory.fn_insts_blocks_def] >>
      qexists `mk_inst 7 DRET [Lit 1w; Var "src1"; Var "size1"; Var "ret1"] []` >>
      simp[venomInstTheory.mk_inst_def]) >>
  simp[dretDesugarDefsTheory.dret_desugar_input_def, dret_multi_fn_def,
       dret_test_block_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def, venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[] >>
  simp[dretShapeDefsTheory.parse_dret_shape_def, dret_value_operand_simps]
QED
Theorem dret_multiple_expansion_eval:
  case dret_desugar_function prague_capabilities dret_test_supply dret_multi_fn of
    NONE => F
  | SOME (fn',s') =>
      no_dret fn' /\
      dret_opcode_count GETFMP fn' = 2 /\
      dret_opcode_count MCOPY fn' = 2 /\
      dret_opcode_count RETFMP fn' = 2 /\
      ALL_DISTINCT (fn_ir_inst_ids fn') /\
      ALL_DISTINCT (dret_output_vars fn') /\
      MEM "formal_var_0" (dret_output_vars fn') /\
      s'.irs_next_inst = 114
Proof
  mp_tac dret_multi_fn_ready >> strip_tac >>
  simp[dretDesugarDefsTheory.dret_desugar_function_def,
       venomPolicyTypesTheory.prague_capabilities_def] >>
  EVAL_TAC >>
  simp[dretDesugarDefsTheory.expand_dret_pairs_def,
       irSupplyTheory.fresh_ir_var_def,
       irSupplyTheory.seek_fresh_name_def] >> EVAL_TAC >>
  rpt strip_tac >> gvs[]
QED

Definition dret_collision_fn1_def:
  dret_collision_fn1 = mk_raw_function "collision_1"
    [dret_test_block "collision_entry_1"
      [mk_inst 1000 GETFMP [] ["formal_var_0"];
       mk_inst 7 DRET [Lit 1w; Var "src_a"; Var "size_a"; Var "ret_a"] []]]
End

Definition dret_collision_fn2_def:
  dret_collision_fn2 = mk_raw_function "collision_2"
    [dret_test_block "collision_entry_2"
      [mk_inst 9000 GETFMP [] ["formal_var_1"];
       mk_inst 71 DRET [Lit 1w; Var "src_b"; Var "size_b"; Var "ret_b"] []]]
End

Theorem dret_collision_fn1_ready:
  ~no_dret dret_collision_fn1 /\ dret_desugar_input dret_collision_fn1
Proof
  conj_tac
  >- (simp[dretDesugarDefsTheory.no_dret_def, dret_collision_fn1_def,
           dret_test_block_def, venomInstTheory.mk_raw_function_def,
           venomInstTheory.mk_inst_def, venomInstTheory.fn_insts_def,
           venomInstTheory.fn_insts_blocks_def] >>
      qexists `mk_inst 7 DRET [Lit 1w; Var "src_a"; Var "size_a"; Var "ret_a"] []` >>
      simp[venomInstTheory.mk_inst_def]) >>
  simp[dretDesugarDefsTheory.dret_desugar_input_def, dret_collision_fn1_def,
       dret_test_block_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def, venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[] >>
  simp[dretShapeDefsTheory.parse_dret_shape_def, dret_value_operand_simps]
QED

Theorem dret_collision_fn2_ready:
  ~no_dret dret_collision_fn2 /\ dret_desugar_input dret_collision_fn2
Proof
  conj_tac
  >- (simp[dretDesugarDefsTheory.no_dret_def, dret_collision_fn2_def,
           dret_test_block_def, venomInstTheory.mk_raw_function_def,
           venomInstTheory.mk_inst_def, venomInstTheory.fn_insts_def,
           venomInstTheory.fn_insts_blocks_def] >>
      qexists `mk_inst 71 DRET [Lit 1w; Var "src_b"; Var "size_b"; Var "ret_b"] []` >>
      simp[venomInstTheory.mk_inst_def]) >>
  simp[dretDesugarDefsTheory.dret_desugar_input_def, dret_collision_fn2_def,
       dret_test_block_def, venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def, venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[] >>
  simp[dretShapeDefsTheory.parse_dret_shape_def, dret_value_operand_simps]
QED

Definition dret_collision_unit_def:
  dret_collision_unit =
    <| cu_context := mk_venom_context
         [dret_collision_fn1; dret_collision_fn2] (SOME "collision_1");
       cu_data_segment := [] |>
End

Definition dret_unit_output_vars_def:
  dret_unit_output_vars unit =
    FLAT (MAP dret_output_vars unit.cu_context.ctx_functions)
End

Definition dret_unit_opcode_count_def:
  dret_unit_opcode_count op unit =
    SUM (MAP (dret_opcode_count op) unit.cu_context.ctx_functions)
End

Theorem dret_collision_supply_eval:
  init_ir_supply dret_collision_unit =
    <| irs_next_inst := 9001; irs_next_var := 0; irs_next_label := 0;
       irs_used_inst_ids := [1000;7;9000;71];
       irs_used_vars := ["formal_var_0";"src_a";"size_a";"ret_a";
                         "formal_var_1";"src_b";"size_b";"ret_b"];
       irs_used_labels := ["collision_1";"collision_1";"collision_entry_1";
                           "collision_2";"collision_entry_2"] |>
Proof
  EVAL_TAC
QED

Theorem dret_collision_unit_eval:
  case dret_desugar_configured prague_capabilities dret_collision_unit of
    NONE => F
  | SOME unit' =>
      EVERY no_dret unit'.cu_context.ctx_functions /\
      dret_unit_opcode_count GETFMP unit' = 4 /\
      dret_unit_opcode_count MCOPY unit' = 2 /\
      dret_unit_opcode_count RETFMP unit' = 2 /\
      ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids unit'.cu_context.ctx_functions)) /\
      ALL_DISTINCT (dret_unit_output_vars unit') /\
      MEM "formal_var_0" (dret_unit_output_vars unit') /\
      MEM "formal_var_1" (dret_unit_output_vars unit')
Proof
  mp_tac dret_collision_fn1_ready >>
  mp_tac dret_collision_fn2_ready >>
  rpt strip_tac >>
  simp[dret_collision_unit_def, venomInstTheory.mk_venom_context_def,
       dret_collision_supply_eval, dret_collision_fn1_ready,
       dret_collision_fn2_ready,
       dretDesugarDefsTheory.dret_desugar_configured_def,
       dretDesugarDefsTheory.dret_desugar_configured_with_supply_def,
       dretDesugarDefsTheory.dret_desugar_context_def,
       dretDesugarDefsTheory.map_ctx_functions_supply_def,
       dretDesugarDefsTheory.map_functions_supply_def,
       dretDesugarDefsTheory.dret_desugar_function_def,
       venomPolicyTypesTheory.prague_capabilities_def] >>
  EVAL_TAC >>
  simp[dretDesugarDefsTheory.expand_dret_pairs_def,
       irSupplyTheory.fresh_ir_var_def,
       irSupplyTheory.seek_fresh_name_def] >> EVAL_TAC >>
  rpt strip_tac >> gvs[]
QED

val _ = export_theory();
