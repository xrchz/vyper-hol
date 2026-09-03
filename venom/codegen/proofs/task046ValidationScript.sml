(* Focused executable validation for TASK 046 checked unit codegen. *)

Theory task046Validation
Ancestors
  contextPlanCodegenProps
Libs
  BasicProvers

Definition task046_empty_ctx_def:
  task046_empty_ctx =
    <|ctx_functions := []; ctx_entry := NONE; ctx_global_reserved := []|>
End

Definition task046_data_def:
  task046_data =
    [<|ds_label := "data"; ds_items := [DataBytes [1w; 2w]]|>]
End

Definition task046_safe_policy_def:
  task046_safe_policy =
    <|rpol_target := prague_capabilities;
      rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Preserve|>
End

Definition task046_optimize_policy_def:
  task046_optimize_policy =
    task046_safe_policy with rpol_final_assembly := FAP_Optimize
End

Definition task046_legacy_policy_def:
  task046_legacy_policy =
    <|rpol_target := (\c. c = CapPush0);
      rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Preserve|>
End

Definition task046_no_push0_policy_def:
  task046_no_push0_policy =
    <|rpol_target := (K F : target_capabilities);
      rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Preserve|>
End

Definition task046_data_unit_def:
  task046_data_unit =
    <|cu_context := task046_empty_ctx; cu_data_segment := task046_data|>
End

Definition task046_empty_unit_def:
  task046_empty_unit =
    <|cu_context := task046_empty_ctx; cu_data_segment := []|>
End

Definition task046_missing_fn_def:
  task046_missing_fn = mk_raw_function "missing_eom" []
End

Definition task046_missing_unit_def:
  task046_missing_unit =
    <|cu_context :=
        <|ctx_functions := [task046_missing_fn]; ctx_entry := NONE;
          ctx_global_reserved := []|>;
      cu_data_segment := []|>
End

Definition task046_mcopy_fn_def:
  task046_mcopy_fn =
    (mk_raw_function "uses_mcopy"
      [<|bb_label := "entry";
         bb_instructions := [mk_inst 0 MCOPY [] []]|>]) with
      fn_eom := SOME 0
End

Definition task046_mcopy_unit_def:
  task046_mcopy_unit =
    <|cu_context :=
        <|ctx_functions := [task046_mcopy_fn]; ctx_entry := SOME "uses_mcopy";
          ctx_global_reserved := []|>;
      cu_data_segment := []|>
End

Definition task046_identity_finalizer_def:
  task046_identity_finalizer policy asm = SOME asm
End

Definition task046_rejecting_finalizer_def:
  task046_rejecting_finalizer policy asm = NONE
End

Definition task046_mcopy_finalizer_def:
  task046_mcopy_finalizer policy asm = SOME (asm ++ [AsmOp "MCOPY"])
End

Definition task046_unknown_finalizer_def:
  task046_unknown_finalizer policy asm = SOME (asm ++ [AsmOp "NOT_AN_OPCODE"])
End

Theorem task046_empty_plan_eval[local,simp]:
  generate_context_plan task046_empty_ctx =
    SOME <|cp_regions := []; cp_max_static_eom := 0;
           cp_peak_spill_end := 0; cp_initial_fmp := 0|>
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem task046_empty_context_safe[local,simp]:
  context_target_safe prague_capabilities task046_empty_ctx
Proof
  EVAL_TAC
QED

Theorem task046_empty_context_legacy_safe[local,simp]:
  context_target_safe (\c. c = CapPush0) task046_empty_ctx
Proof
  EVAL_TAC
QED

Theorem task046_revert_exec_eval[local,simp]:
  execute_plan 0
    [SOLabel "revert"; SOPush (Lit 0w); SOEmit "DUP1"; SOEmit "REVERT"] =
    [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"]
Proof
  rewrite_tac[planExecTheory.execute_plan_def] >>
  simp[planExecTheory.exec_stack_op_def, Excl "encode_num_bytes_def"] >>
  once_rewrite_tac[asmIRTheory.encode_num_bytes_def] >> simp[]
QED

Theorem task046_revert_data_safe[local,simp]:
  assembly_target_safe prague_capabilities
    [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT";
     AsmDataHeader "data"; AsmDataItem [1w; 2w]]
Proof
  EVAL_TAC
QED

Theorem task046_revert_legacy_safe[local,simp]:
  assembly_target_safe (\c. c = CapPush0)
    [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"]
Proof
  EVAL_TAC
QED

Theorem task046_data_append_eval:
  codegen_assembly task046_safe_policy task046_data_unit =
    SOME [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT";
          AsmDataHeader "data"; AsmDataItem [1w; 2w]]
Proof
  simp[codegenTheory.codegen_assembly_def, task046_safe_policy_def,
       task046_data_unit_def, task046_data_def,
       venomPolicyTypesTheory.prague_capabilities_wf,
       stackPlanGenTheory.context_plan_ops_def,
       stackPlanGenTheory.revert_postamble_def,
       asmIRTheory.data_segment_asm_def, asmIRTheory.data_section_asm_def]
QED

Theorem task046_empty_codegen_eval[local,simp]:
  codegen_assembly task046_legacy_policy task046_empty_unit =
    SOME [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"]
Proof
  simp[codegenTheory.codegen_assembly_def, task046_legacy_policy_def,
       task046_empty_unit_def,
       venomPolicyTypesTheory.target_capabilities_wf_def,
       stackPlanGenTheory.context_plan_ops_def,
       stackPlanGenTheory.revert_postamble_def,
       asmIRTheory.data_segment_asm_def]
QED

Theorem task046_missing_eom_eval:
  codegen_assembly task046_safe_policy task046_missing_unit = NONE
Proof
  EVAL_TAC
QED

Theorem task046_source_target_rejection_eval:
  codegen_assembly task046_legacy_policy task046_mcopy_unit = NONE /\
  codegen_assembly_fuel 20 task046_legacy_policy task046_mcopy_unit = NONE
Proof
  EVAL_TAC
QED

Theorem task046_no_push0_revert_unsafe[local,simp]:
  ~assembly_target_safe (K F)
    [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT"]
Proof
  EVAL_TAC
QED

Theorem task046_no_push0_codegen_eval[local,simp]:
  codegen_assembly task046_no_push0_policy task046_empty_unit = NONE
Proof
  simp[codegenTheory.codegen_assembly_def, task046_no_push0_policy_def,
       task046_empty_unit_def,
       venomPolicyTypesTheory.target_capabilities_wf_def,
       venomTargetSafetyTheory.context_target_safe_def,
       stackPlanGenTheory.context_plan_ops_def,
       stackPlanGenTheory.revert_postamble_def,
       asmIRTheory.data_segment_asm_def]
QED

Theorem task046_assembly_target_rejection_eval:
  codegen_assembly task046_no_push0_policy task046_empty_unit = NONE /\
  ~assembly_target_safe (K F) [AsmPush []] /\
  ~assembly_target_safe prague_capabilities [AsmOp "NOT_AN_OPCODE"]
Proof
  simp[] >> EVAL_TAC
QED

Theorem task046_injected_assembly_unsafe[local,simp]:
  ~assembly_target_safe (\c. c = CapPush0)
    [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT";
     AsmOp "MCOPY"] /\
  ~assembly_target_safe (\c. c = CapPush0)
    [AsmLabel "revert"; AsmPush []; AsmOp "DUP1"; AsmOp "REVERT";
     AsmOp "NOT_AN_OPCODE"]
Proof
  EVAL_TAC
QED

Theorem task046_finalizer_rejection_eval:
  finalize_codegen task046_mcopy_finalizer task046_legacy_policy
    task046_empty_unit = NONE /\
  finalize_codegen task046_unknown_finalizer task046_legacy_policy
    task046_empty_unit = NONE
Proof
  simp[codegenTheory.finalize_codegen_def, task046_legacy_policy_def,
       task046_mcopy_finalizer_def, task046_unknown_finalizer_def]
QED

Theorem task046_optimize_callback_eval:
  finalize_codegen task046_rejecting_finalizer task046_optimize_policy
    task046_empty_unit = NONE
Proof
  Cases_on `codegen_assembly task046_optimize_policy task046_empty_unit` >>
  simp[codegenTheory.finalize_codegen_def, task046_rejecting_finalizer_def]
QED

Theorem task046_explicit_identity_eval:
  finalize_codegen task046_identity_finalizer task046_safe_policy
    task046_data_unit = SOME [0x5Bw; 0x5Fw; 0x80w; 0xFDw; 1w; 2w]
Proof
  rewrite_tac[codegenTheory.finalize_codegen_def, task046_data_append_eval,
              task046_identity_finalizer_def] >>
  simp[] >> EVAL_TAC
QED

val _ = export_theory();
