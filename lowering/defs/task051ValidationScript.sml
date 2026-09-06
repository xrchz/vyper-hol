(* Executable and definitional validation for TASK_051 compiler interfaces. *)
Theory task051Validation
Ancestors compileVyper

Theorem checked_unit_pipeline_pipeline_none:
  pipeline rpolicy unit = NONE ==>
  checked_unit_pipeline pipeline finalizer rpolicy unit = NONE
Proof
  simp[checked_unit_pipeline_def]
QED

Theorem checked_unit_pipeline_rejects_policy_mismatch:
  pipeline rpolicy unit = SOME out /\
  out.po_final_assembly <> rpolicy.rpol_final_assembly ==>
  checked_unit_pipeline pipeline finalizer rpolicy unit = NONE
Proof
  simp[checked_unit_pipeline_def]
QED

Theorem checked_unit_pipeline_finalizer_none:
  pipeline rpolicy unit = SOME out /\
  out.po_final_assembly = rpolicy.rpol_final_assembly /\
  finalize_codegen finalizer rpolicy out.po_unit = NONE ==>
  checked_unit_pipeline pipeline finalizer rpolicy unit = NONE
Proof
  simp[checked_unit_pipeline_def]
QED

Theorem compile_vyper_with_rejects_missing_mcopy_first:
  compile_vyper_with pipeline finalizer
    <|cpol_target := (\c. c <> CapMcopy)|> tops = NONE
Proof
  simp[compile_vyper_with_def,
       venomCompilerTypesTheory.resolve_o1_policy_missing_mcopy]
QED

Theorem compile_vyper_with_runtime_lowering_none:
  resolve_o1_policy policy = SOME rpolicy /\
  lower_vyper_runtime_unit tops rpolicy = NONE ==>
  compile_vyper_with pipeline finalizer policy tops = NONE
Proof
  simp[compile_vyper_with_def]
QED

Theorem compile_vyper_with_runtime_pipeline_none:
  resolve_o1_policy policy = SOME rpolicy /\
  lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
  pipeline rpolicy runtime_unit = NONE ==>
  compile_vyper_with pipeline finalizer policy tops = NONE
Proof
  simp[compile_vyper_with_def, checked_unit_pipeline_def]
QED

Theorem compile_vyper_with_runtime_finalizer_none:
  resolve_o1_policy policy = SOME rpolicy /\
  lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
  pipeline rpolicy runtime_unit = SOME out /\
  out.po_final_assembly = rpolicy.rpol_final_assembly /\
  finalize_codegen finalizer rpolicy out.po_unit = NONE ==>
  compile_vyper_with pipeline finalizer policy tops = NONE
Proof
  simp[compile_vyper_with_def, checked_unit_pipeline_def]
QED

Theorem compile_vyper_with_deploy_lowering_none:
  resolve_o1_policy policy = SOME rpolicy /\
  lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
  checked_unit_pipeline pipeline finalizer rpolicy runtime_unit =
    SOME runtime_bytecode /\
  lower_vyper_deploy_unit tops rpolicy runtime_bytecode = NONE ==>
  compile_vyper_with pipeline finalizer policy tops = NONE
Proof
  simp[compile_vyper_with_def]
QED

Theorem compile_vyper_with_deploy_pipeline_none:
  resolve_o1_policy policy = SOME rpolicy /\
  lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
  checked_unit_pipeline pipeline finalizer rpolicy runtime_unit =
    SOME runtime_bytecode /\
  lower_vyper_deploy_unit tops rpolicy runtime_bytecode = SOME deploy_unit /\
  pipeline rpolicy deploy_unit = NONE ==>
  compile_vyper_with pipeline finalizer policy tops = NONE
Proof
  simp[compile_vyper_with_def, checked_unit_pipeline_def]
QED

Theorem compile_vyper_with_deploy_finalizer_none:
  resolve_o1_policy policy = SOME rpolicy /\
  lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
  checked_unit_pipeline pipeline finalizer rpolicy runtime_unit =
    SOME runtime_bytecode /\
  lower_vyper_deploy_unit tops rpolicy runtime_bytecode = SOME deploy_unit /\
  pipeline rpolicy deploy_unit = SOME out /\
  out.po_final_assembly = rpolicy.rpol_final_assembly /\
  finalize_codegen finalizer rpolicy out.po_unit = NONE ==>
  compile_vyper_with pipeline finalizer policy tops = NONE
Proof
  simp[compile_vyper_with_def, checked_unit_pipeline_def]
QED

Theorem compile_vyper_with_success_order:
  resolve_o1_policy policy = SOME rpolicy /\
  lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
  checked_unit_pipeline pipeline finalizer rpolicy runtime_unit =
    SOME runtime_bytecode /\
  lower_vyper_deploy_unit tops rpolicy runtime_bytecode = SOME deploy_unit /\
  checked_unit_pipeline pipeline finalizer rpolicy deploy_unit =
    SOME deploy_bytecode ==>
  compile_vyper_with pipeline finalizer policy tops =
    SOME (deploy_bytecode, runtime_bytecode)
Proof
  simp[compile_vyper_with_def]
QED

Theorem task051_runtime_installed_before_deploy:
  case lower_vyper_deploy_unit ([] : toplevel list)
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |>
         ([170w; 187w] : byte list) of
    NONE => F
  | SOME u =>
      MEM <| ds_label := "runtime_begin";
             ds_items := [DataBytes ([170w; 187w] : byte list)] |>
          u.cu_data_segment
Proof
  ACCEPT_TAC lower_vyper_deploy_unit_empty_installs_runtime
QED

Theorem resolve_prague_o1_requests_optimization:
  resolve_o1_policy (o1_policy prague_capabilities) =
    SOME <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |>
Proof
  simp[venomPipelineDriverTheory.o1_policy_def,
       venomCompilerTypesTheory.resolve_o1_policy_def,
       venomPolicyTypesTheory.target_capabilities_wf_def,
       venomPolicyTypesTheory.prague_capabilities_def]
QED

Theorem compile_vyper_o1_is_prague_specialization:
  compile_vyper_o1 finalizer tops =
  compile_vyper finalizer (o1_policy prague_capabilities) tops
Proof
  simp[compile_vyper_o1_def]
QED

val _ = export_theory()
