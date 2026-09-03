(*
 * Checked codegen failure facts at the public unit-based API boundary.
 *)

Theory contextPlanCodegenProps
Ancestors
  contextPlanProps codegen

Theorem codegen_missing_eom:
  (?fn. MEM fn unit.cu_context.ctx_functions /\ fn.fn_eom = NONE) ==>
  codegen_assembly rpolicy unit = NONE
Proof
  strip_tac >>
  `generate_context_plan unit.cu_context = NONE` by
    metis_tac[generate_context_plan_missing_eom] >>
  simp[codegen_assembly_def]
QED

Theorem codegen_assembly_target_not_wf:
  ~target_capabilities_wf rpolicy.rpol_target ==>
  codegen_assembly rpolicy unit = NONE
Proof
  simp[codegen_assembly_def]
QED

Theorem codegen_assembly_context_unsafe:
  ~context_target_safe rpolicy.rpol_target unit.cu_context ==>
  codegen_assembly rpolicy unit = NONE
Proof
  simp[codegen_assembly_def]
QED

Theorem codegen_assembly_fuel_target_not_wf:
  ~target_capabilities_wf rpolicy.rpol_target ==>
  codegen_assembly_fuel fuel rpolicy unit = NONE
Proof
  simp[codegen_assembly_fuel_def]
QED

Theorem codegen_assembly_fuel_context_unsafe:
  ~context_target_safe rpolicy.rpol_target unit.cu_context ==>
  codegen_assembly_fuel fuel rpolicy unit = NONE
Proof
  simp[codegen_assembly_fuel_def]
QED

Theorem finalize_codegen_callback_none:
  codegen_assembly rpolicy unit = SOME asm /\
  finalizer rpolicy asm = NONE ==>
  finalize_codegen finalizer rpolicy unit = NONE
Proof
  simp[finalize_codegen_def]
QED

Theorem finalize_codegen_unsafe_output:
  codegen_assembly rpolicy unit = SOME asm /\
  finalizer rpolicy asm = SOME finalized_asm /\
  ~assembly_target_safe rpolicy.rpol_target finalized_asm ==>
  finalize_codegen finalizer rpolicy unit = NONE
Proof
  simp[finalize_codegen_def]
QED

Theorem finalize_codegen_optimize_callback_rejects:
  rpolicy.rpol_final_assembly = FAP_Optimize ==>
  finalize_codegen
    (\policy asm.
       if policy.rpol_final_assembly = FAP_Optimize then NONE else SOME asm)
    rpolicy unit = NONE
Proof
  strip_tac >>
  simp[finalize_codegen_def] >>
  Cases_on `codegen_assembly rpolicy unit` >> simp[]
QED

val _ = export_theory();
