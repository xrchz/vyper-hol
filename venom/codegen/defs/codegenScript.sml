(*
 * Unit-based, target-aware Venom -> EVM code generation.
 *
 * Planning and plan execution produce checked assembly.  Byte assembly occurs
 * only after an explicit finalizer callback has returned another checked
 * assembly program.
 *)

Theory codegen
Ancestors
  asmTargetSafety
  assemblyFinalizer

Definition codegen_assembly_def:
  codegen_assembly (rpolicy : resolved_compiler_policy)
                   (unit : compilation_unit) : asm_inst list option =
    if ~target_capabilities_wf rpolicy.rpol_target then NONE
    else if ~context_target_safe rpolicy.rpol_target unit.cu_context then NONE
    else
      case generate_context_plan unit.cu_context of
        NONE => NONE
      | SOME plan =>
          let asm =
            execute_plan plan.cp_initial_fmp (context_plan_ops plan) ++
            data_segment_asm unit.cu_data_segment
          in
            if assembly_target_safe rpolicy.rpol_target asm
            then SOME asm
            else NONE
End

Definition codegen_assembly_fuel_def:
  codegen_assembly_fuel fuel (rpolicy : resolved_compiler_policy)
                           (unit : compilation_unit) : asm_inst list option =
    if ~target_capabilities_wf rpolicy.rpol_target then NONE
    else if ~context_target_safe rpolicy.rpol_target unit.cu_context then NONE
    else
      case generate_context_plan_fuel fuel unit.cu_context of
        NONE => NONE
      | SOME plan =>
          let asm =
            execute_plan plan.cp_initial_fmp (context_plan_ops plan) ++
            data_segment_asm unit.cu_data_segment
          in
            if assembly_target_safe rpolicy.rpol_target asm
            then SOME asm
            else NONE
End

Definition finalize_codegen_def:
  finalize_codegen (finalizer : assembly_finalizer)
                   (rpolicy : resolved_compiler_policy)
                   (unit : compilation_unit) : byte list option =
    case codegen_assembly rpolicy unit of
      NONE => NONE
    | SOME asm =>
        case finalizer rpolicy asm of
          NONE => NONE
        | SOME finalized_asm =>
            if assembly_target_safe rpolicy.rpol_target finalized_asm
            then SOME (assemble finalized_asm)
            else NONE
End

val _ = export_theory ();
