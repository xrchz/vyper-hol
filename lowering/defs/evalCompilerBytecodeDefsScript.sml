(* Shared testing-only compiler wrappers used by bytecode evaluation theories. *)
Theory evalCompilerBytecodeDefs
Ancestors evalCompiler compileVyper concretizeMemLocDefs

(* The fixture profile deliberately requests the configured formal O1 IR
   pipeline while abstracting only the final assembly implementation. *)
Definition formal_o1_ir_no_asm_opt_identity_finalizer_def:
  formal_o1_ir_no_asm_opt_identity_finalizer
    (rpolicy : resolved_compiler_policy) asm = SOME asm
End

Definition formal_o1_ir_no_asm_opt_def:
  formal_o1_ir_no_asm_opt fuel (tops : toplevel list) =
    compile_vyper_fuel_for_testing fuel
      (\rpolicy unit.
         run_venom_pipeline (K T) (K T) (K T)
           rpolicy o1_pipeline_spec unit)
      formal_o1_ir_no_asm_opt_identity_finalizer
      (o1_policy prague_capabilities) tops
End

Theorem formal_o1_ir_no_asm_opt_identity_finalizer_thm:
  formal_o1_ir_no_asm_opt_identity_finalizer rpolicy asm = SOME asm
Proof
  simp[formal_o1_ir_no_asm_opt_identity_finalizer_def]
QED

Theorem formal_o1_ir_no_asm_opt_policy:
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

Theorem formal_o1_ir_no_asm_opt_pipeline:
  formal_o1_ir_no_asm_opt fuel tops =
    compile_vyper_fuel_for_testing fuel
      (\rpolicy unit.
         run_venom_pipeline (K T) (K T) (K T)
           rpolicy o1_pipeline_spec unit)
      formal_o1_ir_no_asm_opt_identity_finalizer
      (o1_policy prague_capabilities) tops
Proof
  simp[formal_o1_ir_no_asm_opt_def]
QED

(* Temporary compatibility names for existing evaluation proofs.  Fixture
   consumers use [formal_o1_ir_no_asm_opt] as the canonical profile. *)
Definition bytecode_unit_pipeline_for_testing_def:
  bytecode_unit_pipeline_for_testing rpolicy unit =
    case concretize_context_eval unit.cu_context of
      NONE => NONE
    | SOME ctx =>
        SOME <| po_unit := unit with cu_context := ctx;
                po_final_assembly := rpolicy.rpol_final_assembly |>
End

Definition bytecode_identity_finalizer_for_testing_def:
  bytecode_identity_finalizer_for_testing =
    formal_o1_ir_no_asm_opt_identity_finalizer
End

Definition compile_vyper_o1_fuel_for_testing_def:
  compile_vyper_o1_fuel_for_testing = formal_o1_ir_no_asm_opt
End

val _ = export_theory()
