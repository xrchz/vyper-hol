(* Shared testing-only compiler wrappers used by bytecode evaluation theories. *)
Theory evalCompilerBytecodeDefs
Ancestors evalCompiler compileVyper concretizeMemLocDefs

Definition bytecode_unit_pipeline_for_testing_def:
  bytecode_unit_pipeline_for_testing rpolicy unit =
    case concretize_context_eval unit.cu_context of
      NONE => NONE
    | SOME ctx =>
        SOME <| po_unit := unit with cu_context := ctx;
                po_final_assembly := rpolicy.rpol_final_assembly |>
End

Definition bytecode_identity_finalizer_for_testing_def:
  bytecode_identity_finalizer_for_testing
    (rpolicy : resolved_compiler_policy) asm = SOME asm
End

Definition compile_vyper_o1_fuel_for_testing_def:
  compile_vyper_o1_fuel_for_testing fuel (tops : toplevel list) =
    compile_vyper_fuel_for_testing fuel
      bytecode_unit_pipeline_for_testing
      bytecode_identity_finalizer_for_testing
      (o1_policy prague_capabilities) tops
End

val _ = export_theory()
