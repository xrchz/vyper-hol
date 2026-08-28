(*
 * Compiler-facing policy and atomic compilation-unit types.
 *)

Theory venomCompilerTypes
Ancestors
  venomInst

Datatype:
  resolved_compiler_policy = <|
    rpol_target : target_capabilities;
    rpol_frontend_dispatch : dispatch_strategy;
    rpol_final_assembly : final_assembly_policy
  |>
End

Datatype:
  compilation_unit = <|
    cu_context : venom_context;
    cu_data_segment : data_section list
  |>
End

Datatype:
  pipeline_output = <|
    po_unit : compilation_unit;
    po_final_assembly : final_assembly_policy
  |>
End

val _ = export_theory ();
