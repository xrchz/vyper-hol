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

Definition resolve_o1_policy_def:
  resolve_o1_policy policy =
    if target_capabilities_wf policy.cpol_target /\
       policy.cpol_target CapMcopy
    then SOME <|
      rpol_target := policy.cpol_target;
      rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Optimize
    |>
    else NONE
End

Theorem resolve_o1_policy_shape:
  resolve_o1_policy policy = SOME rpolicy ==>
  rpolicy.rpol_frontend_dispatch = Linear /\
  rpolicy.rpol_final_assembly = FAP_Optimize /\
  rpolicy.rpol_target = policy.cpol_target
Proof
  simp [resolve_o1_policy_def] >>
  strip_tac >>
  gvs []
QED

val _ = export_theory ();
