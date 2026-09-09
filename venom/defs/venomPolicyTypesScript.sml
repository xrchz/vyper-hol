(*
 * Pipeline-neutral compiler policy types.
 *
 * This theory deliberately sits above Venom IR and code generation.
 *)

Theory venomPolicyTypes

Datatype:
  dispatch_strategy = Linear | Sparse | Dense
End

Datatype:
  evm_capability = CapPush0 | CapMcopy | CapTransientStorage | CapBlobOps
End

Type target_capabilities = ``:evm_capability -> bool``

Definition target_capabilities_wf_def:
  target_capabilities_wf caps <=>
    (caps CapMcopy ==> caps CapPush0) /\
    (caps CapTransientStorage ==> caps CapPush0) /\
    (caps CapBlobOps ==> caps CapPush0)
End

Definition prague_capabilities_def:
  prague_capabilities = (K T : target_capabilities)
End

Datatype:
  final_assembly_policy = FAP_Preserve | FAP_Optimize
End

Datatype:
  compiler_policy = <| cpol_target : target_capabilities |>
End

Theorem prague_capabilities_wf:
  target_capabilities_wf prague_capabilities
Proof
  simp [target_capabilities_wf_def, prague_capabilities_def]
QED

val _ = export_theory ();
