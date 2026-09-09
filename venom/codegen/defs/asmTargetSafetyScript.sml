(*
 * Target-capability and encodability checks for concrete assembly.
 *)

Theory asmTargetSafety
Ancestors
  symbolResolve
  venomTargetSafety

Definition asm_opcode_target_supported_def:
  asm_opcode_target_supported caps name <=>
    IS_SOME (evm_opcode_byte name) /\
    (name = "MCOPY" ==> caps CapMcopy) /\
    (MEM name ["TLOAD"; "TSTORE"] ==> caps CapTransientStorage) /\
    (MEM name ["BLOBHASH"; "BLOBBASEFEE"] ==> caps CapBlobOps) /\
    (name = "PUSH0" ==> caps CapPush0)
End

Definition asm_inst_target_safe_def:
  asm_inst_target_safe caps inst <=>
    case inst of
      AsmOp name => asm_opcode_target_supported caps name
    | AsmPush bytes =>
        if bytes = [] then caps CapPush0 else LENGTH bytes <= 32
    | _ => T
End

Definition assembly_target_safe_def:
  assembly_target_safe caps asm <=> EVERY (asm_inst_target_safe caps) asm
End

val _ = export_theory ();
