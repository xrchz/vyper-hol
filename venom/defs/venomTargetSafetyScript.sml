(*
 * Shared target-capability checks for Venom source IR.
 *)

Theory venomTargetSafety
Ancestors
  venomInst

Definition opcode_target_supported_def:
  opcode_target_supported caps op <=>
    (op = MCOPY ==> caps CapMcopy) /\
    (MEM op [TLOAD; TSTORE] ==> caps CapTransientStorage) /\
    (MEM op [BLOBHASH; BLOBBASEFEE] ==> caps CapBlobOps)
End

Definition instruction_target_safe_def:
  instruction_target_safe caps inst <=>
    opcode_target_supported caps inst.inst_opcode
End

Definition basic_block_target_safe_def:
  basic_block_target_safe caps bb <=>
    EVERY (instruction_target_safe caps) bb.bb_instructions
End

Definition function_target_safe_def:
  function_target_safe caps fn <=>
    EVERY (basic_block_target_safe caps) fn.fn_blocks
End

Definition context_target_safe_def:
  context_target_safe caps ctx <=>
    EVERY (function_target_safe caps) ctx.ctx_functions
End

val _ = export_theory ();
