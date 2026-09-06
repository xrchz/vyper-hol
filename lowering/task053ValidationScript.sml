(* Focused finalizer-boundary validation for TASK 053. *)

Theory task053Validation
Ancestors
  e2eDefs
Libs
  BasicProvers

Definition task053_opt_policy_def:
  task053_opt_policy =
    <| rpol_target := K T;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
End

Definition task053_replacing_finalizer_def:
  task053_replacing_finalizer rp asm = SOME [AsmOp "STOP"]
End

Theorem task053_optimized_finalizer_changes_program:
  finalizer_correct task053_opt_policy task053_replacing_finalizer /\
  task053_replacing_finalizer task053_opt_policy [] =
    SOME [AsmOp "STOP"] /\
  [AsmOp "STOP"] <> []
Proof
  simp[finalizer_correct_def, task053_opt_policy_def,
       task053_replacing_finalizer_def,
       asmTargetSafetyTheory.assembly_target_safe_def,
       asmTargetSafetyTheory.asm_inst_target_safe_def,
       asmTargetSafetyTheory.asm_opcode_target_supported_def,
       symbolResolveTheory.evm_opcode_byte_def,
       symbolResolveTheory.evm_opcode_table_def]
QED

val _ = export_theory ();
