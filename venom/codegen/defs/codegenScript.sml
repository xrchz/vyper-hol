(*
 * Top-Level Venom -> EVM Codegen
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Composes the three stages:
 *   1. Stack plan generation (Venom → stack_op list)
 *   2. Plan execution (stack_op list → asm_inst list)
 *   3. Assembly (asm_inst list → byte list)
 *
 * Data segment (selector tables, deploy code, CBOR metadata) is passed
 * separately and appended after the code assembly — it bypasses the
 * stack plan / plan executor stages.
 *
 * TOP-LEVEL:
 *   codegen — venom_context → (string, num) fmap → data_section list → byte list option
 *   codegen_fuel — bounded dataflow variant for evaluator use
 *)

Theory codegen
Ancestors
  symbolResolve

(* =========================================================================
   Full Pipeline
   ========================================================================= *)

Definition codegen_def:
  codegen (ctx : venom_context)
          (fn_eom_map : (string, num) fmap)
          (data_seg : data_section list) : byte list option =
    case generate_context_plan ctx of
      NONE => NONE
    | SOME plan =>
        let code_asm = execute_plan plan.cp_initial_fmp (context_plan_ops plan) in
        let data_asm = data_segment_asm data_seg in
        SOME (assemble (code_asm ++ data_asm))
End

Definition codegen_fuel_def:
  codegen_fuel fuel (ctx : venom_context)
               (fn_eom_map : (string, num) fmap)
               (data_seg : data_section list) : byte list option =
    case generate_context_plan_fuel fuel ctx of
      NONE => NONE
    | SOME plan =>
        let code_asm = execute_plan plan.cp_initial_fmp (context_plan_ops plan) in
        let data_asm = data_segment_asm data_seg in
        SOME (assemble (code_asm ++ data_asm))
End
