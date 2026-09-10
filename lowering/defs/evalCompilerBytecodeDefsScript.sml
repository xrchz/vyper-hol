(*
 * Closed compiler evaluation definitions.
 *
 * This theory fixes the testing profile used by evalCompilerLib: the formal
 * O1 IR pipeline for Prague, with final assembly optimization requested by the
 * policy but an identity finalizer so that only the formal pipeline executes.
 *)
Theory evalCompilerBytecodeDefs
Ancestors compileVyper

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

(* Successful planner computations are stable when their testing fuel is
   increased.  The ML evaluator uses this to prove a large-fuel call by
   computing it first at the smallest configured successful bound. *)
Theorem fn_plan_fuel_success_stable:
  (!fuel liveness dfg cfg fn worklist visited ps result extra.
    generate_fn_plan_aux_fuel fuel liveness dfg cfg fn worklist visited ps =
      SOME result ==>
    generate_fn_plan_aux_fuel (fuel + extra) liveness dfg cfg fn
      worklist visited ps = SOME result) /\
  (!fuel liveness dfg cfg fn ss sp succs visited ps result extra.
    generate_succs_plan_fuel fuel liveness dfg cfg fn ss sp succs visited ps =
      SOME result ==>
    generate_succs_plan_fuel (fuel + extra) liveness dfg cfg fn ss sp succs
      visited ps = SOME result)
Proof
  ho_match_mp_tac stackPlanGenTheory.generate_fn_plan_aux_fuel_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[Ntimes stackPlanGenTheory.generate_fn_plan_aux_fuel_def 2] >>
  rpt strip_tac >> BasicProvers.every_case_tac >> gvs[] >>
  simp[arithmeticTheory.ADD_CLAUSES,
       Once stackPlanGenTheory.generate_fn_plan_aux_fuel_def] >>
  metis_tac[]
QED

Theorem generate_fn_plan_aux_fuel_success_stable:
  !fuel liveness dfg cfg fn worklist visited ps result extra.
    generate_fn_plan_aux_fuel fuel liveness dfg cfg fn worklist visited ps =
      SOME result ==>
    generate_fn_plan_aux_fuel (fuel + extra) liveness dfg cfg fn
      worklist visited ps = SOME result
Proof
  metis_tac[fn_plan_fuel_success_stable]
QED

Theorem generate_succs_plan_fuel_success_stable:
  !fuel liveness dfg cfg fn ss sp succs visited ps result extra.
    generate_succs_plan_fuel fuel liveness dfg cfg fn ss sp succs visited ps =
      SOME result ==>
    generate_succs_plan_fuel (fuel + extra) liveness dfg cfg fn ss sp succs
      visited ps = SOME result
Proof
  metis_tac[fn_plan_fuel_success_stable]
QED
