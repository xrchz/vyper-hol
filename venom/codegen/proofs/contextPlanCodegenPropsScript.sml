(*
 * Context planner failure exposed through the top-level codegen API.
 *)

Theory contextPlanCodegenProps
Ancestors
  contextPlanProps codegen

Theorem codegen_missing_eom:
  (?fn. MEM fn ctx.ctx_functions /\ fn.fn_eom = NONE) ==>
  codegen ctx fn_eom_map data_seg = NONE
Proof
  strip_tac >>
  `generate_context_plan ctx = NONE` by
    metis_tac[generate_context_plan_missing_eom] >>
  simp[codegen_def]
QED

val _ = export_theory();
