(* Structural consequences of successful checked pipeline execution. *)

Theory venomPipelineDriverProps
Ancestors
  venomPipelineDriver

Theorem run_venom_pipeline_success_boundary:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out ==>
  out.po_final_assembly = spec.ps_final_assembly /\
  unit_wf out.po_unit /\
  unit_labels_wf out.po_unit /\
  context_target_safe rpolicy.rpol_target out.po_unit.cu_context /\
  concretized_static_layouts_wf out.po_unit.cu_context /\
  fmp_lowered_context_wf out.po_unit.cu_context /\
  mem_ok out.po_unit.cu_context /\
  calling_ok out.po_unit.cu_context /\
  post_ok out.po_unit.cu_context /\
  reachable_fcg_acyclic out.po_unit.cu_context
    (fcg_analyze out.po_unit.cu_context) /\
  codegen_ready out.po_unit.cu_context
Proof
  simp [run_venom_pipeline_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs []
QED

Theorem run_venom_pipeline_final_policy:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out ==>
  out.po_final_assembly = spec.ps_final_assembly
Proof
  metis_tac [run_venom_pipeline_success_boundary]
QED

Theorem run_venom_pipeline_success_unit_wf:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit = SOME out ==>
  unit_wf out.po_unit
Proof
  metis_tac [run_venom_pipeline_success_boundary]
QED

Theorem o1_pipeline_spec_wf:
  resolve_o1_policy (o1_policy target) = SOME rpolicy ==>
  pipeline_spec_wf rpolicy o1_pipeline_spec
Proof
  metis_tac [o1_pipeline_spec_wf_resolved]
QED

Theorem o1_pipeline_post_lowering:
  o1_pipeline mem_ok calling_ok post_ok target unit = SOME out /\
  (!c. post_ok c <=>
       fmp_lowered_context_wf c /\ codegen_ready c) ==>
  fmp_lowered_context_wf out.po_unit.cu_context /\
  codegen_ready out.po_unit.cu_context
Proof
  simp [o1_pipeline_def, AllCaseEqs()] >>
  metis_tac [run_venom_pipeline_success_boundary]
QED

Theorem o1_pipeline_no_level_control_flow:
  o1_pipeline mem_ok calling_ok post_ok target unit =
    case resolve_o1_policy <|cpol_target := target|> of
      NONE => NONE
    | SOME rpolicy =>
        run_venom_pipeline mem_ok calling_ok post_ok rpolicy
          o1_pipeline_spec unit
Proof
  simp [o1_pipeline_def, o1_policy_def]
QED

val _ = export_theory ();
