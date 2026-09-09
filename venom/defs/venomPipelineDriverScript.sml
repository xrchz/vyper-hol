(*
 * Generic checked Venom pipeline interfaces and driver.
 *
 * The definitions in this theory are deliberately optimization-level neutral:
 * an optimization level contributes only a resolved policy and pipeline data.
 *)

Theory venomPipelineDriver
Ancestors
  venomPassSchedule
  venomCompilerTypes
  venomPolicyTypes
  venomPipelineRunner
  fcgPruning
  staticLayoutWf
  fmpWfDefs
  stackPlanGen
  venomTargetSafety
Definition pipeline_stage_tags_def:
  (pipeline_stage_tags [] = []) /\
  (pipeline_stage_tags (PS_MapFunctions pass::stages) =
     fn_pass_tag pass::pipeline_stage_tags stages) /\
  (pipeline_stage_tags (PS_DiscardAnalyses::stages) =
     pipeline_stage_tags stages)
End

Definition pipeline_spec_tags_def:
  pipeline_spec_tags spec =
    pipeline_stage_tags spec.ps_pre_walk_stages ++
    MAP fn_pass_tag spec.ps_fn_passes ++
    pipeline_stage_tags spec.ps_post_walk_stages
End

(* Every FMP lowering is guarded by an earlier DRET desugaring, even when the
 * two passes occur in different pipeline scopes.  The Boolean accumulator
 * records whether DRET has already occurred in the strict prefix. *)
Definition dret_before_fmp_aux_def:
  (dret_before_fmp_aux seen [] = T) /\
  (dret_before_fmp_aux seen (tag::tags) =
     if tag = VP_DretDesugar then dret_before_fmp_aux T tags
     else if tag = VP_FmpLowering then
       seen /\ dret_before_fmp_aux seen tags
     else dret_before_fmp_aux seen tags)
End

Definition dret_before_fmp_def:
  dret_before_fmp tags = dret_before_fmp_aux F tags
End

Definition pass_target_supported_def:
  pass_target_supported caps tag <=>
    case tag of
      VP_DretDesugar => caps CapMcopy
    | _ => T
End

Definition pipeline_stage_wf_def:
  pipeline_stage_wf stage <=>
    case stage of
      PS_MapFunctions pass => configured_fn_pass_wf pass
    | PS_DiscardAnalyses => T
End

Definition pipeline_spec_wf_def:
  pipeline_spec_wf rpolicy spec <=>
    target_capabilities_wf rpolicy.rpol_target /\
    rpolicy.rpol_final_assembly = spec.ps_final_assembly /\
    EVERY pipeline_stage_wf spec.ps_pre_walk_stages /\
    EVERY configured_fn_pass_wf spec.ps_fn_passes /\
    EVERY pipeline_stage_wf spec.ps_post_walk_stages /\
    valid_pass_order (MAP fn_pass_tag spec.ps_fn_passes) /\
    dret_before_fmp (pipeline_spec_tags spec) /\
    EVERY (pass_target_supported rpolicy.rpol_target)
          (pipeline_spec_tags spec)
End

(* Checked generic execution.  The call graph bound as [frozen_fcg] is used
 * both for pruning and for the callee-first name list; only the final safety
 * check recomputes analysis over the actual result. *)
Definition run_venom_pipeline_def:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy spec unit =
    if ~pipeline_spec_wf rpolicy spec then NONE
    else if ~unit_wf unit then NONE
    else if ~raw_static_inputs_wf unit.cu_context then NONE
    else if ~mem_ok unit.cu_context then NONE
    else if ~calling_ok unit.cu_context then NONE
    else
      case run_pipeline_stages rpolicy spec.ps_pre_walk_stages unit
             (init_ir_supply unit) of
        NONE => NONE
      | SOME (pre_unit,pre_supply) =>
          let frozen_fcg = fcg_analyze pre_unit.cu_context;
              walk_unit =
                if spec.ps_prune_unreachable then
                  prune_unit_fcg_unreachable pre_unit frozen_fcg
                else pre_unit
          in
            if spec.ps_require_acyclic_calls /\
               ~reachable_fcg_acyclic pre_unit.cu_context frozen_fcg
            then NONE
            else
              case pre_unit.cu_context.ctx_entry of
                NONE => NONE
              | SOME entry =>
                  case run_callee_first rpolicy spec.ps_fn_passes
                         (fcg_postorder frozen_fcg entry)
                         walk_unit pre_supply of
                    NONE => NONE
                  | SOME (walked_unit,walked_supply) =>
                      case run_pipeline_stages rpolicy
                             spec.ps_post_walk_stages
                             walked_unit walked_supply of
                        NONE => NONE
                      | SOME (final_unit,final_supply) =>
                          if unit_wf final_unit /\
                             unit_labels_wf final_unit /\
                             context_target_safe rpolicy.rpol_target
                               final_unit.cu_context /\
                             concretized_static_layouts_wf
                               final_unit.cu_context /\
                             fmp_lowered_context_wf final_unit.cu_context /\
                             mem_ok final_unit.cu_context /\
                             calling_ok final_unit.cu_context /\
                             post_ok final_unit.cu_context /\
                             reachable_fcg_acyclic final_unit.cu_context
                               (fcg_analyze final_unit.cu_context) /\
                             codegen_ready final_unit.cu_context
                          then SOME <|po_unit := final_unit;
                                      po_final_assembly :=
                                        spec.ps_final_assembly|>
                          else NONE
End

Definition o1_policy_def:
  o1_policy target = <|cpol_target := target|>
End

Definition o1_pipeline_def:
  o1_pipeline mem_ok calling_ok post_ok target unit =
    case resolve_o1_policy (o1_policy target) of
      NONE => NONE
    | SOME rpolicy =>
        run_venom_pipeline mem_ok calling_ok post_ok rpolicy
          o1_pipeline_spec unit
End

Theorem o1_pipeline_spec_wf_resolved:
  resolve_o1_policy policy = SOME rpolicy ==>
  pipeline_spec_wf rpolicy o1_pipeline_spec
Proof
  simp [resolve_o1_policy_def, pipeline_spec_wf_def,
        pipeline_stage_wf_def, pipeline_spec_tags_def,
        pipeline_stage_tags_def, o1_pipeline_spec_def,
        o1_fn_passes_def, fn_pass_tag_def, configured_fn_pass_wf_def,
        o1_fn_pass_order_valid, dret_before_fmp_def,
        dret_before_fmp_aux_def,
        pass_target_supported_def, target_capabilities_wf_def] >>
  strip_tac >>
  gvs [] >>
  EVAL_TAC
QED

val _ = export_theory ();
