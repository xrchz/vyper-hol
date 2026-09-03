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
  simplifyCfgLabelProps
  dretDesugarProofs
  fmpLowerProps
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

Theorem pipeline_spec_wf_prague_probe:
  pipeline_spec_wf
    <|rpol_target := prague_capabilities;
      rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Optimize|>
    o1_pipeline_spec
Proof
  EVAL_TAC
QED

Theorem pipeline_spec_wf_bad_order_probe:
  ~pipeline_spec_wf
    <|rpol_target := prague_capabilities;
      rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Optimize|>
    (o1_pipeline_spec with
       ps_fn_passes := [CFP_Simple VP_DFT; CFP_Simple VP_MakeSSA])
Proof
  EVAL_TAC
QED

Theorem pipeline_spec_wf_unsupported_target_probe:
  ~pipeline_spec_wf
    <|rpol_target := (\cap. cap = CapPush0);
      rpol_frontend_dispatch := Linear;
      rpol_final_assembly := FAP_Optimize|>
    o1_pipeline_spec
Proof
  EVAL_TAC
QED

(* Closed end-to-end validation fixtures for the checked driver. *)
Definition task041_raw_function_def:
  task041_raw_function name id =
    mk_raw_function name
      [<|bb_label := "entry";
          bb_instructions := [mk_inst id RET [Lit 0w] []]|>]
End

Definition task041_raw_unit_def:
  task041_raw_unit = <|
    cu_context := mk_venom_context [task041_raw_function "main" 1]
      (SOME "main");
    cu_data_segment := []
  |>
End

Definition task041_dead_function_def:
  task041_dead_function =
    mk_raw_function "unreachable"
      [<|bb_label := "dead_entry";
          bb_instructions := [mk_inst 0 RET [Lit 0w] []]|>]
End

Definition task041_pruning_unit_def:
  task041_pruning_unit = <|
    cu_context := mk_venom_context
      [task041_raw_function "main" 1; task041_dead_function] (SOME "main");
    cu_data_segment := []
  |>
End

Definition task041_cycle_unit_def:
  task041_cycle_unit = <|
    cu_context := mk_venom_context
      [(mk_raw_function "loop"
        [<|bb_label := "entry";
            bb_instructions :=
              [mk_inst 1 INVOKE [Label "loop"] [];
               mk_inst 2 STOP [] []]|>])] (SOME "loop");
    cu_data_segment := []
  |>
End

Definition task041_bad_schedule_def:
  task041_bad_schedule =
    o1_pipeline_spec with
      ps_fn_passes := [CFP_Simple VP_DFT; CFP_Simple VP_MakeSSA]
End

Definition task041_pruning_spec_def:
  task041_pruning_spec = <|
    ps_pre_walk_stages := [];
    ps_fn_passes := CFP_Simple VP_DretDesugar :: o1_fn_passes;
    ps_prune_unreachable := T;
    ps_require_acyclic_calls := T;
    ps_post_walk_stages := [];
    ps_final_assembly := FAP_Optimize
  |>
End

Theorem task041_pruning_spec_wf:
  pipeline_spec_wf task039_policy task041_pruning_spec
Proof
  EVAL_TAC
QED

Theorem task041_schedule_evaluations:
  pipeline_spec_wf task039_policy o1_pipeline_spec /\
  run_venom_pipeline (K T) (K T) (K T) task039_policy
    task041_bad_schedule task041_raw_unit = NONE
Proof
  EVAL_TAC
QED

Theorem task041_unsupported_target_eval:
  o1_pipeline (K T) (K T) (K T) (\cap. cap = CapPush0)
    task041_raw_unit = NONE
Proof
  EVAL_TAC
QED

Definition task041_cycle_spec_def:
  task041_cycle_spec = <|
    ps_pre_walk_stages := [];
    ps_fn_passes := [];
    ps_prune_unreachable := F;
    ps_require_acyclic_calls := T;
    ps_post_walk_stages := [];
    ps_final_assembly := FAP_Optimize
  |>
End

Theorem task041_cycle_rejection_eval:
  run_venom_pipeline (K T) (K T) (K T) task039_policy
    task041_cycle_spec task041_cycle_unit = NONE
Proof
  EVAL_TAC
QED

Theorem task041_simplify_result:
  simplify_cfg_fn_with_labels (task041_raw_function "main" 1) =
    (task041_raw_function "main" 1,[])
Proof
  simp [task041_raw_function_def, simplify_cfg_single_ret_with_labels]
QED

Theorem task041_simplify_execute:
  execute_configured_fn_pass task039_policy
    (CFP_Simple VP_SimplifyCFG) task041_raw_unit
    (init_ir_supply task041_raw_unit) (task041_raw_function "main" 1) =
  SOME <|fpo_function := task041_raw_function "main" 1;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  simp [task041_raw_function_def, simplify_cfg_single_ret_with_labels]
QED

Theorem task041_raw_transaction_facts:
  ir_supply_covers_unit
    (init_ir_supply task041_raw_unit) task041_raw_unit /\
  fn_pass_effects_hold VP_SimplifyCFG
    (task041_raw_function "main" 1)
    <|fpo_function := task041_raw_function "main" 1;
      fpo_label_map := [];
      fpo_supply := init_ir_supply task041_raw_unit|> /\
  introduces_no_invoke_edges
    (task041_raw_function "main" 1) (task041_raw_function "main" 1) /\
  ir_supply_extends
    (init_ir_supply task041_raw_unit) (init_ir_supply task041_raw_unit) /\
  ir_supply_covers_fn
    (init_ir_supply task041_raw_unit) (task041_raw_function "main" 1) /\
  unit_labels_wf task041_raw_unit /\
  unit_global_inst_ids_distinct task041_raw_unit
Proof
  EVAL_TAC
QED

Theorem task041_raw_structure_facts:
  ctx_fn_names task041_raw_unit.cu_context = ["main"] /\
  lookup_unique_function "main" task041_raw_unit.cu_context.ctx_functions =
    SOME (task041_raw_function "main" 1) /\
  replace_unique_function "main" (task041_raw_function "main" 1)
    task041_raw_unit.cu_context.ctx_functions =
    SOME task041_raw_unit.cu_context.ctx_functions /\
  (task041_raw_unit with cu_context :=
     task041_raw_unit.cu_context with ctx_functions :=
       task041_raw_unit.cu_context.ctx_functions) = task041_raw_unit /\
  unit_with_current_fn task041_raw_unit
    (task041_raw_function "main" 1) = SOME task041_raw_unit /\
  apply_unit_label_map [] task041_raw_unit = SOME task041_raw_unit /\
  list_subset (unit_invoke_targets task041_raw_unit)
    (unit_invoke_targets task041_raw_unit)
Proof
  EVAL_TAC
QED

Theorem task041_simplify_transaction:
  run_configured_fn_passes execute_configured_fn_pass task039_policy
    [CFP_Simple VP_SimplifyCFG] "main" task041_raw_unit
    (init_ir_supply task041_raw_unit) =
  SOME (task041_raw_unit,init_ir_supply task041_raw_unit)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  pure_rewrite_tac [task041_raw_transaction_facts,
                    task041_raw_structure_facts] >>
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_simplify_execute] >>
  simp [fn_pass_tag_def, task041_simplify_result,
        task041_raw_transaction_facts, task041_raw_structure_facts,
        venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def]
QED

Theorem task041_simplify_mapped:
  run_pipeline_stage task039_policy
    (PS_MapFunctions (CFP_Simple VP_SimplifyCFG)) task041_raw_unit
    (init_ir_supply task041_raw_unit) =
  SOME (task041_raw_unit,init_ir_supply task041_raw_unit)
Proof
  simp [run_pipeline_stage_def, run_mapped_functions_def,
        run_named_fn_schedules_def, task041_raw_structure_facts,
        task041_simplify_transaction]
QED

Theorem task041_raw_no_dret:
  no_dret (task041_raw_function "main" 1)
Proof
  EVAL_TAC >> simp []
QED

Theorem task041_dret_execute:
  execute_configured_fn_pass task039_policy
    (CFP_Simple VP_DretDesugar) task041_raw_unit
    (init_ir_supply task041_raw_unit) (task041_raw_function "main" 1) =
  SOME <|fpo_function := task041_raw_function "main" 1;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  simp [dret_desugar_function_identity, task041_raw_no_dret]
QED

Theorem task041_dret_effect_fact:
  fn_pass_effects_hold VP_DretDesugar
    (task041_raw_function "main" 1)
    <|fpo_function := task041_raw_function "main" 1;
      fpo_label_map := [];
      fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  EVAL_TAC
QED

Theorem task041_dret_transaction:
  run_configured_fn_passes execute_configured_fn_pass task039_policy
    [CFP_Simple VP_DretDesugar] "main" task041_raw_unit
    (init_ir_supply task041_raw_unit) =
  SOME (task041_raw_unit,init_ir_supply task041_raw_unit)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  pure_rewrite_tac [task041_raw_transaction_facts,
                    task041_raw_structure_facts] >>
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_dret_execute] >>
  simp [fn_pass_tag_def, dret_desugar_function_identity,
        task041_raw_no_dret, task041_dret_effect_fact,
        task041_raw_transaction_facts, task041_raw_structure_facts,
        venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def]
QED

Theorem task041_dret_mapped:
  run_pipeline_stage task039_policy
    (PS_MapFunctions (CFP_Simple VP_DretDesugar)) task041_raw_unit
    (init_ir_supply task041_raw_unit) =
  SOME (task041_raw_unit,init_ir_supply task041_raw_unit)
Proof
  simp [run_pipeline_stage_def, run_mapped_functions_def,
        run_named_fn_schedules_def, task041_raw_structure_facts,
        task041_dret_transaction]
QED

Theorem task041_dret_mapped_functions:
  run_mapped_functions task039_policy (CFP_Simple VP_DretDesugar)
    task041_raw_unit (init_ir_supply task041_raw_unit) =
  SOME (task041_raw_unit,init_ir_supply task041_raw_unit)
Proof
  mp_tac task041_dret_mapped >> simp [run_pipeline_stage_def]
QED

Theorem task041_pre_walk:
  run_pipeline_stages task039_policy o1_pipeline_spec.ps_pre_walk_stages
    task041_raw_unit (init_ir_supply task041_raw_unit) =
  SOME (task041_raw_unit,init_ir_supply task041_raw_unit)
Proof
  simp [o1_pipeline_spec_def, run_pipeline_stages_def,
        run_pipeline_stage_def, task041_simplify_mapped,
        task041_dret_mapped, task041_dret_mapped_functions]
QED

Theorem task041_make_ssa_result:
  make_ssa_current_fn (init_ir_supply task041_raw_unit)
    (task041_raw_function "main" 1) =
  (task041_raw_function "main" 1,init_ir_supply task041_raw_unit)
Proof
  EVAL_TAC
QED

Theorem task041_lower_dload_result:
  lower_dload_function_supply (init_ir_supply task041_raw_unit)
    (task041_raw_function "main" 1) =
  (task041_raw_function "main" 1,init_ir_supply task041_raw_unit)
Proof
  EVAL_TAC
QED

Definition task041_concretized_function_def:
  task041_concretized_function =
    (task041_raw_function "main" 1) with fn_eom := SOME 0
End

Theorem task041_concretize_result:
  concretize_function_eval [] (task041_raw_function "main" 1) =
  SOME task041_concretized_function
Proof
  EVAL_TAC
QED

Definition task041_concretized_observation_def:
  task041_concretized_observation =
    task041_raw_unit with cu_context :=
      task041_raw_unit.cu_context with ctx_functions :=
        [task041_concretized_function]
End

Theorem task041_concretized_observation_result:
  unit_with_current_fn task041_raw_unit task041_concretized_function =
  SOME task041_concretized_observation /\
  lookup_unique_function "main"
    task041_concretized_observation.cu_context.ctx_functions =
  SOME task041_concretized_function
Proof
  EVAL_TAC
QED

Definition task041_fmp_function_def:
  task041_fmp_function =
    task041_concretized_function with fn_fmp_signature :=
      SOME <|fms_has_fmp_param := F; fms_publishes := F|>
End

Definition task041_fmp_infos_def:
  task041_fmp_infos =
    FEMPTY |+ ("main",fmp_info_bottom)
End

Definition task041_fmp_states_def:
  task041_fmp_states = THE (fmp_reclaim_states task041_concretized_function)
End

Theorem task041_fmp_analysis_result:
  analyze_fmp_context task041_concretized_observation.cu_context =
  SOME task041_fmp_infos
Proof
  EVAL_TAC
QED

Theorem task041_fmp_info_valid:
  fmp_info_valid task041_concretized_observation.cu_context task041_fmp_infos
Proof
  irule fmpAnalysisPropsTheory.analyze_fmp_context_valid >>
  ACCEPT_TAC task041_fmp_analysis_result
QED

Theorem task041_fmp_lower_input:
  fmp_lower_input task041_fmp_infos
    task041_concretized_observation.cu_context task041_concretized_function
Proof
  EVAL_TAC
QED

Theorem task041_fmp_function_wf:
  wf_function task041_concretized_function /\
  fn_inst_wf task041_concretized_function
Proof
  EVAL_TAC >>
  simp [listTheory.REV_DEF, venomInstTheory.is_terminator_def,
        venomStateTheory.get_label_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs []
QED

Theorem task041_fmp_states_result:
  fmp_reclaim_states task041_concretized_function =
  SOME task041_fmp_states
Proof
  EVAL_TAC
QED

Theorem task041_fmp_candidate_empty:
  fmp_candidate_plan task041_fmp_infos
    task041_concretized_observation.cu_context task041_concretized_function
    task041_fmp_states = FEMPTY
Proof
  EVAL_TAC >>
  simp [finite_mapTheory.FLOOKUP_FUNION,
        finite_mapTheory.FLOOKUP_UPDATE,
        fmpReclaimDefsTheory.fmp_plan_of_list_def]
QED

Theorem task041_fmp_reclaim_result:
  analyze_fmp_reclaims task041_fmp_infos
    task041_concretized_observation.cu_context task041_concretized_function =
  SOME FEMPTY
Proof
  irule fmpReclaimPropsTheory.analyze_fmp_reclaims_ready >>
  simp [task041_fmp_info_valid, task041_fmp_function_wf,
        task041_fmp_states_result, task041_fmp_candidate_empty,
        fmpReclaimDefsTheory.fmp_reclaim_plan_ok_def] >>
  EVAL_TAC
QED

Theorem task041_fmp_pre_seal_facts:
  task041_concretized_function.fn_fmp_signature = NONE /\
  FLOOKUP task041_fmp_infos task041_concretized_function.fn_name =
    SOME fmp_info_bottom /\
  fmp_reclaim_input task041_concretized_function FEMPTY
Proof
  EVAL_TAC >>
  simp [fmpLowerDefsTheory.fmp_reclaim_input_def]
QED

Theorem task041_fmp_checked_seal_result:
  fmp_checked_seal task041_concretized_observation.cu_context
    task041_concretized_function
    <|fi_needs_fmp := F; fi_publishes_fmp := F|>
    task041_concretized_function.fn_blocks = SOME task041_fmp_function
Proof
  EVAL_TAC
QED

Theorem task041_fmp_after_concretize_result:
  fmp_lower_function task041_concretized_observation.cu_context
    (init_ir_supply task041_raw_unit) task041_concretized_function =
  SOME (task041_fmp_function,init_ir_supply task041_raw_unit)
Proof
  rewrite_tac [fmpLowerDefsTheory.fmp_lower_function_def,
               task041_fmp_analysis_result] >>
  simp [fmpLowerDefsTheory.fmp_lower_function_with_info_def,
        task041_fmp_info_valid, task041_fmp_lower_input,
        task041_fmp_reclaim_result, task041_fmp_pre_seal_facts,
        task041_fmp_checked_seal_result,
        fmpAnalysisDefsTheory.fmp_info_bottom_def]
QED

Definition task041_fmp_observation_def:
  task041_fmp_observation =
    task041_raw_unit with cu_context :=
      task041_raw_unit.cu_context with ctx_functions := [task041_fmp_function]
End

Theorem task041_fmp_observation_result:
  unit_with_current_fn task041_raw_unit task041_fmp_function =
  SOME task041_fmp_observation
Proof
  EVAL_TAC
QED

Theorem task041_fmp_make_ssa_result:
  make_ssa_current_fn (init_ir_supply task041_raw_unit) task041_fmp_function =
    (task041_fmp_function,init_ir_supply task041_raw_unit)
Proof
  EVAL_TAC
QED

Theorem task041_fmp_after_concretize_result_any:
  !s. fmp_lower_function task041_concretized_observation.cu_context s
        task041_concretized_function = SOME (task041_fmp_function,s)
Proof
  gen_tac >>
  rewrite_tac [fmpLowerDefsTheory.fmp_lower_function_def,
               task041_fmp_analysis_result] >>
  simp [fmpLowerDefsTheory.fmp_lower_function_with_info_def,
        task041_fmp_info_valid, task041_fmp_lower_input,
        task041_fmp_reclaim_result, task041_fmp_pre_seal_facts,
        task041_fmp_checked_seal_result,
        fmpAnalysisDefsTheory.fmp_info_bottom_def]
QED

Theorem task041_supply_preserving_pass_results:
  (!s. make_ssa_current_fn s (task041_raw_function "main" 1) =
       (task041_raw_function "main" 1,s)) /\
  (!s. lower_dload_function_supply s (task041_raw_function "main" 1) =
       (task041_raw_function "main" 1,s)) /\
  (!s. make_ssa_current_fn s task041_fmp_function =
       (task041_fmp_function,s))
Proof
  EVAL_TAC >> simp []
QED

Definition task041_sue_function_def:
  task041_sue_function =
    task041_fmp_function with fn_blocks :=
      [<|bb_label := "entry";
         bb_instructions :=
           [mk_inst 2 ASSIGN [Lit 0w] ["formal_var_0"];
            mk_inst 1 RET [Var "formal_var_0"] []]|>]
End

Definition task041_sue_supply_def:
  task041_sue_supply =
    init_ir_supply task041_raw_unit with <|
      irs_next_inst := 3;
      irs_next_var := 1;
      irs_used_inst_ids := [2;1];
      irs_used_vars := ["formal_var_0"]
    |>
End

Definition task041_pruning_sue_supply_def:
  task041_pruning_sue_supply =
    init_ir_supply task041_pruning_unit with <|
      irs_next_inst := 3;
      irs_next_var := 1;
      irs_used_inst_ids := [2;1;0];
      irs_used_vars := ["formal_var_0"]
    |>
End

Theorem task041_pruning_fmp_sue_result:
  sue_expand_function_supply (init_ir_supply task041_pruning_unit)
    task041_fmp_function =
  (task041_sue_function,task041_pruning_sue_supply)
Proof
  EVAL_TAC
QED

Theorem task041_fmp_sue_result:
  sue_expand_function_supply (init_ir_supply task041_raw_unit)
    task041_fmp_function = (task041_sue_function,task041_sue_supply)
Proof
  EVAL_TAC
QED

Theorem task041_sue_dft_result:
  dft_fn task041_sue_function = task041_sue_function
Proof
  EVAL_TAC
QED

Theorem task041_sue_cfg_norm_result:
  cfg_norm_function_supply task041_sue_supply task041_sue_function =
    (task041_sue_function,task041_sue_supply)
Proof
  EVAL_TAC
QED

Theorem task041_fmp_function_blocks:
  task041_fmp_function.fn_blocks =
    [<|bb_label := "entry";
       bb_instructions := [mk_inst 1 RET [Lit 0w] []]|>]
Proof
  EVAL_TAC
QED

Theorem task041_fmp_function_blocks_update:
  (task041_fmp_function with fn_blocks :=
    [<|bb_label := "entry";
       bb_instructions := [mk_inst 1 RET [Lit 0w] []]|>]) =
  task041_fmp_function
Proof
  EVAL_TAC
QED
Theorem task041_fmp_simplify_result:
  simplify_cfg_fn_with_labels task041_fmp_function =
    (task041_fmp_function,[])
Proof
  qspecl_then [`task041_fmp_function`,`"entry"`,`1`] mp_tac
    simplify_cfg_single_ret_updated_with_labels >>
  simp [task041_fmp_function_blocks_update]
QED


Definition task041_sue_observation_def:
  task041_sue_observation =
    task041_raw_unit with cu_context :=
      task041_raw_unit.cu_context with ctx_functions := [task041_sue_function]
End

Theorem task041_sue_observation_result:
  unit_with_current_fn task041_raw_unit task041_sue_function =
  SOME task041_sue_observation
Proof
  EVAL_TAC
QED

Theorem task041_walk_make_ssa_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_MakeSSA)
    task041_raw_unit (init_ir_supply task041_raw_unit)
    (task041_raw_function "main" 1) =
  SOME <|fpo_function := task041_raw_function "main" 1;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  simp [task041_make_ssa_result]
QED

Theorem task041_walk_lower_dload_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_LowerDload)
    task041_raw_unit (init_ir_supply task041_raw_unit)
    (task041_raw_function "main" 1) =
  SOME <|fpo_function := task041_raw_function "main" 1;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  simp [task041_lower_dload_result]
QED

Theorem task041_raw_reserved:
  task041_raw_unit.cu_context.ctx_global_reserved = []
Proof
  EVAL_TAC
QED

Theorem task041_walk_concretize_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_ConcretizeMemLoc)
    task041_raw_unit (init_ir_supply task041_raw_unit)
    (task041_raw_function "main" 1) =
  SOME <|fpo_function := task041_concretized_function;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  simp [task041_raw_reserved, task041_concretize_result]
QED

Theorem task041_walk_fmp_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_FmpLowering)
    task041_concretized_observation (init_ir_supply task041_raw_unit)
    task041_concretized_function =
  SOME <|fpo_function := task041_fmp_function;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  simp [task041_fmp_after_concretize_result]
QED

Theorem task041_walk_second_make_ssa_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_MakeSSA)
    task041_fmp_observation (init_ir_supply task041_raw_unit)
    task041_fmp_function =
  SOME <|fpo_function := task041_fmp_function;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  simp [task041_fmp_make_ssa_result]
QED

Theorem task041_walk_simplify_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_SimplifyCFG)
    task041_fmp_observation (init_ir_supply task041_raw_unit)
    task041_fmp_function =
  SOME <|fpo_function := task041_fmp_function;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_raw_unit|>
Proof
  simp [task041_fmp_simplify_result]
QED

Theorem task041_walk_sue_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_SingleUseExpansion)
    task041_fmp_observation (init_ir_supply task041_raw_unit)
    task041_fmp_function =
  SOME <|fpo_function := task041_sue_function;
         fpo_label_map := [];
         fpo_supply := task041_sue_supply|>
Proof
  simp [task041_fmp_sue_result]
QED

Theorem task041_walk_dft_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_DFT)
    task041_sue_observation task041_sue_supply task041_sue_function =
  SOME <|fpo_function := task041_sue_function;
         fpo_label_map := [];
         fpo_supply := task041_sue_supply|>
Proof
  simp [task041_sue_dft_result]
QED

Theorem task041_walk_cfg_norm_execute:
  execute_configured_fn_pass task039_policy (CFP_Simple VP_CFGNormalization)
    task041_sue_observation task041_sue_supply task041_sue_function =
  SOME <|fpo_function := task041_sue_function;
         fpo_label_map := [];
         fpo_supply := task041_sue_supply|>
Proof
  simp [task041_sue_cfg_norm_result]
QED



Theorem task041_walk_make_ssa_guard:
  let out = <|fpo_function := task041_raw_function "main" 1;
               fpo_label_map := [];
               fpo_supply := init_ir_supply task041_raw_unit|> in
    out.fpo_function.fn_name = (task041_raw_function "main" 1).fn_name /\
    fn_pass_effects_hold VP_MakeSSA (task041_raw_function "main" 1) out /\
    introduces_no_invoke_edges (task041_raw_function "main" 1) out.fpo_function /\
    ir_supply_extends (init_ir_supply task041_raw_unit) out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_raw_unit
Proof
  EVAL_TAC
QED

Theorem task041_walk_lower_dload_guard:
  let out = <|fpo_function := task041_raw_function "main" 1;
               fpo_label_map := [];
               fpo_supply := init_ir_supply task041_raw_unit|> in
    out.fpo_function.fn_name = (task041_raw_function "main" 1).fn_name /\
    fn_pass_effects_hold VP_LowerDload (task041_raw_function "main" 1) out /\
    introduces_no_invoke_edges (task041_raw_function "main" 1) out.fpo_function /\
    ir_supply_extends (init_ir_supply task041_raw_unit) out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_raw_unit
Proof
  EVAL_TAC
QED

Theorem task041_walk_concretize_guard:
  let out = <|fpo_function := task041_concretized_function;
               fpo_label_map := [];
               fpo_supply := init_ir_supply task041_raw_unit|> in
    out.fpo_function.fn_name = (task041_raw_function "main" 1).fn_name /\
    fn_pass_effects_hold VP_ConcretizeMemLoc (task041_raw_function "main" 1) out /\
    introduces_no_invoke_edges (task041_raw_function "main" 1) out.fpo_function /\
    ir_supply_extends (init_ir_supply task041_raw_unit) out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_raw_unit
Proof
  EVAL_TAC
QED

Theorem task041_walk_fmp_guard:
  let out = <|fpo_function := task041_fmp_function;
               fpo_label_map := [];
               fpo_supply := init_ir_supply task041_raw_unit|> in
    out.fpo_function.fn_name = task041_concretized_function.fn_name /\
    fn_pass_effects_hold VP_FmpLowering task041_concretized_function out /\
    introduces_no_invoke_edges task041_concretized_function out.fpo_function /\
    ir_supply_extends (init_ir_supply task041_raw_unit) out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_concretized_observation
Proof
  EVAL_TAC
QED

Theorem task041_walk_second_make_ssa_guard:
  let out = <|fpo_function := task041_fmp_function;
               fpo_label_map := [];
               fpo_supply := init_ir_supply task041_raw_unit|> in
    out.fpo_function.fn_name = task041_fmp_function.fn_name /\
    fn_pass_effects_hold VP_MakeSSA task041_fmp_function out /\
    introduces_no_invoke_edges task041_fmp_function out.fpo_function /\
    ir_supply_extends (init_ir_supply task041_raw_unit) out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_fmp_observation
Proof
  EVAL_TAC
QED

Theorem task041_walk_simplify_guard:
  let out = <|fpo_function := task041_fmp_function;
               fpo_label_map := [];
               fpo_supply := init_ir_supply task041_raw_unit|> in
    out.fpo_function.fn_name = task041_fmp_function.fn_name /\
    fn_pass_effects_hold VP_SimplifyCFG task041_fmp_function out /\
    introduces_no_invoke_edges task041_fmp_function out.fpo_function /\
    ir_supply_extends (init_ir_supply task041_raw_unit) out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_fmp_observation
Proof
  EVAL_TAC
QED

Theorem task041_walk_sue_guard:
  let out = <|fpo_function := task041_sue_function;
               fpo_label_map := [];
               fpo_supply := task041_sue_supply|> in
    out.fpo_function.fn_name = task041_fmp_function.fn_name /\
    fn_pass_effects_hold VP_SingleUseExpansion task041_fmp_function out /\
    introduces_no_invoke_edges task041_fmp_function out.fpo_function /\
    ir_supply_extends (init_ir_supply task041_raw_unit) out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_fmp_observation
Proof
  EVAL_TAC
QED

Theorem task041_walk_dft_guard:
  let out = <|fpo_function := task041_sue_function;
               fpo_label_map := [];
               fpo_supply := task041_sue_supply|> in
    out.fpo_function.fn_name = task041_sue_function.fn_name /\
    fn_pass_effects_hold VP_DFT task041_sue_function out /\
    introduces_no_invoke_edges task041_sue_function out.fpo_function /\
    ir_supply_extends task041_sue_supply out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_sue_observation
Proof
  EVAL_TAC
QED

Theorem task041_walk_cfg_norm_guard:
  let out = <|fpo_function := task041_sue_function;
               fpo_label_map := [];
               fpo_supply := task041_sue_supply|> in
    out.fpo_function.fn_name = task041_sue_function.fn_name /\
    fn_pass_effects_hold VP_CFGNormalization task041_sue_function out /\
    introduces_no_invoke_edges task041_sue_function out.fpo_function /\
    ir_supply_extends task041_sue_supply out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply task041_sue_observation
Proof
  EVAL_TAC
QED


Theorem task041_fold_cfg_norm:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_CFGNormalization] task041_raw_unit task041_sue_supply
    task041_sue_function [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_sue_observation_result] >>
  simp [task041_sue_cfg_norm_result, fn_pass_tag_def,
        venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  mp_tac task041_walk_cfg_norm_guard >> simp []
QED


Theorem task041_fold_dft:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    task041_raw_unit task041_sue_supply task041_sue_function [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_sue_observation_result] >>
  simp [task041_sue_dft_result, fn_pass_tag_def, task041_fold_cfg_norm] >>
  mp_tac task041_walk_dft_guard >> simp []
QED

Theorem task041_fold_sue:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_raw_unit)
    task041_fmp_function [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_fmp_observation_result] >>
  simp [task041_fmp_sue_result, fn_pass_tag_def, task041_fold_dft] >>
  mp_tac task041_walk_sue_guard >> simp []
QED

Theorem task041_fold_simplify:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_SimplifyCFG; CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_raw_unit)
    task041_fmp_function [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_fmp_observation_result] >>
  simp [task041_fmp_simplify_result, fn_pass_tag_def, task041_fold_sue] >>
  mp_tac task041_walk_simplify_guard >> simp []
QED

Theorem task041_fold_second_make_ssa:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_raw_unit)
    task041_fmp_function [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_fmp_observation_result] >>
  simp [task041_fmp_make_ssa_result, fn_pass_tag_def,
        task041_fold_simplify] >>
  mp_tac task041_walk_second_make_ssa_guard >> simp []
QED

Theorem task041_fold_fmp:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_FmpLowering; CFP_Simple VP_MakeSSA;
     CFP_Simple VP_SimplifyCFG; CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_raw_unit)
    task041_concretized_function [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [CONJUNCT1 task041_concretized_observation_result] >>
  simp [task041_fmp_after_concretize_result, fn_pass_tag_def,
        task041_fold_second_make_ssa] >>
  mp_tac task041_walk_fmp_guard >> simp []
QED

Theorem task041_fold_concretize:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_ConcretizeMemLoc; CFP_Simple VP_FmpLowering;
     CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_raw_unit)
    (task041_raw_function "main" 1) [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [cj 5 task041_raw_structure_facts] >>
  simp [task041_raw_reserved, task041_concretize_result, fn_pass_tag_def,
        task041_fold_fmp] >>
  mp_tac task041_walk_concretize_guard >> simp []
QED

Theorem task041_fold_lower_dload:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_LowerDload; CFP_Simple VP_ConcretizeMemLoc;
     CFP_Simple VP_FmpLowering; CFP_Simple VP_MakeSSA;
     CFP_Simple VP_SimplifyCFG; CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_raw_unit)
    (task041_raw_function "main" 1) [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [cj 5 task041_raw_structure_facts] >>
  simp [task041_lower_dload_result, fn_pass_tag_def,
        task041_fold_concretize] >>
  mp_tac task041_walk_lower_dload_guard >> simp []
QED

Theorem task041_o1_fold:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    o1_fn_passes task041_raw_unit (init_ir_supply task041_raw_unit)
    (task041_raw_function "main" 1) [] =
  SOME (task041_sue_function,[],task041_sue_supply)
Proof
  rewrite_tac [o1_fn_passes_def] >>
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [cj 5 task041_raw_structure_facts] >>
  simp [task041_make_ssa_result, fn_pass_tag_def,
        task041_fold_lower_dload] >>
  mp_tac task041_walk_make_ssa_guard >> simp []
QED



Theorem task041_pruning_sue_cfg_norm_result:
  cfg_norm_function_supply task041_pruning_sue_supply task041_sue_function =
    (task041_sue_function,task041_pruning_sue_supply)
Proof
  EVAL_TAC
QED

Theorem task041_pruning_fold_cfg_norm:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_CFGNormalization] task041_raw_unit
    task041_pruning_sue_supply task041_sue_function [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_sue_observation_result] >>
  simp [task041_pruning_sue_cfg_norm_result, fn_pass_tag_def,
        venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  EVAL_TAC
QED

Theorem task041_pruning_fold_dft:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    task041_raw_unit task041_pruning_sue_supply task041_sue_function [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_sue_observation_result] >>
  simp [task041_sue_dft_result, fn_pass_tag_def,
        task041_pruning_fold_cfg_norm] >>
  EVAL_TAC
QED

Theorem task041_pruning_fold_sue:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_pruning_unit)
    task041_fmp_function [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_fmp_observation_result] >>
  simp [task041_pruning_fmp_sue_result, fn_pass_tag_def,
        task041_pruning_fold_dft] >>
  EVAL_TAC
QED

Theorem task041_pruning_fold_simplify:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_SimplifyCFG; CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_pruning_unit)
    task041_fmp_function [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_fmp_observation_result] >>
  simp [task041_fmp_simplify_result, fn_pass_tag_def,
        task041_pruning_fold_sue] >>
  EVAL_TAC
QED

Theorem task041_pruning_fold_second_make_ssa:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_pruning_unit)
    task041_fmp_function [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [task041_fmp_observation_result] >>
  simp [cj 3 task041_supply_preserving_pass_results, fn_pass_tag_def,
        task041_pruning_fold_simplify] >>
  EVAL_TAC
QED

Theorem task041_pruning_fold_fmp:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_FmpLowering; CFP_Simple VP_MakeSSA;
     CFP_Simple VP_SimplifyCFG; CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_pruning_unit)
    task041_concretized_function [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [CONJUNCT1 task041_concretized_observation_result] >>
  simp [task041_fmp_after_concretize_result_any, fn_pass_tag_def,
        task041_pruning_fold_second_make_ssa] >>
  EVAL_TAC
QED

Theorem task041_pruning_fold_concretize:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_ConcretizeMemLoc; CFP_Simple VP_FmpLowering;
     CFP_Simple VP_MakeSSA; CFP_Simple VP_SimplifyCFG;
     CFP_Simple VP_SingleUseExpansion; CFP_Simple VP_DFT;
     CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_pruning_unit)
    (task041_raw_function "main" 1) [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [cj 5 task041_raw_structure_facts] >>
  simp [task041_raw_reserved, task041_concretize_result, fn_pass_tag_def,
        task041_pruning_fold_fmp] >>
  EVAL_TAC
QED

Theorem task041_pruning_fold_lower_dload:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    [CFP_Simple VP_LowerDload; CFP_Simple VP_ConcretizeMemLoc;
     CFP_Simple VP_FmpLowering; CFP_Simple VP_MakeSSA;
     CFP_Simple VP_SimplifyCFG; CFP_Simple VP_SingleUseExpansion;
     CFP_Simple VP_DFT; CFP_Simple VP_CFGNormalization]
    task041_raw_unit (init_ir_supply task041_pruning_unit)
    (task041_raw_function "main" 1) [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [cj 5 task041_raw_structure_facts] >>
  simp [cj 2 task041_supply_preserving_pass_results, fn_pass_tag_def,
        task041_pruning_fold_concretize] >>
  EVAL_TAC
QED

Theorem task041_pruning_o1_fold:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    o1_fn_passes task041_raw_unit (init_ir_supply task041_pruning_unit)
    (task041_raw_function "main" 1) [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  rewrite_tac [o1_fn_passes_def] >>
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [cj 5 task041_raw_structure_facts] >>
  simp [cj 1 task041_supply_preserving_pass_results, fn_pass_tag_def,
        task041_pruning_fold_lower_dload] >>
  EVAL_TAC
QED

Theorem task041_pruning_dret_execute:
  execute_configured_fn_pass task039_policy
    (CFP_Simple VP_DretDesugar) task041_raw_unit
    (init_ir_supply task041_pruning_unit) (task041_raw_function "main" 1) =
  SOME <|fpo_function := task041_raw_function "main" 1;
         fpo_label_map := [];
         fpo_supply := init_ir_supply task041_pruning_unit|>
Proof
  simp [dret_desugar_function_identity, task041_raw_no_dret]
QED

Theorem task041_pruning_dret_guard_facts:
  fn_pass_effects_hold VP_DretDesugar (task041_raw_function "main" 1)
    <|fpo_function := task041_raw_function "main" 1;
      fpo_label_map := [];
      fpo_supply := init_ir_supply task041_pruning_unit|> /\
  introduces_no_invoke_edges (task041_raw_function "main" 1)
    (task041_raw_function "main" 1) /\
  ir_supply_extends (init_ir_supply task041_pruning_unit)
    (init_ir_supply task041_pruning_unit) /\
  ir_supply_covers_fn (init_ir_supply task041_pruning_unit)
    (task041_raw_function "main" 1) /\
  ir_supply_covers_unit (init_ir_supply task041_pruning_unit)
    task041_raw_unit
Proof
  EVAL_TAC
QED

Theorem task041_pruning_schedule_fold:
  run_configured_fn_pass_fold execute_configured_fn_pass task039_policy
    (CFP_Simple VP_DretDesugar :: o1_fn_passes) task041_raw_unit
    (init_ir_supply task041_pruning_unit)
    (task041_raw_function "main" 1) [] =
  SOME (task041_sue_function,[],task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  pure_once_rewrite_tac [cj 5 task041_raw_structure_facts] >>
  SIMP_TAC pure_ss [] >>
  once_rewrite_tac [task041_pruning_dret_execute] >>
  simp [fn_pass_tag_def, dret_desugar_function_identity,
        task041_raw_no_dret, task041_pruning_dret_guard_facts,
        task041_pruning_o1_fold]
QED

Definition task041_walked_unit_def:
  task041_walked_unit =
    task041_raw_unit with cu_context :=
      task041_raw_unit.cu_context with ctx_functions := [task041_sue_function]
End

Theorem task041_walked_transaction_facts:
  replace_unique_function "main" task041_sue_function
    task041_raw_unit.cu_context.ctx_functions = SOME [task041_sue_function] /\
  (task041_raw_unit with cu_context :=
     task041_raw_unit.cu_context with ctx_functions := [task041_sue_function]) =
    task041_walked_unit /\
  apply_unit_label_map [] task041_walked_unit = SOME task041_walked_unit /\
  unit_labels_wf task041_walked_unit /\
  list_subset (unit_invoke_targets task041_walked_unit)
    (unit_invoke_targets task041_raw_unit) /\
  ir_supply_covers_unit task041_sue_supply task041_walked_unit /\
  unit_global_inst_ids_distinct task041_walked_unit
Proof
  EVAL_TAC
QED

Theorem task041_o1_function_transaction:
  run_configured_fn_passes execute_configured_fn_pass task039_policy
    o1_fn_passes "main" task041_raw_unit (init_ir_supply task041_raw_unit) =
  SOME (task041_walked_unit,task041_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  pure_rewrite_tac [task041_raw_transaction_facts,
                    task041_raw_structure_facts] >>
  simp [task041_o1_fold, task041_walked_transaction_facts]
QED


Theorem task041_pruning_walked_transaction_facts:
  ir_supply_covers_unit (init_ir_supply task041_pruning_unit)
    task041_raw_unit /\
  replace_unique_function "main" task041_sue_function
    task041_raw_unit.cu_context.ctx_functions = SOME [task041_sue_function] /\
  (task041_raw_unit with cu_context :=
     task041_raw_unit.cu_context with ctx_functions := [task041_sue_function]) =
    task041_walked_unit /\
  apply_unit_label_map [] task041_walked_unit = SOME task041_walked_unit /\
  unit_labels_wf task041_walked_unit /\
  list_subset (unit_invoke_targets task041_walked_unit)
    (unit_invoke_targets task041_raw_unit) /\
  ir_supply_covers_unit task041_pruning_sue_supply task041_walked_unit /\
  unit_global_inst_ids_distinct task041_walked_unit
Proof
  EVAL_TAC
QED

Theorem task041_pruning_o1_function_transaction:
  run_configured_fn_passes execute_configured_fn_pass task039_policy
    o1_fn_passes "main" task041_raw_unit
    (init_ir_supply task041_pruning_unit) =
  SOME (task041_walked_unit,task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  pure_rewrite_tac [task041_pruning_walked_transaction_facts,
                    task041_raw_structure_facts] >>
  simp [task041_pruning_o1_fold,
        task041_pruning_walked_transaction_facts]
QED

Theorem task041_pruning_schedule_function_transaction:
  run_configured_fn_passes execute_configured_fn_pass task039_policy
    task041_pruning_spec.ps_fn_passes "main" task041_raw_unit
    (init_ir_supply task041_pruning_unit) =
  SOME (task041_walked_unit,task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  pure_rewrite_tac [task041_pruning_walked_transaction_facts,
                    task041_raw_structure_facts] >>
  simp [task041_pruning_spec_def, task041_pruning_schedule_fold,
        task041_pruning_walked_transaction_facts]
QED

Theorem task041_pruning_supply_differs:
  init_ir_supply task041_pruning_unit <> init_ir_supply task041_raw_unit
Proof
  EVAL_TAC
QED

Theorem task041_dead_simplify_result:
  simplify_cfg_fn_with_labels task041_dead_function =
    (task041_dead_function,[])
Proof
  simp [task041_dead_function_def, simplify_cfg_single_ret_with_labels]
QED


Theorem task041_pruning_structure_facts:
  ctx_fn_names task041_pruning_unit.cu_context = ["main";"unreachable"] /\
  lookup_unique_function "main"
    task041_pruning_unit.cu_context.ctx_functions =
      SOME (task041_raw_function "main" 1) /\
  lookup_unique_function "unreachable"
    task041_pruning_unit.cu_context.ctx_functions = SOME task041_dead_function /\
  unit_with_current_fn task041_pruning_unit
    (task041_raw_function "main" 1) = SOME task041_pruning_unit /\
  unit_with_current_fn task041_pruning_unit task041_dead_function =
    SOME task041_pruning_unit /\
  apply_unit_label_map [] task041_pruning_unit = SOME task041_pruning_unit /\
  list_subset (unit_invoke_targets task041_pruning_unit)
    (unit_invoke_targets task041_pruning_unit)
Proof
  EVAL_TAC
QED

Theorem task041_pruning_transaction_facts:
  ir_supply_covers_unit (init_ir_supply task041_pruning_unit)
    task041_pruning_unit /\
  ir_supply_extends (init_ir_supply task041_pruning_unit)
    (init_ir_supply task041_pruning_unit) /\
  ir_supply_covers_fn (init_ir_supply task041_pruning_unit)
    (task041_raw_function "main" 1) /\
  ir_supply_covers_fn (init_ir_supply task041_pruning_unit)
    task041_dead_function /\
  fn_pass_effects_hold VP_SimplifyCFG (task041_raw_function "main" 1)
    <|fpo_function := task041_raw_function "main" 1;
      fpo_label_map := [];
      fpo_supply := init_ir_supply task041_pruning_unit|> /\
  fn_pass_effects_hold VP_SimplifyCFG task041_dead_function
    <|fpo_function := task041_dead_function;
      fpo_label_map := [];
      fpo_supply := init_ir_supply task041_pruning_unit|> /\
  introduces_no_invoke_edges (task041_raw_function "main" 1)
    (task041_raw_function "main" 1) /\
  introduces_no_invoke_edges task041_dead_function task041_dead_function /\
  unit_labels_wf task041_pruning_unit /\
  unit_global_inst_ids_distinct task041_pruning_unit
Proof
  EVAL_TAC
QED


Theorem task041_pruning_reduces_to_raw:
  prune_unit_fcg_unreachable task041_pruning_unit
    (fcg_analyze task041_pruning_unit.cu_context) = task041_raw_unit /\
  fcg_postorder (fcg_analyze task041_pruning_unit.cu_context) "main" = ["main"]
Proof
  EVAL_TAC
QED

Theorem task041_pruned_o1_walk:
  run_callee_first task039_policy o1_fn_passes
    (fcg_postorder (fcg_analyze task041_pruning_unit.cu_context) "main")
    (prune_unit_fcg_unreachable task041_pruning_unit
      (fcg_analyze task041_pruning_unit.cu_context))
    (init_ir_supply task041_raw_unit) =
  SOME (task041_walked_unit,task041_sue_supply)
Proof
  simp [run_callee_first_def, run_named_fn_schedules_def,
        task041_pruning_reduces_to_raw, task041_o1_function_transaction]
QED
Theorem task041_pruning_o1_walk:
  run_callee_first task039_policy o1_fn_passes
    (fcg_postorder (fcg_analyze task041_pruning_unit.cu_context) "main")
    (prune_unit_fcg_unreachable task041_pruning_unit
      (fcg_analyze task041_pruning_unit.cu_context))
    (init_ir_supply task041_pruning_unit) =
  SOME (task041_walked_unit,task041_pruning_sue_supply)
Proof
  simp [run_callee_first_def, run_named_fn_schedules_def,
        task041_pruning_reduces_to_raw,
        task041_pruning_o1_function_transaction]
QED

Theorem task041_pruning_schedule_walk:
  run_callee_first task039_policy task041_pruning_spec.ps_fn_passes
    (fcg_postorder (fcg_analyze task041_pruning_unit.cu_context) "main")
    (prune_unit_fcg_unreachable task041_pruning_unit
      (fcg_analyze task041_pruning_unit.cu_context))
    (init_ir_supply task041_pruning_unit) =
  SOME (task041_walked_unit,task041_pruning_sue_supply)
Proof
  simp [run_callee_first_def, run_named_fn_schedules_def,
        task041_pruning_reduces_to_raw,
        task041_pruning_schedule_function_transaction]
QED



Theorem task041_raw_unit_wf:
  unit_wf task041_raw_unit
Proof
  EVAL_TAC >>
  simp [listTheory.REV_DEF, venomInstTheory.is_terminator_def,
        venomStateTheory.get_label_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs []
QED

Theorem task041_walked_unit_wf:
  unit_wf task041_walked_unit
Proof
  EVAL_TAC >>
  simp [listTheory.REV_DEF, venomInstTheory.is_terminator_def,
        venomStateTheory.get_label_def] >>
  EVAL_TAC >> rpt strip_tac >> gvs [] >> Cases_on `i` >>
  gvs [venomInstTheory.is_terminator_def] >> Cases_on `j` >>
  gvs [venomInstTheory.is_terminator_def] >> Cases_on `n` >>
  gvs [venomInstTheory.is_terminator_def]
QED


Theorem task041_pruning_unit_wf:
  unit_wf task041_pruning_unit
Proof
  EVAL_TAC >>
  simp [listTheory.REV_DEF, venomInstTheory.is_terminator_def,
        venomStateTheory.get_label_def] >>
  EVAL_TAC >> rpt strip_tac >>
  gvs [venomInstTheory.fn_insts_blocks_def,
       venomInstTheory.is_terminator_def, listTheory.REV_DEF,
       venomStateTheory.get_label_def]
QED

Theorem task041_pruning_driver_facts:
  unit_wf task041_pruning_unit /\
  raw_static_inputs_wf task041_pruning_unit.cu_context /\
  reachable_fcg_acyclic task041_pruning_unit.cu_context
    (fcg_analyze task041_pruning_unit.cu_context) /\
  task041_pruning_unit.cu_context.ctx_entry = SOME "main" /\
  prune_unit_fcg_unreachable task041_pruning_unit
    (fcg_analyze task041_pruning_unit.cu_context) = task041_raw_unit /\
  fcg_postorder (fcg_analyze task041_pruning_unit.cu_context) "main" = ["main"]
Proof
  simp [task041_pruning_unit_wf, task041_pruning_reduces_to_raw] >>
  EVAL_TAC >> rpt strip_tac >> gvs []
QED
Theorem task041_raw_driver_facts:
  unit_wf task041_raw_unit /\
  raw_static_inputs_wf task041_raw_unit.cu_context /\
  reachable_fcg_acyclic task041_raw_unit.cu_context
    (fcg_analyze task041_raw_unit.cu_context) /\
  task041_raw_unit.cu_context.ctx_entry = SOME "main" /\
  prune_unit_fcg_unreachable task041_raw_unit
    (fcg_analyze task041_raw_unit.cu_context) = task041_raw_unit /\
  fcg_postorder (fcg_analyze task041_raw_unit.cu_context) "main" = ["main"]
Proof
  simp [task041_raw_unit_wf] >> EVAL_TAC >> rpt strip_tac >> gvs []
QED

Theorem task041_get_label_formal_var:
  get_label (Var "formal_var_0") = NONE
Proof
  EVAL_TAC
QED

Theorem task041_walked_final_facts:
  unit_wf task041_walked_unit /\
  unit_labels_wf task041_walked_unit /\
  context_target_safe task039_policy.rpol_target task041_walked_unit.cu_context /\
  concretized_static_layouts_wf task041_walked_unit.cu_context /\
  fmp_lowered_context_wf task041_walked_unit.cu_context /\
  reachable_fcg_acyclic task041_walked_unit.cu_context
    (fcg_analyze task041_walked_unit.cu_context) /\
  codegen_ready task041_walked_unit.cu_context
Proof
  simp [task041_walked_unit_wf] >> EVAL_TAC >> rpt strip_tac >>
  gvs [venomInstTheory.fn_insts_blocks_def,
       callLayoutDefsTheory.canonical_entry_params_from_def,
       callLayoutDefsTheory.no_param_insts_def,
       listTheory.INDEX_FIND_def,
       venomInstTheory.is_param_opcode_def,
       venomInstTheory.is_terminator_def,
       venomInstTheory.is_raw_fmp_opcode_def,
       callLayoutDefsTheory.lowered_return_inst_layout_wf_def,
       fmpWfDefsTheory.fmp_runner_inst_wf_def,
       fmpWfDefsTheory.fmp_bump_consumer_wf_def,
       fmpWfDefsTheory.fmp_invoke_consumer_wf_def,
       fmpWfDefsTheory.fmp_return_consumer_wf_def,
       fmpWfDefsTheory.invoke_layout_wf_def]
  >~ [`i = 1`] >- (Cases_on `i` >> gvs [venomInstTheory.is_terminator_def])
  >~ [`_ = PHI`] >-
    (Cases_on `j` >> gvs [] >> Cases_on `i` >> gvs [] >>
     Cases_on `n` >> gvs [])
  >~ [`succ = "entry"`] >-
    gvs [task041_get_label_formal_var, listTheory.REV_DEF]
  >> TRY
    (qexists `<|inst_id := 2; inst_opcode := ASSIGN;
                inst_operands := [Lit 0w];
                inst_outputs := ["formal_var_0"]|>` >>
     simp [] >> conj_tac
     >- (rpt strip_tac >> Cases_on `path` >> gvs []) >>
     qexistsl [`0`,`1`] >> simp [] >> NO_TAC)
  >> Cases_on `v = "formal_var_0"` >> simp []
QED


Theorem task041_walked_fn_names:
  ctx_fn_names task041_walked_unit.cu_context = ["main"]
Proof
  EVAL_TAC
QED

Theorem task041_pruning_schedule_transaction_closed:
  run_configured_fn_passes execute_configured_fn_pass task039_policy
    (CFP_Simple VP_DretDesugar :: o1_fn_passes) "main" task041_raw_unit
    (init_ir_supply task041_pruning_unit) =
  SOME (task041_walked_unit,task041_pruning_sue_supply)
Proof
  pure_once_rewrite_tac
    [venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  pure_rewrite_tac [task041_pruning_walked_transaction_facts,
                    task041_raw_structure_facts] >>
  simp [task041_pruning_schedule_fold,
        task041_pruning_walked_transaction_facts]
QED

Theorem task041_pruning_validation:
  ctx_fn_names task041_pruning_unit.cu_context = ["main";"unreachable"] /\
  ctx_fn_names task041_walked_unit.cu_context = ["main"] /\
  run_venom_pipeline (K T) (K T) (K T) task039_policy
    task041_pruning_spec task041_pruning_unit =
  SOME <|po_unit := task041_walked_unit;
         po_final_assembly := FAP_Optimize|>
Proof
  simp [run_venom_pipeline_def, task041_pruning_spec_wf,
        task041_pruning_spec_def, task041_pruning_driver_facts,
        task041_pruning_structure_facts, task041_walked_fn_names,
        run_pipeline_stages_def, task041_pruning_schedule_walk,
        run_callee_first_def, run_named_fn_schedules_def,
        task041_pruning_schedule_transaction_closed,
        task041_walked_final_facts]
QED
Theorem task041_o1_walk:
  run_callee_first task039_policy o1_fn_passes
    (fcg_postorder (fcg_analyze task041_raw_unit.cu_context) "main")
    (prune_unit_fcg_unreachable task041_raw_unit
      (fcg_analyze task041_raw_unit.cu_context))
    (init_ir_supply task041_raw_unit) =
  SOME (task041_walked_unit,task041_sue_supply)
Proof
  simp [run_callee_first_def, run_named_fn_schedules_def,
        task041_raw_driver_facts, task041_o1_function_transaction]
QED

Theorem task041_o1_walk_closed:
  run_callee_first task039_policy o1_fn_passes ["main"]
    task041_raw_unit (init_ir_supply task041_raw_unit) =
  SOME (task041_walked_unit,task041_sue_supply)
Proof
  simp [run_callee_first_def, run_named_fn_schedules_def,
        task041_o1_function_transaction]
QED

Theorem task041_run_venom_pipeline_success:
  run_venom_pipeline (K T) (K T) (K T) task039_policy o1_pipeline_spec
    task041_raw_unit =
  SOME <|po_unit := task041_walked_unit;
         po_final_assembly := FAP_Optimize|>
Proof
  simp [run_venom_pipeline_def, task041_schedule_evaluations,
        task041_raw_driver_facts, task041_pre_walk,
        task041_o1_walk, task041_o1_walk_closed, o1_pipeline_spec_def,
        run_pipeline_stages_def, task041_walked_final_facts]
QED

Theorem task041_o1_policy_result:
  resolve_o1_policy (o1_policy prague_capabilities) = SOME task039_policy
Proof
  EVAL_TAC
QED

Theorem task041_o1_pipeline_success:
  o1_pipeline (K T) (K T) (K T) prague_capabilities task041_raw_unit =
  SOME <|po_unit := task041_walked_unit;
         po_final_assembly := FAP_Optimize|>
Proof
  simp [o1_pipeline_def, task041_o1_policy_result,
        task041_run_venom_pipeline_success]
QED


Theorem task041_success_validation:
  let out = <|po_unit := task041_walked_unit;
              po_final_assembly := FAP_Optimize|> in
    o1_pipeline (K T) (K T) (K T) prague_capabilities task041_raw_unit =
      SOME out /\
    out.po_final_assembly = FAP_Optimize /\
    unit_wf out.po_unit /\
    fmp_lowered_context_wf out.po_unit.cu_context /\
    codegen_ready out.po_unit.cu_context
Proof
  simp [task041_o1_pipeline_success, task041_walked_final_facts]
QED

Theorem task041_final_check_rejection:
  run_venom_pipeline (K T) (K T) (K F) task039_policy o1_pipeline_spec
    task041_raw_unit = NONE
Proof
  simp [run_venom_pipeline_def, task041_schedule_evaluations,
        task041_raw_driver_facts, task041_pre_walk,
        task041_o1_walk, task041_o1_walk_closed, o1_pipeline_spec_def,
        run_pipeline_stages_def, task041_walked_final_facts]
QED


val _ = export_theory ();
