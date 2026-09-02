(* Structural proof interface for mapped and callee-first runners. *)

Theory venomPipelineRunnerProps
Ancestors
  venomPipelineRunner venomFnScheduleRunnerProps fcgDefs

Theorem run_named_fn_schedules_append:
  run_named_fn_schedules runner rpolicy passes (xs ++ ys) unit supply =
      SOME out <=>
  ?mid_unit mid_supply.
    run_named_fn_schedules runner rpolicy passes xs unit supply =
      SOME (mid_unit,mid_supply) /\
    run_named_fn_schedules runner rpolicy passes ys mid_unit mid_supply =
      SOME out
Proof
  qid_spec_tac `supply` >> qid_spec_tac `unit` >>
  Induct_on `xs`
  >- simp[run_named_fn_schedules_def]
  >> simp[run_named_fn_schedules_def] >>
  Cases_on `run_configured_fn_passes runner rpolicy passes h unit supply` >>
  gvs[] >> PairCases_on `x` >> gvs[]
QED

Theorem list_split_at_EL:
  i < LENGTH names ==>
  names = TAKE i names ++ EL i names :: DROP (SUC i) names
Proof
  qid_spec_tac `names` >> Induct_on `i`
  >- (Cases_on `names` >> simp[])
  >> Cases_on `names` >> simp[] >>
  first_x_assum (qspec_then `t` mp_tac) >> simp[]
QED

Theorem list_index_split:
  list_index name names = SOME i ==>
  names = TAKE i names ++ name :: DROP (SUC i) names
Proof
  simp[list_index_def, listTheory.INDEX_OF_eq_SOME] >> strip_tac >>
  drule list_split_at_EL >> simp[]
QED

Theorem run_named_fn_schedules_indexed:
  run_named_fn_schedules runner rpolicy passes names unit supply = SOME out /\
  list_index name names = SOME i ==>
  ?prefix_unit prefix_supply name_unit name_supply.
    run_named_fn_schedules runner rpolicy passes (TAKE i names) unit supply =
      SOME (prefix_unit,prefix_supply) /\
    run_configured_fn_passes runner rpolicy passes name
      prefix_unit prefix_supply = SOME (name_unit,name_supply) /\
    run_named_fn_schedules runner rpolicy passes (DROP (SUC i) names)
      name_unit name_supply = SOME out
Proof
  strip_tac >> drule list_index_split >> strip_tac >>
  qpat_assum `names = TAKE i names ++ name :: DROP (SUC i) names`
    (fn eq =>
      qpat_x_assum
        `run_named_fn_schedules runner rpolicy passes names unit supply = SOME out`
        (fn th => mp_tac (ONCE_REWRITE_RULE [eq] th))) >>
  simp[run_named_fn_schedules_append, run_named_fn_schedules_def,
       AllCaseEqs()] >> metis_tac[]
QED

Theorem run_configured_fn_passes_structural:
  run_configured_fn_passes runner rpolicy passes name unit supply =
    SOME (unit',supply') ==>
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  list_subset (unit_invoke_targets unit') (unit_invoke_targets unit)
Proof
  simp[venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >> strip_tac >>
  gvs[AllCaseEqs()] >>
  drule replace_unique_function_name_order >> strip_tac >>
  drule apply_unit_label_map_function_names >> strip_tac >>
  gvs[venomInstTheory.ctx_fn_names_def]
QED

Theorem run_named_fn_schedules_cons_success:
  run_named_fn_schedules runner rpolicy passes (name::names) unit supply =
    SOME out ==>
  ?unit1 supply1.
    run_configured_fn_passes runner rpolicy passes name unit supply =
      SOME (unit1,supply1) /\
    run_named_fn_schedules runner rpolicy passes names unit1 supply1 = SOME out
Proof
  simp[run_named_fn_schedules_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem run_named_fn_schedules_structural:
  run_named_fn_schedules runner rpolicy passes names unit supply =
    SOME (unit',supply') ==>
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  list_subset (unit_invoke_targets unit') (unit_invoke_targets unit)
Proof
  qid_spec_tac `supply` >> qid_spec_tac `unit` >> Induct_on `names`
  >- simp[run_named_fn_schedules_def,
          venomFnScheduleRunnerTheory.list_subset_def,
          listTheory.EVERY_MEM]
  >> rpt strip_tac >> drule run_named_fn_schedules_cons_success >> strip_tac >>
  drule run_configured_fn_passes_structural >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- metis_tac[]
  >> irule list_subset_trans >> metis_tac[]
QED

Theorem run_mapped_functions_structural:
  run_mapped_functions rpolicy pass unit supply = SOME (unit',supply') ==>
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  list_subset (unit_invoke_targets unit') (unit_invoke_targets unit)
Proof
  simp[run_mapped_functions_def] >>
  metis_tac[run_named_fn_schedules_structural]
QED

Theorem run_pipeline_stage_structural:
  run_pipeline_stage rpolicy stage unit supply = SOME (unit',supply') ==>
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  list_subset (unit_invoke_targets unit') (unit_invoke_targets unit)
Proof
  Cases_on `stage`
  >- (simp[run_pipeline_stage_def] >>
      metis_tac[run_mapped_functions_structural])
  >> simp[run_pipeline_stage_def,
          venomFnScheduleRunnerTheory.list_subset_def,
          listTheory.EVERY_MEM]
QED

Theorem run_pipeline_stages_cons_success:
  run_pipeline_stages rpolicy (stage::stages) unit supply = SOME out ==>
  ?unit1 supply1.
    run_pipeline_stage rpolicy stage unit supply = SOME (unit1,supply1) /\
    run_pipeline_stages rpolicy stages unit1 supply1 = SOME out
Proof
  simp[run_pipeline_stages_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem run_pipeline_stages_structural:
  run_pipeline_stages rpolicy stages unit supply = SOME (unit',supply') ==>
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  list_subset (unit_invoke_targets unit') (unit_invoke_targets unit)
Proof
  qid_spec_tac `supply` >> qid_spec_tac `unit` >> Induct_on `stages`
  >- simp[run_pipeline_stages_def,
          venomFnScheduleRunnerTheory.list_subset_def,
          listTheory.EVERY_MEM]
  >> rpt strip_tac >> drule run_pipeline_stages_cons_success >> strip_tac >>
  drule run_pipeline_stage_structural >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- metis_tac[]
  >> irule list_subset_trans >> metis_tac[]
QED

Theorem run_callee_first_structural:
  run_callee_first rpolicy passes names unit supply = SOME (unit',supply') ==>
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context /\
  list_subset (unit_invoke_targets unit') (unit_invoke_targets unit)
Proof
  simp[run_callee_first_def] >>
  metis_tac[run_named_fn_schedules_structural]
QED

Theorem run_pipeline_stage_discard[simp]:
  run_pipeline_stage rpolicy PS_DiscardAnalyses unit supply =
    SOME (unit,supply)
Proof
  simp[run_pipeline_stage_def]
QED

Theorem run_named_fn_schedules_head_failure:
  run_configured_fn_passes runner rpolicy passes name unit supply = NONE ==>
  run_named_fn_schedules runner rpolicy passes (name::names) unit supply = NONE
Proof
  simp[run_named_fn_schedules_def]
QED

Theorem run_pipeline_stages_head_failure:
  run_pipeline_stage rpolicy stage unit supply = NONE ==>
  run_pipeline_stages rpolicy (stage::stages) unit supply = NONE
Proof
  simp[run_pipeline_stages_def]
QED
val _ = export_theory ();
