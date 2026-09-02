(* Structural proof interface for mapped and callee-first runners. *)

Theory venomPipelineRunnerProps
Ancestors
  venomPipelineRunner venomFnScheduleRunnerProps fcgPostorder
  venomPassDispatcherProps fmpLowerProps venomPassSchedule

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
  simp[fcgDefsTheory.list_index_def, listTheory.INDEX_OF_eq_SOME] >> strip_tac >>
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

Theorem run_callee_first_direct_callee_processed_first:
  fcg = fcg_analyze ctx /\ ctx.ctx_entry = SOME entry /\
  ctx_wf ctx /\ wf_invoke_targets ctx /\
  reachable_fcg_acyclic ctx fcg /\
  fn_directly_calls ctx caller callee /\
  fcg_is_reachable fcg caller /\
  run_callee_first rpolicy passes (fcg_postorder fcg entry) unit supply =
    SOME out ==>
  ?callee_i caller_i
   callee_prefix_unit callee_prefix_supply callee_unit callee_supply
   caller_prefix_unit caller_prefix_supply caller_unit caller_supply.
    list_index callee (fcg_postorder fcg entry) = SOME callee_i /\
    list_index caller (fcg_postorder fcg entry) = SOME caller_i /\
    callee_i < caller_i /\
    run_named_fn_schedules execute_configured_fn_pass rpolicy passes
      (TAKE callee_i (fcg_postorder fcg entry)) unit supply =
      SOME (callee_prefix_unit,callee_prefix_supply) /\
    run_configured_fn_passes execute_configured_fn_pass rpolicy passes callee
      callee_prefix_unit callee_prefix_supply =
      SOME (callee_unit,callee_supply) /\
    run_named_fn_schedules execute_configured_fn_pass rpolicy passes
      (DROP (SUC callee_i) (fcg_postorder fcg entry))
      callee_unit callee_supply = SOME out /\
    run_named_fn_schedules execute_configured_fn_pass rpolicy passes
      (TAKE caller_i (fcg_postorder fcg entry)) unit supply =
      SOME (caller_prefix_unit,caller_prefix_supply) /\
    run_configured_fn_passes execute_configured_fn_pass rpolicy passes caller
      caller_prefix_unit caller_prefix_supply =
      SOME (caller_unit,caller_supply) /\
    run_named_fn_schedules execute_configured_fn_pass rpolicy passes
      (DROP (SUC caller_i) (fcg_postorder fcg entry))
      caller_unit caller_supply = SOME out
Proof
  rpt strip_tac >>
  drule_all fcg_postorder_callee_before_caller >> strip_tac >>
  gvs[run_callee_first_def] >>
  metis_tac[run_named_fn_schedules_indexed]
QED
Theorem fmp_lower_function_success_no_raw[local]:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  no_raw_fmp_ops fn'
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def] >>
  Cases_on `analyze_fmp_context ctx` >> simp[] >>
  rename1 `analyze_fmp_context ctx = SOME infos` >>
  Cases_on `fn.fn_fmp_signature`
  >- (strip_tac >>
      `fmp_lower_input infos ctx fn` by
        (qpat_x_assum `fmp_lower_function_with_info _ _ _ _ = SOME _`
          mp_tac >>
         simp[fmpLowerDefsTheory.fmp_lower_function_with_info_def,
              AllCaseEqs()]) >>
      `fmp_lower_function ctx s fn = SOME (fn',s')` by
        simp[fmpLowerDefsTheory.fmp_lower_function_def] >>
      metis_tac[fmp_lower_function_removes_raw_ops]) >>
  gvs[fmpLowerDefsTheory.fmp_lower_function_with_info_def,AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Definition o1_fn_structural_output_def[local]:
  o1_fn_structural_output fn <=>
    IS_SOME fn.fn_eom /\ no_raw_fmp_ops fn /\
    IS_SOME fn.fn_fmp_signature
End

Theorem run_configured_fn_pass_fold_first_step[local]:
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    (pass::passes) unit s fn labels = SOME result ==>
  ?out.
    execute_configured_fn_pass rpolicy pass unit s fn = SOME out /\
    fn_pass_effects_hold (fn_pass_tag pass) fn out /\
    run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
      passes unit out.fpo_supply out.fpo_function
      (labels ++ out.fpo_label_map) = SOME result
Proof
  simp[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def] >>
  Cases_on `execute_configured_fn_pass rpolicy pass unit s fn` >> simp[] >>
  Cases_on `x.fpo_function.fn_name = fn.fn_name /\
            fn_pass_effects_hold (fn_pass_tag pass) fn x /\
            introduces_no_invoke_edges fn x.fpo_function /\
            ir_supply_extends s x.fpo_supply /\
            ir_supply_covers_fn x.fpo_supply x.fpo_function /\
            ir_supply_covers_unit x.fpo_supply unit` >> simp[] >>
  metis_tac[]
QED

Theorem execute_configured_fn_pass_o1_suffix_structural[local]:
  MEM tag [VP_MakeSSA; VP_SimplifyCFG; VP_SingleUseExpansion;
           VP_DFT; VP_CFGNormalization] /\
  o1_fn_structural_output fn /\
  execute_configured_fn_pass rpolicy (CFP_Simple tag) unit s fn = SOME out /\
  fn_pass_effects_hold (fn_pass_tag (CFP_Simple tag)) fn out ==>
  o1_fn_structural_output out.fpo_function
Proof
  rpt strip_tac >>
  `no_raw_fmp_ops fn` by
    fs[o1_fn_structural_output_def] >>
  `no_raw_fmp_ops out.fpo_function` by
    (irule execute_configured_fn_pass_o1_suffix_no_raw_fmp_ops >>
     qexistsl [`fn`,`rpolicy`,`s`,`tag`,`unit`] >>
     simp[]) >>
  Cases_on `tag` >>
  gvs[o1_fn_structural_output_def,
      venomPassScheduleTheory.fn_pass_tag_def,
      venomPassDispatcherTheory.fn_pass_effects_hold_def,
      venomPassDispatcherTheory.fn_static_layout_effect_holds_def,
      venomPassDispatcherTheory.fn_abi_effect_holds_def,
      venomPassDispatcherTheory.fn_pass_static_layout_effect_def,
      venomPassDispatcherTheory.fn_pass_abi_effect_def,
      venomInstTheory.fn_static_layout_eq_def,
      venomInstTheory.fn_fmp_convention_eq_def]
QED

Theorem subst_label_map_blocks_opcode_every[local]:
  EVERY (\inst. P inst.inst_opcode)
    (fn_insts_blocks (MAP (subst_label_map_block label_map) blocks)) <=>
  EVERY (\inst. P inst.inst_opcode) (fn_insts_blocks blocks)
Proof
  Induct_on `blocks` >>
  simp[venomInstTheory.fn_insts_blocks_def,
       cfgTransformTheory.subst_label_map_block_def,
       cfgTransformTheory.subst_label_map_inst_def,
       listTheory.EVERY_APPEND, listTheory.EVERY_MAP]
QED

Theorem subst_label_map_fn_o1_structural[local]:
  o1_fn_structural_output fn ==>
  o1_fn_structural_output (subst_label_map_fn label_map fn)
Proof
  simp[o1_fn_structural_output_def,
       venomInstTheory.no_raw_fmp_ops_def,
       venomInstTheory.fn_insts_def,
       cfgTransformTheory.subst_label_map_fn_def] >>
  strip_tac >>
  fs[GSYM listTheory.EVERY_MEM, subst_label_map_blocks_opcode_every]
QED

Theorem filter_subst_label_map_fn_name[local]:
  FILTER (\fn. fn.fn_name = name)
    (MAP (subst_label_map_fn label_map) fns) =
  MAP (subst_label_map_fn label_map)
    (FILTER (\fn. fn.fn_name = name) fns)
Proof
  Induct_on `fns`
  >- simp[]
  >> simp[cfgTransformTheory.subst_label_map_fn_def] >>
  gen_tac >> Cases_on `h.fn_name = name` >>
  simp[cfgTransformTheory.subst_label_map_fn_def]
QED

Theorem lookup_unique_function_subst_label_map[local]:
  lookup_unique_function name fns = SOME fn ==>
  lookup_unique_function name (MAP (subst_label_map_fn label_map) fns) =
    SOME (subst_label_map_fn label_map fn)
Proof
  strip_tac >>
  drule lookup_unique_function_FILTER >>
  simp[venomFnScheduleRunnerTheory.lookup_unique_function_def,
       filter_subst_label_map_fn_name]
QED

Theorem apply_unit_label_map_o1_lookup[local]:
  apply_unit_label_map label_map unit = SOME unit' ==>
  lookup_unique_function name unit.cu_context.ctx_functions = SOME fn ==>
  o1_fn_structural_output fn ==>
  ?fn'. lookup_unique_function name unit'.cu_context.ctx_functions = SOME fn' /\
        o1_fn_structural_output fn'
Proof
  rpt strip_tac >>
  qpat_x_assum `apply_unit_label_map label_map unit = SOME unit'` mp_tac >>
  simp[unitLabelMapTheory.apply_unit_label_map_def] >>
  Cases_on `resolve_label_map label_map` >> simp[] >>
  Cases_on `resolved_label_endpoints_valid unit x` >> simp[] >>
  strip_tac >>
  gvs[unitLabelMapTheory.apply_resolved_unit_label_map_def] >>
  qexists `subst_label_map_fn x fn` >>
  simp[lookup_unique_function_subst_label_map,
       subst_label_map_fn_o1_structural]
QED

Theorem run_o1_fn_pass_fold_structural[local]:
  run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
    o1_fn_passes unit s fn labels = SOME result ==>
  o1_fn_structural_output (FST result)
Proof
  strip_tac >>
  qpat_x_assum
    `run_configured_fn_pass_fold execute_configured_fn_pass rpolicy
       o1_fn_passes unit s fn labels = SOME result`
    (fn th => mp_tac (REWRITE_RULE [o1_fn_passes_def] th)) >>
  strip_tac >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_MakeSSA)
             unit s fn = SOME out1` >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_LowerDload)
             unit out1.fpo_supply out1.fpo_function = SOME out2` >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_ConcretizeMemLoc)
             unit out2.fpo_supply out2.fpo_function = SOME out3` >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_FmpLowering)
             unit out3.fpo_supply out3.fpo_function = SOME out4` >>
  `IS_SOME out3.fpo_function.fn_eom` by
    gvs[venomPassScheduleTheory.fn_pass_tag_def,
        venomPassDispatcherTheory.fn_pass_effects_hold_def,
        venomPassDispatcherTheory.fn_static_layout_effect_holds_def,
        venomPassDispatcherTheory.fn_pass_static_layout_effect_def] >>
  `IS_SOME out4.fpo_function.fn_eom /\
   IS_SOME out4.fpo_function.fn_fmp_signature` by
    gvs[venomPassScheduleTheory.fn_pass_tag_def,
        venomPassDispatcherTheory.fn_pass_effects_hold_def,
        venomPassDispatcherTheory.fn_static_layout_effect_holds_def,
        venomPassDispatcherTheory.fn_abi_effect_holds_def,
        venomPassDispatcherTheory.fn_pass_static_layout_effect_def,
        venomPassDispatcherTheory.fn_pass_abi_effect_def,
        venomInstTheory.fn_static_layout_eq_def] >>
  `no_raw_fmp_ops out4.fpo_function` by
    (Cases_on
       `fmp_lower_function unit.cu_context out3.fpo_supply out3.fpo_function` >>
     gvs[] >> PairCases_on `x` >> gvs[] >>
     metis_tac[fmp_lower_function_success_no_raw]) >>
  `o1_fn_structural_output out4.fpo_function` by
    simp[o1_fn_structural_output_def] >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_MakeSSA)
             unit out4.fpo_supply out4.fpo_function = SOME out5` >>
  `o1_fn_structural_output out5.fpo_function` by
    (irule execute_configured_fn_pass_o1_suffix_structural >>
     qexistsl [`out4.fpo_function`,`rpolicy`,`out4.fpo_supply`,
               `VP_MakeSSA`,`unit`] >> simp[venomPassScheduleTheory.fn_pass_tag_def]) >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_SimplifyCFG)
             unit out5.fpo_supply out5.fpo_function = SOME out6` >>
  `o1_fn_structural_output out6.fpo_function` by
    (irule execute_configured_fn_pass_o1_suffix_structural >>
     qexistsl [`out5.fpo_function`,`rpolicy`,`out5.fpo_supply`,
               `VP_SimplifyCFG`,`unit`] >> simp[venomPassScheduleTheory.fn_pass_tag_def]) >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_SingleUseExpansion)
             unit out6.fpo_supply out6.fpo_function = SOME out7` >>
  `o1_fn_structural_output out7.fpo_function` by
    (irule execute_configured_fn_pass_o1_suffix_structural >>
     qexistsl [`out6.fpo_function`,`rpolicy`,`out6.fpo_supply`,
               `VP_SingleUseExpansion`,`unit`] >> simp[venomPassScheduleTheory.fn_pass_tag_def]) >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_DFT)
             unit out7.fpo_supply out7.fpo_function = SOME out8` >>
  `o1_fn_structural_output out8.fpo_function` by
    (irule execute_configured_fn_pass_o1_suffix_structural >>
     qexistsl [`out7.fpo_function`,`rpolicy`,`out7.fpo_supply`,
               `VP_DFT`,`unit`] >> simp[venomPassScheduleTheory.fn_pass_tag_def]) >>
  dxrule run_configured_fn_pass_fold_first_step >> strip_tac >>
  rename1 `execute_configured_fn_pass rpolicy (CFP_Simple VP_CFGNormalization)
             unit out8.fpo_supply out8.fpo_function = SOME out9` >>
  `o1_fn_structural_output out9.fpo_function` by
    (irule execute_configured_fn_pass_o1_suffix_structural >>
     qexistsl [`out8.fpo_function`,`rpolicy`,`out8.fpo_supply`,
               `VP_CFGNormalization`,`unit`] >> simp[venomPassScheduleTheory.fn_pass_tag_def]) >>
  gvs[venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def]
QED

Theorem run_configured_fn_passes_o1_structural:
  run_configured_fn_passes execute_configured_fn_pass rpolicy o1_fn_passes
    name unit s = SOME (unit',s') ==>
  ?fn'.
    lookup_unique_function name unit'.cu_context.ctx_functions = SOME fn' /\
    IS_SOME fn'.fn_eom /\ no_raw_fmp_ops fn' /\
    IS_SOME fn'.fn_fmp_signature
Proof
  simp[venomFnScheduleRunnerTheory.run_configured_fn_passes_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  `o1_fn_structural_output fn'` by
    (drule run_o1_fn_pass_fold_structural >> simp[]) >>
  `lookup_unique_function name fns = SOME fn'` by
    (drule replace_unique_function_exactly_one >>
     simp[venomFnScheduleRunnerTheory.lookup_unique_function_def]) >>
  `apply_unit_label_map label_map
      (unit with cu_context := unit.cu_context with ctx_functions := fns) =
        SOME unit' /\
   lookup_unique_function name fns = SOME fn' /\
   o1_fn_structural_output fn'` by simp[] >>
  `lookup_unique_function name
      (unit with cu_context := unit.cu_context with ctx_functions := fns).
        cu_context.ctx_functions = SOME fn' /\
   o1_fn_structural_output fn'` by simp[] >>
  drule apply_unit_label_map_o1_lookup >>
  disch_then drule >> (impl_tac >- simp[]) >> strip_tac >>
  goal_assum $ drule_at Any >>
  gvs[o1_fn_structural_output_def]
QED

val _ = export_theory ();
