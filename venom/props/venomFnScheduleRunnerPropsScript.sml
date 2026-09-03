(* Structural interfaces for the atomic configured function scheduler. *)

Theory venomFnScheduleRunnerProps
Ancestors
  venomFnScheduleRunner

Theorem lookup_unique_function_FILTER:
  lookup_unique_function name fns = SOME fn ==>
  FILTER (\f. f.fn_name = name) fns = [fn]
Proof
  simp[lookup_unique_function_def] >>
  Cases_on `FILTER (\f. f.fn_name = name) fns` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem lookup_unique_function_member:
  lookup_unique_function name fns = SOME fn ==>
  MEM fn fns /\ fn.fn_name = name
Proof
  strip_tac >> drule lookup_unique_function_FILTER >>
  simp[listTheory.FILTER_EQ_CONS] >> strip_tac >> gvs[] >> simp[]
QED

Theorem lookup_unique_function_unique:
  lookup_unique_function name fns = SOME fn /\
  MEM other fns /\ other.fn_name = name ==>
  other = fn
Proof
  strip_tac >> drule lookup_unique_function_FILTER >>
  simp[listTheory.FILTER_EQ_CONS] >> strip_tac >>
  gvs[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem replace_unique_function_length:
  replace_unique_function name replacement fns = SOME fns' ==>
  LENGTH fns' = LENGTH fns
Proof
  simp[replace_unique_function_def] >>
  Cases_on `replacement.fn_name = name` >> simp[] >>
  Cases_on `FILTER (\fn. fn.fn_name = name) fns` >> simp[] >>
  Cases_on `t` >> simp[] >> strip_tac >> gvs[]
QED

Theorem replace_unique_function_name_order:
  replace_unique_function name replacement fns = SOME fns' ==>
  MAP (\f. f.fn_name) fns' = MAP (\f. f.fn_name) fns
Proof
  simp[replace_unique_function_def] >>
  Cases_on `replacement.fn_name = name` >> simp[] >>
  Cases_on `FILTER (\fn. fn.fn_name = name) fns` >> simp[] >>
  Cases_on `t` >> simp[] >>
  strip_tac >> gvs[] >>
  simp[listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> simp[] >> metis_tac[]
QED

Theorem replace_unique_function_preserves_nonmatching:
  replace_unique_function name replacement fns = SOME fns' /\
  MEM fn fns /\ fn.fn_name <> name ==>
  MEM fn fns'
Proof
  simp[replace_unique_function_def] >>
  Cases_on `replacement.fn_name = name` >> simp[] >>
  Cases_on `FILTER (\f. f.fn_name = name) fns` >> simp[] >>
  Cases_on `t` >> simp[] >>
  rpt strip_tac >> gvs[listTheory.MEM_MAP] >>
  qexists `fn` >> simp[]
QED

Theorem FILTER_MAP_replace_empty:
  FILTER P xs = [] ==>
  FILTER P (MAP (\x. if P x then replacement else x) xs) = []
Proof
  Induct_on `xs`
  >- simp[]
  >> simp[] >> strip_tac >>
  Cases_on `P h` >> gvs[]
QED

Theorem FILTER_MAP_replace_single:
  FILTER P xs = [old] /\ P replacement ==>
  FILTER P (MAP (\x. if P x then replacement else x) xs) = [replacement]
Proof
  Induct_on `xs`
  >- simp[]
  >> simp[] >> strip_tac >>
  Cases_on `P h` >> gvs[]
  >- (strip_tac >> gvs[] >>
      irule FILTER_MAP_replace_empty >> simp[])
  >> strip_tac >> first_x_assum irule >> simp[]
QED
Theorem FILTER_MAP_replace_unique:
  (?old. FILTER P xs = [old]) /\ P replacement ==>
  FILTER P (MAP (\x. if P x then replacement else x) xs) = [replacement]
Proof
  strip_tac >> drule FILTER_MAP_replace_single >> simp[]
QED

Theorem replace_unique_function_exactly_one:
  replace_unique_function name replacement fns = SOME fns' ==>
  FILTER (\f. f.fn_name = name) fns' = [replacement]
Proof
  simp[replace_unique_function_def] >>
  Cases_on `replacement.fn_name = name` >> simp[] >>
  Cases_on `FILTER (\f. f.fn_name = name) fns` >> simp[] >>
  Cases_on `t` >> simp[] >>
  strip_tac >> gvs[] >>
  ho_match_mp_tac FILTER_MAP_replace_unique >> simp[] >>
  qexists `h` >> simp[]
QED

Theorem unit_with_current_fn_lookup:
  unit_with_current_fn unit fn = SOME observed ==>
  lookup_unique_function fn.fn_name observed.cu_context.ctx_functions =
    SOME fn
Proof
  simp[unit_with_current_fn_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule replace_unique_function_exactly_one >>
  simp[lookup_unique_function_def]
QED

Theorem unit_with_current_fn_preserves_nonfunctions:
  unit_with_current_fn unit fn = SOME observed ==>
  observed.cu_data_segment = unit.cu_data_segment /\
  observed.cu_context.ctx_entry = unit.cu_context.ctx_entry /\
  observed.cu_context.ctx_global_reserved =
    unit.cu_context.ctx_global_reserved
Proof
  simp[unit_with_current_fn_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED

Theorem run_configured_fn_pass_fold_first_effects:
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s fn labels =
    SOME result ==>
  ?observed out.
    unit_with_current_fn unit fn = SOME observed /\
    runner rpolicy pass observed s fn = SOME out /\
    fn_pass_effects_hold (fn_pass_tag pass) fn out
Proof
  simp[run_configured_fn_pass_fold_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem run_configured_fn_pass_fold_first_invoke:
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s fn labels =
    SOME result ==>
  ?observed out.
    unit_with_current_fn unit fn = SOME observed /\
    runner rpolicy pass observed s fn = SOME out /\
    introduces_no_invoke_edges fn out.fpo_function
Proof
  simp[run_configured_fn_pass_fold_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem run_configured_fn_pass_fold_first_supply:
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s fn labels =
    SOME result ==>
  ?observed out.
    unit_with_current_fn unit fn = SOME observed /\
    runner rpolicy pass observed s fn = SOME out /\
    ir_supply_extends s out.fpo_supply /\
    ir_supply_covers_fn out.fpo_supply out.fpo_function /\
    ir_supply_covers_unit out.fpo_supply observed
Proof
  simp[run_configured_fn_pass_fold_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem run_configured_fn_pass_fold_threads_current:
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s fn labels =
    SOME result ==>
  ?observed out.
    unit_with_current_fn unit fn = SOME observed /\
    runner rpolicy pass observed s fn = SOME out /\
    run_configured_fn_pass_fold runner rpolicy passes unit
      out.fpo_supply out.fpo_function (labels ++ out.fpo_label_map) =
      SOME result
Proof
  simp[run_configured_fn_pass_fold_def, AllCaseEqs()] >> metis_tac[]
QED


Theorem apply_unit_label_map_function_names:
  apply_unit_label_map label_map unit = SOME unit' ==>
  MAP (\f. f.fn_name) unit'.cu_context.ctx_functions =
  MAP (\f. f.fn_name) unit.cu_context.ctx_functions
Proof
  simp[unitLabelMapTheory.apply_unit_label_map_def] >>
  Cases_on `resolve_label_map label_map` >> simp[] >>
  Cases_on `resolved_label_endpoints_valid unit x` >> simp[] >>
  strip_tac >> gvs[unitLabelMapTheory.apply_resolved_unit_label_map_def,
                    listTheory.MAP_MAP_o, combinTheory.o_DEF,
                    cfgTransformTheory.subst_label_map_fn_def]
QED

Theorem apply_unit_label_map_global_reserved:
  apply_unit_label_map label_map unit = SOME unit' ==>
  unit'.cu_context.ctx_global_reserved =
  unit.cu_context.ctx_global_reserved
Proof
  simp[unitLabelMapTheory.apply_unit_label_map_def] >>
  Cases_on `resolve_label_map label_map` >> simp[] >>
  Cases_on `resolved_label_endpoints_valid unit x` >> simp[] >>
  strip_tac >> gvs[unitLabelMapTheory.apply_resolved_unit_label_map_def]
QED

Theorem run_fn_schedule_name_order:
  run_fn_schedule rpolicy passes name unit = SOME (unit',s') ==>
  ctx_fn_names unit'.cu_context = ctx_fn_names unit.cu_context
Proof
  simp[run_fn_schedule_def, run_configured_fn_passes_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule replace_unique_function_name_order >> strip_tac >>
  drule apply_unit_label_map_function_names >> strip_tac >>
  gvs[venomInstTheory.ctx_fn_names_def]
QED

Theorem run_fn_schedule_unit_labels_wf:
  run_fn_schedule rpolicy passes name unit = SOME (unit',s') ==>
  unit_labels_wf unit'
Proof
  simp[run_fn_schedule_def, run_configured_fn_passes_def] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem run_fn_schedule_global_reserved:
  run_fn_schedule rpolicy passes name unit = SOME (unit',s') ==>
  unit'.cu_context.ctx_global_reserved = unit.cu_context.ctx_global_reserved
Proof
  simp[run_fn_schedule_def, run_configured_fn_passes_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  drule apply_unit_label_map_global_reserved >> simp[]
QED

Theorem list_subset_trans:
  list_subset xs ys /\ list_subset ys zs ==> list_subset xs zs
Proof
  simp[list_subset_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem run_fn_schedule_call_graph_subgraph:
  run_fn_schedule rpolicy passes name unit = SOME (unit',s') ==>
  list_subset (unit_invoke_targets unit') (unit_invoke_targets unit)
Proof
  simp[run_fn_schedule_def, run_configured_fn_passes_def] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Theorem run_fn_schedule_global_inst_ids_distinct:
  run_fn_schedule rpolicy passes name unit = SOME (unit',s') ==>
  unit_global_inst_ids_distinct unit'
Proof
  simp[run_fn_schedule_def, run_configured_fn_passes_def] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Definition task039_rotate_function_def:
  task039_rotate_function fn =
    fn with fn_blocks := TL fn.fn_blocks ++ [HD fn.fn_blocks]
End

Definition task039_sequence_runner_def:
  task039_sequence_runner rpolicy (CFP_Simple tag) unit s fn =
    if tag = VP_MakeSSA /\ (HD fn.fn_blocks).bb_label = "old" then
      SOME <| fpo_function := task039_rotate_function fn;
              fpo_label_map := []; fpo_supply := s |>
    else if tag = VP_DFT /\ (HD fn.fn_blocks).bb_label = "mid" then
      SOME <| fpo_function := task039_rotate_function fn;
              fpo_label_map := []; fpo_supply := s |>
    else NONE
End

Definition task039_rotate_unit_def:
  task039_rotate_unit unit =
    unit with cu_context := unit.cu_context with ctx_functions :=
      MAP task039_rotate_function unit.cu_context.ctx_functions
End

Theorem run_configured_fn_passes_current_output_eval:
  run_configured_fn_passes task039_sequence_runner task039_policy
    [CFP_Simple VP_MakeSSA; CFP_Simple VP_DFT] "f"
    (task009_label_fixture "old")
    (init_ir_supply (task009_label_fixture "old")) =
  SOME (task039_rotate_unit
          (task039_rotate_unit (task009_label_fixture "old")),
        init_ir_supply (task009_label_fixture "old")) /\
  MAP (\bb. bb.bb_label)
    (HD (task039_rotate_unit
      (task039_rotate_unit (task009_label_fixture "old"))).cu_context
      .ctx_functions).fn_blocks = ["new";"old";"mid"]
Proof
  EVAL_TAC
QED

Theorem run_configured_fn_passes_atomic_label_eval:
  run_configured_fn_passes
    (task039_map_runner [("old","new")]) task039_policy
    [CFP_Simple VP_MakeSSA] "f" (task009_label_fixture "old")
    (init_ir_supply (task009_label_fixture "old")) =
  SOME (task009_label_fixture "new",
        init_ir_supply (task009_label_fixture "old")) /\
  (HD ((HD (task009_label_fixture "new").cu_context.ctx_functions)
      .fn_blocks)).bb_instructions =
    [mk_inst 1 OFFSET [Label "new"; Var "x"] ["out"]] /\
  (HD (task009_label_fixture "new").cu_data_segment).ds_items =
    [DataLabel "new"; DataBytes [1w; 2w]]
Proof
  EVAL_TAC
QED

Theorem task039_rejection_evaluations:
  run_configured_fn_passes task039_identity_runner task039_policy [] "dup"
    task039_duplicate_unit (init_ir_supply task039_duplicate_unit) = NONE /\
  run_configured_fn_passes task039_identity_runner task039_policy [] "missing"
    (task009_label_fixture "old")
    (init_ir_supply (task009_label_fixture "old")) = NONE /\
  run_configured_fn_passes task039_invalid_effect_runner task039_policy
    [CFP_Simple VP_MakeSSA] "f" (task009_label_fixture "old")
    (init_ir_supply (task009_label_fixture "old")) = NONE /\
  run_configured_fn_passes task039_stale_supply_runner task039_policy
    [CFP_Simple VP_MakeSSA] "f" (task009_label_fixture "old")
    (init_ir_supply (task009_label_fixture "old")) = NONE /\
  run_configured_fn_passes
    (task039_map_runner [("old","missing")]) task039_policy
    [CFP_Simple VP_MakeSSA] "f" (task009_label_fixture "old")
    (init_ir_supply (task009_label_fixture "old")) = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
