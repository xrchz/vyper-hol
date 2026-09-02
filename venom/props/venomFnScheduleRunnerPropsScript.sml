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

Theorem run_configured_fn_pass_fold_first_effects:
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s fn labels =
    SOME result ==>
  ?out. runner rpolicy pass unit s fn = SOME out /\
        fn_pass_effects_hold (fn_pass_tag pass) fn out
Proof
  simp[run_configured_fn_pass_fold_def] >>
  Cases_on `runner rpolicy pass unit s fn` >> simp[] >>
  Cases_on `x.fpo_function.fn_name = fn.fn_name /\
            fn_pass_effects_hold (fn_pass_tag pass) fn x /\
            introduces_no_invoke_edges fn x.fpo_function /\
            ir_supply_extends s x.fpo_supply /\
            ir_supply_covers_fn x.fpo_supply x.fpo_function /\
            ir_supply_covers_unit x.fpo_supply unit` >> simp[] >>
  metis_tac[]
QED

Theorem run_configured_fn_pass_fold_first_invoke:
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s fn labels =
    SOME result ==>
  ?out. runner rpolicy pass unit s fn = SOME out /\
        introduces_no_invoke_edges fn out.fpo_function
Proof
  simp[run_configured_fn_pass_fold_def] >>
  Cases_on `runner rpolicy pass unit s fn` >> simp[] >>
  Cases_on `x.fpo_function.fn_name = fn.fn_name /\
            fn_pass_effects_hold (fn_pass_tag pass) fn x /\
            introduces_no_invoke_edges fn x.fpo_function /\
            ir_supply_extends s x.fpo_supply /\
            ir_supply_covers_fn x.fpo_supply x.fpo_function /\
            ir_supply_covers_unit x.fpo_supply unit` >> simp[] >>
  metis_tac[]
QED

Theorem run_configured_fn_pass_fold_first_supply:
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s fn labels =
    SOME result ==>
  ?out. runner rpolicy pass unit s fn = SOME out /\
        ir_supply_extends s out.fpo_supply /\
        ir_supply_covers_fn out.fpo_supply out.fpo_function /\
        ir_supply_covers_unit out.fpo_supply unit
Proof
  simp[run_configured_fn_pass_fold_def] >>
  Cases_on `runner rpolicy pass unit s fn` >> simp[] >>
  Cases_on `x.fpo_function.fn_name = fn.fn_name /\
            fn_pass_effects_hold (fn_pass_tag pass) fn x /\
            introduces_no_invoke_edges fn x.fpo_function /\
            ir_supply_extends s x.fpo_supply /\
            ir_supply_covers_fn x.fpo_supply x.fpo_function /\
            ir_supply_covers_unit x.fpo_supply unit` >> simp[] >>
  metis_tac[]
QED
Theorem run_configured_fn_pass_fold_threads_current:
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s fn labels =
    SOME result ==>
  ?out. runner rpolicy pass unit s fn = SOME out /\
        run_configured_fn_pass_fold runner rpolicy passes unit
          out.fpo_supply out.fpo_function (labels ++ out.fpo_label_map) =
          SOME result
Proof
  simp[run_configured_fn_pass_fold_def] >>
  Cases_on `runner rpolicy pass unit s fn` >> simp[] >>
  Cases_on `x.fpo_function.fn_name = fn.fn_name /\
            fn_pass_effects_hold (fn_pass_tag pass) fn x /\
            introduces_no_invoke_edges fn x.fpo_function /\
            ir_supply_extends s x.fpo_supply /\
            ir_supply_covers_fn x.fpo_supply x.fpo_function /\
            ir_supply_covers_unit x.fpo_supply unit` >> simp[] >>
  metis_tac[]
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

val _ = export_theory ();
