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

val _ = export_theory ();
