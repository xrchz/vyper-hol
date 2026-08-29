(*
 * Checked, chain-compressing compilation-unit label maps.
 *)

Theory unitLabelMap
Ancestors
  venomCompilerWf
  cfgTransform

Definition resolve_label_fuel_def:
  resolve_label_fuel label_map visited 0 label =
    (case ALOOKUP label_map label of
       NONE => SOME label
     | SOME next => NONE) /\
  resolve_label_fuel label_map visited (SUC fuel) label =
    if MEM label visited then NONE
    else
      case ALOOKUP label_map label of
        NONE => SOME label
      | SOME next =>
          resolve_label_fuel label_map (label::visited) fuel next
End

Definition resolve_label_entries_def:
  resolve_label_entries label_map fuel [] = SOME [] /\
  resolve_label_entries label_map fuel ((source,target)::rest) =
    case resolve_label_fuel label_map [] fuel source of
      NONE => NONE
    | SOME terminal =>
        case resolve_label_entries label_map fuel rest of
          NONE => NONE
        | SOME resolved => SOME ((source,terminal)::resolved)
End

Definition resolve_label_map_def:
  resolve_label_map label_map =
    if ALL_DISTINCT (MAP FST label_map) then
      resolve_label_entries label_map (SUC (LENGTH label_map)) label_map
    else NONE
End

Theorem resolve_label_map_singleton:
  a <> b ==> resolve_label_map [(a,b)] = SOME [(a,b)]
Proof
  strip_tac >>
  EVAL_TAC >> gvs[]
QED

Theorem resolve_label_map_two_link:
  ALL_DISTINCT [a;b;c] ==>
  resolve_label_map [(a,b);(b,c)] = SOME [(a,c);(b,c)]
Proof
  strip_tac >> EVAL_TAC >> gvs[listTheory.ALL_DISTINCT]
QED

Theorem resolve_label_map_self_cycle[simp]:
  resolve_label_map [(a,a)] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_direct_eval:
  resolve_label_map [("a","b")] = SOME [("a","b")]
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_chain_eval:
  resolve_label_map [("a","b");("b","c")] =
    SOME [("a","c");("b","c")]
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_non_topological_chain_eval:
  resolve_label_map [("b","c");("a","b")] =
    SOME [("b","c");("a","c")]
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_two_cycle_eval:
  resolve_label_map [("a","b");("b","a")] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_three_cycle_eval:
  resolve_label_map [("a","b");("b","c");("c","a")] = NONE
Proof
  EVAL_TAC
QED

Theorem resolve_label_map_duplicate_domain_eval:
  resolve_label_map [("a","b");("a","c")] = NONE
Proof
  EVAL_TAC
QED

Definition map_unit_data_item_def:
  map_unit_data_item label_map (DataBytes bytes) = DataBytes bytes /\
  map_unit_data_item label_map (DataLabel label) =
    DataLabel (case ALOOKUP label_map label of
                 NONE => label
               | SOME new_label => new_label)
End

Definition map_unit_data_section_def:
  map_unit_data_section label_map section =
    section with ds_items := MAP (map_unit_data_item label_map) section.ds_items
End

Definition resolved_label_endpoints_valid_def:
  resolved_label_endpoints_valid unit resolved <=>
    EVERY (\entry. MEM (SND entry) (unit_label_namespace unit)) resolved
End

Definition apply_resolved_unit_label_map_def:
  apply_resolved_unit_label_map resolved unit =
    unit with <|
      cu_context := unit.cu_context with ctx_functions :=
        MAP (subst_label_map_fn resolved) unit.cu_context.ctx_functions;
      cu_data_segment :=
        MAP (map_unit_data_section resolved) unit.cu_data_segment
    |>
End

Definition apply_unit_label_map_def:
  apply_unit_label_map label_map unit =
    case resolve_label_map label_map of
      NONE => NONE
    | SOME resolved =>
        if resolved_label_endpoints_valid unit resolved then
          SOME (apply_resolved_unit_label_map resolved unit)
        else NONE
End

Theorem map_unit_data_item_bytes[simp]:
  map_unit_data_item label_map (DataBytes bytes) = DataBytes bytes
Proof
  simp[map_unit_data_item_def]
QED

Theorem map_unit_data_item_label[simp]:
  map_unit_data_item label_map (DataLabel label) =
  DataLabel (case ALOOKUP label_map label of
               NONE => label
             | SOME new_label => new_label)
Proof
  simp[map_unit_data_item_def]
QED

Definition task009_label_fixture_def:
  task009_label_fixture reference = <|
    cu_context := mk_venom_context
      [mk_raw_function "f"
        [<|bb_label := "old";
            bb_instructions :=
              [mk_inst 1 OFFSET [Label reference; Var "x"] ["out"]]|>;
         <|bb_label := "mid"; bb_instructions := []|>;
         <|bb_label := "new"; bb_instructions := []|>]]
      (SOME "f");
    cu_data_segment :=
      [<|ds_label := "table";
          ds_items := [DataLabel reference; DataBytes [1w; 2w]]|>]
  |>
End

Theorem apply_unit_label_map_direct_eval:
  apply_unit_label_map [("old","new")] (task009_label_fixture "old") =
  SOME (task009_label_fixture "new")
Proof
  EVAL_TAC
QED

Theorem apply_unit_label_map_chain_eval:
  apply_unit_label_map [("old","mid");("mid","new")]
    (task009_label_fixture "old") =
  SOME (task009_label_fixture "new")
Proof
  EVAL_TAC
QED

Theorem apply_unit_label_map_cycle_eval:
  apply_unit_label_map [("old","mid");("mid","old")]
    (task009_label_fixture "old") = NONE
Proof
  EVAL_TAC
QED

Theorem apply_unit_label_map_dangling_eval:
  apply_unit_label_map [("old","missing")]
    (task009_label_fixture "old") = NONE
Proof
  EVAL_TAC
QED

Theorem apply_unit_label_map_duplicate_source_eval:
  apply_unit_label_map [("old","mid");("old","new")]
    (task009_label_fixture "old") = NONE
Proof
  EVAL_TAC
QED

val _ = export_theory ();
