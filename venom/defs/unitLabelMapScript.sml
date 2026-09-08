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

Theorem fn_labels_subst_label_map_fn[simp]:
  fn_labels (subst_label_map_fn label_map fn) = fn_labels fn
Proof
  simp[venomInstTheory.fn_labels_def, subst_label_map_fn_def,
       subst_label_map_block_def, listTheory.MAP_MAP_o,
       combinTheory.o_DEF]
QED

Theorem apply_resolved_unit_label_map_namespace[simp]:
  unit_label_namespace (apply_resolved_unit_label_map resolved unit) =
  unit_label_namespace unit
Proof
  simp[apply_resolved_unit_label_map_def, unit_label_namespace_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]
QED

Theorem map_unit_data_item_refs_valid:
  EVERY (\label. MEM label namespace) (data_item_label_refs item) /\
  (!entry. MEM entry resolved ==> MEM (SND entry) namespace) ==>
  EVERY (\label. MEM label namespace)
    (data_item_label_refs (map_unit_data_item resolved item))
Proof
  Cases_on `item` >>
  simp[data_item_label_refs_def, map_unit_data_item_def] >>
  Cases_on `ALOOKUP resolved s` >> gvs[] >>
  strip_tac >> drule alistTheory.ALOOKUP_MEM >>
  disch_then assume_tac >>
  first_x_assum (qspec_then `(s,x)` mp_tac) >> simp[]
QED

Theorem unit_data_labels_consistent_sections:
  unit_data_labels_consistent unit <=>
  EVERY (\section.
    EVERY (\item.
      EVERY (\label. MEM label (unit_label_namespace unit))
        (data_item_label_refs item)) section.ds_items)
    unit.cu_data_segment
Proof
  simp[unit_data_labels_consistent_def, unit_data_label_refs_def,
       data_section_label_refs_def, listTheory.EVERY_FLAT,
       listTheory.EVERY_MAP]
QED

Theorem apply_resolved_unit_label_map_data_consistent:
  unit_data_labels_consistent unit /\
  resolved_label_endpoints_valid unit resolved ==>
  unit_data_labels_consistent
    (apply_resolved_unit_label_map resolved unit)
Proof
  simp[unit_data_labels_consistent_sections,
       resolved_label_endpoints_valid_def,
       apply_resolved_unit_label_map_def, map_unit_data_section_def,
       listTheory.EVERY_MAP, Excl "MEM_unit_label_namespace"] >>
  strip_tac >> gvs[listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  Cases_on `x'` >> gvs[map_unit_data_item_def] >>
  Cases_on `ALOOKUP resolved s` >> gvs[]
  >- metis_tac[] >>
  drule alistTheory.ALOOKUP_MEM >> disch_then assume_tac >>
  qpat_x_assum `!entry. MEM entry resolved ==> _`
    (qspec_then `(s,x')` mp_tac) >> simp[]
QED

Theorem apply_unit_label_map_namespace:
  apply_unit_label_map label_map unit = SOME unit' ==>
  unit_label_namespace unit' = unit_label_namespace unit
Proof
  simp[apply_unit_label_map_def] >>
  Cases_on `resolve_label_map label_map` >> simp[] >>
  Cases_on `resolved_label_endpoints_valid unit x` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem apply_unit_label_map_context_data_consistent:
  unit_labels_wf unit /\
  apply_unit_label_map label_map unit = SOME unit' ==>
  unit_labels_wf unit'
Proof
  simp[apply_unit_label_map_def] >>
  Cases_on `resolve_label_map label_map` >> simp[] >>
  Cases_on `resolved_label_endpoints_valid unit x` >> simp[] >>
  strip_tac >>
  gvs[unit_labels_wf_def] >>
  irule apply_resolved_unit_label_map_data_consistent >> simp[]
QED

val _ = export_theory ();
