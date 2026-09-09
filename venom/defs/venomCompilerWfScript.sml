(*
 * Compilation-unit label namespace and well-formedness.
 *)

Theory venomCompilerWf
Ancestors
  venomCompilerTypes
  venomWf

Definition data_item_label_refs_def:
  data_item_label_refs (DataBytes bytes) = [] /\
  data_item_label_refs (DataLabel label) = [label]
End

Definition data_section_label_refs_def:
  data_section_label_refs section =
    FLAT (MAP data_item_label_refs section.ds_items)
End

Definition unit_data_label_refs_def:
  unit_data_label_refs unit =
    FLAT (MAP data_section_label_refs unit.cu_data_segment)
End

Definition unit_label_namespace_def:
  unit_label_namespace unit =
    FLAT (MAP fn_labels unit.cu_context.ctx_functions)
End

Definition unit_data_labels_consistent_def:
  unit_data_labels_consistent unit <=>
    EVERY (\label. MEM label (unit_label_namespace unit))
      (unit_data_label_refs unit)
End

Definition unit_labels_wf_def:
  unit_labels_wf unit <=>
    ALL_DISTINCT (unit_label_namespace unit) /\
    unit_data_labels_consistent unit
End

Definition unit_distinct_fn_names_def:
  unit_distinct_fn_names unit <=>
    ctx_distinct_fn_names unit.cu_context
End

Definition unit_global_inst_ids_distinct_def:
  unit_global_inst_ids_distinct unit <=>
    ctx_inst_ids_distinct unit.cu_context
End

Definition unit_wf_def:
  unit_wf unit <=>
    venom_wf unit.cu_context /\ unit_labels_wf unit
End

Theorem MEM_data_item_label_refs[simp]:
  MEM label (data_item_label_refs item) <=> item = DataLabel label
Proof
  Cases_on `item` >> simp[data_item_label_refs_def] >> metis_tac[]
QED

Theorem MEM_data_section_label_refs[simp]:
  MEM label (data_section_label_refs section) <=>
  MEM (DataLabel label) section.ds_items
Proof
  simp[data_section_label_refs_def, listTheory.MEM_FLAT,
       listTheory.MEM_MAP, PULL_EXISTS]
QED

Theorem MEM_unit_data_label_refs[simp]:
  MEM label (unit_data_label_refs unit) <=>
  ?section. MEM section unit.cu_data_segment /\
            MEM (DataLabel label) section.ds_items
Proof
  simp[unit_data_label_refs_def, listTheory.MEM_FLAT,
       listTheory.MEM_MAP, PULL_EXISTS, MEM_data_section_label_refs]
QED

Theorem MEM_unit_label_namespace[simp]:
  MEM label (unit_label_namespace unit) <=>
  ?fn. MEM fn unit.cu_context.ctx_functions /\ MEM label (fn_labels fn)
Proof
  simp[unit_label_namespace_def, listTheory.MEM_FLAT,
       listTheory.MEM_MAP, PULL_EXISTS]
QED

Theorem unit_wf_distinct_fn_names:
  unit_wf unit ==> ALL_DISTINCT (ctx_fn_names unit.cu_context)
Proof
  simp[unit_wf_def, venom_wf_def, ctx_wf_def, ctx_distinct_fn_names_def]
QED

Theorem unit_wf_global_inst_ids_distinct:
  unit_wf unit ==> ctx_inst_ids_distinct unit.cu_context
Proof
  simp[unit_wf_def, venom_wf_def]
QED

Theorem unit_wf_unit_distinct_fn_names:
  unit_wf unit ==> unit_distinct_fn_names unit
Proof
  simp[unit_wf_def, unit_distinct_fn_names_def, venom_wf_def,
       ctx_wf_def]
QED

Theorem unit_wf_unit_global_inst_ids_distinct:
  unit_wf unit ==> unit_global_inst_ids_distinct unit
Proof
  simp[unit_wf_def, unit_global_inst_ids_distinct_def, venom_wf_def]
QED

val _ = export_theory ();
