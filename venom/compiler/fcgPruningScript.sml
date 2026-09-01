(*
 * Pruning of compilation units using a frozen function-call graph.
 *)

Theory fcgPruning
Ancestors
  fcgCorrectnessProof fcgDefs venomCompilerWf irSupply venomInst

Definition prune_unit_fcg_unreachable_def:
  prune_unit_fcg_unreachable unit fcg =
    unit with cu_context :=
      unit.cu_context with ctx_functions :=
        FILTER (\fn. fcg_is_reachable fcg fn.fn_name)
               unit.cu_context.ctx_functions
End

Theorem MAP_FILTER_fn_name_reachable[local]:
  !fns.
  MAP (\fn. fn.fn_name)
      (FILTER (\fn. fcg_is_reachable fcg fn.fn_name) fns) =
  FILTER (\name. fcg_is_reachable fcg name)
         (MAP (\fn. fn.fn_name) fns)
Proof
  Induct >> simp[] >> gen_tac >>
  Cases_on `fcg_is_reachable fcg h.fn_name` >> gvs[]
QED

Theorem prune_fcg_unreachable_names:
  MAP (\fn. fn.fn_name)
      (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions =
  FILTER (\name. fcg_is_reachable fcg name)
         (MAP (\fn. fn.fn_name) unit.cu_context.ctx_functions)
Proof
  simp[prune_unit_fcg_unreachable_def, MAP_FILTER_fn_name_reachable]
QED

Theorem prune_unit_fcg_unreachable_fields:
  (prune_unit_fcg_unreachable unit fcg).cu_data_segment =
    unit.cu_data_segment /\
  (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_entry =
    unit.cu_context.ctx_entry /\
  (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_global_reserved =
    unit.cu_context.ctx_global_reserved
Proof
  simp[prune_unit_fcg_unreachable_def]
QED

Theorem MEM_prune_unit_fcg_unreachable_functions:
  MEM fn (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions <=>
  MEM fn unit.cu_context.ctx_functions /\
  fcg_is_reachable fcg fn.fn_name
Proof
  simp[prune_unit_fcg_unreachable_def, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

Theorem lookup_function_FILTER_reachable[local]:
  !fns.
  fcg_is_reachable fcg name ==>
  lookup_function name
    (FILTER (\fn. fcg_is_reachable fcg fn.fn_name) fns) =
  lookup_function name fns
Proof
  Induct >> simp[lookup_function_def, listTheory.FIND_thm] >>
  rpt strip_tac >>
  Cases_on `fcg_is_reachable fcg h.fn_name` >> simp[] >>
  Cases_on `h.fn_name = name` >>
  gvs[lookup_function_def, listTheory.FIND_thm]
QED

Theorem lookup_function_prune_fcg_reachable:
  fcg_is_reachable fcg name ==>
  lookup_function name
    (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions =
  lookup_function name unit.cu_context.ctx_functions
Proof
  simp[prune_unit_fcg_unreachable_def, lookup_function_FILTER_reachable]
QED

Theorem prune_fcg_function_names_subset:
  MEM name (ctx_fn_names
    (prune_unit_fcg_unreachable unit fcg).cu_context) ==>
  MEM name (ctx_fn_names unit.cu_context)
Proof
  simp[ctx_fn_names_def, prune_fcg_unreachable_names,
       listTheory.MEM_FILTER]
QED

Theorem prune_fcg_inst_ids_subset:
  MEM id (unit_ir_inst_ids (prune_unit_fcg_unreachable unit fcg)) ==>
  MEM id (unit_ir_inst_ids unit)
Proof
  simp[MEM_unit_ir_inst_ids] >>
  metis_tac[MEM_prune_unit_fcg_unreachable_functions]
QED

Theorem prune_fcg_labels_subset:
  MEM label (unit_ir_labels (prune_unit_fcg_unreachable unit fcg)) ==>
  MEM label (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, prune_unit_fcg_unreachable_def,
       listTheory.MEM_FLAT, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

Theorem lookup_function_exists_for_name_local[local]:
  !name fns.
  MEM name (MAP (\fn. fn.fn_name) fns) ==>
  ?found. lookup_function name fns = SOME found
Proof
  Induct_on `fns`
  >- simp[lookup_function_def, listTheory.FIND_thm]
  >> rpt strip_tac >> Cases_on `h.fn_name = name`
  >- (qexists `h` >> simp[lookup_function_def, listTheory.FIND_thm])
  >> gvs[] >> first_x_assum drule >> strip_tac >>
  qexists `found` >> gvs[lookup_function_def, listTheory.FIND_thm]
QED

Theorem lookup_function_name[local]:
  !fns name fn.
  lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct >>
  simp[lookup_function_def, listTheory.FIND_thm] >>
  rpt strip_tac >>
  Cases_on `h.fn_name = name` >> gvs[lookup_function_def]
QED

Theorem prune_fcg_no_new_edges:
  fn_directly_calls
    (prune_unit_fcg_unreachable unit fcg).cu_context caller callee ==>
  fn_directly_calls unit.cu_context caller callee
Proof
  simp[fn_directly_calls_def] >> rpt strip_tac >>
  qexistsl [`func`, `inst`, `rest`] >> simp[] >>
  drule lookup_function_name >> strip_tac >>
  drule lookup_function_MEM >>
  simp[prune_unit_fcg_unreachable_def, listTheory.MEM_FILTER] >>
  strip_tac >> gvs[] >>
  `lookup_function func.fn_name
      (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions =
   lookup_function func.fn_name unit.cu_context.ctx_functions` by
    (irule lookup_function_prune_fcg_reachable >> simp[]) >>
  gvs[]
QED

Theorem END_OF_fcgPruning:
  T
Proof
  simp[]
QED

