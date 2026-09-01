(*
 * Pruning of compilation units using a frozen function-call graph.
 *)

Theory fcgPruning
Ancestors
  fcgCorrectnessProof venomCompilerWf irSupply

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

Theorem END_OF_fcgPruning:
  T
Proof
  simp[]
QED

