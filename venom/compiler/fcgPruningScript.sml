(*
 * Pruning of compilation units using a frozen function-call graph.
 *)

Theory fcgPruning
Ancestors
  fcgPostorder fcgVisit fcgCorrectnessProof fcgDefs venomWf venomCompilerWf
  irSupply venomInst relation

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

Theorem distinct_function_names_unique_local[local]:
  !fns fn1 fn2 name.
  ALL_DISTINCT (MAP (\fn. fn.fn_name) fns) /\
  MEM fn1 fns /\ MEM fn2 fns /\
  fn1.fn_name = name /\ fn2.fn_name = name ==>
  fn1 = fn2
Proof
  Induct_on `fns`
  >- simp[]
  >> rpt strip_tac >>
  Cases_on `fn1 = h` >> Cases_on `fn2 = h` >>
  gvs[listTheory.MEM_MAP] >> metis_tac[]
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


Theorem lookup_function_of_MEM_distinct_names[local]:
  !fns fn.
  ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\ MEM fn fns ==>
  lookup_function fn.fn_name fns = SOME fn
Proof
  rpt strip_tac >>
  `MEM fn.fn_name (MAP (\f. f.fn_name) fns)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  drule lookup_function_exists_for_name_local >> strip_tac >>
  `MEM found fns` by metis_tac[lookup_function_MEM] >>
  `found.fn_name = fn.fn_name` by metis_tac[lookup_function_name] >>
  `found = fn` by metis_tac[distinct_function_names_unique_local] >>
  gvs[]
QED

Theorem prune_fcg_reachable_direct_callee:
  fcg = fcg_analyze ctx /\
  ctx_wf ctx /\ wf_invoke_targets ctx /\
  fcg_is_reachable fcg caller /\
  fn_directly_calls ctx caller callee ==>
  fcg_is_reachable fcg callee
Proof
  rpt strip_tac >> gvs[] >>
  drule_all fcg_analyze_reachable_sound_proof >> strip_tac >> gvs[] >>
  `MEM callee (ctx_fn_names ctx)` by
    (gvs[fn_directly_calls_def, wf_invoke_targets_def,
         ctx_fn_names_def] >>
     imp_res_tac lookup_function_MEM >> res_tac >> gvs[]) >>
  irule fcg_analyze_reachable_complete_proof >> simp[] >>
  fs[fcg_path_def] >>
  irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1)) >>
  qexists `caller` >> simp[]
QED


Theorem ctx_wf_prune_unit_fcg_unreachable:
  fcg = fcg_analyze unit.cu_context /\
  ctx_wf unit.cu_context ==>
  ctx_wf (prune_unit_fcg_unreachable unit fcg).cu_context
Proof
  rpt strip_tac >>
  gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_has_entry_def,
      ctx_fn_names_def] >>
  conj_tac
  >- (rewrite_tac[prune_fcg_unreachable_names] >>
      irule listTheory.FILTER_ALL_DISTINCT >> simp[])
  >> qexists `entry_name` >> conj_tac
  >- simp[prune_unit_fcg_unreachable_def]
  >> rewrite_tac[prune_fcg_unreachable_names] >>
  simp[listTheory.MEM_FILTER] >>
  irule fcg_analyze_reachable_complete_proof >>
  simp[ctx_wf_def, ctx_distinct_fn_names_def, ctx_has_entry_def,
       ctx_fn_names_def, fcg_path_def, relationTheory.RTC_REFL]
QED

Theorem wf_invoke_targets_prune_unit_fcg_unreachable:
  fcg = fcg_analyze unit.cu_context /\
  ctx_wf unit.cu_context /\
  wf_invoke_targets unit.cu_context ==>
  wf_invoke_targets (prune_unit_fcg_unreachable unit fcg).cu_context
Proof
  rpt strip_tac >>
  rw[wf_invoke_targets_def] >> rpt strip_tac >>
  drule (iffLR MEM_prune_unit_fcg_unreachable_functions) >> strip_tac >>
  qpat_assum `wf_invoke_targets unit.cu_context`
    (fn th => qspecl_then [`func`, `inst`] mp_tac
      (REWRITE_RULE [wf_invoke_targets_def] th)) >>
  simp[] >> strip_tac >>
  qexistsl [`lbl`, `rest`] >> simp[] >>
  rewrite_tac[ctx_fn_names_def, prune_fcg_unreachable_names] >>
  simp[listTheory.MEM_FILTER] >>
  `lookup_function func.fn_name unit.cu_context.ctx_functions = SOME func` by
    (irule lookup_function_of_MEM_distinct_names >>
     gvs[ctx_wf_def, ctx_distinct_fn_names_def, ctx_fn_names_def]) >>
  `fn_directly_calls unit.cu_context func.fn_name lbl` by
    (simp[fn_directly_calls_def] >>
     qexistsl [`inst`, `rest`] >> simp[]) >>
  conj_tac
  >- (drule_all fcg_analyze_reachable_sound_proof >> strip_tac >> gvs[] >>
      irule fcg_analyze_reachable_complete_proof >> simp[] >>
      fs[fcg_path_def] >>
      irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1)) >>
      qexists `func.fn_name` >> simp[])
  >> gvs[ctx_fn_names_def]
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


Theorem fcg_dfs_lookup_sim[local]:
  !ctx1 stack visited graph.
  (!name. R name ==>
     lookup_function name ctx1.ctx_functions =
     lookup_function name ctx2.ctx_functions) /\
  (!name callee. R name /\ fn_directly_calls ctx2 name callee ==>
     R callee) /\
  (!name. MEM name stack ==> R name) ==>
  fcg_dfs ctx1 stack visited graph =
  fcg_dfs ctx2 stack visited graph
Proof
  recInduct fcg_dfs_ind >> rpt strip_tac >>
  simp[fcg_dfs_def] >>
  Cases_on `MEM fn_name visited`
  >- (gvs[] >> first_x_assum irule >> simp[] >> first_assum ACCEPT_TAC)
  >> gvs[] >>
  `R fn_name` by metis_tac[] >>
  `lookup_function fn_name ctx.ctx_functions =
   lookup_function fn_name ctx2.ctx_functions` by metis_tac[] >>
  `fcg_visit ctx fn_name fcg = fcg_visit ctx2 fn_name fcg` by
    simp[fcg_visit_def] >>
  Cases_on `fcg_visit ctx2 fn_name fcg` >> gvs[] >>
  first_x_assum irule >> conj_tac
  >- first_assum ACCEPT_TAC
  >> rpt strip_tac >> gvs[]
  >- (`fn_directly_calls ctx2 fn_name name` by
        (irule fcg_visit_fst_calls >> qexists `fcg` >> simp[]) >>
      metis_tac[])
  >> metis_tac[]
QED

Theorem fcg_analyze_prune_unit_fcg_unreachable:
  fcg = fcg_analyze unit.cu_context /\
  ctx_wf unit.cu_context /\
  wf_invoke_targets unit.cu_context ==>
  fcg_analyze (prune_unit_fcg_unreachable unit fcg).cu_context = fcg
Proof
  rpt strip_tac >> gvs[] >>
  gvs[ctx_wf_def, ctx_has_entry_def] >>
  simp[fcg_analyze_def, prune_unit_fcg_unreachable_def] >>
  irule fcg_dfs_lookup_sim >>
  qexists `(\name. fcg_is_reachable (fcg_analyze unit.cu_context) name)` >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `ctx_wf unit.cu_context` by
        simp[ctx_wf_def, ctx_has_entry_def] >>
      drule_all fcg_analyze_reachable_sound_proof >> strip_tac >> gvs[] >>
      `MEM callee (ctx_fn_names unit.cu_context)` by
        (gvs[fn_directly_calls_def, wf_invoke_targets_def,
             ctx_fn_names_def] >>
         imp_res_tac lookup_function_MEM >> res_tac >> gvs[]) >>
      irule fcg_analyze_reachable_complete_proof >> simp[] >>
      fs[fcg_path_def] >>
      irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1)) >>
      qexists `name` >> simp[])
  >> conj_tac
  >- (rpt strip_tac >> gvs[] >>
      irule lookup_function_FILTER_reachable >>
      gvs[fcg_analyze_def])
  >> rpt strip_tac >> gvs[] >>
  irule fcg_analyze_reachable_complete_proof >>
  simp[ctx_wf_def, ctx_has_entry_def, fcg_path_def,
       relationTheory.RTC_REFL]
QED

Theorem prune_fcg_analyzed_callees:
  fcg = fcg_analyze unit.cu_context /\
  ctx_wf unit.cu_context /\
  wf_invoke_targets unit.cu_context ==>
  fcg_get_callees
    (fcg_analyze (prune_unit_fcg_unreachable unit fcg).cu_context) name =
  fcg_get_callees fcg name
Proof
  rpt strip_tac >>
  drule_all fcg_analyze_prune_unit_fcg_unreachable >> simp[]
QED

Theorem prune_fcg_analyzed_reachable:
  fcg = fcg_analyze unit.cu_context /\
  ctx_wf unit.cu_context /\
  wf_invoke_targets unit.cu_context ==>
  (fcg_analyze
    (prune_unit_fcg_unreachable unit fcg).cu_context).fcg_reachable =
  fcg.fcg_reachable
Proof
  rpt strip_tac >>
  drule_all fcg_analyze_prune_unit_fcg_unreachable >> simp[]
QED

Theorem prune_fcg_postorder_lookup:
  fcg = fcg_analyze unit.cu_context /\
  ctx_wf unit.cu_context /\
  wf_invoke_targets unit.cu_context /\
  unit.cu_context.ctx_entry = SOME entry /\
  MEM name (fcg_postorder fcg entry) ==>
  ?fn.
    lookup_function name unit.cu_context.ctx_functions = SOME fn /\
    lookup_function name
      (prune_unit_fcg_unreachable unit fcg).cu_context.ctx_functions = SOME fn
Proof
  rpt strip_tac >>
  `fcg_is_reachable fcg name` by
    (gvs[] >> irule fcg_postorder_mem_reachable >> simp[]) >>
  `MEM name (ctx_fn_names unit.cu_context)` by
    (gvs[] >> irule fcg_analyze_reachable_in_context_proof >> simp[]) >>
  gvs[ctx_fn_names_def] >>
  drule lookup_function_exists_for_name_local >> strip_tac >>
  qexists `found` >> simp[] >>
  `lookup_function name
      (prune_unit_fcg_unreachable unit
        (fcg_analyze unit.cu_context)).cu_context.ctx_functions =
   lookup_function name unit.cu_context.ctx_functions` by
    (irule lookup_function_prune_fcg_reachable >> simp[]) >>
  gvs[]
QED
