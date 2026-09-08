(*
 * FCG postorder traversal properties.
 *)

Theory fcgPostorder
Ancestors
  cfgHelpers fcgCorrectnessProof fcgDefs cfgDefs pred_set venomWf venomInst relation

Theorem fcg_postorder_all_distinct:
  ∀fcg entry. ALL_DISTINCT (fcg_postorder fcg entry)
Proof
  simp[fcg_postorder_def, dfs_post_walk_distinct]
QED

Theorem fmap_lookup_list_fcg_callees:
  ∀fcg fn_name.
    fmap_lookup_list fcg.fcg_callees fn_name =
    fcg_get_callees fcg fn_name
Proof
  simp[fmap_lookup_list_def, fcg_get_callees_def]
QED

Definition fcg_callee_edge_def:
  fcg_callee_edge fcg caller callee ⇔
    MEM callee (fmap_lookup_list fcg.fcg_callees caller)
End

Definition fcg_callee_rtc_def:
  fcg_callee_rtc fcg source target ⇔
    RTC (fcg_callee_edge fcg) source target
End

Theorem fcg_callees_rtc_in_context:
  ∀ctx entry target.
    ctx_wf ctx ∧ wf_invoke_targets ctx ∧
    MEM entry (ctx_fn_names ctx) ∧
    RTC (fcg_callee_edge (fcg_analyze ctx)) entry target ⇒
    MEM target (ctx_fn_names ctx)
Proof
  rpt strip_tac >>
  qpat_x_assum `RTC _ entry target` mp_tac >>
  qid_spec_tac `target` >>
  ho_match_mp_tac RTC_ALT_RIGHT_INDUCT >>
  conj_tac >- simp[] >>
  rpt strip_tac >>
  gvs[fcg_callee_edge_def, fmap_lookup_list_fcg_callees] >>
  drule_all fcg_analyze_callees_in_context_proof >> simp[]
QED

Theorem fcg_postorder_mem_reachable:
  ∀ctx entry target.
    ctx_wf ctx ∧ wf_invoke_targets ctx ∧
    ctx.ctx_entry = SOME entry ∧
    MEM target (fcg_postorder (fcg_analyze ctx) entry) ⇒
    fcg_is_reachable (fcg_analyze ctx) target
Proof
  rpt strip_tac >> fs[fcg_postorder_def] >>
  `MEM entry (ctx_fn_names ctx)` by
    (gvs[ctx_wf_def, ctx_has_entry_def] >> metis_tac[]) >>
  `RTC (fcg_callee_edge (fcg_analyze ctx)) entry target` by
    (drule dfs_post_walk_sound_thm >> strip_tac >>
     irule RTC_MONOTONE >>
     qexists `λa b.
       MEM b (fmap_lookup_list (fcg_analyze ctx).fcg_callees a)` >>
     simp[fcg_callee_edge_def]) >>
  `∀a b. fcg_callee_edge (fcg_analyze ctx) a b ⇒
          fn_directly_calls ctx a b` by
    (rpt strip_tac >>
     irule fcg_analyze_callees_sound_proof >>
     gvs[fcg_callee_edge_def, fmap_lookup_list_fcg_callees]) >>
  `fcg_path ctx entry target` by
    (simp[fcg_path_def] >> irule RTC_MONOTONE >>
     qexists `fcg_callee_edge (fcg_analyze ctx)` >> simp[]) >>
  `MEM target (ctx_fn_names ctx)` by
    (drule_all fcg_callees_rtc_in_context >> simp[]) >>
  irule fcg_analyze_reachable_complete_proof >> simp[]
QED


Theorem fcg_path_callee_rtc:
  ∀ctx entry target.
    ctx_wf ctx ∧ ctx.ctx_entry = SOME entry ∧
    fcg_path ctx entry target ⇒
    fcg_callee_rtc (fcg_analyze ctx) entry target
Proof
  rpt strip_tac >> fs[fcg_path_def, fcg_callee_rtc_def] >>
  `∀target. RTC (fn_directly_calls ctx) entry target ⇒
      RTC (fn_directly_calls ctx) entry target ∧
      RTC (fcg_callee_edge (fcg_analyze ctx)) entry target`
    suffices_by metis_tac[] >>
  ho_match_mp_tac RTC_ALT_RIGHT_INDUCT >>
  conj_tac >- simp[] >>
  rpt strip_tac >>
  rename1 `fn_directly_calls ctx caller callee` >>
  `MEM caller (ctx_fn_names ctx)` by
    (gvs[fn_directly_calls_def, ctx_fn_names_def] >>
     imp_res_tac lookup_function_mem >> simp[listTheory.MEM_MAP] >>
     qexists_tac `func` >> simp[]) >>
  `fcg_is_reachable (fcg_analyze ctx) caller` by
    (irule fcg_analyze_reachable_complete_proof >>
     simp[fcg_path_def]) >>
  `fcg_callee_edge (fcg_analyze ctx) caller callee` by
    (gvs[fcg_callee_edge_def, fmap_lookup_list_fcg_callees] >>
     irule fcg_analyze_callees_complete_proof >> simp[]) >>
  irule (CONJUNCT2 (SPEC_ALL RTC_RULES_RIGHT1))
  >- (qexists `caller` >> simp[])
  >> qexists `caller` >> simp[]
QED
Theorem fcg_reachable_mem_postorder:
  ∀ctx entry target.
    ctx_wf ctx ∧ wf_invoke_targets ctx ∧
    ctx.ctx_entry = SOME entry ∧
    fcg_is_reachable (fcg_analyze ctx) target ⇒
    MEM target (fcg_postorder (fcg_analyze ctx) entry)
Proof
  rpt strip_tac >>
  drule_all fcg_analyze_reachable_sound_proof >> strip_tac >>
  gvs[] >>
  `RTC (fcg_callee_edge (fcg_analyze ctx)) entry target` by
    (drule_all fcg_path_callee_rtc >> simp[fcg_callee_rtc_def]) >>
  simp[fcg_postorder_def] >>
  irule dfs_post_walk_complete >>
  irule RTC_MONOTONE >>
  qexists `fcg_callee_edge (fcg_analyze ctx)` >>
  simp[fcg_callee_edge_def]
QED

Theorem fcg_postorder_reachable_set:
  ∀ctx entry.
    ctx_wf ctx ∧ wf_invoke_targets ctx ∧
    ctx.ctx_entry = SOME entry ⇒
    set (fcg_postorder (fcg_analyze ctx) entry) =
    set (fcg_analyze ctx).fcg_reachable
Proof
  rw[EXTENSION] >> iff_tac >> strip_tac
  >- (drule_all fcg_postorder_mem_reachable >>
      simp[fcg_is_reachable_def])
  >> irule fcg_reachable_mem_postorder
  >> simp[fcg_is_reachable_def]
QED

Theorem reachable_fcg_acyclic_direct_edge_rank:
  fcg = fcg_analyze ctx /\ ctx.ctx_entry = SOME entry /\
  ctx_wf ctx /\ wf_invoke_targets ctx /\
  reachable_fcg_acyclic ctx fcg /\
  fn_directly_calls ctx caller callee /\
  fcg_is_reachable fcg caller ==>
  ?callee_i caller_i.
    list_index callee (fcg_postorder fcg entry) = SOME callee_i /\
    list_index caller (fcg_postorder fcg entry) = SOME caller_i /\
    callee_i < caller_i
Proof
  rpt strip_tac >>
  gvs[reachable_fcg_acyclic_def, fcg_is_reachable_def, listTheory.EVERY_MEM] >>
  `MEM callee (fcg_get_callees (fcg_analyze ctx) caller)` by
    (irule fcg_analyze_callees_complete_proof >>
     simp[fcg_is_reachable_def]) >>
  res_tac >>
  gvs[list_precedes_iff]
QED


Theorem fcg_postorder_callee_before_caller:
  fcg = fcg_analyze ctx /\ ctx.ctx_entry = SOME entry /\
  ctx_wf ctx /\ wf_invoke_targets ctx /\
  reachable_fcg_acyclic ctx fcg /\
  fn_directly_calls ctx caller callee /\
  fcg_is_reachable fcg caller ==>
  ?callee_i caller_i.
    list_index callee (fcg_postorder fcg entry) = SOME callee_i /\
    list_index caller (fcg_postorder fcg entry) = SOME caller_i /\
    callee_i < caller_i
Proof
  metis_tac[reachable_fcg_acyclic_direct_edge_rank]
QED

Theorem fcg_reachable_direct_callee:
  fcg = fcg_analyze ctx /\ ctx.ctx_entry = SOME entry /\
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

Theorem reachable_fcg_acyclic_tc_rank:
  fcg = fcg_analyze ctx /\ ctx.ctx_entry = SOME entry /\
  ctx_wf ctx /\ wf_invoke_targets ctx /\
  reachable_fcg_acyclic ctx fcg /\
  fcg_is_reachable fcg source /\
  TC (fn_directly_calls ctx) source target ==>
  fcg_is_reachable fcg target /\
  ?target_i source_i.
    list_index target (fcg_postorder fcg entry) = SOME target_i /\
    list_index source (fcg_postorder fcg entry) = SOME source_i /\
    target_i < source_i
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `fcg_is_reachable fcg source` mp_tac >>
  qpat_x_assum `TC _ source target` mp_tac >>
  qid_spec_tac `target` >> qid_spec_tac `source` >>
  ho_match_mp_tac TC_INDUCT >>
  conj_tac
  >- (rpt strip_tac >>
      `fcg_is_reachable fcg target` by
        (drule_all fcg_reachable_direct_callee >> simp[]) >>
      drule_all reachable_fcg_acyclic_direct_edge_rank >> simp[])
  >> rpt gen_tac >> strip_tac >> strip_tac >>
  conj_tac
  >- metis_tac[]
  >> qpat_x_assum `fcg_is_reachable fcg source ==> _` mp_tac >>
  simp[] >> strip_tac >>
  qpat_x_assum `fcg_is_reachable fcg source' ==> _` mp_tac >>
  simp[] >> strip_tac >>
  qexists `target_i'` >>
  gvs[]
QED

Theorem reachable_fcg_acyclic_no_reachable_cycle:
  fcg = fcg_analyze ctx /\ ctx.ctx_entry = SOME entry /\
  ctx_wf ctx /\ wf_invoke_targets ctx /\
  reachable_fcg_acyclic ctx fcg /\
  fcg_is_reachable fcg name ==>
  ~TC (fn_directly_calls ctx) name name
Proof
  rpt strip_tac >>
  drule_all reachable_fcg_acyclic_tc_rank >>
  simp[]
QED
