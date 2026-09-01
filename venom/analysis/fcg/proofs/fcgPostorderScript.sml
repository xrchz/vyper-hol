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


(* Kernel-checked computations exercising ordinary, cyclic, and unreachable
 * call-graph shapes. *)
Definition fcg_postorder_acyclic_test_fcg_def[local]:
  fcg_postorder_acyclic_test_fcg =
    fcg_empty with fcg_callees :=
      FEMPTY |+ ("a", ["b"; "c"]) |+ ("b", ["c"])
End

Definition fcg_postorder_self_cycle_test_fcg_def[local]:
  fcg_postorder_self_cycle_test_fcg =
    fcg_empty with fcg_callees := FEMPTY |+ ("a", ["a"])
End

Definition fcg_postorder_mutual_cycle_test_fcg_def[local]:
  fcg_postorder_mutual_cycle_test_fcg =
    fcg_empty with fcg_callees :=
      FEMPTY |+ ("a", ["b"]) |+ ("b", ["a"])
End

Definition fcg_postorder_unreachable_test_fcg_def[local]:
  fcg_postorder_unreachable_test_fcg =
    fcg_empty with fcg_callees :=
      FEMPTY |+ ("a", ["b"]) |+ ("u", ["a"])
End

Theorem fcg_postorder_edge_case_evaluations:
  fcg_postorder fcg_postorder_acyclic_test_fcg "a" = ["c"; "b"; "a"] ∧
  fcg_postorder fcg_postorder_self_cycle_test_fcg "a" = ["a"] ∧
  fcg_postorder fcg_postorder_mutual_cycle_test_fcg "a" = ["b"; "a"] ∧
  ¬MEM "u" (fcg_postorder fcg_postorder_unreachable_test_fcg "a") ∧
  ALL_DISTINCT (fcg_postorder fcg_postorder_self_cycle_test_fcg "a") ∧
  ALL_DISTINCT (fcg_postorder fcg_postorder_mutual_cycle_test_fcg "a")
Proof
  EVAL_TAC
QED
