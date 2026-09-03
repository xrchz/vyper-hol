(*
 * Public structural properties of checked context spill plans.
 *)

Theory contextPlanProps
Ancestors
  contextPlanEomProofs contextPlanRegionProofs stackPlanGen stackPlanTypes venomLayout
  list

Theorem generate_context_plan_layout_wf:
  generate_context_plan ctx = SOME cp ==>
  context_plan_layout_wf cp
Proof
  simp[generate_context_plan_def, generate_context_plan_with_def] >>
  Cases_on `max_live_eom ctx`
  >- simp[] >>
  simp[] >>
  Cases_on `generate_context_regions generate_fn_plan ctx.ctx_functions
    <|cpa_regions := []; cpa_label_counter := 0;
      cpa_next_spill_base := x; cpa_peak_spill_end := 0|>`
  >- simp[] >>
  simp[finish_context_plan_def] >>
  strip_tac >> gvs[] >>
  `context_region_acc_wf x
     <|cpa_regions := []; cpa_label_counter := 0;
       cpa_next_spill_base := x; cpa_peak_spill_end := 0|>` by
    simp[context_region_acc_wf_def, ordered_spill_regions_def] >>
  drule_all generate_context_regions_layout_regular >>
  strip_tac >>
  gvs[context_plan_layout_wf_def, context_region_acc_wf_def] >>
  gvs[EVERY_MEM] >>
  qsuff_tac
    `MAX x x'.cpa_peak_spill_end <=
       ceil32 (MAX x x'.cpa_peak_spill_end)`
  >- simp[ceil32_aligned] >>
  MATCH_ACCEPT_TAC ceil32_ge
QED

Theorem generate_context_plan_region_names:
  generate_context_plan ctx = SOME cp ==>
  MAP (\r. r.sr_fn_name) cp.cp_regions =
    MAP (\fn. fn.fn_name) ctx.ctx_functions
Proof
  simp[generate_context_plan_def, generate_context_plan_with_def] >>
  Cases_on `max_live_eom ctx`
  >- simp[] >>
  simp[] >>
  Cases_on `generate_context_regions generate_fn_plan ctx.ctx_functions
    <|cpa_regions := []; cpa_label_counter := 0;
      cpa_next_spill_base := x; cpa_peak_spill_end := 0|>`
  >- simp[] >>
  simp[finish_context_plan_def] >>
  strip_tac >> gvs[] >>
  drule generate_context_regions_names >>
  simp[]
QED

Theorem generate_context_plan_initial_fmp_bound:
  generate_context_plan ctx = SOME cp ==>
  cp.cp_initial_fmp < dimword (:256)
Proof
  simp[generate_context_plan_def, generate_context_plan_with_def] >>
  Cases_on `max_live_eom ctx`
  >- simp[] >>
  simp[] >>
  Cases_on `generate_context_regions generate_fn_plan ctx.ctx_functions
    <|cpa_regions := []; cpa_label_counter := 0;
      cpa_next_spill_base := x; cpa_peak_spill_end := 0|>`
  >- simp[] >>
  simp[finish_context_plan_def] >>
  strip_tac >> gvs[]
QED


Theorem generate_context_plan_max_live_eom[local]:
  generate_context_plan ctx = SOME cp ==>
  max_live_eom ctx = SOME cp.cp_max_static_eom
Proof
  simp[generate_context_plan_def, generate_context_plan_with_def] >>
  Cases_on `max_live_eom ctx`
  >- simp[] >>
  simp[] >>
  Cases_on `generate_context_regions generate_fn_plan ctx.ctx_functions
    <|cpa_regions := []; cpa_label_counter := 0;
      cpa_next_spill_base := x; cpa_peak_spill_end := 0|>`
  >- simp[] >>
  simp[finish_context_plan_def] >>
  strip_tac >> gvs[]
QED

Theorem spill_regions_static_disjoint:
  generate_context_plan ctx = SOME cp /\
  MEM fn ctx.ctx_functions /\ fn.fn_eom = SOME eom /\
  MEM r cp.cp_regions ==>
  eom <= r.sr_spill_base
Proof
  rpt strip_tac >>
  drule generate_context_plan_max_live_eom >>
  disch_then (fn th => assume_tac th) >>
  drule_all max_live_eom_bound >>
  drule generate_context_plan_layout_wf >>
  simp[context_plan_layout_wf_def, EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem spill_regions_global_disjoint:
  generate_context_plan ctx = SOME cp /\
  MEM ((pos : num),(sz : num)) ctx.ctx_global_reserved /\
  MEM r cp.cp_regions ==>
  pos + sz <= r.sr_spill_base
Proof
  rpt strip_tac >>
  drule generate_context_plan_max_live_eom >>
  disch_then (fn th => assume_tac th) >>
  drule_all max_live_eom_global_bound >>
  drule generate_context_plan_layout_wf >>
  simp[context_plan_layout_wf_def, EVERY_MEM] >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ordered_spill_regions_EL[local]:
  !rs i j.
    ordered_spill_regions rs /\ i < j /\ j < LENGTH rs ==>
    (EL i rs).sr_spill_end <= (EL j rs).sr_spill_base
Proof
  Induct_on `rs`
  >- simp[] >>
  rpt gen_tac >>
  Cases_on `i`
  >- (Cases_on `j` >>
      gvs[ordered_spill_regions_def, EVERY_MEM] >>
      metis_tac[EL_MEM]) >>
  Cases_on `j` >>
  gvs[ordered_spill_regions_def]
QED

Theorem spill_regions_pairwise_disjoint:
  generate_context_plan ctx = SOME cp /\
  i < j /\ j < LENGTH cp.cp_regions ==>
  (EL i cp.cp_regions).sr_spill_end <=
  (EL j cp.cp_regions).sr_spill_base
Proof
  rpt strip_tac >>
  drule generate_context_plan_layout_wf >>
  simp[context_plan_layout_wf_def] >>
  metis_tac[ordered_spill_regions_EL]
QED
val _ = export_theory();
