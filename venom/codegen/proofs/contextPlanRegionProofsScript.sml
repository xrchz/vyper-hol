(*
 * Structural invariants for context spill-region generation.
 *)

Theory contextPlanRegionProofs
Ancestors
  planSpillBounds allocMono stackPlanGen stackPlanTypes
  list arithmetic
Libs
  BasicProvers pairLib

Definition context_region_acc_wf_def:
  context_region_acc_wf static acc <=>
    static <= acc.cpa_next_spill_base /\
    EVERY
      (\r. static <= r.sr_spill_base /\
           r.sr_spill_base <= r.sr_spill_end /\
           r.sr_spill_end <= acc.cpa_next_spill_base)
      acc.cpa_regions /\
    ordered_spill_regions acc.cpa_regions /\
    EVERY
      (\r. r.sr_spill_base < r.sr_spill_end ==>
           r.sr_spill_end <= acc.cpa_peak_spill_end)
      acc.cpa_regions
End

Theorem ordered_spill_regions_SNOC[local]:
  !rs r.
    ordered_spill_regions (SNOC r rs) <=>
    ordered_spill_regions rs /\
    r.sr_spill_base <= r.sr_spill_end /\
    EVERY (\q. q.sr_spill_end <= r.sr_spill_base) rs
Proof
  Induct >> simp[ordered_spill_regions_def, EVERY_SNOC] >>
  metis_tac[]
QED

Theorem context_region_acc_wf_step[local]:
  !static acc fn ops ps.
    context_region_acc_wf static acc /\
    acc.cpa_next_spill_base <= ps.ps_alloc.sa_next_offset ==>
    context_region_acc_wf static
      (acc with <|
        cpa_regions := SNOC
          <|sr_fn_name := fn.fn_name;
            sr_spill_base := acc.cpa_next_spill_base;
            sr_spill_end := ps.ps_alloc.sa_next_offset;
            sr_plan := ops|>
          acc.cpa_regions;
        cpa_label_counter := ps.ps_label_counter;
        cpa_next_spill_base := ps.ps_alloc.sa_next_offset;
        cpa_peak_spill_end :=
          if acc.cpa_next_spill_base < ps.ps_alloc.sa_next_offset then
            MAX acc.cpa_peak_spill_end ps.ps_alloc.sa_next_offset
          else acc.cpa_peak_spill_end
      |>)
Proof
  simp[context_region_acc_wf_def, ordered_spill_regions_SNOC,
       EVERY_SNOC] >>
  rpt strip_tac >> fs[EVERY_MEM]
  >- (rpt strip_tac >>
      qpat_assum `!q. MEM q acc.cpa_regions ==> _ /\ _ /\ _`
        (qspec_then `r` (drule_then strip_assume_tac)) >>
      decide_tac) >>
  rpt strip_tac >>
  qpat_assum
    `!q. MEM q acc.cpa_regions ==>
         q.sr_spill_base < q.sr_spill_end ==>
         q.sr_spill_end <= acc.cpa_peak_spill_end`
    (qspec_then `r` (drule_then (drule_then assume_tac))) >>
  Cases_on `acc.cpa_next_spill_base < ps.ps_alloc.sa_next_offset` >>
  gvs[] >> decide_tac
QED

val _ = export_theory();
