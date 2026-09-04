(*
 * do_swap simulation for all distances.
 * Allocator boundary probes below are deliberately factored.
 *
 * For dist <= 16: simple SOSwap via simple_prefix_venom_asm_rel + do_swap_align.
 * For dist > 16: via mixed_prefix_venom_asm_rel (spill/restore sequence).
 *
 * Key results:
 *   alloc_spill_slot_wf           -- alloc preserves wf, produces valid offset
 *   venom_asm_rel_ps_transfer      -- plan state transfer (relevant fields)
 *   do_swap_venom_asm_rel         -- preserves venom_asm_rel for ALL dist
 *)

Theory doSwapSim
Ancestors
  spillSim strongPrefixSim planAlign planWf prefixExec
  mixedPrefixSim
  codegenRel stackOpSim blockSimHelpers
  stackPlanOps stackPlanTypes stackModel
  asmSem planExec
  finite_map alist pred_set
  list rich_list arithmetic sorting
Libs BasicProvers

(* =========================================================================
   Spill allocator well-formedness
   ========================================================================= *)

Definition spill_alloc_wf_def:
  spill_alloc_wf (al : spill_alloc) (spilled : (operand, num) fmap) <=>
    al.sa_spill_base <= al.sa_next_offset /\
    (!op off. FLOOKUP spilled op = SOME off ==>
       al.sa_spill_base <= off /\ off + 32 <= al.sa_next_offset) /\
    (!off. MEM off al.sa_free_slots ==>
       al.sa_spill_base <= off /\ off + 32 <= al.sa_next_offset) /\
    (!op1 off1 op2 off2.
       FLOOKUP spilled op1 = SOME off1 /\
       FLOOKUP spilled op2 = SOME off2 /\
       op1 <> op2 ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
    ALL_DISTINCT al.sa_free_slots /\
    (!i j. i < LENGTH al.sa_free_slots /\
           j < LENGTH al.sa_free_slots /\ i <> j ==>
       EL i al.sa_free_slots + 32 <= EL j al.sa_free_slots \/
       EL j al.sa_free_slots + 32 <= EL i al.sa_free_slots) /\
    (!op off1 off2.
       FLOOKUP spilled op = SOME off1 /\
       MEM off2 al.sa_free_slots ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
    al.sa_next_offset < dimword(:256)
End

(* Durable allocator layout safety.  Unlike [spill_alloc_wf], this predicate
   does not assert readiness for another fresh allocation. *)
Definition spill_alloc_layout_wf_def:
  spill_alloc_layout_wf (al : spill_alloc) (spilled : (operand, num) fmap) <=>
    al.sa_spill_base <= al.sa_next_offset /\
    (!op off. FLOOKUP spilled op = SOME off ==>
       al.sa_spill_base <= off /\ off + 32 <= al.sa_next_offset) /\
    (!off. MEM off al.sa_free_slots ==>
       al.sa_spill_base <= off /\ off + 32 <= al.sa_next_offset) /\
    (!op1 off1 op2 off2.
       FLOOKUP spilled op1 = SOME off1 /\
       FLOOKUP spilled op2 = SOME off2 /\
       op1 <> op2 ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
    ALL_DISTINCT al.sa_free_slots /\
    (!i j. i < LENGTH al.sa_free_slots /\
           j < LENGTH al.sa_free_slots /\ i <> j ==>
       EL i al.sa_free_slots + 32 <= EL j al.sa_free_slots \/
       EL j al.sa_free_slots + 32 <= EL i al.sa_free_slots) /\
    (!op off1 off2.
       FLOOKUP spilled op = SOME off1 /\
       MEM off2 al.sa_free_slots ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1)
End

Theorem spill_alloc_wf_iff_layout_ready:
  !al spilled.
    spill_alloc_wf al spilled <=>
    spill_alloc_layout_wf al spilled /\
    al.sa_next_offset < dimword(:256)
Proof
  simp[spill_alloc_wf_def, spill_alloc_layout_wf_def] >>
  metis_tac[]
QED

Theorem spill_alloc_wf_layout:
  !al spilled.
    spill_alloc_wf al spilled ==> spill_alloc_layout_wf al spilled
Proof
  simp[spill_alloc_wf_iff_layout_ready]
QED

(* =========================================================================
   Helpers: alloc_spill_slot basic properties
   ========================================================================= *)

Theorem alloc_spill_slot_ge_spill_base:
  !al off al'.
    alloc_spill_slot al = (off, al') /\
    al.sa_spill_base <= al.sa_next_offset /\
    EVERY (\s. al.sa_spill_base <= s) al.sa_free_slots ==>
    al.sa_spill_base <= off
Proof
  rpt strip_tac >>
  fs[alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots`
  >- (gvs[] >> decide_tac)
  >> gvs[] >>
  `MEM (LAST (h::t)) (h::t)` by simp[MEM_LAST] >>
  fs[EVERY_MEM]
QED

Theorem alloc_spill_slot_spill_base:
  !al off al'.
    alloc_spill_slot al = (off, al') ==>
    al'.sa_spill_base = al.sa_spill_base
Proof
  rpt strip_tac >>
  fs[alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots` >> gvs[]
QED

Theorem alloc_spill_slot_next_offset_mono:
  !al off al'.
    alloc_spill_slot al = (off, al') ==>
    al.sa_next_offset <= al'.sa_next_offset
Proof
  rpt strip_tac >>
  fs[alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots` >> gvs[]
QED

Theorem alloc_spill_slot_next_offset_upper[local]:
  !al off al'.
    alloc_spill_slot al = (off, al') ==>
    al'.sa_next_offset <= al.sa_next_offset + 32
Proof
  rpt strip_tac >> fs[alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots` >> gvs[]
QED

Theorem alloc_spill_slot_off_bound_empty:
  !al off al'.
    alloc_spill_slot al = (off, al') /\
    al.sa_free_slots = [] ==>
    off = al.sa_next_offset /\
    al'.sa_next_offset = off + 32
Proof
  rpt strip_tac >> gvs[alloc_spill_slot_def]
QED

Theorem free_spill_slot_preserves:
  !off al.
    (free_spill_slot off al).sa_spill_base = al.sa_spill_base /\
    (free_spill_slot off al).sa_next_offset = al.sa_next_offset
Proof
  rpt strip_tac >> simp[free_spill_slot_def]
QED

(* Helper: pairwise separation between FRONT element and LAST *)
Theorem front_last_pairwise[local]:
  !h t x.
    ALL_DISTINCT (h::t) /\
    MEM x (FRONT (h::t)) /\
    (!i j. i < LENGTH (h::t) /\ j < LENGTH (h::t) /\ i <> j ==>
       EL i (h::t) + 32 <= EL j (h::t) \/ EL j (h::t) + 32 <= EL i (h::t)) ==>
    x + 32 <= LAST (h::t) \/ LAST (h::t) + 32 <= x
Proof
  rpt strip_tac >>
  (`MEM x (h::t)` by metis_tac[MEM_FRONT]) >>
  (`MEM (LAST (h::t)) (h::t)` by simp[MEM_LAST]) >>
  (`~MEM (LAST (h::t)) (FRONT (h::t))` by
    (irule MEM_FRONT_NOT_LAST >> simp[])) >>
  (`?ix. ix < LENGTH (h::t) /\ x = EL ix (h::t)` by metis_tac[MEM_EL]) >>
  (`?il. il < LENGTH (h::t) /\ LAST (h::t) = EL il (h::t)` by metis_tac[MEM_EL]) >>
  (`ix <> il` by (strip_tac >> gvs[])) >>
  first_x_assum (qspecl_then [`ix`, `il`] mp_tac) >> simp[]
QED

(* =========================================================================
   alloc_spill_slot preserves wf and produces valid offset
   ========================================================================= *)

Theorem alloc_spill_slot_wf:
  !al spilled off al'.
    spill_alloc_wf al spilled /\
    alloc_spill_slot al = (off, al') ==>
    al.sa_spill_base <= off /\
    off + 32 <= al'.sa_next_offset /\
    al'.sa_spill_base = al.sa_spill_base /\
    al.sa_next_offset <= al'.sa_next_offset /\
    off < dimword(:256) /\
    (!op2 off2. FLOOKUP spilled op2 = SOME off2 ==>
       off2 + 32 <= off \/ off + 32 <= off2) /\
    (!off2. MEM off2 al'.sa_free_slots ==>
       off2 + 32 <= off \/ off + 32 <= off2)
Proof
  rpt gen_tac >> strip_tac >>
  fs[spill_alloc_wf_def, alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots` >> gvs[]
  (* Empty: off = next_offset, al' bumps by 32 *)
  >- (rpt strip_tac >>
      qpat_x_assum `!op off'. FLOOKUP _ _ = _ ==> _` drule >>
      strip_tac >> decide_tac)
  (* Non-empty: off = LAST, al'.sa_free_slots = FRONT *)
  >> rename1 `h :: t'` >>
  (`MEM (LAST (h::t')) (h::t')` by simp[MEM_LAST]) >>
  (`~MEM (LAST (h::t')) (FRONT (h::t'))` by
    (irule MEM_FRONT_NOT_LAST >> simp[])) >>
  (`al.sa_spill_base <= LAST (h::t') /\ LAST (h::t') + 32 <= al.sa_next_offset` by
    (qpat_x_assum `!off'. _ ==> _` (qspec_then `LAST (h::t')` mp_tac) >>
     fs[MEM])) >>
  rpt conj_tac >> rpt gen_tac
  >- simp[]
  >- simp[]
  >- decide_tac
  >- (strip_tac >>
      qpat_x_assum `!op off1 off2. _`
        (qspecl_then [`op2`, `off2`, `LAST (h::t')`] mp_tac) >>
      fs[MEM])
  >- (strip_tac >>
      `MEM off2 (h::t')` by metis_tac[MEM_FRONT] >>
      `?ix. ix < LENGTH (h::t') /\ off2 = EL ix (h::t')` by metis_tac[MEM_EL] >>
      `?il. il < LENGTH (h::t') /\ LAST (h::t') = EL il (h::t')` by metis_tac[MEM_EL, MEM_LAST] >>
      (`ix <> il` by (strip_tac >> gvs[])) >>
      first_x_assum (qspecl_then [`ix`, `il`] mp_tac) >> fs[])
QED

(* spill_alloc_wf preserved after one allocation + FUPDATE *)
Theorem spill_alloc_wf_after_spill:
  !al spilled off al' op.
    spill_alloc_wf al spilled /\
    alloc_spill_slot al = (off, al') /\
    al'.sa_next_offset < dimword(:256) ==>
    spill_alloc_wf al' (spilled |+ (op, off))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all alloc_spill_slot_wf >> strip_tac >>
  fs[spill_alloc_wf_def] >>
  fs[alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots` >> gvs[]
  (* Empty free_slots: off = next_offset, al' bumps by 32 *)
  >- (fs[FLOOKUP_UPDATE] >> rpt conj_tac >> rpt gen_tac >>
      every_case_tac >> rpt strip_tac >> gvs[] >>
      res_tac >> decide_tac)
  (* Non-empty free_slots: off = LAST, al' uses FRONT *)
  >> rename1 `h::t'` >>
  simp[FLOOKUP_UPDATE] >> rpt conj_tac >> rpt gen_tac >>
  every_case_tac >> rpt strip_tac >> gvs[MEM_FRONT, ALL_DISTINCT_FRONT] >>
  TRY (res_tac >> decide_tac) >>
  TRY decide_tac >>
  (* remaining: FRONT membership → full list membership *)
  TRY (imp_res_tac MEM_FRONT >> gvs[] >> res_tac >> decide_tac) >>
  (* EL FRONT pairwise *)
  TRY (fs[EL_FRONT, LENGTH_FRONT] >>
       qpat_x_assum `!i j. i < SUC _ /\ _ ==> _`
         (qspecl_then [`i`, `j`] mp_tac) >>
       simp[]) >>
  (* spilled vs FRONT: need MEM_FRONT then use spilled-vs-free hyp *)
  imp_res_tac MEM_FRONT >> fs[] >>
  qpat_x_assum `!op off1 off2. FLOOKUP _ _ = SOME _ /\ _ ==> _`
    (qspecl_then [`op'`, `off1`, `off2`] mp_tac) >>
  simp[]
QED


(* One allocator step plus the matching map update preserves durable layout.
   Concrete access validity (off < dimword) remains a call-site obligation. *)
Theorem spill_alloc_layout_wf_after_spill:
  !al spilled off al' op.
    spill_alloc_layout_wf al spilled /\
    al.sa_next_offset < dimword(:256) /\
    alloc_spill_slot al = (off, al') ==>
    spill_alloc_layout_wf al' (spilled |+ (op, off))
Proof
  rpt gen_tac >> strip_tac >>
  `spill_alloc_wf al spilled` by
    simp[spill_alloc_wf_iff_layout_ready] >>
  drule_all alloc_spill_slot_wf >> strip_tac >>
  fs[spill_alloc_layout_wf_def, alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots` >> gvs[]
  >- (fs[FLOOKUP_UPDATE, spill_alloc_layout_wf_def] >>
      rpt conj_tac >> rpt gen_tac >>
      every_case_tac >> rpt strip_tac >> gvs[] >>
      res_tac >> decide_tac)
  >> rename1 `h::t'` >>
  simp[FLOOKUP_UPDATE, spill_alloc_layout_wf_def] >>
  rpt conj_tac >> rpt gen_tac >>
  every_case_tac >> rpt strip_tac >> gvs[MEM_FRONT, ALL_DISTINCT_FRONT] >>
  TRY (res_tac >> decide_tac) >>
  TRY decide_tac >>
  TRY (imp_res_tac MEM_FRONT >> gvs[] >> res_tac >> decide_tac) >>
  TRY (fs[EL_FRONT, LENGTH_FRONT] >>
       qpat_x_assum `!i j. i < SUC _ /\ _ ==> _`
         (qspecl_then [`i`, `j`] mp_tac) >>
       simp[]) >>
  imp_res_tac MEM_FRONT >> fs[] >>
  qpat_x_assum `!op off1 off2. FLOOKUP _ _ = SOME _ /\ _ ==> _`
    (qspecl_then [`op'`, `off1`, `off2`] mp_tac) >>
  simp[]
QED


(* Allocation preserves durable layout even at allocator saturation. *)
Theorem spill_alloc_layout_wf_after_alloc:
  !al spilled off al' op.
    spill_alloc_layout_wf al spilled /\
    alloc_spill_slot al = (off, al') ==>
    spill_alloc_layout_wf al' (spilled |+ (op, off))
Proof
  rpt gen_tac >> strip_tac >>
  fs[spill_alloc_layout_wf_def, alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots` >> gvs[]
  >- (simp[FLOOKUP_UPDATE, spill_alloc_layout_wf_def] >>
      rpt conj_tac >> rpt gen_tac >>
      every_case_tac >> rpt strip_tac >> gvs[] >>
      res_tac >> decide_tac)
  >> rename1 `h::tail` >>
  `al.sa_spill_base <= LAST (h::tail) /\
   LAST (h::tail) + 32 <= al.sa_next_offset` by (
    qpat_x_assum `!off'. off' = h \/ MEM off' tail ==> _`
      (qspec_then `LAST (h::tail)` mp_tac) >>
    (impl_tac >-
      (`MEM (LAST (h::tail)) (h::tail)` by simp[MEM_LAST] >> fs[])) >>
    simp[]) >>
  `!op0 off0. FLOOKUP spilled op0 = SOME off0 ==>
      off0 + 32 <= LAST (h::tail) \/ LAST (h::tail) + 32 <= off0` by (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `!op off1 off2. FLOOKUP spilled op = SOME off1 /\ _ ==> _`
      (qspecl_then [`op0`, `off0`, `LAST (h::tail)`] mp_tac) >>
    (impl_tac >- (`MEM (LAST (h::tail)) (h::tail)` by simp[MEM_LAST] >> fs[])) >>
    simp[]) >>
  `!x. MEM x (FRONT (h::tail)) ==>
      x + 32 <= LAST (h::tail) \/ LAST (h::tail) + 32 <= x` by (
    rpt strip_tac >>
    `MEM x (h::tail)` by metis_tac[MEM_FRONT] >>
    `MEM (LAST (h::tail)) (h::tail)` by simp[MEM_LAST] >>
    `ALL_DISTINCT (h::tail)` by simp[] >>
    `~MEM (LAST (h::tail)) (FRONT (h::tail))` by
      (irule MEM_FRONT_NOT_LAST >> simp[]) >>
    `x <> LAST (h::tail)` by metis_tac[] >>
    `?ix. ix < LENGTH (h::tail) /\ x = EL ix (h::tail)` by
      metis_tac[MEM_EL] >>
    `?il. il < LENGTH (h::tail) /\ LAST (h::tail) = EL il (h::tail)` by
      metis_tac[MEM_EL] >>
    `ix <> il` by metis_tac[] >>
    qpat_x_assum `!i j. i < SUC _ /\ j < SUC _ /\ i <> j ==> _`
      (qspecl_then [`ix`, `il`] mp_tac) >>
    (impl_tac >- gvs[]) >> simp[]) >>
  simp[FLOOKUP_UPDATE, spill_alloc_layout_wf_def] >>
  rpt conj_tac >> rpt gen_tac >>
  every_case_tac >> rpt strip_tac >> gvs[MEM_FRONT, ALL_DISTINCT_FRONT] >>
  TRY (res_tac >> decide_tac) >>
  TRY decide_tac >>
  TRY (imp_res_tac MEM_FRONT >> gvs[] >> res_tac >> decide_tac) >>
  TRY (fs[EL_FRONT, LENGTH_FRONT] >>
       qpat_x_assum `!i j. i < SUC _ /\ _ ==> _`
         (qspecl_then [`i`, `j`] mp_tac) >>
       simp[]) >>
  imp_res_tac MEM_FRONT >> fs[] >>
  qpat_x_assum `!op off1 off2. FLOOKUP _ _ = SOME _ /\ _ ==> _`
    (qspecl_then [`op'`, `off1`, `off2`] mp_tac) >>
  simp[]
QED


Theorem separated_slots_snoc[local]:
  !slots off.
    (!i j. i < LENGTH slots /\ j < LENGTH slots /\ i <> j ==>
       EL i slots + 32 <= EL j slots \/ EL j slots + 32 <= EL i slots) /\
    (!old. MEM old slots ==>
       old + 32 <= off \/ off + 32 <= old) ==>
    !i j. i < SUC (LENGTH slots) /\
          j < SUC (LENGTH slots) /\ i <> j ==>
       EL i (SNOC off slots) + 32 <= EL j (SNOC off slots) \/
       EL j (SNOC off slots) + 32 <= EL i (SNOC off slots)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  fs[] >>
  Cases_on `i = LENGTH slots` >> Cases_on `j = LENGTH slots`
  >- gvs[]
  >- (`j < LENGTH slots` by decide_tac >>
      simp[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
      first_x_assum (qspec_then `EL j slots` mp_tac) >>
      simp[MEM_EL] >> metis_tac[])
  >- (`i < LENGTH slots` by decide_tac >>
      simp[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
      first_x_assum match_mp_tac >> metis_tac[MEM_EL])
  >> `i < LENGTH slots /\ j < LENGTH slots` by decide_tac >>
     simp[listTheory.EL_SNOC] >> metis_tac[]
QED
(* Returning an active slot to the reusable list preserves canonical allocator
   consistency, provided its map entry is removed in the same transition. *)
Theorem spill_alloc_wf_after_free:
  !al spilled op off.
    spill_alloc_wf al spilled /\
    FLOOKUP spilled op = SOME off ==>
    spill_alloc_wf (free_spill_slot off al) (spilled \\ op)
Proof
  rpt gen_tac >> strip_tac >>
  fs[spill_alloc_wf_def] >>
  simp[spill_alloc_wf_def, free_spill_slot_def, ALL_DISTINCT_SNOC,
       finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (strip_tac >>
      qpat_x_assum `!op' off1 off2. _`
        (qspecl_then [`op`, `off`, `off`] mp_tac) >>
      simp[] >> decide_tac)
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `i = LENGTH al.sa_free_slots` >>
      Cases_on `j = LENGTH al.sa_free_slots`
      >- gvs[]
      >- (`j < LENGTH al.sa_free_slots` by decide_tac >>
          simp[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
          qpat_x_assum `!op' off1 off2. _`
            (qspecl_then [`op`, `off`, `EL j al.sa_free_slots`] mp_tac) >>
          simp[MEM_EL] >> metis_tac[])
      >- (`i < LENGTH al.sa_free_slots` by decide_tac >>
          simp[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
          qpat_x_assum `!op' off1 off2. _`
            (qspecl_then [`op`, `off`, `EL i al.sa_free_slots`] mp_tac) >>
          simp[MEM_EL] >> metis_tac[])
      >> `i < LENGTH al.sa_free_slots /\ j < LENGTH al.sa_free_slots`
           by decide_tac >>
         simp[listTheory.EL_SNOC] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

(* Returning an active slot preserves durable layout safety even when the
   allocator is saturated and no further fresh allocation is ready. *)
Theorem spill_alloc_layout_wf_after_free:
  !al spilled op off.
    spill_alloc_layout_wf al spilled /\
    FLOOKUP spilled op = SOME off ==>
    spill_alloc_layout_wf (free_spill_slot off al) (spilled \\ op)
Proof
  rpt gen_tac >> strip_tac >>
  fs[spill_alloc_layout_wf_def] >>
  simp[spill_alloc_layout_wf_def, free_spill_slot_def, ALL_DISTINCT_SNOC,
       finite_mapTheory.DOMSUB_FLOOKUP_THM] >>
  rpt conj_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (strip_tac >>
      qpat_x_assum `!op' off1 off2. _`
        (qspecl_then [`op`, `off`, `off`] mp_tac) >>
      simp[] >> decide_tac)
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `i = LENGTH al.sa_free_slots` >>
      Cases_on `j = LENGTH al.sa_free_slots`
      >- gvs[]
      >- (`j < LENGTH al.sa_free_slots` by decide_tac >>
          simp[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
          qpat_x_assum `!op' off1 off2. _`
            (qspecl_then [`op`, `off`, `EL j al.sa_free_slots`] mp_tac) >>
          simp[MEM_EL] >> metis_tac[])
      >- (`i < LENGTH al.sa_free_slots` by decide_tac >>
          simp[listTheory.EL_SNOC, listTheory.EL_LENGTH_SNOC] >>
          qpat_x_assum `!op' off1 off2. _`
            (qspecl_then [`op`, `off`, `EL i al.sa_free_slots`] mp_tac) >>
          simp[MEM_EL] >> metis_tac[])
      >> `i < LENGTH al.sa_free_slots /\ j < LENGTH al.sa_free_slots`
           by decide_tac >>
         simp[listTheory.EL_SNOC] >> metis_tac[])
  >> rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

(* =========================================================================
   venom_asm_rel transfer: two plan states that agree on relevant fields
   ========================================================================= *)

Theorem venom_asm_rel_ps_transfer:
  !lo ps1 ps2 vs st.
    venom_asm_rel lo ps1 vs st /\
    ps2.ps_stack = ps1.ps_stack /\
    ps2.ps_spilled = ps1.ps_spilled /\
    ps2.ps_alloc.sa_spill_base = ps1.ps_alloc.sa_spill_base /\
    ps2.ps_alloc.sa_next_offset = ps1.ps_alloc.sa_next_offset ==>
    venom_asm_rel lo ps2 vs st
Proof
  rw[venom_asm_rel_def, memory_rel_def]
QED

(* =========================================================================
   dist <= 16 case: use simple_prefix_venom_asm_rel + do_swap_align
   ========================================================================= *)

Theorem do_swap_venom_asm_rel_small[local]:
  !dist ps ops ps' lo o2pc prog vs st.
    do_swap dist ps = (ops, ps') /\
    dist <= 16 /\
    dist < LENGTH ps.ps_stack /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt strip_tac >>
  Cases_on `dist = 0`
  >- gvs[do_swap_def, execute_plan_def, asm_steps_def]
  >>
  `ops = [SOSwap dist] /\
   ps' = ps with ps_stack := stack_swap dist ps.ps_stack` by
    (fs[do_swap_def] >> gvs[]) >>
  gvs[] >>
  qspecl_then [`[SOSwap dist]`, `initial_fmp`, `lo`, `o2pc`, `prog`, `ps`, `vs`, `st`]
    mp_tac simple_prefix_venom_asm_rel >>
  (impl_tac >- (
    simp[is_simple_stack_op_def, prefix_wf_def, stack_op_wf_def] >>
    ASM_REWRITE_TAC[]
  )) >>
  strip_tac >>
  qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  fs[apply_simple_ops_def, apply_simple_op_def]
QED

(* =========================================================================
   apply_prefix_ops field preservation
   ========================================================================= *)

(* sa_spill_base is unchanged by any prefix op *)
Theorem apply_prefix_op_spill_base[local]:
  !lo op ps.
    (apply_prefix_op initial_fmp lo op ps).ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[apply_prefix_op_def, apply_simple_op_def,
       stack_push_def, stack_pop_def, stack_swap_def, stack_dup_def,
       stack_poke_def, spill_lookup_def] >>
  TRY (Cases_on `o'` >> simp[apply_simple_op_def])
QED

Theorem apply_prefix_ops_spill_base[local]:
  !lo ops ps.
    (apply_prefix_ops initial_fmp lo ops ps).ps_alloc.sa_spill_base =
    ps.ps_alloc.sa_spill_base
Proof
  Induct_on `ops` >>
  simp[apply_prefix_ops_def, apply_prefix_op_spill_base]
QED

(* sa_next_offset only grows via SOSpill *)
Theorem apply_prefix_op_next_offset[local]:
  !lo op ps.
    ps.ps_alloc.sa_next_offset <=
    (apply_prefix_op initial_fmp lo op ps).ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[apply_prefix_op_def, apply_simple_op_def,
       stack_push_def, stack_pop_def, stack_swap_def, stack_dup_def,
       stack_poke_def, spill_lookup_def, MAX_DEF] >>
  TRY (Cases_on `o'` >> simp[apply_simple_op_def]) >>
  TRY decide_tac
QED

(* alloc_spill_slot and MAX agree on sa_next_offset *)
Theorem alloc_spill_slot_max_agree[local]:
  !al spilled off al'.
    alloc_spill_slot al = (off, al') /\
    spill_alloc_layout_wf al spilled ==>
    MAX al.sa_next_offset (off + 32) = al'.sa_next_offset
Proof
  rpt strip_tac >>
  fs[alloc_spill_slot_def, spill_alloc_layout_wf_def] >>
  Cases_on `al.sa_free_slots` >> gvs[]
  >- (
    (* empty case: MAX n (n+32) = n+32 *)
    simp[MAX_DEF]
  )
  >> (
    (* non-empty case: reuse slot, MAX n (off+32) = n when off+32 <= n *)
    rename1 `h::t'` >>
    gvs[] >>
    simp[MAX_DEF] >>
    `LAST (h::t') + 32 <= al.sa_next_offset` suffices_by decide_tac >>
    qpat_x_assum `!off'. off' = h \/ MEM off' t' ==> _`
      (qspec_then `LAST (h::t')` mp_tac) >>
    `MEM (LAST (h::t')) (h::t')` suffices_by (strip_tac >> fs[MEM]) >>
    simp[MEM_LAST]
  )
QED

(* SORestore doesn't change ps_alloc at all *)
Theorem apply_prefix_op_restore_alloc[local]:
  !lo off ps.
    (apply_prefix_op initial_fmp lo (SORestore off) ps).ps_alloc = ps.ps_alloc
Proof
  simp[apply_prefix_op_def, spill_lookup_def]
QED

(* apply_prefix_ops over all-SORestore preserves sa_next_offset *)
Theorem apply_prefix_ops_restore_next_offset[local]:
  !lo ops ps.
    EVERY (\op. ?off. op = SORestore off) ops ==>
    (apply_prefix_ops initial_fmp lo ops ps).ps_alloc.sa_next_offset =
    ps.ps_alloc.sa_next_offset
Proof
  Induct_on `ops` >>
  simp[apply_prefix_ops_def] >>
  rpt strip_tac >> gvs[] >>
  fs[apply_prefix_op_restore_alloc]
QED

Theorem every_map_restore[local]:
  !offsets. EVERY (\op. ?off. op = SORestore off) (MAP SORestore offsets)
Proof
  Induct >> simp[] >> metis_tac[]
QED

(* =========================================================================
   spill_alloc_n: factored 2-component FOLDL for spill allocation.
   Eliminates ops-dependency from offset/alloc reasoning.
   ========================================================================= *)

Definition spill_alloc_n_def:
  spill_alloc_n offs0 al0 [] = (offs0, al0) /\
  spill_alloc_n offs0 al0 (item::items) =
    let (off, al1) = alloc_spill_slot al0 in
    spill_alloc_n (SNOC off offs0) al1 items
End

(* Bridge: the 3-component FOLDL's SND equals spill_alloc_n *)
Theorem spill_foldl_snd_eq[local]:
  !items ops0 offs0 al0.
    SND (FOLDL
      (\(ops,offs,al) item.
         (\(off,al2). (ops ++ [SOSpill off], SNOC off offs, al2))
           (alloc_spill_slot al))
      (ops0, offs0, al0) items) =
    spill_alloc_n offs0 al0 items
Proof
  Induct >> simp[spill_alloc_n_def] >>
  rpt strip_tac >>
  Cases_on `alloc_spill_slot al0` >>
  simp[]
QED

(* =========================================================================
   spill_alloc_n basic properties
   ========================================================================= *)

Theorem spill_alloc_n_spill_base[local]:
  !items offs0 al0.
    (SND (spill_alloc_n offs0 al0 items)).sa_spill_base = al0.sa_spill_base
Proof
  Induct >> simp[spill_alloc_n_def] >>
  rpt strip_tac >>
  Cases_on `alloc_spill_slot al0` >>
  simp[] >>
  imp_res_tac alloc_spill_slot_spill_base >> simp[]
QED

Theorem spill_alloc_n_offsets_length[local]:
  !items offs0 al0.
    LENGTH (FST (spill_alloc_n offs0 al0 items)) =
    LENGTH offs0 + LENGTH items
Proof
  Induct >> simp[spill_alloc_n_def] >>
  rpt strip_tac >>
  Cases_on `alloc_spill_slot al0` >>
  simp[LENGTH_SNOC]
QED

(* spill_ops = MAP SOSpill offsets after the FOLDL *)
Theorem spill_foldl_ops_eq_map[local]:
  !items ops0 offs0 al0.
    ops0 = MAP SOSpill offs0 ==>
    FST (FOLDL
      (\(ops,offs,al) item.
         (\(off,al'). (ops ++ [SOSpill off], SNOC off offs, al'))
           (alloc_spill_slot al))
      (ops0,offs0,al0) items) =
    MAP SOSpill (FST (spill_alloc_n offs0 al0 items))
Proof
  Induct >> simp[spill_alloc_n_def] >>
  rpt strip_tac >>
  Cases_on `alloc_spill_slot al0` >>
  simp[] >>
  first_x_assum irule >>
  simp[MAP_SNOC]
QED

(* =========================================================================
   Spill-phase plan state characterization
   ========================================================================= *)

(* After applying n SOSpill ops, the stack loses n elements from the top *)
Theorem apply_spill_ops_stack:
  !offsets lo ps.
    LENGTH offsets <= LENGTH ps.ps_stack ==>
    (apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps).ps_stack =
    TAKE (LENGTH ps.ps_stack - LENGTH offsets) ps.ps_stack
Proof
  Induct >>
  simp[apply_prefix_ops_def] >>
  rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC[apply_prefix_ops_def, apply_prefix_op_def,
                   stack_pop_def] >>
  qpat_x_assum `!lo ps. _` (qspecl_then [`lo`,
    `ps with <| ps_stack := TAKE (LENGTH ps.ps_stack - 1) ps.ps_stack;
                ps_spilled := ps.ps_spilled |+ (stack_peek 0 ps.ps_stack, h);
                ps_alloc := ps.ps_alloc with sa_next_offset :=
                  MAX ps.ps_alloc.sa_next_offset (h + 32) |>`] mp_tac) >>
  simp[LENGTH_TAKE_EQ] >> strip_tac >>
  `LENGTH ps.ps_stack - (LENGTH offsets + 1) <=
   LENGTH ps.ps_stack - 1` by decide_tac >>
  fs[TAKE_TAKE_T] >>
  REWRITE_TAC[ADD1]
QED

(* After applying n SOSpill ops, sa_spill_base unchanged *)
(* (already follows from apply_prefix_ops_spill_base) *)

(* =========================================================================
   prefix_spill_wf decomposition (must come before spill_gen)
   ========================================================================= *)

Theorem prefix_spill_wf_append[local]:
  !l1 l2 lo ps.
    prefix_spill_wf initial_fmp lo (l1 ++ l2) ps <=>
    prefix_spill_wf initial_fmp lo l1 ps /\
    prefix_spill_wf initial_fmp lo l2 (apply_prefix_ops initial_fmp lo l1 ps)
Proof
  Induct >> simp[prefix_spill_wf_def, apply_prefix_ops_def] >>
  metis_tac[]
QED


(* SOSpill applies the same high-water MAX fold as the allocator interface. *)
Theorem apply_spill_ops_next_offset[local]:
  !offsets lo ps.
    (apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps).
      ps_alloc.sa_next_offset =
    FOLDL MAX ps.ps_alloc.sa_next_offset (MAP (\off. off + 32) offsets)
Proof
  Induct >> simp[apply_prefix_ops_def, apply_prefix_op_def]
QED
(* =========================================================================
   prefix_spill_wf for spill ops via spill_alloc_wf invariant
   ========================================================================= *)

(* spill_op_wf for SOSpill when alloc produces non-overlapping offset *)
Theorem spill_op_wf_from_alloc[local]:
  !ps al off al'.
    alloc_spill_slot al = (off, al') /\
    spill_alloc_wf al ps.ps_spilled /\
    al.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    al'.sa_next_offset < dimword(:256) ==>
    spill_op_wf ps (SOSpill off)
Proof
  rpt strip_tac >>
  drule_all alloc_spill_slot_wf >> strip_tac >>
  simp[spill_op_wf_def] >>
  rpt strip_tac >> res_tac >> decide_tac
QED

(* Generalized: prefix_spill_wf for spill FOLDL starting from arbitrary acc. *)
Theorem prefix_spill_wf_spill_gen[local]:
  !items ops0 offs0 al0 lo ps.
    prefix_spill_wf initial_fmp lo ops0 ps /\
    spill_alloc_wf al0 (apply_prefix_ops initial_fmp lo ops0 ps).ps_spilled /\
    al0.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    LENGTH items <= LENGTH (apply_prefix_ops initial_fmp lo ops0 ps).ps_stack /\
    al0.sa_next_offset + 32 * LENGTH items < dimword(:256) ==>
    (let (ops, offs, al') =
       FOLDL
         (\(ops,offs,al) item.
            (\(off,al'). (ops ++ [SOSpill off], SNOC off offs, al'))
              (alloc_spill_slot al))
         (ops0,offs0,al0) items
     in prefix_spill_wf initial_fmp lo ops ps)
Proof
  Induct
  >- simp[]
  >>
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot al0` >>
  (* Grab and instantiate the IH before simp can consume it *)
  qpat_x_assum `!ops0 offs0 al0 lo ps. _`
    (qspecl_then [`ops0 ++ [SOSpill q]`, `SNOC q offs0`, `r`,
                  `lo`, `ps`] mp_tac) >>
  simp[] >>
  disch_then irule >>
  rpt conj_tac
  (* Goal 1: dimword bound *)
  >- (
    imp_res_tac alloc_spill_slot_next_offset_upper >>
    fs[LENGTH] >> decide_tac
  )
  (* Goal 2: LENGTH *)
  >- (
    simp[apply_prefix_ops_append, apply_prefix_ops_def,
         apply_prefix_op_def, stack_pop_def, LENGTH_TAKE_EQ] >>
    fs[LENGTH]
  )
  (* Goal 3: fn_eom *)
  >- (imp_res_tac alloc_spill_slot_spill_base >> simp[])
  (* Goal 4: spill_alloc_wf *)
  >- (
    simp[apply_prefix_ops_append, apply_prefix_ops_def,
         apply_prefix_op_def] >>
    match_mp_tac spill_alloc_wf_after_spill >>
    qexists_tac `al0` >>
    simp[] >>
    imp_res_tac alloc_spill_slot_next_offset_upper >>
    fs[LENGTH] >> decide_tac
  )
  (* Goal 5: prefix_spill_wf *)
  >> (
    simp[prefix_spill_wf_append, prefix_spill_wf_def] >>
    irule spill_op_wf_from_alloc >>
    qexistsl_tac [`al0`, `r`] >>
    simp[apply_prefix_ops_spill_base] >>
    imp_res_tac alloc_spill_slot_next_offset_upper >>
    fs[]
  )
QED

(* Specialized: starting from empty ops *)
Theorem prefix_spill_wf_spill_phase[local]:
  !items offs0 al0 lo ps.
    spill_alloc_wf al0 ps.ps_spilled /\
    LENGTH items <= LENGTH ps.ps_stack /\
    al0.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    al0.sa_next_offset + 32 * LENGTH items < dimword(:256) ==>
    (let (ops, offs, al') =
       FOLDL
         (\(ops,offs,al) item.
            (\(off,al'). (ops ++ [SOSpill off], SNOC off offs, al'))
              (alloc_spill_slot al))
         ([],offs0,al0) items
     in prefix_spill_wf initial_fmp lo ops ps)
Proof
  rpt strip_tac >>
  irule prefix_spill_wf_spill_gen >>
  simp[prefix_spill_wf_def, apply_prefix_ops_def]
QED

(* =========================================================================
   do_swap ops: EVERY is_prefix_op
   ========================================================================= *)

Theorem do_swap_every_prefix_op[local]:
  !dist ps ops ps'.
    do_swap dist ps = (ops, ps') ==>
    EVERY is_prefix_op ops
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist = 0`
  >- gvs[do_swap_def]
  >> Cases_on `dist <= 16`
  >- (gvs[do_swap_def] >>
      simp[prefixSimTheory.is_prefix_op_def, is_simple_stack_op_def])
  >> fs[do_swap_def] >>
  qabbrev_tac `fres = FOLDL
    (\(ops,offs,al) item.
       (\(off,al'). (ops ++ [SOSpill off], SNOC off offs, al'))
         (alloc_spill_slot al))
    ([],[],ps.ps_alloc)
    (top_n (dist + 1) ps.ps_stack)` >>
  PairCases_on `fres` >> fs[] >>
  (* Derive: spill ops = MAP SOSpill offsets *)
  qspecl_then [`top_n (dist + 1) ps.ps_stack`, `[]`, `[]`, `ps.ps_alloc`]
    mp_tac spill_foldl_ops_eq_map >>
  simp[] >> strip_tac >>
  (* fres0 = MAP SOSpill fres1, so all are is_prefix_op *)
  simp[EVERY_APPEND, EVERY_MAP, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  TRY (simp[prefixSimTheory.is_prefix_op_def] >> NO_TAC) >>
  fs[MEM_MAP] >> gvs[] >> simp[prefixSimTheory.is_prefix_op_def]
QED

(* =========================================================================
   do_swap dist > 16: via mixed_prefix_venom_asm_rel

   Strategy:
   1. Show prefix_spill_wf for do_swap ops
   2. Use mixed_prefix_venom_asm_rel
   3. Show apply_prefix_ops result agrees with do_swap ps' on relevant fields
   4. Bridge via venom_asm_rel_ps_transfer
   ========================================================================= *)

(* prefix_wf for MAP SOSpill: just need enough stack elements *)
Theorem prefix_wf_map_spill[local]:
  !offsets lo n.
    n >= LENGTH offsets ==>
    prefix_wf lo n (MAP SOSpill offsets)
Proof
  Induct >> simp[prefix_wf_def, stack_op_wf_def]
QED

(* prefix_end_len for MAP SOSpill *)
Theorem prefix_end_len_map_spill[local]:
  !offsets lo n.
    prefix_end_len lo n (MAP SOSpill offsets) = n - LENGTH offsets
Proof
  Induct >> simp[prefix_end_len_def, stack_op_wf_def]
QED

(* prefix_wf for MAP SORestore: always OK *)
Theorem prefix_wf_map_restore[local]:
  !indices offsets lo n.
    prefix_wf lo n (MAP (\idx. SORestore (EL idx offsets)) indices)
Proof
  Induct >> simp[prefix_wf_def, stack_op_wf_def]
QED

(* prefix_wf for spill ++ restore via prefix_wf_append *)
Theorem prefix_wf_spill_restore[local]:
  !offsets indices lo n.
    n >= LENGTH offsets ==>
    prefix_wf lo n
      (MAP SOSpill offsets ++
       MAP (\idx. SORestore (EL idx offsets)) indices)
Proof
  rpt strip_tac >>
  irule prefix_wf_append >>
  simp[prefix_wf_map_spill, prefix_end_len_map_spill,
       prefix_wf_map_restore]
QED

(* =========================================================================
   Direct chain approach for dist > 16.
   Compose spill_op_venom_asm_rel / restore_op_venom_asm_rel
   via asm_steps_compose_ok.

   Key helpers:
   1. take_reverse_decompose - list decomposition for induction step
   2. stack_peek_last - stack_peek 0 = LAST
   3. spill_n_sim - n spill steps by induction on pairs
   4. restore_n_sim - n restore steps by induction
   ========================================================================= *)

(* ---------------------------------------------------------------
   List helper: TAKE (SUC n) (REVERSE stk) decomposes to
   LAST stk :: TAKE n (REVERSE (FRONT stk))
   --------------------------------------------------------------- *)
Theorem take_reverse_decompose[local]:
  !n stk.
    SUC n <= LENGTH stk ==>
    TAKE (SUC n) (REVERSE stk) =
      LAST stk :: TAKE n (REVERSE (FRONT stk))
Proof
  rpt strip_tac >>
  `stk <> []` by (Cases_on `stk` >> fs[]) >>
  `SNOC (LAST stk) (FRONT stk) = stk` by simp[SNOC_LAST_FRONT] >>
  `REVERSE stk = LAST stk :: REVERSE (FRONT stk)` by
    metis_tac[REVERSE_SNOC] >>
  ASM_REWRITE_TAC[TAKE_def] >> simp[]
QED

(* stack_peek 0 stk = LAST stk *)
Theorem stack_peek_last[local]:
  !stk. stk <> [] ==> stack_peek 0 stk = LAST stk
Proof
  rpt strip_tac >>
  simp[stack_peek_def] >>
  `0 < LENGTH stk` by (Cases_on `stk` >> fs[]) >>
  `LENGTH stk - 1 = PRE (LENGTH stk)` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[EL_PRE_LENGTH]
QED

(* ---------------------------------------------------------------
   spill_n_sim: Induction on pairs list.
   pairs = [(item0, off0), ...] in TOS-first pop order.
   --------------------------------------------------------------- *)
Theorem plan_state_self_update[local]:
  (ps:plan_state) with <| ps_stack := ps.ps_stack;
    ps_spilled := ps.ps_spilled;
    ps_alloc := ps.ps_alloc with sa_next_offset :=
      ps.ps_alloc.sa_next_offset |> = ps
Proof
  simp[plan_state_component_equality, spill_alloc_component_equality]
QED

(* Index-shift transfer: properties at SUC k on (h::t) give
   properties at k on t, with FLOOKUP through |+ *)
Theorem spill_offset_transfer[local]:
  !item0 off0 pairs fn_eom sp.
    (!k. k < SUC (LENGTH pairs) ==>
       SND (EL k ((item0,off0)::pairs)) < dimword(:256) /\
       fn_eom <= SND (EL k ((item0,off0)::pairs)) /\
       (!op2 off2. FLOOKUP sp op2 = SOME off2 ==>
          off2 + 32 <= SND (EL k ((item0,off0)::pairs)) \/
          SND (EL k ((item0,off0)::pairs)) + 32 <= off2) /\
       (!j. j < k ==>
          SND (EL j ((item0,off0)::pairs)) + 32 <=
            SND (EL k ((item0,off0)::pairs)) \/
          SND (EL k ((item0,off0)::pairs)) + 32 <=
            SND (EL j ((item0,off0)::pairs)))) ==>
    (!k. k < LENGTH pairs ==>
       SND (EL k pairs) < dimword(:256) /\
       fn_eom <= SND (EL k pairs) /\
       (!op2 off2. FLOOKUP (sp |+ (item0, off0)) op2 = SOME off2 ==>
          off2 + 32 <= SND (EL k pairs) \/
          SND (EL k pairs) + 32 <= off2) /\
       (!j. j < k ==>
          SND (EL j pairs) + 32 <= SND (EL k pairs) \/
          SND (EL k pairs) + 32 <= SND (EL j pairs)))
Proof
  rpt gen_tac >> DISCH_TAC >>
  rpt gen_tac >> DISCH_TAC >>
  qpat_assum `!k. k < SUC _ ==> _`
    (fn th => ASSUME_TAC (SIMP_RULE (srw_ss()) [] (Q.SPEC `SUC k` th))) >>
  pop_assum mp_tac >> simp[] >> strip_tac >>
  conj_tac
  >| [
    (* FLOOKUP: ∀op2 off2. FLOOKUP (sp |+ (item0,off0)) op2 = SOME off2 ⇒ ... *)
    rpt strip_tac >> fs[FLOOKUP_UPDATE] >>
    Cases_on `op2 = item0` >> gvs[]
    >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
    >> metis_tac[],
    (* inter-pair: ∀j. j < k ⇒ sep(EL j pairs, EL k pairs) *)
    rpt strip_tac >>
    first_x_assum (qspec_then `SUC j` mp_tac) >> simp[]
  ]
QED

Theorem prefix_spill_wf_map_spill_pairs[local]:
  !pairs lo ps.
    MAP FST pairs = TAKE (LENGTH pairs) (REVERSE ps.ps_stack) /\
    LENGTH pairs <= LENGTH ps.ps_stack /\
    ALL_DISTINCT (MAP FST pairs) /\
    (!k. k < LENGTH pairs ==>
       SND (EL k pairs) < dimword(:256) /\
       ps.ps_alloc.sa_spill_base <= SND (EL k pairs) /\
       (!op2 off2. FLOOKUP ps.ps_spilled op2 = SOME off2 ==>
          off2 + 32 <= SND (EL k pairs) \/
          SND (EL k pairs) + 32 <= off2) /\
       (!j. j < k ==>
          SND (EL j pairs) + 32 <= SND (EL k pairs) \/
          SND (EL k pairs) + 32 <= SND (EL j pairs))) ==>
    prefix_spill_wf initial_fmp lo (MAP SOSpill (MAP SND pairs)) ps
Proof
  Induct_on `pairs` >> rpt gen_tac >> strip_tac
  >- simp[prefix_spill_wf_def]
  >> Cases_on `h` >> rename1 `(item0,off0)` >> gvs[MAP] >>
  simp[prefix_spill_wf_def] >>
  `ps.ps_stack <> []` by (Cases_on `ps.ps_stack` >> fs[]) >>
  `item0 = stack_peek 0 ps.ps_stack` by
    (qspecl_then [`LENGTH (pairs:(operand#num) list)`, `ps.ps_stack`]
       mp_tac take_reverse_decompose >>
     simp[stack_peek_last] >> strip_tac >> gvs[]) >>
  conj_tac
  >- (simp[spill_op_wf_def] >>
      qpat_x_assum `!k. k < SUC _ ==> _` (qspec_then `0` mp_tac) >>
      simp[] >> metis_tac[]) >>
  first_x_assum irule >>
  simp[apply_prefix_op_def, stack_pop_def, FRONT_BY_TAKE] >>
  conj_tac
  >- (qspecl_then [`stack_peek 0 ps.ps_stack`, `off0`,
        `pairs:(operand#num) list`, `ps.ps_alloc.sa_spill_base`,
        `ps.ps_spilled`] mp_tac spill_offset_transfer >>
      (impl_tac >- (gvs[] >> metis_tac[])) >>
      strip_tac >> gvs[wordsTheory.dimword_def]) >>
  conj_tac
  >- (`ALL_DISTINCT (stack_peek 0 ps.ps_stack ::
          MAP FST (pairs:(operand#num) list))` by metis_tac[] >>
      fs[ALL_DISTINCT]) >>
  qspecl_then [`LENGTH (pairs:(operand#num) list)`, `ps.ps_stack`]
    mp_tac take_reverse_decompose >>
  simp[] >> strip_tac >> gvs[FRONT_BY_TAKE]
QED


Theorem do_swap_spill_lookup_flookup[local]:
  !off sp.
    (?op. FLOOKUP sp op = SOME off) ==>
    FLOOKUP sp (spill_lookup off sp) = SOME off
Proof
  simp[spill_lookup_def] >> metis_tac[SELECT_AX]
QED

Theorem prefix_spill_wf_map_restore_lookup[local]:
  !items offsets lo ps.
    LENGTH items = LENGTH offsets /\
    ALL_DISTINCT items /\
    ALL_DISTINCT offsets /\
    (!k. k < LENGTH items ==>
       FLOOKUP ps.ps_spilled (EL k items) = SOME (EL k offsets) /\
       EL k offsets < dimword(:256)) ==>
    prefix_spill_wf initial_fmp lo (MAP SORestore offsets) ps
Proof
  Induct_on `items` >> rpt gen_tac >> strip_tac
  >- (Cases_on `offsets` >> fs[prefix_spill_wf_def]) >>
  Cases_on `offsets` >> fs[] >>
  `FLOOKUP ps.ps_spilled h = SOME h' /\ h' < dimword(:256)` by
    (qpat_x_assum `!k. k < SUC _ ==> _` (qspec_then `0` mp_tac) >>
     simp[wordsTheory.dimword_def]) >>
  `FLOOKUP ps.ps_spilled (spill_lookup h' ps.ps_spilled) = SOME h'` by
    (irule do_swap_spill_lookup_flookup >> metis_tac[]) >>
  simp[prefix_spill_wf_def] >>
  conj_tac
  >- (simp[spill_op_wf_def] >> metis_tac[]) >>
  first_x_assum irule >>
  simp[apply_prefix_op_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!k. k < SUC _ ==> _` (qspec_then `SUC k` mp_tac) >>
  simp[DOMSUB_FLOOKUP_THM, wordsTheory.dimword_def] >>
  strip_tac >>
  spose_not_then assume_tac >> gvs[] >>
  `MEM (EL k t) t` by metis_tac[MEM_EL] >>
  metis_tac[]
QED
Theorem spill_n_sim[local]:
  !pairs lo o2pc prog ps vs st.
    venom_asm_rel lo ps vs st /\
    MAP FST pairs = TAKE (LENGTH pairs) (REVERSE ps.ps_stack) /\
    LENGTH pairs <= LENGTH ps.ps_stack /\
    ALL_DISTINCT (MAP FST pairs) /\
    (!k. k < LENGTH pairs ==>
       SND (EL k pairs) < dimword(:256) /\
       ps.ps_alloc.sa_spill_base <= SND (EL k pairs) /\
       (!op2 off2. FLOOKUP ps.ps_spilled op2 = SOME off2 ==>
          off2 + 32 <= SND (EL k pairs) \/
          SND (EL k pairs) + 32 <= off2) /\
       (!j. j < k ==>
          SND (EL j pairs) + 32 <= SND (EL k pairs) \/
          SND (EL k pairs) + 32 <= SND (EL j pairs))) /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp (MAP SOSpill (MAP SND pairs))) ==>
    ?st'.
      asm_steps lo o2pc prog (2 * LENGTH pairs) st = AsmOK st' /\
      st'.as_pc = st.as_pc + 2 * LENGTH pairs /\
      venom_asm_rel lo
        (ps with <| ps_stack :=
           TAKE (LENGTH ps.ps_stack - LENGTH pairs) ps.ps_stack;
           ps_spilled := ps.ps_spilled |++ pairs;
           ps_alloc := ps.ps_alloc with sa_next_offset :=
             FOLDL MAX ps.ps_alloc.sa_next_offset
                   (MAP (\p. SND p + 32) pairs) |>)
        vs st'
Proof
  Induct_on `pairs` >> rpt gen_tac >> strip_tac
  (* Base case: pairs = [] *)
  >- (
    qexists_tac `st` >>
    simp[FUPDATE_LIST_THM, TAKE_LENGTH_ID] >>
    simp[Once asm_steps_def] >>
    simp[plan_state_self_update]
  )
  (* Step case: h::pairs *)
  >> Cases_on `h` >> rename1 `(item0, off0)` >> gvs[MAP] >>
  (* Extract k=0 properties from the universal *)
  qpat_assum `!k. k < SUC _ ==> _` (fn kth =>
    let val k0 = Q.SPEC `0` kth
    in ASSUME_TAC k0 end) >>
  fs[] >>
  SUBGOAL_THEN ``ps.ps_stack <> []`` ASSUME_TAC
  >- (Cases_on `ps.ps_stack` >> fs[]) >>
  SUBGOAL_THEN ``LENGTH ps.ps_stack >= 1`` ASSUME_TAC >- decide_tac >>
  SUBGOAL_THEN ``item0 = stack_peek 0 ps.ps_stack`` ASSUME_TAC
  >- (
    SUBGOAL_THEN ``TAKE (SUC (LENGTH (pairs:(operand#num) list)))
       (REVERSE ps.ps_stack) =
       LAST ps.ps_stack ::
       TAKE (LENGTH pairs) (REVERSE (FRONT ps.ps_stack))``
      ASSUME_TAC
    >- (match_mp_tac take_reverse_decompose >> simp[]) >>
    fs[stack_peek_last]
  ) >>
  (* Apply spill_op_venom_asm_rel for first element *)
  mp_tac spill_op_venom_asm_rel >>
  disch_then (qspecl_then [`lo`, `o2pc`, `prog`, `off0`,
    `item0`, `ps`, `vs`, `st`] mp_tac) >>
  (impl_tac
  >- (
    rpt conj_tac >> TRY (fs[] >> NO_TAC) >>
    qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp _)` mp_tac >>
    simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons,
         asm_block_at_nil]
  )) >>
  strip_tac >>
  (* Extract asm_block_at for remaining spill ops *)
  SUBGOAL_THEN ``asm_block_at prog (st.as_pc + 2)
    (execute_plan initial_fmp (MAP SOSpill (MAP SND (pairs:(operand#num) list))))``
    ASSUME_TAC
  >- (
    qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp _)` mp_tac >>
    simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons,
         asm_block_at_nil]
  ) >>
  (* Establish IH preconditions *)
  SUBGOAL_THEN ``MAP FST (pairs:(operand#num) list) =
       TAKE (LENGTH pairs) (REVERSE (stack_pop 1 ps.ps_stack)) /\
     ALL_DISTINCT (MAP FST (pairs:(operand#num) list)) /\
     (!k. k < LENGTH (pairs:(operand#num) list) ==>
        SND (EL k pairs) < dimword(:256) /\
        ps.ps_alloc.sa_spill_base <= SND (EL k pairs) /\
        (!op2 off2. FLOOKUP (ps.ps_spilled |+ (stack_peek 0 ps.ps_stack, off0))
           op2 = SOME off2 ==>
           off2 + 32 <= SND (EL k pairs) \/
           SND (EL k pairs) + 32 <= off2) /\
        (!j. j < k ==>
           SND (EL j pairs) + 32 <= SND (EL k pairs) \/
           SND (EL k pairs) + 32 <= SND (EL j pairs)))``
    ASSUME_TAC
  >- (
    rpt conj_tac
    (* conjunct 1: MAP FST *)
    >- (
      SUBGOAL_THEN ``TAKE (SUC (LENGTH (pairs:(operand#num) list)))
         (REVERSE ps.ps_stack) =
       LAST ps.ps_stack ::
         TAKE (LENGTH pairs) (REVERSE (FRONT ps.ps_stack))``
        ASSUME_TAC
      >- (match_mp_tac take_reverse_decompose >> simp[]) >>
      fs[stack_pop_def, FRONT_BY_TAKE]
    )
    (* conjunct 2: ALL_DISTINCT *)
    >- (
      SUBGOAL_THEN ``ALL_DISTINCT (item0::MAP FST (pairs:(operand#num) list))``
        ASSUME_TAC
      >- metis_tac[] >>
      fs[ALL_DISTINCT]
    )
    (* conjunct 3: offset properties — via spill_offset_transfer *)
    >> (
      match_mp_tac spill_offset_transfer >>
      gvs[] >> metis_tac[]
    )
  ) >>
  (* Apply IH *)
  first_x_assum (qspecl_then [`lo`, `o2pc`, `prog`,
    `ps with <| ps_stack := stack_pop 1 ps.ps_stack;
                ps_spilled := ps.ps_spilled |+ (item0, off0);
                ps_alloc := ps.ps_alloc with sa_next_offset :=
                  MAX ps.ps_alloc.sa_next_offset (off0 + 32) |>`,
    `vs`, `st'`] mp_tac) >>
  simp[] >>
  (impl_tac >- (gvs[] >> metis_tac[])) >>
  strip_tac >>
  (* Compose: 2 steps (spill first) + 2*LENGTH pairs steps (IH) *)
  qexists_tac `st''` >>
  rpt conj_tac
  (* asm_steps composition *)
  >- (
    SUBGOAL_THEN ``2 * SUC (LENGTH (pairs:(operand#num) list)) =
      2 + 2 * LENGTH pairs`` SUBST1_TAC
    >- simp[] >>
    irule (GEN_ALL asm_steps_compose_ok) >>
    qexists_tac `st'` >> fs[]
  )
  (* PC *)
  >- fs[]
  (* venom_asm_rel: IH gives rel on stack_pop, need rel on original stack *)
  >> (
    qpat_x_assum `venom_asm_rel lo _ vs st''` mp_tac >>
    simp[stack_pop_def, FUPDATE_LIST_THM, LENGTH_FRONT,
         TAKE_TAKE_T, ADD1]
  )
QED

(* ---------------------------------------------------------------
   restore_n_sim: Induction on items to restore.
   Each step uses restore_op_venom_asm_rel.
   FLOOKUP persistence: ALL_DISTINCT items ensures removing
   item_k via domsub doesn't affect FLOOKUP of item_{k+1}..
   --------------------------------------------------------------- *)
Theorem restore_n_sim[local]:
  !items offsets lo o2pc prog ps vs st.
    venom_asm_rel lo ps vs st /\
    LENGTH items = LENGTH offsets /\
    ALL_DISTINCT items /\
    (!k. k < LENGTH items ==>
       FLOOKUP ps.ps_spilled (EL k items) = SOME (EL k offsets) /\
       EL k offsets < dimword(:256)) /\
    asm_block_at prog st.as_pc
      (execute_plan initial_fmp (MAP SORestore offsets)) ==>
    ?st'.
      asm_steps lo o2pc prog (2 * LENGTH items) st = AsmOK st' /\
      st'.as_pc = st.as_pc + 2 * LENGTH items /\
      venom_asm_rel lo
        (ps with <| ps_stack :=
           ps.ps_stack ++ items;
           ps_spilled :=
             FOLDL (\sp item. sp \\ item) ps.ps_spilled items |>)
        vs st'
Proof
  Induct_on `items` >> rpt gen_tac >> strip_tac
  >| [
    (* Base case: items = [] *)
    qexists_tac `st` >>
    simp[Once asm_steps_def] >>
    Cases_on `offsets` >> fs[] >>
    SUBGOAL_THEN ``ps with <| ps_stack := ps.ps_stack;
      ps_spilled := ps.ps_spilled |> = ps``
      (fn th => rewrite_tac [th])
    >- simp[plan_state_component_equality] >>
    fs[],
    (* Step case: h::items *)
    Cases_on `offsets` >> fs[] >>
    rename1 `LENGTH items = LENGTH t` >>
    mp_tac restore_op_venom_asm_rel >>
    disch_then (qspecl_then [`lo`, `o2pc`, `prog`, `h'`,
      `h`, `ps`, `vs`, `st`] mp_tac) >>
    (impl_tac
    >- (
      rpt conj_tac >> TRY (fs[] >> NO_TAC)
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[])
      >> (qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp _)` mp_tac >>
          simp[execute_plan_def, exec_stack_op_def, asm_block_at_cons,
               asm_block_at_nil])
    )) >>
    strip_tac >>
    SUBGOAL_THEN ``asm_block_at prog (st.as_pc + 2)
      (execute_plan initial_fmp (MAP SORestore t))`` ASSUME_TAC
    >- (
      qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp _)` mp_tac >>
      simp[execute_plan_def, exec_stack_op_def,
           asm_block_at_append, asm_block_at_cons, asm_block_at_nil]
    ) >>
    first_x_assum (qspecl_then [`t`, `lo`, `o2pc`, `prog`,
      `ps with <| ps_stack := stack_push h ps.ps_stack;
                  ps_spilled := ps.ps_spilled \\ h |>`,
      `vs`, `st'`] mp_tac) >>
    impl_tac >- suspend "ih_precond" >>
    strip_tac >>
    qexists_tac `st''` >>
    suspend "compose"
  ]
QED

Resume restore_n_sim[ih_precond]:
  simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!k. k < SUC _ ==> _`
    (qspec_then `SUC k` mp_tac) >>
  simp[] >>
  strip_tac >>
  simp[DOMSUB_FLOOKUP_THM] >>
  CCONTR_TAC >> gvs[] >>
  metis_tac[MEM_EL]
QED

Resume restore_n_sim[compose]:
  fs[] >>
  conj_tac
  >- (
    SUBGOAL_THEN ``2 * SUC (LENGTH (t:num list)) =
      2 + 2 * LENGTH t`` SUBST1_TAC
    >- simp[] >>
    irule (GEN_ALL asm_steps_compose_ok) >>
    qexists_tac `st'` >>
    simp[]
  ) >>
  qpat_x_assum `venom_asm_rel lo _ vs st''` mp_tac >>
  CONV_TAC (DEPTH_CONV (REWR_CONV stack_push_def)) >>
  REWRITE_TAC[SNOC_APPEND, GSYM APPEND_ASSOC, APPEND]
QED

Finalise restore_n_sim;

(* ---------------------------------------------------------------
   do_swap_venom_asm_rel_big: dist > 16 case.
   Strategy: unfold do_swap into spill_ops ++ restore_ops,
   apply spill_n_sim for spill phase, restore_n_sim for restore,
   compose via asm_steps_compose_ok.
   --------------------------------------------------------------- *)
(*  flookup_fupdate_list_el: after |++ ZIP(items, offsets),
    looking up EL idx items gives EL idx offsets *)
Theorem flookup_fupdate_list_el[local]:
  !items offsets sp idx.
    ALL_DISTINCT items /\
    LENGTH items = LENGTH offsets /\
    idx < LENGTH items ==>
    FLOOKUP (sp |++ ZIP(items, offsets)) (EL idx items) =
      SOME (EL idx offsets)
Proof
  rpt strip_tac >>
  simp[flookup_fupdate_list,
       alookup_distinct_reverse, MAP_ZIP] >>
  SUBGOAL_THEN ``items❲idx❳ = FST ((ZIP(items,offsets))❲idx❳)``
    SUBST1_TAC
  >- simp[EL_ZIP] >>
  simp[ALOOKUP_ALL_DISTINCT_EL, MAP_ZIP, LENGTH_ZIP, EL_ZIP]
QED

Theorem flookup_fupdate_list_disjoint[local]:
  !keys offsets sp op off.
    LENGTH keys = LENGTH offsets /\
    DISJOINT (set keys) (FDOM sp) /\
    FLOOKUP sp op = SOME off ==>
    FLOOKUP (sp |++ ZIP(keys,offsets)) op = SOME off
Proof
  rpt strip_tac >>
  simp[flookup_fupdate_list] >>
  `op IN FDOM sp` by
    (CCONTR_TAC >> fs[FLOOKUP_DEF]) >>
  `~MEM op keys` by
    (fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `ALOOKUP (REVERSE (ZIP(keys,offsets))) op = NONE` by
    simp[ALOOKUP_NONE, MAP_REVERSE, MAP_ZIP] >>
  simp[]
QED

Theorem prefix_spill_wf_map_spill_from_layout[local]:
  !keys offsets lo ps al'.
    LENGTH keys = LENGTH offsets /\
    keys = TAKE (LENGTH offsets) (REVERSE ps.ps_stack) /\
    ALL_DISTINCT keys /\
    DISJOINT (set keys) (FDOM ps.ps_spilled) /\
    EVERY (\off. off < dimword(:256)) offsets /\
    al'.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    spill_alloc_layout_wf al' (ps.ps_spilled |++ ZIP(keys,offsets)) ==>
    prefix_spill_wf initial_fmp lo (MAP SOSpill offsets) ps
Proof
  rpt strip_tac >>
  qspecl_then [`ZIP(keys,offsets)`, `lo`, `ps`]
    mp_tac prefix_spill_wf_map_spill_pairs >>
  simp[MAP_ZIP] >>
  disch_then irule >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      `k < LENGTH keys` by decide_tac >>
      `LENGTH (TAKE (LENGTH offsets) (REVERSE ps.ps_stack)) = LENGTH offsets` by
        metis_tac[] >>
      `EL k (ZIP(TAKE (LENGTH offsets) (REVERSE ps.ps_stack),offsets)) =
         (EL k (TAKE (LENGTH offsets) (REVERSE ps.ps_stack)), EL k offsets)` by
        (irule EL_ZIP >> simp[]) >>
      ASM_REWRITE_TAC[] >>
      conj_tac >- (fs[EVERY_EL] >> metis_tac[]) >>
      `FLOOKUP (ps.ps_spilled |++ ZIP(keys,offsets)) (EL k keys) =
         SOME (EL k offsets)` by metis_tac[flookup_fupdate_list_el] >>
      conj_tac
      >- (fs[spill_alloc_layout_wf_def] >> metis_tac[]) >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          `FLOOKUP (ps.ps_spilled |++ ZIP(keys,offsets)) op2 = SOME off2` by
            metis_tac[flookup_fupdate_list_disjoint] >>
          `op2 <> EL k keys` by
            (fs[DISJOINT_DEF, EXTENSION] >>
             `op2 IN FDOM ps.ps_spilled` by (CCONTR_TAC >> fs[FLOOKUP_DEF]) >>
             metis_tac[MEM_EL]) >>
          fs[spill_alloc_layout_wf_def] >> metis_tac[]) >>
      rpt strip_tac >>
      `j < LENGTH keys` by decide_tac >>
      `FLOOKUP (ps.ps_spilled |++ ZIP(keys,offsets)) (EL j keys) =
         SOME (EL j offsets)` by metis_tac[flookup_fupdate_list_el] >>
      `j <> k` by decide_tac >>
      `EL j keys <> EL k keys` by metis_tac[ALL_DISTINCT_EL_IMP] >>
      `EL j (ZIP(TAKE (LENGTH offsets) (REVERSE ps.ps_stack),offsets)) =
         (EL j (TAKE (LENGTH offsets) (REVERSE ps.ps_stack)), EL j offsets)` by
        (irule EL_ZIP >> simp[]) >>
      ASM_REWRITE_TAC[] >>
      fs[spill_alloc_layout_wf_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  Cases_on `LENGTH offsets <= LENGTH ps.ps_stack` >> simp[] >>
  fs[LENGTH_TAKE_EQ, LENGTH_REVERSE]
QED

(* spill_alloc_n: wf preservation through the allocation FOLDL *)
Theorem spill_alloc_n_wf[local]:
  !items offs0 al0 sp prev_items.
    spill_alloc_wf al0 (sp |++ ZIP(prev_items, offs0)) /\
    LENGTH prev_items = LENGTH offs0 /\
    ALL_DISTINCT (prev_items ++ items) /\
    al0.sa_next_offset + 32 * LENGTH items < dimword(:256) ==>
    spill_alloc_wf
      (SND (spill_alloc_n offs0 al0 items))
      (sp |++ ZIP(prev_items ++ items,
                  FST (spill_alloc_n offs0 al0 items)))
Proof
  Induct >- simp[spill_alloc_n_def] >>
  simp[spill_alloc_n_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot al0` >>
  rename1 `alloc_spill_slot al0 = (off0, al1)` >>
  simp[] >>
  imp_res_tac alloc_spill_slot_next_offset_upper >>
  first_x_assum (qspecl_then [`SNOC off0 offs0`, `al1`, `sp`,
    `prev_items ++ [h]`] mp_tac) >>
  simp[LENGTH_SNOC] >>
  suspend "step_case"
QED

Resume spill_alloc_n_wf[step_case]:
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[CONS_APPEND]
    THENC REWRITE_CONV[APPEND_ASSOC])) >>
  disch_then irule >>
  suspend "wf_preconds"
QED

Resume spill_alloc_n_wf[wf_preconds]:
  conj_tac
  >- (
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    REWRITE_TAC[APPEND, GSYM APPEND_ASSOC]
  )
  >>
  PURE_REWRITE_TAC[SNOC_APPEND] >>
  simp[GSYM ZIP_APPEND, FUPDATE_LIST_APPEND, FUPDATE_LIST_THM] >>
  irule spill_alloc_wf_after_spill >>
  conj_tac >- (gvs[] >> decide_tac) >>
  qexists_tac `al0` >> simp[]
QED

Finalise spill_alloc_n_wf;


(* spill_alloc_n prefix-split: offs0 prefix factored out *)
Theorem spill_alloc_n_fst_prefix[local]:
  !items a b al0.
    FST (spill_alloc_n (a ++ b) al0 items) =
    a ++ FST (spill_alloc_n b al0 items)
Proof
  Induct >> simp[spill_alloc_n_def] >>
  rpt strip_tac >>
  Cases_on `alloc_spill_slot al0` >> simp[] >>
  (* SNOC off (a ++ b) = a ++ SNOC off b *)
  REWRITE_TAC[SNOC_APPEND, GSYM APPEND_ASSOC] >>
  simp[]
QED

Theorem spill_alloc_n_fst_cons[local]:
  !items x al0.
    FST (spill_alloc_n [x] al0 items) =
    x :: FST (spill_alloc_n [] al0 items)
Proof
  rpt strip_tac >>
  qspecl_then [`items`, `[x]`, `[]`, `al0`] mp_tac spill_alloc_n_fst_prefix >>
  simp[]
QED

(* spill_alloc_n: per-offset properties with DISJOINT precondition *)
Theorem spill_alloc_n_offset_props[local]:
  !items al0 sp.
    spill_alloc_wf al0 sp /\
    ALL_DISTINCT items /\
    DISJOINT (set items) (FDOM sp) /\
    al0.sa_next_offset + 32 * LENGTH items < dimword(:256) ==>
    let offsets = FST (spill_alloc_n [] al0 items) in
    !k. k < LENGTH offsets ==>
      EL k offsets < dimword(:256) /\
      al0.sa_spill_base <= EL k offsets /\
      (!op2 off2. FLOOKUP sp op2 = SOME off2 ==>
         off2 + 32 <= EL k offsets \/
         EL k offsets + 32 <= off2) /\
      (!j. j < k ==>
         EL j offsets + 32 <= EL k offsets \/
         EL k offsets + 32 <= EL j offsets)
Proof
  Induct >> simp[spill_alloc_n_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot al0` >>
  rename1 `alloc_spill_slot al0 = (off0, al1)` >>
  simp[] >>
  drule_all alloc_spill_slot_wf >> strip_tac >>
  imp_res_tac alloc_spill_slot_spill_base >>
  imp_res_tac alloc_spill_slot_next_offset_upper >>
  simp[spill_alloc_n_fst_cons, LET_THM] >>
  suspend "setup"
QED

Resume spill_alloc_n_offset_props[setup]:
  (* Apply IH, simplify preconditions *)
  first_x_assum (qspecl_then [`al1`, `sp |+ (h, off0)`] mp_tac) >>
  simp[LET_THM, spill_alloc_n_offsets_length, FDOM_FUPDATE,
       DISJOINT_INSERT'] >>
  SUBGOAL_THEN ``spill_alloc_wf al1 (sp |+ (h, off0))``
    (fn th => REWRITE_TAC[th]) THENL
    [irule spill_alloc_wf_after_spill >>
     CONJ_TAC THENL [gvs[] >> decide_tac, ALL_TAC] >>
     qexists_tac `al0` >> simp[FUPDATE_LIST_THM],
     ALL_TAC] >>
  disch_tac >>
  suspend "cases"
QED

Resume spill_alloc_n_offset_props[cases]:
  rpt strip_tac >>
  Cases_on `k` >> simp[]
  >| [
    (* k=0: off0 separation from FLOOKUP sp *)
    metis_tac[],
    (* k=SUC n: FLOOKUP separation — weaken IH from sp|+(h,off0) to sp *)
    first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
    qpat_x_assum `!op2 off2. FLOOKUP (sp |+ (h,off0)) op2 = SOME off2 ==> _`
      (qspecl_then [`op2`, `off2`] mp_tac) >>
    simp[FLOOKUP_UPDATE] >>
    disch_then match_mp_tac >>
    Cases_on `h = op2` >> simp[] >> gvs[flookup_thm],
    (* k=SUC n: pairwise j — j=0 uses off0 via FLOOKUP_UPDATE, j>0 from IH *)
    first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
    Cases_on `j` >> simp[] >>
    qpat_x_assum `!op2 off2. FLOOKUP (sp |+ (h,off0)) op2 = SOME off2 ==> _`
      (qspecl_then [`h`, `off0`] mp_tac) >>
    simp[FLOOKUP_UPDATE]
  ]
QED

Finalise spill_alloc_n_offset_props;

(* ---------------------------------------------------------------
   do_swap desired permutation helpers
   --------------------------------------------------------------- *)

(* The desired permutation indices are all < chunk *)
Theorem desired_indices_bound[local]:
  !(n:num) k.
    n >= 2 /\
    k < n ==>
    EL k (REVERSE ([n - 1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0])) < n
Proof
  rpt strip_tac >>
  qabbrev_tac `l = [n-1] ++ GENLIST (\i. i+1) (n-2) ++ [0]` >>
  `EVERY (\x. x < n) (REVERSE l)` suffices_by
    (strip_tac >>
     imp_res_tac (SIMP_RULE std_ss [AND_IMP_INTRO] EVERY_EL) >>
     fs[LENGTH_REVERSE, Abbr `l`, LENGTH_GENLIST]) >>
  simp[EVERY_REVERSE, Abbr `l`, EVERY_APPEND, EVERY_GENLIST]
QED

(* The desired permutation indices are ALL_DISTINCT *)
Theorem desired_indices_all_distinct[local]:
  !(n:num).
    n >= 2 ==>
    ALL_DISTINCT (REVERSE ([n - 1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0]))
Proof
  simp[ALL_DISTINCT_REVERSE, ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST,
       MEM_GENLIST]
QED

(* ALL_DISTINCT preserved when mapping EL over ALL_DISTINCT indices
   into an ALL_DISTINCT list *)
Theorem all_distinct_map_el[local]:
  !idxs items.
    ALL_DISTINCT idxs /\
    ALL_DISTINCT items /\
    EVERY (\i. i < LENGTH items) idxs ==>
    ALL_DISTINCT (MAP (\i. EL i items) idxs)
Proof
  Induct >> simp[] >>
  rpt strip_tac >> fs[EVERY_MEM, MEM_MAP] >>
  CCONTR_TAC >> fs[] >>
  metis_tac[EL_ALL_DISTINCT_EL_EQ]
QED

(* LENGTH of desired permutation = n *)
Theorem desired_length[local]:
  !(n:num).
    n >= 2 ==>
    LENGTH (REVERSE ([n - 1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0])) = n
Proof
  simp[LENGTH_REVERSE, LENGTH_GENLIST]
QED

(* Structural decomposition of do_swap for dist > 16.
   Extracts spill_ops, restore_ops, and final state. *)
Theorem do_swap_big_decompose[local]:
  !dist ps.
    dist > 16 /\ dist < LENGTH ps.ps_stack ==>
    let items = top_n (dist + 1) ps.ps_stack;
        offsets = FST (spill_alloc_n [] ps.ps_alloc items);
        alloc1 = SND (spill_alloc_n [] ps.ps_alloc items);
        desired = [dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0];
        desired_rev = REVERSE desired;
        restore_offsets = MAP (\idx. EL idx offsets) desired_rev;
        base_stack = TAKE (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack;
        restored = MAP (\idx. EL idx items) desired;
        alloc2 = FOLDL (\al off. free_spill_slot off al) alloc1 offsets
    in
      do_swap dist ps =
        (MAP SOSpill offsets ++ MAP SORestore restore_offsets,
         ps with <| ps_stack := base_stack ++ restored;
                    ps_alloc := alloc2 |>)
Proof
  rpt strip_tac >>
  simp[LET_THM, do_swap_def] >>
  qabbrev_tac `fres = FOLDL
    (\(ops,offs,al) item.
       (\(off,al2). (ops ++ [SOSpill off], SNOC off offs, al2))
         (alloc_spill_slot al))
    ([],[],ps.ps_alloc) (top_n (dist + 1) ps.ps_stack)` >>
  PairCases_on `fres` >> fs[] >>
  qspecl_then [`top_n (dist+1) ps.ps_stack`, `[]`,
               `[]`, `ps.ps_alloc`]
    mp_tac spill_foldl_snd_eq >>
  fs[] >> strip_tac >>
  qspecl_then [`top_n (dist+1) ps.ps_stack`, `[]`,
               `[]`, `ps.ps_alloc`]
    mp_tac spill_foldl_ops_eq_map >>
  simp[] >> fs[] >> strip_tac >>
  Cases_on `spill_alloc_n [] ps.ps_alloc
    (top_n (dist + 1) ps.ps_stack)` >>
  gvs[plan_state_component_equality, MAP_MAP_o, combinTheory.o_DEF]
QED

(* Structural decomposition of the deep duplication branch. *)
Theorem do_dup_big_decompose[local]:
  !dist ps.
    dist > 15 /\ dist < LENGTH ps.ps_stack ==>
    let items = top_n (dist + 1) ps.ps_stack;
        offsets = FST (spill_alloc_n [] ps.ps_alloc items);
        alloc1 = SND (spill_alloc_n [] ps.ps_alloc items);
        desired = GENLIST I (dist + 1) ++ [0];
        base_stack = TAKE (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack;
        restored = MAP (\idx. EL idx items) desired;
        alloc2 = FOLDL (\al off. free_spill_slot off al) alloc1 offsets
    in
      do_dup dist ps =
        (MAP SOSpill offsets ++
           MAP (\idx. SORestore (EL idx offsets)) (REVERSE desired),
         ps with <| ps_stack := base_stack ++ restored;
                    ps_alloc := alloc2 |>)
Proof
  rpt strip_tac >>
  simp[LET_THM, do_dup_def] >>
  qabbrev_tac `fres = FOLDL
    (\(ops,offs,al) item.
       (\(off,al2). (ops ++ [SOSpill off], SNOC off offs, al2))
         (alloc_spill_slot al))
    ([],[],ps.ps_alloc) (top_n (dist + 1) ps.ps_stack)` >>
  PairCases_on `fres` >> fs[] >>
  qspecl_then [`top_n (dist+1) ps.ps_stack`, `[]`,
               `[]`, `ps.ps_alloc`]
    mp_tac spill_foldl_snd_eq >>
  fs[] >> strip_tac >>
  qspecl_then [`top_n (dist+1) ps.ps_stack`, `[]`,
               `[]`, `ps.ps_alloc`]
    mp_tac spill_foldl_ops_eq_map >>
  simp[] >> fs[] >> strip_tac >>
  Cases_on `spill_alloc_n [] ps.ps_alloc
    (top_n (dist + 1) ps.ps_stack)` >>
  gvs[plan_state_component_equality, MAP_MAP_o, combinTheory.o_DEF]
QED

(* FOLDL DOMSUB removes all listed keys from a map's domain *)
Theorem fdom_foldl_domsub[local]:
  !keys fm. FDOM (FOLDL (\sp k. sp \\ k) fm keys) = FDOM fm DIFF set keys
Proof
  Induct >> simp[DIFF_INSERT, DOMSUB_FUPDATE_THM]
QED

(* FLOOKUP through FOLDL DOMSUB for keys not removed *)
Theorem flookup_foldl_domsub[local]:
  !keys fm k. ~MEM k keys ==>
    FLOOKUP (FOLDL (\sp (k':operand). sp \\ k') fm keys) k = FLOOKUP fm k
Proof
  Induct >> simp[DOMSUB_FLOOKUP_THM]
QED

(* After adding then removing the same keys, the map is unchanged *)
Theorem foldl_domsub_cancel[local]:
  !keys kvs (fm:operand |-> num).
    set keys = set (MAP FST kvs) /\
    DISJOINT (set keys) (FDOM fm) ==>
    FOLDL (\sp k. sp \\ k) (fm |++ kvs) keys = fm
Proof
  rpt strip_tac >>
  simp[FLOOKUP_EXT, FUN_EQ_THM] >>
  rpt strip_tac >>
  Cases_on `MEM x keys`
  >- (
    `x NOTIN FDOM (FOLDL (\sp k. sp \\ k) (fm |++ kvs) keys) /\
     x NOTIN FDOM fm` suffices_by metis_tac[FLOOKUP_DEF] >>
    simp[fdom_foldl_domsub] >>
    fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
  )
  >>
  `FLOOKUP (fm |++ kvs) x = FLOOKUP fm x` suffices_by
    simp[flookup_foldl_domsub] >>
  simp[flookup_fupdate_list] >>
  `ALOOKUP (REVERSE kvs) x = NONE` suffices_by simp[] >>
  simp[ALOOKUP_NONE, MAP_REVERSE, MEM_REVERSE] >>
  fs[EXTENSION] >> metis_tac[]
QED

(* Durable layout preservation through a batch of temporary allocations. *)
Theorem spill_alloc_n_layout_wf[local]:
  !items offs0 al0 sp prev_items.
    spill_alloc_layout_wf al0 (sp |++ ZIP(prev_items, offs0)) /\
    LENGTH prev_items = LENGTH offs0 /\
    ALL_DISTINCT (prev_items ++ items) ==>
    spill_alloc_layout_wf
      (SND (spill_alloc_n offs0 al0 items))
      (sp |++ ZIP(prev_items ++ items,
                  FST (spill_alloc_n offs0 al0 items)))
Proof
  Induct >- simp[spill_alloc_n_def] >>
  simp[spill_alloc_n_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot al0` >>
  rename1 `alloc_spill_slot al0 = (off0, al1)` >>
  simp[] >>
  first_x_assum (qspecl_then [`SNOC off0 offs0`, `al1`, `sp`,
    `prev_items ++ [h]`] mp_tac) >>
  simp[LENGTH_SNOC] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV[CONS_APPEND]
    THENC REWRITE_CONV[APPEND_ASSOC])) >>
  disch_then irule >>
  conj_tac
  >- (qpat_x_assum `ALL_DISTINCT _` mp_tac >>
      REWRITE_TAC[APPEND, GSYM APPEND_ASSOC]) >>
  PURE_REWRITE_TAC[SNOC_APPEND] >>
  simp[GSYM ZIP_APPEND, FUPDATE_LIST_APPEND, FUPDATE_LIST_THM] >>
  irule spill_alloc_layout_wf_after_alloc >>
  qexists_tac `al0` >> simp[]
QED

(* Allocation offsets and allocator evolution depend only on item count. *)
Theorem spill_alloc_n_length_cong[local]:
  !xs ys offs al.
    LENGTH xs = LENGTH ys ==>
    spill_alloc_n offs al xs = spill_alloc_n offs al ys
Proof
  Induct >> Cases_on `ys` >> simp[spill_alloc_n_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot al` >> simp[]
QED

(* Durable batch allocation with keys independent of the list used to drive
   allocator iteration.  This matches do_swap, whose spills pop REVERSE items. *)
Theorem spill_alloc_n_layout_wf_keys[local]:
  !alloc_items keys al sp.
    spill_alloc_layout_wf al sp /\
    LENGTH keys = LENGTH alloc_items /\
    ALL_DISTINCT keys /\
    DISJOINT (set keys) (FDOM sp) ==>
    spill_alloc_layout_wf
      (SND (spill_alloc_n [] al alloc_items))
      (sp |++ ZIP(keys, FST (spill_alloc_n [] al alloc_items)))
Proof
  rpt gen_tac >> strip_tac >>
  `spill_alloc_n [] al keys = spill_alloc_n [] al alloc_items` by
    metis_tac[spill_alloc_n_length_cong] >>
  qspecl_then [`keys`, `[]`, `al`, `sp`, `[]`]
    mp_tac spill_alloc_n_layout_wf >>
  simp[FUPDATE_LIST_THM]
QED


(* Project the pairwise spilled-offset separation clause without unfolding the
   full durable-layout invariant in large consumer goals. *)
Theorem spill_alloc_layout_wf_spilled_separated:
  !al spilled.
    spill_alloc_layout_wf al spilled ==>
    !op1 off1 op2 off2.
      FLOOKUP spilled op1 = SOME off1 /\
      FLOOKUP spilled op2 = SOME off2 /\
      op1 <> op2 ==>
      off1 + 32 <= off2 \/ off2 + 32 <= off1
Proof
  rpt gen_tac >> rw[spill_alloc_layout_wf_def] >> metis_tac[]
QED

(* Initial offset accumulator does not affect allocator evolution. *)
Theorem spill_alloc_n_snd_initial[local]:
  !items offs1 offs2 al.
    SND (spill_alloc_n offs1 al items) = SND (spill_alloc_n offs2 al items)
Proof
  Induct >> simp[spill_alloc_n_def] >>
  rpt gen_tac >> Cases_on `alloc_spill_slot al` >> simp[]
QED

(* The MAX updates performed by SOSpill track the allocator high-water mark,
   including free-slot reuse.  Temporary keys witness durable layout at each step. *)
Theorem spill_alloc_n_foldl_max_next[local]:
  !items (keys:operand list) al sp.
    spill_alloc_layout_wf al sp /\
    LENGTH keys = LENGTH items /\ ALL_DISTINCT keys /\
    DISJOINT (set keys) (FDOM sp) ==>
    FOLDL MAX al.sa_next_offset
      (MAP (\off. off + 32) (FST (spill_alloc_n [] al items))) =
    (SND (spill_alloc_n [] al items)).sa_next_offset
Proof
  Induct
  >- (Cases_on `keys` >> simp[spill_alloc_n_def]) >>
  rpt gen_tac >> Cases_on `keys` >- simp[] >> strip_tac >>
  Cases_on `alloc_spill_slot al` >>
  rename1 `alloc_spill_slot al = (off,al1)` >>
  `MAX al.sa_next_offset (off + 32) = al1.sa_next_offset` by
    metis_tac[alloc_spill_slot_max_agree] >>
  `spill_alloc_layout_wf al1 (sp |+ (h',off))` by
    (irule spill_alloc_layout_wf_after_alloc >> metis_tac[]) >>
  first_x_assum (qspecl_then [`t`, `al1`, `sp |+ (h',off)`] mp_tac) >>
  impl_tac
  >- (gvs[ALL_DISTINCT, DISJOINT_INSERT] >>
      fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  simp[spill_alloc_n_def, spill_alloc_n_fst_cons] >> strip_tac >>
  metis_tac[spill_alloc_n_snd_initial]
QED



(* Free matching offsets while deleting their temporary map keys. *)
Theorem foldl_free_domsub_layout_wf[local]:
  !items offsets al fm.
    LENGTH items = LENGTH offsets /\ ALL_DISTINCT items /\
    (!i. i < LENGTH items ==>
         FLOOKUP fm (EL i items) = SOME (EL i offsets)) /\
    spill_alloc_layout_wf al fm ==>
    spill_alloc_layout_wf
      (FOLDL (\a off. free_spill_slot off a) al offsets)
      (FOLDL (\sp item. sp \\ item) fm items)
Proof
  Induct >- (Cases_on `offsets` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `offsets` >> gvs[] >>
  rename1 `off::offs` >>
  simp[] >>
  `FLOOKUP fm off = SOME h'` by (
    qpat_x_assum `!i. i < SUC _ ==> _` (qspec_then `0` mp_tac) >> simp[]) >>
  `spill_alloc_layout_wf (free_spill_slot h' al) (fm \\ off)` by (
    irule spill_alloc_layout_wf_after_free >> simp[]) >>
  first_x_assum (qspecl_then [`t`, `free_spill_slot h' al`, `fm \\ off`] irule) >>
  simp[] >>
  rpt strip_tac >>
  `EL i offs <> off` by metis_tac[MEM_EL] >>
  simp[DOMSUB_FLOOKUP_THM] >>
  qpat_x_assum `!j. j < SUC _ ==> _` (qspec_then `SUC i` mp_tac) >>
  simp[]
QED

Theorem spill_alloc_n_free_layout_wf[local]:
  !al spilled items.
    spill_alloc_layout_wf al spilled /\ ALL_DISTINCT items /\
    DISJOINT (set items) (FDOM spilled) ==>
    let res = spill_alloc_n [] al items;
        offsets = FST res;
        alloc2 = FOLDL (\a off. free_spill_slot off a) (SND res) offsets
    in spill_alloc_layout_wf alloc2 spilled
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] al items)` >>
  qabbrev_tac `alloc1 = SND (spill_alloc_n [] al items)` >>
  `LENGTH items = LENGTH offsets` by
    simp[Abbr `offsets`, spill_alloc_n_offsets_length] >>
  `spill_alloc_layout_wf alloc1 (spilled |++ ZIP(items, offsets))` by (
    qunabbrev_tac `alloc1` >> qunabbrev_tac `offsets` >>
    qspecl_then [`items`, `[]`, `al`, `spilled`, `[]`]
      mp_tac spill_alloc_n_layout_wf >> simp[FUPDATE_LIST_THM]) >>
  `!i. i < LENGTH items ==>
       FLOOKUP (spilled |++ ZIP(items, offsets)) (EL i items) =
         SOME (EL i offsets)` by
    metis_tac[flookup_fupdate_list_el] >>
  `spill_alloc_layout_wf
     (FOLDL (\a off. free_spill_slot off a) alloc1 offsets)
     (FOLDL (\sp item. sp \\ item)
       (spilled |++ ZIP(items, offsets)) items)` by (
    irule foldl_free_domsub_layout_wf >> simp[]) >>
  `FOLDL (\sp item. sp \\ item)
      (spilled |++ ZIP(items, offsets)) items = spilled` by (
    irule foldl_domsub_cancel >>
    simp[MAP_ZIP]) >>
  gvs[Abbr `alloc1`, Abbr `offsets`]
QED

(* Operands are infinite because variables contain strings of arbitrary length. *)
Theorem operand_univ_infinite[local]:
  INFINITE (UNIV:operand set)
Proof
  `INFINITE (IMAGE (\n:num. Var (REPLICATE n #"x")) UNIV)` by
    (irule IMAGE_11_INFINITE >> simp[] >>
     rpt strip_tac >>
     pop_assum (mp_tac o AP_TERM ``LENGTH:string -> num``) >> simp[]) >>
  irule INFINITE_SUBSET >>
  qexists_tac `IMAGE (\n:num. Var (REPLICATE n #"x")) UNIV` >>
  simp[]
QED

(* An operand list of any finite length can be chosen fresh from a finite map. *)
Theorem fresh_operand_list[local]:
  !n (s:operand set).
    FINITE s ==>
    ?keys. LENGTH keys = n /\ ALL_DISTINCT keys /\ DISJOINT (set keys) s
Proof
  Induct
  >- simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  disch_then (qx_choose_then `keys` strip_assume_tac) >>
  `?x:operand. x IN UNIV /\ x NOTIN (s UNION set keys)` by
    (irule IN_INFINITE_NOT_FINITE >> simp[operand_univ_infinite]) >>
  qexists_tac `x::keys` >>
  simp[DISJOINT_INSERT'] >>
  fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

(* Allocating one temporary slot per list occurrence and freeing exactly the
   returned offsets restores durable layout, independently of item values. *)
Theorem spill_alloc_n_free_layout_wf_arbitrary:
  !al spilled items.
    spill_alloc_layout_wf al spilled ==>
    let res = spill_alloc_n [] al items;
        offsets = FST res;
        alloc2 = FOLDL (\a off. free_spill_slot off a) (SND res) offsets
    in spill_alloc_layout_wf alloc2 spilled
Proof
  rpt gen_tac >> strip_tac >>
  `?keys:operand list.
      LENGTH keys = LENGTH items /\ ALL_DISTINCT keys /\
      DISJOINT (set keys) (FDOM spilled)` by
    (irule fresh_operand_list >> simp[]) >>
  `spill_alloc_n [] al keys = spill_alloc_n [] al items` by
    metis_tac[spill_alloc_n_length_cong] >>
  qspecl_then [`al`, `spilled`, `keys`] mp_tac
    spill_alloc_n_free_layout_wf >>
  simp[]
QED



(* A valid stack swap is a transposition of two in-range positions. *)
Theorem stack_swap_permutation:
  !dist stk.
    0 < dist /\ dist < LENGTH stk /\ ALL_DISTINCT stk ==>
    ALL_DISTINCT (stack_swap dist stk) /\
    set (stack_swap dist stk) = set stk
Proof
  rpt strip_tac >>
  `LENGTH stk - 1 < LENGTH stk /\
   LENGTH stk - (dist + 1) < LENGTH stk` by decide_tac >>
  `!i j. i < LENGTH stk /\ j < LENGTH stk /\ i <> j ==>
      EL i stk <> EL j stk` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  simp[stack_swap_def]
  >- (rw[EL_ALL_DISTINCT_EL_EQ] >>
      rpt strip_tac >>
      simp[EL_LUPDATE] >>
      rpt IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
  `MEM (EL (LENGTH stk - 1) stk) stk /\
   MEM (EL (LENGTH stk - (dist + 1)) stk) stk` by (
    conj_tac
    >- (simp[MEM_EL] >> qexists_tac `LENGTH stk - 1` >> simp[]) >>
    simp[MEM_EL] >> qexists_tac `LENGTH stk - (dist + 1)` >> simp[]) >>
  rw[EXTENSION] >> eq_tac >> strip_tac
  >- (drule MEM_LUPDATE_E >> strip_tac >- gvs[] >>
      drule MEM_LUPDATE_E >> strip_tac >> gvs[]) >>
  Cases_on `x = EL (LENGTH stk - 1) stk`
  >- simp[MEM_LUPDATE] >>
  Cases_on `x = EL (LENGTH stk - (dist + 1)) stk`
  >- (simp[MEM_LUPDATE] >>
      qexists_tac `LENGTH stk - 1` >> simp[EL_LUPDATE] >> decide_tac) >>
  qpat_x_assum `MEM x stk` mp_tac >> simp[MEM_EL] >>
  disch_then (qx_choose_then `k` strip_assume_tac) >>
  simp[MEM_LUPDATE] >>
  qexists_tac `k` >> simp[EL_LUPDATE] >>
  metis_tac[]
QED

Theorem top_n_suffix[local]:
  !n stk. n <= LENGTH stk ==>
    TAKE (LENGTH stk - n) stk ++ top_n n stk = stk
Proof
  rpt strip_tac >>
  `top_n n stk = LASTN n stk` by simp[top_n_def, LASTN_def] >>
  `TAKE (LENGTH stk - n) stk = BUTLASTN n stk` by
    metis_tac[BUTLASTN_TAKE] >>
  metis_tac[APPEND_BUTLASTN_LASTN]
QED

(* Duplication appends exactly the selected operand, including in the deep
   spill/restore implementation. *)
Theorem do_dup_stack_exact:
  !dist ps.
    dist < LENGTH ps.ps_stack ==>
    (SND (do_dup dist ps)).ps_stack =
      ps.ps_stack ++ [stack_peek dist ps.ps_stack]
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist <= 15`
  >- simp[do_dup_def, stack_dup_def] >>
  `dist > 15 /\ dist + 1 <= LENGTH ps.ps_stack` by decide_tac >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_dup_big_decompose) >>
  simp[LET_THM] >> strip_tac >>
  `LENGTH (top_n (dist + 1) ps.ps_stack) = dist + 1` by
    simp[top_n_def, LENGTH_REVERSE, LENGTH_TAKE] >>
  `MAP (\idx. EL idx (top_n (dist + 1) ps.ps_stack))
       (GENLIST I (dist + 1)) = top_n (dist + 1) ps.ps_stack` by
    (simp[MAP_GENLIST, combinTheory.I_THM] >>
     metis_tac[GENLIST_ID]) >>
  `ps.ps_stack <> []` by (Cases_on `ps.ps_stack` >> fs[]) >>
  `EL 0 (top_n (dist + 1) ps.ps_stack) =
     stack_peek dist ps.ps_stack` by
    (`TAKE (dist + 1) (REVERSE ps.ps_stack) <> []` by
       simp[LENGTH_TAKE] >>
     simp[top_n_def, stack_peek_def, HD_REVERSE, LAST_EL, EL_TAKE,
          EL_REVERSE, PRE_SUB1]) >>
  `TAKE (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack ++
     top_n (dist + 1) ps.ps_stack = ps.ps_stack` by
    metis_tac[top_n_suffix] >>
  gvs[MAP_APPEND]
QED

(* Duplication preserves the spill map and its durable allocator layout. *)
Theorem do_dup_layout_wf:
  !dist ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dist < LENGTH ps.ps_stack ==>
    (SND (do_dup dist ps)).ps_spilled = ps.ps_spilled /\
    spill_alloc_layout_wf (SND (do_dup dist ps)).ps_alloc
                          (SND (do_dup dist ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist <= 15`
  >- simp[do_dup_def] >>
  `dist > 15 /\ dist + 1 <= LENGTH ps.ps_stack` by decide_tac >>
  `spill_alloc_layout_wf
     (FOLDL (\a off. free_spill_slot off a)
       (SND (spill_alloc_n [] ps.ps_alloc
         (top_n (dist + 1) ps.ps_stack)))
       (FST (spill_alloc_n [] ps.ps_alloc
         (top_n (dist + 1) ps.ps_stack))))
     ps.ps_spilled` by
    (drule_then
       (qspec_then `top_n (dist + 1) ps.ps_stack` mp_tac)
       spill_alloc_n_free_layout_wf_arbitrary >>
     simp[LET_THM]) >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_dup_big_decompose) >>
  simp[LET_THM] >> strip_tac >> gvs[]
QED

(* Consumer boundary: exact multiplicity, unchanged spill ownership, and
   preserved layout, with no distinctness premise on the stack. *)
Theorem do_dup_multiplicity_layout:
  !dist ps ops ps'.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dist < LENGTH ps.ps_stack /\
    do_dup dist ps = (ops, ps') ==>
    ps'.ps_spilled = ps.ps_spilled /\
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
    (!x. LIST_ELEM_COUNT x ps'.ps_stack =
         LIST_ELEM_COUNT x ps.ps_stack +
           (if x = stack_peek dist ps.ps_stack then 1 else 0))
Proof
  rpt gen_tac >> strip_tac >>
  `ps' = SND (do_dup dist ps)` by
    (Cases_on `do_dup dist ps` >> gvs[]) >>
  qpat_x_assum `ps' = _` SUBST_ALL_TAC >>
  drule_all do_dup_layout_wf >> strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  gen_tac >>
  drule do_dup_stack_exact >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[LIST_ELEM_COUNT_DEF, FILTER_APPEND] >>
  Cases_on `x = stack_peek dist ps.ps_stack` >> simp[]
QED

(* ---------------------------------------------------------------
   Helpers for do_swap_venom_asm_rel_big
   --------------------------------------------------------------- *)

(* When sa_free_slots = [], alloc bumps sa_next_offset by 32 per item *)
Theorem spill_alloc_n_next_offset_no_free[local]:
  !items offs0 al.
    al.sa_free_slots = [] ==>
    (SND (spill_alloc_n offs0 al items)).sa_next_offset =
      al.sa_next_offset + 32 * LENGTH items
Proof
  Induct >> simp[spill_alloc_n_def] >>
  rpt strip_tac >>
  simp[alloc_spill_slot_def] >>
  first_x_assum (qspecl_then [`SNOC al.sa_next_offset offs0`,
    `al with sa_next_offset := al.sa_next_offset + 32`] mp_tac) >>
  simp[LEFT_ADD_DISTRIB]
QED

(* When sa_free_slots = [], alloc keeps sa_free_slots = [] *)
Theorem spill_alloc_n_free_slots_nil[local]:
  !items offs0 al.
    al.sa_free_slots = [] ==>
    (SND (spill_alloc_n offs0 al items)).sa_free_slots = []
Proof
  Induct >> simp[spill_alloc_n_def] >>
  rpt strip_tac >>
  simp[alloc_spill_slot_def] >>
  first_x_assum (qspecl_then [`SNOC al.sa_next_offset offs0`,
    `al with sa_next_offset := al.sa_next_offset + 32`] mp_tac) >>
  simp[]
QED

(* When sa_free_slots = [], offsets are base, base+32, base+64, ... *)
Theorem spill_alloc_n_offsets_val[local]:
  !items al.
    al.sa_free_slots = [] ==>
    FST (spill_alloc_n [] al items) =
      GENLIST (\i. al.sa_next_offset + 32 * i) (LENGTH items)
Proof
  Induct >> simp[spill_alloc_n_def, alloc_spill_slot_def] >>
  rpt strip_tac >>
  qabbrev_tac `al1 = al with sa_next_offset := al.sa_next_offset + 32` >>
  simp[spill_alloc_n_fst_cons] >>
  first_x_assum (qspec_then `al1` mp_tac) >>
  simp[Abbr `al1`] >> strip_tac >> simp[] >>
  simp[GENLIST_CONS, combinTheory.o_DEF] >>
  simp[LIST_EQ_REWRITE, EL_GENLIST, LENGTH_GENLIST]
QED

(* FOLDL free_spill_slot preserves sa_next_offset *)
Theorem foldl_free_next_offset[local]:
  !offsets al.
    (FOLDL (\al off. free_spill_slot off al) al offsets).sa_next_offset =
      al.sa_next_offset
Proof
  Induct >> rpt strip_tac >> simp[] >>
  simp[Once free_spill_slot_def]
QED

(* FOLDL free_spill_slot preserves sa_spill_base *)
Theorem foldl_free_spill_base[local]:
  !offsets al.
    (FOLDL (\al off. free_spill_slot off al) al offsets).sa_spill_base =
      al.sa_spill_base
Proof
  Induct >> rpt strip_tac >> simp[] >>
  simp[Once free_spill_slot_def]
QED

(* FOLDL free_spill_slot appends each returned slot in order. *)
Theorem foldl_free_free_slots[local]:
  !offsets al.
    (FOLDL (\al off. free_spill_slot off al) al offsets).sa_free_slots =
    al.sa_free_slots ++ offsets
Proof
  Induct >> rpt strip_tac >> simp[] >>
  simp[Once free_spill_slot_def] >>
  first_x_assum (qspec_then
    `al with sa_free_slots := SNOC h al.sa_free_slots` mp_tac) >>
  simp[SNOC_APPEND]
QED

(* FOLDL MAX over monotone increasing sequence *)
Theorem foldl_max_genlist[local]:
  !(n:num) base.
    FOLDL MAX base (GENLIST (\i. base + 32 * (i + 1)) n) = base + 32 * n
Proof
  Induct >> simp[GENLIST, FOLDL_SNOC] >>
  rpt strip_tac >> simp[MAX_DEF]
QED

(* set of desired permutation = count_list *)
Theorem set_desired_eq[local]:
  !(n:num).
    n >= 2 ==>
    set ([n-1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0]) =
      count n
Proof
  rpt strip_tac >>
  simp[EXTENSION, MEM_GENLIST, IN_COUNT] >>
  rpt strip_tac >> eq_tac >> strip_tac >> simp[] >>
  Cases_on `x = 0` >> simp[] >>
  Cases_on `x = n - 1` >> simp[] >>
  qexists_tac `x - 1` >> decide_tac
QED

(* set (MAP (\idx. EL idx items) desired) = set items
   when desired is a permutation of [0..LENGTH items - 1] *)
Theorem set_map_el_perm[local]:
  !idxs items.
    LENGTH items >= 2 /\
    set idxs = count (LENGTH items) /\
    LENGTH idxs = LENGTH items ==>
    set (MAP (\idx. EL idx items) idxs) = set items
Proof
  rpt strip_tac >>
  simp[EXTENSION, MEM_MAP, IN_COUNT] >>
  rpt strip_tac >> eq_tac >> strip_tac
  >- (fs[] >> metis_tac[MEM_EL])
  >> fs[MEM_EL] >> qexists_tac `n` >>
  simp[] >> fs[EXTENSION, IN_COUNT] >>
  metis_tac[]
QED

(* Combined: desired permutation preserves set, parametric in n *)
Theorem set_desired_perm[local]:
  !(n:num) items.
    LENGTH items = n /\ n >= 2 ==>
    set (MAP (\idx. EL idx items)
         ([n - 1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0]))
    = set items
Proof
  rpt strip_tac >>
  irule set_map_el_perm >>
  ASM_REWRITE_TAC[LENGTH_GENLIST, LENGTH_APPEND, LENGTH] >>
  (conj_tac >- (irule set_desired_eq >> decide_tac)) >>
  decide_tac
QED

(* Helper: EL k of the desired permutation list *)
Theorem el_desired_list[local]:
  !(n:num) k.
    n >= 2 /\ k < n ==>
    EL k ([n-1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0]) =
    if k = 0 then n - 1
    else if k < n - 1 then k
    else 0
Proof
  rpt strip_tac >>
  Cases_on `k = 0` >- simp[] >>
  Cases_on `k < n - 1`
  >- simp[EL_APPEND1, EL_APPEND2, LENGTH_GENLIST, EL_GENLIST]
  >> `k = n - 1` suffices_by (
    strip_tac >> gvs[EL_APPEND1, EL_APPEND2, LENGTH_GENLIST]
  ) >>
  decide_tac
QED

(* EL k of the reversed desired permutation list *)
Theorem el_reverse_desired_list[local]:
  !(n:num) k.
    n >= 2 /\ k < n ==>
    EL k (REVERSE ([n-1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0])) =
    if k = 0 then 0
    else if k < n - 1 then n - 1 - k
    else n - 1
Proof
  rpt strip_tac >>
  simp[EL_REVERSE, LENGTH_GENLIST, LENGTH_APPEND, PRE_SUB1] >>
  ONCE_REWRITE_TAC[CONS_APPEND] >>
  REWRITE_TAC[APPEND_ASSOC] >>
  simp[el_desired_list]
QED

(* EL k (REVERSE desired) complements EL k desired:
   for the desired permutation, EL k desired + EL k (REVERSE desired) = dist *)
Theorem el_reverse_genlist_sum[local]:
  !(n:num) k.
    n >= 2 /\ k < n ==>
    EL k ([n-1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0]) +
    EL k (REVERSE ([n-1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0])) = n - 1
Proof
  rpt strip_tac >>
  simp[el_desired_list, el_reverse_desired_list]
QED

(* execute_plan initial_fmp length for MAP SOSpill *)
Theorem execute_plan_map_spill_length[local]:
  !offs. LENGTH (execute_plan initial_fmp (MAP SOSpill offs)) = 2 * LENGTH offs
Proof
  Induct >> simp[execute_plan_def, exec_stack_op_def] >>
  fs[execute_plan_def]
QED

(* execute_plan initial_fmp length for MAP SORestore *)
Theorem execute_plan_map_restore_length[local]:
  !offs. LENGTH (execute_plan initial_fmp (MAP SORestore offs)) = 2 * LENGTH offs
Proof
  Induct >> simp[execute_plan_def, exec_stack_op_def] >>
  fs[execute_plan_def]
QED

(* execute_plan initial_fmp length for spill ++ restore *)
Theorem execute_plan_spill_restore_length[local]:
  !spill_offs restore_offs.
    LENGTH (execute_plan initial_fmp (MAP SOSpill spill_offs ++ MAP SORestore restore_offs)) =
      2 * LENGTH spill_offs + 2 * LENGTH restore_offs
Proof
  simp[execute_plan_append, LENGTH_APPEND,
       execute_plan_map_spill_length, execute_plan_map_restore_length]
QED

(* Helper: all elements of desired are < LENGTH items *)
Theorem desired_el_bound[local]:
  !(n:num) k. n >= 2 /\ k < n ==>
    EL k ([n-1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0]) < n
Proof
  rpt strip_tac >> simp[el_desired_list]
QED

(* Helper: all elements of REVERSE desired are < LENGTH items *)
Theorem desired_rev_el_bound[local]:
  !(n:num) k. n >= 2 /\ k < n ==>
    EL k (REVERSE ([n-1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0])) < n
Proof
  rpt strip_tac >> simp[el_reverse_desired_list]
QED

(* EL at a desired-permuted index in items equals EL at the
   reverse-permuted index in REVERSE items. *)
Theorem el_desired_reverse_items[local]:
  !(items:'a list) k.
    LENGTH items >= 2 /\ k < LENGTH items ==>
    EL (EL k ([LENGTH items - 1] ++ GENLIST (\i. i + 1)
              (LENGTH items - 2) ++ [0])) items =
    EL (EL k (REVERSE ([LENGTH items - 1] ++ GENLIST (\i. i + 1)
              (LENGTH items - 2) ++ [0]))) (REVERSE items)
Proof
  rpt strip_tac >>
  simp[EL_REVERSE, el_desired_list, el_reverse_desired_list] >>
  rpt IF_CASES_TAC >> gvs[] >> simp[PRE_SUB1]
QED

(* The deep-swap index schedule is a rotation of every index exactly once. *)
Theorem desired_perm_indices[local]:
  !(n:num).
    n >= 2 ==>
    PERM ([n - 1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0])
         (GENLIST I n)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT
     ([n - 1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0])` by
    simp[ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST, MEM_GENLIST] >>
  `ALL_DISTINCT (GENLIST I n)` by
    simp[ALL_DISTINCT_GENLIST, combinTheory.I_THM] >>
  irule PERM_ALL_DISTINCT >> simp[] >> gen_tac >>
  `MEM x ([n - 1] ++ GENLIST (\i. i + 1) (n - 2) ++ [0]) <=>
   x IN count n` by
    metis_tac[set_desired_eq] >>
  gvs[MEM_GENLIST, IN_COUNT, combinTheory.I_THM]
QED


Theorem lupdate_take_drop[local]:
  !(xs:'a list) k v.
    k < LENGTH xs ==>
    LUPDATE v k xs = TAKE k xs ++ v :: DROP (SUC k) xs
Proof
  rw[LIST_EQ_REWRITE] >>
  simp[EL_LUPDATE, EL_APPEND_EQN, EL_TAKE, EL_DROP] >>
  rw[] >> gvs[EL_DROP] >>
  Cases_on `x - k` >> gvs[EL_DROP] >>
  `x = n + SUC k` by decide_tac >> simp[]
QED
(* Updating two in-range positions with each other's old values is a genuine
   permutation even when the list contains duplicates. *)

Theorem filter_eq_rotate[local]:
  !(xs:'a list) a.
    a :: FILTER ($= a) xs = FILTER ($= a) xs ++ [a]
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `a = h` >> gvs[]
QED

Theorem perm_replace_extract[local]:
  !(xs:'a list) k v.
    k < LENGTH xs ==>
    PERM (EL k xs :: LUPDATE v k xs) (v :: xs)
Proof
  rpt strip_tac >>
  qabbrev_tac `a = EL k xs` >>
  qabbrev_tac `pre = TAKE k xs` >>
  qabbrev_tac `suf = DROP (SUC k) xs` >>
  `LUPDATE v k xs = pre ++ v :: suf` by
    simp[Abbr `pre`, Abbr `suf`, lupdate_take_drop] >>
  `xs = pre ++ [a] ++ suf` by
    simp[Abbr `a`, Abbr `pre`, Abbr `suf`, TAKE_DROP_SUC] >>
  qpat_x_assum `LUPDATE v k xs = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `xs = _` (fn th => once_rewrite_tac[th]) >>
  simp[PERM_DEF, FILTER_APPEND_DISTRIB] >> gen_tac >>
  Cases_on `x = a` >> Cases_on `x = v` >>
  gvs[APPEND_ASSOC, filter_eq_rotate]
QED
Theorem lupdate_exchange_perm[local]:
  !(xs:'a list) i j.
    i < LENGTH xs /\ j < LENGTH xs ==>
    PERM (LUPDATE (EL i xs) j (LUPDATE (EL j xs) i xs)) xs
Proof
  rpt gen_tac >> strip_tac >>
  `EL j (LUPDATE (EL j xs) i xs) = EL j xs` by
    simp[EL_LUPDATE] >>
  `PERM
     (EL j xs :: LUPDATE (EL i xs) j (LUPDATE (EL j xs) i xs))
     (EL i xs :: LUPDATE (EL j xs) i xs)` by
    (qspecl_then [`LUPDATE (EL j xs) i xs`, `j`, `EL i xs`]
       mp_tac perm_replace_extract >> simp[]) >>
  `PERM (EL i xs :: LUPDATE (EL j xs) i xs) (EL j xs :: xs)` by
    simp[perm_replace_extract] >>
  metis_tac[PERM_TRANS, PERM_CONS_IFF]
QED

Theorem stack_poke_exchange_multiplicity:
  !(stk : operand list) d1 d2 x.
    d1 < LENGTH stk /\ d2 < LENGTH stk ==>
    LIST_ELEM_COUNT x
      (stack_poke d2 (stack_peek d1 stk)
        (stack_poke d1 (stack_peek d2 stk) stk)) =
    LIST_ELEM_COUNT x stk
Proof
  rpt strip_tac >>
  `PERM
     (stack_poke d2 (stack_peek d1 stk)
       (stack_poke d1 (stack_peek d2 stk) stk)) stk` by
    (simp[stack_poke_def, stack_peek_def] >>
     irule lupdate_exchange_perm >> simp[]) >>
  fs[PERM_DEF] >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[LIST_ELEM_COUNT_DEF, FILTER_EQ, EQ_SYM_EQ] >>
  strip_tac >>
  `((\y. x = y) : operand -> bool) = ($= x)` by
    simp[FUN_EQ_THM, EQ_SYM_EQ] >>
  gvs[]
QED

Theorem desired_values_perm[local]:
  !(items:'a list).
    LENGTH items >= 2 ==>
    PERM
      (MAP (\idx. EL idx items)
        ([LENGTH items - 1] ++
         GENLIST (\i. i + 1) (LENGTH items - 2) ++ [0]))
      items
Proof
  rpt strip_tac >>
  `PERM
     (MAP (\idx. EL idx items)
       ([LENGTH items - 1] ++
        GENLIST (\i. i + 1) (LENGTH items - 2) ++ [0]))
     (MAP (\idx. EL idx items) (GENLIST I (LENGTH items)))` by
    (irule PERM_MAP >> simp[desired_perm_indices]) >>
  gvs[MAP_GENLIST, combinTheory.I_THM, combinTheory.o_DEF, GENLIST_ID]
QED


Theorem do_swap_stack_perm:
  !dist ps.
    dist < LENGTH ps.ps_stack ==>
    PERM (SND (do_swap dist ps)).ps_stack ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist = 0` >- simp[do_swap_def] >>
  Cases_on `dist <= 16`
  >- (simp[do_swap_def, stack_swap_def] >>
      irule lupdate_exchange_perm >> simp[] >> decide_tac)
  >> `dist > 16 /\ dist + 1 <= LENGTH ps.ps_stack` by decide_tac >>
     mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
     simp[LET_THM] >> strip_tac >>
     `LENGTH (top_n (dist + 1) ps.ps_stack) = dist + 1` by
       simp[top_n_def, LENGTH_REVERSE, LENGTH_TAKE] >>
     `PERM
       (MAP (\idx. EL idx (top_n (dist + 1) ps.ps_stack))
         ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]))
       (top_n (dist + 1) ps.ps_stack)` by
       (qspec_then `top_n (dist + 1) ps.ps_stack` mp_tac
          desired_values_perm >> simp[]) >>
     `TAKE (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack ++
        top_n (dist + 1) ps.ps_stack = ps.ps_stack` by
       metis_tac[top_n_suffix] >>
     gvs[] >>
     qpat_assum `_ ++ top_n (dist + 1) ps.ps_stack = ps.ps_stack`
       (fn th => once_rewrite_tac[GSYM th]) >>
     irule PERM_CONG >> simp[]
QED

Theorem do_swap_multiplicity:
  !dist ps x.
    dist < LENGTH ps.ps_stack ==>
    LIST_ELEM_COUNT x (SND (do_swap dist ps)).ps_stack =
    LIST_ELEM_COUNT x ps.ps_stack
Proof
  rpt strip_tac >> drule do_swap_stack_perm >>
  simp[PERM_DEF] >> strip_tac >>
  first_x_assum (qspec_then `x` assume_tac) >>
  simp[LIST_ELEM_COUNT_DEF] >>
  qpat_x_assum `FILTER ($= x) _ = _` mp_tac >>
  simp[FILTER_EQ, EQ_SYM_EQ] >> strip_tac >>
  `(\x'. x = x') = ($= x)` by simp[FUN_EQ_THM, EQ_SYM_EQ] >>
  gvs[]
QED

Theorem do_swap_layout_wf:
  !dist ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dist < LENGTH ps.ps_stack ==>
    (SND (do_swap dist ps)).ps_spilled = ps.ps_spilled /\
    spill_alloc_layout_wf (SND (do_swap dist ps)).ps_alloc
                          (SND (do_swap dist ps)).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist = 0` >- simp[do_swap_def] >>
  Cases_on `dist <= 16` >- simp[do_swap_def] >>
  `dist > 16 /\ dist + 1 <= LENGTH ps.ps_stack` by decide_tac >>
  `spill_alloc_layout_wf
     (FOLDL (\a off. free_spill_slot off a)
       (SND (spill_alloc_n [] ps.ps_alloc
         (top_n (dist + 1) ps.ps_stack)))
       (FST (spill_alloc_n [] ps.ps_alloc
         (top_n (dist + 1) ps.ps_stack))))
     ps.ps_spilled` by
    (drule_then
       (qspec_then `top_n (dist + 1) ps.ps_stack` mp_tac)
       spill_alloc_n_free_layout_wf_arbitrary >>
     simp[LET_THM]) >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
  simp[LET_THM] >> strip_tac >> gvs[]
QED

Theorem do_swap_multiplicity_layout:
  !dist ps ops ps'.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    dist < LENGTH ps.ps_stack /\
    do_swap dist ps = (ops, ps') ==>
    ps'.ps_spilled = ps.ps_spilled /\
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
    (!x. LIST_ELEM_COUNT x ps'.ps_stack =
         LIST_ELEM_COUNT x ps.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  `ps' = SND (do_swap dist ps)` by
    (Cases_on `do_swap dist ps` >> gvs[]) >>
  qpat_x_assum `ps' = _` SUBST_ALL_TAC >>
  drule_all do_swap_layout_wf >> strip_tac >>
  simp[] >> gen_tac >> simp[do_swap_multiplicity]
QED

(* The k-th restored item's FLOOKUP in the spill map gives the k-th
   restore offset. *)
Theorem flookup_restore_offset[local]:
  !(items:operand list) offsets desired (sp:operand |-> num) (k:num).
    ALL_DISTINCT items /\
    LENGTH items = LENGTH offsets /\
    LENGTH items >= 2 /\
    desired = [LENGTH items - 1] ++ GENLIST (\i. i + 1) (LENGTH items - 2) ++ [0] /\
    k < LENGTH items ==>
    FLOOKUP (sp |++ ZIP (REVERSE items, offsets))
      (EL (EL k desired) items) =
    SOME (EL (EL k (REVERSE desired)) offsets)
Proof
  rpt gen_tac >> strip_tac >>
  (* Substitute desired = [...] *)
  qpat_x_assum `desired = _` (fn th => REWRITE_TAC[th]) >>
  (* Apply the EL equation to rewrite LHS *)
  qspecl_then [`items`, `k`] mp_tac el_desired_reverse_items >>
  ASM_REWRITE_TAC[] >>
  disch_then (fn eq_th => REWRITE_TAC[eq_th]) >>
  (* Now goal: FLOOKUP (sp |++ ZIP(REV items, offsets))
                (EL (EL k (REVERSE desired')) (REVERSE items))
              = SOME (EL (EL k (REVERSE desired')) offsets) *)
  irule flookup_fupdate_list_el >>
  ASM_REWRITE_TAC[ALL_DISTINCT_REVERSE, LENGTH_REVERSE] >>
  simp[desired_rev_el_bound]
QED


Theorem do_swap_big_stack_permutation[local]:
  !dist ps.
    dist > 16 /\ dist < LENGTH ps.ps_stack /\ ALL_DISTINCT ps.ps_stack ==>
    ALL_DISTINCT (SND (do_swap dist ps)).ps_stack /\
    set (SND (do_swap dist ps)).ps_stack = set ps.ps_stack
Proof
  rpt strip_tac >>
  qabbrev_tac `items = top_n (dist + 1) ps.ps_stack` >>
  qabbrev_tac `desired = [dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]` >>
  qabbrev_tac `base_stack = TAKE (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack` >>
  qabbrev_tac `restored = MAP (\idx. EL idx items) desired` >>
  `dist + 1 <= LENGTH ps.ps_stack` by decide_tac >>
  `LENGTH items = dist + 1` by
    simp[Abbr `items`, top_n_def, LENGTH_REVERSE, LENGTH_TAKE] >>
  `ALL_DISTINCT items` by
    simp[Abbr `items`, top_n_def, ALL_DISTINCT_REVERSE,
         ALL_DISTINCT_TAKE] >>
  `ALL_DISTINCT desired` by (
    simp[Abbr `desired`, ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST,
         MEM_GENLIST] >> decide_tac) >>
  `EVERY (\i. i < LENGTH items) desired` by
    simp[Abbr `desired`, EVERY_APPEND, EVERY_GENLIST] >>
  `ALL_DISTINCT restored` by (
    simp[Abbr `restored`] >> irule all_distinct_map_el >> simp[]) >>
  `set restored = set items` by (
    simp[Abbr `restored`, Abbr `desired`] >>
    qspecl_then [`dist + 1`, `items`] mp_tac set_desired_perm >>
    simp[]) >>
  `base_stack ++ items = ps.ps_stack` by
    simp[Abbr `base_stack`, Abbr `items`, top_n_suffix] >>
  `ALL_DISTINCT (base_stack ++ items)` by metis_tac[] >>
  `set (base_stack ++ items) = set ps.ps_stack` by metis_tac[] >>
  `ALL_DISTINCT (base_stack ++ restored) /\
   set (base_stack ++ restored) = set ps.ps_stack` by (
    fs[ALL_DISTINCT_APPEND] >>
    metis_tac[]) >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
  simp[LET_THM] >> strip_tac >>
  gvs[Abbr `base_stack`, Abbr `restored`, Abbr `items`, Abbr `desired`]
QED

Theorem do_swap_stack_permutation:
  !dist ps. dist < LENGTH ps.ps_stack /\ ALL_DISTINCT ps.ps_stack ==>
    ALL_DISTINCT (SND (do_swap dist ps)).ps_stack /\
    set (SND (do_swap dist ps)).ps_stack = set ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist = 0`
  >- ((conj_tac >- simp[do_swap_def]) >> simp[do_swap_def]) >>
  Cases_on `dist <= 16`
  >- (`ALL_DISTINCT (stack_swap dist ps.ps_stack) /\
       set (stack_swap dist ps.ps_stack) = set ps.ps_stack` by (
        irule stack_swap_permutation >> simp[]) >>
      (conj_tac >- gvs[do_swap_def]) >> gvs[do_swap_def]) >>
  irule do_swap_big_stack_permutation >> simp[] >> decide_tac
QED

Theorem do_swap_structural_layout_wf:
  !dist ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    dist < LENGTH ps.ps_stack ==>
    spill_alloc_layout_wf (SND (do_swap dist ps)).ps_alloc
                          (SND (do_swap dist ps)).ps_spilled /\
    ALL_DISTINCT (SND (do_swap dist ps)).ps_stack /\
    DISJOINT (set (SND (do_swap dist ps)).ps_stack)
             (FDOM (SND (do_swap dist ps)).ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (SND (do_swap dist ps)).ps_stack /\
   set (SND (do_swap dist ps)).ps_stack = set ps.ps_stack` by (
    irule do_swap_stack_permutation >> simp[]) >>
  `(SND (do_swap dist ps)).ps_spilled = ps.ps_spilled` by (
    Cases_on `dist = 0` >- simp[do_swap_def] >>
    Cases_on `dist <= 16` >- simp[do_swap_def] >>
    mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
    simp[LET_THM]) >>
  `spill_alloc_layout_wf (SND (do_swap dist ps)).ps_alloc
                         (SND (do_swap dist ps)).ps_spilled` by (
    Cases_on `dist = 0` >- gvs[do_swap_def] >>
    Cases_on `dist <= 16` >- gvs[do_swap_def] >>
    `dist > 16 /\ dist + 1 <= LENGTH ps.ps_stack` by decide_tac >>
    `ALL_DISTINCT (top_n (dist + 1) ps.ps_stack)` by
      simp[top_n_def, ALL_DISTINCT_REVERSE, ALL_DISTINCT_TAKE] >>
    `DISJOINT (set (top_n (dist + 1) ps.ps_stack))
              (FDOM ps.ps_spilled)` by (
      fs[DISJOINT_DEF, EXTENSION] >> gen_tac >>
      qpat_x_assum `!x. ~MEM x ps.ps_stack \/ _`
        (qspec_then `x` mp_tac) >>
      simp[top_n_def] >> metis_tac[MEM_TAKE, MEM_REVERSE]) >>
    `spill_alloc_layout_wf
       (FOLDL (\a off. free_spill_slot off a)
          (SND (spill_alloc_n [] ps.ps_alloc
             (top_n (dist + 1) ps.ps_stack)))
          (FST (spill_alloc_n [] ps.ps_alloc
             (top_n (dist + 1) ps.ps_stack))))
       ps.ps_spilled` by (
      mp_tac (Q.SPECL [`ps.ps_alloc`, `ps.ps_spilled`,
        `top_n (dist + 1) ps.ps_stack`] spill_alloc_n_free_layout_wf) >>
      simp[LET_THM]) >>
    mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
    simp[LET_THM] >> strip_tac >> gvs[]) >>
  rpt conj_tac >> simp[] >>
  fs[DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED


(* Helper: ps_spilled after applying a batch of generated spill operations. *)
Theorem apply_spill_ops_spilled[local]:
  !offsets lo ps.
    LENGTH offsets <= LENGTH ps.ps_stack ==>
    (apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps).ps_spilled =
    ps.ps_spilled |++
      ZIP (TAKE (LENGTH offsets) (REVERSE ps.ps_stack), offsets)
Proof
  Induct >>
  simp[apply_prefix_ops_def, FUPDATE_LIST_THM] >>
  rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC[apply_prefix_ops_def, apply_prefix_op_def,
                   stack_pop_def] >>
  qpat_x_assum `!lo ps. _` (qspecl_then [`lo`,
    `ps with <| ps_stack := TAKE (LENGTH ps.ps_stack - 1) ps.ps_stack;
                ps_spilled := ps.ps_spilled |+ (stack_peek 0 ps.ps_stack, h);
                ps_alloc := ps.ps_alloc with sa_next_offset :=
                  MAX ps.ps_alloc.sa_next_offset (h + 32) |>`] mp_tac) >>
  simp[LENGTH_TAKE_EQ] >> strip_tac >>
  `LENGTH ps.ps_stack - (LENGTH offsets + 1) <=
   LENGTH ps.ps_stack - 1` by decide_tac >>
  `ps.ps_stack <> []` by (Cases_on `ps.ps_stack` >> fs[]) >>
  `TAKE (SUC (LENGTH offsets)) (REVERSE ps.ps_stack) =
   LAST ps.ps_stack ::
   TAKE (LENGTH offsets) (REVERSE (FRONT ps.ps_stack))` by (
    match_mp_tac take_reverse_decompose >> simp[]) >>
  simp[ZIP_def, FUPDATE_LIST_THM] >>
  `stack_peek 0 ps.ps_stack = LAST ps.ps_stack` by
    simp[stack_peek_last] >>
  simp[] >>
  `FRONT ps.ps_stack = TAKE (LENGTH ps.ps_stack - 1) ps.ps_stack` by
    simp[FRONT_BY_TAKE] >>
  simp[]
QED

Theorem prefix_spill_wf_map_spill_bounds[local]:
  !offsets lo ps.
    prefix_spill_wf initial_fmp lo (MAP SOSpill offsets) ps ==>
    EVERY (\off. off < dimword(:256)) offsets
Proof
  Induct >> simp[prefix_spill_wf_def, spill_op_wf_def] >>
  rpt strip_tac >>
  qpat_x_assum `!lo ps. _`
    (qspecl_then [`lo`, `apply_prefix_op initial_fmp lo (SOSpill h) ps`] mp_tac) >>
  simp[]
QED


Theorem do_swap_deep_restore_prefix_spill_wf[local]:
  !dist ps lo.
    dist > 16 /\ dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    prefix_spill_wf initial_fmp lo
      (MAP SOSpill (FST (spill_alloc_n [] ps.ps_alloc
        (top_n (dist + 1) ps.ps_stack)))) ps ==>
    prefix_spill_wf initial_fmp lo
      (MAP SORestore
        (MAP (\idx. EL idx (FST (spill_alloc_n [] ps.ps_alloc
          (top_n (dist + 1) ps.ps_stack))))
          (REVERSE ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]))))
      (apply_prefix_ops initial_fmp lo
        (MAP SOSpill (FST (spill_alloc_n [] ps.ps_alloc
          (top_n (dist + 1) ps.ps_stack)))) ps)
Proof
  rpt strip_tac >>
  qabbrev_tac `items = top_n (dist + 1) ps.ps_stack` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc items)` >>
  qabbrev_tac `desired_rev =
    REVERSE ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0])` >>
  `LENGTH items = dist + 1` by
    simp[Abbr `items`, top_n_def, LENGTH_REVERSE, LENGTH_TAKE] >>
  `LENGTH offsets = LENGTH items` by
    simp[Abbr `offsets`, spill_alloc_n_offsets_length] >>
  `LENGTH desired_rev = LENGTH items` by
    simp[Abbr `desired_rev`, LENGTH_REVERSE, LENGTH_GENLIST] >>
  `ALL_DISTINCT items` by
    simp[Abbr `items`, top_n_def, ALL_DISTINCT_REVERSE, ALL_DISTINCT_TAKE] >>
  `DISJOINT (set items) (FDOM ps.ps_spilled)` by (
    fs[DISJOINT_DEF, EXTENSION] >> gen_tac >>
    qpat_x_assum `!x. ~MEM x ps.ps_stack \/ _` (qspec_then `x` mp_tac) >>
    simp[Abbr `items`, top_n_def] >> metis_tac[MEM_TAKE, MEM_REVERSE]) >>
  `EVERY (\off. off < dimword(:256)) offsets` by
    metis_tac[prefix_spill_wf_map_spill_bounds] >>
  `EVERY (\i. i < LENGTH items) desired_rev` by
    simp[Abbr `desired_rev`, EVERY_REVERSE, EVERY_APPEND, EVERY_GENLIST] >>
  `ALL_DISTINCT desired_rev` by (
    qspec_then `dist + 1` mp_tac desired_indices_all_distinct >>
    simp[Abbr `desired_rev`]) >>
  `spill_alloc_layout_wf
     (SND (spill_alloc_n [] ps.ps_alloc items))
     (ps.ps_spilled |++ ZIP(items, offsets))` by (
    qspecl_then [`items`, `[]`, `ps.ps_alloc`, `ps.ps_spilled`, `[]`]
      mp_tac spill_alloc_n_layout_wf >>
    simp[FUPDATE_LIST_THM, Abbr `offsets`]) >>
  `ALL_DISTINCT offsets` by (
    rewrite_tac[EL_ALL_DISTINCT_EL_EQ] >>
    rpt gen_tac >> strip_tac >> eq_tac
    >- (strip_tac >>
        Cases_on `n1 = n2` >- simp[] >>
        `FLOOKUP (ps.ps_spilled |++ ZIP(items, offsets)) (EL n1 items) =
           SOME (EL n1 offsets)` by
          metis_tac[flookup_fupdate_list_el] >>
        `FLOOKUP (ps.ps_spilled |++ ZIP(items, offsets)) (EL n2 items) =
           SOME (EL n2 offsets)` by
          metis_tac[flookup_fupdate_list_el] >>
        `EL n1 items <> EL n2 items` by metis_tac[ALL_DISTINCT_EL_IMP] >>
        fs[spill_alloc_layout_wf_def] >>
        qpat_x_assum `!op1 off1 op2 off2. _`
          (qspecl_then [`EL n1 items`, `EL n1 offsets`,
                        `EL n2 items`, `EL n2 offsets`] mp_tac) >>
        simp[] >> decide_tac) >>
    simp[]) >>
  `(apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps).ps_spilled =
     ps.ps_spilled |++ ZIP(REVERSE items, offsets)` by (
    qspecl_then [`offsets`, `lo`, `ps`] mp_tac apply_spill_ops_spilled >>
    `TAKE (LENGTH offsets) (REVERSE ps.ps_stack) = REVERSE items` by
      simp[Abbr `items`, top_n_def, REVERSE_REVERSE] >>
    simp[]) >>
  qabbrev_tac `restore_items =
    MAP (\idx. EL idx (REVERSE items)) desired_rev` >>
  qabbrev_tac `restore_offsets = MAP (\idx. EL idx offsets) desired_rev` >>
  qspecl_then [`restore_items`, `restore_offsets`, `lo`,
    `apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps`]
    mp_tac prefix_spill_wf_map_restore_lookup >>
  (impl_tac >- (
    conj_tac >- simp[Abbr `restore_items`, Abbr `restore_offsets`] >>
    conj_tac
    >- (simp[Abbr `restore_items`] >>
        irule all_distinct_map_el >>
        simp[ALL_DISTINCT_REVERSE] >> metis_tac[]) >>
    conj_tac
    >- (simp[Abbr `restore_offsets`] >>
        irule all_distinct_map_el >> simp[] >> metis_tac[]) >>
    rpt gen_tac >> strip_tac >>
    `k < LENGTH desired_rev` by fs[Abbr `restore_items`] >>
    simp[Abbr `restore_items`, Abbr `restore_offsets`, EL_MAP] >>
    conj_tac
    >- (ASM_REWRITE_TAC[] >>
        irule flookup_fupdate_list_el >>
        simp[ALL_DISTINCT_REVERSE] >>
        fs[EVERY_EL] >> metis_tac[]) >>
    fs[EVERY_EL] >> metis_tac[])) >>
  simp[Abbr `restore_offsets`]
QED

Theorem do_swap_prefix_spill_wf_from_front:
  !dist ps ops ps' lo.
    do_swap dist ps = (ops,ps') /\
    dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    prefix_spill_wf initial_fmp lo (FRONT ops) ps ==>
    prefix_spill_wf initial_fmp lo ops ps
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist = 0`
  >- gvs[do_swap_def, prefix_spill_wf_def] >>
  Cases_on `dist <= 16`
  >- gvs[do_swap_def, prefix_spill_wf_def, spill_op_wf_def] >>
  `dist > 16` by decide_tac >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
  simp[LET_THM] >> strip_tac >> gvs[] >>
  qpat_x_assum `prefix_spill_wf initial_fmp lo (FRONT _) ps` mp_tac >>
  simp[FRONT_APPEND_NOT_NIL, prefix_spill_wf_append] >> strip_tac >>
  mp_tac (Q.SPECL [`dist`, `ps`, `lo`]
    do_swap_deep_restore_prefix_spill_wf) >>
  simp[] >> strip_tac >>
  simp[prefix_spill_wf_append] >>
  qpat_x_assum
    `prefix_spill_wf initial_fmp lo
       (MAP SORestore _ ++ [SORestore _]) _` mp_tac >>
  simp[prefix_spill_wf_append, apply_prefix_ops_append] >>
  strip_tac >>
  `dist + 1 <= LENGTH ps.ps_stack` by decide_tac >>
  `LENGTH (FST (spill_alloc_n [] ps.ps_alloc
      (top_n (dist + 1) ps.ps_stack))) = dist + 1` by
    simp[spill_alloc_n_offsets_length, top_n_def, LENGTH_TAKE] >>
  `FST (spill_alloc_n [] ps.ps_alloc
      (top_n (dist + 1) ps.ps_stack)) <> []` by (
    Cases_on `FST (spill_alloc_n [] ps.ps_alloc
      (top_n (dist + 1) ps.ps_stack))` >> gvs[] >> decide_tac) >>
  gvs[REVERSE_APPEND, MAP_APPEND, apply_prefix_ops_append] >>
  PURE_ONCE_REWRITE_TAC[GSYM apply_prefix_ops_append] >>
  simp[] >> first_assum ACCEPT_TAC
QED

Theorem prefix_spill_wf_front_after_initial_prefix[local]:
  !xs ys source initial_fmp lo.
    ys <> [] /\
    prefix_spill_wf initial_fmp lo (FRONT (SOInitialFmp::(xs ++ ys))) source ==>
    prefix_spill_wf initial_fmp lo xs
      (apply_prefix_op initial_fmp lo SOInitialFmp source)
Proof
  rpt strip_tac >>
  `FRONT (xs ++ ys) = xs ++ FRONT ys` by
    metis_tac[FRONT_APPEND_NOT_NIL] >>
  `xs ++ ys <> []` by simp[] >>
  qpat_x_assum `prefix_spill_wf _ _ (FRONT _) _` mp_tac >>
  rewrite_tac[FRONT_DEF] >> ASM_REWRITE_TAC[] >>
  strip_tac >>
  qpat_x_assum `prefix_spill_wf _ _ (SOInitialFmp::_) _` mp_tac >>
  simp[Once prefix_spill_wf_def, prefix_spill_wf_append]
QED

Theorem do_swap_initial_fmp_front_transport:
  !dist source target ops target' initial_fmp lo.
    do_swap dist target = (ops,target') /\
    dist < LENGTH target.ps_stack /\
    spill_alloc_layout_wf target.ps_alloc target.ps_spilled /\
    ALL_DISTINCT target.ps_stack /\
    DISJOINT (set target.ps_stack) (FDOM target.ps_spilled) /\
    prefix_spill_wf initial_fmp lo (FRONT (SOInitialFmp::ops)) source ==>
    prefix_spill_wf initial_fmp lo ops target
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `dist = 0`
  >- gvs[do_swap_def, prefix_spill_wf_def] >>
  Cases_on `dist <= 16`
  >- gvs[do_swap_def, prefix_spill_wf_def, spill_op_wf_def] >>
  `dist > 16` by decide_tac >>
  mp_tac (Q.SPECL [`dist`, `target`] do_swap_big_decompose) >>
  simp[LET_THM] >> strip_tac >> gvs[] >>
  `prefix_spill_wf initial_fmp lo
     (MAP SOSpill (FST (spill_alloc_n [] target.ps_alloc
       (top_n (dist + 1) target.ps_stack))))
     (apply_prefix_op initial_fmp lo SOInitialFmp source)` by
    (irule prefix_spill_wf_front_after_initial_prefix >>
     qexists `
       [SORestore (HD (FST (spill_alloc_n [] target.ps_alloc
          (top_n (dist + 1) target.ps_stack))))] ++
       MAP SORestore
         (MAP (\idx. EL idx (FST (spill_alloc_n [] target.ps_alloc
            (top_n (dist + 1) target.ps_stack))))
           (REVERSE (GENLIST (\i. i + 1) (dist - 1)))) ++
       [SORestore (EL dist (FST (spill_alloc_n [] target.ps_alloc
          (top_n (dist + 1) target.ps_stack))))]` >>
     simp[APPEND_ASSOC]) >>
  qabbrev_tac `items = top_n (dist + 1) target.ps_stack` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] target.ps_alloc items)` >>
  `prefix_spill_wf initial_fmp lo (MAP SOSpill offsets)
     (apply_prefix_op initial_fmp lo SOInitialFmp source)` by
    metis_tac[] >>
  `EVERY (\off. off < dimword(:256)) offsets` by
    metis_tac[prefix_spill_wf_map_spill_bounds] >>
  `LENGTH items = dist + 1` by
    simp[Abbr `items`, top_n_def, LENGTH_REVERSE, LENGTH_TAKE] >>
  `LENGTH offsets = LENGTH items` by
    simp[Abbr `offsets`, spill_alloc_n_offsets_length] >>
  `ALL_DISTINCT (REVERSE items)` by
    simp[Abbr `items`, top_n_def, ALL_DISTINCT_REVERSE, ALL_DISTINCT_TAKE] >>
  `DISJOINT (set (REVERSE items)) (FDOM target.ps_spilled)` by
    (fs[DISJOINT_DEF, EXTENSION] >> gen_tac >>
     qpat_x_assum `!x. ~MEM x target.ps_stack \/ _` (qspec_then `x` mp_tac) >>
     simp[Abbr `items`, top_n_def] >> metis_tac[MEM_TAKE, MEM_REVERSE]) >>
  `REVERSE items = TAKE (LENGTH offsets) (REVERSE target.ps_stack)` by
    simp[Abbr `items`, top_n_def] >>
  `spill_alloc_layout_wf
     (SND (spill_alloc_n [] target.ps_alloc items))
     (target.ps_spilled |++ ZIP(REVERSE items,offsets))` by
    (qspecl_then [`items`, `REVERSE items`, `target.ps_alloc`,
       `target.ps_spilled`] mp_tac spill_alloc_n_layout_wf_keys >>
     simp[Abbr `offsets`]) >>
  `prefix_spill_wf initial_fmp lo (MAP SOSpill offsets) target` by
    (irule prefix_spill_wf_map_spill_from_layout >>
     conj_tac >- simp[] >>
     qexists `SND (spill_alloc_n [] target.ps_alloc items)` >>
     qexists `REVERSE items` >>
     simp[spill_alloc_n_spill_base]) >>
  `FST (spill_alloc_n [] target.ps_alloc
      (top_n (dist + 1) target.ps_stack)) <> []` by
    (Cases_on `FST (spill_alloc_n [] target.ps_alloc
       (top_n (dist + 1) target.ps_stack))` >> gvs[] >> decide_tac) >>
  mp_tac (Q.SPECL [`dist`, `target`, `lo`]
    do_swap_deep_restore_prefix_spill_wf) >>
  simp[Abbr `items`, Abbr `offsets`] >> strip_tac >>
  `([SORestore (HD (FST (spill_alloc_n [] target.ps_alloc
        (top_n (dist + 1) target.ps_stack))))] ++
      MAP SORestore
        (MAP (\idx. EL idx (FST (spill_alloc_n [] target.ps_alloc
          (top_n (dist + 1) target.ps_stack))))
          (REVERSE (GENLIST (\i. i + 1) (dist - 1)))) ++
      [SORestore (EL dist (FST (spill_alloc_n [] target.ps_alloc
        (top_n (dist + 1) target.ps_stack))))]) =
     MAP SORestore
       (MAP (\idx. EL idx (FST (spill_alloc_n [] target.ps_alloc
         (top_n (dist + 1) target.ps_stack))))
         (REVERSE ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0])))` by
    simp[REVERSE_APPEND, MAP_APPEND] >>
  `MAP SOSpill (FST (spill_alloc_n [] target.ps_alloc
       (top_n (dist + 1) target.ps_stack))) ++
     [SORestore (HD (FST (spill_alloc_n [] target.ps_alloc
       (top_n (dist + 1) target.ps_stack))))] ++
     MAP SORestore
       (MAP (\idx. EL idx (FST (spill_alloc_n [] target.ps_alloc
         (top_n (dist + 1) target.ps_stack))))
         (REVERSE (GENLIST (\i. i + 1) (dist - 1)))) ++
     [SORestore (EL dist (FST (spill_alloc_n [] target.ps_alloc
       (top_n (dist + 1) target.ps_stack))))] =
     MAP SOSpill (FST (spill_alloc_n [] target.ps_alloc
       (top_n (dist + 1) target.ps_stack))) ++
     MAP SORestore
       (MAP (\idx. EL idx (FST (spill_alloc_n [] target.ps_alloc
         (top_n (dist + 1) target.ps_stack))))
         (REVERSE ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0])))` by
    metis_tac[APPEND_ASSOC] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  simp[prefix_spill_wf_append]
QED


(* ---------------------------------------------------------------
   do_swap_venom_asm_rel_big: dist > 16 case
   --------------------------------------------------------------- *)

Theorem do_swap_venom_asm_rel_big[local]:
  !dist ps ops ps' lo o2pc prog vs st.
    do_swap dist ps = (ops, ps') /\
    dist > 16 /\
    dist < LENGTH ps.ps_stack /\
    spill_alloc_wf ps.ps_alloc ps.ps_spilled /\
    ps.ps_alloc.sa_next_offset + 32 * (dist + 1) < dimword(:256) /\
    ps.ps_alloc.sa_free_slots = [] /\
    ALL_DISTINCT (top_n (dist + 1) ps.ps_stack) /\
    DISJOINT (set (top_n (dist + 1) ps.ps_stack)) (FDOM ps.ps_spilled) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt strip_tac >>
  (* Abbreviations *)
  qabbrev_tac `items = top_n (dist + 1) ps.ps_stack` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc items)` >>
  qabbrev_tac `desired = [dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]` >>
  qabbrev_tac `desired_rev = REVERSE desired` >>
  qabbrev_tac `restore_offsets = MAP (\idx. EL idx offsets) desired_rev` >>
  qabbrev_tac `restored = MAP (\idx. EL idx items) desired` >>
  (* Key length fact *)
  `LENGTH items = dist + 1`
    suffices_by (strip_tac >> suspend "main") >>
  simp[Abbr `items`, top_n_def, LENGTH_REVERSE, LENGTH_TAKE]
QED

Resume do_swap_venom_asm_rel_big[main]:
  (* Get decomposition from do_swap_big_decompose *)
  mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
  simp[LET_THM] >>
  `top_n (dist + 1) ps.ps_stack = items` suffices_by (
    strip_tac >> simp[] >> strip_tac >>
    (* Now: ops = MAP SOSpill offsets ++ MAP SORestore restore_offsets
       and ps' has the decomposed form *)
    suspend "spill_phase"
  ) >>
  simp[Abbr `items`]
QED

Resume do_swap_venom_asm_rel_big[spill_phase]:
  (* Apply spill_n_sim with pairs = ZIP(REVERSE items, offsets) *)
  qspecl_then [`ZIP(REVERSE items, offsets)`, `lo`, `o2pc`, `prog`,
    `ps`, `vs`, `st`] mp_tac spill_n_sim >>
  (impl_tac >- (
    suspend "spill_precond"
  )) >>
  strip_tac >>
  suspend "restore_phase"
QED

Resume do_swap_venom_asm_rel_big[spill_precond]:
  (* Preconditions for spill_n_sim *)
  `LENGTH offsets = dist + 1`
    suffices_by (strip_tac >> suspend "spill_precond2") >>
  simp[Abbr `offsets`, spill_alloc_n_offsets_length]
QED

Resume do_swap_venom_asm_rel_big[spill_precond2]:
  simp[] >>
  rpt conj_tac
  >| [
    (* 1. MAP FST pairs = TAKE (dist+1) (REVERSE ps.ps_stack) *)
    simp[MAP_ZIP, LENGTH_REVERSE, Abbr `items`, top_n_def, REVERSE_REVERSE],
    (* 2. ALL_DISTINCT (MAP FST pairs) *)
    simp[MAP_ZIP, LENGTH_REVERSE, ALL_DISTINCT_REVERSE],
    (* 3. offset properties *)
    suspend "offset_props",
    (* 4. asm_block_at for spill phase *)
    qpat_x_assum `asm_block_at prog st.as_pc (execute_plan initial_fmp _)` mp_tac >>
    simp[execute_plan_append, asm_block_at_append] >>
    simp[MAP_ZIP, LENGTH_REVERSE]
  ]
QED

Resume do_swap_venom_asm_rel_big[offset_props]:
  rpt gen_tac >> strip_tac >>
  simp[EL_ZIP, LENGTH_REVERSE, Abbr `offsets`] >>
  qspecl_then [`items`, `ps.ps_alloc`, `ps.ps_spilled`]
    mp_tac spill_alloc_n_offset_props >>
  gvs[LET_THM, spill_alloc_n_offsets_length] >>
  disch_then (qspec_then `k` mp_tac) >>
  simp[] >> metis_tac[]
QED

Resume do_swap_venom_asm_rel_big[restore_phase]:
  (* Intermediate plan state after spill *)
  qabbrev_tac `ps_mid =
    ps with <| ps_stack :=
      TAKE (LENGTH ps.ps_stack - LENGTH (ZIP (REVERSE items,offsets)))
           ps.ps_stack;
      ps_spilled := ps.ps_spilled |++ ZIP (REVERSE items,offsets);
      ps_alloc := ps.ps_alloc with sa_next_offset :=
        FOLDL MAX ps.ps_alloc.sa_next_offset
              (MAP (\p. SND p + 32) (ZIP (REVERSE items,offsets))) |>` >>
  (* Apply restore_n_sim *)
  qspecl_then [`restored`, `restore_offsets`, `lo`, `o2pc`, `prog`,
    `ps_mid`, `vs`, `st'`] mp_tac restore_n_sim >>
  (impl_tac >- (
    suspend "restore_precond"
  )) >>
  strip_tac >>
  suspend "compose"
QED

Resume do_swap_venom_asm_rel_big[restore_precond]:
  simp[Abbr `ps_mid`] >>
  `LENGTH desired = dist + 1`
    suffices_by (strip_tac >> suspend "restore_precond2") >>
  simp[Abbr `desired`, LENGTH_GENLIST]
QED

Resume do_swap_venom_asm_rel_big[restore_precond2]:
  `LENGTH desired_rev = dist + 1`
    suffices_by (strip_tac >> suspend "restore_precond3") >>
  simp[Abbr `desired_rev`, LENGTH_REVERSE]
QED

Resume do_swap_venom_asm_rel_big[restore_precond3]:
  (* 4 conjuncts: LENGTH, ALL_DISTINCT, FLOOKUP/bound, asm_block_at *)
  conj_tac >- (simp[Abbr `restored`, Abbr `restore_offsets`]) >>
  conj_tac >- (suspend "all_distinct") >>
  conj_tac >- (suspend "flookup_bound") >>
  suspend "asm_block_at_restore"
QED

Resume do_swap_venom_asm_rel_big[all_distinct]:
  simp[Abbr `restored`] >>
  irule all_distinct_map_el >>
  simp[Abbr `desired`, EVERY_GENLIST, EVERY_APPEND,
       ALL_DISTINCT_GENLIST, ALL_DISTINCT_REVERSE, ALL_DISTINCT_APPEND,
       MEM_GENLIST]
QED

(* All spill offsets are < dimword(:256) — EVERY form *)
Theorem spill_offsets_every_bound[local]:
  !items al sp.
    spill_alloc_wf al sp /\
    al.sa_next_offset + 32 * LENGTH items < dimword(:256) /\
    al.sa_free_slots = [] /\
    ALL_DISTINCT items /\
    DISJOINT (set items) (FDOM sp) ==>
    EVERY (\off. off < dimword(:256)) (FST (spill_alloc_n [] al items))
Proof
  rpt strip_tac >> simp[EVERY_EL] >> rpt strip_tac >>
  qspecl_then [`items`, `al`, `sp`] mp_tac spill_alloc_n_offset_props >>
  simp[LET_THM, spill_alloc_n_offsets_length] >>
  disch_then (qspec_then `n` mp_tac) >>
  fs[spill_alloc_n_offsets_length]
QED

(* Every element of a permuted sublist is bounded if every element of
   the original is bounded *)
Theorem every_el_map_index_bound[local]:
  !offsets perm k (bound:num).
    EVERY (\idx. idx < LENGTH offsets) perm /\
    EVERY (\off. off < bound) offsets /\
    k < LENGTH perm ==>
    EL k (MAP (\idx. EL idx offsets) perm) < bound
Proof
  rpt strip_tac >> simp[EL_MAP] >> fs[EVERY_EL]
QED

Resume do_swap_venom_asm_rel_big[flookup_bound]:
  rpt gen_tac >> strip_tac >>
  (conj_tac >- (suspend "flookup_eq")) >>
  simp[Abbr `restore_offsets`, Abbr `desired_rev`] >>
  match_mp_tac every_el_map_index_bound >>
  simp[Abbr `offsets`, Abbr `restored`, LENGTH_REVERSE] >>
  (conj_tac >- (
    simp[EVERY_EL, Abbr `desired`, el_desired_list,
         spill_alloc_n_offsets_length] >>
    rpt strip_tac >> rpt IF_CASES_TAC >> simp[]
  )) >>
  (conj_tac >- (
    match_mp_tac (SIMP_RULE (srw_ss()) [] spill_offsets_every_bound) >>
    qexists_tac `ps.ps_spilled` >> gvs[]
  )) >>
  fs[LENGTH_MAP, LENGTH_REVERSE, spill_alloc_n_offsets_length]
QED

Resume do_swap_venom_asm_rel_big[flookup_eq]:
  fs[Abbr `restored`, Abbr `restore_offsets`,
     Abbr `desired_rev`, LENGTH_REVERSE, LENGTH_MAP, EL_MAP] >>
  irule flookup_restore_offset >>
  simp[Abbr `desired`, Abbr `offsets`, spill_alloc_n_offsets_length]
QED

Resume do_swap_venom_asm_rel_big[asm_block_at_restore]:
  qpat_x_assum `asm_block_at prog _ (execute_plan initial_fmp _)` mp_tac >>
  simp[execute_plan_append, asm_block_at_append,
       execute_plan_map_spill_length, MAP_ZIP, LENGTH_REVERSE,
       Abbr `offsets`, spill_alloc_n_offsets_length]
QED

Resume do_swap_venom_asm_rel_big[compose]:
  (* Chain spill steps + restore steps via asm_steps_compose_ok *)
  qexists_tac `st''` >>
  (* Split into 3: asm_steps, venom_asm_rel, as_pc *)
  (conj_tac >- (suspend "compose_steps")) >>
  (conj_tac >- (suspend "compose_rel")) >>
  suspend "compose_pc"
QED

Resume do_swap_venom_asm_rel_big[compose_steps]:
  (* Rewrite LENGTH(execute_plan initial_fmp ops) to match assumption step counts *)
  qpat_x_assum `asm_steps _ _ _ (2 * LENGTH (ZIP _)) st = _`
    (fn th1 =>
     qpat_x_assum `asm_steps _ _ _ (2 * LENGTH restored) st' = _`
       (fn th2 =>
        mp_tac (MATCH_MP (GEN_ALL asm_steps_compose_ok)
                         (CONJ th1 th2)))) >>
  simp[execute_plan_spill_restore_length, MAP_ZIP, LENGTH_REVERSE,
       Abbr `restore_offsets`, LENGTH_MAP, Abbr `desired_rev`,
       LENGTH_REVERSE, LENGTH_ZIP, Abbr `restored`, Abbr `offsets`,
       spill_alloc_n_offsets_length, arithmeticTheory.MIN_DEF]
QED

Resume do_swap_venom_asm_rel_big[compose_rel]:
  irule venom_asm_rel_ps_transfer >>
  qexists_tac
    `ps_mid with <| ps_stack := ps_mid.ps_stack ++ restored;
      ps_spilled :=
        FOLDL (\sp item. sp \\ item) ps_mid.ps_spilled restored |>` >>
  simp[Abbr `ps_mid`] >>
  (* After simp[Abbr ps_mid], conjuncts are:
     1. ps_spilled, 2. ps_stack, 3. next_offset, 4. spill_base *)
  (* 1. ps_spilled: round-trip cancellation *)
  (conj_tac >- (suspend "compose_spilled")) >>
  (* 2. ps_stack *)
  (conj_tac >- (suspend "compose_stack")) >>
  (* 3. sa_next_offset *)
  (conj_tac >- (suspend "compose_next_offset")) >>
  (* 4. sa_spill_base *)
  simp[foldl_free_spill_base, spill_alloc_n_spill_base]
QED

Resume do_swap_venom_asm_rel_big[compose_stack]:
  simp[Abbr `restored`, Abbr `desired`, Abbr `offsets`,
       spill_alloc_n_offsets_length, arithmeticTheory.MIN_DEF,
       MAP_APPEND, MAP_MAP_o, combinTheory.o_DEF]
QED

Resume do_swap_venom_asm_rel_big[compose_spilled]:
  match_mp_tac (GSYM foldl_domsub_cancel) >>
  (* Goal: set restored = set (MAP FST (ZIP(REVERSE items, offsets))) /\
           DISJOINT (set restored) (FDOM ps.ps_spilled) *)
  (conj_tac >- (suspend "compose_set_eq")) >>
  suspend "compose_disjoint"
QED

(*
  set_desired_perm specialized to dist+1.
  _dist: set items = set (MAP ...) — for rewriting assumptions/goals containing set items
  _dist_fwd: set (MAP ...) = set items — for rewriting goals containing set (MAP ...)
  Precondition: LENGTH items = dist + 1 /\ dist >= 1
*)
val set_desired_perm_dist = GSYM set_desired_perm
  |> Q.SPECL [`dist + 1`, `items`]
  |> REWRITE_RULE[DECIDE ``((d:num) + 1 >= 2) = (d >= 1)``,
                  DECIDE ``(d:num) + 1 - 1 = d``,
                  DECIDE ``(d:num) + 1 - 2 = d - 1``]
  |> CONV_RULE (LAND_CONV (LAND_CONV (REWR_CONV EQ_SYM_EQ)));
val set_desired_perm_dist_fwd = set_desired_perm
  |> Q.SPECL [`dist + 1`, `items`]
  |> REWRITE_RULE[DECIDE ``((d:num) + 1 >= 2) = (d >= 1)``,
                  DECIDE ``(d:num) + 1 - 1 = d``,
                  DECIDE ``(d:num) + 1 - 2 = d - 1``,
                  DECIDE ``((d:num) + 1 = n) = (n = d + 1)``];

Resume do_swap_venom_asm_rel_big[compose_set_eq]:
  simp[MAP_ZIP, LENGTH_REVERSE, Abbr `offsets`,
       spill_alloc_n_offsets_length, Abbr `restored`] >>
  simp[LIST_TO_SET_REVERSE] >>
  qpat_x_assum `Abbrev (desired = _)`
    (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  simp[Once set_desired_perm_dist]
QED

Resume do_swap_venom_asm_rel_big[compose_disjoint]:
  qpat_x_assum `Abbrev (restored = _)`
    (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_x_assum `Abbrev (desired = _)`
    (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_x_assum `DISJOINT (set items) _` mp_tac >>
  qpat_x_assum `dist > 16` (fn gt16 =>
    qpat_x_assum `LENGTH items = _` (fn len_eq =>
      REWRITE_TAC[MATCH_MP set_desired_perm_dist_fwd
        (CONJ len_eq (MATCH_MP (DECIDE ``(d:num) > 16 ==> d >= 1``) gt16))]
    ))
QED

Theorem map_snd_plus_zip[local]:
  !l1 (l2:num list).
    LENGTH l1 = LENGTH l2 ==>
    MAP (\p. SND p + 32) (ZIP (l1,l2)) = MAP (\x. x + 32) l2
Proof
  Induct >> simp[] >> Cases_on `l2` >> simp[]
QED

(*
  Direct: FOLDL MAX base (MAP SND+32 (ZIP(REVERSE items, spill offsets))) = base + 32*n.
  Uses spill_alloc_n_offsets_val to rewrite offsets, then MAP_GENLIST + foldl_max_genlist.
*)
Theorem spill_foldl_max_eq[local]:
  !items (al:spill_alloc).
    al.sa_free_slots = [] ==>
    FOLDL MAX al.sa_next_offset
      (MAP (\p. SND p + 32)
        (ZIP (REVERSE items, FST (spill_alloc_n [] al items)))) =
    al.sa_next_offset + 32 * LENGTH items
Proof
  rpt strip_tac >>
  simp[spill_alloc_n_offsets_val, map_snd_plus_zip,
       LENGTH_REVERSE, LENGTH_GENLIST] >>
  simp[MAP_GENLIST, combinTheory.o_DEF] >>
  SUBGOAL_THEN ``GENLIST (\i. 32 * i + (al.sa_next_offset + 32))
                   (LENGTH (items:'a list)) =
                 GENLIST (\i. al.sa_next_offset + 32 * (i + 1))
                   (LENGTH items)``
    (fn th => REWRITE_TAC[th]) THENL [
    simp[LIST_EQ_REWRITE, EL_GENLIST], ALL_TAC] >>
  simp[foldl_max_genlist]
QED

Resume do_swap_venom_asm_rel_big[compose_next_offset]:
  simp[foldl_free_next_offset, Abbr `offsets`] >>
  qpat_x_assum `ps.ps_alloc.sa_free_slots = []`
    (fn th =>
      REWRITE_TAC[MATCH_MP spill_alloc_n_next_offset_no_free th,
                  MATCH_MP spill_foldl_max_eq th]) >>
  simp[]
QED

Resume do_swap_venom_asm_rel_big[compose_pc]:
  simp[execute_plan_spill_restore_length, LENGTH_MAP, LENGTH_ZIP,
       LENGTH_REVERSE, spill_alloc_n_offsets_length] >>
  simp[Abbr `restored`, Abbr `restore_offsets`, Abbr `desired_rev`,
       Abbr `desired`, Abbr `offsets`, LENGTH_MAP, LENGTH_REVERSE,
       LENGTH_GENLIST, spill_alloc_n_offsets_length] >>
  decide_tac
QED

Finalise do_swap_venom_asm_rel_big;

(* Combined do_swap simulation for all distances *)
Theorem do_swap_venom_asm_rel:
  !dist ps ops ps' lo o2pc prog vs st.
    do_swap dist ps = (ops, ps') /\
    dist < LENGTH ps.ps_stack /\
    (dist > 16 ==>
       spill_alloc_wf ps.ps_alloc ps.ps_spilled /\
       ps.ps_alloc.sa_next_offset + 32 * (dist + 1) < dimword(:256) /\
       ps.ps_alloc.sa_free_slots = [] /\
       ALL_DISTINCT (top_n (dist + 1) ps.ps_stack) /\
       DISJOINT (set (top_n (dist + 1) ps.ps_stack))
                (FDOM ps.ps_spilled)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt strip_tac >>
  Cases_on `dist <= 16`
  >- (irule do_swap_venom_asm_rel_small >> metis_tac[])
  >>
  `dist > 16` by decide_tac >>
  irule do_swap_venom_asm_rel_big >>
  metis_tac[]
QED

(* ---------------------------------------------------------------
   do_swap_apply_stack_align_layout: apply_prefix_ops of do_swap ops
   gives the same ps_stack as the direct do_swap computation.
   --------------------------------------------------------------- *)


(* Helper: ps_stack after applying restore ops.
   Requires a global separation condition: ALL pairs in ps_spilled
   have separated offsets. This is stronger than pairwise on items only
   but is needed because spill_hilbert_unique quantifies over all entries. *)
Theorem apply_restore_ops_stack[local]:
  !items offsets lo ps.
    LENGTH items = LENGTH offsets /\
    ALL_DISTINCT items /\
    (!k. k < LENGTH items ==>
      FLOOKUP ps.ps_spilled (EL k items) = SOME (EL k offsets)) /\
    (!op1 off1 op2 off2.
       FLOOKUP ps.ps_spilled op1 = SOME off1 /\
       FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1) ==>
    (apply_prefix_ops initial_fmp lo (MAP SORestore offsets) ps).ps_stack =
    ps.ps_stack ++ items
Proof
  Induct
  >- simp[apply_prefix_ops_def] >>
  rpt gen_tac >>
  Cases_on `offsets`
  >- simp[] >>
  strip_tac >>
  simp[apply_prefix_ops_def, apply_prefix_op_def, LET_THM] >>
  (* spill_lookup: the first offset h' uniquely maps to h *)
  `FLOOKUP ps.ps_spilled h = SOME h'` by (
    first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `spill_lookup h' ps.ps_spilled = h` by (
    simp[spill_lookup_def] >>
    irule spill_hilbert_unique >> simp[] >>
    metis_tac[]) >>
  simp[stack_push_def] >>
  (* IH: apply to the state after this restore *)
  qabbrev_tac `ps2 = ps with <| ps_stack := SNOC h ps.ps_stack;
                                  ps_spilled := ps.ps_spilled \\ h |>` >>
  qpat_x_assum `!offsets lo ps. _` (qspecl_then [`t`, `lo`, `ps2`] mp_tac) >>
  simp[Abbr `ps2`] >>
  suspend "ih_preconds"
QED

Resume apply_restore_ops_stack[ih_preconds]:
  impl_tac
  >- (
    gvs[ALL_DISTINCT] >>
    conj_tac
    >- (
      rpt strip_tac >>
      simp[DOMSUB_FLOOKUP_THM] >>
      reverse conj_tac
      >- (first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]) >>
      metis_tac[MEM_EL]) >>
    rpt strip_tac >>
    gvs[DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
  rewrite_tac[SNOC_APPEND, GSYM APPEND_ASSOC]
QED

Finalise apply_restore_ops_stack

(* The matching restore sequence removes exactly the named temporary spills. *)
Theorem apply_restore_ops_spilled[local]:
  !items offsets lo ps.
    LENGTH items = LENGTH offsets /\ ALL_DISTINCT items /\
    (!k. k < LENGTH items ==>
       FLOOKUP ps.ps_spilled (EL k items) = SOME (EL k offsets)) /\
    (!op1 off1 op2 off2.
       FLOOKUP ps.ps_spilled op1 = SOME off1 /\
       FLOOKUP ps.ps_spilled op2 = SOME off2 /\ op1 <> op2 ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1) ==>
    (apply_prefix_ops initial_fmp lo (MAP SORestore offsets) ps).ps_spilled =
      FOLDL (\sp item. sp \\ item) ps.ps_spilled items
Proof
  Induct
  >- (Cases_on `offsets` >> simp[apply_prefix_ops_def]) >>
  rpt gen_tac >> Cases_on `offsets` >- simp[] >> strip_tac >>
  `FLOOKUP ps.ps_spilled h = SOME h'` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `spill_lookup h' ps.ps_spilled = h` by
    (simp[spill_lookup_def] >> irule spill_hilbert_unique >> simp[] >>
     metis_tac[]) >>
  simp[apply_prefix_ops_def, apply_prefix_op_def, LET_THM] >>
  qabbrev_tac `ps2 = ps with <| ps_stack := SNOC h ps.ps_stack;
                                  ps_spilled := ps.ps_spilled \\ h |>` >>
  first_x_assum (qspecl_then [`t`, `lo`, `ps2`] mp_tac) >>
  simp[Abbr `ps2`] >>
  impl_tac
  >- (gvs[ALL_DISTINCT] >>
      conj_tac
      >- (rpt strip_tac >> simp[DOMSUB_FLOOKUP_THM] >>
          reverse conj_tac
          >- (first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]) >>
          metis_tac[MEM_EL]) >>
      rpt strip_tac >> gvs[DOMSUB_FLOOKUP_THM] >> metis_tac[]) >>
  simp[stack_push_def]
QED


(* Main alignment theorem *)
Theorem do_swap_apply_stack_align_layout:
  !dist ps lo.
    dist < LENGTH ps.ps_stack /\
    (dist > 16 ==>
       ALL_DISTINCT (top_n (dist + 1) ps.ps_stack) /\
       DISJOINT (set (top_n (dist + 1) ps.ps_stack))
                (FDOM ps.ps_spilled) /\
       spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled) ==>
    (apply_prefix_ops initial_fmp lo (FST (do_swap dist ps)) ps).ps_stack =
    (SND (do_swap dist ps)).ps_stack
Proof
  rpt strip_tac >>
  Cases_on `dist = 0`
  >- simp[do_swap_def, apply_prefix_ops_def] >>
  Cases_on `dist <= 16`
  >- (
    `?ops ps'. do_swap dist ps = (ops, ps')` by metis_tac[pairTheory.PAIR] >>
    drule_all do_swap_align >> simp[]) >>
  (* dist > 16 *)
  `dist > 16` by decide_tac >> fs[] >>
  qabbrev_tac `chunk = dist + 1` >>
  qabbrev_tac `items = top_n chunk ps.ps_stack` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc items)` >>
  qabbrev_tac `desired = [dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]` >>
  qabbrev_tac `desired_rev = REVERSE desired` >>
  qabbrev_tac `restore_offsets = MAP (\idx. EL idx offsets) desired_rev` >>
  qabbrev_tac `base_stack = TAKE (LENGTH ps.ps_stack - chunk) ps.ps_stack` >>
  qabbrev_tac `restored = MAP (\idx. EL idx items) desired` >>
  `LENGTH items = chunk` by (
    simp[Abbr `items`, top_n_def, LENGTH_REVERSE] >>
    irule LENGTH_TAKE >> simp[Abbr `chunk`]) >>
  `LENGTH offsets = chunk` by
    simp[Abbr `offsets`, spill_alloc_n_offsets_length] >>
  `LENGTH desired = chunk` by
    simp[Abbr `desired`, Abbr `chunk`, LENGTH_GENLIST] >>
  `chunk >= 2` by (simp[Abbr `chunk`] >> decide_tac) >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
  simp[LET_THM] >>
  `top_n chunk ps.ps_stack = items` by simp[Abbr `items`] >>
  simp[] >> strip_tac >>
  simp[apply_prefix_ops_append] >>
  (* After spill phase: stack = base_stack *)
  `(apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps).ps_stack = base_stack` by (
    qspecl_then [`offsets`, `lo`, `ps`] mp_tac apply_spill_ops_stack >>
    simp[Abbr `base_stack`, Abbr `chunk`]) >>
  (* After spill phase: spilled *)
  `(apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps).ps_spilled =
   ps.ps_spilled |++ ZIP(REVERSE items, offsets)` by (
    qspecl_then [`offsets`, `lo`, `ps`] mp_tac apply_spill_ops_spilled >>
    simp[Abbr `chunk`] >>
    `TAKE (dist + 1) (REVERSE ps.ps_stack) = REVERSE items` by
      simp[Abbr `items`, top_n_def, REVERSE_REVERSE] >>
    simp[]) >>
  suspend "restore"
QED

Resume do_swap_apply_stack_align_layout[restore]:
  (* The items pushed by restore = MAP (λidx. EL idx (REVERSE items)) desired_rev *)
  (* which equals restored = MAP (λidx. EL idx items) desired by el_desired_reverse_items *)
  (* Use apply_restore_ops_stack with:
     items_arg = MAP (λidx. EL idx (REVERSE items)) desired_rev
     offsets_arg = restore_offsets = MAP (λidx. EL idx offsets) desired_rev *)
  qabbrev_tac `rev_items = REVERSE items` >>
  qabbrev_tac `items_pushed = MAP (\idx. EL idx rev_items) desired_rev` >>
  `LENGTH desired_rev = chunk` by
    simp[Abbr `desired_rev`, LENGTH_REVERSE] >>
  `LENGTH restore_offsets = chunk` by
    simp[Abbr `restore_offsets`] >>
  `LENGTH items_pushed = chunk` by
    simp[Abbr `items_pushed`] >>
  `LENGTH rev_items = chunk` by
    simp[Abbr `rev_items`, LENGTH_REVERSE] >>
  (* Apply apply_restore_ops_stack *)
  qspecl_then [`items_pushed`, `restore_offsets`, `lo`,
    `apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps`]
    mp_tac apply_restore_ops_stack >>
  (* Discharge LENGTH and rewrite spilled/stack, but keep items_pushed *)
  simp[] >>
  (impl_tac >- (
    rpt conj_tac
    >- suspend "all_distinct"
    >- suspend "flookup"
    >> suspend "separation")) >>
  disch_then SUBST1_TAC >>
  (* Goal: base_stack ⧺ items_pushed = base_stack ⧺ ... *)
  suspend "items_eq"
QED

(*  Separation is preserved after spill phase update.
    Case-split on old vs new for each operand. *)
Theorem spilled_after_spill_separated[local]:
  !items offsets sp al.
    spill_alloc_wf al sp /\
    ALL_DISTINCT items /\
    DISJOINT (set items) (FDOM sp) /\
    LENGTH offsets = LENGTH items /\
    offsets = FST (spill_alloc_n [] al items) /\
    al.sa_next_offset + 32 * LENGTH items < dimword(:256) ==>
    (!op1 off1 op2 off2.
       FLOOKUP (sp |++ ZIP(REVERSE items, offsets)) op1 = SOME off1 /\
       FLOOKUP (sp |++ ZIP(REVERSE items, offsets)) op2 = SOME off2 /\
       op1 <> op2 ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1)
Proof
  rpt strip_tac >>
  qpat_x_assum `FLOOKUP _ op1 = _` mp_tac >>
  qpat_x_assum `FLOOKUP _ op2 = _` mp_tac >>
  simp[flookup_fupdate_list] >>
  Cases_on `ALOOKUP (REVERSE (ZIP (REVERSE items,offsets))) op1` >>
  Cases_on `ALOOKUP (REVERSE (ZIP (REVERSE items,offsets))) op2` >>
  simp[] >> rpt strip_tac
  >- suspend "both_old"
  >- suspend "old_new"
  >- suspend "new_old"
  >> suspend "both_new"
QED

Resume spilled_after_spill_separated[both_old]:
  gvs[spill_alloc_wf_def] >> metis_tac[]
QED

(* old_new: op1 from sp, op2 from new allocation *)
Resume spilled_after_spill_separated[old_new]:
  gvs[] >> imp_res_tac ALOOKUP_MEM >>
  qpat_x_assum `MEM (op2,_) (REVERSE _)` mp_tac >>
  simp[MEM_REVERSE, MEM_ZIP, LENGTH_REVERSE] >> strip_tac >> gvs[] >>
  qspecl_then [`items`, `al`, `sp`] mp_tac spill_alloc_n_offset_props >>
  simp[LET_THM] >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule >> metis_tac[]
QED

(* new_old: op1 from new allocation, op2 from sp *)
Resume spilled_after_spill_separated[new_old]:
  gvs[] >> imp_res_tac ALOOKUP_MEM >>
  qpat_x_assum `MEM (op1,_) (REVERSE _)` mp_tac >>
  simp[MEM_REVERSE, MEM_ZIP, LENGTH_REVERSE] >> strip_tac >> gvs[] >>
  qspecl_then [`items`, `al`, `sp`] mp_tac spill_alloc_n_offset_props >>
  simp[LET_THM] >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  first_x_assum drule >> metis_tac[]
QED

Resume spilled_after_spill_separated[both_new]:
  gvs[] >> imp_res_tac ALOOKUP_MEM >>
  qpat_x_assum `MEM (op1,_) (REVERSE _)` mp_tac >>
  qpat_x_assum `MEM (op2,_) (REVERSE _)` mp_tac >>
  simp[MEM_REVERSE, MEM_ZIP, LENGTH_REVERSE] >>
  rpt strip_tac >> gvs[] >>
  qspecl_then [`items`, `al`, `sp`] mp_tac spill_alloc_n_offset_props >>
  simp[LET_THM] >> strip_tac >>
  `n' < n \/ n = n' \/ n < n'` by decide_tac
  >- (first_x_assum (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
      first_x_assum (qspec_then `n'` mp_tac) >> simp[])
  >- gvs[]
  >> first_x_assum (qspec_then `n'` mp_tac) >> simp[] >> strip_tac >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Finalise spilled_after_spill_separated

Resume do_swap_apply_stack_align_layout[all_distinct]:
  simp[Abbr `items_pushed`, Abbr `rev_items`] >>
  irule all_distinct_map_el >>
  simp[Abbr `desired_rev`, ALL_DISTINCT_REVERSE, LENGTH_REVERSE] >>
  conj_tac
  >- (simp[Abbr `desired`, ALL_DISTINCT_APPEND, ALL_DISTINCT_GENLIST,
           MEM_GENLIST] >> simp[Abbr `chunk`] >> decide_tac)
  >>
    simp[Abbr `desired`, EVERY_APPEND, EVERY_GENLIST, Abbr `chunk`]
QED

Resume do_swap_apply_stack_align_layout[flookup]:
  rpt strip_tac >>
  simp[Abbr `items_pushed`, Abbr `restore_offsets`, EL_MAP,
       Abbr `rev_items`] >>
  irule flookup_fupdate_list_el >>
  simp[ALL_DISTINCT_REVERSE, LENGTH_REVERSE] >>
  (* Goal: desired_rev❲k❳ < chunk *)
  qspecl_then [`chunk`, `k`] mp_tac desired_rev_el_bound >>
  simp[Abbr `desired_rev`, Abbr `desired`, Abbr `chunk`]
QED

Resume do_swap_apply_stack_align_layout[items_eq]:
  (* Cancel base_stack, then prove items_pushed = desired form *)
  simp[APPEND_11] >>
  `items_pushed = restored` suffices_by
    simp[Abbr `restored`, Abbr `desired`, MAP_APPEND,
         Once (GSYM EL_def)] >>
  simp[Abbr `items_pushed`, Abbr `restored`, LIST_EQ_REWRITE, EL_MAP,
       Abbr `desired_rev`, LENGTH_REVERSE, Abbr `rev_items`] >>
  rpt strip_tac >>
  qspecl_then [`items`, `x`] mp_tac el_desired_reverse_items >>
  simp[Abbr `desired`, Abbr `chunk`]
QED

Resume do_swap_apply_stack_align_layout[separation]:
  simp[Abbr `rev_items`] >>
  `spill_alloc_layout_wf
     (SND (spill_alloc_n [] ps.ps_alloc items))
     (ps.ps_spilled |++ ZIP(REVERSE items, offsets))` by (
    qspecl_then [`items`, `REVERSE items`, `ps.ps_alloc`, `ps.ps_spilled`]
      mp_tac spill_alloc_n_layout_wf_keys >>
    simp[Abbr `offsets`, LENGTH_REVERSE, ALL_DISTINCT_REVERSE]) >>
  fs[spill_alloc_layout_wf_def]
QED

Finalise do_swap_apply_stack_align_layout

(* Compatibility wrapper for consumers that still carry fresh-allocation
   readiness; the semantic alignment itself only needs durable layout. *)
Theorem do_swap_apply_stack_align:
  !dist ps lo.
    dist < LENGTH ps.ps_stack /\
    (dist > 16 ==>
       ALL_DISTINCT (top_n (dist + 1) ps.ps_stack) /\
       DISJOINT (set (top_n (dist + 1) ps.ps_stack))
                (FDOM ps.ps_spilled) /\
       spill_alloc_wf ps.ps_alloc ps.ps_spilled /\
       ps.ps_alloc.sa_next_offset + 32 * (dist + 1) < dimword(:256)) ==>
    (apply_prefix_ops initial_fmp lo (FST (do_swap dist ps)) ps).ps_stack =
    (SND (do_swap dist ps)).ps_stack
Proof
  rpt strip_tac >>
  irule do_swap_apply_stack_align_layout >> simp[] >>
  strip_tac >> first_x_assum drule >>
  metis_tac[spill_alloc_wf_layout]
QED


(* Direct do_swap and prefix interpretation agree on exactly the fields
   observed by venom_asm_rel. *)
Theorem do_swap_apply_relevant_align_layout:
  !dist ps lo.
    dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
    let via = apply_prefix_ops initial_fmp lo (FST (do_swap dist ps)) ps;
        direct = SND (do_swap dist ps)
    in via.ps_stack = direct.ps_stack /\
       via.ps_spilled = direct.ps_spilled /\
       via.ps_alloc.sa_spill_base = direct.ps_alloc.sa_spill_base /\
       via.ps_alloc.sa_next_offset = direct.ps_alloc.sa_next_offset
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `dist <= 16`
  >- (`apply_prefix_ops initial_fmp lo (FST (do_swap dist ps)) ps =
        SND (do_swap dist ps)` by
        (mp_tac (Q.SPECL [`dist`, `ps`, `FST (do_swap dist ps)`,
                           `SND (do_swap dist ps)`] do_swap_align) >>
         simp[]) >> simp[]) >>
  `dist > 16` by decide_tac >>
  suspend "deep"
QED

Resume do_swap_apply_relevant_align_layout[deep]:
  conj_tac
  >- (irule do_swap_apply_stack_align_layout >> simp[] >>
      rpt strip_tac
      >- (fs[top_n_def] >>
          metis_tac[ALL_DISTINCT_APPEND, TAKE_DROP, ALL_DISTINCT_REVERSE]) >>
      fs[DISJOINT_DEF, EXTENSION, top_n_def] >>
      metis_tac[MEM_TAKE, MEM_REVERSE]) >>
  qabbrev_tac `items = top_n (dist + 1) ps.ps_stack` >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] ps.ps_alloc items)` >>
  qabbrev_tac `desired = [dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]` >>
  qabbrev_tac `desired_rev = REVERSE desired` >>
  qabbrev_tac `restore_offsets = MAP (\idx. EL idx offsets) desired_rev` >>
  `LENGTH items = dist + 1` by
    simp[Abbr `items`, top_n_def, LENGTH_REVERSE, LENGTH_TAKE] >>
  `LENGTH offsets = dist + 1` by
    simp[Abbr `offsets`, spill_alloc_n_offsets_length] >>
  mp_tac (Q.SPECL [`dist`, `ps`] do_swap_big_decompose) >>
  simp[LET_THM] >>
  `top_n (dist + 1) ps.ps_stack = items` by simp[Abbr `items`] >>
  simp[] >> strip_tac >>
  qabbrev_tac `restore_items =
    MAP (\idx. EL idx (REVERSE items)) desired_rev` >>
  `LENGTH desired_rev = dist + 1` by
    simp[Abbr `desired_rev`, Abbr `desired`, LENGTH_REVERSE, LENGTH_GENLIST] >>
  `EVERY (\i. i < LENGTH items) desired_rev` by
    simp[Abbr `desired_rev`, Abbr `desired`, EVERY_REVERSE,
         EVERY_APPEND, EVERY_GENLIST] >>
  `ALL_DISTINCT items` by
    simp[Abbr `items`, top_n_def, ALL_DISTINCT_REVERSE, ALL_DISTINCT_TAKE] >>
  `DISJOINT (set items) (FDOM ps.ps_spilled)` by
    (qpat_x_assum `top_n _ _ = items` (fn th => REWRITE_TAC[GSYM th]) >>
     fs[DISJOINT_DEF, EXTENSION, top_n_def] >>
     metis_tac[MEM_TAKE, MEM_REVERSE]) >>
  `ALL_DISTINCT desired_rev` by
    (qspec_then `dist + 1` mp_tac desired_indices_all_distinct >>
     simp[Abbr `desired_rev`, Abbr `desired`]) >>
  `ALL_DISTINCT restore_items` by
    (simp[Abbr `restore_items`] >> irule all_distinct_map_el >>
     simp[ALL_DISTINCT_REVERSE] >> metis_tac[]) >>
  `(apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps).ps_spilled =
     ps.ps_spilled |++ ZIP(REVERSE items, offsets)` by
    (qspecl_then [`offsets`, `lo`, `ps`] mp_tac apply_spill_ops_spilled >>
     `TAKE (LENGTH offsets) (REVERSE ps.ps_stack) = REVERSE items` by
       simp[Abbr `items`, top_n_def, REVERSE_REVERSE] >>
     simp[]) >>
  `spill_alloc_layout_wf
     (SND (spill_alloc_n [] ps.ps_alloc items))
     (ps.ps_spilled |++ ZIP(REVERSE items, offsets))` by
    (qspecl_then [`items`, `REVERSE items`, `ps.ps_alloc`, `ps.ps_spilled`]
       mp_tac spill_alloc_n_layout_wf_keys >>
     simp[Abbr `offsets`, LENGTH_REVERSE, ALL_DISTINCT_REVERSE]) >>
  `!k. k < LENGTH restore_items ==>
       FLOOKUP (ps.ps_spilled |++ ZIP(REVERSE items,offsets))
         (EL k restore_items) = SOME (EL k restore_offsets)` by
    (rpt strip_tac >>
     `k < LENGTH desired_rev` by fs[Abbr `restore_items`] >>
     simp[Abbr `restore_items`, Abbr `restore_offsets`, EL_MAP] >>
     irule flookup_fupdate_list_el >> simp[ALL_DISTINCT_REVERSE] >>
     fs[EVERY_EL] >> metis_tac[]) >>
  `restore_items = MAP (\idx. EL idx items) desired` by
    (rewrite_tac[LIST_EQ_REWRITE] >> conj_tac
     >- simp[Abbr `restore_items`, Abbr `desired_rev`, Abbr `desired`] >>
     rpt strip_tac >>
     `x < LENGTH desired_rev` by fs[Abbr `restore_items`] >>
     `x < LENGTH desired` by fs[Abbr `desired_rev`] >>
     simp[Abbr `restore_items`, Abbr `desired_rev`, EL_MAP] >>
     qpat_x_assum `Abbrev (desired = _)`
       (SUBST1_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     sym_tac >>
     qspecl_then [`items`, `x`] mp_tac el_desired_reverse_items >>
     simp[]) >>
  `set restore_items = set items` by
    (ASM_REWRITE_TAC[] >>
     qspecl_then [`dist + 1`, `items`] mp_tac set_desired_perm >>
     simp[Abbr `desired`]) >>
  `!op1 off1 op2 off2.
      FLOOKUP (ps.ps_spilled |++ ZIP(REVERSE items,offsets)) op1 = SOME off1 /\
      FLOOKUP (ps.ps_spilled |++ ZIP(REVERSE items,offsets)) op2 = SOME off2 /\
      op1 <> op2 ==>
      off1 + 32 <= off2 \/ off2 + 32 <= off1` by
    (ho_match_mp_tac spill_alloc_layout_wf_spilled_separated >>
     qexists `SND (spill_alloc_n [] ps.ps_alloc items)` >>
     qpat_assum
       `spill_alloc_layout_wf (SND (spill_alloc_n [] ps.ps_alloc items)) _`
       ACCEPT_TAC) >>
  `(apply_prefix_ops initial_fmp lo
      (MAP SOSpill offsets ++ MAP SORestore restore_offsets) ps).ps_spilled =
     ps.ps_spilled` by
    (simp[apply_prefix_ops_append] >>
     qspecl_then [`restore_items`, `restore_offsets`, `lo`,
       `apply_prefix_ops initial_fmp lo (MAP SOSpill offsets) ps`]
       mp_tac apply_restore_ops_spilled >>
     impl_tac
     >- (rpt conj_tac
         >- simp[Abbr `restore_items`, Abbr `restore_offsets`]
         >- simp[]
         >- (rpt strip_tac >> ASM_REWRITE_TAC[] >> metis_tac[]) >>
         ho_match_mp_tac spill_alloc_layout_wf_spilled_separated >>
         qexists `SND (spill_alloc_n [] ps.ps_alloc items)` >>
         ASM_REWRITE_TAC[]) >>
     disch_then SUBST1_TAC >>
     ASM_REWRITE_TAC[] >>
     irule foldl_domsub_cancel >>
     simp[MAP_ZIP, LIST_TO_SET_REVERSE] >>
     conj_tac >- metis_tac[] >> metis_tac[]) >>
  simp[] >>
  conj_tac
  >- simp[apply_prefix_ops_spill_base, foldl_free_spill_base,
          spill_alloc_n_spill_base] >>
  simp[apply_prefix_ops_append, apply_prefix_ops_restore_next_offset,
       apply_spill_ops_next_offset, foldl_free_next_offset] >>
  qspecl_then [`items`, `items`, `ps.ps_alloc`, `ps.ps_spilled`]
    mp_tac spill_alloc_n_foldl_max_next >>
  simp[Abbr `offsets`] >> strip_tac >>
  `(apply_prefix_ops initial_fmp lo (MAP SORestore restore_offsets)
      (apply_prefix_ops initial_fmp lo
        (MAP SOSpill (FST (spill_alloc_n [] ps.ps_alloc items))) ps)).
      ps_alloc.sa_next_offset =
    (apply_prefix_ops initial_fmp lo
      (MAP SOSpill (FST (spill_alloc_n [] ps.ps_alloc items))) ps).
      ps_alloc.sa_next_offset` by
    (irule apply_prefix_ops_restore_next_offset >>
     simp[every_map_restore]) >>
  ASM_REWRITE_TAC[apply_spill_ops_next_offset]
QED

Finalise do_swap_apply_relevant_align_layout


(* Durable semantic simulation for generated swaps.  Prefix execution may
   differ from direct planning in allocator bookkeeping, so transfer only the
   fields observed by venom_asm_rel. *)
Theorem do_swap_venom_asm_rel_layout:
  !dist ps ops ps' lo o2pc prog vs st.
    do_swap dist ps = (ops,ps') /\
    dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    prefix_spill_wf initial_fmp lo ops ps /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt strip_tac >>
  qspecl_then [`ops`, `initial_fmp`, `lo`, `o2pc`, `prog`, `ps`, `vs`, `st`]
    mp_tac mixed_prefix_venom_asm_rel >>
  impl_tac
  >- (rpt conj_tac
      >- (qspecl_then [`dist`, `ps`, `lo`] mp_tac do_swap_wf_len >>
          impl_tac >- ASM_REWRITE_TAC[] >>
          ASM_REWRITE_TAC[LET_THM] >> BETA_TAC >> simp[])
      >- ASM_REWRITE_TAC[]
      >- metis_tac[do_swap_prefix_op]
      >- ASM_REWRITE_TAC[] >>
      ASM_REWRITE_TAC[]) >>
  strip_tac >>
  mp_tac (Q.SPECL [`dist`, `ps`, `lo`]
    do_swap_apply_relevant_align_layout) >>
  ASM_REWRITE_TAC[LET_THM] >> strip_tac >>
  qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  irule venom_asm_rel_ps_transfer >>
  qexists `apply_prefix_ops initial_fmp lo ops ps` >>
  ASM_REWRITE_TAC[] >> BETA_TAC >> metis_tac[]
QED



(* -------------------------------------------------------------------------
   Factored high-water boundary probe
   ------------------------------------------------------------------------- *)

Definition headroom_slots_def:
  (headroom_slots : num list) =
    [0;32;64;96;128;160;192;224;256;
     288;320;352;384;416;448;480;512]
End

Definition headroom_stack_def:
  headroom_stack =
    [Var "a"; Var "b"; Var "c"; Var "d"; Var "e"; Var "f";
     Var "g"; Var "h"; Var "i"; Var "j"; Var "k"; Var "l";
     Var "m"; Var "n"; Var "o"; Var "p"; Var "q"; Var "r"]
End

Definition headroom_alloc_def:
  headroom_alloc =
    <| sa_free_slots := headroom_slots;
       sa_next_offset := dimword(:256) - 32;
       sa_spill_base := 0 |>
End

Definition headroom_ps_def:
  headroom_ps = (init_plan_state 0) with <|
    ps_stack := headroom_stack;
    ps_alloc := headroom_alloc |>
End

Theorem spill_alloc_n_exhausts_free[local]:
  !items offs al.
    LENGTH items = LENGTH al.sa_free_slots ==>
    (SND (spill_alloc_n offs al items)).sa_free_slots = [] /\
    (SND (spill_alloc_n offs al items)).sa_next_offset = al.sa_next_offset /\
    FST (spill_alloc_n offs al items) =
      offs ++ REVERSE al.sa_free_slots
Proof
  Induct
  >- simp[spill_alloc_n_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `al.sa_free_slots`
  >- gvs[] >>
  simp[spill_alloc_n_def, alloc_spill_slot_def] >>
  first_x_assum (qspecl_then
    [`SNOC (LAST (h'::t)) offs`,
     `al with sa_free_slots := FRONT (h'::t)`] mp_tac) >>
  simp[] >>
  (impl_tac >- fs[]) >> strip_tac >>
  `SNOC (LAST (h'::t)) (FRONT (h'::t)) = h'::t` by
    simp[SNOC_LAST_FRONT] >>
  `REVERSE (h'::t) = LAST (h'::t) :: REVERSE (FRONT (h'::t))` by
    metis_tac[REVERSE_SNOC] >>
  gvs[SNOC_APPEND]
QED

Theorem headroom_allocator_trajectory[local]:
  let res = spill_alloc_n [] headroom_alloc headroom_stack
  in
    (SND res).sa_free_slots = [] /\
    (SND res).sa_next_offset = dimword(:256) /\
    FST res = REVERSE headroom_slots ++ [dimword(:256) - 32]
Proof
  simp[LET_THM, headroom_alloc_def, headroom_stack_def,
       headroom_slots_def, spill_alloc_n_def, alloc_spill_slot_def] >>
  `32 <= dimword(:256)` by
    (simp[wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> decide_tac) >>
  decide_tac
QED


Theorem headroom_offsets_all_distinct[local]:
  ALL_DISTINCT (FST (spill_alloc_n [] headroom_alloc headroom_stack))
Proof
  mp_tac headroom_allocator_trajectory >>
  simp[LET_THM] >> strip_tac >>
  ASM_REWRITE_TAC[] >>
  simp[headroom_slots_def, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> decide_tac
QED




Theorem headroom_offsets_symbolic[local]:
  FST (spill_alloc_n [] headroom_alloc headroom_stack) =
    GENLIST (\k. 32 * (16 - k)) 17 ++ [dimword(:256) - 32]
Proof
  mp_tac headroom_allocator_trajectory >>
  simp[LET_THM] >> strip_tac >>
  ASM_REWRITE_TAC[] >>
  simp[headroom_slots_def]
QED


Theorem headroom_offset_formula_props[local]:
  let offsets = GENLIST (\k. 32 * (16 - k)) 17 ++ [dimword(:256) - 32]
  in !k. k < LENGTH offsets ==>
       EL k offsets < dimword(:256) /\
       (!j. j < k ==>
          EL j offsets + 32 <= EL k offsets \/
          EL k offsets + 32 <= EL j offsets)
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  `576 <= dimword(:256)` by
    (simp[wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> decide_tac) >>
  gen_tac >> strip_tac >>
  `k < 18` by fs[LENGTH_APPEND, LENGTH_GENLIST] >>
  Cases_on `k < 17`
  >- (conj_tac
      >- (ASM_SIMP_TAC pure_ss [EL_APPEND1, LENGTH_GENLIST, EL_GENLIST] >>
          decide_tac) >>
      rpt strip_tac >>
      `j < 17` by decide_tac >>
      ASM_SIMP_TAC pure_ss [EL_APPEND1, LENGTH_GENLIST, EL_GENLIST] >>
      decide_tac) >>
  `k = 17` by decide_tac >>
  qpat_x_assum `k = 17` SUBST_ALL_TAC >>
  `EL 17 (GENLIST (\k. 32 * (16 - k)) 17 ++ [dimword(:256) - 32]) =
     dimword(:256) - 32` by
    simp[EL_APPEND2] >>
  conj_tac
  >- (ASM_REWRITE_TAC[] >> decide_tac) >>
  rpt strip_tac >>
  `j < 17` by decide_tac >>
  ASM_SIMP_TAC pure_ss
    [EL_APPEND1, LENGTH_GENLIST, EL_GENLIST] >>
  decide_tac
QED



Theorem headroom_offset_layout_props[local]:
  let offsets = FST (spill_alloc_n [] headroom_alloc headroom_stack)
  in !k. k < LENGTH offsets ==>
       EL k offsets + 32 <= dimword(:256) /\
       (!j. j < k ==>
          EL j offsets + 32 <= EL k offsets \/
          EL k offsets + 32 <= EL j offsets)
Proof
  rewrite_tac[headroom_offsets_symbolic, LET_THM] >> BETA_TAC >>
  `576 <= dimword(:256)` by
    (simp[wordsTheory.dimword_def] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> decide_tac) >>
  gen_tac >> strip_tac >>
  `k < 18` by fs[LENGTH_APPEND, LENGTH_GENLIST] >>
  Cases_on `k < 17`
  >- (conj_tac
      >- (ASM_SIMP_TAC pure_ss [EL_APPEND1, LENGTH_GENLIST, EL_GENLIST] >>
          decide_tac) >>
      rpt strip_tac >>
      `j < 17` by decide_tac >>
      ASM_SIMP_TAC pure_ss [EL_APPEND1, LENGTH_GENLIST, EL_GENLIST] >>
      decide_tac) >>
  `k = 17` by decide_tac >>
  qpat_x_assum `k = 17` SUBST_ALL_TAC >>
  `EL 17 (GENLIST (\k. 32 * (16 - k)) 17 ++ [dimword(:256) - 32]) =
     dimword(:256) - 32` by simp[EL_APPEND2] >>
  conj_tac
  >- (ASM_REWRITE_TAC[] >> decide_tac) >>
  rpt strip_tac >>
  `j < 17` by decide_tac >>
  ASM_SIMP_TAC pure_ss [EL_APPEND1, LENGTH_GENLIST, EL_GENLIST] >>
  decide_tac
QED

Theorem headroom_final_allocator[local]:
  let res = spill_alloc_n [] headroom_alloc headroom_stack;
      offsets = FST res;
      alloc2 = FOLDL (\al off. free_spill_slot off al) (SND res) offsets
  in alloc2.sa_free_slots = offsets /\
     alloc2.sa_next_offset = dimword(:256) /\
     alloc2.sa_spill_base = 0
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  mp_tac headroom_allocator_trajectory >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  simp[foldl_free_free_slots, foldl_free_next_offset,
       foldl_free_spill_base, spill_alloc_n_spill_base,
       headroom_alloc_def]
QED
Theorem headroom_spill_pairs_preconditions[local]:
  let offsets = FST (spill_alloc_n [] headroom_alloc headroom_stack);
      pairs = ZIP (REVERSE headroom_stack, offsets)
  in
    MAP FST pairs = TAKE (LENGTH pairs) (REVERSE headroom_ps.ps_stack) /\
    LENGTH pairs <= LENGTH headroom_ps.ps_stack /\
    ALL_DISTINCT (MAP FST pairs) /\
    (!k. k < LENGTH pairs ==>
       SND (EL k pairs) < dimword(:256) /\
       headroom_ps.ps_alloc.sa_spill_base <= SND (EL k pairs) /\
       (!op2 off2. FLOOKUP headroom_ps.ps_spilled op2 = SOME off2 ==>
          off2 + 32 <= SND (EL k pairs) \/ SND (EL k pairs) + 32 <= off2) /\
       (!j. j < k ==>
          SND (EL j pairs) + 32 <= SND (EL k pairs) \/
          SND (EL k pairs) + 32 <= SND (EL j pairs)))
Proof
  rewrite_tac[headroom_offsets_symbolic, LET_THM] >> BETA_TAC >>
  qabbrev_tac
    `offsets = GENLIST (\k. 32 * (16 - k)) 17 ++ [dimword(:256) - 32]` >>
  `LENGTH offsets = 18` by simp[Abbr `offsets`] >>
  `LENGTH (REVERSE headroom_stack) = LENGTH offsets` by
    simp[headroom_stack_def] >>
  `!k. k < LENGTH offsets ==>
       EL k offsets < dimword(:256) /\
       (!j. j < k ==>
          EL j offsets + 32 <= EL k offsets \/
          EL k offsets + 32 <= EL j offsets)` by
    (mp_tac headroom_offset_formula_props >>
     rewrite_tac[LET_THM] >> BETA_TAC >>
     simp[Abbr `offsets`]) >>
  conj_tac
  >- simp[MAP_ZIP, headroom_ps_def, headroom_stack_def] >>
  conj_tac
  >- simp[LENGTH_ZIP, headroom_ps_def, headroom_stack_def] >>
  conj_tac
  >- simp[MAP_ZIP, headroom_ps_def, headroom_stack_def] >>
  gen_tac >> strip_tac >>
  `k < LENGTH offsets` by fs[LENGTH_ZIP] >>
  qpat_x_assum `!k. k < LENGTH offsets ==> _`
    (qspec_then `k` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `EL k (ZIP (REVERSE headroom_stack,offsets)) =
     (EL k (REVERSE headroom_stack), EL k offsets)` by
    (irule EL_ZIP >> simp[]) >>
  conj_tac
  >- ASM_REWRITE_TAC[] >>
  conj_tac
  >- simp[headroom_ps_def, headroom_alloc_def, init_plan_state_def] >>
  conj_tac
  >- simp[headroom_ps_def, init_plan_state_def] >>
  gen_tac >> strip_tac >>
  `j < LENGTH offsets` by decide_tac >>
  `EL j (ZIP (REVERSE headroom_stack,offsets)) =
     (EL j (REVERSE headroom_stack), EL j offsets)` by
    (irule EL_ZIP >> simp[]) >>
  qpat_x_assum `!j. j < k ==> _` (qspec_then `j` mp_tac) >>
  ASM_REWRITE_TAC[] >> simp[]
QED

Theorem headroom_restore_phase[local]:
  let offsets = FST (spill_alloc_n [] headroom_alloc headroom_stack);
      desired_rev = REVERSE ([17] ++ GENLIST (\i. i + 1) 16 ++ [0]);
      post = apply_prefix_ops initial_fmp FEMPTY (MAP SOSpill offsets) headroom_ps
  in prefix_spill_wf initial_fmp FEMPTY
       (MAP SORestore (MAP (\idx. EL idx offsets) desired_rev)) post
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  qabbrev_tac `offsets = FST (spill_alloc_n [] headroom_alloc headroom_stack)` >>
  qabbrev_tac `desired_rev = REVERSE ([17] ++ GENLIST (\i. i + 1) 16 ++ [0])` >>
  qabbrev_tac `items = MAP (\idx. EL idx (REVERSE headroom_stack)) desired_rev` >>
  qabbrev_tac `restore_offsets = MAP (\idx. EL idx offsets) desired_rev` >>
  qabbrev_tac `post = apply_prefix_ops initial_fmp FEMPTY (MAP SOSpill offsets) headroom_ps` >>
  `LENGTH offsets = 18` by
    simp[Abbr `offsets`, spill_alloc_n_offsets_length, headroom_stack_def] >>
  `LENGTH desired_rev = 18` by
    simp[Abbr `desired_rev`] >>
  `ALL_DISTINCT desired_rev` by
    (simp[Abbr `desired_rev`] >>
     irule desired_indices_all_distinct >> decide_tac) >>
  `EVERY (\i. i < 18) desired_rev` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     qspecl_then [`18`, `n`] mp_tac desired_rev_el_bound >>
     simp[Abbr `desired_rev`]) >>
  `ALL_DISTINCT items` by
    (simp[Abbr `items`] >>
     irule all_distinct_map_el >>
     simp[headroom_stack_def, ALL_DISTINCT_REVERSE] >>
     ASM_REWRITE_TAC[] >>
     fs[EVERY_EL]) >>
  `ALL_DISTINCT restore_offsets` by
    (simp[Abbr `restore_offsets`] >>
     irule all_distinct_map_el >>
     simp[Abbr `offsets`, headroom_offsets_all_distinct] >>
     fs[EVERY_EL]) >>
  `post.ps_spilled = FEMPTY |++ ZIP (REVERSE headroom_stack,offsets)` by
    (simp[Abbr `post`] >>
     qspecl_then [`offsets`, `FEMPTY`, `headroom_ps`]
       mp_tac apply_spill_ops_spilled >>
     (impl_tac >- simp[headroom_ps_def, headroom_stack_def]) >>
     strip_tac >> ASM_REWRITE_TAC[] >>
     simp[headroom_ps_def, init_plan_state_def, headroom_stack_def]) >>
  qspecl_then [`items`, `restore_offsets`, `FEMPTY`, `post`]
    mp_tac prefix_spill_wf_map_restore_lookup >>
  (impl_tac >-
    (rpt conj_tac
     >- simp[Abbr `items`, Abbr `restore_offsets`]
     >- simp[]
     >- simp[] >>
     gen_tac >> strip_tac >>
     `k < LENGTH desired_rev` by fs[Abbr `items`] >>
     simp[Abbr `items`, Abbr `restore_offsets`, EL_MAP] >>
     conj_tac
     >- (ASM_REWRITE_TAC[] >>
         irule flookup_fupdate_list_el >>
         simp[headroom_stack_def, ALL_DISTINCT_REVERSE] >>
         qspecl_then [`18`, `k`] mp_tac desired_rev_el_bound >>
         simp[Abbr `desired_rev`]) >>
     mp_tac headroom_offset_formula_props >>
     rewrite_tac[LET_THM] >> BETA_TAC >>
     simp[GSYM headroom_offsets_symbolic, Abbr `offsets`] >>
     disch_then (qspec_then `EL k desired_rev` mp_tac) >>
     impl_tac
     >- (qspecl_then [`18`, `k`] mp_tac desired_rev_el_bound >>
         simp[Abbr `desired_rev`]) >>
     simp[])) >>
  simp[Abbr `items`, Abbr `restore_offsets`, Abbr `post`]
QED



Theorem do_swap_headroom_witness_facts:
  prefix_spill_wf initial_fmp FEMPTY (FST (do_swap 17 headroom_ps)) headroom_ps /\
  spill_alloc_wf headroom_ps.ps_alloc headroom_ps.ps_spilled /\
  (SND (do_swap 17 headroom_ps)).ps_alloc.sa_next_offset = dimword(:256)
Proof
  conj_tac
  >- (qabbrev_tac `offsets = FST (spill_alloc_n [] headroom_alloc headroom_stack)` >>
      qabbrev_tac `desired_rev = REVERSE ([17] ++ GENLIST (\i. i + 1) 16 ++ [0])` >>
      `FST (do_swap 17 headroom_ps) =
         MAP SOSpill offsets ++
         MAP SORestore (MAP (\idx. EL idx offsets) desired_rev)` by
        (mp_tac (Q.SPECL [`17`, `headroom_ps`] do_swap_big_decompose) >>
         simp[LET_THM, headroom_ps_def, headroom_stack_def, top_n_def,
              Abbr `offsets`, Abbr `desired_rev`]) >>
      `offsets = REVERSE headroom_slots ++ [dimword(:256) - 32]` by
        (mp_tac headroom_allocator_trajectory >>
         simp[LET_THM, Abbr `offsets`]) >>
      ASM_REWRITE_TAC[prefix_spill_wf_append] >>
      conj_tac
      >- (`MAP SND (ZIP (REVERSE headroom_stack,offsets)) = offsets` by
            (irule (cj 2 MAP_ZIP) >>
             simp[headroom_stack_def, Abbr `offsets`,
                  spill_alloc_n_offsets_length]) >>
          qspecl_then
            [`ZIP (REVERSE headroom_stack,offsets)`, `FEMPTY`, `headroom_ps`]
            mp_tac prefix_spill_wf_map_spill_pairs >>
          (impl_tac >-
            (mp_tac headroom_spill_pairs_preconditions >>
             rewrite_tac[LET_THM] >> BETA_TAC >>
             simp[Abbr `offsets`])) >>
          ASM_REWRITE_TAC[]) >>
      mp_tac headroom_restore_phase >>
      rewrite_tac[LET_THM] >> BETA_TAC >>
      simp[Abbr `offsets`, Abbr `desired_rev`])
  >> conj_tac
  >- (`576 <= dimword(:256)` by
        (simp[wordsTheory.dimword_def] >>
         CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> decide_tac) >>
      simp[headroom_ps_def, headroom_alloc_def, init_plan_state_def,
           spill_alloc_wf_def] >>
      `headroom_slots = GENLIST (\k. 32 * k) 17` by
        simp[headroom_slots_def] >>
      ASM_REWRITE_TAC[] >>
      conj_tac
      >- (gen_tac >> simp[MEM_GENLIST] >> decide_tac) >>
      conj_tac
      >- (simp[ALL_DISTINCT_GENLIST] >> decide_tac) >>
      rpt gen_tac >> strip_tac >>
      gvs[LENGTH_GENLIST] >>
      ASM_SIMP_TAC pure_ss [EL_GENLIST] >>
      decide_tac)
  >> mp_tac (Q.SPECL [`17`, `headroom_ps`] do_swap_big_decompose) >>
  (impl_tac >- simp[headroom_ps_def, headroom_stack_def]) >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  gvs[foldl_free_next_offset] >>
  `headroom_ps.ps_alloc = headroom_alloc` by
    simp[headroom_ps_def] >>
  `top_n 18 headroom_ps.ps_stack = headroom_stack` by
    simp[headroom_ps_def, top_n_def, headroom_stack_def] >>
  ASM_REWRITE_TAC[] >>
  mp_tac headroom_allocator_trajectory >>
  simp[LET_THM]
QED


Theorem headroom_final_allocator_layout[local]:
  let res = spill_alloc_n [] headroom_alloc headroom_stack;
      offsets = FST res;
      alloc2 = FOLDL (\al off. free_spill_slot off al) (SND res) offsets
  in spill_alloc_layout_wf alloc2 FEMPTY
Proof
  rewrite_tac[LET_THM] >> BETA_TAC >>
  mp_tac headroom_final_allocator >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  fs[spill_alloc_layout_wf_def] >>
  conj_tac
  >- (rpt strip_tac >> fs[MEM_EL] >>
      mp_tac headroom_offset_layout_props >>
      rewrite_tac[LET_THM] >> BETA_TAC >>
      disch_then (qspec_then `n` mp_tac) >> simp[]) >>
  conj_tac
  >- simp[headroom_offsets_all_distinct] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i < j`
  >- (mp_tac headroom_offset_layout_props >>
      rewrite_tac[LET_THM] >> BETA_TAC >>
      disch_then (qspec_then `j` mp_tac) >> simp[] >>
      disch_then (qspec_then `i` mp_tac) >> simp[]) >>
  `j < i` by decide_tac >>
  mp_tac headroom_offset_layout_props >>
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (qspec_then `i` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!j. j < i ==> _` (qspec_then `j` mp_tac) >>
  simp[]
QED

Theorem do_swap_headroom_post_layout:
  let post = SND (do_swap 17 headroom_ps) in
    spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
    post.ps_alloc.sa_spill_base = 0 /\
    post.ps_alloc.sa_next_offset = dimword(:256) /\
    post.ps_spilled = FEMPTY /\
    ALL_DISTINCT post.ps_stack /\
    ~spill_alloc_wf post.ps_alloc post.ps_spilled
Proof
  rewrite_tac[LET_THM] >>
  mp_tac (Q.SPECL [`17`, `headroom_ps`] do_swap_big_decompose) >>
  (impl_tac >- simp[headroom_ps_def, headroom_stack_def]) >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `do_swap 17 headroom_ps = _`
    (fn th => rewrite_tac[th]) >>
  `headroom_ps.ps_alloc = headroom_alloc` by
    simp[headroom_ps_def] >>
  `top_n 18 headroom_ps.ps_stack = headroom_stack` by
    simp[headroom_ps_def, headroom_stack_def, top_n_def] >>
  `ALL_DISTINCT
     (TAKE (LENGTH headroom_ps.ps_stack - (17 + 1)) headroom_ps.ps_stack ++
      MAP (\idx. EL idx (top_n (17 + 1) headroom_ps.ps_stack))
        ([17] ++ GENLIST (\i. i + 1) (17 - 1) ++ [0]))` by
    simp[headroom_ps_def, headroom_stack_def, top_n_def] >>
  `headroom_ps.ps_spilled = FEMPTY` by
    simp[headroom_ps_def, init_plan_state_def] >>
  simp[] >>
  mp_tac headroom_final_allocator_layout >>
  rewrite_tac[LET_THM] >> BETA_TAC >> disch_then assume_tac >>
  mp_tac headroom_final_allocator >>
  rewrite_tac[LET_THM] >> BETA_TAC >> strip_tac >>
  ASM_REWRITE_TAC[spill_alloc_wf_iff_layout_ready] >>
  simp[headroom_ps_def, headroom_stack_def, top_n_def]
QED
