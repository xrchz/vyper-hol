(* Checked static-layout completion invariants. *)

Theory staticLayoutCompletionProofs
Ancestors
  staticLayoutAllocatorProofs staticLayoutFoldProofs concretizeMemLocDefs
  staticLayoutDefs staticLayoutWf list finite_map arithmetic

Theorem reserved_intervals_disjoint_sym_completion[local]:
  !r1 r2.
    reserved_intervals_disjoint r1 r2 <=>
    reserved_intervals_disjoint r2 r1
Proof
  PairCases >> PairCases >>
  simp[reserved_intervals_disjoint_def] >> metis_tac[]
QED

Theorem reserved_intervals_wf_insert_after[local]:
  !prefix suffix r.
    reserved_intervals_wf (prefix ++ suffix) /\
    reserved_interval_wf r /\
    EVERY (reserved_intervals_disjoint r) (prefix ++ suffix) ==>
    reserved_intervals_wf (prefix ++ r::suffix)
Proof
  Induct_on `prefix`
  >- simp[reserved_intervals_wf_def]
  >> gen_tac >> rpt gen_tac >>
  simp[reserved_intervals_wf_def] >> strip_tac >>
  gvs[EVERY_APPEND] >>
  metis_tac[reserved_intervals_disjoint_sym_completion]
QED

Theorem checked_preserved_intervals_aux_invariant:
  !items positions reserved occupied result.
    reserved_intervals_wf (reserved ++ occupied) /\
    checked_preserved_intervals_aux items positions reserved occupied =
      SOME result ==>
    reserved_intervals_wf (reserved ++ result) /\
    (!r. MEM r occupied ==> MEM r result) /\
    (!alloc sz pos.
       MEM (alloc,sz) items /\ FLOOKUP positions alloc = SOME pos ==>
       pos + sz < dimword (:256) /\
       (0 < sz ==> MEM (pos,sz) result))
Proof
  Induct_on `items`
  >- simp[checked_preserved_intervals_aux_def]
  >> gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP positions h0`
  >- (gvs[checked_preserved_intervals_aux_def] >>
      first_x_assum
        (qspecl_then [`positions`,`reserved`,`occupied`,`result`] mp_tac) >>
      simp[] >> strip_tac >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      qpat_x_assum `!alloc sz pos. _`
        (qspecl_then [`alloc`,`sz`,`pos`] mp_tac) >> simp[])
  >> Cases_on `x + h1 < dimword (:256)`
  >- (Cases_on `h1 = 0`
      >- (gvs[checked_preserved_intervals_aux_def] >>
          first_x_assum
            (qspecl_then [`positions`,`reserved`,`occupied`,`result`] mp_tac) >>
          simp[] >> strip_tac >>
          rpt gen_tac >> strip_tac >> gvs[] >>
          qpat_x_assum `!alloc sz pos. _`
            (qspecl_then [`alloc`,`sz`,`pos`] mp_tac) >> simp[])
      >> Cases_on
           `EVERY (reserved_intervals_disjoint (x,h1))
                  (reserved ++ occupied)`
      >- (gvs[checked_preserved_intervals_aux_def] >>
          `reserved_intervals_wf
             (reserved ++ (x,h1)::occupied)` by
            (irule reserved_intervals_wf_insert_after >>
             simp[reserved_interval_wf_def]) >>
          first_x_assum
            (qspecl_then
              [`positions`,`reserved`,`(x,h1)::occupied`,`result`] mp_tac) >>
          simp[] >> strip_tac >>
          rpt gen_tac >> strip_tac >> gvs[]
          >- (qpat_x_assum `!alloc sz pos. _`
                (qspecl_then [`alloc`,`sz`,`pos`] mp_tac) >> simp[])
          >> simp[ADD_COMM] >>
             qpat_x_assum `!r. _` (qspec_then `(x,h1)` mp_tac) >> simp[])
      >> gvs[checked_preserved_intervals_aux_def, EVERY_MEM, EXISTS_MEM])
  >> gvs[checked_preserved_intervals_aux_def]
QED

Theorem checked_preserved_intervals_invariant:
  checked_preserved_intervals items positions reserved = SOME occupied ==>
  reserved_intervals_wf (reserved ++ occupied) /\
  (!alloc sz pos.
     MEM (alloc,sz) items /\ FLOOKUP positions alloc = SOME pos ==>
     pos + sz < dimword (:256) /\
     (0 < sz ==> MEM (pos,sz) occupied))
Proof
  simp[checked_preserved_intervals_def] >> strip_tac >>
  qspecl_then [`items`,`positions`,`reserved`,`[]`,`occupied`] mp_tac
    checked_preserved_intervals_aux_invariant >> simp[] >> strip_tac >> simp[]
QED

Theorem reserved_intervals_wf_MEM_wf[local]:
  !rs r.
    reserved_intervals_wf rs /\ MEM r rs ==>
    reserved_interval_wf r
Proof
  Induct_on `rs` >> simp[reserved_intervals_wf_def] >> metis_tac[]
QED

Theorem reserved_intervals_wf_MEM_disjoint[local]:
  !rs r1 r2.
    reserved_intervals_wf rs /\ MEM r1 rs /\ MEM r2 rs /\ r1 <> r2 ==>
    reserved_intervals_disjoint r1 r2
Proof
  Induct_on `rs` >> simp[reserved_intervals_wf_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[reserved_intervals_disjoint_sym_completion, EVERY_MEM]
QED

Theorem checked_preserved_intervals_item:
  checked_preserved_intervals items positions reserved = SOME occupied /\
  MEM (alloc,sz) items /\ FLOOKUP positions alloc = SOME pos ==>
  pos + sz < dimword (:256) /\
  (0 < sz ==> MEM (pos,sz) occupied)
Proof
  metis_tac[checked_preserved_intervals_invariant]
QED


Definition positive_preserved_item_def[local]:
  positive_preserved_item items
      (positions : (allocation,num) fmap) item interval <=>
    ?(alloc : allocation) (sz : num) (pos : num).
      item = (alloc,sz) /\ interval = (pos,sz) /\
      MEM (alloc,sz) items /\ FLOOKUP positions alloc = SOME pos /\
      0 < sz
End

Theorem positive_preserved_item_intro[local]:
  MEM (alloc,sz) items /\ FLOOKUP positions alloc = SOME pos /\ 0 < sz ==>
  positive_preserved_item items positions (alloc,sz) (pos,sz)
Proof
  simp[positive_preserved_item_def] >> metis_tac[]
QED

Theorem positive_preserved_item_elim[local]:
  positive_preserved_item items positions (alloc,sz) interval ==>
  MEM (alloc,sz) items /\ 0 < sz /\
  ?pos. interval = (pos,sz) /\ FLOOKUP positions alloc = SOME pos
Proof
  simp[positive_preserved_item_def] >> metis_tac[]
QED

Theorem positive_preserved_item_tail_mono[local]:
  positive_preserved_item items positions item interval ==>
  positive_preserved_item (h::items) positions item interval
Proof
  simp[positive_preserved_item_def] >> metis_tac[]
QED

Theorem positive_preserved_item_lookup_NONE[local]:
  FLOOKUP positions alloc = NONE ==>
  ~positive_preserved_item items positions (alloc,sz) interval
Proof
  simp[positive_preserved_item_def] >> metis_tac[]
QED

Theorem positive_preserved_item_zero[local]:
  ~positive_preserved_item items positions (alloc,0) interval
Proof
  simp[positive_preserved_item_def]
QED

Theorem checked_preserved_intervals_aux_relational[local]:
  !items positions reserved occupied result.
    checked_preserved_intervals_aux items positions reserved occupied =
      SOME result ==>
    (!item i r.
      positive_preserved_item items positions item i /\
      MEM r (reserved ++ occupied) ==>
      reserved_intervals_disjoint i r) /\
    (!item1 i1 item2 i2.
      positive_preserved_item items positions item1 i1 /\
      positive_preserved_item items positions item2 i2 /\ item1 <> item2 ==>
      reserved_intervals_disjoint i1 i2)
Proof
  Induct
  >- simp[positive_preserved_item_def]
  >> Cases_on `h` >> rpt gen_tac
  >> Cases_on `FLOOKUP positions q`
  >- (gvs[checked_preserved_intervals_aux_def,
          positive_preserved_item_def] >> strip_tac
      >> first_x_assum drule >> strip_tac
      >> conj_tac
      >- (rpt strip_tac >> gvs[] >> metis_tac[])
      >> rpt strip_tac >> gvs[]
      >> qpat_x_assum `!item1 i1 item2 i2. _`
           (qspecl_then [`(alloc,sz)`,`(pos,sz)`,
                         `(alloc',sz')`,`(pos',sz')`] mp_tac)
      >> simp[] >> metis_tac[])
  >> Cases_on `x + r < dimword (:256)`
  >- (Cases_on `r = 0`
      >- (gvs[checked_preserved_intervals_aux_def,
              positive_preserved_item_def] >> strip_tac
          >> first_x_assum drule >> strip_tac
          >> conj_tac
          >- (rpt strip_tac >> gvs[] >> metis_tac[])
          >> rpt strip_tac >> gvs[]
          >> qpat_x_assum `!item1 i1 item2 i2. _`
               (qspecl_then [`(alloc,sz)`,`(pos,sz)`,
                             `(alloc',sz')`,`(pos',sz')`] mp_tac)
          >> simp[] >> metis_tac[])
      >> Cases_on
           `EVERY (reserved_intervals_disjoint (x,r))
                  (reserved ++ occupied)`
      >- (gvs[checked_preserved_intervals_aux_def,
              positive_preserved_item_def, EVERY_MEM] >> strip_tac
          >> first_x_assum drule >> strip_tac
          >> conj_tac
          >- (rpt strip_tac >> gvs[] >>
              metis_tac[reserved_intervals_disjoint_sym_completion])
          >> rpt strip_tac >> gvs[]
          >- (qpat_assum `!item i r''. _`
                (qspecl_then [`(alloc',sz')`,`(pos',sz')`,`(pos,r)`] mp_tac) >>
              simp[] >>
              metis_tac[reserved_intervals_disjoint_sym_completion])
          >- (qpat_assum `!item i r''. _`
                (qspecl_then [`(alloc,sz)`,`(pos,sz)`,`(pos',r)`] mp_tac) >>
              simp[] >> metis_tac[])
          >> qpat_assum `!item1 i1 item2 i2. _`
               (qspecl_then [`(alloc,sz)`,`(pos,sz)`,
                             `(alloc',sz')`,`(pos',sz')`] mp_tac)
          >> simp[] >> metis_tac[])
      >> gvs[checked_preserved_intervals_aux_def, EVERY_MEM, EXISTS_MEM]
      >> strip_tac >> metis_tac[])
  >> gvs[checked_preserved_intervals_aux_def]
QED

Theorem checked_preserved_intervals_pairwise:
  checked_preserved_intervals items positions reserved = SOME occupied /\
  MEM (alloc1,sz1) items /\ MEM (alloc2,sz2) items /\
  FLOOKUP positions alloc1 = SOME pos1 /\
  FLOOKUP positions alloc2 = SOME pos2 /\
  0 < sz1 /\ 0 < sz2 /\ (alloc1,sz1) <> (alloc2,sz2) ==>
  reserved_intervals_disjoint (pos1,sz1) (pos2,sz2)
Proof
  simp[checked_preserved_intervals_def] >> strip_tac
  >> qspecl_then [`items`,`positions`,`reserved`,`[]`,`occupied`] mp_tac
       checked_preserved_intervals_aux_relational
  >> simp[] >> disch_then strip_assume_tac
  >> qpat_x_assum `!item1 i1 item2 i2. _` irule
  >> qexistsl [`(alloc1,sz1)`,`(alloc2,sz2)`]
  >> simp[positive_preserved_item_intro] >> metis_tac[]
QED


Definition completion_state_inv_def[local]:
  completion_state_inv items positions occupied <=>
    reserved_intervals_wf occupied /\
    (!alloc sz pos.
      MEM (alloc,sz) items /\ FLOOKUP positions alloc = SOME pos ==>
      pos + sz < dimword (:256) /\
      (0 < sz ==> MEM (pos,sz) occupied)) /\
    (!alloc1 sz1 pos1 alloc2 sz2 pos2.
      MEM (alloc1,sz1) items /\ MEM (alloc2,sz2) items /\
      FLOOKUP positions alloc1 = SOME pos1 /\
      FLOOKUP positions alloc2 = SOME pos2 /\
      0 < sz1 /\ 0 < sz2 /\ (alloc1,sz1) <> (alloc2,sz2) ==>
      reserved_intervals_disjoint (pos1,sz1) (pos2,sz2))
End

Theorem item_key_MEM_MAP[local]:
  MEM (alloc,sz) items ==> MEM alloc (MAP FST items)
Proof
  strip_tac >> simp[MEM_MAP] >> qexists `(alloc,sz)` >> simp[]
QED

Theorem all_distinct_item_key_unique[local]:
  !items alloc sz1 sz2.
    ALL_DISTINCT (MAP FST items) /\
    MEM (alloc,sz1) items /\ MEM (alloc,sz2) items ==>
    sz1 = sz2
Proof
  Induct_on `items`
  >- simp[]
  >> gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac
  >> gvs[] >> metis_tac[item_key_MEM_MAP]
QED

Theorem completion_state_inv_insert[local]:
  ALL_DISTINCT (MAP FST items) /\ MEM (alloc,sz) items /\
  FLOOKUP positions alloc = NONE /\
  checked_first_fit occupied sz = SOME pos /\
  completion_state_inv items positions occupied ==>
  completion_state_inv items (positions |+ (alloc,pos))
    (if sz = 0 then occupied else (pos,sz)::occupied)
Proof
  strip_tac
  >> qpat_x_assum `checked_first_fit occupied sz = SOME pos`
       (fn th => assume_tac (MATCH_MP checked_first_fit_SOME th))
  >> gvs[completion_state_inv_def]
  >> conj_tac
  >- (Cases_on `sz = 0` >> gvs[])
  >> conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `alloc' = alloc`
      >- (`sz' = sz` by metis_tac[all_distinct_item_key_unique] >>
          gvs[FLOOKUP_UPDATE])
      >> gvs[FLOOKUP_UPDATE]
      >> qpat_assum
           `!a s p. MEM (a,s) items /\ FLOOKUP positions a = SOME p ==> _`
           (qspecl_then [`alloc'`,`sz'`,`pos'`] mp_tac)
      >> simp[] >> strip_tac >> Cases_on `sz = 0` >> gvs[])
  >> rpt gen_tac >> strip_tac
  >> Cases_on `alloc1 = alloc`
  >- (Cases_on `alloc2 = alloc`
      >- (`sz1 = sz` by metis_tac[all_distinct_item_key_unique] >>
          `sz2 = sz` by metis_tac[all_distinct_item_key_unique] >>
          gvs[FLOOKUP_UPDATE])
      >> `sz1 = sz` by metis_tac[all_distinct_item_key_unique]
      >> gvs[EVERY_MEM, FLOOKUP_UPDATE]
      >> metis_tac[])
  >> Cases_on `alloc2 = alloc`
  >- (`sz2 = sz` by metis_tac[all_distinct_item_key_unique]
      >> gvs[EVERY_MEM, FLOOKUP_UPDATE]
      >> metis_tac[reserved_intervals_disjoint_sym_completion])
  >> gvs[FLOOKUP_UPDATE]
  >> qpat_x_assum `!a1 s1 p1 a2 s2 p2. _`
       (qspecl_then [`alloc1`,`sz1`,`pos1`,`alloc2`,`sz2`,`pos2`] mp_tac)
  >> simp[]
QED

Theorem complete_alloc_positions_aux_invariant[local]:
  !insts items positions occupied completed.
    ALL_DISTINCT (MAP FST items) /\
    (!inst item. MEM inst insts /\ exact_static_alloca inst = SOME item ==>
       MEM item items) /\
    completion_state_inv items positions occupied /\
    complete_alloc_positions_aux insts positions occupied = SOME completed ==>
    ?final_occupied.
      completion_state_inv items completed final_occupied /\
      (!r. MEM r occupied ==> MEM r final_occupied) /\
      (!alloc pos. FLOOKUP positions alloc = SOME pos ==>
         FLOOKUP completed alloc = SOME pos) /\
      (!inst alloc sz. MEM inst insts /\
         exact_static_alloca inst = SOME (alloc,sz) ==>
         ?pos. FLOOKUP completed alloc = SOME pos)
Proof
  Induct
  >- (rpt gen_tac >> simp[complete_alloc_positions_aux_def] >> strip_tac
      >> qexists `occupied` >> gvs[])
  >> rpt gen_tac >> strip_tac
  >> Cases_on `h.inst_opcode = ALLOCA`
  >- (Cases_on `exact_static_alloca_size h`
      >> gvs[complete_alloc_positions_aux_def]
      >> Cases_on `FLOOKUP positions (Allocation h.inst_id)`
      >- (Cases_on `checked_first_fit occupied x`
          >> gvs[complete_alloc_positions_aux_def]
          >> suspend "missing_alloc")
      >> gvs[complete_alloc_positions_aux_def]
      >> suspend "existing_alloc")
  >> gvs[complete_alloc_positions_aux_def, exact_static_alloca_def,
         exact_static_alloca_size_def]
  >> suspend "nonalloc"
QED


Resume complete_alloc_positions_aux_invariant[missing_alloc]:
  `MEM (Allocation h.inst_id,x) items` by
    (qpat_x_assum `!inst item. _`
       (qspecl_then [`h`,`(Allocation h.inst_id,x)`] mp_tac) >>
     simp[exact_static_alloca_def])
  >> `!inst item. MEM inst insts /\
         exact_static_alloca inst = SOME item ==> MEM item items` by metis_tac[]
  >> `completion_state_inv items (positions |+ (Allocation h.inst_id,x'))
        (if x = 0 then occupied else (x',x)::occupied)` by
       metis_tac[completion_state_inv_insert]
  >> qpat_x_assum `!items positions occupied completed. _`
       (qspecl_then
         [`items`,`positions |+ (Allocation h.inst_id,x')`,
          `if x = 0 then occupied else (x',x)::occupied`,`completed`] mp_tac)
  >> simp[] >> (impl_tac >- metis_tac[])
  >> disch_then (qx_choose_then `final_occupied` strip_assume_tac)
  >> qexists `final_occupied` >> simp[]
  >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >>
      Cases_on `x = 0` >> gvs[])
  >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >>
      `Allocation h.inst_id <> alloc` by (CCONTR_TAC >> gvs[]) >>
      simp[FLOOKUP_UPDATE])
  >> rpt gen_tac >> strip_tac >> Cases_on `inst = h`
  >- (gvs[exact_static_alloca_def] >> qexists `x'` >>
      qpat_x_assum
        `!a p. FLOOKUP (positions |+ (Allocation h.inst_id,x')) a = SOME p ==> _`
        irule >> simp[FLOOKUP_UPDATE])
  >> qpat_x_assum `!inst alloc sz. MEM inst insts /\ _ ==> _` irule
  >> metis_tac[]
QED

Resume complete_alloc_positions_aux_invariant[existing_alloc]:
  `!inst item. MEM inst insts /\ exact_static_alloca inst = SOME item ==>
     MEM item items` by metis_tac[]
  >> qpat_x_assum `!items positions occupied completed. _`
       (qspecl_then [`items`,`positions`,`occupied`,`completed`] mp_tac)
  >> simp[] >> (impl_tac >- metis_tac[])
  >> disch_then (qx_choose_then `final_occupied` strip_assume_tac)
  >> qexists `final_occupied` >> simp[]
  >> rpt gen_tac >> strip_tac >> Cases_on `inst = h`
  >- (gvs[exact_static_alloca_def] >> qexists `x'` >>
      qpat_x_assum `!a p. FLOOKUP positions a = SOME p ==> _` irule >> simp[])
  >> qpat_x_assum `!inst alloc sz. MEM inst insts /\ _ ==> _` irule
  >> metis_tac[]
QED

Resume complete_alloc_positions_aux_invariant[nonalloc]:
  `!inst item. MEM inst insts /\ exact_static_alloca inst = SOME item ==>
     MEM item items` by
    (simp[exact_static_alloca_def, exact_static_alloca_size_def] >> metis_tac[])
  >> qpat_x_assum `!items positions occupied completed. _`
       (qspecl_then [`items`,`positions`,`occupied`,`completed`] mp_tac)
  >> simp[] >> (impl_tac >- metis_tac[])
  >> disch_then (qx_choose_then `final_occupied` strip_assume_tac)
  >> qexists `final_occupied` >> simp[]
  >> rpt gen_tac >> strip_tac >> Cases_on `inst = h`
  >- gvs[]
  >> qpat_x_assum `!inst alloc sz. MEM inst insts /\ _ ==> _` irule
  >> metis_tac[]
QED

Finalise complete_alloc_positions_aux_invariant

Theorem complete_alloc_positions_aux_keys_valid[local]:
  !insts allocs positions occupied completed.
    (!inst alloc sz. MEM inst insts /\
       exact_static_alloca inst = SOME (alloc,sz) ==> MEM alloc allocs) /\
    candidate_alloc_keys_valid allocs positions /\
    complete_alloc_positions_aux insts positions occupied = SOME completed ==>
    candidate_alloc_keys_valid allocs completed
Proof
  Induct
  >- simp[complete_alloc_positions_aux_def]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `h.inst_opcode = ALLOCA`
  >- (Cases_on `exact_static_alloca_size h`
      >> gvs[complete_alloc_positions_aux_def]
      >> Cases_on `FLOOKUP positions (Allocation h.inst_id)`
      >- (Cases_on `checked_first_fit occupied x`
          >> gvs[complete_alloc_positions_aux_def]
          >> first_x_assum irule
          >> conj_tac >- metis_tac[]
          >> qexistsl
               [`if x = 0 then occupied else (x',x)::occupied`,
                `positions |+ (Allocation h.inst_id,x')`]
          >> simp[]
          >> simp[candidate_alloc_keys_valid_def, FDOM_FUPDATE]
          >> qpat_x_assum `!inst alloc sz. _`
               (qspecl_then [`h`,`Allocation h.inst_id`,`x`] mp_tac)
          >> simp[exact_static_alloca_def] >> strip_tac
          >> fs[candidate_alloc_keys_valid_def])
      >> gvs[complete_alloc_positions_aux_def] >> first_x_assum irule
      >> metis_tac[])
  >> gvs[complete_alloc_positions_aux_def, exact_static_alloca_def,
         exact_static_alloca_size_def]
  >> first_x_assum irule >> metis_tac[]
QED


Theorem merge_forced_positions_keys_valid[local]:
  !items allocs forced positions merged.
    (!item. MEM item items ==> MEM (FST item) allocs) /\
    candidate_alloc_keys_valid allocs positions /\
    merge_forced_positions items forced positions = SOME merged ==>
    candidate_alloc_keys_valid allocs merged
Proof
  Induct
  >- simp[merge_forced_positions_def]
  >> rpt gen_tac >> strip_tac >> PairCases_on `h`
  >> Cases_on `FLOOKUP forced (allocation_id h0)`
  >- (gvs[merge_forced_positions_def] >> first_x_assum irule >> metis_tac[])
  >> Cases_on `FLOOKUP positions h0`
  >- (gvs[merge_forced_positions_def]
      >> first_x_assum
           (qspecl_then [`allocs`,`forced`,`positions |+ (h0,x)`,`merged`] mp_tac)
      >> simp[] >> (impl_tac
          >- (simp[candidate_alloc_keys_valid_def, FDOM_FUPDATE] >> conj_tac
              >- (qpat_x_assum `!item. _`
                    (qspec_then `(h0,h1)` mp_tac) >> simp[])
              >> fs[candidate_alloc_keys_valid_def]))
      >> simp[])
  >> Cases_on `x' = x` >> gvs[merge_forced_positions_def]
  >> first_x_assum irule >> metis_tac[]
QED

Theorem complete_alloc_positions_aux_reserved_disjoint:
  !insts items positions occupied completed fixed.
    ALL_DISTINCT (MAP FST items) /\
    (!inst item. MEM inst insts /\ exact_static_alloca inst = SOME item ==>
       MEM item items) /\
    (!r. MEM r fixed ==> MEM r occupied) /\
    (!a sz p r. MEM (a,sz) items /\ FLOOKUP positions a = SOME p /\
       0 < sz /\ MEM r fixed ==>
       reserved_intervals_disjoint (p,sz) r) /\
    complete_alloc_positions_aux insts positions occupied = SOME completed ==>
    !a sz p r. MEM (a,sz) items /\ FLOOKUP completed a = SOME p /\
      0 < sz /\ MEM r fixed ==>
      reserved_intervals_disjoint (p,sz) r
Proof
  Induct
  >- (simp[complete_alloc_positions_aux_def] >> metis_tac[])
  >> rpt gen_tac >> strip_tac
  >> Cases_on `h.inst_opcode = ALLOCA`
  >- (Cases_on `exact_static_alloca_size h`
      >> gvs[complete_alloc_positions_aux_def]
      >> Cases_on `FLOOKUP positions (Allocation h.inst_id)`
      >- (Cases_on `checked_first_fit occupied x`
          >> gvs[complete_alloc_positions_aux_def]
          >> `MEM (Allocation h.inst_id,x) items` by
               (qpat_x_assum `!inst item. _`
                  (qspecl_then [`h`,`(Allocation h.inst_id,x)`] mp_tac) >>
                simp[exact_static_alloca_def])
          >> qpat_x_assum `!items positions occupied completed fixed. _`
               (qspecl_then
                 [`items`,`positions |+ (Allocation h.inst_id,x')`,
                  `if x = 0 then occupied else (x',x)::occupied`,
                  `completed`,`fixed`] mp_tac)
          >> simp[] >> (impl_tac
              >- (conj_tac >- metis_tac[]
                  >> conj_tac
                  >- (rpt strip_tac >> Cases_on `x = 0` >> gvs[])
                  >> rpt gen_tac >> strip_tac
                  >> Cases_on `a = Allocation h.inst_id`
                  >- (`sz = x` by metis_tac[all_distinct_item_key_unique]
                      >> gvs[FLOOKUP_UPDATE]
                      >> qpat_x_assum `checked_first_fit occupied x = SOME x'`
                           (fn th => assume_tac (MATCH_MP checked_first_fit_SOME th))
                      >> gvs[EVERY_MEM])
                  >> gvs[FLOOKUP_UPDATE]
                  >> metis_tac[]))
          >> simp[])
      >> gvs[complete_alloc_positions_aux_def]
      >> qpat_x_assum `!items positions occupied completed fixed. _`
           (qspecl_then [`items`,`positions`,`occupied`,`completed`,`fixed`] mp_tac)
      >> simp[] >> metis_tac[])
  >> gvs[complete_alloc_positions_aux_def, exact_static_alloca_def,
         exact_static_alloca_size_def]
  >> qpat_x_assum `!items positions occupied completed fixed. _`
       (qspecl_then [`items`,`positions`,`occupied`,`completed`,`fixed`] mp_tac)
  >> simp[] >> metis_tac[]
QED

Theorem complete_alloc_positions_aux_success:
  ALL_DISTINCT (MAP FST items) /\
  (!inst item. MEM inst insts /\ exact_static_alloca inst = SOME item ==>
     MEM item items) /\
  reserved_intervals_wf occupied /\
  (!alloc sz pos.
    MEM (alloc,sz) items /\ FLOOKUP positions alloc = SOME pos ==>
    pos + sz < dimword (:256) /\
    (0 < sz ==> MEM (pos,sz) occupied)) /\
  (!alloc1 sz1 pos1 alloc2 sz2 pos2.
    MEM (alloc1,sz1) items /\ MEM (alloc2,sz2) items /\
    FLOOKUP positions alloc1 = SOME pos1 /\
    FLOOKUP positions alloc2 = SOME pos2 /\
    0 < sz1 /\ 0 < sz2 /\ (alloc1,sz1) <> (alloc2,sz2) ==>
    reserved_intervals_disjoint (pos1,sz1) (pos2,sz2)) /\
  complete_alloc_positions_aux insts positions occupied = SOME completed ==>
  (!alloc pos. FLOOKUP positions alloc = SOME pos ==>
     FLOOKUP completed alloc = SOME pos) /\
  (!inst alloc sz. MEM inst insts /\
     exact_static_alloca inst = SOME (alloc,sz) ==>
     ?pos. FLOOKUP completed alloc = SOME pos /\
           pos + sz < dimword (:256)) /\
  (!alloc1 sz1 pos1 alloc2 sz2 pos2.
    MEM (alloc1,sz1) items /\ MEM (alloc2,sz2) items /\
    FLOOKUP completed alloc1 = SOME pos1 /\
    FLOOKUP completed alloc2 = SOME pos2 /\
    0 < sz1 /\ 0 < sz2 /\ (alloc1,sz1) <> (alloc2,sz2) ==>
    reserved_intervals_disjoint (pos1,sz1) (pos2,sz2))
Proof
  strip_tac
  >> `completion_state_inv items positions occupied` by
       (simp[completion_state_inv_def] >> conj_tac
        >- (rpt gen_tac >> strip_tac >>
            qpat_assum
              `!a s p. MEM (a,s) items /\ FLOOKUP positions a = SOME p ==> _`
              (qspecl_then [`alloc`,`sz`,`pos`] mp_tac) >> simp[])
        >> rpt gen_tac >> strip_tac
        >> qpat_x_assum `!alloc1 sz1 pos1 alloc2 sz2 pos2. _`
             (qspecl_then
               [`alloc1`,`sz1`,`pos1`,`alloc2`,`sz2`,`pos2`] mp_tac)
        >> simp[] >> metis_tac[])
  >> qspecl_then [`insts`,`items`,`positions`,`occupied`,`completed`] mp_tac
       complete_alloc_positions_aux_invariant
  >> simp[] >> (impl_tac >- metis_tac[])
  >> disch_then (qx_choose_then `final_occupied` strip_assume_tac)
  >> qpat_x_assum `completion_state_inv items completed final_occupied` mp_tac
  >> simp[completion_state_inv_def] >> strip_tac
  >> conj_tac
  >- (rpt gen_tac >> strip_tac
      >> qpat_x_assum `!inst alloc sz. _`
           (qspecl_then [`inst`,`alloc`,`sz`] mp_tac)
      >> simp[] >> disch_then (qx_choose_then `pos` assume_tac)
      >> qexists `pos` >> simp[]
      >> qpat_x_assum `!alloc sz pos. _`
           (qspecl_then [`alloc`,`sz`,`pos`] mp_tac)
      >> simp[] >> metis_tac[])
  >> rpt gen_tac >> strip_tac
  >> qpat_x_assum `!alloc1 sz1 pos1 alloc2 sz2 pos2. _`

       (qspecl_then [`alloc1`,`sz1`,`pos1`,`alloc2`,`sz2`,`pos2`] mp_tac)
  >> simp[]
QED

Theorem static_alloca_items_exact_MEM[local]:
  static_alloca_items fn = SOME items /\
  MEM inst (fn_insts fn) /\
  exact_static_alloca inst = SOME item ==>
  MEM item items
Proof
  strip_tac
  >> `inst.inst_opcode = ALLOCA` by
       (Cases_on `inst.inst_opcode = ALLOCA`
        >> gvs[exact_static_alloca_def, exact_static_alloca_size_def])
  >> drule static_alloca_items_MEM
  >> metis_tac[]
QED

Theorem checked_preserved_intervals_reserved_disjoint[local]:
  checked_preserved_intervals items positions reserved = SOME occupied ==>
  !a sz p r.
    MEM (a,sz) items /\ FLOOKUP positions a = SOME p /\
    0 < sz /\ MEM r reserved ==>
    reserved_intervals_disjoint (p,sz) r
Proof
  strip_tac >> rpt gen_tac >> strip_tac
  >> qpat_x_assum
       `checked_preserved_intervals items positions reserved = SOME occupied`
       mp_tac
  >> simp[checked_preserved_intervals_def] >> strip_tac
  >> qspecl_then [`items`,`positions`,`reserved`,`[]`,`occupied`] mp_tac
       checked_preserved_intervals_aux_relational
  >> simp[] >> disch_then strip_assume_tac
  >> qpat_x_assum `!item i r. _`
       (qspecl_then [`(a,sz)`,`(p,sz)`,`r`] mp_tac)
  >> simp[positive_preserved_item_intro]
QED

Theorem prepared_aux_completion_certificate[local]:
  static_alloca_items fn = SOME items /\
  ALL_DISTINCT (MAP FST items) /\
  candidate_alloc_keys_valid (MAP FST items) merged /\
  checked_preserved_intervals items merged reserved = SOME added /\
  complete_alloc_positions_aux (fn_insts fn) merged (reserved ++ added) =
    SOME completed ==>
  ((!alloc pos. FLOOKUP merged alloc = SOME pos ==>
      FLOOKUP completed alloc = SOME pos) /\
   (!inst alloc sz. MEM inst (fn_insts fn) /\
      exact_static_alloca inst = SOME (alloc,sz) ==>
      ?pos. FLOOKUP completed alloc = SOME pos /\
            pos + sz < dimword (:256)) /\
   (!alloc1 sz1 pos1 alloc2 sz2 pos2.
      MEM (alloc1,sz1) items /\ MEM (alloc2,sz2) items /\
      FLOOKUP completed alloc1 = SOME pos1 /\
      FLOOKUP completed alloc2 = SOME pos2 /\
      0 < sz1 /\ 0 < sz2 /\ (alloc1,sz1) <> (alloc2,sz2) ==>
      reserved_intervals_disjoint (pos1,sz1) (pos2,sz2))) /\
  candidate_alloc_keys_valid (MAP FST items) completed
Proof
  strip_tac
  >> `reserved_intervals_wf (reserved ++ added) /\
       (!alloc sz pos. MEM (alloc,sz) items /\
          FLOOKUP merged alloc = SOME pos ==>
          pos + sz < dimword (:256) /\
          (0 < sz ==> MEM (pos,sz) added))` by
       metis_tac[checked_preserved_intervals_invariant]
  >> conj_tac
  >- (irule complete_alloc_positions_aux_success
      >> conj_tac
      >- (rpt gen_tac >> strip_tac
          >> irule checked_preserved_intervals_pairwise
          >> simp[]
          >> qexistsl [`alloc1`,`alloc2`,`items`,`added`,`merged`,`reserved`]
          >> simp[] >> metis_tac[])
      >> conj_tac
      >- metis_tac[static_alloca_items_exact_MEM]
      >> conj_tac >- (first_assum ACCEPT_TAC)
      >> qexists `reserved ++ added`
      >> simp[] >> rpt gen_tac >> strip_tac
      >> qpat_x_assum `!alloc sz pos. _`
           (qspecl_then [`alloc`,`sz`,`pos`] mp_tac)
      >> simp[] >> metis_tac[])
  >> qspecl_then
       [`fn_insts fn`,`MAP FST items`,`merged`,`reserved ++ added`,`completed`]
       mp_tac complete_alloc_positions_aux_keys_valid
  >> simp[] >> (impl_tac
      >- (rpt strip_tac >> irule item_key_MEM_MAP >> qexists `sz`
          >> metis_tac[static_alloca_items_exact_MEM]))
  >> simp[]
QED

Theorem prepared_aux_completion_reserved_disjoint[local]:
  static_alloca_items fn = SOME items /\
  ALL_DISTINCT (MAP FST items) /\
  checked_preserved_intervals items merged reserved = SOME added /\
  complete_alloc_positions_aux (fn_insts fn) merged (reserved ++ added) =
    SOME completed ==>
  !a sz p r. MEM (a,sz) items /\ FLOOKUP completed a = SOME p /\
    0 < sz /\ MEM r reserved ==>
    reserved_intervals_disjoint (p,sz) r
Proof
  strip_tac
  >> qspecl_then
       [`fn_insts fn`,`items`,`merged`,`reserved ++ added`,`completed`,`reserved`]
       mp_tac complete_alloc_positions_aux_reserved_disjoint
  >> simp[] >> (impl_tac
      >- (conj_tac
          >- metis_tac[static_alloca_items_exact_MEM]
          >> metis_tac[checked_preserved_intervals_reserved_disjoint]))
  >> simp[]
QED

Theorem completed_lookup_source_reserved[local]:
  static_alloca_items fn = SOME items /\
  candidate_alloc_keys_valid (MAP FST items) completed /\
  (!inst alloc sz. MEM inst (fn_insts fn) /\
     exact_static_alloca inst = SOME (alloc,sz) ==>
     ?pos. FLOOKUP completed alloc = SOME pos /\
           pos + sz < dimword (:256)) /\
  (!a sz p r. MEM (a,sz) items /\ FLOOKUP completed a = SOME p /\
     0 < sz /\ MEM r reserved ==>
     reserved_intervals_disjoint (p,sz) r) ==>
  !alloc pos. FLOOKUP completed alloc = SOME pos ==>
    ?inst sz. MEM inst (fn_insts fn) /\
      exact_static_alloca inst = SOME (alloc,sz) /\
      pos + sz < dimword (:256) /\
      (0 < sz ==> EVERY (reserved_intervals_disjoint (pos,sz)) reserved)
Proof
  strip_tac >> rpt gen_tac >> strip_tac
  >> `MEM alloc (MAP FST items)` by
       (`alloc IN FDOM completed` by (CCONTR_TAC >> fs[FLOOKUP_DEF])
        >> fs[candidate_alloc_keys_valid_def, pred_setTheory.SUBSET_DEF])
  >> qpat_x_assum `MEM alloc (MAP FST items)` mp_tac
  >> simp[MEM_MAP]
  >> disch_then (qx_choose_then `item` strip_assume_tac)
  >> PairCases_on `item` >> gvs[]
  >> drule static_alloca_items_MEM
  >> disch_then (qspec_then `(alloc,item1)` mp_tac)
  >> simp[] >> strip_tac
  >> qpat_x_assum `!inst alloc sz. _`
       (qspecl_then [`inst`,`alloc`,`item1`] mp_tac)
  >> simp[] >> strip_tac
  >> qexistsl [`inst`,`item1`] >> simp[EVERY_MEM]
  >> rpt strip_tac
  >> qpat_x_assum `!a sz p r. _`
       (qspecl_then [`alloc`,`item1`,`pos`,`e`] mp_tac)
  >> simp[]
QED

Theorem source_allocas_pairwise[local]:
  static_alloca_items fn = SOME items /\
  (!alloc1 sz1 pos1 alloc2 sz2 pos2.
     MEM (alloc1,sz1) items /\ MEM (alloc2,sz2) items /\
     FLOOKUP completed alloc1 = SOME pos1 /\
     FLOOKUP completed alloc2 = SOME pos2 /\
     0 < sz1 /\ 0 < sz2 /\ (alloc1,sz1) <> (alloc2,sz2) ==>
     reserved_intervals_disjoint (pos1,sz1) (pos2,sz2)) ==>
  !inst1 inst2 alloc1 sz1 pos1 alloc2 sz2 pos2.
    MEM inst1 (fn_insts fn) /\
    exact_static_alloca inst1 = SOME (alloc1,sz1) /\
    MEM inst2 (fn_insts fn) /\
    exact_static_alloca inst2 = SOME (alloc2,sz2) /\
    FLOOKUP completed alloc1 = SOME pos1 /\
    FLOOKUP completed alloc2 = SOME pos2 /\
    0 < sz1 /\ 0 < sz2 /\ (alloc1,sz1) <> (alloc2,sz2) ==>
    reserved_intervals_disjoint (pos1,sz1) (pos2,sz2)
Proof
  strip_tac >> rpt gen_tac >> strip_tac
  >> `MEM (alloc1,sz1) items` by
       metis_tac[static_alloca_items_exact_MEM]
  >> `MEM (alloc2,sz2) items` by
       metis_tac[static_alloca_items_exact_MEM]
  >> qpat_x_assum `!alloc1 sz1 pos1 alloc2 sz2 pos2. _`
       (qspecl_then [`alloc1`,`sz1`,`pos1`,`alloc2`,`sz2`,`pos2`] mp_tac)
  >> simp[] >> metis_tac[]
QED

Theorem completed_static_fn_positions_wf[local]:
  (!alloc pos. FLOOKUP completed alloc = SOME pos ==>
     ?inst sz. MEM inst (fn_insts fn) /\
       exact_static_alloca inst = SOME (alloc,sz) /\
       pos + sz < dimword (:256) /\
       (0 < sz ==> EVERY (reserved_intervals_disjoint (pos,sz)) reserved)) ==>
  static_fn_positions_wf reserved completed fn
Proof
  strip_tac >> simp[static_fn_positions_wf_def]
  >> rpt gen_tac >> strip_tac
  >> qpat_x_assum `!alloc pos. FLOOKUP completed alloc = SOME pos ==> _`
       (qspecl_then [`Allocation aid`,`pos`] mp_tac)
  >> simp[] >> strip_tac
  >> qpat_x_assum `exact_static_alloca inst = SOME (Allocation aid,sz)` mp_tac
  >> gvs[exact_static_alloca_def, exact_static_alloca_size_def,
         AllCaseEqs(), static_position_wf_def]
  >> strip_tac
  >> qexistsl [`inst`,`sz'`]
  >> gvs[]
QED

Theorem complete_alloc_positions_package[local]:
  static_alloca_items fn = SOME items /\
  merge_forced_positions items forced positions = SOME merged /\
  candidate_alloc_keys_valid (MAP FST items) completed /\
  (!alloc pos. FLOOKUP merged alloc = SOME pos ==>
     FLOOKUP completed alloc = SOME pos) /\
  (!inst alloc sz. MEM inst (fn_insts fn) /\
     exact_static_alloca inst = SOME (alloc,sz) ==>
     ?pos. FLOOKUP completed alloc = SOME pos /\
           pos + sz < dimword (:256)) /\
  (!alloc1 sz1 pos1 alloc2 sz2 pos2.
     MEM (alloc1,sz1) items /\ MEM (alloc2,sz2) items /\
     FLOOKUP completed alloc1 = SOME pos1 /\
     FLOOKUP completed alloc2 = SOME pos2 /\
     0 < sz1 /\ 0 < sz2 /\ (alloc1 = alloc2 ==> sz1 <> sz2) ==>
     reserved_intervals_disjoint (pos1,sz1) (pos2,sz2)) /\
  (!a sz p r. MEM (a,sz) items /\ FLOOKUP completed a = SOME p /\
     0 < sz /\ MEM r reserved ==>
     reserved_intervals_disjoint (p,sz) r) ==>
  (!alloc pos. FLOOKUP positions alloc = SOME pos ==>
     FLOOKUP completed alloc = SOME pos) /\
  (!inst alloc sz. MEM inst (fn_insts fn) /\
     exact_static_alloca inst = SOME (alloc,sz) ==>
     ?pos. FLOOKUP completed alloc = SOME pos /\
           pos + sz < dimword (:256)) /\
  (!alloc pos. FLOOKUP completed alloc = SOME pos ==>
     ?inst sz. MEM inst (fn_insts fn) /\
       exact_static_alloca inst = SOME (alloc,sz) /\
       pos + sz < dimword (:256) /\
       (0 < sz ==> EVERY (reserved_intervals_disjoint (pos,sz)) reserved)) /\
  (!inst1 inst2 alloc1 sz1 pos1 alloc2 sz2 pos2.
     MEM inst1 (fn_insts fn) /\
     exact_static_alloca inst1 = SOME (alloc1,sz1) /\
     MEM inst2 (fn_insts fn) /\
     exact_static_alloca inst2 = SOME (alloc2,sz2) /\
     FLOOKUP completed alloc1 = SOME pos1 /\
     FLOOKUP completed alloc2 = SOME pos2 /\
     0 < sz1 /\ 0 < sz2 /\ (alloc1 = alloc2 ==> sz1 <> sz2) ==>
     reserved_intervals_disjoint (pos1,sz1) (pos2,sz2)) /\
  static_fn_positions_wf reserved completed fn
Proof
  strip_tac
  >> `!alloc pos. FLOOKUP completed alloc = SOME pos ==>
         ?inst sz. MEM inst (fn_insts fn) /\
           exact_static_alloca inst = SOME (alloc,sz) /\
           pos + sz < dimword (:256) /\
           (0 < sz ==>
            EVERY (reserved_intervals_disjoint (pos,sz)) reserved)` by
       (drule completed_lookup_source_reserved
        >> disch_then (qspecl_then [`reserved`,`completed`] mp_tac)
        >> simp[] >> disch_then assume_tac
        >> rpt gen_tac >> strip_tac
        >> qpat_x_assum `!alloc pos. (_ /\ FLOOKUP completed alloc = SOME pos ==> _)`
             (qspecl_then [`alloc`,`pos`] mp_tac)
        >> simp[] >> disch_then irule
        >> conj_tac >- (first_assum ACCEPT_TAC)
        >> first_assum ACCEPT_TAC)
  >> conj_tac
  >- (rpt gen_tac >> strip_tac
      >> drule merge_forced_positions_extends
      >> disch_then (qspecl_then [`alloc`,`pos`] mp_tac)
      >> simp[] >> disch_then drule >> simp[])
  >> conj_tac >- (first_assum ACCEPT_TAC)
  >> conj_asm1_tac >- (first_assum ACCEPT_TAC)
  >> conj_tac
  >- (drule source_allocas_pairwise
      >> disch_then (qspec_then `completed` assume_tac)
      >> rpt gen_tac >> strip_tac
      >> qpat_x_assum
           `!inst1 inst2 alloc1 sz1 pos1 alloc2 sz2 pos2. (_ /\ MEM inst1 _ /\ _ ==> _)`
           (qspecl_then
             [`inst1`,`inst2`,`alloc1`,`sz1`,`pos1`,`alloc2`,`sz2`,`pos2`]
             mp_tac)
      >> simp[] >> disch_then irule
      >> qpat_x_assum
           `!a s p b t q.
              MEM (a,s) items /\ MEM (b,t) items /\
              FLOOKUP completed a = SOME p /\
              FLOOKUP completed b = SOME q /\
              0 < s /\ 0 < t /\ (a = b ==> s <> t) ==>
              reserved_intervals_disjoint (p,s) (q,t)`
           mp_tac
      >> simp[])
  >> irule completed_static_fn_positions_wf >> simp[]
QED

Theorem complete_alloc_positions_success:
  complete_alloc_positions forced reserved fn positions = SOME completed ==>
  (!alloc pos. FLOOKUP positions alloc = SOME pos ==>
     FLOOKUP completed alloc = SOME pos) /\
  (!inst alloc sz. MEM inst (fn_insts fn) /\
     exact_static_alloca inst = SOME (alloc,sz) ==>
     ?pos. FLOOKUP completed alloc = SOME pos /\
           pos + sz < dimword (:256)) /\
  (!alloc pos. FLOOKUP completed alloc = SOME pos ==>
     ?inst sz. MEM inst (fn_insts fn) /\
       exact_static_alloca inst = SOME (alloc,sz) /\
       pos + sz < dimword (:256) /\
       (0 < sz ==>
        EVERY (reserved_intervals_disjoint (pos,sz)) reserved)) /\
  (!inst1 inst2 alloc1 sz1 pos1 alloc2 sz2 pos2.
     MEM inst1 (fn_insts fn) /\
     exact_static_alloca inst1 = SOME (alloc1,sz1) /\
     MEM inst2 (fn_insts fn) /\
     exact_static_alloca inst2 = SOME (alloc2,sz2) /\
     FLOOKUP completed alloc1 = SOME pos1 /\
     FLOOKUP completed alloc2 = SOME pos2 /\
     0 < sz1 /\ 0 < sz2 /\ (alloc1,sz1) <> (alloc2,sz2) ==>
     reserved_intervals_disjoint (pos1,sz1) (pos2,sz2)) /\
  static_fn_positions_wf reserved completed fn
Proof
  simp[complete_alloc_positions_def]
  >> Cases_on `static_alloca_items fn` >> gvs[]
  >> Cases_on `forced_alloc_keys_valid (MAP FST x) forced` >> gvs[]
  >> Cases_on `candidate_alloc_keys_valid (MAP FST x) positions` >> gvs[]
  >> Cases_on `merge_forced_positions x forced positions` >> gvs[]
  >> Cases_on `checked_preserved_intervals x x' reserved` >> gvs[]
  >> strip_tac
  >> `ALL_DISTINCT (MAP FST x)` by
       metis_tac[static_alloca_items_ALL_DISTINCT]
  >> `candidate_alloc_keys_valid (MAP FST x) x'` by
       (qspecl_then [`x`,`MAP FST x`,`forced`,`positions`,`x'`] mp_tac
          merge_forced_positions_keys_valid
        >> simp[] >> (impl_tac
            >- (rpt strip_tac >> PairCases_on `item`
                >> simp[MEM_MAP] >> qexists `(item0,item1)` >> simp[]))
        >> simp[])
  >> drule prepared_aux_completion_certificate
  >> disch_then (qspecl_then [`reserved`,`x'`,`completed`,`x''`] mp_tac)
  >> simp[] >> strip_tac
  >> drule prepared_aux_completion_reserved_disjoint
  >> disch_then (qspecl_then [`reserved`,`x'`,`completed`,`x''`] mp_tac)
  >> simp[] >> strip_tac
  >> drule complete_alloc_positions_package
  >> disch_then assume_tac
  >> qpat_x_assum `!reserved positions merged forced completed. _`
       (qspecl_then [`reserved`,`positions`,`x'`,`forced`,`completed`] mp_tac)
  >> disch_then irule
  >> simp[pairTheory.PAIR_EQ]
  >> conj_tac >- (first_assum ACCEPT_TAC)
  >> conj_tac >- (first_assum ACCEPT_TAC)
  >> first_assum ACCEPT_TAC
QED

Theorem complete_alloc_positions_forced:
  complete_alloc_positions forced reserved fn positions = SOME completed /\
  static_alloca_items fn = SOME items /\
  FLOOKUP forced aid = SOME pos /\
  MEM (Allocation aid) (MAP FST items) ==>
  FLOOKUP completed (Allocation aid) = SOME pos
Proof
  simp[complete_alloc_positions_def]
  >> Cases_on `static_alloca_items fn` >> gvs[]
  >> Cases_on `forced_alloc_keys_valid (MAP FST x) forced` >> gvs[]
  >> Cases_on `candidate_alloc_keys_valid (MAP FST x) positions` >> gvs[]
  >> Cases_on `merge_forced_positions x forced positions` >> gvs[]
  >> Cases_on `checked_preserved_intervals x x' reserved` >> gvs[]
  >> strip_tac
  >> `ALL_DISTINCT (MAP FST x)` by
       metis_tac[static_alloca_items_ALL_DISTINCT]
  >> `candidate_alloc_keys_valid (MAP FST x) x'` by
       (qspecl_then [`x`,`MAP FST x`,`forced`,`positions`,`x'`] mp_tac
          merge_forced_positions_keys_valid
        >> simp[] >> (impl_tac
            >- (rpt strip_tac >> PairCases_on `item`
                >> simp[MEM_MAP] >> qexists `(item0,item1)` >> simp[]))
        >> simp[])
  >> drule prepared_aux_completion_certificate
  >> disch_then (qspecl_then [`reserved`,`x'`,`completed`,`x''`] mp_tac)
  >> simp[] >> strip_tac
  >> `FLOOKUP x' (Allocation aid) = SOME pos` by
       (drule merge_forced_positions_forced_aid >> simp[])
  >> metis_tac[]
QED

Theorem compute_function_layout_fuel_wf:
  compute_function_layout_fuel fuel reserved fn = SOME layout ==>
  concretize_layout_wf reserved fn layout
Proof
  simp[compute_function_layout_fuel_def]
  >> Cases_on `static_alloca_items fn` >> gvs[]
  >> Cases_on `complete_alloc_positions fn.fn_forced_alloc_positions
                 reserved fn
                 (compute_alloc_map_fuel fuel fn
                    (bp_analyze_fuel fuel (cfg_analyze fn) fn)
                    (K []) [] (cfg_analyze fn)
                    (forced_candidate_positions x
                       fn.fn_forced_alloc_positions FEMPTY) reserved)`
  >> gvs[]
  >> Cases_on `global_reserved_end reserved 0` >> gvs[mk_concretize_layout_def]
  >> Cases_on `allocation_eom_fold x' (fn_insts fn) x''`
  >> gvs[mk_concretize_layout_def]
  >> strip_tac >> gvs[]
  >> drule complete_alloc_positions_success
  >> strip_tac
  >> simp[concretize_layout_wf_def]
  >> drule allocation_eom_fold_success >> strip_tac
  >> `x'' < dimword (:256)` by
       (qspecl_then [`reserved`,`0`,`x''`] mp_tac
          global_reserved_end_lt_dimword
        >> simp[])
  >> conj_tac
  >- (qspecl_then [`x'`,`fn_insts fn`,`x''`,`x'³'`] mp_tac
        allocation_eom_fold_lt_dimword
      >> simp[])
  >> rpt gen_tac >> strip_tac
  >> `?size. inst.inst_operands = [Lit size] /\
             exact_static_alloca inst =
               SOME (Allocation inst.inst_id,w2n size)` by
       metis_tac[static_alloca_items_ALLOCA_exact]
  >> qpat_x_assum `!inst alloc sz. _`
       (qspecl_then [`inst`,`Allocation inst.inst_id`,`w2n size'`] mp_tac)
  >> simp[] >> strip_tac
  >> qpat_x_assum `!inst. MEM inst (fn_insts fn) /\ _ ==> _`
       (qspec_then `inst` mp_tac)
  >> simp[] >> strip_tac
  >> qpat_x_assum `allocation_end x' inst = SOME alloc_end` mp_tac
  >> simp[allocation_end_def] >> strip_tac
  >> qpat_x_assum `!alloc pos. FLOOKUP x' alloc = SOME pos ==> _`
       (qspecl_then [`Allocation inst.inst_id`,`pos`] mp_tac)
  >> simp[] >> strip_tac
  >> `w2n size' = sz` by
       metis_tac[static_alloca_items_exact_key_size_unique]
  >> gvs[]
  >> simp[static_position_wf_def]
QED

val _ = export_theory();
