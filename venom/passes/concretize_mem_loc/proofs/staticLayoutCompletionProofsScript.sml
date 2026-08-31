(* Checked static-layout completion invariants. *)

Theory staticLayoutCompletionProofs
Ancestors
  staticLayoutAllocatorProofs concretizeMemLocDefs staticLayoutDefs
  list finite_map arithmetic

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

val _ = export_theory();
