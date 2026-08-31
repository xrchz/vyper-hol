(* Checked static-layout allocator proof interface. *)

Theory staticLayoutAllocatorProofs
Ancestors
  concretizeMemLocDefs staticLayoutDefs list

Definition reserved_positions_sorted_def:
  reserved_positions_sorted [] = T /\
  reserved_positions_sorted (((pos : num),size)::rs) =
    (EVERY (\((pos' : num),size'). pos <= pos') rs /\
     reserved_positions_sorted rs)
End

Theorem reserved_intervals_disjoint_sym[local]:
  !r1 r2.
    reserved_intervals_disjoint r1 r2 <=>
    reserved_intervals_disjoint r2 r1
Proof
  PairCases >> PairCases >>
  simp[reserved_intervals_disjoint_def] >> metis_tac[]
QED

Theorem MEM_insert_reserved_by_pos[local]:
  !r x rs.
    MEM x (insert_reserved_by_pos r rs) <=> x = r \/ MEM x rs
Proof
  gen_tac >> gen_tac >> Induct_on `rs`
  >- simp[insert_reserved_by_pos_def]
  >> gen_tac >> PairCases_on `h` >> PairCases_on `r` >>
  Cases_on `r0 <= h0` >> gvs[insert_reserved_by_pos_def] >> metis_tac[]
QED

Theorem MEM_sort_reserved_by_pos:
  !x rs.
    MEM x (sort_reserved_by_pos rs) <=> MEM x rs
Proof
  gen_tac >> Induct_on `rs` >>
  simp[sort_reserved_by_pos_def, MEM_insert_reserved_by_pos]
QED

Theorem EVERY_insert_reserved_by_pos[local]:
  !P r rs.
    EVERY P (insert_reserved_by_pos r rs) <=> P r /\ EVERY P rs
Proof
  rpt gen_tac >>
  simp[EVERY_MEM, MEM_insert_reserved_by_pos] >> metis_tac[]
QED

Theorem insert_reserved_by_pos_wf[local]:
  !r rs.
    reserved_interval_wf r /\
    EVERY (reserved_intervals_disjoint r) rs /\
    reserved_intervals_wf rs ==>
    reserved_intervals_wf (insert_reserved_by_pos r rs)
Proof
  gen_tac >> Induct_on `rs`
  >- simp[insert_reserved_by_pos_def, reserved_intervals_wf_def]
  >> gen_tac >> PairCases_on `h` >> PairCases_on `r` >>
  Cases_on `r0 <= h0` >> gvs[insert_reserved_by_pos_def] >> strip_tac
  >- gvs[reserved_intervals_wf_def]
  >> gvs[reserved_intervals_wf_def, EVERY_insert_reserved_by_pos,
         reserved_intervals_disjoint_sym]
QED

Theorem sort_reserved_by_pos_wf:
  !rs.
    reserved_intervals_wf rs ==>
    reserved_intervals_wf (sort_reserved_by_pos rs)
Proof
  Induct >> simp[sort_reserved_by_pos_def, reserved_intervals_wf_def] >>
  gen_tac >> strip_tac >> irule insert_reserved_by_pos_wf >>
  gvs[EVERY_MEM, MEM_sort_reserved_by_pos]
QED

Theorem insert_reserved_by_pos_sorted[local]:
  !r rs.
    reserved_positions_sorted rs ==>
    reserved_positions_sorted (insert_reserved_by_pos r rs)
Proof
  gen_tac >> PairCases_on `r` >> Induct_on `rs`
  >- simp[insert_reserved_by_pos_def, reserved_positions_sorted_def]
  >> gen_tac >> PairCases_on `h` >>
  Cases_on `r0 <= h0` >> gvs[insert_reserved_by_pos_def] >> strip_tac
  >- (gvs[reserved_positions_sorted_def, EVERY_MEM] >>
      gen_tac >> PairCases_on `e` >> gvs[] >> strip_tac >>
      `h0 <= e0` by
        (qpat_x_assum `!x. MEM x rs ==> _`
           (qspec_then `(e0,e1)` mp_tac) >> simp[]) >>
      decide_tac)
  >> gvs[reserved_positions_sorted_def, EVERY_MEM,
         MEM_insert_reserved_by_pos] >>
     gen_tac >> PairCases_on `e` >> gvs[] >> strip_tac >> gvs[] >>
     qpat_x_assum `!x. MEM x rs ==> _`
       (qspec_then `(e0,e1)` mp_tac) >> simp[]
QED

Theorem sort_reserved_by_pos_sorted:
  !rs. reserved_positions_sorted (sort_reserved_by_pos rs)
Proof
  Induct >> simp[sort_reserved_by_pos_def, reserved_positions_sorted_def,
                 insert_reserved_by_pos_sorted]
QED

Theorem EVERY_sort_reserved_by_pos:
  !P rs.
    EVERY P (sort_reserved_by_pos rs) <=> EVERY P rs
Proof
  simp[EVERY_MEM, MEM_sort_reserved_by_pos]
QED
Theorem intervals_after_disjoint[local]:
  !base pos sz rs.
    EVERY (\((rpos : num),rsz). base <= rpos) rs /\
    pos + sz <= base ==>
    EVERY (reserved_intervals_disjoint (pos,sz)) rs
Proof
  simp[EVERY_MEM] >> rpt strip_tac >> PairCases_on `e` >>
  qpat_x_assum `!x. MEM x rs ==> _`
    (qspec_then `(e0,e1)` mp_tac) >>
  simp[reserved_intervals_disjoint_def] >> decide_tac
QED

Theorem checked_first_fit_scan_SOME[local]:
  !rs sz start pos.
    reserved_positions_sorted rs /\
    reserved_intervals_wf rs /\
    checked_first_fit_scan rs sz start = SOME pos ==>
    start <= pos /\
    pos + sz < dimword (:256) /\
    EVERY (reserved_intervals_disjoint (pos,sz)) rs
Proof
  Induct_on `rs`
  >- simp[checked_first_fit_scan_def]
  >> gen_tac >> PairCases_on `h` >> rpt gen_tac >> strip_tac >>
  Cases_on `start + sz >= dimword (:256)`
  >- gvs[checked_first_fit_scan_def]
  >> Cases_on `h0 + h1 <= start`
  >- (gvs[reserved_positions_sorted_def, reserved_intervals_wf_def,
          checked_first_fit_scan_def] >>
      first_x_assum (qspecl_then [`sz`,`start`,`pos`] mp_tac) >>
      simp[] >> strip_tac >>
      simp[reserved_intervals_disjoint_def] >> decide_tac)
  >> Cases_on `start + sz <= h0`
  >- (gvs[reserved_positions_sorted_def, reserved_intervals_wf_def,
          checked_first_fit_scan_def] >>
      conj_tac
      >- (simp[reserved_intervals_disjoint_def] >> decide_tac)
      >> irule intervals_after_disjoint >> qexists `h0` >> simp[])
  >> gvs[reserved_positions_sorted_def, reserved_intervals_wf_def,
         checked_first_fit_scan_def] >>
     first_x_assum (qspecl_then [`sz`,`h0 + h1`,`pos`] mp_tac) >>
     simp[] >> strip_tac >>
     simp[reserved_intervals_disjoint_def] >> decide_tac
QED

Theorem checked_first_fit_SOME:
  !occupied sz pos.
    checked_first_fit occupied sz = SOME pos ==>
    pos + sz < dimword (:256) /\
    EVERY (reserved_intervals_disjoint (pos,sz)) occupied /\
    (0 < sz ==> reserved_intervals_wf ((pos,sz)::occupied))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[checked_first_fit_def] >>
  `0 <= pos /\ pos + sz < dimword (:256) /\
   EVERY (reserved_intervals_disjoint (pos,sz))
     (sort_reserved_by_pos occupied)` by
    (irule checked_first_fit_scan_SOME >>
     simp[sort_reserved_by_pos_sorted, sort_reserved_by_pos_wf]) >>
  gvs[EVERY_sort_reserved_by_pos, reserved_intervals_wf_def,
      reserved_interval_wf_def]
QED

val _ = export_theory();
