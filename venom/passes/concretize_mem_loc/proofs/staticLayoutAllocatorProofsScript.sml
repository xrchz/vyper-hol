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

val _ = export_theory();
