(* Semantic contracts for the checked static-layout folds. *)

Theory staticLayoutFoldProofs
Ancestors
  staticLayoutDefs arithmetic

Theorem le_max_left[local]:
  !a b. a <= MAX a b
Proof
  simp[MAX_DEF] >> decide_tac
QED

Theorem le_max_right[local]:
  !a b. b <= MAX a b
Proof
  simp[MAX_DEF] >> decide_tac
QED

Theorem max_le[local]:
  !a b c. a <= c /\ b <= c ==> MAX a b <= c
Proof
  simp[MAX_DEF] >> decide_tac
QED

Theorem max_lt_bound[local]:
  !a b c. a < c /\ b < c ==> MAX a b < c
Proof
  simp[MAX_DEF] >> decide_tac
QED

Theorem global_reserved_end_success:
  !reserved e0 e.
    global_reserved_end reserved e0 = SOME e ==>
    EVERY reserved_interval_wf reserved /\ e0 <= e /\
    (!p sz. MEM (p,sz) reserved ==> p + sz <= e) /\
    (!b. e0 <= b /\
         (!p sz. MEM (p,sz) reserved ==> p + sz <= b) ==>
         e <= b)
Proof
  Induct
  >- simp[global_reserved_end_def]
  >> Cases_on `h`
  >> simp[global_reserved_end_def]
  >> rpt gen_tac >> disch_then strip_assume_tac
  >> first_x_assum drule
  >> strip_tac
  >> conj_tac >- simp[]
  >> conj_tac >- metis_tac[le_max_left, le_max_right, max_le, LESS_EQ_TRANS]
  >> conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[le_max_left, le_max_right, max_le, LESS_EQ_TRANS])
  >> rpt strip_tac
  >> first_x_assum irule
  >> conj_tac
  >- metis_tac[le_max_left, le_max_right, max_le, LESS_EQ_TRANS]
  >> rpt strip_tac
  >> irule max_le
  >> simp[]
QED

Theorem global_reserved_end_lt_dimword:
  !reserved e0 e.
    global_reserved_end reserved e0 = SOME e /\
    e0 < dimword (:256) ==>
    e < dimword (:256)
Proof
  Induct
  >- simp[global_reserved_end_def]
  >> Cases_on `h`
  >> simp[global_reserved_end_def, reserved_interval_wf_def]
  >> rpt strip_tac
  >> first_x_assum irule
  >> metis_tac[max_lt_bound]
QED

val _ = export_theory();
