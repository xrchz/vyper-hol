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


Theorem allocation_eom_fold_success:
  !positions insts e0 e.
    allocation_eom_fold positions insts e0 = SOME e ==>
    e0 <= e /\
    (!inst. MEM inst insts /\ inst.inst_opcode = ALLOCA ==>
      ?alloc_end. allocation_end positions inst = SOME alloc_end /\
                  alloc_end <= e) /\
    (!b. e0 <= b /\
      (!inst alloc_end.
        MEM inst insts /\ inst.inst_opcode = ALLOCA /\
        allocation_end positions inst = SOME alloc_end ==>
        alloc_end <= b) ==>
      e <= b)
Proof
  gen_tac >> Induct
  >- simp[allocation_eom_fold_def]
  >> rpt gen_tac
  >> Cases_on `h.inst_opcode = ALLOCA`
  >- (Cases_on `allocation_end positions h`
      >- simp[allocation_eom_fold_def]
      >> rename1 `allocation_end positions h = SOME alloc_end`
      >> Cases_on `alloc_end < dimword (:256)`
      >- (simp[allocation_eom_fold_def] >> strip_tac
          >> first_x_assum drule >> strip_tac
          >> conj_tac
          >- metis_tac[le_max_left, LESS_EQ_TRANS]
          >> conj_tac
          >- (rpt strip_tac >> gvs[]
              >> metis_tac[le_max_right, LESS_EQ_TRANS])
          >> rpt strip_tac
          >> qpat_x_assum `!b. _ ==> e <= b` irule
          >> conj_tac
          >- (rpt strip_tac
              >> qpat_x_assum `!inst alloc_end'. _ ==> alloc_end' <= b` irule
              >> qexists `inst` >> simp[])
          >> irule max_le
          >> simp[] >> metis_tac[])
      >> simp[allocation_eom_fold_def])
  >> simp[allocation_eom_fold_def]
  >> strip_tac
  >> first_x_assum drule
  >> strip_tac
  >> conj_tac >- metis_tac[]
  >> rpt strip_tac
  >> qpat_x_assum `!b. _ ==> e <= b` irule
  >> simp[]
  >> rpt strip_tac
  >> qpat_x_assum `!inst alloc_end. _ ==> alloc_end <= b` irule
  >> qexists `inst` >> simp[]
QED

Theorem allocation_eom_fold_acc_bound:
  allocation_eom_fold positions insts acc = SOME eom ==> acc <= eom
Proof
  metis_tac[allocation_eom_fold_success]
QED
Theorem allocation_eom_fold_lt_dimword:
  !positions insts e0 e.
    allocation_eom_fold positions insts e0 = SOME e /\
    e0 < dimword (:256) ==>
    e < dimword (:256)
Proof
  gen_tac >> Induct
  >- simp[allocation_eom_fold_def]
  >> rpt gen_tac
  >> Cases_on `h.inst_opcode = ALLOCA`
  >- (Cases_on `allocation_end positions h`
      >- simp[allocation_eom_fold_def]
      >> rename1 `allocation_end positions h = SOME alloc_end`
      >> Cases_on `alloc_end < dimword (:256)`
      >- (simp[allocation_eom_fold_def] >> rpt strip_tac
          >> first_x_assum irule
          >> metis_tac[max_lt_bound])
      >> simp[allocation_eom_fold_def])
  >> simp[allocation_eom_fold_def]
  >> metis_tac[]
QED
val _ = export_theory();
