(* Structural proofs for target-checked DRET desugaring. *)
Theory dretDesugarProofs
Ancestors
  dretDesugarDefs irSupply
Libs
  bossLib listTheory

Definition dret_supply_extends_def:
  dret_supply_extends old new <=>
    (?ids. new.irs_used_inst_ids = ids ++ old.irs_used_inst_ids /\
           ALL_DISTINCT ids /\
           EVERY (\id. ~MEM id old.irs_used_inst_ids) ids) /\
    (?vars. new.irs_used_vars = vars ++ old.irs_used_vars /\
            ALL_DISTINCT vars /\
            EVERY (\v. ~MEM v old.irs_used_vars) vars) /\
    new.irs_used_labels = old.irs_used_labels
End

Theorem dret_supply_extends_refl:
  dret_supply_extends s s
Proof
  simp[dret_supply_extends_def] >> qexistsl [`[]`,`[]`] >> simp[]
QED

Theorem all_distinct_append_fresh:
  ALL_DISTINCT xs /\ ALL_DISTINCT ys /\ EVERY (\x. ~MEM x ys) xs ==>
  ALL_DISTINCT (xs ++ ys)
Proof
  Induct_on `xs` >> simp[] >> metis_tac[]
QED

Theorem dret_supply_extends_trans:
  dret_supply_extends s1 s2 /\ dret_supply_extends s2 s3 ==>
  dret_supply_extends s1 s3
Proof
  simp[dret_supply_extends_def] >> rpt strip_tac
  >- (qexists `ids' ++ ids` >> gvs[] >>
      conj_tac
      >- (irule all_distinct_append_fresh >> simp[] >> gvs[EVERY_MEM])
      >> gvs[EVERY_MEM])
  >> qexists `vars' ++ vars` >> gvs[] >>
  conj_tac
  >- (irule all_distinct_append_fresh >> simp[] >> gvs[EVERY_MEM])
  >> gvs[EVERY_MEM]
QED

Theorem fresh_var_extends:
  fresh_ir_var s = (v,s') ==> dret_supply_extends s s'
Proof
  strip_tac >> drule fresh_ir_var_contract >> strip_tac >>
  simp[dret_supply_extends_def] >> gvs[]
QED

Theorem fresh_id_extends:
  ir_supply_inst_ok s /\ fresh_inst_id s = (id,s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  strip_tac >> drule fresh_inst_id_contract >> disch_then drule >> strip_tac >>
  conj_tac >- (simp[dret_supply_extends_def] >> gvs[]) >>
  simp[]
QED

Theorem expand_dret_pairs_empty:
  expand_dret_pairs s cursor [] =
    SOME (DretPairExpansion [] [] cursor s)
Proof
  simp[expand_dret_pairs_def]
QED

Theorem expand_dret_pairs_singleton:
  expand_dret_pairs s cursor [x] = NONE
Proof
  simp[expand_dret_pairs_def]
QED

Theorem expand_dret_pairs_success_fields:
  IS_SOME (expand_dret_pairs s cursor pairs) ==>
  ?emitted dsts final_cursor final_supply.
    expand_dret_pairs s cursor pairs =
      SOME (DretPairExpansion emitted dsts final_cursor final_supply)
Proof
  Cases_on `expand_dret_pairs s cursor pairs` >> simp[] >>
  Cases_on `x` >> simp[]
QED

Theorem expand_dret_pairs_no_dret:
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  EVERY (\i. i.inst_opcode <> DRET) emitted
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs(), venomInstTheory.mk_inst_def]
QED

Theorem replace_dret_inst_no_dret:
  replace_dret_inst s entry_cursor inst = SOME (replacement,s') ==>
  EVERY (\i. i.inst_opcode <> DRET) replacement
Proof
  gvs[replace_dret_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[venomInstTheory.mk_inst_def] >>
  drule expand_dret_pairs_no_dret >> simp[]
QED

Theorem expand_dret_pairs_supply:
  ir_supply_inst_ok s /\
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs()]
  >- simp[dret_supply_extends_refl]
  >> `dret_supply_extends s s1` by (irule fresh_var_extends >> simp[]) >>
  `dret_supply_extends s1 s2` by (irule fresh_var_extends >> simp[]) >>
  `dret_supply_extends s2 s3` by (irule fresh_var_extends >> simp[]) >>
  `ir_supply_inst_ok s3` by
    (qpat_assum `fresh_ir_var s = (plus31_v,s1)`
       (mp_tac o MATCH_MP fresh_ir_var_contract) >>
     qpat_assum `fresh_ir_var s1 = (aligned_v,s2)`
       (mp_tac o MATCH_MP fresh_ir_var_contract) >>
     qpat_assum `fresh_ir_var s2 = (next_v,s3)`
       (mp_tac o MATCH_MP fresh_ir_var_contract) >>
     rpt strip_tac >> gvs[ir_supply_inst_ok_def]) >>
  `dret_supply_extends s3 s4 /\ ir_supply_inst_ok s4` by
    (irule fresh_id_extends >> simp[]) >>
  `dret_supply_extends s4 s5 /\ ir_supply_inst_ok s5` by
    (irule fresh_id_extends >> simp[]) >>
  `dret_supply_extends s5 s6 /\ ir_supply_inst_ok s6` by
    (irule fresh_id_extends >> simp[]) >>
  `dret_supply_extends s6 s7 /\ ir_supply_inst_ok s7` by
    (irule fresh_id_extends >> simp[]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  metis_tac[dret_supply_extends_trans]
QED

val _ = export_theory();
