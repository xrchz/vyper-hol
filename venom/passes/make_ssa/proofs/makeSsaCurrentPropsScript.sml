(* Structural and supply contracts for the configured MakeSSA adapter. *)
Theory makeSsaCurrentProps
Ancestors
  makeSsaCurrentDefs makeSsaCurrentInduct makeSsaHelper
  cfgTransformProps fcgDefs irSupply list alist

Definition ssa_supply_extends_def:
  ssa_supply_extends s s' <=>
    (!id. MEM id s.irs_used_inst_ids ==> MEM id s'.irs_used_inst_ids) /\
    (!v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars) /\
    s'.irs_used_labels = s.irs_used_labels /\
    s.irs_next_inst <= s'.irs_next_inst /\
    s.irs_next_var <= s'.irs_next_var /\
    s'.irs_next_label = s.irs_next_label
End

Theorem ssa_supply_extends_refl:
  ssa_supply_extends s s
Proof
  simp[ssa_supply_extends_def]
QED

Theorem ssa_supply_extends_trans:
  ssa_supply_extends s s1 /\ ssa_supply_extends s1 s2 ==>
  ssa_supply_extends s s2
Proof
  simp[ssa_supply_extends_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Definition ssa_ids_supply_ok_def:
  ssa_ids_supply_ok s old_ids new_ids s' <=>
    ssa_supply_extends s s' /\
    ir_supply_inst_ok s' /\
    ALL_DISTINCT new_ids /\
    EVERY (\id. MEM id s'.irs_used_inst_ids) new_ids /\
    (!id. MEM id new_ids /\ MEM id s.irs_used_inst_ids ==>
          MEM id old_ids)
End

Definition ssa_vars_covered_def:
  ssa_vars_covered s vars <=>
    EVERY (\v. MEM v s.irs_used_vars) vars
End

Definition ssa_stacks_covered_def:
  ssa_stacks_covered s stacks <=>
    EVERY (\entry. ssa_vars_covered s (SND entry)) stacks
End

Theorem ssa_ids_supply_ok_refl:
  ir_supply_inst_ok s /\ ALL_DISTINCT ids /\
  EVERY (\id. MEM id s.irs_used_inst_ids) ids ==>
  ssa_ids_supply_ok s ids ids s
Proof
  simp[ssa_ids_supply_ok_def, ssa_supply_extends_refl]
QED

Theorem ssa_ids_supply_ok_trans:
  ssa_ids_supply_ok s old_ids mid_ids s1 /\
  ssa_ids_supply_ok s1 mid_ids new_ids s2 ==>
  ssa_ids_supply_ok s old_ids new_ids s2
Proof
  simp[ssa_ids_supply_ok_def, listTheory.EVERY_MEM] >>
  rpt strip_tac
  >- metis_tac[ssa_supply_extends_trans]
  >> `MEM id s1.irs_used_inst_ids` by
       (gvs[ssa_supply_extends_def] >> metis_tac[]) >>
     metis_tac[]
QED

Theorem ssa_ids_supply_ok_append:
  ALL_DISTINCT (old1 ++ old2) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (old1 ++ old2) /\
  ssa_ids_supply_ok s old1 new1 s1 /\
  ssa_ids_supply_ok s1 old2 new2 s2 ==>
  ssa_ids_supply_ok s (old1 ++ old2) (new1 ++ new2) s2
Proof
  rpt strip_tac >>
  qpat_x_assum `ssa_ids_supply_ok s old1 new1 s1` mp_tac >>
  simp[ssa_ids_supply_ok_def] >> strip_tac >>
  qpat_x_assum `ssa_ids_supply_ok s1 old2 new2 s2` mp_tac >>
  simp[ssa_ids_supply_ok_def] >> strip_tac >>
  `!id. MEM id new1 ==> ~MEM id new2` by
    (rpt strip_tac >>
     `MEM id s1.irs_used_inst_ids` by
       (qpat_assum `EVERY (\x. MEM x s1.irs_used_inst_ids) new1` mp_tac >>
        pure_rewrite_tac[listTheory.EVERY_MEM] >>
        disch_then (qspec_then `id` mp_tac) >> simp[]) >>
     `MEM id old2` by metis_tac[] >>
     `MEM id s.irs_used_inst_ids` by
       (qpat_assum
          `EVERY (\x. MEM x s.irs_used_inst_ids) (old1 ++ old2)` mp_tac >>
        pure_rewrite_tac[listTheory.EVERY_MEM] >>
        disch_then (qspec_then `id` mp_tac) >> simp[]) >>
     `MEM id old1` by metis_tac[] >>
     gvs[listTheory.ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `EVERY (\id. MEM id s2.irs_used_inst_ids) new1` by
    (gvs[listTheory.EVERY_MEM, ssa_supply_extends_def] >> metis_tac[]) >>
  gvs[ssa_ids_supply_ok_def, ssa_supply_extends_def,
      listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM] >>
  metis_tac[ssa_supply_extends_trans]
QED

Theorem fresh_inst_id_extends:
  fresh_inst_id s = (id,s') ==> ssa_supply_extends s s'
Proof
  simp[fresh_inst_id_def, ssa_supply_extends_def] >>
  rpt strip_tac >> gvs[] >> simp[]
QED

Theorem fresh_ir_var_extends:
  fresh_ir_var s = (v,s') ==> ssa_supply_extends s s'
Proof
  strip_tac >> drule fresh_ir_var_contract >>
  simp[ssa_supply_extends_def] >> metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ]
QED

Theorem fresh_ir_var_inst_ok:
  ir_supply_inst_ok s /\ fresh_ir_var s = (v,s') ==> ir_supply_inst_ok s'
Proof
  rpt strip_tac >> drule fresh_ir_var_contract >> strip_tac >>
  gvs[ir_supply_inst_ok_def]
QED

Theorem fresh_inst_id_supply_ok:
  ir_supply_inst_ok s /\ fresh_inst_id s = (id,s') ==>
  ssa_ids_supply_ok s [] [id] s'
Proof
  rpt strip_tac >> drule fresh_inst_id_contract >>
  disch_then drule >> strip_tac >>
  simp[ssa_ids_supply_ok_def] >>
  metis_tac[fresh_inst_id_extends]
QED

Theorem fresh_ir_var_covered:
  ssa_vars_covered s vars /\ fresh_ir_var s = (v,s') ==>
  ssa_vars_covered s' (v::vars) /\ ssa_supply_extends s s'
Proof
  rewrite_tac[ssa_vars_covered_def] >> strip_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  conj_tac
  >- (gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >> metis_tac[fresh_ir_var_extends]
QED

Theorem map_insert_phi_absent:
  !bbs lbl phi.
    ~MEM lbl (MAP basic_block_bb_label bbs) ==>
    MAP (\bb. if bb.bb_label = lbl then insert_phi_at_block phi bb else bb) bbs = bbs
Proof
  Induct >> simp[] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem insert_phi_blocks_supply_ok:
  ir_supply_inst_ok s /\
  ALL_DISTINCT (FLAT (MAP block_ir_inst_ids bbs)) /\
  EVERY (\id. MEM id s.irs_used_inst_ids)
    (FLAT (MAP block_ir_inst_ids bbs)) /\
  ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
  fresh_inst_id s = (id,s') ==>
  ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
    (FLAT (MAP block_ir_inst_ids
      (MAP (\bb. if bb.bb_label = lbl then
                    insert_phi_at_block
                      (build_phi_inst_supply id var preds) bb
                  else bb) bbs))) s'
Proof
  Induct_on `bbs`
  >- (simp[ssa_ids_supply_ok_def] >>
      metis_tac[fresh_inst_id_extends, fresh_inst_id_contract])
  >> pop_assum $ mk_asm "ih" >> rpt strip_tac >>
     drule fresh_inst_id_contract >> disch_then drule >> strip_tac >>
     Cases_on `h.bb_label = lbl`
  >- (gvs[ssa_ids_supply_ok_def, block_ir_inst_ids_def,
          makeSsaDefsTheory.insert_phi_at_block_def,
          build_phi_inst_supply_def, map_insert_phi_absent,
          ssa_supply_extends_def, listTheory.EVERY_MEM] >>
      rpt conj_tac >> rpt strip_tac >> gvs[] >> metis_tac[])
  >> `ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
        (FLAT (MAP block_ir_inst_ids
          (MAP (\bb. if bb.bb_label = lbl then
                       insert_phi_at_block
                         (build_phi_inst_supply id var preds) bb
                     else bb) bbs))) s'` by
       (asm "ih" irule >>
        gvs[block_ir_inst_ids_def, listTheory.ALL_DISTINCT_APPEND]) >>
     gvs[ssa_ids_supply_ok_def, block_ir_inst_ids_def,
         listTheory.EVERY_MEM] >>
     rpt conj_tac >> rpt strip_tac >>
     gvs[listTheory.ALL_DISTINCT_APPEND] >> metis_tac[]
QED

Theorem ssa_ids_supply_ok_output:
  ssa_ids_supply_ok s old_ids new_ids s' ==>
  ir_supply_inst_ok s' /\ ALL_DISTINCT new_ids /\
  EVERY (\id. MEM id s'.irs_used_inst_ids) new_ids
Proof
  simp[ssa_ids_supply_ok_def]
QED

Theorem ssa_ids_supply_ok_extends:
  ssa_ids_supply_ok s old_ids new_ids s' ==> ssa_supply_extends s s'
Proof
  simp[ssa_ids_supply_ok_def]
QED

Theorem phi_operand_vars:
  !preds var.
    operand_vars (FLAT (MAP (\l. [Label l; Var var]) preds)) =
    REPLICATE (LENGTH preds) var
Proof
  Induct >> simp[venomInstTheory.operand_vars_def,
                 venomInstTheory.operand_var_def]
QED

Theorem insert_phi_blocks_vars_covered:
  !bbs s id var preds lbl.
    ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
    MEM var s.irs_used_vars ==>
    ssa_vars_covered s
      (FLAT (MAP block_ir_vars
        (MAP (\bb. if bb.bb_label = lbl then
                      insert_phi_at_block
                        (build_phi_inst_supply id var preds) bb
                    else bb) bbs)))
Proof
  Induct
  >- simp[ssa_vars_covered_def]
  >> pop_assum $ mk_asm "ih" >> rpt strip_tac >>
     `ssa_vars_covered s
        (FLAT (MAP block_ir_vars
          (MAP (\bb. if bb.bb_label = lbl then
                        insert_phi_at_block
                          (build_phi_inst_supply id var preds) bb
                      else bb) bbs)))` by
       (asm "ih" irule >>
        gvs[ssa_vars_covered_def, block_ir_vars_def,
            listTheory.EVERY_MEM]) >>

     Cases_on `h.bb_label = lbl` >>
     gvs[ssa_vars_covered_def, block_ir_vars_def,
         makeSsaDefsTheory.insert_phi_at_block_def,
         build_phi_inst_supply_def, inst_ir_vars_def,
         venomInstTheory.inst_uses_def, phi_operand_vars,
         listTheory.EVERY_MEM] >>
     rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ssa_vars_covered_mono:
  ssa_vars_covered s vars /\ ssa_supply_extends s s' ==>
  ssa_vars_covered s' vars
Proof
  simp[ssa_vars_covered_def, ssa_supply_extends_def,
       listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem process_frontiers_supply_ids_ok:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    ir_supply_inst_ok s /\
    ALL_DISTINCT (FLAT (MAP block_ir_inst_ids bbs)) /\
    EVERY (\id. MEM id s.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs)) /\
    ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
      (FLAT (MAP block_ir_inst_ids bbs')) s' /\
    MAP basic_block_bb_label bbs' = MAP basic_block_bb_label bbs
Proof
  Induct
  >- simp[process_frontiers_supply_def, ssa_ids_supply_ok_refl]
  >> pop_assum $ mk_asm "ih" >>
     simp[process_frontiers_supply_def] >> rpt gen_tac >>
     IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule_all >> simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule_all >> simp[])
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
     qmatch_asmsub_abbrev_tac
       `process_frontiers_supply s'' var pm li next_bbs next_rest next_hp fs = _` >>
     `ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
        (FLAT (MAP block_ir_inst_ids next_bbs)) s''` by
       (unabbrev_all_tac >> irule insert_phi_blocks_supply_ok >> simp[]) >>
     `MAP basic_block_bb_label next_bbs =
        MAP basic_block_bb_label bbs` by
       (simp[Abbr `next_bbs`, MAP_MAP_o] >>
        irule MAP_CONG >> rw[] >>
        Cases_on `e.bb_label = h` >>
        simp[makeSsaDefsTheory.insert_phi_at_block_def]) >>
     drule ssa_ids_supply_ok_output >> strip_tac >>
     `ALL_DISTINCT (MAP basic_block_bb_label next_bbs)` by metis_tac[] >>
     `ssa_ids_supply_ok s'' (FLAT (MAP block_ir_inst_ids next_bbs))
        (FLAT (MAP block_ir_inst_ids bbs')) s' /\
      MAP basic_block_bb_label bbs' = MAP basic_block_bb_label next_bbs` by
       (asm "ih" drule_all >> simp[]) >>
     metis_tac[ssa_ids_supply_ok_trans]
QED

Theorem process_frontiers_supply_vars_covered:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
    MEM var s.irs_used_vars /\
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs'))
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule_all >> simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> asm "ih" drule_all >> simp[])
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
     qmatch_asmsub_abbrev_tac
       `process_frontiers_supply s'' var pm li next_bbs next_rest next_hp fs = _` >>
     `ssa_vars_covered s (FLAT (MAP block_ir_vars next_bbs))` by
       (unabbrev_all_tac >> irule insert_phi_blocks_vars_covered >> simp[]) >>
     `ssa_supply_extends s s''` by metis_tac[fresh_inst_id_extends] >>
     `ssa_vars_covered s'' (FLAT (MAP block_ir_vars next_bbs))` by
       metis_tac[ssa_vars_covered_mono] >>
     `MEM var s''.irs_used_vars` by
       (gvs[ssa_supply_extends_def] >> metis_tac[]) >>
     asm "ih" drule_all >> simp[]
QED

Theorem insert_phis_for_var_supply_ok:
  !s var df pm li bbs wl hp bbs' s'.
    ir_supply_inst_ok s /\
    ALL_DISTINCT (FLAT (MAP block_ir_inst_ids bbs)) /\
    EVERY (\id. MEM id s.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs)) /\
    ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
    ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
    MEM var s.irs_used_vars /\
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
      (FLAT (MAP block_ir_inst_ids bbs')) s' /\
    MAP basic_block_bb_label bbs' = MAP basic_block_bb_label bbs /\
    ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs'))
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[]
  >- simp[ssa_ids_supply_ok_refl]
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
     `ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
        (FLAT (MAP block_ir_inst_ids bbs'')) s'' /\
      MAP basic_block_bb_label bbs'' = MAP basic_block_bb_label bbs` by
       (irule process_frontiers_supply_ids_ok >> metis_tac[]) >>
     `ssa_vars_covered s'' (FLAT (MAP block_ir_vars bbs''))` by
       (irule process_frontiers_supply_vars_covered >> metis_tac[]) >>
     drule ssa_ids_supply_ok_output >> strip_tac >>
     `ALL_DISTINCT (MAP basic_block_bb_label bbs'')` by metis_tac[] >>
     `MEM var s''.irs_used_vars` by
       (drule ssa_ids_supply_ok_extends >>
        simp[ssa_supply_extends_def] >> metis_tac[]) >>
     first_x_assum drule_all >> strip_tac >>
     metis_tac[ssa_ids_supply_ok_trans]
QED

Theorem add_phi_nodes_supply_ok:
  !defs s df pm li bbs bbs' s'.
    ir_supply_inst_ok s /\
    ALL_DISTINCT (FLAT (MAP block_ir_inst_ids bbs)) /\
    EVERY (\id. MEM id s.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs)) /\
    ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
    ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
    ssa_vars_covered s (MAP FST defs) /\
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
      (FLAT (MAP block_ir_inst_ids bbs')) s' /\
    MAP basic_block_bb_label bbs' = MAP basic_block_bb_label bbs /\
    ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs'))
Proof
  Induct
  >- simp[add_phi_nodes_supply_def, ssa_ids_supply_ok_refl]
  >> rpt gen_tac >> PairCases_on `h` >>
     simp[add_phi_nodes_supply_def] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
     `MEM h0 s.irs_used_vars` by
       (gvs[ssa_vars_covered_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
     `ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
        (FLAT (MAP block_ir_inst_ids bbs'')) s'' /\
      MAP basic_block_bb_label bbs'' = MAP basic_block_bb_label bbs /\
      ssa_vars_covered s'' (FLAT (MAP block_ir_vars bbs''))` by
       (drule_all insert_phis_for_var_supply_ok >> simp[]) >>
     drule ssa_ids_supply_ok_output >> strip_tac >>
     `ALL_DISTINCT (MAP basic_block_bb_label bbs'')` by metis_tac[] >>
     `ssa_supply_extends s s''` by
       metis_tac[ssa_ids_supply_ok_extends] >>
     `ssa_vars_covered s'' (MAP FST defs)` by
       (gvs[ssa_vars_covered_def, ssa_supply_extends_def,
            listTheory.EVERY_MEM] >> metis_tac[]) >>
     first_x_assum drule_all >> strip_tac >>
     metis_tac[ssa_ids_supply_ok_trans]
QED

Theorem process_frontiers_supply_extends:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    ssa_supply_extends s s'
Proof
  Induct >- simp[process_frontiers_supply_def, ssa_supply_extends_refl] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  `ssa_supply_extends s s''` by metis_tac[fresh_inst_id_extends] >>
  `ssa_supply_extends s'' s'` by (asm "ih" irule >> metis_tac[]) >>
  metis_tac[ssa_supply_extends_trans]
QED

Theorem insert_phis_for_var_supply_extends:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    ssa_supply_extends s s'
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[]
  >- simp[ssa_supply_extends_refl]
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  drule process_frontiers_supply_extends >> strip_tac >>
  metis_tac[ssa_supply_extends_trans]
QED

Theorem add_phi_nodes_supply_extends:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    ssa_supply_extends s s'
Proof
  Induct >> simp[add_phi_nodes_supply_def, ssa_supply_extends_refl] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule insert_phis_for_var_supply_extends >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[ssa_supply_extends_trans]
QED


Theorem ssa_stacks_covered_mono:
  ssa_stacks_covered s stacks /\ ssa_supply_extends s s' ==>
  ssa_stacks_covered s' stacks
Proof
  simp[ssa_stacks_covered_def, ssa_vars_covered_def,
       ssa_supply_extends_def, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem latest_current_name_covered:
  ssa_stacks_covered s stacks /\ MEM var s.irs_used_vars ==>
  MEM (latest_current_name (ctrs,stacks) var) s.irs_used_vars
Proof
  simp[latest_current_name_def] >> rpt CASE_TAC >> gvs[] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  gvs[ssa_stacks_covered_def, ssa_vars_covered_def,
      listTheory.EVERY_MEM] >> strip_tac >>
  qpat_x_assum `!entry. _`
    (qspec_then `(var,h::t)` mp_tac) >> simp[]
QED

Theorem push_current_name_extends:
  push_current_name s rs v = (rs',s',name) ==> ssa_supply_extends s s'
Proof
  PairCases_on `rs` >>
  simp[push_current_name_def] >> rpt CASE_TAC >> gvs[] >>
  simp[ssa_supply_extends_refl] >>
  pairarg_tac >> gvs[] >>
  metis_tac[fresh_ir_var_extends]
QED

Theorem push_current_name_inst_ok:
  ir_supply_inst_ok s /\
  push_current_name s rs v = (rs',s',name) ==>
  ir_supply_inst_ok s'
Proof
  PairCases_on `rs` >>
  simp[push_current_name_def] >> rpt CASE_TAC >> gvs[] >>
  TRY (pairarg_tac >> gvs[]) >>
  metis_tac[fresh_ir_var_inst_ok]
QED

Theorem push_current_name_covered:
  ssa_stacks_covered s (SND rs) /\
  MEM v s.irs_used_vars /\
  push_current_name s rs v = (rs',s',name) ==>
  ssa_stacks_covered s' (SND rs') /\
  MEM name s'.irs_used_vars /\
  ssa_supply_extends s s'
Proof
  PairCases_on `rs` >>
  simp[push_current_name_def] >> rpt CASE_TAC >> gvs[] >>
  TRY (pairarg_tac >> gvs[]) >>
  simp[ssa_stacks_covered_def, ssa_vars_covered_def,
       listTheory.EVERY_MEM, ssa_supply_extends_refl] >>
  rpt strip_tac >> gvs[MEM_FILTER] >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  TRY (qpat_x_assum `!entry'. _`
         (qspec_then `entry` mp_tac) >> simp[] >> NO_TAC) >>
  TRY (qpat_x_assum `!entry'. _` drule >> simp[] >> NO_TAC) >>
  imp_res_tac fresh_ir_var_contract >>
  imp_res_tac fresh_ir_var_extends >>
  gvs[ssa_supply_extends_def] >>
  TRY (qpat_x_assum `!entry'. _`
         (qspec_then `entry` mp_tac) >> simp[] >> NO_TAC) >>
  TRY (qpat_x_assum `!entry'. _` drule >> simp[] >> NO_TAC) >>
  metis_tac[]
QED



Theorem rename_current_operands_covered:
  !ops s ctrs stacks.
    ssa_vars_covered s (operand_vars ops) /\
    ssa_stacks_covered s stacks ==>
    ssa_vars_covered s
      (operand_vars (rename_current_operands (ctrs,stacks) ops))
Proof
  Induct >- simp[rename_current_operands_def, venomInstTheory.operand_vars_def,
                  ssa_vars_covered_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[rename_current_operands_def, venomInstTheory.operand_vars_def,
       venomInstTheory.operand_var_def, ssa_vars_covered_def] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`s`,`ctrs`,`stacks`] mp_tac) >>
  simp[ssa_vars_covered_def] >>
  metis_tac[latest_current_name_covered]
QED


Theorem update_current_phi_for_pred_covered:
  !ops rs cur s.
    ssa_vars_covered s (operand_vars ops) /\
    ssa_stacks_covered s (SND rs) ==>
    ssa_vars_covered s
      (operand_vars (update_current_phi_for_pred rs cur ops))
Proof
  measureInduct_on `LENGTH ops` >> rpt gen_tac >> strip_tac >>
  Cases_on `ops`
  >- simp[update_current_phi_for_pred_def,
           venomInstTheory.operand_vars_def, ssa_vars_covered_def] >>
  rename1 `op::rest` >> Cases_on `rest`
  >- (Cases_on `op` >>
      gvs[update_current_phi_for_pred_def,
          venomInstTheory.operand_vars_def,
          venomInstTheory.operand_var_def,
          ssa_vars_covered_def]) >>
  rename1 `op1::op2::rest` >>
  Cases_on `op1` >> Cases_on `op2` >>
  simp[update_current_phi_for_pred_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def,
       ssa_vars_covered_def] >>
  first_x_assum (qspec_then `rest` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`rs`,`cur`,`s`] mp_tac) >>
  simp[ssa_vars_covered_def] >>
  (impl_tac >-
    gvs[ssa_vars_covered_def, venomInstTheory.operand_vars_def,
        venomInstTheory.operand_var_def]) >>
  rpt strip_tac >>
  gvs[ssa_vars_covered_def, venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def] >>
  IF_CASES_TAC >>
  gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >>
  PairCases_on `rs` >> irule latest_current_name_covered >> gvs[]
QED


Theorem update_current_phi_insts_vars_covered:
  !insts rs cur s.
    ssa_vars_covered s (FLAT (MAP inst_ir_vars insts)) /\
    ssa_stacks_covered s (SND rs) ==>
    ssa_vars_covered s
      (FLAT (MAP inst_ir_vars
        (MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else inst with inst_operands :=
                        update_current_phi_for_pred rs cur inst.inst_operands)
             insts)))
Proof
  Induct
  >- simp[ssa_vars_covered_def] >>
  rpt gen_tac >> simp[] >> rpt strip_tac >>
  `ssa_vars_covered s (inst_ir_vars h)` by
    gvs[ssa_vars_covered_def, listTheory.EVERY_APPEND] >>
  `ssa_vars_covered s (FLAT (MAP inst_ir_vars insts))` by
    gvs[ssa_vars_covered_def, listTheory.EVERY_APPEND] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[inst_ir_vars_def, venomInstTheory.inst_uses_def,
      ssa_vars_covered_def, listTheory.EVERY_APPEND] >>
  rewrite_tac[GSYM ssa_vars_covered_def] >>
  PairCases_on `rs` >>
  irule update_current_phi_for_pred_covered >>
  gvs[ssa_vars_covered_def]
QED


Theorem replace_block_vars_covered:
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
  ssa_vars_covered s (block_ir_vars new_bb) ==>
  ssa_vars_covered s
    (FLAT (MAP block_ir_vars (replace_block lbl new_bb bbs)))
Proof
  simp[ssa_vars_covered_def, listTheory.EVERY_MEM,
       cfgTransformTheory.replace_block_def, listTheory.MEM_FLAT,
       listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem FOLDL_preserves:
  !xs step acc P.
    (!a x. P a ==> P (step a x)) /\ P acc ==>
    P (FOLDL step acc xs)
Proof
  Induct >> simp[] >> metis_tac[]
QED

Theorem update_current_succ_phis_vars_covered:
  !succs rs cur bbs s.
    ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
    ssa_stacks_covered s (SND rs) ==>
    ssa_vars_covered s (FLAT (MAP block_ir_vars
      (update_current_succ_phis rs cur bbs succs)))
Proof
  Induct >- simp[update_current_succ_phis_def] >>
  rpt gen_tac >> strip_tac >>
  simp[update_current_succ_phis_def] >>
  Cases_on `lookup_block h bbs` >> gvs[]
  >- (first_x_assum drule_all >>
      disch_then (qspec_then `cur` mp_tac) >>
      simp[update_current_succ_phis_def]) >>
  `MEM x bbs` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `ssa_vars_covered s (block_ir_vars x)` by
    (gvs[ssa_vars_covered_def, listTheory.EVERY_MEM,
         listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]) >>
  `ssa_vars_covered s
     (block_ir_vars
       (x with bb_instructions :=
         MAP (\inst. if inst.inst_opcode <> PHI then inst
                      else inst with inst_operands :=
                        update_current_phi_for_pred rs cur
                          inst.inst_operands)
             x.bb_instructions))` by
    (gvs[block_ir_vars_def] >>
     irule update_current_phi_insts_vars_covered >> simp[]) >>
  `ssa_vars_covered s
     (FLAT (MAP block_ir_vars
       (replace_block h
         (x with bb_instructions :=
           MAP (\inst. if inst.inst_opcode <> PHI then inst
                        else inst with inst_operands :=
                          update_current_phi_for_pred rs cur
                            inst.inst_operands)
               x.bb_instructions) bbs)))` by
    (irule replace_block_vars_covered >> simp[]) >>
  first_x_assum drule_all >>
  disch_then (qspec_then `cur` mp_tac) >>
  simp[update_current_succ_phis_def]
QED


Theorem rename_current_outputs_extends:
  !vs s rs rs' s' outs.
    rename_current_outputs s rs vs = (rs',s',outs) ==>
    ssa_supply_extends s s'
Proof
  Induct >- simp[rename_current_outputs_def, ssa_supply_extends_refl] >>
  pop_assum $ mk_asm "ih" >>
  rpt gen_tac >> simp[rename_current_outputs_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule push_current_name_extends >> strip_tac >>
  asm "ih" drule >> strip_tac >>
  metis_tac[ssa_supply_extends_trans]
QED

Theorem rename_current_outputs_inst_ok:
  !vs s rs rs' s' outs.
    ir_supply_inst_ok s /\
    rename_current_outputs s rs vs = (rs',s',outs) ==>
    ir_supply_inst_ok s'
Proof
  Induct >- simp[rename_current_outputs_def] >>
  pop_assum $ mk_asm "ih" >>
  rpt gen_tac >> simp[rename_current_outputs_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule_all push_current_name_inst_ok >> strip_tac >>
  asm "ih" drule_all >> simp[]
QED


Theorem rename_current_outputs_covered:
  !vs s rs rs' s' outs.
    ssa_vars_covered s vs /\
    ssa_stacks_covered s (SND rs) /\
    rename_current_outputs s rs vs = (rs',s',outs) ==>
    ssa_vars_covered s' outs /\
    ssa_stacks_covered s' (SND rs') /\
    ssa_supply_extends s s'
Proof
  Induct
  >- simp[rename_current_outputs_def, ssa_vars_covered_def,
           ssa_supply_extends_refl] >>
  pop_assum $ mk_asm "ih" >> rpt gen_tac >>
  simp[rename_current_outputs_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  rename [`push_current_name s rs h = (rs1,s1,name)`,
          `rename_current_outputs s1 rs1 vs = (rs2,s2,rest)`] >>
  `MEM h s.irs_used_vars` by gvs[ssa_vars_covered_def] >>
  `ssa_stacks_covered s1 (SND rs1) /\
   MEM name s1.irs_used_vars /\
   ssa_supply_extends s s1` by
    (drule_all push_current_name_covered >> simp[]) >>
  `ssa_vars_covered s1 vs` by
    (gvs[ssa_vars_covered_def, ssa_supply_extends_def,
         listTheory.EVERY_MEM] >> metis_tac[]) >>
  `ssa_vars_covered s2 rest /\
   ssa_stacks_covered s2 (SND rs2) /\
   ssa_supply_extends s1 s2` by
    (asm "ih" drule_all >> simp[]) >>
  `MEM name s2.irs_used_vars` by
    (gvs[ssa_supply_extends_def] >> metis_tac[]) >>
  `ssa_supply_extends s s2` by
    (irule ssa_supply_extends_trans >> qexists `s1` >> simp[]) >>
  gvs[ssa_vars_covered_def]
QED


Theorem rename_current_inst_extends:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  ssa_supply_extends s s'
Proof
  simp[rename_current_inst_def] >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule rename_current_outputs_extends >> simp[]
QED

Theorem rename_current_inst_inst_ok:
  ir_supply_inst_ok s /\
  rename_current_inst s rs inst = (rs',s',inst') ==>
  ir_supply_inst_ok s'
Proof
  simp[rename_current_inst_def] >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule_all rename_current_outputs_inst_ok >> simp[]
QED



Theorem rename_current_inst_covered:
  ssa_vars_covered s (inst_ir_vars inst) /\
  ssa_stacks_covered s (SND rs) /\
  rename_current_inst s rs inst = (rs',s',inst') ==>
  ssa_vars_covered s' (inst_ir_vars inst') /\
  ssa_stacks_covered s' (SND rs') /\
  ssa_supply_extends s s'
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  rename1 `rename_current_outputs s rs inst.inst_outputs = (rs1,s1,outs1)`
  >- (`ssa_vars_covered s inst.inst_outputs` by
        gvs[inst_ir_vars_def, ssa_vars_covered_def,
            listTheory.EVERY_APPEND] >>
      `ssa_vars_covered s1 outs1 /\
       ssa_stacks_covered s1 (SND rs1) /\
       ssa_supply_extends s s1` by
        (drule_all rename_current_outputs_covered >> simp[]) >>
      gvs[inst_ir_vars_def, venomInstTheory.inst_uses_def,
          ssa_vars_covered_def, listTheory.EVERY_APPEND,
          ssa_supply_extends_def, listTheory.EVERY_MEM] >>
      metis_tac[])
  >> `ssa_vars_covered s inst.inst_outputs` by
       gvs[inst_ir_vars_def, ssa_vars_covered_def,
           listTheory.EVERY_APPEND] >>
     `ssa_vars_covered s
        (operand_vars (rename_current_operands rs inst.inst_operands))` by
       (PairCases_on `rs` >> irule rename_current_operands_covered >>
        gvs[inst_ir_vars_def, venomInstTheory.inst_uses_def,
            ssa_vars_covered_def, listTheory.EVERY_APPEND]) >>
     `ssa_vars_covered s1 outs1 /\
      ssa_stacks_covered s1 (SND rs1) /\
      ssa_supply_extends s s1` by
       (drule_all rename_current_outputs_covered >> simp[]) >>
     gvs[inst_ir_vars_def, venomInstTheory.inst_uses_def,
         ssa_vars_covered_def, listTheory.EVERY_APPEND,
         ssa_supply_extends_def, listTheory.EVERY_MEM] >>
     metis_tac[]
QED

Theorem rename_current_block_insts_extends:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    ssa_supply_extends s s'
Proof
  Induct >- simp[rename_current_block_insts_def, ssa_supply_extends_refl] >>
  pop_assum $ mk_asm "ih" >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule rename_current_inst_extends >> strip_tac >>
  asm "ih" drule >> strip_tac >>
  metis_tac[ssa_supply_extends_trans]
QED

Theorem rename_current_block_insts_inst_ok:
  !insts s rs rs' s' insts'.
    ir_supply_inst_ok s /\
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    ir_supply_inst_ok s'
Proof
  Induct >- simp[rename_current_block_insts_def] >>
  pop_assum $ mk_asm "ih" >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule_all rename_current_inst_inst_ok >> strip_tac >>
  asm "ih" drule_all >> simp[]
QED


Theorem rename_current_block_insts_covered:
  !insts s rs rs' s' insts'.
    ssa_vars_covered s (FLAT (MAP inst_ir_vars insts)) /\
    ssa_stacks_covered s (SND rs) /\
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    ssa_vars_covered s' (FLAT (MAP inst_ir_vars insts')) /\
    ssa_stacks_covered s' (SND rs') /\
    ssa_supply_extends s s'
Proof
  Induct
  >- simp[rename_current_block_insts_def, ssa_vars_covered_def,
           ssa_supply_extends_refl] >>
  pop_assum $ mk_asm "ih" >> rpt gen_tac >>
  simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  rename [`rename_current_inst s rs h = (rs1,s1,inst1)`,
          `rename_current_block_insts s1 rs1 insts = (rs2,s2,rest)`] >>
  `ssa_vars_covered s (inst_ir_vars h)` by
    gvs[ssa_vars_covered_def, listTheory.EVERY_APPEND] >>
  `ssa_vars_covered s1 (inst_ir_vars inst1) /\
   ssa_stacks_covered s1 (SND rs1) /\
   ssa_supply_extends s s1` by
    (drule_all rename_current_inst_covered >> simp[]) >>
  `ssa_vars_covered s1 (FLAT (MAP inst_ir_vars insts))` by
    (gvs[ssa_vars_covered_def, ssa_supply_extends_def,
         listTheory.EVERY_APPEND, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `ssa_vars_covered s2 (FLAT (MAP inst_ir_vars rest)) /\
   ssa_stacks_covered s2 (SND rs2) /\
   ssa_supply_extends s1 s2` by
    (asm "ih" drule_all >> simp[]) >>
  `ssa_vars_covered s2 (inst_ir_vars inst1)` by
    (gvs[ssa_vars_covered_def, ssa_supply_extends_def,
         listTheory.EVERY_MEM] >> metis_tac[]) >>
  `ssa_supply_extends s s2` by
    (irule ssa_supply_extends_trans >> qexists `s1` >> simp[]) >>
  gvs[ssa_vars_covered_def, listTheory.EVERY_APPEND]
QED


Theorem rename_current_inst_id:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  inst'.inst_id = inst.inst_id
Proof
  simp[rename_current_inst_def] >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >> gvs[]
QED

Theorem rename_current_block_insts_ids:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    MAP (\inst. inst.inst_id) insts' = MAP (\inst. inst.inst_id) insts
Proof
  Induct >- simp[rename_current_block_insts_def] >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule rename_current_inst_id >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem rename_current_blocks_extends:
  (!s rs bbs sm t ctrs s' bbs'.
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     ssa_supply_extends s s') /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     ssa_supply_extends s s')
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
        ssa_supply_extends s s') /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
        ssa_supply_extends s s')`
  >- metis_tac[]
  >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()]
      >- simp[ssa_supply_extends_refl]
      >> pairarg_tac >> gvs[] >>
      drule rename_current_block_insts_extends >> strip_tac >>
      first_x_assum drule >> strip_tac >>
      metis_tac[ssa_supply_extends_trans])
  >- simp[rename_current_blocks_def, ssa_supply_extends_refl]
  >> rpt strip_tac >>
  gvs[rename_current_blocks_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[ssa_supply_extends_trans]
QED

Theorem rename_current_blocks_inst_supply_ok:
  (!s rs bbs sm t ctrs s' bbs'.
     ir_supply_inst_ok s /\
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     ir_supply_inst_ok s') /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     ir_supply_inst_ok s /\
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     ir_supply_inst_ok s')
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        ir_supply_inst_ok s /\
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
        ir_supply_inst_ok s') /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        ir_supply_inst_ok s /\
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
        ir_supply_inst_ok s')`
  >- metis_tac[]
  >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()]
      >> pairarg_tac >> gvs[] >>
      drule_all rename_current_block_insts_inst_ok >> strip_tac >>
      first_x_assum drule_all >> simp[])
  >- simp[rename_current_blocks_def]
  >> rpt strip_tac >>
  gvs[rename_current_blocks_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED


Theorem make_ssa_current_fn_extends:
  make_ssa_current_fn s fn = (fn',s') ==> ssa_supply_extends s s'
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[]
  >- simp[ssa_supply_extends_refl]
  >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
     drule add_phi_nodes_supply_extends >> strip_tac >>
     drule (CONJUNCT1 rename_current_blocks_extends) >> strip_tac >>
     metis_tac[ssa_supply_extends_trans]
QED


Theorem insert_phis_for_var_supply_labels:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[]
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
     drule process_frontiers_supply_labels >> strip_tac >>
     first_x_assum drule >> simp[]
QED

Theorem add_phi_nodes_supply_labels:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule insert_phis_for_var_supply_labels >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem FOLDL_map_invariant:
  !xs step acc f.
    (!a x. MAP f (step a x) = MAP f a) ==>
    MAP f (FOLDL step acc xs) = MAP f acc
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem update_current_succ_phis_labels:
  !succs rs current_label bbs.
    MAP (\bb. bb.bb_label)
      (update_current_succ_phis rs current_label bbs succs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  rpt gen_tac >> simp[update_current_succ_phis_def] >>
  irule FOLDL_map_invariant >> rpt strip_tac >>
  Cases_on `lookup_block x a` >> gvs[] >>
  drule lookup_block_label >> strip_tac >>
  simp[fn_labels_replace_block]
QED

Theorem rename_current_blocks_labels:
  (!s rs bbs sm t ctrs s' bbs'.
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs) /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs)
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
        MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs) /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
        MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs)`
  >- metis_tac[]
  >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()]
      >> pairarg_tac >> gvs[] >>
         drule lookup_block_label >> strip_tac >>
         first_x_assum drule >> strip_tac >>
         gvs[update_current_succ_phis_labels, fn_labels_replace_block])
  >- simp[rename_current_blocks_def]
  >> rpt strip_tac >> gvs[rename_current_blocks_def] >>
     pairarg_tac >> gvs[] >>
     first_x_assum drule >> strip_tac >>
     first_x_assum drule >> strip_tac >>
     metis_tac[]
QED

Theorem make_ssa_current_fn_metadata:
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn /\
  fn_fmp_convention_eq fn' fn
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[]
  >- simp[venomInstTheory.fn_identity_metadata_eq_def, venomInstTheory.fn_static_input_eq_def,
          venomInstTheory.fn_static_layout_eq_def, venomInstTheory.fn_fmp_convention_eq_def]
  >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
     gvs[venomInstTheory.fn_identity_metadata_eq_def, venomInstTheory.fn_static_input_eq_def,
         venomInstTheory.fn_static_layout_eq_def, venomInstTheory.fn_fmp_convention_eq_def]
QED

Theorem make_ssa_current_fn_labels:
  make_ssa_current_fn s fn = (fn',s') ==>
  MAP (\bb. bb.bb_label) fn'.fn_blocks =
  MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[]
  >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
     drule add_phi_nodes_supply_labels >> strip_tac >>
     drule (CONJUNCT1 rename_current_blocks_labels) >> strip_tac >>
     gvs[]
QED

Theorem make_ssa_current_fn_structural:
  make_ssa_current_fn s fn = (fn',s') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn /\
  fn_fmp_convention_eq fn' fn /\
  MAP (\bb. bb.bb_label) fn'.fn_blocks =
  MAP (\bb. bb.bb_label) fn.fn_blocks
Proof
  metis_tac[make_ssa_current_fn_metadata, make_ssa_current_fn_labels]
QED

Theorem rename_current_operands_label_head:
  rename_current_operands rs (Label lbl::ops) =
  Label lbl::rename_current_operands rs ops
Proof
  simp[rename_current_operands_def]
QED

Theorem rename_current_inst_invoke_target:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  MAP FST (get_invoke_targets [inst']) =
  MAP FST (get_invoke_targets [inst])
Proof
  simp[rename_current_inst_def] >> IF_CASES_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[get_invoke_targets_def]
  >- (Cases_on `inst.inst_operands` >> gvs[rename_current_operands_def] >>
      rename1 `op::ops` >> Cases_on `op` >>
      gvs[rename_current_operands_def])
QED

Theorem invoke_target_labels_cons:
  MAP FST (get_invoke_targets (inst::insts)) =
  MAP FST (get_invoke_targets [inst]) ++
  MAP FST (get_invoke_targets insts)
Proof
  simp[get_invoke_targets_def] >> rpt CASE_TAC >> gvs[]
QED

Theorem rename_current_block_insts_invoke_targets:
  !insts s rs rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    MAP FST (get_invoke_targets insts') =
    MAP FST (get_invoke_targets insts)
Proof
  Induct >- simp[rename_current_block_insts_def, get_invoke_targets_def] >>
  pop_assum $ mk_asm "ih" >> rpt gen_tac >>
  simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule rename_current_inst_invoke_target >> strip_tac >>
  asm "ih" drule >> strip_tac >> gvs[] >>
  once_rewrite_tac[invoke_target_labels_cons] >> simp[]
QED

Definition block_invoke_labels_def:
  block_invoke_labels bb =
    MAP FST (get_invoke_targets bb.bb_instructions)
End


Theorem MAP_if_not_mem:
  !xs p (y:'a).
    (!x. MEM x xs ==> ~p x) ==>
    MAP (\x. if p x then y else x) xs = xs
Proof
  Induct >> simp[] >> metis_tac[]
QED

Theorem MAP_replace_at_FIND_distinct:
  !xs (key:'a -> 'b) k old new (f:'a -> 'c).
    ALL_DISTINCT (MAP key xs) /\
    FIND (\x. key x = k) xs = SOME old /\
    f new = f old ==>
    MAP f (MAP (\x. if key x = k then new else x) xs) = MAP f xs
Proof
  Induct >- simp[] >> rpt gen_tac >>
  simp[listTheory.FIND_thm] >> rpt strip_tac >>
  Cases_on `key h = k`
  >- (gvs[MEM_MAP] >>
      `MAP (\x. if key x = k then new else x) xs = xs` by
        (ho_match_mp_tac MAP_if_not_mem >> metis_tac[]) >>
      simp[])
  >> gvs[MEM_MAP] >>
  `MAP (\x. if key x = key h then new else x) xs = xs` by
    (ho_match_mp_tac MAP_if_not_mem >> rpt strip_tac >>
     qpat_x_assum `!y. key h = key y ==> ~MEM y xs`
       (qspec_then `x` mp_tac) >> simp[]) >>
  simp[]
QED

Theorem bb_label_eta:
  (\bb. bb.bb_label) = basic_block_bb_label
Proof
  simp[FUN_EQ_THM]
QED

Theorem replace_block_invoke_labels_distinct:
  !bbs lbl bb bb'.
    ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
    lookup_block lbl bbs = SOME bb /\
    bb'.bb_label = lbl /\
    block_invoke_labels bb' = block_invoke_labels bb ==>
    MAP block_invoke_labels (replace_block lbl bb' bbs) =
    MAP block_invoke_labels bbs
Proof
  rpt strip_tac >>
  simp[cfgTransformTheory.replace_block_def] >>
  ho_match_mp_tac MAP_replace_at_FIND_distinct >>
  qexists `bb` >> conj_tac
  >- (qpat_assum `ALL_DISTINCT _` mp_tac >> simp[GSYM bb_label_eta])
  >> gvs[venomInstTheory.lookup_block_def]
QED

Theorem replace_block_inst_ids_distinct:
  !bbs lbl bb bb'.
    ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
    lookup_block lbl bbs = SOME bb /\
    bb'.bb_label = lbl /\
    block_ir_inst_ids bb' = block_ir_inst_ids bb ==>
    FLAT (MAP block_ir_inst_ids (replace_block lbl bb' bbs)) =
    FLAT (MAP block_ir_inst_ids bbs)
Proof
  rpt strip_tac >>
  simp[cfgTransformTheory.replace_block_def] >>
  `MAP block_ir_inst_ids
      (MAP (\x. if basic_block_bb_label x = lbl then bb' else x) bbs) =
    MAP block_ir_inst_ids bbs` by
    (ho_match_mp_tac MAP_replace_at_FIND_distinct >>
     qexists `bb` >> conj_tac
     >- (qpat_assum `ALL_DISTINCT _` mp_tac >> simp[GSYM bb_label_eta])
     >> gvs[venomInstTheory.lookup_block_def]) >>
  simp[]
QED

Theorem invoke_target_labels_append:
  !xs ys.
    MAP FST (get_invoke_targets (xs ++ ys)) =
    MAP FST (get_invoke_targets xs) ++ MAP FST (get_invoke_targets ys)
Proof
  Induct >- simp[get_invoke_targets_def] >> rpt gen_tac >>
  pure_once_rewrite_tac[APPEND] >>
  once_rewrite_tac[invoke_target_labels_cons] >> simp[]
QED

Theorem fn_insts_blocks_invoke_labels:
  !bbs.
    MAP FST (get_invoke_targets (fn_insts_blocks bbs)) =
    FLAT (MAP block_invoke_labels bbs)
Proof
  Induct >>
  simp[venomInstTheory.fn_insts_blocks_def, block_invoke_labels_def,
       invoke_target_labels_append, get_invoke_targets_def]
QED

Theorem fcg_scan_function_invoke_labels:
  MAP FST (fcg_scan_function fn) =
  FLAT (MAP block_invoke_labels fn.fn_blocks)
Proof
  simp[fcg_scan_function_def, venomInstTheory.fn_insts_def,
       fn_insts_blocks_invoke_labels]
QED

Definition invoke_blocks_subset_def[local]:
  invoke_blocks_subset input output <=>
    EVERY (\t. MEM t (FLAT (MAP block_invoke_labels input)))
          (FLAT (MAP block_invoke_labels output))
End

Theorem invoke_blocks_subset_refl[local]:
  invoke_blocks_subset bbs bbs
Proof
  simp[invoke_blocks_subset_def,listTheory.EVERY_MEM]
QED

Theorem invoke_blocks_subset_trans[local]:
  invoke_blocks_subset bbs0 bbs1 /\ invoke_blocks_subset bbs1 bbs2 ==>
  invoke_blocks_subset bbs0 bbs2
Proof
  simp[invoke_blocks_subset_def,listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem MEM_FLAT_MAP_replace_block_subset[local]:
  !bbs lbl new_bb C x.
    MEM x (FLAT (MAP C (replace_block lbl new_bb bbs))) ==>
    MEM x (C new_bb) \/ MEM x (FLAT (MAP C bbs))
Proof
  Induct_on `bbs` >>
  simp[cfgTransformTheory.replace_block_def,listTheory.MEM_APPEND] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >>
  gvs[cfgTransformTheory.replace_block_def,listTheory.MEM_APPEND] >>
  metis_tac[]
QED

Theorem MEM_FLAT_MAP_component[local]:
  MEM e es /\ MEM x (C e) ==> MEM x (FLAT (MAP C es))
Proof
  simp[listTheory.MEM_FLAT,listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem lookup_block_MEM_subset[local]:
  !bbs lbl bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct >> simp[venomInstTheory.lookup_block_def,listTheory.FIND_thm] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> gvs[] >>
  disj2_tac >> first_x_assum irule >> qexists `lbl` >>
  gvs[venomInstTheory.lookup_block_def]
QED

Theorem replace_block_invoke_labels_subset[local]:
  lookup_block lbl bbs = SOME bb /\
  block_invoke_labels new_bb = block_invoke_labels bb ==>
  invoke_blocks_subset bbs (replace_block lbl new_bb bbs)
Proof
  simp[invoke_blocks_subset_def,listTheory.EVERY_MEM] >> rpt strip_tac >>
  drule MEM_FLAT_MAP_replace_block_subset >> strip_tac
  >- (`MEM bb bbs` by metis_tac[lookup_block_MEM_subset] >>
      metis_tac[MEM_FLAT_MAP_component])
  >> simp[]
QED


Theorem insert_phi_at_block_invoke_labels:
  phi.inst_opcode = PHI ==>
  block_invoke_labels (insert_phi_at_block phi bb) = block_invoke_labels bb
Proof
  simp[block_invoke_labels_def, makeSsaDefsTheory.insert_phi_at_block_def,
       get_invoke_targets_def]
QED


Theorem process_frontiers_supply_invoke_labels:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') ==>
    MAP block_invoke_labels bbs' = MAP block_invoke_labels bbs
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[])
  >> rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  asm "ih" drule >> rw[MAP_MAP_o] >>
  irule MAP_CONG >> rw[] >>
  Cases_on `e.bb_label = h` >>
  simp[makeSsaDefsTheory.insert_phi_at_block_def,
       block_invoke_labels_def, build_phi_inst_supply_def,
       get_invoke_targets_def]
QED



Theorem insert_phis_for_var_supply_invoke_labels:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') ==>
    MAP block_invoke_labels bbs' = MAP block_invoke_labels bbs
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  drule process_frontiers_supply_invoke_labels >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem add_phi_nodes_supply_invoke_labels:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    MAP block_invoke_labels bbs' = MAP block_invoke_labels bbs
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule insert_phis_for_var_supply_invoke_labels >> strip_tac >>
  first_x_assum drule >> simp[]
QED


Theorem update_current_phi_insts_invoke_labels:
  !insts rs cur.
    MAP FST (get_invoke_targets
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else inst with inst_operands :=
                      update_current_phi_for_pred rs cur inst.inst_operands)
           insts)) =
    MAP FST (get_invoke_targets insts)
Proof
  Induct >- simp[get_invoke_targets_def] >> rpt gen_tac >>
  pure_once_rewrite_tac[MAP] >>
  once_rewrite_tac[invoke_target_labels_cons] >> simp[] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[get_invoke_targets_def]
QED


Theorem FOLDL_two_maps_invariant_distinct:
  !xs step acc f g.
    (!a x. ALL_DISTINCT (MAP g a) ==>
       MAP f (step a x) = MAP f a /\
       MAP g (step a x) = MAP g a) ==>
    ALL_DISTINCT (MAP g acc) ==>
    MAP f (FOLDL step acc xs) = MAP f acc /\
    MAP g (FOLDL step acc xs) = MAP g acc
Proof
  Induct >- simp[] >> rpt strip_tac >> simp[] >>
  qpat_assum `!a x. ALL_DISTINCT (MAP g a) ==> _`
    (qspecl_then [`acc`,`h`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!step acc f g. _`
    (qspecl_then [`step'`,`step' acc h`,`f`,`g`] mp_tac) >>
  (impl_tac >- simp[]) >> (impl_tac >- simp[]) >> simp[]
QED

Theorem replace_block_labels_selector:
  new_bb.bb_label = lbl ==>
  MAP basic_block_bb_label (replace_block lbl new_bb bbs) =
  MAP basic_block_bb_label bbs
Proof
  strip_tac >> simp[cfgTransformTheory.replace_block_def, MAP_MAP_o] >>
  irule MAP_CONG >> rw[] >>
  Cases_on `e.bb_label = lbl` >> simp[]
QED


Theorem FOLDL_invoke_blocks_subset[local]:
  !xs step acc.
    (!a x. invoke_blocks_subset a (step a x)) ==>
    invoke_blocks_subset acc (FOLDL step acc xs)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[invoke_blocks_subset_refl]
  >> simp[] >> metis_tac[invoke_blocks_subset_trans]
QED

Theorem update_current_succ_phis_invoke_labels_subset[local]:
  !succs rs cur bbs.
    invoke_blocks_subset bbs (update_current_succ_phis rs cur bbs succs)
Proof
  rpt gen_tac >> simp[update_current_succ_phis_def] >>
  irule FOLDL_invoke_blocks_subset >> rpt strip_tac >>
  Cases_on `lookup_block x a`
  >- simp[invoke_blocks_subset_refl]
  >> gvs[] >> irule replace_block_invoke_labels_subset >> simp[] >>
     simp[block_invoke_labels_def,update_current_phi_insts_invoke_labels]
QED

Theorem update_current_succ_phis_invoke_labels:
  !succs rs cur bbs.
    ALL_DISTINCT (MAP basic_block_bb_label bbs) ==>
    MAP block_invoke_labels
      (update_current_succ_phis rs cur bbs succs) =
    MAP block_invoke_labels bbs
Proof
  rpt gen_tac >> strip_tac >>
  simp[update_current_succ_phis_def] >>
  qsuff_tac
    `MAP block_invoke_labels
       (FOLDL (\bs lbl.
          case lookup_block lbl bs of
            NONE => bs
          | SOME bb =>
              replace_block lbl
                (bb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                               else inst with inst_operands :=
                                 update_current_phi_for_pred rs cur
                                   inst.inst_operands)
                      bb.bb_instructions) bs) bbs succs) =
       MAP block_invoke_labels bbs /\
     MAP basic_block_bb_label
       (FOLDL (\bs lbl.
          case lookup_block lbl bs of
            NONE => bs
          | SOME bb =>
              replace_block lbl
                (bb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                               else inst with inst_operands :=
                                 update_current_phi_for_pred rs cur
                                   inst.inst_operands)
                      bb.bb_instructions) bs) bbs succs) =
       MAP basic_block_bb_label bbs`
  >- simp[] >>
  irule FOLDL_two_maps_invariant_distinct >> rpt strip_tac >>
  Cases_on `lookup_block x a` >> gvs[] >>
  drule lookup_block_label >> strip_tac
  >- (irule replace_block_invoke_labels_distinct >>
      simp[block_invoke_labels_def, update_current_phi_insts_invoke_labels])
  >> irule replace_block_labels_selector >> simp[]
QED
Theorem update_current_succ_phis_labels_selector:
  MAP basic_block_bb_label
    (update_current_succ_phis rs cur bbs succs) =
  MAP basic_block_bb_label bbs
Proof
  simp[update_current_succ_phis_def] >>
  irule FOLDL_map_invariant >> rpt strip_tac >>
  Cases_on `lookup_block x a` >> gvs[] >>
  drule lookup_block_label >> strip_tac >>
  irule replace_block_labels_selector >> simp[]
QED

Theorem update_current_succ_phis_inst_ids:
  !succs rs cur bbs.
    ALL_DISTINCT (MAP basic_block_bb_label bbs) ==>
    FLAT (MAP block_ir_inst_ids
      (update_current_succ_phis rs cur bbs succs)) =
    FLAT (MAP block_ir_inst_ids bbs)
Proof
  rpt gen_tac >> strip_tac >>
  simp[update_current_succ_phis_def] >>
  qsuff_tac
    `MAP block_ir_inst_ids
       (FOLDL (\bs lbl.
          case lookup_block lbl bs of
            NONE => bs
          | SOME bb =>
              replace_block lbl
                (bb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                               else inst with inst_operands :=
                                 update_current_phi_for_pred rs cur
                                   inst.inst_operands)
                      bb.bb_instructions) bs) bbs succs) =
       MAP block_ir_inst_ids bbs /\
     MAP basic_block_bb_label
       (FOLDL (\bs lbl.
          case lookup_block lbl bs of
            NONE => bs
          | SOME bb =>
              replace_block lbl
                (bb with bb_instructions :=
                  MAP (\inst. if inst.inst_opcode <> PHI then inst
                               else inst with inst_operands :=
                                 update_current_phi_for_pred rs cur
                                   inst.inst_operands)
                      bb.bb_instructions) bs) bbs succs) =
       MAP basic_block_bb_label bbs`
  >- simp[] >>
  irule FOLDL_two_maps_invariant_distinct >> rpt strip_tac >>
  Cases_on `lookup_block x a` >> gvs[] >>
  drule lookup_block_label >> strip_tac
  >- (simp[cfgTransformTheory.replace_block_def] >>
      irule MAP_replace_at_FIND_distinct >>
      conj_tac >- simp[] >> qexists `x'` >> conj_tac
      >- (simp[block_ir_inst_ids_def, MAP_MAP_o] >>
          irule MAP_CONG >> rw[] >>
          Cases_on `e.inst_opcode = PHI` >> simp[])
      >> gvs[venomInstTheory.lookup_block_def])
  >> irule replace_block_labels_selector >> simp[]
QED


Theorem block_vars_covered_of_mem:
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\ MEM bb bbs ==>
  ssa_vars_covered s (block_ir_vars bb)
Proof
  simp[ssa_vars_covered_def, listTheory.EVERY_MEM,
       listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]
QED

Definition rename_current_blocks_covered_inv_def:
  rename_current_blocks_covered_inv t <=>
    !s rs bbs sm ctrs s' bbs'.
      rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
      ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) ==>
      ssa_stacks_covered s (SND rs) ==>
      ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs')) /\
      ssa_supply_extends s s'
End

Definition rename_current_children_covered_inv_def:
  rename_current_children_covered_inv ts <=>
    !s ctrs stacks bbs sm ctrs' s' bbs'.
      rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
      ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) ==>
      ssa_stacks_covered s stacks ==>
      ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs')) /\
      ssa_supply_extends s s'
End

Theorem rename_current_blocks_covered_inv_vars_apply:
  rename_current_blocks_covered_inv t ==>
  rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) ==>
  ssa_stacks_covered s (SND rs) ==>
  ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs'))
Proof
  simp[rename_current_blocks_covered_inv_def] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem rename_current_blocks_covered_inv_supply_apply:
  rename_current_blocks_covered_inv t ==>
  rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) ==>
  ssa_stacks_covered s (SND rs) ==>
  ssa_supply_extends s s'
Proof
  simp[rename_current_blocks_covered_inv_def] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem rename_current_children_covered_inv_vars_apply:
  rename_current_children_covered_inv ts ==>
  rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) ==>
  ssa_stacks_covered s stacks ==>
  ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs'))
Proof
  simp[rename_current_children_covered_inv_def] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem rename_current_children_covered_inv_supply_apply:
  rename_current_children_covered_inv ts ==>
  rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) ==>
  ssa_stacks_covered s stacks ==>
  ssa_supply_extends s s'
Proof
  simp[rename_current_children_covered_inv_def] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem rename_current_blocks_vars_covered:
  (!s rs bbs sm t ctrs s' bbs'.
     ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
     ssa_stacks_covered s (SND rs) /\
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs')) /\
     ssa_supply_extends s s') /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) /\
     ssa_stacks_covered s stacks /\
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs')) /\
     ssa_supply_extends s s')
Proof
  qsuff_tac
    `(!t. rename_current_blocks_covered_inv t) /\
     (!ts. rename_current_children_covered_inv ts)`
  >- (simp[rename_current_blocks_covered_inv_def,
           rename_current_children_covered_inv_def] >> metis_tac[])
  >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      simp[rename_current_blocks_covered_inv_def] >> rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()] >>
      TRY (rename1 `lookup_block _ _ = NONE` >>
           simp[ssa_supply_extends_refl] >> NO_TAC) >>
      pairarg_tac >> gvs[] >>
         drule venomExecPropsTheory.lookup_block_MEM >> strip_tac >>
         `ssa_vars_covered s (block_ir_vars bb)` by
           (irule block_vars_covered_of_mem >> qexists `bbs` >> simp[]) >>
         `ssa_vars_covered s (FLAT (MAP inst_ir_vars bb.bb_instructions))` by
           gvs[block_ir_vars_def] >>
         `ssa_vars_covered s1 (FLAT (MAP inst_ir_vars insts')) /\
          ssa_stacks_covered s1 (SND rs1) /\
          ssa_supply_extends s s1` by
           (drule_all rename_current_block_insts_covered >> simp[]) >>
         `ssa_vars_covered s1 (FLAT (MAP block_ir_vars bbs))` by
           (gvs[ssa_vars_covered_def, ssa_supply_extends_def,
                listTheory.EVERY_MEM] >> metis_tac[]) >>
         `ssa_vars_covered s1
            (block_ir_vars (bb with bb_instructions := insts'))` by
           gvs[block_ir_vars_def] >>
         `ssa_vars_covered s1 (FLAT (MAP block_ir_vars
            (replace_block lbl
              (bb with bb_instructions := insts') bbs)))` by
           (irule replace_block_vars_covered >> simp[]) >>
         `ssa_vars_covered s1 (FLAT (MAP block_ir_vars
            (update_current_succ_phis rs1 lbl
              (replace_block lbl
                (bb with bb_instructions := insts') bbs)
              (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss))))` by
           (irule update_current_succ_phis_vars_covered >> simp[]) >>
         `ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs'))` by
           (drule rename_current_children_covered_inv_vars_apply >>
            disch_then drule >> disch_then drule >> simp[]) >>
         `ssa_supply_extends s1 s'` by
           (drule rename_current_children_covered_inv_supply_apply >>
            disch_then drule >> disch_then drule >> simp[]) >>
         irule ssa_supply_extends_trans >> qexists `s1` >> simp[])
  >- simp[rename_current_children_covered_inv_def,
           rename_current_blocks_def, ssa_supply_extends_refl]
  >> rpt strip_tac >>
     simp[rename_current_children_covered_inv_def] >> rpt strip_tac >>
     gvs[rename_current_blocks_def] >>
     pairarg_tac >> gvs[] >>
     `ssa_vars_covered s'' (FLAT (MAP block_ir_vars bbs''))` by
       (drule rename_current_blocks_covered_inv_vars_apply >>
        disch_then drule >> disch_then drule >> simp[]) >>
     `ssa_supply_extends s s''` by
       (drule rename_current_blocks_covered_inv_supply_apply >>
        disch_then drule >> disch_then drule >> simp[]) >>
     `ssa_stacks_covered s'' stacks` by
       (irule ssa_stacks_covered_mono >> qexists `s` >> simp[]) >>
     `ssa_vars_covered s' (FLAT (MAP block_ir_vars bbs'))` by
       (drule rename_current_children_covered_inv_vars_apply >>
        disch_then drule >> disch_then drule >> simp[]) >>
     `ssa_supply_extends s'' s'` by
       (drule rename_current_children_covered_inv_supply_apply >>
        disch_then drule >> disch_then drule >> simp[]) >>
     irule ssa_supply_extends_trans >> qexists `s''` >> simp[]
QED

Theorem rename_current_blocks_inst_ids:
  (!s rs bbs sm t ctrs s' bbs'.
     ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     FLAT (MAP block_ir_inst_ids bbs') =
     FLAT (MAP block_ir_inst_ids bbs)) /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     FLAT (MAP block_ir_inst_ids bbs') =
     FLAT (MAP block_ir_inst_ids bbs))
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
        FLAT (MAP block_ir_inst_ids bbs') =
        FLAT (MAP block_ir_inst_ids bbs)) /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
        FLAT (MAP block_ir_inst_ids bbs') =
        FLAT (MAP block_ir_inst_ids bbs))`
  >- metis_tac[]
  >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()]
      >> pairarg_tac >> gvs[] >>
         drule lookup_block_label >> strip_tac >>
         drule rename_current_block_insts_ids >> strip_tac >>
         `FLAT (MAP block_ir_inst_ids
            (replace_block lbl
              (bb with bb_instructions := insts') bbs)) =
          FLAT (MAP block_ir_inst_ids bbs)` by
           (irule replace_block_inst_ids_distinct >>
            simp[block_ir_inst_ids_def]) >>
         `ALL_DISTINCT (MAP basic_block_bb_label
            (update_current_succ_phis rs1 lbl
              (replace_block lbl
                (bb with bb_instructions := insts') bbs)
              (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss)))` by
           simp[update_current_succ_phis_labels_selector,
                replace_block_labels_selector] >>
         `FLAT (MAP block_ir_inst_ids
            (update_current_succ_phis rs1 lbl
              (replace_block lbl
                (bb with bb_instructions := insts') bbs)
              (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss))) =
          FLAT (MAP block_ir_inst_ids
            (replace_block lbl
              (bb with bb_instructions := insts') bbs))` by
           (irule update_current_succ_phis_inst_ids >>
            simp[replace_block_labels_selector]) >>
         first_x_assum drule >> strip_tac >>
         qpat_assum `!s0 c0 st0 sm0 c1 s2 out. _ ==> _` drule >>
         strip_tac >> metis_tac[])
  >- simp[rename_current_blocks_def]
  >> rpt strip_tac >> gvs[rename_current_blocks_def] >>
     pairarg_tac >> gvs[] >>
     qpat_assum `!s0 rs0 b0 sm0 c0 s1 b1. _`
       (drule_all_then assume_tac) >>
     `ALL_DISTINCT (MAP basic_block_bb_label bbs'')` by
       (drule (CONJUNCT1 rename_current_blocks_labels) >> simp[bb_label_eta]) >>
     qpat_assum `!s0 c0 st0 b0 sm0 c1 s1 b1. _`
       (drule_all_then assume_tac) >>
     metis_tac[]
QED

Theorem alist_update_or_prepend_key_MEM[local]:
  !alist k f d v.
    MEM v (MAP FST (alist_update_or_prepend k f d alist)) ==>
    v = k \/ MEM v (MAP FST alist)
Proof
  Induct >> simp[makeSsaDefsTheory.alist_update_or_prepend_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[makeSsaDefsTheory.alist_update_or_prepend_def] >>
  IF_CASES_TAC >> gvs[] >> metis_tac[]
QED

Theorem foldr_alist_update_key_MEM[local]:
  !vars lbl acc v.
    MEM v (MAP FST
      (FOLDR (\var a.
        alist_update_or_prepend var (CONS lbl) [lbl] a) acc vars)) ==>
    MEM v vars \/ MEM v (MAP FST acc)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  drule alist_update_or_prepend_key_MEM >>
  metis_tac[]
QED

Theorem compute_defs_key_MEM_block_ir_vars:
  MEM v (MAP FST (compute_defs bbs)) ==>
  MEM v (FLAT (MAP block_ir_vars bbs))
Proof
  Induct_on `bbs` >- simp[makeSsaDefsTheory.compute_defs_def] >>
  simp[Once makeSsaDefsTheory.compute_defs_def] >> rpt strip_tac >>
  drule foldr_alist_update_key_MEM >> strip_tac
  >- (gvs[makeSsaDefsTheory.block_assignments_def, block_ir_vars_def, inst_ir_vars_def,
          listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      disj1_tac >>
      qexists `inst.inst_outputs ++ inst_uses inst` >> simp[] >>
      metis_tac[])
  >> gvs[]
QED

Theorem lookup_blocks_filter_MEM:
  MEM bb (MAP THE (FILTER IS_SOME
    (MAP (\lbl. lookup_block lbl bbs) labels))) ==>
  MEM bb bbs
Proof
  Induct_on `labels` >- simp[] >>
  gen_tac >>
  Cases_on `lookup_block h bbs`
  >- (simp[] >> metis_tac[])
  >> `MEM x bbs` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  simp[] >> metis_tac[]
QED

Theorem compute_defs_lookup_blocks_vars_covered:
  ssa_vars_covered s (FLAT (MAP block_ir_vars bbs)) ==>
  ssa_vars_covered s
    (MAP FST (compute_defs
      (MAP THE (FILTER IS_SOME
        (MAP (\lbl. lookup_block lbl bbs) labels)))))
Proof
  simp[ssa_vars_covered_def, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  first_x_assum irule >>
  drule compute_defs_key_MEM_block_ir_vars >>
  rewrite_tac[listTheory.MEM_FLAT] >> strip_tac >>
  qpat_x_assum `MEM l (MAP block_ir_vars _)` mp_tac >>
  once_rewrite_tac[listTheory.MEM_MAP] >> strip_tac >> gvs[] >>
  drule lookup_blocks_filter_MEM >> strip_tac >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem make_ssa_current_fn_supply_ok:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  ir_supply_inst_ok s /\
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn) /\
  ssa_vars_covered s (fn_ir_vars fn) /\
  make_ssa_current_fn s fn = (fn',s') ==>
  ssa_ids_supply_ok s (fn_ir_inst_ids fn) (fn_ir_inst_ids fn') s' /\
  ssa_vars_covered s' (fn_ir_vars fn')
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[]
  >- (rpt strip_tac >> gvs[ssa_ids_supply_ok_refl]) >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  `ssa_vars_covered s
     (MAP FST (compute_defs
       (MAP THE (FILTER IS_SOME
         (MAP (\lbl. lookup_block lbl fn.fn_blocks)
           (dom_tree_postorder
             (current_dom_tree_aux (dom_analyze (cfg_analyze fn) fn)
               (LENGTH (fn_labels fn)) x)))))))` by
    (irule compute_defs_lookup_blocks_vars_covered >>
     gvs[fn_ir_vars_def]) >>
  `ssa_ids_supply_ok s (FLAT (MAP block_ir_inst_ids fn.fn_blocks))
      (FLAT (MAP block_ir_inst_ids bbs1)) s1 /\
   MAP basic_block_bb_label bbs1 =
      MAP basic_block_bb_label fn.fn_blocks /\
   ssa_vars_covered s1 (FLAT (MAP block_ir_vars bbs1))` by
    (irule add_phi_nodes_supply_ok >>
     gvs[fn_ir_vars_def, fn_ir_inst_ids_def] >>
     (conj_tac
      >- (qpat_assum `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` mp_tac >>
          once_rewrite_tac[GSYM bb_label_eta] >> simp[])) >>
     metis_tac[]) >>
  `ssa_supply_extends s s1` by
    metis_tac[ssa_ids_supply_ok_extends] >>
  `ssa_vars_covered s1
     (MAP FST (compute_defs
       (MAP THE (FILTER IS_SOME
         (MAP (\lbl. lookup_block lbl fn.fn_blocks)
           (dom_tree_postorder
             (current_dom_tree_aux (dom_analyze (cfg_analyze fn) fn)
               (LENGTH (fn_labels fn)) x)))))))` by
    (irule ssa_vars_covered_mono >> qexists `s` >> simp[]) >>
  `ssa_stacks_covered s1
     (SND (init_current_rename_state
       (compute_defs
         (MAP THE (FILTER IS_SOME
           (MAP (\lbl. lookup_block lbl fn.fn_blocks)
             (dom_tree_postorder
               (current_dom_tree_aux (dom_analyze (cfg_analyze fn) fn)
                 (LENGTH (fn_labels fn)) x))))))))` by
    (gvs[init_current_rename_state_def, ssa_stacks_covered_def,
         ssa_vars_covered_def, listTheory.EVERY_MEM,
         listTheory.MEM_MAP] >>
     rpt strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all (CONJUNCT1 rename_current_blocks_vars_covered) >> strip_tac >>
  `ir_supply_inst_ok s1` by
    metis_tac[ssa_ids_supply_ok_output] >>
  `ir_supply_inst_ok s'` by
    (drule_all (CONJUNCT1 rename_current_blocks_inst_supply_ok) >>
     simp[]) >>
  `ALL_DISTINCT (MAP basic_block_bb_label bbs1)` by metis_tac[] >>
  `FLAT (MAP block_ir_inst_ids bbs2) =
   FLAT (MAP block_ir_inst_ids bbs1)` by
    (irule (CONJUNCT1 rename_current_blocks_inst_ids) >> metis_tac[]) >>
  conj_tac
  >- (gvs[fn_ir_inst_ids_def, ssa_ids_supply_ok_def] >>
      (conj_tac
       >- (irule ssa_supply_extends_trans >> qexists `s1` >> simp[])) >>
      gvs[ssa_supply_extends_def, listTheory.EVERY_MEM]) >>
  gvs[fn_ir_vars_def]
QED


Theorem make_ssa_functions_supply_ok:
  !fns s fns' s'.
    EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)) fns /\
    ir_supply_inst_ok s /\
    ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns)) /\
    EVERY (\id. MEM id s.irs_used_inst_ids)
      (FLAT (MAP fn_ir_inst_ids fns)) /\
    ssa_vars_covered s (FLAT (MAP fn_ir_vars fns)) /\
    make_ssa_functions_supply s fns = (fns',s') ==>
    ssa_ids_supply_ok s (FLAT (MAP fn_ir_inst_ids fns))
      (FLAT (MAP fn_ir_inst_ids fns')) s' /\
    ssa_vars_covered s' (FLAT (MAP fn_ir_vars fns'))
Proof
  qid_spec_tac `s'` >> qid_spec_tac `fns'` >> qid_spec_tac `s` >>
  Induct_on `fns`
  >- simp[make_ssa_functions_supply_def, ssa_ids_supply_ok_refl,
          ssa_vars_covered_def] >>
  pop_assum $ mk_asm "ih" >>
  rpt gen_tac >> simp[make_ssa_functions_supply_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  `ssa_ids_supply_ok s (fn_ir_inst_ids h) (fn_ir_inst_ids fn') s'' /\
   ssa_vars_covered s'' (fn_ir_vars fn')` by
    (irule make_ssa_current_fn_supply_ok >>
     gvs[listTheory.ALL_DISTINCT_APPEND, ssa_vars_covered_def]) >>
  `ssa_supply_extends s s''` by
    metis_tac[ssa_ids_supply_ok_extends] >>
  `ir_supply_inst_ok s''` by
    metis_tac[ssa_ids_supply_ok_output] >>
  `EVERY (\id. MEM id s''.irs_used_inst_ids)
     (FLAT (MAP fn_ir_inst_ids fns))` by
    (gvs[listTheory.EVERY_MEM, ssa_supply_extends_def] >> metis_tac[]) >>
  `ssa_vars_covered s'' (FLAT (MAP fn_ir_vars fns))` by
    (irule ssa_vars_covered_mono >> qexists `s` >>
     gvs[ssa_vars_covered_def]) >>
  `ssa_ids_supply_ok s'' (FLAT (MAP fn_ir_inst_ids fns))
       (FLAT (MAP fn_ir_inst_ids fns'')) s' /\
   ssa_vars_covered s' (FLAT (MAP fn_ir_vars fns''))` by
    (asm "ih" irule >>
     gvs[listTheory.ALL_DISTINCT_APPEND]) >>
  `ssa_ids_supply_ok s
       (fn_ir_inst_ids h ++ FLAT (MAP fn_ir_inst_ids fns))
       (fn_ir_inst_ids fn' ++ FLAT (MAP fn_ir_inst_ids fns'')) s'` by
    (irule ssa_ids_supply_ok_append >> simp[] >>
     qexists `s''` >> simp[]) >>
  `ssa_vars_covered s' (fn_ir_vars fn')` by
    (irule ssa_vars_covered_mono >> qexists `s''` >>
     simp[] >> metis_tac[ssa_ids_supply_ok_extends]) >>
  gvs[ssa_vars_covered_def]
QED

Theorem make_ssa_ctx_supply_ok:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    ctx.ctx_functions /\
  ir_supply_inst_ok s /\
  ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  EVERY (\id. MEM id s.irs_used_inst_ids)
    (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  ssa_vars_covered s (FLAT (MAP fn_ir_vars ctx.ctx_functions)) /\
  make_ssa_ctx_supply s ctx = (ctx',s') ==>
  ssa_ids_supply_ok s (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions))
    (FLAT (MAP fn_ir_inst_ids ctx'.ctx_functions)) s' /\
  ssa_vars_covered s' (FLAT (MAP fn_ir_vars ctx'.ctx_functions))
Proof
  simp[make_ssa_ctx_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule_all make_ssa_functions_supply_ok >> gvs[]
QED

Theorem make_ssa_unit_supply_ok:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    unit.cu_context.ctx_functions /\
  ir_supply_inst_ok s /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (unit_ir_inst_ids unit) /\
  ssa_vars_covered s (unit_ir_vars unit) /\
  make_ssa_unit_supply s unit = (unit',s') ==>
  ssa_ids_supply_ok s (unit_ir_inst_ids unit)
    (unit_ir_inst_ids unit') s' /\
  ssa_vars_covered s' (unit_ir_vars unit')
Proof
  simp[make_ssa_unit_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  gvs[unit_ir_inst_ids_def, unit_ir_vars_def] >>
  drule_all make_ssa_ctx_supply_ok >>
  gvs[unit_ir_inst_ids_def, unit_ir_vars_def]
QED

Theorem make_ssa_configured_supply_contract[local]:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  make_ssa_configured_with_supply unit = (unit',s') ==>
  ssa_ids_supply_ok (init_ir_supply unit) (unit_ir_inst_ids unit)
    (unit_ir_inst_ids unit') s' /\
  ssa_vars_covered s' (unit_ir_vars unit')
Proof
  strip_tac >>
  irule make_ssa_unit_supply_ok >>
  gvs[make_ssa_configured_with_supply_def, init_ir_supply_inst_ok,
      init_ir_supply_fields, ssa_vars_covered_def, listTheory.EVERY_MEM]
QED

Theorem make_ssa_configured_inst_ids_distinct:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  make_ssa_configured_with_supply unit = (unit',s') ==>
  ALL_DISTINCT (unit_ir_inst_ids unit')
Proof
  strip_tac >> drule_all make_ssa_configured_supply_contract >>
  simp[ssa_ids_supply_ok_def]
QED

Theorem make_ssa_configured_supply_extends:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  make_ssa_configured_with_supply unit = (unit',s') ==>
  ssa_supply_extends (init_ir_supply unit) s'
Proof
  strip_tac >> drule_all make_ssa_configured_supply_contract >>
  simp[ssa_ids_supply_ok_def]
QED

Theorem make_ssa_configured_inst_ids_covered:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  make_ssa_configured_with_supply unit = (unit',s') ==>
  EVERY (\id. MEM id s'.irs_used_inst_ids) (unit_ir_inst_ids unit')
Proof
  strip_tac >> drule_all make_ssa_configured_supply_contract >>
  simp[ssa_ids_supply_ok_def]
QED

Theorem make_ssa_configured_vars_covered:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  make_ssa_configured_with_supply unit = (unit',s') ==>
  ssa_vars_covered s' (unit_ir_vars unit')
Proof
  strip_tac >> drule_all make_ssa_configured_supply_contract >> simp[]
QED

Theorem make_ssa_configured_global_ids_distinct:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) ==>
  ALL_DISTINCT (unit_ir_inst_ids (make_ssa_configured unit))
Proof
  rpt strip_tac >>
  Cases_on `make_ssa_configured_with_supply unit` >>
  drule_all make_ssa_configured_inst_ids_distinct >>
  gvs[make_ssa_configured_def]
QED

Theorem make_ssa_current_fn_second_call_current_analysis:
  make_ssa_current_fn s fn = (fn1,s1) ==>
  make_ssa_current_fn s1 fn1 =
    case fn_entry_label fn1 of
      NONE => (fn1,s1)
    | SOME entry =>
        let cfg = cfg_analyze fn1 in
        let dom = dom_analyze cfg fn1 in
        let live = liveness_analyze fn1 in
        let pred_map = current_query_map (fn_labels fn1) (cfg_preds_of cfg) in
        let succ_map = current_query_map (fn_labels fn1) (cfg_succs_of cfg) in
        let frontiers = current_query_map (fn_labels fn1) (frontier_of dom) in
        let live_in = current_query_map (fn_labels fn1)
                                        (\l. live_vars_at live l 0) in
        let dtree = current_dom_tree_aux dom (LENGTH (fn_labels fn1)) entry in
        let postorder = dom_tree_postorder dtree in
        let ordered_bbs = MAP THE (FILTER IS_SOME
          (MAP (\lbl. lookup_block lbl fn1.fn_blocks) postorder)) in
        let defs = compute_defs ordered_bbs in
        let (bbs1,s2) = add_phi_nodes_supply s1 frontiers pred_map live_in
                                             fn1.fn_blocks defs in
        let rs0 = init_current_rename_state defs in
        let (_,s3,bbs2) = rename_current_blocks s2 rs0 bbs1 succ_map dtree in
          (fn1 with fn_blocks := bbs2,s3)
Proof
  strip_tac >> simp[make_ssa_current_fn_current_analysis_eq]
QED

Theorem rename_current_blocks_invoke_labels_subset:
  (!s rs bbs sm t ctrs s' bbs'.
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     invoke_blocks_subset bbs bbs') /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     invoke_blocks_subset bbs bbs')
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
        invoke_blocks_subset bbs bbs') /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
        invoke_blocks_subset bbs bbs')`
  >- metis_tac[]
  >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def,AllCaseEqs(),invoke_blocks_subset_refl] >>
      pairarg_tac >> gvs[] >>
      drule rename_current_block_insts_invoke_targets >> strip_tac >>
      `invoke_blocks_subset bbs
         (replace_block lbl (bb with bb_instructions := insts') bbs)` by
        (irule replace_block_invoke_labels_subset >>
         simp[block_invoke_labels_def]) >>
      `invoke_blocks_subset
         (replace_block lbl (bb with bb_instructions := insts') bbs)
         (update_current_succ_phis rs1 lbl
           (replace_block lbl (bb with bb_instructions := insts') bbs)
           (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss))` by
        simp[update_current_succ_phis_invoke_labels_subset] >>
      first_x_assum drule >> strip_tac >>
      metis_tac[invoke_blocks_subset_trans])
  >- simp[rename_current_blocks_def,invoke_blocks_subset_refl]
  >> rpt strip_tac >> gvs[rename_current_blocks_def] >>
     pairarg_tac >> gvs[] >>
     qpat_assum `!s0 rs0 b0 sm0 c0 s1 b1. _`
       (drule_all_then assume_tac) >>
     qpat_assum `!s0 c0 st0 b0 sm0 c1 s1 b1. _`
       (drule_all_then assume_tac) >>
     metis_tac[invoke_blocks_subset_trans]
QED

Theorem rename_current_blocks_invoke_labels:
  (!s rs bbs sm t ctrs s' bbs'.
     ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     MAP block_invoke_labels bbs' = MAP block_invoke_labels bbs) /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     MAP block_invoke_labels bbs' = MAP block_invoke_labels bbs)
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
        MAP block_invoke_labels bbs' = MAP block_invoke_labels bbs) /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        ALL_DISTINCT (MAP basic_block_bb_label bbs) /\
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
        MAP block_invoke_labels bbs' = MAP block_invoke_labels bbs)`
  >- metis_tac[]
  >> ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >>
      gvs[rename_current_blocks_def, AllCaseEqs()]
      >> pairarg_tac >> gvs[] >>
         drule lookup_block_label >> strip_tac >>
         drule rename_current_block_insts_invoke_targets >> strip_tac >>
         `MAP block_invoke_labels
            (replace_block lbl
              (bb with bb_instructions := insts') bbs) =
          MAP block_invoke_labels bbs` by
           (irule replace_block_invoke_labels_distinct >>
            simp[block_invoke_labels_def]) >>
         `MAP basic_block_bb_label
            (replace_block lbl
              (bb with bb_instructions := insts') bbs) =
          MAP basic_block_bb_label bbs` by
           (irule replace_block_labels_selector >> simp[]) >>
         `ALL_DISTINCT (MAP basic_block_bb_label
            (update_current_succ_phis rs1 lbl
              (replace_block lbl
                (bb with bb_instructions := insts') bbs)
              (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss)))` by
           simp[update_current_succ_phis_labels_selector] >>
         first_x_assum drule >> strip_tac >>
         qpat_assum `!s0 c0 st0 sm0 c1 s2 out. _ ==> _` drule >>
         strip_tac >>
         simp[update_current_succ_phis_invoke_labels])
  >- simp[rename_current_blocks_def]
  >> rpt strip_tac >> gvs[rename_current_blocks_def] >>
     pairarg_tac >> gvs[] >>
     qpat_assum `!s0 rs0 b0 sm0 c0 s1 b1. _`
       (drule_all_then assume_tac) >>
     `ALL_DISTINCT (MAP basic_block_bb_label bbs'')` by
       (drule (CONJUNCT1 rename_current_blocks_labels) >> simp[bb_label_eta]) >>
     qpat_assum `!s0 c0 st0 b0 sm0 c1 s1 b1. _`
       (drule_all_then assume_tac) >>
     metis_tac[]
QED

Theorem make_ssa_current_fn_invoke_targets_subset:
  make_ssa_current_fn s fn = (fn',s') ==>
  EVERY (\t. MEM t (MAP FST (fcg_scan_function fn)))
        (MAP FST (fcg_scan_function fn'))
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >>
  gvs[invoke_blocks_subset_refl,fcg_scan_function_invoke_labels,
      listTheory.EVERY_MEM] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule add_phi_nodes_supply_invoke_labels >> strip_tac >>
  drule_all_then assume_tac
    (CONJUNCT1 rename_current_blocks_invoke_labels_subset) >>
  `invoke_blocks_subset fn.fn_blocks bbs1` by
    gvs[invoke_blocks_subset_def,listTheory.EVERY_MEM] >>
  `invoke_blocks_subset fn.fn_blocks bbs2` by
    metis_tac[invoke_blocks_subset_trans] >>
  gvs[invoke_blocks_subset_def,fcg_scan_function_invoke_labels,
      listTheory.EVERY_MEM]
QED

Theorem make_ssa_current_fn_invoke_targets:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  make_ssa_current_fn s fn = (fn',s') ==>
  MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[]
  >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
     drule add_phi_nodes_supply_invoke_labels >> strip_tac >>
     `ALL_DISTINCT (MAP basic_block_bb_label bbs1)` by
       (drule add_phi_nodes_supply_labels >> strip_tac >>
        gvs[bb_label_eta]) >>
     drule_all_then assume_tac
       (CONJUNCT1 rename_current_blocks_invoke_labels) >>
     gvs[fcg_scan_function_invoke_labels]
QED

Theorem make_ssa_functions_supply_invoke_targets:
  !fns s fns' s'.
    EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)) fns /\
    make_ssa_functions_supply s fns = (fns',s') ==>
    MAP (\fn. MAP FST (fcg_scan_function fn)) fns' =
    MAP (\fn. MAP FST (fcg_scan_function fn)) fns
Proof
  Induct >- simp[make_ssa_functions_supply_def] >>
  rpt gen_tac >> simp[make_ssa_functions_supply_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule_all make_ssa_current_fn_invoke_targets >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem make_ssa_functions_supply_metadata:
  !fns s fns' s'.
    make_ssa_functions_supply s fns = (fns',s') ==>
    LIST_REL (\fn' fn.
      fn_identity_metadata_eq fn' fn /\
      fn_static_input_eq fn' fn /\
      fn_static_layout_eq fn' fn /\
      fn_fmp_convention_eq fn' fn) fns' fns
Proof
  Induct >- simp[make_ssa_functions_supply_def] >>
  rpt gen_tac >> simp[make_ssa_functions_supply_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_current_fn_metadata >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem make_ssa_functions_supply_labels:
  !fns s fns' s'.
    make_ssa_functions_supply s fns = (fns',s') ==>
    MAP (\fn. MAP (\bb. bb.bb_label) fn.fn_blocks) fns' =
    MAP (\fn. MAP (\bb. bb.bb_label) fn.fn_blocks) fns
Proof
  Induct >- simp[make_ssa_functions_supply_def] >>
  rpt gen_tac >> simp[make_ssa_functions_supply_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED




Theorem make_ssa_ctx_supply_invoke_targets:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    ctx.ctx_functions /\
  make_ssa_ctx_supply s ctx = (ctx',s') ==>
  MAP (\fn. MAP FST (fcg_scan_function fn)) ctx'.ctx_functions =
  MAP (\fn. MAP FST (fcg_scan_function fn)) ctx.ctx_functions
Proof
  simp[make_ssa_ctx_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule_all make_ssa_functions_supply_invoke_targets >> gvs[]
QED

Theorem make_ssa_ctx_supply_metadata:
  make_ssa_ctx_supply s ctx = (ctx',s') ==>
  LIST_REL (\fn' fn.
    fn_identity_metadata_eq fn' fn /\
    fn_static_input_eq fn' fn /\
    fn_static_layout_eq fn' fn /\
    fn_fmp_convention_eq fn' fn)
    ctx'.ctx_functions ctx.ctx_functions
Proof
  simp[make_ssa_ctx_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_functions_supply_metadata >> gvs[]
QED

Theorem make_ssa_ctx_supply_labels:
  make_ssa_ctx_supply s ctx = (ctx',s') ==>
  MAP (\fn. MAP (\bb. bb.bb_label) fn.fn_blocks) ctx'.ctx_functions =
  MAP (\fn. MAP (\bb. bb.bb_label) fn.fn_blocks) ctx.ctx_functions
Proof
  simp[make_ssa_ctx_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_functions_supply_labels >> gvs[]
QED

Theorem make_ssa_unit_supply_invoke_targets:
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    unit.cu_context.ctx_functions /\
  make_ssa_unit_supply s unit = (unit',s') ==>
  MAP (\fn. MAP FST (fcg_scan_function fn))
    unit'.cu_context.ctx_functions =
  MAP (\fn. MAP FST (fcg_scan_function fn))
    unit.cu_context.ctx_functions
Proof
  simp[make_ssa_unit_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule_all make_ssa_ctx_supply_invoke_targets >> gvs[]
QED

Theorem make_ssa_unit_supply_metadata:
  make_ssa_unit_supply s unit = (unit',s') ==>
  LIST_REL (\fn' fn.
    fn_identity_metadata_eq fn' fn /\
    fn_static_input_eq fn' fn /\
    fn_static_layout_eq fn' fn /\
    fn_fmp_convention_eq fn' fn)
    unit'.cu_context.ctx_functions unit.cu_context.ctx_functions
Proof
  simp[make_ssa_unit_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_ctx_supply_metadata >> gvs[]
QED

Theorem make_ssa_unit_supply_labels:
  make_ssa_unit_supply s unit = (unit',s') ==>
  MAP (\fn. MAP (\bb. bb.bb_label) fn.fn_blocks)
    unit'.cu_context.ctx_functions =
  MAP (\fn. MAP (\bb. bb.bb_label) fn.fn_blocks)
    unit.cu_context.ctx_functions
Proof
  simp[make_ssa_unit_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_ctx_supply_labels >> gvs[]
QED

Theorem make_ssa_functions_supply_extends:
  !fns s fns' s'.
    make_ssa_functions_supply s fns = (fns',s') ==>
    ssa_supply_extends s s'
Proof
  Induct >- simp[make_ssa_functions_supply_def, ssa_supply_extends_refl] >>
  pop_assum $ mk_asm "ih" >>
  rpt gen_tac >> simp[make_ssa_functions_supply_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_current_fn_extends >> strip_tac >>
  asm "ih" drule >> strip_tac >>
  metis_tac[ssa_supply_extends_trans]
QED

Theorem make_ssa_ctx_supply_extends:
  make_ssa_ctx_supply s ctx = (ctx',s') ==> ssa_supply_extends s s'
Proof
  simp[make_ssa_ctx_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_functions_supply_extends >> simp[]
QED

Theorem make_ssa_unit_supply_extends:
  make_ssa_unit_supply s unit = (unit',s') ==> ssa_supply_extends s s'
Proof
  simp[make_ssa_unit_supply_def] >> pairarg_tac >> gvs[] >> strip_tac >>
  drule make_ssa_ctx_supply_extends >> simp[]
QED
Definition ssa_blocks_no_raw_def[local]:
  ssa_blocks_no_raw bbs <=>
    EVERY (\bb. EVERY (\inst. ~is_raw_fmp_opcode inst.inst_opcode)
                       bb.bb_instructions) bbs
End

Theorem ssa_blocks_no_raw_fn_insts[local]:
  ssa_blocks_no_raw bbs <=>
  !inst. MEM inst (fn_insts_blocks bbs) ==>
         ~is_raw_fmp_opcode inst.inst_opcode
Proof
  rewrite_tac[ssa_blocks_no_raw_def] >>
  Induct_on `bbs` >>
  simp[venomInstTheory.fn_insts_blocks_def, listTheory.EVERY_MEM,
       listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem ssa_blocks_no_raw_lookup[local]:
  ssa_blocks_no_raw bbs /\ lookup_block lbl bbs = SOME bb ==>
  EVERY (\inst. ~is_raw_fmp_opcode inst.inst_opcode) bb.bb_instructions
Proof
  simp[ssa_blocks_no_raw_def, listTheory.EVERY_MEM] >>
  metis_tac[lookup_block_MEM_subset]
QED

Theorem ssa_blocks_no_raw_replace[local]:
  ssa_blocks_no_raw bbs /\
  EVERY (\inst. ~is_raw_fmp_opcode inst.inst_opcode) new_bb.bb_instructions ==>
  ssa_blocks_no_raw (replace_block lbl new_bb bbs)
Proof
  simp[ssa_blocks_no_raw_def, cfgTransformTheory.replace_block_def,
       listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  qpat_x_assum `MEM _ (MAP _ _)` mp_tac >>
  simp[listTheory.MEM_MAP] >> strip_tac >>
  rename1 `MEM source bbs` >>
  Cases_on `source.bb_label = lbl` >> gvs[] >> metis_tac[]
QED
Theorem ssa_blocks_no_raw_insert_phi[local]:
  ~is_raw_fmp_opcode phi.inst_opcode /\ ssa_blocks_no_raw bbs ==>
  ssa_blocks_no_raw
    (MAP (\bb. if bb.bb_label = lbl then insert_phi_at_block phi bb else bb)
         bbs)
Proof
  simp[ssa_blocks_no_raw_def, listTheory.EVERY_MAP,
       makeSsaDefsTheory.insert_phi_at_block_def, listTheory.EVERY_MEM] >>
  rpt strip_tac >> Cases_on `bb.bb_label = lbl` >> gvs[] >> metis_tac[]
QED


Theorem process_frontiers_supply_no_raw[local]:
  !fs s var pm li bbs rest hp bbs' rest' hp' s'.
    process_frontiers_supply s var pm li bbs rest hp fs =
      (bbs',rest',hp',s') /\ ssa_blocks_no_raw bbs ==>
    ssa_blocks_no_raw bbs'
Proof
  Induct >- simp[process_frontiers_supply_def] >>
  pop_assum $ mk_asm "ih" >>
  simp[process_frontiers_supply_def] >> rpt gen_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[]) >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> asm "ih" drule >> simp[]) >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  asm "ih" drule >>
  (impl_tac >-
    (irule ssa_blocks_no_raw_insert_phi >>
     simp[build_phi_inst_supply_def,
          venomInstTheory.is_raw_fmp_opcode_def])) >>
  simp[]
QED

Theorem insert_phis_for_var_supply_no_raw[local]:
  !s var df pm li bbs wl hp bbs' s'.
    insert_phis_for_var_supply s var df pm li bbs wl hp = (bbs',s') /\
    ssa_blocks_no_raw bbs ==>
    ssa_blocks_no_raw bbs'
Proof
  recInduct insert_phis_for_var_supply_ind >>
  rw[insert_phis_for_var_supply_def] >> gvs[] >>
  rpt CASE_TAC >> gvs[] >> pairarg_tac >> gvs[] >>
  drule_all process_frontiers_supply_no_raw >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem add_phi_nodes_supply_no_raw[local]:
  !defs s df pm li bbs bbs' s'.
    add_phi_nodes_supply s df pm li bbs defs = (bbs',s') ==>
    ssa_blocks_no_raw bbs ==>
    ssa_blocks_no_raw bbs'
Proof
  Induct >- simp[add_phi_nodes_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >> simp[add_phi_nodes_supply_def] >>
  pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule_all insert_phis_for_var_supply_no_raw >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem rename_current_inst_no_raw[local]:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  inst'.inst_opcode = inst.inst_opcode
Proof
  simp[rename_current_inst_def] >> rpt CASE_TAC >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[]
QED

Theorem rename_current_block_insts_no_raw[local]:
  !s rs insts rs' s' insts'.
    rename_current_block_insts s rs insts = (rs',s',insts') ==>
    EVERY (\inst. ~is_raw_fmp_opcode inst.inst_opcode) insts ==>
    EVERY (\inst. ~is_raw_fmp_opcode inst.inst_opcode) insts'
Proof
  Induct_on `insts` >- simp[rename_current_block_insts_def] >>
  rpt gen_tac >> simp[rename_current_block_insts_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  drule rename_current_inst_no_raw >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Theorem FOLDL_ssa_blocks_no_raw[local]:
  !xs step acc.
    (!a x. ssa_blocks_no_raw a ==> ssa_blocks_no_raw (step a x)) /\
    ssa_blocks_no_raw acc ==>
    ssa_blocks_no_raw (FOLDL step acc xs)
Proof
  Induct >> simp[] >> metis_tac[]
QED

Theorem update_current_succ_phis_no_raw[local]:
  !succs rs cur bbs.
    ssa_blocks_no_raw bbs ==>
    ssa_blocks_no_raw (update_current_succ_phis rs cur bbs succs)
Proof
  rpt gen_tac >> strip_tac >> simp[update_current_succ_phis_def] >>
  irule FOLDL_ssa_blocks_no_raw >> simp[] >> rpt strip_tac >>
  Cases_on `lookup_block x a` >- simp[] >> gvs[] >>
  irule ssa_blocks_no_raw_replace >> simp[] >>
  drule_all ssa_blocks_no_raw_lookup >> strip_tac >>
  simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  `~is_raw_fmp_opcode inst.inst_opcode` by
    (qpat_x_assum `EVERY _ x'.bb_instructions` mp_tac >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = PHI` >>
  gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem rename_current_blocks_no_raw[local]:
  (!s rs bbs sm t ctrs s' bbs'.
     rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
     ssa_blocks_no_raw bbs ==> ssa_blocks_no_raw bbs') /\
  (!s ctrs stacks bbs sm ts ctrs' s' bbs'.
     rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
     ssa_blocks_no_raw bbs ==> ssa_blocks_no_raw bbs')
Proof
  qsuff_tac
    `(!t s rs bbs sm ctrs s' bbs'.
        rename_current_blocks s rs bbs sm t = (ctrs,s',bbs') ==>
        ssa_blocks_no_raw bbs ==> ssa_blocks_no_raw bbs') /\
     (!ts s ctrs stacks bbs sm ctrs' s' bbs'.
        rename_current_children s ctrs stacks bbs sm ts = (ctrs',s',bbs') ==>
        ssa_blocks_no_raw bbs ==> ssa_blocks_no_raw bbs')`
  >- metis_tac[] >>
  ho_match_mp_tac current_dom_tree_induction >> rpt conj_tac
  >- (rpt strip_tac >> gvs[rename_current_blocks_def, AllCaseEqs()] >>
      pairarg_tac >> gvs[] >>
      rename [`lookup_block lbl bbs = SOME bb`,
              `rename_current_block_insts s rs bb.bb_instructions =
                 (rs1,s1,insts')`] >>
      `EVERY (\inst. ~is_raw_fmp_opcode inst.inst_opcode)
             insts'` by
        (drule rename_current_block_insts_no_raw >>
         disch_then irule >>
         drule_all ssa_blocks_no_raw_lookup >> simp[]) >>
      `ssa_blocks_no_raw (replace_block lbl
         (bb with bb_instructions := insts') bbs)` by
        (irule ssa_blocks_no_raw_replace >> simp[]) >>
      `ssa_blocks_no_raw
         (update_current_succ_phis rs1 lbl
           (replace_block lbl (bb with bb_instructions := insts') bbs)
           (case ALOOKUP sm lbl of NONE => [] | SOME ss => ss))` by
        (irule update_current_succ_phis_no_raw >> simp[]) >>
      first_x_assum drule_all >> simp[])
  >- simp[rename_current_blocks_def] >>
  rpt strip_tac >> gvs[rename_current_blocks_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem make_ssa_current_fn_no_raw_fmp_ops:
  no_raw_fmp_ops fn ==>
  no_raw_fmp_ops (FST (make_ssa_current_fn s fn))
Proof
  simp[make_ssa_current_fn_def] >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> rpt strip_tac >>
  `ssa_blocks_no_raw fn.fn_blocks` by
    gvs[ssa_blocks_no_raw_fn_insts,
        venomInstTheory.no_raw_fmp_ops_def,
        venomInstTheory.fn_insts_def] >>
  `ssa_blocks_no_raw bbs1` by
    (drule add_phi_nodes_supply_no_raw >> disch_then drule >> simp[]) >>
  `ssa_blocks_no_raw bbs2` by
    (drule (CONJUNCT1 rename_current_blocks_no_raw) >>
     disch_then drule >> simp[]) >>
  gvs[ssa_blocks_no_raw_fn_insts,
      venomInstTheory.no_raw_fmp_ops_def,
      venomInstTheory.fn_insts_def]
QED

val _ = export_theory();
