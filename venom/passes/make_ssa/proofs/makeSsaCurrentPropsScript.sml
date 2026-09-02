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

Theorem push_current_name_extends:
  push_current_name s rs v = (rs',s',name) ==> ssa_supply_extends s s'
Proof
  PairCases_on `rs` >>
  simp[push_current_name_def] >> rpt CASE_TAC >> gvs[] >>
  simp[ssa_supply_extends_refl] >>
  pairarg_tac >> gvs[] >>
  metis_tac[fresh_ir_var_extends]
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

Theorem rename_current_inst_extends:
  rename_current_inst s rs inst = (rs',s',inst') ==>
  ssa_supply_extends s s'
Proof
  simp[rename_current_inst_def] >> rpt CASE_TAC >> gvs[] >>
  pairarg_tac >> gvs[] >> strip_tac >>
  drule rename_current_outputs_extends >> simp[]
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
Theorem process_frontiers_duplicate_label_id_probe:
  let s = <| irs_next_inst := 3; irs_next_var := 0; irs_next_label := 0;
             irs_used_inst_ids := [1;2]; irs_used_vars := ["v"];
             irs_used_labels := ["x"] |> in
  let bb1 = <| bb_label := "x";
               bb_instructions := [mk_inst 1 STOP [] []] |> in
  let bb2 = <| bb_label := "x";
               bb_instructions := [mk_inst 2 STOP [] []] |> in
  let (bbs',rest',hp',s') =
    process_frontiers_supply s "v" [("x",[])] [("x",["v"])]
      [bb1;bb2] [] [] ["x"] in
    ~ALL_DISTINCT (FLAT (MAP block_ir_inst_ids bbs'))
Proof
  EVAL_TAC
QED



Theorem make_ssa_current_fn_duplicate_label_invoke_probe:
  let s = <| irs_next_inst := 1; irs_next_var := 0; irs_next_label := 0;
             irs_used_inst_ids := [0]; irs_used_vars := [];
             irs_used_labels := ["entry"] |> in
  let invoke = mk_inst 0 INVOKE [Label "callee"] [] in
  let bb0 = <| bb_label := "entry"; bb_instructions := [] |> in
  let bb1 = <| bb_label := "entry"; bb_instructions := [invoke] |> in
  let fn = mk_raw_function "f" [bb0;bb1] in
    MAP FST (fcg_scan_function (FST (make_ssa_current_fn s fn))) <>
    MAP FST (fcg_scan_function fn)
Proof
  EVAL_TAC
QED

val _ = export_theory();
