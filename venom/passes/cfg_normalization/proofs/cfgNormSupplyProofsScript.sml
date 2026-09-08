Theory cfgNormSupplyProofs
Ancestors
  cfgNormDefs irSupply cfgTransform fcgDefs

Definition cfg_supply_extends_def:
  cfg_supply_extends s s' <=>
    ?new_ids new_vars new_labels.
      s'.irs_used_inst_ids = new_ids ++ s.irs_used_inst_ids /\
      ALL_DISTINCT new_ids /\
      EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids /\
      s'.irs_used_vars = new_vars ++ s.irs_used_vars /\
      ALL_DISTINCT new_vars /\
      EVERY (\v. ~MEM v s.irs_used_vars) new_vars /\
      s'.irs_used_labels = new_labels ++ s.irs_used_labels /\
      ALL_DISTINCT new_labels /\
      EVERY (\l. ~MEM l s.irs_used_labels) new_labels /\
      ir_supply_inst_ok s'
End

Theorem cfg_supply_extends_refl:
  ir_supply_inst_ok s ==> cfg_supply_extends s s
Proof
  simp[cfg_supply_extends_def] >> metis_tac[]
QED

Theorem cfg_supply_extends_members:
  cfg_supply_extends s s' ==>
  (!id. MEM id s.irs_used_inst_ids ==> MEM id s'.irs_used_inst_ids) /\
  (!v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars) /\
  (!l. MEM l s.irs_used_labels ==> MEM l s'.irs_used_labels)
Proof
  strip_tac >> gvs[cfg_supply_extends_def]
QED

Theorem cfg_supply_extends_trans:
  cfg_supply_extends s s1 /\ cfg_supply_extends s1 s2 ==>
  cfg_supply_extends s s2
Proof
  simp[cfg_supply_extends_def] >>
  rpt strip_tac >>
  qexistsl [`new_ids' ++ new_ids`,
            `new_vars' ++ new_vars`,
            `new_labels' ++ new_labels`] >>
  gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM] >>
  simp[listTheory.APPEND_ASSOC] >> metis_tac[]
QED

Definition cfg_id_declared_def:
  cfg_id_declared unit id <=> MEM id (unit_ir_inst_ids unit)
End

Definition cfg_var_declared_def:
  cfg_var_declared unit v <=>
    EXISTS (\fn.
      EXISTS (\bb.
        EXISTS (\inst. MEM v inst.inst_outputs) bb.bb_instructions)
      fn.fn_blocks)
    unit.cu_context.ctx_functions
End

Definition cfg_block_label_declared_def:
  cfg_block_label_declared unit l <=>
    EXISTS (\fn. EXISTS (\bb. bb.bb_label = l) fn.fn_blocks)
      unit.cu_context.ctx_functions
End

Definition cfg_insts_id_declared_def:
  cfg_insts_id_declared insts id <=>
    EXISTS (\inst. inst.inst_id = id) insts
End

Definition cfg_insts_var_declared_def:
  cfg_insts_var_declared insts v <=>
    EXISTS (\inst. MEM v inst.inst_outputs) insts
End

Definition cfg_forwarding_supply_contract_def:
  cfg_forwarding_supply_contract s insts s' <=>
    cfg_supply_extends s s' /\
    (!id. MEM id s'.irs_used_inst_ids /\
          ~MEM id s.irs_used_inst_ids ==>
          cfg_insts_id_declared insts id) /\
    (!v. MEM v s'.irs_used_vars /\ ~MEM v s.irs_used_vars ==>
         cfg_insts_var_declared insts v) /\
    s'.irs_used_labels = s.irs_used_labels
End

Definition cfg_block_supply_contract_def:
  cfg_block_supply_contract s bb s' <=>
    cfg_supply_extends s s' /\
    (!id. MEM id s'.irs_used_inst_ids /\
          ~MEM id s.irs_used_inst_ids ==>
          cfg_insts_id_declared bb.bb_instructions id) /\
    (!v. MEM v s'.irs_used_vars /\ ~MEM v s.irs_used_vars ==>
         cfg_insts_var_declared bb.bb_instructions v) /\
    (!l. MEM l s'.irs_used_labels /\ ~MEM l s.irs_used_labels ==>
         bb.bb_label = l)
End

Theorem fresh_ir_var_cfg_supply_extends:
  ir_supply_inst_ok s /\ fresh_ir_var s = (v,s') ==>
  cfg_supply_extends s s'
Proof
  rpt strip_tac >> drule fresh_ir_var_contract >> strip_tac >>
  `ir_supply_inst_ok s'` by gvs[ir_supply_inst_ok_def] >>
  simp[cfg_supply_extends_def] >> gvs[]
QED

Theorem fresh_ir_label_cfg_supply_extends:
  ir_supply_inst_ok s /\ fresh_ir_label s = (l,s') ==>
  cfg_supply_extends s s'
Proof
  rpt strip_tac >> drule fresh_ir_label_contract >> strip_tac >>
  `ir_supply_inst_ok s'` by gvs[ir_supply_inst_ok_def] >>
  simp[cfg_supply_extends_def] >> gvs[]
QED

Theorem fresh_inst_id_cfg_supply_extends:
  ir_supply_inst_ok s /\ fresh_inst_id s = (id,s') ==>
  cfg_supply_extends s s'
Proof
  rpt strip_tac >> drule_all fresh_inst_id_contract >> strip_tac >>
  simp[cfg_supply_extends_def] >> metis_tac[]
QED

Theorem build_forwarding_assigns_supply_contract:
  !vars s repls insts s'.
    ir_supply_inst_ok s /\
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    cfg_forwarding_supply_contract s insts s'
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def,
          cfg_forwarding_supply_contract_def,
          cfg_supply_extends_refl]
  >> Cases_on `fresh_ir_var s` >>
     rename1 `fresh_ir_var s = (new_var,s1)` >>
     Cases_on `fresh_inst_id s1` >>
     rename1 `fresh_inst_id s1 = (id,s2)` >>
     Cases_on `build_forwarding_assigns_supply s2 vars` >>
     PairCases_on `r` >>
     rename1 `build_forwarding_assigns_supply s2 vars =
              (rest_repls,rest_insts,s3)` >>
     gvs[build_forwarding_assigns_supply_def] >>
     `cfg_supply_extends s s1` by
       metis_tac[fresh_ir_var_cfg_supply_extends] >>
     `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
     `cfg_supply_extends s1 s2` by
       metis_tac[fresh_inst_id_cfg_supply_extends] >>
     `ir_supply_inst_ok s2` by gvs[cfg_supply_extends_def] >>
     `cfg_forwarding_supply_contract s2 rest_insts s'` by metis_tac[] >>
     drule fresh_ir_var_contract >> strip_tac >>
     drule_all fresh_inst_id_contract >> strip_tac >>
     gvs[cfg_forwarding_supply_contract_def,
         cfg_insts_id_declared_def,cfg_insts_var_declared_def] >>
     metis_tac[cfg_supply_extends_trans]
QED

Theorem build_split_block_supply_contract:
  ir_supply_inst_ok s /\
  build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') ==>
  cfg_block_supply_contract s split_bb s'
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (split_label,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
              (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
                       target_bb.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ =
           (var_repls,fwd_insts,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (jmp_id,s3)` >>
  gvs[build_split_block_supply_def] >>
  `cfg_supply_extends s s1` by
    metis_tac[fresh_ir_label_cfg_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
  `cfg_forwarding_supply_contract s1 fwd_insts s2` by
    metis_tac[build_forwarding_assigns_supply_contract] >>
  `cfg_supply_extends s1 s2` by
    gvs[cfg_forwarding_supply_contract_def] >>
  `ir_supply_inst_ok s2` by gvs[cfg_supply_extends_def] >>
  `cfg_supply_extends s2 s'` by
    metis_tac[fresh_inst_id_cfg_supply_extends] >>
  drule fresh_ir_label_contract >> strip_tac >>
  drule_all fresh_inst_id_contract >> strip_tac >>
  gvs[cfg_block_supply_contract_def,
      cfg_forwarding_supply_contract_def,
      cfg_insts_id_declared_def,cfg_insts_var_declared_def] >>
  metis_tac[cfg_supply_extends_trans]
QED


Theorem cfg_insts_id_declared_subst_label_terminator[simp]:
  cfg_insts_id_declared
    (subst_label_terminator old new bb).bb_instructions id <=>
  cfg_insts_id_declared bb.bb_instructions id
Proof
  simp[cfg_insts_id_declared_def,subst_label_terminator_def,
       subst_label_inst_def,listTheory.EXISTS_MAP,COND_RAND] >> metis_tac[]
QED

Theorem cfg_insts_var_declared_subst_label_terminator[simp]:
  cfg_insts_var_declared
    (subst_label_terminator old new bb).bb_instructions v <=>
  cfg_insts_var_declared bb.bb_instructions v
Proof
  simp[cfg_insts_var_declared_def,subst_label_terminator_def,
       subst_label_inst_def,listTheory.EXISTS_MAP,COND_RAND] >> metis_tac[]
QED

Theorem cfg_insts_id_declared_update_phis_for_split[simp]:
  cfg_insts_id_declared
    (update_phis_for_split old new repls bb).bb_instructions id <=>
  cfg_insts_id_declared bb.bb_instructions id
Proof
  simp[cfg_insts_id_declared_def,update_phis_for_split_def,
       listTheory.EXISTS_MAP,COND_RAND] >> metis_tac[]
QED

Theorem cfg_insts_var_declared_update_phis_for_split[simp]:
  cfg_insts_var_declared
    (update_phis_for_split old new repls bb).bb_instructions v <=>
  cfg_insts_var_declared bb.bb_instructions v
Proof
  simp[cfg_insts_var_declared_def,update_phis_for_split_def,
       listTheory.EXISTS_MAP,COND_RAND] >> metis_tac[]
QED


Definition cfg_fn_id_declared_def:
  cfg_fn_id_declared fn id <=>
    EXISTS (\bb. cfg_insts_id_declared bb.bb_instructions id) fn.fn_blocks
End

Definition cfg_fn_var_declared_def:
  cfg_fn_var_declared fn v <=>
    EXISTS (\bb. cfg_insts_var_declared bb.bb_instructions v) fn.fn_blocks
End

Definition cfg_fn_label_declared_def:
  cfg_fn_label_declared fn l <=>
    EXISTS (\bb. bb.bb_label = l) fn.fn_blocks
End

Definition cfg_fn_supply_contract_def:
  cfg_fn_supply_contract s fn s' <=>
    cfg_supply_extends s s' /\
    (!id. MEM id s'.irs_used_inst_ids /\
          ~MEM id s.irs_used_inst_ids ==> cfg_fn_id_declared fn id) /\
    (!v. MEM v s'.irs_used_vars /\
         ~MEM v s.irs_used_vars ==> cfg_fn_var_declared fn v) /\
    (!l. MEM l s'.irs_used_labels /\
         ~MEM l s.irs_used_labels ==> cfg_fn_label_declared fn l)
End

Theorem insert_split_supply_contract:
  ir_supply_inst_ok s /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  cfg_fn_supply_contract s fn' s'
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  rename1 `build_split_block_supply s pred_bb target_bb =
           (split_bb,repls,s1)` >>
  gvs[insert_split_supply_def] >>
  drule_all build_split_block_supply_contract >>
  strip_tac >>
  gvs[cfg_fn_supply_contract_def,cfg_block_supply_contract_def,
      cfg_fn_id_declared_def,cfg_fn_var_declared_def,
      cfg_fn_label_declared_def] >>
  metis_tac[]
QED


Theorem find_and_split_supply_contract:
  !bbs fn s fn' changed s'.
    ir_supply_inst_ok s /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    cfg_fn_supply_contract s fn' s'
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[find_and_split_supply_def,cfg_fn_supply_contract_def,
          cfg_supply_extends_refl]
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     metis_tac[insert_split_supply_contract]
QED

Theorem cfg_norm_round_supply_contract:
  ir_supply_inst_ok s /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  cfg_fn_supply_contract s fn' s'
Proof
  simp[cfg_norm_round_supply_def] >>
  metis_tac[find_and_split_supply_contract]
QED


Theorem build_forwarding_assigns_supply_repls_covered:
  !vars s repls insts s'.
    ir_supply_inst_ok s /\
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    EVERY (\p. MEM (SND p) s'.irs_used_vars) repls
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def]
  >> Cases_on `fresh_ir_var s` >>
     rename1 `fresh_ir_var s = (new_var,s1)` >>
     Cases_on `fresh_inst_id s1` >>
     rename1 `fresh_inst_id s1 = (id,s2)` >>
     Cases_on `build_forwarding_assigns_supply s2 vars` >>
     PairCases_on `r` >>
     rename1 `build_forwarding_assigns_supply s2 vars =
              (rest_repls,rest_insts,s3)` >>
     gvs[build_forwarding_assigns_supply_def] >>
     `cfg_supply_extends s s1` by
       metis_tac[fresh_ir_var_cfg_supply_extends] >>
     `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
     `cfg_supply_extends s1 s2` by
       metis_tac[fresh_inst_id_cfg_supply_extends] >>
     `ir_supply_inst_ok s2` by gvs[cfg_supply_extends_def] >>
     `cfg_forwarding_supply_contract s2 rest_insts s'` by
       metis_tac[build_forwarding_assigns_supply_contract] >>
     `cfg_supply_extends s2 s'` by
       gvs[cfg_forwarding_supply_contract_def] >>
     `EVERY (\p. MEM (SND p) s'.irs_used_vars) rest_repls` by
       metis_tac[] >>
     drule fresh_ir_var_contract >> strip_tac >>
     `MEM new_var s1.irs_used_vars` by simp[] >>
     `MEM new_var s2.irs_used_vars` by
       metis_tac[cfg_supply_extends_members] >>
     `MEM new_var s'.irs_used_vars` by
       metis_tac[cfg_supply_extends_members] >>
     gvs[]
QED


Definition cfg_supply_covers_fn_def:
  cfg_supply_covers_fn s fn <=>
    EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn) /\
    EVERY (\v. MEM v s.irs_used_vars) (fn_ir_vars fn) /\
    EVERY (\l. MEM l s.irs_used_labels) (fn_ir_labels fn)
End

Theorem ALOOKUP_SND_covered:
  !repls k v P.
    EVERY (\p. P (SND p)) repls /\ ALOOKUP repls k = SOME v ==> P v
Proof
  Induct_on `repls` >> rpt strip_tac
  >- gvs[]
  >> PairCases_on `h` >> gvs[] >>
     Cases_on `h0 = k` >> gvs[] >> metis_tac[]
QED

Theorem operand_vars_update_phi_ops_covered:
  !old new repls ops s.
    EVERY (\v. MEM v s.irs_used_vars) (operand_vars ops) /\
    EVERY (\p. MEM (SND p) s.irs_used_vars) repls ==>
    EVERY (\v. MEM v s.irs_used_vars)
      (operand_vars (update_phi_ops old new repls ops))
Proof
  recInduct update_phi_ops_ind >>
  rpt strip_tac >>
  TRY (Cases_on `l = old_label`) >>
  TRY (Cases_on `val_op`) >>
  TRY (Cases_on `y`) >>
  TRY (Cases_on `ALOOKUP var_repls s'`) >>
  gvs[update_phi_ops_def,venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def,AllCaseEqs()] >>
  imp_res_tac ALOOKUP_SND_covered >>
  gvs[]
QED


Theorem operand_ir_labels_update_phi_ops_covered:
  !old new repls ops s.
    EVERY (\l. MEM l s.irs_used_labels) (operand_ir_labels ops) /\
    MEM new s.irs_used_labels ==>
    EVERY (\l. MEM l s.irs_used_labels)
      (operand_ir_labels (update_phi_ops old new repls ops))
Proof
  recInduct update_phi_ops_ind >>
  rpt strip_tac >>
  TRY (Cases_on `l = old_label`) >>
  TRY (Cases_on `val_op`) >>
  TRY (Cases_on `y`) >>
  TRY (Cases_on `ALOOKUP var_repls s'`) >>
  gvs[update_phi_ops_def,operand_ir_labels_def]
QED

Theorem operand_ir_labels_subst_label_ops_covered:
  !ops old new s.
    EVERY (\l. MEM l s.irs_used_labels) (operand_ir_labels ops) /\
    MEM new s.irs_used_labels ==>
    EVERY (\l. MEM l s.irs_used_labels)
      (operand_ir_labels (MAP (subst_label_op old new) ops))
Proof
  Induct_on `ops` >> rpt strip_tac
  >- gvs[operand_ir_labels_def]
  >> Cases_on `h` >>
     gvs[operand_ir_labels_def,subst_label_op_def] >>
     Cases_on `s' = old` >> gvs[operand_ir_labels_def]
QED

Definition cfg_supply_covers_block_def:
  cfg_supply_covers_block s bb <=>
    EVERY (\id. MEM id s.irs_used_inst_ids) (block_ir_inst_ids bb) /\
    EVERY (\v. MEM v s.irs_used_vars) (block_ir_vars bb) /\
    EVERY (\l. MEM l s.irs_used_labels) (block_ir_labels bb)
End


Theorem operand_vars_subst_label_ops[simp]:
  !ops old new.
    operand_vars (MAP (subst_label_op old new) ops) = operand_vars ops
Proof
  Induct_on `ops` >> rpt gen_tac
  >- simp[venomInstTheory.operand_vars_def]
  >> Cases_on `h` >>
     TRY (Cases_on `s = old`) >>
     simp[venomInstTheory.operand_vars_def,venomInstTheory.operand_var_def,
          subst_label_op_def]
QED

Theorem inst_ir_vars_subst_label_inst[simp]:
  inst_ir_vars (subst_label_inst old new inst) = inst_ir_vars inst
Proof
  simp[inst_ir_vars_def,venomInstTheory.inst_uses_def,subst_label_inst_def]
QED

Theorem inst_ir_labels_subst_label_inst_covered:
  EVERY (\l. MEM l s.irs_used_labels) (inst_ir_labels inst) /\
  MEM new s.irs_used_labels ==>
  EVERY (\l. MEM l s.irs_used_labels)
    (inst_ir_labels (subst_label_inst old new inst))
Proof
  simp[inst_ir_labels_def,subst_label_inst_def] >>
  metis_tac[operand_ir_labels_subst_label_ops_covered]
QED

Theorem inst_ir_vars_update_phi_ops_covered:
  EVERY (\v. MEM v s.irs_used_vars) (inst_ir_vars inst) /\
  EVERY (\p. MEM (SND p) s.irs_used_vars) repls ==>
  EVERY (\v. MEM v s.irs_used_vars)
    (inst_ir_vars (inst with inst_operands :=
      update_phi_ops old new repls inst.inst_operands))
Proof
  simp[inst_ir_vars_def,venomInstTheory.inst_uses_def] >>
  metis_tac[operand_vars_update_phi_ops_covered]
QED

Theorem inst_ir_labels_update_phi_ops_covered:
  EVERY (\l. MEM l s.irs_used_labels) (inst_ir_labels inst) /\
  MEM new s.irs_used_labels ==>
  EVERY (\l. MEM l s.irs_used_labels)
    (inst_ir_labels (inst with inst_operands :=
      update_phi_ops old new repls inst.inst_operands))
Proof
  simp[inst_ir_labels_def] >>
  metis_tac[operand_ir_labels_update_phi_ops_covered]
QED


Theorem block_ir_inst_ids_subst_label_terminator[simp]:
  block_ir_inst_ids (subst_label_terminator old new bb) =
  block_ir_inst_ids bb
Proof
  simp[block_ir_inst_ids_def,subst_label_terminator_def,
       listTheory.MAP_MAP_o,combinTheory.o_DEF,subst_label_inst_def,COND_RAND]
QED

Theorem block_ir_vars_subst_label_terminator[simp]:
  block_ir_vars (subst_label_terminator old new bb) = block_ir_vars bb
Proof
  simp[block_ir_vars_def,subst_label_terminator_def,
       listTheory.MAP_MAP_o,combinTheory.o_DEF,COND_RAND] >>
  AP_TERM_TAC >> simp[listTheory.MAP_EQ_f]
QED

Theorem EVERY_inst_ir_labels_subst_terminator_covered:
  EVERY (\inst. EVERY (\l. MEM l s.irs_used_labels)
                    (inst_ir_labels inst)) insts /\
  MEM new s.irs_used_labels ==>
  EVERY (\inst. EVERY (\l. MEM l s.irs_used_labels)
                    (inst_ir_labels
                      (if is_terminator inst.inst_opcode then
                         subst_label_inst old new inst else inst))) insts
Proof
  rpt strip_tac >>
  gvs[listTheory.EVERY_MEM] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (gvs[] >> rpt strip_tac >>
      `EVERY (\l. MEM l s.irs_used_labels)
         (inst_ir_labels (subst_label_inst old new inst))` by
        (irule inst_ir_labels_subst_label_inst_covered >>
         simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
      gvs[listTheory.EVERY_MEM])
  >> gvs[] >> metis_tac[]
QED

Theorem cfg_supply_covers_block_subst_label_terminator:
  cfg_supply_covers_block s bb /\ MEM new s.irs_used_labels ==>
  cfg_supply_covers_block s (subst_label_terminator old new bb)
Proof
  rpt strip_tac >>
  gvs[cfg_supply_covers_block_def] >>
  gvs[block_ir_labels_def,subst_label_terminator_def,
      listTheory.MAP_MAP_o,combinTheory.o_DEF,listTheory.EVERY_FLAT,
      listTheory.EVERY_MAP] >>
  irule EVERY_inst_ir_labels_subst_terminator_covered >>
  simp[]
QED

Theorem block_ir_inst_ids_update_phis_for_split[simp]:
  block_ir_inst_ids (update_phis_for_split old new repls bb) =
  block_ir_inst_ids bb
Proof
  simp[block_ir_inst_ids_def,update_phis_for_split_def,
       listTheory.MAP_MAP_o,combinTheory.o_DEF,COND_RAND]
QED

Theorem EVERY_inst_ir_vars_update_phis_covered:
  EVERY (\inst. EVERY (\v. MEM v s.irs_used_vars) (inst_ir_vars inst)) insts /\
  EVERY (\p. MEM (SND p) s.irs_used_vars) repls ==>
  EVERY (\inst. EVERY (\v. MEM v s.irs_used_vars)
             (inst_ir_vars
               (if inst.inst_opcode <> PHI then inst else
                  inst with inst_operands :=
                    update_phi_ops old new repls inst.inst_operands))) insts
Proof
  rpt strip_tac >> gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode <> PHI`
  >- (gvs[] >> metis_tac[])
  >> gvs[] >>
     `EVERY (\v. MEM v s.irs_used_vars)
       (inst_ir_vars (inst with inst_operands :=
          update_phi_ops old new repls inst.inst_operands))` by
       (irule inst_ir_vars_update_phi_ops_covered >>
        simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
     gvs[listTheory.EVERY_MEM]
QED

Theorem EVERY_inst_ir_labels_update_phis_covered:
  EVERY (\inst. EVERY (\l. MEM l s.irs_used_labels) (inst_ir_labels inst)) insts /\
  MEM new s.irs_used_labels ==>
  EVERY (\inst. EVERY (\l. MEM l s.irs_used_labels)
             (inst_ir_labels
               (if inst.inst_opcode <> PHI then inst else
                  inst with inst_operands :=
                    update_phi_ops old new repls inst.inst_operands))) insts
Proof
  rpt strip_tac >> gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  Cases_on `inst.inst_opcode <> PHI`
  >- (gvs[] >> metis_tac[])
  >> gvs[] >>
     `EVERY (\l. MEM l s.irs_used_labels)
       (inst_ir_labels (inst with inst_operands :=
          update_phi_ops old new repls inst.inst_operands))` by
       (irule inst_ir_labels_update_phi_ops_covered >>
        simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
     gvs[listTheory.EVERY_MEM]
QED

Theorem cfg_supply_covers_block_update_phis_for_split:
  cfg_supply_covers_block s bb /\
  EVERY (\p. MEM (SND p) s.irs_used_vars) repls /\
  MEM new s.irs_used_labels ==>
  cfg_supply_covers_block s (update_phis_for_split old new repls bb)
Proof
  rpt strip_tac >>
  gvs[cfg_supply_covers_block_def] >>
  conj_tac
  >- (gvs[block_ir_vars_def,update_phis_for_split_def,
          listTheory.MAP_MAP_o,combinTheory.o_DEF,listTheory.EVERY_FLAT,
          listTheory.EVERY_MAP] >>
      irule EVERY_inst_ir_vars_update_phis_covered >> simp[])
  >> gvs[block_ir_labels_def,update_phis_for_split_def,
         listTheory.MAP_MAP_o,combinTheory.o_DEF,listTheory.EVERY_FLAT,
         listTheory.EVERY_MAP] >>
     irule EVERY_inst_ir_labels_update_phis_covered >> simp[]
QED


Theorem cfg_supply_covers_fn_blocks:
  cfg_supply_covers_fn s fn <=>
  MEM fn.fn_name s.irs_used_labels /\
  EVERY (cfg_supply_covers_block s) fn.fn_blocks
Proof
  simp[cfg_supply_covers_fn_def,cfg_supply_covers_block_def,
       fn_ir_inst_ids_def,fn_ir_vars_def,fn_ir_labels_def,
       listTheory.EVERY_FLAT,listTheory.EVERY_MAP,listTheory.EVERY_MEM,
       listTheory.MEM_FLAT,listTheory.MEM_MAP] >>
  metis_tac[]
QED

Theorem cfg_supply_covers_fn_mono:
  cfg_supply_covers_fn s fn /\ cfg_supply_extends s s' ==>
  cfg_supply_covers_fn s' fn
Proof
  simp[cfg_supply_covers_fn_def,listTheory.EVERY_MEM] >>
  metis_tac[cfg_supply_extends_members]
QED

Theorem EVERY_replace_block_covered:
  EVERY P bbs /\ P bb' ==>
  EVERY P (replace_block lbl bb' bbs)
Proof
  Induct_on `bbs` >> simp[replace_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >>
  gvs[replace_block_def]
QED


Theorem MEM_phi_pairs_SND_operand_vars:
  !ops l v. MEM (l,v) (phi_pairs ops) ==> MEM v (operand_vars ops)
Proof
  recInduct venomInstTheory.phi_pairs_ind >>
  rpt strip_tac >>
  gvs[venomInstTheory.phi_pairs_def,venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def] >>
  TRY (Cases_on `v1`) >>
  gvs[venomInstTheory.operand_var_def] >>
  first_x_assum drule >> simp[venomInstTheory.operand_var_def]
QED
Theorem MEM_phi_pairs_SND_operand_vars_pair:
  MEM p (phi_pairs ops) ==> MEM (SND p) (operand_vars ops)
Proof
  PairCases_on `p` >> simp[] >> rpt strip_tac >>
  irule MEM_phi_pairs_SND_operand_vars >> qexists `p0` >> simp[]
QED


Theorem MEM_phi_vars_needing_forward_block_vars:
  !insts pred_label pred_bb v.
    MEM v (phi_vars_needing_forward pred_label pred_bb insts) ==>
    MEM v (FLAT (MAP inst_ir_vars insts))
Proof
  Induct_on `insts` >> rpt strip_tac
  >- gvs[phi_vars_needing_forward_def]
  >> Cases_on `h.inst_opcode <> PHI`
  >- (gvs[phi_vars_needing_forward_def] >> metis_tac[])
  >> gvs[phi_vars_needing_forward_def,listTheory.MEM_MAP,
         listTheory.MEM_FILTER] >>
     imp_res_tac MEM_phi_pairs_SND_operand_vars_pair >>
     simp[inst_ir_vars_def,venomInstTheory.inst_uses_def] >> metis_tac[]
QED

Theorem EVERY_phi_vars_needing_forward_covered:
  EVERY (\v. MEM v s.irs_used_vars) (block_ir_vars target_bb) ==>
  EVERY (\v. MEM v s.irs_used_vars)
    (nub (phi_vars_needing_forward pred_label pred_bb
            target_bb.bb_instructions))
Proof
  simp[block_ir_vars_def,listTheory.EVERY_MEM] >>
  metis_tac[MEM_phi_vars_needing_forward_block_vars]
QED


Definition cfg_supply_covers_insts_def:
  cfg_supply_covers_insts s insts <=>
    EVERY (\id. MEM id s.irs_used_inst_ids) (MAP (\i. i.inst_id) insts) /\
    EVERY (\v. MEM v s.irs_used_vars) (FLAT (MAP inst_ir_vars insts)) /\
    EVERY (\l. MEM l s.irs_used_labels) (FLAT (MAP inst_ir_labels insts))
End

Theorem build_forwarding_assigns_supply_covered:
  !vars s repls insts s'.
    ir_supply_inst_ok s /\
    EVERY (\v. MEM v s.irs_used_vars) vars /\
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    cfg_supply_covers_insts s' insts
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def,cfg_supply_covers_insts_def]
  >> Cases_on `fresh_ir_var s` >>
     rename1 `fresh_ir_var s = (new_var,s1)` >>
     Cases_on `fresh_inst_id s1` >>
     rename1 `fresh_inst_id s1 = (id,s2)` >>
     Cases_on `build_forwarding_assigns_supply s2 vars` >>
     PairCases_on `r` >>
     rename1 `build_forwarding_assigns_supply s2 vars =
              (rest_repls,rest_insts,s3)` >>
     gvs[build_forwarding_assigns_supply_def] >>
     `cfg_supply_extends s s1` by
       metis_tac[fresh_ir_var_cfg_supply_extends] >>
     `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
     `cfg_supply_extends s1 s2` by
       metis_tac[fresh_inst_id_cfg_supply_extends] >>
     `ir_supply_inst_ok s2` by gvs[cfg_supply_extends_def] >>
     `cfg_forwarding_supply_contract s2 rest_insts s'` by
       metis_tac[build_forwarding_assigns_supply_contract] >>
     `cfg_supply_extends s2 s'` by
       gvs[cfg_forwarding_supply_contract_def] >>
     `EVERY (\v. MEM v s2.irs_used_vars) vars` by
       (gvs[listTheory.EVERY_MEM] >>
        metis_tac[cfg_supply_extends_members]) >>
     `cfg_supply_covers_insts s' rest_insts` by metis_tac[] >>
     drule fresh_ir_var_contract >> strip_tac >>
     drule_all fresh_inst_id_contract >> strip_tac >>
     `MEM new_var s1.irs_used_vars` by simp[] >>
     `MEM new_var s2.irs_used_vars` by
       metis_tac[cfg_supply_extends_members] >>
     `MEM new_var s'.irs_used_vars` by
       metis_tac[cfg_supply_extends_members] >>
     `MEM id s2.irs_used_inst_ids` by simp[] >>
     `MEM id s'.irs_used_inst_ids` by
       metis_tac[cfg_supply_extends_members] >>
     `MEM h s1.irs_used_vars` by
       metis_tac[cfg_supply_extends_members] >>
     `MEM h s2.irs_used_vars` by
       metis_tac[cfg_supply_extends_members] >>
     `MEM h s'.irs_used_vars` by
       metis_tac[cfg_supply_extends_members] >>
     gvs[cfg_supply_covers_insts_def,inst_ir_vars_def,
         venomInstTheory.inst_uses_def,venomInstTheory.operand_vars_def,
         venomInstTheory.operand_var_def,inst_ir_labels_def,
         operand_ir_labels_def]
QED


Theorem cfg_supply_covers_block_insts:
  cfg_supply_covers_block s bb <=>
  MEM bb.bb_label s.irs_used_labels /\
  cfg_supply_covers_insts s bb.bb_instructions
Proof
  simp[cfg_supply_covers_block_def,cfg_supply_covers_insts_def,
       block_ir_inst_ids_def,block_ir_vars_def,block_ir_labels_def] >>
  metis_tac[]
QED

Theorem cfg_supply_covers_insts_mono:
  cfg_supply_covers_insts s insts /\ cfg_supply_extends s s' ==>
  cfg_supply_covers_insts s' insts
Proof
  simp[cfg_supply_covers_insts_def,listTheory.EVERY_MEM] >>
  metis_tac[cfg_supply_extends_members]
QED

Theorem build_split_block_supply_covered:
  ir_supply_inst_ok s /\
  cfg_supply_covers_block s target_bb /\
  build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') ==>
  cfg_supply_covers_block s' split_bb
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (split_label,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
              (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
                      target_bb.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ =
           (var_repls,fwd_insts,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (jmp_id,s3)` >>
  gvs[build_split_block_supply_def] >>
  `cfg_supply_extends s s1` by
    metis_tac[fresh_ir_label_cfg_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
  `EVERY (\v. MEM v s.irs_used_vars)
     (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
             target_bb.bb_instructions))` by
    (irule EVERY_phi_vars_needing_forward_covered >>
     gvs[cfg_supply_covers_block_def]) >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
             target_bb.bb_instructions))` by
    (gvs[listTheory.EVERY_MEM] >>
     metis_tac[cfg_supply_extends_members]) >>
  `cfg_supply_covers_insts s2 fwd_insts` by
    metis_tac[build_forwarding_assigns_supply_covered] >>
  `cfg_forwarding_supply_contract s1 fwd_insts s2` by
    metis_tac[build_forwarding_assigns_supply_contract] >>
  `cfg_supply_extends s1 s2` by
    gvs[cfg_forwarding_supply_contract_def] >>
  `ir_supply_inst_ok s2` by gvs[cfg_supply_extends_def] >>
  `cfg_supply_extends s2 s'` by
    metis_tac[fresh_inst_id_cfg_supply_extends] >>
  `cfg_supply_covers_insts s' fwd_insts` by
    metis_tac[cfg_supply_covers_insts_mono] >>
  drule fresh_ir_label_contract >> strip_tac >>
  drule_all fresh_inst_id_contract >> strip_tac >>
  `MEM split_label s1.irs_used_labels` by simp[] >>
  `MEM split_label s2.irs_used_labels` by
    metis_tac[cfg_supply_extends_members] >>
  `MEM split_label s'.irs_used_labels` by
    metis_tac[cfg_supply_extends_members] >>
  `MEM target_bb.bb_label s.irs_used_labels` by
    gvs[cfg_supply_covers_block_insts] >>
  `MEM target_bb.bb_label s1.irs_used_labels` by
    metis_tac[cfg_supply_extends_members] >>
  `MEM target_bb.bb_label s2.irs_used_labels` by
    metis_tac[cfg_supply_extends_members] >>
  `MEM target_bb.bb_label s'.irs_used_labels` by
    metis_tac[cfg_supply_extends_members] >>
  `MEM jmp_id s'.irs_used_inst_ids` by simp[] >>
  gvs[cfg_supply_covers_block_insts,cfg_supply_covers_insts_def,
      inst_ir_vars_def,venomInstTheory.inst_uses_def,
      venomInstTheory.operand_vars_def,venomInstTheory.operand_var_def,
      inst_ir_labels_def,operand_ir_labels_def]
QED


Theorem build_split_block_supply_repls_covered:
  ir_supply_inst_ok s /\
  build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') ==>
  EVERY (\p. MEM (SND p) s'.irs_used_vars) repls
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (split_label,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
              (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
                      target_bb.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ =
           (var_repls,fwd_insts,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (jmp_id,s3)` >>
  gvs[build_split_block_supply_def] >>
  `cfg_supply_extends s s1` by
    metis_tac[fresh_ir_label_cfg_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
  `EVERY (\p. MEM (SND p) s2.irs_used_vars) repls` by
    (irule build_forwarding_assigns_supply_repls_covered >> simp[] >>
     metis_tac[]) >>
  `cfg_forwarding_supply_contract s1 fwd_insts s2` by
    metis_tac[build_forwarding_assigns_supply_contract] >>
  `ir_supply_inst_ok s2` by
    gvs[cfg_forwarding_supply_contract_def,cfg_supply_extends_def] >>
  `cfg_supply_extends s2 s'` by
    metis_tac[fresh_inst_id_cfg_supply_extends] >>
  gvs[listTheory.EVERY_MEM] >>
  metis_tac[cfg_supply_extends_members]
QED

Theorem cfg_supply_covers_block_mono:
  cfg_supply_covers_block s bb /\ cfg_supply_extends s s' ==>
  cfg_supply_covers_block s' bb
Proof
  simp[cfg_supply_covers_block_def,listTheory.EVERY_MEM] >>
  metis_tac[cfg_supply_extends_members]
QED

Theorem insert_split_supply_covered:
  ir_supply_inst_ok s /\
  cfg_supply_covers_fn s fn /\
  cfg_supply_covers_block s pred_bb /\
  cfg_supply_covers_block s target_bb /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  cfg_supply_covers_fn s' fn'
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  rename1 `build_split_block_supply s pred_bb target_bb =
           (split_bb,repls,s1)` >>
  gvs[insert_split_supply_def] >>
  `cfg_block_supply_contract s split_bb s'` by
    metis_tac[build_split_block_supply_contract] >>
  `cfg_supply_extends s s'` by
    gvs[cfg_block_supply_contract_def] >>
  `cfg_supply_covers_fn s' fn` by
    metis_tac[cfg_supply_covers_fn_mono] >>
  `cfg_supply_covers_block s' pred_bb` by
    metis_tac[cfg_supply_covers_block_mono] >>
  `cfg_supply_covers_block s' target_bb` by
    metis_tac[cfg_supply_covers_block_mono] >>
  `cfg_supply_covers_block s' split_bb` by
    metis_tac[build_split_block_supply_covered] >>
  `EVERY (\p. MEM (SND p) s'.irs_used_vars) repls` by
    metis_tac[build_split_block_supply_repls_covered] >>
  `cfg_supply_covers_block s'
     (subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb)` by
    (irule cfg_supply_covers_block_subst_label_terminator >>
     gvs[cfg_supply_covers_block_insts]) >>
  `cfg_supply_covers_block s'
     (update_phis_for_split pred_bb.bb_label split_bb.bb_label repls target_bb)` by
    (irule cfg_supply_covers_block_update_phis_for_split >>
     gvs[cfg_supply_covers_block_insts]) >>
  gvs[cfg_supply_covers_fn_blocks] >>
  irule EVERY_replace_block_covered >> simp[] >>
  irule EVERY_replace_block_covered >> simp[]
QED


Theorem FIND_SOME_MEM:
  !P xs x. FIND P xs = SOME x ==> MEM x xs
Proof
  Induct_on `xs` >> simp[listTheory.FIND_thm] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[listTheory.FIND_thm] >> metis_tac[]
QED

Theorem find_and_split_supply_covered:
  !bbs fn s fn' changed s'.
    ir_supply_inst_ok s /\
    cfg_supply_covers_fn s fn /\
    EVERY (cfg_supply_covers_block s) bbs /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    cfg_supply_covers_fn s' fn'
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[find_and_split_supply_def]
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     `MEM x (block_preds fn h.bb_label)` by
       metis_tac[FIND_SOME_MEM] >>
     `MEM x fn.fn_blocks` by
       gvs[block_preds_def,listTheory.MEM_FILTER] >>
     `cfg_supply_covers_block s x` by
       (gvs[cfg_supply_covers_fn_blocks,listTheory.EVERY_MEM] >>
        metis_tac[]) >>
     irule insert_split_supply_covered >>
     qexistsl [`fn`,`x`,`s`,`h`] >> simp[]
QED

Theorem cfg_norm_round_supply_covered:
  ir_supply_inst_ok s /\
  cfg_supply_covers_fn s fn /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  cfg_supply_covers_fn s' fn'
Proof
  rpt strip_tac >>
  irule find_and_split_supply_covered >>
  qexistsl [`fn.fn_blocks`,`changed`,`fn`,`s`] >>
  gvs[cfg_norm_round_supply_def,cfg_supply_covers_fn_blocks]
QED


Theorem EVERY_not_MEM:
  EVERY (\x. ~MEM x ys) xs /\ MEM y ys ==> ~MEM y xs
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem build_forwarding_assigns_supply_ids_fresh:
  !vars s repls insts s'.
    ir_supply_inst_ok s /\
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    EVERY (\id. ~MEM id s.irs_used_inst_ids)
      (MAP (\i. i.inst_id) insts)
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def]
  >> Cases_on `fresh_ir_var s` >>
     rename1 `fresh_ir_var s = (new_var,s1)` >>
     Cases_on `fresh_inst_id s1` >>
     rename1 `fresh_inst_id s1 = (id,s2)` >>
     Cases_on `build_forwarding_assigns_supply s2 vars` >>
     PairCases_on `r` >>
     rename1 `build_forwarding_assigns_supply s2 vars =
              (rest_repls,rest_insts,s3)` >>
     gvs[build_forwarding_assigns_supply_def] >>
     `cfg_supply_extends s s1` by
       metis_tac[fresh_ir_var_cfg_supply_extends] >>
     `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
     `cfg_supply_extends s1 s2` by
       metis_tac[fresh_inst_id_cfg_supply_extends] >>
     `ir_supply_inst_ok s2` by gvs[cfg_supply_extends_def] >>
     `ALL_DISTINCT (MAP (\i. i.inst_id) rest_insts) /\
      EVERY (\rid. ~MEM rid s2.irs_used_inst_ids)
        (MAP (\i. i.inst_id) rest_insts)` by metis_tac[] >>
     drule_all fresh_inst_id_contract >> strip_tac >>
     `MEM id s2.irs_used_inst_ids` by simp[] >>
     `~MEM id (MAP (\i. i.inst_id) rest_insts)` by
       metis_tac[EVERY_not_MEM] >>
     `cfg_supply_extends s s2` by
       metis_tac[cfg_supply_extends_trans] >>
     `EVERY (\rid. ~MEM rid s.irs_used_inst_ids)
        (MAP (\i. i.inst_id) rest_insts)` by
       (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
        `MEM rid s2.irs_used_inst_ids` by
          metis_tac[cfg_supply_extends_members] >>
        metis_tac[]) >>
     gvs[] >>
     metis_tac[cfg_supply_extends_members]
QED


Theorem build_forwarding_assigns_supply_ids_covered:
  !vars s repls insts s'.
    ir_supply_inst_ok s /\
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    EVERY (\id. MEM id s'.irs_used_inst_ids) (MAP (\i. i.inst_id) insts)
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def]
  >> Cases_on `fresh_ir_var s` >>
     rename1 `fresh_ir_var s = (new_var,s1)` >>
     Cases_on `fresh_inst_id s1` >>
     rename1 `fresh_inst_id s1 = (id,s2)` >>
     Cases_on `build_forwarding_assigns_supply s2 vars` >>
     PairCases_on `r` >>
     rename1 `build_forwarding_assigns_supply s2 vars =
              (rest_repls,rest_insts,s3)` >>
     gvs[build_forwarding_assigns_supply_def] >>
     `cfg_supply_extends s s1` by
       metis_tac[fresh_ir_var_cfg_supply_extends] >>
     `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
     `cfg_supply_extends s1 s2` by
       metis_tac[fresh_inst_id_cfg_supply_extends] >>
     `ir_supply_inst_ok s2` by gvs[cfg_supply_extends_def] >>
     `cfg_forwarding_supply_contract s2 rest_insts s'` by
       metis_tac[build_forwarding_assigns_supply_contract] >>
     `cfg_supply_extends s2 s'` by
       gvs[cfg_forwarding_supply_contract_def] >>
     `EVERY (\rid. MEM rid s'.irs_used_inst_ids)
        (MAP (\i. i.inst_id) rest_insts)` by metis_tac[] >>
     drule_all fresh_inst_id_contract >> strip_tac >>
     `MEM id s2.irs_used_inst_ids` by simp[] >>
     `MEM id s'.irs_used_inst_ids` by
       metis_tac[cfg_supply_extends_members] >>
     gvs[]
QED

Theorem EVERY_MEM_not:
  EVERY (\x. MEM x ys) xs /\ ~MEM y ys ==> ~MEM y xs
Proof
  simp[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem build_split_block_supply_ids_fresh:
  ir_supply_inst_ok s /\
  build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') ==>
  ALL_DISTINCT (block_ir_inst_ids split_bb) /\
  EVERY (\id. ~MEM id s.irs_used_inst_ids) (block_ir_inst_ids split_bb)
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (split_label,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
              (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
                      target_bb.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ =
           (var_repls,fwd_insts,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (jmp_id,s3)` >>
  gvs[build_split_block_supply_def] >>
  `cfg_supply_extends s s1` by
    metis_tac[fresh_ir_label_cfg_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) fwd_insts) /\
   EVERY (\id. ~MEM id s1.irs_used_inst_ids)
     (MAP (\i. i.inst_id) fwd_insts)` by
    metis_tac[build_forwarding_assigns_supply_ids_fresh] >>
  `cfg_forwarding_supply_contract s1 fwd_insts s2` by
    metis_tac[build_forwarding_assigns_supply_contract] >>
  `cfg_supply_extends s1 s2` by
    gvs[cfg_forwarding_supply_contract_def] >>
  `ir_supply_inst_ok s2` by gvs[cfg_supply_extends_def] >>
  `EVERY (\id. MEM id s2.irs_used_inst_ids)
     (MAP (\i. i.inst_id) fwd_insts)` by
    metis_tac[build_forwarding_assigns_supply_ids_covered] >>
  drule_all fresh_inst_id_contract >> strip_tac >>
  `~MEM jmp_id (MAP (\i. i.inst_id) fwd_insts)` by
    metis_tac[EVERY_MEM_not] >>
  `EVERY (\id. ~MEM id s.irs_used_inst_ids)
     (MAP (\i. i.inst_id) fwd_insts)` by
    (gvs[listTheory.EVERY_MEM,cfg_supply_extends_def] >> metis_tac[]) >>
  `~MEM jmp_id s.irs_used_inst_ids` by
    (gvs[cfg_supply_extends_def] >> metis_tac[]) >>
  gvs[block_ir_inst_ids_def,listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_MEM] >>
  metis_tac[]
QED


Theorem all_distinct_map_mem_inj_cfg:
  !f xs a b.
    ALL_DISTINCT (MAP f xs) /\ MEM a xs /\ MEM b xs /\ f a = f b ==>
    a = b
Proof
  rpt strip_tac >> gvs[listTheory.MEM_EL] >>
  metis_tac[listTheory.ALL_DISTINCT_EL_IMP,listTheory.LENGTH_MAP,
            listTheory.EL_MAP]
QED

Theorem FLAT_MAP_replace_block_preserved:
  !bbs lbl new_bb C.
    EVERY (\b. b.bb_label = lbl ==> C b = C new_bb) bbs ==>
    FLAT (MAP C (replace_block lbl new_bb bbs)) = FLAT (MAP C bbs)
Proof
  Induct_on `bbs` >> simp[replace_block_def] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[replace_block_def]
QED

Theorem FLAT_MAP_replace_block_unique:
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
  MEM old_bb bbs /\ old_bb.bb_label = lbl /\ C new_bb = C old_bb ==>
  FLAT (MAP C (replace_block lbl new_bb bbs)) = FLAT (MAP C bbs)
Proof
  rpt strip_tac >>
  `EVERY (\b. b.bb_label = lbl ==> C b = C new_bb) bbs` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     `b = old_bb` by metis_tac[all_distinct_map_mem_inj_cfg] >>
     gvs[]) >>
  irule FLAT_MAP_replace_block_preserved >> simp[]
QED

Theorem MAP_labels_replace_block[simp]:
  new_bb.bb_label = lbl ==>
  MAP (\b. b.bb_label) (replace_block lbl new_bb bbs) =
  MAP (\b. b.bb_label) bbs
Proof
  Induct_on `bbs` >> simp[replace_block_def] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[replace_block_def]
QED

Theorem build_split_block_supply_label_fresh:
  ir_supply_inst_ok s /\
  build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') ==>
  ~MEM split_bb.bb_label s.irs_used_labels
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (split_label,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
              (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
                      target_bb.bb_instructions))` >>
  PairCases_on `r` >>
  Cases_on `fresh_inst_id r1` >>
  gvs[build_split_block_supply_def] >>
  drule fresh_ir_label_contract >> simp[]
QED


Theorem MEM_replace_block_new:
  !bbs old_bb lbl new_bb.
    MEM old_bb bbs /\ old_bb.bb_label = lbl ==>
    MEM new_bb (replace_block lbl new_bb bbs)
Proof
  Induct_on `bbs` >> simp[replace_block_def] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[replace_block_def] >> metis_tac[]
QED

Theorem MEM_replace_block_other:
  !bbs bb lbl new_bb.
    MEM bb bbs /\ bb.bb_label <> lbl ==>
    MEM bb (replace_block lbl new_bb bbs)
Proof
  Induct_on `bbs` >> simp[replace_block_def] >> rpt strip_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[replace_block_def] >> metis_tac[]
QED

Theorem insert_split_supply_inst_ids:
  ir_supply_inst_ok s /\
  ALL_DISTINCT (fn_labels fn) /\
  MEM pred_bb fn.fn_blocks /\ MEM target_bb fn.fn_blocks /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  ?split_bb repls.
    build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') /\
    fn_ir_inst_ids fn' = fn_ir_inst_ids fn ++ block_ir_inst_ids split_bb
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  rename1 `build_split_block_supply s pred_bb target_bb =
           (split_bb,repls,s1)` >>
  gvs[insert_split_supply_def] >>
  qabbrev_tac `pred' = subst_label_terminator
    target_bb.bb_label split_bb.bb_label pred_bb` >>
  qabbrev_tac `target' = update_phis_for_split
    pred_bb.bb_label split_bb.bb_label repls target_bb` >>
  `block_ir_inst_ids pred' = block_ir_inst_ids pred_bb` by
    simp[Abbr `pred'`] >>
  `block_ir_inst_ids target' = block_ir_inst_ids target_bb` by
    simp[Abbr `target'`] >>
  `pred'.bb_label = pred_bb.bb_label` by
    simp[Abbr `pred'`,subst_label_terminator_def] >>
  `target'.bb_label = target_bb.bb_label` by
    simp[Abbr `target'`,update_phis_for_split_def] >>
  `FLAT (MAP block_ir_inst_ids
      (replace_block pred_bb.bb_label pred' fn.fn_blocks)) =
   FLAT (MAP block_ir_inst_ids fn.fn_blocks)` by
    (irule FLAT_MAP_replace_block_unique >>
     conj_tac >- gvs[venomInstTheory.fn_labels_def] >>
     qexists `pred_bb` >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
      (replace_block pred_bb.bb_label pred' fn.fn_blocks))` by
    gvs[venomInstTheory.fn_labels_def] >>
  Cases_on `pred_bb.bb_label = target_bb.bb_label`
  >- (`pred_bb = target_bb` by
        metis_tac[all_distinct_map_mem_inj_cfg,
                  venomInstTheory.fn_labels_def] >>
      `MEM pred'
         (replace_block pred_bb.bb_label pred' fn.fn_blocks)` by
        metis_tac[MEM_replace_block_new] >>
      `FLAT (MAP block_ir_inst_ids
          (replace_block target_bb.bb_label target'
            (replace_block pred_bb.bb_label pred' fn.fn_blocks))) =
       FLAT (MAP block_ir_inst_ids
          (replace_block pred_bb.bb_label pred' fn.fn_blocks))` by
        (irule FLAT_MAP_replace_block_unique >> simp[] >> metis_tac[]) >>
      gvs[fn_ir_inst_ids_def,Abbr `pred'`,Abbr `target'`])
  >> `MEM target_bb
        (replace_block pred_bb.bb_label pred' fn.fn_blocks)` by
       metis_tac[MEM_replace_block_other] >>
     `FLAT (MAP block_ir_inst_ids
        (replace_block target_bb.bb_label target'
          (replace_block pred_bb.bb_label pred' fn.fn_blocks))) =
      FLAT (MAP block_ir_inst_ids
        (replace_block pred_bb.bb_label pred' fn.fn_blocks))` by
       (irule FLAT_MAP_replace_block_unique >> simp[] >> metis_tac[]) >>
     gvs[fn_ir_inst_ids_def,Abbr `pred'`,Abbr `target'`]
QED


Theorem insert_split_supply_labels:
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  ?split_bb repls.
    build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') /\
    fn_labels fn' = fn_labels fn ++ [split_bb.bb_label]
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  gvs[insert_split_supply_def,venomInstTheory.fn_labels_def,
      subst_label_terminator_def,update_phis_for_split_def]
QED

Theorem MEM_fn_labels_fn_ir_labels:
  MEM l (fn_labels fn) ==> MEM l (fn_ir_labels fn)
Proof
  simp[venomInstTheory.fn_labels_def,fn_ir_labels_def,
       block_ir_labels_def,listTheory.MEM_FLAT,listTheory.MEM_MAP] >>
  rpt strip_tac >> disj2_tac >>
  qexists `bb.bb_label :: FLAT (MAP inst_ir_labels bb.bb_instructions)` >>
  simp[] >> qexists `bb` >> simp[]
QED

Theorem insert_split_supply_distinct:
  ir_supply_inst_ok s /\
  cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  MEM pred_bb fn.fn_blocks /\ MEM target_bb fn.fn_blocks /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  ALL_DISTINCT (fn_labels fn') /\ ALL_DISTINCT (fn_ir_inst_ids fn')
Proof
  strip_tac >>
  drule insert_split_supply_labels >> strip_tac >>
  `~MEM split_bb.bb_label s.irs_used_labels` by
    metis_tac[build_split_block_supply_label_fresh] >>
  `~MEM split_bb.bb_label (fn_labels fn)` by
    (CCONTR_TAC >> gvs[] >>
     `MEM split_bb.bb_label (fn_ir_labels fn)` by
       metis_tac[MEM_fn_labels_fn_ir_labels] >>
     gvs[cfg_supply_covers_fn_def,listTheory.EVERY_MEM]) >>
  conj_tac >- gvs[listTheory.ALL_DISTINCT_APPEND] >>
  drule_all insert_split_supply_inst_ids >> strip_tac >>
  `split_bb' = split_bb /\ repls' = repls` by
    (qpat_x_assum `build_split_block_supply s pred_bb target_bb =
                    (split_bb',repls',s')` mp_tac >>
     simp[]) >>
  gvs[] >>
  `ALL_DISTINCT (block_ir_inst_ids split_bb) /\
   EVERY (\id. ~MEM id s.irs_used_inst_ids)
     (block_ir_inst_ids split_bb)` by
    metis_tac[build_split_block_supply_ids_fresh] >>
  gvs[listTheory.ALL_DISTINCT_APPEND,listTheory.EVERY_MEM,
      cfg_supply_covers_fn_def] >>
  metis_tac[]
QED


Theorem find_and_split_supply_distinct:
  !bbs fn s fn' changed s'.
    ir_supply_inst_ok s /\
    cfg_supply_covers_fn s fn /\
    EVERY (cfg_supply_covers_block s) bbs /\
    EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_ir_inst_ids fn) /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    ALL_DISTINCT (fn_labels fn') /\ ALL_DISTINCT (fn_ir_inst_ids fn')
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- gvs[find_and_split_supply_def]
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     `MEM x (block_preds fn h.bb_label)` by
       metis_tac[FIND_SOME_MEM] >>
     `MEM x fn.fn_blocks` by
       gvs[block_preds_def,listTheory.MEM_FILTER] >>
     irule insert_split_supply_distinct >>
     qexistsl [`fn`,`x`,`s`,`r`,`h`] >> simp[]
QED

Theorem cfg_norm_round_supply_distinct:
  ir_supply_inst_ok s /\
  cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  ALL_DISTINCT (fn_labels fn') /\ ALL_DISTINCT (fn_ir_inst_ids fn')
Proof
  strip_tac >>
  irule find_and_split_supply_distinct >>
  qexistsl [`fn.fn_blocks`,`changed`,`fn`,`s`] >>
  gvs[cfg_norm_round_supply_def,cfg_supply_covers_fn_blocks,
      listTheory.EVERY_MEM]
QED


Theorem cfg_norm_iter_supply_invariants:
  !n s fn fn' s'.
    ir_supply_inst_ok s /\
    cfg_supply_covers_fn s fn /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_ir_inst_ids fn) /\
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    cfg_supply_extends s s' /\
    cfg_supply_covers_fn s' fn' /\
    ALL_DISTINCT (fn_labels fn') /\
    ALL_DISTINCT (fn_ir_inst_ids fn')
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def,cfg_supply_extends_refl]
  >> Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
     rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
     Cases_on `changed`
  >- (gvs[cfg_norm_iter_supply_def] >>
      `cfg_fn_supply_contract s fn1 s1` by
        metis_tac[cfg_norm_round_supply_contract] >>
      `cfg_supply_extends s s1` by
        gvs[cfg_fn_supply_contract_def] >>
      `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
      `cfg_supply_covers_fn s1 fn1` by
        metis_tac[cfg_norm_round_supply_covered] >>
      `ALL_DISTINCT (fn_labels fn1) /\
       ALL_DISTINCT (fn_ir_inst_ids fn1)` by
        metis_tac[cfg_norm_round_supply_distinct] >>
      `cfg_supply_extends s1 s' /\
       cfg_supply_covers_fn s' fn' /\
       ALL_DISTINCT (fn_labels fn') /\
       ALL_DISTINCT (fn_ir_inst_ids fn')` by metis_tac[] >>
      metis_tac[cfg_supply_extends_trans])
  >> gvs[cfg_norm_iter_supply_def] >>
     `cfg_fn_supply_contract s fn' s'` by
       metis_tac[cfg_norm_round_supply_contract] >>
     `cfg_supply_extends s s'` by gvs[cfg_fn_supply_contract_def] >>
     metis_tac[cfg_norm_round_supply_covered,
               cfg_norm_round_supply_distinct]
QED

Theorem cfg_blocks_id_declared_iff:
  !bbs id.
    EXISTS (\bb. cfg_insts_id_declared bb.bb_instructions id) bbs <=>
    MEM id (FLAT (MAP block_ir_inst_ids bbs))
Proof
  Induct_on `bbs` >>
  simp[cfg_insts_id_declared_def,block_ir_inst_ids_def,
       listTheory.MEM_MAP,listTheory.EXISTS_MEM,EQ_SYM_EQ] >>
  metis_tac[]
QED

Theorem cfg_fn_id_declared_iff:
  cfg_fn_id_declared fn id <=> MEM id (fn_ir_inst_ids fn)
Proof
  simp[cfg_fn_id_declared_def,fn_ir_inst_ids_def,
       cfg_blocks_id_declared_iff]
QED

Theorem cfg_fn_label_declared_iff:
  cfg_fn_label_declared fn l <=> MEM l (fn_labels fn)
Proof
  simp[cfg_fn_label_declared_def,venomInstTheory.fn_labels_def,
       listTheory.MEM_MAP,listTheory.EXISTS_MEM,EQ_SYM_EQ] >> metis_tac[]
QED

Theorem EXISTS_replace_block_unique_preserved:
  !bbs old_bb P new_bb.
  ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
  MEM old_bb bbs /\ EXISTS P bbs /\ (P old_bb ==> P new_bb) ==>
  EXISTS P (replace_block old_bb.bb_label new_bb bbs)
Proof
  rpt strip_tac >>
  gvs[listTheory.EXISTS_MEM] >>
  rename1 `MEM witness bbs` >>
  Cases_on `witness.bb_label = old_bb.bb_label`
  >- (`witness = old_bb` by
        metis_tac[all_distinct_map_mem_inj_cfg] >>
      qexists `new_bb` >> simp[] >>
      metis_tac[MEM_replace_block_new])
  >> qexists `witness` >> simp[] >>
     metis_tac[MEM_replace_block_other]
QED

Theorem EXISTS_replace_block_preserved_if:
  !bbs lbl new_bb P.
    EXISTS P bbs /\
    (!old_bb. MEM old_bb bbs /\ old_bb.bb_label = lbl /\ P old_bb ==>
              P new_bb) ==>
    EXISTS P (replace_block lbl new_bb bbs)
Proof
  rpt strip_tac >> gvs[listTheory.EXISTS_MEM] >>
  rename1 `MEM witness bbs` >>
  Cases_on `witness.bb_label = lbl`
  >- (qexists `new_bb` >> simp[] >>
      metis_tac[MEM_replace_block_new])
  >> qexists `witness` >> simp[] >>
     metis_tac[MEM_replace_block_other]
QED

Definition cfg_block_decl_vars_def:
  cfg_block_decl_vars bb = FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)
End

Definition cfg_fn_decl_vars_def:
  cfg_fn_decl_vars fn = FLAT (MAP cfg_block_decl_vars fn.fn_blocks)
End

Theorem cfg_insts_var_declared_iff:
  !insts v.
    cfg_insts_var_declared insts v <=>
    MEM v (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  simp[cfg_insts_var_declared_def,listTheory.EXISTS_MEM,
       listTheory.MEM_FLAT,listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem cfg_blocks_var_declared_iff:
  !bbs v.
    EXISTS (\bb. cfg_insts_var_declared bb.bb_instructions v) bbs <=>
    MEM v (FLAT (MAP cfg_block_decl_vars bbs))
Proof
  Induct_on `bbs` >>
  simp[cfg_block_decl_vars_def,cfg_insts_var_declared_iff]
QED

Theorem cfg_fn_var_declared_iff:
  cfg_fn_var_declared fn v <=> MEM v (cfg_fn_decl_vars fn)
Proof
  simp[cfg_fn_var_declared_def,cfg_fn_decl_vars_def,
       cfg_blocks_var_declared_iff]
QED

Theorem cfg_block_decl_vars_subst_label_terminator[simp]:
  cfg_block_decl_vars (subst_label_terminator old new bb) =
  cfg_block_decl_vars bb
Proof
  simp[cfg_block_decl_vars_def,subst_label_terminator_def,
       subst_label_inst_def,listTheory.MAP_MAP_o,combinTheory.o_DEF,
       COND_RAND]
QED

Theorem cfg_block_decl_vars_update_phis_for_split[simp]:
  cfg_block_decl_vars (update_phis_for_split old new repls bb) =
  cfg_block_decl_vars bb
Proof
  simp[cfg_block_decl_vars_def,update_phis_for_split_def,
       listTheory.MAP_MAP_o,combinTheory.o_DEF,COND_RAND]
QED

Theorem insert_split_supply_decl_vars:
  ALL_DISTINCT (fn_labels fn) /\
  MEM pred_bb fn.fn_blocks /\ MEM target_bb fn.fn_blocks /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  ?split_bb repls.
    build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') /\
    cfg_fn_decl_vars fn' =
      cfg_fn_decl_vars fn ++ cfg_block_decl_vars split_bb
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  rename1 `build_split_block_supply s pred_bb target_bb =
           (split_bb,repls,s1)` >>
  gvs[insert_split_supply_def] >>
  qabbrev_tac `pred1 = subst_label_terminator
    target_bb.bb_label split_bb.bb_label pred_bb` >>
  qabbrev_tac `target1 = update_phis_for_split
    pred_bb.bb_label split_bb.bb_label repls target_bb` >>
  `cfg_block_decl_vars pred1 = cfg_block_decl_vars pred_bb` by
    simp[Abbr `pred1`] >>
  `cfg_block_decl_vars target1 = cfg_block_decl_vars target_bb` by
    simp[Abbr `target1`] >>
  `pred1.bb_label = pred_bb.bb_label` by
    simp[Abbr `pred1`,subst_label_terminator_def] >>
  `target1.bb_label = target_bb.bb_label` by
    simp[Abbr `target1`,update_phis_for_split_def] >>
  `FLAT (MAP cfg_block_decl_vars
      (replace_block pred_bb.bb_label pred1 fn.fn_blocks)) =
   FLAT (MAP cfg_block_decl_vars fn.fn_blocks)` by
    (irule FLAT_MAP_replace_block_unique >>
     conj_tac >- gvs[venomInstTheory.fn_labels_def] >>
     qexists `pred_bb` >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
      (replace_block pred_bb.bb_label pred1 fn.fn_blocks))` by
    gvs[venomInstTheory.fn_labels_def] >>
  Cases_on `pred_bb.bb_label = target_bb.bb_label`
  >- (`pred_bb = target_bb` by
        metis_tac[all_distinct_map_mem_inj_cfg,
                  venomInstTheory.fn_labels_def] >>
      `MEM pred1
         (replace_block pred_bb.bb_label pred1 fn.fn_blocks)` by
        metis_tac[MEM_replace_block_new] >>
      `FLAT (MAP cfg_block_decl_vars
          (replace_block target_bb.bb_label target1
            (replace_block pred_bb.bb_label pred1 fn.fn_blocks))) =
       FLAT (MAP cfg_block_decl_vars
          (replace_block pred_bb.bb_label pred1 fn.fn_blocks))` by
        (irule FLAT_MAP_replace_block_unique >> simp[] >> metis_tac[]) >>
      gvs[cfg_fn_decl_vars_def,Abbr `pred1`,Abbr `target1`])
  >> `MEM target_bb
        (replace_block pred_bb.bb_label pred1 fn.fn_blocks)` by
       metis_tac[MEM_replace_block_other] >>
     `FLAT (MAP cfg_block_decl_vars
        (replace_block target_bb.bb_label target1
          (replace_block pred_bb.bb_label pred1 fn.fn_blocks))) =
      FLAT (MAP cfg_block_decl_vars
        (replace_block pred_bb.bb_label pred1 fn.fn_blocks))` by
       (irule FLAT_MAP_replace_block_unique >> simp[] >> metis_tac[]) >>
     gvs[cfg_fn_decl_vars_def,Abbr `pred1`,Abbr `target1`]
QED

Theorem insert_split_supply_declared_preserved:
  ir_supply_inst_ok s /\
  ALL_DISTINCT (fn_labels fn) /\
  MEM pred_bb fn.fn_blocks /\ MEM target_bb fn.fn_blocks /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  (!id. cfg_fn_id_declared fn id ==> cfg_fn_id_declared fn' id) /\
  (!v. cfg_fn_var_declared fn v ==> cfg_fn_var_declared fn' v) /\
  (!l. cfg_fn_label_declared fn l ==> cfg_fn_label_declared fn' l)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all insert_split_supply_inst_ids >> strip_tac >>
  drule insert_split_supply_labels >> strip_tac >>
  `?split_bb repls.
     build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') /\
     cfg_fn_decl_vars fn' =
       cfg_fn_decl_vars fn ++ cfg_block_decl_vars split_bb` by
    metis_tac[insert_split_supply_decl_vars] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[cfg_fn_id_declared_iff,cfg_fn_var_declared_iff,
      cfg_fn_label_declared_iff]
QED


Theorem find_and_split_supply_declared_preserved:
  !bbs fn s fn' changed s'.
    ir_supply_inst_ok s /\
    cfg_supply_covers_fn s fn /\
    EVERY (cfg_supply_covers_block s) bbs /\
    EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
    ALL_DISTINCT (fn_labels fn) /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    (!id. cfg_fn_id_declared fn id ==> cfg_fn_id_declared fn' id) /\
    (!v. cfg_fn_var_declared fn v ==> cfg_fn_var_declared fn' v) /\
    (!l. cfg_fn_label_declared fn l ==> cfg_fn_label_declared fn' l)
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- gvs[find_and_split_supply_def]
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     `MEM x (block_preds fn h.bb_label)` by
       metis_tac[FIND_SOME_MEM] >>
     `MEM x fn.fn_blocks` by
       gvs[block_preds_def,listTheory.MEM_FILTER] >>
     irule insert_split_supply_declared_preserved >>
     conj_tac >- simp[] >>
     qexistsl [`x`,`s`,`r`,`h`] >> simp[]
QED

Theorem cfg_norm_round_supply_declared_preserved:
  ir_supply_inst_ok s /\
  cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  (!id. cfg_fn_id_declared fn id ==> cfg_fn_id_declared fn' id) /\
  (!v. cfg_fn_var_declared fn v ==> cfg_fn_var_declared fn' v) /\
  (!l. cfg_fn_label_declared fn l ==> cfg_fn_label_declared fn' l)
Proof
  strip_tac >> irule find_and_split_supply_declared_preserved >>
  conj_tac >- simp[] >>
  qexistsl [`fn.fn_blocks`,`changed`,`s`,`s'`] >>
  gvs[cfg_norm_round_supply_def,cfg_supply_covers_fn_blocks,
      listTheory.EVERY_MEM]
QED

Theorem cfg_norm_iter_supply_declared_preserved:
  !n s fn fn' s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_ir_inst_ids fn) /\
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    (!id. cfg_fn_id_declared fn id ==> cfg_fn_id_declared fn' id) /\
    (!v. cfg_fn_var_declared fn v ==> cfg_fn_var_declared fn' v) /\
    (!l. cfg_fn_label_declared fn l ==> cfg_fn_label_declared fn' l)
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def]
  >> Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
     rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
     Cases_on `changed`
  >- (gvs[cfg_norm_iter_supply_def] >>
      `cfg_fn_supply_contract s fn1 s1` by
        metis_tac[cfg_norm_round_supply_contract] >>
      `cfg_supply_extends s s1` by gvs[cfg_fn_supply_contract_def] >>
      `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
      `cfg_supply_covers_fn s1 fn1` by
        metis_tac[cfg_norm_round_supply_covered] >>
      `ALL_DISTINCT (fn_labels fn1) /\
       ALL_DISTINCT (fn_ir_inst_ids fn1)` by
        metis_tac[cfg_norm_round_supply_distinct] >>
      `(!id. cfg_fn_id_declared fn id ==> cfg_fn_id_declared fn1 id) /\
       (!v. cfg_fn_var_declared fn v ==> cfg_fn_var_declared fn1 v) /\
       (!l. cfg_fn_label_declared fn l ==> cfg_fn_label_declared fn1 l)` by
        metis_tac[cfg_norm_round_supply_declared_preserved] >>
      metis_tac[])
  >> gvs[cfg_norm_iter_supply_def] >>
     metis_tac[cfg_norm_round_supply_declared_preserved]
QED

Theorem cfg_norm_iter_supply_contract:
  !n s fn fn' s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_ir_inst_ids fn) /\
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    cfg_fn_supply_contract s fn' s'
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def,cfg_fn_supply_contract_def,
          cfg_supply_extends_refl]
  >> Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
     rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
     Cases_on `changed`
  >- (gvs[cfg_norm_iter_supply_def] >>
      `cfg_fn_supply_contract s fn1 s1` by
        metis_tac[cfg_norm_round_supply_contract] >>
      `cfg_supply_extends s s1` by gvs[cfg_fn_supply_contract_def] >>
      `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
      `cfg_supply_covers_fn s1 fn1` by
        metis_tac[cfg_norm_round_supply_covered] >>
      `ALL_DISTINCT (fn_labels fn1) /\
       ALL_DISTINCT (fn_ir_inst_ids fn1)` by
        metis_tac[cfg_norm_round_supply_distinct] >>
      `cfg_fn_supply_contract s1 fn' s'` by metis_tac[] >>
      `(!id. cfg_fn_id_declared fn1 id ==> cfg_fn_id_declared fn' id) /\
       (!v. cfg_fn_var_declared fn1 v ==> cfg_fn_var_declared fn' v) /\
       (!l. cfg_fn_label_declared fn1 l ==> cfg_fn_label_declared fn' l)` by
        metis_tac[cfg_norm_iter_supply_declared_preserved] >>
      `(!id. cfg_fn_id_declared fn id ==> cfg_fn_id_declared fn1 id) /\
       (!v. cfg_fn_var_declared fn v ==> cfg_fn_var_declared fn1 v) /\
       (!l. cfg_fn_label_declared fn l ==> cfg_fn_label_declared fn1 l)` by
        metis_tac[cfg_norm_round_supply_declared_preserved] >>
      gvs[cfg_fn_supply_contract_def] >>
      metis_tac[cfg_supply_extends_trans,cfg_supply_extends_members])
  >> gvs[cfg_norm_iter_supply_def] >>
     metis_tac[cfg_norm_round_supply_contract]
QED


Theorem cfg_norm_function_supply_contract:
  ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  cfg_fn_supply_contract s fn' s'
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_contract]
QED

Theorem cfg_norm_function_supply_invariants:
  ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  cfg_supply_extends s s' /\ cfg_supply_covers_fn s' fn' /\
  ALL_DISTINCT (fn_labels fn') /\
  ALL_DISTINCT (fn_ir_inst_ids fn')
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_invariants]
QED

Definition cfg_supply_covers_functions_def:
  cfg_supply_covers_functions s fns <=> EVERY (cfg_supply_covers_fn s) fns
End

Definition cfg_functions_id_declared_def:
  cfg_functions_id_declared fns id <=> EXISTS (\fn. cfg_fn_id_declared fn id) fns
End

Definition cfg_functions_var_declared_def:
  cfg_functions_var_declared fns v <=> EXISTS (\fn. cfg_fn_var_declared fn v) fns
End

Definition cfg_functions_label_declared_def:
  cfg_functions_label_declared fns l <=> EXISTS (\fn. cfg_fn_label_declared fn l) fns
End

Definition cfg_functions_supply_contract_def:
  cfg_functions_supply_contract s fns s' <=>
    cfg_supply_extends s s' /\ cfg_supply_covers_functions s' fns /\
    (!id. MEM id s'.irs_used_inst_ids /\ ~MEM id s.irs_used_inst_ids ==>
          cfg_functions_id_declared fns id) /\
    (!v. MEM v s'.irs_used_vars /\ ~MEM v s.irs_used_vars ==>
         cfg_functions_var_declared fns v) /\
    (!l. MEM l s'.irs_used_labels /\ ~MEM l s.irs_used_labels ==>
         cfg_functions_label_declared fns l)
End


Theorem cfg_supply_covers_functions_mono:
  cfg_supply_covers_functions s fns /\ cfg_supply_extends s s' ==>
  cfg_supply_covers_functions s' fns
Proof
  simp[cfg_supply_covers_functions_def,listTheory.EVERY_MEM] >>
  metis_tac[cfg_supply_covers_fn_mono]
QED

Theorem cfg_norm_functions_supply_contract:
  !fns s fns' s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_functions s fns /\
    EVERY (\fn. ALL_DISTINCT (fn_labels fn)) fns /\
    EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn)) fns /\
    cfg_norm_functions_supply s fns = (fns',s') ==>
    cfg_functions_supply_contract s fns' s' /\
    EVERY (\fn. ALL_DISTINCT (fn_labels fn)) fns' /\
    EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn)) fns'
Proof
  Induct_on `fns` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_functions_supply_def,cfg_functions_supply_contract_def,
          cfg_supply_covers_functions_def,cfg_supply_extends_refl,
          cfg_functions_id_declared_def,cfg_functions_var_declared_def,
          cfg_functions_label_declared_def]
  >> Cases_on `cfg_norm_function_supply s h` >>
     rename1 `cfg_norm_function_supply s h = (h',s1)` >>
     Cases_on `cfg_norm_functions_supply s1 fns` >>
     rename1 `cfg_norm_functions_supply s1 fns = (rest,s2)` >>
     gvs[cfg_norm_functions_supply_def,cfg_supply_covers_functions_def] >>
     `cfg_fn_supply_contract s h' s1` by
       metis_tac[cfg_norm_function_supply_contract] >>
     `cfg_supply_extends s s1` by gvs[cfg_fn_supply_contract_def] >>
     `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
     `cfg_supply_covers_fn s1 h' /\
      ALL_DISTINCT (fn_labels h') /\
      ALL_DISTINCT (fn_ir_inst_ids h')` by
       metis_tac[cfg_norm_function_supply_invariants] >>
     `cfg_supply_covers_functions s1 fns` by
       (gvs[cfg_supply_covers_functions_def,listTheory.EVERY_MEM] >>
        metis_tac[cfg_supply_covers_fn_mono]) >>
     `cfg_functions_supply_contract s1 rest s' /\
      EVERY (\fn. ALL_DISTINCT (fn_labels fn)) rest /\
      EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn)) rest` by
       (first_x_assum (qspecl_then [`s1`,`rest`,`s'`] mp_tac) >>
        disch_then irule >>
        gvs[cfg_supply_covers_functions_def]) >>
     `cfg_supply_extends s1 s'` by
       gvs[cfg_functions_supply_contract_def] >>
     `cfg_supply_covers_fn s' h'` by
       metis_tac[cfg_supply_covers_fn_mono] >>
     gvs[cfg_functions_supply_contract_def,
         cfg_supply_covers_functions_def,
         cfg_functions_id_declared_def,cfg_functions_var_declared_def,
         cfg_functions_label_declared_def,cfg_fn_supply_contract_def] >>
     metis_tac[cfg_supply_extends_trans,cfg_supply_extends_members]
QED


Definition cfg_supply_covers_unit_def:
  cfg_supply_covers_unit s unit <=>
    EVERY (\id. MEM id s.irs_used_inst_ids) (unit_ir_inst_ids unit) /\
    EVERY (\v. MEM v s.irs_used_vars) (unit_ir_vars unit) /\
    EVERY (\l. MEM l s.irs_used_labels) (unit_ir_labels unit)
End

Theorem MEM_FLAT_MAP_component:
  MEM e es /\ MEM x (C e) ==> MEM x (FLAT (MAP C es))
Proof
  simp[listTheory.MEM_FLAT,listTheory.MEM_MAP] >>
  rpt strip_tac >> qexists `C e` >> simp[] >>
  qexists `e` >> simp[]
QED

Theorem cfg_supply_covers_unit_functions:
  cfg_supply_covers_unit s unit ==>
  cfg_supply_covers_functions s unit.cu_context.ctx_functions
Proof
  strip_tac >>
  gvs[cfg_supply_covers_unit_def,cfg_supply_covers_functions_def,
      cfg_supply_covers_fn_def,unit_ir_inst_ids_def,unit_ir_vars_def,
      unit_ir_labels_def,listTheory.EVERY_FLAT,listTheory.EVERY_MAP,
      listTheory.EVERY_MEM] >>
  metis_tac[MEM_FLAT_MAP_component]
QED

Theorem cfg_supply_covers_unit_update_functions:
  cfg_supply_covers_unit s unit /\ cfg_supply_extends s s' /\
  cfg_supply_covers_functions s' fns ==>
  cfg_supply_covers_unit s'
    (unit with cu_context := unit.cu_context with ctx_functions := fns)
Proof
  rpt strip_tac >>
  gvs[cfg_supply_covers_unit_def,cfg_supply_covers_functions_def,
      cfg_supply_covers_fn_def,cfg_supply_extends_def,
      unit_ir_inst_ids_def,unit_ir_vars_def,unit_ir_labels_def,
      listTheory.EVERY_FLAT,listTheory.EVERY_MAP,listTheory.EVERY_MEM] >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[listTheory.MEM_FLAT,listTheory.MEM_MAP] >> metis_tac[])
  >> conj_tac
  >- (rpt strip_tac >>
      gvs[listTheory.MEM_FLAT,listTheory.MEM_MAP] >> metis_tac[])
  >> rpt strip_tac >>
     gvs[listTheory.MEM_FLAT,listTheory.MEM_MAP,AllCaseEqs()] >>
     metis_tac[]
QED

Definition cfg_unit_supply_contract_def:
  cfg_unit_supply_contract s unit s' <=>
    cfg_supply_extends s s' /\ cfg_supply_covers_unit s' unit /\
    (!id. MEM id s'.irs_used_inst_ids /\ ~MEM id s.irs_used_inst_ids ==>
          cfg_id_declared unit id) /\
    (!v. MEM v s'.irs_used_vars /\ ~MEM v s.irs_used_vars ==>
         cfg_var_declared unit v) /\
    (!l. MEM l s'.irs_used_labels /\ ~MEM l s.irs_used_labels ==>
         cfg_block_label_declared unit l)
End

Theorem cfg_functions_id_declared_unit_update[simp]:
  cfg_id_declared
    (unit with cu_context := unit.cu_context with ctx_functions := fns) id <=>
  cfg_functions_id_declared fns id
Proof
  simp[cfg_id_declared_def,cfg_functions_id_declared_def,
       cfg_fn_id_declared_iff,unit_ir_inst_ids_def,
       listTheory.EXISTS_MEM,listTheory.MEM_FLAT,listTheory.MEM_MAP] >>
  metis_tac[]
QED

Theorem cfg_functions_var_declared_unit_update[simp]:
  cfg_var_declared
    (unit with cu_context := unit.cu_context with ctx_functions := fns) v <=>
  cfg_functions_var_declared fns v
Proof
  simp[cfg_var_declared_def,cfg_functions_var_declared_def,
       cfg_fn_var_declared_def,cfg_insts_var_declared_def]
QED

Theorem cfg_functions_label_declared_unit_update[simp]:
  cfg_block_label_declared
    (unit with cu_context := unit.cu_context with ctx_functions := fns) l <=>
  cfg_functions_label_declared fns l
Proof
  simp[cfg_block_label_declared_def,cfg_functions_label_declared_def,
       cfg_fn_label_declared_def]
QED

Theorem cfg_norm_unit_supply_contract:
  ir_supply_inst_ok s /\ cfg_supply_covers_unit s unit /\
  EVERY (\fn. ALL_DISTINCT (fn_labels fn))
    unit.cu_context.ctx_functions /\
  EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn))
    unit.cu_context.ctx_functions /\
  cfg_norm_unit_supply s unit = (unit',s') ==>
  cfg_unit_supply_contract s unit' s' /\
  EVERY (\fn. ALL_DISTINCT (fn_labels fn))
    unit'.cu_context.ctx_functions /\
  EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn))
    unit'.cu_context.ctx_functions
Proof
  rpt strip_tac >>
  Cases_on `cfg_norm_context_supply s unit.cu_context` >>
  rename1 `cfg_norm_context_supply s unit.cu_context = (ctx',s1)` >>
  Cases_on `cfg_norm_functions_supply s unit.cu_context.ctx_functions` >>
  rename1 `cfg_norm_functions_supply s unit.cu_context.ctx_functions =
           (fns',s2)` >>
  gvs[cfg_norm_unit_supply_def,cfg_norm_context_supply_def] >>
  `cfg_supply_covers_functions s unit.cu_context.ctx_functions` by
    metis_tac[cfg_supply_covers_unit_functions] >>
  `cfg_functions_supply_contract s fns' s' /\
   EVERY (\fn. ALL_DISTINCT (fn_labels fn)) fns' /\
   EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn)) fns'` by
    metis_tac[cfg_norm_functions_supply_contract] >>
  `cfg_supply_extends s s'` by gvs[cfg_functions_supply_contract_def] >>
  `cfg_supply_covers_unit s'
     (unit with cu_context := unit.cu_context with ctx_functions := fns')` by
    (irule cfg_supply_covers_unit_update_functions >>
     conj_tac
     >- gvs[cfg_functions_supply_contract_def]
     >> qexists `s` >> simp[]) >>
  gvs[cfg_unit_supply_contract_def,cfg_functions_supply_contract_def,
      cfg_functions_id_declared_def,cfg_functions_var_declared_def,
      cfg_functions_label_declared_def,cfg_id_declared_def,
      cfg_var_declared_def,cfg_block_label_declared_def,
      cfg_fn_id_declared_def,cfg_fn_var_declared_def,
      cfg_fn_label_declared_def] >>
  metis_tac[]
QED


Theorem cfg_norm_context_supply_contract:
  ir_supply_inst_ok s /\
  cfg_supply_covers_functions s ctx.ctx_functions /\
  EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions /\
  EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn)) ctx.ctx_functions /\
  cfg_norm_context_supply s ctx = (ctx',s') ==>
  cfg_functions_supply_contract s ctx'.ctx_functions s' /\
  EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx'.ctx_functions /\
  EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn)) ctx'.ctx_functions
Proof
  rpt strip_tac >>
  Cases_on `cfg_norm_functions_supply s ctx.ctx_functions` >>
  rename1 `cfg_norm_functions_supply s ctx.ctx_functions = (fns',s1)` >>
  gvs[cfg_norm_context_supply_def] >>
  metis_tac[cfg_norm_functions_supply_contract]
QED


Theorem find_and_split_supply_inst_ids_delta:
  !bbs fn s fn' changed s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
    EVERY (cfg_supply_covers_block s) bbs /\
    EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
    ALL_DISTINCT (fn_labels fn) /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    ?new_ids.
      fn_ir_inst_ids fn' = fn_ir_inst_ids fn ++ new_ids /\
      ALL_DISTINCT new_ids /\
      EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- (gvs[find_and_split_supply_def] >> qexists `[]` >> simp[])
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> qexists `[]` >> simp[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> qexists `[]` >> simp[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     `MEM x (block_preds fn h.bb_label)` by metis_tac[FIND_SOME_MEM] >>
     `MEM x fn.fn_blocks` by
       gvs[block_preds_def,listTheory.MEM_FILTER] >>
     drule_all insert_split_supply_inst_ids >> strip_tac >>
     qexists `block_ir_inst_ids split_bb` >> simp[] >>
     metis_tac[build_split_block_supply_ids_fresh]
QED

Theorem cfg_norm_round_supply_inst_ids_delta:
  ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  ?new_ids.
    fn_ir_inst_ids fn' = fn_ir_inst_ids fn ++ new_ids /\
    ALL_DISTINCT new_ids /\
    EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids
Proof
  strip_tac >> irule find_and_split_supply_inst_ids_delta >>
  simp[] >> qexistsl [`fn.fn_blocks`,`changed`,`s'`] >>
  gvs[cfg_norm_round_supply_def,cfg_supply_covers_fn_blocks,
      listTheory.EVERY_MEM]
QED


Theorem cfg_norm_iter_supply_inst_ids_delta:
  !n s fn fn' s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
    ALL_DISTINCT (fn_labels fn) /\
    ALL_DISTINCT (fn_ir_inst_ids fn) /\
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    ?new_ids.
      fn_ir_inst_ids fn' = fn_ir_inst_ids fn ++ new_ids /\
      ALL_DISTINCT new_ids /\
      EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- (gvs[cfg_norm_iter_supply_def] >> qexists `[]` >> simp[])
  >> Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
     rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
     Cases_on `changed`
  >- (gvs[cfg_norm_iter_supply_def] >>
      `cfg_fn_supply_contract s fn1 s1` by
        metis_tac[cfg_norm_round_supply_contract] >>
      `cfg_supply_extends s s1` by gvs[cfg_fn_supply_contract_def] >>
      `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
      `cfg_supply_covers_fn s1 fn1` by
        metis_tac[cfg_norm_round_supply_covered] >>
      `ALL_DISTINCT (fn_labels fn1) /\
       ALL_DISTINCT (fn_ir_inst_ids fn1)` by
        metis_tac[cfg_norm_round_supply_distinct] >>
      `?new1. fn_ir_inst_ids fn1 = fn_ir_inst_ids fn ++ new1 /\
              ALL_DISTINCT new1 /\
              EVERY (\id. ~MEM id s.irs_used_inst_ids) new1` by
        metis_tac[cfg_norm_round_supply_inst_ids_delta] >>
      `?new2. fn_ir_inst_ids fn' = fn_ir_inst_ids fn1 ++ new2 /\
              ALL_DISTINCT new2 /\
              EVERY (\id. ~MEM id s1.irs_used_inst_ids) new2` by
        metis_tac[] >>
      qexists `new1 ++ new2` >>
      simp[listTheory.APPEND_ASSOC,listTheory.ALL_DISTINCT_APPEND,
           listTheory.EVERY_MEM] >>
      rpt strip_tac
      >- (gvs[cfg_supply_covers_fn_def,listTheory.EVERY_MEM] >>
          metis_tac[])
      >> `MEM id s1.irs_used_inst_ids` by
           (drule cfg_supply_extends_members >> strip_tac >> metis_tac[]) >>
         gvs[listTheory.EVERY_MEM])
  >> gvs[cfg_norm_iter_supply_def] >>
     metis_tac[cfg_norm_round_supply_inst_ids_delta]
QED

Theorem cfg_norm_function_supply_inst_ids_delta:
  ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  ?new_ids.
    fn_ir_inst_ids fn' = fn_ir_inst_ids fn ++ new_ids /\
    ALL_DISTINCT new_ids /\
    EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_inst_ids_delta]
QED


Theorem cfg_norm_functions_supply_inst_ids_delta:
  !fns s fns' s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_functions s fns /\
    EVERY (\fn. ALL_DISTINCT (fn_labels fn)) fns /\
    ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns)) /\
    cfg_norm_functions_supply s fns = (fns',s') ==>
    ?new_ids.
      ALL_DISTINCT new_ids /\
      EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids /\
      (!id. MEM id (FLAT (MAP fn_ir_inst_ids fns')) <=>
            MEM id (FLAT (MAP fn_ir_inst_ids fns)) \/ MEM id new_ids) /\
      ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns'))
Proof
  Induct_on `fns` >> rpt gen_tac >> strip_tac
  >- (gvs[cfg_norm_functions_supply_def] >> qexists `[]` >> simp[])
  >> Cases_on `cfg_norm_function_supply s h` >>
     rename1 `cfg_norm_function_supply s h = (h',s1)` >>
     Cases_on `cfg_norm_functions_supply s1 fns` >>
     rename1 `cfg_norm_functions_supply s1 fns = (rest,s2)` >>
     gvs[cfg_norm_functions_supply_def,cfg_supply_covers_functions_def,
         listTheory.ALL_DISTINCT_APPEND] >>
     `cfg_fn_supply_contract s h' s1` by
       metis_tac[cfg_norm_function_supply_contract] >>
     `cfg_supply_extends s s1` by gvs[cfg_fn_supply_contract_def] >>
     `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
     `cfg_supply_covers_fn s1 h' /\
      ALL_DISTINCT (fn_labels h') /\
      ALL_DISTINCT (fn_ir_inst_ids h')` by
       metis_tac[cfg_norm_function_supply_invariants] >>
     `cfg_supply_covers_functions s1 fns` by
       (gvs[cfg_supply_covers_functions_def,listTheory.EVERY_MEM] >>
        metis_tac[cfg_supply_covers_fn_mono]) >>
     `?new1.
        fn_ir_inst_ids h' = fn_ir_inst_ids h ++ new1 /\
        ALL_DISTINCT new1 /\
        EVERY (\id. ~MEM id s.irs_used_inst_ids) new1` by
       metis_tac[cfg_norm_function_supply_inst_ids_delta] >>
     `?new2.
        ALL_DISTINCT new2 /\
        EVERY (\id. ~MEM id s1.irs_used_inst_ids) new2 /\
        (!id. MEM id (FLAT (MAP fn_ir_inst_ids rest)) <=>
              MEM id (FLAT (MAP fn_ir_inst_ids fns)) \/ MEM id new2) /\
        ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids rest))` by
       (first_x_assum (qspecl_then [`s1`,`rest`,`s'`] mp_tac) >>
        disch_then irule >> gvs[cfg_supply_covers_functions_def]) >>
     qexists `new1 ++ new2` >>
     simp[listTheory.ALL_DISTINCT_APPEND,listTheory.EVERY_MEM] >>
     rpt strip_tac
     >- (gvs[cfg_supply_covers_fn_def,listTheory.EVERY_MEM] >> metis_tac[])
     >- (drule cfg_supply_extends_members >> strip_tac >>
         gvs[listTheory.EVERY_MEM] >> metis_tac[])
     >- metis_tac[]
     >> gvs[cfg_supply_covers_fn_def,cfg_supply_covers_functions_def,
            listTheory.EVERY_MEM,listTheory.ALL_DISTINCT_APPEND]
     >- (`MEM e s.irs_used_inst_ids` by metis_tac[] >>
         `MEM e s1.irs_used_inst_ids` by
           (drule cfg_supply_extends_members >> strip_tac >> metis_tac[]) >>
         metis_tac[])
     >- (`MEM e s.irs_used_inst_ids` by
           (gvs[listTheory.MEM_FLAT,listTheory.MEM_MAP] >> metis_tac[]) >>
         metis_tac[])
     >> `MEM e s1.irs_used_inst_ids` by metis_tac[] >>
        metis_tac[]
QED


Theorem cfg_norm_context_supply_inst_ids_delta:
  ir_supply_inst_ok s /\
  cfg_supply_covers_functions s ctx.ctx_functions /\
  EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions /\
  ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  cfg_norm_context_supply s ctx = (ctx',s') ==>
  ?new_ids.
    ALL_DISTINCT new_ids /\
    EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids /\
    (!id. MEM id (FLAT (MAP fn_ir_inst_ids ctx'.ctx_functions)) <=>
          MEM id (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) \/
          MEM id new_ids) /\
    ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids ctx'.ctx_functions))
Proof
  rpt strip_tac >>
  Cases_on `cfg_norm_functions_supply s ctx.ctx_functions` >>
  rename1 `cfg_norm_functions_supply s ctx.ctx_functions = (fns',s1)` >>
  gvs[cfg_norm_context_supply_def] >>
  metis_tac[cfg_norm_functions_supply_inst_ids_delta]
QED

Theorem cfg_norm_unit_supply_inst_ids_delta:
  ir_supply_inst_ok s /\ cfg_supply_covers_unit s unit /\
  EVERY (\fn. ALL_DISTINCT (fn_labels fn))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  cfg_norm_unit_supply s unit = (unit',s') ==>
  ?new_ids.
    ALL_DISTINCT new_ids /\
    EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids /\
    (!id. MEM id (unit_ir_inst_ids unit') <=>
          MEM id (unit_ir_inst_ids unit) \/ MEM id new_ids) /\
    ALL_DISTINCT (unit_ir_inst_ids unit')
Proof
  rpt strip_tac >>
  Cases_on `cfg_norm_context_supply s unit.cu_context` >>
  rename1 `cfg_norm_context_supply s unit.cu_context = (ctx',s1)` >>
  gvs[cfg_norm_unit_supply_def,unit_ir_inst_ids_def] >>
  irule cfg_norm_context_supply_inst_ids_delta >>
  gvs[unit_ir_inst_ids_def] >>
  metis_tac[cfg_supply_covers_unit_functions]
QED


Theorem cfg_norm_context_supply_inst_ids_all_distinct:
  ir_supply_inst_ok s /\
  cfg_supply_covers_functions s ctx.ctx_functions /\
  EVERY (\fn. ALL_DISTINCT (fn_labels fn)) ctx.ctx_functions /\
  ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  cfg_norm_context_supply s ctx = (ctx',s') ==>
  ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids ctx'.ctx_functions))
Proof
  metis_tac[cfg_norm_context_supply_inst_ids_delta]
QED

Theorem cfg_norm_unit_supply_inst_ids_all_distinct:
  ir_supply_inst_ok s /\ cfg_supply_covers_unit s unit /\
  EVERY (\fn. ALL_DISTINCT (fn_labels fn))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  cfg_norm_unit_supply s unit = (unit',s') ==>
  ALL_DISTINCT (unit_ir_inst_ids unit')
Proof
  metis_tac[cfg_norm_unit_supply_inst_ids_delta]
QED


Theorem init_ir_supply_cfg_supply_covers_unit:
  cfg_supply_covers_unit (init_ir_supply unit) unit
Proof
  simp[cfg_supply_covers_unit_def,init_ir_supply_fields,
       listTheory.EVERY_MEM]
QED

Theorem cfg_norm_configured_with_supply_contract:
  EVERY (\fn. ALL_DISTINCT (fn_labels fn))
    unit.cu_context.ctx_functions /\
  EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn))
    unit.cu_context.ctx_functions /\
  cfg_norm_configured_with_supply unit = (unit',s') ==>
  ?new_ids new_vars new_labels.
    s'.irs_used_inst_ids = new_ids ++ unit_ir_inst_ids unit /\
    ALL_DISTINCT new_ids /\
    EVERY (\id. ~MEM id (unit_ir_inst_ids unit)) new_ids /\
    s'.irs_used_vars = new_vars ++ unit_ir_vars unit /\
    ALL_DISTINCT new_vars /\
    EVERY (\v. ~MEM v (unit_ir_vars unit)) new_vars /\
    s'.irs_used_labels = new_labels ++ unit_ir_labels unit /\
    ALL_DISTINCT new_labels /\
    EVERY (\l. ~MEM l (unit_ir_labels unit)) new_labels /\
    EVERY (\id. MEM id s'.irs_used_inst_ids) (unit_ir_inst_ids unit') /\
    EVERY (\v. MEM v s'.irs_used_vars) (unit_ir_vars unit') /\
    EVERY (\l. MEM l s'.irs_used_labels) (unit_ir_labels unit') /\
    EVERY (cfg_id_declared unit') new_ids /\
    EVERY (cfg_var_declared unit') new_vars /\
    EVERY (cfg_block_label_declared unit') new_labels
Proof
  rpt strip_tac >>
  `cfg_unit_supply_contract (init_ir_supply unit) unit' s' /\
   EVERY (\fn. ALL_DISTINCT (fn_labels fn))
     unit'.cu_context.ctx_functions /\
   EVERY (\fn. ALL_DISTINCT (fn_ir_inst_ids fn))
     unit'.cu_context.ctx_functions` by
    (`cfg_norm_unit_supply (init_ir_supply unit) unit = (unit',s')` by
       gvs[cfg_norm_configured_with_supply_def] >>
     metis_tac[cfg_norm_unit_supply_contract,init_ir_supply_inst_ok,
               init_ir_supply_cfg_supply_covers_unit]) >>
  gvs[cfg_unit_supply_contract_def,cfg_supply_extends_def,
      cfg_supply_covers_unit_def,init_ir_supply_fields,
      listTheory.EVERY_MEM] >>
  metis_tac[]
QED


Theorem cfg_norm_configured_inst_ids_all_distinct:
  EVERY (\fn. ALL_DISTINCT (fn_labels fn))
    unit.cu_context.ctx_functions /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  cfg_norm_configured_with_supply unit = (unit',s') ==>
  ALL_DISTINCT (unit_ir_inst_ids unit')
Proof
  rpt strip_tac >>
  `cfg_norm_unit_supply (init_ir_supply unit) unit = (unit',s')` by
    gvs[cfg_norm_configured_with_supply_def] >>
  metis_tac[cfg_norm_unit_supply_inst_ids_all_distinct,
            init_ir_supply_inst_ok,init_ir_supply_cfg_supply_covers_unit]
QED


(* ===== Structural preservation for the configured CFG adapter ===== *)

Theorem insert_split_supply_metadata:
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn /\
  fn_fmp_convention_eq fn' fn
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  gvs[insert_split_supply_def,venomInstTheory.fn_identity_metadata_eq_def,
      venomInstTheory.fn_static_input_eq_def,venomInstTheory.fn_static_layout_eq_def,
      venomInstTheory.fn_fmp_convention_eq_def]
QED

Theorem find_and_split_supply_metadata:
  !bbs fn s fn' changed s'.
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    fn_identity_metadata_eq fn' fn /\
    fn_static_input_eq fn' fn /\
    fn_static_layout_eq fn' fn /\
    fn_fmp_convention_eq fn' fn
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- gvs[find_and_split_supply_def,venomInstTheory.fn_identity_metadata_eq_def,
          venomInstTheory.fn_static_input_eq_def,venomInstTheory.fn_static_layout_eq_def,
          venomInstTheory.fn_fmp_convention_eq_def]
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     metis_tac[insert_split_supply_metadata]
QED

Theorem cfg_norm_round_supply_metadata:
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn /\
  fn_fmp_convention_eq fn' fn
Proof
  simp[cfg_norm_round_supply_def] >>
  metis_tac[find_and_split_supply_metadata]
QED

Theorem cfg_norm_iter_supply_metadata:
  !n s fn fn' s'.
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    fn_identity_metadata_eq fn' fn /\
    fn_static_input_eq fn' fn /\
    fn_static_layout_eq fn' fn /\
    fn_fmp_convention_eq fn' fn
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def,venomInstTheory.fn_identity_metadata_eq_def,
          venomInstTheory.fn_static_input_eq_def,venomInstTheory.fn_static_layout_eq_def,
          venomInstTheory.fn_fmp_convention_eq_def]
  >> Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
     rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
     Cases_on `changed`
  >- (gvs[cfg_norm_iter_supply_def] >>
      `fn_identity_metadata_eq fn1 fn /\
       fn_static_input_eq fn1 fn /\
       fn_static_layout_eq fn1 fn /\
       fn_fmp_convention_eq fn1 fn` by
        metis_tac[cfg_norm_round_supply_metadata] >>
      `fn_identity_metadata_eq fn' fn1 /\
       fn_static_input_eq fn' fn1 /\
       fn_static_layout_eq fn' fn1 /\
       fn_fmp_convention_eq fn' fn1` by metis_tac[] >>
      gvs[venomInstTheory.fn_identity_metadata_eq_def,venomInstTheory.fn_static_input_eq_def,
          venomInstTheory.fn_static_layout_eq_def,venomInstTheory.fn_fmp_convention_eq_def])
  >> gvs[cfg_norm_iter_supply_def] >>
     metis_tac[cfg_norm_round_supply_metadata]
QED

Theorem cfg_norm_function_supply_metadata:
  cfg_norm_function_supply s fn = (fn',s') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn /\
  fn_fmp_convention_eq fn' fn
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_metadata]
QED

Theorem cfg_norm_functions_supply_metadata:
  !s fns fns' s'.
    cfg_norm_functions_supply s fns = (fns',s') ==>
    LIST_REL
      (\fn' fn.
         fn_identity_metadata_eq fn' fn /\
         fn_static_input_eq fn' fn /\
         fn_static_layout_eq fn' fn /\
         fn_fmp_convention_eq fn' fn) fns' fns
Proof
  Induct_on `fns` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_functions_supply_def]
  >> Cases_on `cfg_norm_function_supply s h` >>
     rename1 `cfg_norm_function_supply s h = (h',s1)` >>
     Cases_on `cfg_norm_functions_supply s1 fns` >>
     rename1 `cfg_norm_functions_supply s1 fns = (rest,s2)` >>
     gvs[cfg_norm_functions_supply_def] >>
     metis_tac[cfg_norm_function_supply_metadata]
QED

Theorem cfg_norm_configured_metadata:
  cfg_norm_configured_with_supply unit = (unit',s') ==>
  LIST_REL
    (\fn' fn.
       fn_identity_metadata_eq fn' fn /\
       fn_static_input_eq fn' fn /\
       fn_static_layout_eq fn' fn /\
       fn_fmp_convention_eq fn' fn)
    unit'.cu_context.ctx_functions unit.cu_context.ctx_functions
Proof
  rpt strip_tac >>
  Cases_on `cfg_norm_functions_supply (init_ir_supply unit)
              unit.cu_context.ctx_functions` >>
  gvs[cfg_norm_configured_with_supply_def,cfg_norm_unit_supply_def,
      cfg_norm_context_supply_def] >>
  metis_tac[cfg_norm_functions_supply_metadata]
QED


(* ===== INVOKE-target collector boundaries ===== *)

Definition cfg_block_invoke_labels_def:
  cfg_block_invoke_labels bb =
    MAP FST (get_invoke_targets bb.bb_instructions)
End

Theorem cfg_invoke_labels_cons:
  MAP FST (get_invoke_targets (inst::insts)) =
  MAP FST (get_invoke_targets [inst]) ++
  MAP FST (get_invoke_targets insts)
Proof
  simp[get_invoke_targets_def] >> rpt CASE_TAC >> gvs[]
QED

Theorem cfg_invoke_labels_append:
  !xs ys.
    MAP FST (get_invoke_targets (xs ++ ys)) =
    MAP FST (get_invoke_targets xs) ++ MAP FST (get_invoke_targets ys)
Proof
  Induct >- simp[get_invoke_targets_def] >> rpt gen_tac >>
  pure_once_rewrite_tac[listTheory.APPEND] >>
  once_rewrite_tac[cfg_invoke_labels_cons] >> simp[]
QED

Theorem cfg_fn_insts_blocks_invoke_labels:
  !bbs.
    MAP FST (get_invoke_targets (fn_insts_blocks bbs)) =
    FLAT (MAP cfg_block_invoke_labels bbs)
Proof
  Induct >>
  simp[venomInstTheory.fn_insts_blocks_def,cfg_block_invoke_labels_def,
       cfg_invoke_labels_append,get_invoke_targets_def]
QED

Theorem cfg_fcg_scan_function_invoke_labels:
  MAP FST (fcg_scan_function fn) =
  FLAT (MAP cfg_block_invoke_labels fn.fn_blocks)
Proof
  simp[fcg_scan_function_def,venomInstTheory.fn_insts_def,
       cfg_fn_insts_blocks_invoke_labels]
QED

Theorem subst_label_inst_opcode[simp]:
  (subst_label_inst old new inst).inst_opcode = inst.inst_opcode
Proof
  simp[subst_label_inst_def]
QED

Theorem map_subst_label_terminator_invoke_labels:
  !insts.
    MAP FST
      (get_invoke_targets
        (MAP (\inst. if is_terminator inst.inst_opcode
                     then subst_label_inst old new inst else inst) insts)) =
    MAP FST (get_invoke_targets insts)
Proof
  Induct >- simp[get_invoke_targets_def] >> rpt gen_tac >>
  Cases_on `is_terminator h.inst_opcode`
  >- (`h.inst_opcode <> INVOKE` by
        (strip_tac >> gvs[venomInstTheory.is_terminator_def]) >>
      simp[Once get_invoke_targets_def] >>
      once_rewrite_tac[get_invoke_targets_def] >> simp[])
  >> simp[Once get_invoke_targets_def] >>
     once_rewrite_tac[get_invoke_targets_def] >> rpt CASE_TAC >> gvs[]
QED

Theorem subst_label_terminator_invoke_labels:
  cfg_block_invoke_labels (subst_label_terminator old new bb) =
  cfg_block_invoke_labels bb
Proof
  simp[cfg_block_invoke_labels_def,subst_label_terminator_def,
       map_subst_label_terminator_invoke_labels]
QED

Theorem map_update_phis_for_split_invoke_labels:
  !insts.
    MAP FST
      (get_invoke_targets
        (MAP (\inst. if inst.inst_opcode <> PHI then inst
                     else inst with inst_operands :=
                       update_phi_ops old new repls inst.inst_operands) insts)) =
    MAP FST (get_invoke_targets insts)
Proof
  Induct >- simp[get_invoke_targets_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (gvs[] >> simp[Once get_invoke_targets_def] >>
      once_rewrite_tac[get_invoke_targets_def] >> simp[])
  >> simp[Once get_invoke_targets_def] >>
     once_rewrite_tac[get_invoke_targets_def] >> rpt CASE_TAC >> gvs[]
QED

Theorem update_phis_for_split_invoke_labels:
  cfg_block_invoke_labels (update_phis_for_split old new repls bb) =
  cfg_block_invoke_labels bb
Proof
  simp[cfg_block_invoke_labels_def,update_phis_for_split_def,
       map_update_phis_for_split_invoke_labels]
QED

Theorem build_forwarding_assigns_supply_no_invoke:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    get_invoke_targets insts = []
Proof
  Induct_on `vars` >> rpt gen_tac >> strip_tac
  >- gvs[build_forwarding_assigns_supply_def,get_invoke_targets_def]
  >> Cases_on `fresh_ir_var s` >>
     rename1 `fresh_ir_var s = (new_var,s1)` >>
     Cases_on `fresh_inst_id s1` >>
     rename1 `fresh_inst_id s1 = (id,s2)` >>
     Cases_on `build_forwarding_assigns_supply s2 vars` >>
     PairCases_on `r` >>
     rename1 `build_forwarding_assigns_supply s2 vars =
              (rest_repls,rest_insts,s3)` >>
     gvs[build_forwarding_assigns_supply_def,get_invoke_targets_def] >>
     metis_tac[]
QED

Theorem build_split_block_supply_no_invoke:
  build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') ==>
  cfg_block_invoke_labels split_bb = []
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (split_label,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
      (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
              target_bb.bb_instructions))` >> PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ =
           (var_repls,fwd_insts,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (jmp_id,s3)` >>
  gvs[build_split_block_supply_def,cfg_block_invoke_labels_def,
      cfg_invoke_labels_append,get_invoke_targets_def] >>
  metis_tac[build_forwarding_assigns_supply_no_invoke]
QED



Theorem MEM_FLAT_MAP_replace_block_subset:
  !bbs lbl new_bb C x.
    MEM x (FLAT (MAP C (replace_block lbl new_bb bbs))) ==>
    MEM x (C new_bb) \/ MEM x (FLAT (MAP C bbs))
Proof
  Induct_on `bbs`
  >> simp[replace_block_def, listTheory.MEM_APPEND]
  >> rpt strip_tac
  >> Cases_on `h.bb_label = lbl`
  >> gvs[replace_block_def, listTheory.MEM_APPEND]
  >> metis_tac[]
QED

Theorem insert_split_supply_invoke_labels_subset:
  MEM pred_bb fn.fn_blocks /\ MEM target_bb fn.fn_blocks /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  EVERY (\t. MEM t (MAP FST (fcg_scan_function fn)))
        (MAP FST (fcg_scan_function fn'))
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  rename1 `build_split_block_supply s pred_bb target_bb =
           (split_bb,repls,s1)` >>
  gvs[insert_split_supply_def] >>
  qabbrev_tac `pred' = subst_label_terminator
    target_bb.bb_label split_bb.bb_label pred_bb` >>
  qabbrev_tac `target' = update_phis_for_split
    pred_bb.bb_label split_bb.bb_label repls target_bb` >>
  `cfg_block_invoke_labels pred' = cfg_block_invoke_labels pred_bb` by
    simp[Abbr `pred'`,subst_label_terminator_invoke_labels] >>
  `cfg_block_invoke_labels target' = cfg_block_invoke_labels target_bb` by
    simp[Abbr `target'`,update_phis_for_split_invoke_labels] >>
  `cfg_block_invoke_labels split_bb = []` by
    metis_tac[build_split_block_supply_no_invoke] >>
  simp[cfg_fcg_scan_function_invoke_labels,listTheory.EVERY_MEM,
       listTheory.MEM_APPEND] >>
  metis_tac[MEM_FLAT_MAP_replace_block_subset,MEM_FLAT_MAP_component]
QED
Theorem insert_split_supply_invoke_labels:
  ALL_DISTINCT (fn_labels fn) /\
  MEM pred_bb fn.fn_blocks /\ MEM target_bb fn.fn_blocks /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  rename1 `build_split_block_supply s pred_bb target_bb =
           (split_bb,repls,s1)` >>
  gvs[insert_split_supply_def] >>
  qabbrev_tac `pred' = subst_label_terminator
    target_bb.bb_label split_bb.bb_label pred_bb` >>
  qabbrev_tac `target' = update_phis_for_split
    pred_bb.bb_label split_bb.bb_label repls target_bb` >>
  `cfg_block_invoke_labels pred' = cfg_block_invoke_labels pred_bb` by
    simp[Abbr `pred'`,subst_label_terminator_invoke_labels] >>
  `cfg_block_invoke_labels target' = cfg_block_invoke_labels target_bb` by
    simp[Abbr `target'`,update_phis_for_split_invoke_labels] >>
  `pred'.bb_label = pred_bb.bb_label` by
    simp[Abbr `pred'`,subst_label_terminator_def] >>
  `target'.bb_label = target_bb.bb_label` by
    simp[Abbr `target'`,update_phis_for_split_def] >>
  `cfg_block_invoke_labels split_bb = []` by
    metis_tac[build_split_block_supply_no_invoke] >>
  `FLAT (MAP cfg_block_invoke_labels
      (replace_block pred_bb.bb_label pred' fn.fn_blocks)) =
   FLAT (MAP cfg_block_invoke_labels fn.fn_blocks)` by
    (irule FLAT_MAP_replace_block_unique >>
     conj_tac >- gvs[venomInstTheory.fn_labels_def] >>
     qexists `pred_bb` >> simp[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label)
      (replace_block pred_bb.bb_label pred' fn.fn_blocks))` by
    gvs[venomInstTheory.fn_labels_def] >>
  Cases_on `pred_bb.bb_label = target_bb.bb_label`
  >- (`pred_bb = target_bb` by
        metis_tac[all_distinct_map_mem_inj_cfg,
                  venomInstTheory.fn_labels_def] >>
      `MEM pred'
         (replace_block pred_bb.bb_label pred' fn.fn_blocks)` by
        metis_tac[MEM_replace_block_new] >>
      `FLAT (MAP cfg_block_invoke_labels
          (replace_block target_bb.bb_label target'
            (replace_block pred_bb.bb_label pred' fn.fn_blocks))) =
       FLAT (MAP cfg_block_invoke_labels
          (replace_block pred_bb.bb_label pred' fn.fn_blocks))` by
        (irule FLAT_MAP_replace_block_unique >> simp[] >> metis_tac[]) >>
      gvs[cfg_fcg_scan_function_invoke_labels,Abbr `pred'`,Abbr `target'`])
  >> `MEM target_bb
        (replace_block pred_bb.bb_label pred' fn.fn_blocks)` by
       metis_tac[MEM_replace_block_other] >>
     `FLAT (MAP cfg_block_invoke_labels
        (replace_block target_bb.bb_label target'
          (replace_block pred_bb.bb_label pred' fn.fn_blocks))) =
      FLAT (MAP cfg_block_invoke_labels
        (replace_block pred_bb.bb_label pred' fn.fn_blocks))` by
       (irule FLAT_MAP_replace_block_unique >> simp[] >> metis_tac[]) >>
     gvs[cfg_fcg_scan_function_invoke_labels,Abbr `pred'`,Abbr `target'`]
QED


Theorem find_and_split_supply_invoke_labels_subset:
  !bbs fn s fn' changed s'.
    EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    EVERY (\t. MEM t (MAP FST (fcg_scan_function fn)))
          (MAP FST (fcg_scan_function fn'))
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- gvs[find_and_split_supply_def,listTheory.EVERY_MEM]
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     `MEM x (block_preds fn h.bb_label)` by metis_tac[FIND_SOME_MEM] >>
     `MEM x fn.fn_blocks` by gvs[block_preds_def,listTheory.MEM_FILTER] >>
     metis_tac[insert_split_supply_invoke_labels_subset]
QED

Theorem find_and_split_supply_invoke_labels:
  !bbs fn s fn' changed s'.
    EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
    ALL_DISTINCT (fn_labels fn) /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- gvs[find_and_split_supply_def]
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     `MEM x (block_preds fn h.bb_label)` by metis_tac[FIND_SOME_MEM] >>
     `MEM x fn.fn_blocks` by gvs[block_preds_def,listTheory.MEM_FILTER] >>
     metis_tac[insert_split_supply_invoke_labels]
QED


Theorem cfg_norm_round_supply_invoke_labels_subset:
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  EVERY (\t. MEM t (MAP FST (fcg_scan_function fn)))
        (MAP FST (fcg_scan_function fn'))
Proof
  rpt strip_tac >>
  irule find_and_split_supply_invoke_labels_subset >>
  qexistsl [`fn.fn_blocks`,`changed`,`s`,`s'`] >>
  gvs[cfg_norm_round_supply_def,listTheory.EVERY_MEM]
QED

Theorem cfg_norm_round_supply_invoke_labels:
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  rpt strip_tac >>
  irule find_and_split_supply_invoke_labels >>
  conj_tac >- simp[] >>
  qexistsl [`fn.fn_blocks`,`changed`,`s`,`s'`] >>
  gvs[cfg_norm_round_supply_def,listTheory.EVERY_MEM]
QED


Theorem insert_split_supply_labels_distinct:
  ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  MEM pred_bb fn.fn_blocks /\ MEM target_bb fn.fn_blocks /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  ALL_DISTINCT (fn_labels fn')
Proof
  strip_tac >>
  drule insert_split_supply_labels >> strip_tac >>
  `~MEM split_bb.bb_label s.irs_used_labels` by
    metis_tac[build_split_block_supply_label_fresh] >>
  `~MEM split_bb.bb_label (fn_labels fn)` by
    (CCONTR_TAC >> gvs[] >>
     `MEM split_bb.bb_label (fn_ir_labels fn)` by
       metis_tac[MEM_fn_labels_fn_ir_labels] >>
     gvs[cfg_supply_covers_fn_def,listTheory.EVERY_MEM]) >>
  gvs[listTheory.ALL_DISTINCT_APPEND]
QED

Theorem find_and_split_supply_labels_distinct:
  !bbs fn s fn' changed s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
    EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
    ALL_DISTINCT (fn_labels fn) /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    ALL_DISTINCT (fn_labels fn')
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- gvs[find_and_split_supply_def]
  >> Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[])
  >> Cases_on `insert_split_supply s fn x h` >>
     gvs[find_and_split_supply_def] >>
     `MEM x (block_preds fn h.bb_label)` by metis_tac[FIND_SOME_MEM] >>
     `MEM x fn.fn_blocks` by gvs[block_preds_def,listTheory.MEM_FILTER] >>
     metis_tac[insert_split_supply_labels_distinct]
QED

Theorem cfg_norm_round_supply_labels_distinct:
  ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  ALL_DISTINCT (fn_labels fn')
Proof
  rpt strip_tac >>
  irule find_and_split_supply_labels_distinct >>
  qexistsl [`fn.fn_blocks`,`changed`,`fn`,`s`,`s'`] >>
  gvs[cfg_norm_round_supply_def,listTheory.EVERY_MEM]
QED



Theorem cfg_norm_iter_supply_invoke_labels_subset:
  !n s fn fn' s'.
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    EVERY (\t. MEM t (MAP FST (fcg_scan_function fn)))
          (MAP FST (fcg_scan_function fn'))
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def,listTheory.EVERY_MEM]
  >> Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
     rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
     Cases_on `changed`
  >- (gvs[cfg_norm_iter_supply_def] >>
      `EVERY (\t. MEM t (MAP FST (fcg_scan_function fn)))
             (MAP FST (fcg_scan_function fn1))` by
        metis_tac[cfg_norm_round_supply_invoke_labels_subset] >>
      `EVERY (\t. MEM t (MAP FST (fcg_scan_function fn1)))
             (MAP FST (fcg_scan_function fn'))` by metis_tac[] >>
      gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >> gvs[cfg_norm_iter_supply_def] >>
     metis_tac[cfg_norm_round_supply_invoke_labels_subset]
QED

Theorem cfg_norm_iter_supply_invoke_labels:
  !n s fn fn' s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
    ALL_DISTINCT (fn_labels fn) /\
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def]
  >> Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
     rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
     Cases_on `changed`
  >- (gvs[cfg_norm_iter_supply_def] >>
      `cfg_fn_supply_contract s fn1 s1` by
        metis_tac[cfg_norm_round_supply_contract] >>
      `cfg_supply_extends s s1` by gvs[cfg_fn_supply_contract_def] >>
      `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
      `cfg_supply_covers_fn s1 fn1` by
        metis_tac[cfg_norm_round_supply_covered] >>
      `ALL_DISTINCT (fn_labels fn1)` by
        metis_tac[cfg_norm_round_supply_labels_distinct] >>
      `MAP FST (fcg_scan_function fn1) =
       MAP FST (fcg_scan_function fn)` by
        metis_tac[cfg_norm_round_supply_invoke_labels] >>
      `MAP FST (fcg_scan_function fn') =
       MAP FST (fcg_scan_function fn1)` by metis_tac[] >>
      metis_tac[])
  >> gvs[cfg_norm_iter_supply_def] >>
     metis_tac[cfg_norm_round_supply_invoke_labels]
QED


Theorem cfg_norm_function_supply_invoke_labels_subset:
  cfg_norm_function_supply s fn = (fn',s') ==>
  EVERY (\t. MEM t (MAP FST (fcg_scan_function fn)))
        (MAP FST (fcg_scan_function fn'))
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_invoke_labels_subset]
QED

Theorem cfg_norm_function_supply_invoke_labels:
  ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_invoke_labels]
QED


Theorem cfg_norm_iter_supply_label_invariants:
  !n s fn fn' s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
    ALL_DISTINCT (fn_labels fn) /\
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    cfg_supply_extends s s' /\ cfg_supply_covers_fn s' fn' /\
    ALL_DISTINCT (fn_labels fn')
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def,cfg_supply_extends_refl]
  >> Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
     rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
     Cases_on `changed`
  >- (gvs[cfg_norm_iter_supply_def] >>
      `cfg_fn_supply_contract s fn1 s1` by
        metis_tac[cfg_norm_round_supply_contract] >>
      `cfg_supply_extends s s1` by gvs[cfg_fn_supply_contract_def] >>
      `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
      `cfg_supply_covers_fn s1 fn1` by
        metis_tac[cfg_norm_round_supply_covered] >>
      `ALL_DISTINCT (fn_labels fn1)` by
        metis_tac[cfg_norm_round_supply_labels_distinct] >>
      `cfg_supply_extends s1 s' /\ cfg_supply_covers_fn s' fn' /\
       ALL_DISTINCT (fn_labels fn')` by metis_tac[] >>
      metis_tac[cfg_supply_extends_trans])
  >> gvs[cfg_norm_iter_supply_def] >>
     `cfg_fn_supply_contract s fn' s'` by
       metis_tac[cfg_norm_round_supply_contract] >>
     `cfg_supply_extends s s'` by gvs[cfg_fn_supply_contract_def] >>
     metis_tac[cfg_norm_round_supply_covered,
               cfg_norm_round_supply_labels_distinct]
QED

Theorem cfg_norm_function_supply_label_invariants:
  ir_supply_inst_ok s /\ cfg_supply_covers_fn s fn /\
  ALL_DISTINCT (fn_labels fn) /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  cfg_supply_extends s s' /\ cfg_supply_covers_fn s' fn' /\
  ALL_DISTINCT (fn_labels fn')
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_label_invariants]
QED


Theorem cfg_norm_functions_supply_invoke_labels:
  !s fns fns' s'.
    ir_supply_inst_ok s /\ cfg_supply_covers_functions s fns /\
    EVERY (\fn. ALL_DISTINCT (fn_labels fn)) fns /\
    cfg_norm_functions_supply s fns = (fns',s') ==>
    MAP (\fn. MAP FST (fcg_scan_function fn)) fns' =
    MAP (\fn. MAP FST (fcg_scan_function fn)) fns
Proof
  Induct_on `fns` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_functions_supply_def]
  >> Cases_on `cfg_norm_function_supply s h` >>
     rename1 `cfg_norm_function_supply s h = (h',s1)` >>
     Cases_on `cfg_norm_functions_supply s1 fns` >>
     rename1 `cfg_norm_functions_supply s1 fns = (rest,s2)` >>
     gvs[cfg_norm_functions_supply_def,cfg_supply_covers_functions_def] >>
     `MAP FST (fcg_scan_function h') =
      MAP FST (fcg_scan_function h)` by
       metis_tac[cfg_norm_function_supply_invoke_labels] >>
     `cfg_supply_extends s s1` by
       metis_tac[cfg_norm_function_supply_label_invariants] >>
     `ir_supply_inst_ok s1` by gvs[cfg_supply_extends_def] >>
     `cfg_supply_covers_functions s1 fns` by
       (gvs[cfg_supply_covers_functions_def,listTheory.EVERY_MEM] >>
        metis_tac[cfg_supply_covers_fn_mono]) >>
     conj_tac >- simp[] >>
     first_x_assum irule >>
     qexistsl [`s1`,`s'`] >>
     gvs[cfg_supply_covers_functions_def]
QED

Theorem cfg_norm_configured_invoke_labels:
  EVERY (\fn. ALL_DISTINCT (fn_labels fn))
    unit.cu_context.ctx_functions /\
  cfg_norm_configured_with_supply unit = (unit',s') ==>
  MAP (\fn. MAP FST (fcg_scan_function fn))
      unit'.cu_context.ctx_functions =
  MAP (\fn. MAP FST (fcg_scan_function fn))
      unit.cu_context.ctx_functions
Proof
  rpt strip_tac >>
  Cases_on `cfg_norm_functions_supply (init_ir_supply unit)
              unit.cu_context.ctx_functions` >>
  rename1 `cfg_norm_functions_supply (init_ir_supply unit)
             unit.cu_context.ctx_functions = (fns',s1)` >>
  gvs[cfg_norm_configured_with_supply_def,cfg_norm_unit_supply_def,
      cfg_norm_context_supply_def] >>
  irule cfg_norm_functions_supply_invoke_labels >>
  conj_tac >- simp[] >>
  qexistsl [`init_ir_supply unit`,`s'`] >>
  simp[init_ir_supply_inst_ok] >>
  metis_tac[init_ir_supply_cfg_supply_covers_unit,
            cfg_supply_covers_unit_functions]
QED

(* ===== Raw FMP opcode preservation ===== *)
Definition cfg_blocks_no_raw_def[local]:
  cfg_blocks_no_raw blocks <=>
    EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                       bb.bb_instructions) blocks
End

Theorem cfg_blocks_no_raw_fn_insts[local]:
  cfg_blocks_no_raw blocks <=>
  !inst. MEM inst (fn_insts_blocks blocks) ==>
         ~is_raw_fmp_opcode inst.inst_opcode
Proof
  rewrite_tac[cfg_blocks_no_raw_def] >>
  Induct_on `blocks` >>
  simp[venomInstTheory.fn_insts_blocks_def,listTheory.EVERY_MEM,listTheory.MEM_APPEND,
       DISJ_IMP_THM,FORALL_AND_THM]
QED

Theorem build_forwarding_assigns_supply_no_raw[local]:
  !vars s repls insts s'.
    build_forwarding_assigns_supply s vars = (repls,insts,s') ==>
    EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) insts
Proof
  Induct_on `vars` >> rpt strip_tac
  >- gvs[build_forwarding_assigns_supply_def] >>
  Cases_on `fresh_ir_var s` >>
  rename1 `fresh_ir_var s = (new_var,s1)` >>
  Cases_on `fresh_inst_id s1` >>
  rename1 `fresh_inst_id s1 = (id,s2)` >>
  Cases_on `build_forwarding_assigns_supply s2 vars` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s2 vars =
           (rest_repls,rest_insts,s3)` >>
  gvs[build_forwarding_assigns_supply_def,
      venomInstTheory.is_raw_fmp_opcode_def] >>
  metis_tac[]
QED

Theorem build_split_block_supply_no_raw[local]:
  build_split_block_supply s pred_bb target_bb = (split_bb,repls,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) split_bb.bb_instructions
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_label s` >>
  rename1 `fresh_ir_label s = (split_label,s1)` >>
  Cases_on `build_forwarding_assigns_supply s1
    (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
           target_bb.bb_instructions))` >>
  PairCases_on `r` >>
  rename1 `build_forwarding_assigns_supply s1 _ =
           (var_repls,fwd_insts,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (jmp_id,s3)` >>
  gvs[build_split_block_supply_def,
      venomInstTheory.is_raw_fmp_opcode_def] >>
  metis_tac[build_forwarding_assigns_supply_no_raw]
QED

Theorem subst_label_terminator_no_raw[local]:
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) bb.bb_instructions ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
        (subst_label_terminator old new bb).bb_instructions
Proof
  simp[subst_label_terminator_def,listTheory.EVERY_MAP,COND_RAND,
       subst_label_inst_opcode]
QED

Theorem update_phis_for_split_no_raw[local]:
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) bb.bb_instructions ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
        (update_phis_for_split old new repls bb).bb_instructions
Proof
  strip_tac >>
  simp[update_phis_for_split_def,listTheory.EVERY_MAP] >>
  irule listTheory.EVERY_MONOTONIC >>
  qexists `\i. ~is_raw_fmp_opcode i.inst_opcode` >> simp[] >>
  rpt strip_tac >> Cases_on `x.inst_opcode <> PHI` >>
  gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem replace_block_no_raw[local]:
  !blocks. cfg_blocks_no_raw blocks /\
    EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) new_bb.bb_instructions ==>
    cfg_blocks_no_raw (replace_block lbl new_bb blocks)
Proof
  rewrite_tac[cfg_blocks_no_raw_def,replace_block_def,
              listTheory.EVERY_MAP] >>
  rpt strip_tac >>
  irule listTheory.EVERY_MONOTONIC >>
  qexists `\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                      bb.bb_instructions` >> simp[] >>
  rpt strip_tac >> Cases_on `x.bb_label = lbl` >> gvs[]
QED

Theorem insert_split_supply_no_raw[local]:
  cfg_blocks_no_raw fn.fn_blocks /\
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) pred_bb.bb_instructions /\
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) target_bb.bb_instructions /\
  insert_split_supply s fn pred_bb target_bb = (fn',s') ==>
  cfg_blocks_no_raw fn'.fn_blocks
Proof
  rpt strip_tac >>
  Cases_on `build_split_block_supply s pred_bb target_bb` >>
  PairCases_on `r` >>
  rename1 `build_split_block_supply s pred_bb target_bb =
           (split_bb,repls,s1)` >>
  gvs[insert_split_supply_def] >>
  `EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
         split_bb.bb_instructions` by
    metis_tac[build_split_block_supply_no_raw] >>
  `EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
         (subst_label_terminator target_bb.bb_label split_bb.bb_label
            pred_bb).bb_instructions` by
    metis_tac[subst_label_terminator_no_raw] >>
  `cfg_blocks_no_raw
     (replace_block pred_bb.bb_label
       (subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb)
       fn.fn_blocks)` by metis_tac[replace_block_no_raw] >>
  `EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
         (update_phis_for_split pred_bb.bb_label split_bb.bb_label repls
            target_bb).bb_instructions` by
    metis_tac[update_phis_for_split_no_raw] >>
  `cfg_blocks_no_raw
     (replace_block target_bb.bb_label
       (update_phis_for_split pred_bb.bb_label split_bb.bb_label repls target_bb)
       (replace_block pred_bb.bb_label
         (subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb)
         fn.fn_blocks))` by metis_tac[replace_block_no_raw] >>
  gvs[cfg_blocks_no_raw_def]
QED

Theorem find_and_split_supply_no_raw[local]:
  !bbs fn s fn' changed s'.
    cfg_blocks_no_raw fn.fn_blocks /\
    EVERY (\bb. MEM bb fn.fn_blocks) bbs /\
    find_and_split_supply fn s bbs = (fn',changed,s') ==>
    cfg_blocks_no_raw fn'.fn_blocks
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- gvs[find_and_split_supply_def] >>
  Cases_on `LENGTH (block_preds fn h.bb_label) <= 1`
  >- (gvs[find_and_split_supply_def] >> metis_tac[]) >>
  Cases_on `FIND (\p. num_succs p > 1) (block_preds fn h.bb_label)`
  >- (gvs[find_and_split_supply_def] >> metis_tac[]) >>
  Cases_on `insert_split_supply s fn x h` >>
  gvs[find_and_split_supply_def] >>
  `EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) h.bb_instructions` by
    (gvs[cfg_blocks_no_raw_def,listTheory.EVERY_MEM] >> metis_tac[]) >>
  `MEM x fn.fn_blocks` by
    (imp_res_tac FIND_SOME_MEM >>
     gvs[block_preds_def,listTheory.MEM_FILTER]) >>
  `EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) x.bb_instructions` by
    (gvs[cfg_blocks_no_raw_def,listTheory.EVERY_MEM] >> metis_tac[]) >>
  metis_tac[insert_split_supply_no_raw]
QED

Theorem cfg_norm_round_supply_no_raw[local]:
  cfg_blocks_no_raw fn.fn_blocks /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  cfg_blocks_no_raw fn'.fn_blocks
Proof
  rpt strip_tac >>
  irule find_and_split_supply_no_raw >>
  qexistsl [`fn.fn_blocks`,`changed`,`fn`,`s`,`s'`] >>
  gvs[cfg_norm_round_supply_def,listTheory.EVERY_MEM]
QED

Theorem cfg_norm_iter_supply_no_raw[local]:
  !n s fn fn' s'.
    cfg_blocks_no_raw fn.fn_blocks /\
    cfg_norm_iter_supply n s fn = (fn',s') ==>
    cfg_blocks_no_raw fn'.fn_blocks
Proof
  Induct_on `n` >> rpt gen_tac >> strip_tac
  >- gvs[cfg_norm_iter_supply_def] >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def] >>
  metis_tac[cfg_norm_round_supply_no_raw]
QED

Theorem cfg_norm_function_supply_no_raw_fmp_ops:
  no_raw_fmp_ops fn ==>
  no_raw_fmp_ops (FST (cfg_norm_function_supply s fn))
Proof
  simp[venomInstTheory.no_raw_fmp_ops_def,venomInstTheory.fn_insts_def,
       GSYM cfg_blocks_no_raw_fn_insts,cfg_norm_function_supply_def] >>
  Cases_on `cfg_norm_iter_supply (2 * LENGTH fn.fn_blocks) s fn` >>
  simp[] >> metis_tac[cfg_norm_iter_supply_no_raw]
QED
