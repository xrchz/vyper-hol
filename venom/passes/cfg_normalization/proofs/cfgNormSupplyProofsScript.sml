Theory cfgNormSupplyProofs
Ancestors
  cfgNormDefs irSupply

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

(* The all-occurrence variable and label collectors are coverage collectors,
   not declaration-identity collectors.  Generated forwarding variables occur
   once as ASSIGN outputs and again as PHI operands; block labels also occur as
   both declarations and branch operands. *)
Theorem cfg_norm_supply_collectors_not_identity_sets[local]:
  let result = cfg_norm_configured_with_supply
                 cfg_norm_supply_collision_probe_unit in
    ~ALL_DISTINCT (unit_ir_vars (FST result)) /\
    ~ALL_DISTINCT (unit_ir_labels (FST result))
Proof
  EVAL_TAC
QED

(* In contrast, the allocator-event prefixes are pairwise fresh and each event
   is materialized as a declaration in the configured result. *)
Theorem cfg_norm_supply_delta_collision_probe:
  let unit = cfg_norm_supply_collision_probe_unit in
  let result = cfg_norm_configured_with_supply unit in
  let unit' = FST result in
  let s' = SND result in
    cfg_supply_extends (init_ir_supply unit) s' /\
    EVERY (cfg_id_declared unit') [9004;9003;9002;9001] /\
    EVERY (cfg_var_declared unit') ["formal_var_2";"formal_var_1"] /\
    EVERY (cfg_block_label_declared unit')
      ["formal_label_2";"formal_label_1"]
Proof
  simp[] >>
  conj_tac
  >- (simp[cfg_supply_extends_def] >>
      qexistsl [`[9004;9003;9002;9001]`,
                `["formal_var_2";"formal_var_1"]`,
                `["formal_label_2";"formal_label_1"]`] >>
      EVAL_TAC)
  >> EVAL_TAC
QED


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
