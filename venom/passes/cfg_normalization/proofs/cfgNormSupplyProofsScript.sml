Theory cfgNormSupplyProofs
Ancestors
  cfgNormDefs

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
