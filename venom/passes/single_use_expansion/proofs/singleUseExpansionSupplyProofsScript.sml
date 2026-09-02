(*
 * Supply freshness and structural contracts for configured SUE.
 *)

Theory singleUseExpansionSupplyProofs
Ancestors
  singleUseExpansionDefs irSupply

(* unit_ir_vars is an occurrence collector (definitions and uses), so it is
   deliberately not ALL_DISTINCT after a generated ASSIGN feeds the rewritten
   instruction.  This checked probe guards the proof interface against
   confusing occurrence uniqueness with uniqueness of generated names. *)
Theorem sue_unit_ir_vars_occurrence_counterexample:
  ~ALL_DISTINCT
     (unit_ir_vars
        (FST (sue_configured_with_supply sue_supply_collision_probe_unit)))
Proof
  EVAL_TAC
QED

Theorem sue_alloc_assign_supply_contract:
  ir_supply_inst_ok s /\ sue_alloc_assign_supply s op = (a,newop,s') ==>
  ?v id.
    a.inst_id = id /\ a.inst_outputs = [v] /\ newop = Var v /\
    ~MEM v s.irs_used_vars /\
    s'.irs_used_vars = v::s.irs_used_vars /\
    ~MEM id s.irs_used_inst_ids /\
    s'.irs_used_inst_ids = id::s.irs_used_inst_ids /\
    ir_supply_inst_ok s'
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_var s` >>
  rename1 `fresh_ir_var s = (v,s1)` >>
  Cases_on `fresh_inst_id s1` >>
  rename1 `fresh_inst_id s1 = (id,s2)` >>
  gvs[sue_alloc_assign_supply_def] >>
  `~MEM v s.irs_used_vars /\
   s1.irs_used_vars = v::s.irs_used_vars /\
   s1.irs_used_inst_ids = s.irs_used_inst_ids /\
   s1.irs_next_inst = s.irs_next_inst` by
    metis_tac[fresh_ir_var_contract] >>
  `ir_supply_inst_ok s1` by
    gvs[ir_supply_inst_ok_def] >>
  `~MEM id s1.irs_used_inst_ids /\
   s'.irs_used_inst_ids = id::s1.irs_used_inst_ids /\
   s'.irs_used_vars = s1.irs_used_vars /\
   ir_supply_inst_ok s'` by
    metis_tac[fresh_inst_id_contract] >>
  gvs[]
QED
