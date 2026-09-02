(*
 * Supply freshness and structural contracts for configured SUE.
 *)

Theory singleUseExpansionSupplyProofs
Ancestors
  singleUseExpansionDefs irSupply venomInst

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


Definition sue_supply_extends_def:
  sue_supply_extends s s' <=>
    ?new_vars new_ids.
      s'.irs_used_vars = new_vars ++ s.irs_used_vars /\
      ALL_DISTINCT new_vars /\
      EVERY (\v. ~MEM v s.irs_used_vars) new_vars /\
      s'.irs_used_inst_ids = new_ids ++ s.irs_used_inst_ids /\
      ALL_DISTINCT new_ids /\
      EVERY (\id. ~MEM id s.irs_used_inst_ids) new_ids /\
      ir_supply_inst_ok s'
End

Theorem sue_supply_extends_refl:
  ir_supply_inst_ok s ==> sue_supply_extends s s
Proof
  simp[sue_supply_extends_def] >> metis_tac[]
QED

Theorem sue_supply_extends_members:
  sue_supply_extends s s' ==>
  (!v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars) /\
  (!id. MEM id s.irs_used_inst_ids ==> MEM id s'.irs_used_inst_ids)
Proof
  strip_tac >> gvs[sue_supply_extends_def]
QED

Theorem sue_supply_extends_trans:
  sue_supply_extends s s1 /\ sue_supply_extends s1 s2 ==>
  sue_supply_extends s s2
Proof
  simp[sue_supply_extends_def] >>
  rpt strip_tac >>
  qexistsl [`new_vars' ++ new_vars`,`new_ids' ++ new_ids`] >>
  gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM] >>
  simp[listTheory.APPEND_ASSOC] >> metis_tac[]
QED

Theorem sue_alloc_assign_supply_extends:
  ir_supply_inst_ok s /\ sue_alloc_assign_supply s op = (a,newop,s') ==>
  sue_supply_extends s s'
Proof
  strip_tac >> drule_all sue_alloc_assign_supply_contract >>
  strip_tac >>
  simp[sue_supply_extends_def] >> metis_tac[]
QED


Theorem sue_expand_ops_supply_extends:
  !dfg inst s ops op_idx assigns new_ops s'.
    ir_supply_inst_ok s /\
    sue_expand_ops_supply dfg inst s ops op_idx = (assigns,new_ops,s') ==>
    sue_supply_extends s s'
Proof
  Induct_on `ops` >> rpt strip_tac
  >- gvs[sue_expand_ops_supply_def, sue_supply_extends_refl]
  >> Cases_on `sue_expand_ops_supply dfg inst s ops (op_idx + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (op_idx + 1) =
           (more_assigns,more_ops,s1)` >>
  `sue_supply_extends s s1` by metis_tac[] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  Cases_on `~sue_needs_assign dfg inst op_idx`
  >- gvs[sue_expand_ops_supply_def] >>
  Cases_on `h`
  >- (Cases_on `sue_alloc_assign_supply s1 (Lit c)` >>
      PairCases_on `r` >>
      gvs[sue_expand_ops_supply_def] >>
      metis_tac[sue_alloc_assign_supply_extends,
                sue_supply_extends_trans])
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- gvs[sue_expand_ops_supply_def]
      >> Cases_on `sue_alloc_assign_supply s1 (Var s'')` >>
         PairCases_on `r` >>
         gvs[sue_expand_ops_supply_def] >>
         metis_tac[sue_alloc_assign_supply_extends,
                   sue_supply_extends_trans])
  >> gvs[sue_expand_ops_supply_def]
QED


Theorem sue_expand_inst_supply_extends:
  ir_supply_inst_ok s /\ sue_expand_inst_supply dfg s inst = (out,s') ==>
  sue_supply_extends s s'
Proof
  rpt strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def, sue_supply_extends_refl] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  gvs[sue_expand_inst_supply_def] >>
  metis_tac[sue_expand_ops_supply_extends]
QED

Theorem sue_expand_insts_supply_extends:
  !dfg s insts outs s'.
    ir_supply_inst_ok s /\
    sue_expand_insts_supply dfg s insts = (outs,s') ==>
    sue_supply_extends s s'
Proof
  Induct_on `insts` >> rpt strip_tac
  >- gvs[sue_expand_insts_supply_def, sue_supply_extends_refl] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (tail_out,s2)` >>
  gvs[sue_expand_insts_supply_def] >>
  `sue_supply_extends s s1` by metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `sue_supply_extends s1 s'` by metis_tac[] >>
  metis_tac[sue_supply_extends_trans]
QED

Theorem sue_expand_block_supply_extends:
  ir_supply_inst_ok s /\ sue_expand_block_supply dfg s bb = (bb',s') ==>
  sue_supply_extends s s'
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  metis_tac[sue_expand_insts_supply_extends]
QED

Theorem sue_expand_blocks_supply_extends:
  !dfg s bbs bbs' s'.
    ir_supply_inst_ok s /\
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    sue_supply_extends s s'
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[sue_expand_blocks_supply_def, sue_supply_extends_refl] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  rename1 `sue_expand_block_supply dfg s h = (bb1,s1)` >>
  Cases_on `sue_expand_blocks_supply dfg s1 bbs` >>
  rename1 `sue_expand_blocks_supply dfg s1 bbs = (bbs1,s2)` >>
  gvs[sue_expand_blocks_supply_def] >>
  `sue_supply_extends s s1` by metis_tac[sue_expand_block_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `sue_supply_extends s1 s'` by metis_tac[] >>
  metis_tac[sue_supply_extends_trans]
QED

Theorem sue_expand_function_supply_extends:
  ir_supply_inst_ok s /\ sue_expand_function_supply s fn = (fn',s') ==>
  sue_supply_extends s s'
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  metis_tac[sue_expand_blocks_supply_extends]
QED

Theorem sue_expand_functions_supply_extends:
  !s fns fns' s'.
    ir_supply_inst_ok s /\
    sue_expand_functions_supply s fns = (fns',s') ==>
    sue_supply_extends s s'
Proof
  Induct_on `fns` >> rpt strip_tac
  >- gvs[sue_expand_functions_supply_def, sue_supply_extends_refl] >>
  Cases_on `sue_expand_function_supply s h` >>
  rename1 `sue_expand_function_supply s h = (fn1,s1)` >>
  Cases_on `sue_expand_functions_supply s1 fns` >>
  rename1 `sue_expand_functions_supply s1 fns = (fns1,s2)` >>
  gvs[sue_expand_functions_supply_def] >>
  `sue_supply_extends s s1` by metis_tac[sue_expand_function_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `sue_supply_extends s1 s'` by metis_tac[] >>
  metis_tac[sue_supply_extends_trans]
QED

Theorem sue_expand_context_supply_extends:
  ir_supply_inst_ok s /\ sue_expand_context_supply s ctx = (ctx',s') ==>
  sue_supply_extends s s'
Proof
  rpt strip_tac >> Cases_on `sue_expand_functions_supply s ctx.ctx_functions` >>
  gvs[sue_expand_context_supply_def] >>
  metis_tac[sue_expand_functions_supply_extends]
QED

Theorem sue_unit_supply_extends:
  ir_supply_inst_ok s /\ sue_unit_supply s unit = (unit',s') ==>
  sue_supply_extends s s'
Proof
  rpt strip_tac >> Cases_on `sue_expand_context_supply s unit.cu_context` >>
  gvs[sue_unit_supply_def] >>
  metis_tac[sue_expand_context_supply_extends]
QED


Theorem sue_supply_extends_all_distinct:
  sue_supply_extends s s' /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT s.irs_used_inst_ids ==>
  ALL_DISTINCT s'.irs_used_vars /\
  ALL_DISTINCT s'.irs_used_inst_ids
Proof
  strip_tac >>
  gvs[sue_supply_extends_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_MEM] >> metis_tac[]
QED


Theorem sue_alloc_assign_supply_covered:
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars) (venomInst$operand_vars [op]) /\
  sue_alloc_assign_supply s op = (a,newop,s') ==>
  EVERY (\v. MEM v s'.irs_used_vars)
    (inst_ir_vars a ++ venomInst$operand_vars [newop]) /\
  MEM a.inst_id s'.irs_used_inst_ids
Proof
  rpt strip_tac >>
  drule_all sue_alloc_assign_supply_contract >> strip_tac >>
  gvs[sue_alloc_assign_supply_def, AllCaseEqs(), inst_ir_vars_def,
      inst_uses_def, operand_vars_def] >>
  Cases_on `op` >>
  gvs[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]
QED


Theorem sue_expand_ops_supply_covered:
  !dfg inst s ops op_idx assigns new_ops s'.
    ir_supply_inst_ok s /\
    EVERY (\v. MEM v s.irs_used_vars) (venomInst$operand_vars ops) /\
    sue_expand_ops_supply dfg inst s ops op_idx = (assigns,new_ops,s') ==>
    EVERY (\v. MEM v s'.irs_used_vars)
      (FLAT (MAP inst_ir_vars assigns) ++ venomInst$operand_vars new_ops) /\
    EVERY (\i. MEM i.inst_id s'.irs_used_inst_ids) assigns
Proof
  Induct_on `ops`
  >- (rpt strip_tac >>
      gvs[sue_expand_ops_supply_def,
          venomInstTheory.operand_vars_def])
  >> rpt strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (op_idx + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (op_idx + 1) =
           (more_assigns,more_ops,s1)` >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_ops_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `EVERY (\v. MEM v s.irs_used_vars) (venomInst$operand_vars ops)` by
    (Cases_on `h` >>
     gvs[venomInstTheory.operand_vars_def,
         venomInstTheory.operand_var_def]) >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (FLAT (MAP inst_ir_vars more_assigns) ++
      venomInst$operand_vars more_ops) /\
   EVERY (\i. MEM i.inst_id s1.irs_used_inst_ids) more_assigns` by
    metis_tac[] >>
  `!v. MEM v s.irs_used_vars ==> MEM v s1.irs_used_vars` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (venomInst$operand_vars [h])` by
    (Cases_on `h` >>
     gvs[venomInstTheory.operand_vars_def,
         venomInstTheory.operand_var_def] >>
     qpat_assum `!v. MEM v s.irs_used_vars ==>
                      MEM v s1.irs_used_vars`
       (qspec_then `s''` irule) >> simp[]) >>
  Cases_on `sue_alloc_assign_supply s1 h` >>
  PairCases_on `r` >>
  rename1 `sue_alloc_assign_supply s1 h = (a,newop,s2)` >>
  `sue_supply_extends s1 s2` by
    metis_tac[sue_alloc_assign_supply_extends] >>
  `EVERY (\v. MEM v s2.irs_used_vars)
     (inst_ir_vars a ++ venomInst$operand_vars [newop]) /\
   MEM a.inst_id s2.irs_used_inst_ids` by
    metis_tac[sue_alloc_assign_supply_covered] >>
  `!v. MEM v s1.irs_used_vars ==> MEM v s2.irs_used_vars` by
    metis_tac[sue_supply_extends_members] >>
  `!id. MEM id s1.irs_used_inst_ids ==> MEM id s2.irs_used_inst_ids` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\i. MEM i.inst_id s2.irs_used_inst_ids) more_assigns` by
    (gvs[listTheory.EVERY_MEM] >> rpt strip_tac >>
     qpat_assum `!i. MEM i more_assigns ==>
                      MEM i.inst_id s1.irs_used_inst_ids`
       (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `!id. MEM id s1.irs_used_inst_ids ==>
                       MEM id s2.irs_used_inst_ids`
       (qspec_then `i.inst_id` irule) >> simp[]) >>
  Cases_on `~sue_needs_assign dfg inst op_idx`
  >- (gvs[sue_expand_ops_supply_def] >>
      Cases_on `h` >>
      gvs[venomInstTheory.operand_vars_def,
          venomInstTheory.operand_var_def]) >>
  Cases_on `h`
  >- (gvs[sue_expand_ops_supply_def, listTheory.EVERY_MEM,
          venomInstTheory.operand_vars_def] >>
      rpt strip_tac >> Cases_on `venomInst$operand_var newop` >>
      gvs[] >> metis_tac[])
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- (gvs[sue_expand_ops_supply_def,
              venomInstTheory.operand_vars_def,
              venomInstTheory.operand_var_def])
      >> gvs[sue_expand_ops_supply_def, listTheory.EVERY_MEM,
             venomInstTheory.operand_vars_def,
             venomInstTheory.operand_var_def] >>
         rpt strip_tac >> Cases_on `venomInst$operand_var newop` >>
         gvs[] >> metis_tac[])
  >> gvs[sue_expand_ops_supply_def,
         venomInstTheory.operand_vars_def,
         venomInstTheory.operand_var_def] >>
  gvs[AllCaseEqs()]
QED


Theorem sue_expand_inst_supply_covered:
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars) (inst_ir_vars inst) /\
  MEM inst.inst_id s.irs_used_inst_ids /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY (\v. MEM v s'.irs_used_vars) (FLAT (MAP inst_ir_vars out)) /\
  EVERY (\i. MEM i.inst_id s'.irs_used_inst_ids) out
Proof
  rpt strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s inst.inst_operands 0 =
           (assigns,new_ops,s1)` >>
  gvs[sue_expand_inst_supply_def] >>
  `sue_supply_extends s s'` by
    metis_tac[sue_expand_ops_supply_extends] >>
  `EVERY (\v. MEM v s.irs_used_vars)
     (venomInst$operand_vars inst.inst_operands)` by
    gvs[inst_ir_vars_def, inst_uses_def, listTheory.EVERY_APPEND] >>
  `EVERY (\v. MEM v s'.irs_used_vars)
      (FLAT (MAP inst_ir_vars assigns) ++
       venomInst$operand_vars new_ops) /\
   EVERY (\i. MEM i.inst_id s'.irs_used_inst_ids) assigns` by
    metis_tac[sue_expand_ops_supply_covered] >>
  `(!v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars) /\
   (!id. MEM id s.irs_used_inst_ids ==> MEM id s'.irs_used_inst_ids)` by
    metis_tac[sue_supply_extends_members] >>
  gvs[inst_ir_vars_def, inst_uses_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED


Theorem sue_expand_insts_supply_covered:
  !dfg s insts outs s'.
    ir_supply_inst_ok s /\
    EVERY (\v. MEM v s.irs_used_vars)
      (FLAT (MAP inst_ir_vars insts)) /\
    EVERY (\i. MEM i.inst_id s.irs_used_inst_ids) insts /\
    sue_expand_insts_supply dfg s insts = (outs,s') ==>
    EVERY (\v. MEM v s'.irs_used_vars) (FLAT (MAP inst_ir_vars outs)) /\
    EVERY (\i. MEM i.inst_id s'.irs_used_inst_ids) outs
Proof
  Induct_on `insts`
  >- simp[sue_expand_insts_supply_def]
  >> rpt strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (tail_out,s2)` >>
  gvs[sue_expand_insts_supply_def, listTheory.EVERY_APPEND] >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `EVERY (\v. MEM v s1.irs_used_vars) (FLAT (MAP inst_ir_vars head_out)) /\
   EVERY (\i. MEM i.inst_id s1.irs_used_inst_ids) head_out` by
    metis_tac[sue_expand_inst_supply_covered] >>
  `(!v. MEM v s.irs_used_vars ==> MEM v s1.irs_used_vars) /\
   (!id. MEM id s.irs_used_inst_ids ==> MEM id s1.irs_used_inst_ids)` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\v. MEM v s1.irs_used_vars)
      (FLAT (MAP inst_ir_vars insts)) /\
   EVERY (\i. MEM i.inst_id s1.irs_used_inst_ids) insts` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\v. MEM v s'.irs_used_vars) (FLAT (MAP inst_ir_vars tail_out)) /\
   EVERY (\i. MEM i.inst_id s'.irs_used_inst_ids) tail_out` by
    metis_tac[] >>
  `sue_supply_extends s1 s'` by
    metis_tac[sue_expand_insts_supply_extends] >>
  `(!v. MEM v s1.irs_used_vars ==> MEM v s'.irs_used_vars) /\
   (!id. MEM id s1.irs_used_inst_ids ==> MEM id s'.irs_used_inst_ids)` by
    metis_tac[sue_supply_extends_members] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED


Theorem sue_expand_block_supply_covered:
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars) (block_ir_vars bb) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (block_ir_inst_ids bb) /\
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  EVERY (\v. MEM v s'.irs_used_vars) (block_ir_vars bb') /\
  EVERY (\id. MEM id s'.irs_used_inst_ids) (block_ir_inst_ids bb')
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def, block_ir_vars_def,
      block_ir_inst_ids_def, listTheory.EVERY_MAP] >>
  metis_tac[sue_expand_insts_supply_covered]
QED

Theorem sue_expand_blocks_supply_covered:
  !dfg s bbs bbs' s'.
    ir_supply_inst_ok s /\
    EVERY (\v. MEM v s.irs_used_vars)
      (FLAT (MAP block_ir_vars bbs)) /\
    EVERY (\id. MEM id s.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs)) /\
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    EVERY (\v. MEM v s'.irs_used_vars)
      (FLAT (MAP block_ir_vars bbs')) /\
    EVERY (\id. MEM id s'.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs'))
Proof
  Induct_on `bbs`
  >- simp[sue_expand_blocks_supply_def]
  >> rpt strip_tac >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  rename1 `sue_expand_block_supply dfg s h = (bb1,s1)` >>
  Cases_on `sue_expand_blocks_supply dfg s1 bbs` >>
  rename1 `sue_expand_blocks_supply dfg s1 bbs = (bbs1,s2)` >>
  gvs[sue_expand_blocks_supply_def, listTheory.EVERY_APPEND] >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_block_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `EVERY (\v. MEM v s1.irs_used_vars) (block_ir_vars bb1) /\
   EVERY (\id. MEM id s1.irs_used_inst_ids) (block_ir_inst_ids bb1)` by
    metis_tac[sue_expand_block_supply_covered] >>
  `(!v. MEM v s.irs_used_vars ==> MEM v s1.irs_used_vars) /\
   (!id. MEM id s.irs_used_inst_ids ==> MEM id s1.irs_used_inst_ids)` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\v. MEM v s1.irs_used_vars) (FLAT (MAP block_ir_vars bbs)) /\
   EVERY (\id. MEM id s1.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs))` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\v. MEM v s'.irs_used_vars)
      (FLAT (MAP block_ir_vars bbs1)) /\
   EVERY (\id. MEM id s'.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs1))` by metis_tac[] >>
  `sue_supply_extends s1 s'` by
    metis_tac[sue_expand_blocks_supply_extends] >>
  `(!v. MEM v s1.irs_used_vars ==> MEM v s'.irs_used_vars) /\
   (!id. MEM id s1.irs_used_inst_ids ==> MEM id s'.irs_used_inst_ids)` by
    metis_tac[sue_supply_extends_members] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED


Theorem sue_expand_function_supply_covered:
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars) (fn_ir_vars fn) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn) /\
  sue_expand_function_supply s fn = (fn',s') ==>
  EVERY (\v. MEM v s'.irs_used_vars) (fn_ir_vars fn') /\
  EVERY (\id. MEM id s'.irs_used_inst_ids) (fn_ir_inst_ids fn')
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, fn_ir_vars_def,
      fn_ir_inst_ids_def] >>
  metis_tac[sue_expand_blocks_supply_covered]
QED

Theorem sue_expand_functions_supply_covered:
  !s fns fns' s'.
    ir_supply_inst_ok s /\
    EVERY (\v. MEM v s.irs_used_vars) (FLAT (MAP fn_ir_vars fns)) /\
    EVERY (\id. MEM id s.irs_used_inst_ids)
      (FLAT (MAP fn_ir_inst_ids fns)) /\
    sue_expand_functions_supply s fns = (fns',s') ==>
    EVERY (\v. MEM v s'.irs_used_vars) (FLAT (MAP fn_ir_vars fns')) /\
    EVERY (\id. MEM id s'.irs_used_inst_ids)
      (FLAT (MAP fn_ir_inst_ids fns'))
Proof
  Induct_on `fns`
  >- simp[sue_expand_functions_supply_def]
  >> rpt strip_tac >>
  Cases_on `sue_expand_function_supply s h` >>
  rename1 `sue_expand_function_supply s h = (fn1,s1)` >>
  Cases_on `sue_expand_functions_supply s1 fns` >>
  rename1 `sue_expand_functions_supply s1 fns = (fns1,s2)` >>
  gvs[sue_expand_functions_supply_def, listTheory.EVERY_APPEND] >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_function_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `EVERY (\v. MEM v s1.irs_used_vars) (fn_ir_vars fn1) /\
   EVERY (\id. MEM id s1.irs_used_inst_ids) (fn_ir_inst_ids fn1)` by
    metis_tac[sue_expand_function_supply_covered] >>
  `(!v. MEM v s.irs_used_vars ==> MEM v s1.irs_used_vars) /\
   (!id. MEM id s.irs_used_inst_ids ==> MEM id s1.irs_used_inst_ids)` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\v. MEM v s1.irs_used_vars) (FLAT (MAP fn_ir_vars fns)) /\
   EVERY (\id. MEM id s1.irs_used_inst_ids)
      (FLAT (MAP fn_ir_inst_ids fns))` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\v. MEM v s'.irs_used_vars) (FLAT (MAP fn_ir_vars fns1)) /\
   EVERY (\id. MEM id s'.irs_used_inst_ids)
      (FLAT (MAP fn_ir_inst_ids fns1))` by metis_tac[] >>
  `sue_supply_extends s1 s'` by
    metis_tac[sue_expand_functions_supply_extends] >>
  `(!v. MEM v s1.irs_used_vars ==> MEM v s'.irs_used_vars) /\
   (!id. MEM id s1.irs_used_inst_ids ==> MEM id s'.irs_used_inst_ids)` by
    metis_tac[sue_supply_extends_members] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_expand_context_supply_covered:
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars)
    (FLAT (MAP fn_ir_vars ctx.ctx_functions)) /\
  EVERY (\id. MEM id s.irs_used_inst_ids)
    (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  sue_expand_context_supply s ctx = (ctx',s') ==>
  EVERY (\v. MEM v s'.irs_used_vars)
    (FLAT (MAP fn_ir_vars ctx'.ctx_functions)) /\
  EVERY (\id. MEM id s'.irs_used_inst_ids)
    (FLAT (MAP fn_ir_inst_ids ctx'.ctx_functions))
Proof
  rpt strip_tac >> Cases_on `sue_expand_functions_supply s ctx.ctx_functions` >>
  gvs[sue_expand_context_supply_def] >>
  metis_tac[sue_expand_functions_supply_covered]
QED

Theorem sue_unit_supply_covered:
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars) (unit_ir_vars unit) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (unit_ir_inst_ids unit) /\
  sue_unit_supply s unit = (unit',s') ==>
  EVERY (\v. MEM v s'.irs_used_vars) (unit_ir_vars unit') /\
  EVERY (\id. MEM id s'.irs_used_inst_ids) (unit_ir_inst_ids unit')
Proof
  rpt strip_tac >> Cases_on `sue_expand_context_supply s unit.cu_context` >>
  gvs[sue_unit_supply_def, unit_ir_vars_def, unit_ir_inst_ids_def] >>
  metis_tac[sue_expand_context_supply_covered]
QED


Theorem sue_configured_with_supply_contract:
  sue_configured_with_supply unit = (unit',s') ==>
  ?new_vars new_ids.
    s'.irs_used_vars = new_vars ++ unit_ir_vars unit /\
    ALL_DISTINCT new_vars /\
    EVERY (\v. ~MEM v (unit_ir_vars unit)) new_vars /\
    s'.irs_used_inst_ids = new_ids ++ unit_ir_inst_ids unit /\
    ALL_DISTINCT new_ids /\
    EVERY (\id. ~MEM id (unit_ir_inst_ids unit)) new_ids /\
    EVERY (\v. MEM v s'.irs_used_vars) (unit_ir_vars unit') /\
    EVERY (\id. MEM id s'.irs_used_inst_ids) (unit_ir_inst_ids unit')
Proof
  strip_tac >>
  `sue_unit_supply (init_ir_supply unit) unit = (unit',s')` by
    gvs[sue_configured_with_supply_def] >>
  `sue_supply_extends (init_ir_supply unit) s'` by
    metis_tac[sue_unit_supply_extends, init_ir_supply_inst_ok] >>
  `EVERY (\v. MEM v (init_ir_supply unit).irs_used_vars)
      (unit_ir_vars unit)` by
    simp[init_ir_supply_fields, listTheory.EVERY_MEM] >>
  `EVERY (\id. MEM id (init_ir_supply unit).irs_used_inst_ids)
      (unit_ir_inst_ids unit)` by
    simp[init_ir_supply_fields, listTheory.EVERY_MEM] >>
  `EVERY (\v. MEM v s'.irs_used_vars) (unit_ir_vars unit') /\
   EVERY (\id. MEM id s'.irs_used_inst_ids) (unit_ir_inst_ids unit')` by
    metis_tac[sue_unit_supply_covered, init_ir_supply_inst_ok] >>
  gvs[sue_supply_extends_def, init_ir_supply_fields] >>
  metis_tac[]
QED

Theorem sue_configured_used_vars_all_distinct:
  ALL_DISTINCT (unit_ir_vars unit) /\
  sue_configured_with_supply unit = (unit',s') ==>
  ALL_DISTINCT s'.irs_used_vars
Proof
  rpt strip_tac >>
  `sue_unit_supply (init_ir_supply unit) unit = (unit',s')` by
    gvs[sue_configured_with_supply_def] >>
  `sue_supply_extends (init_ir_supply unit) s'` by
    metis_tac[sue_unit_supply_extends, init_ir_supply_inst_ok] >>
  gvs[sue_supply_extends_def, init_ir_supply_fields,
      listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM]
QED

Theorem sue_configured_used_inst_ids_all_distinct:
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  sue_configured_with_supply unit = (unit',s') ==>
  ALL_DISTINCT s'.irs_used_inst_ids
Proof
  rpt strip_tac >>
  `sue_unit_supply (init_ir_supply unit) unit = (unit',s')` by
    gvs[sue_configured_with_supply_def] >>
  `sue_supply_extends (init_ir_supply unit) s'` by
    metis_tac[sue_unit_supply_extends, init_ir_supply_inst_ok] >>
  gvs[sue_supply_extends_def, init_ir_supply_fields,
      listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM]
QED


Definition sue_ids_supply_ok_def:
  sue_ids_supply_ok s old_ids new_ids s' <=>
    sue_supply_extends s s' /\
    ALL_DISTINCT new_ids /\
    EVERY (\id. MEM id s'.irs_used_inst_ids) new_ids /\
    (!id. MEM id new_ids /\ MEM id s.irs_used_inst_ids ==>
          MEM id old_ids)
End

Theorem sue_ids_supply_ok_append:
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT (old1 ++ old2) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (old1 ++ old2) /\
  sue_ids_supply_ok s old1 new1 s1 /\
  sue_ids_supply_ok s1 old2 new2 s2 ==>
  sue_ids_supply_ok s (old1 ++ old2) (new1 ++ new2) s2
Proof
  rpt strip_tac >>
  qpat_x_assum `sue_ids_supply_ok s old1 new1 s1` mp_tac >>
  simp[sue_ids_supply_ok_def] >> strip_tac >>
  qpat_x_assum `sue_ids_supply_ok s1 old2 new2 s2` mp_tac >>
  simp[sue_ids_supply_ok_def] >> strip_tac >>
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
     gvs[listTheory.ALL_DISTINCT_APPEND] >> metis_tac[]) >>
  `EVERY (\id. MEM id s2.irs_used_inst_ids) new1` by
    (gvs[listTheory.EVERY_MEM] >>
     metis_tac[sue_supply_extends_members]) >>
  gvs[sue_ids_supply_ok_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_MEM] >>
  metis_tac[sue_supply_extends_trans, sue_supply_extends_members]
QED


Theorem sue_ids_supply_ok_nil_append:
  sue_ids_supply_ok s [] new1 s1 /\
  sue_ids_supply_ok s1 [] new2 s2 ==>
  sue_ids_supply_ok s [] (new1 ++ new2) s2
Proof
  rpt strip_tac >>
  gvs[sue_ids_supply_ok_def] >>
  `!id. MEM id new1 ==> ~MEM id new2` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\id. MEM id s2.irs_used_inst_ids) new1` by
    (gvs[listTheory.EVERY_MEM] >>
     metis_tac[sue_supply_extends_members]) >>
  gvs[sue_ids_supply_ok_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_MEM] >>
  metis_tac[sue_supply_extends_trans, sue_supply_extends_members]
QED

Theorem sue_alloc_assign_supply_ids_ok:
  ir_supply_inst_ok s /\
  sue_alloc_assign_supply s op = (a,newop,s') ==>
  sue_ids_supply_ok s [] [a.inst_id] s'
Proof
  rpt strip_tac >>
  drule_all sue_alloc_assign_supply_contract >> strip_tac >>
  `sue_supply_extends s s'` by
    metis_tac[sue_alloc_assign_supply_extends] >>
  gvs[sue_ids_supply_ok_def]
QED


Theorem sue_ids_supply_ok_nil_rev_append:
  sue_ids_supply_ok s [] new1 s1 /\
  sue_ids_supply_ok s1 [] new2 s2 ==>
  sue_ids_supply_ok s [] (new2 ++ new1) s2
Proof
  rpt strip_tac >>
  gvs[sue_ids_supply_ok_def] >>
  `!id. MEM id new1 ==> ~MEM id new2` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\id. MEM id s2.irs_used_inst_ids) new1` by
    (gvs[listTheory.EVERY_MEM] >>
     metis_tac[sue_supply_extends_members]) >>
  gvs[sue_ids_supply_ok_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_MEM] >>
  metis_tac[sue_supply_extends_trans, sue_supply_extends_members]
QED

Theorem sue_expand_ops_supply_ids_ok:
  !dfg inst s ops op_idx assigns new_ops s'.
    ir_supply_inst_ok s /\
    sue_expand_ops_supply dfg inst s ops op_idx = (assigns,new_ops,s') ==>
    sue_ids_supply_ok s [] (MAP (\i. i.inst_id) assigns) s'
Proof
  Induct_on `ops` >> rpt strip_tac
  >- gvs[sue_expand_ops_supply_def, sue_ids_supply_ok_def,
          sue_supply_extends_refl] >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (op_idx + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (op_idx + 1) =
           (more_assigns,more_ops,s1)` >>
  `sue_ids_supply_ok s [] (MAP (\i. i.inst_id) more_assigns) s1` by
    metis_tac[] >>
  `ir_supply_inst_ok s1` by
    gvs[sue_ids_supply_ok_def, sue_supply_extends_def] >>
  Cases_on `~sue_needs_assign dfg inst op_idx`
  >- gvs[sue_expand_ops_supply_def] >>
  Cases_on `h`
  >- (Cases_on `sue_alloc_assign_supply s1 (Lit c)` >>
      PairCases_on `r` >>
      gvs[sue_expand_ops_supply_def] >>
      `sue_ids_supply_ok s1 [] [q.inst_id] r1` by
        metis_tac[sue_alloc_assign_supply_ids_ok] >>
      drule_all sue_ids_supply_ok_nil_rev_append >> simp[])
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- gvs[sue_expand_ops_supply_def]
      >> Cases_on `sue_alloc_assign_supply s1 (Var s'')` >>
         PairCases_on `r` >>
         gvs[sue_expand_ops_supply_def] >>
         `sue_ids_supply_ok s1 [] [q.inst_id] r1` by
           metis_tac[sue_alloc_assign_supply_ids_ok] >>
         drule_all sue_ids_supply_ok_nil_rev_append >> simp[])
  >> gvs[sue_expand_ops_supply_def]
QED


Theorem sue_expand_inst_supply_ids_ok:
  ir_supply_inst_ok s /\
  MEM inst.inst_id s.irs_used_inst_ids /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  sue_ids_supply_ok s [inst.inst_id] (MAP (\i. i.inst_id) out) s'
Proof
  rpt strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def, sue_ids_supply_ok_def,
          sue_supply_extends_refl] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s inst.inst_operands 0 =
           (assigns,new_ops,s1)` >>
  gvs[sue_expand_inst_supply_def] >>
  `sue_ids_supply_ok s [] (MAP (\i. i.inst_id) assigns) s'` by
    metis_tac[sue_expand_ops_supply_ids_ok] >>
  gvs[sue_ids_supply_ok_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_MEM] >>
  metis_tac[sue_supply_extends_members]
QED
