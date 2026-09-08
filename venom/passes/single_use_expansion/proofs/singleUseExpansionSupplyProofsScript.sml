(*
 * Supply freshness and structural contracts for configured SUE.
 *)

Theory singleUseExpansionSupplyProofs
Ancestors
  singleUseExpansionDefs irSupply venomInst fcgDefs

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
      FIRST_PROVE
        [qpat_x_assum `MEM v (inst_ir_vars a)` mp_tac >>
         qpat_assum `!x. MEM x (inst_ir_vars a) ==> MEM x _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[],
         qpat_x_assum `MEM v _` mp_tac >>
         qpat_assum
           `!x. MEM x (case _ of NONE => [] | SOME y => [y]) ==> MEM x _`
           mp_tac >>
         qpat_assum
           `!x. MEM x (venomInst$operand_vars more_ops) ==> MEM x _`
           mp_tac >>
         qpat_assum
           `!x. MEM x (FLAT (MAP inst_ir_vars more_assigns)) ==> MEM x _`
           mp_tac >>
         qpat_assum `!x. MEM x s1.irs_used_vars ==> MEM x _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]])
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


Theorem sue_expand_insts_supply_ids_ok:
  !dfg s insts outs s'.
    ir_supply_inst_ok s /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    EVERY (\i. MEM i.inst_id s.irs_used_inst_ids) insts /\
    sue_expand_insts_supply dfg s insts = (outs,s') ==>
    sue_ids_supply_ok s (MAP (\i. i.inst_id) insts)
      (MAP (\i. i.inst_id) outs) s'
Proof
  Induct_on `insts`
  >- simp[sue_expand_insts_supply_def, sue_ids_supply_ok_def,
          sue_supply_extends_refl] >>
  rpt strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (tail_out,s2)` >>
  gvs[sue_expand_insts_supply_def] >>
  `sue_ids_supply_ok s [h.inst_id]
      (MAP (\i. i.inst_id) head_out) s1` by
    metis_tac[sue_expand_inst_supply_ids_ok] >>
  `sue_supply_extends s s1` by gvs[sue_ids_supply_ok_def] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `EVERY (\i. MEM i.inst_id s1.irs_used_inst_ids) insts` by
    (gvs[listTheory.EVERY_MEM] >>
     metis_tac[sue_supply_extends_members]) >>
  `sue_ids_supply_ok s1 (MAP (\i. i.inst_id) insts)
      (MAP (\i. i.inst_id) tail_out) s'` by metis_tac[] >>
  `ALL_DISTINCT ([h.inst_id] ++ MAP (\i. i.inst_id) insts)` by simp[] >>
  `EVERY (\id. MEM id s.irs_used_inst_ids)
      ([h.inst_id] ++ MAP (\i. i.inst_id) insts)` by
    gvs[listTheory.EVERY_MAP] >>
  drule_all sue_ids_supply_ok_append >> simp[]
QED


Theorem sue_expand_block_supply_ids_ok:
  ir_supply_inst_ok s /\
  ALL_DISTINCT (block_ir_inst_ids bb) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (block_ir_inst_ids bb) /\
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  sue_ids_supply_ok s (block_ir_inst_ids bb) (block_ir_inst_ids bb') s'
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def, block_ir_inst_ids_def,
      listTheory.EVERY_MAP] >>
  metis_tac[sue_expand_insts_supply_ids_ok]
QED

Theorem sue_expand_blocks_supply_ids_ok:
  !dfg s bbs bbs' s'.
    ir_supply_inst_ok s /\
    ALL_DISTINCT (FLAT (MAP block_ir_inst_ids bbs)) /\
    EVERY (\id. MEM id s.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs)) /\
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    sue_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
      (FLAT (MAP block_ir_inst_ids bbs')) s'
Proof
  Induct_on `bbs`
  >- simp[sue_expand_blocks_supply_def, sue_ids_supply_ok_def,
          sue_supply_extends_refl] >>
  rpt strip_tac >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  rename1 `sue_expand_block_supply dfg s h = (bb1,s1)` >>
  Cases_on `sue_expand_blocks_supply dfg s1 bbs` >>
  rename1 `sue_expand_blocks_supply dfg s1 bbs = (bbs1,s2)` >>
  gvs[sue_expand_blocks_supply_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_APPEND] >>
  `sue_ids_supply_ok s (block_ir_inst_ids h)
      (block_ir_inst_ids bb1) s1` by
    metis_tac[sue_expand_block_supply_ids_ok] >>
  `sue_supply_extends s s1` by gvs[sue_ids_supply_ok_def] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `EVERY (\id. MEM id s1.irs_used_inst_ids)
      (FLAT (MAP block_ir_inst_ids bbs))` by
    (gvs[listTheory.EVERY_MEM] >>
     metis_tac[sue_supply_extends_members]) >>
  `sue_ids_supply_ok s1 (FLAT (MAP block_ir_inst_ids bbs))
      (FLAT (MAP block_ir_inst_ids bbs1)) s'` by metis_tac[] >>
  `ALL_DISTINCT
      (block_ir_inst_ids h ++ FLAT (MAP block_ir_inst_ids bbs))` by
    simp[listTheory.ALL_DISTINCT_APPEND] >>
  `EVERY (\id. MEM id s.irs_used_inst_ids)
      (block_ir_inst_ids h ++ FLAT (MAP block_ir_inst_ids bbs))` by
    simp[listTheory.EVERY_APPEND] >>
  drule_all sue_ids_supply_ok_append >> simp[]
QED


Theorem sue_expand_function_supply_ids_ok:
  ir_supply_inst_ok s /\
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn) /\
  sue_expand_function_supply s fn = (fn',s') ==>
  sue_ids_supply_ok s (fn_ir_inst_ids fn) (fn_ir_inst_ids fn') s'
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, fn_ir_inst_ids_def] >>
  metis_tac[sue_expand_blocks_supply_ids_ok]
QED

Theorem sue_expand_functions_supply_ids_ok:
  !s fns fns' s'.
    ir_supply_inst_ok s /\
    ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns)) /\
    EVERY (\id. MEM id s.irs_used_inst_ids)
      (FLAT (MAP fn_ir_inst_ids fns)) /\
    sue_expand_functions_supply s fns = (fns',s') ==>
    sue_ids_supply_ok s (FLAT (MAP fn_ir_inst_ids fns))
      (FLAT (MAP fn_ir_inst_ids fns')) s'
Proof
  Induct_on `fns`
  >- simp[sue_expand_functions_supply_def, sue_ids_supply_ok_def,
          sue_supply_extends_refl] >>
  rpt strip_tac >>
  Cases_on `sue_expand_function_supply s h` >>
  rename1 `sue_expand_function_supply s h = (fn1,s1)` >>
  Cases_on `sue_expand_functions_supply s1 fns` >>
  rename1 `sue_expand_functions_supply s1 fns = (fns1,s2)` >>
  gvs[sue_expand_functions_supply_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_APPEND] >>
  `sue_ids_supply_ok s (fn_ir_inst_ids h) (fn_ir_inst_ids fn1) s1` by
    metis_tac[sue_expand_function_supply_ids_ok] >>
  `sue_supply_extends s s1` by gvs[sue_ids_supply_ok_def] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `EVERY (\id. MEM id s1.irs_used_inst_ids)
      (FLAT (MAP fn_ir_inst_ids fns))` by
    (gvs[listTheory.EVERY_MEM] >>
     metis_tac[sue_supply_extends_members]) >>
  `sue_ids_supply_ok s1 (FLAT (MAP fn_ir_inst_ids fns))
      (FLAT (MAP fn_ir_inst_ids fns1)) s'` by metis_tac[] >>
  `ALL_DISTINCT (fn_ir_inst_ids h ++ FLAT (MAP fn_ir_inst_ids fns))` by
    simp[listTheory.ALL_DISTINCT_APPEND] >>
  `EVERY (\id. MEM id s.irs_used_inst_ids)
      (fn_ir_inst_ids h ++ FLAT (MAP fn_ir_inst_ids fns))` by
    simp[listTheory.EVERY_APPEND] >>
  drule_all sue_ids_supply_ok_append >> simp[]
QED

Theorem sue_expand_context_supply_ids_ok:
  ir_supply_inst_ok s /\
  ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  EVERY (\id. MEM id s.irs_used_inst_ids)
    (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  sue_expand_context_supply s ctx = (ctx',s') ==>
  sue_ids_supply_ok s (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions))
    (FLAT (MAP fn_ir_inst_ids ctx'.ctx_functions)) s'
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_functions_supply s ctx.ctx_functions` >>
  gvs[sue_expand_context_supply_def] >>
  metis_tac[sue_expand_functions_supply_ids_ok]
QED

Theorem sue_unit_supply_ids_ok:
  ir_supply_inst_ok s /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (unit_ir_inst_ids unit) /\
  sue_unit_supply s unit = (unit',s') ==>
  sue_ids_supply_ok s (unit_ir_inst_ids unit)
    (unit_ir_inst_ids unit') s'
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_context_supply s unit.cu_context` >>
  gvs[sue_unit_supply_def, unit_ir_inst_ids_def] >>
  metis_tac[sue_expand_context_supply_ids_ok]
QED


Theorem sue_configured_inst_ids_all_distinct:
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  sue_configured_with_supply unit = (unit',s') ==>
  ALL_DISTINCT (unit_ir_inst_ids unit')
Proof
  rpt strip_tac >>
  `sue_unit_supply (init_ir_supply unit) unit = (unit',s')` by
    gvs[sue_configured_with_supply_def] >>
  `sue_ids_supply_ok (init_ir_supply unit) (unit_ir_inst_ids unit)
      (unit_ir_inst_ids unit') s'` by
    (irule sue_unit_supply_ids_ok >>
     gvs[init_ir_supply_inst_ok, init_ir_supply_fields,
         listTheory.EVERY_MEM]) >>
  gvs[sue_ids_supply_ok_def]
QED


(* ===== Structural preservation for the configured adapter ===== *)

Definition sue_operand_label_def:
  sue_operand_label op =
    case op of Label l => SOME l | _ => NONE
End

Definition sue_fn_invoke_labels_def:
  sue_fn_invoke_labels fn =
    FLAT (MAP (\bb. MAP FST (get_invoke_targets bb.bb_instructions))
              fn.fn_blocks)
End

Theorem sue_alloc_assign_supply_shape:
  sue_alloc_assign_supply s op = (a,newop,s') ==>
  a.inst_opcode = ASSIGN /\ sue_operand_label newop = NONE
Proof
  Cases_on `fresh_ir_var s` >>
  Cases_on `fresh_inst_id r` >>
  rpt strip_tac >>
  gvs[sue_alloc_assign_supply_def, sue_operand_label_def]
QED
Theorem sue_get_invoke_targets_cons:
  MAP FST (get_invoke_targets (inst::insts)) =
  MAP FST (get_invoke_targets [inst]) ++
  MAP FST (get_invoke_targets insts)
Proof
  simp[get_invoke_targets_def] >> rpt CASE_TAC >> gvs[]
QED

Theorem sue_get_invoke_targets_append:
  MAP FST (get_invoke_targets (xs ++ ys)) =
  MAP FST (get_invoke_targets xs) ++ MAP FST (get_invoke_targets ys)
Proof
  Induct_on `xs` >- simp[get_invoke_targets_def] >>
  rpt gen_tac >> pure_once_rewrite_tac[listTheory.APPEND] >>
  once_rewrite_tac[sue_get_invoke_targets_cons] >> simp[]
QED

Theorem sue_expand_ops_supply_operand_labels:
  !dfg inst s ops k assigns new_ops s'.
    sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
    MAP sue_operand_label new_ops = MAP sue_operand_label ops
Proof
  Induct_on `ops`
  >- (rpt strip_tac >> gvs[sue_expand_ops_supply_def]) >>
  rpt strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (k + 1) =
           (more_assigns,more_ops,s1)` >>
  `MAP sue_operand_label more_ops = MAP sue_operand_label ops` by
    metis_tac[] >>
  Cases_on `~sue_needs_assign dfg inst k`
  >- gvs[sue_expand_ops_supply_def] >>
  Cases_on `h`
  >- (Cases_on `fresh_ir_var s1` >> Cases_on `fresh_inst_id r` >>
      gvs[sue_expand_ops_supply_def, sue_alloc_assign_supply_def,
          sue_operand_label_def])
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- gvs[sue_expand_ops_supply_def, sue_operand_label_def]
      >> Cases_on `fresh_ir_var s1` >> Cases_on `fresh_inst_id r` >>
         gvs[sue_expand_ops_supply_def, sue_alloc_assign_supply_def,
             sue_operand_label_def])
  >> gvs[sue_expand_ops_supply_def, sue_operand_label_def]
QED

Theorem sue_expand_ops_supply_assigns_no_invokes:
  !dfg inst s ops k assigns new_ops s'.
    sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
    get_invoke_targets assigns = []
Proof
  Induct_on `ops`
  >- (rpt strip_tac >> gvs[sue_expand_ops_supply_def,
                            get_invoke_targets_def]) >>
  rpt strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (k + 1) =
           (more_assigns,more_ops,s1)` >>
  `get_invoke_targets more_assigns = []` by metis_tac[] >>
  Cases_on `~sue_needs_assign dfg inst k`
  >- gvs[sue_expand_ops_supply_def] >>
  Cases_on `h`
  >- (Cases_on `fresh_ir_var s1` >> Cases_on `fresh_inst_id r` >>
      gvs[sue_expand_ops_supply_def, sue_alloc_assign_supply_def,
          get_invoke_targets_def])
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- gvs[sue_expand_ops_supply_def]
      >> Cases_on `fresh_ir_var s1` >> Cases_on `fresh_inst_id r` >>
         gvs[sue_expand_ops_supply_def, sue_alloc_assign_supply_def,
             get_invoke_targets_def])
  >> gvs[sue_expand_ops_supply_def]
QED

Theorem sue_expand_inst_supply_invoke_labels:
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  MAP FST (get_invoke_targets out) =
  MAP FST (get_invoke_targets [inst])
Proof
  rpt strip_tac >>
  Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s inst.inst_operands 0 =
           (assigns,new_ops,s1)` >>
  gvs[sue_expand_inst_supply_def] >>
  `get_invoke_targets assigns = []` by
    metis_tac[sue_expand_ops_supply_assigns_no_invokes] >>
  `MAP sue_operand_label new_ops =
   MAP sue_operand_label inst.inst_operands` by
    metis_tac[sue_expand_ops_supply_operand_labels] >>
  rewrite_tac[sue_get_invoke_targets_append] >> simp[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `inst.inst_operands` >> Cases_on `new_ops` >>
      gvs[get_invoke_targets_def, sue_operand_label_def] >>
      Cases_on `h` >> gvs[sue_operand_label_def] >>
      rpt CASE_TAC >> gvs[get_invoke_targets_def, sue_operand_label_def])
  >> gvs[get_invoke_targets_def]
QED

Theorem sue_expand_insts_supply_invoke_labels:
  !dfg s insts out s'.
    sue_expand_insts_supply dfg s insts = (out,s') ==>
    MAP FST (get_invoke_targets out) =
    MAP FST (get_invoke_targets insts)
Proof
  Induct_on `insts`
  >- simp[sue_expand_insts_supply_def, get_invoke_targets_def] >>
  rpt strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (tail_out,s2)` >>
  gvs[sue_expand_insts_supply_def] >>
  `MAP FST (get_invoke_targets head_out) =
   MAP FST (get_invoke_targets [h])` by
    metis_tac[sue_expand_inst_supply_invoke_labels] >>
  `MAP FST (get_invoke_targets tail_out) =
   MAP FST (get_invoke_targets insts)` by metis_tac[] >>
  once_rewrite_tac[sue_get_invoke_targets_append] >>
  once_rewrite_tac[sue_get_invoke_targets_cons] >> simp[]
QED

Theorem sue_expand_block_supply_invoke_labels:
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  MAP FST (get_invoke_targets bb'.bb_instructions) =
  MAP FST (get_invoke_targets bb.bb_instructions)
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  metis_tac[sue_expand_insts_supply_invoke_labels]
QED

Theorem sue_expand_blocks_supply_invoke_labels:
  !dfg s bbs bbs' s'.
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    MAP (\bb. MAP FST (get_invoke_targets bb.bb_instructions)) bbs' =
    MAP (\bb. MAP FST (get_invoke_targets bb.bb_instructions)) bbs
Proof
  Induct_on `bbs`
  >- simp[sue_expand_blocks_supply_def] >>
  rpt strip_tac >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  rename1 `sue_expand_block_supply dfg s h = (bb1,s1)` >>
  Cases_on `sue_expand_blocks_supply dfg s1 bbs` >>
  rename1 `sue_expand_blocks_supply dfg s1 bbs = (bbs1,s2)` >>
  gvs[sue_expand_blocks_supply_def] >>
  `MAP FST (get_invoke_targets bb1.bb_instructions) =
   MAP FST (get_invoke_targets h.bb_instructions)` by
    metis_tac[sue_expand_block_supply_invoke_labels] >>
  `MAP (\bb. MAP FST (get_invoke_targets bb.bb_instructions)) bbs1 =
   MAP (\bb. MAP FST (get_invoke_targets bb.bb_instructions)) bbs` by
    metis_tac[] >>
  simp[]
QED

Theorem sue_expand_function_supply_structural:
  sue_expand_function_supply s fn = (fn',s') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn /\
  fn_fmp_convention_eq fn' fn /\
  sue_fn_invoke_labels fn' = sue_fn_invoke_labels fn
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  `MAP (\bb. MAP FST (get_invoke_targets bb.bb_instructions)) q =
   MAP (\bb. MAP FST (get_invoke_targets bb.bb_instructions)) fn.fn_blocks` by
    metis_tac[sue_expand_blocks_supply_invoke_labels] >>
  gvs[fn_identity_metadata_eq_def, fn_static_input_eq_def,
      fn_static_layout_eq_def, fn_fmp_convention_eq_def,
      sue_fn_invoke_labels_def]
QED

Theorem sue_expand_functions_supply_structural:
  !s fns fns' s'.
    sue_expand_functions_supply s fns = (fns',s') ==>
    LIST_REL
      (\fn' fn.
         fn_identity_metadata_eq fn' fn /\
         fn_static_input_eq fn' fn /\
         fn_static_layout_eq fn' fn /\
         fn_fmp_convention_eq fn' fn) fns' fns /\
    MAP sue_fn_invoke_labels fns' = MAP sue_fn_invoke_labels fns
Proof
  Induct_on `fns`
  >- simp[sue_expand_functions_supply_def] >>
  rpt strip_tac >>
  Cases_on `sue_expand_function_supply s h` >>
  rename1 `sue_expand_function_supply s h = (fn1,s1)` >>
  Cases_on `sue_expand_functions_supply s1 fns` >>
  rename1 `sue_expand_functions_supply s1 fns = (fns1,s2)` >>
  gvs[sue_expand_functions_supply_def] >>
  `fn_identity_metadata_eq fn1 h /\
   fn_static_input_eq fn1 h /\
   fn_static_layout_eq fn1 h /\
   fn_fmp_convention_eq fn1 h /\
   sue_fn_invoke_labels fn1 = sue_fn_invoke_labels h` by
    metis_tac[sue_expand_function_supply_structural] >>
  `LIST_REL
      (\fn' fn.
         fn_identity_metadata_eq fn' fn /\
         fn_static_input_eq fn' fn /\
         fn_static_layout_eq fn' fn /\
         fn_fmp_convention_eq fn' fn) fns1 fns /\
   MAP sue_fn_invoke_labels fns1 = MAP sue_fn_invoke_labels fns` by
    metis_tac[] >>
  simp[]
QED

Theorem sue_configured_structural:
  sue_configured_with_supply unit = (unit',s') ==>
  LIST_REL
    (\fn' fn.
       fn_identity_metadata_eq fn' fn /\
       fn_static_input_eq fn' fn /\
       fn_static_layout_eq fn' fn /\
       fn_fmp_convention_eq fn' fn)
    unit'.cu_context.ctx_functions unit.cu_context.ctx_functions /\
  MAP sue_fn_invoke_labels unit'.cu_context.ctx_functions =
  MAP sue_fn_invoke_labels unit.cu_context.ctx_functions
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_functions_supply (init_ir_supply unit)
              unit.cu_context.ctx_functions` >>
  gvs[sue_configured_with_supply_def, sue_unit_supply_def,
      sue_expand_context_supply_def] >>
  metis_tac[sue_expand_functions_supply_structural]
QED


(* Raw FMP opcode preservation for the supply-aware implementation. *)
Theorem sue_expand_ops_supply_assign_opcodes[local]:
  !dfg inst s ops k assigns new_ops s'.
    sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
    EVERY (\a. a.inst_opcode = ASSIGN) assigns
Proof
  Induct_on `ops`
  >- (rpt strip_tac >> gvs[sue_expand_ops_supply_def]) >>
  rpt strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (k + 1) =
           (more_assigns,more_ops,s1)` >>
  `EVERY (\a. a.inst_opcode = ASSIGN) more_assigns` by metis_tac[] >>
  Cases_on `~sue_needs_assign dfg inst k`
  >- gvs[sue_expand_ops_supply_def] >>
  Cases_on `h`
  >- (Cases_on `fresh_ir_var s1` >> Cases_on `fresh_inst_id r` >>
      gvs[sue_expand_ops_supply_def, sue_alloc_assign_supply_def])
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- gvs[sue_expand_ops_supply_def]
      >> Cases_on `fresh_ir_var s1` >> Cases_on `fresh_inst_id r` >>
         gvs[sue_expand_ops_supply_def, sue_alloc_assign_supply_def])
  >> gvs[sue_expand_ops_supply_def]
QED

Theorem sue_expand_inst_supply_no_raw[local]:
  ~is_raw_fmp_opcode inst.inst_opcode /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  rpt strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s inst.inst_operands 0 =
           (assigns,new_ops,s1)` >>
  gvs[sue_expand_inst_supply_def, listTheory.EVERY_APPEND] >>
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    metis_tac[sue_expand_ops_supply_assign_opcodes] >>
  gvs[listTheory.EVERY_MEM, is_raw_fmp_opcode_def]
QED

Theorem sue_expand_insts_supply_no_raw[local]:
  !dfg s insts out s'.
    EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) insts /\
    sue_expand_insts_supply dfg s insts = (out,s') ==>
    EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  Induct_on `insts`
  >- simp[sue_expand_insts_supply_def] >>
  rpt strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (tail_out,s2)` >>
  gvs[sue_expand_insts_supply_def, listTheory.EVERY_APPEND] >>
  metis_tac[sue_expand_inst_supply_no_raw]
QED

Theorem sue_expand_block_supply_no_raw[local]:
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) bb.bb_instructions /\
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) bb'.bb_instructions
Proof
  rpt strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  metis_tac[sue_expand_insts_supply_no_raw]
QED

Theorem sue_expand_blocks_supply_no_raw[local]:
  !dfg s bbs bbs' s'.
    EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                      bb.bb_instructions) bbs /\
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                      bb.bb_instructions) bbs'
Proof
  Induct_on `bbs`
  >- simp[sue_expand_blocks_supply_def] >>
  rpt strip_tac >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  rename1 `sue_expand_block_supply dfg s h = (bb1,s1)` >>
  Cases_on `sue_expand_blocks_supply dfg s1 bbs` >>
  rename1 `sue_expand_blocks_supply dfg s1 bbs = (bbs1,s2)` >>
  gvs[sue_expand_blocks_supply_def] >>
  metis_tac[sue_expand_block_supply_no_raw]
QED

Theorem sue_blocks_no_raw_iff[local]:
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                    bb.bb_instructions) bbs <=>
  !inst. MEM inst (fn_insts_blocks bbs) ==>
         ~is_raw_fmp_opcode inst.inst_opcode
Proof
  Induct_on `bbs` >>
  simp[fn_insts_blocks_def, listTheory.EVERY_MEM,
       listTheory.MEM_APPEND, DISJ_IMP_THM, FORALL_AND_THM]
QED

Theorem sue_expand_function_supply_no_raw_fmp_ops:
  no_raw_fmp_ops fn ==>
  no_raw_fmp_ops (FST (sue_expand_function_supply s fn))
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  rename1 `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks =
           (bbs,s')` >>
  `EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) fn.fn_blocks` by
    (simp[sue_blocks_no_raw_iff, GSYM fn_insts_def,
          GSYM no_raw_fmp_ops_def]) >>
  `EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) bbs` by
    metis_tac[sue_expand_blocks_supply_no_raw] >>
  gvs[sue_expand_function_supply_def, no_raw_fmp_ops_def,
      fn_insts_def, GSYM sue_blocks_no_raw_iff]
QED

val _ = export_theory();
