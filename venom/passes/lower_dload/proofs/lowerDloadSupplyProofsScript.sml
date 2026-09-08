(* Supply-aware lower-DLOAD contracts. *)
Theory lowerDloadSupplyProofs
Ancestors
  lowerDloadDefs irSupply venomInst fcgDefs

(* A supply extension preserves every reservation and preserves distinctness.
   Consequently the final-list delta is a pairwise-fresh set of generated
   resources, disjoint from every reservation in the initial supply. *)
Definition ld_supply_extends_def:
  ld_supply_extends s s' <=>
    ir_supply_inst_ok s' /\
    (!id. MEM id s.irs_used_inst_ids ==> MEM id s'.irs_used_inst_ids) /\
    (!v. MEM v s.irs_used_vars ==> MEM v s'.irs_used_vars) /\
    (ALL_DISTINCT s.irs_used_inst_ids ==>
       ALL_DISTINCT s'.irs_used_inst_ids) /\
    (ALL_DISTINCT s.irs_used_vars ==> ALL_DISTINCT s'.irs_used_vars)
End

Theorem ld_supply_extends_refl:
  ir_supply_inst_ok s ==> ld_supply_extends s s
Proof
  simp[ld_supply_extends_def]
QED

Theorem ld_supply_extends_trans:
  ld_supply_extends s s1 /\ ld_supply_extends s1 s2 ==>
  ld_supply_extends s s2
Proof
  simp[ld_supply_extends_def] >> metis_tac[]
QED

Theorem fresh_inst_id_extends:
  ir_supply_inst_ok s /\ fresh_inst_id s = (id,s') ==>
  ld_supply_extends s s'
Proof
  strip_tac >> drule_all fresh_inst_id_contract >>
  simp[ld_supply_extends_def] >> metis_tac[]
QED

Theorem fresh_ir_var_extends:
  ir_supply_inst_ok s /\ fresh_ir_var s = (v,s') ==>
  ld_supply_extends s s'
Proof
  strip_tac >> drule fresh_ir_var_contract >> strip_tac >>
  gvs[ld_supply_extends_def, ir_supply_inst_ok_def]
QED

Definition ld_inst_supply_ok_def:
  ld_inst_supply_ok s inst outs s' <=>
    ld_supply_extends s s' /\
    ALL_DISTINCT (MAP (\i. i.inst_id) outs) /\
    EVERY (\i. MEM i.inst_id s'.irs_used_inst_ids) outs /\
    (!id. MEM id (MAP (\i. i.inst_id) outs) /\
          MEM id s.irs_used_inst_ids ==> id = inst.inst_id)
End

Definition ld_insts_supply_ok_def:
  ld_insts_supply_ok s insts outs s' <=>
    ld_supply_extends s s' /\
    ALL_DISTINCT (MAP (\i. i.inst_id) outs) /\
    EVERY (\i. MEM i.inst_id s'.irs_used_inst_ids) outs /\
    (!id. MEM id (MAP (\i. i.inst_id) outs) /\
          MEM id s.irs_used_inst_ids ==>
          MEM id (MAP (\i. i.inst_id) insts))
End


Definition ld_ids_supply_ok_def:
  ld_ids_supply_ok s old_ids new_ids s' <=>
    ld_supply_extends s s' /\
    ALL_DISTINCT new_ids /\
    EVERY (\id. MEM id s'.irs_used_inst_ids) new_ids /\
    (!id. MEM id new_ids /\ MEM id s.irs_used_inst_ids ==>
          MEM id old_ids)
End

Theorem ld_insts_supply_ok_ids:
  ld_insts_supply_ok s insts outs s' <=>
  ld_ids_supply_ok s
    (MAP (\i. i.inst_id) insts) (MAP (\i. i.inst_id) outs) s'
Proof
  simp[ld_insts_supply_ok_def, ld_ids_supply_ok_def,
       listTheory.EVERY_MAP]
QED
Theorem lower_dload_inst_supply_shaped_dload:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  MEM inst.inst_id s.irs_used_inst_ids /\
  inst.inst_opcode = DLOAD /\
  inst.inst_operands = [ptr] /\
  inst.inst_outputs = [outv] /\
  lower_dload_inst_supply s inst = (outs,s') ==>
  ld_inst_supply_ok s inst outs s'
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_var s` >>
  rename1 `fresh_ir_var s = (alloca_v,s1)` >>
  Cases_on `fresh_ir_var s1` >>
  rename1 `fresh_ir_var s1 = (add_v,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (alloca_id,s3)` >>
  Cases_on `fresh_inst_id s3` >>
  rename1 `fresh_inst_id s3 = (add_id,s4)` >>
  Cases_on `fresh_inst_id s4` >>
  rename1 `fresh_inst_id s4 = (copy_id,s5)` >>
  Cases_on `fresh_inst_id s5` >>
  rename1 `fresh_inst_id s5 = (load_id,s6)` >>
  gvs[lower_dload_inst_supply_def] >>
  `ld_supply_extends s s1` by metis_tac[fresh_ir_var_extends] >>
  `ld_supply_extends s1 s2` by
    metis_tac[fresh_ir_var_extends, ld_supply_extends_def] >>
  `ld_supply_extends s s2` by metis_tac[ld_supply_extends_trans] >>
  `ld_supply_extends s2 s3` by
    metis_tac[fresh_inst_id_extends, ld_supply_extends_def] >>
  `ld_supply_extends s3 s4` by
    metis_tac[fresh_inst_id_extends, ld_supply_extends_def] >>
  `ld_supply_extends s4 s5` by
    metis_tac[fresh_inst_id_extends, ld_supply_extends_def] >>
  `ld_supply_extends s5 s'` by
    metis_tac[fresh_inst_id_extends, ld_supply_extends_def] >>
  `ld_supply_extends s s'` by metis_tac[ld_supply_extends_trans] >>
  `ir_supply_inst_ok s2 /\ ir_supply_inst_ok s3 /\
   ir_supply_inst_ok s4 /\ ir_supply_inst_ok s5` by
    gvs[ld_supply_extends_def] >>
  `~MEM alloca_id s2.irs_used_inst_ids /\
   s3.irs_used_inst_ids = alloca_id::s2.irs_used_inst_ids` by
    metis_tac[fresh_inst_id_contract] >>
  `~MEM add_id s3.irs_used_inst_ids /\
   s4.irs_used_inst_ids = add_id::s3.irs_used_inst_ids` by
    metis_tac[fresh_inst_id_contract] >>
  `~MEM copy_id s4.irs_used_inst_ids /\
   s5.irs_used_inst_ids = copy_id::s4.irs_used_inst_ids` by
    metis_tac[fresh_inst_id_contract] >>
  `~MEM load_id s5.irs_used_inst_ids /\
   s'.irs_used_inst_ids = load_id::s5.irs_used_inst_ids` by
    metis_tac[fresh_inst_id_contract] >>
  gvs[ld_inst_supply_ok_def, ld_supply_extends_def] >> metis_tac[]
QED

Theorem lower_dload_inst_supply_shaped_dloadbytes:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  MEM inst.inst_id s.irs_used_inst_ids /\
  inst.inst_opcode = DLOADBYTES /\
  inst.inst_operands = [dst_op;src_op;size_op] /\
  lower_dload_inst_supply s inst = (outs,s') ==>
  ld_inst_supply_ok s inst outs s'
Proof
  rpt strip_tac >>
  Cases_on `fresh_ir_var s` >>
  rename1 `fresh_ir_var s = (add_v,s1)` >>
  Cases_on `fresh_inst_id s1` >>
  rename1 `fresh_inst_id s1 = (add_id,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (copy_id,s3)` >>
  gvs[lower_dload_inst_supply_def] >>
  `ld_supply_extends s s1` by metis_tac[fresh_ir_var_extends] >>
  `ld_supply_extends s1 s2` by
    metis_tac[fresh_inst_id_extends, ld_supply_extends_def] >>
  `ld_supply_extends s2 s'` by
    metis_tac[fresh_inst_id_extends, ld_supply_extends_def] >>
  `ld_supply_extends s s'` by metis_tac[ld_supply_extends_trans] >>
  `ir_supply_inst_ok s1 /\ ir_supply_inst_ok s2` by
    gvs[ld_supply_extends_def] >>
  `~MEM add_id s1.irs_used_inst_ids /\
   s2.irs_used_inst_ids = add_id::s1.irs_used_inst_ids` by
    metis_tac[fresh_inst_id_contract] >>
  `~MEM copy_id s2.irs_used_inst_ids /\
   s'.irs_used_inst_ids = copy_id::s2.irs_used_inst_ids` by
    metis_tac[fresh_inst_id_contract] >>
  gvs[ld_inst_supply_ok_def, ld_supply_extends_def] >> metis_tac[]
QED

Theorem lower_dload_inst_supply_passthrough:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  MEM inst.inst_id s.irs_used_inst_ids /\
  lower_dload_inst_supply s inst = ([inst],s) ==>
  ld_inst_supply_ok s inst [inst] s
Proof
  simp[ld_inst_supply_ok_def, ld_supply_extends_refl]
QED

Theorem lower_dload_inst_supply_contract:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  MEM inst.inst_id s.irs_used_inst_ids /\
  lower_dload_inst_supply s inst = (outs,s') ==>
  ld_inst_supply_ok s inst outs s'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = DLOAD`
  >- (Cases_on `?ptr. inst.inst_operands = [ptr]`
      >- (Cases_on `?outv. inst.inst_outputs = [outv]`
          >- metis_tac[lower_dload_inst_supply_shaped_dload]
          >> `lower_dload_inst_supply s inst = ([inst],s)` by
               gvs[lower_dload_inst_supply_def, AllCaseEqs()]
          >> gvs[] >> metis_tac[lower_dload_inst_supply_passthrough])
      >> `lower_dload_inst_supply s inst = ([inst],s)` by
           gvs[lower_dload_inst_supply_def, AllCaseEqs()]
      >> gvs[] >> metis_tac[lower_dload_inst_supply_passthrough]) >>
  Cases_on `inst.inst_opcode = DLOADBYTES`
  >- (Cases_on
        `?dst_op src_op size_op.
           inst.inst_operands = [dst_op;src_op;size_op]`
      >- metis_tac[lower_dload_inst_supply_shaped_dloadbytes]
      >> `lower_dload_inst_supply s inst = ([inst],s)` by
           gvs[lower_dload_inst_supply_def, AllCaseEqs()]
      >> gvs[] >> metis_tac[lower_dload_inst_supply_passthrough]) >>
  gvs[lower_dload_inst_supply_def] >>
  irule lower_dload_inst_supply_passthrough >>
  simp[lower_dload_inst_supply_def]
QED

Theorem lower_dload_insts_supply_contract:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
  EVERY (\i. MEM i.inst_id s.irs_used_inst_ids) insts /\
  lower_dload_insts_supply s insts = (outs,s') ==>
  ld_insts_supply_ok s insts outs s'
Proof
  qid_spec_tac `s'` >> qid_spec_tac `outs` >> qid_spec_tac `s` >>
  Induct_on `insts`
  >- simp[lower_dload_insts_supply_def, ld_insts_supply_ok_def,
          ld_supply_extends_refl] >>
  rpt strip_tac >>
  Cases_on `lower_dload_inst_supply s h` >>
  rename1 `lower_dload_inst_supply s h = (head_out,s1)` >>
  Cases_on `lower_dload_insts_supply s1 insts` >>
  rename1 `lower_dload_insts_supply s1 insts = (tail_out,s2)` >>
  gvs[lower_dload_insts_supply_def] >>
  `ld_inst_supply_ok s h head_out s1` by
    metis_tac[lower_dload_inst_supply_contract] >>
  `ld_supply_extends s s1` by
    gvs[ld_inst_supply_ok_def] >>
  `ir_supply_inst_ok s1 /\
   ALL_DISTINCT s1.irs_used_inst_ids /\
   ALL_DISTINCT s1.irs_used_vars` by
    gvs[ld_supply_extends_def] >>
  `EVERY (\i. MEM i.inst_id s1.irs_used_inst_ids) insts` by
    gvs[listTheory.EVERY_MEM, ld_supply_extends_def] >>
  `ld_insts_supply_ok s1 insts tail_out s'` by
    (first_x_assum irule >> metis_tac[]) >>
  qpat_x_assum
    `!s'' outs' s'''. _ ==> ld_insts_supply_ok s'' insts outs' s'''`
    kall_tac >>
  qpat_x_assum `ld_inst_supply_ok s h head_out s1` mp_tac >>
  simp[ld_inst_supply_ok_def] >> strip_tac >>
  qpat_x_assum `ld_insts_supply_ok s1 insts tail_out s'` mp_tac >>
  simp[ld_insts_supply_ok_def] >> strip_tac >>
  `!id. MEM id (MAP (\i. i.inst_id) head_out) ==>
        ~MEM id (MAP (\i. i.inst_id) tail_out)` by
    (rpt strip_tac >>
     `MEM id s1.irs_used_inst_ids` by
       (qpat_x_assum `MEM id (MAP (\i. i.inst_id) head_out)` mp_tac >>
        pure_rewrite_tac[listTheory.MEM_MAP] >> strip_tac >>
        gvs[listTheory.EVERY_MEM]) >>
     `MEM id (MAP (\i. i.inst_id) insts)` by metis_tac[] >>
     `MEM id s.irs_used_inst_ids` by
       (qpat_x_assum `MEM id (MAP (\i. i.inst_id) insts)` mp_tac >>
        pure_rewrite_tac[listTheory.MEM_MAP] >> strip_tac >>
        gvs[listTheory.EVERY_MEM]) >>
     metis_tac[]) >>
  `EVERY (\i. MEM i.inst_id s'.irs_used_inst_ids) head_out` by
    (gvs[listTheory.EVERY_MEM, ld_supply_extends_def] >> metis_tac[]) >>
  gvs[ld_insts_supply_ok_def, ld_supply_extends_def,
      listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM,
      listTheory.MEM_MAP] >>
  metis_tac[ld_supply_extends_trans]
QED

Theorem ld_ids_supply_ok_append:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT (old1 ++ old2) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (old1 ++ old2) /\
  ld_ids_supply_ok s old1 new1 s1 /\
  ld_ids_supply_ok s1 old2 new2 s2 ==>
  ld_ids_supply_ok s (old1 ++ old2) (new1 ++ new2) s2
Proof
  rpt strip_tac >>
  qpat_x_assum `ld_ids_supply_ok s old1 new1 s1` mp_tac >>
  simp[ld_ids_supply_ok_def] >> strip_tac >>
  qpat_x_assum `ld_ids_supply_ok s1 old2 new2 s2` mp_tac >>
  simp[ld_ids_supply_ok_def] >> strip_tac >>
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
    (gvs[listTheory.EVERY_MEM, ld_supply_extends_def] >> metis_tac[]) >>
  gvs[ld_ids_supply_ok_def, ld_supply_extends_def,
      listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM] >>
  metis_tac[ld_supply_extends_trans]
QED

Theorem lower_dload_block_supply_contract:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT (block_ir_inst_ids bb) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (block_ir_inst_ids bb) /\
  lower_dload_block_supply s bb = (bb',s') ==>
  ld_ids_supply_ok s (block_ir_inst_ids bb) (block_ir_inst_ids bb') s'
Proof
  rpt strip_tac >>
  Cases_on `lower_dload_insts_supply s bb.bb_instructions` >>
  rename1 `lower_dload_insts_supply s bb.bb_instructions = (insts,s1)` >>
  gvs[lower_dload_block_supply_def, block_ir_inst_ids_def,
      listTheory.EVERY_MAP] >>
  `ld_insts_supply_ok s bb.bb_instructions insts s'` by
    metis_tac[lower_dload_insts_supply_contract] >>
  gvs[ld_insts_supply_ok_ids]
QED

Theorem lower_dload_blocks_supply_contract:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT (FLAT (MAP block_ir_inst_ids bbs)) /\
  EVERY (\id. MEM id s.irs_used_inst_ids)
    (FLAT (MAP block_ir_inst_ids bbs)) /\
  lower_dload_blocks_supply s bbs = (bbs',s') ==>
  ld_ids_supply_ok s (FLAT (MAP block_ir_inst_ids bbs))
    (FLAT (MAP block_ir_inst_ids bbs')) s'
Proof
  qid_spec_tac `s'` >> qid_spec_tac `bbs'` >> qid_spec_tac `s` >>
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def, ld_ids_supply_ok_def,
          ld_supply_extends_refl] >>
  rpt strip_tac >>
  Cases_on `lower_dload_block_supply s h` >>
  rename1 `lower_dload_block_supply s h = (bb1,s1)` >>
  Cases_on `lower_dload_blocks_supply s1 bbs` >>
  rename1 `lower_dload_blocks_supply s1 bbs = (bbs1,s2)` >>
  gvs[lower_dload_blocks_supply_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_APPEND] >>
  `ld_ids_supply_ok s (block_ir_inst_ids h) (block_ir_inst_ids bb1) s1` by
    metis_tac[lower_dload_block_supply_contract] >>
  `ld_supply_extends s s1` by gvs[ld_ids_supply_ok_def] >>
  `ir_supply_inst_ok s1 /\
   ALL_DISTINCT s1.irs_used_inst_ids /\
   ALL_DISTINCT s1.irs_used_vars` by
    gvs[ld_supply_extends_def] >>
  `EVERY (\id. MEM id s1.irs_used_inst_ids)
     (FLAT (MAP block_ir_inst_ids bbs))` by
    gvs[listTheory.EVERY_MEM, ld_supply_extends_def] >>
  `ld_ids_supply_ok s1 (FLAT (MAP block_ir_inst_ids bbs))
     (FLAT (MAP block_ir_inst_ids bbs1)) s'` by
    (first_x_assum irule >> metis_tac[]) >>
  irule ld_ids_supply_ok_append >>
  simp[] >>
  conj_tac >- simp[listTheory.ALL_DISTINCT_APPEND] >>
  qexists `s1` >> simp[]
QED

Theorem lower_dload_function_supply_contract:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT (fn_ir_inst_ids fn) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn) /\
  lower_dload_function_supply s fn = (fn',s') ==>
  ld_ids_supply_ok s (fn_ir_inst_ids fn) (fn_ir_inst_ids fn') s'
Proof
  rpt strip_tac >>
  Cases_on `lower_dload_blocks_supply s fn.fn_blocks` >>
  rename1 `lower_dload_blocks_supply s fn.fn_blocks = (bbs,s1)` >>
  gvs[lower_dload_function_supply_def, fn_ir_inst_ids_def] >>
  metis_tac[lower_dload_blocks_supply_contract]
QED

Theorem lower_dload_functions_supply_contract:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids fns)) /\
  EVERY (\id. MEM id s.irs_used_inst_ids)
    (FLAT (MAP fn_ir_inst_ids fns)) /\
  lower_dload_functions_supply s fns = (fns',s') ==>
  ld_ids_supply_ok s (FLAT (MAP fn_ir_inst_ids fns))
    (FLAT (MAP fn_ir_inst_ids fns')) s'
Proof
  qid_spec_tac `s'` >> qid_spec_tac `fns'` >> qid_spec_tac `s` >>
  Induct_on `fns`
  >- simp[lower_dload_functions_supply_def, ld_ids_supply_ok_def,
          ld_supply_extends_refl] >>
  rpt strip_tac >>
  Cases_on `lower_dload_function_supply s h` >>
  rename1 `lower_dload_function_supply s h = (fn1,s1)` >>
  Cases_on `lower_dload_functions_supply s1 fns` >>
  rename1 `lower_dload_functions_supply s1 fns = (fns1,s2)` >>
  gvs[lower_dload_functions_supply_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_APPEND] >>
  `ld_ids_supply_ok s (fn_ir_inst_ids h) (fn_ir_inst_ids fn1) s1` by
    metis_tac[lower_dload_function_supply_contract] >>
  `ld_supply_extends s s1` by gvs[ld_ids_supply_ok_def] >>
  `ir_supply_inst_ok s1 /\
   ALL_DISTINCT s1.irs_used_inst_ids /\
   ALL_DISTINCT s1.irs_used_vars` by
    gvs[ld_supply_extends_def] >>
  `EVERY (\id. MEM id s1.irs_used_inst_ids)
     (FLAT (MAP fn_ir_inst_ids fns))` by
    gvs[listTheory.EVERY_MEM, ld_supply_extends_def] >>
  `ld_ids_supply_ok s1 (FLAT (MAP fn_ir_inst_ids fns))
     (FLAT (MAP fn_ir_inst_ids fns1)) s'` by
    (first_x_assum irule >> metis_tac[]) >>
  irule ld_ids_supply_ok_append >>
  simp[] >>
  conj_tac >- simp[listTheory.ALL_DISTINCT_APPEND] >>
  qexists `s1` >> simp[]
QED

Theorem lower_dload_context_supply_contract:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  EVERY (\id. MEM id s.irs_used_inst_ids)
    (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions)) /\
  lower_dload_context_supply s ctx = (ctx',s') ==>
  ld_ids_supply_ok s (FLAT (MAP fn_ir_inst_ids ctx.ctx_functions))
    (FLAT (MAP fn_ir_inst_ids ctx'.ctx_functions)) s'
Proof
  rpt strip_tac >>
  Cases_on `lower_dload_functions_supply s ctx.ctx_functions` >>
  rename1 `lower_dload_functions_supply s ctx.ctx_functions = (fns,s1)` >>
  gvs[lower_dload_context_supply_def] >>
  metis_tac[lower_dload_functions_supply_contract]
QED

Theorem lower_dload_unit_supply_contract:
  ir_supply_inst_ok s /\
  ALL_DISTINCT s.irs_used_inst_ids /\
  ALL_DISTINCT s.irs_used_vars /\
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  EVERY (\id. MEM id s.irs_used_inst_ids) (unit_ir_inst_ids unit) /\
  lower_dload_unit_supply s unit = (unit',s') ==>
  ld_ids_supply_ok s (unit_ir_inst_ids unit) (unit_ir_inst_ids unit') s'
Proof
  rpt strip_tac >>
  Cases_on `lower_dload_context_supply s unit.cu_context` >>
  rename1 `lower_dload_context_supply s unit.cu_context = (ctx,s1)` >>
  gvs[lower_dload_unit_supply_def, unit_ir_inst_ids_def] >>
  metis_tac[lower_dload_context_supply_contract]
QED

Theorem lower_dload_configured_with_supply_fresh:
  ALL_DISTINCT (unit_ir_inst_ids unit) /\
  ALL_DISTINCT (unit_ir_vars unit) /\
  lower_dload_configured_with_supply unit = (unit',s') ==>
  ALL_DISTINCT (unit_ir_inst_ids unit') /\
  EVERY (\id. MEM id s'.irs_used_inst_ids) (unit_ir_inst_ids unit') /\
  ld_supply_extends (init_ir_supply unit) s'
Proof
  rpt strip_tac >>
  `ld_ids_supply_ok (init_ir_supply unit) (unit_ir_inst_ids unit)
     (unit_ir_inst_ids unit') s'` by
    (irule lower_dload_unit_supply_contract >>
     gvs[init_ir_supply_inst_ok, init_ir_supply_fields,
         lower_dload_configured_with_supply_def,
         listTheory.EVERY_MEM]) >>
  gvs[ld_ids_supply_ok_def]
QED


Theorem lower_dload_invalidates_layout_shaped:
  MEM bb fn.fn_blocks /\
  MEM inst bb.bb_instructions /\
  inst.inst_opcode = DLOAD /\
  inst.inst_operands = [ptr] /\
  inst.inst_outputs = [out] ==>
  lower_dload_invalidates_layout fn
Proof
  simp[lower_dload_invalidates_layout_def] >> metis_tac[]
QED

Theorem lower_dload_invalidates_layout_cases:
  lower_dload_invalidates_layout fn <=>
  ?bb inst ptr out.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = DLOAD /\
    inst.inst_operands = [ptr] /\ inst.inst_outputs = [out]
Proof
  simp[lower_dload_invalidates_layout_def]
QED

Theorem lower_dload_function_supply_metadata:
  lower_dload_function_supply s fn = (fn',s') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_fmp_convention_eq fn' fn /\
  fn'.fn_eom =
    if lower_dload_invalidates_layout fn then NONE else fn.fn_eom
Proof
  rpt strip_tac >>
  Cases_on `lower_dload_blocks_supply s fn.fn_blocks` >>
  gvs[lower_dload_function_supply_def, fn_identity_metadata_eq_def,
      fn_static_input_eq_def, fn_fmp_convention_eq_def]
QED

Theorem lower_dload_function_supply_preserves_layout:
  lower_dload_function_supply s fn = (fn',s') /\
  ~lower_dload_invalidates_layout fn ==>
  fn_static_layout_eq fn' fn
Proof
  rpt strip_tac >>
  drule lower_dload_function_supply_metadata >>
  simp[fn_static_layout_eq_def]
QED

Theorem lower_dload_function_supply_clears_layout:
  lower_dload_function_supply s fn = (fn',s') /\
  lower_dload_invalidates_layout fn ==>
  fn'.fn_eom = NONE
Proof
  rpt strip_tac >>
  drule lower_dload_function_supply_metadata >> simp[]
QED

Theorem lower_dload_malformed_dloads_preserve_layout:
  (!bb inst.
     MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
     inst.inst_opcode = DLOAD ==>
       (~(?ptr. inst.inst_operands = [ptr]) \/
        ~(?out. inst.inst_outputs = [out]))) /\
  lower_dload_function_supply s fn = (fn',s') ==>
  fn_static_layout_eq fn' fn
Proof
  rpt strip_tac >>
  irule lower_dload_function_supply_preserves_layout >>
  simp[] >>
  simp[lower_dload_invalidates_layout_def] >> metis_tac[]
QED

Theorem lower_dload_dloadbytes_only_preserves_layout:
  (!bb inst.
     MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
     inst.inst_opcode = DLOADBYTES) /\
  lower_dload_function_supply s fn = (fn',s') ==>
  fn_static_layout_eq fn' fn
Proof
  rpt strip_tac >>
  `~lower_dload_invalidates_layout fn` by
    (simp[lower_dload_invalidates_layout_def] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`bb`,`inst`] mp_tac) >> simp[]) >>
  metis_tac[lower_dload_function_supply_preserves_layout]
QED
Theorem lower_dload_get_invoke_targets_append[local]:
  get_invoke_targets (xs ++ ys) =
  get_invoke_targets xs ++ get_invoke_targets ys
Proof
  Induct_on `xs`
  >- simp[get_invoke_targets_def]
  >> gen_tac >>
     Cases_on `h.inst_opcode = INVOKE`
  >- (Cases_on `h.inst_operands`
      >- simp[get_invoke_targets_def]
      >> Cases_on `h'` >> simp[get_invoke_targets_def])
  >> simp[get_invoke_targets_def]
QED

Theorem lower_dload_inst_supply_invoke_targets[local]:
  lower_dload_inst_supply s inst = (out,s') ==>
  get_invoke_targets out = get_invoke_targets [inst]
Proof
  Cases_on `inst.inst_opcode = DLOAD`
  >- (gvs[lower_dload_inst_supply_def, get_invoke_targets_def, AllCaseEqs()] >>
      strip_tac >> gvs[get_invoke_targets_def])
  >> Cases_on `inst.inst_opcode = DLOADBYTES`
  >- (gvs[lower_dload_inst_supply_def, get_invoke_targets_def, AllCaseEqs()] >>
      strip_tac >> gvs[get_invoke_targets_def])
  >> simp[lower_dload_inst_supply_def]
QED

Theorem lower_dload_insts_supply_invoke_targets[local]:
  !s out s'.
    lower_dload_insts_supply s insts = (out,s') ==>
    get_invoke_targets out = get_invoke_targets insts
Proof
  Induct_on `insts`
  >- simp[lower_dload_insts_supply_def, get_invoke_targets_def]
  >> rpt gen_tac >>
     Cases_on `lower_dload_inst_supply s h` >>
     rename1 `lower_dload_inst_supply s h = (head,s1)` >>
     Cases_on `lower_dload_insts_supply s1 insts` >>
     rename1 `lower_dload_insts_supply s1 insts = (tail,s2)` >>
     simp[lower_dload_insts_supply_def] >> strip_tac >>
     drule lower_dload_inst_supply_invoke_targets >>
     first_x_assum drule >>
     rpt strip_tac >>
     gvs[lower_dload_get_invoke_targets_append, get_invoke_targets_def] >>
     Cases_on `h.inst_opcode = INVOKE` >> gvs[] >>
     Cases_on `h.inst_operands` >> gvs[] >>
     Cases_on `h'` >> gvs[]
QED

Theorem lower_dload_blocks_supply_invoke_targets[local]:
  !s out s'.
    lower_dload_blocks_supply s bbs = (out,s') ==>
    get_invoke_targets (fn_insts_blocks out) =
    get_invoke_targets (fn_insts_blocks bbs)
Proof
  Induct_on `bbs`
  >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def,
          get_invoke_targets_def]
  >> rpt gen_tac >>
     Cases_on `lower_dload_block_supply s h` >>
     rename1 `lower_dload_block_supply s h = (head,s1)` >>
     Cases_on `lower_dload_blocks_supply s1 bbs` >>
     rename1 `lower_dload_blocks_supply s1 bbs = (tail,s2)` >>
     simp[lower_dload_blocks_supply_def] >> strip_tac >>
     first_x_assum drule >>
     gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
     imp_res_tac lower_dload_insts_supply_invoke_targets >>
     simp[fn_insts_blocks_def, lower_dload_get_invoke_targets_append]
QED

Theorem lower_dload_function_supply_invoke_targets:
  lower_dload_function_supply s fn = (fn',s') ==>
  MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac lower_dload_blocks_supply_invoke_targets >>
  gvs[fcg_scan_function_def, fn_insts_def]
QED

val _ = export_theory();
