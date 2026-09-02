(* Structural and supply contracts for the configured MakeSSA adapter. *)
Theory makeSsaCurrentProps
Ancestors
  makeSsaCurrentDefs makeSsaCurrentInduct irSupply
  list alist

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

val _ = export_theory();
