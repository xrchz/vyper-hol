(* Structural proofs for target-checked DRET desugaring. *)
Theory dretDesugarProofs
Ancestors
  dretDesugarDefs irSupply fcgDefs
Libs
  bossLib listTheory

Definition dret_supply_extends_def:
  dret_supply_extends old new <=>
    (?ids. new.irs_used_inst_ids = ids ++ old.irs_used_inst_ids /\
           ALL_DISTINCT ids /\
           EVERY (\id. ~MEM id old.irs_used_inst_ids) ids) /\
    (?vars. new.irs_used_vars = vars ++ old.irs_used_vars /\
            ALL_DISTINCT vars /\
            EVERY (\v. ~MEM v old.irs_used_vars) vars) /\
    new.irs_used_labels = old.irs_used_labels
End

Theorem dret_supply_extends_refl:
  dret_supply_extends s s
Proof
  simp[dret_supply_extends_def] >> qexistsl [`[]`,`[]`] >> simp[]
QED

Theorem all_distinct_append_fresh:
  ALL_DISTINCT xs /\ ALL_DISTINCT ys /\ EVERY (\x. ~MEM x ys) xs ==>
  ALL_DISTINCT (xs ++ ys)
Proof
  Induct_on `xs` >> simp[] >> metis_tac[]
QED

Theorem dret_supply_extends_trans:
  dret_supply_extends s1 s2 /\ dret_supply_extends s2 s3 ==>
  dret_supply_extends s1 s3
Proof
  simp[dret_supply_extends_def] >> rpt strip_tac
  >- (qexists `ids' ++ ids` >> gvs[] >>
      conj_tac
      >- (irule all_distinct_append_fresh >> simp[] >> gvs[EVERY_MEM])
      >> gvs[EVERY_MEM])
  >> qexists `vars' ++ vars` >> gvs[] >>
  conj_tac
  >- (irule all_distinct_append_fresh >> simp[] >> gvs[EVERY_MEM])
  >> gvs[EVERY_MEM]
QED

Theorem fresh_var_extends:
  fresh_ir_var s = (v,s') ==> dret_supply_extends s s'
Proof
  strip_tac >> drule fresh_ir_var_contract >> strip_tac >>
  simp[dret_supply_extends_def] >> gvs[]
QED

Theorem fresh_id_extends:
  ir_supply_inst_ok s /\ fresh_inst_id s = (id,s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  strip_tac >> drule fresh_inst_id_contract >> disch_then drule >> strip_tac >>
  conj_tac >- (simp[dret_supply_extends_def] >> gvs[]) >>
  simp[]
QED

Theorem fresh_var_extends_ok:
  ir_supply_inst_ok s /\ fresh_ir_var s = (v,s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  strip_tac >> conj_tac
  >- metis_tac[fresh_var_extends]
  >> drule fresh_ir_var_contract >> strip_tac >>
  gvs[ir_supply_inst_ok_def]
QED

Theorem expand_dret_pairs_empty:
  expand_dret_pairs s cursor [] =
    SOME (DretPairExpansion [] [] cursor s)
Proof
  simp[expand_dret_pairs_def]
QED

Theorem expand_dret_pairs_singleton:
  expand_dret_pairs s cursor [x] = NONE
Proof
  simp[expand_dret_pairs_def]
QED

Theorem expand_dret_pairs_success_fields:
  IS_SOME (expand_dret_pairs s cursor pairs) ==>
  ?emitted dsts final_cursor final_supply.
    expand_dret_pairs s cursor pairs =
      SOME (DretPairExpansion emitted dsts final_cursor final_supply)
Proof
  Cases_on `expand_dret_pairs s cursor pairs` >> simp[] >>
  Cases_on `x` >> simp[]
QED

Theorem expand_dret_pairs_no_dret:
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  EVERY (\i. i.inst_opcode <> DRET) emitted
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs(), venomInstTheory.mk_inst_def]
QED

Theorem replace_dret_inst_no_dret:
  replace_dret_inst s entry_cursor inst = SOME (replacement,s') ==>
  EVERY (\i. i.inst_opcode <> DRET) replacement
Proof
  gvs[replace_dret_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  gvs[venomInstTheory.mk_inst_def] >>
  drule expand_dret_pairs_no_dret >> simp[]
QED

Theorem expand_dret_pairs_supply:
  ir_supply_inst_ok s /\
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs()]
  >- simp[dret_supply_extends_refl]
  >> `dret_supply_extends s s1` by (irule fresh_var_extends >> simp[]) >>
  `dret_supply_extends s1 s2` by (irule fresh_var_extends >> simp[]) >>
  `dret_supply_extends s2 s3` by (irule fresh_var_extends >> simp[]) >>
  `ir_supply_inst_ok s3` by
    (qpat_assum `fresh_ir_var s = (plus31_v,s1)`
       (mp_tac o MATCH_MP fresh_ir_var_contract) >>
     qpat_assum `fresh_ir_var s1 = (aligned_v,s2)`
       (mp_tac o MATCH_MP fresh_ir_var_contract) >>
     qpat_assum `fresh_ir_var s2 = (next_v,s3)`
       (mp_tac o MATCH_MP fresh_ir_var_contract) >>
     rpt strip_tac >> gvs[ir_supply_inst_ok_def]) >>
  `dret_supply_extends s3 s4 /\ ir_supply_inst_ok s4` by
    (irule fresh_id_extends >> simp[]) >>
  `dret_supply_extends s4 s5 /\ ir_supply_inst_ok s5` by
    (irule fresh_id_extends >> simp[]) >>
  `dret_supply_extends s5 s6 /\ ir_supply_inst_ok s6` by
    (irule fresh_id_extends >> simp[]) >>
  `dret_supply_extends s6 s7 /\ ir_supply_inst_ok s7` by
    (irule fresh_id_extends >> simp[]) >>
  first_x_assum (drule_then strip_assume_tac) >>
  metis_tac[dret_supply_extends_trans]
QED

Theorem dret_desugar_insts_no_dret:
  dret_desugar_insts s entry_cursor insts = SOME (out,s') ==>
  EVERY (\i. i.inst_opcode <> DRET) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`entry_cursor`,`s`] >>
  Induct_on `insts` >> rpt strip_tac >>
  gvs[dret_desugar_insts_def, AllCaseEqs()] >>
  metis_tac[replace_dret_inst_no_dret]
QED

Theorem dret_desugar_blocks_no_dret:
  dret_desugar_blocks s entry_cursor blocks = SOME (out,s') ==>
  EVERY (\bb. EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`entry_cursor`,`s`] >>
  Induct_on `blocks` >> rpt strip_tac >>
  gvs[dret_desugar_blocks_def, AllCaseEqs()] >>
  metis_tac[dret_desugar_insts_no_dret]
QED

Theorem fn_insts_blocks_every:
  EVERY (\bb. EVERY p bb.bb_instructions) blocks ==>
  EVERY p (fn_insts_blocks blocks)
Proof
  Induct_on `blocks` >> simp[venomInstTheory.fn_insts_blocks_def]
QED

Theorem dret_desugar_function_no_dret:
  dret_desugar_function target supply fn = SOME (fn',supply') ==>
  no_dret fn'
Proof
  Cases_on `no_dret fn`
  >- (strip_tac >> gvs[dret_desugar_function_def])
  >> rpt strip_tac >>
  gvs[dret_desugar_function_def, AllCaseEqs()] >>
  simp[no_dret_def, venomInstTheory.fn_insts_def] >> rpt strip_tac >>
  drule dret_desugar_blocks_no_dret >> strip_tac >>
  `EVERY (\bb. EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions)
     ((first' with bb_instructions :=
        mk_inst getfmp_id GETFMP [] [entry_v]::first'.bb_instructions)::rest')` by
    gvs[venomInstTheory.mk_inst_def] >>
  drule fn_insts_blocks_every >> disch_then assume_tac >> gvs[EVERY_MEM]
QED

Theorem dret_desugar_function_identity:
  no_dret fn ==>
  dret_desugar_function target supply fn = SOME (fn,supply)
Proof
  simp[dret_desugar_function_def]
QED

Theorem map_functions_dret_no_dret:
  map_functions_supply (dret_desugar_function target) s fns = SOME (out,s') ==>
  EVERY no_dret out
Proof
  map_every qid_spec_tac [`s'`,`out`,`s`] >>
  Induct_on `fns` >> rpt strip_tac >>
  gvs[map_functions_supply_def, AllCaseEqs()] >>
  metis_tac[dret_desugar_function_no_dret]
QED

Theorem map_functions_dret_identity:
  EVERY no_dret fns ==>
  map_functions_supply (dret_desugar_function target) s fns = SOME (fns,s)
Proof
  map_every qid_spec_tac [`s`] >>
  Induct_on `fns` >>
  simp[map_functions_supply_def, dret_desugar_function_identity]
QED

Theorem dret_desugar_context_no_dret:
  dret_desugar_context target s ctx = SOME (ctx',s') ==>
  EVERY no_dret ctx'.ctx_functions
Proof
  strip_tac >>
  gvs[dret_desugar_context_def, map_ctx_functions_supply_def, AllCaseEqs()] >>
  metis_tac[map_functions_dret_no_dret]
QED

Theorem dret_desugar_context_identity:
  EVERY no_dret ctx.ctx_functions ==>
  dret_desugar_context target s ctx = SOME (ctx,s)
Proof
  strip_tac >> Cases_on `ctx` >>
  gvs[dret_desugar_context_def, map_ctx_functions_supply_def,
      map_functions_dret_identity, venomInstTheory.venom_context_component_equality]
QED

Theorem dret_desugar_configured_no_dret:
  dret_desugar_configured target unit = SOME unit' ==>
  EVERY no_dret unit'.cu_context.ctx_functions
Proof
  strip_tac >>
  gvs[dret_desugar_configured_def,
      dret_desugar_configured_with_supply_def, AllCaseEqs()] >>
  metis_tac[dret_desugar_context_no_dret]
QED

Theorem dret_desugar_configured_identity:
  EVERY no_dret unit.cu_context.ctx_functions ==>
  dret_desugar_configured target unit = SOME unit
Proof
  strip_tac >> Cases_on `unit` >>
  gvs[dret_desugar_configured_def,
      dret_desugar_configured_with_supply_def,
      dret_desugar_context_identity,
      venomCompilerTypesTheory.compilation_unit_component_equality]
QED

Theorem replace_dret_inst_supply:
  ir_supply_inst_ok s /\
  replace_dret_inst s entry_cursor inst = SOME (replacement,s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  gvs[replace_dret_inst_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  `dret_supply_extends s s1 /\ ir_supply_inst_ok s1` by
    (drule_all expand_dret_pairs_supply >> simp[]) >>
  `dret_supply_extends s1 s2 /\ ir_supply_inst_ok s2` by
    (irule fresh_id_extends >> simp[]) >>
  `dret_supply_extends s2 s' /\ ir_supply_inst_ok s'` by
    (irule fresh_id_extends >> simp[]) >>
  metis_tac[dret_supply_extends_trans]
QED

Theorem dret_desugar_insts_supply:
  ir_supply_inst_ok s /\
  dret_desugar_insts s entry_cursor insts = SOME (out,s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  map_every qid_spec_tac [`s'`,`out`,`entry_cursor`,`s`] >>
  Induct_on `insts` >> rpt strip_tac >>
  gvs[dret_desugar_insts_def, AllCaseEqs()]
  >- simp[dret_supply_extends_refl]
  >> metis_tac[replace_dret_inst_supply, dret_supply_extends_trans]
QED

Theorem dret_desugar_blocks_supply:
  ir_supply_inst_ok s /\
  dret_desugar_blocks s entry_cursor blocks = SOME (out,s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  map_every qid_spec_tac [`s'`,`out`,`entry_cursor`,`s`] >>
  Induct_on `blocks` >> rpt strip_tac >>
  gvs[dret_desugar_blocks_def, AllCaseEqs()]
  >- simp[dret_supply_extends_refl]
  >> metis_tac[dret_desugar_insts_supply, dret_supply_extends_trans]
QED

Theorem dret_desugar_function_supply:
  ir_supply_inst_ok s /\
  dret_desugar_function target s fn = SOME (fn',s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  rpt strip_tac >> gvs[dret_desugar_function_def, AllCaseEqs()]
  >- simp[dret_supply_extends_refl]
  >> rpt strip_tac >>
  `dret_supply_extends s s1 /\ ir_supply_inst_ok s1` by
    (irule fresh_var_extends_ok >> simp[]) >>
  `dret_supply_extends s1 s2 /\ ir_supply_inst_ok s2` by
    (irule fresh_id_extends >> simp[]) >>
  `dret_supply_extends s2 s' /\ ir_supply_inst_ok s'` by
    (drule_all dret_desugar_blocks_supply >> simp[]) >>
  metis_tac[dret_supply_extends_trans]
QED

Theorem map_functions_dret_supply:
  ir_supply_inst_ok s /\
  map_functions_supply (dret_desugar_function target) s fns = SOME (fns',s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  map_every qid_spec_tac [`s'`,`fns'`,`s`] >>
  Induct_on `fns` >> rpt strip_tac >>
  gvs[map_functions_supply_def, AllCaseEqs()]
  >- simp[dret_supply_extends_refl]
  >> metis_tac[dret_desugar_function_supply, dret_supply_extends_trans]
QED

Theorem dret_desugar_context_supply:
  ir_supply_inst_ok s /\
  dret_desugar_context target s ctx = SOME (ctx',s') ==>
  dret_supply_extends s s' /\ ir_supply_inst_ok s'
Proof
  gvs[dret_desugar_context_def, map_ctx_functions_supply_def, AllCaseEqs()] >>
  metis_tac[map_functions_dret_supply]
QED

Theorem dret_desugar_configured_supply:
  dret_desugar_configured_with_supply target unit = SOME (unit',s') ==>
  dret_supply_extends (init_ir_supply unit) s' /\ ir_supply_inst_ok s'
Proof
  gvs[dret_desugar_configured_with_supply_def, AllCaseEqs()] >>
  metis_tac[dret_desugar_context_supply, init_ir_supply_inst_ok]
QED

Theorem dret_desugar_configured_fresh:
  dret_desugar_configured_with_supply target unit = SOME (unit',s') ==>
  ?generated_ids generated_vars.
    s'.irs_used_inst_ids = generated_ids ++ unit_ir_inst_ids unit /\
    ALL_DISTINCT generated_ids /\
    EVERY (\id. ~MEM id (unit_ir_inst_ids unit)) generated_ids /\
    s'.irs_used_vars = generated_vars ++ unit_ir_vars unit /\
    ALL_DISTINCT generated_vars /\
    EVERY (\v. ~MEM v (unit_ir_vars unit)) generated_vars
Proof
  strip_tac >> drule dret_desugar_configured_supply >> strip_tac >>
  gvs[dret_supply_extends_def, init_ir_supply_fields] >>
  metis_tac[]
QED

Theorem dret_value_operand_simps[simp]:
  dret_value_operand (Lit w) /\
  dret_value_operand (Var v) /\
  ~dret_value_operand (Label l)
Proof
  simp[dret_value_operand_def]
QED

Theorem dret_label_size_input_rejected:
  let inst = mk_inst 0 DRET
    [Lit 1w; Var "src"; Label "size_label"; Var "retpc"] [] in
    IS_SOME (parse_dret_shape inst) /\
    ~EVERY dret_value_operand inst.inst_operands
Proof
  EVAL_TAC >> simp[dret_value_operand_def]
QED

Theorem dret_value_input_accepted:
  let inst = mk_inst 0 DRET
    [Lit 1w; Var "src"; Var "size"; Var "retpc"] [] in
    parse_dret_shape inst = SOME (0,1) /\
    EVERY dret_value_operand inst.inst_operands
Proof
  simp[venomInstTheory.mk_inst_def, dretShapeDefsTheory.parse_dret_shape_def,
       dret_value_operand_simps]
QED

Theorem dret_value_operand_no_labels:
  dret_value_operand op ==> operand_ir_labels [op] = []
Proof
  Cases_on `op` >> simp[dret_value_operand_def, operand_ir_labels_def]
QED

Theorem dret_value_operands_no_labels:
  EVERY dret_value_operand ops ==> operand_ir_labels ops = []
Proof
  Induct_on `ops` >> simp[operand_ir_labels_def] >>
  Cases_on `h` >> simp[dret_value_operand_def, operand_ir_labels_def]
QED

Theorem expand_dret_pairs_labels:
  EVERY dret_value_operand pairs /\
  dret_value_operand cursor /\
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  FLAT (MAP inst_ir_labels emitted) = []
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs(), venomInstTheory.mk_inst_def,
      inst_ir_labels_def, dret_value_operands_no_labels]
QED

Theorem expand_dret_pairs_dsts_legal:
  EVERY dret_value_operand pairs /\
  dret_value_operand cursor /\
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  EVERY dret_value_operand dsts
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs()]
QED

Theorem expand_dret_pairs_final_cursor_legal:
  EVERY dret_value_operand pairs /\
  dret_value_operand cursor /\
  expand_dret_pairs s cursor pairs =
    SOME (DretPairExpansion emitted dsts final_cursor s') ==>
  dret_value_operand final_cursor
Proof
  map_every qid_spec_tac
    [`emitted`,`dsts`,`final_cursor`,`s'`,`pairs`,`cursor`,`s`] >>
  recInduct expand_dret_pairs_ind >> rpt strip_tac >>
  gvs[expand_dret_pairs_def, AllCaseEqs()]
QED

Theorem every_take:
  EVERY p xs ==> EVERY p (TAKE n xs)
Proof
  map_every qid_spec_tac [`n`,`xs`] >> Induct_on `xs` >>
  Cases_on `n` >> simp[]
QED

Theorem every_tl:
  EVERY p xs ==> EVERY p (TL xs)
Proof
  Cases_on `xs` >> simp[]
QED

Theorem every_drop:
  EVERY p xs ==> EVERY p (DROP n xs)
Proof
  map_every qid_spec_tac [`n`,`xs`] >> Induct_on `xs` >>
  Cases_on `n` >> simp[]
QED

Theorem split_dret_operands_legal:
  EVERY dret_value_operand inst.inst_operands /\
  split_dret_operands inst = SOME (ordinary,pairs,return_pc) ==>
  EVERY dret_value_operand ordinary /\
  EVERY dret_value_operand pairs /\
  dret_value_operand return_pc
Proof
  strip_tac >> gvs[split_dret_operands_def, AllCaseEqs()] >>
  drule dretShapeDefsTheory.parse_dret_shape_length >> strip_tac >>
  conj_tac >- metis_tac[every_tl, every_take] >>
  conj_tac >- metis_tac[every_tl, every_take, every_drop] >>
  `EVERY dret_value_operand (TL inst.inst_operands)` by
    metis_tac[every_tl] >>
  gvs[listTheory.EVERY_EL] >> first_x_assum irule >> decide_tac
QED


Theorem replace_dret_inst_labels:
  EVERY dret_value_operand inst.inst_operands /\
  dret_value_operand entry_cursor /\
  replace_dret_inst s entry_cursor inst = SOME (out,s') ==>
  FLAT (MAP inst_ir_labels out) = inst_ir_labels inst
Proof
  strip_tac >>
  `inst_ir_labels inst = []` by
    (simp[inst_ir_labels_def] >>
     irule dret_value_operands_no_labels >> simp[]) >>
  gvs[replace_dret_inst_def, AllCaseEqs()] >> rpt strip_tac >>
  `EVERY dret_value_operand ordinary /\
   EVERY dret_value_operand pairs /\
   dret_value_operand return_pc` by
    metis_tac[split_dret_operands_legal] >>
  `FLAT (MAP inst_ir_labels body) = []` by
    metis_tac[expand_dret_pairs_labels] >>
  `EVERY dret_value_operand dsts` by
    metis_tac[expand_dret_pairs_dsts_legal] >>
  `dret_value_operand final_cursor` by
    metis_tac[expand_dret_pairs_final_cursor_legal] >>
  `EVERY dret_value_operand (ordinary ++ dsts ++ [return_pc])` by simp[] >>
  `operand_ir_labels (ordinary ++ dsts ++ [return_pc]) = []` by
    metis_tac[dret_value_operands_no_labels] >>
  `operand_ir_labels [final_cursor] = []` by
    metis_tac[dret_value_operand_no_labels] >>
  gvs[venomInstTheory.mk_inst_def, inst_ir_labels_def]
QED
Theorem dret_desugar_insts_labels:
  EVERY (\inst. inst.inst_opcode = DRET ==>
          EVERY dret_value_operand inst.inst_operands) insts /\
  dret_value_operand entry_cursor /\
  dret_desugar_insts s entry_cursor insts = SOME (out,s') ==>
  FLAT (MAP inst_ir_labels out) = FLAT (MAP inst_ir_labels insts)
Proof
  map_every qid_spec_tac [`s'`,`out`,`entry_cursor`,`s`] >>
  Induct_on `insts` >> rpt strip_tac >>
  gvs[dret_desugar_insts_def, AllCaseEqs()] >>
  metis_tac[replace_dret_inst_labels]
QED

Theorem dret_desugar_blocks_labels:
  EVERY (\bb. EVERY (\inst. inst.inst_opcode = DRET ==>
          EVERY dret_value_operand inst.inst_operands) bb.bb_instructions) blocks /\
  dret_value_operand entry_cursor /\
  dret_desugar_blocks s entry_cursor blocks = SOME (out,s') ==>
  FLAT (MAP block_ir_labels out) = FLAT (MAP block_ir_labels blocks)
Proof
  map_every qid_spec_tac [`s'`,`out`,`entry_cursor`,`s`] >>
  Induct_on `blocks` >> rpt strip_tac >>
  gvs[dret_desugar_blocks_def, AllCaseEqs(), block_ir_labels_def] >>
  metis_tac[dret_desugar_insts_labels]
QED

Theorem mem_fn_insts_blocks:
  MEM bb blocks /\ MEM inst bb.bb_instructions ==>
  MEM inst (fn_insts_blocks blocks)
Proof
  map_every qid_spec_tac [`inst`,`bb`] >> Induct_on `blocks` >>
  simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]
QED

Theorem dret_desugar_input_blocks_legal:
  dret_desugar_input fn ==>
  EVERY (\bb. EVERY (\inst. inst.inst_opcode = DRET ==>
          EVERY dret_value_operand inst.inst_operands) bb.bb_instructions)
    fn.fn_blocks
Proof
  strip_tac >> simp[EVERY_MEM] >> rpt strip_tac >>
  gvs[dret_desugar_input_def] >>
  `MEM inst (fn_insts fn)` by
    (simp[venomInstTheory.fn_insts_def] >>
     metis_tac[mem_fn_insts_blocks]) >>
  `EVERY dret_value_operand inst.inst_operands` by metis_tac[] >>
  gvs[EVERY_MEM]
QED

Theorem dret_desugar_function_labels:
  dret_desugar_function target s fn = SOME (fn',s') ==>
  fn_ir_labels fn' = fn_ir_labels fn
Proof
  rpt strip_tac >>
  gvs[dret_desugar_function_def, AllCaseEqs()] >> rpt strip_tac >>
  `EVERY (\bb. EVERY (\inst. inst.inst_opcode = DRET ==>
      EVERY dret_value_operand inst.inst_operands) bb.bb_instructions)
    (first::rest)` by metis_tac[dret_desugar_input_blocks_legal] >>
  `FLAT (MAP block_ir_labels (first'::rest')) =
   FLAT (MAP block_ir_labels (first::rest))` by
    metis_tac[dret_desugar_blocks_labels, dret_value_operand_simps] >>
  gvs[fn_ir_labels_def, block_ir_labels_def, venomInstTheory.mk_inst_def,
      inst_ir_labels_def, operand_ir_labels_def]
QED

Theorem dret_desugar_function_metadata:
  dret_desugar_function target s fn = SOME (fn',s') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn /\
  fn_fmp_convention_eq fn' fn
Proof
  rpt strip_tac >>
  gvs[dret_desugar_function_def, AllCaseEqs(),
      venomInstTheory.fn_identity_metadata_eq_def,
      venomInstTheory.fn_static_input_eq_def,
      venomInstTheory.fn_static_layout_eq_def,
      venomInstTheory.fn_fmp_convention_eq_def]
QED

Theorem map_functions_dret_labels:
  map_functions_supply (dret_desugar_function target) s fns =
    SOME (fns',s') ==>
  FLAT (MAP fn_ir_labels fns') = FLAT (MAP fn_ir_labels fns)
Proof
  map_every qid_spec_tac [`s'`,`fns'`,`s`] >>
  Induct_on `fns` >> rpt strip_tac >>
  gvs[map_functions_supply_def, AllCaseEqs()] >>
  metis_tac[dret_desugar_function_labels]
QED

Theorem dret_desugar_context_labels:
  dret_desugar_context target s ctx = SOME (ctx',s') ==>
  FLAT (MAP fn_ir_labels ctx'.ctx_functions) =
  FLAT (MAP fn_ir_labels ctx.ctx_functions)
Proof
  rpt strip_tac >>
  gvs[dret_desugar_context_def, map_ctx_functions_supply_def, AllCaseEqs()] >>
  metis_tac[map_functions_dret_labels]
QED

Theorem dret_desugar_configured_with_supply_labels:
  dret_desugar_configured_with_supply target unit = SOME (unit',s') ==>
  unit_ir_labels unit' = unit_ir_labels unit
Proof
  rpt strip_tac >>
  gvs[dret_desugar_configured_with_supply_def, dret_desugar_context_def,
      map_ctx_functions_supply_def, AllCaseEqs(), unit_ir_labels_def] >>
  drule map_functions_dret_labels >> simp[]
QED

Theorem dret_desugar_configured_labels:
  dret_desugar_configured target unit = SOME unit' ==>
  unit_ir_labels unit' = unit_ir_labels unit
Proof
  rpt strip_tac >> gvs[dret_desugar_configured_def, AllCaseEqs()] >>
  Cases_on `z` >> gvs[] >>
  metis_tac[dret_desugar_configured_with_supply_labels]
QED

Theorem map_functions_dret_metadata:
  map_functions_supply (dret_desugar_function target) s fns =
    SOME (fns',s') ==>
  LIST_REL (\f' f.
    fn_identity_metadata_eq f' f /\
    fn_static_input_eq f' f /\
    fn_static_layout_eq f' f /\
    fn_fmp_convention_eq f' f) fns' fns
Proof
  map_every qid_spec_tac [`s'`,`fns'`,`s`] >>
  Induct_on `fns` >> rpt strip_tac >>
  gvs[map_functions_supply_def, AllCaseEqs()] >>
  metis_tac[dret_desugar_function_metadata]
QED

Theorem dret_desugar_context_metadata:
  dret_desugar_context target s ctx = SOME (ctx',s') ==>
  LIST_REL (\f' f.
    fn_identity_metadata_eq f' f /\
    fn_static_input_eq f' f /\
    fn_static_layout_eq f' f /\
    fn_fmp_convention_eq f' f)
    ctx'.ctx_functions ctx.ctx_functions
Proof
  rpt strip_tac >>
  gvs[dret_desugar_context_def, map_ctx_functions_supply_def, AllCaseEqs()] >>
  metis_tac[map_functions_dret_metadata]
QED

Theorem dret_desugar_configured_with_supply_metadata:
  dret_desugar_configured_with_supply target unit = SOME (unit',s') ==>
  LIST_REL (\f' f.
    fn_identity_metadata_eq f' f /\
    fn_static_input_eq f' f /\
    fn_static_layout_eq f' f /\
    fn_fmp_convention_eq f' f)
    unit'.cu_context.ctx_functions unit.cu_context.ctx_functions
Proof
  rpt strip_tac >>
  gvs[dret_desugar_configured_with_supply_def, dret_desugar_context_def,
      map_ctx_functions_supply_def, AllCaseEqs()] >>
  metis_tac[map_functions_dret_metadata]
QED

Theorem dret_desugar_configured_metadata:
  dret_desugar_configured target unit = SOME unit' ==>
  LIST_REL (\f' f.
    fn_identity_metadata_eq f' f /\
    fn_static_input_eq f' f /\
    fn_static_layout_eq f' f /\
    fn_fmp_convention_eq f' f)
    unit'.cu_context.ctx_functions unit.cu_context.ctx_functions
Proof
  rpt strip_tac >> gvs[dret_desugar_configured_def, AllCaseEqs()] >>
  Cases_on `z` >> gvs[] >>
  metis_tac[dret_desugar_configured_with_supply_metadata]
QED
Theorem dret_get_invoke_targets_append[local]:
  get_invoke_targets (xs ++ ys) =
  get_invoke_targets xs ++ get_invoke_targets ys
Proof
  Induct_on `xs`
  >- simp[get_invoke_targets_def]
  >> gen_tac >> Cases_on `h.inst_opcode = INVOKE`
  >- (Cases_on `h.inst_operands`
      >- simp[get_invoke_targets_def]
      >> Cases_on `h'` >> simp[get_invoke_targets_def])
  >> simp[get_invoke_targets_def]
QED

Theorem expand_dret_pairs_no_invoke[local]:
  !s cursor pairs body dsts final_cursor s'.
    expand_dret_pairs s cursor pairs =
      SOME (DretPairExpansion body dsts final_cursor s') ==>
    get_invoke_targets body = []
Proof
  recInduct expand_dret_pairs_ind >>
  rpt strip_tac >>
  gvs[Once expand_dret_pairs_def, AllCaseEqs(),
      get_invoke_targets_def, venomInstTheory.mk_inst_def]
QED

Theorem replace_dret_inst_no_invoke[local]:
  replace_dret_inst s cursor inst = SOME (replacement,s') ==>
  get_invoke_targets replacement = []
Proof
  simp[replace_dret_inst_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac expand_dret_pairs_no_invoke >>
  gvs[dret_get_invoke_targets_append, get_invoke_targets_def,
      venomInstTheory.mk_inst_def]
QED

Theorem dret_desugar_insts_invoke_targets[local]:
  !s out s'.
    dret_desugar_insts s cursor insts = SOME (out,s') ==>
    get_invoke_targets out = get_invoke_targets insts
Proof
  Induct_on `insts`
  >- simp[dret_desugar_insts_def, get_invoke_targets_def]
  >> gen_tac >> rpt gen_tac >>
     Cases_on `h.inst_opcode = DRET`
  >- (gvs[dret_desugar_insts_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac replace_dret_inst_no_invoke >>
      first_x_assum drule >> strip_tac >>
      gvs[dret_get_invoke_targets_append, get_invoke_targets_def])
  >> gvs[dret_desugar_insts_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     first_x_assum drule >> strip_tac >>
     gvs[get_invoke_targets_def]
QED

Theorem dret_desugar_blocks_invoke_targets[local]:
  !s out s'.
    dret_desugar_blocks s cursor blocks = SOME (out,s') ==>
    get_invoke_targets (fn_insts_blocks out) =
    get_invoke_targets (fn_insts_blocks blocks)
Proof
  Induct_on `blocks`
  >- simp[dret_desugar_blocks_def, venomInstTheory.fn_insts_blocks_def,
          get_invoke_targets_def]
  >> gen_tac >> rpt gen_tac >>
     gvs[dret_desugar_blocks_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >>
     imp_res_tac dret_desugar_insts_invoke_targets >>
     first_x_assum drule >> strip_tac >>
     gvs[venomInstTheory.fn_insts_blocks_def, dret_get_invoke_targets_append]
QED

Theorem dret_desugar_function_invoke_targets:
  dret_desugar_function target s fn = SOME (fn',s') ==>
  MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  simp[dret_desugar_function_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac dret_desugar_blocks_invoke_targets >>
  gvs[fcg_scan_function_def, venomInstTheory.fn_insts_def, venomInstTheory.fn_insts_blocks_def,
      get_invoke_targets_def, venomInstTheory.mk_inst_def]
QED

val _ = export_theory();
