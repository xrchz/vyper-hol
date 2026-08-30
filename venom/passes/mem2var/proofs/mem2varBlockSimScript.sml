Theory mem2varBlockSim
Ancestors
  mem2varBlockSimHelpers
  mem2varDefs mem2varProofs
  passSharedTransfer passSharedField
  venomExecSemantics venomState venomWf
  venomInst venomInstProofs venomExecProofs
  stateEquiv
  passSimulationDefs passSimulationProps
  instIdxIndep analysisSimDefs
  dfgDefs dfgCorrectnessProof
  basePtrDefs basePtrProofs
  pointerConfinedDefs memLocDefs
  venomEffects venomMemDefs venomMemProps venomMemProofs
  finite_map list rich_list pred_set pair
Libs
  HolKernel boolLib bossLib BasicProvers dep_rewrite markerLib

Theorem m2v_per_block_sim_at[local]:
  !n fn bb fuel ctx s1 s2.
    n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    wf_function fn /\
    fn_inst_wf fn /\
    ssa_form fn /\
    m2v_promotable_wf fn /\
    m2v_fresh_names_disjoint fn /\
    m2v_promo_sizes_bounded fn /\
    m2v_return_size_bounded fn /\
    alloca_pointer_confined fn /\
    all_mem_via_pointer fn (alloca_roots fn) /\
    alloca_inv s1 /\
    alloca_bridge fn s1 /\
    s1.vs_alloca_next < dimword (:256) /\
    m2v_nonpromoted_access_safe fn s1 /\
    MEM bb fn.fn_blocks /\
    bb_well_formed bb /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> RETFMP) bb.bb_instructions /\
    EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
    s1.vs_inst_idx <= LENGTH bb.bb_instructions /\
    s2.vs_inst_idx = s1.vs_inst_idx /\
    m2v_inv_noix fn s1 s2 /\
    m2v_non32_ok fn s1 s2 /\
    m2v_ao_undef_sync fn s1 s2 /\
    m2v_fresh_undef fn s1 /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    m2v_pvars_set fn bb s1.vs_inst_idx s2 /\
    (* m2v_nonpromoted_access_safe preservation *)
    (!i fuel' ctx' s s'. i < LENGTH bb.bb_instructions /\
      m2v_nonpromoted_access_safe fn s /\
      step_inst fuel' ctx' (EL i bb.bb_instructions) s = OK s' ==>
      m2v_nonpromoted_access_safe fn s') /\
    (* vs_alloca_next preservation per-step *)
    (!inst fuel' ctx' s s'. MEM inst (fn_insts fn) /\
      s.vs_alloca_next < dimword (:256) /\
      step_inst fuel' ctx' inst s = OK s' ==>
      s'.vs_alloca_next < dimword (:256)) ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
                (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
                (\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                         m2v_ao_undef_sync fn s1 s2 /\
                         s1.vs_alloca_next = s2.vs_alloca_next)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (m2v_bt fn bb) s2)
Proof
  Induct_on `n` >> rpt strip_tac
  (* Base: n=0, idx=LENGTH → get_instruction NONE → Error *)
  >- (DISJ1_TAC >>
      ONCE_REWRITE_TAC[exec_block_def] >>
      simp[get_instruction_def])
  (* Step: n = SUC n', idx < LENGTH *)
  >> suspend "step"
QED
Resume m2v_per_block_sim_at[step]:
  SUBGOAL_THEN ``s1.vs_inst_idx < LENGTH bb.bb_instructions`` assume_tac
  >- decide_tac >>
  qabbrev_tac `idx = s1.vs_inst_idx` >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "terminal"
  >> SUBGOAL_THEN ``idx < LENGTH bb.bb_instructions - 1`` assume_tac
  >- (irule nonterm_not_last >> simp[Abbr `inst`]) >>
  suspend "nonterminal"
QED
Resume m2v_per_block_sim_at[terminal]:
  (* idx = last index *)
  SUBGOAL_THEN ``idx = PRE (LENGTH bb.bb_instructions)`` assume_tac
  >- (qpat_x_assum `bb_well_formed bb` mp_tac >>
      PURE_REWRITE_TAC[bb_well_formed_def] >> strip_tac >>
      qpat_x_assum `!i. i < LENGTH bb.bb_instructions /\ _ ==> _`
        (qspec_then `idx` mp_tac) >>
      impl_tac
      >- (conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
          qpat_x_assum `Abbrev (inst = bb.bb_instructions❲idx❳)`
            (fn th => SUBST1_TAC
              (GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th))) >>
          FIRST_ASSUM ACCEPT_TAC) >>
      simp[]) >>
  (* inst = LAST bb.bb_instructions *)
  SUBGOAL_THEN ``inst = LAST bb.bb_instructions`` assume_tac
  >- (gvs[Abbr `inst`] >>
      `bb.bb_instructions <> []` by (gvs[bb_well_formed_def] >>
        Cases_on `bb.bb_instructions` >> gvs[]) >>
      simp[LAST_EL]) >>
  (* Case split on FIND (promoted vs non-promoted) *)
  Cases_on `FIND (\(ao,_,_). MEM (Var ao) inst.inst_operands)
            (m2v_promo_list fn)`
  (* FIND=NONE: instruction unchanged *)
  >- (SUBGOAL_THEN ``m2v_rewrite_inst fn inst = [inst]`` assume_tac
      >- simp[m2v_rewrite_inst_def] >>
      suspend "find_none")
  (* FIND=SOME: promoted terminal (RETURN), 2-step simulation *)
  >> suspend "find_some"
QED
Resume m2v_per_block_sim_at[find_none]:
  mp_tac (Q.SPECL [
    `\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
             m2v_ao_undef_sync fn s1 s2 /\
             s1.vs_alloca_next = s2.vs_alloca_next`,
    `inst`, `inst`, `bb`, `m2v_bt fn bb`, `s1`, `s2`, `fuel`, `ctx`]
    exec_block_terminal_lift) >>
  impl_tac
  >- (rpt conj_tac
      (* get_instruction original *)
      >- gvs[get_instruction_def, Abbr `inst`, Abbr `idx`]
      (* get_instruction transformed *)
      >- suspend "find_none_get_inst"
      (* is_terminator (x2) *)
      >- simp[] >- simp[]
      (* R preserves vs_halted *)
      >- (rpt strip_tac >> gvs[m2v_inv_noix_def])
      (* Error \/ lift_result for step_inst *)
      >> suspend "find_none_step_sim")
  >> simp[]
QED
Resume m2v_per_block_sim_at[find_none_get_inst]:
  mp_tac (Q.SPECL [`fn`,`bb`,`0`] m2v_bt_get_inst_term) >>
  simp[] >> gvs[Abbr `idx`, arithmeticTheory.PRE_SUB1]
QED
Resume m2v_per_block_sim_at[find_none_step_sim]:
  (* Derive MEM facts shared by both branches *)
  SUBGOAL_THEN ``MEM inst (fn_insts fn)`` assume_tac
  >- (irule MEM_fn_insts >> qexists `bb` >> simp[MEM_EL] >>
      qexists `PRE (LENGTH bb.bb_instructions)` >>
      `bb.bb_instructions <> []` by
        (qpat_x_assum `bb_well_formed bb` mp_tac >>
         simp[bb_well_formed_def] >>
         Cases_on `bb.bb_instructions` >> simp[]) >>
      gvs[Abbr `inst`, Abbr `idx`, LAST_EL]) >>
  SUBGOAL_THEN ``MEM inst bb.bb_instructions`` assume_tac
  >- (`bb.bb_instructions <> []` by
        (qpat_x_assum `bb_well_formed bb` mp_tac >>
         simp[bb_well_formed_def] >>
         Cases_on `bb.bb_instructions` >> simp[]) >>
      metis_tac[MEM_LAST_NOT_NIL]) >>
  `inst_wf inst` by (
    drule_all fn_inst_wf_every_bb >> simp[EVERY_MEM] >>
    disch_then drule >> simp[]) >>
  Cases_on `inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT`
  (* RETURN/REVERT: use m2v_step_return_revert_find_none *)
  >- (mp_tac (Q.SPECL [`fn`,`bb`,`inst`,`s1`,`s2`,`fuel`,`ctx`]
        m2v_step_return_revert_find_none) >> simp[])
  (* Other terminators: use m2v_step_easy_terminator_full *)
  >> DISJ2_TAC >>
  mp_tac (Q.SPECL [`fn`,`inst`,`s1`,`s2`,`fuel`,`ctx`]
    m2v_step_easy_terminator_full) >>
  (impl_tac >- gvs[EVERY_EL, Abbr `inst`]) >> simp[]
QED
Resume m2v_per_block_sim_at[find_some]:
  PairCases_on `x` >> rename1 `SOME (ao, pvar, sz)` >>
  (* Establish MEM facts while inst abbreviation is live *)
  `MEM inst bb.bb_instructions` by (
    qunabbrev_tac `inst` >> irule EL_MEM >> simp[]) >>
  `MEM inst (fn_insts fn)` by (
    irule MEM_fn_insts >> qexists `bb` >> simp[]) >>
  `inst.inst_opcode = RETURN` by (
    drule_all promo_find_inst_opcode >> strip_tac >>
    gvs[is_terminator_def]) >>
  (* Remove inst=LAST equation NOW, before any gvs[] can use it *)
  qpat_x_assum `inst = LAST _` kall_tac >>
  (* Now safe to use gvs[] freely *)
  imp_res_tac FIND_MEM >> imp_res_tac FIND_P >> gvs[] >>
  `sz = 32` by (
    qpat_x_assum `m2v_promo_sizes_bounded _`
      (strip_assume_tac o REWRITE_RULE [m2v_promo_sizes_bounded_def]) >>
    first_x_assum drule >> simp[]) >> gvs[] >>
  (* Derive operands = [Var ao; Lit n] with w2n n <= 32 *)
  `?n. inst.inst_operands = [Var ao; Lit n] /\ w2n n <= 32` by (
    qpat_x_assum `m2v_return_size_bounded _`
      (strip_assume_tac o REWRITE_RULE [m2v_return_size_bounded_def]) >>
    first_x_assum (qspecl_then [`bb`,`inst`,`ao`,`pvar`,`32`] mp_tac) >>
    simp[]) >> gvs[] >>
  (* Promoted rewrite: RETURN → [MSTORE; RETURN] *)
  `m2v_promote_inst pvar ao 32 inst =
    [<|inst_id := inst.inst_id; inst_opcode := MSTORE;
       inst_operands := [Var ao; Var pvar]; inst_outputs := []|>; inst]`
    by simp[m2v_promote_inst_def, LET_THM] >>
  qmatch_asmsub_abbrev_tac `_ = [store_inst; _]` >>
  `m2v_rewrite_inst fn inst = [store_inst; inst]` by
    simp[m2v_rewrite_inst_def] >>
  (* Derive pvar IS_SOME via pvars_set *)
  `IS_SOME (lookup_var pvar s2)` by (
    mp_tac (Q.SPECL [`fn`,`bb`,`PRE (LENGTH bb.bb_instructions)`,`s2`,
                      `ao`,`pvar`] m2v_pvars_set_use_is_some) >>
    (impl_tac >- (simp[] >> gvs[Abbr `inst`])) >>
    simp[]) >>
  (* Step 1: ao lookup agrees *)
  `ao NOTIN m2v_fresh_vars fn` by (
    irule m2v_promo_list_ao_not_fresh >> metis_tac[]) >>
  `lookup_var ao s2 = lookup_var ao s1` by
    gvs[m2v_inv_noix_def] >>
  (* Step 2: Case split on ao being defined *)
  Cases_on `lookup_var ao s1`
  >- (DISJ1_TAC >> ONCE_REWRITE_TAC[exec_block_def] >>
      simp[get_instruction_def, Abbr `inst`] >>
      simp[step_inst_non_invoke, step_inst_base_def, eval_operand_def]) >>
  rename1 `lookup_var ao s1 = SOME addr_val` >>
  (* Step 3: sync clause gives pvar value *)
  `lookup_var pvar s2 = SOME (mload (w2n addr_val) s1)` by (
    qpat_x_assum `m2v_inv_noix _ _ _`
      (strip_assume_tac o REWRITE_RULE [m2v_inv_noix_def]) >>
    first_x_assum drule >> simp[]) >>
  (* Step 4: derive LAST = inst *)
  `LAST bb.bb_instructions = inst` by (
    `bb.bb_instructions <> []` by
      (gvs[bb_well_formed_def] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
    gvs[Abbr `inst`, LAST_EL]) >>
  (* Step 5: MSTORE step on s2 *)
  qabbrev_tac `pval = mload (w2n addr_val) s1` >>
  `step_inst fuel ctx store_inst s2 =
     OK (mstore (w2n addr_val) pval s2)` by (
    simp[step_inst_non_invoke, Abbr `store_inst`, step_inst_base_def,
         exec_write2_def, eval_operand_def, Abbr `pval`]) >>
  (* Step 6: Apply exec_block_1to2_terminal_lift *)
  mp_tac (Q.SPECL [
    `\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
             m2v_ao_undef_sync fn s1 s2 /\
             s1.vs_alloca_next = s2.vs_alloca_next`,
    `inst`, `store_inst`, `inst`, `bb`, `m2v_bt fn bb`,
    `s1`, `s2`, `fuel`, `ctx`,
    `mstore (w2n (addr_val:256 word)) pval s2`] exec_block_1to2_terminal_lift) >>
  impl_tac >> suspend "lift_impl"
QED
Resume m2v_per_block_sim_at[lift_impl]:
  RESUME_TAC >> TRY (disch_then ACCEPT_TAC >> NO_TAC) >>
  (* get_instruction original *)
  conj_tac >- (simp[get_instruction_def] >>
               qunabbrev_tac `inst` >> simp[]) >>
  (* get_instruction j=0 *)
  conj_tac >- (
    mp_tac (Q.SPECL [`fn`,`bb`,`0`] m2v_bt_get_inst_pre) >> simp[]) >>
  (* get_instruction j=1 *)
  conj_tac >- (
    once_rewrite_tac [arithmeticTheory.ADD1] >>
    mp_tac (Q.SPECL [`fn`,`bb`,`1`] m2v_bt_get_inst_pre) >> simp[]) >>
  (* is_terminator + store_inst *)
  simp[is_terminator_def, Abbr `store_inst`] >>
  (* halted agreement *)
  conj_tac >- (rpt strip_tac >> gvs[m2v_inv_noix_def]) >>
  (* RETURN simulation *)
  DISJ2_TAC >>
  simp[step_inst_non_invoke, step_inst_base_def,
       eval_operand_def, mstore_preserves, lookup_var_mstore_idx,
       LET_THM] >>
  DEP_ONCE_REWRITE_TAC [return_data_mstore_roundtrip] >>
  simp[Abbr `pval`, lift_result_def] >>
  (* invariant preservation: inv_noix *)
  conj_tac
  >- (MATCH_MP_TAC m2v_inv_noix_halt_state >>
      MATCH_MP_TAC m2v_inv_noix_set_returndata >>
      MATCH_MP_TAC m2v_inv_noix_update_idx_s2 >>
      MATCH_MP_TAC m2v_inv_noix_mstore_s2_only >>
      metis_tac[]) >>
  (* invariant preservation: non32_ok *)
  conj_tac
  >- (MATCH_MP_TAC m2v_non32_ok_halt_state >>
      MATCH_MP_TAC m2v_non32_ok_set_returndata >>
      MATCH_MP_TAC m2v_non32_ok_update_idx_s2 >>
      MATCH_MP_TAC m2v_non32_ok_mstore >>
      metis_tac[]) >>
  (* invariant preservation: ao_undef_sync *)
  conj_tac
  >- (MATCH_MP_TAC m2v_ao_undef_sync_frame >>
      qexistsl [`s1`, `s2`] >>
      simp[halt_state_def, set_returndata_def, mstore_def,
           lookup_var_def, LET_THM]) >>
  (* invariant preservation: nao *)
  simp[nao_halt_revert] >>
  simp[mstore_preserves] >>
  `s1.vs_alloca_next = s2.vs_alloca_next` by gvs[m2v_inv_noix_def] >>
  simp[LENGTH_mstore_eq] >>
  `?ainst. MEM ainst (fn_insts fn) /\ ainst.inst_opcode = ALLOCA /\
           ainst.inst_outputs = [ao]` by metis_tac[m2v_promo_list_is_alloca] >>
  `FLOOKUP s1.vs_allocas ainst.inst_id = SOME (w2n addr_val, 32)` by (
    qpat_x_assum `m2v_inv_noix _ _ _`
      (strip_assume_tac o REWRITE_RULE [m2v_inv_noix_def]) >>
    first_x_assum (qspecl_then [`ao`,`pvar`,`32`,`ainst`] mp_tac) >>
    simp[]) >>
  `w2n addr_val + 32 <= s1.vs_alloca_next` by (
    qpat_x_assum `alloca_inv _`
      (strip_assume_tac o REWRITE_RULE [alloca_inv_def]) >>
    qpat_x_assum `alloca_next_valid _`
      (strip_assume_tac o REWRITE_RULE [alloca_next_valid_def]) >>
    first_x_assum (qspecl_then [`ainst.inst_id`,`w2n addr_val`,`32`] mp_tac) >>
    simp[]) >>
  simp[arithmeticTheory.MAX_DEF]
QED
Resume m2v_per_block_sim_at[nonterminal]:
  mp_tac (Q.SPECL
    [`\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
              m2v_ao_undef_sync fn s1 s2 /\
              s1.vs_alloca_next = s2.vs_alloca_next`,
     `\s1 s2. m2v_inv_noix fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
              m2v_ao_undef_sync fn s1 s2 /\
              s1.vs_alloca_next = s2.vs_alloca_next`,
    `EL idx bb.bb_instructions`,
    `HD (m2v_rewrite_inst fn (EL idx bb.bb_instructions))`,
    `bb`, `m2v_bt fn bb`, `fuel`, `ctx`, `s1`, `s2`]
    m2v_exec_block_step_chain) >>
  (impl_tac >- (
    rpt conj_tac
    (* source index is in range *)
    >- (qpat_x_assum `Abbrev (idx = s1.vs_inst_idx)`
          (fn th => SUBST1_TAC
            (GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th))) >>
        FIRST_ASSUM ACCEPT_TAC)
    (* target and source indices agree *)
    >- (qpat_x_assum `Abbrev (idx = s1.vs_inst_idx)`
          (fn th => SUBST1_TAC
            (GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th))) >>
        FIRST_ASSUM ACCEPT_TAC)
    (* selected source instruction *)
    >- (qpat_x_assum `Abbrev (idx = s1.vs_inst_idx)`
          (fn th => SUBST1_TAC
            (GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th))) >>
        REFL_TAC)
    (* get_instruction on transformed block *)
    >- (qpat_x_assum `Abbrev (idx = s1.vs_inst_idx)`
          (fn th => SUBST1_TAC
            (GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th))) >>
        irule m2v_bt_get_inst_nonterm >> simp[])
    (* source instruction is non-terminal *)
    >- (qpat_x_assum `Abbrev (inst = bb.bb_instructions❲idx❳)`
          (fn th => SUBST1_TAC
            (GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th))) >>
        FIRST_ASSUM ACCEPT_TAC)
    (* inst2 is non-terminal *)
    >- (irule m2v_rewrite_nonterm >> simp[])
    (* Step-level simulation: Error ∨ lift_result *)
    >- suspend "step_sim"
    (* IH continuation *)
    >> suspend "ih_cont")) >>
  simp[]
QED
Resume m2v_per_block_sim_at[step_sim]:
  (* Derive no-invoke for this instruction *)
  SUBGOAL_THEN ``inst.inst_opcode <> INVOKE`` assume_tac
  >- (qpat_x_assum `Abbrev (inst = bb.bb_instructions❲idx❳)`
        (fn th => SUBST1_TAC
          (REWRITE_RULE [markerTheory.Abbrev_def] th)) >>
      qpat_x_assum `EVERY (λi. i.inst_opcode <> INVOKE) bb.bb_instructions`
        (fn th => irule
          (SIMP_RULE (srw_ss()) []
            (Q.SPEC `idx` (REWRITE_RULE [EVERY_EL] th)))) >>
      FIRST_ASSUM ACCEPT_TAC) >>
  Cases_on `step_inst fuel ctx inst s1`
  (* OK: dispatch handles all opcodes + non32_ok preservation *)
  >- suspend "ok_case"
  (* Halt: impossible — step_inst_base can't halt for non-terminators *)
  >- (gvs[step_inst_non_invoke] >>
      imp_res_tac step_inst_base_no_halt >> gvs[])
  (* Abort: both sides abort identically *)
  >- suspend "abort"
  (* IntRet: impossible — step_inst_base can't intret for non-terminators *)
  >- (gvs[step_inst_non_invoke] >>
      imp_res_tac step_inst_base_no_intret >> gvs[])
  (* Error *)
  >> simp[]
QED
Resume m2v_per_block_sim_at[ok_case]:
  DISJ2_TAC >>
  SUBGOAL_THEN ``MEM (EL idx bb.bb_instructions) (fn_insts fn)`` assume_tac
  >- (irule MEM_fn_insts >> qexists `bb` >>
      simp[MEM_EL] >> qexists `idx` >> simp[]) >>
  mp_tac (Q.SPECL [`fn`, `bb`, `idx`, `fuel`, `ctx`, `s1`, `s2`, `v`]
    m2v_nonterminal_step_dispatch) >>
  simp[Abbr `inst`] >>
  (disch_then strip_assume_tac) >>
  SUBGOAL_THEN ``m2v_non32_ok fn (v:venom_state) v2`` assume_tac
  >- (mp_tac (Q.SPECL [`fn`, `EL idx bb.bb_instructions`,
        `s2`, `v2`, `fuel`, `ctx`] m2v_non32_ok_preserved_step) >>
      (impl_tac >- (
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        qpat_x_assum `m2v_non32_ok _ _ _` mp_tac >>
        simp[m2v_non32_ok_def])) >>
      simp[m2v_non32_ok_def]) >>
  SUBGOAL_THEN ``m2v_ao_undef_sync fn (v:venom_state) v2`` assume_tac
  >- (mp_tac (Q.SPECL [`fn`, `bb`, `idx`, `fuel`, `ctx`,
        `s1`, `s2`, `v`, `v2`] m2v_ao_undef_sync_preserved_step) >>
      simp[]) >>
  (* nao preserved *)
  SUBGOAL_THEN ``v.vs_alloca_next = v2.vs_alloca_next`` assume_tac
  >- (mp_tac (Q.SPECL [`fn`, `bb`, `idx`, `fuel`, `ctx`,
        `s1`, `s2`, `v`, `v2`] nao_dispatch_preserved) >>
      simp[]) >>
  qpat_x_assum `step_inst _ _ (HD _) _ = OK _`
    (fn th => rewrite_tac[th]) >>
  simp[lift_result_def]
QED
Resume m2v_per_block_sim_at[abort]:
  DISJ2_TAC >>
  simp[lift_result_def] >>
  mp_tac (Q.SPECL [`fn`, `EL idx bb.bb_instructions`, `s1`, `s2`,
    `a`, `v`, `fuel`, `ctx`] m2v_nonterminal_abort_sim) >>
  simp[Abbr `inst`] >>
  (impl_tac >- (
    rpt conj_tac >>
    TRY (irule MEM_fn_insts >> qexists `bb` >> simp[MEM_EL] >>
         qexists `idx` >> simp[] >> NO_TAC) >>
    gvs[])) >>
  strip_tac >> simp[lift_result_def] >>
  suspend "abort_non32"
QED
Resume m2v_per_block_sim_at[abort_non32]:
  (* Both sides abort with same type a. Get base forms. *)
  `step_inst_base (EL idx bb.bb_instructions) s1 = Abort a v` by
    gvs[step_inst_non_invoke] >>
  `~is_terminator (HD (m2v_rewrite_inst fn
      (EL idx bb.bb_instructions))).inst_opcode` by
    (irule m2v_rewrite_nonterm >> simp[]) >>
  `(HD (m2v_rewrite_inst fn (EL idx bb.bb_instructions))).inst_opcode
     <> INVOKE` by (irule m2v_rewrite_not_invoke >> simp[]) >>
  `step_inst_base (HD (m2v_rewrite_inst fn (EL idx bb.bb_instructions)))
     s2 = Abort a s2'` by gvs[step_inst_non_invoke] >>
  (* Get concrete abort forms for both sides *)
  imp_res_tac step_inst_base_abort_form >>
  gvs[] >>
  imp_res_tac m2v_non32_ok_abort_state >>
  imp_res_tac m2v_ao_undef_sync_abort_state >>
  simp[nao_halt_revert]
QED
Resume m2v_per_block_sim_at[ih_cont]:
  rpt strip_tac >>
  qpat_x_assum `(λs1 s2. _) s1' s2'`
    (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  SUBGOAL_THEN
    ``~is_terminator (EL idx bb.bb_instructions).inst_opcode`` assume_tac
  >- (qpat_x_assum `Abbrev (inst = bb.bb_instructions❲idx❳)`
        (fn th => SUBST1_TAC
          (GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th))) >>
      FIRST_ASSUM ACCEPT_TAC) >>
  SUBGOAL_THEN ``MEM (EL idx bb.bb_instructions) (fn_insts fn)``
    assume_tac
  >- (irule MEM_fn_insts >> qexists `bb` >> simp[MEM_EL] >>
      qexists `idx` >> simp[]) >>
  SUBGOAL_THEN ``m2v_fresh_undef fn s1'`` assume_tac
  >- (mp_tac (Q.SPECL [`fn`, `EL idx bb.bb_instructions`,
        `fuel`, `ctx`, `s1`, `s1'`] m2v_fresh_undef_preserved_step) >>
      simp[]) >>
  (* Derive pvars_set(SUC idx) from step_inst on s2 side *)
  SUBGOAL_THEN ``m2v_pvars_set fn bb (SUC idx) s2'`` assume_tac
  >- (mp_tac (Q.SPECL [`fn`, `bb`, `idx`, `fuel`, `ctx`, `s2`, `s2'`]
        m2v_pvars_set_after_dispatch) >>
      simp[]) >>
  (* Derive ao_undef_sync preserved through step *)
  SUBGOAL_THEN ``m2v_ao_undef_sync fn s1' s2'`` assume_tac
  >- (mp_tac (Q.SPECL [`fn`, `bb`, `idx`, `fuel`, `ctx`,
        `s1`, `s2`, `s1'`, `s2'`] m2v_ao_undef_sync_preserved_step) >>
      simp[]) >>
  (* Apply IH *)
  last_x_assum (qspecl_then [`fn`, `bb`, `fuel`, `ctx`,
    `s1' with vs_inst_idx := SUC idx`,
    `s2' with vs_inst_idx := SUC idx`] mp_tac) >>
  simp[] >>
  SUBGOAL_THEN ``alloca_inv s1'`` assume_tac
  >- metis_tac[alloca_inv_step_inst_proof] >>
  (* Derive alloca_bridge preserved through step *)
  SUBGOAL_THEN ``alloca_bridge fn s1'`` assume_tac
  >- (mp_tac (Q.SPECL [`fn`, `fuel`, `ctx`, `EL idx bb.bb_instructions`,
        `s1`, `s1'`] alloca_bridge_step) >>
      (impl_tac >- (gvs[EVERY_EL])) >> simp[]) >>
  (* Derive vs_alloca_next preserved *)
  SUBGOAL_THEN ``s1'.vs_alloca_next < dimword (:256)`` assume_tac
  >- (qpat_x_assum `!inst fuel' ctx' s s'. MEM _ _ /\ _.vs_alloca_next < _ /\ _ ==> _`
        (qspecl_then [`EL idx bb.bb_instructions`,`fuel`,`ctx`,`s1`,`s1'`] mp_tac) >>
      simp[] >> disch_then irule >>
      irule MEM_fn_insts >> qexists `bb` >> simp[MEM_EL]) >>
  (* Derive m2v_nonpromoted_access_safe for s1' from step-preservation *)
  SUBGOAL_THEN ``m2v_nonpromoted_access_safe fn s1'`` assume_tac
  >- (qpat_assum `!i fuel' ctx' s s'. _ /\ m2v_nonpromoted_access_safe _ _ /\ _ ==>
        m2v_nonpromoted_access_safe _ _`
        (qspecl_then [`idx`,`fuel`,`ctx`,`s1`,`s1'`] mp_tac) >>
      simp[]) >>
  (impl_tac >- (
    simp[vs_inst_idx_update_transparent_export] >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    FIRST
      [(irule m2v_inv_noix_update_idx >> simp[]),
       (MATCH_MP_TAC m2v_non32_ok_update_idx >> simp[]),
       (irule m2v_ao_undef_sync_update_idx >> simp[]),
       (irule m2v_pvars_set_update_idx >> simp[]),
       (irule (Q.SPECL [`fn`, `bb`, `idx`, `fuel`, `ctx`, `s1`, `s2`,
                         `s1'`, `s2'`] nao_dispatch_preserved) >>
        rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)])) >>
  simp[]
QED
Finalise m2v_per_block_sim_at
Theorem m2v_per_block_sim:
  !fn.
    wf_function fn /\
    fn_inst_wf fn /\
    ssa_form fn /\
    m2v_promotable_wf fn /\
    m2v_fresh_names_disjoint fn /\
    m2v_promo_sizes_bounded fn /\
    m2v_return_size_bounded fn /\
    alloca_pointer_confined fn /\
    all_mem_via_pointer fn (alloca_roots fn) /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE)
      bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> DRET)
      bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> RETFMP)
      bb.bb_instructions) fn.fn_blocks /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> MEMTOP)
      bb.bb_instructions) fn.fn_blocks ==>
    !bb. MEM bb fn.fn_blocks ==>
    !fuel ctx s1 s2.
      m2v_inv fn s1 s2 /\
      m2v_non32_ok fn s1 s2 /\
      m2v_ao_undef_sync fn s1 s2 /\
      m2v_fresh_undef fn s1 /\
      alloca_inv s1 /\
      alloca_bridge fn s1 /\
      s1.vs_alloca_next < dimword (:256) /\
      m2v_nonpromoted_access_safe fn s1 /\
      s1.vs_alloca_next = s2.vs_alloca_next /\
      m2v_pvars_set fn bb 0 s2 /\
      (* m2v_nonpromoted_access_safe preservation *)
      (!i fuel' ctx' s s'. i < LENGTH bb.bb_instructions /\
        m2v_nonpromoted_access_safe fn s /\
        step_inst fuel' ctx' (EL i bb.bb_instructions) s = OK s' ==>
        m2v_nonpromoted_access_safe fn s') /\
      (* vs_alloca_next preservation per-step *)
      (!inst fuel' ctx' s s'. MEM inst (fn_insts fn) /\
        s.vs_alloca_next < dimword (:256) /\
        step_inst fuel' ctx' inst s = OK s' ==>
        s'.vs_alloca_next < dimword (:256)) /\
      s1.vs_inst_idx = 0 ==>
      (?e. exec_block fuel ctx bb s1 = Error e) \/
      lift_result (\s1 s2. m2v_inv fn s1 s2 /\ m2v_non32_ok fn s1 s2 /\
                           m2v_ao_undef_sync fn s1 s2 /\
                           s1.vs_alloca_next = s2.vs_alloca_next)
                  (m2v_equiv (m2v_fresh_vars fn))
                  (m2v_equiv (m2v_fresh_vars fn))
        (exec_block fuel ctx bb s1)
        (exec_block fuel ctx (m2v_bt fn bb) s2)
Proof
  rpt strip_tac >>
  (* Bridge m2v_inv → m2v_inv_noix *)
  SUBGOAL_THEN ``m2v_inv_noix fn s1 s2`` assume_tac
  >- (irule m2v_inv_implies_noix >> simp[] >>
      conj_tac
      >- metis_tac[alloca_bridge_def]
      >> gvs[alloca_inv_def]) >>
  (* Get bb_well_formed from wf_function *)
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  (* Get EVERY no_invoke for this block *)
  `EVERY (\i. i.inst_opcode <> INVOKE)
    bb.bb_instructions` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> DRET)
    bb.bb_instructions` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> RETFMP)
    bb.bb_instructions` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> MEMTOP)
    bb.bb_instructions` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  (* Extract inst_idx agreement from m2v_inv *)
  `s2.vs_inst_idx = s1.vs_inst_idx` by gvs[m2v_inv_def, m2v_equiv_def] >>
  (* Apply m2v_per_block_sim_at — gives combined_R *)
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`,
    `fn`, `bb`, `fuel`, `ctx`, `s1`, `s2`]
    m2v_per_block_sim_at) >>
  (impl_tac >- (rpt conj_tac >> simp[] >> TRY (first_assum ACCEPT_TAC))) >>
  strip_tac
  >- simp[] >>
  (* Bridge combined_R to (m2v_inv /\ m2v_non32_ok /\ ao_undef_sync /\ nao) / m2v_equiv *)
  DISJ2_TAC >>
  irule lift_result_bridge >> simp[] >>
  metis_tac[venomExecProofsTheory.exec_block_OK_inst_idx_0]
QED
