(*
 * Parameterized Execution Equivalence — Proofs
 *
 * TOP-LEVEL:
 *   step_inst_preserves_R_proof                          — master theorem
 *   exec_block_preserves_R_proof                          — mutual: exec_block + run_blocks
 *   state_equiv_execution_equiv_valid_state_rel_proof    — instantiation
 *)

Theory execEquivParamProofs
Ancestors
  execEquivParamHelpers execEquivParamHelpers2 execEquivParamBase
  execEquivParamDefs passSimulationDefs stateEquivProps execEquivProps
  stateEquiv venomInst venomExecSemantics venomState
  finite_map list rich_list option pred_set

(* Helper: flatten the inner ∀s1 s2 in the operand agreement assumption.
   The original assumption has ∀s1 s2. R_ok s1 s2 ⇒ ... which shadows free s1/s2.
   This version takes the free s1/s2 directly, making metis_tac usable. *)
Theorem operand_agreement_flat:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   fn bb inst x s1 s2.
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM (Var x) inst.inst_operands /\ R_ok s1 s2
    ==> lookup_var x s1 = lookup_var x s2
Proof
  rpt strip_tac >> first_x_assum drule >> disch_then drule >> simp[]
QED

(* Helper: EVERY weakening via list induction.
   Proves EVERY with PHI guard from a stronger condition that doesn't need
   the PHI guard. Avoids namespace collision with ∀s1 s2 inside the operand
   agreement assumption that breaks metis_tac. *)
Theorem EVERY_PHI_operand_agreement:
  !s1 s2 (l : instruction list).
    (!inst. MEM inst l /\ inst.inst_opcode = PHI ==>
      !x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2)
    ==>
    EVERY (\inst. inst.inst_opcode = PHI ==>
      !x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) l
Proof
  Induct_on `l` >> rw[] >> Cases_on `h.inst_opcode = PHI` >> rw[] >> metis_tac[]
QED

(* Bridge lemma: from universal operand agreement (all blocks, all instructions)
   to the EVERY condition needed by eval_phis_preserves_R_ok (PHI instructions only).
   Trivial weakening: instantiate ∀bb to the specific block, guard to just PHI. *)
Theorem operand_agreement_EVERY:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn bb s1 s2.
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
    EVERY (\inst. inst.inst_opcode = PHI ==>
      !x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2)
      bb.bb_instructions
Proof
  rpt strip_tac >> match_mp_tac EVERY_PHI_operand_agreement >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`bb`,`inst`,`x`] mp_tac) >> simp[]
QED


(* Master theorem: step_inst preserves any valid (R_ok, R_term) pair.
   Non-INVOKE: step_inst_non_invoke reduces to step_inst_base, dispatch to helpers.
   INVOKE: identical callee state (setup_callee from R_ok + same args) →
   same run_blocks result → merge_callee_state + bind_outputs preserve R_ok. *)
Theorem step_inst_preserves_R_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fuel ctx inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE: both sides unfold to identical callee call *)
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [step_inst_def])) >>
    simp[Once step_inst_def] >>
    Cases_on `decode_invoke inst` >> gvs[lift_result_def] >>
    Cases_on `x` >> gvs[] >>
    rename1 `decode_invoke inst = SOME (callee_name, arg_ops)` >>
    `!x. MEM (Var x) arg_ops ==> MEM (Var x) inst.inst_operands` by
      (gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
    Cases_on `lookup_function callee_name ctx.ctx_functions` >>
    gvs[lift_result_def] >>
    rename1 `lookup_function _ _ = SOME callee_fn` >>
    `eval_operands arg_ops s1 = eval_operands arg_ops s2` by
      (irule vsr_eval_operands >> simp[] >> metis_tac[]) >>
    gvs[] >>
    Cases_on `eval_operands arg_ops s2` >> gvs[lift_result_def] >>
    rename1 `eval_operands _ _ = SOME args` >>
    `setup_callee callee_fn args s1 = setup_callee callee_fn args s2` by
      (irule vsr_setup_callee_eq >> metis_tac[]) >>
    gvs[] >>
    Cases_on `setup_callee callee_fn args s2` >> gvs[lift_result_def] >>
    rename1 `setup_callee _ _ _ = SOME callee_s` >>
    (* Same callee state → same run_blocks result *)
    Cases_on `run_blocks fuel ctx callee_fn callee_s` >> gvs[lift_result_def]
    >- metis_tac[vsr_R_term_refl]
    >- metis_tac[vsr_R_term_refl]
    >- (
      (* IntRet: merge, optional FMP adoption, and output binding preserve R_ok. *)
      rename1 `run_blocks _ _ _ _ = IntRet vals callee_s'` >>
      sg `OPTREL R_ok
            (bind_outputs inst.inst_outputs vals.iret_values
              (adopt_return_fmp vals (merge_callee_state s1 callee_s')))
            (bind_outputs inst.inst_outputs vals.iret_values
              (adopt_return_fmp vals (merge_callee_state s2 callee_s')))`
      >- (`R_ok (merge_callee_state s1 callee_s')
                 (merge_callee_state s2 callee_s')` by
            (irule vsr_merge_callee_R_ok >> metis_tac[]) >>
          `R_ok (adopt_return_fmp vals (merge_callee_state s1 callee_s'))
                (adopt_return_fmp vals (merge_callee_state s2 callee_s'))` by
            (Cases_on `vals.iret_adopt_fmp` >>
             gvs[adopt_return_fmp_def] >>
             metis_tac[vsr_fmp_R_ok]) >>
          drule_all vsr_bind_outputs_R_ok >>
          disch_then
            (qspecl_then [`inst.inst_outputs`, `vals.iret_values`] mp_tac) >>
          simp[])
      >>
      gvs[optionTheory.OPTREL_def, lift_result_def])
  )
  >>
  (* Non-INVOKE: reduce to step_inst_base, dispatch to opcode helpers *)
  `step_inst fuel ctx inst s1 = step_inst_base inst s1 /\
   step_inst fuel ctx inst s2 = step_inst_base inst s2` by
    (conj_tac >> irule step_inst_non_invoke >> simp[]) >>
  gvs[] >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  FIRST [
    irule vsr_step_inst_pure2 >> simp[] >> metis_tac[],
    irule vsr_step_inst_pure1 >> simp[] >> metis_tac[],
    irule vsr_step_inst_pure3 >> simp[] >> metis_tac[],
    irule vsr_step_inst_read0 >> simp[] >> metis_tac[],
    irule vsr_step_inst_read1 >> simp[] >> metis_tac[],
    irule vsr_step_inst_extcodehash >> simp[] >> metis_tac[],
    irule vsr_step_inst_write2 >> simp[] >> metis_tac[],
    irule vsr_step_inst_terminator >> simp[] >> metis_tac[],
    irule vsr_step_inst_return >> simp[] >> metis_tac[],
    irule vsr_step_inst_revert >> simp[] >> metis_tac[],
    irule vsr_step_inst_control >> simp[] >> metis_tac[],
    irule vsr_step_inst_djmp >> simp[] >> metis_tac[],
    irule vsr_step_inst_ssa >> simp[] >> metis_tac[],
    irule vsr_step_inst_assert >> simp[] >> metis_tac[],
    irule vsr_step_inst_sha3 >> simp[] >> metis_tac[],
    irule vsr_step_inst_mcopy >> simp[] >> metis_tac[],
    irule vsr_step_inst_istore >> simp[] >> metis_tac[],
    irule vsr_step_inst_data_copy >> simp[] >> metis_tac[],
    irule vsr_step_inst_extcodecopy >> simp[] >> metis_tac[],
    irule vsr_step_inst_copy >> simp[] >> metis_tac[],
    irule vsr_step_inst_param >> simp[] >> metis_tac[],
    irule vsr_step_inst_ret >> simp[] >> metis_tac[],
    irule vsr_step_inst_log >> simp[] >> metis_tac[],
    irule vsr_step_inst_selfdestruct >> simp[] >> metis_tac[],
    irule vsr_step_inst_invalid >> simp[] >> metis_tac[],
    irule vsr_step_inst_ext_call >> simp[] >> metis_tac[],
    irule vsr_step_inst_delegatecall >> simp[] >> metis_tac[],
    irule vsr_step_inst_create >> simp[] >> metis_tac[],
    irule vsr_step_inst_alloca >> simp[] >> metis_tac[],
    irule vsr_step_inst_fmp_opcode >> simp[] >> metis_tac[],
    irule vsr_step_inst_dret >> simp[] >> metis_tac[],
    irule vsr_step_inst_retfmp >> simp[] >> metis_tac[]
  ]
QED

Theorem vsr_lift_ok_halted:
  !R_ok R_term v v'.
    valid_state_rel R_ok R_term /\ R_ok v v' ==>
    lift_result R_ok R_term R_term
      (if v.vs_halted then Halt v else OK v)
      (if v'.vs_halted then Halt v' else OK v')
Proof
  rpt strip_tac >>
  imp_res_tac vsr_R_ok_R_term >>
  imp_res_tac vsr_R_ok_fields >>
  Cases_on `v.vs_halted` >> gvs[lift_result_def]
QED

(* exec_block/run_blocks preserve R. Mutual induction via exec_block_ind.
   New exec_block is simpler (no INVOKE special case - step_inst handles it).
   Uses vs_inst_idx := SUC s.vs_inst_idx (not next_inst). *)

(* Generalized: exec_block preserves R with auxiliary invariant Q.
   Q tracks additional agreement (e.g., fresh variable agreement) that R_ok
   alone doesn't capture. Operand agreement uses R_ok AND Q; Q is preserved
   by non-terminator steps. *)
Theorem exec_block_same_preserves_RQ_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (Q : venom_state -> venom_state -> bool)
   bb fuel ctx s1 s2.
    valid_state_rel R_ok R_term /\
    R_ok s1 s2 /\ Q s1 s2 /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (!inst. MEM inst bb.bb_instructions ==>
            inst.inst_opcode <> INVOKE) /\
    (* Operand agreement using R_ok AND Q *)
    (!i s1' s2'. i < LENGTH bb.bb_instructions /\
       R_ok s1' s2' /\ Q s1' s2' /\
       s1'.vs_inst_idx = i /\ s2'.vs_inst_idx = i ==>
       !x. MEM (Var x) (EL i bb.bb_instructions).inst_operands ==>
           lookup_var x s1' = lookup_var x s2') /\
    (* Q preserved by non-terminator steps *)
    (!i s1' s2' v1 v2.
       i < LENGTH bb.bb_instructions /\
       ~is_terminator (EL i bb.bb_instructions).inst_opcode /\
       R_ok s1' s2' /\ Q s1' s2' /\
       s1'.vs_inst_idx = i /\ s2'.vs_inst_idx = i /\
       step_inst fuel ctx (EL i bb.bb_instructions) s1' = OK v1 /\
       step_inst fuel ctx (EL i bb.bb_instructions) s2' = OK v2 /\
       R_ok v1 v2 ==>
       Q (v1 with vs_inst_idx := SUC i)
         (v2 with vs_inst_idx := SUC i)) ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  ntac 6 (pop_assum mp_tac) >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
  gvs[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx`
  >- simp[lift_result_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `s2.vs_inst_idx < LENGTH bb.bb_instructions /\
   inst = EL s2.vs_inst_idx bb.bb_instructions` by
    fs[get_instruction_def] >>
  `!x. MEM (Var x) inst.inst_operands ==>
       lookup_var x s1 = lookup_var x s2` by
    (rpt strip_tac >> first_x_assum irule >> gvs[]) >>
  `lift_result R_ok R_term R_term (step_inst fuel ctx inst s1)
     (step_inst fuel ctx inst s2)` by
    (match_mp_tac step_inst_preserves_R_proof >> fs[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  fs[lift_result_def] >>
  IF_CASES_TAC >> fs[]
  >- (irule vsr_lift_ok_halted >> simp[])
  >>
  (* Substitute inst = EL ... so IH guard matches *)
  qpat_x_assum `inst = _` SUBST_ALL_TAC >>
  (* Apply IH: spec s'' := v, discharge step_inst guard *)
  qpat_x_assum `!s''. _ ==> !s2'. _ ==> _ ==> _ ==> _ ==>
    lift_result _ _ _ (exec_block _ _ _ _) (exec_block _ _ _ _)`
    (qspec_then `v` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qspec_then `v' with vs_inst_idx := SUC s2.vs_inst_idx` mp_tac) >>
  simp[] >>
  disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- metis_tac[]
  >- (irule vsr_inst_idx_R_ok >> metis_tac[])
QED

(* Helper: exec_block preserves R. By induction on the instruction list via
   run_defs_ind, using step_inst_preserves_R at each step. *)
Theorem exec_block_preserves_R_helper:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx bb s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (exec_block fuel ctx bb s1)
                                (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
  gvs[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[lift_result_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def] >> irule listTheory.EL_MEM >> simp[]) >>
  `lift_result R_ok R_term R_term (step_inst fuel ctx inst s1)
     (step_inst fuel ctx inst s2)` by
    (irule step_inst_preserves_R_proof >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[lift_result_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[lift_result_def]
  >- (`v.vs_halted <=> v'.vs_halted` by
        (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
      Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
      metis_tac[vsr_R_ok_R_term])
  >>
  first_x_assum irule >> irule vsr_inst_idx_R_ok >> simp[] >> metis_tac[]
QED
(* Helper: run_block (which wraps eval_phis + exec_block) preserves R.
   Handles the eval_phis layer internally so the main theorem doesn't need
   manual case splits on eval_phis results. *)
Theorem run_block_preserves_R_helper:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx bb s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `s1.vs_prev_bb = s2.vs_prev_bb` by (drule vsr_R_ok_prev_bb >> simp[]) >>
  `EVERY (λinst. inst.inst_opcode = PHI ⇒ ∀x. MEM (Var x) inst.inst_operands ⇒ lookup_var x s1 = lookup_var x s2) bb.bb_instructions` by
    (mp_tac (Q.SPECL [`R_ok`, `R_term`, `fn`, `bb`, `s1`, `s2`]
       operand_agreement_EVERY) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  ONCE_REWRITE_TAC[run_block_def] >> qspec_then `s1` assume_tac eval_phis_ok_or_error_defs >> qspec_then `s2` assume_tac eval_phis_ok_or_error_defs >>
  DISJ_CASES_TAC (Q.SPECL [`s1`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >-
    (DISJ_CASES_TAC (Q.SPECL [`s2`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >-
      (* Both OK *)
      (fs[] >> `R_ok s' s''` by (drule_all eval_phis_preserves_R_ok >> simp[]) >>
       `R_ok (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)
              (s'' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
         (drule_all vsr_inst_idx_R_ok >> simp[]) >>
       irule exec_block_preserves_R_helper >> metis_tac[]) >>
     (* s1 OK, s2 Error *)
     (fs[] >> qspecl_then [`R_ok`,`R_term`,`s1`,`s2`,`bb.bb_instructions`] mp_tac
        eval_phis_agreement >> simp[] >> metis_tac[])) >>
  (* s1 Error *)
  DISJ_CASES_TAC (Q.SPECL [`s2`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >-
    (* s1 Error, s2 OK *)
    (fs[] >> qspecl_then [`R_ok`,`R_term`,`s1`,`s2`,`bb.bb_instructions`] mp_tac
       eval_phis_error_agreement >> simp[] >> metis_tac[]) >>
  (* Both Error *)
  fs[lift_result_def]
QED

Theorem exec_block_preserves_R_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    (!fuel ctx bb s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (exec_block fuel ctx bb s1)
                                (exec_block fuel ctx bb s2)) /\
    (!fuel ctx s1 s2.
       R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_blocks fuel ctx fn s1)
                                (run_blocks fuel ctx fn s2))
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (rpt strip_tac >>
      irule exec_block_preserves_R_helper >> metis_tac[])
  >>
  Induct_on `fuel` >> rw[]
  >- (simp[run_blocks_def, lift_result_def]) >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[vsr_R_ok_current_bb] >>
  simp[] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks` >>
  simp[lift_result_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[FIND_MEM, lookup_block_def] >>
  `lift_result R_ok R_term R_term (run_block_entry fuel ctx bb s1)
                                  (run_block_entry fuel ctx bb s2)` by
    (irule run_block_preserves_R_helper >> metis_tac[]) >>
  Cases_on `run_block_entry fuel ctx bb s1` >>
  Cases_on `run_block_entry fuel ctx bb s2` >>
  gvs[AllCaseEqs(), lift_result_def] >>
  `v.vs_halted ⇔ v'.vs_halted` by
    (qspecl_then [`R_ok`,`R_term`,`v`,`v'`] mp_tac vsr_R_ok_halted >> simp[]) >>
  Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
  qspecl_then [`R_ok`,`R_term`,`v`,`v'`] mp_tac vsr_R_ok_R_term >> simp[]
QED
Theorem state_equiv_execution_equiv_valid_state_rel_proof:
  !vars. valid_state_rel (state_equiv vars) (execution_equiv vars)
Proof
  rw[valid_state_rel_def] >>
  fs[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def] >>
  rpt strip_tac >>
  simp[FLOOKUP_UPDATE, eval_operand_def, lookup_var_def] >>
  TRY (Cases_on `op` >> fs[eval_operand_def, lookup_var_def] >> NO_TAC) >>
  TRY (rw[] >> first_x_assum irule >> simp[] >> NO_TAC) >>
  metis_tac[]
QED

(* Generalized: R_ok vars can differ from R_term vars' when vars SUBSET vars' *)
Theorem valid_state_rel_mixed_proof:
  !vars vars'. vars SUBSET vars' ==>
    valid_state_rel (state_equiv vars) (execution_equiv vars')
Proof
  rw[valid_state_rel_def] >>
  fs[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def, SUBSET_DEF] >>
  rpt strip_tac >>
  simp[FLOOKUP_UPDATE, eval_operand_def, lookup_var_def] >>
  TRY (Cases_on `op` >> fs[eval_operand_def, lookup_var_def] >> NO_TAC) >>
  TRY (rw[] >> first_x_assum irule >> simp[] >> NO_TAC) >>
  metis_tac[]
QED
