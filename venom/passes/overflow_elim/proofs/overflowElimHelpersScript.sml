(*
 * Overflow Check Elimination — Proofs
 *
 * Uses the analysis_inst_simulates framework (like assert_elim):
 * 1. Extended DFG soundness for ADD/SUB/LT/GT Var-Var chains
 * 2. overflow_elim_sim: range + DFG chain → ASSERT operand nonzero
 * 3. overflow_elim_inst simulation under sound state
 * 4. range_analysis_pass_correct lifts to function level
 * 5. Compose with clear_nops_function_correct
 *
 * Reuses shared range-pass infrastructure from assertElimProofs:
 *   range_transfer_sound, range_sound_state_equiv,
 *   range_analysis_pass_correct, range_successor_obligation
 *)

Theory overflowElimHelpers
Ancestors
  overflowElimDefs assertElimProofs
  analysisSimDefs analysisSimProps
  passSimulationDefs passSimulationProps
  passSharedDefs passSharedProps
  stateEquiv stateEquivProps
  venomExecSemantics venomState venomInst venomWf
  venomInstProps venomExecProps
  execEquivParamProps
  rangeAnalysisDefs rangeEvalDefs valueRangeDefs
  variableRangeAnalysisProps rangeAnalysisProofs
  dfAnalyzeWidenDefs
  dfgDefs dfgAnalysisProps dfgSoundStep
  worklistDefs
  list finite_map
Libs
  BasicProvers

(* ================================================================
   Section 1: Extended DFG soundness for arithmetic chains
   ================================================================

   dfg_sound tracks ASSIGN, ISZERO, EQ, LT/GT/SLT/SGT (Var/Lit only).
   overflow_elim needs ADD/SUB and LT/GT for arbitrary operand mixes.

   eval_op_env evaluates an operand against a variable environment,
   handling Var, Lit, and Label uniformly. *)

(* eval_op_env, dfg_arith_sound, dfg_compare_full_sound are
   imported from dfgSoundStepTheory *)

(* Combined extended DFG soundness *)
Definition dfg_ext_sound_def:
  dfg_ext_sound dfg env <=>
    dfg_sound dfg env /\
    dfg_arith_sound dfg env /\
    dfg_compare_full_sound dfg env /\
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       vv IN FDOM env /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM env)
End

(* Metis-friendly FDOM↔FLOOKUP bridge (FLOOKUP_DEF uses conditionals
   which metis can't case-split on) *)
Theorem FDOM_FLOOKUP:
  !f x. x IN FDOM f <=> ?y. FLOOKUP f x = SOME y
Proof
  rw[FLOOKUP_DEF] >> eq_tac >> rw[]
QED

(* --- Preservation through fupdate --- *)

(* Helper: eval_op_env is stable under fupdate when the operand's
   variable (if Var) differs from the new key *)
Theorem eval_op_env_fupdate:
  !op env k nv.
    (!v. op = Var v ==> v <> k) ==>
    eval_op_env op (env |+ (k, nv)) = eval_op_env op env
Proof
  Cases >> simp[eval_op_env_def, FLOOKUP_UPDATE]
QED

(* Corollary: if k ∉ FDOM env and the var is in FDOM env, then var ≠ k *)
Theorem eval_op_env_fupdate_in_dom:
  !op env k nv.
    k NOTIN FDOM env /\
    (!v. op = Var v ==> v IN FDOM env) ==>
    eval_op_env op (env |+ (k, nv)) = eval_op_env op env
Proof
  rpt strip_tac >> irule eval_op_env_fupdate >>
  rpt strip_tac >> gvs[] >>
  CCONTR_TAC >> gvs[]
QED

(* Key helper: eval_op_env op env = SOME w implies eval_op_env is stable *)
Theorem eval_op_env_fupdate_from_some:
  !op env k nv w.
    eval_op_env op env = SOME w /\ k NOTIN FDOM env ==>
    eval_op_env op (env |+ (k, nv)) = SOME w
Proof
  Cases >> simp[eval_op_env_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  `s <> k` by (CCONTR_TAC >> gvs[] >> fs[FLOOKUP_DEF]) >>
  simp[]
QED

(* Generic fupdate preservation for DFG operand-based predicates.
   The proof pattern is: for v=k use the new-variable condition,
   for v∈FDOM env use the old predicate; in both cases
   eval_op_env is stable because SOME values can't come from k *)
Theorem dfg_arith_sound_fupdate:
  !dfg env k nv.
    dfg_arith_sound dfg env /\ k NOTIN FDOM env /\
    (!dinst op1 op2.
       dfg_get_def dfg k = SOME dinst /\
       (dinst.inst_opcode = ADD \/ dinst.inst_opcode = SUB) /\
       dinst.inst_operands = [op1; op2] /\
       (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
       ?w1 w2.
         eval_op_env op1 env = SOME w1 /\
         eval_op_env op2 env = SOME w2 /\
         nv = (if dinst.inst_opcode = ADD
               then word_add w1 w2
               else word_sub w1 w2)) ==>
    dfg_arith_sound dfg (env |+ (k, nv))
Proof
  simp[dfg_arith_sound_def, FDOM_FUPDATE, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = k` >> gvs[]
  (* v = k: new-variable condition already gave us w1, w2 *)
  >> (TRY (`v IN FDOM env` by metis_tac[]
           >> first_x_assum
                (qspecl_then [`v`, `inst`, `op1`, `op2`] mp_tac)
           >> simp[] >> strip_tac))
  >> metis_tac[eval_op_env_fupdate_from_some]
QED

Theorem dfg_compare_full_sound_fupdate:
  !dfg env k nv.
    dfg_compare_full_sound dfg env /\ k NOTIN FDOM env /\
    (!dinst op1 op2.
       dfg_get_def dfg k = SOME dinst /\
       (dinst.inst_opcode = LT \/ dinst.inst_opcode = GT) /\
       dinst.inst_operands = [op1; op2] /\
       (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
       ?w1 w2.
         eval_op_env op1 env = SOME w1 /\
         eval_op_env op2 env = SOME w2 /\
         nv = bool_to_word
               (if dinst.inst_opcode = LT
                then w2n w1 < w2n w2
                else w2n w1 > w2n w2)) ==>
    dfg_compare_full_sound dfg (env |+ (k, nv))
Proof
  simp[dfg_compare_full_sound_def, FDOM_FUPDATE, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `v = k` >> gvs[]
  >> (TRY (`v IN FDOM env` by metis_tac[]
           >> first_x_assum
                (qspecl_then [`v`, `inst`, `op1`, `op2`] mp_tac)
           >> simp[] >> strip_tac))
  >> metis_tac[eval_op_env_fupdate_from_some]
QED

(* Both predicates hold trivially on FEMPTY *)
Theorem dfg_arith_sound_fempty:
  !dfg. dfg_arith_sound dfg FEMPTY
Proof
  simp[dfg_arith_sound_def]
QED

Theorem dfg_compare_full_sound_fempty:
  !dfg. dfg_compare_full_sound dfg FEMPTY
Proof
  simp[dfg_compare_full_sound_def]
QED

Theorem dfg_ext_sound_fempty:
  !dfg. dfg_ext_sound dfg FEMPTY
Proof
  simp[dfg_ext_sound_def, dfg_sound_fempty,
       dfg_arith_sound_fempty, dfg_compare_full_sound_fempty]
QED

(* Fresh outputs of an untracked instruction preserve the extended arithmetic
   predicates: every tracked result and each of its variable operands remains
   in the unchanged part of the environment. *)
Theorem dfg_arith_sound_fresh_untracked_extension:
  !dfg env env'.
    dfg_arith_sound dfg env /\
    (!x. x IN FDOM env ==> FLOOKUP env' x = FLOOKUP env x) /\
    (!v dinst. dfg_get_def dfg v = SOME dinst /\
       v IN FDOM env' /\ dfg_tracked_opcode dinst.inst_opcode ==>
       v IN FDOM env) /\
    (!v dinst u. dfg_get_def dfg v = SOME dinst /\
       v IN FDOM env /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM env) ==>
    dfg_arith_sound dfg env'
Proof
  rpt strip_tac >> PURE_ONCE_REWRITE_TAC[dfg_arith_sound_def] >>
  rpt strip_tac >>
  `dfg_tracked_opcode inst.inst_opcode` by
    simp[dfg_tracked_opcode_def] >>
  `v IN FDOM env` by metis_tac[] >>
  `FLOOKUP env' v = FLOOKUP env v` by metis_tac[] >>
  `!u. MEM (Var u) [op1; op2] ==> u IN FDOM env` by metis_tac[] >>
  `eval_op_env op1 env' = eval_op_env op1 env` by
    (Cases_on `op1` >> gvs[eval_op_env_def]) >>
  `eval_op_env op2 env' = eval_op_env op2 env` by
    (Cases_on `op2` >> gvs[eval_op_env_def]) >>
  qpat_x_assum `dfg_arith_sound dfg env` mp_tac >>
  PURE_ONCE_REWRITE_TAC[dfg_arith_sound_def] >> strip_tac >>
  first_x_assum drule_all >> metis_tac[]
QED

Theorem dfg_compare_full_sound_fresh_untracked_extension:
  !dfg env env'.
    dfg_compare_full_sound dfg env /\
    (!x. x IN FDOM env ==> FLOOKUP env' x = FLOOKUP env x) /\
    (!v dinst. dfg_get_def dfg v = SOME dinst /\
       v IN FDOM env' /\ dfg_tracked_opcode dinst.inst_opcode ==>
       v IN FDOM env) /\
    (!v dinst u. dfg_get_def dfg v = SOME dinst /\
       v IN FDOM env /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM env) ==>
    dfg_compare_full_sound dfg env'
Proof
  rpt strip_tac >> PURE_ONCE_REWRITE_TAC[dfg_compare_full_sound_def] >>
  rpt strip_tac >>
  `dfg_tracked_opcode inst.inst_opcode` by
    simp[dfg_tracked_opcode_def] >>
  `v IN FDOM env` by metis_tac[] >>
  `FLOOKUP env' v = FLOOKUP env v` by metis_tac[] >>
  `!u. MEM (Var u) [op1; op2] ==> u IN FDOM env` by metis_tac[] >>
  `eval_op_env op1 env' = eval_op_env op1 env` by
    (Cases_on `op1` >> gvs[eval_op_env_def]) >>
  `eval_op_env op2 env' = eval_op_env op2 env` by
    (Cases_on `op2` >> gvs[eval_op_env_def]) >>
  qpat_x_assum `dfg_compare_full_sound dfg env` mp_tac >>
  PURE_ONCE_REWRITE_TAC[dfg_compare_full_sound_def] >> strip_tac >>
  first_x_assum drule_all >> metis_tac[]
QED

(* --- Preservation through step_inst --- *)

(* eval_op_env on vs_vars = eval_operand *)
(* eval_op_env_eval_operand imported from dfgSoundStepTheory *)

(* step_inst_base for ADD/SUB gives values matching eval_op_env *)
Theorem step_inst_base_arith_condition:
  !inst s s' out nv op1 op2.
    step_inst_base inst s = OK s' /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    inst.inst_operands = [op1; op2] /\
    inst.inst_outputs = [out] /\
    (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) /\
    s'.vs_vars = s.vs_vars |+ (out, nv) ==>
    ?w1 w2. eval_op_env op1 s.vs_vars = SOME w1 /\
            eval_op_env op2 s.vs_vars = SOME w2 /\
            nv = (if inst.inst_opcode = ADD
                  then word_add w1 w2 else word_sub w1 w2)
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def, exec_pure2_def] >>
  strip_tac >>
  Cases_on `op1` >> Cases_on `op2` >>
  fs[eval_op_env_def, eval_operand_def, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  gvs[update_var_def, venom_state_component_equality,
      FUPD11_SAME_KEY_AND_BASE]
QED

(* step_inst_base for LT/GT gives values matching eval_op_env *)
Theorem step_inst_base_compare_condition:
  !inst s s' out nv op1 op2.
    step_inst_base inst s = OK s' /\
    (inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
    inst.inst_operands = [op1; op2] /\
    inst.inst_outputs = [out] /\
    (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) /\
    s'.vs_vars = s.vs_vars |+ (out, nv) ==>
    ?w1 w2. eval_op_env op1 s.vs_vars = SOME w1 /\
            eval_op_env op2 s.vs_vars = SOME w2 /\
            nv = bool_to_word
                  (if inst.inst_opcode = LT
                   then w2n w1 < w2n w2
                   else w2n w1 > w2n w2)
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def, exec_pure2_def] >>
  strip_tac >>
  Cases_on `op1` >> Cases_on `op2` >>
  fs[eval_op_env_def, eval_operand_def, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  gvs[update_var_def, venom_state_component_equality,
      FUPD11_SAME_KEY_AND_BASE]
QED

(* Main step_inst preservation: compose dfg_sound_step_inst with fupdate lemmas *)
Theorem dfg_ext_sound_step_inst:
  !fn fuel ctx inst s s'.
    dfg_ext_sound (dfg_build_function fn) s.vs_vars /\
    step_inst fuel ctx inst s = OK s' /\
    MEM inst (fn_insts fn) /\ fn_inst_wf fn /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> i1 = i2) /\
    inst.inst_opcode <> INVOKE /\
    (!out. MEM out inst.inst_outputs ==> out NOTIN FDOM s.vs_vars) /\
    (!v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars) ==>
    dfg_ext_sound (dfg_build_function fn) s'.vs_vars
Proof
  rpt strip_tac >> fs[dfg_ext_sound_def] >>
  (* dfg_sound + closure: delegate to dfg_sound_step_inst *)
  `dfg_sound (dfg_build_function fn) s'.vs_vars /\
   (!v dinst u. dfg_get_def (dfg_build_function fn) v = SOME dinst /\
      v IN FDOM s'.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
      MEM (Var u) dinst.inst_operands ==> u IN FDOM s'.vs_vars)` by
    (mp_tac dfg_sound_step_inst >>
     disch_then (qspecl_then [`fn`, `fuel`, `ctx`, `inst`, `s`, `s'`]
       mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp[]) >>
  (* Resolve dfg_sound and closure conjuncts immediately *)
  simp[] >>
  (* arith + compare: case split on vars change *)
  Cases_on `is_terminator inst.inst_opcode`
  >- (`s'.vs_vars = s.vs_vars` by
        (`!x. lookup_var x s' = lookup_var x s` suffices_by
           (strip_tac >> fs[fmap_eq_flookup, lookup_var_def]) >>
         metis_tac[step_terminator_preserves_vars]) >>
      ASM_REWRITE_TAC[]) >>
  `step_inst_base inst s = OK s'` by (fs[step_inst_def] >> gvs[]) >>
  `inst_wf inst` by metis_tac[fn_insts_inst_wf] >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (`FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs` by
        (irule venomExecPropsTheory.step_inst_base_fdom >> simp[]) >>
      `!x. x IN FDOM s.vs_vars ==>
           FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x` by
        (rpt strip_tac >>
         `~MEM x inst.inst_outputs` by metis_tac[] >>
         `lookup_var x s' = lookup_var x s` by
           metis_tac[step_preserves_non_output_vars] >>
         fs[lookup_var_def]) >>
      `!v dinst. dfg_get_def (dfg_build_function fn) v = SOME dinst /\
         v IN FDOM s'.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode ==>
         v IN FDOM s.vs_vars` by
        (rpt strip_tac >> CCONTR_TAC >>
         `MEM v inst.inst_outputs` by
           (qpat_x_assum `v IN FDOM s'.vs_vars` mp_tac >>
            ASM_REWRITE_TAC[] >> simp[]) >>
         `MEM v dinst.inst_outputs /\ MEM dinst (fn_insts fn)` by
           metis_tac[dfg_build_function_correct] >>
         `dinst = inst` by metis_tac[] >>
         `~dfg_tracked_opcode BUMP` by simp[dfg_tracked_opcode_def] >>
         metis_tac[]) >>
      rpt conj_tac
      >- (mp_tac (Q.SPECL [`dfg_build_function fn`, `s.vs_vars`,
                            `s'.vs_vars`]
                           dfg_arith_sound_fresh_untracked_extension) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[])
      >- (mp_tac (Q.SPECL [`dfg_build_function fn`, `s.vs_vars`,
                            `s'.vs_vars`]
                           dfg_compare_full_sound_fresh_untracked_extension) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[])
      >- first_assum ACCEPT_TAC) >>
  Cases_on `?out. out NOTIN FDOM s.vs_vars /\ out IN FDOM s'.vs_vars`
  >- (fs[] >>
      `inst_wf inst` by metis_tac[fn_insts_inst_wf] >>
      `inst.inst_outputs = [out]` by
        (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
           step_inst_base_new_var_singleton) >>
         impl_tac >- (
           rpt conj_tac >>
           TRY (qpat_x_assum `step_inst_base inst s = OK s'` ACCEPT_TAC) >>
           TRY (qpat_x_assum `inst_wf inst` ACCEPT_TAC) >>
           TRY (qpat_x_assum `~is_terminator inst.inst_opcode` ACCEPT_TAC) >>
           TRY (qpat_x_assum `inst.inst_opcode <> BUMP` ACCEPT_TAC) >>
           TRY (qpat_x_assum `out NOTIN FDOM s.vs_vars` ACCEPT_TAC) >>
           TRY (qpat_x_assum `out IN FDOM s'.vs_vars` ACCEPT_TAC)) >>
         DISCH_THEN ACCEPT_TAC) >>
      `s'.vs_vars = s.vs_vars |+ (out, THE (FLOOKUP s'.vs_vars out))` by
        metis_tac[step_inst_base_vars_fupdate] >>
      qabbrev_tac `nv = THE (FLOOKUP s'.vs_vars out)` >>
      `!d. dfg_get_def (dfg_build_function fn) out = SOME d ==>
           d = inst` by
        (rpt strip_tac >> imp_res_tac dfg_build_function_correct >>
         metis_tac[MEM]) >>
      ASM_REWRITE_TAC[] >>
      (* Establish arith and compare fupdate conditions together *)
      `(!di op1' op2'.
         dfg_get_def (dfg_build_function fn) out = SOME di /\
         (di.inst_opcode = ADD \/ di.inst_opcode = SUB) /\
         di.inst_operands = [op1'; op2'] /\
         (!lbl. op1' <> Label lbl) /\ (!lbl. op2' <> Label lbl) ==>
         ?w1 w2. eval_op_env op1' s.vs_vars = SOME w1 /\
                 eval_op_env op2' s.vs_vars = SOME w2 /\
                 nv = (if di.inst_opcode = ADD
                       then word_add w1 w2 else word_sub w1 w2)) /\
       (!di op1' op2'.
         dfg_get_def (dfg_build_function fn) out = SOME di /\
         (di.inst_opcode = LT \/ di.inst_opcode = GT) /\
         di.inst_operands = [op1'; op2'] /\
         (!lbl. op1' <> Label lbl) /\ (!lbl. op2' <> Label lbl) ==>
         ?w1 w2. eval_op_env op1' s.vs_vars = SOME w1 /\
                 eval_op_env op2' s.vs_vars = SOME w2 /\
                 nv = bool_to_word
                       (if di.inst_opcode = LT
                        then w2n w1 < w2n w2
                        else w2n w1 > w2n w2))` by
        (conj_tac
         >- (rpt strip_tac >> `di = inst` by metis_tac[] >>
             pop_assum SUBST_ALL_TAC >>
             mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`, `nv`,
               `op1'`, `op2'`] step_inst_base_arith_condition) >>
             impl_tac >- simp[] >> simp[])
         >- (rpt strip_tac >> `di = inst` by metis_tac[] >>
             pop_assum SUBST_ALL_TAC >>
             mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`, `nv`,
               `op1'`, `op2'`] step_inst_base_compare_condition) >>
             impl_tac >- simp[] >> simp[])) >>
      fs[] >>
      conj_tac
      >- (irule dfg_arith_sound_fupdate >> simp[] >>
          rpt strip_tac >> `dinst = inst` by metis_tac[] >> gvs[])
      >- (irule dfg_compare_full_sound_fupdate >> simp[] >>
          rpt strip_tac >> `dinst = inst` by metis_tac[] >> gvs[]))
  >- (`s'.vs_vars = s.vs_vars` by metis_tac[step_inst_vars_unchanged] >>
      ASM_REWRITE_TAC[])
QED

(* dfg_ext_sound preserved through run_block *)
Theorem dfg_ext_sound_run_block:
  !fn bb fuel ctx s r.
    dfg_ext_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> i1 = i2) /\
    ALL_DISTINCT (fn_labels fn) /\ dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\ s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_ext_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt strip_tac >> fs[dfg_ext_sound_def] >>
  `dfg_sound (dfg_build_function fn) r.vs_vars /\
   (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
      vv IN FDOM r.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
      MEM (Var u) dinst.inst_operands ==> u IN FDOM r.vs_vars)` by
    (irule dfg_sound_run_block >> metis_tac[]) >>
  rpt conj_tac
  >- gvs[]
  >- (irule dfg_arith_sound_run_block >> metis_tac[])
  >- (irule dfg_compare_full_sound_run_block >> metis_tac[])
  >- gvs[]
QED

(* dfg_ext_sound stable under state_equiv {} *)
Theorem dfg_ext_sound_state_equiv:
  !dfg s1 s2. state_equiv {} s1 s2 /\
    dfg_ext_sound dfg s1.vs_vars ==>
    dfg_ext_sound dfg s2.vs_vars
Proof
  rw[dfg_ext_sound_def]
  >- metis_tac[dfg_sound_state_equiv, state_equiv_empty_vars_eq]
  >- (fs[dfg_arith_sound_def, eval_op_env_def] >> rpt strip_tac >>
      imp_res_tac state_equiv_empty_vars_eq >> gvs[])
  >- (fs[dfg_compare_full_sound_def, eval_op_env_def] >> rpt strip_tac >>
      imp_res_tac state_equiv_empty_vars_eq >> gvs[])
  >- (rpt strip_tac >>
      imp_res_tac state_equiv_empty_vars_eq >> gvs[] >>
      metis_tac[])
QED

(* ================================================================
   Section 2: The core arithmetic soundness argument
   ================================================================ *)

(* Helper: range_nonneg + in_range ==> non-negative word value *)
Theorem range_nonneg_in_range_nonneg_w2i:
  !r w. range_nonneg r /\ in_range r w ==> 0 <= w2i w /\ w2i w <= vr_hi r
Proof
  Cases_on `r` >> simp[range_nonneg_def, in_range_def, vr_hi_def] >>
  rpt strip_tac >> intLib.ARITH_TAC
QED

(* Helper: non-negative w2i implies w2n = Num(w2i) *)
Theorem nonneg_w2i_eq_w2n:
  !(w: 256 word). 0 <= w2i w ==> w2n w = Num (w2i w)
Proof
  rpt strip_tac >>
  Cases_on `word_msb w`
  >- (fs[integer_wordTheory.w2i_def] >>
      `w2n w < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
      intLib.ARITH_TAC)
  >- simp[integer_wordTheory.w2i_def]
QED

(* Helper: UINT256_MAX_int = dimword(:256) - 1 as integer *)
Theorem UINT256_MAX_int_eq:
  UINT256_MAX_int = &(dimword (:256)) - 1
Proof
  EVAL_TAC
QED

Theorem Num_UINT256_MAX_int:
  Num UINT256_MAX_int + 1 = dimword (:256)
Proof
  simp[UINT256_MAX_def, integer_wordTheory.UINT_MAX_def,
       wordsTheory.UINT_MAX_def, wordsTheory.dimword_def] >>
  simp[integerTheory.NUM_OF_INT, integerTheory.INT_SUB] >>
  `0 < 2n ** dimindex (:256)` by simp[] >> simp[]
QED

(* The add overflow argument:
   If x,y have nonneg ranges with hi(x)+hi(y) <= UINT256_MAX,
   then w2n(x+y) >= w2n(x), so lt(x+y, x) = 0w *)
Theorem add_no_overflow_lt_zero:
  !wx wy xr yr.
    range_nonneg xr /\ range_nonneg yr /\
    in_range xr wx /\ in_range yr wy /\
    vr_hi xr + vr_hi yr <= UINT256_MAX_int ==>
    bool_to_word (w2n (word_add wx wy) < w2n wx) = 0w
Proof
  rpt strip_tac >>
  imp_res_tac range_nonneg_in_range_nonneg_w2i >>
  `w2n wx = Num (w2i wx)` by metis_tac[nonneg_w2i_eq_w2n] >>
  `w2n wy = Num (w2i wy)` by metis_tac[nonneg_w2i_eq_w2n] >>
  `w2n wx + w2n wy < dimword (:256)` by
    (`0 <= vr_hi xr /\ 0 <= vr_hi yr` by
       (Cases_on `xr` >> Cases_on `yr` >>
        fs[range_nonneg_def, vr_hi_def] >> intLib.ARITH_TAC) >>
     `Num (w2i wx) + Num (w2i wy) <= Num (vr_hi xr + vr_hi yr)` by
       intLib.ARITH_TAC >>
     `Num (vr_hi xr + vr_hi yr) <= Num UINT256_MAX_int` by
       intLib.ARITH_TAC >>
     `Num UINT256_MAX_int < dimword (:256)` by
       (mp_tac Num_UINT256_MAX_int >> DECIDE_TAC) >>
     DECIDE_TAC) >>
  imp_res_tac wordsTheory.w2n_add_2 >>
  simp[bool_to_word_def]
QED

(* The sub underflow argument:
   If x,y have nonneg ranges with lo(x) >= hi(y),
   then w2n(x-y) <= w2n(x), so gt(x-y, x) = 0w *)
Theorem sub_no_underflow_gt_zero:
  !wx wy xr yr.
    range_nonneg xr /\ range_nonneg yr /\
    in_range xr wx /\ in_range yr wy /\
    vr_lo xr >= vr_hi yr ==>
    bool_to_word (w2n (word_sub wx wy) > w2n wx) = 0w
Proof
  rpt strip_tac >>
  imp_res_tac range_nonneg_in_range_nonneg_w2i >>
  `0 <= w2i wx /\ 0 <= w2i wy` by simp[] >>
  `w2n wx = Num (w2i wx)` by metis_tac[nonneg_w2i_eq_w2n] >>
  `w2n wy = Num (w2i wy)` by metis_tac[nonneg_w2i_eq_w2n] >>
  `w2n wy <= w2n wx` by
    (Cases_on `xr` >> Cases_on `yr` >>
     fs[range_nonneg_def, vr_lo_def, vr_hi_def, in_range_def] >>
     intLib.ARITH_TAC) >>
  `wy <=+ wx` by simp[wordsTheory.WORD_LS] >>
  imp_res_tac wordsTheory.word_sub_w2n >>
  simp[bool_to_word_def]
QED

(* ================================================================
   Section 3: Transform equivalence
   ================================================================

   Show overflow_elim_function = clear_nops(analysis_function_transform_widen ...)
   by connecting overflow_elim_block_insts to MAPi. *)

(* Helper: overflow_elim_block_insts from offset k = MAPi from k *)
Theorem overflow_elim_block_insts_eq_mapi:
  !insts dfg ra lbl k.
    overflow_elim_block_insts dfg ra lbl k insts =
    MAPi (\i inst. overflow_elim_inst dfg ra lbl (k + i) inst) insts
Proof
  Induct >> simp[overflow_elim_block_insts_def, indexedListsTheory.MAPi_def] >>
  rpt strip_tac >>
  simp[combinTheory.o_DEF] >>
  first_x_assum (qspecl_then [`dfg`, `ra`, `lbl`, `k + 1`] mp_tac) >>
  strip_tac >>
  irule listTheory.LIST_EQ >> simp[indexedListsTheory.EL_MAPi] >>
  rpt strip_tac >>
  `k + 1 + x = k + SUC x` by DECIDE_TAC >>
  `k + (x + 1) = k + SUC x` by DECIDE_TAC >>
  simp[]
QED




(* ================================================================
   Section 4: Per-instruction simulation
   ================================================================ *)

(* The sound predicate for overflow_elim includes range + dfg_ext *)
(* overflow_elim_inst needs (ra, lbl, idx) for range_get_range, but the
   framework only provides v = df_widen_at NONE ra lbl idx. Since
   range_get_range ra lbl idx op = range_get_range_v (range_unwrap v) op
   (see range_get_range_eq_v, overflow_elim_inst_eq_v, overflow_elim_inst_via_widen),
   the transform can be expressed via v alone. *)

(* Range query taking range state directly *)
Definition range_get_range_v_def:
  range_get_range_v rs (Lit w) = vr_constant (w2i w) /\
  range_get_range_v rs (Var v) = rs_lookup rs v /\
  range_get_range_v rs (Label _) = VR_Top
End

(* Equivalence between range_get_range and range_get_range_v *)
Theorem range_get_range_eq_v:
  !ra lbl idx op.
    range_get_range ra lbl idx op =
    range_get_range_v (range_at_inst ra lbl idx) op
Proof
  Cases_on `op` >> simp[range_get_range_def, range_get_range_v_def]
QED

(* If range_nonneg holds for range_get_range_v, the operand is not a Label.
   Label -> VR_Top, range_nonneg VR_Top = F. *)
Theorem range_nonneg_not_label:
  !rs op. range_nonneg (range_get_range_v rs op) ==> (!lbl. op <> Label lbl)
Proof
  Cases_on `op` >> simp[range_get_range_v_def, range_nonneg_def]
QED

(* _v variants: take range state directly instead of (ra, lbl, idx) *)

Definition try_elim_add_overflow_v_def:
  try_elim_add_overflow_v dfg rs (lt_inst : instruction) =
    case lt_inst.inst_operands of
      [res_op; x_op] =>
        (case get_producer dfg res_op of
           SOME add_inst =>
             if add_inst.inst_opcode <> ADD then F
             else (case add_inst.inst_operands of
               [add_op0; add_op1] =>
                 let y_op =
                   if add_op0 = x_op then SOME add_op1
                   else if add_op1 = x_op then SOME add_op0
                   else NONE
                 in
                 (case y_op of
                    NONE => F
                  | SOME y =>
                      let x_range = range_get_range_v rs x_op in
                      let y_range = range_get_range_v rs y in
                      range_nonneg x_range /\ range_nonneg y_range /\
                      vr_hi x_range + vr_hi y_range <= UINT256_MAX_int)
             | _ => F)
         | NONE => F)
    | _ => F
End

Definition try_elim_sub_underflow_v_def:
  try_elim_sub_underflow_v dfg rs (gt_inst : instruction) =
    case gt_inst.inst_operands of
      [res_op; x_op] =>
        (case get_producer dfg res_op of
           SOME sub_inst =>
             if sub_inst.inst_opcode <> SUB then F
             else (case sub_inst.inst_operands of
               [sub_x; sub_y] =>
                 if sub_x <> x_op then F
                 else
                   let x_range = range_get_range_v rs x_op in
                   let y_range = range_get_range_v rs sub_y in
                   range_nonneg x_range /\ range_nonneg y_range /\
                   vr_lo x_range >= vr_hi y_range
             | _ => F)
         | NONE => F)
    | _ => F
End

Definition try_elim_overflow_check_v_def:
  try_elim_overflow_check_v dfg rs (assert_inst : instruction) =
    case assert_inst.inst_operands of
      [assert_op] =>
        (case get_producer dfg assert_op of
           SOME iszero_inst =>
             if iszero_inst.inst_opcode <> ISZERO then F
             else (case iszero_inst.inst_operands of
               [cmp_op] =>
                 (case get_producer dfg cmp_op of
                    SOME cmp_inst =>
                      if cmp_inst.inst_opcode = LT then
                        try_elim_add_overflow_v dfg rs cmp_inst
                      else if cmp_inst.inst_opcode = GT then
                        try_elim_sub_underflow_v dfg rs cmp_inst
                      else F
                  | NONE => F)
             | _ => F)
         | NONE => F)
    | _ => F
End

Definition overflow_elim_inst_v_def:
  overflow_elim_inst_v dfg rs inst =
    if inst.inst_opcode <> ASSERT then inst
    else if try_elim_overflow_check_v dfg rs inst
    then mk_nop_inst inst
    else inst
End

(* Equivalence: the _v versions compute the same as the originals *)
Theorem try_elim_add_overflow_eq_v:
  !dfg ra lbl idx lt_inst.
    try_elim_add_overflow dfg ra lbl idx lt_inst =
    try_elim_add_overflow_v dfg (range_at_inst ra lbl idx) lt_inst
Proof
  rpt gen_tac >>
  simp[try_elim_add_overflow_def, try_elim_add_overflow_v_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[range_get_range_eq_v]
QED

Theorem try_elim_sub_underflow_eq_v:
  !dfg ra lbl idx gt_inst.
    try_elim_sub_underflow dfg ra lbl idx gt_inst =
    try_elim_sub_underflow_v dfg (range_at_inst ra lbl idx) gt_inst
Proof
  rpt gen_tac >>
  simp[try_elim_sub_underflow_def, try_elim_sub_underflow_v_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[range_get_range_eq_v]
QED

Theorem try_elim_overflow_check_eq_v:
  !dfg ra lbl idx inst.
    try_elim_overflow_check dfg ra lbl idx inst =
    try_elim_overflow_check_v dfg (range_at_inst ra lbl idx) inst
Proof
  rpt gen_tac >>
  simp[try_elim_overflow_check_def, try_elim_overflow_check_v_def] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[try_elim_add_overflow_eq_v, try_elim_sub_underflow_eq_v]
QED

Theorem overflow_elim_inst_eq_v:
  !dfg ra lbl idx inst.
    overflow_elim_inst dfg ra lbl idx inst =
    overflow_elim_inst_v dfg (range_at_inst ra lbl idx) inst
Proof
  simp[overflow_elim_inst_def, overflow_elim_inst_v_def,
       try_elim_overflow_check_eq_v]
QED

(* The _v variant takes the abstract domain value directly *)

(* Connect to framework: the transform via df_widen_at *)
Theorem overflow_elim_inst_via_widen:
  !dfg ra lbl idx inst.
    overflow_elim_inst dfg ra lbl idx inst =
    overflow_elim_inst_v dfg (range_unwrap (df_widen_at NONE ra lbl idx)) inst
Proof
  simp[overflow_elim_inst_eq_v, range_at_inst_def]
QED

Theorem FLAT_MAPi_SING:
  !f l. FLAT (MAPi (\i x. [f i x]) l) = MAPi f l
Proof
  Induct_on `l` >> simp[indexedListsTheory.MAPi_def] >>
  rpt gen_tac >>
  first_x_assum (qspec_then `f o SUC` mp_tac) >>
  simp[combinTheory.o_DEF]
QED

(* Transform equivalence: overflow_elim_function =
   clear_nops(analysis_function_transform_widen NONE ra
     (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst]) fn) *)
Theorem overflow_elim_function_eq:
  !fn.
    let dfg = dfg_build_function fn in
    let ra = range_analyze fn in
    overflow_elim_function fn =
    clear_nops_function
      (analysis_function_transform_widen NONE ra
        (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst]) fn)
Proof
  simp[overflow_elim_function_def, LET_THM,
       analysis_function_transform_widen_def,
       function_map_transform_def,
       analysis_block_transform_widen_def] >>
  rpt gen_tac >>
  AP_TERM_TAC >> (* clear_nops_function *)
  simp[ir_function_component_equality] >>
  irule listTheory.LIST_EQ >>
  simp[listTheory.EL_MAP, listTheory.LENGTH_MAP] >>
  rpt strip_tac >>
  simp[overflow_elim_block_def, basic_block_component_equality] >>
  simp[overflow_elim_block_insts_eq_mapi] >>
  (* MAPi (\i inst. overflow_elim_inst dfg ra (EL x fn.fn_blocks).bb_label (0+i) inst) =
     FLAT (MAPi (\i inst. [overflow_elim_inst_v dfg (range_unwrap (df_widen_at NONE ra lbl i)) inst]) ...) *)
  simp[FLAT_MAPi_SING, analysis_block_transform_widen_def,
       analysis_block_transform_def, basic_block_component_equality] >>
  irule listTheory.LIST_EQ >>
  simp[indexedListsTheory.EL_MAPi] >>
  rpt strip_tac >>
  simp[overflow_elim_inst_via_widen]
QED

(* ================================================================
   Range-DFG chain contradiction helpers
   ================================================================

   When try_elim_overflow_check_v succeeds, the DFG chain
   ASSERT → ISZERO → LT/GT → ADD/SUB constrains variable values.
   Combined with range analysis, the ASSERT operand cannot be 0w. *)

(* Soundness of range_get_range_v: if in_range_state holds and
   eval_op_env gives SOME, then in_range holds for the range query *)
Theorem range_get_range_v_sound:
  !rs env op w.
    in_range_state rs env /\ eval_op_env op env = SOME w ==>
    in_range (range_get_range_v rs op) w
Proof
  rpt strip_tac >>
  Cases_on `op` >>
  gvs[eval_op_env_def, range_get_range_v_def, rs_lookup_def,
      vr_constant_def, in_range_def] >>
  Cases_on `FLOOKUP rs s` >> gvs[in_range_def, in_range_state_def] >>
  metis_tac[]
QED

(* Helper: dfg_arith_sound + concrete operands + range_nonneg ==>
   eval_op_env values exist. Wraps dfg_arith_sound_def to hide no-Label guard. *)
Triviality dfg_arith_sound_instantiate:
  !dfg env v inst op1 op2 rs.
    dfg_arith_sound dfg env /\
    dfg_get_def dfg v = SOME inst /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    inst.inst_operands = [op1; op2] /\
    v IN FDOM env /\
    range_nonneg (range_get_range_v rs op1) /\
    range_nonneg (range_get_range_v rs op2) ==>
    ?w1 w2. eval_op_env op1 env = SOME w1 /\
            eval_op_env op2 env = SOME w2 /\
            FLOOKUP env v = SOME
              (if inst.inst_opcode = ADD then w1 + w2 else w1 - w2)
Proof
  rpt strip_tac >>
  imp_res_tac range_nonneg_not_label >>
  fs[dfg_arith_sound_def] >>
  first_x_assum (qspecl_then [`v`, `inst`, `op1`, `op2`] mp_tac) >>
  simp[]
QED

(* ADD overflow contradiction:
   If the DFG chain for the ADD case is satisfied, dfg_ext_sound holds,
   in_range_state holds, and the ISZERO output is 0w, then False. *)
Theorem add_overflow_contradiction:
  !dfg rs env assert_v iszero_inst cmp_v cmp_inst.
    dfg_ext_sound dfg env /\ in_range_state rs env /\
    (* ISZERO chain *)
    dfg_get_def dfg assert_v = SOME iszero_inst /\
    iszero_inst.inst_opcode = ISZERO /\
    iszero_inst.inst_operands = [Var cmp_v] /\
    (* LT comparison *)
    dfg_get_def dfg cmp_v = SOME cmp_inst /\
    cmp_inst.inst_opcode = LT /\
    (* ADD overflow check succeeds *)
    try_elim_add_overflow_v dfg rs cmp_inst /\
    (* ISZERO result is 0w *)
    FLOOKUP env assert_v = SOME 0w ==>
    F
Proof
  rpt strip_tac >>
  fs[dfg_ext_sound_def] >>
  (* Get assert_v IN FDOM *)
  `assert_v IN FDOM env` by fs[FLOOKUP_DEF] >>
  (* closure: ISZERO tracked, Var cmp_v operand => cmp_v IN FDOM *)
  `cmp_v IN FDOM env` by
    (first_x_assum (qspecl_then [`assert_v`, `iszero_inst`, `cmp_v`] mp_tac) >>
     simp[dfg_tracked_opcode_def, MEM]) >>
  (* dfg_iszero_sound: assert_v = 0w => cmp_v value ≠ 0w *)
  `!w'. FLOOKUP env cmp_v = SOME w' ==> w' <> 0w` by
    (rpt strip_tac >>
     `dfg_iszero_sound dfg env` by fs[dfg_sound_def] >>
     fs[dfg_iszero_sound_def] >>
     first_x_assum (qspecl_then [`assert_v`, `iszero_inst`, `cmp_v`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  (* Get a concrete value for cmp_v *)
  `?cmp_w. FLOOKUP env cmp_v = SOME cmp_w /\ cmp_w <> 0w` by
    (Cases_on `FLOOKUP env cmp_v` >- fs[FLOOKUP_DEF] >>
     metis_tac[]) >>
  (* Extract chain components from try_elim_add_overflow_v.
     Keep in assumptions, decompose via fs + FULL_CASE_TAC *)
  fs[try_elim_add_overflow_v_def] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[] >>
  (* Extract res_v, get compare and arith semantics *)
  rename1 `get_producer dfg res_op = SOME add_inst` >>
  rename1 `cmp_inst.inst_operands = [res_op; x_op]` >>
  Cases_on `res_op` >> gvs[get_producer_def] >>
  rename1 `dfg_get_def dfg res_v = SOME add_inst` >>
  `res_v IN FDOM env` by
    (first_x_assum (qspecl_then [`cmp_v`, `cmp_inst`, `res_v`] mp_tac) >>
     simp[dfg_tracked_opcode_def, MEM]) >>
  (* Establish no-Label for x_op from range_nonneg *)
  (`(!lbl. x_op <> Label lbl)` by
    (match_mp_tac range_nonneg_not_label >> metis_tac[])) >>
  (* compare: LT(res_v, x_op) *)
  qpat_x_assum `dfg_compare_full_sound _ _`
    (mp_tac o REWRITE_RULE [dfg_compare_full_sound_def]) >>
  disch_then (qspecl_then [`cmp_v`, `cmp_inst`,
    `Var res_v`, `x_op`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Establish no-Label for all ADD operands (h'/h'' in branches 2&3) *)
  imp_res_tac range_nonneg_not_label >>
  (* arith: expand dfg_arith_sound_def, specialize for res_v/add_inst.
     Keep eval_op_env intact for range_get_range_v_sound. *)
  fs[dfg_arith_sound_def] >>
  qpat_x_assum `!v inst op1 op2. _ ==> ?w1 w2. _`
    (qspecl_then [`res_v`, `add_inst`,
      `HD add_inst.inst_operands`, `HD (TL add_inst.inst_operands)`] mp_tac) >>
  (* Use impl_tac to cleanly discharge the antecedent, then use the result *)
  (impl_tac >- simp[]) >>
  strip_tac >>
  (* Now we have eval_op_env op1/op2 = SOME w1'/w2' and FLOOKUP res_v = SOME (w1'+w2').
     Derive in_range for both operands, then use add_no_overflow_lt_zero. *)
  imp_res_tac range_get_range_v_sound >>
  gvs[eval_op_env_def] >>
  metis_tac[add_no_overflow_lt_zero, bool_to_word_def,
            wordsTheory.WORD_ADD_COMM, integerTheory.INT_ADD_COMM]
QED

(* SUB underflow contradiction: symmetric to ADD case *)
Theorem sub_underflow_contradiction:
  !dfg rs env assert_v iszero_inst cmp_v cmp_inst.
    dfg_ext_sound dfg env /\ in_range_state rs env /\
    dfg_get_def dfg assert_v = SOME iszero_inst /\
    iszero_inst.inst_opcode = ISZERO /\
    iszero_inst.inst_operands = [Var cmp_v] /\
    dfg_get_def dfg cmp_v = SOME cmp_inst /\
    cmp_inst.inst_opcode = GT /\
    try_elim_sub_underflow_v dfg rs cmp_inst /\
    FLOOKUP env assert_v = SOME 0w ==>
    F
Proof
  rpt strip_tac >>
  fs[dfg_ext_sound_def] >>
  `assert_v IN FDOM env` by fs[FLOOKUP_DEF] >>
  `cmp_v IN FDOM env` by
    (first_x_assum (qspecl_then [`assert_v`, `iszero_inst`, `cmp_v`] mp_tac) >>
     simp[dfg_tracked_opcode_def, MEM]) >>
  `!w'. FLOOKUP env cmp_v = SOME w' ==> w' <> 0w` by
    (rpt strip_tac >>
     `dfg_iszero_sound dfg env` by fs[dfg_sound_def] >>
     fs[dfg_iszero_sound_def] >>
     first_x_assum (qspecl_then [`assert_v`, `iszero_inst`, `cmp_v`] mp_tac) >>
     simp[] >> metis_tac[]) >>
  fs[try_elim_sub_underflow_v_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  rename1 `get_producer dfg res_op = SOME sub_inst` >>
  Cases_on `res_op` >> gvs[get_producer_def] >>
  rename1 `dfg_get_def dfg res_v = SOME sub_inst` >>
  `res_v IN FDOM env` by
    (first_x_assum (qspecl_then [`cmp_v`, `cmp_inst`, `res_v`] mp_tac) >>
     simp[dfg_tracked_opcode_def, MEM]) >>
  (* Establish no-Label for all operands from range_nonneg *)
  imp_res_tac range_nonneg_not_label >>
  (* compare: GT(res_v, h') *)
  qpat_x_assum `dfg_compare_full_sound _ _`
    (mp_tac o REWRITE_RULE [dfg_compare_full_sound_def]) >>
  disch_then (qspecl_then [`cmp_v`, `cmp_inst`,
    `Var res_v`, `HD (TL cmp_inst.inst_operands)`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* arith: expand dfg_arith_sound_def, specialize for res_v/sub_inst *)
  fs[dfg_arith_sound_def] >>
  qpat_x_assum `!v inst op1 op2. _ ==> ?w1 w2. _`
    (qspecl_then [`res_v`, `sub_inst`,
      `HD sub_inst.inst_operands`, `HD (TL sub_inst.inst_operands)`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  imp_res_tac range_get_range_v_sound >>
  gvs[eval_op_env_def] >>
  metis_tac[sub_no_underflow_gt_zero, bool_to_word_def]
QED

(* Master contradiction: try_elim_overflow_check_v + dfg_ext_sound +
   range_sound + eval_operand = SOME 0w ==> F *)
Theorem overflow_check_contradiction:
  !dfg rs v s op.
    try_elim_overflow_check_v dfg rs (v with inst_operands := [op]) /\
    dfg_ext_sound dfg s.vs_vars /\
    in_range_state rs s.vs_vars /\
    eval_operand op s = SOME 0w ==>
    F
Proof
  rpt strip_tac >>
  fs[try_elim_overflow_check_v_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  (* op must be Var for get_producer to return SOME *)
  Cases_on `op` >> gvs[get_producer_def] >>
  rename1 `dfg_get_def dfg assert_v = SOME iszero_inst` >>
  `eval_operand (Var assert_v) s = SOME 0w` by simp[] >>
  `FLOOKUP s.vs_vars assert_v = SOME 0w` by
    fs[eval_operand_def, lookup_var_def] >>
  Cases_on `h` >> gvs[get_producer_def] >>
  rename1 `iszero_inst.inst_operands = [Var cmp_v]` >>
  rename1 `dfg_get_def dfg cmp_v = SOME cmp_inst` >>
  Cases_on `cmp_inst.inst_opcode = LT` >> gvs[]
  >- metis_tac[add_overflow_contradiction]
  >- (Cases_on `cmp_inst.inst_opcode = GT` >> gvs[] >>
      metis_tac[sub_underflow_contradiction])
QED

(* ================================================================
   Section 5: Core correctness — overflow_elim_sim
   ================================================================

   The sound predicate gives us
   range_sound v s and dfg_ext_sound dfg s.vs_vars. We need to show
   that when try_elim_overflow_check_v dfg (range_unwrap v) inst holds,
   the ASSERT instruction either errors or returns OK s (passes). *)

Theorem overflow_elim_sim:
  !dfg fn v fuel ctx inst s.
    dfg = dfg_build_function fn /\
    (range_sound v s /\ dfg_ext_sound dfg s.vs_vars) /\
    inst_wf inst ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (step_inst fuel ctx inst s)
      (step_inst fuel ctx (overflow_elim_inst_v dfg (range_unwrap v) inst) s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ASSERT`
  >- (
    (* ASSERT case *)
    simp[overflow_elim_inst_v_def] >>
    IF_CASES_TAC
    >- (
      (* try_elim_overflow_check_v succeeded — ASSERT becomes NOP *)
      `?op. inst.inst_operands = [op]` by
        (`LENGTH inst.inst_operands = 1` by fs[inst_wf_def] >>
         Cases_on `inst.inst_operands` >> fs[] >> metis_tac[]) >>
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `op`] step_inst_assert_1) >>
      simp[] >> disch_then (fn th => REWRITE_TAC [th]) >>
      Cases_on `eval_operand op s`
      >- (DISJ1_TAC >> qexists_tac `"undefined operand"` >> simp[])
      >- (
        rename1 `SOME w` >>
        Cases_on `w = 0w`
        >- (
          `in_range_state (range_unwrap v) s.vs_vars` by
            (Cases_on `v` >>
             fs[range_sound_def, range_unwrap_def,
                in_range_state_def, FLOOKUP_DEF]) >>
          `inst = inst with inst_operands := [op]` by
            simp[instruction_component_equality] >>
          metis_tac[overflow_check_contradiction]
        )
        >- simp[mk_nop_inst_correct, lift_result_def, state_equiv_refl]
      )
    )
    >- metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl]
  )
  >- (
    simp[overflow_elim_inst_v_def] >>
    metis_tac[lift_result_refl, state_equiv_refl, execution_equiv_refl]
  )
QED

Theorem overflow_elim_inst_simulates_1:
  !dfg fn.
    dfg = dfg_build_function fn ==>
    analysis_inst_simulates_1
      (state_equiv {}) (execution_equiv {})
      (\v s. range_sound v s /\ dfg_ext_sound dfg s.vs_vars)
      (\v inst. overflow_elim_inst_v dfg (range_unwrap v) inst)
Proof
  rpt strip_tac >> gvs[] >>
  simp[analysis_inst_simulates_1_def, inst_transform_structural_1_def] >>
  rpt conj_tac
  >- metis_tac[overflow_elim_sim]
  >- (rpt strip_tac >> simp[overflow_elim_inst_v_def] >>
      Cases_on `inst.inst_opcode` >> fs[is_terminator_def])
  >- (rpt strip_tac >> simp[overflow_elim_inst_v_def])
  >- (rpt strip_tac >> simp[overflow_elim_inst_v_def])
  >> (rpt strip_tac >> gvs[overflow_elim_inst_v_def] >>
      BasicProvers.every_case_tac >>
      gvs[mk_nop_inst_def, is_terminator_def])
QED

Theorem overflow_elim_inst_simulates:
  !dfg fn.
    dfg = dfg_build_function fn ==>
    analysis_inst_simulates
      (state_equiv {}) (execution_equiv {})
      (\v s. range_sound v s /\ dfg_ext_sound dfg s.vs_vars)
      (\v inst. [overflow_elim_inst_v dfg (range_unwrap v) inst])
Proof
  rpt strip_tac >>
  `analysis_inst_simulates_1
      (state_equiv {}) (execution_equiv {})
      (\v s. range_sound v s /\ dfg_ext_sound (dfg_build_function fn) s.vs_vars)
      (\v inst. overflow_elim_inst_v (dfg_build_function fn) (range_unwrap v) inst)` by
    metis_tac[overflow_elim_inst_simulates_1] >>
  imp_res_tac analysis_inst_simulates_from_1 >>
  fs[]
QED

(* ================================================================
   Section 6: Block-level simulation
   ================================================================

   Strategy: Thread range_sound per-step; for eliminated ASSERTs, derive
   the contradiction from pointwise DFG conditions on chain variables.

   Key insight: within a block, each variable is written at most once (SSA).
   After a tracked DFG instruction executes, its output persists. So at the
   ASSERT position, all chain entries are sound — even though full
   dfg_ext_sound may be temporarily broken for unrelated entries.

   We define dfg_prefix_sound to capture: every tracked DFG entry whose
   defining instruction is at a position < idx has its output value
   matching the DFG computation. This IS per-step preservable within a
   block under SSA, and gives the chain conditions needed for the
   overflow_check_contradiction at the ASSERT position. *)

(* Helper: run_insts append decomposition *)
Theorem run_insts_append:
  !fuel ctx l1 l2 s.
    run_insts fuel ctx (l1 ++ l2) s =
    case run_insts fuel ctx l1 s of
      OK s' => run_insts fuel ctx l2 s'
    | Halt v => Halt v
    | Abort a v => Abort a v
    | IntRet vals v => IntRet vals v
    | Error e => Error e
Proof
  Induct_on `l1` >> simp[run_insts_def] >>
  rpt gen_tac >> Cases_on `step_inst fuel ctx h s` >> simp[]
QED
