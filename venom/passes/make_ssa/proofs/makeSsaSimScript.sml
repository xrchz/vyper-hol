(*
 * Make SSA Pass — Fuel Induction Simulation
 *
 * Contains run_function_ssa_sim: the core fuel induction proof
 * that uses phi_args_ok_from_pipeline and run_block_ssa_sim
 * from makeSsaHelper.
 *)

Theory makeSsaSim
Ancestors
  makeSsaHelper ssaSimDefs ssaRenamedSim ssaPipeline makeSsaDefs stateEquiv stateEquivProps
  venomExecSemantics venomExecProofs venomWf venomState venomInst
  cfgTransform cfgTransformProps passSimulationDefs passSimulationProps
  execEquivParamDefs execEquivParamProofs execEquivProofs
  list rich_list alist finite_map pred_set string arithmetic

(* IH ref cell — must be val, not fun *)
val ih_ref : thm ref = ref TRUTH;
val sigma_exit_ref : thm ref = ref TRUTH;
val func'_eq_ref : thm ref = ref TRUTH;
val bbs2_eq_ref : thm ref = ref TRUTH;

Triviality phi_prefix_bridge:
  !phis bd P insts.
    insts = phis ++ bd /\
    EVERY P phis /\
    EVERY (\x. ~P x) bd ==>
    FILTER P insts = phis /\
    (!i. MEM i insts /\ P i ==> MEM i phis) /\
    (EXISTS P insts <=> phis <> [])
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (ASM_REWRITE_TAC[FILTER_APPEND_DISTRIB] >>
      `FILTER P phis = phis` by simp[FILTER_EQ_ID] >>
      `FILTER P bd = []` by simp[FILTER_EQ_NIL] >>
      ASM_REWRITE_TAC[APPEND_NIL]) >>
  conj_tac
  >- (ASM_REWRITE_TAC[] >> rpt strip_tac >> gvs[MEM_APPEND, EVERY_MEM]) >>
  ASM_REWRITE_TAC[] >> EQ_TAC >> strip_tac
  >- (spose_not_then ASSUME_TAC >> gvs[EXISTS_MEM, MEM_APPEND, EVERY_MEM])
  >> simp[EXISTS_MEM, MEM_APPEND] >>
     Cases_on `phis` >> gvs[EVERY_DEF] >>
     DISJ1_TAC >> qexists_tac `h` >> simp[]
QED

Triviality FILTER_MEM_IMP:
  !P l l'. FILTER P l = l' ==>
    !x. MEM x l /\ P x ==> MEM x l'
Proof
  rpt strip_tac >> gvs[MEM_FILTER]
QED

Triviality coverage_bridge_inner:
  !phis bb_mid x.
    FILTER (\i. i.inst_opcode = PHI) bb_mid.bb_instructions = phis /\
    (!i. MEM i phis ==> ~MEM x i.inst_outputs) ==>
    (!i. MEM i bb_mid.bb_instructions /\ i.inst_opcode = PHI ==>
         ~MEM x i.inst_outputs)
Proof
  rpt strip_tac >>
  `MEM i phis` by (imp_res_tac FILTER_MEM_IMP >> gvs[]) >>
  res_tac
QED

Triviality phi_outputs_from_prefix:
  !phis bdy lbl bbs1 bb_mid.
    bb_mid.bb_instructions = phis ++ bdy /\
    EVERY (\i. i.inst_opcode = PHI) phis /\
    lookup_block lbl bbs1 = SOME bb_mid /\
    (!lbl' bb_mid' inst.
       lookup_block lbl' bbs1 = SOME bb_mid' /\
       MEM inst bb_mid'.bb_instructions /\ inst.inst_opcode = PHI ==>
       ?bv. inst.inst_outputs = [bv] /\ colon_free bv) ==>
    !j. j < LENGTH phis ==>
      ?bv. (EL j phis).inst_outputs = [bv] /\ colon_free bv
Proof
  rpt strip_tac >>
  `MEM (EL j phis) phis` by metis_tac[EL_MEM] >>
  first_x_assum (qspecl_then [`lbl`, `bb_mid`, `EL j phis`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    gvs[MEM_APPEND] >>
    gvs[EVERY_MEM])
  >> simp[]
QED

Triviality phis_nonempty_prev_bb:
  !phis bdy bb_mid_insts.
    bb_mid_insts = phis ++ bdy /\
    EVERY (\i. i.inst_opcode = PHI) phis /\
    phis <> [] ==>
    EXISTS (\i. i.inst_opcode = PHI) bb_mid_insts
Proof
  rpt strip_tac >>
  simp[EXISTS_MEM, MEM_APPEND] >>
  Cases_on `phis` >> gvs[EVERY_MEM] >>
  qexists_tac `h` >> simp[]
QED

Triviality bb_succs_phi_prepend:
  !phis bdy bb_mid bb.
    bb_mid.bb_instructions = phis ++ bdy /\
    bb.bb_instructions = bdy /\ bdy <> [] ==>
    bb_succs bb_mid = bb_succs bb
Proof
  rpt strip_tac >>
  simp[bb_succs_def] >>
  Cases_on `bdy` >> gvs[] >>
  `phis ++ h::t <> []` by simp[] >>
  Cases_on `phis ++ h::t` >> gvs[] >>
  `LAST (h'::t') = LAST (h::t)` suffices_by simp[] >>
  `h'::t' = phis ++ h::t` by gvs[] >>
  ASM_REWRITE_TAC[] >> irule LAST_APPEND_NOT_NIL >> simp[]
QED

Triviality MEM_ALOOKUP_SOME:
  MEM x (MAP FST l) ==> ?v. ALOOKUP l x = SOME v
Proof
  rpt strip_tac >> Cases_on `ALOOKUP l x` >> fs[ALOOKUP_NONE]
QED

(* stash_ih: remove IH from context into ih_ref.
   Matches: !v1 v2 ... vN. <conjunction> ==> ... with 7+ universals *)
val stash_ih : thm ref -> tactic =
  fn r => FIRST_X_ASSUM (fn th =>
    (let val (vs, body) = strip_forall (concl th)
         val (ant, _) = dest_imp body
     in if length vs >= 7 andalso is_conj ant
        then (r := th; ALL_TAC)
        else NO_TAC
     end) handle HOL_ERR _ => NO_TAC);


(* Phi resolve at successor block — extracted to avoid rich-context
   pattern matching issues inside nested by blocks. *)
Triviality phi_resolve_at_succ:
  !v1_prev_bb s1_cur_bb v1_cur_bb func' bbs1 bbs2
   bb_mid bb' rs_b_entry rs_a_end dtree succ_map rs0.
    v1_prev_bb = SOME s1_cur_bb /\
    valid_phi_operands bbs1 bbs2 dtree succ_map rs0 /\
    lookup_block s1_cur_bb bbs2 = SOME bb' /\
    lookup_block s1_cur_bb bbs1 = SOME bb_mid /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
      s1_cur_bb = SOME rs_b_entry /\
    MEM v1_cur_bb (bb_succs bb') /\
    func'.fn_blocks = bbs2 /\
    rs_a_end = FST (rename_block_insts rs_b_entry bb_mid.bb_instructions) ==>
    !bb_cur inst bvar ver.
      lookup_block v1_cur_bb func'.fn_blocks = SOME bb_cur /\
      MEM inst bb_cur.bb_instructions /\ inst.inst_opcode = PHI /\
      inst.inst_outputs = [version_var bvar ver] /\
      colon_free bvar /\ v1_prev_bb <> NONE ==>
      resolve_phi (THE v1_prev_bb) inst.inst_operands =
        SOME (Var (latest_version rs_a_end bvar))
Proof
  rpt strip_tac >>
  gvs[optionTheory.THE_DEF] >>
  qpat_assum `valid_phi_operands _ _ _ _ _` mp_tac >>
  PURE_REWRITE_TAC[valid_phi_operands_def] >>
  disch_then (qspecl_then [`s1_cur_bb`, `v1_cur_bb`,
    `bb_mid`, `bb'`, `bb_cur`, `inst`, `bvar`, `ver`,
    `rs_b_entry`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* Lift concrete coverage to universal form for IH.
   Given: lookup_block lbl bbs = SOME b_known,
          ALOOKUP al lbl = SOME rs_known,
          !x. P b_known x ==> f rs_known x = f rs_end x
   Derive: !x b rs. lookup_block lbl bbs = SOME b /\
                     ALOOKUP al lbl = SOME rs /\ P b x ==> f rs x = f rs_end x *)
Triviality coverage_lift:
  !lbl bbs al b_known rs_known rs_end.
    lookup_block lbl bbs = SOME b_known /\
    ALOOKUP al lbl = SOME rs_known /\
    (!x. (!i. MEM i b_known.bb_instructions /\ i.inst_opcode = PHI ==>
              ~MEM x i.inst_outputs) ==>
         latest_version rs_known x = latest_version rs_end x) ==>
    (!x bb1 rs_b.
       lookup_block lbl bbs = SOME bb1 /\
       ALOOKUP al lbl = SOME rs_b /\
       (!i. MEM i bb1.bb_instructions /\ i.inst_opcode = PHI ==>
            ~MEM x i.inst_outputs) ==>
       latest_version rs_b x = latest_version rs_end x)
Proof
  rpt strip_tac >>
  `bb1 = b_known` by metis_tac[optionTheory.SOME_11] >>
  `rs_b = rs_known` by metis_tac[optionTheory.SOME_11] >>
  gvs[]
QED

(* ===== State-equiv propagation for stale variables ===== *)

(* Helper: eval_operands gives same result under state_equiv *)
Triviality eval_operands_se:
  !ops s1 s2 vars.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> rw[eval_operands_def] >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  Cases_on `h` >> gvs[eval_operand_def] >>
  gvs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Helper: setup_callee identical under state_equiv *)
Triviality setup_callee_se:
  !fn args s1 s2 vars.
    state_equiv vars s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[setup_callee_def] >>
  gvs[state_equiv_def, execution_equiv_def] >>
  rw[venom_state_component_equality]
QED

(* Helper: merge_callee_state preserves state_equiv *)
Triviality merge_callee_se:
  !s1 s2 callee vars.
    state_equiv vars s1 s2 ==>
    state_equiv vars (merge_callee_state s1 callee)
                     (merge_callee_state s2 callee)
Proof
  rw[state_equiv_def, execution_equiv_def, merge_callee_state_def] >>
  gvs[lookup_var_def]
QED

(* Helper: adopting the same returned FMP preserves state equivalence. *)
Triviality adopt_return_fmp_se:
  !ir s1 s2 vars.
    state_equiv vars s1 s2 ==>
    state_equiv vars (adopt_return_fmp ir s1) (adopt_return_fmp ir s2)
Proof
  rpt strip_tac >> Cases_on `ir.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, state_equiv_def, execution_equiv_def,
      lookup_var_def]
QED

(* Helper: FOLDL update_var preserves state_equiv *)
Triviality foldl_update_var_se:
  !pairs s1 s2 vars.
    state_equiv vars s1 s2 ==>
    state_equiv vars
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct >> rw[] >>
  PairCases_on `h` >> gvs[] >>
  first_x_assum irule >>
  gvs[state_equiv_def, execution_equiv_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE]
QED

(* Helper: step_inst result_equiv for ALL opcodes including INVOKE.
   Key insight: for INVOKE, setup_callee uses FEMPTY for vs_vars,
   so the callee state is identical for state_equiv states.
   Hence run_function on the callee gives the same result. *)
Triviality step_inst_se:
  !vars fuel ctx inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (step_inst fuel ctx inst s1)
                      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    simp[step_inst_def] >>
    Cases_on `decode_invoke inst` >> gvs[result_equiv_def] >>
    PairCases_on `x` >> gvs[] >>
    rename1 `SOME (callee_name, arg_ops)` >>
    `inst.inst_operands = Label callee_name :: arg_ops`
      by gvs[decode_invoke_def, AllCaseEqs()] >>
    `eval_operands arg_ops s1 = eval_operands arg_ops s2` by (
      irule eval_operands_se >> qexists_tac `vars` >> gvs[] >>
      rpt strip_tac >> first_x_assum irule >> gvs[]) >>
    Cases_on `lookup_function callee_name ctx.ctx_functions`
    >> gvs[result_equiv_def] >>
    Cases_on `eval_operands arg_ops s2` >> gvs[result_equiv_def] >>
    rename1 `SOME args` >>
    `setup_callee x args s1 = setup_callee x args s2`
      by (irule setup_callee_se >> metis_tac[]) >>
    Cases_on `setup_callee x args s2` >> gvs[result_equiv_def] >>
    (* run_blocks on identical callee state — same call, same result *)
    Cases_on `run_blocks fuel ctx x x'` >> simp[] >>
    gvs[result_equiv_def, stateEquivPropsTheory.execution_equiv_refl] >>
    (* IntRet: merge + bind_outputs *)
    `state_equiv vars (merge_callee_state s1 v)
                      (merge_callee_state s2 v)` by
      (irule merge_callee_se >> gvs[]) >>
    `state_equiv vars
       (adopt_return_fmp i (merge_callee_state s1 v))
       (adopt_return_fmp i (merge_callee_state s2 v))` by
      (irule adopt_return_fmp_se >> gvs[]) >>
    simp[bind_outputs_def] >>
    IF_CASES_TAC >> gvs[result_equiv_def] >>
    irule foldl_update_var_se >> gvs[])
  >> (simp[step_inst_non_invoke] >>
      irule execEquivProofsTheory.step_inst_result_equiv >> gvs[])
QED

(* Helper: exec_block result_equiv for ALL instructions including INVOKE.
   Uses cj 2 of run_defs_ind with P_step=T, P_fn=T. *)
Triviality exec_block_se:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >>
  gvs[result_equiv_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars` by
    (gvs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  `result_equiv vars (step_inst fuel ctx inst s1)
                      (step_inst fuel ctx inst s2)` by
    (irule step_inst_se >> gvs[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[result_equiv_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[]
  >- (`v.vs_halted = v'.vs_halted` by
       fs[state_equiv_def, execution_equiv_def] >>
     Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
     fs[state_equiv_def]) >>
  (* Non-terminator: recurse via IH *)
  first_x_assum irule >> simp[] >>
  fs[state_equiv_def, execution_equiv_def] >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* run_block wrapper for exec_block_se *)
Triviality run_block_se:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)
Proof
  ONCE_REWRITE_TAC[run_block_def] >> rpt strip_tac >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
      !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) bb.bb_instructions` by (
    simp[EVERY_MEM] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`s1`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s1 bb.bb_instructions` >> gvs[exec_result_distinct] >>
  mp_tac (Q.SPECL [`s2`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s2 bb.bb_instructions` >> gvs[exec_result_distinct]
  >- (
    qspecl_then [`s1`, `s2`, `vars`, `bb.bb_instructions`, `v`] mp_tac
      eval_phis_state_equiv >> simp[] >> strip_tac >> gvs[] >>
    irule exec_block_se >>
    conj_tac >-
      qpat_x_assum `!inst. MEM inst bb.bb_instructions ==> _` ACCEPT_TAC >>
    gvs[state_equiv_def, execution_equiv_def, lookup_var_def])
  >- (
    qspecl_then [`s1`, `s2`, `vars`, `bb.bb_instructions`, `v`] mp_tac
      eval_phis_state_equiv >> simp[] >> strip_tac >> gvs[])
  >- (
    qspecl_then [`s2`, `s1`, `vars`, `bb.bb_instructions`, `v`] mp_tac
      eval_phis_state_equiv >> simp[state_equiv_sym] >> strip_tac >> gvs[])
  >- simp[result_equiv_def]
QED

(* State-equiv propagation for stale variables.
   If two states differ only on variables that are never read as operands,
   then run_blocks gives result_equiv results. Handles INVOKE. *)
Triviality run_blocks_stale_equiv:
  !fuel ctx vars fn s1 s2.
    state_equiv vars s1 s2 /\
    (!lbl bb inst v.
       lookup_block lbl fn.fn_blocks = SOME bb /\
       MEM inst bb.bb_instructions /\
       MEM (Var v) inst.inst_operands ==> v NOTIN vars) ==>
    result_equiv vars
      (run_blocks fuel ctx fn s1)
      (run_blocks fuel ctx fn s2)
Proof
  Induct_on `fuel` >-
  (simp[Once run_blocks_def, result_equiv_def] >>
   simp[Once run_blocks_def, result_equiv_def]) >>
  rpt strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by
    fs[state_equiv_def] >>
  CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [run_blocks_unfold]))) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_blocks_unfold])) >>
  simp[] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks` >-
  simp[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >> simp[] >>
  `result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)` by (
    irule run_block_se >> conj_tac
    >- metis_tac[] >>
    first_assum ACCEPT_TAC) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx bb s2` >>
  gvs[result_equiv_def] >>
  `v.vs_halted <=> v'.vs_halted` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[result_equiv_def] >-
  fs[state_equiv_def, execution_equiv_def] >>
  (* OK/OK, not halted — apply IH *)
  first_x_assum irule >>
  rpt strip_tac >> TRY res_tac >> TRY (first_assum ACCEPT_TAC)
QED

Theorem run_function_stale_equiv:
  !fuel ctx vars fn s1 s2.
    state_equiv vars s1 s2 /\
    (!lbl bb inst v.
       lookup_block lbl fn.fn_blocks = SOME bb /\
       MEM inst bb.bb_instructions /\
       MEM (Var v) inst.inst_operands ==> v NOTIN vars) ==>
    result_equiv vars
      (run_function fuel ctx fn s1)
      (run_function fuel ctx fn s2)
Proof
  rw[run_function_def] >>
  Cases_on `fn_entry_label fn` >> simp[result_equiv_def] >>
  irule run_blocks_stale_equiv >>
  conj_tac >- (first_assum ACCEPT_TAC) >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Closed-set version: operand condition only for reachable blocks. *)
Triviality run_blocks_stale_equiv_closed:
  !fuel ctx vars fn s1 s2 safe.
    state_equiv vars s1 s2 /\
    s1.vs_current_bb IN safe /\
    (!lbl bb.
       lbl IN safe /\
       lookup_block lbl fn.fn_blocks = SOME bb ==>
       bb_well_formed bb /\
       EVERY inst_wf bb.bb_instructions /\
       (!inst v. MEM inst bb.bb_instructions /\
                 MEM (Var v) inst.inst_operands ==> v NOTIN vars) /\
       (!s. MEM s (bb_succs bb) ==> s IN safe)) ==>
    result_equiv vars
      (run_blocks fuel ctx fn s1)
      (run_blocks fuel ctx fn s2)
Proof
  Induct_on `fuel` >-
  (simp[Once run_blocks_def, result_equiv_def] >>
   simp[Once run_blocks_def, result_equiv_def]) >>
  rpt strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by
    fs[state_equiv_def] >>
  CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [run_blocks_unfold]))) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_blocks_unfold])) >>
  simp[] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks` >-
  simp[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >> simp[] >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
   (!inst v. MEM inst bb.bb_instructions /\
             MEM (Var v) inst.inst_operands ==> v NOTIN vars) /\
   (!s. MEM s (bb_succs bb) ==> s IN safe)` by metis_tac[] >>
  `result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)` by (
    irule run_block_se >> conj_tac
    >- metis_tac[] >>
    first_assum ACCEPT_TAC) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx bb s2` >>
  gvs[result_equiv_def] >>
  `v.vs_halted <=> v'.vs_halted` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[result_equiv_def] >-
  fs[state_equiv_def, execution_equiv_def] >>
  (* OK/OK, not halted — apply IH *)
  (* Successor is in safe *)
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> spose_not_then strip_assume_tac >>
    qpat_x_assum `bb_well_formed bb`
      (STRIP_ASSUME_TAC o REWRITE_RULE [bb_well_formed_def]) >>
    res_tac >> DECIDE_TAC) >>
  `MEM v.vs_current_bb (bb_succs bb)` by (
    mp_tac run_block_current_bb_in_succs >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `v`] mp_tac) >>
    impl_tac >- simp[] >> simp[]) >>
  first_x_assum irule >> simp[] >>
  qexists_tac `safe` >> simp[] >>
  rpt strip_tac >> res_tac
QED

Theorem run_function_stale_equiv_closed:
  !fuel ctx vars fn s1 s2 safe.
    state_equiv vars s1 s2 /\
    (!lbl. fn_entry_label fn = SOME lbl ==> lbl IN safe) /\
    (!lbl bb.
       lbl IN safe /\
       lookup_block lbl fn.fn_blocks = SOME bb ==>
       bb_well_formed bb /\
       EVERY inst_wf bb.bb_instructions /\
       (!inst v. MEM inst bb.bb_instructions /\
                 MEM (Var v) inst.inst_operands ==> v NOTIN vars) /\
       (!s. MEM s (bb_succs bb) ==> s IN safe)) ==>
    result_equiv vars
      (run_function fuel ctx fn s1)
      (run_function fuel ctx fn s2)
Proof
  rw[run_function_def] >>
  Cases_on `fn_entry_label fn` >> simp[result_equiv_def] >>
  irule run_blocks_stale_equiv_closed >>
  conj_tac >- (
    qexists_tac `safe` >> simp[] >> metis_tac[]) >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* ===== PHI-aware stale_equiv infrastructure ===== *)

(* step_inst for PHI: only the RESOLVED operand needs to agree.
   Non-resolved PHI operands may disagree between state_equiv states. *)
Triviality step_inst_se_phi:
  !vars fuel ctx inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode = PHI /\
    (!v. s1.vs_prev_bb <> NONE /\
         resolve_phi (THE s1.vs_prev_bb) inst.inst_operands = SOME (Var v) ==>
         v NOTIN vars) ==>
    result_equiv vars (step_inst fuel ctx inst s1) (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  `s1.vs_prev_bb = s2.vs_prev_bb` by fs[state_equiv_def] >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  simp[step_inst_non_invoke] >>
  gvs[step_inst_base_def] >>
  (* PHI case expanded, s1/s2 share prev_bb *)
  Cases_on `inst.inst_outputs` >> gvs[result_equiv_def] >>
  Cases_on `t` >> gvs[result_equiv_def] >>
  Cases_on `s2.vs_prev_bb` >> gvs[result_equiv_def] >>
  rename1 `s2.vs_prev_bb = SOME prev_lbl` >>
  Cases_on `resolve_phi prev_lbl inst.inst_operands` >>
  gvs[result_equiv_def] >>
  rename1 `_ = SOME resolved_op` >>
  `eval_operand resolved_op s1 = eval_operand resolved_op s2` by (
    irule stateEquivPropsTheory.eval_operand_equiv >>
    qexists_tac `vars` >> simp[]) >>
  Cases_on `eval_operand resolved_op s2` >> gvs[result_equiv_def] >>
  irule stateEquivPropsTheory.update_var_preserves >> simp[]
QED

(* run_block with PHI-aware condition: PHI uses resolve_phi condition,
   non-PHI uses standard all-operands condition. *)
Triviality exec_block_se_phi:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
      (inst.inst_opcode = PHI ==>
        !v. s1.vs_prev_bb <> NONE /\
            resolve_phi (THE s1.vs_prev_bb) inst.inst_operands =
              SOME (Var v) ==>
            v NOTIN vars) /\
      (inst.inst_opcode <> PHI ==>
        !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
    result_equiv vars (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >>
  gvs[result_equiv_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def] >> metis_tac[EL_MEM]) >>
  (* Dispatch on PHI vs non-PHI *)
  Cases_on `inst.inst_opcode = PHI`
  >- (
    `result_equiv vars (step_inst fuel ctx inst s1)
                        (step_inst fuel ctx inst s2)` by (
      irule step_inst_se_phi >> gvs[] >> metis_tac[]) >>
    (* Pre-establish prev_bb preservation: PHI is not a terminator *)
    `!r. step_inst fuel ctx inst s1 = OK r ==>
         r.vs_prev_bb = s1.vs_prev_bb` by (
      rpt strip_tac >>
      `~is_terminator inst.inst_opcode` by gvs[is_terminator_def] >>
      metis_tac[step_inst_preserves_prev_bb]) >>
    Cases_on `step_inst fuel ctx inst s1` >>
    Cases_on `step_inst fuel ctx inst s2` >>
    gvs[result_equiv_def] >>
    Cases_on `is_terminator inst.inst_opcode` >> gvs[]
    >- (`v.vs_halted = v'.vs_halted` by
          fs[state_equiv_def, execution_equiv_def] >>
        Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
        fs[state_equiv_def]) >>
    first_x_assum irule >> simp[] >>
    fs[state_equiv_def, execution_equiv_def] >>
    simp[lookup_var_def] >> metis_tac[lookup_var_def])
  >> (
    `!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars` by
      metis_tac[] >>
    `result_equiv vars (step_inst fuel ctx inst s1)
                        (step_inst fuel ctx inst s2)` by (
      irule step_inst_se >> gvs[]) >>
    Cases_on `step_inst fuel ctx inst s1` >>
    Cases_on `step_inst fuel ctx inst s2` >>
    gvs[result_equiv_def] >>
    Cases_on `is_terminator inst.inst_opcode` >> gvs[]
    >- (`v.vs_halted = v'.vs_halted` by
          fs[state_equiv_def, execution_equiv_def] >>
        Cases_on `v.vs_halted` >> gvs[result_equiv_def] >>
        fs[state_equiv_def]) >>
    (* prev_bb preserved by non-terminator step_inst *)
    `v.vs_prev_bb = s1.vs_prev_bb` by
      metis_tac[step_inst_preserves_prev_bb] >>
    first_x_assum irule >> simp[] >>
    gvs[] >>
    fs[state_equiv_def, execution_equiv_def] >>
    simp[lookup_var_def] >> metis_tac[lookup_var_def])
QED

Triviality eval_one_phi_equiv_resolved:
  !s1 s2 vars inst out v.
    state_equiv vars s1 s2 /\
    eval_one_phi s1 inst = SOME (out, v) /\
    (!x. s1.vs_prev_bb <> NONE /\
         resolve_phi (THE s1.vs_prev_bb) inst.inst_operands = SOME (Var x) ==>
         x NOTIN vars) ==>
    eval_one_phi s2 inst = SOME (out, v)
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def, AllCaseEqs()] >>
  `eval_operand val_op s1 = eval_operand val_op s2` by (
    irule stateEquivPropsTheory.eval_operand_equiv >>
    qexists_tac `vars` >> simp[] >>
    rpt strip_tac >> first_x_assum irule >> gvs[]) >>
  fs[state_equiv_def] >> qexists_tac `prev` >> simp[]
QED

Triviality eval_phis_state_equiv_phi:
  !s1 s2 vars insts s1'.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode = PHI ==>
      !v. s1.vs_prev_bb <> NONE /\
          resolve_phi (THE s1.vs_prev_bb) inst.inst_operands = SOME (Var v) ==>
          v NOTIN vars) insts /\
    eval_phis s1 insts = OK s1' ==>
    ?s2'. eval_phis s2 insts = OK s2' /\ state_equiv vars s1' s2'
Proof
  Induct_on `insts` >> rpt strip_tac >> fs[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> rfs[] >>
  Cases_on `eval_one_phi s1 h` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `eval_phis s1 insts` >> gvs[] >>
  `eval_one_phi s2 h = SOME (x0,x1)` by (
    irule eval_one_phi_equiv_resolved >>
    qexists_tac `s1` >> qexists_tac `vars` >> gvs[EVERY_DEF]) >>
  `?s2'. eval_phis s2 insts = OK s2' /\ state_equiv vars v s2'` by (
    first_x_assum irule >> qexists_tac `s1` >> gvs[EVERY_DEF]) >>
  qexists_tac `update_var x0 x1 s2'` >> simp[eval_phis_def] >>
  metis_tac[stateEquivPropsTheory.update_var_preserves]
QED

Triviality eval_phis_state_equiv_phi_OK_pair:
  !s1 s2 vars insts v v'.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode = PHI ==>
      !x. s1.vs_prev_bb <> NONE /\
          resolve_phi (THE s1.vs_prev_bb) inst.inst_operands = SOME (Var x) ==>
          x NOTIN vars) insts /\
    eval_phis s1 insts = OK v /\
    eval_phis s2 insts = OK v' ==>
    state_equiv vars v v'
Proof
  rpt strip_tac >>
  qspecl_then [`s1`, `s2`, `vars`, `insts`, `v`] mp_tac
    eval_phis_state_equiv_phi >> simp[] >> strip_tac >> gvs[]
QED

Triviality phi_exec_cond_inst_idx:
  !vars s_base s_phi insts n.
    s_phi.vs_prev_bb = s_base.vs_prev_bb /\
    (!inst. MEM inst insts ==>
      (inst.inst_opcode = PHI ==>
        !v. s_base.vs_prev_bb <> NONE /\
            resolve_phi (THE s_base.vs_prev_bb) inst.inst_operands = SOME (Var v) ==>
            v NOTIN vars) /\
      (inst.inst_opcode <> PHI ==>
        !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
    (!inst. MEM inst insts ==>
      (inst.inst_opcode = PHI ==>
        !v. (s_phi with vs_inst_idx := n).vs_prev_bb <> NONE /\
            resolve_phi (THE ((s_phi with vs_inst_idx := n).vs_prev_bb))
              inst.inst_operands = SOME (Var v) ==>
            v NOTIN vars) /\
      (inst.inst_opcode <> PHI ==>
        !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars))
Proof
  rw[] >> res_tac >> fs[]
QED

Triviality phi_exec_cond_after_eval:
  !vars s s_phi insts.
    eval_phis s insts = OK s_phi /\
    (!inst. MEM inst insts ==>
      (inst.inst_opcode = PHI ==>
        !v. s.vs_prev_bb <> NONE /\
            resolve_phi (THE s.vs_prev_bb) inst.inst_operands = SOME (Var v) ==>
            v NOTIN vars) /\
      (inst.inst_opcode <> PHI ==>
        !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
    (!inst. MEM inst insts ==>
      (inst.inst_opcode = PHI ==>
        !v. s_phi.vs_prev_bb <> NONE /\
            resolve_phi (THE s_phi.vs_prev_bb) inst.inst_operands = SOME (Var v) ==>
            v NOTIN vars) /\
      (inst.inst_opcode <> PHI ==>
        !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars))
Proof
  rw[] >>
  imp_res_tac eval_phis_only_updates_vs_vars >>
  gvs[venom_state_component_equality] >> metis_tac[]
QED

Triviality exec_block_se_phi_after_eval:
  !fuel ctx vars bb s1 s2 s1_phi s2_phi.
    state_equiv vars s1 s2 /\
    eval_phis s1 bb.bb_instructions = OK s1_phi /\
    eval_phis s2 bb.bb_instructions = OK s2_phi /\
    (!inst. MEM inst bb.bb_instructions ==>
      (inst.inst_opcode = PHI ==>
        !v. s1.vs_prev_bb <> NONE /\
            resolve_phi (THE s1.vs_prev_bb) inst.inst_operands = SOME (Var v) ==>
            v NOTIN vars) /\
      (inst.inst_opcode <> PHI ==>
        !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
    result_equiv vars
      (exec_block fuel ctx bb
        (s1_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions))
      (exec_block fuel ctx bb
        (s2_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions))
Proof
  rpt strip_tac >>
  irule exec_block_se_phi >> simp[] >>
  conj_tac >- (
    mp_tac (Q.SPECL [`vars`, `s1`, `s1_phi`, `bb.bb_instructions`]
      phi_exec_cond_after_eval) >>
    simp[] >> disch_then match_mp_tac >>
    first_assum ACCEPT_TAC) >>
  irule state_equiv_inst_idx >>
  irule eval_phis_state_equiv_phi_OK_pair >> simp[EVERY_MEM] >>
  metis_tac[]
QED

(* run_block wrapper for exec_block_se_phi *)
Triviality run_block_se_phi:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
      (inst.inst_opcode = PHI ==>
        !v. s1.vs_prev_bb <> NONE /\
            resolve_phi (THE s1.vs_prev_bb) inst.inst_operands =
              SOME (Var v) ==>
            v NOTIN vars) /\
      (inst.inst_opcode <> PHI ==>
        !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
    result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)
Proof
  ONCE_REWRITE_TAC[run_block_def] >> rpt strip_tac >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
      !v. s1.vs_prev_bb <> NONE /\
          resolve_phi (THE s1.vs_prev_bb) inst.inst_operands = SOME (Var v) ==>
          v NOTIN vars) bb.bb_instructions` by (
    simp[EVERY_MEM] >> rpt strip_tac >>
    qpat_x_assum `!inst. MEM inst bb.bb_instructions ==> _` drule >>
    simp[]) >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
      !v. s2.vs_prev_bb <> NONE /\
          resolve_phi (THE s2.vs_prev_bb) inst.inst_operands = SOME (Var v) ==>
          v NOTIN vars) bb.bb_instructions` by (
    qpat_x_assum `EVERY _ bb.bb_instructions` mp_tac >>
    gvs[state_equiv_def]) >>
  mp_tac (Q.SPECL [`s1`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s1 bb.bb_instructions` >> gvs[exec_result_distinct] >>
  mp_tac (Q.SPECL [`s2`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s2 bb.bb_instructions` >> gvs[exec_result_distinct]
  >- (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `vars`, `bb`, `s1`, `s2`, `v`, `v'`]
      exec_block_se_phi_after_eval) >>
    simp[] >> disch_then match_mp_tac >>
    qpat_x_assum `!inst. MEM inst bb.bb_instructions ==> _` ACCEPT_TAC)
  >- (
    qspecl_then [`s1`, `s2`, `vars`, `bb.bb_instructions`, `v`] mp_tac
      eval_phis_state_equiv_phi >> simp[] >> strip_tac >> gvs[])
  >- (
    qspecl_then [`s2`, `s1`, `vars`, `bb.bb_instructions`, `v`] mp_tac
      eval_phis_state_equiv_phi >> simp[state_equiv_sym] >> strip_tac >> gvs[])
  >- simp[result_equiv_def]
QED

(* run_function with PHI-aware stale_equiv. Safe-set version.
   PHI operands: only resolved operand (via prev_bb) must not be stale.
   Tracks prev_bb through safe set for recursive calls. *)
Triviality run_blocks_stale_equiv_phi:
  !fuel ctx vars fn s1 s2 safe.
    state_equiv vars s1 s2 /\
    s1.vs_current_bb IN safe /\
    (!p. s1.vs_prev_bb = SOME p ==> p IN safe) /\
    (!lbl bb.
       lbl IN safe /\
       lookup_block lbl fn.fn_blocks = SOME bb ==>
       bb_well_formed bb /\
       EVERY inst_wf bb.bb_instructions /\
       (!inst v. MEM inst bb.bb_instructions /\
                 inst.inst_opcode <> PHI /\
                 MEM (Var v) inst.inst_operands ==> v NOTIN vars) /\
       (!inst prev_lbl v. MEM inst bb.bb_instructions /\
                 inst.inst_opcode = PHI /\
                 prev_lbl IN safe /\
                 resolve_phi prev_lbl inst.inst_operands = SOME (Var v) ==>
                 v NOTIN vars) /\
       (!s. MEM s (bb_succs bb) ==> s IN safe)) ==>
    result_equiv vars
      (run_blocks fuel ctx fn s1)
      (run_blocks fuel ctx fn s2)
Proof
  Induct_on `fuel` >-
  (simp[Once run_blocks_def, result_equiv_def] >>
   simp[Once run_blocks_def, result_equiv_def]) >>
  rpt strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [run_blocks_unfold]))) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_blocks_unfold])) >>
  simp[] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks` >-
  simp[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >> simp[] >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
   (!inst v. MEM inst bb.bb_instructions /\
             inst.inst_opcode <> PHI /\
             MEM (Var v) inst.inst_operands ==> v NOTIN vars) /\
   (!inst prev_lbl v. MEM inst bb.bb_instructions /\
             inst.inst_opcode = PHI /\
             prev_lbl IN safe /\
             resolve_phi prev_lbl inst.inst_operands = SOME (Var v) ==>
             v NOTIN vars) /\
   (!s. MEM s (bb_succs bb) ==> s IN safe)` by metis_tac[] >>
  `result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)` by (
    irule run_block_se_phi >> simp[] >>
    rpt gen_tac >> strip_tac >> conj_tac
    >- (
      rpt strip_tac >>
      Cases_on `s1.vs_prev_bb` >> gvs[] >>
      rename1 `s1.vs_prev_bb = SOME prev_lbl` >>
      `prev_lbl IN safe` by metis_tac[] >>
      first_x_assum (qspecl_then [`inst`, `prev_lbl`, `v`] mp_tac) >>
      simp[])
    >- metis_tac[]) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx bb s2` >>
  gvs[result_equiv_def] >>
  `v.vs_halted <=> v'.vs_halted` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[result_equiv_def] >-
  fs[state_equiv_def, execution_equiv_def] >>
  (* OK/OK, not halted — apply IH *)
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> spose_not_then strip_assume_tac >>
    gvs[bb_well_formed_def] >> res_tac >> DECIDE_TAC) >>
  `MEM v.vs_current_bb (bb_succs bb)` by (
    mp_tac run_block_current_bb_in_succs >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `v`] mp_tac) >>
    impl_tac >- simp[] >> simp[]) >>
  `v.vs_prev_bb = SOME s2.vs_current_bb` by (
    mp_tac run_block_ok_prev_bb >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `v`] mp_tac) >>
    impl_tac >- simp[] >> simp[]) >>
  first_x_assum irule >> simp[] >>
  qexists_tac `safe` >> simp[] >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC)
QED

Theorem run_function_stale_equiv_phi:
  !fuel ctx vars fn s1 s2 safe.
    state_equiv vars s1 s2 /\
    (!lbl. fn_entry_label fn = SOME lbl ==> lbl IN safe) /\
    (!p. s1.vs_prev_bb = SOME p ==> p IN safe) /\
    (!lbl bb.
       lbl IN safe /\
       lookup_block lbl fn.fn_blocks = SOME bb ==>
       bb_well_formed bb /\
       EVERY inst_wf bb.bb_instructions /\
       (!inst v. MEM inst bb.bb_instructions /\
                 inst.inst_opcode <> PHI /\
                 MEM (Var v) inst.inst_operands ==> v NOTIN vars) /\
       (!inst prev_lbl v. MEM inst bb.bb_instructions /\
                 inst.inst_opcode = PHI /\
                 prev_lbl IN safe /\
                 resolve_phi prev_lbl inst.inst_operands = SOME (Var v) ==>
                 v NOTIN vars) /\
       (!s. MEM s (bb_succs bb) ==> s IN safe)) ==>
    result_equiv vars
      (run_function fuel ctx fn s1)
      (run_function fuel ctx fn s2)
Proof
  rw[run_function_def] >>
  Cases_on `fn_entry_label fn` >> simp[result_equiv_def] >>
  irule run_blocks_stale_equiv_phi >>
  conj_tac >- (
    qexists_tac `safe` >> simp[] >> metis_tac[]) >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* sigma_next equation for PHI base variables.
   When bvar is a PHI base (live at block via phi_bases_live_in), the mixed
   sigma definition picks latest_version rs_a_end regardless of version equality. *)
Triviality sigma_mixed_phi_base:
  !sigma_next bvar live_in lbl rs_a_end rs_b_next bbs.
    (!y. sigma_next y =
      if (?vs. ALOOKUP live_in lbl = SOME vs /\ MEM y vs) /\
         latest_version rs_b_next y <> latest_version rs_a_end y
      then latest_version rs_a_end y
      else latest_version rs_b_next y) /\
    (!lbl' bb inst base ver.
      lookup_block lbl' bbs = SOME bb /\
      MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
      MEM (version_var base ver) inst.inst_outputs /\ colon_free base ==>
      ?vs. ALOOKUP live_in lbl' = SOME vs /\ MEM base vs) /\
    (?bb inst ver.
      lookup_block lbl bbs = SOME bb /\
      MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
      inst.inst_outputs = [version_var bvar ver] /\ colon_free bvar) ==>
    sigma_next bvar = latest_version rs_a_end bvar
Proof
  rpt strip_tac >>
  ASM_REWRITE_TAC[] >>
  Cases_on `latest_version rs_b_next bvar = latest_version rs_a_end bvar`
  >- ASM_REWRITE_TAC[] >>
  ASM_REWRITE_TAC[] >>
  (* bvar is live via inlined phi_bases_live_in *)
  first_x_assum (qspecl_then [`lbl`, `bb`, `inst`, `bvar`, `ver`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
  strip_tac >>
  `?vs. ALOOKUP live_in lbl = SOME vs /\ MEM bvar vs`
    by (qexists_tac `vs` >> ASM_REWRITE_TAC[]) >>
  simp[]
QED

(* sigma_next equation for non-PHI variables.
   Coverage: when x has no PHI at successor, sigma_next x = latest_version rs_b_next x.
   If x is live AND versions differ, valid_phi_coverage gives a PHI, contradiction. *)
Triviality sigma_mixed_coverage:
  !sigma_next x live_in lbl_a lbl_b rs_a_end rs_b_next rs_b_entry
   bb_mid bb_mid_next bbs1 dtree succ_map rs0.
    (!y. sigma_next y =
      if (?vs. ALOOKUP live_in lbl_b = SOME vs /\ MEM y vs) /\
         latest_version rs_b_next y <> latest_version rs_a_end y
      then latest_version rs_a_end y
      else latest_version rs_b_next y) /\
    valid_phi_coverage bbs1 dtree succ_map rs0 live_in /\
    lookup_block lbl_a bbs1 = SOME bb_mid /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_a =
      SOME rs_b_entry /\
    MEM lbl_b (bb_succs bb_mid) /\
    lookup_block lbl_b bbs1 = SOME bb_mid_next /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_b =
      SOME rs_b_next /\
    rs_a_end = FST (rename_block_insts rs_b_entry bb_mid.bb_instructions) /\
    (!i. MEM i bb_mid_next.bb_instructions /\ i.inst_opcode = PHI ==>
         ~MEM x i.inst_outputs) ==>
    latest_version rs_b_next x = sigma_next x
Proof
  rpt strip_tac >>
  qpat_x_assum `!y. sigma_next y = _`
    (fn th => PURE_REWRITE_TAC [th]) >>
  Cases_on `?vs. ALOOKUP live_in lbl_b = SOME vs /\ MEM x vs`
  >- (
    (* x is live — show versions equal by valid_phi_coverage contradiction *)
    Cases_on `latest_version rs_b_next x = latest_version rs_a_end x`
    >- simp[] >>
    (* x live, versions differ, no PHI → contradiction *)
    `F` suffices_by simp[] >>
    qpat_x_assum `?vs. _` strip_assume_tac >>
    (* Substitute rs_a_end so vpc conditions match *)
    qpat_x_assum `rs_a_end = _` (SUBST_ALL_TAC) >>
    qpat_x_assum `valid_phi_coverage _ _ _ _ _` mp_tac >>
    PURE_REWRITE_TAC[valid_phi_coverage_def] >>
    disch_then (qspecl_then [`lbl_a`, `lbl_b`,
      `bb_mid`, `bb_mid_next`, `rs_b_entry`, `rs_b_next`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then (qspecl_then [`x`, `vs`] mp_tac) >>
    impl_tac >- (
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >>
    first_x_assum (qspec_then `i` mp_tac) >>
    ASM_REWRITE_TAC[])
  >- simp[]
QED

(* Wrapper: universally-quantified coverage using deterministic lookups.
   Avoids rich-context issues by doing SOME_11 reasoning outside ok_ok_step. *)
Triviality sigma_mixed_coverage_at_block:
  !sigma_next live_in lbl_a lbl_b rs_a_end rs_b_next rs_b_entry
   bb_mid bb_mid_next bbs1 dtree succ_map rs0.
    (!y. sigma_next y =
      if (?vs. ALOOKUP live_in lbl_b = SOME vs /\ MEM y vs) /\
         latest_version rs_b_next y <> latest_version rs_a_end y
      then latest_version rs_a_end y
      else latest_version rs_b_next y) /\
    valid_phi_coverage bbs1 dtree succ_map rs0 live_in /\
    lookup_block lbl_a bbs1 = SOME bb_mid /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_a =
      SOME rs_b_entry /\
    MEM lbl_b (bb_succs bb_mid) /\
    lookup_block lbl_b bbs1 = SOME bb_mid_next /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_b =
      SOME rs_b_next /\
    rs_a_end = FST (rename_block_insts rs_b_entry bb_mid.bb_instructions) ==>
    !x bb1 rs_b.
      lookup_block lbl_b bbs1 = SOME bb1 /\
      ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree) lbl_b =
        SOME rs_b /\
      (!i. MEM i bb1.bb_instructions /\ i.inst_opcode = PHI ==>
           ~MEM x i.inst_outputs) ==>
      latest_version rs_b x = sigma_next x
Proof
  rpt strip_tac >>
  `bb1 = bb_mid_next` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >>
  `rs_b = rs_b_next` by metis_tac[optionTheory.SOME_11] >>
  pop_assum SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`sigma_next`, `x`, `live_in`, `lbl_a`, `lbl_b`,
    `rs_a_end`, `rs_b_next`, `rs_b_entry`,
    `bb_mid`, `bb_mid_next`, `bbs1`, `dtree`, `succ_map`, `rs0`]
    sigma_mixed_coverage) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

(* sigma_next always returns version_var x n for colon_free x. *)
Triviality sigma_mixed_version_var:
  !sigma_next rs_a rs_b live_in lbl.
    (!x. sigma_next x =
      if (?vs. ALOOKUP live_in lbl = SOME vs /\ MEM x vs) /\
         latest_version rs_b x <> latest_version rs_a x
      then latest_version rs_a x
      else latest_version rs_b x) ==>
    !x. colon_free x ==> ?n:num. sigma_next x = version_var x n
Proof
  rpt strip_tac >>
  first_x_assum (qspec_then `x` SUBST1_TAC) >>
  Cases_on `(?vs. ALOOKUP live_in lbl = SOME vs /\ MEM x vs) /\
            latest_version rs_b x <> latest_version rs_a x`
  >- simp[latest_version_is_version_var]
  >> simp[latest_version_is_version_var]
QED

(* SML-level terms for record field accesses that can't appear in Q.SPECL
   backtick quotations ("No consistent parse" in batch build). *)
local
  val v1 = mk_var("v1", ``:venom_state``)
  val s1 = mk_var("s1", ``:venom_state``)
  val bb = mk_var("bb", ``:basic_block``)
in
  val v1_cur_bb_tm = ``^v1.vs_current_bb``
  val s1_cur_bb_tm = ``^s1.vs_current_bb``
  val v1_prev_bb_tm = ``^v1.vs_prev_bb``
  val bb_insts_tm = ``^bb.bb_instructions``
  val bb_lbl_tm = ``^bb.bb_label``
end;
val univ_str_tm = ``UNIV : string set``;

(* Wrapper for exec_block_OK_not_halted via run_block *)
Triviality run_block_OK_not_halted:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  ONCE_REWRITE_TAC[run_block_def] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_distinct] >>
  imp_res_tac exec_block_OK_not_halted >> fs[]
QED

(* Wrapper for exec_block_ok_sets_prev_bb via run_block *)
Triviality run_block_ok_sets_prev_bb:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v ==> v.vs_prev_bb <> NONE
Proof
  ONCE_REWRITE_TAC[run_block_def] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_distinct] >>
  imp_res_tac exec_block_ok_sets_prev_bb >> fs[]
QED

(* OK/OK branch of the fuel induction — extracted as standalone Triviality
   to avoid rich-context issues. All facts are explicit
   hypotheses; no universals from the outer proof leak in. *)
Triviality ok_ok_step:
  !fuel ctx func func' bbs1 bbs2 rs0 dtree succ_map pred_map
   dom_frontiers dom_post_order live_in
   sigma (bb:basic_block) (bb':basic_block) (bb_mid:basic_block)
   phis rs_b_entry sigma_exit
   (v1:venom_state) (v2:venom_state) (s1:venom_state) (s2:venom_state).
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    fn_inst_wf func /\
    phi_extends func.fn_blocks bbs1 /\
    valid_phi_operands bbs1 bbs2 dtree succ_map rs0 /\
    valid_phi_coverage bbs1 dtree succ_map rs0 live_in /\
    phi_bases_live_in live_in func' /\
    valid_liveness_flow live_in func /\
    valid_liveness_uses live_in func /\
    func' = make_ssa_fn dom_frontiers dtree dom_post_order
              pred_map succ_map live_in func /\
    bbs2 = SND (rename_blocks rs0 bbs1 succ_map dtree) /\
    func'.fn_blocks = bbs2 /\
    lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
    lookup_block s1.vs_current_bb func'.fn_blocks = SOME bb' /\
    bb.bb_label = s1.vs_current_bb /\
    MEM bb func.fn_blocks /\
    bb_well_formed bb /\ bb.bb_instructions <> [] /\
    EVERY inst_wf bb.bb_instructions /\
    EVERY (\inst. EVERY colon_free inst.inst_outputs) bb.bb_instructions /\
    (!j. j < LENGTH bb.bb_instructions ==>
       ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
       (EL j bb.bb_instructions).inst_outputs = []) /\
    (!j. j < LENGTH bb.bb_instructions ==>
       ALL_DISTINCT (EL j bb.bb_instructions).inst_outputs) /\
    (!inst. MEM inst bb.bb_instructions ==>
       inst.inst_opcode <> PHI /\
       EVERY colon_free inst.inst_outputs /\
       ALL_DISTINCT inst.inst_outputs /\
       (~opcode_has_output inst.inst_opcode ==> inst.inst_outputs = [])) /\
    lookup_block bb.bb_label bbs1 = SOME bb_mid /\
    lookup_block s1.vs_current_bb bbs1 = SOME bb_mid /\
    lookup_block s1.vs_current_bb bbs2 = SOME bb' /\
    bb_mid.bb_instructions = phis ++ bb.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) phis /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
      bb.bb_label = SOME rs_b_entry /\
    ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
      s1.vs_current_bb = SOME rs_b_entry /\
    ssa_sim sigma s1 s2 /\
    (!x. colon_free x ==> ?n:num. sigma x = version_var x n) /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    s2.vs_current_bb = s1.vs_current_bb /\
    vars_colon_free s1 /\
    live_in_scope live_in s1 /\
    run_block fuel ctx bb s1 = OK v1 /\
    run_block fuel ctx bb' s2 = OK v2 /\
    ssa_sim sigma_exit v1 v2 /\
    (!x. colon_free x ==> ?n. sigma_exit x = version_var x n) /\
    (* sigma_exit = latest_version rs_a_end for live vars at current block *)
    (!x vs'. ALOOKUP live_in s1.vs_current_bb = SOME vs' /\ MEM x vs' ==>
       sigma_exit x = latest_version
         (FST (rename_block_insts rs_b_entry bb_mid.bb_instructions)) x) /\
    (* sigma_exit = latest_version rs_a_end for output vars *)
    (!x j. j < LENGTH bb.bb_instructions /\
           MEM x (EL j bb.bb_instructions).inst_outputs ==>
       sigma_exit x = latest_version
         (FST (rename_block_insts rs_b_entry bb_mid.bb_instructions)) x) /\
    vars_colon_free v1 /\
    (!inst bvar ver.
       MEM inst bb'.bb_instructions /\ inst.inst_opcode = PHI /\
       inst.inst_outputs = [version_var bvar ver] /\
       colon_free bvar /\ s1.vs_prev_bb <> NONE ==>
       resolve_phi (THE s1.vs_prev_bb) inst.inst_operands =
         SOME (Var (sigma bvar))) /\
    (!x. (!i. MEM i phis ==> ~MEM x i.inst_outputs) /\
         (?vs. ALOOKUP live_in s1.vs_current_bb = SOME vs /\
               MEM x vs) ==>
       latest_version rs_b_entry x = sigma x) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis)) /\
    (phis <> [] ==> s1.vs_prev_bb <> NONE) /\
    (!j. j < LENGTH phis ==>
       ?bvar. (EL j phis).inst_outputs = [bvar] /\ colon_free bvar) /\
    (!lbl bb1 inst.
       lookup_block lbl bbs1 = SOME bb1 /\
       MEM inst bb1.bb_instructions /\ inst.inst_opcode = PHI ==>
       ?bvar. inst.inst_outputs = [bvar] /\ colon_free bvar) /\
    (!lbl bb1.
       lookup_block lbl bbs1 = SOME bb1 ==>
       ALL_DISTINCT
         (FLAT (MAP (\i. i.inst_outputs)
           (FILTER (\i. i.inst_opcode = PHI) bb1.bb_instructions)))) /\
    (!blk inst. MEM blk func.fn_blocks /\
              MEM inst blk.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs /\
              ALL_DISTINCT inst.inst_outputs /\
              (~opcode_has_output inst.inst_opcode ==>
               inst.inst_outputs = [])) /\
    (!bb1. lookup_block v1.vs_current_bb bbs1 = SOME bb1 /\
       EXISTS (\i. i.inst_opcode = PHI) bb1.bb_instructions ==>
       v1.vs_prev_bb <> NONE) /\
    (!e. run_blocks (SUC fuel) ctx func s1 <> Error e) /\
    (!e. run_block fuel ctx bb s1 <> Error e) /\
    (!l. MEM l (dom_tree_labels dtree) ==>
       ?b. lookup_block l bbs1 = SOME b) /\
    MAP FST (block_rename_states rs0 bbs1 succ_map dtree) =
      dom_tree_labels dtree /\
    (!sigma' s1' s2'.
       wf_function func /\
       valid_dom_tree dom_frontiers dtree dom_post_order func /\
       valid_cfg_maps pred_map succ_map func /\
       valid_liveness live_in func /\
       fn_entry_no_preds func /\
       fn_inst_wf func /\
       ssa_sim sigma' s1' s2' /\
       (!x. colon_free x ==> ?n:num. sigma' x = version_var x n) /\
       s1'.vs_inst_idx = 0 /\ s2'.vs_inst_idx = 0 /\
       vars_colon_free s1' /\
       live_in_scope live_in s1' /\
       phi_bases_live_in live_in func' /\
       valid_liveness_flow live_in func /\
       valid_liveness_uses live_in func /\
       phi_extends func.fn_blocks bbs1 /\
       (!lbl bb1 inst.
          lookup_block lbl bbs1 = SOME bb1 /\
          MEM inst bb1.bb_instructions /\ inst.inst_opcode = PHI ==>
          ?bvar. inst.inst_outputs = [bvar] /\ colon_free bvar) /\
       func'.fn_blocks = bbs2 /\
       valid_phi_operands bbs1 bbs2 dtree succ_map rs0 /\
       valid_phi_coverage bbs1 dtree succ_map rs0 live_in /\
       (!bb_cur inst bvar ver.
          lookup_block s1'.vs_current_bb func'.fn_blocks = SOME bb_cur /\
          MEM inst bb_cur.bb_instructions /\ inst.inst_opcode = PHI /\
          inst.inst_outputs = [version_var bvar ver] /\
          colon_free bvar /\ s1'.vs_prev_bb <> NONE ==>
          resolve_phi (THE s1'.vs_prev_bb) inst.inst_operands =
            SOME (Var (sigma' bvar))) /\
       (!x bb1 rs_b.
          lookup_block s1'.vs_current_bb bbs1 = SOME bb1 /\
          ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
            s1'.vs_current_bb = SOME rs_b /\
          (!i. MEM i bb1.bb_instructions /\ i.inst_opcode = PHI ==>
               ~MEM x i.inst_outputs) /\
          (?vs. ALOOKUP live_in s1'.vs_current_bb = SOME vs /\
                MEM x vs) ==>
          latest_version rs_b x = sigma' x) /\
       (!lbl bb1.
          lookup_block lbl bbs1 = SOME bb1 ==>
          ALL_DISTINCT
            (FLAT (MAP (\i. i.inst_outputs)
              (FILTER (\i. i.inst_opcode = PHI) bb1.bb_instructions)))) /\
       (!bb1. lookup_block s1'.vs_current_bb bbs1 = SOME bb1 /\
          EXISTS (\i. i.inst_opcode = PHI) bb1.bb_instructions ==>
          s1'.vs_prev_bb <> NONE) /\
       (!e. run_blocks fuel ctx func s1' <> Error e) /\
       (!blk inst. MEM blk func.fn_blocks /\
                 MEM inst blk.bb_instructions ==>
                 inst.inst_opcode <> PHI /\
                 EVERY colon_free inst.inst_outputs /\
                 ALL_DISTINCT inst.inst_outputs /\
                 (~opcode_has_output inst.inst_opcode ==>
                  inst.inst_outputs = [])) ==>
       result_equiv UNIV
         (run_blocks fuel ctx func s1')
         (run_blocks fuel ctx func' s2')) ==>
    result_equiv UNIV
      (run_blocks fuel ctx func v1)
      (run_blocks fuel ctx func' v2)
Proof
  rpt strip_tac >>
  (* v1/v2 basic properties *)
  `~(v1:venom_state).vs_halted` by metis_tac[run_block_OK_not_halted] >>
  `~(v2:venom_state).vs_halted` by metis_tac[run_block_OK_not_halted] >>
  `(v1:venom_state).vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
  `(v2:venom_state).vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
  (* No error at successor *)
  `!e. run_blocks fuel ctx func v1 <> Error e` by (
    spose_not_then strip_assume_tac >>
    `run_blocks (SUC fuel) ctx func s1 = Error e` by (
      ONCE_REWRITE_TAC [run_blocks_unfold] >>
      PURE_REWRITE_TAC [GSYM run_block_def] >> simp[]) >>
    metis_tac[]) >>
  (* live_in_scope preserved *)
  `live_in_scope live_in v1` by (
    irule live_in_scope_preserved >>
    qexistsl_tac [`bb`, `ctx`, `fuel`, `func`, `s1`] >> simp[]) >>
  (* rs_a_end abbreviation *)
  qabbrev_tac `rs_a_end = FST (rename_block_insts rs_b_entry
    (bb_mid:basic_block).bb_instructions)` >>
  `FST (rename_block_insts
     (FST (rename_block_insts rs_b_entry phis)) (bb:basic_block).bb_instructions) =
   rs_a_end` by (
    simp[Abbr `rs_a_end`] >>
    qpat_assum `(bb_mid:basic_block).bb_instructions = _`
      (fn eq => REWRITE_TAC [eq]) >>
    simp[rename_block_insts_fst_append]) >>
  (* Navigation *)
  `(v1:venom_state).vs_prev_bb = SOME (s1:venom_state).vs_current_bb` by (
    mp_tac run_block_ok_navigation >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `v1`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  `MEM (v1:venom_state).vs_current_bb (bb_succs bb)` by (
    mp_tac run_block_ok_navigation >>
    disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `v1`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  (* succs_preserved *)
  `succs_preserved bbs1 bbs2` by (
    ASM_REWRITE_TAC[] >>
    ACCEPT_TAC (Q.SPECL [`dtree`, `bbs1`, `rs0`, `succ_map`]
      (CONJUNCT1 rename_blocks_succs_preserved_export))) >>
  (* bb_succs bb_mid = bb_succs bb *)
  `bb_succs bb_mid = bb_succs bb` by (
    mp_tac (Q.SPECL [`phis`, `(bb:basic_block).bb_instructions`, `bb_mid`, `bb`]
              bb_succs_phi_prepend) >>
    impl_tac >- (rpt conj_tac >> TRY REFL_TAC >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  `MEM (v1:venom_state).vs_current_bb (bb_succs bb_mid)` by metis_tac[] >>
  (* Successor in fn_labels *)
  `MEM (v1:venom_state).vs_current_bb (fn_labels func)` by
    metis_tac[wf_function_def, fn_succs_closed_def] >>
  `MEM (v1:venom_state).vs_current_bb (dom_tree_labels dtree)` by
    metis_tac[fn_label_in_dtree] >>
  (* Successor block in bbs1 *)
  `?bb_mid_next. lookup_block (v1:venom_state).vs_current_bb bbs1 = SOME bb_mid_next` by
    metis_tac[] >>
  (* Successor in block_rename_states *)
  `MEM (v1:venom_state).vs_current_bb
     (MAP FST (block_rename_states rs0 bbs1 succ_map dtree))` by
    metis_tac[] >>
  `?rs_b_next. ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
     (v1:venom_state).vs_current_bb = SOME rs_b_next` by metis_tac[MEM_ALOOKUP_SOME] >>
  (* bb_succs bb' = bb_succs bb_mid via succs_preserved *)
  `lookup_block (s1:venom_state).vs_current_bb bbs2 = SOME bb'` by metis_tac[] >>
  `bb_succs bb' = bb_succs bb_mid` by (
    qpat_assum `succs_preserved bbs1 bbs2` mp_tac >>
    PURE_REWRITE_TAC[succs_preserved_def] >>
    disch_then (qspecl_then [`(s1:venom_state).vs_current_bb`, `bb'`] mp_tac) >>
    simp[] >>
    strip_tac >>
    `bb0 = bb_mid` by metis_tac[optionTheory.SOME_11] >>
    simp[]) >>
  `MEM (v1:venom_state).vs_current_bb (bb_succs bb')` by metis_tac[] >>
  (* phi_resolve at successor — via extracted Triviality *)
  `rs_a_end = FST (rename_block_insts rs_b_entry (bb_mid:basic_block).bb_instructions)` by (
    qpat_assum `Abbrev (rs_a_end = _)`
      (fn th => ACCEPT_TAC (PURE_REWRITE_RULE [markerTheory.Abbrev_def] th))) >>
  mp_tac (Q.SPECL [`(v1:venom_state).vs_prev_bb`, `(s1:venom_state).vs_current_bb`,
      `(v1:venom_state).vs_current_bb`, `func'`, `bbs1`, `bbs2`,
      `bb_mid`, `bb'`, `rs_b_entry`, `rs_a_end`,
      `dtree`, `succ_map`, `rs0`] phi_resolve_at_succ) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* ===== Weakened coverage: for live non-PHI x at successor,
     latest_version rs_b = sigma_exit ===== *)
  `!x bb1 rs_b.
     lookup_block (v1:venom_state).vs_current_bb bbs1 = SOME bb1 /\
     ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
       (v1:venom_state).vs_current_bb = SOME rs_b /\
     (!i. MEM i (bb1:basic_block).bb_instructions /\ (i:instruction).inst_opcode = PHI ==>
          ~MEM x (i:instruction).inst_outputs) /\
     (?vs. ALOOKUP live_in (v1:venom_state).vs_current_bb = SOME vs /\
           MEM x vs) ==>
     latest_version rs_b x = sigma_exit x` by suspend "coverage" >>
  (* Bridge: derive phi_resolve with sigma_exit from phi_resolve_at_succ *)
  `!bb_cur inst bvar ver.
     lookup_block (v1:venom_state).vs_current_bb func'.fn_blocks = SOME bb_cur /\
     MEM inst bb_cur.bb_instructions /\ inst.inst_opcode = PHI /\
     inst.inst_outputs = [version_var bvar ver] /\ colon_free bvar /\
     (v1:venom_state).vs_prev_bb <> NONE ==>
     resolve_phi (THE (v1:venom_state).vs_prev_bb) inst.inst_operands =
       SOME (Var (sigma_exit bvar))` by suspend "phi_resolve_sigma" >>
  (* Apply IH directly with sigma_exit, v1, v2 *)
  qpat_x_assum `!sigma' s1' s2'. _ ==>
    result_equiv UNIV (run_blocks fuel ctx func s1')
      (run_blocks fuel ctx func' s2')`
    (qspecl_then [`sigma_exit`, `v1`, `v2`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

(* Bridge: phi_resolve with sigma_exit
   phi_resolve_at_succ gives latest_version rs_a_end bvar,
   IH needs sigma_exit bvar. Bridge via phi_bases_live_in + valid_liveness_flow. *)
Resume ok_ok_step[phi_resolve_sigma]:
  rpt strip_tac >>
  (* From phi_resolve_at_succ *)
  qpat_x_assum `!bb_cur' inst' bvar' ver'.
     lookup_block _ func'.fn_blocks = SOME bb_cur' /\ _ ==>
     resolve_phi _ _ = SOME (Var (latest_version rs_a_end _))`
    (qspecl_then [`bb_cur`, `inst`, `bvar`, `ver`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  (* From phi_bases_live_in: bvar is live at v1.vs_current_bb *)
  `?vs_succ. ALOOKUP live_in (v1:venom_state).vs_current_bb = SOME vs_succ /\
             MEM bvar vs_succ` by suspend "live_at_succ" >>
  pop_assum strip_assume_tac >>
  (* From valid_liveness_flow: live at successor -> live at current V output *)
  `sigma_exit bvar = latest_version rs_a_end bvar` by
    suspend "sigma_bridge" >>
  qpat_x_assum `sigma_exit bvar = _` (fn eq => REWRITE_TAC [eq]) >>
  first_assum ACCEPT_TAC
QED

(* Coverage: for live non-PHI x at successor, latest_version rs_b = sigma_exit *)
Resume ok_ok_step[coverage]:
    rpt strip_tac >>
    `bb1 = bb_mid_next` by metis_tac[optionTheory.SOME_11] >>
    pop_assum SUBST_ALL_TAC >>
    `rs_b = rs_b_next` by metis_tac[optionTheory.SOME_11] >>
    pop_assum SUBST_ALL_TAC >>
    (* Step 1: latest_version rs_b_next x = latest_version rs_a_end x
       from valid_phi_coverage *)
    `latest_version rs_b_next x = latest_version rs_a_end x` by (
      spose_not_then strip_assume_tac >>
      qpat_x_assum `rs_a_end = _` (fn eq => SUBST_ALL_TAC eq) >>
      qpat_x_assum `valid_phi_coverage _ _ _ _ _` mp_tac >>
      PURE_REWRITE_TAC[valid_phi_coverage_def] >>
      disch_then (qspecl_then [`(s1:venom_state).vs_current_bb`,
        `(v1:venom_state).vs_current_bb`,
        `bb_mid`, `bb_mid_next`, `rs_b_entry`, `rs_b_next`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qspecl_then [`x`, `vs`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >>
      first_x_assum (qspec_then `i` mp_tac) >>
      ASM_REWRITE_TAC[]) >>
    (* Step 2: sigma_exit x = latest_version rs_a_end x
       via valid_liveness_flow: x live at successor -> live at current V output *)
    `sigma_exit x = latest_version rs_a_end x` by (
      qpat_x_assum `valid_liveness_flow _ _` mp_tac >>
      PURE_REWRITE_TAC[valid_liveness_flow_def] >>
      disch_then (qspecl_then [`bb`, `(v1:venom_state).vs_current_bb`,
        `vs`, `x`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac
      >- ((* Subst bb.bb_label -> s1.vs_current_bb *)
         qpat_x_assum `(bb:basic_block).bb_label = _`
           (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
         qpat_x_assum `!x' vs''. _ /\ _ ==> sigma_exit x' = _`
           (qspecl_then [`x`, `vs'`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         simp_tac std_ss [])
      >> (* x defined by non-terminator in bb *)
         rename1 `MEM inst' bb.bb_instructions` >>
         `?j'. j' < LENGTH (bb:basic_block).bb_instructions /\
               EL j' (bb:basic_block).bb_instructions = inst'` by
           metis_tac[MEM_EL] >>
         qpat_x_assum `!x' j'. j' < LENGTH bb.bb_instructions /\ _ ==> sigma_exit x' = _`
           (qspecl_then [`x`, `j'`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
         simp_tac std_ss []) >>
    pop_assum (fn eq => REWRITE_TAC [eq]) >>
    first_assum ACCEPT_TAC
QED

Resume ok_ok_step[sigma_bridge]:
  qpat_assum `valid_liveness_flow _ _` mp_tac >>
  PURE_REWRITE_TAC[valid_liveness_flow_def] >>
  disch_then (qspecl_then [`bb`, `(v1:venom_state).vs_current_bb`,
    `vs_succ`, `bvar`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac
  >- ((* Subst bb.bb_label -> s1.vs_current_bb in assumptions *)
     qpat_x_assum `(bb:basic_block).bb_label = _`
       (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
     qpat_x_assum `!x' vs''. _ /\ _ ==> sigma_exit x' = _`
       (qspecl_then [`bvar`, `vs'`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     simp_tac std_ss [])
  >> rename1 `MEM inst' (bb:basic_block).bb_instructions` >>
     `?j'. j' < LENGTH (bb:basic_block).bb_instructions /\
           EL j' (bb:basic_block).bb_instructions = inst'` by
       metis_tac[MEM_EL] >>
     qpat_x_assum `!x' j'. j' < LENGTH bb.bb_instructions /\ _ ==> sigma_exit x' = _`
       (qspecl_then [`bvar`, `j'`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
     simp_tac std_ss []
QED

Resume ok_ok_step[live_at_succ]:
  qpat_x_assum `phi_bases_live_in _ _` mp_tac >>
  PURE_REWRITE_TAC[phi_bases_live_in_def] >>
  disch_then (qspecl_then [`(v1:venom_state).vs_current_bb`,
    `bb_cur`, `inst`, `bvar`, `ver`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    qpat_x_assum `(inst:instruction).inst_outputs = _` (fn eq => REWRITE_TAC[eq]) >>
    simp_tac std_ss [listTheory.MEM]) >>
  strip_tac >> qexists_tac `vs` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise ok_ok_step;

(* Core fuel induction.
   No callback — directly uses phi_args_ok_from_pipeline.
   phi_resolve_ok is an induction hypothesis: at entry block vacuous,
   at IH call derived from valid_phi_operands.
   coverage/distinct/prev_bb are per-block invariants threaded through IH. *)
Theorem run_blocks_ssa_sim:
  !fuel dom_frontiers dtree dom_post_order pred_map succ_map live_in
   func sigma bbs1 rs0 ctx s1 s2.
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    let bbs2 = SND (rename_blocks rs0 bbs1 succ_map dtree) in
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    fn_inst_wf func /\
    ssa_sim sigma s1 s2 /\
    (!x. colon_free x ==> ?n:num. sigma x = version_var x n) /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    vars_colon_free s1 /\
    live_in_scope live_in s1 /\
    phi_bases_live_in live_in func' /\
    valid_liveness_flow live_in func /\
    valid_liveness_uses live_in func /\
    (* Pipeline structure *)
    phi_extends func.fn_blocks bbs1 /\
    (* PHI outputs in bbs1 are singleton colon_free *)
    (!lbl bb_mid inst.
       lookup_block lbl bbs1 = SOME bb_mid /\
       MEM inst bb_mid.bb_instructions /\ inst.inst_opcode = PHI ==>
       ?bv. inst.inst_outputs = [bv] /\ colon_free bv) /\
    func'.fn_blocks = bbs2 /\
    valid_phi_operands bbs1 bbs2 dtree succ_map rs0 /\
    valid_phi_coverage bbs1 dtree succ_map rs0 live_in /\
    (* PHI resolution at current block entry *)
    (!bb_cur inst base ver.
       lookup_block s1.vs_current_bb func'.fn_blocks = SOME bb_cur /\
       MEM inst bb_cur.bb_instructions /\ inst.inst_opcode = PHI /\
       inst.inst_outputs = [version_var base ver] /\
       colon_free base /\ s1.vs_prev_bb <> NONE ==>
       resolve_phi (THE s1.vs_prev_bb) inst.inst_operands =
         SOME (Var (sigma base))) /\
    (* Coverage: at current block, live non-PHI vars agree *)
    (!x bb_mid rs_b.
       lookup_block s1.vs_current_bb bbs1 = SOME bb_mid /\
       ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
         s1.vs_current_bb = SOME rs_b /\
       (!i. MEM i bb_mid.bb_instructions /\ i.inst_opcode = PHI ==>
            ~MEM x i.inst_outputs) /\
       (?vs. ALOOKUP live_in s1.vs_current_bb = SOME vs /\
             MEM x vs) ==>
       latest_version rs_b x = sigma x) /\
    (* Distinct PHI output bases — universal over all blocks *)
    (!lbl bb_mid.
       lookup_block lbl bbs1 = SOME bb_mid ==>
       ALL_DISTINCT
         (FLAT (MAP (\i. i.inst_outputs)
           (FILTER (\i. i.inst_opcode = PHI) bb_mid.bb_instructions)))) /\
    (* PHIs only in blocks with predecessor *)
    (!bb_mid.
       lookup_block s1.vs_current_bb bbs1 = SOME bb_mid /\
       EXISTS (\i. i.inst_opcode = PHI) bb_mid.bb_instructions ==>
       s1.vs_prev_bb <> NONE) /\
    (* No errors in original execution *)
    (!e. run_blocks fuel ctx func s1 <> Error e) /\
    (* Per-instruction well-formedness for original func *)
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs /\
              ALL_DISTINCT inst.inst_outputs /\
              (~opcode_has_output inst.inst_opcode ==>
               inst.inst_outputs = [])) ==>
    result_equiv UNIV
      (run_blocks fuel ctx func s1)
      (run_blocks fuel ctx func' s2)
Proof
  Induct_on `fuel` >>
  simp_tac std_ss [LET_THM] >>
  RULE_ASSUM_TAC (SIMP_RULE std_ss [LET_THM]) >>
  rpt strip_tac
  (* Base: fuel = 0 *)
  >- (fs[Once run_blocks_def, result_equiv_def]) >>
  (* Step: fuel = SUC fuel — keep IH in the assumption list.
     holbuild checkpoints do not reliably restore ML ref side effects. *)
  CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [run_blocks_unfold]))) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_blocks_unfold])) >>
  PURE_REWRITE_TAC [GSYM run_block_def] >>
  qabbrev_tac `func' = make_ssa_fn dom_frontiers dtree dom_post_order
    pred_map succ_map live_in func` >>
  qabbrev_tac `bbs2 = SND (rename_blocks rs0 bbs1 succ_map dtree)` >>
  qpat_assum `Abbrev (bbs2 = _)` (fn th => let
    val _ = bbs2_eq_ref := PURE_REWRITE_RULE [markerTheory.Abbrev_def] th
  in ASSUME_TAC th end) >>
  `MAP (\bb. bb.bb_label) func.fn_blocks =
   MAP (\bb. bb.bb_label) func'.fn_blocks`
    by simp[Abbr `func'`, make_ssa_fn_preserves_labels] >>
  `s2.vs_current_bb = s1.vs_current_bb` by
    metis_tac[ssa_sim_current_bb] >>
  `IS_SOME (lookup_block s1.vs_current_bb func.fn_blocks) <=>
   IS_SOME (lookup_block s1.vs_current_bb func'.fn_blocks)` by
    metis_tac[lookup_block_labels_agree] >>
  Cases_on `lookup_block s1.vs_current_bb func.fn_blocks`
  >- (`lookup_block s2.vs_current_bb func'.fn_blocks = NONE` by (
        gvs[] >>
        Cases_on `lookup_block s1.vs_current_bb func'.fn_blocks` >> gvs[]) >>
      simp[result_equiv_def]) >>
  `?bb'. lookup_block s1.vs_current_bb func'.fn_blocks = SOME bb'` by (
    gvs[] >>
    Cases_on `lookup_block s1.vs_current_bb func'.fn_blocks` >> gvs[]) >>
  `lookup_block s1.vs_current_bb bbs2 = SOME bb'` by gvs[] >>
  gvs[] >>
  rename1 `lookup_block _ func.fn_blocks = SOME bb` >>
  `!e. run_block fuel ctx bb s1 <> Error e` by (
    spose_not_then strip_assume_tac >>
    `run_blocks (SUC fuel) ctx func s1 = Error e` by (
      ONCE_REWRITE_TAC [run_blocks_unfold] >>
      PURE_REWRITE_TAC [GSYM run_block_def] >> simp[]) >>
    metis_tac[]) >>
  `MEM bb func.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `bb.bb_instructions <> []` by
    (qpat_assum `bb_well_formed bb`
       (strip_assume_tac o REWRITE_RULE [bb_well_formed_def])) >>
  `EVERY inst_wf bb.bb_instructions` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `fn_inst_wf func` mp_tac >>
     simp[fn_inst_wf_def] >> metis_tac[]) >>
  `!inst. MEM inst bb.bb_instructions ==>
    inst.inst_opcode <> PHI /\
    EVERY colon_free inst.inst_outputs /\
    ALL_DISTINCT inst.inst_outputs /\
    (~opcode_has_output inst.inst_opcode ==> inst.inst_outputs = [])` by
    metis_tac[] >>
  `EVERY (\inst. EVERY colon_free inst.inst_outputs) bb.bb_instructions` by (
    simp[EVERY_MEM] >> metis_tac[]) >>
  `!j. j < LENGTH bb.bb_instructions ==>
    ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
    (EL j bb.bb_instructions).inst_outputs = []` by
    metis_tac[MEM_EL] >>
  `!j. j < LENGTH bb.bb_instructions ==>
    ALL_DISTINCT (EL j bb.bb_instructions).inst_outputs` by
    metis_tac[MEM_EL] >>
  `bb.bb_label = s1.vs_current_bb` by metis_tac[lookup_block_label] >>
  (* Derive bb_mid, phis, rs_b_entry before phi_args_ok_from_pipeline *)
  `ALL_DISTINCT (MAP (\b. b.bb_label) func.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `?bb_mid phis.
    lookup_block bb.bb_label bbs1 = SOME bb_mid /\
    bb_mid.bb_instructions = phis ++ bb.bb_instructions /\
    EVERY (\i. i.inst_opcode = PHI) phis` by (
    drule_all phi_extends_lookup >> strip_tac >>
    qexistsl_tac [`bb_mid`, `phis`] >> simp[]) >>
  `MEM bb.bb_label (fn_labels func)` by
    metis_tac[fn_labels_def, MEM_MAP_f] >>
  `MEM bb.bb_label (dom_tree_labels dtree)` by
    metis_tac[fn_label_in_dtree] >>
  `!l. MEM l (dom_tree_labels dtree) ==> ?b. lookup_block l bbs1 = SOME b` by (
    mp_tac dtree_labels_have_blocks >>
    disch_then (qspecl_then [`dtree`, `func`, `bbs1`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp[]) >>
  `MAP FST (block_rename_states rs0 bbs1 succ_map dtree) =
   dom_tree_labels dtree` by (
    irule (CONJUNCT1 block_rename_states_keys) >>
    first_assum ACCEPT_TAC) >>
  `MEM bb.bb_label (MAP FST (block_rename_states rs0 bbs1 succ_map dtree))` by (
    qpat_x_assum `MAP FST _ = dom_tree_labels _`
      (fn eq => REWRITE_TAC [eq]) >>
    first_assum ACCEPT_TAC) >>
  drule_then strip_assume_tac MEM_ALOOKUP_SOME >>
  rename1 `ALOOKUP _ _ = SOME rs_b_entry` >>
  (* Specialize the 3 per-block hypotheses now that we have bb_mid, rs_b_entry *)
  `lookup_block s1.vs_current_bb bbs1 = SOME bb_mid` by (
    qpat_assum `bb.bb_label = _` (fn eq => REWRITE_TAC [GSYM eq]) >>
    first_assum ACCEPT_TAC) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
    (FILTER (\i. i.inst_opcode = PHI) bb_mid.bb_instructions)))` by (
    qpat_assum `!lbl bb_mid. lookup_block lbl bbs1 = SOME bb_mid ==> _`
      (qspecl_then [`(s1:venom_state).vs_current_bb`, `bb_mid`] mp_tac) >> simp[]) >>
  `EXISTS (\i. i.inst_opcode = PHI) bb_mid.bb_instructions ==>
    s1.vs_prev_bb <> NONE` by (
    strip_tac >>
    qpat_x_assum `!bb_mid. _ /\ EXISTS _ _ ==> _` drule_all >>
    simp_tac std_ss []) >>
  `ALOOKUP (block_rename_states rs0 bbs1 succ_map dtree)
    s1.vs_current_bb = SOME rs_b_entry` by (
    qpat_assum `bb.bb_label = _` (fn eq => REWRITE_TAC [GSYM eq]) >>
    first_assum ACCEPT_TAC) >>
  `!x. (!i. MEM i bb_mid.bb_instructions /\ i.inst_opcode = PHI ==>
            ~MEM x i.inst_outputs) /\
       (?vs. ALOOKUP live_in s1.vs_current_bb = SOME vs /\ MEM x vs) ==>
       latest_version rs_b_entry x = sigma x` by (
    rpt strip_tac >>
    qpat_x_assum `!x bb_mid rs_b. _`
      (qspecl_then [`x`, `bb_mid`, `rs_b_entry`] mp_tac) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `vs` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >>
  (* Bridge: derive key facts from phis ++ body decomposition *)
  `EVERY (\x. x.inst_opcode <> PHI) bb.bb_instructions` by (
    PURE_REWRITE_TAC[EVERY_MEM] >> rpt strip_tac >>
    first_x_assum drule >> simp[]) >>
  `FILTER (\i. i.inst_opcode = PHI) bb_mid.bb_instructions = phis` by (
    qpat_assum `bb_mid.bb_instructions = _` (fn eq => REWRITE_TAC [eq]) >>
    REWRITE_TAC[FILTER_APPEND_DISTRIB] >>
    `FILTER (\i. i.inst_opcode = PHI) phis = phis` by (
      simp_tac std_ss [FILTER_EQ_ID] >> first_assum ACCEPT_TAC) >>
    `FILTER (\i. i.inst_opcode = PHI) bb.bb_instructions = []` by (
      simp_tac std_ss [FILTER_EQ_NIL] >> first_assum ACCEPT_TAC) >>
    ASM_REWRITE_TAC[APPEND_NIL]) >>
  (* Coverage bridge *)
  `!x. (!i. MEM i phis ==> ~MEM x i.inst_outputs) /\
       (?vs. ALOOKUP live_in s1.vs_current_bb = SOME vs /\ MEM x vs) ==>
       latest_version rs_b_entry x = sigma x` by (
    rpt strip_tac >>
    `!i. MEM i bb_mid.bb_instructions /\ i.inst_opcode = PHI ==>
         ~MEM x i.inst_outputs` by (
      mp_tac (Q.SPECL [`phis`, `bb_mid`, `x`] coverage_bridge_inner) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      simp_tac std_ss []) >>
    qpat_x_assum `!x'. _ ==> latest_version rs_b_entry x' = _`
      (qspec_then `x` mp_tac) >>
    (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qexists_tac `vs` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    disch_then ACCEPT_TAC) >>
  (* ALL_DISTINCT bridge *)
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis))` by (
    qpat_assum `FILTER _ _ = phis`
      (fn eq => qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ (FILTER _ _)))`
        (fn th => ACCEPT_TAC (REWRITE_RULE [eq] th)))) >>
  (* prev_bb bridge: derive phis <> [] ==> s1.vs_prev_bb <> NONE
     as standalone assumption for both phi_args_ok_from_pipeline AND ok_ok_step.
     Context has: EXISTS P bb_mid.bb_instructions ==> prev_bb <> NONE
     and: bb_mid.bb_instructions = phis ++ bb.bb_instructions
     and: EVERY P phis *)
  `phis <> [] ==> s1.vs_prev_bb <> NONE` by (
    DISCH_TAC >>
    qpat_assum `EXISTS _ bb_mid.bb_instructions ==> _` mp_tac >>
    (impl_tac >- (
      qpat_assum `bb_mid.bb_instructions = _`
        (fn eq => PURE_REWRITE_TAC [eq]) >>
      PURE_REWRITE_TAC[EXISTS_APPEND] >>
      DISJ1_TAC >>
      PURE_REWRITE_TAC[EXISTS_MEM] >>
      Cases_on `phis` >- full_simp_tac std_ss [] >>
      qexists_tac `h` >>
      full_simp_tac std_ss [MEM, EVERY_DEF])) >>
    simp_tac std_ss []) >>
  (* Per-PHI output structure *)
  mp_tac phi_outputs_from_prefix >>
  disch_then (qspecl_then [`phis`, `(bb:basic_block).bb_instructions`, `(bb:basic_block).bb_label`,
    `bbs1`, `bb_mid`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Apply phi_args_ok_from_pipeline *)
  mp_tac (Q.SPECL [`bb`, `bb'`, `sigma`, `bbs1`, `dtree`,
    `succ_map`, `rs0`, `func`, `func'`, `s1`, `s2`, `live_in`,
    `bb_mid`, `rs_b_entry`, `phis`, `dom_frontiers`, `dom_post_order`]
    phi_args_ok_from_pipeline) >>
  (impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    TRY (simp[Abbr `func'`]) >>
    TRY (qpat_assum `func'.fn_blocks = SND _`
           (fn th => REWRITE_TAC [th]) >> first_assum ACCEPT_TAC) >>
    TRY (qpat_assum `bb.bb_label = _` (fn th =>
           ACCEPT_TAC (GSYM th)) >> NO_TAC) >>
    TRY (qpat_assum `bb.bb_label = _` (fn th => REWRITE_TAC [th]) >>
         first_assum ACCEPT_TAC) >>
    TRY (simp[]))) >>
  strip_tac >>
  (* rs_mid = FST (rename_block_insts rs_b_entry phis),
     rs_a_end = FST (rename_block_insts rs_b_entry bb_mid.bb_instructions) *)
  qabbrev_tac `rs_mid = FST (rename_block_insts rs_b_entry phis)` >>
  `FST (rename_block_insts rs_mid (bb:basic_block).bb_instructions) =
     FST (rename_block_insts rs_b_entry (bb_mid:basic_block).bb_instructions)` by (
    simp[Abbr `rs_mid`] >>
    qpat_assum `bb_mid.bb_instructions = _`
      (fn eq => REWRITE_TAC [eq]) >>
    simp[rename_block_insts_fst_append]) >>
  (* Derive operand agreement for run_block_ssa_sim:
     sigma_out x = latest_version rs_mid x for used-before-def x in bb *)
  `!j x. j < LENGTH (bb:basic_block).bb_instructions /\
         MEM (Var x) (EL j (bb:basic_block).bb_instructions).inst_operands /\
         (!m. m < j ==> ~MEM x (EL m (bb:basic_block).bb_instructions).inst_outputs) ==>
         sigma_out x = latest_version rs_mid x` by (
    rpt strip_tac >>
    Cases_on `?i. MEM i phis /\ MEM x (i:instruction).inst_outputs`
    >- ((* x is a PHI output *)
       pop_assum strip_assume_tac >>
       qpat_x_assum `!x' i'. MEM i' phis /\ MEM x' i'.inst_outputs ==> _`
         (qspecl_then [`x`, `i`] mp_tac) >>
       simp[] >> disch_then SUBST1_TAC >>
       simp[Abbr `rs_mid`])
    >> (* x is NOT a PHI output *)
       `!i'. MEM i' phis ==> ~MEM x (i':instruction).inst_outputs` by
         (rpt strip_tac >> metis_tac[]) >>
       qpat_x_assum `!x'. (!i'. MEM i' phis ==> _) ==> sigma_out x' = sigma x'`
         (qspec_then `x` mp_tac) >> simp[] >> DISCH_TAC >>
       (* x is live-in via valid_liveness_uses *)
       `?vs. ALOOKUP live_in (s1:venom_state).vs_current_bb = SOME vs /\
           MEM x vs` by (
         qpat_x_assum `valid_liveness_uses _ _` mp_tac >>
         simp[valid_liveness_uses_def] >>
         disch_then (qspecl_then [`bb`, `x`, `j`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         strip_tac >>
         qpat_assum `bb.bb_label = _` (fn eq =>
           PURE_REWRITE_TAC [GSYM eq]) >>
         qexists_tac `vs` >> simp[]) >>
       qpat_x_assum `!x'. (!i'. MEM i' phis ==> _) /\ _ ==>
         latest_version rs_b_entry x' = sigma x'`
         (qspec_then `x` mp_tac) >>
       impl_tac >- (conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qexists_tac `vs` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
       DISCH_TAC >>
       `latest_version rs_mid x = latest_version rs_b_entry x` by (
         qpat_assum `Abbrev (rs_mid = _)` (fn ab =>
           PURE_REWRITE_TAC [PURE_REWRITE_RULE [markerTheory.Abbrev_def] ab]) >>
         irule rename_block_insts_non_output_stable_any >>
         first_assum ACCEPT_TAC) >>
       simp[]) >>
  (* Apply run_block_ssa_sim — extract terms from phi_args_ok to ensure
     SAME ML variable identities. Type-instantiate the polymorphic sigma. *)
  (fn (asl, gl) => let
    val pao_tm = valOf (List.find (fn a =>
      can (match_term ``phi_args_ok a b c d e f g``) a) asl)
    val [bb_tm, bb'_tm, sigma_tm, sigma_out_tm, s1_tm, s2_tm, rs_tm] =
      snd (strip_comb pao_tm)
    val run_bl_asm = valOf (List.find (fn a => let
      val s = term_to_string a
    in String.isSubstring "run_block" s andalso
       String.isSubstring "Error" s end) asl)
    val (_, fbc) = strip_forall run_bl_asm
    val neg_tm = dest_neg fbc
    val (lhs_eq, _) = dest_eq neg_tm
    val args = snd (strip_comb lhs_eq)
    val fuel_tm = List.nth(args, 0)
    val ctx_tm = List.nth(args, 1)
    val sigma_ty = type_of sigma_tm
    val thm0 = INST_TYPE [alpha |-> sigma_ty] run_block_ssa_sim
    val spec = SPECL [fuel_tm, ctx_tm, bb_tm, bb'_tm, sigma_tm,
      sigma_out_tm, s1_tm, s2_tm, rs_tm] thm0
  in
    (mp_tac spec >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac) (asl, gl)
  end) >>
  (* Stash \forall v v' in ML ref before case analysis *)
  (* Split result cases before opening ssa_result_equiv_def. *)
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx bb' s2` >- (
    gvs[ssa_result_equiv_def] >>
    (* OK/OK case remains *)
    rename1 `ssa_sim sigma_exit (v1:venom_state) (v2:venom_state)` >>
    qabbrev_tac `rs_a_end =
      FST (rename_block_insts rs_b_entry (phis ++ bb.bb_instructions))` >>
    `!x vs'. ALOOKUP live_in s1.vs_current_bb = SOME vs' /\ MEM x vs' ==>
       sigma_exit x = latest_version rs_a_end x` by (
      rpt strip_tac >>
      Cases_on `?j'. j' < LENGTH (bb:basic_block).bb_instructions /\
                     MEM x (EL j' (bb:basic_block).bb_instructions).inst_outputs`
      >- ((* x is a bb output *)
         pop_assum strip_assume_tac >>
         qpat_x_assum `!x j. j < LENGTH _ /\ MEM x (EL j _).inst_outputs ==>
           sigma_exit x = latest_version rs_a_end x`
           (qspecl_then [`x`, `j'`] mp_tac) >> simp[])
      >> (* x is not a bb output *)
         `!j'. j' < LENGTH (bb:basic_block).bb_instructions ==>
               ~MEM x (EL j' (bb:basic_block).bb_instructions).inst_outputs`
           by (rpt strip_tac >> CCONTR_TAC >>
               qpat_x_assum `~(?j'. _)` mp_tac >> simp[] >>
               qexists_tac `j'` >> simp[]) >>
         `sigma_exit x = sigma_out x` by (
           qpat_x_assum `!x. (!j. j < LENGTH _ ==> ~MEM x _) ==>
             sigma_exit x = sigma_out x`
             (qspec_then `x` mp_tac) >> simp[]) >>
         Cases_on `?i. MEM i phis /\ MEM x (i:instruction).inst_outputs`
         >- ((* x is a PHI output *)
            pop_assum strip_assume_tac >>
            `sigma_out x = latest_version rs_mid x` by (
              qpat_x_assum `!x' i. MEM i phis /\ MEM x' i.inst_outputs ==>
                sigma_out x' = latest_version rs_mid x'`
                (qspecl_then [`x`, `i`] mp_tac) >> simp[]) >>
            `latest_version rs_a_end x = latest_version rs_mid x` by (
              qpat_assum `FST (rename_block_insts rs_mid _) = rs_a_end`
                (fn eq => REWRITE_TAC [GSYM eq]) >>
              irule rename_block_insts_non_output_stable_any >>
              rpt strip_tac >> metis_tac[MEM_EL]) >>
            simp[])
         >> (* x is not a PHI output *)
            `!i. MEM i phis ==> ~MEM x (i:instruction).inst_outputs`
              by (rpt strip_tac >> CCONTR_TAC >>
                  qpat_x_assum `~(?i. _)` mp_tac >> simp[] >>
                  qexists_tac `i` >> simp[]) >>
            `sigma_out x = sigma x` by (
              qpat_x_assum `!x'. (!i. MEM i phis ==> ~MEM x' _) ==>
                sigma_out x' = sigma x'`
                (qspec_then `x` mp_tac) >> simp[]) >>
            `latest_version rs_b_entry x = sigma x` by (
              qpat_x_assum `!x'. (!i. MEM i phis ==> _) /\ _ ==>
                latest_version rs_b_entry x' = _`
                (qspec_then `x` mp_tac) >>
              simp[] >>
              qexists_tac `vs'` >> simp[]) >>
            `latest_version rs_a_end x = latest_version rs_b_entry x` by (
              qpat_assum `Abbrev (rs_a_end = _)` (fn ab =>
                REWRITE_TAC [PURE_REWRITE_RULE [markerTheory.Abbrev_def] ab]) >>
              qpat_assum `bb_mid.bb_instructions = _`
                (fn eq => REWRITE_TAC [eq]) >>
              irule rename_block_insts_non_output_stable_any >>
              simp[MEM_APPEND] >> rpt strip_tac >> metis_tac[MEM_EL]) >>
            simp[]) >>
    (* Derive: sigma_exit x = latest_version rs_a_end x for output x *)
    `!x j'. j' < LENGTH (bb:basic_block).bb_instructions /\
            MEM x (EL j' (bb:basic_block).bb_instructions).inst_outputs ==>
       sigma_exit x = latest_version rs_a_end x` by (
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `!x j. j < LENGTH _ /\ MEM x (EL j _).inst_outputs ==>
        sigma_exit x = latest_version rs_a_end x`
        (qspecl_then [`x`, `j'`] mp_tac) >> simp[]) >>
    mp_tac ok_ok_step >>
    disch_then (qspecl_then [
      `fuel`, `ctx`, `func`, `func'`, `bbs1`, `func'.fn_blocks`, `rs0`,
      `dtree`, `succ_map`, `pred_map`, `dom_frontiers`, `dom_post_order`,
      `live_in`, `sigma`, `bb`, `bb'`, `bb_mid`, `phis`,
      `rs_b_entry`, `sigma_exit`, `v1`, `v2`, `s1`, `s2`] mp_tac) >>
    PURE_REWRITE_TAC[AND_IMP_INTRO] >>
    (impl_tac >- (
      (* Fold FST(rename_block_insts ...) to rs_a_end in goal.
         First substitute bb_mid.bb_instructions, then contract. *)
      qpat_assum `bb_mid.bb_instructions = _` (fn eq =>
        qpat_assum `Abbrev (rs_a_end = _)` (fn ab =>
          PURE_REWRITE_TAC [eq,
            GSYM (PURE_REWRITE_RULE [markerTheory.Abbrev_def] ab)])) >>
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      TRY REFL_TAC >>
      TRY (qpat_assum `Abbrev (func' = _)` (fn ab =>
             PURE_REWRITE_TAC [PURE_REWRITE_RULE [markerTheory.Abbrev_def] ab]) >>
           simp[] >> NO_TAC) >>
      TRY (simp[] >> NO_TAC) >>
      TRY (qpat_assum `_ = func'.fn_blocks`
             (fn th => REWRITE_TAC [GSYM th]) >>
           first_assum ACCEPT_TAC) >>
      TRY (qpat_assum `_ = func'.fn_blocks`
             (fn th => PURE_REWRITE_TAC [GSYM th]) >>
           first_assum ACCEPT_TAC) >>
      (* ssa_sim goal: use fst_append to match rs_mid form *)
      TRY (PURE_REWRITE_TAC [rename_block_insts_fst_append] >>
           first_assum ACCEPT_TAC >> NO_TAC) >>
      (* v1 prev_bb: run_block OK ==> vs_prev_bb <> NONE, unconditionally *)
      TRY (rpt strip_tac >>
           mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s1`, `v1`]
                     run_block_ok_sets_prev_bb) >>
           (impl_tac >- first_assum ACCEPT_TAC) >>
           strip_tac >> first_assum ACCEPT_TAC) >>
      (* IH: use explicit variable names to avoid gen_tac renaming *)
      Q.X_GEN_TAC `sigma_ih` >>
      Q.X_GEN_TAC `s1_ih` >>
      Q.X_GEN_TAC `s2_ih` >>
      strip_tac >>
      (* Expand func' in goal for irule matching *)
      qpat_assum `Abbrev (func' = _)`
        (fn th => let val eq = PURE_REWRITE_RULE [markerTheory.Abbrev_def] th
          in (func'_eq_ref := eq; PURE_REWRITE_TAC [eq]) end) >>
      (* Recursive IH goal: deterministic application avoids goalfrag/no-open-goal
         failures from FIRST/TRY after the subgoals are already closed. *)
      FIRST_X_ASSUM (fn th =>
        (let val (vs, body) = strip_forall (concl th)
             val (ant, _) = dest_imp body
         in if length vs >= 7 andalso is_conj ant
            then MATCH_MP_TAC th
            else NO_TAC
         end) handle HOL_ERR _ => NO_TAC) >>
      qexists_tac `sigma_ih` >>
      qexists_tac `bbs1` >>
      qexists_tac `rs0` >>
      PURE_REWRITE_TAC [GSYM (!func'_eq_ref)] >>
      rpt conj_tac >>
      TRY (first_assum ACCEPT_TAC) >>
      gvs[] >>
      TRY (`~(v1:venom_state).vs_halted` by metis_tac[run_block_OK_not_halted] >>
           `~(v2:venom_state).vs_halted` by metis_tac[run_block_OK_not_halted] >>
           ASM_REWRITE_TAC[] >> strip_tac >> first_assum ACCEPT_TAC))) >>
    (* ok_ok_step concluded; strip and simplify halted ifs *)
    strip_tac >>
    `~v1.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    `~v2.vs_halted` by metis_tac[run_block_OK_not_halted] >>
    ASM_REWRITE_TAC[] >>
    first_assum ACCEPT_TAC) >>
  TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `ssa_result_equiv _ _` mp_tac >>
  PURE_REWRITE_TAC[ssa_result_equiv_def] >>
  simp_tac std_ss [exec_result_case_def, result_equiv_def]
QED




