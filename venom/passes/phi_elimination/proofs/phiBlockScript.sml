(*
 * PHI Elimination Block-Level Correctness
 *
 * Per-block simulation: transform_block preserves execution semantics
 * when vs_prev_bb is set (reachable non-entry blocks).
 *
 * Uses lift_result for compatibility with block_sim_function_pointwise_reachable.
 *)

Theory phiBlock
Ancestors
  phiWellFormed execEquivProps venomExecProofs venomInstProps venomExecSemantics venomState venomInst venomWf phiDefs phiOrigins phiTransform stateEquiv stateEquivProps analysisSimDefs analysisSimProofsBase instIdxIndep finite_map list
Libs
  pairLib

(* ==========================================================================
   Instruction Step Lemmas
   ========================================================================== *)

Theorem step_inst_assign_eval:
  !inst out op s.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op] /\
    inst.inst_outputs = [out]
  ==>
    step_inst_base inst s =
      case eval_operand op s of
        SOME v => OK (update_var out v s)
      | NONE => Error "undefined operand"
Proof
  rw[step_inst_base_def]
QED

Theorem step_inst_phi_resolves_var_ok:
  !inst s s' src_var out prev.
    is_phi_inst inst /\
    inst.inst_outputs = [out] /\
    s.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME (Var src_var) /\
    step_inst_base inst s = OK s'
  ==>
    ?v. lookup_var src_var s = SOME v /\ s' = update_var out v s
Proof
  rpt strip_tac >>
  fs[is_phi_inst_def] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def, eval_operand_def] >>
  Cases_on `lookup_var src_var s` >> simp[]
QED

(* ==========================================================================
   Transform Instruction Correctness
   ========================================================================== *)

(* KEY LEMMA: Transform instruction correctness *)
Theorem transform_inst_correct:
  !dfg inst s s' origin prev_bb v.
    step_inst_base inst s = OK s' /\
    phi_single_origin dfg inst = SOME origin /\
    s.vs_prev_bb = SOME prev_bb /\
    resolve_phi prev_bb inst.inst_operands = SOME (Var v) /\
    dfg_lookup dfg v = SOME origin
  ==>
    ?s''. step_inst_base (transform_inst dfg inst) s = OK s'' /\
          state_equiv {} s' s''
Proof
  rpt strip_tac >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  fs[is_phi_inst_def, step_inst_base_def]
QED

(* ==========================================================================
   Block Step Equivalence
   ========================================================================== *)

(* KEY LEMMA: Single step in block produces equivalent states *)
Theorem block_step_equiv:
  !dfg bb s s' is_term.
    transform_block dfg bb = bb /\
    block_step bb s = (OK s', is_term) /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       s.vs_prev_bb = SOME prev_bb /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       dfg_lookup dfg v = SOME origin)
  ==>
    ?s''. block_step (transform_block dfg bb) s = (OK s'', is_term) /\
          state_equiv {} s' s''
Proof
  rpt strip_tac >>
  qexists_tac `s'` >>
  simp[state_equiv_refl]
QED

(* ==========================================================================
   Halt/Revert/Error Cases
   ========================================================================== *)

(* For Halt/Abort/IntRet cases, block_step on transformed block gives same result *)
Theorem block_step_nonOK_transform:
  !dfg bb s s' is_term.
    transform_block dfg bb = bb /\
    (block_step bb s = (Halt s', is_term) \/
     block_step bb s = (Abort a s', is_term) \/
     (?vs. block_step bb s = (IntRet vs s', is_term)))
  ==>
    block_step (transform_block dfg bb) s = block_step bb s
Proof
  rw[]
QED

Theorem block_step_halt_transform:
  !dfg bb s s' is_term.
    transform_block dfg bb = bb /\
    block_step bb s = (Halt s', is_term) ==>
    block_step (transform_block dfg bb) s = (Halt s', is_term)
Proof
  metis_tac[block_step_nonOK_transform]
QED

Theorem block_step_abort_transform:
  !dfg bb s a s' is_term.
    transform_block dfg bb = bb /\
    block_step bb s = (Abort a s', is_term) ==>
    block_step (transform_block dfg bb) s = (Abort a s', is_term)
Proof
  metis_tac[block_step_nonOK_transform]
QED

Theorem block_step_intret_transform:
  !dfg bb s vals s' is_term.
    transform_block dfg bb = bb /\
    block_step bb s = (IntRet vals s', is_term) ==>
    block_step (transform_block dfg bb) s = (IntRet vals s', is_term)
Proof
  rw[]
QED

(* ==========================================================================
   prev_bb Preservation
   ========================================================================== *)

(* Local version for step_inst_base (used by block_step_preserves_prev_bb).
   The general version for step_inst (covering INVOKE) is in venomExecProofsTheory. *)
Triviality step_inst_base_preserves_prev_bb:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  drule step_inst_base_OK_not_INVOKE >> strip_tac >>
  `step_inst 0 ARB inst s = step_inst_base inst s` by
    (irule step_inst_non_invoke >> simp[]) >>
  mp_tac (Q.SPECL [`0`, `ARB`, `inst`, `s`, `s'`]
    step_inst_preserves_prev_bb) >>
  ASM_REWRITE_TAC[]
QED

Theorem block_step_preserves_prev_bb:
  !bb s s' is_term.
    block_step bb s = (OK s', is_term) /\
    ~is_term ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> fs[] >>
  gvs[AllCaseEqs()] >>
  drule_all step_inst_base_preserves_prev_bb >>
  simp[next_inst_def]
QED

(* ==========================================================================
   Per-Block Simulation (KEY THEOREM)

   This is the main block-level correctness theorem.
   Uses lift_result for direct integration with block_sim_function_pointwise_reachable.
   Guarded by vs_prev_bb <> NONE (satisfied for all reachable non-entry blocks).
   ========================================================================== *)

(* Helper: state_equiv {} implies equality *)
Theorem state_equiv_empty_eq[local]:
  !s1 s2. state_equiv {} s1 s2 ==> (s1 = s2)
Proof
  rw[state_equiv_def, execution_equiv_def,
     venom_state_component_equality] >>
  `FLOOKUP s1.vs_vars = FLOOKUP s2.vs_vars` by
    (simp[FUN_EQ_THM] >> fs[lookup_var_def]) >>
  fs[finite_mapTheory.FLOOKUP_EXT]
QED

(* Helper: phi_single_origin always gives an origin with singleton output *)
Theorem phi_single_origin_has_output[local]:
  !dfg inst origin.
    phi_single_origin dfg inst = SOME origin ==>
    ?v. origin.inst_outputs = [v] /\ dfg_lookup dfg v = SOME origin
Proof
  rw[phi_single_origin_def] >> gvs[AllCaseEqs()] >>
  `compute_origins dfg inst DELETE inst <> {}` by
    (strip_tac >> gvs[]) >>
  `CHOICE (compute_origins dfg inst DELETE inst) IN
   (compute_origins dfg inst DELETE inst)` by
    metis_tac[pred_setTheory.CHOICE_DEF] >>
  fs[pred_setTheory.IN_DELETE] >>
  drule_all compute_origins_non_self_in_dfg >> strip_tac >>
  metis_tac[dfg_lookup_single_output]
QED

(* When a PHI step succeeds, resolve_phi must have returned SOME *)
Triviality phi_step_ok_resolve:
  !inst s s' prev.
    is_phi_inst inst /\
    s.vs_prev_bb = SOME prev /\
    step_inst_base inst s = OK s' ==>
    ?op. resolve_phi prev inst.inst_operands = SOME op
Proof
  rw[is_phi_inst_def, step_inst_base_def] >>
  gvs[AllCaseEqs()]
QED

Triviality all_distinct_flat_mem:
  !ls (l:'a list). ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

Triviality ssa_form_block_outputs_distinct:
  !fn bb. ssa_form fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  simp[venomWfTheory.ssa_form_def, venomInstTheory.fn_insts_def] >>
  rpt strip_tac >>
  ntac 2 (pop_assum mp_tac) >>
  qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[venomInstTheory.fn_insts_blocks_def] >>
  rpt strip_tac >> gvs[ALL_DISTINCT_APPEND, MAP_APPEND, FLAT_APPEND]
QED

Triviality all_distinct_outputs_not_mem_other:
  !inst producer insts out.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
    MEM inst insts /\ MEM producer insts /\ inst <> producer /\
    MEM out inst.inst_outputs ==>
    ~MEM out producer.inst_outputs
Proof
  Induct_on `insts` >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Triviality wf_ir_phi_output_not_other_output:
  !func bb inst producer out.
    wf_ir_fn func /\ MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\ MEM producer bb.bb_instructions /\
    inst <> producer /\ MEM out inst.inst_outputs ==>
    ~MEM out producer.inst_outputs
Proof
  rw[wf_ir_fn_def] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    metis_tac[ssa_form_block_outputs_distinct] >>
  metis_tac[all_distinct_outputs_not_mem_other]
QED

Triviality wf_ir_single_origin_phi_output_not_other_output:
  !func bb inst origin out producer.
    wf_ir_fn func /\ MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    phi_single_origin (dfg_build_function func) inst = SOME origin /\
    inst.inst_outputs = [out] /\
    MEM producer bb.bb_instructions /\ producer <> inst ==>
    ~MEM out producer.inst_outputs
Proof
  rpt strip_tac >>
  `MEM out inst.inst_outputs` by simp[] >>
  qspecl_then [`func`, `bb`, `inst`, `producer`, `out`]
    mp_tac wf_ir_phi_output_not_other_output >>
  simp[]
QED

Triviality run_insts_append:
  !xs ys fuel ctx s.
    run_insts fuel ctx (xs ++ ys) s =
    case run_insts fuel ctx xs s of
      OK s' => run_insts fuel ctx ys s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | IntRet v s' => IntRet v s'
    | Error e => Error e
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[run_insts_def]
QED

Triviality param_insts_nonterm_noninvoke:
  !insts.
    EVERY (\inst. ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE)
      (FILTER (\inst. is_param_opcode inst.inst_opcode) insts)
Proof
  rw[EVERY_MEM, MEM_FILTER] >>
  fs[is_param_opcode_iff, is_terminator_def]
QED

Triviality transformed_eliminated_phis_nonterm_noninvoke:
  !dfg insts.
    EVERY (\inst. ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE)
      (MAP (transform_inst dfg)
        (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin) insts))
Proof
  rw[EVERY_MEM, MEM_MAP, MEM_FILTER] >>
  drule transform_inst_single_origin_assign >> strip_tac >>
  simp[is_terminator_def]
QED

Triviality step_param_ok_same_vs_params:
  !inst fuel ctx s1 s1' s2.
    is_param_opcode inst.inst_opcode /\
    s2.vs_params = s1.vs_params /\
    s2.vs_return_pc_token = s1.vs_return_pc_token /\
    step_inst fuel ctx inst s1 = OK s1' ==>
    ?s2'. step_inst fuel ctx inst s2 = OK s2'
Proof
  rpt strip_tac >>
  fs[is_param_opcode_iff]
  >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[Once step_inst_def, step_inst_base_def] >>
      rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[]) >>
      rpt strip_tac >>
      rename [`inst.inst_outputs = [out]`, `inst.inst_operands = [Lit idx]`] >>
      qexists_tac `update_var out (EL (w2n idx) s2.vs_params) s2` >>
      simp[Once step_inst_def, step_inst_base_def])
  >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[Once step_inst_def, step_inst_base_def] >>
      rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[]) >>
      rpt strip_tac >>
      rename [`inst.inst_outputs = [out]`, `inst.inst_operands = [Lit idx]`] >>
      qexists_tac `update_var out (EL (w2n idx) s2.vs_params) s2` >>
      simp[Once step_inst_def, step_inst_base_def])
  >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      simp[Once step_inst_def, step_inst_base_def] >>
      rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[]) >>
      rpt strip_tac >>
      rename [`inst.inst_outputs = [out]`, `inst.inst_operands = [Lit idx]`] >>
      qexists_tac `update_var out s2.vs_return_pc_token s2` >>
      simp[Once step_inst_def, step_inst_base_def])
QED

Triviality step_param_preserves_input_fields:
  !inst fuel ctx s s'.
    is_param_opcode inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_params = s.vs_params /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  rpt strip_tac >>
  fs[is_param_opcode_iff] >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst` >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[update_var_def]) >>
  rpt strip_tac >> gvs[update_var_def]
QED

Triviality run_insts_params_ok_same_vs_params:
  !params fuel ctx s1 s1' s2.
    EVERY (\inst. is_param_opcode inst.inst_opcode) params /\
    s2.vs_params = s1.vs_params /\
    s2.vs_return_pc_token = s1.vs_return_pc_token /\
    run_insts fuel ctx params s1 = OK s1' ==>
    ?s2'. run_insts fuel ctx params s2 = OK s2'
Proof
  Induct >> simp[run_insts_def] >> rpt strip_tac >>
  Cases_on `step_inst fuel ctx h s1` >> gvs[] >>
  rename1 `step_inst fuel ctx h s1 = OK s1_mid` >>
  `?s2_mid. step_inst fuel ctx h s2 = OK s2_mid` by
    (irule step_param_ok_same_vs_params >> metis_tac[]) >>
  simp[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `s1_mid`, `s1'`, `s2_mid`] mp_tac) >>
  impl_tac >-
    (`~is_terminator h.inst_opcode` by
       fs[is_param_opcode_iff, is_terminator_def] >>
     `s1_mid.vs_params = s1.vs_params /\
      s1_mid.vs_return_pc_token = s1.vs_return_pc_token` by
       metis_tac[step_param_preserves_input_fields] >>
     `s2_mid.vs_params = s2.vs_params /\
      s2_mid.vs_return_pc_token = s2.vs_return_pc_token` by
       metis_tac[step_param_preserves_input_fields] >>
     gvs[]) >>
  disch_then ACCEPT_TAC
QED

Triviality step_param_lift_result:
  !inst fuel ctx vars s1 s2.
    is_param_opcode inst.inst_opcode /\
    state_equiv vars s1 s2 ==>
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars)
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  `s2.vs_params = s1.vs_params` by
    fs[state_equiv_def, execution_equiv_def] >>
  `s2.vs_return_pc_token = s1.vs_return_pc_token` by
    fs[state_equiv_def, execution_equiv_def] >>
  fs[is_param_opcode_iff] >>
  simp[step_inst_def, step_inst_base_def, lift_result_def] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def]) >>
  metis_tac[stateEquivPropsTheory.update_var_preserves]
QED

Triviality step_param_state_equiv:
  !inst fuel ctx vars s1 s1' s2.
    is_param_opcode inst.inst_opcode /\
    state_equiv vars s1 s2 /\
    step_inst fuel ctx inst s1 = OK s1' ==>
    ?s2'. step_inst fuel ctx inst s2 = OK s2' /\ state_equiv vars s1' s2'
Proof
  rpt strip_tac >>
  qspecl_then [`inst`, `fuel`, `ctx`, `vars`, `s1`, `s2`] mp_tac
    step_param_lift_result >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst s2` >>
  simp[lift_result_def]
QED

Triviality run_insts_params_lift_result:
  !params fuel ctx vars s1 s2.
    EVERY (\inst. is_param_opcode inst.inst_opcode) params /\
    state_equiv vars s1 s2 ==>
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars)
      (run_insts fuel ctx params s1)
      (run_insts fuel ctx params s2)
Proof
  Induct >> simp[run_insts_def, lift_result_def] >> rpt strip_tac >>
  `lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars)
      (step_inst fuel ctx h s1) (step_inst fuel ctx h s2)` by
    (irule step_param_lift_result >> simp[]) >>
  Cases_on `step_inst fuel ctx h s1` >>
  Cases_on `step_inst fuel ctx h s2` >>
  gvs[lift_result_def, run_insts_def] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `vars`, `v`, `v'`] mp_tac) >>
  simp[]
QED

Triviality run_insts_params_state_equiv:
  !params fuel ctx vars s1 s1' s2.
    EVERY (\inst. is_param_opcode inst.inst_opcode) params /\
    state_equiv vars s1 s2 /\
    run_insts fuel ctx params s1 = OK s1' ==>
    ?s2'. run_insts fuel ctx params s2 = OK s2' /\ state_equiv vars s1' s2'
Proof
  Induct >> simp[run_insts_def] >> rpt strip_tac >>
  Cases_on `step_inst fuel ctx h s1` >> gvs[] >>
  rename1 `step_inst fuel ctx h s1 = OK s1_mid` >>
  drule_all step_param_state_equiv >> strip_tac >>
  rename1 `step_inst fuel ctx h s2 = OK s2_mid` >>
  simp[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `vars`, `s1_mid`, `s1'`, `s2_mid`] mp_tac) >>
  simp[]
QED

Triviality eval_phis_same_start_same_param_fields:
  !s insts1 s1 insts2 s2.
    eval_phis s insts1 = OK s1 /\
    eval_phis s insts2 = OK s2 ==>
    s2.vs_params = s1.vs_params /\
    s2.vs_return_pc_token = s1.vs_return_pc_token
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_phis s insts1 = OK s1`
    (fn th => assume_tac (MATCH_MP eval_phis_only_updates_vs_vars th)) >>
  qpat_x_assum `eval_phis s insts2 = OK s2`
    (fn th => assume_tac (MATCH_MP eval_phis_only_updates_vs_vars th)) >>
  qpat_x_assum `s2 = _` SUBST1_TAC >>
  qpat_x_assum `s1 = _` SUBST1_TAC >>
  simp[]
QED

Triviality run_insts_params_ok_after_eval_phis:
  !params fuel ctx s insts1 s1 insts2 s2 s1_params.
    EVERY (\inst. is_param_opcode inst.inst_opcode) params /\
    eval_phis s insts1 = OK s1 /\
    eval_phis s insts2 = OK s2 /\
    run_insts fuel ctx params s1 = OK s1_params ==>
    ?s2_params. run_insts fuel ctx params s2 = OK s2_params
Proof
  rpt strip_tac >>
  `s2.vs_params = s1.vs_params /\
   s2.vs_return_pc_token = s1.vs_return_pc_token` by
    metis_tac[eval_phis_same_start_same_param_fields] >>
  qspecl_then [`params`, `fuel`, `ctx`, `s1`, `s1_params`, `s2`]
    mp_tac run_insts_params_ok_same_vs_params >>
  simp[]
QED

Triviality step_inst_idx_ok_non_invoke:
  !fuel ctx inst s j s'.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst fuel ctx inst (s with vs_inst_idx := j) =
      OK (s' with vs_inst_idx := j)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j) (step_inst fuel ctx inst s)` by
    simp[step_inst_idx_indep] >>
  gvs[instIdxIndepTheory.exec_result_map_def]
QED

Triviality exec_block_skip_prefix_non_invoke:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\inst. ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s' ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  Cases_on `step_inst fuel ctx h s` >> gvs[run_insts_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
     OK (s1 with vs_inst_idx := j)` by
    (irule step_inst_idx_ok_non_invoke >> simp[]) >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  `bb.bb_instructions❲j❳ = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >> simp[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `s'`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES]) >>
  simp[]
QED

Triviality exec_block_prefix_error:
  !prefix fuel ctx bb s j e.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\inst. ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = Error e ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) = Error e
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `h :: prefix` >>
  fs[EVERY_DEF] >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j) (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  `bb.bb_instructions❲j❳ = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[instIdxIndepTheory.exec_result_map_def, Once run_insts_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `e`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES]) >>
  simp[]
QED

Triviality step_param_ok_or_error:
  !inst fuel ctx s.
    is_param_opcode inst.inst_opcode ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  metis_tac[step_inst_param_ok_or_error]
QED

Triviality run_insts_params_ok_or_error:
  !params fuel ctx s.
    EVERY (\inst. is_param_opcode inst.inst_opcode) params ==>
    (?s'. run_insts fuel ctx params s = OK s') \/
    (?e. run_insts fuel ctx params s = Error e)
Proof
  Induct >> simp[run_insts_def] >> rpt strip_tac >>
  `(?s1. step_inst fuel ctx h s = OK s1) \/
   (?e. step_inst fuel ctx h s = Error e)` by
    (irule step_param_ok_or_error >> gvs[]) >>
  gvs[run_insts_def] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `s1`] mp_tac) >> simp[]
QED

Triviality exec_block_same_suffix:
  !fuel ctx bb1 bb2 s.
    DROP s.vs_inst_idx bb1.bb_instructions =
    DROP s.vs_inst_idx bb2.bb_instructions ==>
    exec_block fuel ctx bb1 s = exec_block fuel ctx bb2 s
Proof
  completeInduct_on `LENGTH bb1.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  Cases_on `s.vs_inst_idx < LENGTH bb1.bb_instructions`
  >- (`s.vs_inst_idx < LENGTH bb2.bb_instructions` by
        (CCONTR_TAC >> fs[] >>
         `DROP s.vs_inst_idx bb1.bb_instructions =
          bb1.bb_instructions❲s.vs_inst_idx❳ :: DROP (SUC s.vs_inst_idx) bb1.bb_instructions` by
            (irule rich_listTheory.DROP_CONS_EL >> simp[]) >>
         `DROP s.vs_inst_idx bb2.bb_instructions = []` by
            (irule DROP_LENGTH_TOO_LONG >> simp[]) >>
         gvs[]) >>
      `bb1.bb_instructions❲s.vs_inst_idx❳ =
       bb2.bb_instructions❲s.vs_inst_idx❳ /\
       DROP (SUC s.vs_inst_idx) bb1.bb_instructions =
       DROP (SUC s.vs_inst_idx) bb2.bb_instructions` by
        (`DROP s.vs_inst_idx bb1.bb_instructions =
          bb1.bb_instructions❲s.vs_inst_idx❳ :: DROP (SUC s.vs_inst_idx) bb1.bb_instructions` by
            (irule rich_listTheory.DROP_CONS_EL >> simp[]) >>
         `DROP s.vs_inst_idx bb2.bb_instructions =
          bb2.bb_instructions❲s.vs_inst_idx❳ :: DROP (SUC s.vs_inst_idx) bb2.bb_instructions` by
            (irule rich_listTheory.DROP_CONS_EL >> simp[]) >>
         gvs[]) >>
      simp[get_instruction_def] >>
      Cases_on `step_inst fuel ctx (bb2.bb_instructions❲s.vs_inst_idx❳) s` >> gvs[] >>
      Cases_on `is_terminator (bb2.bb_instructions❲s.vs_inst_idx❳).inst_opcode` >> gvs[] >>
      first_x_assum irule >> simp[]) >>
  `~(s.vs_inst_idx < LENGTH bb2.bb_instructions)` by
    (CCONTR_TAC >> fs[] >>
     `DROP s.vs_inst_idx bb1.bb_instructions = []` by
        (irule DROP_LENGTH_TOO_LONG >> simp[]) >>
     `DROP s.vs_inst_idx bb2.bb_instructions =
      bb2.bb_instructions❲s.vs_inst_idx❳ :: DROP (SUC s.vs_inst_idx) bb2.bb_instructions` by
        (irule rich_listTheory.DROP_CONS_EL >> simp[]) >>
     gvs[]) >>
  simp[get_instruction_def]
QED

Triviality sorted_pred_split:
  !l P. (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) ==>
    FILTER P l ++ FILTER ($~ o P) l = l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `P h` >> simp[]
  >- (first_x_assum (qspec_then `P` mp_tac) >>
      impl_tac >- (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      simp[]) >>
  `EVERY (\x. ~P x) l` by
    (simp[EVERY_MEM, MEM_EL, PULL_EXISTS] >> rpt strip_tac >>
     spose_not_then assume_tac >>
     first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  `FILTER P l = []` by simp[FILTER_EQ_NIL] >>
  `FILTER ($~ o P) l = l` by (simp[FILTER_EQ_ID] >> fs[EVERY_MEM]) >>
  simp[]
QED

Triviality sorted_prefix_take_filter:
  !l P.
    (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) ==>
    TAKE (LENGTH (FILTER P l)) l = FILTER P l
Proof
  rpt strip_tac >>
  `FILTER P l ++ FILTER ($~ o P) l = l` by metis_tac[sorted_pred_split] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))) >>
  simp[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Triviality sorted_suffix_drop_filter:
  !l P.
    (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) ==>
    DROP (LENGTH (FILTER P l)) l = FILTER ($~ o P) l
Proof
  rpt strip_tac >>
  `FILTER P l ++ FILTER ($~ o P) l = l` by metis_tac[sorted_pred_split] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Triviality phi_prefix_take_filter:
  !insts lbl.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> ==>
    TAKE (LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)) insts =
    FILTER (\inst. inst.inst_opcode = PHI) insts
Proof
  rpt strip_tac >> irule sorted_prefix_take_filter >>
  rpt strip_tac >> fs[bb_well_formed_def] >> metis_tac[]
QED

Triviality pseudo_prefix_take_filter:
  !insts lbl.
    pseudos_prefix <| bb_label := lbl; bb_instructions := insts |> ==>
    TAKE (LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts)) insts =
    FILTER (\inst. is_pseudo inst.inst_opcode) insts
Proof
  rpt strip_tac >> irule sorted_prefix_take_filter >>
  rpt strip_tac >> fs[pseudos_prefix_def] >> metis_tac[]
QED

Triviality filter_pseudo_no_phi_param:
  !insts.
    EVERY (\inst. inst.inst_opcode <> PHI) insts ==>
    FILTER (\inst. is_pseudo inst.inst_opcode) insts =
    FILTER (\inst. is_param_opcode inst.inst_opcode) insts
Proof
  Induct >> rw[] >> Cases_on `h.inst_opcode` >>
  gvs[is_pseudo_def, is_param_opcode_def]
QED

Triviality filter_pseudo_original_phi_param:
  !insts lbl.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> ==>
    FILTER (\inst. is_pseudo inst.inst_opcode) insts =
    FILTER (\inst. inst.inst_opcode = PHI) insts ++
    FILTER (\inst. is_param_opcode inst.inst_opcode) insts
Proof
  Induct_on `insts` >> simp[] >> rpt gen_tac >> strip_tac >>
  rename1 `bb_well_formed <|bb_label := label; bb_instructions := h::insts|>` >>
  fs[bb_well_formed_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (simp[is_pseudo_def, is_param_opcode_def] >>
      Cases_on `insts = []` >- simp[is_param_opcode_def] >>
      qpat_x_assum `_ ==> FILTER _ insts = _` mp_tac >> simp[] >>
      impl_tac >-
        (conj_tac >- (Cases_on `insts` >> gvs[LAST_DEF]) >>
         conj_tac >- (rpt strip_tac >>
           qpat_x_assum `!i. _ /\ is_terminator _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
         rpt strip_tac >>
         qpat_x_assum `!i j. _ /\ _ /\ _.inst_opcode = PHI ==> _`
           (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      simp[]) >>
  `EVERY (\inst. inst.inst_opcode <> PHI) insts` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  `FILTER (\inst. inst.inst_opcode = PHI) insts = []` by simp[FILTER_EQ_NIL] >>
  `FILTER (\inst. is_pseudo inst.inst_opcode) insts =
   FILTER (\inst. is_param_opcode inst.inst_opcode) insts` by
    (irule filter_pseudo_no_phi_param >> simp[]) >>
  Cases_on `h.inst_opcode` >> EVAL_TAC >> ASM_REWRITE_TAC[] >>
  PURE_REWRITE_TAC[APPEND] >> REFL_TAC
QED

Triviality phi_prefix_length_filter_phi:
  !insts lbl.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> ==>
    phi_prefix_length insts = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)
Proof
  Induct_on `insts` >> simp[phi_prefix_length_def] >> rpt gen_tac >> strip_tac >>
  rename1 `bb_well_formed <|bb_label := label; bb_instructions := h::insts|>` >>
  fs[bb_well_formed_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def]
  >- (Cases_on `insts = []` >- simp[phi_prefix_length_def] >>
      qpat_x_assum `_ ==> phi_prefix_length insts = _` mp_tac >> simp[] >>
      impl_tac >-
        (conj_tac >- (Cases_on `insts` >> gvs[LAST_DEF]) >>
         conj_tac >- (rpt strip_tac >>
           qpat_x_assum `!i. _ /\ is_terminator _ ==> _` (qspec_then `SUC i` mp_tac) >> simp[]) >>
         rpt strip_tac >>
         qpat_x_assum `!i j. _ /\ _ /\ _.inst_opcode = PHI ==> _`
           (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      simp[]) >>
  `EVERY (\inst. inst.inst_opcode <> PHI) insts` by
    (simp[EVERY_EL] >> rpt strip_tac >>
     first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
  simp[FILTER_EQ_NIL]
QED

Triviality original_param_prefix_eq_filter_param:
  !insts lbl.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
    pseudos_prefix <| bb_label := lbl; bb_instructions := insts |> ==>
    DROP (phi_prefix_length insts)
      (TAKE (LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts)) insts) =
    FILTER (\inst. is_param_opcode inst.inst_opcode) insts
Proof
  rpt strip_tac >>
  `TAKE (LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts)) insts =
   FILTER (\inst. is_pseudo inst.inst_opcode) insts` by
    metis_tac[pseudo_prefix_take_filter] >>
  `FILTER (\inst. is_pseudo inst.inst_opcode) insts =
   FILTER (\inst. inst.inst_opcode = PHI) insts ++
   FILTER (\inst. is_param_opcode inst.inst_opcode) insts` by
    metis_tac[filter_pseudo_original_phi_param] >>
  `phi_prefix_length insts = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` by
    metis_tac[phi_prefix_length_filter_phi] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND]
QED

Triviality exec_block_skip_original_params:
  !insts lbl fuel ctx s s'.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
    pseudos_prefix <| bb_label := lbl; bb_instructions := insts |> /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s = OK s' ==>
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := insts |>
      (s with vs_inst_idx := phi_prefix_length insts) =
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := insts |>
      (s' with vs_inst_idx :=
        phi_prefix_length insts + LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts))
Proof
  rpt strip_tac >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `p = phi_prefix_length insts` >>
  qabbrev_tac `q = LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts)` >>
  `FILTER (\inst. is_pseudo inst.inst_opcode) insts =
   FILTER (\inst. inst.inst_opcode = PHI) insts ++ params` by
    (simp[Abbr `params`] >> metis_tac[filter_pseudo_original_phi_param]) >>
  `p = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` by
    (simp[Abbr `p`] >> metis_tac[phi_prefix_length_filter_phi]) >>
  `q = p + LENGTH params` by simp[Abbr `q`] >>
  `DROP p (TAKE q insts) = params` by
    (unabbrev_all_tac >> metis_tac[original_param_prefix_eq_filter_param]) >>
  `p + LENGTH params <= LENGTH insts` by
    (`q <= LENGTH insts` by simp[Abbr `q`, rich_listTheory.LENGTH_FILTER_LEQ] >> decide_tac) >>
  `!k. k < LENGTH params ==> EL (p + k) insts = EL k params` by
    (rpt strip_tac >>
     `p + k < q` by decide_tac >>
     `EL k params = EL k (DROP p (TAKE q insts))` by simp[] >>
     pop_assum SUBST1_TAC >> simp[EL_DROP, EL_TAKE]) >>
  qspecl_then [`params`, `fuel`, `ctx`, `<| bb_label := lbl; bb_instructions := insts |>`,
                `s`, `p`, `s'`] mp_tac exec_block_skip_prefix_non_invoke >>
  simp[param_insts_nonterm_noninvoke, Abbr `params`] >>
  impl_tac >-
    (rw[] >>
     qpat_x_assum `!k. k < LENGTH _ ==> insts❲_ + k❳ = _`
       (qspec_then `k` mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     `k + LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts) =
      LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts) + k` by decide_tac >>
     asm_rewrite_tac[]) >>
  disch_then ACCEPT_TAC
QED

Triviality exec_block_original_params_error:
  !insts lbl fuel ctx s e.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
    pseudos_prefix <| bb_label := lbl; bb_instructions := insts |> /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s = Error e ==>
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := insts |>
      (s with vs_inst_idx := phi_prefix_length insts) = Error e
Proof
  rpt strip_tac >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `p = phi_prefix_length insts` >>
  qabbrev_tac `q = LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts)` >>
  `FILTER (\inst. is_pseudo inst.inst_opcode) insts =
   FILTER (\inst. inst.inst_opcode = PHI) insts ++ params` by
    (simp[Abbr `params`] >> metis_tac[filter_pseudo_original_phi_param]) >>
  `p = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` by
    (simp[Abbr `p`] >> metis_tac[phi_prefix_length_filter_phi]) >>
  `q = p + LENGTH params` by simp[Abbr `q`] >>
  `DROP p (TAKE q insts) = params` by
    (unabbrev_all_tac >> metis_tac[original_param_prefix_eq_filter_param]) >>
  `p + LENGTH params <= LENGTH insts` by
    (`q <= LENGTH insts` by simp[Abbr `q`, rich_listTheory.LENGTH_FILTER_LEQ] >> decide_tac) >>
  `!k. k < LENGTH params ==> EL (p + k) insts = EL k params` by
    (rpt strip_tac >>
     `p + k < q` by decide_tac >>
     `EL k params = EL k (DROP p (TAKE q insts))` by simp[] >>
     pop_assum SUBST1_TAC >> simp[EL_DROP, EL_TAKE]) >>
  qspecl_then [`params`, `fuel`, `ctx`, `<| bb_label := lbl; bb_instructions := insts |>`,
                `s`, `p`, `e`] mp_tac exec_block_prefix_error >>
  simp[param_insts_nonterm_noninvoke, Abbr `params`] >>
  impl_tac >-
    (rw[] >>
     qpat_x_assum `!k. k < LENGTH _ ==> insts❲_ + k❳ = _`
       (qspec_then `k` mp_tac) >>
     impl_tac >- simp[] >> strip_tac >>
     `k + LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts) =
      LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts) + k` by decide_tac >>
     asm_rewrite_tac[]) >>
  disch_then ACCEPT_TAC
QED

Triviality exec_block_original_params_ok_from_non_error:
  !insts lbl fuel ctx s r.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
    pseudos_prefix <| bb_label := lbl; bb_instructions := insts |> /\
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := insts |>
      (s with vs_inst_idx := phi_prefix_length insts) = r /\
    (!e. r <> Error e) ==>
    ?s'. run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s = OK s'
Proof
  rpt strip_tac >>
  qspecl_then [`FILTER (\inst. is_param_opcode inst.inst_opcode) insts`, `fuel`, `ctx`, `s`]
    mp_tac run_insts_params_ok_or_error >>
  simp[param_insts_nonterm_noninvoke, EVERY_MEM, MEM_FILTER] >>
  strip_tac >- metis_tac[] >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := insts|>
      (s with vs_inst_idx := phi_prefix_length insts) = Error e` by
    (qspecl_then [`insts`, `lbl`, `fuel`, `ctx`, `s`, `e`]
       mp_tac exec_block_original_params_error >>
     simp[]) >>
  gvs[]
QED

Triviality exec_block_skip_transformed_params:
  !dfg insts lbl fuel ctx s s'.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s = OK s' ==>
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := transform_insts dfg insts |>
      (s with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts)) =
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := transform_insts dfg insts |>
      (s' with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts) +
        LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts))
Proof
  rpt strip_tac >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `elim = MAP (transform_inst dfg)
    (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
      (TAKE (phi_prefix_length insts) insts))` >>
  qabbrev_tac `tail = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
        (MAP (transform_inst dfg) (DROP (phi_prefix_length insts) insts)) ++
      FILTER (\inst. is_terminator inst.inst_opcode) (MAP (transform_inst dfg) insts)` >>
  `transform_insts dfg insts = kept ++ params ++ elim ++ tail` by
    (qunabbrev_tac `tail` >> qunabbrev_tac `elim` >> qunabbrev_tac `kept` >>
     qunabbrev_tac `params` >> drule transform_insts_decompose_phi_prefix >> simp[]) >>
  `LENGTH kept + LENGTH params <= LENGTH (transform_insts dfg insts)` by
    (qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `!k. k < LENGTH params ==>
       EL (LENGTH kept + k) (transform_insts dfg insts) = EL k params` by
    (rpt strip_tac >>
     qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
     simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]) >>
  qspecl_then [`params`, `fuel`, `ctx`, `<| bb_label := lbl; bb_instructions := transform_insts dfg insts |>`,
                `s`, `LENGTH kept`, `s'`] mp_tac exec_block_skip_prefix_non_invoke >>
  impl_tac >-
    (simp[Abbr `params`, param_insts_nonterm_noninvoke] >>
     rpt strip_tac >>
     qpat_x_assum `!k. k < LENGTH params ==> _` (qspec_then `k` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     `k + LENGTH kept = LENGTH kept + k` by decide_tac >>
     pop_assum (fn th => rewrite_tac[th]) >>
     qpat_x_assum `(transform_insts dfg insts)❲LENGTH kept + k❳ = _` mp_tac >>
     qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
     disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Triviality exec_block_transformed_params_error:
  !dfg insts lbl fuel ctx s e.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s = Error e ==>
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := transform_insts dfg insts |>
      (s with vs_inst_idx := phi_prefix_length (transform_insts dfg insts)) = Error e
Proof
  rw[] >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  qabbrev_tac `elim = MAP (transform_inst dfg) eliminated` >>
  qabbrev_tac `tail = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
        (MAP (transform_inst dfg) (DROP (phi_prefix_length insts) insts)) ++
      FILTER (\inst. is_terminator inst.inst_opcode) (MAP (transform_inst dfg) insts)` >>
  `transform_insts dfg insts = kept ++ params ++ elim ++ tail` by
    (qunabbrev_tac `tail` >> qunabbrev_tac `elim` >> qunabbrev_tac `eliminated` >>
     qunabbrev_tac `kept` >> qunabbrev_tac `params` >>
     qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_decompose_phi_prefix >>
     simp[APPEND_ASSOC]) >>
  `phi_prefix_length (transform_insts dfg insts) = LENGTH kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `LENGTH kept + LENGTH params <= LENGTH (transform_insts dfg insts)` by
    (qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `!k. k < LENGTH params ==>
       EL (LENGTH kept + k) (transform_insts dfg insts) = EL k params` by
    (rpt strip_tac >>
     qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
     simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]) >>
  qspecl_then [`params`, `fuel`, `ctx`, `<| bb_label := lbl; bb_instructions := transform_insts dfg insts |>`,
                `s`, `LENGTH kept`, `e`] mp_tac exec_block_prefix_error >>
  impl_tac >-
    (simp[param_insts_nonterm_noninvoke, Abbr `params`] >>
     rpt strip_tac >>
     qpat_x_assum `!k. k < LENGTH params ==> _` (qspec_then `k` mp_tac) >>
     simp[] >>
     `LENGTH kept + k = LENGTH kept + k` by simp[] >>
     disch_then ACCEPT_TAC) >>
  simp[Abbr `params`]
QED

Triviality exec_block_skip_transformed_eliminated:
  !dfg insts lbl fuel ctx s s'.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
    run_insts fuel ctx
      (MAP (transform_inst dfg)
        (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
          (TAKE (phi_prefix_length insts) insts))) s = OK s' ==>
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := transform_insts dfg insts |>
      (s with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts) +
        LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts)) =
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := transform_insts dfg insts |>
      (s' with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts) +
        LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) +
        LENGTH (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
          (TAKE (phi_prefix_length insts) insts)))
Proof
  rw[] >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  qabbrev_tac `elim = MAP (transform_inst dfg) eliminated` >>
  qabbrev_tac `tail = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
        (MAP (transform_inst dfg) (DROP (phi_prefix_length insts) insts)) ++
      FILTER (\inst. is_terminator inst.inst_opcode) (MAP (transform_inst dfg) insts)` >>
  `transform_insts dfg insts = kept ++ params ++ elim ++ tail` by
    (qunabbrev_tac `tail` >> qunabbrev_tac `elim` >> qunabbrev_tac `eliminated` >>
     qunabbrev_tac `kept` >> qunabbrev_tac `params` >>
     qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_decompose_phi_prefix >>
     simp[APPEND_ASSOC]) >>
  `LENGTH kept + LENGTH params + LENGTH elim <= LENGTH (transform_insts dfg insts)` by
    (qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `!k. k < LENGTH elim ==>
       EL (LENGTH kept + LENGTH params + k) (transform_insts dfg insts) = EL k elim` by
    (rpt strip_tac >>
     qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
     simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]) >>
  qspecl_then [`elim`, `fuel`, `ctx`, `<| bb_label := lbl; bb_instructions := transform_insts dfg insts |>`,
                `s`, `LENGTH kept + LENGTH params`, `s'`] mp_tac exec_block_skip_prefix_non_invoke >>
  impl_tac >-
    (simp[Abbr `elim`, Abbr `eliminated`, transformed_eliminated_phis_nonterm_noninvoke] >>
     rpt strip_tac >>
     qpat_x_assum `!k. k < LENGTH elim ==> _` (qspec_then `k` mp_tac) >>
     simp[] >>
     `LENGTH kept + LENGTH params + k = LENGTH kept + LENGTH params + k` by simp[] >>
     disch_then ACCEPT_TAC) >>
  simp[Abbr `elim`]
QED

Triviality map_transform_non_phi_id:
  !dfg insts.
    EVERY (\inst. inst.inst_opcode <> PHI) insts ==>
    MAP (transform_inst dfg) insts = insts
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  `~is_phi_inst h` by fs[is_phi_inst_def] >>
  simp[transform_inst_non_phi]
QED

Triviality filter_transform_terminators:
  !dfg insts.
    FILTER (\inst. is_terminator inst.inst_opcode) (MAP (transform_inst dfg) insts) =
    FILTER (\inst. is_terminator inst.inst_opcode) insts
Proof
  gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  Cases_on `is_terminator h.inst_opcode`
  >- (`~is_phi_inst h` by (fs[is_phi_inst_def] >> Cases_on `h.inst_opcode` >> fs[is_terminator_def]) >>
      simp[transform_inst_non_phi]) >>
  simp[transform_inst_preserves_terminator]
QED

Triviality filter_regular_nonphi:
  !insts.
    FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
      (FILTER (\inst. inst.inst_opcode <> PHI) insts) =
    FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode) insts
Proof
  Induct >- simp[] >>
  gen_tac >> simp[] >>
  Cases_on `h.inst_opcode` >> simp[is_pseudo_def, is_terminator_def]
QED

Triviality filter_terminator_nonpseudo:
  !insts.
    FILTER (\inst. ~is_pseudo inst.inst_opcode)
      (FILTER (\inst. is_terminator inst.inst_opcode) insts) =
    FILTER (\inst. is_terminator inst.inst_opcode) insts
Proof
  Induct >- simp[] >> gen_tac >> simp[] >>
  Cases_on `h.inst_opcode` >> simp[is_terminator_def, is_pseudo_def]
QED

Triviality filter_nonpseudo_regular_terms:
  !insts lbl.
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> ==>
    FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode) insts ++
    FILTER (\inst. is_terminator inst.inst_opcode) insts =
    FILTER ($~ o (\inst. is_pseudo inst.inst_opcode)) insts
Proof
  rpt strip_tac >>
  `FILTER (\inst. ~is_terminator inst.inst_opcode) insts ++
   FILTER (\inst. is_terminator inst.inst_opcode) insts = insts` by
    (qspecl_then [`insts`, `\inst. ~is_terminator inst.inst_opcode`] mp_tac sorted_pred_split >>
     simp[combinTheory.o_DEF] >>
     impl_tac >-
       (rpt strip_tac >> fs[bb_well_formed_def] >>
        CCONTR_TAC >> gvs[] >>
        qpat_x_assum `!i. _ /\ is_terminator _ ==> _` (qspec_then `i` mp_tac) >>
        simp[] >> decide_tac) >>
     disch_then ACCEPT_TAC) >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >>
  simp[rich_listTheory.FILTER_APPEND, rich_listTheory.FILTER_FILTER, combinTheory.o_DEF] >>
  simp[GSYM rich_listTheory.FILTER_FILTER, filter_terminator_nonpseudo]
QED

Triviality transform_suffix_after_eliminated_eq:
  !dfg insts lbl.
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> /\
    pseudos_prefix <|bb_label := lbl; bb_instructions := insts|> ==>
    let kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts in
    let params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts in
    let eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
          (TAKE (phi_prefix_length insts) insts) in
      DROP (phi_prefix_length insts + LENGTH params) insts =
      DROP (LENGTH kept + LENGTH params + LENGTH eliminated) (transform_insts dfg insts)
Proof
  rpt strip_tac >> simp[LET_DEF] >>
  qabbrev_tac `p = phi_prefix_length insts` >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin) (TAKE p insts)` >>
  qabbrev_tac `regulars = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
        (MAP (transform_inst dfg) (DROP p insts))` >>
  qabbrev_tac `terms = FILTER (\inst. is_terminator inst.inst_opcode) (MAP (transform_inst dfg) insts)` >>
  `transform_insts dfg insts = kept ++ params ++ MAP (transform_inst dfg) eliminated ++ regulars ++ terms` by
    (qunabbrev_tac `regulars` >> qunabbrev_tac `terms` >> qunabbrev_tac `eliminated` >>
     qunabbrev_tac `kept` >> qunabbrev_tac `params` >> qunabbrev_tac `p` >>
     drule transform_insts_decompose_phi_prefix >> simp[]) >>
  `p = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` by
    (simp[Abbr `p`] >> metis_tac[phi_prefix_length_filter_phi]) >>
  `DROP p insts = FILTER (\inst. inst.inst_opcode <> PHI) insts` by
    (qpat_x_assum `p = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)`
       (fn th => rewrite_tac[th]) >>
     qspecl_then [`insts`, `\inst. inst.inst_opcode = PHI`] mp_tac sorted_suffix_drop_filter >>
     simp[combinTheory.o_DEF] >>
     impl_tac >- (rpt strip_tac >> fs[bb_well_formed_def] >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `EVERY (\inst. inst.inst_opcode <> PHI) (DROP p insts)` by
    (qpat_x_assum `DROP p insts = _` (fn th => rewrite_tac[th]) >>
     simp[EVERY_MEM, MEM_FILTER]) >>
  `regulars = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode) (DROP p insts)` by
    simp[Abbr `regulars`, map_transform_non_phi_id] >>
  `FILTER (\inst. is_terminator inst.inst_opcode) (MAP (transform_inst dfg) insts) =
   FILTER (\inst. is_terminator inst.inst_opcode) insts` by
    ACCEPT_TAC (Q.SPECL [`dfg`, `insts`] filter_transform_terminators) >>
  `terms = FILTER (\inst. is_terminator inst.inst_opcode) insts` by simp[Abbr `terms`] >>
  `DROP (LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts)) insts =
   FILTER ($~ o (\inst. is_pseudo inst.inst_opcode)) insts` by
    (qspecl_then [`insts`, `\inst. is_pseudo inst.inst_opcode`] mp_tac sorted_suffix_drop_filter >>
     simp[] >>
     impl_tac >- fs[pseudos_prefix_def] >>
     disch_then ACCEPT_TAC) >>
  `LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts) = p + LENGTH params` by
    (`FILTER (\inst. is_pseudo inst.inst_opcode) insts =
      FILTER (\inst. inst.inst_opcode = PHI) insts ++ params` by
        (simp[Abbr `params`] >> metis_tac[filter_pseudo_original_phi_param]) >>
     simp[]) >>
  `FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode) (DROP p insts) =
   FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode) insts` by
    (qpat_x_assum `DROP p insts = _` (fn th => rewrite_tac[th]) >>
     simp[filter_regular_nonphi]) >>
  `FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode) insts ++
   FILTER (\inst. is_terminator inst.inst_opcode) insts =
   FILTER ($~ o (\inst. is_pseudo inst.inst_opcode)) insts` by
    (qspecl_then [`insts`, `lbl`] mp_tac filter_nonpseudo_regular_terms >>
     simp[] >> disch_then ACCEPT_TAC) >>
  qpat_x_assum `p = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` SUBST_ALL_TAC >>
  `LENGTH params + LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts) =
   LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts)` by decide_tac >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `DROP (LENGTH (FILTER (\inst. is_pseudo inst.inst_opcode) insts)) insts = _`
    SUBST1_TAC >>
  qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
  `DROP (LENGTH eliminated + (LENGTH params + LENGTH kept))
      (kept ++ params ++ MAP (transform_inst dfg) eliminated ++ regulars ++ terms) =
   regulars ++ terms` by
    (`LENGTH eliminated + (LENGTH params + LENGTH kept) =
      LENGTH (kept ++ params ++ MAP (transform_inst dfg) eliminated)` by
        (simp[] >> decide_tac) >>
     pop_assum SUBST1_TAC >>
     `kept ++ params ++ MAP (transform_inst dfg) eliminated ++ regulars ++ terms =
      (kept ++ params ++ MAP (transform_inst dfg) eliminated) ++ (regulars ++ terms)` by
        simp[APPEND_ASSOC] >>
     pop_assum SUBST1_TAC >>
     qspecl_then [`kept ++ params ++ MAP (transform_inst dfg) eliminated`,
                  `regulars ++ terms`] ACCEPT_TAC rich_listTheory.DROP_LENGTH_APPEND) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `regulars = _` SUBST_ALL_TAC >>
  qpat_x_assum `terms = _` SUBST_ALL_TAC >>
  asm_rewrite_tac[]
QED

Triviality phi_partition_prefix_length:
  !dfg insts lbl.
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> ==>
    LENGTH (FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts) +
    LENGTH (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
      (TAKE (phi_prefix_length insts) insts)) =
    phi_prefix_length insts
Proof
  rpt strip_tac >>
  qabbrev_tac `phis = FILTER (\inst. inst.inst_opcode = PHI) insts` >>
  `TAKE (phi_prefix_length insts) insts = phis` by
    (qunabbrev_tac `phis` >>
     `TAKE (LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)) insts =
      FILTER (\inst. inst.inst_opcode = PHI) insts` by
        metis_tac[phi_prefix_take_filter] >>
     `phi_prefix_length insts = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` by
        metis_tac[phi_prefix_length_filter_phi] >>
     simp[]) >>
  `FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts =
   FILTER (\inst. phi_single_origin dfg inst = NONE) phis` by
    simp[Abbr `phis`, rich_listTheory.FILTER_FILTER, combinTheory.o_DEF, CONJ_COMM] >>
  `LENGTH phis = phi_prefix_length insts` by
    (simp[Abbr `phis`] >> metis_tac[phi_prefix_length_filter_phi]) >>
  `!xs. LENGTH (FILTER (\inst. phi_single_origin dfg inst = NONE) xs) +
        LENGTH (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin) xs) =
        LENGTH xs` by
    (Induct >> simp[] >> Cases_on `phi_single_origin dfg h` >> simp[]) >>
  simp[]
QED

Triviality exec_block_same_after_transform_prefix:
  !dfg insts lbl fuel ctx s.
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> /\
    pseudos_prefix <|bb_label := lbl; bb_instructions := insts|> ==>
    let params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts in
    let eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
          (TAKE (phi_prefix_length insts) insts) in
      exec_block fuel ctx <|bb_label := lbl; bb_instructions := insts|>
        (s with vs_inst_idx := phi_prefix_length insts + LENGTH params) =
      exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
        (s with vs_inst_idx :=
          phi_prefix_length (transform_insts dfg insts) + LENGTH params + LENGTH eliminated)
Proof
  rpt strip_tac >> simp[LET_DEF] >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  `phi_prefix_length (transform_insts dfg insts) = LENGTH kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `LENGTH kept + LENGTH eliminated = phi_prefix_length insts` by
    (qunabbrev_tac `kept` >> qunabbrev_tac `eliminated` >>
     qspecl_then [`dfg`, `insts`, `lbl`] mp_tac phi_partition_prefix_length >> simp[]) >>
  `phi_prefix_length (transform_insts dfg insts) + LENGTH params + LENGTH eliminated =
   phi_prefix_length insts + LENGTH params` by decide_tac >>
  qspecl_then [`fuel`, `ctx`,
    `<|bb_label := lbl; bb_instructions := insts|>`,
    `<|bb_label := lbl; bb_instructions := transform_insts dfg insts|>`,
    `s with vs_inst_idx := phi_prefix_length insts + LENGTH params`]
    mp_tac exec_block_same_suffix >>
  impl_tac >-
    (`DROP (phi_prefix_length insts + LENGTH params) insts =
      DROP (phi_prefix_length insts + LENGTH params) (transform_insts dfg insts)` by
       (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_suffix_after_eliminated_eq >>
        simp[LET_DEF, Abbr `kept`, Abbr `params`, Abbr `eliminated`] >>
        strip_tac >>
        `LENGTH (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
            (TAKE (phi_prefix_length insts) insts)) +
         (LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) +
          LENGTH (FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts)) =
         phi_prefix_length insts + LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts)` by
          decide_tac >>
        `LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) + phi_prefix_length insts =
         phi_prefix_length insts + LENGTH (FILTER (\inst. is_param_opcode inst.inst_opcode) insts)` by
          decide_tac >>
        qpat_x_assum `DROP _ insts = DROP _ (transform_insts dfg insts)` mp_tac >>
        asm_rewrite_tac[] >>
        disch_then ACCEPT_TAC) >>
     simp[] >>
     `LENGTH params + phi_prefix_length insts = phi_prefix_length insts + LENGTH params` by
       decide_tac >>
     asm_rewrite_tac[]) >>
  strip_tac >>
  `LENGTH params + phi_prefix_length insts = phi_prefix_length insts + LENGTH params` by
    decide_tac >>
  `LENGTH eliminated + (LENGTH params + phi_prefix_length (transform_insts dfg insts)) =
   phi_prefix_length insts + LENGTH params` by
    decide_tac >>
  asm_rewrite_tac[]
QED

Triviality exec_block_after_transform_prefix_state_eq:
  !dfg insts lbl fuel ctx s_phi s_kept s_params t_params t_elim.
    bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
    pseudos_prefix <| bb_label := lbl; bb_instructions := insts |> /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s_phi = OK s_params /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s_kept = OK t_params /\
    run_insts fuel ctx
      (MAP (transform_inst dfg)
        (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
          (TAKE (phi_prefix_length insts) insts))) t_params = OK t_elim /\
    t_elim = s_params ==>
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := insts |>
      (s_phi with vs_inst_idx := phi_prefix_length insts) =
    exec_block fuel ctx <| bb_label := lbl; bb_instructions := transform_insts dfg insts |>
      (s_kept with vs_inst_idx := phi_prefix_length (transform_insts dfg insts))
Proof
  rpt strip_tac >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  `phi_prefix_length (transform_insts dfg insts) = LENGTH kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := insts|>
      (s_phi with vs_inst_idx := phi_prefix_length insts) =
   exec_block fuel ctx <|bb_label := lbl; bb_instructions := insts|>
      (s_params with vs_inst_idx := phi_prefix_length insts + LENGTH params)` by
    (qspecl_then [`insts`, `lbl`, `fuel`, `ctx`, `s_phi`, `s_params`]
       mp_tac exec_block_skip_original_params >>
     simp[Abbr `params`]) >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
      (s_kept with vs_inst_idx := phi_prefix_length (transform_insts dfg insts)) =
   exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
      (t_params with vs_inst_idx := LENGTH kept + LENGTH params)` by
    (asm_rewrite_tac[] >>
     qspecl_then [`dfg`, `insts`, `lbl`, `fuel`, `ctx`, `s_kept`, `t_params`]
       mp_tac exec_block_skip_transformed_params >>
     simp[Abbr `kept`, Abbr `params`]) >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
      (t_params with vs_inst_idx := LENGTH kept + LENGTH params) =
   exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
      (t_elim with vs_inst_idx := LENGTH kept + LENGTH params + LENGTH eliminated)` by
    (qspecl_then [`dfg`, `insts`, `lbl`, `fuel`, `ctx`, `t_params`, `t_elim`]
       mp_tac exec_block_skip_transformed_eliminated >>
     simp[Abbr `kept`, Abbr `params`, Abbr `eliminated`]) >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := insts|>
      (s_params with vs_inst_idx := phi_prefix_length insts + LENGTH params) =
   exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
      (s_params with vs_inst_idx :=
        phi_prefix_length (transform_insts dfg insts) + LENGTH params + LENGTH eliminated)` by
    (qspecl_then [`dfg`, `insts`, `lbl`, `fuel`, `ctx`, `s_params`]
       mp_tac exec_block_same_after_transform_prefix >>
     simp[LET_DEF, Abbr `params`, Abbr `eliminated`]) >>
  gvs[]
QED

Triviality update_var_commutes:
  !x1 x2 v1 v2 s.
    x1 <> x2 ==>
    update_var x1 v1 (update_var x2 v2 s) =
    update_var x2 v2 (update_var x1 v1 s)
Proof
  rw[update_var_def, venom_state_component_equality, FUPDATE_COMMUTES]
QED

Triviality update_var_same:
  !x v1 v2 s.
    update_var x v1 (update_var x v2 s) = update_var x v1 s
Proof
  rw[update_var_def, venom_state_component_equality]
QED

Triviality state_equiv_update_var_remove:
  !vars x v s1 s2.
    x NOTIN vars /\
    lookup_var x s1 = SOME v /\
    state_equiv (x INSERT vars) s1 s2 ==>
    state_equiv vars s1 (update_var x v s2)
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[]
QED

Triviality state_equiv_update_left_insert:
  !vars x v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv (x INSERT vars) (update_var x v s1) s2
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def,
     FLOOKUP_UPDATE]
QED

Triviality eval_phis_filter_removed_state_equiv:
  !phis keep s s_all s_keep.
    EVERY (\inst. inst.inst_opcode = PHI) phis /\
    eval_phis s phis = OK s_all /\
    eval_phis s (FILTER keep phis) = OK s_keep ==>
    state_equiv
      (set (FLAT (MAP (\inst. inst.inst_outputs) (FILTER ($~ o keep) phis))))
      s_all s_keep
Proof
  Induct >> simp[eval_phis_def, state_equiv_refl] >> rpt strip_tac >> gvs[] >>
  Cases_on `eval_one_phi s h` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `eval_phis s phis` >> gvs[] >>
  rename1 `eval_phis s phis = OK s_tail` >>
  Cases_on `keep h` >> gvs[eval_phis_def]
  >- (Cases_on `eval_phis s (FILTER keep phis)` >> gvs[] >>
      first_x_assum (qspecl_then [`keep`, `s`, `s_tail`, `v`] mp_tac) >>
      simp[] >> strip_tac >>
      metis_tac[stateEquivPropsTheory.update_var_preserves]) >>
  first_x_assum (qspecl_then [`keep`, `s`, `s_tail`, `s_keep`] mp_tac) >>
  simp[] >> strip_tac >>
  drule eval_one_phi_imp_inst_outputs >> strip_tac >> gvs[] >>
  `{x0} UNION set (FLAT (MAP (\inst. inst.inst_outputs) (FILTER ($~ o keep) phis))) =
   x0 INSERT set (FLAT (MAP (\inst. inst.inst_outputs) (FILTER ($~ o keep) phis)))` by
    simp[pred_setTheory.EXTENSION] >>
  pop_assum SUBST1_TAC >>
  irule state_equiv_update_left_insert >> simp[]
QED

Triviality eval_phis_filter_removed_error_index:
  !phis keep s s_keep e.
    EVERY (\inst. inst.inst_opcode = PHI) phis /\
    eval_phis s phis = Error e /\
    eval_phis s (FILTER keep phis) = OK s_keep ==>
    ?k.
      k < LENGTH (FILTER ($~ o keep) phis) /\
      eval_one_phi s (EL k (FILTER ($~ o keep) phis)) = NONE /\
      !j. j < k ==>
        ?out v. eval_one_phi s (EL j (FILTER ($~ o keep) phis)) = SOME (out, v)
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `eval_one_phi s h` >> gvs[]
  >- (Cases_on `keep h` >> gvs[eval_phis_def] >>
      qexists_tac `0` >> simp[]) >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `eval_phis s phis` >> gvs[] >>
  Cases_on `keep h` >> gvs[eval_phis_def]
  >- (Cases_on `eval_phis s (FILTER keep phis)` >> gvs[] >>
      first_x_assum (qspecl_then [`keep`, `s`, `v`, `e`] mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `k` >> simp[])
  >- (first_x_assum (qspecl_then [`keep`, `s`, `s_keep`, `e`] mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `SUC k` >> simp[] >>
      Cases_on `j` >> simp[] >> metis_tac[])
QED

Triviality phi_prefix_length_every_phi:
  !insts.
    EVERY (\inst. inst.inst_opcode = PHI) insts ==>
    phi_prefix_length insts = LENGTH insts
Proof
  Induct >> rw[phi_prefix_length_def]
QED

Triviality phi_prefix_all_phi_local:
  !insts. EVERY (\inst. inst.inst_opcode = PHI) (TAKE (phi_prefix_length insts) insts)
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def]
QED

Triviality eval_phis_take_phi_prefix_eq:
  !insts lbl s.
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> ==>
    eval_phis s insts = eval_phis s (TAKE (phi_prefix_length insts) insts)
Proof
  rpt strip_tac >>
  `phi_prefix_length (TAKE (phi_prefix_length insts) insts) = phi_prefix_length insts` by
    (`EVERY (\inst. inst.inst_opcode = PHI) (TAKE (phi_prefix_length insts) insts)` by
       simp[phi_prefix_all_phi_local] >>
     `LENGTH (TAKE (phi_prefix_length insts) insts) = phi_prefix_length insts` by
       simp[venomExecProofsTheory.phi_prefix_length_le] >>
     simp[phi_prefix_length_every_phi]) >>
  irule venomExecProofsTheory.eval_phis_same_phi_prefix >> simp[] >>
  rpt strip_tac >> simp[EL_TAKE]
QED

Triviality eval_phis_take_phi_prefix:
  !insts lbl s s_phi.
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> /\
    eval_phis s insts = OK s_phi ==>
    eval_phis s (TAKE (phi_prefix_length insts) insts) = OK s_phi
Proof
  rpt strip_tac >>
  `phi_prefix_length (TAKE (phi_prefix_length insts) insts) = phi_prefix_length insts` by
    (`EVERY (\inst. inst.inst_opcode = PHI) (TAKE (phi_prefix_length insts) insts)` by
       simp[phi_prefix_all_phi_local] >>
     `LENGTH (TAKE (phi_prefix_length insts) insts) = phi_prefix_length insts` by
       simp[venomExecProofsTheory.phi_prefix_length_le] >>
     simp[phi_prefix_length_every_phi]) >>
  `!i. i < phi_prefix_length insts ==>
       EL i insts = EL i (TAKE (phi_prefix_length insts) insts)` by
    simp[EL_TAKE] >>
  `eval_phis s insts = eval_phis s (TAKE (phi_prefix_length insts) insts)` by
    (irule venomExecProofsTheory.eval_phis_same_phi_prefix >> simp[]) >>
  gvs[]
QED

Triviality kept_eq_filter_prefix:
  !dfg insts lbl.
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> ==>
    FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts =
    FILTER (\inst. phi_single_origin dfg inst = NONE) (TAKE (phi_prefix_length insts) insts)
Proof
  rpt strip_tac >>
  `TAKE (phi_prefix_length insts) insts = FILTER (\inst. inst.inst_opcode = PHI) insts` by
    (`TAKE (LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)) insts =
      FILTER (\inst. inst.inst_opcode = PHI) insts` by
        metis_tac[phi_prefix_take_filter] >>
     `phi_prefix_length insts = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` by
        metis_tac[phi_prefix_length_filter_phi] >>
     simp[]) >>
  simp[rich_listTheory.FILTER_FILTER, combinTheory.o_DEF, CONJ_COMM]
QED

Triviality removed_single_origin_filter_eq:
  !dfg insts.
    FILTER ($~ o (\inst. phi_single_origin dfg inst = NONE)) insts =
    FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin) insts
Proof
  gen_tac >> Induct >> simp[combinTheory.o_DEF] >>
  Cases_on `phi_single_origin dfg h` >> simp[]
QED

Triviality eval_phis_original_error_eliminated_index:
  !dfg insts lbl kept eliminated s e s_kept.
    kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts /\
    eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
      (TAKE (phi_prefix_length insts) insts) /\
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> /\
    eval_phis s insts = Error e /\
    eval_phis s kept = OK s_kept ==>
    ?k.
      k < LENGTH eliminated /\
      eval_one_phi s (EL k eliminated) = NONE /\
      !j. j < k ==> ?out v. eval_one_phi s (EL j eliminated) = SOME (out, v)
Proof
  rpt strip_tac >>
  qabbrev_tac `phis = TAKE (phi_prefix_length insts) insts` >>
  `eval_phis s phis = Error e` by
    (qunabbrev_tac `phis` >> metis_tac[eval_phis_take_phi_prefix_eq]) >>
  `EVERY (\inst. inst.inst_opcode = PHI) phis` by
    (simp[Abbr `phis`, phi_prefix_all_phi_local]) >>
  `kept = FILTER (\inst. phi_single_origin dfg inst = NONE) phis` by
    (qunabbrev_tac `phis` >> metis_tac[kept_eq_filter_prefix]) >>
  `eliminated = FILTER ($~ o (\inst. phi_single_origin dfg inst = NONE)) phis` by
    (qunabbrev_tac `phis` >> simp[removed_single_origin_filter_eq]) >>
  qspecl_then [`phis`, `\inst. phi_single_origin dfg inst = NONE`, `s`, `s_kept`, `e`]
    mp_tac eval_phis_filter_removed_error_index >>
  simp[] >>
  qpat_x_assum
    `kept = FILTER (\inst. phi_single_origin dfg inst = NONE) phis`
    (SUBST1_TAC o SYM) >>
  simp[] >> strip_tac >>
  qexists_tac `k` >> simp[]
QED

Triviality eval_phis_original_kept_state_equiv:
  !dfg insts lbl kept eliminated s s_phi s_kept.
    kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts /\
    eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
      (TAKE (phi_prefix_length insts) insts) /\
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> /\
    eval_phis s insts = OK s_phi /\
    eval_phis s kept = OK s_kept ==>
    state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))) s_phi s_kept
Proof
  rpt strip_tac >>
  qabbrev_tac `phis = TAKE (phi_prefix_length insts) insts` >>
  `eval_phis s phis = OK s_phi` by
    (qunabbrev_tac `phis` >> metis_tac[eval_phis_take_phi_prefix]) >>
  `EVERY (\inst. inst.inst_opcode = PHI) phis` by
    (simp[Abbr `phis`, phi_prefix_all_phi_local]) >>
  `kept = FILTER (\inst. phi_single_origin dfg inst = NONE) phis` by
    (qunabbrev_tac `phis` >> metis_tac[kept_eq_filter_prefix]) >>
  `eliminated = FILTER ($~ o (\inst. phi_single_origin dfg inst = NONE)) phis` by
    (qunabbrev_tac `phis` >> simp[removed_single_origin_filter_eq]) >>
  qspecl_then [`phis`, `\inst. phi_single_origin dfg inst = NONE`, `s`, `s_phi`, `s_kept`]
    mp_tac eval_phis_filter_removed_state_equiv >>
  impl_tac >-
    (simp[] >>
     qpat_x_assum
       `kept = FILTER (\inst. phi_single_origin dfg inst = NONE) phis`
       (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  strip_tac >>
  qpat_x_assum
    `eliminated = FILTER ($~ o (\inst. phi_single_origin dfg inst = NONE)) phis`
    SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Triviality lookup_var_update_var_neq:
  !x y v s. x <> y ==> lookup_var x (update_var y v s) = lookup_var x s
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[lookup_var_def, update_var_def] >>
  simp[] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [FLOOKUP_UPDATE])) >>
  `y <> x` by
    (strip_tac >> qpat_x_assum `x <> y` mp_tac >> asm_rewrite_tac[]) >>
  `(y = x) = F` by
    (qpat_x_assum `y <> x` (ACCEPT_TAC o EQF_INTRO)) >>
  asm_rewrite_tac[]
QED

Triviality eval_phis_lookup_phi_output:
  !insts s s' i out v.
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) /\
    eval_phis s insts = OK s' /\
    i < phi_prefix_length insts /\
    eval_one_phi s (EL i insts) = SOME (out, v) ==>
    lookup_var out s' = SOME v
Proof
  Induct >> simp[eval_phis_def, phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def, eval_phis_def] >>
  Cases_on `eval_one_phi s h` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `eval_phis s insts` >> gvs[] >>
  rename1 `eval_phis s insts = OK s_tail` >>
  Cases_on `i` >> gvs[]
  >- (drule eval_one_phi_imp_inst_outputs >> strip_tac >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `n < phi_prefix_length insts` >>
  `lookup_var out s_tail = SOME v` by
    (first_x_assum (qspecl_then [`s`, `s_tail`, `n`, `out`, `v`] mp_tac) >>
     simp[] >>
     impl_tac >- fs[ALL_DISTINCT_APPEND] >>
     disch_then ACCEPT_TAC) >>
  `out <> x0` by
    (`h.inst_outputs = [x0]` by metis_tac[eval_one_phi_imp_inst_outputs] >>
     `(EL n insts).inst_outputs = [out]` by metis_tac[eval_one_phi_imp_inst_outputs] >>
     `n < LENGTH insts` by
       (irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
        qexists_tac `phi_prefix_length insts` >>
        simp[venomExecProofsTheory.phi_prefix_length_le]) >>
     `MEM (EL n insts) insts` by simp[EL_MEM] >>
     `MEM out (EL n insts).inst_outputs` by simp[] >>
     `MEM out (FLAT (MAP (\inst. inst.inst_outputs) insts))` by
       (simp[MEM_FLAT] >>
        qexists_tac `(EL n insts).inst_outputs` >> simp[] >>
        simp[MEM_MAP] >>
        qexists_tac `EL n insts` >> simp[EL_MEM]) >>
     `ALL_DISTINCT ([x0] ++ FLAT (MAP (\inst. inst.inst_outputs) insts))` by gvs[] >>
     `~MEM x0 (FLAT (MAP (\inst. inst.inst_outputs) insts))` by fs[ALL_DISTINCT_APPEND] >>
     strip_tac >> gvs[]) >>
  `lookup_var out (update_var x0 x1 s_tail) = lookup_var out s_tail` by
    (irule lookup_var_update_var_neq >> first_assum ACCEPT_TAC) >>
  pop_assum SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Triviality flat_map_filter_sublist:
  !f P l. rich_list$sublist (FLAT (MAP f (FILTER P l))) (FLAT (MAP f l))
Proof
  Induct_on `l` >> simp[rich_listTheory.sublist_refl] >> rpt gen_tac >>
  Cases_on `P h` >> asm_rewrite_tac[]
  >- (PURE_REWRITE_TAC [MAP, FLAT] >>
      irule rich_listTheory.sublist_append_pair >>
      conj_tac >- simp[rich_listTheory.sublist_refl] >>
      last_x_assum (qspec_then `f` (qspec_then `P` ACCEPT_TAC))) >>
  irule rich_listTheory.sublist_append_include >>
  last_x_assum (qspec_then `f` (qspec_then `P` ACCEPT_TAC))
QED

Triviality all_distinct_flat_map_filter:
  !f P l. ALL_DISTINCT (FLAT (MAP f l)) ==>
          ALL_DISTINCT (FLAT (MAP f (FILTER P l)))
Proof
  rpt strip_tac >>
  irule rich_listTheory.sublist_ALL_DISTINCT >>
  qexists_tac `FLAT (MAP f l)` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  ACCEPT_TAC (Q.SPECL [`f`, `P`, `l`] flat_map_filter_sublist)
QED

Triviality flat_map_take_sublist:
  !f n l. rich_list$sublist (FLAT (MAP f (TAKE n l))) (FLAT (MAP f l))
Proof
  Induct_on `l` >> simp[rich_listTheory.sublist_refl] >> rpt gen_tac >>
  Cases_on `n` >> simp[listTheory.TAKE_def, rich_listTheory.sublist_def] >>
  PURE_REWRITE_TAC [MAP, FLAT] >>
  irule rich_listTheory.sublist_append_pair >>
  conj_tac >- simp[rich_listTheory.sublist_refl] >>
  rename1 `TAKE n0 l` >>
  last_x_assum (qspec_then `f` (qspec_then `n0` ACCEPT_TAC))
QED

Triviality all_distinct_flat_map_take:
  !f n l. ALL_DISTINCT (FLAT (MAP f l)) ==>
          ALL_DISTINCT (FLAT (MAP f (TAKE n l)))
Proof
  rpt strip_tac >>
  irule rich_listTheory.sublist_ALL_DISTINCT >>
  qexists_tac `FLAT (MAP f l)` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  ACCEPT_TAC (Q.SPECL [`f`, `n`, `l`] flat_map_take_sublist)
QED

Triviality flat_map_drop_sublist:
  !f n l. rich_list$sublist (FLAT (MAP f (DROP n l))) (FLAT (MAP f l))
Proof
  Induct_on `l` >> simp[rich_listTheory.sublist_refl] >> rpt gen_tac >>
  Cases_on `n` >> simp[listTheory.DROP_def, rich_listTheory.sublist_refl] >>
  PURE_REWRITE_TAC [MAP, FLAT] >>
  irule rich_listTheory.sublist_append_include >>
  rename1 `DROP n0 l` >>
  last_x_assum (qspec_then `f` (qspec_then `n0` ACCEPT_TAC))
QED

Triviality all_distinct_flat_map_drop:
  !f n l. ALL_DISTINCT (FLAT (MAP f l)) ==>
          ALL_DISTINCT (FLAT (MAP f (DROP n l)))
Proof
  rpt strip_tac >>
  irule rich_listTheory.sublist_ALL_DISTINCT >>
  qexists_tac `FLAT (MAP f l)` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  ACCEPT_TAC (Q.SPECL [`f`, `n`, `l`] flat_map_drop_sublist)
QED

Triviality eliminated_outputs_distinct:
  !func bb eliminated.
    eliminated = FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    wf_ir_fn func /\ MEM bb func.fn_blocks ==>
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) eliminated))
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    (fs[wf_ir_fn_def] >> metis_tac[ssa_form_block_outputs_distinct]) >>
  qpat_x_assum `eliminated = _` SUBST1_TAC >>
  irule all_distinct_flat_map_filter >>
  irule all_distinct_flat_map_take >>
  simp[]
QED

Triviality eliminated_output_drop_facts:
  !eliminated k out v s.
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) eliminated)) /\
    k < LENGTH eliminated /\
    eval_one_phi s (EL k eliminated) = SOME (out, v) ==>
    set (FLAT (MAP (\inst. inst.inst_outputs) (DROP k eliminated))) SUBSET
      out INSERT set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated))) /\
    out NOTIN set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated)))
Proof
  rpt gen_tac >> strip_tac >>
  `(EL k eliminated).inst_outputs = [out]` by metis_tac[eval_one_phi_imp_inst_outputs] >>
  `DROP k eliminated = EL k eliminated :: DROP (SUC k) eliminated` by
    simp[rich_listTheory.DROP_CONS_EL] >>
  conj_tac
  >- (asm_rewrite_tac[] >> simp[pred_setTheory.SUBSET_DEF]) >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) (DROP k eliminated)))` by
    (irule all_distinct_flat_map_drop >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `DROP k eliminated = _` SUBST_ALL_TAC >>
  gvs[ALL_DISTINCT_APPEND]
QED

Triviality run_insts_preserves_lookup_no_outputs:
  !insts fuel ctx v st st'.
    run_insts fuel ctx insts st = OK st' /\
    EVERY (\inst. ~MEM v inst.inst_outputs /\ ~is_terminator inst.inst_opcode) insts ==>
    lookup_var v st' = lookup_var v st
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h st` >> gvs[] >>
  `lookup_var v v' = lookup_var v st` by
    (drule_all venomInstPropsTheory.step_preserves_non_output_vars >> simp[]) >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `v'`, `st'`] mp_tac) >>
  simp[]
QED

Triviality run_insts_params_preserves_eliminated_eval:
  !func bb eliminated k out v fuel ctx s s_phi s_params.
    eliminated = FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    wf_ir_fn func /\ MEM bb func.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    k < LENGTH eliminated /\
    eval_one_phi s (EL k eliminated) = SOME (out, v) /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_phi = OK s_params ==>
    lookup_var out s_params = SOME v
Proof
  rpt strip_tac >>
  qabbrev_tac `inst = EL k eliminated` >>
  `MEM inst eliminated` by simp[Abbr `inst`, EL_MEM] >>
  `MEM inst (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` by
    (qpat_x_assum `eliminated = _` SUBST_ALL_TAC >> gvs[MEM_FILTER]) >>
  `MEM inst bb.bb_instructions` by metis_tac[rich_listTheory.MEM_TAKE] >>
  `?origin. phi_single_origin (dfg_build_function func) inst = SOME origin` by
    (qpat_x_assum `eliminated = _` SUBST_ALL_TAC >> gvs[MEM_FILTER]) >>
  `inst.inst_opcode = PHI` by
    (`is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >> fs[is_phi_inst_def]) >>
  `inst.inst_outputs = [out]` by metis_tac[eval_one_phi_imp_inst_outputs] >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by
    (fs[wf_ir_fn_def] >> metis_tac[ssa_form_block_outputs_distinct]) >>
  `lookup_var out s_phi = SOME v` by
    (`?i. i < LENGTH (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
          EL i (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst` by
       metis_tac[MEM_EL] >>
     `i < phi_prefix_length bb.bb_instructions` by
       (gvs[LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le]) >>
     `EL i bb.bb_instructions = inst` by
       (qpat_x_assum `EL i (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = inst` mp_tac >>
        simp[EL_TAKE]) >>
     qspecl_then [`bb.bb_instructions`, `s`, `s_phi`, `i`, `out`, `v`]
       mp_tac eval_phis_lookup_phi_output >>
     impl_tac >-
       (rpt conj_tac >> simp[] >>
        qpat_x_assum `EL i bb.bb_instructions = inst` SUBST1_TAC >>
        simp[]) >>
     disch_then ACCEPT_TAC) >>
  `lookup_var out s_params = lookup_var out s_phi` by
    (qspecl_then [`FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions`,
                  `fuel`, `ctx`, `out`, `s_phi`, `s_params`]
       mp_tac run_insts_preserves_lookup_no_outputs >>
     simp[] >>
     impl_tac >-
       (rw[EVERY_MEM, MEM_FILTER]
        >- (`inst' <> inst` by (strip_tac >> gvs[is_param_opcode_def]) >>
            qspecl_then [`func`, `bb`, `inst`, `inst'`, `out`]
              mp_tac wf_ir_phi_output_not_other_output >>
            simp[])
        >- fs[is_param_opcode_iff, is_terminator_def]) >>
     disch_then ACCEPT_TAC) >>
  simp[]
QED

Triviality transform_insts_preserves_lookup_source:
  !insts dfg fuel ctx v st st'.
    run_insts fuel ctx (MAP (transform_inst dfg) insts) st = OK st' /\
    EVERY (\inst. ~MEM v inst.inst_outputs /\ ~is_terminator (transform_inst dfg inst).inst_opcode) insts ==>
    lookup_var v st' = lookup_var v st
Proof
  rpt strip_tac >>
  qspecl_then [`MAP (transform_inst dfg) insts`, `fuel`, `ctx`, `v`, `st`, `st'`]
    mp_tac run_insts_preserves_lookup_no_outputs >>
  simp[EVERY_MAP] >>
  gvs[EVERY_MEM, transform_inst_preserves_outputs]
QED

Triviality eliminated_phi_prefix_members:
  !dfg insts n inst.
    MEM inst
      (TAKE n (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length insts) insts))) ==>
    MEM inst insts /\
    (?origin. phi_single_origin dfg inst = SOME origin) /\
    ~is_terminator (transform_inst dfg inst).inst_opcode
Proof
  rpt strip_tac >>
  drule rich_listTheory.MEM_TAKE >> strip_tac >>
  gvs[MEM_FILTER] >>
  drule rich_listTheory.MEM_TAKE >> strip_tac >>
  metis_tac[transform_inst_single_origin_not_terminator]
QED

Triviality eliminated_phi_prefix_every_for_block:
  !func bb n.
    EVERY (\producer.
      MEM producer bb.bb_instructions /\
      ~is_terminator (transform_inst (dfg_build_function func) producer).inst_opcode)
    (TAKE n (FILTER (\inst.
      ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)))
Proof
  rw[EVERY_MEM] >>
  drule eliminated_phi_prefix_members >> simp[]
QED

Triviality phi_elim_safe_transform_insts_preserves_source:
  !func bb prefix inst origin src_var fuel ctx st st'.
    let dfg = dfg_build_function func in
      phi_elim_safe_fn func /\
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      phi_single_origin dfg inst = SOME origin /\
      origin.inst_outputs = [src_var] /\
      EVERY (\producer.
        MEM producer bb.bb_instructions /\
        ~is_terminator (transform_inst dfg producer).inst_opcode) prefix /\
      run_insts fuel ctx (MAP (transform_inst dfg) prefix) st = OK st' ==>
      lookup_var src_var st' = lookup_var src_var st
Proof
  rw[LET_DEF] >>
  qspecl_then
    [`prefix`, `dfg_build_function func`, `fuel`, `ctx`, `src_var`, `st`, `st'`]
    mp_tac transform_insts_preserves_lookup_source >>
  simp[] >>
  gvs[EVERY_MEM] >> rpt strip_tac >>
  metis_tac[phi_elim_safe_fn_source_not_output]
QED

Triviality run_insts_params_preserves_single_origin_source:
  !func bb inst origin src_var fuel ctx st st'.
    let dfg = dfg_build_function func in
      phi_elim_safe_fn func /\
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      phi_single_origin dfg inst = SOME origin /\
      origin.inst_outputs = [src_var] /\
      run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) st = OK st' ==>
      lookup_var src_var st' = lookup_var src_var st
Proof
  rw[LET_DEF] >>
  qspecl_then
    [`FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions`,
     `fuel`, `ctx`, `src_var`, `st`, `st'`]
    mp_tac run_insts_preserves_lookup_no_outputs >>
  simp[] >>
  impl_tac >-
    (rw[EVERY_MEM, MEM_FILTER]
     >- (drule_all phi_elim_safe_fn_source_not_output >> simp[])
     >- fs[is_param_opcode_iff, is_terminator_def]) >>
  disch_then ACCEPT_TAC
QED

Triviality run_insts_params_and_eliminated_prefix_preserves_single_origin_source:
  !func bb inst origin src_var n fuel ctx st st_params st'.
    let dfg = dfg_build_function func in
    let prefix =
      TAKE n (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) in
      phi_elim_safe_fn func /\
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      phi_single_origin dfg inst = SOME origin /\
      origin.inst_outputs = [src_var] /\
      run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) st = OK st_params /\
      run_insts fuel ctx (MAP (transform_inst dfg) prefix) st_params = OK st' ==>
      lookup_var src_var st' = lookup_var src_var st
Proof
  rw[LET_DEF] >>
  `lookup_var src_var st_params = lookup_var src_var st` by
    (qspecl_then [`func`, `bb`, `inst`, `origin`, `src_var`, `fuel`, `ctx`, `st`, `st_params`]
       mp_tac run_insts_params_preserves_single_origin_source >>
     simp[LET_DEF]) >>
  `lookup_var src_var st' = lookup_var src_var st_params` by
    (qspecl_then
       [`func`, `bb`,
        `TAKE n (FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
          (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))`,
        `inst`, `origin`, `src_var`, `fuel`, `ctx`, `st_params`, `st'`]
       mp_tac phi_elim_safe_transform_insts_preserves_source >>
     simp[LET_DEF, eliminated_phi_prefix_every_for_block]) >>
  simp[]
QED

Triviality eval_one_phi_update_inst_idx:
  !s idx inst.
    eval_one_phi (s with vs_inst_idx := idx) inst = eval_one_phi s inst
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_outputs` >> simp[eval_one_phi_def] >>
  Cases_on `t` >> simp[eval_one_phi_def] >>
  Cases_on `s.vs_prev_bb` >> simp[eval_one_phi_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  Cases_on `x'` >> simp[eval_operand_def, lookup_var_def]
QED

Triviality eliminated_phi_eval_one_none_source_lookup:
  !func bb eliminated k s origin src_var.
    eliminated =
      FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    wf_ir_fn func /\
    MEM bb func.fn_blocks /\
    s.vs_prev_bb <> NONE /\
    k < LENGTH eliminated /\
    phi_single_origin (dfg_build_function func) (EL k eliminated) = SOME origin /\
    origin.inst_outputs = [src_var] /\
    eval_one_phi s (EL k eliminated) = NONE ==>
    lookup_var src_var s = NONE
Proof
  rpt strip_tac >>
  `phi_wf_fn func` by metis_tac[wf_ir_implies_phi_wf] >>
  qabbrev_tac `inst = EL k eliminated` >>
  `MEM inst eliminated` by simp[Abbr `inst`, EL_MEM] >>
  `MEM inst bb.bb_instructions` by
    (qpat_x_assum `eliminated = _` SUBST_ALL_TAC >>
     gvs[MEM_FILTER] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
  `?idx. get_instruction bb idx = SOME inst` by
    (fs[MEM_EL, get_instruction_def] >> metis_tac[]) >>
  Cases_on `s.vs_prev_bb` >> gvs[] >>
  qpat_x_assum `phi_wf_fn func` mp_tac >>
  simp[phi_wf_fn_def, LET_DEF] >> strip_tac >>
  qpat_x_assum `!bb inst origin src_var prev s. _`
    (qspecl_then [`bb`, `inst`, `origin`, `src_var`, `x`, `s with vs_inst_idx := idx`] mp_tac) >>
  simp[eval_one_phi_update_inst_idx, lookup_var_def]
QED

Triviality mem_get_instruction:
  !bb inst.
    MEM inst bb.bb_instructions ==> ?idx. get_instruction bb idx = SOME inst
Proof
  rw[MEM_EL, get_instruction_def] >> metis_tac[]
QED

Triviality eval_phis_ok_mem_phi_prefix:
  !insts s s' inst.
    eval_phis s insts = OK s' /\
    MEM inst (TAKE (phi_prefix_length insts) insts) ==>
    ?out v. eval_one_phi s inst = SOME (out, v)
Proof
  Induct >> simp[eval_phis_def, phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `eval_one_phi s h` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  Cases_on `eval_phis s insts` >> gvs[] >>
  res_tac
QED

Triviality mem_phi_prefix_opcode:
  !insts inst.
    MEM inst (TAKE (phi_prefix_length insts) insts) ==>
    inst.inst_opcode = PHI
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def]
QED

Triviality eval_phis_ok_phi_prefix_sublist:
  !phis s insts s'.
    eval_phis s insts = OK s' /\
    EVERY (\inst. MEM inst (TAKE (phi_prefix_length insts) insts)) phis ==>
    ?s_phis. eval_phis s phis = OK s_phis
Proof
  Induct >> simp[eval_phis_def] >> rpt strip_tac >>
  `h.inst_opcode = PHI` by metis_tac[mem_phi_prefix_opcode] >>
  `?out v. eval_one_phi s h = SOME (out, v)` by
    metis_tac[eval_phis_ok_mem_phi_prefix] >>
  `?s_tail. eval_phis s phis = OK s_tail` by
    (first_x_assum (qspecl_then [`s`, `insts`, `s'`] mp_tac) >>
     simp[]) >>
  qexists_tac `update_var out v s_tail` >>
  simp[eval_phis_def]
QED

Triviality eval_phis_kept_ok_from_original:
  !dfg insts lbl kept s s_phi.
    kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts /\
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> /\
    eval_phis s insts = OK s_phi ==>
    ?s_kept. eval_phis s kept = OK s_kept
Proof
  rpt strip_tac >>
  `TAKE (phi_prefix_length insts) insts = FILTER (\inst. inst.inst_opcode = PHI) insts` by
    (`TAKE (LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)) insts =
      FILTER (\inst. inst.inst_opcode = PHI) insts` by
        metis_tac[phi_prefix_take_filter] >>
     `phi_prefix_length insts = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` by
        metis_tac[phi_prefix_length_filter_phi] >>
     simp[]) >>
  qspecl_then [`kept`, `s`, `insts`, `s_phi`] mp_tac eval_phis_ok_phi_prefix_sublist >>
  simp[] >>
  impl_tac >-
    (gvs[EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
  disch_then ACCEPT_TAC
QED

Triviality transform_eval_phis_ok_from_original:
  !dfg insts lbl s s_phi.
    bb_well_formed <|bb_label := lbl; bb_instructions := insts|> /\
    eval_phis s insts = OK s_phi ==>
    ?s_kept. eval_phis s (transform_insts dfg insts) = OK s_kept
Proof
  rpt strip_tac >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  `?s_kept. eval_phis s kept = OK s_kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`, `kept`, `s`, `s_phi`]
       mp_tac eval_phis_kept_ok_from_original >>
     simp[Abbr `kept`]) >>
  qexists_tac `s_kept` >>
  qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
  simp[LET_DEF, Abbr `kept`]
QED

Triviality eliminated_phi_eval_one_info:
  !func bb inst s s_phi.
    let dfg = dfg_build_function func in
      wf_ir_fn func /\ MEM bb func.fn_blocks /\
      eval_phis s bb.bb_instructions = OK s_phi /\
      MEM inst (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) ==>
      ?origin src_var out v.
        phi_single_origin dfg inst = SOME origin /\
        origin.inst_outputs = [src_var] /\
        phi_well_formed inst.inst_operands /\
        phi_operands_direct dfg inst /\
        eval_one_phi s inst = SOME (out, v)
Proof
  rw[LET_DEF] >> gvs[MEM_FILTER] >>
  `MEM inst bb.bb_instructions` by metis_tac[rich_listTheory.MEM_TAKE] >>
  `?idx. get_instruction bb idx = SOME inst` by metis_tac[mem_get_instruction] >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  `phi_well_formed inst.inst_operands` by metis_tac[wf_ir_fn_def] >>
  `phi_operands_direct (dfg_build_function func) inst` by
    (fs[wf_ir_fn_def, LET_DEF] >> metis_tac[]) >>
  `?out v. eval_one_phi s inst = SOME (out, v)` by
    metis_tac[eval_phis_ok_mem_phi_prefix] >>
  `?src_var. origin.inst_outputs = [src_var]` by metis_tac[phi_single_origin_has_output] >>
  metis_tac[]
QED

Triviality eval_one_phi_single_origin_lookup:
  !dfg inst origin src_var s out v.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    phi_well_formed inst.inst_operands /\
    phi_operands_direct dfg inst /\
    eval_one_phi s inst = SOME (out, v) ==>
    inst.inst_outputs = [out] /\ lookup_var src_var s = SOME v
Proof
  rw[eval_one_phi_def] >> gvs[AllCaseEqs()] >>
  rename1 `resolve_phi prev inst.inst_operands = SOME op` >>
  `?var. op = Var var` by
    metis_tac[resolve_phi_well_formed] >>
  gvs[eval_operand_def] >>
  `dfg_lookup dfg var = SOME origin` by
    metis_tac[phi_operands_direct_lookup] >>
  `origin.inst_outputs = [var]` by metis_tac[dfg_lookup_single_output] >>
  gvs[]
QED

Triviality eval_phis_preserves_single_origin_source:
  !dfg inst origin src_var s phis s' out v.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    phi_well_formed inst.inst_operands /\
    phi_operands_direct dfg inst /\
    eval_one_phi s inst = SOME (out, v) /\
    eval_phis s phis = OK s' /\
    (!producer. MEM producer phis ==> producer.inst_opcode = PHI ==> ~MEM src_var producer.inst_outputs) ==>
    lookup_var src_var s' = SOME v
Proof
  rpt strip_tac >>
  drule_all eval_one_phi_single_origin_lookup >> strip_tac >>
  `FLOOKUP s'.vs_vars src_var = FLOOKUP s.vs_vars src_var` by
    (qspecl_then [`s`, `phis`, `src_var`, `s'`] mp_tac eval_phis_flookup_not_phi_output >>
     simp[]) >>
  gvs[lookup_var_def]
QED

Triviality transform_single_origin_phi_assign_step:
  !dfg inst origin src_var s out v.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    phi_well_formed inst.inst_operands /\
    phi_operands_direct dfg inst /\
    eval_one_phi s inst = SOME (out, v) ==>
    step_inst_base (transform_inst dfg inst) s = OK (update_var out v s)
Proof
  rpt strip_tac >>
  drule_all eval_one_phi_single_origin_lookup >> strip_tac >>
  `transform_inst dfg inst =
     inst with <| inst_opcode := ASSIGN; inst_operands := [Var src_var] |>` by
    metis_tac[transform_inst_phi_to_assign] >>
  simp[step_inst_base_def, eval_operand_def]
QED

Triviality transform_single_origin_phi_assign_step_stable_lookup:
  !dfg inst origin src_var s t out v.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    phi_well_formed inst.inst_operands /\
    phi_operands_direct dfg inst /\
    eval_one_phi s inst = SOME (out, v) /\
    lookup_var src_var t = lookup_var src_var s ==>
    step_inst_base (transform_inst dfg inst) t = OK (update_var out v t)
Proof
  rpt strip_tac >>
  drule_all eval_one_phi_single_origin_lookup >> strip_tac >>
  `transform_inst dfg inst =
     inst with <| inst_opcode := ASSIGN; inst_operands := [Var src_var] |>` by
    metis_tac[transform_inst_phi_to_assign] >>
  simp[step_inst_base_def, eval_operand_def]
QED

Triviality transform_single_origin_phi_assign_step_after_prefix:
  !func bb prefix inst origin src_var fuel ctx s st st' out v.
    let dfg = dfg_build_function func in
      phi_elim_safe_fn func /\
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      phi_single_origin dfg inst = SOME origin /\
      origin.inst_outputs = [src_var] /\
      phi_well_formed inst.inst_operands /\
      phi_operands_direct dfg inst /\
      eval_one_phi s inst = SOME (out, v) /\
      lookup_var src_var st = lookup_var src_var s /\
      EVERY (\producer.
        MEM producer bb.bb_instructions /\
        ~is_terminator (transform_inst dfg producer).inst_opcode) prefix /\
      run_insts fuel ctx (MAP (transform_inst dfg) prefix) st = OK st' ==>
      step_inst_base (transform_inst dfg inst) st' = OK (update_var out v st')
Proof
  rw[LET_DEF] >>
  `lookup_var src_var st' = lookup_var src_var st` by
    (qspecl_then [`func`, `bb`, `prefix`, `inst`, `origin`, `src_var`,
                  `fuel`, `ctx`, `st`, `st'`]
       mp_tac phi_elim_safe_transform_insts_preserves_source >>
     simp[LET_DEF]) >>
  qspecl_then [`dfg_build_function func`, `inst`, `origin`, `src_var`,
                `s`, `st'`, `out`, `v`]
    mp_tac transform_single_origin_phi_assign_step_stable_lookup >>
  simp[]
QED

Triviality transform_single_origin_phi_assign_run_insts_after_prefix:
  !func bb prefix inst origin src_var fuel ctx s st st' out v.
    let dfg = dfg_build_function func in
      phi_elim_safe_fn func /\
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      phi_single_origin dfg inst = SOME origin /\
      origin.inst_outputs = [src_var] /\
      phi_well_formed inst.inst_operands /\
      phi_operands_direct dfg inst /\
      eval_one_phi s inst = SOME (out, v) /\
      lookup_var src_var st = lookup_var src_var s /\
      EVERY (\producer.
        MEM producer bb.bb_instructions /\
        ~is_terminator (transform_inst dfg producer).inst_opcode) prefix /\
      run_insts fuel ctx (MAP (transform_inst dfg) prefix) st = OK st' ==>
      run_insts fuel ctx (MAP (transform_inst dfg) prefix ++ [transform_inst dfg inst]) st =
      OK (update_var out v st')
Proof
  rw[LET_DEF] >>
  simp[run_insts_append] >>
  `step_inst_base (transform_inst (dfg_build_function func) inst) st' =
   OK (update_var out v st')` by
    (qspecl_then [`func`, `bb`, `prefix`, `inst`, `origin`, `src_var`,
                  `fuel`, `ctx`, `s`, `st`, `st'`, `out`, `v`]
       mp_tac transform_single_origin_phi_assign_step_after_prefix >>
     simp[LET_DEF]) >>
  `~((transform_inst (dfg_build_function func) inst).inst_opcode = INVOKE)` by
    (drule transform_inst_single_origin_assign >> strip_tac >> simp[]) >>
  simp[run_insts_def, step_inst_def]
QED

Triviality transform_single_origin_phi_assign_run_insts_after_eliminated_prefix:
  !func bb n inst origin src_var fuel ctx s st st' out v.
    let dfg = dfg_build_function func in
    let prefix =
      TAKE n (FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) in
      phi_elim_safe_fn func /\
      MEM bb func.fn_blocks /\
      MEM inst bb.bb_instructions /\
      phi_single_origin dfg inst = SOME origin /\
      origin.inst_outputs = [src_var] /\
      phi_well_formed inst.inst_operands /\
      phi_operands_direct dfg inst /\
      eval_one_phi s inst = SOME (out, v) /\
      lookup_var src_var st = lookup_var src_var s /\
      run_insts fuel ctx (MAP (transform_inst dfg) prefix) st = OK st' ==>
      run_insts fuel ctx (MAP (transform_inst dfg) prefix ++ [transform_inst dfg inst]) st =
      OK (update_var out v st')
Proof
  rw[LET_DEF] >>
  qspecl_then
    [`func`, `bb`,
     `TAKE n (FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
       (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))`,
     `inst`, `origin`, `src_var`, `fuel`, `ctx`, `s`, `st`, `st'`, `out`, `v`]
    mp_tac transform_single_origin_phi_assign_run_insts_after_prefix >>
  simp[LET_DEF, eliminated_phi_prefix_every_for_block]
QED

Triviality transform_eliminated_phi_assign_run_insts_after_params_prefix:
  !func bb n inst fuel ctx s s_phi st st_params st'.
    let dfg = dfg_build_function func in
    let eliminated =
      FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) in
    let prefix = TAKE n eliminated in
      phi_elim_safe_fn func /\
      wf_ir_fn func /\
      MEM bb func.fn_blocks /\
      eval_phis s bb.bb_instructions = OK s_phi /\
      n < LENGTH eliminated /\
      inst = EL n eliminated /\
      (!phi origin src_var.
        MEM phi eliminated /\
        phi_single_origin dfg phi = SOME origin /\
        origin.inst_outputs = [src_var] ==>
        lookup_var src_var st = lookup_var src_var s) /\
      run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) st = OK st_params /\
      run_insts fuel ctx (MAP (transform_inst dfg) prefix) st_params = OK st' ==>
      ?out v.
        eval_one_phi s inst = SOME (out, v) /\
        run_insts fuel ctx (MAP (transform_inst dfg) prefix ++ [transform_inst dfg inst]) st_params =
          OK (update_var out v st')
Proof
  rw[LET_DEF] >>
  qabbrev_tac `dfg = dfg_build_function func` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)` >>
  qabbrev_tac `prefix = TAKE n eliminated` >>
  `EVERY (\producer.
      MEM producer bb.bb_instructions /\
      ~is_terminator (transform_inst (dfg_build_function func) producer).inst_opcode) prefix` by
    simp[Abbr `prefix`, Abbr `eliminated`, Abbr `dfg`, eliminated_phi_prefix_every_for_block] >>
  `MEM (EL n eliminated) eliminated` by (irule listTheory.EL_MEM >> simp[]) >>
  `MEM (EL n eliminated) bb.bb_instructions` by
    (qpat_x_assum `MEM (EL n eliminated) eliminated` mp_tac >>
     simp[Abbr `eliminated`, MEM_FILTER] >>
     metis_tac[rich_listTheory.MEM_TAKE]) >>
  qspecl_then [`func`, `bb`, `EL n eliminated`, `s`, `s_phi`] mp_tac eliminated_phi_eval_one_info >>
  simp[LET_DEF, Abbr `dfg`, Abbr `eliminated`] >>
  strip_tac >>
  rename1 `phi_single_origin (dfg_build_function func) (EL n eliminated) = SOME origin` >>
  rename1 `origin.inst_outputs = [src_var]` >>
  rename1 `eval_one_phi s (EL n eliminated) = SOME (out, v)` >>
  `lookup_var src_var st_params = lookup_var src_var s` by
    (`lookup_var src_var st = lookup_var src_var s` by
       (qpat_x_assum `!phi origin src_var. _` (qspecl_then [`EL n eliminated`, `origin`, `src_var`] mp_tac) >>
        simp[]) >>
     `lookup_var src_var st_params = lookup_var src_var st` by
       (qspecl_then [`func`, `bb`, `EL n eliminated`, `origin`, `src_var`, `fuel`, `ctx`, `st`, `st_params`]
          mp_tac run_insts_params_preserves_single_origin_source >>
        simp[LET_DEF]) >>
     simp[]) >>
  qexists_tac `out` >> qexists_tac `v` >> simp[] >>
  qspecl_then [`func`, `bb`, `prefix`, `EL n eliminated`, `origin`, `src_var`, `fuel`, `ctx`,
                `s`, `st_params`, `st'`, `out`, `v`]
    mp_tac transform_single_origin_phi_assign_run_insts_after_prefix >>
  simp[LET_DEF]
QED

Triviality transform_eliminated_phi_assign_state_equiv_after_params_prefix:
  !func bb n fuel ctx s s_phi st st_params st' s_ref vars.
    let dfg = dfg_build_function func in
    let eliminated =
      FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) in
    let prefix = TAKE n eliminated in
      phi_elim_safe_fn func /\
      wf_ir_fn func /\
      MEM bb func.fn_blocks /\
      eval_phis s bb.bb_instructions = OK s_phi /\
      n < LENGTH eliminated /\
      (!phi origin src_var.
        MEM phi eliminated /\
        phi_single_origin dfg phi = SOME origin /\
        origin.inst_outputs = [src_var] ==>
        lookup_var src_var st = lookup_var src_var s) /\
      run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) st = OK st_params /\
      run_insts fuel ctx (MAP (transform_inst dfg) prefix) st_params = OK st' /\
      (!out v.
        eval_one_phi s (EL n eliminated) = SOME (out, v) ==>
        out NOTIN vars /\ lookup_var out s_ref = SOME v /\
        state_equiv (out INSERT vars) s_ref st') ==>
      ?out v.
        eval_one_phi s (EL n eliminated) = SOME (out, v) /\
        run_insts fuel ctx (MAP (transform_inst dfg) prefix ++ [transform_inst dfg (EL n eliminated)]) st_params =
          OK (update_var out v st') /\
        state_equiv vars s_ref (update_var out v st')
Proof
  rw[LET_DEF] >>
  qspecl_then [`func`, `bb`, `n`, `EL n (FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
    (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))`,
                `fuel`, `ctx`, `s`, `s_phi`, `st`, `st_params`, `st'`]
    mp_tac transform_eliminated_phi_assign_run_insts_after_params_prefix >>
  simp[LET_DEF] >>
  impl_tac >-
    (rpt conj_tac >> simp[] >>
     rpt strip_tac >>
     qpat_x_assum `!phi origin src_var. _` (qspecl_then [`phi`, `origin`, `src_var`] mp_tac) >>
     simp[]) >>
  strip_tac >>
  qexists_tac `out` >> qexists_tac `v` >> simp[] >>
  first_x_assum (qspecl_then [`out`, `v`] strip_assume_tac) >>
  simp[] >>
  irule state_equiv_update_var_remove >> simp[]
QED

Triviality transform_eliminated_phi_prefix_state_equiv:
  !func bb eliminated n fuel ctx s s_phi st st_params s_ref.
    eliminated =
      FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    MEM bb func.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    n <= LENGTH eliminated /\
    (!phi origin src_var.
      MEM phi eliminated /\
      phi_single_origin (dfg_build_function func) phi = SOME origin /\
      origin.inst_outputs = [src_var] ==>
      lookup_var src_var st = lookup_var src_var s) /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) st = OK st_params /\
    state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))) s_ref st_params /\
    (!k out v.
      k < n /\ eval_one_phi s (EL k eliminated) = SOME (out, v) ==>
      set (FLAT (MAP (\inst. inst.inst_outputs) (DROP k eliminated))) SUBSET
        out INSERT set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated))) /\
      out NOTIN set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated))) /\
      lookup_var out s_ref = SOME v) ==>
    ?st'.
      run_insts fuel ctx (MAP (transform_inst (dfg_build_function func)) (TAKE n eliminated))
        st_params = OK st' /\
      state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) (DROP n eliminated)))) s_ref st'
Proof
  Induct_on `n` >-
    (rw[run_insts_def] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `n <= LENGTH eliminated` by decide_tac >>
  `n < LENGTH eliminated` by decide_tac >>
  `!k out v.
      k < n /\ eval_one_phi s (EL k eliminated) = SOME (out,v) ==>
      set (FLAT (MAP (\inst. inst.inst_outputs) (DROP k eliminated))) SUBSET
        out INSERT set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated))) /\
      out NOTIN set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated))) /\
      lookup_var out s_ref = SOME v` by
    (rpt strip_tac >>
     qpat_x_assum `!k out v. _` (qspecl_then [`k`, `out`, `v`] mp_tac) >>
     impl_tac >- simp[] >> simp[]) >>
  `?st_mid.
      run_insts fuel ctx (MAP (transform_inst (dfg_build_function func)) (TAKE n eliminated))
        st_params = OK st_mid /\
      state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) (DROP n eliminated)))) s_ref st_mid` by
    (qpat_x_assum
       `!func bb eliminated fuel ctx s s_phi st st_params s_ref. _`
       (qspecl_then [`func`, `bb`, `eliminated`, `fuel`, `ctx`,
                     `s`, `s_phi`, `st`, `st_params`, `s_ref`] mp_tac) >>
     impl_tac >-
       (rpt conj_tac >> simp[] >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  qspecl_then [`func`, `bb`, `n`, `fuel`, `ctx`, `s`, `s_phi`, `st`,
                `st_params`, `st_mid`, `s_ref`,
                `set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC n) eliminated)))`]
    mp_tac transform_eliminated_phi_assign_state_equiv_after_params_prefix >>
  simp[LET_DEF] >>
  qpat_x_assum `eliminated = _` (fn th => PURE_REWRITE_TAC[GSYM th]) >>
  impl_tac >-
    (simp[] >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!phi origin src_var. _` (qspecl_then [`phi`, `origin`, `src_var`] mp_tac) >>
        simp[]) >>
     rpt strip_tac >>
     qpat_x_assum `!k out v. k < SUC n /\ _ ==> _` (qspecl_then [`n`, `out`, `v`] mp_tac) >>
     impl_tac >- simp[] >>
     strip_tac >> gvs[] >>
     irule state_equiv_subset >>
     qexists_tac `set (FLAT (MAP (\inst. inst.inst_outputs) (DROP n eliminated)))` >>
     simp[]) >>
  strip_tac >>
  qexists_tac `update_var out v st_mid` >>
  `TAKE (SUC n) eliminated = TAKE n eliminated ++ [EL n eliminated]` by
    simp[GSYM SNOC_APPEND, rich_listTheory.SNOC_EL_TAKE] >>
  simp[MAP_APPEND]
QED

Triviality transform_eliminated_phi_prefix_state_eq_from_facts:
  !func bb eliminated fuel ctx s s_phi st st_params s_ref.
    eliminated =
      FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    MEM bb func.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    (!phi origin src_var.
      MEM phi eliminated /\
      phi_single_origin (dfg_build_function func) phi = SOME origin /\
      origin.inst_outputs = [src_var] ==>
      lookup_var src_var st = lookup_var src_var s) /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) st = OK st_params /\
    state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))) s_ref st_params /\
    (!k out v.
      k < LENGTH eliminated /\ eval_one_phi s (EL k eliminated) = SOME (out, v) ==>
      set (FLAT (MAP (\inst. inst.inst_outputs) (DROP k eliminated))) SUBSET
        out INSERT set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated))) /\
      out NOTIN set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated))) /\
      lookup_var out s_ref = SOME v) ==>
    ?st'.
      run_insts fuel ctx (MAP (transform_inst (dfg_build_function func)) eliminated)
        st_params = OK st' /\
      st' = s_ref
Proof
  rpt strip_tac >>
  qspecl_then [`func`, `bb`, `eliminated`, `LENGTH eliminated`,
                `fuel`, `ctx`, `s`, `s_phi`, `st`, `st_params`, `s_ref`]
    mp_tac transform_eliminated_phi_prefix_state_equiv >>
  impl_tac >-
    (simp[] >>
     conj_tac >-
       (rpt strip_tac >>
        qpat_x_assum `!phi origin src_var. _` (qspecl_then [`phi`, `origin`, `src_var`] mp_tac) >>
        simp[]) >>
     rpt strip_tac >>
     qpat_x_assum `!k out v. _` (qspecl_then [`k`, `out`, `v`] mp_tac) >>
     simp[]) >>
  strip_tac >>
  qexists_tac `st'` >> conj_tac
  >- (qpat_x_assum `run_insts _ _ (MAP _ (TAKE _ _)) _ = OK _` mp_tac >> simp[]) >>
  irule EQ_SYM >> irule state_equiv_empty_eq >>
  qpat_x_assum `state_equiv _ s_ref st'` mp_tac >> simp[]
QED

Triviality eval_phis_kept_preserves_eliminated_source_lookup:
  !func bb kept eliminated s s_phi s_kept phi origin src_var.
    kept = FILTER (\inst. inst.inst_opcode = PHI /\
                   phi_single_origin (dfg_build_function func) inst = NONE)
             bb.bb_instructions /\
    eliminated = FILTER (\inst. ?origin.
                   phi_single_origin (dfg_build_function func) inst = SOME origin)
             (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    phi_elim_safe_fn func /\
    MEM bb func.fn_blocks /\
    eval_phis s kept = OK s_kept /\
    MEM phi eliminated /\
    phi_single_origin (dfg_build_function func) phi = SOME origin /\
    origin.inst_outputs = [src_var] ==>
    lookup_var src_var s_kept = lookup_var src_var s
Proof
  rw[lookup_var_def] >>
  qspecl_then [`s`,
    `FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin (dfg_build_function func) inst = NONE)
       bb.bb_instructions`,
    `src_var`, `s_kept`] mp_tac eval_phis_flookup_not_phi_output >>
  simp[] >>
  impl_tac >-
    (rw[MEM_FILTER] >>
     `MEM phi bb.bb_instructions` by
       (qpat_x_assum `MEM phi (FILTER _ _)` mp_tac >>
        simp[MEM_FILTER] >> metis_tac[rich_listTheory.MEM_TAKE]) >>
     qspecl_then [`func`, `bb`, `phi`, `origin`, `src_var`, `inst`]
       mp_tac phi_elim_safe_fn_source_not_output >>
     simp[]) >>
  disch_then ACCEPT_TAC
QED

Triviality transform_eliminated_phi_prefix_after_kept_params_state_eq:
  !func bb kept eliminated fuel ctx s s_phi s_kept s_params t_params.
    kept = FILTER (\inst. inst.inst_opcode = PHI /\
                   phi_single_origin (dfg_build_function func) inst = NONE)
             bb.bb_instructions /\
    eliminated =
      FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    MEM bb func.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    eval_phis s kept = OK s_kept /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_phi = OK s_params /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK t_params /\
    state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))) s_params t_params ==>
    ?t_elim.
      run_insts fuel ctx (MAP (transform_inst (dfg_build_function func)) eliminated)
        t_params = OK t_elim /\
      t_elim = s_params
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) eliminated))` by
    (qspecl_then [`func`, `bb`, `eliminated`] mp_tac eliminated_outputs_distinct >>
     simp[]) >>
  qspecl_then [`func`, `bb`, `eliminated`, `fuel`, `ctx`, `s`, `s_phi`,
                `s_kept`, `t_params`, `s_params`]
    mp_tac transform_eliminated_phi_prefix_state_eq_from_facts >>
  simp[] >>
  impl_tac >-
    (conj_tac >-
       (rpt strip_tac >>
        qspecl_then [`func`, `bb`, `kept`, `eliminated`, `s`, `s_phi`, `s_kept`,
                      `phi`, `origin`, `src_var`]
          mp_tac eval_phis_kept_preserves_eliminated_source_lookup >>
        simp[]) >>
     rpt strip_tac >>
     `set (FLAT (MAP (\inst. inst.inst_outputs) (DROP k eliminated))) SUBSET
        out INSERT set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated))) /\
      out NOTIN set (FLAT (MAP (\inst. inst.inst_outputs) (DROP (SUC k) eliminated)))` by
       (qspecl_then [`eliminated`, `k`, `out`, `v`, `s`] mp_tac eliminated_output_drop_facts >>
        simp[]) >>
     `lookup_var out s_params = SOME v` by
       (qspecl_then [`func`, `bb`, `eliminated`, `k`, `out`, `v`,
                     `fuel`, `ctx`, `s`, `s_phi`, `s_params`]
          mp_tac run_insts_params_preserves_eliminated_eval >>
        simp[]) >>
     qpat_x_assum `eliminated = _` SUBST_ALL_TAC >>
     gvs[]) >>
  disch_then ACCEPT_TAC
QED

Triviality transform_eliminated_phi_prefix_run_insts_ok:
  !func bb eliminated n fuel ctx s s_phi st st_params.
    eliminated =
      FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    MEM bb func.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    n <= LENGTH eliminated /\
    (!phi origin src_var.
      MEM phi eliminated /\
      phi_single_origin (dfg_build_function func) phi = SOME origin /\
      origin.inst_outputs = [src_var] ==>
      lookup_var src_var st = lookup_var src_var s) /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) st = OK st_params ==>
    ?st'. run_insts fuel ctx
      (MAP (transform_inst (dfg_build_function func)) (TAKE n eliminated)) st_params = OK st'
Proof
  Induct_on `n` >- rw[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  `n <= LENGTH eliminated` by decide_tac >>
  `n < LENGTH eliminated` by decide_tac >>
  `?st_mid. run_insts fuel ctx
      (MAP (transform_inst (dfg_build_function func)) (TAKE n eliminated)) st_params = OK st_mid` by
    (first_x_assum (qspecl_then [`func`, `bb`, `eliminated`, `fuel`, `ctx`, `s`, `s_phi`, `st`, `st_params`] mp_tac) >>
     impl_tac >-
       (rpt conj_tac >> simp[] >>
        rpt strip_tac >>
        qpat_x_assum `!phi origin src_var. _` (qspecl_then [`phi`, `origin`, `src_var`] mp_tac) >>
        simp[]) >>
     disch_then ACCEPT_TAC) >>
  qspecl_then [`func`, `bb`, `n`, `EL n eliminated`, `fuel`, `ctx`, `s`, `s_phi`,
                `st`, `st_params`, `st_mid`]
    mp_tac transform_eliminated_phi_assign_run_insts_after_params_prefix >>
  simp[LET_DEF] >>
  qpat_x_assum `eliminated = _` (fn th => PURE_REWRITE_TAC[GSYM th]) >>
  impl_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!phi origin src_var. _` (qspecl_then [`phi`, `origin`, `src_var`] mp_tac) >>
     simp[]) >>
  strip_tac >>
  qexists_tac `update_var out v st_mid` >>
  `TAKE (SUC n) eliminated = TAKE n eliminated ++ [EL n eliminated]` by
    simp[GSYM SNOC_APPEND, rich_listTheory.SNOC_EL_TAKE] >>
  simp[MAP_APPEND]
QED

Triviality transform_eliminated_phi_prefix_after_kept_params_ok:
  !func bb kept eliminated n fuel ctx s s_phi s_kept st_params.
    kept = FILTER (\inst. inst.inst_opcode = PHI /\
                   phi_single_origin (dfg_build_function func) inst = NONE)
             bb.bb_instructions /\
    eliminated =
      FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    MEM bb func.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    eval_phis s kept = OK s_kept /\
    n <= LENGTH eliminated /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK st_params ==>
    ?st'. run_insts fuel ctx
      (MAP (transform_inst (dfg_build_function func)) (TAKE n eliminated)) st_params = OK st'
Proof
  rpt strip_tac >>
  qspecl_then [`func`, `bb`, `eliminated`, `n`, `fuel`, `ctx`, `s`, `s_phi`, `s_kept`, `st_params`]
    mp_tac transform_eliminated_phi_prefix_run_insts_ok >>
  simp[] >>
  impl_tac >-
    (rpt strip_tac >>
     qspecl_then [`func`, `bb`, `kept`, `eliminated`, `s`, `s_phi`, `s_kept`,
                   `phi`, `origin`, `src_var`]
       mp_tac eval_phis_kept_preserves_eliminated_source_lookup >>
     simp[]) >>
  disch_then ACCEPT_TAC
QED

Triviality transform_block_prefix_ok_from_original_params_ok:
  !func bb kept eliminated fuel ctx s s_phi s_params.
    let dfg = dfg_build_function func in
      kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE)
        bb.bb_instructions /\
      eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
      phi_elim_safe_fn func /\
      wf_ir_fn func /\
      bb_well_formed bb /\
      MEM bb func.fn_blocks /\
      eval_phis s bb.bb_instructions = OK s_phi /\
      run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_phi = OK s_params ==>
      ?s_kept t_params t_elim.
        eval_phis s (transform_insts dfg bb.bb_instructions) = OK s_kept /\
        run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK t_params /\
        run_insts fuel ctx (MAP (transform_inst dfg) eliminated) t_params = OK t_elim
Proof
  rw[LET_DEF] >>
  Cases_on `bb` >> gvs[] >>
  rename1 `basic_block lbl insts` >>
  qabbrev_tac `dfg = dfg_build_function func` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  `bb_well_formed <|bb_label := lbl; bb_instructions := insts|>` by
    (`<|bb_label := lbl; bb_instructions := insts|> = basic_block lbl insts` by
       simp[venomInstTheory.basic_block_component_equality] >>
     simp[]) >>
  `TAKE (phi_prefix_length insts) insts = FILTER (\inst. inst.inst_opcode = PHI) insts` by
    (`TAKE (LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)) insts =
      FILTER (\inst. inst.inst_opcode = PHI) insts` by
        (qspecl_then [`insts`, `lbl`] mp_tac phi_prefix_take_filter >> simp[]) >>
     `phi_prefix_length insts = LENGTH (FILTER (\inst. inst.inst_opcode = PHI) insts)` by
        (qspecl_then [`insts`, `lbl`] mp_tac phi_prefix_length_filter_phi >> simp[]) >>
     simp[]) >>
  `?s_kept. eval_phis s kept = OK s_kept` by
    (qspecl_then [`kept`, `s`, `insts`, `s_phi`] mp_tac eval_phis_ok_phi_prefix_sublist >>
     simp[] >>
     impl_tac >-
       (gvs[Abbr `kept`, EVERY_MEM, MEM_FILTER] >> metis_tac[]) >>
     disch_then ACCEPT_TAC) >>
  `eval_phis s (transform_insts dfg insts) = OK s_kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `?t_params. run_insts fuel ctx params s_kept = OK t_params` by
    (qspecl_then [`params`, `fuel`, `ctx`, `s`, `insts`, `s_phi`,
                  `kept`, `s_kept`, `s_params`]
       mp_tac run_insts_params_ok_after_eval_phis >>
     simp[Abbr `params`, EVERY_MEM, MEM_FILTER]) >>
  `?t_elim. run_insts fuel ctx (MAP (transform_inst dfg) eliminated) t_params = OK t_elim` by
    (qspecl_then [`func`, `basic_block lbl insts`, `kept`, `eliminated`, `LENGTH eliminated`,
                  `fuel`, `ctx`, `s`, `s_phi`, `s_kept`, `t_params`]
       mp_tac transform_eliminated_phi_prefix_after_kept_params_ok >>
     simp[LET_DEF, Abbr `dfg`, Abbr `kept`, Abbr `eliminated`]) >>
  qexists_tac `s_kept` >> qexists_tac `t_params` >> qexists_tac `t_elim` >>
  simp[Abbr `params`, Abbr `eliminated`]
QED

Triviality transform_block_prefix_state_eq_from_original_params_ok:
  !func bb fuel ctx s s_phi s_params.
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    bb_well_formed bb /\
    pseudos_prefix bb /\
    MEM bb func.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_phi = OK s_params ==>
    ?s_kept t_params.
      eval_phis s (transform_block (dfg_build_function func) bb).bb_instructions = OK s_kept /\
      run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK t_params /\
      run_insts fuel ctx
        (MAP (transform_inst (dfg_build_function func))
          (FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
            (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))) t_params = OK s_params /\
      exec_block fuel ctx bb
        (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
      exec_block fuel ctx (transform_block (dfg_build_function func) bb)
        (s_kept with vs_inst_idx := phi_prefix_length (transform_block (dfg_build_function func) bb).bb_instructions)
Proof
  rpt strip_tac >>
  Cases_on `bb` >> gvs[transform_block_def] >>
  rename1 `basic_block lbl insts` >>
  qabbrev_tac `dfg = dfg_build_function func` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  `bb_well_formed <|bb_label := lbl; bb_instructions := insts|>` by
    (`<|bb_label := lbl; bb_instructions := insts|> = basic_block lbl insts` by
       simp[venomInstTheory.basic_block_component_equality] >> simp[]) >>
  `pseudos_prefix <|bb_label := lbl; bb_instructions := insts|>` by
    (`<|bb_label := lbl; bb_instructions := insts|> = basic_block lbl insts` by
       simp[venomInstTheory.basic_block_component_equality] >> simp[]) >>
  `?s_kept. eval_phis s kept = OK s_kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`, `kept`, `s`, `s_phi`]
       mp_tac eval_phis_kept_ok_from_original >>
     simp[Abbr `kept`, Abbr `dfg`]) >>
  `eval_phis s (transform_insts dfg insts) = OK s_kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))) s_phi s_kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`, `kept`, `eliminated`, `s`, `s_phi`, `s_kept`]
       mp_tac eval_phis_original_kept_state_equiv >>
     simp[Abbr `kept`, Abbr `eliminated`]) >>
  `?t_params. run_insts fuel ctx params s_kept = OK t_params /\
              state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))) s_params t_params` by
    (qspecl_then [`params`, `fuel`, `ctx`,
                  `set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))`,
                  `s_phi`, `s_params`, `s_kept`]
       mp_tac run_insts_params_state_equiv >>
     simp[Abbr `params`, EVERY_MEM, MEM_FILTER]) >>
  `?t_elim. run_insts fuel ctx (MAP (transform_inst dfg) eliminated) t_params = OK t_elim /\
            t_elim = s_params` by
    (qspecl_then [`func`, `basic_block lbl insts`, `kept`, `eliminated`,
                  `fuel`, `ctx`, `s`, `s_phi`, `s_kept`, `s_params`, `t_params`]
       mp_tac transform_eliminated_phi_prefix_after_kept_params_state_eq >>
     simp[Abbr `dfg`, Abbr `kept`, Abbr `eliminated`, Abbr `params`]) >>
  qexists_tac `s_kept` >> qexists_tac `t_params` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `t_elim = s_params` (fn th => rewrite_tac[GSYM th]) >>
                first_assum ACCEPT_TAC) >>
  `basic_block lbl insts = <|bb_label := lbl; bb_instructions := insts|>` by
    simp[venomInstTheory.basic_block_component_equality] >>
  `basic_block lbl insts with bb_instructions := transform_insts dfg insts =
   <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>` by
    simp[venomInstTheory.basic_block_component_equality] >>
  asm_rewrite_tac[] >>
  irule exec_block_after_transform_prefix_state_eq >>
  simp[Abbr `params`, Abbr `eliminated`]
QED

Triviality transform_single_origin_phi_assign_run_insts_error:
  !dfg inst origin src_var fuel ctx s.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    lookup_var src_var s = NONE ==>
    ?e. run_insts fuel ctx [transform_inst dfg inst] s = Error e
Proof
  rpt strip_tac >>
  fs[transform_inst_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[run_insts_def, step_inst_def, step_inst_base_def, eval_operand_def] >>
  Cases_on `t` >>
  simp[run_insts_def, step_inst_def, step_inst_base_def, eval_operand_def]
QED

Triviality eliminated_phi_static_info:
  !func bb eliminated k.
    let dfg = dfg_build_function func in
      eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
      wf_ir_fn func /\
      MEM bb func.fn_blocks /\
      k < LENGTH eliminated ==>
      ?origin src_var.
        MEM (EL k eliminated) bb.bb_instructions /\
        phi_single_origin dfg (EL k eliminated) = SOME origin /\
        origin.inst_outputs = [src_var] /\
        phi_well_formed (EL k eliminated).inst_operands /\
        phi_operands_direct dfg (EL k eliminated)
Proof
  rpt gen_tac >> simp[LET_DEF] >> strip_tac >>
  qabbrev_tac `inst = EL k eliminated` >>
  `MEM inst eliminated` by simp[Abbr `inst`, EL_MEM] >>
  `MEM inst (FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
      (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))` by
    (qpat_x_assum `eliminated = _` (fn th => rewrite_tac[GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  gvs[MEM_FILTER] >>
  rename1 `phi_single_origin (dfg_build_function func) inst = SOME origin` >>
  `MEM inst bb.bb_instructions` by metis_tac[rich_listTheory.MEM_TAKE] >>
  `?idx. get_instruction bb idx = SOME inst` by metis_tac[mem_get_instruction] >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  `phi_well_formed inst.inst_operands` by metis_tac[wf_ir_fn_def] >>
  `phi_operands_direct (dfg_build_function func) inst` by
    (fs[wf_ir_fn_def, LET_DEF] >> metis_tac[]) >>
  `?src_var. origin.inst_outputs = [src_var]` by metis_tac[phi_single_origin_has_output] >>
  qexists_tac `src_var` >>
  simp[Abbr `inst`]
QED

Triviality transform_eliminated_phi_assign_run_insts_after_params_prefix_from_eval:
  !func bb kept eliminated n fuel ctx s s_kept st_params st'.
    let dfg = dfg_build_function func in
    let prefix = TAKE n eliminated in
      kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE)
        bb.bb_instructions /\
      eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
      phi_elim_safe_fn func /\
      wf_ir_fn func /\
      MEM bb func.fn_blocks /\
      eval_phis s kept = OK s_kept /\
      n < LENGTH eliminated /\
      (?out v. eval_one_phi s (EL n eliminated) = SOME (out, v)) /\
      run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK st_params /\
      run_insts fuel ctx (MAP (transform_inst dfg) prefix) st_params = OK st' ==>
      ?out v.
        eval_one_phi s (EL n eliminated) = SOME (out, v) /\
        run_insts fuel ctx (MAP (transform_inst dfg) prefix ++
          [transform_inst dfg (EL n eliminated)]) st_params = OK (update_var out v st')
Proof
  rpt gen_tac >> simp[LET_DEF] >> strip_tac >>
  qabbrev_tac `dfg = dfg_build_function func` >>
  qabbrev_tac `prefix = TAKE n eliminated` >>
  qspecl_then [`func`, `bb`, `eliminated`, `n`] mp_tac eliminated_phi_static_info >>
  PURE_REWRITE_TAC[LET_DEF] >> BETA_TAC >>
  impl_tac >- simp[Abbr `dfg`] >>
  strip_tac >>
  `lookup_var src_var s_kept = lookup_var src_var s` by
    (qspecl_then [`func`, `bb`, `kept`, `eliminated`, `s`, `s_kept`, `s_kept`,
                  `EL n eliminated`, `origin`, `src_var`]
       mp_tac eval_phis_kept_preserves_eliminated_source_lookup >>
     simp[Abbr `dfg`, EL_MEM]) >>
  `lookup_var src_var st_params = lookup_var src_var s_kept` by
    (qspecl_then [`func`, `bb`, `EL n eliminated`, `origin`, `src_var`,
                  `fuel`, `ctx`, `s_kept`, `st_params`]
       mp_tac run_insts_params_preserves_single_origin_source >>
     simp[LET_DEF, Abbr `dfg`]) >>
  qexists_tac `out` >> qexists_tac `v` >> simp[] >>
  qspecl_then [`func`, `bb`, `prefix`, `EL n eliminated`, `origin`, `src_var`,
                `fuel`, `ctx`, `s`, `st_params`, `st'`, `out`, `v`]
    mp_tac transform_single_origin_phi_assign_run_insts_after_prefix >>
  PURE_REWRITE_TAC[LET_DEF] >> BETA_TAC >>
  impl_tac >-
    (simp[Abbr `dfg`, Abbr `prefix`, eliminated_phi_prefix_every_for_block]) >>
  strip_tac >>
  simp[Abbr `dfg`, Abbr `prefix`] >>
  qpat_x_assum `eliminated = FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin) _`
    (fn th => rewrite_tac[GSYM th]) >>
  simp[]
QED

Triviality transform_eliminated_phi_prefix_run_insts_ok_from_eval_prefix:
  !func bb kept eliminated n fuel ctx s s_kept st_params.
    kept = FILTER (\inst. inst.inst_opcode = PHI /\
                   phi_single_origin (dfg_build_function func) inst = NONE)
             bb.bb_instructions /\
    eliminated = FILTER (\inst. ?origin.
                   phi_single_origin (dfg_build_function func) inst = SOME origin)
             (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    MEM bb func.fn_blocks /\
    eval_phis s kept = OK s_kept /\
    n <= LENGTH eliminated /\
    (!j. j < n ==> ?out v. eval_one_phi s (EL j eliminated) = SOME (out, v)) /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK st_params ==>
    ?st'. run_insts fuel ctx
      (MAP (transform_inst (dfg_build_function func)) (TAKE n eliminated)) st_params = OK st'
Proof
  Induct_on `n` >- rw[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  `n <= LENGTH eliminated` by decide_tac >>
  `n < LENGTH eliminated` by decide_tac >>
  `?st_mid. run_insts fuel ctx
      (MAP (transform_inst (dfg_build_function func)) (TAKE n eliminated)) st_params = OK st_mid` by
    (first_x_assum (qspecl_then [`func`, `bb`, `kept`, `eliminated`, `fuel`, `ctx`,
                                  `s`, `s_kept`, `st_params`] mp_tac) >>
     impl_tac >-
       (rpt conj_tac >> simp[] >>
        rpt strip_tac >> qpat_x_assum `!j. j < SUC n ==> _` (qspec_then `j` mp_tac) >>
        simp[]) >>
     disch_then ACCEPT_TAC) >>
  qspecl_then [`func`, `bb`, `kept`, `eliminated`, `n`, `fuel`, `ctx`,
                `s`, `s_kept`, `st_params`, `st_mid`]
    mp_tac transform_eliminated_phi_assign_run_insts_after_params_prefix_from_eval >>
  PURE_REWRITE_TAC[LET_DEF] >> BETA_TAC >>
  impl_tac >-
    (rpt conj_tac >> simp[] >>
     qpat_x_assum `!j. j < SUC n ==> _` (qspec_then `n` mp_tac) >> simp[]) >>
  strip_tac >>
  qexists_tac `update_var out v st_mid` >>
  `TAKE (SUC n) eliminated = TAKE n eliminated ++ [EL n eliminated]` by
    simp[GSYM SNOC_APPEND, rich_listTheory.SNOC_EL_TAKE] >>
  simp[MAP_APPEND] >>
  qpat_x_assum `eliminated = FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin) _`
    (fn th => rewrite_tac[GSYM th]) >>
  first_assum ACCEPT_TAC
QED

Triviality transform_eliminated_phi_prefix_run_insts_error_from_eval:
  !func bb kept eliminated k fuel ctx s s_kept st_params.
    kept = FILTER (\inst. inst.inst_opcode = PHI /\
                   phi_single_origin (dfg_build_function func) inst = NONE)
             bb.bb_instructions /\
    eliminated = FILTER (\inst. ?origin.
                   phi_single_origin (dfg_build_function func) inst = SOME origin)
             (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    MEM bb func.fn_blocks /\
    s.vs_prev_bb <> NONE /\
    eval_phis s kept = OK s_kept /\
    k < LENGTH eliminated /\
    eval_one_phi s (EL k eliminated) = NONE /\
    (!j. j < k ==> ?out v. eval_one_phi s (EL j eliminated) = SOME (out, v)) /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK st_params ==>
    ?e. run_insts fuel ctx
      (MAP (transform_inst (dfg_build_function func)) (TAKE (SUC k) eliminated)) st_params = Error e
Proof
  rpt strip_tac >>
  `k <= LENGTH eliminated` by decide_tac >>
  `?st_mid. run_insts fuel ctx
      (MAP (transform_inst (dfg_build_function func)) (TAKE k eliminated)) st_params = OK st_mid` by
    (qspecl_then [`func`, `bb`, `kept`, `eliminated`, `k`, `fuel`, `ctx`,
                  `s`, `s_kept`, `st_params`]
       mp_tac transform_eliminated_phi_prefix_run_insts_ok_from_eval_prefix >>
     simp[]) >>
  qspecl_then [`func`, `bb`, `eliminated`, `k`] mp_tac eliminated_phi_static_info >>
  PURE_REWRITE_TAC[LET_DEF] >> BETA_TAC >>
  impl_tac >- simp[] >>
  strip_tac >>
  rename1 `phi_single_origin (dfg_build_function func) (EL k eliminated) = SOME origin` >>
  rename1 `origin.inst_outputs = [src_var]` >>
  `lookup_var src_var s = NONE` by
    (qspecl_then [`func`, `bb`, `eliminated`, `k`, `s`, `origin`, `src_var`]
       mp_tac eliminated_phi_eval_one_none_source_lookup >>
     simp[]) >>
  `lookup_var src_var s_kept = lookup_var src_var s` by
    (qspecl_then [`func`, `bb`, `kept`, `eliminated`, `s`, `s_kept`, `s_kept`,
                  `EL k eliminated`, `origin`, `src_var`]
       mp_tac eval_phis_kept_preserves_eliminated_source_lookup >>
     simp[EL_MEM]) >>
  `lookup_var src_var st_mid = lookup_var src_var s_kept` by
    (qspecl_then [`func`, `bb`, `EL k eliminated`, `origin`, `src_var`, `k`,
                  `fuel`, `ctx`, `s_kept`, `st_params`, `st_mid`]
       mp_tac run_insts_params_and_eliminated_prefix_preserves_single_origin_source >>
     PURE_REWRITE_TAC[LET_DEF] >> BETA_TAC >>
     impl_tac >-
       (simp[EL_MEM] >>
        qpat_x_assum `eliminated = FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin) _`
          (fn th => rewrite_tac[GSYM th]) >>
        simp[]) >>
     disch_then ACCEPT_TAC) >>
  `?e. run_insts fuel ctx [transform_inst (dfg_build_function func) (EL k eliminated)] st_mid = Error e` by
    (qspecl_then [`dfg_build_function func`, `EL k eliminated`, `origin`, `src_var`,
                  `fuel`, `ctx`, `st_mid`]
       mp_tac transform_single_origin_phi_assign_run_insts_error >>
     simp[]) >>
  qexists_tac `e` >>
  `TAKE (SUC k) eliminated = TAKE k eliminated ++ [EL k eliminated]` by
    simp[GSYM SNOC_APPEND, rich_listTheory.SNOC_EL_TAKE] >>
  qpat_x_assum `eliminated = FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin) _`
    (fn th => rewrite_tac[GSYM th]) >>
  simp[MAP_APPEND, run_insts_append]
QED

Triviality exec_block_transformed_eliminated_error:
  !dfg insts lbl fuel ctx s e.
    let kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts in
    let params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts in
    let eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
          (TAKE (phi_prefix_length insts) insts) in
      bb_well_formed <| bb_label := lbl; bb_instructions := insts |> /\
      run_insts fuel ctx (MAP (transform_inst dfg) eliminated) s = Error e ==>
      exec_block fuel ctx <| bb_label := lbl; bb_instructions := transform_insts dfg insts |>
        (s with vs_inst_idx := LENGTH kept + LENGTH params) = Error e
Proof
  rpt gen_tac >> simp[LET_DEF] >> strip_tac >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  qabbrev_tac `elim = MAP (transform_inst dfg) eliminated` >>
  qabbrev_tac `tail = FILTER (\inst. ~is_pseudo inst.inst_opcode /\ ~is_terminator inst.inst_opcode)
        (MAP (transform_inst dfg) (DROP (phi_prefix_length insts) insts)) ++
      FILTER (\inst. is_terminator inst.inst_opcode) (MAP (transform_inst dfg) insts)` >>
  `transform_insts dfg insts = kept ++ params ++ elim ++ tail` by
    (qunabbrev_tac `tail` >> qunabbrev_tac `elim` >> qunabbrev_tac `eliminated` >>
     qunabbrev_tac `kept` >> qunabbrev_tac `params` >>
     qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_decompose_phi_prefix >>
     simp[APPEND_ASSOC]) >>
  `LENGTH kept + LENGTH params + LENGTH elim <= LENGTH (transform_insts dfg insts)` by
    (qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >> simp[]) >>
  `!k. k < LENGTH elim ==>
       EL (LENGTH kept + LENGTH params + k) (transform_insts dfg insts) = EL k elim` by
    (rpt strip_tac >>
     qpat_x_assum `transform_insts dfg insts = _` (fn th => rewrite_tac[th]) >>
     simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_APPEND2]) >>
  qspecl_then [`elim`, `fuel`, `ctx`, `<| bb_label := lbl; bb_instructions := transform_insts dfg insts |>`,
                `s`, `LENGTH kept + LENGTH params`, `e`] mp_tac exec_block_prefix_error >>
  impl_tac >-
    (simp[Abbr `elim`, Abbr `eliminated`, transformed_eliminated_phis_nonterm_noninvoke] >>
     rpt strip_tac >>
     qpat_x_assum `!k. k < LENGTH elim ==> _` (qspec_then `k` mp_tac) >>
     simp[]) >>
  simp[Abbr `elim`, Abbr `eliminated`]
QED

Triviality transform_single_origin_phi_assign_run_insts:
  !dfg inst origin src_var fuel ctx s out v.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    phi_well_formed inst.inst_operands /\
    phi_operands_direct dfg inst /\
    eval_one_phi s inst = SOME (out, v) ==>
    run_insts fuel ctx [transform_inst dfg inst] s = OK (update_var out v s)
Proof
  rpt strip_tac >>
  drule_all transform_single_origin_phi_assign_step >> strip_tac >>
  `~((transform_inst dfg inst).inst_opcode = INVOKE)` by
    (fs[transform_inst_def] >>
     Cases_on `phi_single_origin dfg inst` >> fs[] >>
     Cases_on `x.inst_outputs` >> fs[] >>
     Cases_on `t` >> fs[]) >>
  simp[run_insts_def, step_inst_def]
QED

Triviality eval_phis_single:
  !s inst out v.
    inst.inst_opcode = PHI /\
    eval_one_phi s inst = SOME (out, v) ==>
    eval_phis s [inst] = OK (update_var out v s)
Proof
  rw[eval_phis_def]
QED

Triviality transform_single_origin_phi_run_insts_eval_phis_single:
  !dfg inst origin src_var fuel ctx s out v.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    phi_well_formed inst.inst_operands /\
    phi_operands_direct dfg inst /\
    eval_one_phi s inst = SOME (out, v) ==>
    run_insts fuel ctx [transform_inst dfg inst] s = eval_phis s [inst]
Proof
  rpt strip_tac >>
  drule_all transform_single_origin_phi_assign_run_insts >> strip_tac >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  `eval_phis s [inst] = OK (update_var out v s)` by
    (irule eval_phis_single >> fs[is_phi_inst_def]) >>
  simp[]
QED

Triviality phi_elim_run_block_exec_error:
  !func bb fuel ctx s s_phi e.
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    bb_well_formed bb /\
    pseudos_prefix bb /\
    MEM bb func.fn_blocks /\
    eval_phis s bb.bb_instructions = OK s_phi /\
    exec_block fuel ctx bb
      (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Error e ==>
    ?e'. run_block fuel ctx (transform_block (dfg_build_function func) bb) s = Error e'
Proof
  rpt strip_tac >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions` >>
  `EVERY (\inst. is_param_opcode inst.inst_opcode) params` by
    simp[Abbr `params`, EVERY_MEM, MEM_FILTER] >>
  `(?s_params. run_insts fuel ctx params s_phi = OK s_params) \/
   (?ep. run_insts fuel ctx params s_phi = Error ep)` by
    (qspecl_then [`params`, `fuel`, `ctx`, `s_phi`] mp_tac run_insts_params_ok_or_error >>
     simp[]) >>
  Cases_on `run_insts fuel ctx params s_phi` >> gvs[]
  >- (rename1 `run_insts _ _ _ _ = OK s_params` >>
      `?s_kept t_params.
          eval_phis s (transform_block (dfg_build_function func) bb).bb_instructions = OK s_kept /\
          run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK t_params /\
          run_insts fuel ctx
            (MAP (transform_inst (dfg_build_function func))
              (FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
                (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))) t_params = OK s_params /\
          exec_block fuel ctx bb
            (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
          exec_block fuel ctx (transform_block (dfg_build_function func) bb)
            (s_kept with vs_inst_idx := phi_prefix_length (transform_block (dfg_build_function func) bb).bb_instructions)` by
        (qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `s_phi`, `s_params`]
           mp_tac transform_block_prefix_state_eq_from_original_params_ok >>
         simp[Abbr `params`]) >>
      qexists_tac `e` >>
      ONCE_REWRITE_TAC[run_block_def] >> simp[] >> gvs[])
  >- (rename1 `run_insts _ _ _ _ = Error ep` >>
      Cases_on `bb` >> gvs[transform_block_def] >>
      rename1 `basic_block lbl insts` >>
      qabbrev_tac `dfg = dfg_build_function func` >>
      qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
      qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
        (TAKE (phi_prefix_length insts) insts)` >>
      `bb_well_formed <|bb_label := lbl; bb_instructions := insts|>` by
        (`<|bb_label := lbl; bb_instructions := insts|> = basic_block lbl insts` by
           simp[venomInstTheory.basic_block_component_equality] >> simp[]) >>
      `?s_kept. eval_phis s kept = OK s_kept` by
        (qspecl_then [`dfg`, `insts`, `lbl`, `kept`, `s`, `s_phi`]
           mp_tac eval_phis_kept_ok_from_original >>
         simp[Abbr `kept`, Abbr `dfg`]) >>
      `eval_phis s (transform_insts dfg insts) = OK s_kept` by
        (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
         simp[LET_DEF, Abbr `kept`]) >>
      `state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))) s_phi s_kept` by
        (qspecl_then [`dfg`, `insts`, `lbl`, `kept`, `eliminated`, `s`, `s_phi`, `s_kept`]
           mp_tac eval_phis_original_kept_state_equiv >>
         simp[Abbr `kept`, Abbr `eliminated`]) >>
      `lift_result (state_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))))
           (execution_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))))
           (execution_equiv (set (FLAT (MAP (\inst. inst.inst_outputs) eliminated))))
           (run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s_phi)
           (run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s_kept)` by
        (irule run_insts_params_lift_result >> simp[EVERY_MEM, MEM_FILTER]) >>
      `?ep2. run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s_kept = Error ep2` by
        (Cases_on `run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s_kept` >>
         gvs[lift_result_def]) >>
      `basic_block lbl insts with bb_instructions := transform_insts dfg insts =
       <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>` by
        simp[venomInstTheory.basic_block_component_equality] >>
      qexists_tac `ep2` >>
      ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
      qspecl_then [`dfg`, `insts`, `lbl`, `fuel`, `ctx`, `s_kept`, `ep2`]
        mp_tac exec_block_transformed_params_error >>
      asm_rewrite_tac[] >> simp[Abbr `dfg`])
QED

Triviality phi_elim_run_block_eval_error_params_ok:
  !func lbl insts fuel ctx s e s_kept t_params.
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    bb_well_formed (basic_block lbl insts) /\
    pseudos_prefix (basic_block lbl insts) /\
    MEM (basic_block lbl insts) func.fn_blocks /\
    s.vs_prev_bb <> NONE /\
    eval_phis s insts = Error e /\
    eval_phis s
      (FILTER (\inst. inst.inst_opcode = PHI /\
                      phi_single_origin (dfg_build_function func) inst = NONE) insts) = OK s_kept /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s_kept = OK t_params ==>
    ?e'. run_block fuel ctx
      (basic_block lbl insts with bb_instructions := transform_insts (dfg_build_function func) insts) s = Error e'
Proof
  rpt strip_tac >>
  qabbrev_tac `dfg = dfg_build_function func` >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  `bb_well_formed <|bb_label := lbl; bb_instructions := insts|>` by
    (`<|bb_label := lbl; bb_instructions := insts|> = basic_block lbl insts` by
       simp[venomInstTheory.basic_block_component_equality] >> simp[]) >>
  `eval_phis s kept = OK s_kept` by simp[Abbr `kept`, Abbr `dfg`] >>
  `eval_phis s (transform_insts dfg insts) = OK s_kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `?k.
     k < LENGTH eliminated /\
     eval_one_phi s (EL k eliminated) = NONE /\
     !j. j < k ==> ?out v. eval_one_phi s (EL j eliminated) = SOME (out, v)` by
    (qspecl_then [`dfg`, `insts`, `lbl`, `kept`, `eliminated`, `s`, `e`, `s_kept`]
       mp_tac eval_phis_original_error_eliminated_index >>
     simp[Abbr `dfg`, Abbr `kept`, Abbr `eliminated`]) >>
  `?eprefix. run_insts fuel ctx (MAP (transform_inst dfg) (TAKE (SUC k) eliminated))
               t_params = Error eprefix` by
    (qspecl_then [`func`, `basic_block lbl insts`, `kept`, `eliminated`, `k`,
                  `fuel`, `ctx`, `s`, `s_kept`, `t_params`]
       mp_tac transform_eliminated_phi_prefix_run_insts_error_from_eval >>
     simp[Abbr `dfg`, Abbr `kept`, Abbr `eliminated`, Abbr `params`]) >>
  `run_insts fuel ctx (MAP (transform_inst dfg) eliminated) t_params = Error eprefix` by
    (`eliminated = TAKE (SUC k) eliminated ++ DROP (SUC k) eliminated` by simp[TAKE_DROP] >>
     pop_assum SUBST1_TAC >>
     simp[MAP_APPEND] >>
     CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_insts_append])) >>
     simp[]) >>
  `phi_prefix_length (transform_insts dfg insts) = LENGTH kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
     (s_kept with vs_inst_idx := phi_prefix_length (transform_insts dfg insts)) =
   exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
     (t_params with vs_inst_idx := LENGTH kept + LENGTH params)` by
    (asm_rewrite_tac[] >>
     qspecl_then [`dfg`, `insts`, `lbl`, `fuel`, `ctx`, `s_kept`, `t_params`]
       mp_tac exec_block_skip_transformed_params >>
     simp[Abbr `kept`, Abbr `params`]) >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
     (t_params with vs_inst_idx := LENGTH kept + LENGTH params) = Error eprefix` by
    (qspecl_then [`dfg`, `insts`, `lbl`, `fuel`, `ctx`, `t_params`, `eprefix`]
       mp_tac exec_block_transformed_eliminated_error >>
     simp[LET_DEF, Abbr `kept`, Abbr `params`, Abbr `eliminated`]) >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
     (s_kept with vs_inst_idx := phi_prefix_length (transform_insts dfg insts)) = Error eprefix` by
    (asm_rewrite_tac[]) >>
  qexists_tac `eprefix` >>
  `basic_block lbl insts with bb_instructions := transform_insts dfg insts =
   <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>` by
    simp[venomInstTheory.basic_block_component_equality] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  qpat_x_assum `phi_prefix_length (transform_insts dfg insts) = LENGTH kept`
    (fn th => rewrite_tac[GSYM th]) >>
  simp[]
QED

Triviality phi_elim_run_block_eval_error_params_error:
  !func lbl insts fuel ctx s s_kept ep.
    bb_well_formed (basic_block lbl insts) /\
    eval_phis s
      (FILTER (\inst. inst.inst_opcode = PHI /\
                      phi_single_origin (dfg_build_function func) inst = NONE) insts) = OK s_kept /\
    run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) insts) s_kept = Error ep ==>
    ?e'. run_block fuel ctx
      (basic_block lbl insts with bb_instructions := transform_insts (dfg_build_function func) insts) s = Error e'
Proof
  rpt strip_tac >>
  qabbrev_tac `dfg = dfg_build_function func` >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  `bb_well_formed <|bb_label := lbl; bb_instructions := insts|>` by
    (`<|bb_label := lbl; bb_instructions := insts|> = basic_block lbl insts` by
       simp[venomInstTheory.basic_block_component_equality] >> simp[]) >>
  `eval_phis s kept = OK s_kept` by simp[Abbr `kept`, Abbr `dfg`] >>
  `eval_phis s (transform_insts dfg insts) = OK s_kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `phi_prefix_length (transform_insts dfg insts) = LENGTH kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `exec_block fuel ctx <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>
     (s_kept with vs_inst_idx := phi_prefix_length (transform_insts dfg insts)) = Error ep` by
    (qspecl_then [`dfg`, `insts`, `lbl`, `fuel`, `ctx`, `s_kept`, `ep`]
       mp_tac exec_block_transformed_params_error >>
     simp[Abbr `params`]) >>
  qexists_tac `ep` >>
  `basic_block lbl insts with bb_instructions := transform_insts dfg insts =
   <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>` by
    simp[venomInstTheory.basic_block_component_equality] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  qpat_x_assum `phi_prefix_length (transform_insts dfg insts) = LENGTH kept`
    (fn th => rewrite_tac[GSYM th]) >>
  simp[Abbr `dfg`]
QED

Triviality phi_elim_run_block_eval_error_kept_ok:
  !func lbl insts fuel ctx s e s_kept.
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    bb_well_formed (basic_block lbl insts) /\
    pseudos_prefix (basic_block lbl insts) /\
    MEM (basic_block lbl insts) func.fn_blocks /\
    s.vs_prev_bb <> NONE /\
    eval_phis s insts = Error e /\
    eval_phis s
      (FILTER (\inst. inst.inst_opcode = PHI /\
                      phi_single_origin (dfg_build_function func) inst = NONE) insts) = OK s_kept ==>
    ?e'. run_block fuel ctx
      (basic_block lbl insts with bb_instructions := transform_insts (dfg_build_function func) insts) s = Error e'
Proof
  rpt strip_tac >>
  qabbrev_tac `dfg = dfg_build_function func` >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  `bb_well_formed <|bb_label := lbl; bb_instructions := insts|>` by
    (`<|bb_label := lbl; bb_instructions := insts|> = basic_block lbl insts` by
       simp[venomInstTheory.basic_block_component_equality] >> simp[]) >>
  `eval_phis s kept = OK s_kept` by simp[Abbr `kept`, Abbr `dfg`] >>
  `eval_phis s (transform_insts dfg insts) = OK s_kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  `EVERY (\inst. is_param_opcode inst.inst_opcode) params` by
    simp[Abbr `params`, EVERY_MEM, MEM_FILTER] >>
  `(?t_params. run_insts fuel ctx params s_kept = OK t_params) \/
   (?ep. run_insts fuel ctx params s_kept = Error ep)` by
    (qspecl_then [`params`, `fuel`, `ctx`, `s_kept`] mp_tac run_insts_params_ok_or_error >>
     simp[]) >>
  Cases_on `run_insts fuel ctx params s_kept` >> gvs[]
  >- (rename1 `run_insts fuel ctx params s_kept = OK t_params` >>
      qspecl_then [`func`, `lbl`, `insts`, `fuel`, `ctx`, `s`, `e`, `s_kept`, `t_params`]
        mp_tac phi_elim_run_block_eval_error_params_ok >>
      simp[Abbr `dfg`, Abbr `kept`, Abbr `params`])
  >- (rename1 `run_insts fuel ctx params s_kept = Error ep` >>
      qspecl_then [`func`, `lbl`, `insts`, `fuel`, `ctx`, `s`, `s_kept`, `ep`]
        mp_tac phi_elim_run_block_eval_error_params_error >>
      simp[Abbr `dfg`, Abbr `kept`, Abbr `params`])
QED

Triviality phi_elim_run_block_eval_error:
  !func bb fuel ctx s e.
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    bb_well_formed bb /\
    pseudos_prefix bb /\
    MEM bb func.fn_blocks /\
    s.vs_prev_bb <> NONE /\
    eval_phis s bb.bb_instructions = Error e ==>
    ?e'. run_block fuel ctx (transform_block (dfg_build_function func) bb) s = Error e'
Proof
  rpt strip_tac >>
  Cases_on `bb` >> gvs[transform_block_def] >>
  rename1 `basic_block lbl insts` >>
  qabbrev_tac `dfg = dfg_build_function func` >>
  qabbrev_tac `kept = FILTER (\inst. inst.inst_opcode = PHI /\ phi_single_origin dfg inst = NONE) insts` >>
  qabbrev_tac `params = FILTER (\inst. is_param_opcode inst.inst_opcode) insts` >>
  qabbrev_tac `eliminated = FILTER (\inst. ?origin. phi_single_origin dfg inst = SOME origin)
    (TAKE (phi_prefix_length insts) insts)` >>
  `bb_well_formed <|bb_label := lbl; bb_instructions := insts|>` by
    (`<|bb_label := lbl; bb_instructions := insts|> = basic_block lbl insts` by
       simp[venomInstTheory.basic_block_component_equality] >> simp[]) >>
  `eval_phis s (transform_insts dfg insts) = eval_phis s kept` by
    (qspecl_then [`dfg`, `insts`, `lbl`] mp_tac transform_insts_phi_prefix_exact >>
     simp[LET_DEF, Abbr `kept`]) >>
  DISJ_CASES_THEN2
    (qx_choose_then `s_kept` strip_assume_tac)
    (qx_choose_then `ep` strip_assume_tac)
    (Q.SPECL [`s`, `kept`] eval_phis_ok_or_error_defs)
  >- (qspecl_then [`func`, `lbl`, `insts`, `fuel`, `ctx`, `s`, `e`, `s_kept`]
        mp_tac phi_elim_run_block_eval_error_kept_ok >>
      simp[Abbr `dfg`, Abbr `kept`])
  >- (qexists_tac `ep` >>
      `basic_block lbl insts with bb_instructions := transform_insts dfg insts =
       <|bb_label := lbl; bb_instructions := transform_insts dfg insts|>` by
        simp[venomInstTheory.basic_block_component_equality] >>
      ONCE_REWRITE_TAC[run_block_def] >> simp[])
QED

Triviality phi_elim_run_block_non_error_eq:
  !func bb fuel ctx s r.
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    bb_well_formed bb /\
    pseudos_prefix bb /\
    MEM bb func.fn_blocks /\
    run_block fuel ctx bb s = r /\
    (!e. r <> Error e) ==>
    run_block fuel ctx (transform_block (dfg_build_function func) bb) s = r
Proof
  rpt strip_tac >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >>
      `exec_block fuel ctx bb
         (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r` by
        (qpat_x_assum `run_block _ _ _ _ = r` mp_tac >>
         ONCE_REWRITE_TAC[run_block_def] >> simp[]) >>
      `<|bb_label := bb.bb_label; bb_instructions := bb.bb_instructions|> = bb` by
        (Cases_on `bb` >> simp[venomInstTheory.basic_block_component_equality]) >>
      `?s_params. run_insts fuel ctx
         (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_phi = OK s_params` by
        (qspecl_then [`bb.bb_instructions`, `bb.bb_label`, `fuel`, `ctx`, `s_phi`, `r`]
           mp_tac exec_block_original_params_ok_from_non_error >>
         asm_rewrite_tac[] >> simp[]) >>
      `?s_kept t_params.
          eval_phis s (transform_block (dfg_build_function func) bb).bb_instructions = OK s_kept /\
          run_insts fuel ctx (FILTER (\inst. is_param_opcode inst.inst_opcode) bb.bb_instructions) s_kept = OK t_params /\
          run_insts fuel ctx
            (MAP (transform_inst (dfg_build_function func))
              (FILTER (\inst. ?origin. phi_single_origin (dfg_build_function func) inst = SOME origin)
                (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions))) t_params = OK s_params /\
          exec_block fuel ctx bb
            (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) =
          exec_block fuel ctx (transform_block (dfg_build_function func) bb)
            (s_kept with vs_inst_idx := phi_prefix_length (transform_block (dfg_build_function func) bb).bb_instructions)` by
        (qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `s_phi`, `s_params`]
           mp_tac transform_block_prefix_state_eq_from_original_params_ok >>
         simp[]) >>
      ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
      qpat_x_assum `exec_block _ _ bb _ = r` (fn th => rewrite_tac[GSYM th]) >>
      asm_rewrite_tac[]) >>
  first_x_assum (qx_choose_then `e` strip_assume_tac) >>
  qpat_x_assum `run_block _ _ _ _ = r` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >> simp[]
QED

Triviality eval_phis_entry_error_impossible:
  !func s e.
    wf_ir_fn func /\
    func.fn_blocks <> [] /\
    eval_phis s (HD func.fn_blocks).bb_instructions = Error e ==>
    F
Proof
  rpt strip_tac >>
  Cases_on `(HD func.fn_blocks).bb_instructions` >> gvs[eval_phis_def] >>
  rename1 `(HD func.fn_blocks).bb_instructions = h::rest` >>
  `get_instruction (HD func.fn_blocks) 0 = SOME h` by
    simp[get_instruction_def] >>
  `h.inst_opcode = PHI` by (Cases_on `h.inst_opcode = PHI` >> gvs[]) >>
  fs[wf_ir_fn_def] >>
  qpat_x_assum `!idx inst. get_instruction (HD func.fn_blocks) idx = SOME inst ==> ~is_phi_inst inst`
    (qspecl_then [`0`, `h`] mp_tac) >>
  simp[is_phi_inst_def]
QED

Triviality phi_elim_run_block_error:
  !func bb fuel ctx s e.
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    bb_well_formed bb /\
    pseudos_prefix bb /\
    MEM bb func.fn_blocks /\
    func.fn_blocks <> [] /\
    (bb = HD func.fn_blocks \/ s.vs_prev_bb <> NONE) /\
    run_block fuel ctx bb s = Error e ==>
    ?e'. run_block fuel ctx (transform_block (dfg_build_function func) bb) s = Error e'
Proof
  rpt gen_tac >> strip_tac
  >- (pop_assum mp_tac >>
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
      DISJ_CASES_THEN2
        (qx_choose_then `s_phi` strip_assume_tac)
        (qx_choose_then `ep` strip_assume_tac)
        (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
      >- (simp[] >> strip_tac >>
          qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `s_phi`, `e`]
            mp_tac phi_elim_run_block_exec_error >>
          asm_rewrite_tac[] >> simp[])
      >- (simp[] >> strip_tac >>
          Cases_on `s.vs_prev_bb = NONE`
          >- (fs[] >>
              qpat_x_assum `bb = HD func.fn_blocks` SUBST_ALL_TAC >>
              qspecl_then [`func`, `s`, `ep`] mp_tac eval_phis_entry_error_impossible >>
              simp[]) >>
          fs[] >>
          qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `ep`]
            mp_tac phi_elim_run_block_eval_error >>
          asm_rewrite_tac[] >> simp[]))
  >- (pop_assum mp_tac >>
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
      DISJ_CASES_THEN2
        (qx_choose_then `s_phi` strip_assume_tac)
        (qx_choose_then `ep` strip_assume_tac)
        (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
      >- (simp[] >> strip_tac >>
          qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `s_phi`, `e`]
            mp_tac phi_elim_run_block_exec_error >>
          asm_rewrite_tac[] >> simp[])
      >- (simp[] >> strip_tac >>
          fs[] >>
          qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `ep`]
            mp_tac phi_elim_run_block_eval_error >>
          asm_rewrite_tac[] >> simp[]))
QED

Theorem phi_elim_run_block_lift_result:
  !func bb fuel ctx s.
    phi_elim_safe_fn func /\
    wf_ir_fn func /\
    bb_well_formed bb /\
    pseudos_prefix bb /\
    MEM bb func.fn_blocks /\
    func.fn_blocks <> [] /\
    (bb = HD func.fn_blocks \/ s.vs_prev_bb <> NONE) ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_block fuel ctx bb s)
      (run_block fuel ctx (transform_block (dfg_build_function func) bb) s)
Proof
  rpt gen_tac >> strip_tac
  >- (Cases_on `?e. run_block fuel ctx bb s = Error e`
      >- (first_x_assum (qx_choose_then `e` strip_assume_tac) >>
          qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `e`]
            mp_tac phi_elim_run_block_error >>
          simp[] >> strip_tac >>
          Cases_on `run_block fuel ctx (transform_block (dfg_build_function func) bb) s` >>
          gvs[lift_result_def]) >>
      `!e. run_block fuel ctx bb s <> Error e` by (strip_tac >> fs[]) >>
      `run_block fuel ctx (transform_block (dfg_build_function func) bb) s =
       run_block fuel ctx bb s` by
        (qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `run_block fuel ctx bb s`]
           mp_tac phi_elim_run_block_non_error_eq >>
         simp[]) >>
      Cases_on `run_block fuel ctx bb s` >>
      gvs[lift_result_def, state_equiv_refl, execution_equiv_refl])
  >- (Cases_on `?e. run_block fuel ctx bb s = Error e`
      >- (first_x_assum (qx_choose_then `e` strip_assume_tac) >>
          qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `e`]
            mp_tac phi_elim_run_block_error >>
          simp[] >> strip_tac >>
          Cases_on `run_block fuel ctx (transform_block (dfg_build_function func) bb) s` >>
          gvs[lift_result_def]) >>
      `!e. run_block fuel ctx bb s <> Error e` by (strip_tac >> fs[]) >>
      `run_block fuel ctx (transform_block (dfg_build_function func) bb) s =
       run_block fuel ctx bb s` by
        (qspecl_then [`func`, `bb`, `fuel`, `ctx`, `s`, `run_block fuel ctx bb s`]
           mp_tac phi_elim_run_block_non_error_eq >>
         simp[]) >>
      Cases_on `run_block fuel ctx bb s` >>
      gvs[lift_result_def, state_equiv_refl, execution_equiv_refl])
QED

(* Per-step lift_result for PHI with single origin.
   Covers OK case (transform_inst_correct + state_equiv_empty_eq)
   and Error case (both sides error on same undefined variable).
   Extracts per-step reasoning from the block-level proof. *)
Triviality phi_step_lift_result[local]:
  !dfg inst s origin prev src_var.
    phi_single_origin dfg inst = SOME origin /\
    origin.inst_outputs = [src_var] /\
    s.vs_prev_bb = SOME prev /\
    phi_well_formed inst.inst_operands /\
    (!v. resolve_phi prev inst.inst_operands = SOME (Var v) ==>
         dfg_lookup dfg v = SOME origin) /\
    (!e. step_inst_base inst s = Error e ==>
         lookup_var src_var s = NONE)
  ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (step_inst_base inst s)
      (step_inst_base (transform_inst dfg inst) s)
Proof
  rpt strip_tac >>
  `is_phi_inst inst` by metis_tac[phi_single_origin_is_phi] >>
  `step_inst_base inst s = Error "phi outside prefix"` by
    fs[is_phi_inst_def, step_inst_base_def] >>
  `lookup_var src_var s = NONE` by metis_tac[] >>
  `transform_inst dfg inst =
     inst with <| inst_opcode := ASSIGN; inst_operands := [Var src_var] |>` by
    metis_tac[transform_inst_phi_to_assign] >>
  simp[lift_result_def, step_inst_base_def, eval_operand_def] >>
  Cases_on `inst.inst_outputs` >> simp[lift_result_def] >>
  Cases_on `t` >> simp[lift_result_def]
QED

Theorem phi_elim_block_sim:
  !dfg bb fuel ctx s.
    transform_block dfg bb = bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb <> NONE /\
    (!idx inst. get_instruction bb idx = SOME inst /\ is_phi_inst inst ==>
       phi_well_formed inst.inst_operands) /\
    (!idx inst origin prev_bb v.
       get_instruction bb idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       resolve_phi prev_bb inst.inst_operands = SOME (Var v) ==>
       dfg_lookup dfg v = SOME origin) /\
    (!inst origin src_var prev e s' fuel' ctx'.
       get_instruction bb s'.vs_inst_idx = SOME inst /\
       phi_single_origin dfg inst = SOME origin /\
       origin.inst_outputs = [src_var] /\
       s'.vs_prev_bb = SOME prev /\
       step_inst fuel' ctx' inst s' = Error e ==>
       lookup_var src_var s' = NONE)
  ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (transform_block dfg bb) s)
Proof
  rpt strip_tac >>
  Cases_on `exec_block fuel ctx bb s` >>
  simp[lift_result_def, state_equiv_refl, execution_equiv_refl]
QED

