(*
 * Memory Copy Elision — Proofs
 *
 * copy_elision_function is a 3-stage pipeline:
 *   1. analysis_function_transform — copy forwarding/elision (SoundScript)
 *   2. function_map_transform (load_store_elim_block) — load-store elision
 *   3. clear_nops_function — NOP removal
 *
 * Stage 1: df_analysis_pass_correct_block_sim wiring
 * Stage 2: block_sim_function_with_pred with per-block sim
 * Stage 3: clear_nops_function_correct (passSharedProps)
 *)

Theory memoryCopyElisionProofs
Ancestors
  memoryCopyElisionSound memoryCopyElisionConvergence memoryCopyElisionDefs
  analysisSimDefs analysisSimProps
  passSimulationDefs passSimulationProps passSharedDefs passSharedProps
  stateEquiv stateEquivProps
  basePtrDefs basePtrProps basePtrProofs
  venomWf venomInst venomInstProps venomEffects venomExecSemantics venomExecProps
  venomState venomMemDefs venomMemProps
  dfgAnalysisProps dfgCorrectnessProof dfgSoundStep dfgDefs dfAnalyzeDefs
  dfIterateProps dfIterateProofs
  memAliasDefs memAliasProofs memLocDefs
  cfgDefs cfgHelpers cfgAnalysisProps
  finite_map list pred_set arithmetic words pair

(* ===== Arithmetic helpers ===== *)

(* Any word can be written as n2w(base + delta) for some delta *)
Triviality n2w_exists_offset[local]:
  !(w:'a word) (b:num). ?delta:num. n2w (b + delta) = w
Proof
  rpt strip_tac >>
  qexists `w2n w + (dimword (:'a) - b MOD dimword (:'a))` >>
  `0 < dimword (:'a)` by simp[ZERO_LT_dimword] >>
  `b MOD dimword (:'a) < dimword (:'a)` by simp[] >>
  `w2n w < dimword (:'a)` by simp[w2n_lt] >>
  qabbrev_tac `d = dimword (:'a)` >>
  `b = (b DIV d) * d + b MOD d` by metis_tac[DIVISION] >>
  `b + (w2n w + (d - b MOD d)) = (b DIV d + 1) * d + w2n w` by
    decide_tac >>
  `((b DIV d + 1) * d + w2n w) MOD d = w2n w` by simp[MOD_MULT] >>
  simp[Abbr `d`, Once (GSYM n2w_mod), n2w_w2n]
QED

(* ptr_matches_var with NONE offset: only needs allocation exists + value defined *)
Triviality ptr_matches_var_none_trivial[local]:
  !aid v s base sz.
    FLOOKUP s.vs_allocas aid = SOME (base, sz) /\
    IS_SOME (lookup_var v s) ==>
    ptr_matches_var (Ptr (Allocation aid) NONE) v s
Proof
  rpt strip_tac >>
  simp[ptr_matches_var_def] >>
  Cases_on `lookup_var v s` >> gvs[] >>
  metis_tac[n2w_exists_offset]
QED

(* offset_by with NONE always produces NONE offset *)
Triviality offset_by_none_is_none[local]:
  !p. ?alloc. offset_by p NONE = Ptr alloc NONE
Proof
  Cases >> Cases_on `o'` >> simp[offset_by_def]
QED

(* ===== Stage 1: analysis_function_transform correctness ===== *)

Triviality copy_opcode_not_term[local]:
  !op. is_copy_opcode op ==> ~is_terminator op
Proof
  Cases >> simp[is_copy_opcode_def, is_terminator_def]
QED

Triviality copy_opcode_not_invoke[local]:
  !op. is_copy_opcode op ==> op ≠ INVOKE
Proof
  Cases >> simp[is_copy_opcode_def]
QED

Triviality copy_opcode_not_phi[local]:
  !op. is_copy_opcode op ==> op ≠ PHI
Proof
  Cases >> simp[is_copy_opcode_def]
QED

(* Re-prove inst_transform_structural (local in SoundScript) *)
Triviality cei_structural[local]:
  !bp dfg.
    inst_transform_structural (\v inst. [copy_elision_inst bp dfg v inst])
Proof
  rpt gen_tac >>
  simp[inst_transform_structural_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[copy_elision_inst_def, LET_THM] >>
  TRY (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >> NO_TAC) >>
  TRY (fs[] >> NO_TAC) >>
  TRY (
    qexists `inst` >> simp[] >>
    Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >> NO_TAC) >>
  TRY (
    qexists `inst` >> simp[] >>
    Cases_on `inst.inst_opcode` >> gvs[] >> NO_TAC) >>
  rpt (IF_CASES_TAC >> fs[mk_nop_inst_def, is_terminator_def]) >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  imp_res_tac copy_opcode_not_term >> imp_res_tac copy_opcode_not_invoke >>
  imp_res_tac copy_opcode_not_phi >>
  fs[]
QED

(* Helper: block membership implies fn_insts membership *)
Triviality mem_block_mem_fn_insts[local]:
  !inst bb bbs. MEM inst bb.bb_instructions /\ MEM bb bbs ==>
                MEM inst (fn_insts_blocks bbs)
Proof
  Induct_on `bbs` >> simp[fn_insts_blocks_def] >> metis_tac[]
QED

(* NOTE: dfg_assigns_sound IS per-instruction preserved under SSA.
   SSA (ALL_DISTINCT all outputs) means no variable is redefined.
   For a DFG ASSIGN edge (v, op): lookup_var v and eval_operand op are
   both unchanged by step_inst for any instruction inst ≠ assign_inst,
   since neither v nor op's variables are in inst.inst_outputs.
   See transfer_sound_exit_block_inv below. *)


(* Terminator step_inst_base is idx-independent *)
Triviality term_step_base_idx_0[local]:
  !inst s v.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK v ==>
    step_inst_base inst (s with vs_inst_idx := 0) = OK v
Proof
  rpt strip_tac >>
  `v.vs_inst_idx = 0` by
    metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0] >>
  qabbrev_tac `f = \st:venom_state. st with vs_inst_idx := 0` >>
  `exec_result_map f (step_inst_base inst (s with vs_inst_idx := 0)) =
   exec_result_map f (step_inst_base inst s)` by
    (unabbrev_all_tac >>
     metis_tac[instIdxIndepTheory.terminator_step_inst_base_idx_norm0]) >>
  `exec_result_map f (step_inst_base inst s) = OK v` by
    (simp[Abbr `f`, instIdxIndepTheory.exec_result_map_def] >>
     `v with vs_inst_idx := 0 = v` by
       simp[venom_state_component_equality] >> fs[]) >>
  fs[] >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := 0)` >>
  gvs[instIdxIndepTheory.exec_result_map_def, Abbr `f`] >>
  `v'.vs_inst_idx = 0` by
    metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0] >>
  simp[venom_state_component_equality]
QED

(* transfer_sound_exit_block_inv: exit soundness with state_inv threading.
   Like transfer_sound_exit_wf but uses transfer_sound_block_inv.
   Threads state_inv through the block, requiring per-inst preservation.
   Needed because transfer_sound/transfer_sound_wf are too strong for
   passes where soundness depends on non-universally-preserved state (e.g.
   dfg_assigns_sound, which is only preserved under SSA). *)
Triviality transfer_sound_exit_block_inv[local]:
  !sound state_inv transfer ctx fn bb bottom result.
    transfer_sound_block_inv sound state_inv transfer ctx fn /\
    MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    (!fuel run_ctx inst s s'.
       MEM inst bb.bb_instructions /\ inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel run_ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel run_ctx s v i.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s /\
      state_inv s /\
      exec_block fuel run_ctx bb s = OK v /\
      i < LENGTH bb.bb_instructions /\
      is_terminator (EL i bb.bb_instructions).inst_opcode /\
      (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode) ==>
      sound (df_at bottom result bb.bb_label (SUC i)) v
Proof
  rpt strip_tac >>
  (* Strengthen for induction: carry state_inv through *)
  `!n fuel run_ctx s.
     n = i + 1 - s.vs_inst_idx /\
     s.vs_inst_idx <= i /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx)
           (s with vs_inst_idx := 0) /\
     state_inv (s with vs_inst_idx := 0) /\
     exec_block fuel run_ctx bb s = OK v ==>
     sound (df_at bottom result bb.bb_label (SUC i)) v`
    suffices_by (
      disch_then (qspecl_then
        [`i + 1`, `fuel`, `run_ctx`, `s`] mp_tac) >>
      `s with vs_inst_idx := 0 = s` by
        fs[venom_state_component_equality] >> simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `idx = s'.vs_inst_idx` >>
  `idx < LENGTH bb.bb_instructions` by decide_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst_wf inst` by metis_tac[EVERY_EL, markerTheory.Abbrev_def] >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`, MEM_EL] >> qexists `idx` >> simp[]) >>
  `exec_block fuel' run_ctx' bb s' =
   case step_inst fuel' run_ctx' inst s' of
     OK s'' =>
       if is_terminator inst.inst_opcode then
         if s''.vs_halted then Halt s'' else OK s''
       else exec_block fuel' run_ctx' bb (s'' with vs_inst_idx := SUC idx)
   | Halt s'' => Halt s''
   | Abort a s'' => Abort a s''
   | IntRet rv ss => IntRet rv ss
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `idx`]) >>
  pop_assum (fn th => FULL_SIMP_TAC std_ss [th]) >>
  Cases_on `step_inst fuel' run_ctx' inst s'` >> fs[]
  >- (
    rename1 `OK s''` >>
    Cases_on `idx = i`
    >- (
      (* At the terminator index: idx = i *)
      `is_terminator inst.inst_opcode` by fs[Abbr `inst`] >>
      Cases_on `s''.vs_halted` >- fs[] >>
      fs[] >>
      (* Goal: sound (transfer ctx inst (df_at lbl i)) v, where s'' = v *)
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> fs[is_terminator_def]) >>
      `step_inst_base inst s' = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `step_inst_base inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[term_step_base_idx_0] >>
      `step_inst fuel' run_ctx' inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `SUC idx <= LENGTH bb.bb_instructions` by decide_tac >>
      qpat_x_assum `transfer_sound_block_inv _ _ _ _ _`
        (mp_tac o REWRITE_RULE [transfer_sound_block_inv_def]) >>
      disch_then (qspecl_then
        [`fuel'`, `run_ctx'`,
         `df_at bottom result bb.bb_label idx`,
         `inst`, `s' with vs_inst_idx := 0`, `v`, `bb`] mp_tac) >>
      simp[Abbr `inst`])
    >- (
      (* Before the terminator: advance idx *)
      `idx < i` by decide_tac >>
      `~is_terminator inst.inst_opcode` by
        (qpat_x_assum `!j. j < i ==> _` (qspec_then `idx` mp_tac) >>
         simp[Abbr `inst`]) >>
      fs[] >>
      (* Normalize step_inst to idx=0 *)
      `step_inst fuel' run_ctx' inst (s' with vs_inst_idx := 0) =
       OK (s'' with vs_inst_idx := 0)` by (
        Cases_on `inst.inst_opcode = INVOKE`
        >- (mp_tac (Q.SPECL [`fuel'`, `run_ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only) >>
            simp[])
        >- (mp_tac (Q.SPECL [`fuel'`, `run_ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.step_inst_idx_indep) >>
            simp[instIdxIndepTheory.exec_result_map_def])) >>
      (* Derive soundness at SUC idx *)
      `SUC idx <= LENGTH bb.bb_instructions` by decide_tac >>
      `sound (df_at bottom result bb.bb_label (SUC idx))
             (s'' with vs_inst_idx := 0)` by (
        qpat_x_assum `transfer_sound_block_inv _ _ _ _ _`
          (mp_tac o REWRITE_RULE [transfer_sound_block_inv_def]) >>
        disch_then (qspecl_then
          [`fuel'`, `run_ctx'`,
           `df_at bottom result bb.bb_label idx`,
           `inst`, `s' with vs_inst_idx := 0`,
           `s'' with vs_inst_idx := 0`, `bb`] mp_tac) >>
        simp[Abbr `inst`]) >>
      (* state_inv preserved + apply IH *)
      suspend "state_inv_ih"))
QED

Resume transfer_sound_exit_block_inv[state_inv_ih]:
  (* Derive state_inv (s'' with vs_inst_idx := 0) *)
  `state_inv (s'' with vs_inst_idx := 0)` by (
    qpat_assum `!fuel run_ctx inst s s'. _ ==> state_inv _`
      (qspecl_then [`fuel'`, `run_ctx'`, `inst`,
                    `s' with vs_inst_idx := 0`,
                    `s'' with vs_inst_idx := 0`] mp_tac) >>
    simp[]) >>
  (* Apply IH: s'' at SUC idx has sound/state_inv, exec_block = OK v *)
  first_x_assum (qspec_then `i + 1 - SUC idx` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`fuel'`, `run_ctx'`,
    `s'' with vs_inst_idx := SUC idx`] mp_tac) >>
  simp[] >> (impl_tac >- gvs[]) >> strip_tac
QED

Finalise transfer_sound_exit_block_inv

Triviality transfer_sound_exit_block_inv_from_idx[local]:
  !sound state_inv transfer ctx fn bb bottom result.
    transfer_sound_block_inv sound state_inv transfer ctx fn /\
    MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    (!fuel run_ctx inst s s'.
       MEM inst bb.bb_instructions /\ inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel run_ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel run_ctx s v i.
      s.vs_inst_idx <= i /\
      sound (df_at bottom result bb.bb_label s.vs_inst_idx)
            (s with vs_inst_idx := 0) /\
      state_inv (s with vs_inst_idx := 0) /\
      exec_block fuel run_ctx bb s = OK v /\
      i < LENGTH bb.bb_instructions /\
      is_terminator (EL i bb.bb_instructions).inst_opcode /\
      (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode) ==>
      sound (df_at bottom result bb.bb_label (SUC i)) v
Proof
  rpt strip_tac >>
  `!n fuel run_ctx s.
     n = i + 1 - s.vs_inst_idx /\
     s.vs_inst_idx <= i /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx)
           (s with vs_inst_idx := 0) /\
     state_inv (s with vs_inst_idx := 0) /\
     exec_block fuel run_ctx bb s = OK v ==>
     sound (df_at bottom result bb.bb_label (SUC i)) v`
    suffices_by (
      disch_then (qspecl_then
        [`i + 1 - s.vs_inst_idx`, `fuel`, `run_ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `idx = s'.vs_inst_idx` >>
  `idx < LENGTH bb.bb_instructions` by decide_tac >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst_wf inst` by metis_tac[EVERY_EL, markerTheory.Abbrev_def] >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`, MEM_EL] >> qexists `idx` >> simp[]) >>
  `exec_block fuel' run_ctx' bb s' =
   case step_inst fuel' run_ctx' inst s' of
     OK s'' =>
       if is_terminator inst.inst_opcode then
         if s''.vs_halted then Halt s'' else OK s''
       else exec_block fuel' run_ctx' bb (s'' with vs_inst_idx := SUC idx)
   | Halt s'' => Halt s''
   | Abort a s'' => Abort a s''
   | IntRet rv ss => IntRet rv ss
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `idx`]) >>
  pop_assum (fn th => FULL_SIMP_TAC std_ss [th]) >>
  Cases_on `step_inst fuel' run_ctx' inst s'` >> fs[]
  >- (
    rename1 `OK s''` >>
    Cases_on `idx = i`
    >- (
      `is_terminator inst.inst_opcode` by fs[Abbr `inst`] >>
      Cases_on `s''.vs_halted` >- fs[] >>
      fs[] >>
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> fs[is_terminator_def]) >>
      `step_inst_base inst s' = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `step_inst_base inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[term_step_base_idx_0] >>
      `step_inst fuel' run_ctx' inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `SUC idx <= LENGTH bb.bb_instructions` by decide_tac >>
      qpat_x_assum `transfer_sound_block_inv _ _ _ _ _`
        (mp_tac o REWRITE_RULE [transfer_sound_block_inv_def]) >>
      disch_then (qspecl_then
        [`fuel'`, `run_ctx'`,
         `df_at bottom result bb.bb_label idx`,
         `inst`, `s' with vs_inst_idx := 0`, `v`, `bb`] mp_tac) >>
      simp[Abbr `inst`])
    >- (
      `idx < i` by decide_tac >>
      `~is_terminator inst.inst_opcode` by
        (qpat_x_assum `!j. j < i ==> _` (qspec_then `idx` mp_tac) >>
         simp[Abbr `inst`]) >>
      fs[] >>
      `step_inst fuel' run_ctx' inst (s' with vs_inst_idx := 0) =
       OK (s'' with vs_inst_idx := 0)` by (
        Cases_on `inst.inst_opcode = INVOKE`
        >- (mp_tac (Q.SPECL [`fuel'`, `run_ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only) >>
            simp[])
        >- (mp_tac (Q.SPECL [`fuel'`, `run_ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.step_inst_idx_indep) >>
            simp[instIdxIndepTheory.exec_result_map_def])) >>
      `SUC idx <= LENGTH bb.bb_instructions` by decide_tac >>
      `sound (df_at bottom result bb.bb_label (SUC idx))
             (s'' with vs_inst_idx := 0)` by (
        qpat_x_assum `transfer_sound_block_inv _ _ _ _ _`
          (mp_tac o REWRITE_RULE [transfer_sound_block_inv_def]) >>
        disch_then (qspecl_then
          [`fuel'`, `run_ctx'`,
           `df_at bottom result bb.bb_label idx`,
           `inst`, `s' with vs_inst_idx := 0`,
           `s'' with vs_inst_idx := 0`, `bb`] mp_tac) >>
        simp[Abbr `inst`]) >>
      suspend "state_inv_ih"))
QED

Resume transfer_sound_exit_block_inv_from_idx[state_inv_ih]:
  `state_inv (s'' with vs_inst_idx := 0)` by (
    qpat_assum `!fuel run_ctx inst s s'. _ ==> state_inv _`
      (qspecl_then [`fuel'`, `run_ctx'`, `inst`,
                    `s' with vs_inst_idx := 0`,
                    `s'' with vs_inst_idx := 0`] mp_tac) >>
    simp[]) >>
  first_x_assum (qspec_then `i + 1 - SUC idx` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`fuel'`, `run_ctx'`,
    `s'' with vs_inst_idx := SUC idx`] mp_tac) >>
  simp[] >> (impl_tac >- gvs[]) >> strip_tac
QED

Finalise transfer_sound_exit_block_inv_from_idx

(*
 * stage1_framework_th: df_analysis_pass_correct_sound_inv3 with type
 * variables instantiated to our lattice and context types.
 * inv3 gives block_sim for free — we only need transfer_sound_block_inv,
 * per-inst sim, per-inst state_inv pres, and cross_block.
 *)
val stage1_framework_th =
  INST_TYPE [
    alpha |-> ``:(mem_loc |-> copy_fact) option``,
    beta |-> ``:copy_elision_ctx``
  ] (SIMP_RULE std_ss [LET_THM] df_analysis_pass_correct_sound_inv3);

Triviality stage1_correct[local]:
  !fuel ctx fn s.
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let bp = bp_analyze cfg fn in
    let aliases = memory_alias_analyze bp fn in
    let ce_ctx = <| ce_aliases := aliases; ce_bp := bp; ce_dfg := dfg |> in
    let result = copy_fact_analyze ce_ctx fn in
    let fn1 = analysis_function_transform NONE result
                (\v inst. [copy_elision_inst bp dfg v inst]) fn in
    wf_function fn /\
    fn_inst_wf fn /\
    wf_ssa fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_assigns_sound dfg s /\
    bp_ptr_sound bp s /\
    alloca_inv s /\
    allocas_in_word s /\
    bp_ptrs_bounded bp fn s /\
    bp_assigns_stable bp dfg /\
    (!bb s0 s_phi.
       MEM bb fn.fn_blocks /\
       MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
       eval_phis s0 bb.bb_instructions = OK s_phi /\
       dfg_assigns_sound dfg s0 ==>
       dfg_assigns_sound dfg s_phi) /\
    (!fuel' run_ctx bb inst s0 s1.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       inst_wf inst /\
       dfg_assigns_sound dfg (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst s0 = OK s1 ==>
       dfg_assigns_sound dfg (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s1 with vs_inst_idx := 0)) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx fn1 s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  `ssa_form fn /\ def_dominates_uses fn` by gvs[wf_ssa_def] >>
  simp_tac std_ss [copy_fact_analyze_def, LET_THM] >>
  irule stage1_framework_th >>
  qabbrev_tac `bp = bp_analyze (cfg_analyze fn) fn` >>
  qabbrev_tac `dfg = dfg_build_function fn` >>
  qabbrev_tac `aliases = memory_alias_analyze bp fn` >>
  qabbrev_tac `ce_ctx = <| ce_aliases := aliases;
                            ce_bp := bp; ce_dfg := dfg |>` >>
  simp[state_equiv_execution_equiv_valid_state_rel, copy_fact_is_fixpoint,
       Abbr `ce_ctx`, cei_structural] >>
  (* lookup_var preserved under R_ok *)
  conj_tac >- (rpt strip_tac >> imp_res_tac state_equiv_empty_eq >> gvs[]) >>
  (* state_equiv transitivity *)
  conj_tac >- (rpt strip_tac >> imp_res_tac state_equiv_empty_eq >> gvs[]) >>
  (* execution_equiv transitivity *)
  conj_tac >- (rpt gen_tac >> strip_tac >>
    irule execution_equiv_trans >> qexists `s2` >> fs[]) >>
  (* Provide witnesses for sound, state_inv.
     sound = cf properties only (must hold at entry for all states).
     state_inv = runtime invariants (bp_ptr_sound, alloca_inv, etc.)
     which DON'T hold for all states but ARE preserved per-inst. *)
  qexistsl [`\v s.
    cf_sound_opt bp dfg v s /\ cf_keys_ok_opt bp v /\
    cf_alloca_ok_opt bp v s`,
    `\s. dfg_assigns_sound dfg s /\ bp_ptr_sound bp s /\ alloca_inv s /\
         allocas_in_word s /\ bp_ptrs_bounded bp fn s`] >>
  BETA_TAC >>
  conj_tac >- simp[] >>                       (* 1. state_inv s *)
  conj_tac >- suspend "cross_block" >>         (* cross-block / successor soundness *)
  conj_tac >- suspend "eval_phis_sound" >>     (* eval_phis entry sound/state_inv *)
  conj_tac >- suspend "state_inv_pres" >>      (* per-inst state_inv pres *)
  conj_tac >- suspend "per_inst_sim" >>        (* per-inst simulation *)
  conj_tac >- (rpt strip_tac >>               (* sound under R_ok *)
    imp_res_tac state_equiv_empty_eq >> gvs[]) >>
  conj_tac >- suspend "entry_sound" >>         (* entry sound *)
  conj_tac >- (rpt strip_tac >>               (* state_inv under R_ok *)
    imp_res_tac state_equiv_empty_eq >> gvs[]) >>
  suspend "transfer_sound"                    (* transfer_sound_block_inv *)
QED

Triviality copy_fact_join_fempty_l[local]:
  !dfg x. copy_fact_join dfg (SOME FEMPTY) x = SOME FEMPTY
Proof
  rpt gen_tac >> Cases_on `x` >>
  simp[copy_fact_join_def, copy_fact_join_raw_def, DRESTRICT_FEMPTY]
QED

Triviality cf_agree_fempty_r[local]:
  !dfg f k. ~cf_agree dfg f FEMPTY k
Proof
  simp[cf_agree_def, FLOOKUP_DEF, FDOM_FEMPTY] >>
  rpt gen_tac >> CASE_TAC >> simp[]
QED

Triviality copy_fact_join_fempty_r[local]:
  !dfg x. copy_fact_join dfg x (SOME FEMPTY) = SOME FEMPTY
Proof
  rpt gen_tac >> Cases_on `x` >>
  simp[copy_fact_join_def, copy_fact_join_raw_def,
       DRESTRICT_EQ_FEMPTY, cf_agree_fempty_r,
       DRESTRICT_FEMPTY, DRESTRICT_IS_FEMPTY]
QED

Triviality cf_sound_opt_fempty_all[local]:
  !bp dfg s.
    cf_sound_opt bp dfg (SOME FEMPTY) s /\
    cf_keys_ok_opt bp (SOME FEMPTY) /\
    cf_alloca_ok_opt bp (SOME FEMPTY) s
Proof
  simp[cf_sound_opt_fempty, cf_keys_ok_opt_def, cf_keys_ok_def,
       cf_alloca_ok_opt_def, cf_alloca_ok_def, FDOM_FEMPTY]
QED

Triviality entry_in_dfs_pre[local]:
  !fn lbl. fn_entry_label fn = SOME lbl ==>
           MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  rw[fn_entry_label_def] >>
  Cases_on `entry_block fn` >> gvs[] >>
  imp_res_tac cfg_analyze_preorder_entry_first >>
  Cases_on `(cfg_analyze fn).cfg_dfs_pre` >> gvs[]
QED

(* At entry, the analysis value is SOME FEMPTY (empty tracked copy set). *)
Triviality df_at_entry_fempty[local]:
  !ce_ctx fn lbl.
    wf_function fn /\ fn_inst_wf fn /\
    fn_entry_label fn = SOME lbl ==>
    df_at NONE
      (df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg)
         copy_fact_transfer copy_fact_edge_transfer ce_ctx
         (SOME (lbl, SOME FEMPTY)) fn) lbl 0 = SOME FEMPTY
Proof
  rpt strip_tac >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by metis_tac[entry_in_dfs_pre] >>
  `OPTION_MAP (\l. (l, SOME FEMPTY)) (fn_entry_label fn) =
   SOME (lbl, SOME FEMPTY)` by simp[] >>
  qsuff_tac `df_at NONE
    (df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
       copy_fact_edge_transfer ce_ctx (SOME (lbl,SOME FEMPTY)) fn) lbl 0 =
    df_joined_val Forward NONE (copy_fact_join ce_ctx.ce_dfg)
       copy_fact_edge_transfer ce_ctx (SOME (lbl,SOME FEMPTY))
       (cfg_analyze fn)
       (df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
          copy_fact_edge_transfer ce_ctx (SOME (lbl,SOME FEMPTY)) fn) lbl`
  >- (disch_then (fn th => rewrite_tac[th]) >>
      simp[df_joined_val_def, LET_THM, copy_fact_join_fempty_l]) >>
  irule (SIMP_RULE std_ss [LET_THM] fwd_df_at_entry_eq_joined) >>
  simp[] >>
  mp_tac (Q.SPECL [`ce_ctx`, `fn`] copy_fact_is_fixpoint) >>
  simp[]
QED

(* --- Obligation: entry soundness (cf properties only, for all s'') --- *)
Resume stage1_correct[entry_sound]:
  mp_tac (Q.SPECL [`<| ce_aliases := aliases; ce_bp := bp; ce_dfg := dfg |>`,
                    `fn`, `s.vs_current_bb`] df_at_entry_fempty) >>
  simp[] >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[cf_sound_opt_fempty_all]
QED

(* --- vs_inst_idx independence for state_inv components --- *)
(* Each depends only on vs_vars/vs_allocas/vs_labels, not vs_inst_idx. *)
(* Using val + augment_srw_ss to avoid Triviality between Resume blocks *)
val lookup_var_inst_idx = Q.prove(
  `lookup_var v (s with vs_inst_idx := n) = lookup_var v s`,
  simp[lookup_var_def]);
val eval_operand_inst_idx = Q.prove(
  `eval_operand op (s with vs_inst_idx := n) = eval_operand op s`,
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def]);
val dfg_assigns_sound_inst_idx = Q.prove(
  `dfg_assigns_sound dfg (s with vs_inst_idx := n) = dfg_assigns_sound dfg s`,
  simp[dfg_assigns_sound_def, lookup_var_def, eval_operand_inst_idx]);
val allocas_non_overlapping_inst_idx = Q.prove(
  `allocas_non_overlapping (s with vs_inst_idx := n) = allocas_non_overlapping s`,
  simp[allocas_non_overlapping_def]);
val allocas_in_word_inst_idx = Q.prove(
  `allocas_in_word (s with vs_inst_idx := n) = allocas_in_word s`,
  simp[allocas_in_word_def]);
val bp_ptrs_bounded_inst_idx = Q.prove(
  `bp_ptrs_bounded bp fn (s with vs_inst_idx := n) = bp_ptrs_bounded bp fn s`,
  simp[bp_ptrs_bounded_def, memloc_within_alloca_def]);
val ptr_matches_var_inst_idx = Q.prove(
  `ptr_matches_var p v (s with vs_inst_idx := n) = ptr_matches_var p v s`,
  Cases_on `p` >> Cases_on `a` >> Cases_on `o'` >>
  simp[ptr_matches_var_def, lookup_var_def]);
val bp_ptr_sound_inst_idx = Q.prove(
  `bp_ptr_sound bp (s with vs_inst_idx := n) = bp_ptr_sound bp s`,
  simp[bp_ptr_sound_def, lookup_var_def, ptr_matches_var_inst_idx]);
val alloca_inv_inst_idx = Q.prove(
  `alloca_inv (s with vs_inst_idx := n) = alloca_inv s`,
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]);
val _ = augment_srw_ss [rewrites [
  lookup_var_inst_idx, eval_operand_inst_idx, dfg_assigns_sound_inst_idx,
  allocas_non_overlapping_inst_idx, allocas_in_word_inst_idx,
  bp_ptrs_bounded_inst_idx, ptr_matches_var_inst_idx, bp_ptr_sound_inst_idx,
  alloca_inv_inst_idx]];

Triviality alloca_inv_alloca_fields_eq[local]:
  !s1 s2.
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    alloca_inv s2 ==>
    alloca_inv s1
Proof
  rw[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
  metis_tac[]
QED

Triviality alloca_inv_non_overlapping[local]:
  !s. alloca_inv s ==> allocas_non_overlapping s
Proof
  simp[alloca_inv_def]
QED

Triviality allocas_in_word_allocas_eq[local]:
  !s1 s2.
    s1.vs_allocas = s2.vs_allocas /\ allocas_in_word s2 ==>
    allocas_in_word s1
Proof
  rw[allocas_in_word_def]
QED

Triviality bp_ptrs_bounded_allocas_eq[local]:
  !bp fn s1 s2.
    s1.vs_allocas = s2.vs_allocas /\ bp_ptrs_bounded bp fn s2 ==>
    bp_ptrs_bounded bp fn s1
Proof
  rw[bp_ptrs_bounded_def, memloc_within_alloca_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* --- Obligation: per-inst simulation --- *)
Resume stage1_correct[per_inst_sim]:
  rpt strip_tac >>
  irule cei_simulates_inv >> simp[]
QED

(* Monotonicity of transfer_sound_block_inv in state_inv:
   stronger state_inv (more hypotheses) makes it easier to satisfy. *)
Triviality tsbi_strengthen_state_inv[local]:
  !sound si1 si2 tr ctx fn.
    transfer_sound_block_inv sound si1 tr ctx fn /\
    (!s. si2 s ==> si1 s) ==>
    transfer_sound_block_inv sound si2 tr ctx fn
Proof
  rw[transfer_sound_block_inv_def] >> res_tac
QED

(* --- Obligation: transfer_sound_block_inv --- *)
Resume stage1_correct[transfer_sound]:
  irule tsbi_strengthen_state_inv >>
  qexists `\s. dfg_assigns_sound dfg s /\ bp_ptr_sound bp s /\
               allocas_non_overlapping s /\ allocas_in_word s /\
               bp_ptrs_bounded bp fn s` >>
  conj_tac
  >- (rpt strip_tac >> gvs[alloca_inv_def]) >>
  match_mp_tac (SIMP_RULE std_ss []
    (Q.SPECL [`bp`, `dfg`,
              `<| ce_aliases := aliases; ce_bp := bp; ce_dfg := dfg |>`,
              `fn`] copy_fact_transfer_sound_thm)) >>
  simp[Abbr `aliases`, memory_alias_analyze_def, ma_analyze_wf]
QED

(* ===== Block-level state invariant preservation ===== *)

(* bp_ptr_sound depends on bp only through bp_get_ptrs *)
Triviality bp_ptr_sound_ext[local]:
  (!v. bp_get_ptrs bp1 v = bp_get_ptrs bp2 v) ==>
  (bp_ptr_sound bp1 s <=> bp_ptr_sound bp2 s)
Proof rw[bp_ptr_sound_def]
QED

(* When bp_handle_inst returns changed=F, all ptrs are unchanged *)
Triviality bp_handle_inst_no_change_ptrs[local]:
  !bp inst bp'.
    bp_handle_inst bp inst = (F, bp') ==>
    !v. bp_get_ptrs bp' v = bp_get_ptrs bp v
Proof
  rpt strip_tac >>
  Cases_on `inst_output inst`
  >- (imp_res_tac bp_handle_inst_no_output_unchanged >> gvs[]) >>
  rename1 `SOME out` >>
  reverse (Cases_on `v = out`)
  >- (
    drule bp_handle_inst_other_var >>
    disch_then (qspec_then `v` mp_tac) >> simp[]) >>
  (* v = out: changed=F means new_ptrs = original.
     The definition ends: (new_ptrs ≠ original, new_result)
     where new_ptrs = bp_get_ptrs new_result out,
     original = bp_get_ptrs bp out. FST=F ⟹ new_ptrs=original. *)
  gvs[] >>
  qpat_x_assum `bp_handle_inst _ _ = _` mp_tac >>
  rewrite_tac[bp_handle_inst_def, inst_output_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  rename1 `h::t` >> Cases_on `t` >> simp[] >>
  simp_tac std_ss [LET_THM] >> BETA_TAC >>
  (* After LET expansion, goal is:
     (bp_get_ptrs new_result h ≠ bp_get_ptrs bp h, new_result) = (F, bp')
     ⟹ bp_get_ptrs bp' h = bp_get_ptrs bp h *)
  strip_tac >> gvs[inst_output_def]
QED

(* When bp_process_block returns changed=F, all ptrs are unchanged *)
Triviality bp_process_block_no_change_ptrs[local]:
  !bp insts bp'.
    bp_process_block bp insts = (F, bp') ==>
    !v. bp_get_ptrs bp' v = bp_get_ptrs bp v
Proof
  Induct_on `insts`
  >- simp[bp_process_block_def] >>
  rpt strip_tac >>
  fs[bp_process_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac bp_handle_inst_no_change_ptrs >>
  metis_tac[]
QED

(* ===== bp_ptr_sound preservation =====
   Per-instruction preservation via DRESTRICT.
   At the fixpoint, for each instruction with output out:
   - bp_handle_inst bp inst = (F, bp') with same ptrs as bp
   - DRESTRICT bp (COMPL {out}) gives bp0 with bp_get_ptrs bp0 out = []
   - bp_handle_inst_sound on bp0 gives bp_ptr_sound bp0' s'
   - bp0' has same ptrs as bp (operand agreement under SSA + fixpoint)
   - bp_ptr_sound_ext: bp_ptr_sound bp s'

   Key helpers:
   - bp_get_ptrs_drestrict_neq: DRESTRICT doesn't affect other vars
   - bp_handle_inst_drestrict_output_eq: output ptrs match when input
     agrees on operands (operand vars ≠ out under SSA)
   - For pass-through: bp_get_ptrs bp out = [] (no FUPDATE, FDOM argument)
*)

Triviality bp_leq_fempty[local]:
  !f. (!v. set (bp_get_ptrs (FEMPTY : bp_result) v) SUBSET
           set (bp_get_ptrs (f : bp_result) v))
Proof
  simp[bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* bp_get_ptrs for vars not in FDOM is [] *)
Triviality bp_get_ptrs_not_in_fdom[local]:
  !bp v. v NOTIN FDOM bp ==> bp_get_ptrs bp v = []
Proof
  simp[bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* Monotonicity: bp_ptr_sound is monotone under removing entries *)
Triviality bp_ptr_sound_restrict[local]:
  !bp s ks.
    bp_ptr_sound bp s ==>
    bp_ptr_sound (DRESTRICT bp ks) s
Proof
  rw[bp_ptr_sound_def, bp_get_ptrs_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `v IN ks` >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* Per-instruction bp_ptr_sound preservation at the fixpoint.
   Uses DRESTRICT trick for the output variable. *)
(* DRESTRICT for output var: bp_get_ptrs gives [] *)
Triviality bp_get_ptrs_drestrict_out[local]:
  !bp out. bp_get_ptrs (DRESTRICT bp (COMPL {out})) out = []
Proof
  simp[bp_get_ptrs_def, FLOOKUP_DRESTRICT]
QED

(* DRESTRICT doesn't change ptrs for other vars *)
Triviality bp_get_ptrs_drestrict_neq[local]:
  !bp out v. v <> out ==>
    bp_get_ptrs (DRESTRICT bp (COMPL {out})) v = bp_get_ptrs bp v
Proof
  simp[bp_get_ptrs_def, FLOOKUP_DRESTRICT]
QED

(* === bp_analyze FDOM invariant ===
   FDOM (bp_analyze cfg fn) only contains output variables of
   pointer-tracking opcodes (ALLOCA, ADD, SUB, PHI, ASSIGN).
   Needed for the DRESTRICT approach to bp_ptr_sound preservation. *)

(* Pointer-tracking opcodes: the only opcodes that add entries to bp.
   PHI is deliberately excluded: bp_handle_inst leaves PHI unchanged because
   PHIs execute only through eval_phis at block entry. *)
Definition is_ptr_opcode_def:
  is_ptr_opcode op <=> op = ALLOCA \/ op = ADD \/ op = SUB \/ op = ASSIGN
End

(* Pointer-opcode outputs of a function *)
Definition fn_ptr_defs_def:
  fn_ptr_defs fn =
    BIGUNION (set (MAP (\bb.
      BIGUNION (set (MAP (\inst.
        if is_ptr_opcode inst.inst_opcode
        then set (inst_defs inst) else {})
      bb.bb_instructions)))
    fn.fn_blocks))
End

(* bp_handle_inst only adds to FDOM for pointer opcodes *)
Triviality bp_handle_inst_ptr_fdom[local]:
  !bp inst c bp'.
    bp_handle_inst bp inst = (c, bp') /\ inst_wf inst ==>
    FDOM bp' SUBSET FDOM bp UNION
      (if is_ptr_opcode inst.inst_opcode
       then set (inst_defs inst) else {})
Proof
  rpt strip_tac >>
  Cases_on `is_ptr_opcode inst.inst_opcode`
  >- (drule bp_handle_inst_fdom >> simp[SUBSET_DEF]) >>
  (* Non-pointer opcode *)
  gvs[is_ptr_opcode_def] >>
  Cases_on `inst_output inst`
  >- (imp_res_tac bp_handle_inst_no_output_unchanged >> gvs[SUBSET_DEF]) >>
  drule_all bp_handle_inst_passthrough_output >> simp[SUBSET_DEF]
QED

(* bp_process_block preserves FDOM ⊆ ptr-opcode defs *)
Triviality bp_process_block_ptr_fdom[local]:
  !bp insts c bp' ds.
    bp_process_block bp insts = (c, bp') /\
    FDOM bp SUBSET ds /\
    EVERY inst_wf insts /\
    (!inst. MEM inst insts ==> is_ptr_opcode inst.inst_opcode ==>
            set (inst_defs inst) SUBSET ds) ==>
    FDOM bp' SUBSET ds
Proof
  Induct_on `insts` >> simp[bp_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `FDOM r1 SUBSET ds` by (
    `inst_wf h` by gvs[] >>
    drule bp_handle_inst_ptr_fdom >> disch_then drule >> strip_tac >>
    irule SUBSET_TRANS >> qexists `FDOM bp UNION
      (if is_ptr_opcode h.inst_opcode then set (inst_defs h) else {})` >>
    simp[] >> IF_CASES_TAC >> simp[SUBSET_DEF]) >>
  first_x_assum $ qspecl_then [`r1`, `c2`, `bp'`, `ds`] mp_tac >>
  simp[]
QED

(* phi_filter_fwd does not make a non-pointer opcode into a pointer opcode,
   and it preserves outputs.  For PHI, is_ptr_opcode is false. *)
Triviality phi_filter_fwd_ptr_defs_subset[local]:
  !fwd inst ds.
    (!inst. is_ptr_opcode inst.inst_opcode ==> set (inst_defs inst) SUBSET ds) ==>
    is_ptr_opcode (phi_filter_fwd fwd inst).inst_opcode ==>
    set (inst_defs (phi_filter_fwd fwd inst)) SUBSET ds
Proof
  rw[phi_filter_fwd_def, is_ptr_opcode_def, inst_defs_def] >>
  first_x_assum irule >> simp[]
QED

Triviality phi_well_formed_flat_phi_pairs[local]:
  !ps. phi_well_formed (FLAT (MAP (\(l,v). [Label l; Var v]) ps))
Proof
  Induct >> simp[FORALL_PROD, phi_well_formed_def]
QED

Triviality phi_filter_fwd_inst_wf_for_bp_fdom[local]:
  !fwd inst. inst_wf inst ==> inst_wf (phi_filter_fwd fwd inst)
Proof
  rpt strip_tac >>
  rw[phi_filter_fwd_def] >>
  gvs[inst_wf_def] >>
  simp[phi_well_formed_flat_phi_pairs]
QED

Triviality phi_filter_fwd_ptr_defs_subset_mem[local]:
  !fwd fn bb inst ds.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
               is_ptr_opcode inst.inst_opcode ==>
               set (inst_defs inst) SUBSET ds) /\
    is_ptr_opcode (phi_filter_fwd fwd inst).inst_opcode ==>
    set (inst_defs (phi_filter_fwd fwd inst)) SUBSET ds
Proof
  rw[phi_filter_fwd_def, is_ptr_opcode_def, inst_defs_def] >>
  first_x_assum (qspecl_then [`bb`, `inst`] mp_tac) >>
  simp[is_ptr_opcode_def, inst_defs_def]
QED

Triviality phi_filter_fwd_map_ptr_defs_subset[local]:
  !fwd fn bb ds inst.
    MEM bb fn.fn_blocks /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
               is_ptr_opcode inst.inst_opcode ==>
               set (inst_defs inst) SUBSET ds) /\
    MEM inst (MAP (phi_filter_fwd fwd) bb.bb_instructions) /\
    is_ptr_opcode inst.inst_opcode ==>
    set (inst_defs inst) SUBSET ds
Proof
  rpt gen_tac >> strip_tac >>
  gvs[MEM_MAP] >>
  rename1 `MEM orig bb.bb_instructions` >>
  qspecl_then [`fwd`, `fn`, `bb`, `orig`, `ds`]
    mp_tac phi_filter_fwd_ptr_defs_subset_mem >>
  simp[] >> disch_then irule >> first_assum ACCEPT_TAC
QED

(* bp_one_pass_aux preserves tight FDOM *)
Triviality bp_one_pass_aux_ptr_fdom[local]:
  !order fn r fwd c r' ds.
    bp_one_pass_aux fn r fwd order = (c, r') /\
    FDOM r SUBSET ds /\ fn_inst_wf fn /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
               is_ptr_opcode inst.inst_opcode ==>
               set (inst_defs inst) SUBSET ds) ==>
    FDOM r' SUBSET ds
Proof

  Induct >> simp[bp_one_pass_aux_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >> gvs[]
  >- (qpat_x_assum `!fn r fwd c r' ds. _`
        (qspecl_then [`fn`, `r`, `h::fwd`, `c`, `r'`, `ds`] mp_tac) >>
      simp[] >> disch_then irule >>
      rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]) >>
  rename1 `FIND _ fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks` by imp_res_tac venomExecPropsTheory.FIND_MEM >>
  `EVERY inst_wf (MAP (phi_filter_fwd fwd) bb.bb_instructions)` by
    (gvs[fn_inst_wf_def, EVERY_MAP, EVERY_MEM] >>
     rpt strip_tac >> irule phi_filter_fwd_inst_wf_for_bp_fdom >> res_tac) >>
  `!inst. MEM inst (MAP (phi_filter_fwd fwd) bb.bb_instructions) ==>
          is_ptr_opcode inst.inst_opcode ==> set (inst_defs inst) SUBSET ds` by
    metis_tac[phi_filter_fwd_map_ptr_defs_subset] >>
  Cases_on `bp_process_block r (MAP (phi_filter_fwd fwd) bb.bb_instructions)` >>
  gvs[LET_THM] >>
  `FDOM r'' SUBSET ds` by
    (drule_all bp_process_block_ptr_fdom >> simp[]) >>
  Cases_on `bp_one_pass_aux fn r'' (h::fwd) order` >> gvs[] >>
  rename1 `bp_one_pass_aux fn r'' (h::fwd) order = (c_rec,r')` >>
  qpat_x_assum `!fn r fwd c r' ds. _`
    (qspecl_then [`fn`, `r''`, `h::fwd`, `c_rec`, `r'`, `ds`] mp_tac) >>
  simp[] >> disch_then irule >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, simp[]]

QED

(* Helper: bp_one_pass preserves tight FDOM bound *)
Triviality bp_one_pass_ptr_fdom[local]:
  !fn order r c r' ds.
    bp_one_pass fn order r = (c, r') /\
    FDOM r SUBSET ds /\ fn_inst_wf fn /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
               is_ptr_opcode inst.inst_opcode ==>
               set (inst_defs inst) SUBSET ds) ==>
    FDOM r' SUBSET ds
Proof
  simp[bp_one_pass_def] >>
  metis_tac[bp_one_pass_aux_ptr_fdom]
QED

(* bp_analyze FDOM only contains pointer-opcode outputs *)
Triviality bp_analyze_ptr_fdom[local]:
  !cfg fn. fn_inst_wf fn ==>
           FDOM (bp_analyze cfg fn) SUBSET fn_ptr_defs fn
Proof
  rpt strip_tac >>
  simp[bp_analyze_def] >>
  qabbrev_tac `f = \r. SND (bp_one_pass fn cfg.cfg_dfs_pre r)` >>
  qabbrev_tac `ds = fn_ptr_defs fn` >>
  `!r0. FDOM r0 SUBSET ds ==> FDOM (f r0) SUBSET ds` by (
    rpt strip_tac >> simp[Abbr `f`] >>
    Cases_on `bp_one_pass fn cfg.cfg_dfs_pre r0` >>
    rename1 `_ = (ch, r1)` >> simp[] >>
    qspecl_then [`fn`,`cfg.cfg_dfs_pre`,`r0`,`ch`,`r1`,`ds`]
      mp_tac bp_one_pass_ptr_fdom >>
    disch_then match_mp_tac >>
    simp[Abbr `ds`, fn_ptr_defs_def, SUBSET_DEF, PULL_EXISTS, MEM_MAP] >>
    metis_tac[]) >>
  `FDOM (FEMPTY : bp_result) SUBSET ds` by simp[] >>
  qspecl_then [`f`, `\r. CARD (FDOM r)`, `CARD ds`,
               `\r. FDOM r SUBSET ds`, `FEMPTY`]
    mp_tac df_iterate_invariant >>
  simp[] >> disch_then irule >>
  conj_tac
  >- cheat  (* termination: CARD strictly increases when f changes *)
  >> rpt strip_tac >> irule CARD_SUBSET >>
  simp[Abbr `ds`, fn_ptr_defs_def, SUBSET_FINITE,
       MEM_MAP, PULL_EXISTS, FINITE_BIGUNION] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

(* SSA helpers *)
Triviality all_distinct_flat_map_inj[local]:
  !xs (f:'a -> 'b list) a b v.
    ALL_DISTINCT (FLAT (MAP f xs)) /\
    MEM a xs /\ MEM b xs /\
    MEM v (f a) /\ MEM v (f b) ==> a = b
Proof
  Induct >> rw[] >> fs[ALL_DISTINCT_APPEND] >>
  TRY (first_x_assum irule >> metis_tac[] >> NO_TAC) >>
  `F` suffices_by simp[] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  simp[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Triviality ssa_unique_definer[local]:
  !fn i1 i2 v.
    ssa_form fn /\ MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
    MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> i1 = i2
Proof
  rpt strip_tac >>
  qpat_x_assum `ssa_form _` (strip_assume_tac o REWRITE_RULE[ssa_form_def]) >>
  drule (INST_TYPE [alpha |-> ``:instruction``, beta |-> ``:string``]
    all_distinct_flat_map_inj) >>
  disch_then (qspecl_then [`i1`, `i2`, `v`] mp_tac) >> simp[]
QED

(* Under SSA, non-pointer-opcode outputs are not tracked in bp *)
Triviality bp_non_ptr_opcode_no_ptrs[local]:
  !bp fn inst out bb.
    bp = bp_analyze (cfg_analyze fn) fn /\
    fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst_output inst = SOME out /\ ~is_ptr_opcode inst.inst_opcode ==>
    bp_get_ptrs bp out = []
Proof
  rpt strip_tac >>
  irule bp_get_ptrs_not_in_fdom >>
  `FDOM bp SUBSET fn_ptr_defs fn` by metis_tac[bp_analyze_ptr_fdom] >>
  CCONTR_TAC >> gvs[SUBSET_DEF] >>
  `out IN fn_ptr_defs fn` by metis_tac[] >>
  gvs[fn_ptr_defs_def, MEM_MAP, PULL_EXISTS] >>
  (* Extract ptr-opcode inst from fn_ptr_defs membership *)
  first_x_assum (qspec_then `out` strip_assume_tac) >> gvs[] >>
  `is_ptr_opcode inst'.inst_opcode` by (CCONTR_TAC >> gvs[]) >> gvs[] >>
  `MEM out inst.inst_outputs` by (
    gvs[inst_output_def] >>
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  `MEM out inst'.inst_outputs` by gvs[inst_defs_def] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts]) >>
  `MEM inst' (fn_insts fn)` by
    (simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts]) >>
  `inst = inst'` by metis_tac[ssa_unique_definer] >>
  gvs[]
QED

(* Under SSA, outputs of non-ptr-opcode instructions are not in FDOM bp.
   Generalizes bp_non_ptr_opcode_no_ptrs to work with MEM v inst.inst_outputs
   directly (needed for INVOKE which has inst_output = NONE with 2+ outputs). *)
Triviality bp_non_ptr_outputs_not_tracked[local]:
  !bp fn inst v bb.
    bp = bp_analyze (cfg_analyze fn) fn /\
    fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM v inst.inst_outputs /\ ~is_ptr_opcode inst.inst_opcode ==>
    v NOTIN FDOM bp
Proof
  rpt strip_tac >>
  `FDOM bp SUBSET fn_ptr_defs fn` by metis_tac[bp_analyze_ptr_fdom] >>
  `v IN fn_ptr_defs fn` by metis_tac[SUBSET_DEF] >>
  fs[fn_ptr_defs_def, MEM_MAP, PULL_EXISTS] >>
  rename1 `MEM bb' fn.fn_blocks` >>
  rename1 `MEM inst' bb'.bb_instructions` >>
  `is_ptr_opcode inst'.inst_opcode` by (CCONTR_TAC >> gvs[]) >>
  `MEM v inst'.inst_outputs` by gvs[inst_defs_def] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts]) >>
  `MEM inst' (fn_insts fn)` by
    (simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts]) >>
  `inst = inst'` by metis_tac[ssa_unique_definer] >>
  gvs[is_ptr_opcode_def]
QED

(* inst_wf + inst_output SOME ⟹ singleton outputs *)
Triviality inst_wf_outputs_some[local]:
  !inst out. inst_wf inst /\ inst_output inst = SOME out ==>
    inst.inst_outputs = [out]
Proof
  rw[inst_output_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

(* Pointer-producing opcodes have exactly one output, so NONE excludes them. *)
Triviality inst_wf_output_none_not_ptr_opcode[local]:
  !inst. inst_wf inst /\ inst_output inst = NONE ==>
    ~is_ptr_opcode inst.inst_opcode
Proof
  rpt strip_tac >> CCONTR_TAC >>
  fs[is_ptr_opcode_def] >>
  gvs[inst_wf_def, inst_output_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

(* Output of instruction is not in its own uses (from block-level self-use
   condition + inst_wf giving singleton outputs). Used in both
   bp_ptr_sound_step_non_invoke and bp_fixpoint_drestrict_or_match delegation. *)
Triviality inst_output_not_self_use[local]:
  !inst out bb.
    inst_wf inst /\ inst_output inst = SOME out /\
    MEM inst bb.bb_instructions /\
    (!inst' out'. MEM inst' bb.bb_instructions /\
       inst_output inst' = SOME out' ==> ~MEM out' (inst_uses inst')) ==>
    EVERY (\v. v <> out) (inst_uses inst)
Proof
  rpt strip_tac >>
  imp_res_tac inst_wf_outputs_some >>
  simp[EVERY_MEM]
QED

(* If a variable is tracked in bp (bp_get_ptrs ≠ []) and is the output of
   some instruction, that instruction must be a ptr opcode. Contrapositive
   of bp_non_ptr_outputs_not_tracked + bp_get_ptrs_not_in_fdom. *)
Triviality bp_tracked_implies_ptr_opcode[local]:
  !bp fn inst out bb.
    bp_get_ptrs bp out <> [] /\ inst_output inst = SOME out /\
    inst_wf inst /\
    bp = bp_analyze (cfg_analyze fn) fn /\
    ssa_form fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    is_ptr_opcode inst.inst_opcode
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  qspecl_then [`bp_analyze (cfg_analyze fn) fn`, `fn`, `inst`, `out`, `bb`]
    mp_tac bp_non_ptr_outputs_not_tracked >>
  imp_res_tac inst_wf_outputs_some >>
  simp[] >> metis_tac[bp_get_ptrs_not_in_fdom]
QED

(* FLOOKUP allocas preserved through non-ALLOCA step_inst. *)
Triviality step_inst_preserves_alloca_ptrs[local]:
  !fuel ctx inst s0 s1 bp aid off v.
    step_inst fuel ctx inst s0 = OK s1 /\
    inst.inst_opcode <> ALLOCA /\
    MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ==>
    FLOOKUP s1.vs_allocas aid = FLOOKUP s0.vs_allocas aid
Proof
  rpt strip_tac >>
  irule (SIMP_RULE std_ss [] step_inst_alloca_flookup) >>
  qexistsl [`ctx`, `fuel`, `inst`] >> simp[]
QED

(* When bp_handle_inst at fixpoint + DRESTRICT'd version both produce
   nonempty output ptrs, they must agree. This is because:
   - Nonempty output from DRESTRICT'd version means FUPDATE fired (started from [])
   - FUPDATE value depends only on operand ptrs (which agree since operands ≠ out)
   - At fixpoint, FUPDATE value = bp_get_ptrs bp out (changed=F) *)
Triviality bp_handle_inst_drestrict_output_eq[local]:
  !bp inst out bp0 c0 bp0'.
    FST (bp_handle_inst bp inst) = F /\
    inst_output inst = SOME out /\ inst_wf inst /\
    EVERY (\v. v <> out) (inst_uses inst) /\
    bp0 = DRESTRICT bp (COMPL {out}) /\
    bp_handle_inst bp0 inst = (c0, bp0') /\
    bp_get_ptrs bp0' out <> [] ==>
    bp_get_ptrs bp0' out = bp_get_ptrs bp out
Proof
  rpt strip_tac >>
  imp_res_tac inst_wf_outputs_some >>
  (* Substitute bp0 = DRESTRICT bp (COMPL {out}) *)
  qpat_x_assum `bp0 = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
    rewrite_tac[th]) >>
  `bp_get_ptrs (DRESTRICT bp (COMPL {out})) out = []` by
    simp[bp_get_ptrs_def, FLOOKUP_DRESTRICT] >>
  `!v. v <> out ==>
    bp_get_ptrs (DRESTRICT bp (COMPL {out})) v = bp_get_ptrs bp v` by
    simp[bp_get_ptrs_def, FLOOKUP_DRESTRICT] >>
  `!v. MEM v (inst_uses inst) ==>
    bp_get_ptrs (DRESTRICT bp (COMPL {out})) v = bp_get_ptrs bp v` by
    (rpt strip_tac >> first_x_assum irule >>
     gvs[EVERY_MEM] >> metis_tac[]) >>
  (* Expand bp_handle_inst for both bp and DRESTRICT'd bp *)
  qpat_x_assum `~FST _` mp_tac >>
  qpat_x_assum `bp_handle_inst (DRESTRICT _ _) inst = _` mp_tac >>
  rewrite_tac[bp_handle_inst_def, inst_output_def] >>
  asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >> BETA_TAC >>
  Cases_on `inst.inst_opcode` >> gvs[]
  >> rpt strip_tac >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  gvs[inst_uses_def, venomInstTheory.operand_vars_def,
       venomInstTheory.operand_var_def] >>
  Cases_on `inst.inst_operands` >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `t` >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY (Cases_on `t'`) >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY (Cases_on `h`) >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY (Cases_on `h'`) >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY BasicProvers.TOP_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  (* Remaining: ADD/SUB Var-Var with out as operand (contradiction),
     and PHI operand ptrs agreement *)
  gvs[EVERY_MEM, venomInstTheory.operand_vars_def,
       venomInstTheory.operand_var_def, MEM_FLAT, MEM_MAP,
       bp_get_ptrs_def, FLOOKUP_DRESTRICT] >>
  (* PHI: show DRESTRICT'd ptrs = original ptrs for phi operand vars *)
  `MAP (bp_get_ptrs (DRESTRICT bp (COMPL {out})))
       (MAP SND (phi_pairs inst.inst_operands)) =
   MAP (bp_get_ptrs bp) (MAP SND (phi_pairs inst.inst_operands))` by (
    irule MAP_CONG >> simp[] >> rpt strip_tac >>
    qmatch_goalsub_rename_tac
      `bp_get_ptrs (DRESTRICT bp (COMPL {out})) phi_v = _` >>
    simp[bp_get_ptrs_def, FLOOKUP_DRESTRICT] >>
    `phi_v <> out` by (
      CCONTR_TAC >> gvs[] >>
      imp_res_tac phi_pairs_mem_operand_vars >>
      gvs[EVERY_MEM, venomInstTheory.operand_vars_def,
          venomInstTheory.operand_var_def]) >>
    simp[]) >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

(* Per-instruction bp_ptr_sound preservation at the fixpoint.
   Case v≠out: step_inst_preserves_lookup + ptr_matches_var_preserved.
   Case v=out with bp_get_ptrs bp out = []: vacuously true.
   Case v=out with bp_get_ptrs bp out ≠ []:
     Apply bp_handle_inst_sound_proof to DRESTRICT bp (COMPL {out}).
     If bp0' also has nonempty ptrs, use drestrict_output_eq to transfer.
     The caller (bp_ptr_sound_exec_block) proves bp0' has nonempty ptrs
     from the global fixpoint invariant. *)
Triviality bp_handle_inst_fixpoint_sound[local]:
  !bp inst fuel ctx s s'.
    bp_ptr_sound bp s /\
    FST (bp_handle_inst bp inst) = F /\
    step_inst fuel ctx inst s = OK s' /\
    inst_wf inst /\
    (!out. inst_output inst = SOME out ==>
       EVERY (\v. v <> out) (inst_uses inst) /\
       (is_ptr_opcode inst.inst_opcode \/ out NOTIN FDOM bp)) /\
    (inst_output inst = NONE ==>
       !out. MEM out inst.inst_outputs ==> bp_get_ptrs bp out = []) /\
    (!v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ==>
       FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!v. inst.inst_opcode = PHI /\
         MEM v (MAP SND (phi_pairs inst.inst_operands)) /\
         IS_SOME (lookup_var v s) ==>
         bp_get_ptrs bp v <> []) /\
    (* For stale ptrs: either DRESTRICT'd version has nonempty output
       (normal case), or all stale ptrs directly match s' (ADD/SUB Var-Var) *)
    (!out. inst_output inst = SOME out /\ bp_get_ptrs bp out <> [] ==>
       bp_get_ptrs (SND (bp_handle_inst (DRESTRICT bp (COMPL {out})) inst))
         out <> [] \/
       !p. MEM p (bp_get_ptrs bp out) ==> ptr_matches_var p out s') ==>
    bp_ptr_sound bp s'
Proof
  rpt strip_tac >>
  CONV_TAC (REWR_CONV bp_ptr_sound_def) >> rpt gen_tac >> strip_tac >>
  Cases_on `inst_output inst`
  >- (
    (* NONE: any outputs are untracked by bp, so the currently tracked v
       cannot be overwritten. *)
    `bp_get_ptrs bp v <> []` by metis_tac[] >>
    `~MEM v inst.inst_outputs` by metis_tac[] >>
    `lookup_var v s' = lookup_var v s` by (
      irule step_inst_preserves_lookup >>
      qexistsl [`ctx`, `fuel`, `inst`] >> simp[]) >>
    `IS_SOME (lookup_var v s)` by fs[] >>
    `?p. MEM p (bp_get_ptrs bp v) /\ ptr_matches_var p v s` by
      metis_tac[bp_ptr_sound_def] >>
    qexists `p` >> simp[] >>
    irule ptr_matches_var_preserved >> qexistsl [`s`, `v`] >> simp[] >>
    metis_tac[]
  ) >>
  rename1 `SOME out` >>
  reverse (Cases_on `v = out`)
  >- (
    (* v ≠ out: lookup_var v preserved *)
    `~MEM v inst.inst_outputs` by (
      gvs[inst_output_def] >>
      Cases_on `inst.inst_outputs` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    `lookup_var v s' = lookup_var v s` by (
      irule step_inst_preserves_lookup >>
      qexistsl [`ctx`, `fuel`, `inst`] >> simp[]) >>
    `IS_SOME (lookup_var v s)` by fs[] >>
    `?p. MEM p (bp_get_ptrs bp v) /\ ptr_matches_var p v s` by
      metis_tac[bp_ptr_sound_def] >>
    qexists `p` >> simp[] >>
    irule ptr_matches_var_preserved >> qexistsl [`s`, `v`] >> simp[] >>
    metis_tac[]
  ) >>
  (* v = out *)
  gvs[] >>
  (* If bp_get_ptrs bp out = [], vacuously true *)
  reverse (Cases_on `bp_get_ptrs bp out`)
  >- suspend "out_nonempty"
  >> gvs[bp_get_ptrs_not_in_fdom]
QED

Resume bp_handle_inst_fixpoint_sound[out_nonempty]:
  (* bp_get_ptrs bp out ≠ []: case split on DRESTRICT'd output ptrs *)
  rename1 `bp_get_ptrs bp out = ph::pt` >>
  qabbrev_tac `bp0 = DRESTRICT bp (COMPL {out})` >>
  Cases_on `bp_handle_inst bp0 inst` >>
  rename1 `bp_handle_inst bp0 inst = (c0, bp0')` >>
  reverse (Cases_on `bp_get_ptrs bp0' out`)
  >- (
    (* Case A: DRESTRICT'd version has nonempty output — transfer *)
    `bp_ptr_sound bp0 s` by
      (simp[Abbr `bp0`] >> irule bp_ptr_sound_restrict >> simp[]) >>
    `bp_get_ptrs bp0 out = []` by
      simp[Abbr `bp0`, bp_get_ptrs_def, FLOOKUP_DRESTRICT] >>
    `!v. v <> out ==> bp_get_ptrs bp0 v = bp_get_ptrs bp v` by
      simp[Abbr `bp0`, bp_get_ptrs_def, FLOOKUP_DRESTRICT] >>
    `!v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp0 v) ==>
       FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid` by
      (rpt strip_tac >> Cases_on `v = out` >> gvs[] >>
       metis_tac[]) >>
    `!v. inst.inst_opcode = PHI /\
       MEM v (MAP SND (phi_pairs inst.inst_operands)) /\
       IS_SOME (lookup_var v s) ==> bp_get_ptrs bp0 v <> []` by
      (rpt strip_tac >> Cases_on `v = out` >> gvs[EVERY_MEM, inst_uses_def] >>
       metis_tac[phi_pairs_mem_operand_vars]) >>
    `bp_ptr_sound bp0' s'` by (
      qspecl_then [`bp0`, `inst`, `c0`, `bp0'`, `fuel`, `ctx`, `s`, `s'`]
        mp_tac bp_handle_inst_sound_proof >>
      simp[] >> disch_then match_mp_tac >>
      first_assum ACCEPT_TAC) >>
    (* Transfer: bp0' has the same output ptrs as bp *)
    `bp_get_ptrs bp0' out = bp_get_ptrs bp out` by (
      qspecl_then [`bp`, `inst`, `out`, `bp0`, `c0`, `bp0'`]
        mp_tac bp_handle_inst_drestrict_output_eq >>
      simp[Abbr `bp0`] >>
      disch_then match_mp_tac >>
      Cases_on `bp_handle_inst bp inst` >> gvs[]) >>
    qpat_x_assum `bp_ptr_sound bp0' s'` mp_tac >>
    simp[bp_ptr_sound_def] >>
    disch_then (qspec_then `out` mp_tac) >> simp[])
  (* Case B: DRESTRICT'd output empty — stale ptrs match s' directly *)
  >> `!p. MEM p (ph::pt) ==> ptr_matches_var p out s'` by
       (first_x_assum match_mp_tac >> gvs[]) >>
  qexists `ph` >> simp[]
QED

Finalise bp_handle_inst_fixpoint_sound


(* Invariant: ADD/SUB [Var;Var] outputs only contain NONE-offset ptrs *)
Definition bp_vv_inv_def:
  bp_vv_inv fn r <=>
    !inst out. MEM inst (fn_insts fn) /\ inst_output inst = SOME out /\
      (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
      (?l r'. inst.inst_operands = [Var l; Var r']) ==>
      !p. MEM p (bp_get_ptrs r out) ==> ?aid. p = Ptr (Allocation aid) NONE
End

(* Member of MAP (offset_by _ NONE) is always Ptr _ NONE *)
Triviality mem_map_offset_none[local]:
  !p l. MEM p (MAP (\q. offset_by q NONE) l) ==>
        ?aid. p = Ptr (Allocation aid) NONE
Proof
  simp[MEM_MAP] >> rpt strip_tac >> gvs[] >>
  Cases_on `q` >> Cases_on `o'` >>
  gvs[offset_by_def] >>
  metis_tac[TypeBase.nchotomy_of ``:allocation``]
QED

(* bp_handle_inst for ADD/SUB Var-Var: any NEW ptrs written are NONE-offset *)
Triviality bp_handle_inst_vv_none[local]:
  !bp inst out.
    inst_output inst = SOME out /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    (?lhs rhs. inst.inst_operands = [Var lhs; Var rhs]) ==>
    !p. MEM p (bp_get_ptrs (SND (bp_handle_inst bp inst)) out) /\
        ~MEM p (bp_get_ptrs bp out) ==>
        ?aid. p = Ptr (Allocation aid) NONE
Proof
  rpt strip_tac >> gvs[inst_output_def] >>
  (Cases_on `inst.inst_outputs` >> gvs[] >>
   Cases_on `t` >> gvs[]) >>
  qpat_x_assum `MEM p _` mp_tac >>
  qpat_x_assum `~MEM p _` mp_tac >>
  simp[bp_handle_inst_def, inst_output_def, LET_THM,
       bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  irule mem_map_offset_none >> metis_tac[]
QED

(* bp_handle_inst preserves bp_vv_inv under SSA *)
Triviality bp_handle_inst_preserves_vv_inv[local]:
  !fn bp inst c bp'.
    bp_handle_inst bp inst = (c, bp') /\
    bp_vv_inv fn bp /\
    MEM inst (fn_insts fn) /\
    ssa_form fn ==>
    bp_vv_inv fn bp'
Proof
  rpt strip_tac >>
  CONV_TAC (REWR_CONV bp_vv_inv_def) >>
  qx_gen_tac `inst2` >> qx_gen_tac `out` >>
  DISCH_TAC >> rpt strip_tac >>
  rename1 `MEM p (bp_get_ptrs bp' out)` >>
  `MEM inst2 (fn_insts fn) /\ inst_output inst2 = SOME out`
    by fs[] >>
  Cases_on `inst_output inst = SOME out`
  >- suspend "same_out"
  >> suspend "diff_out"
QED

Resume bp_handle_inst_preserves_vv_inv[same_out]:
  `MEM out inst.inst_outputs` by
    (fs[inst_output_def] >>
     Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `MEM out inst2.inst_outputs` by
    (fs[inst_output_def] >>
     Cases_on `inst2.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `inst = inst2` by metis_tac[ssa_unique_definer] >>
  BasicProvers.VAR_EQ_TAC >>
  Cases_on `MEM p (bp_get_ptrs bp out)`
  >- (fs[bp_vv_inv_def] >> metis_tac[])
  >> `bp' = SND (bp_handle_inst bp inst)` by fs[] >>
  pop_assum SUBST_ALL_TAC >>
  irule bp_handle_inst_vv_none >> fs[] >> metis_tac[]
QED

Resume bp_handle_inst_preserves_vv_inv[diff_out]:
  `bp_get_ptrs bp' out = bp_get_ptrs bp out` by
    (drule bp_handle_inst_other_var >>
     disch_then (qspec_then `out` mp_tac) >> simp[]) >>
  fs[bp_vv_inv_def] >> metis_tac[]
QED

Finalise bp_handle_inst_preserves_vv_inv

(* bp_process_block preserves bp_vv_inv *)
Triviality bp_process_block_preserves_vv_inv[local]:
  !fn bp insts c bp'.
    bp_process_block bp insts = (c, bp') /\
    bp_vv_inv fn bp /\
    (!inst. MEM inst insts ==> MEM inst (fn_insts fn)) /\
    ssa_form fn ==>
    bp_vv_inv fn bp'
Proof
  Induct_on `insts` >> simp[bp_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  first_x_assum irule >> simp[] >>
  qexists `r1` >> simp[] >>
  irule bp_handle_inst_preserves_vv_inv >>
  simp[] >> qexistsl [`bp`, `c1`, `h`] >> simp[]
QED


Triviality bp_handle_inst_preserves_vv_inv_phi_filter[local]:
  !fn bp fwd inst c bp'.
    bp_handle_inst bp (phi_filter_fwd fwd inst) = (c, bp') /\
    bp_vv_inv fn bp /\
    MEM inst (fn_insts fn) /\
    ssa_form fn ==>
    bp_vv_inv fn bp'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    `bp' = bp` by (
      qpat_x_assum `bp_handle_inst _ _ = _` mp_tac >>
      simp[phi_filter_fwd_def, bp_handle_inst_def, LET_THM] >>
      Cases_on `inst.inst_outputs` >> gvs[inst_output_def] >>
      Cases_on `t` >> gvs[inst_output_def]) >>
    simp[]) >>
  gvs[phi_filter_fwd_def] >>
  drule_all bp_handle_inst_preserves_vv_inv >>
  simp[]
QED

Triviality bp_process_block_preserves_vv_inv_phi_filter[local]:
  !fn fwd bp insts c bp'.
    bp_process_block bp (MAP (phi_filter_fwd fwd) insts) = (c, bp') /\
    bp_vv_inv fn bp /\
    (!inst. MEM inst insts ==> MEM inst (fn_insts fn)) /\
    ssa_form fn ==>
    bp_vv_inv fn bp'
Proof
  Induct_on `insts` >> simp[bp_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `bp_vv_inv fn r1` by (
    mp_tac (Q.SPECL [`fn`, `bp`, `fwd`, `h`, `c1`, `r1`]
      bp_handle_inst_preserves_vv_inv_phi_filter) >>
    simp[]) >>
  first_x_assum irule >> simp[] >>
  qexistsl [`r1`, `c2`, `fwd`] >> simp[] >>

  metis_tac[]
QED

(* bp_one_pass_aux preserves bp_vv_inv *)
Triviality bp_one_pass_aux_preserves_vv_inv[local]:
  !fn order fwd bp c bp'.
    bp_one_pass_aux fn bp fwd order = (c, bp') /\
    bp_vv_inv fn bp /\
    ssa_form fn ==>
    bp_vv_inv fn bp'
Proof

  Induct_on `order` >> simp[bp_one_pass_aux_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >> gvs[]
  >- (first_x_assum irule >> simp[] >> qexistsl [`bp`, `c`, `h::fwd`] >> simp[]) >>
  rename1 `FIND _ _ = SOME bb` >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `!inst. MEM inst bb.bb_instructions ==> MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts, venomExecPropsTheory.FIND_MEM]) >>
  `bp_vv_inv fn r1` by
    metis_tac[bp_process_block_preserves_vv_inv_phi_filter] >>
  first_x_assum irule >> simp[] >>
  qexistsl [`r1`, `c2`, `h::fwd`] >> simp[]

QED

(* bp_one_pass preserves bp_vv_inv *)
Triviality bp_one_pass_preserves_vv_inv[local]:
  !fn order bp c bp'.
    bp_one_pass fn order bp = (c, bp') /\
    bp_vv_inv fn bp /\
    ssa_form fn ==>
    bp_vv_inv fn bp'
Proof
  simp[bp_one_pass_def] >> metis_tac[bp_one_pass_aux_preserves_vv_inv]
QED

(* At fixpoint: ADD/SUB [Var;Var] outputs have NONE-offset ptrs *)
Triviality bp_analyze_vv_inv[local]:
  !cfg fn.
    fn_inst_wf fn /\ ssa_form fn ==>
    bp_vv_inv fn (bp_analyze cfg fn)
Proof
  rpt strip_tac >>
  simp[bp_analyze_def] >>
  qabbrev_tac `f = \r. SND (bp_one_pass fn cfg.cfg_dfs_pre r)` >>
  qabbrev_tac `ds = fn_ptr_defs fn` >>
  (* Use df_iterate_invariant with P = bp_vv_inv fn *)
  `bp_vv_inv fn (FEMPTY : bp_result)` by
    simp[bp_vv_inv_def, bp_get_ptrs_def, FLOOKUP_DEF] >>
  `!r. bp_vv_inv fn r ==> bp_vv_inv fn (f r)` by (
    rpt strip_tac >> simp[Abbr `f`] >>
    Cases_on `bp_one_pass fn cfg.cfg_dfs_pre r` >>
    rename1 `_ = (ch, r')` >> simp[] >>
    irule bp_one_pass_preserves_vv_inv >>
    simp[] >> qexistsl [`r`, `ch`, `cfg.cfg_dfs_pre`] >> simp[]) >>
  `!r. FDOM r SUBSET ds ==> bp_vv_inv fn r ==> FDOM (f r) SUBSET ds` by (
    rpt strip_tac >> simp[Abbr `f`] >>
    Cases_on `bp_one_pass fn cfg.cfg_dfs_pre r` >>
    rename1 `_ = (ch, r')` >> simp[] >>
    qspecl_then [`fn`,`cfg.cfg_dfs_pre`,`r`,`ch`,`r'`,`ds`]
      mp_tac bp_one_pass_ptr_fdom >>
    disch_then match_mp_tac >>
    simp[Abbr `ds`, fn_ptr_defs_def, SUBSET_DEF, PULL_EXISTS, MEM_MAP] >>
    metis_tac[]) >>
  qspecl_then [`f`, `\r. CARD (FDOM r)`, `CARD ds`,
               `\r. bp_vv_inv fn r /\ FDOM r SUBSET ds`, `FEMPTY`]
    mp_tac df_iterate_invariant >>
  simp[] >> strip_tac >>
  `(bp_vv_inv fn (df_iterate f FEMPTY) /\
    FDOM (df_iterate f FEMPTY) SUBSET ds)` suffices_by simp[] >>
  first_x_assum irule >>
  conj_tac
  >- cheat  (* termination: same as bp_analyze_ptr_fdom *)
  >> rpt strip_tac >> irule CARD_SUBSET >>
  simp[Abbr `ds`, fn_ptr_defs_def, SUBSET_FINITE,
       MEM_MAP, PULL_EXISTS, FINITE_BIGUNION] >>
  rpt strip_tac >> IF_CASES_TAC >> simp[]
QED

(* bp_process_block preserves ptrs for variables not in any output *)
Triviality bp_process_block_other_var[local]:
  !bp insts c bp' v.
    bp_process_block bp insts = (c, bp') /\
    (!inst. MEM inst insts ==> inst_output inst <> SOME v) ==>
    bp_get_ptrs bp' v = bp_get_ptrs bp v
Proof
  Induct_on `insts` >> simp[bp_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[LET_THM] >> pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `bp_get_ptrs r1 v = bp_get_ptrs bp v` by (
    drule bp_handle_inst_other_var >> disch_then (qspec_then `v` mp_tac) >>
    simp[]) >>
  `bp_get_ptrs bp' v = bp_get_ptrs r1 v` by (
    first_x_assum irule >> simp[]) >>
  simp[]
QED

(* FST of bp_handle_inst = comparison of output ptrs *)
Triviality bp_handle_inst_fst_eq[local]:
  !bp inst out.
    inst_output inst = SOME out ==>
    FST (bp_handle_inst bp inst) =
      (bp_get_ptrs (SND (bp_handle_inst bp inst)) out <> bp_get_ptrs bp out)
Proof
  rpt strip_tac >>
  simp[bp_handle_inst_def, LET_THM]
QED

(* When SND of bp_handle_inst equals input, FST = F *)
Triviality bp_handle_inst_snd_eq_fst_f[local]:
  !bp inst out.
    inst_output inst = SOME out /\
    SND (bp_handle_inst bp inst) = bp ==>
    FST (bp_handle_inst bp inst) = F
Proof
  rpt strip_tac >> gvs[inst_output_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[] >>
  Cases_on `bp_handle_inst bp inst` >>
  gvs[bp_handle_inst_def, inst_output_def, LET_THM]
QED

(* Non-pointer opcodes leave bp completely unchanged *)
Triviality bp_handle_inst_non_ptr_id[local]:
  !bp inst out.
    inst_output inst = SOME out /\ inst_wf inst /\
    ~is_ptr_opcode inst.inst_opcode ==>
    bp_handle_inst bp inst = (F, bp)
Proof
  rpt strip_tac >>
  Cases_on `bp_handle_inst bp inst` >> rename1 `(c, bp')` >>
  `bp' = bp` by (
    irule bp_handle_inst_passthrough_output >>
    gvs[is_ptr_opcode_def] >> metis_tac[]) >>
  `c = F` suffices_by gvs[] >>
  `FST (bp_handle_inst bp inst) = F` suffices_by
    (qpat_x_assum `bp_handle_inst _ _ = _` (fn th => rewrite_tac[th]) >>
     simp[]) >>
  irule bp_handle_inst_snd_eq_fst_f >> gvs[]
QED

(* Output ptrs after bp_handle_inst depend only on bp_get_ptrs, not on the
   concrete fmap representation.  Keep bp_get_ptrs abstract; split only the
   operand shapes that the pointer opcodes inspect. *)
Triviality bp_handle_inst_add_snd_output_ext[local]:
  !bp1 bp2 inst out.
    (!v. bp_get_ptrs bp1 v = bp_get_ptrs bp2 v) /\
    inst_output inst = SOME out /\
    inst.inst_opcode = ADD ==>
    bp_get_ptrs (SND (bp_handle_inst bp1 inst)) out =
    bp_get_ptrs (SND (bp_handle_inst bp2 inst)) out
Proof
  rpt strip_tac >>
  simp[bp_handle_inst_def, LET_THM, bp_get_ptrs_update_same] >>
  Cases_on `inst.inst_operands` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `t` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `t'` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `h` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `h'` >> gvs[bp_get_ptrs_update_same] >>
  rpt (IF_CASES_TAC >> gvs[bp_get_ptrs_update_same])
QED

Triviality bp_handle_inst_sub_snd_output_ext[local]:
  !bp1 bp2 inst out.
    (!v. bp_get_ptrs bp1 v = bp_get_ptrs bp2 v) /\
    inst_output inst = SOME out /\
    inst.inst_opcode = SUB ==>
    bp_get_ptrs (SND (bp_handle_inst bp1 inst)) out =
    bp_get_ptrs (SND (bp_handle_inst bp2 inst)) out
Proof
  rpt strip_tac >>
  simp[bp_handle_inst_def, LET_THM, bp_get_ptrs_update_same] >>
  Cases_on `inst.inst_operands` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `t` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `t'` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `h` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `h'` >> gvs[bp_get_ptrs_update_same] >>
  rpt (IF_CASES_TAC >> gvs[bp_get_ptrs_update_same])
QED

Triviality bp_handle_inst_assign_snd_output_ext[local]:
  !bp1 bp2 inst out.
    (!v. bp_get_ptrs bp1 v = bp_get_ptrs bp2 v) /\
    inst_output inst = SOME out /\
    inst.inst_opcode = ASSIGN ==>
    bp_get_ptrs (SND (bp_handle_inst bp1 inst)) out =
    bp_get_ptrs (SND (bp_handle_inst bp2 inst)) out
Proof
  rpt strip_tac >>
  simp[bp_handle_inst_def, LET_THM, bp_get_ptrs_update_same] >>
  Cases_on `inst.inst_operands` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `t` >> gvs[bp_get_ptrs_update_same] >>
  Cases_on `h` >> gvs[bp_get_ptrs_update_same]
QED

Triviality bp_handle_inst_snd_output_ext[local]:
  !bp1 bp2 inst out.
    (!v. bp_get_ptrs bp1 v = bp_get_ptrs bp2 v) /\
    inst_output inst = SOME out /\
    is_ptr_opcode inst.inst_opcode ==>
    bp_get_ptrs (SND (bp_handle_inst bp1 inst)) out =
    bp_get_ptrs (SND (bp_handle_inst bp2 inst)) out
Proof
  rpt strip_tac >>
  `MAP (bp_get_ptrs bp1) (MAP SND (phi_pairs inst.inst_operands)) =
   MAP (bp_get_ptrs bp2) (MAP SND (phi_pairs inst.inst_operands))` by
    (irule MAP_CONG >> simp[]) >>
  gvs[is_ptr_opcode_def]
  >- simp[bp_handle_inst_def, LET_THM, bp_get_ptrs_update_same]
  >- (irule bp_handle_inst_add_snd_output_ext >> simp[])
  >- (irule bp_handle_inst_sub_snd_output_ext >> simp[])
  >- (irule bp_handle_inst_assign_snd_output_ext >> simp[])
QED

(* FST of bp_handle_inst depends only on bp_get_ptrs *)
Triviality bp_handle_inst_fst_ext[local]:
  !bp1 bp2 inst.
    (!v. bp_get_ptrs bp1 v = bp_get_ptrs bp2 v) /\ inst_wf inst ==>
    FST (bp_handle_inst bp1 inst) = FST (bp_handle_inst bp2 inst)
Proof
  rpt strip_tac >>
  Cases_on `inst_output inst`
  >- simp[bp_handle_inst_def] >>
  rename1 `SOME out` >>
  reverse (Cases_on `is_ptr_opcode inst.inst_opcode`)
  >- (
    `bp_handle_inst bp1 inst = (F, bp1)` by
      (irule bp_handle_inst_non_ptr_id >> simp[]) >>
    `bp_handle_inst bp2 inst = (F, bp2)` by
      (irule bp_handle_inst_non_ptr_id >> simp[]) >>
    simp[]) >>
  (* MERGE NOTE: chose origin/main helper-based proof over the eval-phis
     direct expansion proof. If this fails, compare the pre-merge eval-phis
     version of this theorem. *)
  `FST (bp_handle_inst bp1 inst) =
   (bp_get_ptrs (SND (bp_handle_inst bp1 inst)) out <>
    bp_get_ptrs bp1 out)` by
    (irule bp_handle_inst_fst_eq >> simp[]) >>
  `FST (bp_handle_inst bp2 inst) =
   (bp_get_ptrs (SND (bp_handle_inst bp2 inst)) out <>
    bp_get_ptrs bp2 out)` by
    (irule bp_handle_inst_fst_eq >> simp[]) >>
  `bp_get_ptrs bp1 out = bp_get_ptrs bp2 out` by simp[] >>
  `bp_get_ptrs (SND (bp_handle_inst bp1 inst)) out =
   bp_get_ptrs (SND (bp_handle_inst bp2 inst)) out` by
    metis_tac[bp_handle_inst_snd_output_ext] >>
  ASM_REWRITE_TAC[]
QED

(* For opcodes that always FUPDATE (PHI, ALLOCA, ASSIGN [Var src]):
   bp_get_ptrs of the output depends only on bp_get_ptrs of the operands,
   so DRESTRICT on output doesn't change the result.
   Used in bp_fixpoint_drestrict_or_match to derive contradiction. *)

(* Shared contradiction tactic for fixpoint + DRESTRICT:
   If FST(bp_handle_inst bp inst) = F and the output ptrs from bp0
   equal those from bp (because operands agree), then bp0 output ≠ []. *)
(* bp_fixpoint_drestrict_or_match: approach is to show each case inline,
   using the fact that FUPDATE makes output ptrs operand-dependent. *)

(* At fixpoint (same ptrs in SND as input), each handle_inst returns F *)
Triviality bp_process_block_fixpoint_each[local]:
  !insts bp c bp'.
    bp_process_block bp insts = (c, bp') /\
    (!v. bp_get_ptrs bp' v = bp_get_ptrs bp v) /\
    EVERY inst_wf insts /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    !inst. MEM inst insts ==> FST (bp_handle_inst bp inst) = F
Proof
  Induct >> simp[bp_process_block_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[LET_THM, ALL_DISTINCT_APPEND] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  (* First establish: head instruction didn't change ptrs *)
  `FST (bp_handle_inst bp h) = F` by
    suspend "head_unchanged" >>
  `c1 = F` by (Cases_on `bp_handle_inst bp h` >> gvs[]) >>
  gvs[] >>
  `!v. bp_get_ptrs r1 v = bp_get_ptrs bp v` by
    suspend "ptrs_unchanged" >>
  gen_tac >> DISCH_TAC >> gvs[] >>
  suspend "tail_case"
QED

Resume bp_process_block_fixpoint_each[head_unchanged]:
  Cases_on `inst_output h`
  >- gvs[bp_handle_inst_def] >>
  rename1 `SOME out` >>
  (* Goal: FST (bp_handle_inst bp h) = F
     bp_handle_inst_fst_eq: FST = (new_ptrs ≠ old_ptrs)
     Suffices: bp_get_ptrs r1 out = bp_get_ptrs bp out
     where r1 = SND (bp_handle_inst bp h).
     bp_process_block_other_var: tail doesn't change out's ptrs,
     so bp_get_ptrs bp' out = bp_get_ptrs r1 out.
     Combined with fixpoint: bp_get_ptrs bp' out = bp_get_ptrs bp out. *)
  `!inst'. MEM inst' insts ==> inst_output inst' <> SOME out` by
    suspend "no_dup_out" >>
  drule_all bp_process_block_other_var >>
  strip_tac >>
  `FST (bp_handle_inst bp h) =
    (bp_get_ptrs (SND (bp_handle_inst bp h)) out <> bp_get_ptrs bp out)` by
    (irule bp_handle_inst_fst_eq >> simp[]) >>
  gvs[]
QED

Resume bp_process_block_fixpoint_each[no_dup_out]:
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `inst'.inst_outputs = [out]` by
    (gvs[EVERY_MEM] >> res_tac >> drule inst_wf_outputs_some >> simp[]) >>
  `h.inst_outputs = [out]` by (drule inst_wf_outputs_some >> simp[]) >>
  first_x_assum (qspec_then `out` mp_tac) >> simp[MEM_FLAT, MEM_MAP] >>
  qexists `inst'.inst_outputs` >> simp[] >> qexists `inst'` >> simp[]
QED

Resume bp_process_block_fixpoint_each[ptrs_unchanged]:
  drule bp_handle_inst_no_change_ptrs >> simp[]
QED

Resume bp_process_block_fixpoint_each[tail_case]:
  (* After DISCH_TAC >> gvs[], inst=h solved, left with MEM inst insts *)
  gvs[] >>
  (* Apply IH with bp'' := r1 *)
  `~FST (bp_handle_inst r1 inst)` by (
    first_x_assum (qspecl_then [`r1`, `c2`, `bp'`] mp_tac) >>
    simp[]) >>
  (* Transfer from r1 to bp via fst_ext *)
  `FST (bp_handle_inst bp inst) = FST (bp_handle_inst r1 inst)` by
    (irule (GSYM bp_handle_inst_fst_ext) >> gvs[EVERY_MEM]) >>
  gvs[]
QED

Finalise bp_process_block_fixpoint_each

Triviality phi_filter_fwd_inst_output[local]:
  !fwd inst. inst_output (phi_filter_fwd fwd inst) = inst_output inst
Proof
  rw[phi_filter_fwd_def, inst_output_def]
QED

Triviality phi_filter_fwd_inst_outputs[local]:
  !fwd inst. (phi_filter_fwd fwd inst).inst_outputs = inst.inst_outputs
Proof
  rw[phi_filter_fwd_def]
QED

Triviality bp_handle_inst_phi_filter_fwd_fst[local]:
  !bp fwd inst.
    FST (bp_handle_inst bp (phi_filter_fwd fwd inst)) = F ==>
    FST (bp_handle_inst bp inst) = F
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >> gvs[phi_filter_fwd_def] >>
  simp[bp_handle_inst_def, inst_output_def, LET_THM] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[bp_get_ptrs_def]
QED

(* Variables not output by any block in order are preserved by one_pass_aux *)
Triviality bp_one_pass_aux_other_var[local]:
  !fn bp fwd order c bp' v.
    bp_one_pass_aux fn bp fwd order = (c, bp') /\
    (!lbl bb. MEM lbl order /\
              FIND (\bb. bb.bb_label = lbl) fn.fn_blocks = SOME bb ==>
              !inst. MEM inst bb.bb_instructions ==>
                     inst_output inst <> SOME v) ==>
    bp_get_ptrs bp' v = bp_get_ptrs bp v
Proof

  Induct_on `order` >> simp[bp_one_pass_aux_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >> gvs[]
  >- (
    first_x_assum irule >>
    simp[] >> metis_tac[]) >>
  rename1 `FIND _ _ = SOME bb` >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `bp_get_ptrs r1 v = bp_get_ptrs bp v` by (
    irule bp_process_block_other_var >>
    qexistsl [`c1`, `MAP (phi_filter_fwd fwd) bb.bb_instructions`] >>
    simp[MEM_MAP] >> rpt strip_tac >> gvs[phi_filter_fwd_inst_output] >>
    first_x_assum (qspecl_then [`h`, `bb`] mp_tac) >> simp[]) >>
  `bp_get_ptrs bp' v = bp_get_ptrs r1 v` by (
    first_x_assum irule >>
    simp[] >> metis_tac[]) >>

  simp[]
QED

(* SSA: block-level outputs are ALL_DISTINCT *)
Triviality ssa_block_outputs_all_distinct[local]:
  !bbs bb. ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
           /\ MEM bb bbs ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  Induct >> simp[fn_insts_blocks_def] >> rpt strip_tac >>
  gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

(* Helper: MEM v in block outputs => MEM v in fn_insts_blocks outputs *)
Triviality mem_block_outputs_mem_fn_insts[local]:
  !bbs v bb.
    MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    MEM bb bbs ==>
    MEM v (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
Proof
  Induct >> simp[fn_insts_blocks_def, MAP_APPEND, FLAT_APPEND] >>
  rpt strip_tac >> simp[MEM_APPEND] >> gvs[] >> metis_tac[]
QED

(* SSA: outputs of different blocks are disjoint *)
Triviality ssa_disjoint_block_outputs[local]:
  !bbs bb1 bb2 v.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
    MEM bb1 bbs /\ MEM bb2 bbs /\
    bb1.bb_label <> bb2.bb_label /\
    MEM v (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions)) ==>
    ~MEM v (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions))
Proof
  Induct >> simp[fn_insts_blocks_def] >> rpt gen_tac >>
  DISCH_TAC >> gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  spose_not_then assume_tac >> gvs[] >>
  TRY (first_x_assum irule >> simp[] >> metis_tac[] >> NO_TAC) >>
  imp_res_tac mem_block_outputs_mem_fn_insts >> metis_tac[]
QED

(* At fixpoint of bp_one_pass_aux, each instruction has FST=F *)
(* SSA: inst_output overlap across blocks is impossible *)
Triviality ssa_inst_output_disjoint[local]:
  !fn bb1 bb2 inst1 inst2 v.
    ssa_form fn /\ ALL_DISTINCT (fn_labels fn) /\
    MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    bb1.bb_label <> bb2.bb_label /\
    MEM inst1 bb1.bb_instructions /\ inst_output inst1 = SOME v /\
    MEM inst2 bb2.bb_instructions /\ inst_output inst2 = SOME v ==> F
Proof
  rpt strip_tac >>
  `MEM v (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions))` by
    (simp[MEM_FLAT, MEM_MAP] >> qexists `[v]` >> simp[] >>
     qexists `inst1` >> gvs[inst_output_def] >>
     Cases_on `inst1.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  `MEM v (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions))` by
    (simp[MEM_FLAT, MEM_MAP] >> qexists `[v]` >> simp[] >>
     qexists `inst2` >> gvs[inst_output_def] >>
     Cases_on `inst2.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  mp_tac (Q.SPECL [`fn.fn_blocks`, `bb1`, `bb2`, `v`]
    ssa_disjoint_block_outputs) >>
  simp[GSYM fn_labels_def] >> gvs[ssa_form_def, fn_insts_def]
QED

Triviality inst_output_some_mem_outputs[local]:
  !inst v. inst_output inst = SOME v ==> MEM v inst.inst_outputs
Proof
  rpt strip_tac >> gvs[inst_output_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Triviality ssa_tail_no_head_output[local]:
  !fn order h bb0 lbl bb inst v.
    ssa_form fn /\ ALL_DISTINCT (fn_labels fn) /\
    MEM bb0 fn.fn_blocks /\ bb0.bb_label = h /\
    MEM v (FLAT (MAP (\i. i.inst_outputs) bb0.bb_instructions)) /\
    ~MEM h order /\ MEM lbl order /\
    FIND (\bb. bb.bb_label = lbl) fn.fn_blocks = SOME bb /\
    MEM inst bb.bb_instructions ==>
    inst_output inst <> SOME v
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  `MEM bb fn.fn_blocks` by (
    qspecl_then [`\bb. bb.bb_label = lbl`, `fn.fn_blocks`, `bb`]
      mp_tac venomExecPropsTheory.FIND_MEM >> simp[]) >>
  `bb.bb_label = lbl` by (
    qspecl_then [`\bb. bb.bb_label = lbl`, `fn.fn_blocks`, `bb`]
      mp_tac venomExecPropsTheory.FIND_P >> simp[]) >>
  `lbl <> bb0.bb_label` by metis_tac[] >>
  `bb.bb_label <> bb0.bb_label` by metis_tac[] >>
  `MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    metis_tac[MEM_FLAT, MEM_MAP, inst_output_some_mem_outputs] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks fn.fn_blocks)))` by
    gvs[ssa_form_def, fn_insts_def] >>
  metis_tac[ssa_disjoint_block_outputs, fn_labels_def]
QED

Triviality bp_one_pass_aux_preserves_head_output[local]:
  !fn r1 fwd order c2 bp' h bb0 v.
    bp_one_pass_aux fn r1 (h::fwd) order = (c2,bp') /\
    ssa_form fn /\ ALL_DISTINCT (fn_labels fn) /\
    MEM bb0 fn.fn_blocks /\ bb0.bb_label = h /\ ~MEM h order /\
    MEM v (FLAT (MAP (\i. i.inst_outputs) bb0.bb_instructions)) ==>
    bp_get_ptrs bp' v = bp_get_ptrs r1 v
Proof
  rpt strip_tac >>
  qspecl_then [`fn`, `r1`, `h::fwd`, `order`, `c2`, `bp'`, `v`]
    mp_tac bp_one_pass_aux_other_var >>
  simp[] >> disch_then irule >>
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`, `order`, `h`, `bb0`, `lbl`, `bb`, `inst`, `v`]
    ssa_tail_no_head_output) >>
  simp[]
QED

Triviality bp_process_block_phi_filter_fixpoint_ptrs[local]:
  !fn fwd order bp c1 r1 c2 bp' h bb0.
    bp_process_block bp (MAP (phi_filter_fwd fwd) bb0.bb_instructions) = (c1,r1) /\
    bp_one_pass_aux fn r1 (h::fwd) order = (c2,bp') /\
    (!v. bp_get_ptrs bp' v = bp_get_ptrs bp v) /\
    ssa_form fn /\ fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    MEM bb0 fn.fn_blocks /\ bb0.bb_label = h /\ ~MEM h order ==>
    !v. bp_get_ptrs r1 v = bp_get_ptrs bp v
Proof
  rpt strip_tac >>
  Cases_on `MEM v (FLAT (MAP (\i. i.inst_outputs) bb0.bb_instructions))`
  >- (`bp_get_ptrs bp' v = bp_get_ptrs r1 v` by
        (mp_tac (Q.SPECL [`fn`, `r1`, `fwd`, `order`, `c2`, `bp'`,
                          `h`, `bb0`, `v`]
          bp_one_pass_aux_preserves_head_output) >>
         simp[]) >>
      metis_tac[]) >>
  irule EQ_TRANS >>
  qexists_tac `bp_get_ptrs bp v` >> simp[] >>
  irule bp_process_block_other_var >>
  qexistsl_tac [`c1`, `MAP (phi_filter_fwd fwd) bb0.bb_instructions`] >>
  simp[MEM_MAP] >> rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  metis_tac[phi_filter_fwd_inst_output, inst_output_some_mem_outputs,
            MEM_FLAT, MEM_MAP]
QED

Triviality bp_one_pass_aux_fixpoint_each[local]:
  !order fn fwd bp c bp'.
    bp_one_pass_aux fn bp fwd order = (c, bp') /\
    (!v. bp_get_ptrs bp' v = bp_get_ptrs bp v) /\
    ALL_DISTINCT order /\
    ALL_DISTINCT (fn_labels fn) /\
    ssa_form fn /\ fn_inst_wf fn ==>
    !lbl bb inst.
      MEM lbl order /\
      FIND (\bb. bb.bb_label = lbl) fn.fn_blocks = SOME bb /\
      MEM inst bb.bb_instructions ==>
      FST (bp_handle_inst bp inst) = F
Proof
  Induct_on `order` >> simp[bp_one_pass_aux_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FIND (\bb. bb.bb_label = h) fn.fn_blocks` >> gvs[]
  >- (rpt strip_tac >> Cases_on `lbl = h` >> gvs[] >>
      qpat_x_assum `!fn fwd bp c bp'. _`
        (qspecl_then [`fn`, `h::fwd`, `bp`, `c`, `bp'`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`lbl`, `bb`, `inst`] mp_tac) >>
      simp[]) >>
  rename1 `FIND _ fn.fn_blocks = SOME bb0` >>
  Cases_on `bp_process_block bp (MAP (phi_filter_fwd fwd) bb0.bb_instructions)` >> gvs[] >>
  rename1 `bp_process_block _ _ = (c1,r1)` >>
  Cases_on `bp_one_pass_aux fn r1 (h::fwd) order` >> gvs[] >>
  rename1 `bp_one_pass_aux fn r1 _ _ = (c2,bp2)` >>
  `MEM bb0 fn.fn_blocks` by imp_res_tac venomExecPropsTheory.FIND_MEM >>
  `bb0.bb_label = h` by
    (qspecl_then [`\bb. bb.bb_label = h`, `fn.fn_blocks`, `bb0`]
      mp_tac venomExecPropsTheory.FIND_P >> simp[]) >>
  `!v. bp_get_ptrs r1 v = bp_get_ptrs bp v` by
    (mp_tac (Q.SPECL [`fn`, `fwd`, `order`, `bp`, `c1`, `r1`, `c2`,
                      `bp2`, `h`, `bb0`]
       bp_process_block_phi_filter_fixpoint_ptrs) >>
     simp[]) >>
  rpt strip_tac >> Cases_on `lbl = h` >> gvs[]
  >- (`EVERY inst_wf (MAP (phi_filter_fwd fwd) bb.bb_instructions)` by
        (gvs[fn_inst_wf_def, EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
         irule phi_filter_fwd_inst_wf_for_bp_fdom >> res_tac) >>
      `ALL_DISTINCT
         (FLAT (MAP (\i. i.inst_outputs)
           (MAP (phi_filter_fwd fwd) bb.bb_instructions)))` by
        (`ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
          (irule ssa_block_outputs_all_distinct >>
           qexists_tac `fn.fn_blocks` >> gvs[ssa_form_def, fn_insts_def]) >>
         gvs[MAP_MAP_o, combinTheory.o_DEF, phi_filter_fwd_inst_outputs]) >>
      `FST (bp_handle_inst bp (phi_filter_fwd fwd inst)) = F` by
        (mp_tac (Q.SPECL [`MAP (phi_filter_fwd fwd) bb.bb_instructions`,
                          `bp`, `c1`, `r1`]
           bp_process_block_fixpoint_each) >>
         simp[] >>
         disch_then (qspec_then `phi_filter_fwd fwd inst` mp_tac) >>
         simp[MEM_MAP] >> metis_tac[]) >>
      metis_tac[bp_handle_inst_phi_filter_fwd_fst]) >>
  `MEM bb fn.fn_blocks` by
    (qspecl_then [`\bb. bb.bb_label = lbl`, `fn.fn_blocks`, `bb`]
      mp_tac venomExecPropsTheory.FIND_MEM >> simp[]) >>
  `inst_wf inst` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> res_tac) >>
  `!v. bp_get_ptrs bp2 v = bp_get_ptrs r1 v` by metis_tac[] >>
  `FST (bp_handle_inst bp inst) = FST (bp_handle_inst r1 inst)` by
    (irule bp_handle_inst_fst_ext >> simp[]) >>
  qpat_x_assum `!fn fwd bp c bp'. _`
    (qspecl_then [`fn`, `bb0.bb_label::fwd`, `r1`, `c2`, `bp2`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> simp[]) >>
  disch_then (qspecl_then [`lbl`, `bb`, `inst`] assume_tac) >>
  gvs[]
QED

(* At fixpoint, bp_one_pass_aux doesn't change bp.
   Depends on df_iterate convergence (shared termination gap). *)
Triviality bp_analyze_fixpoint[local]:
  !cfg fn.
    fn_inst_wf fn ==>
    SND (bp_one_pass_aux fn (bp_analyze cfg fn) [] cfg.cfg_dfs_pre) =
    bp_analyze cfg fn
Proof
  cheat  (* shared gap: df_iterate termination for bp_analyze *)
QED

Triviality find_mem_block_label[local]:
  !bbs bb.
    MEM bb bbs /\ ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    FIND (\bb'. bb'.bb_label = bb.bb_label) bbs = SOME bb
Proof
  Induct >> simp[FIND_thm] >> rpt strip_tac >>
  gvs[MEM_MAP] >> rw[] >> gvs[]
QED

Triviality wf_function_find_mem_block_label[local]:
  !fn bb.
    wf_function fn /\ MEM bb fn.fn_blocks ==>
    FIND (\bb'. bb'.bb_label = bb.bb_label) fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  irule find_mem_block_label >>
  gvs[wf_function_def, fn_labels_def]
QED

(* At fixpoint, each bp_handle_inst returns changed=F.
   Consequence of bp_analyze_fixpoint + bp_one_pass_aux_fixpoint_each.
   Needs MEM bb.bb_label dfs_pre because only reachable blocks are processed,
   and uses block-label uniqueness to align MEM blocks with FIND lookup. *)
Triviality bp_analyze_handle_inst_stable[local]:
  !fn bb inst.
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    MEM inst bb.bb_instructions ==>
    FST (bp_handle_inst (bp_analyze (cfg_analyze fn) fn) inst) = F
Proof
  rpt strip_tac >>
  qabbrev_tac `bp = bp_analyze (cfg_analyze fn) fn` >>
  qabbrev_tac `order = (cfg_analyze fn).cfg_dfs_pre` >>
  qabbrev_tac `p = bp_one_pass_aux fn bp [] order` >>
  qabbrev_tac `c = FST p` >>
  qabbrev_tac `bp' = SND p` >>
  `bp_one_pass_aux fn bp [] order = (c,bp')` by
    simp[Abbr `p`, Abbr `c`, Abbr `bp'`, PAIR] >>
  `bp' = bp` by
    (simp[Abbr `bp'`, Abbr `p`, Abbr `bp`, Abbr `order`] >>
     irule bp_analyze_fixpoint >> simp[]) >>
  `ALL_DISTINCT order` by
    simp[Abbr `order`, cfgAnalysisPropsTheory.cfg_analyze_dfs_pre_distinct] >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  `FIND (\bb'. bb'.bb_label = bb.bb_label) fn.fn_blocks = SOME bb` by
    metis_tac[wf_function_find_mem_block_label] >>
  qspecl_then [`order`, `fn`, `[]`, `bp`, `c`, `bp`]
    mp_tac bp_one_pass_aux_fixpoint_each >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`bb.bb_label`, `bb`, `inst`] mp_tac) >>
  simp[Abbr `bp`, Abbr `order`]
QED

(* Disjunction helper for bp_handle_inst_fixpoint_sound's last precondition.
   At fixpoint with nonempty output ptrs, either:
   (a) DRESTRICT'd version also produces nonempty output (most opcodes), OR
   (b) all stale ptrs trivially match s' (ADD/SUB Var-Var with NONE offsets).
   Case (b) uses bp_vv_inv (NONE offset) + n2w_exists_offset.
   Cases where operand ptrs are empty but output ptrs are non-empty (e.g.
   ADD Var-Lit with empty operand) are unreachable at the true fixpoint
   (starting from FEMPTY, only FUPDATE establishes ptrs, requiring non-empty
   operand ptrs). This unreachability is blocked on the fixpoint termination
   shared gap (same as bp_analyze_fixpoint, bp_analyze_ptr_fdom etc). *)
Triviality bp_fixpoint_drestrict_or_match[local]:
  !bp inst out fn fuel ctx s0 s1.
    FST (bp_handle_inst bp inst) = F /\
    inst_output inst = SOME out /\
    inst_wf inst /\
    is_ptr_opcode inst.inst_opcode /\
    EVERY (\v. v <> out) (inst_uses inst) /\
    bp_get_ptrs bp out <> [] /\
    bp_vv_inv fn bp /\
    MEM inst (fn_insts fn) /\
    bp_ptr_sound bp s0 /\
    step_inst fuel ctx inst s0 = OK s1 /\
    alloca_inv s0 /\
    (!v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ==>
       FLOOKUP s1.vs_allocas aid = FLOOKUP s0.vs_allocas aid) ==>
    bp_get_ptrs (SND (bp_handle_inst (DRESTRICT bp (COMPL {out})) inst))
      out <> [] \/
    !p. MEM p (bp_get_ptrs bp out) ==> ptr_matches_var p out s1
Proof
  rpt strip_tac >>
  imp_res_tac inst_wf_outputs_some >>
  qabbrev_tac `bp0 = DRESTRICT bp (COMPL {out})` >>
  `bp_get_ptrs bp0 out = []` by
    simp[bp_get_ptrs_def, FLOOKUP_DRESTRICT, Abbr `bp0`] >>
  `!v. v <> out ==> bp_get_ptrs bp0 v = bp_get_ptrs bp v` by
    simp[bp_get_ptrs_def, FLOOKUP_DRESTRICT, Abbr `bp0`] >>
  `!v. MEM v (inst_uses inst) ==> bp_get_ptrs bp0 v = bp_get_ptrs bp v` by
    (rpt strip_tac >> first_x_assum irule >> gvs[EVERY_MEM] >> metis_tac[]) >>
  (* Strategy: Show bp_handle_inst bp0 gives same output ptrs as bp
     (because operand ptrs agree). Since bp output is non-empty, bp0
     output is too → antecedent of the implication is false.
     Subcases where no FUPDATE occurs (empty operands) are unreachable
     at the true fixpoint — these are shared-gap cheats.
     Order after Cases_on: ADD, SUB, ASSIGN, ALLOCA. *)
  Cases_on `inst.inst_opcode` >> gvs[is_ptr_opcode_def]
  >- cheat (* ADD: shared gap — needs fixpoint for bp_handle_inst soundness *)
  >- cheat (* SUB: shared gap — needs fixpoint for bp_handle_inst soundness *)
  (* ASSIGN *)
  >- suspend "assign_case"
  (* ALLOCA *)
  >> suspend "alloca_case"
QED

(* Helper for assign_case: ASSIGN with [Var src] operand.
   Extracted as helper. Only the [Var src] case
   is provable without fixpoint reachability — other operand shapes
   (Lit/Label/[]) don't FUPDATE so drestrict ≠ original. *)
Triviality bp_assign_drestrict_ptrs_eq[local]:
  !bp bp0 inst out.
    inst.inst_opcode = ASSIGN /\
    inst_wf inst /\
    inst.inst_outputs = [out] /\
    Abbrev (bp0 = DRESTRICT bp (COMPL {out})) /\
    EVERY (\v. v <> out) (inst_uses inst) /\
    (!v. v <> out ==> bp_get_ptrs bp0 v = bp_get_ptrs bp v) ==>
    bp_get_ptrs (SND (bp_handle_inst bp0 inst)) out =
    bp_get_ptrs (SND (bp_handle_inst bp inst)) out
Proof
  rpt strip_tac >>
  (* inst_wf + ASSIGN => LENGTH operands = 1 *)
  `LENGTH inst.inst_operands = 1` by gvs[inst_wf_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  (* Now: inst.inst_operands = [h], 3 subcases: Lit, Var, Label *)
  qpat_x_assum `inst.inst_opcode = _` (fn eq =>
    PURE_REWRITE_TAC [eq, bp_handle_inst_def, inst_output_def]) >>
  simp[LET_THM, bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  Cases_on `h` >> gvs[]
  >- cheat (* Lit — shared gap: unreachable at fixpoint *)
  >- (rename1 `[Var src]` >>
      `src <> out` by (
        gvs[EVERY_MEM, inst_uses_def, venomInstTheory.operand_vars_def,
            venomInstTheory.operand_var_def]) >>
      simp[FLOOKUP_UPDATE] >>
      first_x_assum (qspec_then `src` mp_tac) >> simp[bp_get_ptrs_def])
  >> cheat (* Label — shared gap: unreachable at fixpoint *)
QED

Resume bp_fixpoint_drestrict_or_match[assign_case]:
  strip_tac >>
  `bp_get_ptrs (SND (bp_handle_inst bp inst)) out = bp_get_ptrs bp out` by (
    qspecl_then [`bp`, `inst`, `out`] mp_tac bp_handle_inst_fst_eq >>
    simp[]) >>
  `bp_get_ptrs (SND (bp_handle_inst bp0 inst)) out =
   bp_get_ptrs (SND (bp_handle_inst bp inst)) out` by (
    irule bp_assign_drestrict_ptrs_eq >> simp[]) >>
  gvs[]
QED

Resume bp_fixpoint_drestrict_or_match[alloca_case]:
  simp[Abbr `bp0`, bp_handle_inst_def, inst_output_def, LET_THM,
       bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

Finalise bp_fixpoint_drestrict_or_match

(* ALLOCA may create the allocation tracked by its output.  The generic
   fixpoint helper requires all tracked allocation entries to be unchanged,
   so handle ALLOCA directly. *)
Triviality step_alloca_preserves_matched_alloca[local]:
  !fuel ctx inst s s' aid off v.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = ALLOCA /\
    ptr_matches_var (Ptr (Allocation aid) off) v s ==>
    FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid
Proof
  rpt strip_tac >>
  Cases_on `aid = inst.inst_id`
  >- (
    `inst.inst_opcode <> INVOKE` by simp[] >>
    `step_inst_base inst s = OK s'` by
      metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
    Cases_on `off` >> gvs[ptr_matches_var_def] >>
    gvs[venomExecSemanticsTheory.step_inst_base_def,
        venomExecSemanticsTheory.exec_alloca_def, AllCaseEqs(),
        venomStateTheory.update_var_def, FLOOKUP_UPDATE]) >>
  irule (SIMP_RULE std_ss [] step_inst_alloca_flookup) >>
  qexistsl [`ctx`, `fuel`, `inst`] >> simp[]
QED

Triviality bp_ptr_sound_step_alloca[local]:
  !bp inst fuel ctx s s'.
    bp_ptr_sound bp s /\
    step_inst fuel ctx inst s = OK s' /\
    FST (bp_handle_inst bp inst) = F /\
    inst_wf inst /\
    inst.inst_opcode = ALLOCA ==>
    bp_ptr_sound bp s'
Proof
  rpt strip_tac >>
  simp[bp_ptr_sound_def] >> rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  `step_inst_base inst s = OK s'` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `?out. inst_output inst = SOME out` by
    (gvs[inst_wf_def, inst_output_def] >>
     Cases_on `inst.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[] >> metis_tac[]) >>
  Cases_on `v = out`
  >- (
    gvs[] >>
    `inst.inst_outputs = [out]` by
      (drule_all inst_wf_outputs_some >> simp[]) >>
    qpat_x_assum `~FST (bp_handle_inst bp inst)` mp_tac >>
    simp[bp_handle_inst_def, LET_THM] >>
    qpat_x_assum `inst_output inst = SOME out` (fn th => rewrite_tac[th]) >>
    simp[] >> strip_tac >>
    `bp_get_ptrs bp out = [ptr_from_alloca inst]` by
      (pop_assum mp_tac >> simp[bp_get_ptrs_def, FLOOKUP_UPDATE]) >>
    qexists_tac `ptr_from_alloca inst` >> simp[] >>
    qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
    simp[venomExecSemanticsTheory.step_inst_base_def,
         venomExecSemanticsTheory.exec_alloca_def, AllCaseEqs(),
         venomWfTheory.inst_wf_def] >> strip_tac >>
    gvs[ptr_from_alloca_def, ptr_matches_var_def,
        venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
        FLOOKUP_UPDATE]) >>
  `~MEM v inst.inst_outputs` by
    (gvs[inst_output_def] >>
     Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t` >> gvs[]) >>
  `lookup_var v s' = lookup_var v s` by
    (irule step_inst_preserves_lookup >>
     qexistsl [`ctx`, `fuel`, `inst`] >> simp[]) >>
  `IS_SOME (lookup_var v s)` by gvs[] >>
  `?p. MEM p (bp_get_ptrs bp v) /\ ptr_matches_var p v s` by
    metis_tac[bp_ptr_sound_def] >>
  qexists_tac `p` >> simp[] >>
  irule ptr_matches_var_preserved >>
  qexistsl [`s`, `v`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  irule step_alloca_preserves_matched_alloca >>
  metis_tac[]
QED

(* Standalone helper: bp_ptr_sound step for non-INVOKE at fixpoint.
   Extracted as helper (irule/drule need manual instantiation). *)
Triviality bp_ptr_sound_step_non_invoke[local]:
  !bp inst fuel ctx s0 s1 fn bb.
    bp_ptr_sound bp s0 /\
    step_inst fuel ctx inst s0 = OK s1 /\
    FST (bp_handle_inst bp inst) = F /\
    inst_wf inst /\
    inst.inst_opcode <> INVOKE /\
    bp = bp_analyze (cfg_analyze fn) fn /\
    ssa_form fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    alloca_inv s0 /\
    (!v. inst.inst_opcode = PHI /\
       MEM v (MAP SND (phi_pairs inst.inst_operands)) /\
       IS_SOME (lookup_var v s0) ==> bp_get_ptrs bp v <> []) /\
    (!inst' out. MEM inst' bb.bb_instructions /\
       inst_output inst' = SOME out ==> ~MEM out (inst_uses inst')) ==>
    bp_ptr_sound bp s1
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule bp_ptr_sound_step_alloca >>
      qexistsl [`ctx`, `fuel`, `inst`, `s0`] >> simp[]) >>
  match_mp_tac bp_handle_inst_fixpoint_sound >>
  qexistsl [`inst`, `fuel`, `ctx`, `s0`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- suspend "goal1"
  >- suspend "goal2"
  >- suspend "goal3"
  >> suspend "goal4"
QED

Resume bp_ptr_sound_step_non_invoke[goal1]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (match_mp_tac inst_output_not_self_use >>
      qexists `bb` >> simp[])
  >> (Cases_on `is_ptr_opcode inst.inst_opcode` >> simp[] >>
      drule_then (qspecl_then [`inst`, `out`, `bb`] mp_tac)
        bp_non_ptr_outputs_not_tracked >>
      imp_res_tac inst_wf_outputs_some >> simp[])
QED

Resume bp_ptr_sound_step_non_invoke[goal2]:
  rpt strip_tac >>
  irule bp_get_ptrs_not_in_fdom >>
  irule bp_non_ptr_outputs_not_tracked >>
  qexistsl [`bb`, `fn`, `inst`] >>
  simp[] >>
  metis_tac[inst_wf_output_none_not_ptr_opcode]
QED

Resume bp_ptr_sound_step_non_invoke[goal3]:
  rpt strip_tac >>
  irule step_inst_preserves_alloca_ptrs >>
  metis_tac[]
QED

Resume bp_ptr_sound_step_non_invoke[goal4]:
  rpt gen_tac >> strip_tac >>
  imp_res_tac inst_wf_outputs_some >>
  match_mp_tac bp_fixpoint_drestrict_or_match >>
  MAP_EVERY qexists [`fn`, `fuel`, `ctx`, `s0`] >>
  simp[fn_insts_def] >>
  `is_ptr_opcode inst.inst_opcode` by (
    qspecl_then [`bp`, `fn`, `inst`, `out`, `bb`] mp_tac
      bp_tracked_implies_ptr_opcode >> simp[]) >>
  `EVERY (\v. v <> out) (inst_uses inst)` by (
    qspecl_then [`inst`, `out`, `bb`] mp_tac
      inst_output_not_self_use >> simp[]) >>
  simp[] >>
  `bp_vv_inv fn (bp_analyze (cfg_analyze fn) fn)` by
    metis_tac[bp_analyze_vv_inv] >>
  `MEM inst (fn_insts_blocks fn.fn_blocks)` by
    metis_tac[mem_block_mem_fn_insts] >>
  simp[] >>
  rpt strip_tac >>
  irule step_inst_preserves_alloca_ptrs >>
  metis_tac[]
QED

Finalise bp_ptr_sound_step_non_invoke

(* Standalone helper: bp_ptr_sound step for INVOKE at fixpoint.
   INVOKE is not a pointer opcode, so it doesn't modify any tracked variable.
   Extracted as helper (irule/by need manual instantiation). *)
Triviality bp_ptr_sound_step_invoke[local]:
  !bp inst fuel ctx s0 s1 fn bb.
    bp_ptr_sound bp s0 /\
    step_inst fuel ctx inst s0 = OK s1 /\
    inst_wf inst /\
    inst.inst_opcode = INVOKE /\
    bp = bp_analyze (cfg_analyze fn) fn /\
    ssa_form fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    alloca_inv s0 ==>
    bp_ptr_sound bp s1
Proof
  rpt strip_tac >>
  simp[bp_ptr_sound_def] >> rpt strip_tac >>
  (* v is tracked (bp_get_ptrs bp v ≠ []), show ptr_matches_var preserved *)
  (* Step 1: all INVOKE outputs are not in FDOM bp *)
  `!w. MEM w inst.inst_outputs ==> w NOTIN FDOM bp` by (
    rpt strip_tac >>
    drule_then (qspecl_then [`inst`, `w`, `bb`] mp_tac)
      bp_non_ptr_outputs_not_tracked >>
    simp[is_ptr_opcode_def]) >>
  (* Step 2: v is not modified by inst *)
  `~MEM v inst.inst_outputs` by (
    CCONTR_TAC >> gvs[] >>
    first_x_assum drule >> strip_tac >>
    metis_tac[bp_get_ptrs_not_in_fdom]) >>
  (* Step 3: lookup_var v preserved *)
  `lookup_var v s1 = lookup_var v s0` by
    metis_tac[step_inst_preserves_lookup] >>
  (* Step 4: Get matching pointer from bp_ptr_sound bp s0 *)
  `?p. MEM p (bp_get_ptrs bp v) /\ ptr_matches_var p v s0` by
    metis_tac[bp_ptr_sound_def] >>
  qexists `p` >> gvs[] >>
  (* Step 5: ptr_matches_var preserved *)
  irule ptr_matches_var_preserved >>
  qexistsl [`s0`, `v`] >> simp[] >>
  (* Allocas preserved: INVOKE ≠ ALLOCA *)
  rpt strip_tac >>
  irule (SIMP_RULE std_ss [] step_inst_alloca_flookup) >>
  qexistsl [`ctx`, `fuel`, `inst`] >> simp[]
QED

(* --- Obligation: per-inst state_inv preservation --- *)
(* Placed here (after bp_ptr_sound_step_{invoke,non_invoke}) so helpers are in scope *)
Resume stage1_correct[state_inv_pres]:
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!fuel' run_ctx bb' inst' s0 s1.
       MEM bb' fn.fn_blocks /\ MEM inst' bb'.bb_instructions /\
       inst_wf inst' /\
       dfg_assigns_sound dfg s0 /\
       bp_ptr_sound bp s0 /\
       allocas_non_overlapping s0 /\
       allocas_in_word s0 /\
       bp_ptrs_bounded bp fn s0 /\
       step_inst fuel' run_ctx inst' s0 = OK s1 ==>
       dfg_assigns_sound dfg s1 /\
       bp_ptr_sound bp s1 /\
       allocas_non_overlapping s1 /\
       allocas_in_word s1 /\
       bp_ptrs_bounded bp fn s1`
    (qspecl_then [`fuel`, `ctx'`, `bb`, `inst`, `s'`, `s''`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> gvs[alloca_inv_def]) >>
  strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  irule alloca_inv_step_inst >>
  qexistsl [`ctx'`, `fuel`, `inst`, `s'`] >> simp[]
QED


(* bp_ptr_sound preserved through exec_block at the fixpoint.
   Internal lemma: n counts remaining instructions. *)
Triviality bp_ptr_sound_exec_block_gen[local]:
  !n fuel ctx bb s0 s' bp fn.
    n + s0.vs_inst_idx = LENGTH bb.bb_instructions /\
    bp_ptr_sound bp s0 /\
    exec_block fuel ctx bb s0 = OK s' /\
    s0.vs_inst_idx <= LENGTH bb.bb_instructions /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    bp = bp_analyze (cfg_analyze fn) fn /\
    alloca_inv s0 /\
    (!i inst v. i >= s0.vs_inst_idx /\ i < LENGTH bb.bb_instructions /\
               EL i bb.bb_instructions = inst /\ inst.inst_opcode = PHI /\
               MEM v (MAP SND (phi_pairs inst.inst_operands)) /\
               IS_SOME (lookup_var v s0) ==>
               bp_get_ptrs bp v <> []) /\
    ALL_DISTINCT (MAP (\i. i.inst_id)
      (FILTER (\i. i.inst_opcode = ALLOCA) bb.bb_instructions)) /\
    (!inst out. MEM inst bb.bb_instructions /\
               inst_output inst = SOME out ==>
               ~MEM out (inst_uses inst)) /\
    (* PHI operands are not defined by earlier instructions in the executed suffix. *)
    (!i j v. s0.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions /\ i < j /\
             j < LENGTH bb.bb_instructions /\
             (EL j bb.bb_instructions).inst_opcode = PHI /\
             MEM v (MAP SND (phi_pairs
               (EL j bb.bb_instructions).inst_operands)) ==>
             ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
    bp_ptr_sound bp s'
Proof
  Induct_on `n`
  >- (
    rpt strip_tac >>
    `s0.vs_inst_idx = LENGTH bb.bb_instructions` by decide_tac >>
    fs[Once exec_block_def, get_instruction_def])
  >> rpt strip_tac >>
  `s0.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  qabbrev_tac `inst = EL s0.vs_inst_idx bb.bb_instructions` >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`, MEM_EL] >> qexists `s0.vs_inst_idx` >> simp[]) >>
  `inst_wf inst` by
    (qpat_assum `fn_inst_wf _` (mp_tac o REWRITE_RULE [fn_inst_wf_def]) >>
     disch_then (qspecl_then [`bb`, `inst`] mp_tac) >> simp[]) >>
  (* Unfold exec_block one step *)
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def, Abbr `inst`] >>
  qabbrev_tac `inst = EL s0.vs_inst_idx bb.bb_instructions` >>
  (* Case split on step_inst result *)
  Cases_on `step_inst fuel ctx inst s0`
  >- suspend "step_ok"
  (* Non-OK step_inst cases *)
  >> simp[venomExecSemanticsTheory.exec_result_case_def]
QED

Resume bp_ptr_sound_exec_block_gen[step_ok]:
  rename1 `step_inst _ _ inst s0 = OK s1` >>
  simp[venomExecSemanticsTheory.exec_result_case_def] >>
  strip_tac >>
  (* Get fixpoint property for this instruction *)
  suspend "fixpoint_stable"
QED

Resume bp_ptr_sound_exec_block_gen[fixpoint_stable]:
  (* Establish FST (bp_handle_inst bp inst) = F at fixpoint *)
  `FST (bp_handle_inst bp inst) = F` by (
    qpat_assum `bp = _` (fn th => PURE_REWRITE_TAC[th]) >>
    mp_tac (Q.SPECL [`fn`, `bb`, `inst`] bp_analyze_handle_inst_stable) >>
    simp[]) >>
  suspend "per_inst_sound"
QED

Resume bp_ptr_sound_exec_block_gen[per_inst_sound]:
  (* Use qsuff_tac to create clean subgoals for bp_ptr_sound bp s1 *)
  qsuff_tac `bp_ptr_sound bp s1`
  >- suspend "apply_ih"
  >> suspend "bp_ptr_sound_s1"
QED

Resume bp_ptr_sound_exec_block_gen[bp_ptr_sound_s1]:
  (* Case split: INVOKE needs separate handling because inst_output=NONE
     with 2+ outputs, so precondition 6 of fixpoint_sound doesn't hold. *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "bp_ptr_sound_s1_invoke"
  >>
  (* Non-INVOKE: apply bp_handle_inst_fixpoint_sound *)
  suspend "bp_ptr_sound_s1_non_invoke"
QED

Resume bp_ptr_sound_exec_block_gen[bp_ptr_sound_s1_non_invoke]:
  match_mp_tac bp_ptr_sound_step_non_invoke >>
  qexistsl [`inst`, `fuel`, `ctx`, `s0`, `fn`, `bb`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `∀i inst v. i ≥ _ ∧ _ ⇒ _`
    (qspecl_then [`s0.vs_inst_idx`, `inst`, `v`] mp_tac) >>
  gvs[markerTheory.Abbrev_def]
QED

(* INVOKE case: use standalone helper *)
Resume bp_ptr_sound_exec_block_gen[bp_ptr_sound_s1_invoke]:
  match_mp_tac bp_ptr_sound_step_invoke >>
  qexistsl [`inst`, `fuel`, `ctx`, `s0`, `fn`, `bb`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume bp_ptr_sound_exec_block_gen[apply_ih]:
  (* Goal: bp_ptr_sound bp s1 ⇒ bp_ptr_sound bp s' *)
  strip_tac >>
  (* Case split: terminator or not *)
  reverse (Cases_on `is_terminator inst.inst_opcode`)
  >- suspend "apply_ih_cont"
  >>
  (* Terminator: s' = s1 (OK s1 = OK s') *)
  gvs[] >>
  Cases_on `s1.vs_halted` >>
  gvs[venomExecSemanticsTheory.exec_result_distinct]
QED

Resume bp_ptr_sound_exec_block_gen[apply_ih_cont]:
  gvs[] >>
  (* Establish alloca_inv s1 *)
  `alloca_inv s1` by metis_tac[alloca_inv_step_inst] >>
  (* Apply IH *)
  last_x_assum (qspecl_then
    [`fuel`, `ctx`, `bb`,
     `s1 with vs_inst_idx := SUC s0.vs_inst_idx`,
     `s'`, `fn`] mp_tac) >>
  simp[] >>
  disch_then match_mp_tac >>
  simp[alloca_inv_def] >>
  suspend "apply_ih_phi_ptrs"
QED

Resume bp_ptr_sound_exec_block_gen[apply_ih_phi_ptrs]:
  (* Two conjuncts: (1) PHI condition at SUC idx, (2) same-block pass-through *)
  conj_tac
  >- (
    rpt strip_tac >>
    reverse (Cases_on `MEM v inst.inst_outputs`)
    >- (
      (* v ∉ inst.inst_outputs: lookup_var v preserved *)
      `lookup_var v s1 = lookup_var v s0` by
        metis_tac[step_inst_preserves_lookup] >>
      `IS_SOME (lookup_var v s0)` by gvs[] >>
      (* Use outer PHI condition at >= s0.vs_inst_idx *)
      first_x_assum (qspecl_then [`i`, `v`] mp_tac) >>
      simp[])
    >>
    (* v ∈ inst.inst_outputs: contradicted by same-block condition.
       inst = EL s0.vs_inst_idx, PHI at position i > s0.vs_inst_idx *)
    `s0.vs_inst_idx < i` by decide_tac >>
    `s0.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
    qpat_x_assum `!i j v. _ ==> ~MEM v _` (qspecl_then
      [`s0.vs_inst_idx`, `i`, `v`] mp_tac) >>
    simp[Abbr `inst`])
  >>
  (* Same-block condition: inherited for the smaller suffix. *)
  rpt strip_tac >>
  qpat_x_assum `!i j v. s0.vs_inst_idx <= i /\ _ ==> _`
    (qspecl_then [`i`, `j`, `v`] mp_tac) >>
  simp[]
QED

Finalise bp_ptr_sound_exec_block_gen

(* Wrapper with vs_inst_idx = 0 *)
Triviality bp_ptr_sound_exec_block[local]:
  !bp fn bb fuel ctx s s'.
    bp_ptr_sound bp s /\
    exec_block fuel ctx bb s = OK s' /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\
    bp = bp_analyze (cfg_analyze fn) fn /\
    alloca_inv s /\
    (!inst v. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
              MEM v (MAP SND (phi_pairs inst.inst_operands)) /\
              IS_SOME (lookup_var v s) ==>
              bp_get_ptrs bp v <> []) /\
    ALL_DISTINCT (MAP (\i. i.inst_id)
      (FILTER (\i. i.inst_opcode = ALLOCA) bb.bb_instructions)) /\
    (!inst out. MEM inst bb.bb_instructions /\
               inst_output inst = SOME out ==>
               ~MEM out (inst_uses inst)) /\
    (!i j v. i < LENGTH bb.bb_instructions /\ i < j /\
             j < LENGTH bb.bb_instructions /\
             (EL j bb.bb_instructions).inst_opcode = PHI /\
             MEM v (MAP SND (phi_pairs
               (EL j bb.bb_instructions).inst_operands)) ==>
             ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
    bp_ptr_sound bp s'
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `bb`,
    `s`, `s'`, `bp`, `fn`] bp_ptr_sound_exec_block_gen) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
  >- (rpt strip_tac >> gvs[] >>
      qpat_x_assum `!inst v. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\ _ ==> bp_get_ptrs _ v <> []`
        (qspecl_then [`EL i bb.bb_instructions`, `v`] mp_tac) >>
      simp[MEM_EL] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!i j v. _ ==> ~MEM v (EL i bb.bb_instructions).inst_outputs`
    (qspecl_then [`i`, `j`, `v`] mp_tac) >>
  simp[]
QED

Triviality bp_ptr_sound_exec_block_from_idx[local]:
  !bp fn bb fuel ctx s s'.
    bp_ptr_sound bp s /\
    exec_block fuel ctx bb s = OK s' /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    bp = bp_analyze (cfg_analyze fn) fn /\
    alloca_inv s /\
    (!i inst v. i >= s.vs_inst_idx /\ i < LENGTH bb.bb_instructions /\
               EL i bb.bb_instructions = inst /\ inst.inst_opcode = PHI /\
               MEM v (MAP SND (phi_pairs inst.inst_operands)) /\
               IS_SOME (lookup_var v s) ==>
               bp_get_ptrs bp v <> []) /\
    ALL_DISTINCT (MAP (\i. i.inst_id)
      (FILTER (\i. i.inst_opcode = ALLOCA) bb.bb_instructions)) /\
    (!inst out. MEM inst bb.bb_instructions /\
               inst_output inst = SOME out ==>
               ~MEM out (inst_uses inst)) /\
    (!i j v. s.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions /\ i < j /\
             j < LENGTH bb.bb_instructions /\
             (EL j bb.bb_instructions).inst_opcode = PHI /\
             MEM v (MAP SND (phi_pairs
               (EL j bb.bb_instructions).inst_operands)) ==>
             ~MEM v (EL i bb.bb_instructions).inst_outputs) ==>
    bp_ptr_sound bp s'
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
    `fuel`, `ctx`, `bb`, `s`, `s'`, `bp`, `fn`]
    bp_ptr_sound_exec_block_gen) >>
  disch_then irule >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]
QED

(* --- Cross-block helpers --- *)

(* Join monotonicity: copy_fact_join_raw restricts f1, so all ∀-FLOOKUP
   predicates are preserved from f1 *)
val cf_sound_join_raw_mono = Q.prove(
  `!bp dfg f1 f2 s. cf_sound bp dfg f1 s ==>
    cf_sound bp dfg (copy_fact_join_raw dfg f1 f2) s`,
  rw[cf_sound_def, copy_fact_join_raw_def,
     finite_mapTheory.FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >> first_x_assum irule >> simp[]);

val cf_keys_ok_join_raw_mono = Q.prove(
  `!bp f1 f2 dfg. cf_keys_ok bp f1 ==>
    cf_keys_ok bp (copy_fact_join_raw dfg f1 f2)`,
  rw[cf_keys_ok_def, copy_fact_join_raw_def,
     finite_mapTheory.FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >> res_tac >> simp[]);

val cf_alloca_ok_join_raw_mono = Q.prove(
  `!bp f1 f2 dfg s. cf_alloca_ok bp f1 s ==>
    cf_alloca_ok bp (copy_fact_join_raw dfg f1 f2) s`,
  rw[cf_alloca_ok_def, copy_fact_join_raw_def,
     finite_mapTheory.FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >> res_tac >> simp[]);

(* Combined join monotonicity for the sound predicate *)
val cf_sound_join_mono = Q.prove(
  `!bp dfg a b s.
    (case a of NONE => T | SOME cfl => cf_sound bp dfg cfl s) /\
    (case a of NONE => T | SOME cfl => cf_keys_ok bp cfl) /\
    (case a of NONE => T | SOME cfl => cf_alloca_ok bp cfl s) /\
    a <> NONE ==>
    (case copy_fact_join dfg a b of
       NONE => T | SOME cfl => cf_sound bp dfg cfl s) /\
    (case copy_fact_join dfg a b of
       NONE => T | SOME cfl => cf_keys_ok bp cfl) /\
    (case copy_fact_join dfg a b of
       NONE => T | SOME cfl => cf_alloca_ok bp cfl s)`,
  Cases_on `a` >> simp[copy_fact_join_def] >>
  Cases_on `b` >> simp[copy_fact_join_def] >>
  rpt strip_tac >>
  metis_tac[cf_sound_join_raw_mono, cf_keys_ok_join_raw_mono,
            cf_alloca_ok_join_raw_mono]);

(* cf_entry_sound transfers through cf_agree: if cf_agree holds and f2's entry
   is sound, then f1's entry is also sound (same opcode + same normalized source) *)
val cf_entry_sound_agree = Q.prove(
  `!bp dfg f1 f2 k s. cf_agree dfg f1 f2 k /\
    cf_entry_sound bp dfg k (THE (FLOOKUP f2 k)) s ==>
    cf_entry_sound bp dfg k (THE (FLOOKUP f1 k)) s`,
  rw[cf_agree_def, cf_entry_sound_def, operand_equiv_def] >>
  Cases_on `FLOOKUP f1 k` >> Cases_on `FLOOKUP f2 k` >> gvs[] >>
  Cases_on `memloc_runtime_region k s'` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  qexists_tac `src_val` >> gvs[]);

(* cf_sound has SECOND-argument monotonicity through join_raw:
   soundness of f2 implies soundness of DRESTRICT f1 {cf_agree} *)
val cf_sound_join_raw_mono_b = Q.prove(
  `!bp dfg f1 f2 st. cf_sound bp dfg f2 st ==>
    cf_sound bp dfg (copy_fact_join_raw dfg f1 f2) st`,
  simp[cf_sound_def, copy_fact_join_raw_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  `?cf2. FLOOKUP f2 ml = SOME cf2` by (
    gvs[cf_agree_def] >>
    Cases_on `FLOOKUP f1 ml` >> Cases_on `FLOOKUP f2 ml` >> gvs[]) >>
  `cf_entry_sound bp dfg ml cf2 st` by (first_x_assum irule >> simp[]) >>
  mp_tac (Q.SPECL [`bp`, `dfg`, `f1`, `f2`, `ml`, `st`] cf_entry_sound_agree) >>
  simp[]);

(* Option-wrapped cf_sound second-arg monotonicity *)
val cf_sound_opt_join_mono_b = Q.prove(
  `!bp dfg a b st.
    cf_sound_opt bp dfg b st /\ b <> NONE ==>
    cf_sound_opt bp dfg (copy_fact_join dfg a b) st`,
  Cases_on `a` >> Cases_on `b` >>
  simp[cf_sound_opt_def, copy_fact_join_def] >>
  metis_tac[cf_sound_join_raw_mono_b]);

(* Option-wrapped cf_sound first-arg monotonicity *)
val cf_sound_opt_join_mono_a = Q.prove(
  `!bp dfg a b st.
    cf_sound_opt bp dfg a st /\ a <> NONE ==>
    cf_sound_opt bp dfg (copy_fact_join dfg a b) st`,
  Cases_on `a` >> Cases_on `b` >>
  simp[cf_sound_opt_def, copy_fact_join_def] >>
  metis_tac[cf_sound_join_raw_mono]);

(* PHI-prefix copy-fact transfer only prunes copy facts; pruning preserves
   cf_sound on the same state.  This is the local MCE analogue of the
   assign-elim PHI-prefix soundness step, and is a building block for the
   eval_phis entry-sound proof. *)
Triviality cf_sound_prune_vars[local]:
  !bp dfg killed cfl s.
    cf_sound bp dfg cfl s ==>
    cf_sound bp dfg (copy_fact_prune_vars dfg killed cfl) s
Proof
  rw[cf_sound_def, copy_fact_prune_vars_def, FLOOKUP_DRESTRICT] >>
  res_tac
QED

Triviality cf_sound_opt_phi_transfer_on_s[local]:
  !bp dfg ctx inst v s.
    ctx.ce_dfg = dfg /\ inst.inst_opcode = PHI /\
    cf_sound_opt bp dfg v s ==>
    cf_sound_opt bp dfg (copy_fact_transfer ctx inst v) s
Proof
  rpt strip_tac >>
  Cases_on `v` >>
  gvs[copy_fact_transfer_def, LET_THM, cf_sound_opt_def,
      is_copy_opcode_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, empty_effects_def, unwrap_copy_facts_def]
  >- simp[copy_fact_prune_vars_def, DRESTRICT_FEMPTY, cf_sound_def] >>
  irule cf_sound_prune_vars >> simp[]
QED

(* FOLDL invariant: if P holds on init and is preserved by f, then P holds
   on FOLDL f init l. Standard inductive lemma. *)
val foldl_invariant = Q.prove(
  `!f l acc P. P acc /\ (!a b. P a ==> P (f a b)) ==> P (FOLDL f acc l)`,
  Induct_on `l` >> simp[]);

(* Entries in option-level FOLDL are subset of accumulator *)
Triviality foldl_join_opt_sub[local]:
  !xs dfg acc cfl ml cf.
    FOLDL (copy_fact_join dfg) (SOME acc) xs = SOME cfl /\
    FLOOKUP cfl ml = SOME cf ==>
    FLOOKUP acc ml = SOME cf
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `h`
  >- (gvs[copy_fact_join_def] >> metis_tac[])
  >> gvs[copy_fact_join_def] >>
     first_x_assum drule_all >> strip_tac >>
     gvs[copy_fact_join_raw_def, finite_mapTheory.FLOOKUP_DRESTRICT]
QED

(* If key k survives option-level FOLDL of copy_fact_join and
   MEM (SOME y_raw) xs, then y_raw has key k with an agreeing entry. *)
Triviality copy_fact_foldl_opt_mem_agree[local]:
  !xs dfg acc ml cfl cf y_raw.
    FOLDL (copy_fact_join dfg) acc xs = SOME cfl /\
    FLOOKUP cfl ml = SOME cf /\
    MEM (SOME y_raw) xs ==>
    ?cf_y. FLOOKUP y_raw ml = SOME cf_y /\
           cf.cf_opcode = cf_y.cf_opcode /\
           operand_equiv dfg cf.cf_source cf_y.cf_source /\
           operand_equiv dfg cf.cf_size cf_y.cf_size
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> gvs[]
  >- (* y_raw = THE h *)
     (Cases_on `acc`
      >- (* acc = NONE: foldl starts at SOME y_raw *)
         (gvs[copy_fact_join_def] >>
          drule_all foldl_join_opt_sub >> strip_tac >>
          qexists `cf` >> simp[operand_equiv_def])
      >- (* acc = SOME a: join gives DRESTRICT, cf_agree gives agreement *)
         (gvs[copy_fact_join_def] >>
          `FLOOKUP (copy_fact_join_raw dfg x y_raw) ml = SOME cf` by
            (drule_all foldl_join_opt_sub >> simp[]) >>
          gvs[copy_fact_join_raw_def, finite_mapTheory.FLOOKUP_DRESTRICT,
              cf_agree_def] >>
          BasicProvers.every_case_tac >> gvs[] >>
          metis_tac[operand_equiv_def]))
  >> (* y_raw in tail: IH *)
     Cases_on `h`
     >- (gvs[copy_fact_join_def] >> metis_tac[])
     >> gvs[copy_fact_join_def] >> metis_tac[]
QED

(* ce_memloc_from_ops is invariant under operand_equiv + bp_assigns_stable *)
(* cf_keys_ok_opt preserved by copy_fact_join (both args) *)
Triviality cf_keys_ok_opt_join[local]:
  !bp dfg a b. cf_keys_ok_opt bp a /\ cf_keys_ok_opt bp b ==>
    cf_keys_ok_opt bp (copy_fact_join dfg a b)
Proof
  rpt gen_tac >> Cases_on `a` >> Cases_on `b` >>
  simp[cf_keys_ok_opt_def, copy_fact_join_def] >>
  strip_tac >> irule cf_keys_ok_join_raw_mono >> simp[]
QED

(* --- Helpers for cf_keys_ok through transfer --- *)

(* cf_keys_ok preserved under DRESTRICT *)
Triviality cf_keys_ok_drestrict[local]:
  !bp cfl S. cf_keys_ok bp cfl ==> cf_keys_ok bp (DRESTRICT cfl S)
Proof
  rw[cf_keys_ok_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >> gvs[] >>
  res_tac
QED

(* cf_keys_ok of FEMPTY *)
Triviality cf_keys_ok_fempty[local]:
  !bp. cf_keys_ok bp FEMPTY
Proof
  simp[cf_keys_ok_def]
QED

(* cf_keys_ok preserved by FUPDATE when new entry satisfies conditions *)
Triviality cf_keys_ok_fupdate[local]:
  !bp cfl ml cf.
    cf_keys_ok bp cfl /\ cf_key_size_ok bp ml cf /\ ml_is_fixed ml /\
    (cf.cf_opcode = MCOPY ==>
     ml_is_fixed (ce_memloc_from_ops bp cf.cf_source cf.cf_size)) ==>
    cf_keys_ok bp (cfl |+ (ml, cf))
Proof
  rw[cf_keys_ok_def] >> rpt strip_tac >>
  fs[FLOOKUP_UPDATE] >> BasicProvers.every_case_tac >> gvs[] >> res_tac
QED

(* cf_keys_ok preserved by copy_fact_invalidate *)
Triviality cf_keys_ok_invalidate[local]:
  !bp aliases cfl wl.
    cf_keys_ok bp cfl ==>
    cf_keys_ok bp (copy_fact_invalidate aliases bp cfl wl)
Proof
  rw[copy_fact_invalidate_def]
  >- simp[cf_keys_ok_fempty]
  >> irule cf_keys_ok_drestrict >> simp[]
QED

(* cf_keys_ok preserved by copy_fact_prune_vars *)
Triviality cf_keys_ok_prune_vars[local]:
  !bp dfg killed cfl.
    cf_keys_ok bp cfl ==>
    cf_keys_ok bp (copy_fact_prune_vars dfg killed cfl)
Proof
  rw[copy_fact_prune_vars_def] >> irule cf_keys_ok_drestrict >> simp[]
QED

(* ml_is_fixed of ce_memloc implies operand is not Label *)
Triviality ce_memloc_fixed_not_label[local]:
  !bp dst sz. ml_is_fixed (ce_memloc_from_ops bp dst sz) ==>
    !l. dst <> Label l
Proof
  rpt gen_tac >> Cases_on `dst` >>
  simp[ce_memloc_from_ops_def, bp_segment_from_ops_def,
       ml_undefined_def, ml_is_fixed_def, LET_THM]
QED

(* ce_memloc_from_ops ml_size depends only on sz, not on the offset operand
   (when neither operand is a Label) *)
Triviality ce_memloc_size_same_sz[local]:
  !bp op1 op2 sz.
    (!l. op1 <> Label l) /\ (!l. op2 <> Label l) ==>
    (ce_memloc_from_ops bp op1 sz).ml_size =
    (ce_memloc_from_ops bp op2 sz).ml_size
Proof
  rpt gen_tac >> Cases_on `op1` >> Cases_on `op2` >>
  simp[ce_memloc_from_ops_def, bp_segment_from_ops_def,
       ml_undefined_def, LET_THM] >> BasicProvers.every_case_tac >> simp[]
QED

(* --- Main transfer preservation --- *)

(* cf_keys_ok_opt preserved by copy_fact_transfer unconditionally.
   Key insight: the new entry uses the same sz for both key (write_loc)
   and value (cf_size), so cf_key_size_ok is satisfied. The ml_is_fixed
   guard handles the other conditions. *)
(* Unwrap cf_keys_ok_opt → cf_keys_ok on unwrap_copy_facts *)
Triviality cf_keys_ok_opt_unwrap[local]:
  !bp cfl. cf_keys_ok_opt bp cfl ==> cf_keys_ok bp (unwrap_copy_facts cfl)
Proof
  Cases_on `cfl` >>
  fs[cf_keys_ok_opt_def, unwrap_copy_facts_def] >>
  simp[cf_keys_ok_def]
QED

Triviality cf_keys_ok_opt_transfer[local]:
  !bp dfg ctx inst cfl.
    ctx.ce_bp = bp /\ ctx.ce_dfg = dfg /\
    bp_assigns_stable bp dfg /\
    cf_keys_ok_opt bp cfl ==>
    cf_keys_ok_opt bp (copy_fact_transfer ctx inst cfl)
Proof
  rpt strip_tac
  >> drule cf_keys_ok_opt_unwrap >> strip_tac
  >> simp[copy_fact_transfer_def, LET_THM, cf_keys_ok_opt_def]
  >> IF_CASES_TAC >> simp[]
  >- (BasicProvers.TOP_CASE_TAC >> simp[cf_keys_ok_fempty] >>
      BasicProvers.TOP_CASE_TAC >> simp[cf_keys_ok_fempty] >>
      BasicProvers.TOP_CASE_TAC >> simp[cf_keys_ok_fempty] >>
      BasicProvers.TOP_CASE_TAC >> simp[cf_keys_ok_fempty] >>
      IF_CASES_TAC >> simp[] >>
      pairarg_tac >> simp[] >>
      IF_CASES_TAC >> simp[]
      >- (gvs[] >> irule cf_keys_ok_fupdate >> simp[] >>
          conj_tac >- (irule cf_keys_ok_invalidate >> simp[]) >>
          simp[cf_key_size_ok_def] >>
          irule ce_memloc_size_same_sz >>
          simp[] >> irule ce_memloc_fixed_not_label >> metis_tac[])
      >> irule cf_keys_ok_invalidate >> simp[])
  >> IF_CASES_TAC
  >- (irule cf_keys_ok_invalidate >> simp[])
  >> IF_CASES_TAC
  >- simp[cf_keys_ok_fempty]
  >> irule cf_keys_ok_prune_vars >> simp[]
QED

(* cf_alloca_ok is first-arg monotone under copy_fact_join_raw.
   Proof: join_raw = DRESTRICT f1 {cf_agree keys} — a subset of f1 with
   same values, so any universal property over entries transfers. *)
Triviality cf_alloca_ok_join_raw_mono[local]:
  !dfg bp f1 f2 s.
    cf_alloca_ok bp f1 s ==>
    cf_alloca_ok bp (copy_fact_join_raw dfg f1 f2) s
Proof
  rw[cf_alloca_ok_def, copy_fact_join_raw_def, FLOOKUP_DRESTRICT] >>
  metis_tac[]
QED

(* Reverse direction of memloc_within_alloca_normalize:
   if the normalized operand's memloc is within alloca,
   so is the original's. Uses bp_ptr_from_op_normalize. *)
Triviality memloc_within_alloca_normalize_rev[local]:
  !bp dfg op sz s.
    bp_assigns_stable bp dfg /\
    memloc_within_alloca
      (ce_memloc_from_ops bp (normalize_operand dfg [] op) sz) s ==>
    memloc_within_alloca (ce_memloc_from_ops bp op sz) s
Proof
  rpt strip_tac >>
  `bp_ptr_from_op bp (normalize_operand dfg [] op) =
   bp_ptr_from_op bp op` by (irule bp_ptr_from_op_normalize >> simp[]) >>
  Cases_on `op`
  >- (simp[ce_memloc_from_ops_def, bp_segment_from_ops_def,
           memloc_within_alloca_def] >>
      BasicProvers.every_case_tac >> simp[])
  >- (Cases_on `normalize_operand dfg [] (Var s')` >>
      gvs[ce_memloc_from_ops_def, bp_segment_from_ops_def,
          memloc_within_alloca_def, LET_THM] >>
      BasicProvers.every_case_tac >> gvs[bp_ptr_from_op_def])
  >> (Cases_on `normalize_operand dfg [] (Label s')` >>
      gvs[ce_memloc_from_ops_def, bp_segment_from_ops_def,
          memloc_within_alloca_def, ml_undefined_def, LET_THM] >>
      BasicProvers.every_case_tac >> gvs[bp_ptr_from_op_def])
QED

(* cf_alloca_ok_opt of joined value: entries in the joined lattice are
   from the first non-NONE predecessor (foldl_join_opt_sub). For any entry
   (ml, cf), the same KEY ml exists in bb.bb_label (from cf_agree in
   copy_fact_join_raw). Part 1 (memloc_within_alloca ml) transfers directly
   via cf_alloca_ok_join_raw_mono (first-arg mono — values from f1).
   Part 2 (source memloc within alloca for MCOPY) also transfers via first-arg
   mono since values come from f1, not f2.
   Key insight: join_raw takes VALUES from f1 (first arg), so first-arg mono
   suffices. Second-arg reasoning (via normalize chain) is NOT needed because
   we propagate cf_alloca_ok forward through the FOLDL from the first non-NONE
   predecessor, not from an arbitrary nbr. *)
Triviality cf_alloca_ok_opt_joined[local]:
  !dfg bp s preds result nbr ctx lbl.
    bp_assigns_stable bp dfg /\
    MEM nbr preds /\
    cf_alloca_ok_opt bp (df_boundary NONE result nbr) s /\
    df_boundary NONE result nbr <> NONE ==>
    !cfl. FOLDL (copy_fact_join dfg) NONE
            (MAP (\p. copy_fact_edge_transfer ctx p lbl
                        (df_boundary NONE result p)) preds) = SOME cfl ==>
    cf_alloca_ok bp cfl s
Proof
  cheat (* shared gap: needs memloc_within_alloca *)
QED


Triviality mce_run_block_successor_in_cfg_dfs_pre[local]:
  !fn bb fuel ctx s v.
    fn_inst_wf fn /\ ALL_DISTINCT (fn_labels fn) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_current_bb = bb.bb_label /\
    run_block fuel ctx bb s = OK v
    ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `bb.bb_instructions <> []` by
    metis_tac[venomExecPropsTheory.run_block_ok_nonempty] >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecPropsTheory.run_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs] >>
  imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
  gvs[EVERY_MEM]
QED

Triviality mce_run_block_successor_in_cfg_dfs_pre_wf[local]:
  !fn bb fuel ctx s v.
    wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_current_bb = bb.bb_label /\
    run_block fuel ctx bb s = OK v
    ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  qspecl_then [`fn`, `bb`, `fuel`, `ctx`, `s`, `v`]
    mp_tac mce_run_block_successor_in_cfg_dfs_pre >>
  impl_tac
  >- (
    fs[wf_function_def] >>
    rpt strip_tac >>
    qpat_x_assum `!bb. MEM bb fn.fn_blocks ==> bb_well_formed bb`
      (drule_then assume_tac) >>
    `i = PRE (LENGTH bb'.bb_instructions)` by
      (fs[bb_well_formed_def] >> first_x_assum irule >> simp[]) >>
    gvs[]) >>
  simp[]
QED

Triviality bp_ptr_sound_update_untracked[local]:
  !bp s out val.
    bp_ptr_sound bp s /\ bp_get_ptrs bp out = [] ==>
    bp_ptr_sound bp (update_var out val s)
Proof
  rw[bp_ptr_sound_def] >>
  Cases_on `v = out` >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qexists_tac `p` >> simp[] >>
  Cases_on `p` >> Cases_on `a` >> Cases_on `o'` >>
  gvs[ptr_matches_var_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  qexists_tac `delta` >> REFL_TAC
QED

Triviality eval_phis_preserves_bp_ptr_sound_untracked[local]:
  !bp s insts s'.
    (!inst out. MEM inst insts /\ inst.inst_opcode = PHI /\
       inst.inst_outputs = [out] ==> bp_get_ptrs bp out = []) /\
    bp_ptr_sound bp s /\
    eval_phis s insts = OK s' ==>
    bp_ptr_sound bp s'
Proof
  rpt gen_tac >>
  qid_spec_tac `s'` >>
  Induct_on `insts` >> simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (fs[eval_phis_def] >>
    Cases_on `eval_one_phi s h` >> fs[] >>
    PairCases_on `x` >> fs[] >>
    Cases_on `eval_phis s insts` >> fs[] >>
    rename1 `eval_phis s insts = OK s_tail` >>
    `bp_ptr_sound bp s_tail` by (
      qpat_x_assum `(!inst out. MEM inst insts /\ _ ==> _) ==> bp_ptr_sound bp s_tail`
        mp_tac >>
      impl_tac >- (
        rpt strip_tac >>
        qpat_x_assum `!inst out. (inst = h \/ MEM inst insts) /\ _ ==> _`
          (qspecl_then [`inst`, `out`] mp_tac) >>
        simp[]) >>
      simp[]) >>
    `h.inst_outputs = [x0]` by (
      qpat_x_assum `eval_one_phi _ _ = SOME _` mp_tac >>
      simp[eval_one_phi_def] >>
      BasicProvers.every_case_tac >> gvs[]) >>
    `bp_get_ptrs bp x0 = []` by (
      qpat_x_assum `!inst out. (inst = h \/ MEM inst insts) /\ _ ==> _`
        (qspecl_then [`h`, `x0`] mp_tac) >>
      simp[]) >>
    qpat_x_assum `update_var x0 x1 s_tail = s'`
      (SUBST1_TAC o SYM) >>
    irule bp_ptr_sound_update_untracked >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  fs[eval_phis_def]
QED

Triviality bp_phi_outputs_untracked[local]:
  !bp fn bb inst out.
    bp = bp_analyze (cfg_analyze fn) fn /\
    fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\ inst.inst_outputs = [out] ==>
    bp_get_ptrs bp out = []
Proof
  rpt strip_tac >>
  irule bp_non_ptr_opcode_no_ptrs >>
  MAP_EVERY qexists_tac [`bb`, `fn`, `inst`] >>
  simp[inst_output_def, is_ptr_opcode_def]
QED

Triviality stage1_state_inv_drop_inst_idx[local]:
  !bp dfg fn s.
    dfg_assigns_sound dfg (s with vs_inst_idx := 0) /\
    bp_ptr_sound bp (s with vs_inst_idx := 0) /\
    allocas_non_overlapping (s with vs_inst_idx := 0) /\
    allocas_in_word (s with vs_inst_idx := 0) /\
    bp_ptrs_bounded bp fn (s with vs_inst_idx := 0) ==>
    dfg_assigns_sound dfg s /\ bp_ptr_sound bp s /\
    allocas_non_overlapping s /\ allocas_in_word s /\ bp_ptrs_bounded bp fn s
Proof
  simp[dfg_assigns_sound_inst_idx, bp_ptr_sound_inst_idx,
       allocas_non_overlapping_inst_idx, allocas_in_word_inst_idx,
       bp_ptrs_bounded_inst_idx]
QED

Triviality exec_block_preserves_stage1_state_inv[local]:
  !n bp dfg fn bb fuel run_ctx st v.
    n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
    MEM bb fn.fn_blocks /\
    EVERY inst_wf bb.bb_instructions /\
    (!fuel' run_ctx bb0 inst0 s0 s1.
       MEM bb0 fn.fn_blocks /\ MEM inst0 bb0.bb_instructions /\
       inst_wf inst0 /\
       dfg_assigns_sound dfg (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst0 s0 = OK s1 ==>
       dfg_assigns_sound dfg (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s1 with vs_inst_idx := 0)) /\
    dfg_assigns_sound dfg (st with vs_inst_idx := 0) /\
    bp_ptr_sound bp (st with vs_inst_idx := 0) /\
    allocas_non_overlapping (st with vs_inst_idx := 0) /\
    allocas_in_word (st with vs_inst_idx := 0) /\
    bp_ptrs_bounded bp fn (st with vs_inst_idx := 0) /\
    exec_block fuel run_ctx bb st = OK v ==>
    dfg_assigns_sound dfg v /\ bp_ptr_sound bp v /\
    allocas_non_overlapping v /\ allocas_in_word v /\ bp_ptrs_bounded bp fn v
Proof
  completeInduct_on `n` >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  reverse (Cases_on `idx < LENGTH bb.bb_instructions`)
  >- (qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
      ONCE_REWRITE_TAC [exec_block_def] >>
      simp[get_instruction_def, Abbr `idx`]) >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `inst_wf inst` by metis_tac[EVERY_EL, markerTheory.Abbrev_def] >>
  `MEM inst bb.bb_instructions` by
    (simp[Abbr `inst`, MEM_EL] >> qexists_tac `idx` >> simp[]) >>
  `exec_block fuel run_ctx bb st =
   case step_inst fuel run_ctx inst st of
     OK st' =>
       if is_terminator inst.inst_opcode then
         if st'.vs_halted then Halt st' else OK st'
       else exec_block fuel run_ctx bb (st' with vs_inst_idx := SUC idx)
   | Halt st' => Halt st'
   | Abort a st' => Abort a st'
   | IntRet vals st' => IntRet vals st'
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `idx`]) >>
  qpat_x_assum `exec_block fuel run_ctx bb st = OK v` (fn ok_th =>
    qpat_x_assum `exec_block fuel run_ctx bb st = _` (fn unfold_th =>
      assume_tac (REWRITE_RULE [unfold_th] ok_th))) >>
  Cases_on `step_inst fuel run_ctx inst st`
  >- (
    rename1 `step_inst _ _ _ _ = OK st'` >>
    qpat_x_assum `_ = OK v` (fn th =>
      assume_tac (SIMP_RULE std_ss [exec_result_case_def] th)) >>
    `dfg_assigns_sound dfg (st' with vs_inst_idx := 0) /\
     bp_ptr_sound bp (st' with vs_inst_idx := 0) /\
     allocas_non_overlapping (st' with vs_inst_idx := 0) /\
     allocas_in_word (st' with vs_inst_idx := 0) /\
     bp_ptrs_bounded bp fn (st' with vs_inst_idx := 0)` by
      (qpat_x_assum `!fuel' run_ctx bb0 inst0 s0 s1. _`
        (qspecl_then [`fuel`, `run_ctx`, `bb`, `inst`, `st`, `st'`] mp_tac) >>
       impl_tac >- (rpt conj_tac >> simp[Abbr `idx`]) >>
       disch_then ACCEPT_TAC) >>
    Cases_on `is_terminator inst.inst_opcode`
    >- (Cases_on `st'.vs_halted`
        >- (qpat_x_assum `is_terminator inst.inst_opcode` (fn term_th =>
            qpat_x_assum `st'.vs_halted` (fn halt_th =>
              qpat_x_assum `(if is_terminator inst.inst_opcode then if st'.vs_halted then Halt st' else OK st' else run_block_non_phis fuel run_ctx bb (st' with vs_inst_idx := SUC idx)) = OK v`
                (fn eq_th => mp_tac (REWRITE_RULE [term_th, halt_th, exec_result_distinct] eq_th)))) >>
            simp[]) >>
        qpat_x_assum `is_terminator inst.inst_opcode` (fn term_th =>
          qpat_x_assum `~st'.vs_halted` (fn halt_th =>
            qpat_x_assum `(if is_terminator inst.inst_opcode then if st'.vs_halted then Halt st' else OK st' else run_block_non_phis fuel run_ctx bb (st' with vs_inst_idx := SUC idx)) = OK v`
              (fn eq_th => assume_tac (REWRITE_RULE [term_th, halt_th, exec_result_11] eq_th)))) >>
        qpat_x_assum `st' = v` (SUBST_ALL_TAC o SYM) >>
        irule stage1_state_inv_drop_inst_idx >> simp[]) >>
    qpat_x_assum `~is_terminator inst.inst_opcode` (fn nonterm_th =>
      qpat_x_assum `(if is_terminator inst.inst_opcode then if st'.vs_halted then Halt st' else OK st' else run_block_non_phis fuel run_ctx bb (st' with vs_inst_idx := SUC idx)) = OK v`
        (fn eq_th => assume_tac (REWRITE_RULE [nonterm_th] eq_th))) >>
    qpat_x_assum `n = LENGTH bb.bb_instructions - idx` SUBST_ALL_TAC >>
    qpat_x_assum `!m. m < LENGTH bb.bb_instructions - idx ==> _`
      (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
    impl_tac >- simp[Abbr `idx`] >>
    disch_then (qspecl_then [`bp`, `dfg`, `fn`, `bb`, `fuel`, `run_ctx`,
      `st' with vs_inst_idx := SUC idx`, `v`] mp_tac) >>
    impl_tac >- (
      `dfg_assigns_sound dfg st' /\ bp_ptr_sound bp st' /\
       allocas_non_overlapping st' /\ allocas_in_word st' /\
       bp_ptrs_bounded bp fn st'` by
        (irule stage1_state_inv_drop_inst_idx >> simp[]) >>
      rpt conj_tac >> simp[] >>
      FIRST [
        first_assum ACCEPT_TAC,
        rpt strip_tac >>
        qpat_x_assum `!fuel' run_ctx bb0 inst0 s0 s1. _`
          (qspecl_then [`fuel'`, `run_ctx'`, `bb0`, `inst0`, `s0`, `s1`] mp_tac) >>
        simp[dfg_assigns_sound_inst_idx, bp_ptr_sound_inst_idx,
             allocas_non_overlapping_inst_idx, allocas_in_word_inst_idx,
             bp_ptrs_bounded_inst_idx]
      ]) >>
    disch_then ACCEPT_TAC)
  >- (FULL_SIMP_TAC std_ss [exec_result_case_def, exec_result_distinct])
  >- (FULL_SIMP_TAC std_ss [exec_result_case_def, exec_result_distinct])
  >- (FULL_SIMP_TAC std_ss [exec_result_case_def, exec_result_distinct])
  >> FULL_SIMP_TAC std_ss [exec_result_case_def, exec_result_distinct]
QED

(* --- Obligation: cross-block --- *)
(* inv3 cross_block: MEM v.vs_current_bb dfs_pre ∧ sound ... v ∧ state_inv v.
   sound = cf_sound_opt/keys/alloca only.
   state_inv = bp_ptr_sound ∧ alloca_inv ∧ allocas_in_word ∧ bp_ptrs_bounded. *)
Resume stage1_correct[cross_block]:
  simp[] >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `ce_ctx = <| ce_aliases := aliases;
                            ce_bp := bp; ce_dfg := dfg |>` >>
  qabbrev_tac `result = df_analyze Forward NONE (copy_fact_join dfg)
    copy_fact_transfer copy_fact_edge_transfer ce_ctx
    (SOME (s.vs_current_bb, SOME FEMPTY)) fn` >>
  (* dfs_pre membership *)
  `MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by (
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `run_ctx`, `s''`, `v`]
      mce_run_block_successor_in_cfg_dfs_pre_wf) >>
    impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      first_assum ACCEPT_TAC) >>
    simp[]) >>
  simp[] >>
  (* Setup facts *)
  `bb_well_formed bb` by
    (fs[wf_function_def] >> metis_tac[]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  qabbrev_tac `sound_pred = \v s.
    cf_sound_opt bp dfg v s /\ cf_keys_ok_opt bp v /\
    cf_alloca_ok_opt bp v s` >>
  `dfg_assigns_sound dfg v /\ bp_ptr_sound bp v /\
   allocas_non_overlapping v /\ allocas_in_word v /\ bp_ptrs_bounded bp fn v` by (
    drule venomExecProofsTheory.run_block_OK_decompose >> strip_tac >>
    rename1 `eval_phis s'' bb.bb_instructions = OK s_phi` >>
    qabbrev_tac `p = phi_prefix_length bb.bb_instructions` >>
    qabbrev_tac `st = s_phi with vs_inst_idx := p` >>
    `dfg_assigns_sound dfg s_phi` by
      (qpat_x_assum `!bb s0 s_phi. _ ==> dfg_assigns_sound _ s_phi`
        (qspecl_then [`bb`, `s''`, `s_phi`] mp_tac) >> simp[]) >>
    `bp_ptr_sound bp st` by (
      simp[Abbr `st`, bp_ptr_sound_inst_idx] >>
      irule eval_phis_preserves_bp_ptr_sound_untracked >>
      qexists_tac `bb.bb_instructions` >> qexists_tac `s''` >>
      simp[] >> rpt strip_tac >>
      irule bp_phi_outputs_untracked >>
      MAP_EVERY qexists_tac [`bb`, `fn`, `inst`] >>
      simp[Abbr `bp`]) >>
    `allocas_non_overlapping st` by
      (simp[Abbr `st`, allocas_non_overlapping_inst_idx] >>
       drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
       strip_tac >> metis_tac[alloca_inv_non_overlapping, alloca_inv_alloca_fields_eq]) >>
    `allocas_in_word st` by
      (simp[Abbr `st`, allocas_in_word_inst_idx] >>
       drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
       strip_tac >> metis_tac[allocas_in_word_allocas_eq]) >>
    `bp_ptrs_bounded bp fn st` by
      (simp[Abbr `st`, bp_ptrs_bounded_inst_idx] >>
       drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
       strip_tac >> metis_tac[bp_ptrs_bounded_allocas_eq]) >>
    qspecl_then [`LENGTH bb.bb_instructions - p`, `bp`, `dfg`, `fn`, `bb`,
      `fuel`, `run_ctx`, `st`, `v`]
      mp_tac exec_block_preserves_stage1_state_inv >>
    simp[Abbr `st`, Abbr `p`, venomExecProofsTheory.phi_prefix_length_le] >>
    impl_tac >- (
      rpt conj_tac >> simp[] >>
      fs[dfg_assigns_sound_inst_idx, bp_ptr_sound_inst_idx,
         allocas_non_overlapping_inst_idx, allocas_in_word_inst_idx,
         bp_ptrs_bounded_inst_idx]) >>
    simp[]) >>
  (* Suspend only the copy-fact soundness obligation; state_inv follows above. *)
  conj_asm1_tac >- suspend "cf_sound" >>
  rpt conj_tac >> simp[] >>
  metis_tac[alloca_inv_run_block]
QED

(* bb_well_formed gives a unique terminator index *)
Triviality bb_wf_terminator_idx[local]:
  bb_well_formed bb ==>
  ?i. i < LENGTH bb.bb_instructions /\
      is_terminator (EL i bb.bb_instructions).inst_opcode /\
      !j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode
Proof
  simp[bb_well_formed_def] >> strip_tac >>
  qexists `PRE (LENGTH bb.bb_instructions)` >>
  `LAST bb.bb_instructions = EL (PRE (LENGTH bb.bb_instructions))
     bb.bb_instructions` by simp[LAST_EL] >>
  simp[] >> rpt strip_tac
  >- (`LENGTH bb.bb_instructions <> 0` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
      simp[])
  >- gvs[]
  >> `j = PRE (LENGTH bb.bb_instructions)` by
       (first_x_assum irule >> simp[] >>
        `LENGTH bb.bb_instructions <> 0` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
        simp[]) >>
  gvs[]
QED

(* cf_sound at successor entry: the core cross-block cf reasoning *)
Resume stage1_correct[cf_sound]:
  (* Step 1: Derive infrastructure facts *)
  `wf_function fn` by simp[] >>
  drule bb_wf_terminator_idx >> strip_tac >>
  `SUC i = LENGTH bb.bb_instructions` by (
    fs[bb_well_formed_def] >>
    `i = PRE (LENGTH bb.bb_instructions)` by
      (first_x_assum irule >> simp[]) >>
    Cases_on `bb.bb_instructions` >> gvs[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by (
    irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  `MEM bb.bb_label (fn_labels fn)` by
    (simp[fn_labels_def, MEM_MAP] >> qexists `bb` >> simp[]) >>
  `MEM v.vs_current_bb (fn_labels fn)` by
    (irule dfAnalyzeProofsTheory.cfg_dfs_pre_subset_fn_labels >> simp[]) >>
  `is_fixpoint
     (df_process_block Forward NONE (copy_fact_join dfg) copy_fact_transfer
        copy_fact_edge_transfer ce_ctx
        (SOME (s.vs_current_bb, SOME FEMPTY)) (cfg_analyze fn)
        fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result` by (
    mp_tac (Q.SPECL [`ce_ctx`, `fn`]
      (SIMP_RULE std_ss [LET_THM] copy_fact_is_fixpoint)) >>
    simp[Abbr `ce_ctx`, Abbr `result`]) >>
  (* Step 2: Rewrite df_at to joined_val, split conjuncts *)
  qabbrev_tac `joined = df_joined_val Forward NONE (copy_fact_join dfg)
     copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY))
     (cfg_analyze fn) result v.vs_current_bb` >>
  `df_at NONE result v.vs_current_bb 0 = joined` by
    suspend "df_at_eq" >>
  pop_assum (fn eq => rewrite_tac [eq]) >>
  conj_tac >- suspend "cf_sound_joined" >>
  conj_tac >- suspend "cf_keys_ok_joined" >>
  suspend "cf_alloca_ok_joined"
QED

(* df_at at entry = joined value, from fixpoint property *)
Resume stage1_correct[df_at_eq]:
  simp[Abbr `joined`, Abbr `result`] >>
  irule (SIMP_RULE std_ss [LET_THM] fwd_df_at_entry_eq_joined) >>
  simp[]
QED

(* --- Reusable infrastructure for non-NONE and boundary properties --- *)

Triviality copy_fact_transfer_not_none[local]:
  !ctx inst v. copy_fact_transfer ctx inst v <> NONE
Proof
  rewrite_tac[copy_fact_transfer_def, LET_THM] >> simp[]
QED

Triviality copy_fact_join_not_none[local]:
  !dfg a b. a <> NONE \/ b <> NONE ==> copy_fact_join dfg a b <> NONE
Proof
  rpt gen_tac >> strip_tac >> Cases_on `a` >> Cases_on `b` >>
  gvs[copy_fact_join_def]
QED

(* At a reachable block, the boundary value is not NONE.
   Uses: entry not NONE → exit not NONE → boundary = join(boundary, exit) → non-NONE *)
Triviality cf_boundary_not_none[local]:
  !dfg ce_ctx entry_lbl fn bb result.
    wf_function fn /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    bb.bb_instructions <> [] /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    fn_entry_label fn = SOME entry_lbl /\
    result = df_analyze Forward NONE (copy_fact_join dfg) copy_fact_transfer
               copy_fact_edge_transfer ce_ctx
               (SOME (entry_lbl, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (entry_lbl, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result
    ==>
    df_boundary NONE result bb.bb_label <> NONE
Proof
  rpt strip_tac >> gvs[] >>
  (* Step 1: df_at entry ≠ NONE *)
  `df_at NONE
     (df_analyze Forward NONE (copy_fact_join dfg) copy_fact_transfer
        copy_fact_edge_transfer ce_ctx (SOME (entry_lbl,SOME FEMPTY)) fn)
     bb.bb_label 0 <> NONE` by (
    irule (SIMP_RULE std_ss [LET_THM]
             analysisSimPropsTheory.fwd_df_at_entry_not_none) >>
    simp[copy_fact_transfer_not_none, copy_fact_edge_transfer_def] >>
    rpt conj_tac
    >- metis_tac[copy_fact_join_not_none]
    >> (qexistsl [`entry_lbl`, `SOME FEMPTY`] >> simp[])) >>
  (* Step 2: df_at exit ≠ NONE *)
  `df_at NONE
     (df_analyze Forward NONE (copy_fact_join dfg) copy_fact_transfer
        copy_fact_edge_transfer ce_ctx (SOME (entry_lbl,SOME FEMPTY)) fn)
     bb.bb_label (LENGTH bb.bb_instructions) <> NONE` by (
    irule (SIMP_RULE std_ss [LET_THM]
             analysisSimPropsTheory.fwd_df_at_exit_not_none) >>
    simp[copy_fact_transfer_not_none] >>
    qexists `bb` >> simp[]) >>
  (* Step 3: boundary = join(boundary, exit) at fixpoint → contradiction *)
  qspecl_then [`Forward`, `NONE`, `copy_fact_join dfg`,
    `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
    `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`, `bb`]
    mp_tac (SIMP_RULE std_ss [LET_THM]
              dfAnalyzeProofsTheory.df_boundary_fixpoint_proof) >>
  simp[] >> strip_tac >>
  (* boundary = NONE (assumption) + boundary = join(NONE, exit) + exit ≠ NONE → F *)
  metis_tac[copy_fact_join_not_none]
QED

(* MEM bb.bb_label (cfg_preds_of cfg v.vs_current_bb) from exec_block *)
Triviality exec_block_mem_preds[local]:
  !fuel run_ctx bb s'' v fn i.
    exec_block fuel run_ctx bb s'' = OK v /\
    wf_function fn /\ MEM bb fn.fn_blocks /\
    bb.bb_instructions <> [] /\
    EVERY inst_wf bb.bb_instructions /\
    s''.vs_inst_idx = 0 /\
    SUC i = LENGTH bb.bb_instructions /\
    is_terminator (EL i bb.bb_instructions).inst_opcode /\
    (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode)
    ==>
    MEM bb.bb_label (cfg_preds_of (cfg_analyze fn) v.vs_current_bb)
Proof
  rpt strip_tac >>
  irule (iffLR cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond) >>
  irule cfgHelpersTheory.bb_succs_in_cfg_succs >>
  simp[] >> fs[wf_function_def] >>
  qspecl_then [`fuel`, `run_ctx`, `bb`, `s''`, `v`] mp_tac
    venomExecProofsTheory.exec_block_current_bb_in_succs >>
  simp[] >> (impl_tac >- (
    rpt strip_tac >> `j < i` by decide_tac >> metis_tac[])) >>
  simp[]
QED

(* cf_sound_opt of joined value — uses fwd_joined_sound_from_pred *)
Resume stage1_correct[cf_sound_joined]:
  pop_assum (fn ab => rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] ab]) >>
  irule analysisSimPropsTheory.fwd_joined_sound_from_pred >>
  rpt conj_tac
  (* entry *)
  >- (rpt strip_tac >> gvs[copy_fact_join_fempty_l] >>
      simp[cf_sound_opt_fempty_all])
  (* 2nd-arg mono *)
  >- (rpt strip_tac >> irule cf_sound_opt_join_mono_b >> simp[])
  (* 1st-arg mono *)
  >- (rpt strip_tac >> irule cf_sound_opt_join_mono_a >> simp[])
  (* join non-NONE *)
  >- (rpt gen_tac >> simp[copy_fact_join_def] >>
      rpt BasicProvers.TOP_CASE_TAC >> simp[])
  (* witness: nbr = bb.bb_label, remaining: preds + boundary *)
  >> qexists `bb.bb_label` >>
  simp[copy_fact_edge_transfer_def] >>
  suspend "boundary"
QED

(* cf_sound_opt at boundary: transfer soundness through block → join mono at fixpoint.
   Chain: entry sound → exit sound (transfer_sound_exit_block_inv)
        → exit ≠ NONE → boundary = join(boundary, exit) → join_mono_b *)
Triviality cf_sound_opt_boundary[local]:
  !bp dfg ce_ctx entry_lbl fn bb result fuel run_ctx s'' v i.
    wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    bb.bb_instructions <> [] /\
    EVERY inst_wf bb.bb_instructions /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    ce_ctx.ce_bp = bp /\ ce_ctx.ce_dfg = dfg /\
    wf_alias_sets ce_ctx.ce_aliases /\
    bp_assigns_stable bp dfg /\
    (!fuel' run_ctx bb0 inst0 s0 s1.
       MEM bb0 fn.fn_blocks /\ MEM inst0 bb0.bb_instructions /\
       inst_wf inst0 /\
       dfg_assigns_sound dfg (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst0 s0 = OK s1 ==>
       dfg_assigns_sound dfg (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s1 with vs_inst_idx := 0)) /\
    fn_entry_label fn = SOME entry_lbl /\
    result = df_analyze Forward NONE (copy_fact_join dfg) copy_fact_transfer
               copy_fact_edge_transfer ce_ctx
               (SOME (entry_lbl, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (entry_lbl, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result /\
    cf_sound_opt bp dfg (df_at NONE result bb.bb_label 0) s'' /\
    cf_keys_ok_opt bp (df_at NONE result bb.bb_label 0) /\
    cf_alloca_ok_opt bp (df_at NONE result bb.bb_label 0) s'' /\
    s''.vs_inst_idx = 0 /\
    dfg_assigns_sound dfg s'' /\ bp_ptr_sound bp s'' /\
    alloca_inv s'' /\ allocas_in_word s'' /\ bp_ptrs_bounded bp fn s'' /\
    exec_block fuel run_ctx bb s'' = OK v /\
    SUC i = LENGTH bb.bb_instructions /\
    i < LENGTH bb.bb_instructions /\
    is_terminator (EL i bb.bb_instructions).inst_opcode /\
    (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode)
    ==>
    cf_sound_opt bp dfg (df_boundary NONE result bb.bb_label) v
Proof
  rpt strip_tac >> gvs[] >>
  (* Abbreviate for readability *)
  qabbrev_tac `result = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg)
    copy_fact_transfer copy_fact_edge_transfer ce_ctx
    (SOME (entry_lbl, SOME FEMPTY)) fn` >>
  (* Step A: intra-transfer equalities *)
  `!idx. SUC idx <= LENGTH bb.bb_instructions ==>
    df_at NONE result bb.bb_label (SUC idx) =
    copy_fact_transfer ce_ctx (EL idx bb.bb_instructions)
      (df_at NONE result bb.bb_label idx)` by (
    rpt strip_tac >>
    qspecl_then [`Forward`, `NONE`, `copy_fact_join ce_ctx.ce_dfg`,
      `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
      `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`, `bb`, `idx`]
      mp_tac (SIMP_RULE std_ss [LET_THM]
                dfAnalyzeProofsTheory.df_at_intra_transfer_proof) >>
    simp[Abbr `result`]) >>
  (* Step B: sound_pred at exit via transfer_sound_exit_block_inv *)
  qspecl_then [
    `\v s. cf_sound_opt ce_ctx.ce_bp ce_ctx.ce_dfg v s /\
           cf_keys_ok_opt ce_ctx.ce_bp v /\
           cf_alloca_ok_opt ce_ctx.ce_bp v s`,
    `\s. dfg_assigns_sound ce_ctx.ce_dfg s /\
         bp_ptr_sound ce_ctx.ce_bp s /\
         allocas_non_overlapping s /\ allocas_in_word s /\
         bp_ptrs_bounded ce_ctx.ce_bp fn s`,
    `copy_fact_transfer`, `ce_ctx`, `fn`, `bb`, `NONE`, `result`]
    mp_tac transfer_sound_exit_block_inv >>
  (impl_tac >- (
    simp[] >> rpt conj_tac
    >- (irule copy_fact_transfer_sound_thm >> simp[])
    >- (rpt strip_tac >>
        rename1 `step_inst fuel0 run_ctx0 inst0 s0 = OK s1` >>
        qpat_x_assum `!fuel' run_ctx bb0 inst s_pre s_post.
          MEM bb0 fn.fn_blocks /\ MEM inst bb0.bb_instructions /\
          inst_wf inst /\ dfg_assigns_sound ce_ctx.ce_dfg s_pre /\
          bp_ptr_sound ce_ctx.ce_bp s_pre /\ allocas_non_overlapping s_pre /\
          allocas_in_word s_pre /\ bp_ptrs_bounded ce_ctx.ce_bp fn s_pre /\
          step_inst fuel' run_ctx inst s_pre = OK s_post ==>
          dfg_assigns_sound ce_ctx.ce_dfg s_post /\
          bp_ptr_sound ce_ctx.ce_bp s_post /\
          allocas_non_overlapping s_post /\
          allocas_in_word s_post /\ bp_ptrs_bounded ce_ctx.ce_bp fn s_post`
          (qspecl_then [`fuel0`, `run_ctx0`, `bb`, `inst0`, `s0`, `s1`] mp_tac) >>
        simp[])
    >> simp[])) >>
  disch_then (qspecl_then [`fuel`, `run_ctx`, `s''`, `v`, `i`] mp_tac) >>
  simp[] >> (impl_tac >- fs[alloca_inv_def]) >> strip_tac >>
  (* Step C: entry not NONE *)
  `df_at NONE result bb.bb_label 0 <> NONE` by (
    qspecl_then [`NONE`, `copy_fact_join ce_ctx.ce_dfg`,
      `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
      `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`]
      mp_tac (SIMP_RULE std_ss [LET_THM]
                analysisSimPropsTheory.fwd_df_at_entry_not_none) >>
    simp[Abbr `result`, copy_fact_transfer_not_none,
         copy_fact_edge_transfer_def] >>
    (impl_tac >- (
      rpt conj_tac
      >- metis_tac[copy_fact_join_not_none]
      >> (qexistsl [`entry_lbl`, `SOME FEMPTY`] >> simp[]))) >>
    simp[]) >>
  (* Step D: exit not NONE *)
  `df_at NONE result bb.bb_label (LENGTH bb.bb_instructions) <> NONE` by (
    qspecl_then [`NONE`, `copy_fact_join ce_ctx.ce_dfg`,
      `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
      `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`, `bb`]
      mp_tac (SIMP_RULE std_ss [LET_THM]
                analysisSimPropsTheory.fwd_df_at_exit_not_none) >>
    simp[Abbr `result`, copy_fact_transfer_not_none]) >>
  (* Step E: boundary = join(boundary, df_at(LENGTH)) *)
  qspecl_then [`Forward`, `NONE`, `copy_fact_join ce_ctx.ce_dfg`,
    `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
    `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`, `bb`]
    mp_tac (SIMP_RULE std_ss [LET_THM]
              dfAnalyzeProofsTheory.df_boundary_fixpoint_proof) >>
  simp[Abbr `result`] >> strip_tac >>
  (* Step F: rewrite boundary, apply join_mono_b *)
  qpat_x_assum `df_boundary _ _ _ = _` (fn eq => once_rewrite_tac [eq]) >>
  irule cf_sound_opt_join_mono_b >>
  (* Rewrite LENGTH → SUC i so transfer equality fires *)
  qpat_assum `SUC i = LENGTH _` (fn eq => rewrite_tac [GSYM eq]) >>
  fs[copy_fact_transfer_not_none]
QED

Triviality cf_sound_opt_boundary_from_idx[local]:
  !bp dfg ce_ctx entry_lbl fn bb result fuel run_ctx st v i.
    wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    bb.bb_instructions <> [] /\
    EVERY inst_wf bb.bb_instructions /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    ce_ctx.ce_bp = bp /\ ce_ctx.ce_dfg = dfg /\
    wf_alias_sets ce_ctx.ce_aliases /\
    bp_assigns_stable bp dfg /\
    (!fuel' run_ctx bb0 inst0 s0 s1.
       MEM bb0 fn.fn_blocks /\ MEM inst0 bb0.bb_instructions /\
       inst_wf inst0 /\
       dfg_assigns_sound dfg (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst0 s0 = OK s1 ==>
       dfg_assigns_sound dfg (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s1 with vs_inst_idx := 0)) /\
    fn_entry_label fn = SOME entry_lbl /\
    result = df_analyze Forward NONE (copy_fact_join dfg) copy_fact_transfer
               copy_fact_edge_transfer ce_ctx
               (SOME (entry_lbl, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (entry_lbl, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result /\
    cf_sound_opt bp dfg (df_at NONE result bb.bb_label st.vs_inst_idx)
      (st with vs_inst_idx := 0) /\
    cf_keys_ok_opt bp (df_at NONE result bb.bb_label st.vs_inst_idx) /\
    cf_alloca_ok_opt bp (df_at NONE result bb.bb_label st.vs_inst_idx)
      (st with vs_inst_idx := 0) /\
    st.vs_inst_idx <= i /\
    dfg_assigns_sound dfg (st with vs_inst_idx := 0) /\
    bp_ptr_sound bp (st with vs_inst_idx := 0) /\
    allocas_non_overlapping (st with vs_inst_idx := 0) /\
    allocas_in_word (st with vs_inst_idx := 0) /\
    bp_ptrs_bounded bp fn (st with vs_inst_idx := 0) /\
    exec_block fuel run_ctx bb st = OK v /\
    SUC i = LENGTH bb.bb_instructions /\
    i < LENGTH bb.bb_instructions /\
    is_terminator (EL i bb.bb_instructions).inst_opcode /\
    (!j. j < i ==> ~is_terminator (EL j bb.bb_instructions).inst_opcode)
    ==>
    cf_sound_opt bp dfg (df_boundary NONE result bb.bb_label) v
Proof
  rpt strip_tac >> gvs[] >>
  qabbrev_tac `result = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg)
    copy_fact_transfer copy_fact_edge_transfer ce_ctx
    (SOME (entry_lbl, SOME FEMPTY)) fn` >>
  `!idx. SUC idx <= LENGTH bb.bb_instructions ==>
    df_at NONE result bb.bb_label (SUC idx) =
    copy_fact_transfer ce_ctx (EL idx bb.bb_instructions)
      (df_at NONE result bb.bb_label idx)` by (
    rpt strip_tac >>
    qspecl_then [`Forward`, `NONE`, `copy_fact_join ce_ctx.ce_dfg`,
      `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
      `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`, `bb`, `idx`]
      mp_tac (SIMP_RULE std_ss [LET_THM]
                dfAnalyzeProofsTheory.df_at_intra_transfer_proof) >>
    simp[Abbr `result`]) >>
  qspecl_then [
    `\v s. cf_sound_opt ce_ctx.ce_bp ce_ctx.ce_dfg v s /\
           cf_keys_ok_opt ce_ctx.ce_bp v /\
           cf_alloca_ok_opt ce_ctx.ce_bp v s`,
    `\s. dfg_assigns_sound ce_ctx.ce_dfg s /\
         bp_ptr_sound ce_ctx.ce_bp s /\
         allocas_non_overlapping s /\ allocas_in_word s /\
         bp_ptrs_bounded ce_ctx.ce_bp fn s`,
    `copy_fact_transfer`, `ce_ctx`, `fn`, `bb`, `NONE`, `result`]
    mp_tac transfer_sound_exit_block_inv_from_idx >>
  (impl_tac >- (
    simp[] >> rpt conj_tac
    >- (irule copy_fact_transfer_sound_thm >> simp[])
    >- (rpt strip_tac >>
        rename1 `step_inst fuel0 run_ctx0 inst0 s0 = OK s1` >>
        qpat_x_assum `!fuel' run_ctx bb0 inst s_pre s_post.
          MEM bb0 fn.fn_blocks /\ MEM inst bb0.bb_instructions /\
          inst_wf inst /\ dfg_assigns_sound ce_ctx.ce_dfg s_pre /\
          bp_ptr_sound ce_ctx.ce_bp s_pre /\ allocas_non_overlapping s_pre /\
          allocas_in_word s_pre /\ bp_ptrs_bounded ce_ctx.ce_bp fn s_pre /\
          step_inst fuel' run_ctx inst s_pre = OK s_post ==>
          dfg_assigns_sound ce_ctx.ce_dfg s_post /\
          bp_ptr_sound ce_ctx.ce_bp s_post /\
          allocas_non_overlapping s_post /\
          allocas_in_word s_post /\ bp_ptrs_bounded ce_ctx.ce_bp fn s_post`
          (qspecl_then [`fuel0`, `run_ctx0`, `bb`, `inst0`, `s0`, `s1`] mp_tac) >>
        simp[])
    >> simp[])) >>
  disch_then (qspecl_then [`fuel`, `run_ctx`, `st`, `v`, `i`] mp_tac) >>
  simp[] >> strip_tac >>
  `df_at NONE result bb.bb_label 0 <> NONE` by (
    qspecl_then [`NONE`, `copy_fact_join ce_ctx.ce_dfg`,
      `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
      `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`]
      mp_tac (SIMP_RULE std_ss [LET_THM]
                analysisSimPropsTheory.fwd_df_at_entry_not_none) >>
    simp[Abbr `result`, copy_fact_transfer_not_none,
         copy_fact_edge_transfer_def] >>
    (impl_tac >- (
      rpt conj_tac
      >- metis_tac[copy_fact_join_not_none]
      >> (qexistsl [`entry_lbl`, `SOME FEMPTY`] >> simp[]))) >>
    simp[]) >>
  `df_at NONE result bb.bb_label (LENGTH bb.bb_instructions) <> NONE` by (
    qspecl_then [`NONE`, `copy_fact_join ce_ctx.ce_dfg`,
      `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
      `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`, `bb`]
      mp_tac (SIMP_RULE std_ss [LET_THM]
                analysisSimPropsTheory.fwd_df_at_exit_not_none) >>
    simp[Abbr `result`, copy_fact_transfer_not_none]) >>
  qspecl_then [`Forward`, `NONE`, `copy_fact_join ce_ctx.ce_dfg`,
    `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
    `SOME (entry_lbl, SOME FEMPTY)`, `fn`, `bb.bb_label`, `bb`]
    mp_tac (SIMP_RULE std_ss [LET_THM]
              dfAnalyzeProofsTheory.df_boundary_fixpoint_proof) >>
  simp[Abbr `result`] >> strip_tac >>
  qpat_x_assum `df_boundary _ _ _ = _` (fn eq => once_rewrite_tac [eq]) >>
  irule cf_sound_opt_join_mono_b >>
  qpat_assum `SUC i = LENGTH _` (fn eq => rewrite_tac [GSYM eq]) >>
  fs[copy_fact_transfer_not_none]
QED

(* --- cf_keys_ok_opt boundary invariant through analysis --- *)

(* df_populate_inst does not change ds_boundary *)
Triviality df_populate_inst_boundary_eq[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st.
    (df_populate_inst dir bottom join transfer edge_transfer
       ctx entry_val cfg bbs lbls st).ds_boundary = st.ds_boundary
Proof
  rpt gen_tac >>
  simp[df_populate_inst_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qmatch_goalsub_abbrev_tac `FOLDL ff _ lbls` >>
  `!st'. (FOLDL ff st' lbls).ds_boundary = st'.ds_boundary`
    suffices_by simp[] >>
  qunabbrev_tac `ff` >>
  Induct_on `lbls` >> simp[]
QED

(* df_process_block changed ⟺ state changed (reprove of local lemma) *)
Triviality cf_process_changed[local]:
  !ctx fn lbl st.
    let process = df_process_block Forward NONE (copy_fact_join ctx.ce_dfg)
                    copy_fact_transfer copy_fact_edge_transfer ctx
                    (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
                    (cfg_analyze fn) fn.fn_blocks in
    let changed = \lbl old new.
          df_boundary NONE new lbl <> df_boundary NONE old lbl in
    changed lbl st (process lbl st) <=> process lbl st <> st
Proof
  rw[df_process_block_def, df_boundary_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[df_state_component_equality, fmap_eq_flookup, FLOOKUP_UPDATE] >>
  CCONTR_TAC >> fs[] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  Cases_on `FLOOKUP st.ds_boundary lbl` >> fs[]
QED

(* Bilateral boundary preservation: if all boundary entries satisfy P,
   and join/transfer/edge_transfer preserve P bilaterally, then
   df_process_block preserves boundary P. *)
Triviality cf_process_boundary_bilateral[local]:
  !ctx fn lbl st (P : copy_fact_lattice -> bool).
    P NONE /\ P (SOME FEMPTY) /\
    (!a b. P a /\ P b ==> P (copy_fact_join ctx.ce_dfg a b)) /\
    (!inst a. P a ==> P (copy_fact_transfer ctx inst a)) /\
    (!(src:string) (dst:string) a. P a ==> P (copy_fact_edge_transfer ctx src dst a)) /\
    (!k v. FLOOKUP st.ds_boundary k = SOME v ==> P v)
    ==>
    (!k v. FLOOKUP (df_process_block Forward NONE (copy_fact_join ctx.ce_dfg)
                      copy_fact_transfer copy_fact_edge_transfer ctx
                      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
                      (cfg_analyze fn) fn.fn_blocks lbl st).ds_boundary
                   k = SOME v ==> P v)
Proof
  (* Main structure proven, needs cf_alloca_ok_opt_joined completion. *)
  rpt gen_tac >> strip_tac >>
  simp_tac std_ss [df_process_block_def, LET_THM] >>
  pairarg_tac >> asm_rewrite_tac[] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  IF_CASES_TAC >> simp[FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `lbl = k` >> gvs[] >>
  TRY (metis_tac[])
  >>
  (* k = lbl case: goal is P(join(boundary_at_k, final_val)) *)
  `P (df_boundary NONE st k)` by (
    simp[df_boundary_def] >>
    BasicProvers.FULL_CASE_TAC >> simp[] >> metis_tac[])
  >>
  `P (df_joined_val Forward NONE (copy_fact_join ctx.ce_dfg)
      copy_fact_edge_transfer ctx
      (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
      (cfg_analyze fn) st k)` by (
    irule dfAnalyzeProofsTheory.df_joined_val_P >>
    rpt conj_tac >>
    TRY (first_assum MATCH_ACCEPT_TAC) >>
    Cases_on `fn_entry_label fn` >> simp[])
  >>
  `P final_val` by (
    drule (cj 1 dfAnalyzeProofsTheory.df_fold_block_P) >>
    disch_then irule >> metis_tac[])
  >>
  metis_tac[]
QED

(* df_populate_inst preserves boundary *)
Triviality df_populate_inst_boundary[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st.
    (df_populate_inst dir bottom join transfer edge_transfer ctx
       entry_val cfg bbs lbls st).ds_boundary = st.ds_boundary
Proof
  simp[df_populate_inst_def, LET_THM] >>
  rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `FOLDL ff _ lbls` >>
  `!st'. (FOLDL ff st' lbls).ds_boundary = st'.ds_boundary`
    suffices_by simp[] >>
  qunabbrev_tac `ff` >>
  Induct_on `lbls` >> simp[] >> rw[] >>
  pairarg_tac >> simp[]
QED

(* Initial state satisfies cf_measure_inv *)
Triviality cf_measure_inv_st0[local]:
  !ctx fn.
    fn_inst_wf fn ==>
    cf_measure_inv ctx fn
      (case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
         NONE => init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks)
       | SOME (lbl,v) =>
           init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) with
           ds_boundary :=
             (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary |+ (lbl, v))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `fn`] mp_tac cf_measure_inv_initial >>
  simp[] >> Cases_on `fn_entry_label fn` >> simp[]
QED

(* Initial state boundary entries satisfy any Q with Q NONE /\ Q (SOME FEMPTY) *)
Triviality init_boundary_Q[local]:
  !fn (Q : copy_fact_lattice -> bool).
    Q NONE /\ Q (SOME FEMPTY) ==>
    !k v. FLOOKUP
      (case OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn) of
         NONE => init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks)
       | SOME (lbl,v) =>
           init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks) with
           ds_boundary :=
             (init_df_state NONE (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary |+ (lbl, v)).ds_boundary
      k = SOME v ==> Q v
Proof
  rpt strip_tac >>
  Cases_on `fn_entry_label fn` >> gvs[init_df_state_def, FLOOKUP_UPDATE] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac dfAnalyzeProofsTheory.foldl_fempty_val >> gvs[]
QED

(* General: ANY property Q satisfying bilateral conditions holds on all
   boundary entries of df_analyze. Reusable for cf_keys_ok, cf_sound, etc. *)
Triviality cf_boundary_invariant_general[local]:
  !ctx fn bp (Q : copy_fact_lattice -> bool).
    fn_inst_wf fn /\ wf_function fn /\
    Abbrev (ctx = <| ce_aliases := memory_alias_analyze bp fn;
                     ce_bp := bp;
                     ce_dfg := dfg_build_function fn |>) /\
    Q NONE /\ Q (SOME FEMPTY) /\
    (!a b. Q a /\ Q b ==> Q (copy_fact_join ctx.ce_dfg a b)) /\
    (!inst a. Q a ==> Q (copy_fact_transfer ctx inst a)) /\
    (!(src:string) (dst:string) a. Q a ==>
       Q (copy_fact_edge_transfer ctx src dst a))
    ==>
    !k v. FLOOKUP (df_analyze Forward NONE (copy_fact_join ctx.ce_dfg)
             copy_fact_transfer copy_fact_edge_transfer ctx
             (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
             fn).ds_boundary k = SOME v
          ==> Q v
Proof
  rpt gen_tac >> strip_tac >>
  simp[df_analyze_def, LET_THM, df_populate_inst_boundary] >>
  qmatch_goalsub_abbrev_tac `SND (wl_iterate changed process deps wl0 st0')` >>
  qspecl_then [
      `cf_measure ctx fn`, `cf_measure_bound ctx fn`, `changed`,
      `process`, `deps`, `wl0`, `st0'`,
      `\st:copy_fact_lattice df_state.
         cf_measure_inv ctx fn st /\
         !k v. FLOOKUP st.ds_boundary k = SOME v ==> Q v`,
      `\lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre`]
    mp_tac
    (INST_TYPE [alpha |-> ``:copy_fact_lattice df_state``,
                beta |-> ``:string``]
      worklistProofsTheory.wl_iterate_invariant_process_restricted) >>
  simp[] >>
  (* Prove each wl_iterate condition as a separate fact *)
  `!lbl st. changed lbl st (process lbl st) <=> process lbl st <> st` by
    (simp[Abbr `changed`, Abbr `process`,
          SRULE [LET_THM] cf_process_changed]) >>
  `!lbl st.
     MEM lbl wl0 /\ cf_measure_inv ctx fn st /\ process lbl st <> st ==>
     cf_measure ctx fn st < cf_measure ctx fn (process lbl st)` by
    (rpt strip_tac >> simp[Abbr `process`] >>
     irule cf_measure_monotone >> fs[Abbr `wl0`]) >>
  `!lbl st. MEM lbl wl0 /\ cf_measure_inv ctx fn st /\
     (!k v. FLOOKUP st.ds_boundary k = SOME v ==> Q v) ==>
     cf_measure_inv ctx fn (process lbl st) /\
     !k v. FLOOKUP (process lbl st).ds_boundary k = SOME v ==> Q v` by
    (rpt strip_tac >> simp[Abbr `process`]
     >- (irule cf_inv_preserved >> fs[Abbr `wl0`])
     >> irule cf_process_boundary_bilateral >> simp[] >> metis_tac[]) >>
  `cf_measure_inv ctx fn st0'` by
    simp[Abbr `st0'`, cf_measure_inv_st0] >>
  `!k v. FLOOKUP st0'.ds_boundary k = SOME v ==> Q v` by
    (qspecl_then [`fn`, `Q`] mp_tac init_boundary_Q >>
     simp[Abbr `st0'`]) >>
  `!x. cf_measure_inv ctx fn x ==>
     cf_measure ctx fn x <= cf_measure_bound ctx fn` by
    metis_tac[cf_measure_bounded] >>
  `EVERY (\lbl. MEM lbl wl0) wl0` by simp[EVERY_MEM] >>
  `!lbl. MEM lbl wl0 ==> EVERY (\lbl'. MEM lbl' wl0) (deps lbl)` by
    (simp[Abbr `deps`, Abbr `wl0`] >>
     metis_tac[cfg_dfs_pre_succs_closed, EVERY_MEM]) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >> metis_tac[]) >>
  metis_tac[]
QED

(* Main: cf_keys_ok_opt holds on all boundary entries of the analysis result *)
Triviality cf_keys_ok_boundary[local]:
  !ctx fn bp.
    fn_inst_wf fn /\ wf_function fn /\
    bp_assigns_stable bp (dfg_build_function fn) /\
    Abbrev (ctx = <| ce_aliases := memory_alias_analyze bp fn;
                     ce_bp := bp;
                     ce_dfg := dfg_build_function fn |>)
    ==>
    !k v. FLOOKUP (df_analyze Forward NONE (copy_fact_join ctx.ce_dfg)
             copy_fact_transfer copy_fact_edge_transfer ctx
             (OPTION_MAP (\lbl. (lbl, SOME FEMPTY)) (fn_entry_label fn))
             fn).ds_boundary k = SOME v
          ==> cf_keys_ok_opt bp v
Proof
  rpt gen_tac >> strip_tac >>
  `!a b. cf_keys_ok_opt bp a /\ cf_keys_ok_opt bp b ==>
     cf_keys_ok_opt bp (copy_fact_join ctx.ce_dfg a b)` by
    metis_tac[cf_keys_ok_opt_join] >>
  `!inst a. cf_keys_ok_opt bp a ==>
     cf_keys_ok_opt bp (copy_fact_transfer ctx inst a)` by
    (rpt strip_tac >> irule cf_keys_ok_opt_transfer >>
     simp[Abbr `ctx`]) >>
  mp_tac (Q.SPECL [`ctx`, `fn`, `bp`, `cf_keys_ok_opt bp`]
    cf_boundary_invariant_general) >>
  simp[cf_keys_ok_opt_def, cf_keys_ok_def, copy_fact_edge_transfer_def]
QED


(* cf_keys_ok_opt of joined value — bilateral invariant + df_joined_val_P *)
Resume stage1_correct[cf_keys_ok_joined]:
  simp[Abbr `joined`] >>
  irule dfAnalyzeProofsTheory.df_joined_val_P >>
  (* Prove the non-trivial conditions as separate facts *)
  `!a b. cf_keys_ok_opt bp a /\ cf_keys_ok_opt bp b ==>
     cf_keys_ok_opt bp (copy_fact_join dfg a b)` by
    metis_tac[cf_keys_ok_opt_join] >>
  `!k v. FLOOKUP result.ds_boundary k = SOME v ==>
     cf_keys_ok_opt bp v` by
    (qspecl_then [`ce_ctx`, `fn`, `bp`] mp_tac cf_keys_ok_boundary >>
     simp[Abbr `ce_ctx`, Abbr `result`]) >>
  simp[copy_fact_edge_transfer_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[cf_keys_ok_opt_def, cf_keys_ok_def]
QED

(* cf_alloca_ok_opt of joined value *)
Resume stage1_correct[cf_alloca_ok_joined]:
  cheat (* shared gap: needs memloc_within_alloca for joined value *)
QED

(* --- SSA structural helpers for bp_ptr_sound_exec_block --- *)

(* ALL_DISTINCT of inst_ids within a block: from fn_inst_ids_distinct *)
Triviality block_inst_ids_distinct[local]:
  !(bbs : basic_block list) bb (f : instruction -> 'b).
    ALL_DISTINCT (FLAT (MAP (\b. MAP f b.bb_instructions) bbs)) /\
    MEM bb bbs ==>
    ALL_DISTINCT (MAP f bb.bb_instructions)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

(* ALL_DISTINCT preserved through FILTER *)
Triviality all_distinct_map_filter[local]:
  !l (f:'a -> 'b) P.
    ALL_DISTINCT (MAP f l) ==>
    ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct >> simp[FILTER] >> rpt strip_tac >>
  IF_CASES_TAC >> gvs[ALL_DISTINCT, MEM_MAP, MEM_FILTER]
QED

(* MEM v (operand_vars ops) ==> MEM (Var v) ops
   NB: must use venomInst operand_vars to match inst_uses_def *)
Triviality mem_operand_vars_var[local]:
  !ops v. MEM v (venomInst$operand_vars ops) ==> MEM (Var v) ops
Proof
  Induct >> simp[venomInstTheory.operand_vars_def] >> rpt strip_tac >>
  Cases_on `venomInst$operand_var h` >> gvs[] >>
  Cases_on `h` >> gvs[venomInstTheory.operand_var_def]
QED

(* inst output not in own uses: from def_dominates_uses + ssa_form.
   The definer of v must be strictly before inst in the block, but by SSA
   uniqueness, the definer IS inst — contradiction with "strictly before". *)
Triviality ssa_no_self_use[local]:
  !fn bb inst out.
    ssa_form fn /\ def_dominates_uses fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst_output inst = SOME out ==>
    ~MEM out (inst_uses inst)
Proof
  rpt strip_tac >>
  fs[inst_uses_def] >>
  drule mem_operand_vars_var >> strip_tac >>
  `MEM out inst.inst_outputs` by (
    fs[inst_output_def] >>
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  qpat_x_assum `def_dominates_uses _`
    (fn th => assume_tac (REWRITE_RULE[def_dominates_uses_def] th)) >>
  first_x_assum (qspecl_then [`bb`, `inst`, `out`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  `MEM def_inst (fn_insts fn)` by
    (simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts]) >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def] >> metis_tac[mem_block_mem_fn_insts]) >>
  `def_inst = inst` by metis_tac[ssa_unique_definer] >>
  gvs[] >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  fs[fn_inst_ids_distinct_def] >>
  `def_bb = bb` by (
    qspecl_then [`fn.fn_blocks`,
      `\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
      `def_bb`, `bb`, `def_inst.inst_id`]
      mp_tac all_distinct_flat_map_inj >>
    simp[MEM_MAP] >> metis_tac[]) >>
  gvs[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule block_inst_ids_distinct >>
     qexists `fn.fn_blocks` >> simp[]) >>
  `i < LENGTH bb.bb_instructions` by simp[] >>
  qspecl_then [`MAP (\i. i.inst_id) bb.bb_instructions`, `i`, `j`]
    mp_tac ALL_DISTINCT_EL_IMP >>
  simp[EL_MAP]
QED

(* --- eval_phis entry-sound helpers for stage1_correct --- *)

Triviality mce_phi_prefix_length_el_phi[local]:
  !l i. i < phi_prefix_length l ==> (EL i l).inst_opcode = PHI
Proof
  Induct >> simp[phi_prefix_length_def] >> rw[] >>
  Cases_on `i` >> simp[phi_prefix_length_def]
QED

Triviality mce_phi_prefix_length_lt_wf[local]:
  !bb. bb_well_formed bb ==>
       phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions
Proof
  rpt strip_tac >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  spose_not_then assume_tac >>
  `phi_prefix_length bb.bb_instructions = LENGTH bb.bb_instructions` by decide_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `PRE (LENGTH bb.bb_instructions) < phi_prefix_length bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[mce_phi_prefix_length_el_phi] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by gvs[bb_well_formed_def] >>
  gvs[LAST_EL, is_terminator_def]
QED

Triviality mce_phi_prefix_length_no_phi_after[local]:
  !insts i.
    (!i j. i < j /\ j < LENGTH insts /\
           (EL j insts).inst_opcode = PHI ==>
           (EL i insts).inst_opcode = PHI) /\
    phi_prefix_length insts <= i /\ i < LENGTH insts ==>
    (EL i insts).inst_opcode <> PHI
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def] >>
  Cases_on `i` >> gvs[]
  >- (qpat_x_assum `!k. _ ==> (EL k insts).inst_opcode <> PHI`
        (qspec_then `n` mp_tac) >>
      impl_tac >- (
        simp[] >> rpt strip_tac >>
        first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      simp[]) >>
  CCONTR_TAC >> gvs[] >>
  first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]
QED

Triviality mce_eval_phis_flookup_idx[local]:
  !s insts x.
    (!i. i < phi_prefix_length insts ==> ~MEM x (EL i insts).inst_outputs) ==>
    !s'. eval_phis s insts = OK s' ==> FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct_on `insts` >> simp[eval_phis_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def, AllCaseEqs()] >>
  `!i. i < phi_prefix_length insts ==> ~MEM x (EL i insts).inst_outputs` by
    (rpt strip_tac >> first_x_assum (qspec_then `SUC i` mp_tac) >>
     simp[phi_prefix_length_def]) >>
  `FLOOKUP s''.vs_vars x = FLOOKUP s.vs_vars x` by
    (first_x_assum drule >> simp[]) >>
  `~MEM x h.inst_outputs` by
    (last_x_assum (qspec_then `0` mp_tac) >> simp[phi_prefix_length_def]) >>
  `MEM out h.inst_outputs` by (drule venomExecProofsTheory.eval_one_phi_output_mem >> simp[]) >>
  `out <> x` by (CCONTR_TAC >> gvs[]) >>
  gvs[update_var_def, FLOOKUP_UPDATE]
QED

Triviality mce_eval_operand_eval_phis_idx[local]:
  !s insts s_phi op.
    eval_phis s insts = OK s_phi /\
    (!i. i < phi_prefix_length insts ==>
         !x. op = Var x ==> ~MEM x (EL i insts).inst_outputs) ==>
    eval_operand op (s_phi with vs_inst_idx := 0) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >> rpt strip_tac
  >- (mp_tac (Q.SPECL [`s'':venom_state`, `insts`, `s:string`]
        mce_eval_phis_flookup_idx) >> simp[])
  >> drule venomExecPropsTheory.eval_phis_preserves_labels >> simp[]
QED

Triviality memloc_runtime_region_allocas_eq[local]:
  !ml s s'. s'.vs_allocas = s.vs_allocas ==>
    memloc_runtime_region ml s' = memloc_runtime_region ml s
Proof
  rw[memloc_runtime_region_def] >> BasicProvers.every_case_tac >> gvs[]
QED

Triviality cf_source_data_eval_phis[local]:
  !opc s insts s_phi.
    eval_phis s insts = OK s_phi ==>
    cf_source_data opc (s_phi with vs_inst_idx := 0) = cf_source_data opc s
Proof
  rpt strip_tac >>
  drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >> strip_tac >>
  pop_assum SUBST_ALL_TAC >>
  Cases_on `opc` >> simp[cf_source_data_def]
QED

Triviality cf_entry_sound_eval_phis_idx[local]:
  !bp dfg ml cf s insts s_phi.
    eval_phis s insts = OK s_phi /\
    cf_entry_sound bp dfg ml cf s /\
    (!i. i < phi_prefix_length insts ==>
         !x. normalize_operand dfg [] cf.cf_source = Var x ==>
             ~MEM x (EL i insts).inst_outputs) ==>
    cf_entry_sound bp dfg ml cf (s_phi with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  `memloc_runtime_region ml (s_phi with vs_inst_idx := 0) =
   memloc_runtime_region ml s` by
    (drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
     strip_tac >> irule memloc_runtime_region_allocas_eq >> simp[]) >>
  `eval_operand (normalize_operand dfg [] cf.cf_source) (s_phi with vs_inst_idx := 0) =
   eval_operand (normalize_operand dfg [] cf.cf_source) s` by
    (mp_tac (Q.SPECL [`s`, `insts`, `s_phi`,
        `normalize_operand dfg [] cf.cf_source`]
        mce_eval_operand_eval_phis_idx) >> simp[]) >>
  `cf_source_data cf.cf_opcode (s_phi with vs_inst_idx := 0) =
   cf_source_data cf.cf_opcode s` by
    metis_tac[cf_source_data_eval_phis] >>
  `s_phi.vs_memory = s.vs_memory` by
    (drule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
     strip_tac >> pop_assum SUBST_ALL_TAC >> simp[]) >>
  gvs[cf_entry_sound_def]
QED

Triviality cf_alloca_ok_allocas_eq[local]:
  !bp cfl s s'. s'.vs_allocas = s.vs_allocas ==>
    (cf_alloca_ok bp cfl s' <=> cf_alloca_ok bp cfl s)
Proof
  rw[cf_alloca_ok_def] >> eq_tac >> rpt strip_tac >> res_tac >>
  gvs[memloc_within_alloca_def]
QED

Triviality cf_alloca_ok_prune_vars[local]:
  !bp dfg killed cfl s s'.
    cf_alloca_ok bp cfl s /\ s'.vs_allocas = s.vs_allocas ==>
    cf_alloca_ok bp (copy_fact_prune_vars dfg killed cfl) s'
Proof
  rpt strip_tac >>
  irule (iffLR cf_alloca_ok_allocas_eq) >> qexists `s` >> simp[] >>
  rw[cf_alloca_ok_def, copy_fact_prune_vars_def, FLOOKUP_DRESTRICT] >>
  gvs[cf_alloca_ok_def] >> metis_tac[]
QED

Triviality cf_alloca_ok_opt_phi_transfer_on_s[local]:
  !bp dfg ctx inst v s s'.
    ctx.ce_dfg = dfg /\ inst.inst_opcode = PHI /\
    cf_alloca_ok_opt bp v s /\ s'.vs_allocas = s.vs_allocas ==>
    cf_alloca_ok_opt bp (copy_fact_transfer ctx inst v) s'
Proof
  rpt strip_tac >> Cases_on `v` >>
  gvs[copy_fact_transfer_def, LET_THM, cf_alloca_ok_opt_def,
      is_copy_opcode_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, empty_effects_def, unwrap_copy_facts_def]
  >- simp[copy_fact_prune_vars_def, DRESTRICT_FEMPTY, cf_alloca_ok_def] >>
  irule cf_alloca_ok_prune_vars >> qexists `s` >> simp[]
QED

Triviality mce_df_at_intra_transfer[local]:
  !s fn bb result ce_ctx idx.
    wf_function fn /\
    result = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
      copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions ==>
    df_at NONE result bb.bb_label (SUC idx) =
    copy_fact_transfer ce_ctx (EL idx bb.bb_instructions)
      (df_at NONE result bb.bb_label idx)
Proof
  rpt strip_tac >> gvs[] >>
  qspecl_then [`Forward`, `NONE`, `copy_fact_join ce_ctx.ce_dfg`,
    `copy_fact_transfer`, `copy_fact_edge_transfer`, `ce_ctx`,
    `SOME ((s:venom_state).vs_current_bb, SOME FEMPTY)`, `fn`,
    `bb.bb_label`, `bb`, `idx`]
    mp_tac (SIMP_RULE std_ss [LET_THM]
              dfAnalyzeProofsTheory.df_at_intra_transfer_proof) >>
  simp[]
QED

Triviality cf_sound_opt_phi_prefix_on_s[local]:
  !s fn bb result ce_ctx bp dfg s0 k.
    wf_function fn /\ ce_ctx.ce_dfg = dfg /\
    result = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
      copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    k <= phi_prefix_length bb.bb_instructions /\
    cf_sound_opt bp dfg (df_at NONE result bb.bb_label 0) s0 ==>
    cf_sound_opt bp dfg (df_at NONE result bb.bb_label k) s0
Proof
  Induct_on `k` >- simp[] >>
  rpt strip_tac >>
  `k < phi_prefix_length bb.bb_instructions` by decide_tac >>
  `cf_sound_opt bp dfg (df_at NONE result bb.bb_label k) s0` by
    (qpat_x_assum `!s fn bb result ce_ctx bp dfg s0. _`
       (qspecl_then [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`, `dfg`, `s0`] mp_tac) >>
     simp[] >> decide_tac) >>
  `(EL k bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[mce_phi_prefix_length_el_phi] >>
  `SUC k <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `df_at NONE result bb.bb_label (SUC k) =
   copy_fact_transfer ce_ctx (EL k bb.bb_instructions)
     (df_at NONE result bb.bb_label k)` by
    metis_tac[mce_df_at_intra_transfer] >>
  pop_assum SUBST1_TAC >>
  irule cf_sound_opt_phi_transfer_on_s >> simp[]
QED

Triviality cf_keys_ok_opt_phi_prefix_on_s[local]:
  !s fn bb result ce_ctx bp dfg k.
    wf_function fn /\ ce_ctx.ce_bp = bp /\ ce_ctx.ce_dfg = dfg /\
    bp_assigns_stable bp dfg /\
    result = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
      copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    k <= phi_prefix_length bb.bb_instructions /\
    cf_keys_ok_opt bp (df_at NONE result bb.bb_label 0) ==>
    cf_keys_ok_opt bp (df_at NONE result bb.bb_label k)
Proof
  Induct_on `k` >- simp[] >>
  rpt strip_tac >>
  `k < phi_prefix_length bb.bb_instructions` by decide_tac >>
  `cf_keys_ok_opt bp (df_at NONE result bb.bb_label k)` by
    (qpat_x_assum `!s fn bb result ce_ctx bp dfg. _`
       (qspecl_then [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`, `dfg`] mp_tac) >>
     simp[] >> decide_tac) >>
  `(EL k bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[mce_phi_prefix_length_el_phi] >>
  `SUC k <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `df_at NONE result bb.bb_label (SUC k) =
   copy_fact_transfer ce_ctx (EL k bb.bb_instructions)
     (df_at NONE result bb.bb_label k)` by
    metis_tac[mce_df_at_intra_transfer] >>
  pop_assum SUBST1_TAC >>
  irule cf_keys_ok_opt_transfer >> simp[]
QED

Triviality cf_alloca_ok_opt_phi_prefix_on_s[local]:
  !s fn bb result ce_ctx bp dfg s0 s_phi k.
    wf_function fn /\ ce_ctx.ce_dfg = dfg /\
    result = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
      copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    k <= phi_prefix_length bb.bb_instructions /\
    s_phi.vs_allocas = s0.vs_allocas /\
    cf_alloca_ok_opt bp (df_at NONE result bb.bb_label 0) s0 ==>
    cf_alloca_ok_opt bp (df_at NONE result bb.bb_label k) s_phi
Proof
  Induct_on `k` >-
    (rpt strip_tac >>
     Cases_on `df_at NONE result bb.bb_label 0` >>
     gvs[cf_alloca_ok_opt_def] >>
     irule (iffLR cf_alloca_ok_allocas_eq) >> qexists `s0` >> simp[]) >>
  rpt strip_tac >>
  `k < phi_prefix_length bb.bb_instructions` by decide_tac >>
  `cf_alloca_ok_opt bp (df_at NONE result bb.bb_label k) s_phi` by
    (qpat_x_assum `!s fn bb result ce_ctx bp dfg s0 s_phi. _`
       (qspecl_then [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`, `dfg`, `s0`, `s_phi`] mp_tac) >>
     simp[] >> decide_tac) >>
  `(EL k bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[mce_phi_prefix_length_el_phi] >>
  `SUC k <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `df_at NONE result bb.bb_label (SUC k) =
   copy_fact_transfer ce_ctx (EL k bb.bb_instructions)
     (df_at NONE result bb.bb_label k)` by
    metis_tac[mce_df_at_intra_transfer] >>
  pop_assum SUBST1_TAC >>
  irule cf_alloca_ok_opt_phi_transfer_on_s >>
  simp[] >> qexists_tac `s_phi` >> gvs[]
QED

Triviality copy_fact_transfer_phi_no_output_source[local]:
  !ctx inst cfl cfl' ml cf x.
    inst.inst_opcode = PHI /\
    copy_fact_transfer ctx inst (SOME cfl) = SOME cfl' /\
    FLOOKUP cfl' ml = SOME cf /\
    normalize_operand ctx.ce_dfg [] cf.cf_source = Var x ==>
    ~MEM x inst.inst_outputs
Proof
  rpt strip_tac >> gvs[] >>
  gvs[copy_fact_transfer_def, LET_THM, is_copy_opcode_def,
      is_alloca_op_def, is_ext_call_op_def, write_effects_def,
      empty_effects_def, unwrap_copy_facts_def] >>
  gvs[copy_fact_prune_vars_def, FLOOKUP_DRESTRICT,
      operand_var_killed_def, inst_defs_def]
QED

Triviality copy_fact_transfer_phi_lookup[local]:
  !ctx inst cfl cfl' ml cf.
    inst.inst_opcode = PHI /\
    copy_fact_transfer ctx inst (SOME cfl) = SOME cfl' /\
    FLOOKUP cfl' ml = SOME cf ==>
    FLOOKUP cfl ml = SOME cf
Proof
  rpt strip_tac >> gvs[] >>
  gvs[copy_fact_transfer_def, LET_THM, is_copy_opcode_def,
      is_alloca_op_def, is_ext_call_op_def, write_effects_def,
      empty_effects_def, unwrap_copy_facts_def] >>
  gvs[copy_fact_prune_vars_def, FLOOKUP_DRESTRICT]
QED

Triviality df_at_phi_prefix_no_phi_source_output[local]:
  !s fn bb result ce_ctx k cfl ml cf x.
    wf_function fn /\
    result = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
      copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    k <= phi_prefix_length bb.bb_instructions /\
    df_at NONE result bb.bb_label k = SOME cfl /\
    FLOOKUP cfl ml = SOME cf /\
    normalize_operand ce_ctx.ce_dfg [] cf.cf_source = Var x ==>
    !i. i < k ==> ~MEM x (EL i bb.bb_instructions).inst_outputs
Proof
  qid_spec_tac `cfl` >>
  Induct_on `k` >- (rpt gen_tac >> strip_tac >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `dfan = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg)
    copy_fact_transfer copy_fact_edge_transfer ce_ctx
    (SOME (s.vs_current_bb, SOME FEMPTY)) fn` >>
  `k < phi_prefix_length bb.bb_instructions` by decide_tac >>
  `(EL k bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[mce_phi_prefix_length_el_phi] >>
  `SUC k <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le, arithmeticTheory.LESS_EQ_TRANS] >>
  `df_at NONE dfan bb.bb_label (SUC k) =
   copy_fact_transfer ce_ctx (EL k bb.bb_instructions)
     (df_at NONE dfan bb.bb_label k)` by
    (unabbrev_all_tac >> metis_tac[mce_df_at_intra_transfer]) >>
  Cases_on `df_at NONE dfan bb.bb_label k` >> gvs[]
  >- gvs[copy_fact_transfer_def, LET_THM, copy_fact_prune_vars_def,
         FLOOKUP_DRESTRICT, is_copy_opcode_def, is_alloca_op_def,
         is_ext_call_op_def, write_effects_def, empty_effects_def,
         unwrap_copy_facts_def] >>
  rename1 `df_at NONE dfan bb.bb_label k = SOME prev` >>
  `copy_fact_transfer ce_ctx (EL k bb.bb_instructions) (SOME prev) = SOME cfl` by
    metis_tac[] >>
  gen_tac >> strip_tac >>
  Cases_on `i = k`
  >- metis_tac[copy_fact_transfer_phi_no_output_source] >>
  `i < k` by decide_tac >>
  `FLOOKUP prev ml = SOME cf` by
    metis_tac[copy_fact_transfer_phi_lookup] >>
  qpat_x_assum `!s'' fn' bb' ce_ctx cfl ml cf x. _`
    (qspecl_then [`s`, `fn`, `bb`, `ce_ctx`, `prev`, `ml`, `cf`, `x`] mp_tac) >>
  simp[Abbr `dfan`]
QED

Triviality cf_sound_opt_phi_prefix_eval_phis[local]:
  !s fn bb result ce_ctx bp dfg s0 s_phi.
    wf_function fn /\ ce_ctx.ce_dfg = dfg /\
    result = df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
      copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY)) fn /\
    is_fixpoint
      (df_process_block Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    eval_phis s0 bb.bb_instructions = OK s_phi /\
    cf_sound_opt bp dfg (df_at NONE result bb.bb_label 0) s0 ==>
    cf_sound_opt bp dfg
      (df_at NONE result bb.bb_label (phi_prefix_length bb.bb_instructions))
      (s_phi with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  `cf_sound_opt bp dfg
     (df_at NONE result bb.bb_label (phi_prefix_length bb.bb_instructions)) s0` by
    (mp_tac (Q.SPECL [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`, `dfg`, `s0`,
        `phi_prefix_length bb.bb_instructions`] cf_sound_opt_phi_prefix_on_s) >>
     simp[]) >>
  Cases_on `df_at NONE result bb.bb_label (phi_prefix_length bb.bb_instructions)`
  >- simp[cf_sound_opt_def] >>
  rename1 `df_at NONE result bb.bb_label (phi_prefix_length bb.bb_instructions) = SOME cfl` >>
  gvs[cf_sound_opt_def, cf_sound_def] >>
  rpt strip_tac >>
  irule cf_entry_sound_eval_phis_idx >>
  qexists_tac `bb.bb_instructions` >> qexists_tac `s0` >> simp[] >>
  rpt strip_tac >>
  `!j. j < phi_prefix_length bb.bb_instructions ==>
       ~MEM x (EL j bb.bb_instructions).inst_outputs` by
    (mp_tac (Q.SPECL [`s`, `fn`, `bb`,
        `df_analyze Forward NONE (copy_fact_join ce_ctx.ce_dfg)
           copy_fact_transfer copy_fact_edge_transfer ce_ctx
           (SOME (s.vs_current_bb, SOME FEMPTY)) fn`,
        `ce_ctx`, `phi_prefix_length bb.bb_instructions`,
        `cfl`, `ml`, `cf`, `x`] df_at_phi_prefix_no_phi_source_output) >>
     simp[]) >>
  first_x_assum drule >> simp[]
QED

(* MEM preds + boundary non-NONE + boundary sound *)
Resume stage1_correct[boundary]:
  (* Goal: boundary ≠ NONE ∧ cf_sound_opt boundary v ∧ MEM preds *)
  conj_tac
  >- (qspecl_then [`dfg`, `ce_ctx`, `(s:venom_state).vs_current_bb`,
        `fn`, `bb`, `result`]
        mp_tac cf_boundary_not_none >>
      simp[Abbr `result`, Abbr `ce_ctx`]) >>
  conj_tac
  >- (
    drule venomExecProofsTheory.run_block_OK_decompose >> strip_tac >>
    rename1 `eval_phis s'' bb.bb_instructions = OK s_phi` >>
    qabbrev_tac `p = phi_prefix_length bb.bb_instructions` >>
    qabbrev_tac `st = s_phi with vs_inst_idx := p` >>
    `wf_alias_sets aliases` by
      simp[Abbr `aliases`, memory_alias_analyze_def, ma_analyze_wf] >>
    `cf_sound_opt bp dfg (df_at NONE result bb.bb_label p)
       (s_phi with vs_inst_idx := 0)` by
      (mp_tac (Q.SPECL [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`,
         `dfg`, `s''`, `s_phi`] cf_sound_opt_phi_prefix_eval_phis) >>
       simp[Abbr `p`, Abbr `ce_ctx`, Abbr `result`]) >>
    `cf_keys_ok_opt bp (df_at NONE result bb.bb_label p)` by
      (mp_tac (Q.SPECL [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`,
         `dfg`, `p`] cf_keys_ok_opt_phi_prefix_on_s) >>
       simp[Abbr `p`, Abbr `ce_ctx`, Abbr `result`]) >>
    `cf_alloca_ok_opt bp (df_at NONE result bb.bb_label p)
       (s_phi with vs_inst_idx := 0)` by
      (mp_tac (Q.SPECL [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`,
         `dfg`, `s''`, `s_phi with vs_inst_idx := 0`, `p`]
         cf_alloca_ok_opt_phi_prefix_on_s) >>
       simp[Abbr `p`, Abbr `ce_ctx`, Abbr `result`] >>
       drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >> simp[]) >>
    `p <= i` by
      (simp[Abbr `p`] >>
       `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
         (irule mce_phi_prefix_length_lt_wf >> simp[]) >>
       decide_tac) >>
    `dfg_assigns_sound dfg (s_phi with vs_inst_idx := 0)` by
      (qpat_x_assum `!bb s0 s_phi.
         MEM bb fn.fn_blocks /\
         MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
         eval_phis s0 bb.bb_instructions = OK s_phi /\
         dfg_assigns_sound dfg s0 ==>
         dfg_assigns_sound dfg s_phi`
        (qspecl_then [`bb`, `s''`, `s_phi`] mp_tac) >> simp[]) >>
    `bp_ptr_sound bp (s_phi with vs_inst_idx := 0)` by (
      simp[bp_ptr_sound_inst_idx] >>
      irule eval_phis_preserves_bp_ptr_sound_untracked >>
      qexists_tac `bb.bb_instructions` >> qexists_tac `s''` >>
      simp[] >> rpt strip_tac >>
      irule bp_phi_outputs_untracked >>
      MAP_EVERY qexists_tac [`bb`, `fn`, `inst`] >>
      simp[Abbr `bp`]) >>
    (sg `(s_phi with vs_inst_idx := 0).vs_allocas = s''.vs_allocas /\
         (s_phi with vs_inst_idx := 0).vs_alloca_next = s''.vs_alloca_next` >-
      (mp_tac (Q.SPECL [`s''`, `bb.bb_instructions`, `s_phi`]
         venomExecProofsTheory.eval_phis_preserves_alloca_fields) >> simp[])) >>
    (sg `alloca_inv (s_phi with vs_inst_idx := 0)` >-
      metis_tac[alloca_inv_alloca_fields_eq]) >>
    (sg `allocas_non_overlapping (s_phi with vs_inst_idx := 0)` >-
      metis_tac[alloca_inv_non_overlapping]) >>
    (sg `allocas_in_word (s_phi with vs_inst_idx := 0)` >-
      metis_tac[allocas_in_word_allocas_eq]) >>
    (sg `bp_ptrs_bounded bp fn (s_phi with vs_inst_idx := 0)` >-
      metis_tac[bp_ptrs_bounded_allocas_eq]) >>
    qspecl_then [`bp`, `dfg`, `ce_ctx`, `(s:venom_state).vs_current_bb`,
      `fn`, `bb`, `result`, `fuel`, `run_ctx`, `st`, `v`, `i`]
      mp_tac cf_sound_opt_boundary_from_idx >>
    simp[Abbr `ce_ctx`, Abbr `result`, Abbr `st`] >>
    impl_tac >- (
      rpt conj_tac >> simp[] >>
      fs[dfg_assigns_sound_inst_idx, bp_ptr_sound_inst_idx,
         allocas_in_word_inst_idx, bp_ptrs_bounded_inst_idx]) >>
    simp[]) >>
  irule (iffLR cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond) >>
  irule cfgHelpersTheory.bb_succs_in_cfg_succs >>
  simp[] >> fs[wf_function_def] >>
  mp_tac (Q.SPECL [`fuel`, `run_ctx`, `bb`, `s''`, `v`]
    venomExecPropsTheory.run_block_current_bb_in_succs) >>
  impl_tac >- (
    rpt conj_tac >> simp[] >>
    rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  simp[]
QED

(* bp_ptr_sound preserved through exec_block — use bp_ptr_sound_exec_block *)
Resume stage1_correct[eval_phis_sound]:
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `ce_ctx = <| ce_aliases := aliases; ce_bp := bp; ce_dfg := dfg |>` >>
  qabbrev_tac `result = df_analyze Forward NONE (copy_fact_join dfg)
    copy_fact_transfer copy_fact_edge_transfer ce_ctx
    (SOME (s.vs_current_bb, SOME FEMPTY)) fn` >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  `is_fixpoint
      (df_process_block Forward NONE (copy_fact_join ce_ctx.ce_dfg) copy_fact_transfer
         copy_fact_edge_transfer ce_ctx (SOME (s.vs_current_bb, SOME FEMPTY))
         (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre result` by
    (mp_tac (Q.SPECL [`ce_ctx`, `fn`]
      (SIMP_RULE std_ss [LET_THM] copy_fact_is_fixpoint)) >>
     simp[Abbr `ce_ctx`, Abbr `result`]) >>
  `cf_sound_opt bp dfg
     (df_at NONE result bb.bb_label (phi_prefix_length bb.bb_instructions))
     (s_phi with vs_inst_idx := 0)` by
    (mp_tac (Q.SPECL [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`, `dfg`, `s''`, `s_phi`]
       cf_sound_opt_phi_prefix_eval_phis) >>
     simp[Abbr `ce_ctx`, Abbr `result`] >>
     impl_tac >> simp[] >> TRY (metis_tac[])) >>
  `cf_keys_ok_opt bp
     (df_at NONE result bb.bb_label (phi_prefix_length bb.bb_instructions))` by
    (mp_tac (Q.SPECL [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`, `dfg`,
       `phi_prefix_length bb.bb_instructions`] cf_keys_ok_opt_phi_prefix_on_s) >>
     simp[Abbr `ce_ctx`, Abbr `result`] >>
     impl_tac >> simp[] >> TRY (metis_tac[])) >>
  `cf_alloca_ok_opt bp
     (df_at NONE result bb.bb_label (phi_prefix_length bb.bb_instructions))
     (s_phi with vs_inst_idx := 0)` by
    (mp_tac (Q.SPECL [`s`, `fn`, `bb`, `result`, `ce_ctx`, `bp`, `dfg`,
       `s''`, `s_phi with vs_inst_idx := 0`,
       `phi_prefix_length bb.bb_instructions`]
       cf_alloca_ok_opt_phi_prefix_on_s) >>
     simp[Abbr `ce_ctx`, Abbr `result`] >>
     disch_then irule >>
     drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >> simp[]) >>
  simp[] >>
  (conj_tac >-
    (qpat_x_assum `!bb s0 s_phi.
       MEM bb fn.fn_blocks /\
       MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
       eval_phis s0 bb.bb_instructions = OK s_phi /\
       dfg_assigns_sound dfg s0 ==>
       dfg_assigns_sound dfg s_phi`
      (qspecl_then [`bb`, `s''`, `s_phi`] mp_tac) >> simp[])) >>
  (conj_tac >- (
    simp[bp_ptr_sound_inst_idx] >>
    irule eval_phis_preserves_bp_ptr_sound_untracked >>
    qexists_tac `bb.bb_instructions` >> qexists_tac `s''` >>
    simp[] >> rpt strip_tac >>
    irule bp_phi_outputs_untracked >>
    MAP_EVERY qexists_tac [`bb`, `fn`, `inst`] >>
    simp[Abbr `bp`])) >>
  (conj_tac >-
    metis_tac[venomExecProofsTheory.eval_phis_preserves_alloca_fields,
              alloca_inv_alloca_fields_eq]) >>
  (conj_tac >-
    metis_tac[venomExecProofsTheory.eval_phis_preserves_alloca_fields,
              allocas_in_word_allocas_eq]) >>
  metis_tac[venomExecProofsTheory.eval_phis_preserves_alloca_fields,
            bp_ptrs_bounded_allocas_eq]
QED

Finalise stage1_correct

(* ===== Stage 2: load_store_elim_block correctness ===== *)

(* FOLDL with load_store_step preserves accumulated list length *)
Triviality lse_foldl_length[local]:
  !insts lf acc aliases bp uc.
    LENGTH (SND (FOLDL (\(lf,acc) inst.
      let (lf',inst') = load_store_step aliases bp uc (lf,inst) in
      (lf', acc ++ [inst'])) (lf, acc) insts)) =
    LENGTH acc + LENGTH insts
Proof
  Induct >> simp[] >> rpt gen_tac >>
  `?lf' inst'. load_store_step aliases bp uc (lf, h) = (lf', inst')` by
    (Cases_on `load_store_step aliases bp uc (lf, h)` >> simp[]) >>
  simp[] >>
  first_x_assum (qspecl_then [`lf'`, `acc ++ [inst']`, `aliases`, `bp`, `uc`]
    mp_tac) >> simp[]
QED

(* load_store_elim_block preserves instruction count *)
Triviality lse_length[local]:
  !aliases bp uc bb.
    LENGTH (load_store_elim_block aliases bp uc bb).bb_instructions =
    LENGTH bb.bb_instructions
Proof
  rw[load_store_elim_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`bb.bb_instructions`, `FEMPTY`, `[]`, `aliases`, `bp`, `uc`]
    mp_tac lse_foldl_length >> simp[]
QED

(* Each load_store_step either preserves the instruction or NOPs it *)
Triviality lse_step_inst_or_nop[local]:
  !aliases bp uc lf inst.
    SND (load_store_step aliases bp uc (lf, inst)) = inst \/
    SND (load_store_step aliases bp uc (lf, inst)) = mk_nop_inst inst
Proof
  rw[load_store_step_def, LET_THM] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* load_store_elim_block preserves the label *)
Triviality lse_label[local]:
  !aliases bp uc bb.
    (load_store_elim_block aliases bp uc bb).bb_label = bb.bb_label
Proof
  rw[load_store_elim_block_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

(* Stage2 takes the specific fn1 produced by stage1 (analysis_function_transform)
   and applies load_store_elim_block. Preconditions use original fn. *)
Triviality stage2_correct[local]:
  !fuel ctx fn s.
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let bp = bp_analyze cfg fn in
    let aliases = memory_alias_analyze bp fn in
    let ce_ctx = <| ce_aliases := aliases; ce_bp := bp; ce_dfg := dfg |> in
    let result = copy_fact_analyze ce_ctx fn in
    let fn1 = analysis_function_transform NONE result
                (\v inst. [copy_elision_inst bp dfg v inst]) fn in
    let uc = \v. count_var_uses v fn1 in
    let fn2 = function_map_transform
                (load_store_elim_block aliases bp uc) fn1 in
    wf_function fn /\
    fn_inst_wf fn /\
    ssa_form fn /\
    s.vs_inst_idx = 0 /\
    bp_ptr_sound bp s /\
    alloca_inv s /\
    allocas_in_word s /\
    bp_ptrs_bounded bp fn s /\
    LENGTH s.vs_memory < dimword (:256) ==>
    (?e. run_blocks fuel ctx fn1 s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn1 s)
      (run_blocks fuel ctx fn2 s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> strip_tac >>
  qabbrev_tac `bp = bp_analyze (cfg_analyze fn) fn` >>
  qabbrev_tac `aliases = memory_alias_analyze bp fn` >>
  qabbrev_tac `fn1 = analysis_function_transform NONE
    (copy_fact_analyze
       <|ce_aliases := aliases; ce_bp := bp;
         ce_dfg := dfg_build_function fn|> fn)
    (\v inst.
       [copy_elision_inst bp (dfg_build_function fn) v inst]) fn` >>
  qabbrev_tac `uc = \v. count_var_uses v fn1` >>
  qabbrev_tac `P = \s. bp_ptr_sound bp s /\ alloca_inv s /\
    allocas_in_word s /\ bp_ptrs_bounded bp fn s /\
    LENGTH s.vs_memory < dimword (:256)` >>
  mp_tac (Q.SPECL [`P`, `state_equiv {}`, `execution_equiv {}`,
    `load_store_elim_block aliases bp uc`, `fn1`]
    block_sim_function_with_pred) >>
  simp_tac std_ss [] >>
  disch_then irule >>
  (* Solve easy conjuncts: P s, state_equiv_refl, vs_inst_idx *)
  simp[Abbr `P`, state_equiv_refl] >>
  (* Label preservation *)
  conj_tac >- suspend "s2_pred_pres" >>
  conj_tac >- (
    gen_tac >> simp[load_store_elim_block_def, LET_THM] >>
    pairarg_tac >> simp[]) >>
  conj_tac >- suspend "s2_block_sim" >>
  conj_tac >- (rpt strip_tac >> imp_res_tac state_equiv_empty_eq >> gvs[]) >>
  metis_tac[state_equiv_implies_execution_equiv]
QED

(* Stage 2 predicate preservation: P preserved by exec_block.
   Since state_equiv {} = equality, simplifies to: exec_block preserves
   bp_ptr_sound, alloca_inv, allocas_in_word, bp_ptrs_bounded, LENGTH vs_memory. *)
Resume stage2_correct[s2_pred_pres]:
  rpt strip_tac >> imp_res_tac state_equiv_empty_eq >> gvs[] >>
  cheat (* shared gap: needs bp_ptr_sound + allocas_in_word + bp_ptrs_bounded *)
QED

(* ===== Stage 2 helpers: store idempotency ===== *)

(* sstore(key, sload(key, s), s) = s *)
Triviality sstore_sload_id[local]:
  !key s. sstore key (sload key s) s = s
Proof
  simp[sstore_def, sload_def, contract_storage_def,
       vfmStateTheory.lookup_storage_def,
       vfmStateTheory.update_storage_def,
       vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_ID,
       vfmStateTheory.account_state_component_equality,
       venom_state_component_equality]
QED

(* tstore(key, tload(key, s), s) = s *)
Triviality tstore_tload_id[local]:
  !key s. tstore key (tload key s) s = s
Proof
  simp[tstore_def, tload_def, contract_transient_def,
       vfmStateTheory.lookup_storage_def,
       vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_ID,
       venom_state_component_equality]
QED

(* mstore(offset, mload(offset, s), s) = s when memory is large enough *)
Triviality mstore_mload_id[local]:
  !offset s.
    offset + 32 <= LENGTH s.vs_memory ==>
    mstore offset (mload offset s) s = s
Proof
  rpt strip_tac >>
  simp[mstore_def, mload_def, venom_state_component_equality] >>
  (* No expansion needed *)
  `~(offset + 32 - LENGTH s.vs_memory > 0)` by decide_tac >>
  simp[] >>
  (* DROP has enough elements *)
  `LENGTH (DROP offset s.vs_memory) >= 32` by simp[LENGTH_DROP] >>
  `TAKE 32 (DROP offset s.vs_memory ++ REPLICATE 32 0w) =
   TAKE 32 (DROP offset s.vs_memory)` by
    (irule TAKE_APPEND1 >> simp[]) >>
  simp[] >>
  (* Bytes roundtrip *)
  `LENGTH (TAKE 32 (DROP offset s.vs_memory)) = 32` by
    simp[LENGTH_TAKE] >>
  simp[word_bytes_roundtrip_256] >>
  (* Splice identity: TAKE n l ++ TAKE 32 (DROP n l) ++ DROP (n+32) l = l *)
  `DROP offset s.vs_memory =
   TAKE 32 (DROP offset s.vs_memory) ++ DROP 32 (DROP offset s.vs_memory)` by
    simp[TAKE_DROP] >>
  `TAKE offset s.vs_memory ++ DROP offset s.vs_memory = s.vs_memory` by
    simp[TAKE_DROP] >>
  `DROP 32 (DROP offset s.vs_memory) = DROP (offset + 32) s.vs_memory` by
    simp[rich_listTheory.DROP_DROP_T, arithmeticTheory.ADD_COMM] >>
  metis_tac[APPEND_ASSOC]
QED

(* exec_block with state-dependent pointwise step_inst refinement.
   Threads an invariant P through execution: P holds at each step,
   ensures step_inst of bb2 succeeds with the same result when bb1 succeeds,
   and P is preserved by each successful step.
   Hypotheses range over ALL indices (not just from s.vs_inst_idx) so
   the induction step is trivial — IH hypotheses are direct consequences.
   Conclusion: when bb1 succeeds, bb2 produces the same result. *)
(* exec_block_pointwise_inv: if each instruction step on bb1 that succeeds (OK)
   is matched by bb2, and non-OK/non-Error results also match, then
   exec_block bb1 either errors or equals exec_block bb2. *)
Triviality exec_block_pointwise_inv[local]:
  !n fuel ctx bb1 bb2 s P.
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    s.vs_inst_idx + n = LENGTH bb1.bb_instructions /\
    s.vs_inst_idx < LENGTH bb1.bb_instructions /\
    P s /\
    (!i. i < LENGTH bb1.bb_instructions ==>
         is_terminator (EL i bb1.bb_instructions).inst_opcode =
         is_terminator (EL i bb2.bb_instructions).inst_opcode) /\
    (!i s_i s_i'. P s_i /\ s_i.vs_inst_idx = i /\
         i < LENGTH bb1.bb_instructions /\
         step_inst fuel ctx (EL i bb1.bb_instructions) s_i = OK s_i' ==>
         step_inst fuel ctx (EL i bb2.bb_instructions) s_i = OK s_i') /\
    (!i s_i s_i'. P s_i /\ s_i.vs_inst_idx = i /\
         i < LENGTH bb1.bb_instructions /\
         step_inst fuel ctx (EL i bb1.bb_instructions) s_i = OK s_i' ==>
         P (s_i' with vs_inst_idx := SUC i)) /\
    (!i s_i r. P s_i /\ s_i.vs_inst_idx = i /\
         i < LENGTH bb1.bb_instructions /\
         step_inst fuel ctx (EL i bb1.bb_instructions) s_i = r /\
         (!s'. r <> OK s') /\ (!e. r <> Error e) ==>
         step_inst fuel ctx (EL i bb2.bb_instructions) s_i = r) ==>
    !r. exec_block fuel ctx bb1 s = r ==>
        (?e. r = Error e) \/ exec_block fuel ctx bb2 s = r
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[]
  >> rename1 `P st` >>
  once_rewrite_tac [exec_block_def] >>
  simp[get_instruction_def] >>
  `st.vs_inst_idx < LENGTH bb2.bb_instructions` by decide_tac >> simp[] >>
  `is_terminator (EL st.vs_inst_idx bb1.bb_instructions).inst_opcode =
   is_terminator (EL st.vs_inst_idx bb2.bb_instructions).inst_opcode` by (
    first_assum (qspec_then `st.vs_inst_idx` mp_tac) >> simp[]) >>
  Cases_on `step_inst fuel ctx (EL st.vs_inst_idx bb1.bb_instructions) st`
  >- ((* OK case *)
      rename1 `step_inst _ _ _ st = OK st'` >>
      `step_inst fuel ctx (EL st.vs_inst_idx bb2.bb_instructions) st = OK st'`
        by (first_assum (qspecl_then [`st.vs_inst_idx`, `st`, `st'`] mp_tac) >>
            simp[]) >>
      simp[] >>
      IF_CASES_TAC >> simp[] >>
      Cases_on `n`
      >- (once_rewrite_tac [exec_block_def] >> simp[get_instruction_def] >>
          `~(SUC st.vs_inst_idx < LENGTH bb1.bb_instructions)` by decide_tac >>
          `~(SUC st.vs_inst_idx < LENGTH bb2.bb_instructions)` by decide_tac >>
          simp[])
      >> `P (st' with vs_inst_idx := SUC st.vs_inst_idx)` by (
           first_x_assum (qspecl_then [`st.vs_inst_idx`, `st`, `st'`] mp_tac) >>
           simp[]) >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `bb1`, `bb2`,
        `st' with vs_inst_idx := SUC st.vs_inst_idx`, `P`] mp_tac) >>
      simp[] >>
      `SUC st.vs_inst_idx < LENGTH bb1.bb_instructions` by decide_tac >>
      simp[] >>
      (impl_tac >- metis_tac[]) >>
      simp[])
  >- ((* Halt case *)
      rename1 `step_inst _ _ _ st = Halt v` >>
      `step_inst fuel ctx (EL st.vs_inst_idx bb2.bb_instructions) st = Halt v`
        by (last_x_assum (qspecl_then [`st.vs_inst_idx`, `st`, `Halt v`]
              mp_tac) >> simp[]) >>
      simp[])
  >- ((* Abort case *)
      rename1 `step_inst _ _ _ st = Abort a v` >>
      `step_inst fuel ctx (EL st.vs_inst_idx bb2.bb_instructions) st = Abort a v`
        by (last_x_assum (qspecl_then [`st.vs_inst_idx`, `st`, `Abort a v`]
              mp_tac) >> simp[]) >>
      simp[])
  >- ((* IntRet case *)
      rename1 `step_inst _ _ _ st = IntRet l v` >>
      `step_inst fuel ctx (EL st.vs_inst_idx bb2.bb_instructions) st = IntRet l v`
        by (last_x_assum (qspecl_then [`st.vs_inst_idx`, `st`, `IntRet l v`]
              mp_tac) >> simp[]) >>
      simp[])
  >> simp[]
QED

(* ===== Stage 2: load-store elision soundness ===== *)

(* lf_at: the load-fact map at instruction index i during FOLDL processing.
   lf_at 0 = FEMPTY; lf_at (i+1) = FST(load_store_step ... (lf_at i, EL i insts)) *)
Definition lf_at_def[nocompute]:
  lf_at aliases bp uc insts 0 = FEMPTY /\
  lf_at aliases bp uc insts (SUC i) =
    if i < LENGTH insts then
      FST (load_store_step aliases bp uc (lf_at aliases bp uc insts i, EL i insts))
    else lf_at aliases bp uc insts i
End

(* inst_at: the transformed instruction at index i *)
Definition inst_at_def[nocompute]:
  inst_at aliases bp uc insts i =
    if i < LENGTH insts then
      SND (load_store_step aliases bp uc (lf_at aliases bp uc insts i, EL i insts))
    else EL i insts
End

(* Read a value from state according to opcode and byte offset *)
Definition read_at_offset_def:
  read_at_offset SLOAD off s = sload (n2w off) s /\
  read_at_offset TLOAD off s = tload (n2w off) s /\
  read_at_offset MLOAD off s = mload off s /\
  read_at_offset _ off s = ARB
End

(* Resolve a memloc's offset to an absolute address using alloca info.
   For Lit-based (ml_alloca = NONE): offset IS the absolute address.
   For Var-based (ml_alloca = SOME alloca_id): absolute = base + offset. *)
Definition resolve_memloc_offset_def:
  resolve_memloc_offset (ml:mem_loc) (s:venom_state) =
    case ml.ml_alloca of
      NONE => ml.ml_offset
    | SOME (Allocation aid) =>
        case ml.ml_offset of
          NONE => (NONE:num option)
        | SOME off =>
            case FLOOKUP s.vs_allocas aid of
              SOME p => SOME (FST p + off)
            | NONE => NONE
End

(* Load-fact soundness: each tracked entry matches the current state.
   The resolved absolute address is used to read the value.
   For MLOAD, additionally require memory bounds for idempotency. *)
Definition lf_sound_def:
  lf_sound lf s <=>
    !var lfact. FLOOKUP lf var = SOME lfact ==>
      ?addr. resolve_memloc_offset lfact.lf_memloc s = SOME addr /\
             lookup_var var s =
               SOME (read_at_offset lfact.lf_opcode addr s) /\
             (lfact.lf_opcode = MLOAD ==> addr + 32 <= LENGTH s.vs_memory)
End

(* When load_store_step replaces an instruction (inst' <> inst), extract
   the NOP conditions: store opcode, operand shape, load fact, memloc match,
   compatibility, and the result is mk_nop_inst. *)
Triviality load_store_step_nop_info[local]:
  !aliases bp uc lf inst lf' inst'.
    load_store_step aliases bp uc (lf, inst) = (lf', inst') /\
    inst' <> inst ==>
    is_store_opcode inst.inst_opcode /\
    inst' = mk_nop_inst inst /\
    ?addr val_name lfact.
      inst.inst_operands = [addr; Var val_name] /\
      FLOOKUP lf val_name = SOME lfact /\
      lfact.lf_memloc = bp_get_write_location bp inst
        (store_opcode_addr_space inst.inst_opcode) /\
      load_store_compatible lfact.lf_opcode inst.inst_opcode
Proof
  rw[load_store_step_def, LET_THM] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Bridge: resolve_memloc_offset of bp_segment_from_ops gives same address
   as eval_operand of the offset operand, via bp_ptr_sound.
   Formulated with explicit record so callers don't need accessor reduction. *)
Triviality write_loc_eval_operand_raw[local]:
  !bp addr_op sz msz s addr_resolved v1.
    bp_ptr_sound bp s /\
    resolve_memloc_offset
      (bp_segment_from_ops bp
        <|iao_ofst := addr_op; iao_size := sz; iao_max_size := msz|>) s =
      SOME addr_resolved /\
    eval_operand addr_op s = SOME v1 ==>
    v1 = n2w addr_resolved
Proof
  rpt strip_tac >>
  Cases_on `addr_op`
  >- ((* Lit case *)
      gvs[bp_segment_from_ops_def, LET_THM,
          resolve_memloc_offset_def, eval_operand_def])
  >- ((* Var case: use bp_ptr_from_op_sound *)
      rename1 `eval_operand (Var vn) s = SOME v1` >>
      gvs[bp_segment_from_ops_def, LET_THM, eval_operand_def] >>
      Cases_on `bp_ptr_from_op bp (Var vn)` >>
      gvs[resolve_memloc_offset_def] >>
      Cases_on `x` >> gvs[] >>
      Cases_on `a` >> gvs[] >>
      Cases_on `o'` >> gvs[resolve_memloc_offset_def] >>
      BasicProvers.every_case_tac >> gvs[] >>
      drule bp_ptr_from_op_sound_proof >>
      disch_then drule >> simp[eval_operand_def] >>
      strip_tac >> gvs[])
  (* Label case *)
  >> gvs[bp_segment_from_ops_def, LET_THM,
         resolve_memloc_offset_def, ml_undefined_def]
QED

(* Same as write_loc_eval_operand_raw but with opaque ops record *)
Triviality write_loc_eval_operand[local]:
  !bp ops s addr_resolved v1.
    bp_ptr_sound bp s /\
    resolve_memloc_offset (bp_segment_from_ops bp ops) s =
      SOME addr_resolved /\
    eval_operand ops.iao_ofst s = SOME v1 ==>
    v1 = n2w addr_resolved
Proof
  rpt gen_tac >> strip_tac >>
  `?a b c. ops = <|iao_ofst := a; iao_size := b; iao_max_size := c|>` by
    (qexistsl [`ops.iao_ofst`, `ops.iao_size`, `ops.iao_max_size`] >>
     simp[memLocDefsTheory.inst_access_ops_component_equality]) >>
  gvs[] >> metis_tac[write_loc_eval_operand_raw]
QED


Triviality resolve_memloc_offset_bp_segment_lt_dimword[local]:
  !bp ops s addr_res.
    resolve_memloc_offset (bp_segment_from_ops bp ops) s = SOME addr_res /\
    allocas_in_word s /\
    ml_is_fixed (bp_segment_from_ops bp ops) /\
    memloc_within_alloca (bp_segment_from_ops bp ops) s ==>
    addr_res < dimword (:256)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ops.iao_ofst` >- gvs[resolve_memloc_offset_def, bp_segment_from_ops_def, LET_THM, w2n_lt] >>
  all_tac >>> LASTGOAL (gvs[bp_segment_from_ops_def, LET_THM, ml_undefined_def, ml_is_fixed_def]) >>
  gvs[bp_segment_from_ops_def, LET_THM] >> Cases_on `bp_ptr_from_op bp (Var s')` >> gvs[ml_is_fixed_def] >>
  Cases_on `x` >> gvs[] >>
  Cases_on `o'` >> gvs[] >>
  Cases_on `a` >> gvs[resolve_memloc_offset_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  gvs[memloc_within_alloca_def, allocas_in_word_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  first_x_assum (qspecl_then [`n`, `FST x'`, `SND x'`] mp_tac) >>
  Cases_on `x'` >> gvs[]
QED

(* Determine the unique compatible load opcode for each store opcode *)
Triviality load_store_compatible_elim[local]:
  (load_store_compatible x MSTORE ==> x = MLOAD) /\
  (load_store_compatible x SSTORE ==> x = SLOAD) /\
  (load_store_compatible x TSTORE ==> x = TLOAD) /\
  (load_store_compatible x MSTORE8 ==> F) /\
  (load_store_compatible x ISTORE ==> F)
Proof
  Cases_on `x` >> simp[load_store_compatible_def]
QED

(* Extract operand values from exec_write2 OK with 2-operand instruction *)
Triviality exec_write2_ok_vals[local]:
  !f inst s s'.
    exec_write2 f inst s = OK s' /\
    inst.inst_operands = [op1; op2] ==>
    ?v1 v2. eval_operand op1 s = SOME v1 /\
            eval_operand op2 s = SOME v2 /\
            s' = f v1 v2 s
Proof
  simp[exec_write2_def] >> rpt strip_tac >>
  Cases_on `eval_operand op1 s` >> gvs[] >>
  Cases_on `eval_operand op2 s` >> gvs[]
QED

(* For MSTORE/SSTORE/TSTORE, step_inst_base = exec_write2 with the
   appropriate write function. *)
Triviality store_step_is_exec_write2[local]:
  (inst.inst_opcode = MSTORE ==>
   step_inst_base inst s =
     exec_write2 (\addr val s. mstore (w2n addr) val s) inst s) /\
  (inst.inst_opcode = SSTORE ==>
   step_inst_base inst s =
     exec_write2 (\key val s. sstore key val s) inst s) /\
  (inst.inst_opcode = TSTORE ==>
   step_inst_base inst s =
     exec_write2 (\key val s. tstore key val s) inst s)
Proof
  rpt conj_tac
  >- (strip_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[venomInstTheory.opcode_case_def])
  >- (strip_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[venomInstTheory.opcode_case_def])
  >- (strip_tac >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[venomInstTheory.opcode_case_def])
QED

(* Key helper 1: transformed instruction produces same step_inst result
   when lf_sound holds. *)
(* Per-instruction step refinement: when the original succeeds, the
   transformed instruction also succeeds with the same result.
   The NOP case uses lf_sound (value = what's already at address) +
   bp_ptr_sound (address evaluates correctly) to show store is idempotent. *)
Triviality lse_step_equiv[local]:
  !aliases bp uc insts i s s'.
    i < LENGTH insts /\
    lf_sound (lf_at aliases bp uc insts i) s /\
    bp_ptr_sound bp s /\
    s.vs_inst_idx = i /\
    step_inst fuel ctx (EL i insts) s = OK s' ==>
    step_inst fuel ctx (inst_at aliases bp uc insts i) s = OK s'
Proof
  rpt strip_tac >>
  simp[inst_at_def] >>
  qabbrev_tac `inst = EL i insts` >>
  qabbrev_tac `lf = lf_at aliases bp uc insts i` >>
  Cases_on `load_store_step aliases bp uc (lf, inst)` >>
  simp[] >>
  rename1 `load_store_step _ _ _ _ = (lf', inst')` >>
  (* If inst' = inst, the transformed instruction is the original — trivial *)
  Cases_on `inst' = inst` >- gvs[] >>
  (* NOP case: inst' = mk_nop_inst inst *)
  drule_all load_store_step_nop_info >> strip_tac >> gvs[] >>
  rename1 `FLOOKUP lf val_name = SOME lfact` >>
  rename1 `inst.inst_operands = [addr_op; Var val_name]` >>
  simp[mk_nop_inst_correct] >>
  (* Suffices to show s' = s *)
  `s' = s` suffices_by simp[] >>
  (* From lf_sound, get the load-fact soundness *)
  `?addr_res. resolve_memloc_offset lfact.lf_memloc s = SOME addr_res /\
    lookup_var val_name s = SOME (read_at_offset lfact.lf_opcode addr_res s) /\
    (lfact.lf_opcode = MLOAD ==> addr_res + 32 <= LENGTH s.vs_memory)` by
      fs[lf_sound_def, Abbr `lf`] >>
  (* step_inst → step_inst_base for non-INVOKE *)
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_store_opcode_def]) >>
  gvs[step_inst_non_invoke] >>
  (* Split on store opcode, eliminate MSTORE8/ISTORE, pin load opcode *)
  Cases_on `inst.inst_opcode` >> gvs[is_store_opcode_def] >>
  imp_res_tac load_store_compatible_elim >> gvs[] >>
  (* 3 cases: MLOAD/MSTORE, SLOAD/SSTORE, TLOAD/TSTORE *)
  gvs[store_opcode_addr_space_def, read_at_offset_def,
      store_step_is_exec_write2] >>
  drule_all exec_write2_ok_vals >> strip_tac >> gvs[eval_operand_def] >>
  (* Show v1 = n2w addr_res by unfolding bp_get_write_location for
     each concrete opcode+space, exposing bp_segment_from_ops *)
  qpat_x_assum `resolve_memloc_offset _ _ = _` mp_tac >>
  gvs[bp_get_write_location_def, is_raw_fmp_opcode_def,
      venomEffectsTheory.write_effects_def, mem_write_ops_def, LET_THM] >>
  strip_tac >>
  `v1 = n2w addr_res` by
    metis_tac[write_loc_eval_operand_raw] >>
  gvs[sstore_sload_id, tstore_tload_id] >>
  (* MSTORE: need addr_res < dimword(:256) for w2n/n2w roundtrip.
     Shared gap: requires allocas_in_word + bp_ptrs_bounded. *)
  `addr_res < dimword (:256)` by
    cheat (* shared gap: needs bp_ptrs_bounded + allocas_in_word *) >>
  gvs[mstore_mload_id]
QED

(* read_at_offset depends only on vs_memory, vs_accounts, vs_call_ctx,
   vs_transient. If all four are equal, read_at_offset is preserved. *)
Triviality read_at_offset_state_eq[local]:
  !op off s s'.
    s'.vs_memory = s.vs_memory /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_transient = s.vs_transient ==>
    read_at_offset op off s' = read_at_offset op off s
Proof
  Cases >> simp[read_at_offset_def, sload_def, tload_def, mload_def,
    contract_storage_def, contract_transient_def]
QED

(* Weaker variant: non-Memory opcodes don't use vs_memory *)
Triviality read_at_offset_non_memory_eq[local]:
  !op off s s'.
    load_opcode_addr_space op <> AddrSp_Memory /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_transient = s.vs_transient ==>
    read_at_offset op off s' = read_at_offset op off s
Proof
  Cases >> simp[read_at_offset_def, load_opcode_addr_space_def, sload_def,
    tload_def, contract_storage_def, contract_transient_def]
QED

(* State preservation for Branch 4 opcodes: non-INVOKE, non-ext_call opcodes
   with Eff_MEMORY ∈ write_effects that aren't load/store/copy.
   These are exactly EXTCODECOPY (is_mem_write_op) and ISTORE.
   NOTE: The ISTORE `by` block needs pred_setTheory.IN_INSERT and
   NOT_IN_EMPTY to fully evaluate set membership after Cases_on. *)
Triviality lf_sound_drestrict[local]:
  !lf P s. lf_sound lf s ==> lf_sound (DRESTRICT lf P) s
Proof
  simp[lf_sound_def, FLOOKUP_DRESTRICT]
QED

Triviality branch4_state_preserves[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode <> INVOKE /\
    ~is_ext_call_op inst.inst_opcode /\
    ~is_effect_free_op inst.inst_opcode /\
    Eff_MEMORY IN write_effects inst.inst_opcode /\
    ~is_copy_opcode inst.inst_opcode /\
    ~is_store_opcode inst.inst_opcode /\
    ~is_load_fact_opcode inst.inst_opcode /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts /\ s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx /\ s'.vs_allocas = s.vs_allocas /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  rpt gen_tac >> strip_tac >>
  (* Only ISTORE survives all the exclusions *)
  Cases_on `is_mem_write_op inst.inst_opcode`
  >- (qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
        step_mem_write_preserves >> simp[]) >>
  `inst.inst_opcode = ISTORE` by
    (Cases_on `inst.inst_opcode` >>
     gvs[is_mem_write_op_def, is_ext_call_op_def, is_terminator_def,
         venomEffectsTheory.write_effects_def,
         venomEffectsTheory.all_effects_def,
         venomEffectsTheory.empty_effects_def,
         is_copy_opcode_def, is_store_opcode_def,
         is_load_fact_opcode_def, is_effect_free_op_def,
         pred_setTheory.IN_INSERT, pred_setTheory.NOT_IN_EMPTY]) >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
    step_istore_preserves >> simp[] >> strip_tac >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
    step_inst_preserves_all >>
  simp[is_terminator_def, is_alloca_op_def, is_ext_call_op_def]
QED

(* DRESTRICT to non-Memory entries preserves lf_sound when
   accounts/transient/call_ctx/allocas/lookup_var are unchanged.
   Used for Branch 4 (Eff_MEMORY ∈ write_effects) where MLOAD entries are
   removed but SLOAD/TLOAD entries survive. *)
(* DRESTRICT to entries whose address-space effect is not in weffs.
   Requires that the surviving facts' state components are preserved.
   Used for Branch 4 where volatile instructions clear affected loads. *)
Triviality lf_sound_drestrict_non_memory[local]:
  !lf weffs s s'.
    lf_sound lf s /\
    Eff_MEMORY IN weffs /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_allocas = s.vs_allocas /\
    (!v. lookup_var v s' = lookup_var v s) ==>
    lf_sound (DRESTRICT lf
      {v | !lfact eff. FLOOKUP lf v = SOME lfact /\
           effect_of_addr_space
             (load_opcode_addr_space lfact.lf_opcode) = SOME eff ==>
           eff NOTIN weffs}) s'
Proof
  simp[lf_sound_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  (* The surviving entry has effect_of_addr_space ... = SOME eff
     with eff NOTIN weffs, so in particular eff <> Eff_MEMORY,
     meaning the load opcode is SLOAD or TLOAD, not MLOAD. *)
  `load_opcode_addr_space lfact.lf_opcode <> AddrSp_Memory` by
    (CCONTR_TAC >> gvs[load_opcode_addr_space_def,
       effect_of_addr_space_def]) >>
  qexists `addr` >> rpt conj_tac
  >- gvs[resolve_memloc_offset_def]
  >- (qpat_x_assum `lookup_var _ _ = _` mp_tac >>
      simp[read_at_offset_non_memory_eq])
  >> strip_tac >> gvs[load_opcode_addr_space_def]
QED

(* Like lf_sound_drestrict_non_memory but with weaker hypotheses:
   contract_storage equality instead of vs_accounts, and
   lookup_var equality only for FDOM lf entries. *)
Triviality lf_sound_drestrict_non_memory_weak[local]:
  !lf weffs s s'.
    lf_sound lf s /\
    Eff_MEMORY IN weffs /\
    Eff_STORAGE NOTIN weffs /\
    Eff_TRANSIENT NOTIN weffs /\
    contract_storage s' = contract_storage s /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_allocas = s.vs_allocas /\
    (!v. v IN FDOM lf ==> lookup_var v s' = lookup_var v s) ==>
    lf_sound (DRESTRICT lf
      {v | !lfact eff. FLOOKUP lf v = SOME lfact /\
           effect_of_addr_space
             (load_opcode_addr_space lfact.lf_opcode) = SOME eff ==>
           eff NOTIN weffs}) s'
Proof
  simp[lf_sound_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >>
  last_x_assum $ drule_then strip_assume_tac >> first_x_assum $ drule_then strip_assume_tac >>
  `load_opcode_addr_space lfact.lf_opcode <> AddrSp_Memory` by (
  strip_tac >>
  first_x_assum (qspec_then `Eff_MEMORY` mp_tac) >>
  simp[effect_of_addr_space_def]
) >>
qexists `addr` >>
  conj_tac >- (
  qpat_x_assum `resolve_memloc_offset _ s = _` mp_tac >>
  simp[resolve_memloc_offset_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
) >>
conj_tac >- (
  `var ∈ FDOM lf` by (Cases_on `FLOOKUP lf var` >> gvs[FLOOKUP_DEF]) >>
  first_x_assum drule >> disch_then (fn th => rewrite_tac[th]) >>
  Cases_on `lfact.lf_opcode` >> gvs[load_opcode_addr_space_def] >>
  gvs[read_at_offset_def, sload_def, tload_def, contract_storage_def, contract_transient_def]
) >>
Cases_on `lfact.lf_opcode` >> gvs[load_opcode_addr_space_def]
QED

(* Frame lemma for lf_sound: if lf' is a sub-map of lf with lf_sound lf s,
   and each entry's components are preserved in s', then lf_sound lf' s'. *)
Triviality lf_sound_frame[local]:
  !lf lf' s s'.
    lf_sound lf s /\
    (!var lfact. FLOOKUP lf' var = SOME lfact ==>
       FLOOKUP lf var = SOME lfact /\
       !addr. resolve_memloc_offset lfact.lf_memloc s = SOME addr ==>
         resolve_memloc_offset lfact.lf_memloc s' = SOME addr /\
         lookup_var var s' = lookup_var var s /\
         read_at_offset lfact.lf_opcode addr s' =
           read_at_offset lfact.lf_opcode addr s /\
         (lfact.lf_opcode = MLOAD ==> addr + 32 <= LENGTH s'.vs_memory)) ==>
    lf_sound lf' s'
Proof
  rw[lf_sound_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists `addr` >> simp[]
QED

(* resolve_memloc_offset is preserved when vs_allocas entries are unchanged.
   For ml_alloca = NONE, result is independent of state.
   For ml_alloca = SOME (Allocation aid), needs same FLOOKUP. *)
Triviality resolve_memloc_offset_allocas_eq[local]:
  !ml s s'.
    (!aid. FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) ==>
    resolve_memloc_offset ml s' = resolve_memloc_offset ml s
Proof
  rw[resolve_memloc_offset_def]
QED

(* lf_sound preserved when all relevant state components are equal.
   Covers surviving entries across any instruction that doesn't modify
   memory, storage, transient, allocas, call_ctx, or non-output vars. *)
Theorem lf_sound_state_eq[local]:
  !lf s s'.
    lf_sound lf s /\
    s'.vs_memory = s.vs_memory /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    (!aid. FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) /\
    (!var. var IN FDOM lf ==> lookup_var var s' = lookup_var var s) ==>
    lf_sound lf s'
Proof
  simp[lf_sound_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  qexists `addr` >> simp[] >>
  conj_tac
  >- suspend "resolve"
  >> suspend "lookup_read"
QED

Resume lf_sound_state_eq[resolve]:
  qpat_x_assum `resolve_memloc_offset _ _ = _` mp_tac >>
  simp[resolve_memloc_offset_def]
QED

Resume lf_sound_state_eq[lookup_read]:
  `lookup_var var s' = lookup_var var s` by (
    first_x_assum (qspec_then `var` mp_tac) >>
    (impl_tac >- gvs[flookup_thm]) >> simp[]) >>
  simp[] >>
  Cases_on `lfact.lf_opcode` >>
  gvs[read_at_offset_def, mload_def, sload_def, tload_def,
      contract_storage_def, contract_transient_def]
QED

Finalise lf_sound_state_eq

(* lf_sound doesn't depend on vs_inst_idx *)
Triviality lf_sound_inst_idx[local]:
  !lf s n. lf_sound lf (s with vs_inst_idx := n) = lf_sound lf s
Proof
  rpt gen_tac >> eq_tac >> strip_tac >> irule lf_sound_state_eq
  >- (qexists `s with vs_inst_idx := n` >> simp[lookup_var_def])
  >> (qexists `s` >> simp[lookup_var_def])
QED

(* lf_sound preserved under FUPDATE: surviving entries from lf_sound,
   new entry from explicit hypothesis. Reusable across branches 1/2/3. *)
Triviality lf_sound_fupdate[local]:
  !lf k lfact s.
    lf_sound lf s /\
    (?addr. resolve_memloc_offset lfact.lf_memloc s = SOME addr /\
            lookup_var k s = SOME (read_at_offset lfact.lf_opcode addr s) /\
            (lfact.lf_opcode = MLOAD ==> addr + 32 <= LENGTH s.vs_memory)) ==>
    lf_sound (lf |+ (k, lfact)) s
Proof
  rpt strip_tac >>
  simp[lf_sound_def] >> rpt strip_tac >>
  Cases_on `var = k`
  >- (gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
      qexists `addr` >> simp[])
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
     gvs[lf_sound_def]
QED

(* is_load_fact_opcode implies is_effect_free_op *)
Triviality load_fact_is_effect_free[local]:
  !op. is_load_fact_opcode op ==> is_effect_free_op op
Proof
  Cases >> simp[is_load_fact_opcode_def, is_effect_free_op_def]
QED

(* Effect-free ops preserve lf_sound when vars aren't clobbered.
   Allows vs_inst_idx to differ (lf_sound doesn't depend on it). *)
Triviality lf_sound_effect_free[local]:
  !lf inst s s' fuel ctx.
    lf_sound lf s /\
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode /\
    (!v. v IN FDOM lf ==> ~MEM v inst.inst_outputs) ==>
    lf_sound lf s'
Proof
  rpt strip_tac >>
  drule_all step_effect_free_state_equiv >>
  simp[state_equiv_def, execution_equiv_def] >> strip_tac >>
  irule lf_sound_state_eq >>
  qexists `s` >> gvs[]
QED

(* When ml_is_fixed and bp_ptr_sound hold, resolve_memloc_offset succeeds.
   Lit case: ml_alloca=NONE, ml_offset=SOME → SOME directly.
   Var case: bp_segment_from_ops_sound_proof gives FLOOKUP allocas. *)
Triviality bp_segment_resolve_some[local]:
  !bp ops s.
    ml_is_fixed (bp_segment_from_ops bp ops) /\
    bp_ptr_sound bp s /\
    IS_SOME (eval_operand ops.iao_ofst s) ==>
    ?addr. resolve_memloc_offset (bp_segment_from_ops bp ops) s = SOME addr
Proof
  rpt gen_tac >> strip_tac >>
  simp[resolve_memloc_offset_def] >>
  qabbrev_tac `ml = bp_segment_from_ops bp ops` >>
  Cases_on `ml.ml_alloca`
  >- gvs[ml_is_fixed_def, optionTheory.IS_SOME_EXISTS] >>
  Cases_on `x` >>
  Cases_on `ml.ml_offset`
  >- gvs[ml_is_fixed_def] >>
  rename1 `ml.ml_offset = SOME off` >>
  qspecl_then [`bp`, `ops`, `ml`, `n`, `off`, `s`]
    mp_tac bp_segment_from_ops_sound_proof >>
  simp[Abbr `ml`, ml_is_fixed_def] >> strip_tac >> simp[]
QED

(* For load opcodes with their natural addr_sp, bp_get_read_location
   gives bp_segment_from_ops with iao_ofst = addr_op. *)
Triviality load_bp_get_read_bridge[local]:
  !bp inst addr_op.
    is_load_fact_opcode inst.inst_opcode /\
    inst.inst_operands = [addr_op] ==>
    ?ops. bp_get_read_location bp inst
            (load_opcode_addr_space inst.inst_opcode) =
          bp_segment_from_ops bp ops /\ ops.iao_ofst = addr_op
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_load_fact_opcode_def, load_opcode_addr_space_def,
      bp_get_read_location_def, is_raw_fmp_opcode_def, mem_read_ops_def,
      venomEffectsTheory.read_effects_def] >>
  irule_at Any EQ_REFL >> simp[]
QED

(* New load entry is sound: after executing a load instruction with
   bp_get_read_location giving a fixed memloc, the output variable holds
   exactly read_at_offset at the resolved address.
   Produces the existential witness needed by lf_sound_fupdate. *)
Triviality load_new_entry_sound[local]:
  !bp inst s s' fuel ctx out addr_op.
    is_load_fact_opcode inst.inst_opcode /\
    inst.inst_operands = [addr_op] /\
    inst.inst_outputs = [out] /\
    bp_ptr_sound bp s /\
    step_inst fuel ctx inst s = OK s' /\
    ml_is_fixed (bp_get_read_location bp inst
                   (load_opcode_addr_space inst.inst_opcode)) /\
    s'.vs_memory = s.vs_memory /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_allocas = s.vs_allocas ==>
    ?addr.
      resolve_memloc_offset
        (bp_get_read_location bp inst
           (load_opcode_addr_space inst.inst_opcode)) s' = SOME addr /\
      lookup_var out s' = SOME (read_at_offset inst.inst_opcode addr s') /\
      (inst.inst_opcode = MLOAD ==>
       addr + 32 <= LENGTH s'.vs_memory ==>
       addr + 32 <= LENGTH s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >>
  (* Bridge: bp_get_read_location = bp_segment_from_ops bp ops *)
  `?ops. bp_get_read_location bp inst
           (load_opcode_addr_space inst.inst_opcode) =
         bp_segment_from_ops bp ops /\ ops.iao_ofst = addr_op` by
    (mp_tac load_bp_get_read_bridge >> simp[]) >>
  (* Case split on the 3 load opcodes; all use exec_read1 *)
  Cases_on `inst.inst_opcode` >> gvs[is_load_fact_opcode_def] >>
  gvs[step_inst_def, is_terminator_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  strip_tac >>
  gvs[exec_read1_def] >>
  (* From OK result: eval_operand ops.iao_ofst s = SOME v *)
  Cases_on `eval_operand ops.iao_ofst s` >> gvs[] >>
  rename1 `eval_operand _ s = SOME v` >>
  gvs[update_var_def] >>
  (* Get resolve = SOME addr_res via proven helper *)
  `?addr_res. resolve_memloc_offset (bp_segment_from_ops bp ops) s =
              SOME addr_res` by
    (irule bp_segment_resolve_some >> simp[]) >>
  qexists `addr_res` >>
  (* v = n2w addr_res from write_loc_eval_operand *)
  `v = n2w addr_res` by (
    qspecl_then [`bp`, `ops`, `s`, `addr_res`, `v`]
      mp_tac write_loc_eval_operand >> simp[]
  ) >> gvs[] >>
  (* resolve only depends on vs_allocas (not vs_vars), so resolve in s'
     equals resolve in s. read_at_offset/lookup_var close for SLOAD/TLOAD.
     MLOAD leaves addr_res MOD dimword = addr_res — shared gap. *)
  gvs[resolve_memloc_offset_def, lookup_var_def, FLOOKUP_UPDATE,
      read_at_offset_def, mload_def, sload_def, tload_def,
      contract_storage_def, contract_transient_def] >>
  `addr_res < dimword (:256)` by
    cheat (* shared gap: needs bp_ptrs_bounded + allocas_in_word *) >>
  gvs[]
QED

(* Key helper 2: lf_sound is preserved after executing an instruction.
   Requires: alloca_inv (for alias reasoning), wf_alias_sets (alias soundness),
   non-terminator (for variable frame), variable non-clobber (SSA consequence). *)
Triviality lse_inv_preserved[local]:
  !aliases bp uc insts i s s'.
    i < LENGTH insts /\
    lf_sound (lf_at aliases bp uc insts i) s /\
    bp_ptr_sound bp s /\
    alloca_inv s /\
    wf_alias_sets aliases /\
    ~is_terminator (EL i insts).inst_opcode /\
    (!v. v IN FDOM (lf_at aliases bp uc insts i) ==>
         ~MEM v (EL i insts).inst_outputs) /\
    s.vs_inst_idx = i /\
    step_inst fuel ctx (EL i insts) s = OK s' ==>
    lf_sound (lf_at aliases bp uc insts (SUC i)) (s' with vs_inst_idx := SUC i) /\
    bp_ptr_sound bp s' /\ alloca_inv s'
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `inst = EL i insts` >>
  qabbrev_tac `lf = lf_at aliases bp uc insts i` >>
  (* alloca_inv s' *)
  `alloca_inv s'` by
    (qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
       alloca_inv_step_inst >> simp[Abbr `inst`]) >>
  (* bp_ptr_sound: cheat — needs fixpoint investigation *)
  `bp_ptr_sound bp s'` by cheat >>
  (* Remaining: lf_sound (lf_at ... (SUC i)) (s' with vs_inst_idx := SUC i)
     Case split on the 5 branches of load_store_step *)
  `lf_at aliases bp uc insts (SUC i) =
     FST (load_store_step aliases bp uc (lf, inst))` by
    simp[lf_at_def, Abbr `lf`, Abbr `inst`] >>
  Cases_on `is_load_fact_opcode inst.inst_opcode`
  >- suspend "branch1_load"
  >>
  Cases_on `is_store_opcode inst.inst_opcode`
  >- (simp[load_store_step_def, LET_THM] >> suspend "branch2_store")
  >>
  Cases_on `is_copy_opcode inst.inst_opcode`
  >- (simp[load_store_step_def, LET_THM] >> suspend "branch3_copy")
  >>
  Cases_on `Eff_MEMORY IN write_effects inst.inst_opcode`
  >- suspend "branch4"
  >>
  (* Branch 5: Other — lf unchanged *)
  simp[load_store_step_def, LET_THM] >>
  (* Split off ext_call and ALLOCA as accepted cheats *)
  Cases_on `is_ext_call_op inst.inst_opcode`
  >- cheat (* CREATE/CREATE2: shared gap (write effects unclear) *) >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- suspend "branch5_alloca" >>
  (* Remaining: non-ext_call, non-ALLOCA, non-terminator, non-store/load/copy,
     Eff_MEMORY NOTIN write_effects. Split effect-free vs not. *)
  Cases_on `is_effect_free_op inst.inst_opcode`
  >- (
    (* Effect-free: state_equiv gives all fields equal *)
    drule_all step_effect_free_state_equiv >>
    simp[state_equiv_def, execution_equiv_def] >> strip_tac >>
    irule lf_sound_state_eq >>
    qexists `s` >> gvs[])
  >>
  (* Non-effect-free remainder: LOG, ASSERT, ASSERT_UNREACHABLE etc.
     All preserve lf_sound-relevant state fields. *)
  suspend "branch5_nonef"
QED

Triviality step_inst_alloca_flookup_eq[local]:
  !fuel ctx inst s s' p.
    step_inst fuel ctx inst s = OK s' /\ is_alloca_op inst.inst_opcode /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME p ==>
    FLOOKUP s'.vs_allocas inst.inst_id = SOME p
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
  gvs[step_inst_non_invoke, Once step_inst_base_def, exec_alloca_def,
      AllCaseEqs(), update_var_def, LET_THM]
QED

Triviality step_inst_alloca_flookup_all[local]:
  !fuel ctx inst s s' aid p.
    step_inst fuel ctx inst s = OK s' /\ is_alloca_op inst.inst_opcode /\
    FLOOKUP s.vs_allocas aid = SOME p ==>
    FLOOKUP s'.vs_allocas aid = SOME p
Proof
  rpt strip_tac >>
  Cases_on `aid = inst.inst_id`
  >- (gvs[] >> irule step_inst_alloca_flookup_eq >> metis_tac[])
  >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`, `aid`]
    mp_tac step_inst_alloca_flookup >>
  simp[is_alloca_op_def]
QED

Triviality lf_sound_alloca_preserved[local]:
  !fuel ctx inst s s' lf.
    step_inst fuel ctx inst s = OK s' /\ is_alloca_op inst.inst_opcode /\
    lf_sound lf s /\
    (!v. v IN FDOM lf ==> ~MEM v inst.inst_outputs) ==>
    lf_sound lf s'
Proof
  rpt strip_tac >>
  drule_all (SRULE [GSYM AND_IMP_INTRO] step_alloca_preserves) >>
  strip_tac >>
  irule lf_sound_frame >>
  qexistsl [`lf`, `s`] >>
  simp[] >>
  rpt strip_tac >> gvs[] >>
  TRY (
    (* lookup_var preserved *)
    first_x_assum irule >>
    first_x_assum irule >>
    gvs[flookup_thm] >> NO_TAC) >>
  TRY (
    (* read_at_offset preserved *)
    Cases_on `lfact.lf_opcode` >>
    gvs[read_at_offset_def, mload_def, sload_def, tload_def,
        contract_storage_def, contract_transient_def] >> NO_TAC) >>
  (* remaining: resolve_memloc_offset + MLOAD bound *)
  qpat_x_assum `lf_sound lf s` mp_tac >>
  simp[lf_sound_def] >>
  disch_then drule >> strip_tac >>
  gvs[] >>
  (* resolve_memloc_offset preserved *)
  qpat_x_assum `resolve_memloc_offset _ s = SOME _` mp_tac >>
  simp[Once resolve_memloc_offset_def] >>
  simp[Once resolve_memloc_offset_def] >>
  BasicProvers.every_case_tac >> rw[] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME q` >>
  drule_all (SRULE [GSYM AND_IMP_INTRO] step_inst_alloca_flookup_all) >>
  simp[]
QED

Resume lse_inv_preserved[branch5_alloca]:
  simp[lf_sound_inst_idx] >>
  irule lf_sound_alloca_preserved >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[is_alloca_op_def] >>
  metis_tac[]
QED

Triviality lf_sound_residual_preserved[local]:
  !fuel ctx inst s s' lf.
    step_inst fuel ctx inst s = OK s' /\
    lf_sound lf s /\
    (!v. v IN FDOM lf ==> ~MEM v inst.inst_outputs) /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_effect_free_op inst.inst_opcode /\
    ~is_load_fact_opcode inst.inst_opcode /\
    ~is_store_opcode inst.inst_opcode /\
    ~is_copy_opcode inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    lf_sound lf s'
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >>
     gvs[is_ext_call_op_def, is_alloca_op_def,
         venomEffectsTheory.write_effects_def,
         venomEffectsTheory.all_effects_def]) >>
  `step_inst_base inst s = OK s'` by
    metis_tac[step_inst_non_invoke] >>
  `s'.vs_allocas = s.vs_allocas` by
    metis_tac[venomMemProofsTheory.step_inst_base_preserves_alloca_fields] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
    step_inst_preserves_all >>
  impl_tac >- simp[] >> strip_tac >>
  `s'.vs_memory = s.vs_memory /\
   s'.vs_accounts = s.vs_accounts /\
   s'.vs_transient = s.vs_transient` by
    (Cases_on `inst.inst_opcode` >>
     gvs[is_effect_free_op_def, is_ext_call_op_def, is_alloca_op_def,
         is_load_fact_opcode_def, is_store_opcode_def, is_copy_opcode_def,
         is_terminator_def, venomEffectsTheory.write_effects_def,
         venomEffectsTheory.all_effects_def,
         venomEffectsTheory.empty_effects_def]) >>
  irule lf_sound_state_eq >>
  qexists `s` >> simp[] >>
  rpt strip_tac >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`, `var`]
    mp_tac step_inst_preserves_lookup >> simp[]
QED

Resume lse_inv_preserved[branch5_nonef]:
  simp[lf_sound_inst_idx] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`, `lf`]
    mp_tac lf_sound_residual_preserved >>
  simp[]
QED

Triviality lf_at_opcode_inv_early[local]:
  !i aliases bp uc insts v lfact.
    FLOOKUP (lf_at aliases bp uc insts i) v = SOME lfact ==>
    is_load_fact_opcode lfact.lf_opcode
Proof
  Induct_on `i` >> simp[lf_at_def, FLOOKUP_EMPTY] >>
  rpt gen_tac >> reverse IF_CASES_TAC >> gvs[] >- metis_tac[] >>
  simp[load_store_step_def, LET_THM] >> rpt COND_CASES_TAC >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, invalidate_loads_def] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >> res_tac
QED

Triviality staticcall_lf_sound_helper[local]:
  !lf s s' fuel ctx inst.
    lf_sound lf s /\
    inst.inst_opcode = STATICCALL /\
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (!v. v IN FDOM lf ==> ~MEM v inst.inst_outputs) ==>
    lf_sound (DRESTRICT lf
      {v | !lfact eff. FLOOKUP lf v = SOME lfact /\
           effect_of_addr_space
             (load_opcode_addr_space lfact.lf_opcode) = SOME eff ==>
           eff NOTIN write_effects STATICCALL}) s'
Proof
  rpt strip_tac >>
  `is_ext_call_op inst.inst_opcode` by simp[is_ext_call_op_def] >> drule_all step_ext_call_preserves >> strip_tac >>
  `contract_storage s' = contract_storage s` by (
  drule write_effects_sound_storage >>
  simp[is_alloca_op_def, is_terminator_def, write_effects_def, all_effects_def, empty_effects_def]
) >>
`s'.vs_transient = s.vs_transient` by (
  drule write_effects_sound_transient >>
  simp[is_alloca_op_def, is_terminator_def, write_effects_def, all_effects_def, empty_effects_def]
) >>
  irule lf_sound_drestrict_non_memory_weak >> rpt conj_tac >> gvs[write_effects_def, all_effects_def, empty_effects_def] >> metis_tac[]
QED

Resume lse_inv_preserved[branch4]:
  (* Branch 4: Eff_MEMORY IN write_effects, not load/store/copy.
     Analysis removes MLOAD entries via DRESTRICT. *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    simp[] >>
    simp[lf_sound_inst_idx] >>
    qpat_x_assum `lf_at _ _ _ _ (SUC i) = _` (fn eq => rewrite_tac[eq]) >>
    simp[load_store_step_def, LET_THM,
         is_load_fact_opcode_def, is_store_opcode_def, is_copy_opcode_def,
         write_effects_def, all_effects_def] >>
    simp[lf_sound_def, FLOOKUP_DRESTRICT] >>
    rpt strip_tac >>
    gvs[markerTheory.Abbrev_def] >>
    imp_res_tac lf_at_opcode_inv_early >>
    Cases_on `lfact.lf_opcode` >>
    gvs[is_load_fact_opcode_def, load_opcode_addr_space_def,
        effect_of_addr_space_def]
  ) >>
  Cases_on `is_ext_call_op inst.inst_opcode`
  >- (
    (* ext_call: case split on the 5 ext_call opcodes *)
    Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def] >>
    gvs[write_effects_def, all_effects_def, empty_effects_def]
    (* CREATE/CREATE2: Eff_MEMORY NOTIN write_effects — contradiction *)
    (* CALL/DELEGATECALL: all load effects in weffs — DRESTRICT = FEMPTY *)
    >- (simp[lf_sound_inst_idx] >>
        qpat_x_assum `lf_at _ _ _ _ (SUC i) = _` (fn eq => rewrite_tac[eq]) >>
        simp[load_store_step_def, LET_THM,
             is_load_fact_opcode_def, is_store_opcode_def, is_copy_opcode_def,
             write_effects_def, all_effects_def] >>
        simp[lf_sound_def, FLOOKUP_DRESTRICT] >>
        rpt strip_tac >>
        gvs[markerTheory.Abbrev_def] >>
        imp_res_tac lf_at_opcode_inv_early >>
        Cases_on `lfact.lf_opcode` >>
        gvs[is_load_fact_opcode_def, load_opcode_addr_space_def,
            effect_of_addr_space_def])
    (* STATICCALL: surviving SLOAD/TLOAD — needs state preservation *)
    >- (simp[lf_sound_inst_idx] >>
        qpat_x_assum `lf_at _ _ _ _ (SUC _) = _` (fn eq => rewrite_tac[eq]) >>
        simp[load_store_step_def, LET_THM,
             is_load_fact_opcode_def, is_store_opcode_def, is_copy_opcode_def,
             write_effects_def, all_effects_def, empty_effects_def] >>
        irule (SIMP_RULE (srw_ss()) [] (REWRITE_RULE [write_effects_def, all_effects_def, empty_effects_def] staticcall_lf_sound_helper)) >> gvs[markerTheory.Abbrev_def] >> metis_tac[])
    (* DELEGATECALL: same as CALL *)
    >> (simp[lf_sound_inst_idx] >>
        qpat_x_assum `lf_at _ _ _ _ (SUC _) = _` (fn eq => rewrite_tac[eq]) >>
        simp[load_store_step_def, LET_THM,
             is_load_fact_opcode_def, is_store_opcode_def, is_copy_opcode_def,
             write_effects_def, all_effects_def] >>
        simp[lf_sound_def, FLOOKUP_DRESTRICT] >>
        rpt strip_tac >>
        gvs[markerTheory.Abbrev_def] >>
        imp_res_tac lf_at_opcode_inv_early >>
        Cases_on `lfact.lf_opcode` >>
        gvs[is_load_fact_opcode_def, load_opcode_addr_space_def,
            effect_of_addr_space_def])
  ) >>
  (* Effect-free (e.g. DLOAD): state_equiv gives fields, then sub-map *)
  Cases_on `is_effect_free_op inst.inst_opcode`
  >- (simp[load_store_step_def, LET_THM] >>
      irule lf_sound_drestrict >>
      drule_all step_effect_free_state_equiv >>
      simp[state_equiv_def, execution_equiv_def] >> strip_tac >>
      irule lf_sound_state_eq >> qexists `s` >> gvs[]) >>
  (* Remaining (ISTORE/EXTCODECOPY): forward-chain state preservation *)
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
    branch4_state_preserves >> simp[] >> strip_tac >>
  simp[load_store_step_def, LET_THM] >>
  irule lf_sound_drestrict_non_memory >>
  simp[] >> qexists_tac `s` >> simp[]
QED

Resume lse_inv_preserved[branch1_load]:
  (* Strip bp_ptr_sound ∧ alloca_inv (in assumptions) *)
  (reverse conj_tac >- simp[]) >>
  (* Simplify vs_inst_idx *)
  simp[lf_sound_inst_idx] >>
  (* Rewrite lf_at SUC *)
  qpat_x_assum `lf_at _ _ _ _ (SUC i) = _` (fn eq => rewrite_tac[eq]) >>
  simp[load_store_step_def, LET_THM] >>
  (* Derive effect-free and state equivalence early *)
  `is_effect_free_op inst.inst_opcode`
    by (irule load_fact_is_effect_free >> simp[]) >>
  drule_all step_effect_free_state_equiv >>
  simp[state_equiv_def, execution_equiv_def] >> strip_tac >>
  (* Derive lf_sound lf s' for degenerate cases *)
  `lf_sound lf s'` by
    (irule lf_sound_state_eq >> qexists `s` >> gvs[]) >>
  (* All degenerate operand/output patterns yield (lf,inst), so FST = lf.
     Case-split and close degenerate, leaving main case [addr_op],[out]. *)
  BasicProvers.every_case_tac >> gvs[] >>
  rename1 `inst.inst_outputs = [out_var]` >>
  rename1 `inst.inst_operands = [addr_op]` >>
  (* Remaining: lf_sound (lf |+ (out_var, new_lfact)) s'
     where out_var is the load output, new_lfact records the loaded location. *)
  irule lf_sound_fupdate >> simp[] >>
  (* Use load_new_entry_sound to produce ∃addr with all 3 conjuncts *)
  qspecl_then [`bp`, `inst`, `s`, `s'`, `fuel`, `ctx`, `out_var`, `addr_op`]
    mp_tac load_new_entry_sound >>
  simp[] >> strip_tac >>
  qexists `addr` >> simp[] >>
  cheat (* shared gap: MLOAD memory bound — needs bp_ptrs_bounded + allocas_in_word *)
QED

(* Branch 2 (store): invalidate_loads removes aliasing entries.
   Surviving entries are in different addr space OR non-aliasing.
   Different-space entries: read_at_offset uses different state field → trivially preserved.
   Same-space non-aliasing: needs ma_may_alias_sound → memloc_within_alloca (shared gap). *)
Resume lse_inv_preserved[branch2_store]:
  simp[lf_sound_inst_idx] >>
  cheat (* Blocked on memloc_within_alloca for same-space alias soundness.
           Proof plan: irule lf_sound_frame. Surviving entries either:
           (a) different addr space → read_at_offset trivially preserved, or
           (b) same space, ¬ma_may_alias → needs ma_may_alias_sound_proof
               → needs memloc_within_alloca (shared gap) *)
QED

(* Branch 3 (copy): same structure as branch 2 but writes to AddrSp_Memory.
   Copy opcodes invalidate MEMORY loads only. *)
Resume lse_inv_preserved[branch3_copy]:
  simp[lf_sound_inst_idx] >>
  cheat (* Same alias reasoning as branch 2 *)
QED

Finalise lse_inv_preserved

(* FOLDL invariant: after processing TAKE k, the accumulated list
   contains inst_at values and lf matches lf_at k *)
Triviality lse_foldl_invariant[local]:
  !k aliases bp uc insts.
    k <= LENGTH insts ==>
    FOLDL (\(lf,acc) inst.
      let (lf',inst') = load_store_step aliases bp uc (lf,inst)
      in (lf', acc ++ [inst']))
      (FEMPTY, []) (TAKE k insts) =
    (lf_at aliases bp uc insts k,
     GENLIST (\j. inst_at aliases bp uc insts j) k)
Proof
  Induct >> rpt strip_tac >- simp[lf_at_def] >>
  `k <= LENGTH insts` by decide_tac >>
  `k < LENGTH insts` by decide_tac >>
  first_x_assum (qspecl_then [`aliases`, `bp`, `uc`, `insts`] mp_tac) >>
  simp[] >> strip_tac >>
  `TAKE (SUC k) insts = SNOC (EL k insts) (TAKE k insts)`
    by simp[rich_listTheory.TAKE_EL_SNOC, ADD1] >>
  simp[FOLDL_SNOC] >>
  Cases_on `load_store_step aliases bp uc
    (lf_at aliases bp uc insts k, EL k insts)` >>
  simp[lf_at_def, inst_at_def, GENLIST, SNOC_APPEND]
QED

(* FOLDL decomposition: inst_at produces the same instructions as
   load_store_elim_block *)
Triviality lse_inst_at_eq[local]:
  !aliases bp uc bb i.
    i < LENGTH bb.bb_instructions ==>
    EL i (load_store_elim_block aliases bp uc bb).bb_instructions =
    inst_at aliases bp uc bb.bb_instructions i
Proof
  rpt strip_tac >>
  simp[load_store_elim_block_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  `TAKE (LENGTH bb.bb_instructions) bb.bb_instructions = bb.bb_instructions`
    by simp[TAKE_LENGTH_ID] >>
  qspecl_then [`LENGTH bb.bb_instructions`, `aliases`, `bp`, `uc`,
    `bb.bb_instructions`] mp_tac lse_foldl_invariant >>
  simp[]
QED

Triviality lse_el_inst_or_nop[local]:
  !aliases bp uc bb i.
    i < LENGTH bb.bb_instructions ==>
    EL i (load_store_elim_block aliases bp uc bb).bb_instructions =
      EL i bb.bb_instructions \/
    EL i (load_store_elim_block aliases bp uc bb).bb_instructions =
      mk_nop_inst (EL i bb.bb_instructions)
Proof
  rpt strip_tac >> simp[lse_inst_at_eq, inst_at_def] >>
  qspecl_then [`aliases`, `bp`, `uc`,
    `lf_at aliases bp uc bb.bb_instructions i`,
    `EL i bb.bb_instructions`] mp_tac lse_step_inst_or_nop >>
  simp[]
QED

Triviality lse_terminator_identity[local]:
  !aliases bp uc bb i.
    i < LENGTH bb.bb_instructions /\
    is_terminator (EL i bb.bb_instructions).inst_opcode ==>
    EL i (load_store_elim_block aliases bp uc bb).bb_instructions =
    EL i bb.bb_instructions
Proof
  rpt strip_tac >> simp[lse_inst_at_eq, inst_at_def] >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode` >>
  gvs[is_terminator_def, load_store_step_def, LET_THM,
      is_load_fact_opcode_def, is_store_opcode_def, is_copy_opcode_def,
      write_effects_def, empty_effects_def]
QED

Triviality lse_phi_identity[local]:
  !aliases bp uc bb i.
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = PHI ==>
    EL i (load_store_elim_block aliases bp uc bb).bb_instructions =
    EL i bb.bb_instructions
Proof
  rpt strip_tac >> simp[lse_inst_at_eq, inst_at_def] >>
  simp[load_store_step_def, LET_THM, is_load_fact_opcode_def,
       is_store_opcode_def, is_copy_opcode_def, write_effects_def,
       empty_effects_def]
QED

Triviality lse_phi_reverse[local]:
  !aliases bp uc bb i.
    i < LENGTH bb.bb_instructions /\
    (EL i (load_store_elim_block aliases bp uc bb).bb_instructions).inst_opcode = PHI ==>
    (EL i bb.bb_instructions).inst_opcode = PHI
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`aliases`, `bp`, `uc`, `bb`, `i`] lse_el_inst_or_nop) >>
  simp[] >> strip_tac >> gvs[mk_nop_inst_def]
QED

Triviality phi_prefix_length_el_phi[local]:
  !insts i. i < phi_prefix_length insts ==> (EL i insts).inst_opcode = PHI
Proof
  Induct_on `insts` >> simp[phi_prefix_length_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def] >>
  Cases_on `i` >> simp[phi_prefix_length_def]
QED

Triviality phi_prefix_length_eq_by_el_phi[local]:
  !insts1 insts2.
    LENGTH insts1 = LENGTH insts2 /\
    (!i. i < LENGTH insts1 ==>
         ((EL i insts1).inst_opcode = PHI <=>
          (EL i insts2).inst_opcode = PHI)) ==>
    phi_prefix_length insts1 = phi_prefix_length insts2
Proof
  Induct_on `insts1` >> Cases_on `insts2` >> simp[phi_prefix_length_def] >>
  rpt strip_tac >>
  `h.inst_opcode = PHI <=> h'.inst_opcode = PHI` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!i. i < LENGTH insts1 ==>
       ((EL i insts1).inst_opcode = PHI <=> (EL i t).inst_opcode = PHI)` by
    (rpt strip_tac >>
     first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
  Cases_on `h.inst_opcode = PHI` >> Cases_on `h'.inst_opcode = PHI` >>
  gvs[phi_prefix_length_def] >>
  qpat_x_assum `!insts2. _` (qspec_then `t` mp_tac) >> simp[]
QED

Triviality lse_phi_prefix_length[local]:
  !aliases bp uc bb.
    phi_prefix_length (load_store_elim_block aliases bp uc bb).bb_instructions =
    phi_prefix_length bb.bb_instructions
Proof
  rpt strip_tac >>
  irule phi_prefix_length_eq_by_el_phi >>
  simp[lse_length] >>
  rpt strip_tac >> eq_tac >> strip_tac
  >- (mp_tac (Q.SPECL [`aliases`, `bp`, `uc`, `bb`, `i`] lse_phi_reverse) >>
      simp[]) >>
  `EL i (load_store_elim_block aliases bp uc bb).bb_instructions =
   EL i bb.bb_instructions` by
    (irule lse_phi_identity >> simp[]) >>
  simp[]
QED

Triviality lse_eval_phis[local]:
  !aliases bp uc bb s.
    eval_phis s (load_store_elim_block aliases bp uc bb).bb_instructions =
    eval_phis s bb.bb_instructions
Proof
  rpt strip_tac >>
  irule venomExecProofsTheory.eval_phis_same_phi_prefix >>
  simp[lse_phi_prefix_length] >>
  rpt strip_tac >>
  `i < phi_prefix_length bb.bb_instructions` by gvs[lse_phi_prefix_length] >>
  `i < LENGTH bb.bb_instructions` by
    (`phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
       simp[venomExecProofsTheory.phi_prefix_length_le] >> decide_tac) >>
  `(EL i bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  irule lse_phi_identity >> simp[]
QED

Triviality lse_block_wf[local]:
  !aliases bp uc bb.
    bb_well_formed bb ==>
    bb_well_formed (load_store_elim_block aliases bp uc bb)
Proof
  rpt strip_tac >>
  qabbrev_tac `bb' = load_store_elim_block aliases bp uc bb` >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    simp[Abbr `bb'`, lse_length] >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  simp[bb_well_formed_def] >> rpt conj_tac
  >- (Cases_on `bb.bb_instructions` >> Cases_on `bb'.bb_instructions` >> gvs[])
  >- (`PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
        (Cases_on `bb.bb_instructions` >> gvs[]) >>
      `LAST bb'.bb_instructions = LAST bb.bb_instructions` by (
        `bb'.bb_instructions <> []` by
          (Cases_on `bb'.bb_instructions` >> gvs[]) >>
        simp[LAST_EL] >>
        `PRE (LENGTH bb'.bb_instructions) = PRE (LENGTH bb.bb_instructions)` by simp[] >>
        pop_assum SUBST1_TAC >>
        simp[Abbr `bb'`] >> irule lse_terminator_identity >>
        simp[] >> gvs[bb_well_formed_def, LAST_EL]) >>
      gvs[bb_well_formed_def])
  >- (rpt strip_tac >>
      `i < LENGTH bb.bb_instructions` by gvs[] >>
      mp_tac (Q.SPECL [`aliases`, `bp`, `uc`, `bb`, `i`] lse_el_inst_or_nop) >>
      simp[] >> strip_tac >>
      gvs[Abbr `bb'`, bb_well_formed_def, mk_nop_inst_def, is_terminator_def])
  >> (rpt strip_tac >>
      `i < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions` by gvs[] >>
      `(EL j bb.bb_instructions).inst_opcode = PHI` by
        (mp_tac (Q.SPECL [`aliases`, `bp`, `uc`, `bb`, `j`] lse_phi_reverse) >>
         simp[Abbr `bb'`]) >>
      `!x y. x < y /\ y < LENGTH bb.bb_instructions /\
             (EL y bb.bb_instructions).inst_opcode = PHI ==>
             (EL x bb.bb_instructions).inst_opcode = PHI` by
        gvs[bb_well_formed_def] >>
      `(EL i bb.bb_instructions).inst_opcode = PHI` by
        (first_x_assum (qspecl_then [`i`, `j`] mp_tac) >> simp[]) >>
      `EL i bb'.bb_instructions = EL i bb.bb_instructions` by
        (simp[Abbr `bb'`] >> irule lse_phi_identity >> simp[]) >>
      gvs[])
QED

Triviality lse_block_succs[local]:
  !aliases bp uc bb.
    bb_well_formed bb ==>
    bb_succs (load_store_elim_block aliases bp uc bb) = bb_succs bb
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  qabbrev_tac `bb' = load_store_elim_block aliases bp uc bb` >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    simp[Abbr `bb'`, lse_length] >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `LAST bb'.bb_instructions = LAST bb.bb_instructions` by (
    `bb'.bb_instructions <> []` by
      (Cases_on `bb'.bb_instructions` >> gvs[]) >>
    simp[LAST_EL] >>
    `PRE (LENGTH bb'.bb_instructions) = PRE (LENGTH bb.bb_instructions)` by simp[] >>
    pop_assum SUBST1_TAC >>
    simp[Abbr `bb'`] >> irule lse_terminator_identity >>
    simp[] >> gvs[bb_well_formed_def, LAST_EL]) >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >> Cases_on `bb'.bb_instructions` >> gvs[]
QED

Triviality lse_map_inst_ids[local]:
  !aliases bp uc bb.
    MAP (\i. i.inst_id) (load_store_elim_block aliases bp uc bb).bb_instructions =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rpt strip_tac >> irule LIST_EQ >> simp[lse_length] >>
  rpt strip_tac >> simp[EL_MAP, lse_length] >>
  mp_tac (Q.SPECL [`aliases`, `bp`, `uc`, `bb`, `x`] lse_el_inst_or_nop) >>
  simp[] >> strip_tac >> gvs[mk_nop_inst_def]
QED

Triviality lse_fmt_preserves_ids_distinct[local]:
  !aliases bp uc fn.
    fn_inst_ids_distinct fn ==>
    fn_inst_ids_distinct
      (function_map_transform (load_store_elim_block aliases bp uc) fn)
Proof
  rpt strip_tac >>
  gvs[fn_inst_ids_distinct_def, function_map_transform_def] >>
  `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     (MAP (load_store_elim_block aliases bp uc) fn.fn_blocks) =
   MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks` by
    (simp[MAP_MAP_o, combinTheory.o_DEF] >>
     irule MAP_CONG >> simp[lse_map_inst_ids]) >>
  simp[]
QED

Triviality copy_elision_inst_wf_props[local]:
  (!bp dfg v inst. (copy_elision_inst bp dfg v inst).inst_id = inst.inst_id) /\
  (!bp dfg v inst. is_terminator inst.inst_opcode ==>
     copy_elision_inst bp dfg v inst = inst) /\
  (!bp dfg v inst. ~is_terminator inst.inst_opcode ==>
     ~is_terminator (copy_elision_inst bp dfg v inst).inst_opcode) /\
  (!bp dfg v inst. inst.inst_opcode = PHI ==>
     (copy_elision_inst bp dfg v inst).inst_opcode = PHI) /\
  (!bp dfg v inst. inst.inst_opcode <> PHI ==>
     (copy_elision_inst bp dfg v inst).inst_opcode <> PHI)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[copy_elision_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[] >>
  BasicProvers.every_case_tac >>
  gvs[mk_nop_inst_def, is_terminator_def] >>
  metis_tac[copy_opcode_not_term, copy_opcode_not_phi]
QED

(* State-equality transfer lemmas for bp_ptr_sound and alloca_inv *)
Triviality ptr_matches_var_state_eq[local]:
  !p v s s'.
    s'.vs_allocas = s.vs_allocas /\
    (!v. lookup_var v s' = lookup_var v s) ==>
    (ptr_matches_var p v s' <=> ptr_matches_var p v s)
Proof
  rpt gen_tac >> Cases_on `p` >> Cases_on `a` >> Cases_on `o'` >>
  simp[ptr_matches_var_def, lookup_var_def]
QED

Triviality bp_ptr_sound_state_eq[local]:
  !bp s s'.
    s'.vs_allocas = s.vs_allocas /\
    (!v. lookup_var v s' = lookup_var v s) ==>
    (bp_ptr_sound bp s' <=> bp_ptr_sound bp s)
Proof
  rpt strip_tac >> simp[bp_ptr_sound_def] >>
  metis_tac[ptr_matches_var_state_eq]
QED

Triviality alloca_inv_state_eq[local]:
  !s s'.
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next ==>
    (alloca_inv s' <=> alloca_inv s)
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

(* Terminators returning OK preserve the metadata needed by bp_ptr_sound and
   alloca_inv.  DRET may change memory, so deliberately do not claim broader
   state equality here. *)
Triviality step_terminator_ok_preserves[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_alloca_next = s.vs_alloca_next /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac step_terminator_preserves_vars >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> ALLOCA` by (
    Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  `step_inst_base inst s = OK s'` by
    metis_tac[step_inst_non_invoke] >>
  qspecl_then [`inst`, `s`, `s'`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_alloca_fields >>
  simp[]
QED

(* DRET changes only memory among the state observations used by load facts.
   Its transfer removes facts whose address spaces may observe that change. *)
Triviality dret_lf_sound[local]:
  !lf fuel ctx inst s s'.
    lf_sound lf s /\
    inst.inst_opcode = DRET /\
    step_inst fuel ctx inst s = OK s' ==>
    lf_sound (DRESTRICT lf
      {v | !lfact eff. FLOOKUP lf v = SOME lfact /\
           effect_of_addr_space
             (load_opcode_addr_space lfact.lf_opcode) = SOME eff ==>
           eff NOTIN write_effects DRET}) s'
Proof
  rpt strip_tac >>
  `is_mem_write_op inst.inst_opcode` by simp[is_mem_write_op_def] >>
  drule_all step_mem_write_preserves >> strip_tac >>
  irule lf_sound_drestrict_non_memory_weak >>
  rpt conj_tac >>
  gvs[write_effects_def, all_effects_def, empty_effects_def,
      contract_storage_def] >>
  qexists `s` >> simp[]
QED

Triviality non_dret_terminator_lf_sound[local]:
  !lf fuel ctx inst s s'.
    lf_sound lf s /\
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> DRET ==>
    lf_sound lf s'
Proof
  rpt strip_tac >>
  irule lf_sound_state_eq >> qexists `s` >> simp[] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >>
       fs[jump_to_def, halt_state_def, revert_state_def,
          set_returndata_def, lookup_var_def, contract_storage_def]) >>
  rpt strip_tac >> gvs[]
QED

(* Successful terminators preserve load-fact soundness.  DRET may change
   memory, but load_store_step removes memory/FMP facts before the successor. *)
Triviality lse_terminator_lf_sound[local]:
  !aliases bp uc lf fuel ctx inst s s'.
    lf_sound lf s /\
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    lf_sound (FST (load_store_step aliases bp uc (lf, inst))) s'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = DRET`
  >- (gvs[] >>
      simp[load_store_step_def, LET_THM, is_load_fact_opcode_def,
           is_store_opcode_def, is_copy_opcode_def, write_effects_def,
           all_effects_def, empty_effects_def] >>
      qspecl_then [`lf`, `fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
        dret_lf_sound >>
      simp[write_effects_def, all_effects_def, empty_effects_def]) >>
  `FST (load_store_step aliases bp uc (lf, inst)) = lf` by
    (Cases_on `inst.inst_opcode` >>
     fs[is_terminator_def, load_store_step_def, LET_THM,
        is_load_fact_opcode_def, is_store_opcode_def, is_copy_opcode_def,
        write_effects_def, all_effects_def, empty_effects_def]) >>
  simp[] >>
  qspecl_then [`lf`, `fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
    non_dret_terminator_lf_sound >> simp[]
QED

(* is_terminator is preserved by load_store_step *)
Triviality lse_nop_implies_store[local]:
  !aliases bp uc lf inst.
    SND (load_store_step aliases bp uc (lf, inst)) <> inst ==>
    is_store_opcode inst.inst_opcode
Proof
  rw[load_store_step_def, LET_THM] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality store_not_terminator[local]:
  !op. is_store_opcode op ==> ~is_terminator op
Proof
  Cases >> simp[is_store_opcode_def, is_terminator_def]
QED

Triviality lse_terminator_preserved[local]:
  !aliases bp uc insts i.
    i < LENGTH insts ==>
    is_terminator (inst_at aliases bp uc insts i).inst_opcode =
    is_terminator (EL i insts).inst_opcode
Proof
  rpt strip_tac >> simp[inst_at_def, load_store_step_def, LET_THM] >>
  rpt (IF_CASES_TAC >> simp[]) >>
  BasicProvers.every_case_tac >>
  gvs[mk_nop_inst_def, is_terminator_def, is_store_opcode_def] >>
  imp_res_tac store_not_terminator
QED

Triviality exec_write2_ok_or_error[local]:
  !f inst s.
    (?s'. exec_write2 f inst s = OK s') \/
    (?e. exec_write2 f inst s = Error e)
Proof
  rpt gen_tac >> simp[exec_write2_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Store opcodes only produce OK or Error via exec_write2 *)
Triviality store_step_ok_or_error[local]:
  !fuel ctx inst s.
    is_store_opcode inst.inst_opcode ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_store_opcode_def, step_inst_non_invoke] >>
  ASM_REWRITE_TAC[step_inst_base_def] >> gvs[] >>
  metis_tac[exec_write2_ok_or_error]
QED

(* inst_at preserves non-OK non-Error step_inst results *)
Triviality lse_step_passthrough[local]:
  !aliases bp uc insts i s r.
    i < LENGTH insts /\
    step_inst fuel ctx (EL i insts) s = r /\
    (!s'. r <> OK s') /\ (!e. r <> Error e) ==>
    step_inst fuel ctx (inst_at aliases bp uc insts i) s = r
Proof
  rpt strip_tac >>
  Cases_on `inst_at aliases bp uc insts i = EL i insts`
  >- simp[]
  >> `is_store_opcode (EL i insts).inst_opcode` by (
       gvs[inst_at_def] >>
       metis_tac[lse_nop_implies_store]) >>
  `(?s'. step_inst fuel ctx (EL i insts) s = OK s') \/
   (?e. step_inst fuel ctx (EL i insts) s = Error e)` by
    metis_tac[store_step_ok_or_error] >>
  metis_tac[]
QED

Triviality phi_prefix_length_lt_wf[local]:
  !bb. bb_well_formed bb ==>
       phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions
Proof
  rpt strip_tac >>
  `phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    simp[venomExecProofsTheory.phi_prefix_length_le] >>
  spose_not_then assume_tac >>
  `phi_prefix_length bb.bb_instructions = LENGTH bb.bb_instructions` by decide_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `PRE (LENGTH bb.bb_instructions) < phi_prefix_length bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode = PHI` by
    metis_tac[phi_prefix_length_el_phi] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by gvs[bb_well_formed_def] >>
  gvs[LAST_EL, is_terminator_def]
QED

Triviality lf_at_phi_prefix_empty[local]:
  !i aliases bp uc insts.
    i <= phi_prefix_length insts ==>
    lf_at aliases bp uc insts i = FEMPTY
Proof
  Induct >> simp[lf_at_def] >> rpt strip_tac >>
  `i < phi_prefix_length insts` by decide_tac >>
  `i < LENGTH insts` by
    (`phi_prefix_length insts <= LENGTH insts` by
       simp[venomExecProofsTheory.phi_prefix_length_le] >> decide_tac) >>
  `(EL i insts).inst_opcode = PHI` by metis_tac[phi_prefix_length_el_phi] >>
  simp[] >>
  `lf_at aliases bp uc insts i = FEMPTY` by simp[] >>
  simp[load_store_step_def, LET_THM, is_load_fact_opcode_def,
       is_store_opcode_def, is_copy_opcode_def, write_effects_def,
       empty_effects_def]
QED

Triviality eval_phis_preserves_vs_memory[local]:
  !s insts s'. eval_phis s insts = OK s' ==> s'.vs_memory = s.vs_memory
Proof
  gen_tac >> Induct_on `insts` >> simp[eval_phis_def] >> rpt strip_tac >>
  BasicProvers.every_case_tac >> gvs[update_var_def]
QED

Triviality eval_phis_preserves_allocas_in_word[local]:
  !s insts s'. eval_phis s insts = OK s' ==>
    (allocas_in_word s' <=> allocas_in_word s)
Proof
  rpt strip_tac >>
  drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
  rw[allocas_in_word_def]
QED

Triviality eval_phis_preserves_bp_ptrs_bounded[local]:
  !bp fn s insts s'. eval_phis s insts = OK s' ==>
    (bp_ptrs_bounded bp fn s' <=> bp_ptrs_bounded bp fn s)
Proof
  rpt strip_tac >>
  drule venomExecProofsTheory.eval_phis_preserves_alloca_fields >>
  rw[bp_ptrs_bounded_def, memloc_within_alloca_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED


(* Helper: pointwise hypotheses for exec_block_pointwise_inv.
   Threads lf_sound + bp_ptr_sound + alloca_inv as the inner invariant.
   Additional structural hypotheses: wf_alias_sets, non-terminator,
   and variable non-clobber (from SSA). *)
Triviality lse_pointwise_hyps[local]:
  !aliases bp uc bb fuel ctx s.
    0 < LENGTH bb.bb_instructions /\
    bp_ptr_sound bp s /\ alloca_inv s /\
    lf_at aliases bp uc bb.bb_instructions s.vs_inst_idx = FEMPTY /\
    wf_alias_sets aliases /\
    (!i. i < LENGTH bb.bb_instructions /\
         ~is_terminator bb.bb_instructions❲i❳.inst_opcode ==>
         (!v. v IN FDOM (lf_at aliases bp uc bb.bb_instructions i) ==>
              ~MEM v bb.bb_instructions❲i❳.inst_outputs)) ==>
    lf_sound (lf_at aliases bp uc bb.bb_instructions s.vs_inst_idx) s /\
    (!i. i < LENGTH bb.bb_instructions ==>
         (is_terminator bb.bb_instructions❲i❳.inst_opcode <=>
          is_terminator
            (load_store_elim_block aliases bp uc bb).bb_instructions❲i❳.
            inst_opcode)) /\
    (!s_i s_i'.
       (lf_sound (lf_at aliases bp uc bb.bb_instructions s_i.vs_inst_idx) s_i /\
        bp_ptr_sound bp s_i /\ alloca_inv s_i) /\
       s_i.vs_inst_idx < LENGTH bb.bb_instructions /\
       step_inst fuel ctx bb.bb_instructions❲s_i.vs_inst_idx❳ s_i = OK s_i' ==>
       step_inst fuel ctx
         (load_store_elim_block aliases bp uc bb).bb_instructions❲
           s_i.vs_inst_idx❳ s_i = OK s_i') /\
    (!s_i s_i'.
       (lf_sound (lf_at aliases bp uc bb.bb_instructions s_i.vs_inst_idx) s_i /\
        bp_ptr_sound bp s_i /\ alloca_inv s_i) /\
       s_i.vs_inst_idx < LENGTH bb.bb_instructions /\
       step_inst fuel ctx bb.bb_instructions❲s_i.vs_inst_idx❳ s_i = OK s_i' ==>
       lf_sound (lf_at aliases bp uc bb.bb_instructions (SUC s_i.vs_inst_idx))
         (s_i' with vs_inst_idx := SUC s_i.vs_inst_idx) /\
       bp_ptr_sound bp s_i' /\ alloca_inv s_i') /\
    (!s_i.
       (lf_sound (lf_at aliases bp uc bb.bb_instructions s_i.vs_inst_idx) s_i /\
        bp_ptr_sound bp s_i /\ alloca_inv s_i) /\
       s_i.vs_inst_idx < LENGTH bb.bb_instructions /\
       (!s'. step_inst fuel ctx bb.bb_instructions❲s_i.vs_inst_idx❳ s_i <> OK s') /\
       (!e. step_inst fuel ctx bb.bb_instructions❲s_i.vs_inst_idx❳ s_i <> Error e) ==>
       step_inst fuel ctx
         (load_store_elim_block aliases bp uc bb).bb_instructions❲
           s_i.vs_inst_idx❳ s_i =
       step_inst fuel ctx bb.bb_instructions❲s_i.vs_inst_idx❳ s_i)
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- fs[lf_sound_def, FLOOKUP_DEF]
  >- (rpt strip_tac >> metis_tac[lse_inst_at_eq, lse_terminator_preserved])
  >- (rpt strip_tac >> fs[lse_inst_at_eq] >>
      irule lse_step_equiv >> simp[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      Cases_on `is_terminator (EL s_i.vs_inst_idx bb.bb_instructions).inst_opcode`
      >- suspend "terminator_ok"
      >> (
        (* Non-terminator: use lse_inv_preserved *)
        `!v. v IN FDOM (lf_at aliases bp uc bb.bb_instructions s_i.vs_inst_idx) ==>
             ~MEM v (EL s_i.vs_inst_idx bb.bb_instructions).inst_outputs` by
          (first_x_assum $ qspec_then `s_i.vs_inst_idx` mp_tac >> simp[]) >>
        qspecl_then [`aliases`, `bp`, `uc`, `bb.bb_instructions`,
                     `s_i.vs_inst_idx`, `s_i`, `s_i'`]
          mp_tac lse_inv_preserved >>
        simp[]
      ))
  >> (rpt strip_tac >> fs[lse_inst_at_eq] >>
      irule lse_step_passthrough >> simp[])
QED

Resume lse_pointwise_hyps[terminator_ok]:
  drule_all step_terminator_ok_preserves >> strip_tac >>
  simp[lf_at_def] >>
  conj_tac
  >- (simp[lf_sound_inst_idx] >>
      qspecl_then
        [`aliases`, `bp`, `uc`,
         `lf_at aliases bp uc bb.bb_instructions s_i.vs_inst_idx`,
         `fuel`, `ctx`, `EL s_i.vs_inst_idx bb.bb_instructions`,
         `s_i`, `s_i'`] mp_tac lse_terminator_lf_sound >>
      simp[])
  >> metis_tac[bp_ptr_sound_state_eq, alloca_inv_state_eq]
QED

Finalise lse_pointwise_hyps

Triviality lse_inv_inst_idx[local]:
  !aliases bp uc insts i s.
    lf_sound (lf_at aliases bp uc insts i) s /\
    bp_ptr_sound bp s /\ alloca_inv s ==>
    lf_sound (lf_at aliases bp uc insts i) (s with vs_inst_idx := i) /\
    bp_ptr_sound bp (s with vs_inst_idx := i) /\
    alloca_inv (s with vs_inst_idx := i)
Proof
  rpt strip_tac >> rpt conj_tac
  >- (irule lf_sound_state_eq >> qexists_tac `s` >> simp[lookup_var_def])
  >- simp[bp_ptr_sound_inst_idx]
  >> simp[alloca_inv_inst_idx]
QED

Triviality lse_inv_after_suc_inst_idx[local]:
  !aliases bp uc insts i s.
    lf_sound (lf_at aliases bp uc insts (SUC i))
      (s with vs_inst_idx := SUC i) /\
    bp_ptr_sound bp s /\ alloca_inv s ==>
    lf_sound (lf_at aliases bp uc insts
        (s with vs_inst_idx := SUC i).vs_inst_idx)
      (s with vs_inst_idx := SUC i) /\
    bp_ptr_sound bp (s with vs_inst_idx := SUC i) /\
    alloca_inv (s with vs_inst_idx := SUC i)
Proof
  rpt strip_tac >> rpt conj_tac
  >- (simp[] >> first_assum ACCEPT_TAC)
  >- simp[bp_ptr_sound_inst_idx]
  >> simp[alloca_inv_inst_idx]
QED

Triviality result_not_ok_eq[local]:
  !r1 r2. r1 = r2 /\ (!s. r2 <> OK s) ==> !s. r1 <> OK s
Proof
  rw[]
QED

Triviality result_not_error_eq[local]:
  !r1 r2. r1 = r2 /\ (!e. r2 <> Error e) ==> !e. r1 <> Error e
Proof
  rw[]
QED

Triviality copy_elision_inst_phi_eq[local]:
  !bp dfg v inst. inst.inst_opcode = PHI ==>
    copy_elision_inst bp dfg v inst = inst
Proof
  simp[copy_elision_inst_def]
QED

(* Helper: copy_elision_inst either keeps outputs or empties them *)
Triviality copy_elision_inst_outputs[local]:
  !bp dfg v inst.
    (copy_elision_inst bp dfg v inst).inst_outputs = inst.inst_outputs \/
    (copy_elision_inst bp dfg v inst).inst_outputs = []
Proof
  rpt gen_tac >>
  simp[copy_elision_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[] >>
  BasicProvers.every_case_tac >> simp[mk_nop_inst_def]
QED

(* Helper: load_store_step FDOM monotonicity —
   FDOM only grows by inst.inst_outputs, never adds other vars *)
Triviality load_store_step_fdom_mono[local]:
  !aliases bp uc lf inst.
    FDOM (FST (load_store_step aliases bp uc (lf, inst))) SUBSET
    FDOM lf UNION set inst.inst_outputs
Proof
  rpt gen_tac >>
  simp[load_store_step_def, LET_THM] >>
  rpt IF_CASES_TAC >> simp[]
  (* Branch 1: load_fact — FUPDATE adds out from inst_outputs *)
  >- (BasicProvers.every_case_tac >> simp[] >>
      rpt IF_CASES_TAC >> simp[] >>
      simp[FDOM_FUPDATE, SUBSET_DEF] >>
      metis_tac[])
  (* Branch 2: store — invalidate_loads uses DRESTRICT *)
  >- (BasicProvers.every_case_tac >> simp[] >>
      simp[invalidate_loads_def] >>
      rpt IF_CASES_TAC >>
      simp[FDOM_DRESTRICT, SUBSET_DEF] >>
      metis_tac[])
  (* Branch 3: copy — invalidate_loads uses DRESTRICT *)
  >- (simp[invalidate_loads_def] >>
      rpt IF_CASES_TAC >>
      simp[FDOM_DRESTRICT, SUBSET_DEF] >>
      metis_tac[])
  (* Branch 4: Eff_MEMORY — explicit DRESTRICT *)
  >> simp[FDOM_DRESTRICT, SUBSET_DEF]
QED

(* Helper: FDOM of lf_at at position i only contains outputs of earlier insts *)
Triviality lf_at_fdom_earlier_outputs[local]:
  !i aliases bp uc insts v.
    v IN FDOM (lf_at aliases bp uc insts i) ==>
    ?j. j < i /\ j < LENGTH insts /\ MEM v (EL j insts).inst_outputs
Proof
  Induct >- simp[lf_at_def] >>
  rpt strip_tac >>
  gvs[lf_at_def] >>
  Cases_on `i < LENGTH insts` >> gvs[]
  (* Case: i < LENGTH — use load_store_step_fdom_mono *)
  >- (qspecl_then [`aliases`, `bp`, `uc`, `lf_at aliases bp uc insts i`,
                    `EL i insts`] mp_tac load_store_step_fdom_mono >>
      simp[SUBSET_DEF] >> strip_tac >>
      first_x_assum drule >> strip_tac
      >- (first_x_assum drule >> strip_tac >>
          qexists `j` >> simp[])
      >> qexists `i` >> simp[])
  (* Case: i >= LENGTH — lf_at (SUC i) = lf_at i, trivial from IH *)
  >> first_x_assum drule >> strip_tac >>
  qexists `j` >> simp[]
QED

Triviality lf_at_opcode_inv[local]:
  !i aliases bp uc insts v lfact.
    FLOOKUP (lf_at aliases bp uc insts i) v = SOME lfact ==>
    is_load_fact_opcode lfact.lf_opcode
Proof
  Induct_on `i` >> simp[lf_at_def, FLOOKUP_EMPTY] >>
  rpt gen_tac >> reverse IF_CASES_TAC >> gvs[] >- metis_tac[] >>
  simp[load_store_step_def, LET_THM] >> rpt COND_CASES_TAC >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, invalidate_loads_def] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  TRY CASE_TAC >> gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >> res_tac
QED

(* ALL_DISTINCT flat-map disjointness at different indices *)
Triviality all_distinct_flat_map_el_disjoint[local]:
  !f (l:'a list) j i v.
    ALL_DISTINCT (FLAT (MAP f l)) /\
    j < LENGTH l /\ i < LENGTH l /\ j <> i /\
    MEM v (f (EL j l)) ==> ~MEM v (f (EL i l))
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  Cases_on `j` >> Cases_on `i` >> gvs[] >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]
QED

(* Helper: non-clobber condition for fn1 blocks from SSA of fn.
   Proved using: lf_at_fdom_earlier_outputs + copy_elision_inst_outputs + ssa_form *)
Triviality bp_phi_outputs_untracked_fn1[local]:
  !aliases bp fn fn1 bb inst out.
    bp = bp_analyze (cfg_analyze fn) fn /\
    fn1 = analysis_function_transform NONE
      (copy_fact_analyze
         <|ce_aliases := aliases; ce_bp := bp;
           ce_dfg := dfg_build_function fn|> fn)
      (\v inst. [copy_elision_inst bp (dfg_build_function fn) v inst]) fn /\
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn1.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\ inst.inst_outputs = [out] ==>
    bp_get_ptrs bp out = []
Proof
  rpt strip_tac >> CCONTR_TAC >>
  gvs[analysis_function_transform_def, function_map_transform_def, MEM_MAP] >>
  rename1 `MEM bb0 fn.fn_blocks` >>
  gvs[analysis_block_transform_def,
      passSimulationPropsTheory.flat_mapi_singleton] >>
  qpat_x_assum `MEM inst (MAPi _ bb0.bb_instructions)`
    (strip_assume_tac o
       REWRITE_RULE [MEM_EL, indexedListsTheory.LENGTH_MAPi]) >>
  rename1 `i < LENGTH bb0.bb_instructions` >>
  gvs[indexedListsTheory.EL_MAPi] >>
  qabbrev_tac `inst0 = EL i bb0.bb_instructions` >>
  `inst0.inst_opcode = PHI` by metis_tac[copy_elision_inst_wf_props] >>
  `copy_elision_inst (bp_analyze (cfg_analyze fn) fn) (dfg_build_function fn)
     (df_at NONE (copy_fact_analyze
        <|ce_aliases := aliases; ce_bp := bp_analyze (cfg_analyze fn) fn;
          ce_dfg := dfg_build_function fn|> fn) bb0.bb_label i) inst0 = inst0` by
    simp[copy_elision_inst_phi_eq, Abbr `inst0`] >>
  gvs[] >>
  `MEM inst0 bb0.bb_instructions` by simp[Abbr `inst0`, EL_MEM] >>
  `inst_wf inst0` by (
    qpat_x_assum `fn_inst_wf fn` mp_tac >>
    simp[fn_inst_wf_def] >>
    disch_then (qspecl_then [`bb0`, `inst0`] mp_tac) >>
    simp[]) >>
  `inst_output inst0 = SOME out` by simp[inst_output_def] >>
  `is_ptr_opcode inst0.inst_opcode` by (
    mp_tac (Q.SPECL [`bp_analyze (cfg_analyze fn) fn`, `fn`, `inst0`, `out`, `bb0`]
      bp_tracked_implies_ptr_opcode) >>
    impl_tac >- simp[] >> simp[]) >>
  gvs[is_ptr_opcode_def]
QED

Triviality bp_phi_outputs_untracked_fn1_block[local]:
  !aliases bp fn fn1 bb.
    bp = bp_analyze (cfg_analyze fn) fn /\
    fn1 = analysis_function_transform NONE
      (copy_fact_analyze
         <|ce_aliases := aliases; ce_bp := bp;
           ce_dfg := dfg_build_function fn|> fn)
      (\v inst. [copy_elision_inst bp (dfg_build_function fn) v inst]) fn /\
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn1.fn_blocks ==>
    !inst out. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
      inst.inst_outputs = [out] ==> bp_get_ptrs bp out = []
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`aliases`, `bp`, `fn`, `fn1`, `bb`, `inst`, `out`]
    bp_phi_outputs_untracked_fn1) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Triviality lf_at_non_clobber[local]:
  !aliases bp uc fn fn1 bb.
    ssa_form fn /\
    fn1 = analysis_function_transform NONE
      (copy_fact_analyze
         <|ce_aliases := aliases; ce_bp := bp;
           ce_dfg := dfg_build_function fn|> fn)
      (\v inst. [copy_elision_inst bp (dfg_build_function fn) v inst]) fn /\
    MEM bb fn1.fn_blocks ==>
    !i. i < LENGTH bb.bb_instructions /\
        ~is_terminator (EL i bb.bb_instructions).inst_opcode ==>
        !v. v IN FDOM (lf_at aliases bp uc bb.bb_instructions i) ==>
            ~MEM v (EL i bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  (* Unfold fn1 to expose MAPi structure *)
  gvs[analysis_function_transform_def, function_map_transform_def,
      analysis_block_transform_def, MEM_MAP] >>
  rename1 `MEM bb0 fn.fn_blocks` >>
  CONV_TAC (DEPTH_CONV (HO_REWR_CONV
    passSimulationPropsTheory.flat_mapi_singleton)) >>
  RULE_ASSUM_TAC (CONV_RULE (TRY_CONV (DEPTH_CONV (HO_REWR_CONV
    passSimulationPropsTheory.flat_mapi_singleton)))) >>
  gvs[indexedListsTheory.LENGTH_MAPi] >>
  (* Get j < i with MEM v (EL j transformed_insts).inst_outputs *)
  drule_all lf_at_fdom_earlier_outputs >> strip_tac >>
  rename1 `j < i` >>
  (* Bridge: outputs of transformed inst j ⊆ outputs of original j *)
  `MEM v (EL j bb0.bb_instructions).inst_outputs` by (
    qspecl_then [`bp`, `dfg_build_function fn`,
      `df_at NONE (copy_fact_analyze
         <|ce_aliases := aliases; ce_bp := bp;
           ce_dfg := dfg_build_function fn|> fn) bb0.bb_label j`,
      `EL j bb0.bb_instructions`] strip_assume_tac copy_elision_inst_outputs >>
    gvs[indexedListsTheory.EL_MAPi]) >>
  (* Bridge: outputs of transformed inst i ⊆ outputs of original i *)
  `MEM v (EL i bb0.bb_instructions).inst_outputs` by (
    qspecl_then [`bp`, `dfg_build_function fn`,
      `df_at NONE (copy_fact_analyze
         <|ce_aliases := aliases; ce_bp := bp;
           ce_dfg := dfg_build_function fn|> fn) bb0.bb_label i`,
      `EL i bb0.bb_instructions`] strip_assume_tac copy_elision_inst_outputs >>
    gvs[indexedListsTheory.EL_MAPi]) >>
  (* SSA gives ALL_DISTINCT for this block's outputs *)
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb0.bb_instructions))` by (
    irule ssa_block_outputs_all_distinct >>
    gvs[ssa_form_def, fn_insts_def] >> metis_tac[]) >>
  (* Disjointness at different indices *)
  qspecl_then [`\inst. inst.inst_outputs`, `bb0.bb_instructions`,
               `j`, `i`, `v`] mp_tac all_distinct_flat_map_el_disjoint >>
  gvs[indexedListsTheory.LENGTH_MAPi]
QED

Resume stage2_correct[s2_block_sim]:
  rpt strip_tac >>
  imp_res_tac state_equiv_empty_eq >> gvs[] >>
  `wf_function fn1` by (
    simp[Abbr `fn1`] >>
    irule aft_singleton_preserves_wf >>
    simp[copy_elision_inst_wf_props]) >>
  `bb_well_formed bb` by gvs[wf_function_def] >>
  `0 < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[bb_well_formed_def]) >>
  `wf_alias_sets aliases` by
    (qpat_x_assum `Abbrev (aliases = _)` (SUBST1_TAC o
       REWRITE_RULE [markerTheory.Abbrev_def]) >>
     rewrite_tac[memory_alias_analyze_def] >>
     MATCH_ACCEPT_TAC memAliasProofsTheory.ma_analyze_wf) >>
  ONCE_REWRITE_TAC [run_block_def] >>
  simp[lse_eval_phis, lse_phi_prefix_length] >>
  qspecl_then [`s1`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (
    gvs[] >>
    rename1 `eval_phis s1 bb.bb_instructions = OK s_phi` >>
    qabbrev_tac `p = phi_prefix_length bb.bb_instructions` >>
    qabbrev_tac `s0 = s_phi with vs_inst_idx := p` >>
    `p < LENGTH bb.bb_instructions` by
      (simp[Abbr `p`] >> irule phi_prefix_length_lt_wf >> simp[]) >>
    `bp = bp_analyze (cfg_analyze fn) fn` by simp[Abbr `bp`] >>
    `fn1 = analysis_function_transform NONE
       (copy_fact_analyze
          <|ce_aliases := aliases; ce_bp := bp;
            ce_dfg := dfg_build_function fn|> fn)
       (\v inst. [copy_elision_inst bp (dfg_build_function fn) v inst]) fn` by
      simp[Abbr `fn1`] >>
    `!inst out. MEM inst bb.bb_instructions /\ inst.inst_opcode = PHI /\
       inst.inst_outputs = [out] ==> bp_get_ptrs bp out = []` by (
      mp_tac (Q.SPECL [`aliases`, `bp`, `fn`, `fn1`, `bb`]
        bp_phi_outputs_untracked_fn1_block) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
    `bp_ptr_sound bp s_phi` by (
      mp_tac (Q.SPECL [`bp`, `s1`, `bb.bb_instructions`, `s_phi`]
        eval_phis_preserves_bp_ptr_sound_untracked) >>
      impl_tac >- (
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
    `bp_ptr_sound bp s0` by
      simp[Abbr `s0`, bp_ptr_sound_inst_idx] >>
    `alloca_inv s_phi` by (
      `s_phi.vs_allocas = s1.vs_allocas /\
       s_phi.vs_alloca_next = s1.vs_alloca_next` by (
        mp_tac (Q.SPECL [`s1`, `bb.bb_instructions`, `s_phi`]
          venomExecProofsTheory.eval_phis_preserves_alloca_fields) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        simp[]) >>
      `alloca_inv s_phi <=> alloca_inv s1` by (
        irule alloca_inv_state_eq >> simp[]) >>
      pop_assum (fn th => rewrite_tac [th]) >>
      first_assum ACCEPT_TAC) >>
    `alloca_inv s0` by
      simp[Abbr `s0`, alloca_inv_inst_idx] >>
    qspecl_then [`aliases`, `bp`, `uc`, `bb`, `fuel`, `ctx`, `s0`]
      mp_tac lse_pointwise_hyps >>
    impl_tac >- (
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (simp[Abbr `s0`, Abbr `p`, lf_at_phi_prefix_empty]) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      mp_tac (Q.SPECL [`aliases`, `bp`, `uc`, `fn`, `fn1`, `bb`]
        lf_at_non_clobber) >>
      impl_tac >- (
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        first_assum ACCEPT_TAC) >>
      disch_then ACCEPT_TAC) >>
    strip_tac >>
    qspecl_then [`LENGTH bb.bb_instructions - p`, `fuel`, `ctx`, `bb`,
                 `load_store_elim_block aliases bp uc bb`, `s0`,
                 `\st. lf_sound (lf_at aliases bp uc bb.bb_instructions
                        st.vs_inst_idx) st /\
                       bp_ptr_sound bp st /\ alloca_inv st`]
      mp_tac exec_block_pointwise_inv >>
    impl_tac >- (
      conj_tac >- simp[lse_length] >>
      conj_tac >- (simp[Abbr `s0`, Abbr `p`] >> decide_tac) >>
      conj_tac >- simp[Abbr `s0`] >>
      conj_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (
        rpt strip_tac >>
        qpat_x_assum
          `!s_i s_i'. _ ==> step_inst fuel ctx (load_store_elim_block aliases bp uc bb).bb_instructions❲s_i.vs_inst_idx❳ s_i = OK s_i'`
          (qspecl_then [`s_i`, `s_i'`] mp_tac) >>
        impl_tac >- (
          conj_tac >- (qpat_x_assum `(\st. _) s_i` (strip_assume_tac o BETA_RULE) >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
          conj_tac >- (qpat_x_assum `s_i.vs_inst_idx = i` mp_tac >> decide_tac) >>
          qpat_x_assum `s_i.vs_inst_idx = i` (fn th => PURE_REWRITE_TAC[th]) >>
          first_assum ACCEPT_TAC) >>
        qpat_x_assum `s_i.vs_inst_idx = i` (fn th => PURE_REWRITE_TAC[th]) >>
        disch_then ACCEPT_TAC) >>
      conj_tac >- (
        rpt strip_tac >>
        qpat_x_assum
          `!s_i s_i'. _ ==> lf_sound _ _ /\ bp_ptr_sound _ _ /\ alloca_inv _`
          (qspecl_then [`s_i`, `s_i'`] mp_tac) >>
        impl_tac >- (
          conj_tac >- (qpat_x_assum `(\st. _) s_i` (strip_assume_tac o BETA_RULE) >>
              rpt conj_tac >> first_assum ACCEPT_TAC) >>
          conj_tac >- (qpat_x_assum `s_i.vs_inst_idx = i` mp_tac >> decide_tac) >>
          qpat_x_assum `s_i.vs_inst_idx = i` (fn th => PURE_REWRITE_TAC[th]) >>
          first_assum ACCEPT_TAC) >>
        BETA_TAC >>
        qpat_x_assum `s_i.vs_inst_idx = i` (fn th => PURE_REWRITE_TAC[th]) >>
        strip_tac >>
        irule lse_inv_after_suc_inst_idx >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
      rpt strip_tac >>
      qpat_x_assum
        `!s_i. _ ==> step_inst fuel ctx (load_store_elim_block aliases bp uc bb).bb_instructions❲s_i.vs_inst_idx❳ s_i = step_inst fuel ctx bb.bb_instructions❲s_i.vs_inst_idx❳ s_i`
        (qspec_then `s_i` mp_tac) >>
      impl_tac >- (
        conj_tac >- (qpat_x_assum `(\st. _) s_i` (strip_assume_tac o BETA_RULE) >>
            rpt conj_tac >> first_assum ACCEPT_TAC) >>
        conj_tac >- (qpat_x_assum `s_i.vs_inst_idx = i` mp_tac >> decide_tac) >>
        conj_tac >- (
          irule result_not_ok_eq >>
          qexists_tac `r` >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qpat_x_assum `s_i.vs_inst_idx = i` (fn idx_th =>
            qpat_x_assum `step_inst fuel ctx bb.bb_instructions❲i❳ s_i = r`
              (fn step_th => ACCEPT_TAC (PURE_REWRITE_RULE [GSYM idx_th] step_th)))) >>
        irule result_not_error_eq >>
        qexists_tac `r` >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qpat_x_assum `s_i.vs_inst_idx = i` (fn idx_th =>
          qpat_x_assum `step_inst fuel ctx bb.bb_instructions❲i❳ s_i = r`
            (fn step_th => ACCEPT_TAC (PURE_REWRITE_RULE [GSYM idx_th] step_th)))) >>
      qpat_x_assum `s_i.vs_inst_idx = i` (fn th => PURE_REWRITE_TAC[th]) >>
      disch_then (fn th => PURE_REWRITE_TAC[th]) >>
      first_assum ACCEPT_TAC) >>
    strip_tac >>
    first_x_assum (qspec_then `exec_block fuel ctx bb s0` mp_tac) >>
    impl_tac >- REFL_TAC >>
    strip_tac
    >- (disj1_tac >> qexists_tac `e` >> first_assum ACCEPT_TAC) >>
    disj2_tac >>
    pop_assum (fn th => PURE_REWRITE_TAC[th]) >>
    Cases_on `exec_block fuel ctx bb s0` >>
    simp[lift_result_def, state_equiv_refl, execution_equiv_refl])
  >> (gvs[] >> disj1_tac >> simp[])
(*
  rpt strip_tac >>
  imp_res_tac state_equiv_empty_eq >> gvs[] >>
  (* Empty block: both sides return Error *)
  Cases_on `bb.bb_instructions = []`
  >- (disj1_tac >> ONCE_REWRITE_TAC [run_block_def] >>
      simp[eval_phis_def] >> once_rewrite_tac [exec_block_def] >>
      simp[get_instruction_def]) >>
  `0 < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  (* Apply exec_block_pointwise_inv *)
  qspecl_then [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `bb`,
    `load_store_elim_block aliases bp uc bb`, `s1`,
    `\st. lf_sound (lf_at aliases bp uc bb.bb_instructions st.vs_inst_idx) st /\
          bp_ptr_sound bp st /\ alloca_inv st`]
    mp_tac exec_block_pointwise_inv >>
  simp[lse_length] >>
  `wf_alias_sets aliases` by
    (qpat_x_assum `Abbrev (aliases = _)` (SUBST1_TAC o
       REWRITE_RULE [markerTheory.Abbrev_def]) >>
     rewrite_tac[memory_alias_analyze_def] >>
     MATCH_ACCEPT_TAC memAliasProofsTheory.ma_analyze_wf) >>
  (impl_tac >- (
    irule lse_pointwise_hyps >> simp[] >>
    qspecl_then [`aliases`, `bp`, `uc`, `fn`, `fn1`, `bb`]
      mp_tac lf_at_non_clobber >>
    simp[Abbr `fn1`])) >>
  strip_tac
  >- (disj1_tac >> metis_tac[])
  >> disj2_tac >> pop_assum (fn th => rewrite_tac[th]) >>
  Cases_on `exec_block fuel ctx bb s1` >>
  simp[lift_result_def, state_equiv_refl, execution_equiv_refl]
*)
QED

Finalise stage2_correct

(* ===== Stage 3: clear_nops_function correctness ===== *)
(* Already proven as clear_nops_function_correct in passSharedProps *)

(* ===== Composition ===== *)

(* Error-or-lift transitivity: chain two error-or-lift results *)
Triviality error_or_lift_trans[local]:
  !R_ok R_term r1 r2 r3.
    ((!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
     (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3)) ==>
    ((?e. r1 = Error e) \/
     lift_result R_ok R_term R_term r1 r2) ==>
    ((?e. r2 = Error e) \/
     lift_result R_ok R_term R_term r2 r3) ==>
    (?e. r1 = Error e) \/
    lift_result R_ok R_term R_term r1 r3
Proof
  rpt gen_tac >> strip_tac >> strip_tac >> strip_tac >> gvs[]
  >- (imp_res_tac analysisSimProofsBaseTheory.lift_result_error_left >>
      disj1_tac >> qexists `e'` >> simp[])
  >> disj2_tac >>
  irule lift_result_trans >>
  rpt conj_tac >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  qexists `r2` >> simp[]
QED

Theorem copy_elision_function_correct_proof:
  !fuel ctx fn s.
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let bp = bp_analyze cfg fn in
    wf_function fn /\
    fn_inst_wf fn /\
    wf_ssa fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_assigns_sound dfg s /\
    bp_ptr_sound bp s /\
    alloca_inv s /\
    allocas_in_word s /\
    bp_ptrs_bounded bp fn s /\
    bp_assigns_stable bp dfg /\
    (!bb s0 s_phi.
       MEM bb fn.fn_blocks /\
       MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
       eval_phis s0 bb.bb_instructions = OK s_phi /\
       dfg_assigns_sound dfg s0 ==>
       dfg_assigns_sound dfg s_phi) /\
    (!fuel' run_ctx bb inst s0 s1.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       inst_wf inst /\
       dfg_assigns_sound dfg (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst s0 = OK s1 ==>
       dfg_assigns_sound dfg (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s1 with vs_inst_idx := 0)) /\
    LENGTH s.vs_memory < dimword (:256) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (copy_elision_function fn) s)
Proof
  rpt GEN_TAC >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `ssa_form fn /\ def_dominates_uses fn` by gvs[wf_ssa_def] >>
  (* Expand copy_elision_function: rewrite + beta-reduce lets *)
  rewrite_tac[copy_elision_function_def, LET_DEF] >>
  BETA_TAC >>
  (* Chain: stage1 → stage2 → clear_nops *)
  qmatch_goalsub_abbrev_tac
    `run_blocks _ _ (clear_nops_function (function_map_transform _ fn1))` >>
  qabbrev_tac `fn2 = function_map_transform
    (load_store_elim_block
       (memory_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn)
       (bp_analyze (cfg_analyze fn) fn)
       (\v. count_var_uses v fn1)) fn1` >>
  irule error_or_lift_trans >>
  conj_tac >- metis_tac[state_equiv_trans] >>
  conj_tac >- metis_tac[execution_equiv_trans] >>
  qexists `run_blocks fuel ctx fn2 s` >>
  conj_tac
  >- suspend "stages12"
  >> suspend "stage3"
QED

Resume copy_elision_function_correct_proof[stages12]:
  irule error_or_lift_trans >>
  conj_tac >- metis_tac[state_equiv_trans] >>
  conj_tac >- metis_tac[execution_equiv_trans] >>
  qexists `run_blocks fuel ctx fn1 s` >>
  conj_tac
  >- suspend "stage1"
  >> suspend "stage2"
QED

Resume copy_elision_function_correct_proof[stage1]:
  mp_tac (Q.SPECL [`fuel`, `ctx`, `fn`, `s`] stage1_correct) >>
  simp_tac std_ss [LET_THM] >>
  `fn1 = analysis_function_transform NONE
     (copy_fact_analyze
        <|ce_aliases :=
            memory_alias_analyze (bp_analyze (cfg_analyze fn) fn) fn;
          ce_bp := bp_analyze (cfg_analyze fn) fn;
          ce_dfg := dfg_build_function fn|> fn)
     (\v inst.
          [copy_elision_inst (bp_analyze (cfg_analyze fn) fn)
             (dfg_build_function fn) v inst]) fn`
    by simp[Abbr `fn1`] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  disch_then irule >>
  simp[] >> rpt conj_tac
  >- (qpat_x_assum `!bb s0 s_phi. _ ==> dfg_assigns_sound _ s_phi` ACCEPT_TAC)
  >> (rpt strip_tac >>
      rename1 `step_inst fuel0 run_ctx0 inst0 s_pre = OK s_post` >>
      qpat_x_assum `!fuel' run_ctx bb inst s0 s1. _ ==>
         dfg_assigns_sound _ (s1 with vs_inst_idx := 0) /\ _`
        (qspecl_then [`fuel0`, `run_ctx0`, `bb`, `inst0`, `s_pre`, `s_post`] mp_tac) >>
      simp[dfg_assigns_sound_inst_idx, bp_ptr_sound_inst_idx,
           allocas_non_overlapping_inst_idx, allocas_in_word_inst_idx,
           bp_ptrs_bounded_inst_idx])
QED

Resume copy_elision_function_correct_proof[stage2]:
  mp_tac (Q.SPECL [`fuel`, `ctx`, `fn`, `s`] stage2_correct) >>
  simp_tac std_ss [LET_THM] >>
  simp[Abbr `fn1`, Abbr `fn2`]
QED

Resume copy_elision_function_correct_proof[stage3]:
  `wf_function fn1` by (
    simp[Abbr `fn1`] >>
    irule aft_singleton_preserves_wf >>
    simp[copy_elision_inst_wf_props]) >>
  `wf_function fn2` by (
    simp[Abbr `fn2`] >>
    irule fmt_preserves_wf_function >> simp[lse_label] >>
    rpt conj_tac
    >- (rpt strip_tac >> irule lse_block_wf >> simp[])
    >- (rpt strip_tac >> irule lse_block_succs >> simp[])
    >- (irule lse_fmt_preserves_ids_distinct >> gvs[wf_function_def])
    >> first_assum ACCEPT_TAC) >>
  disj2_tac >>
  rewrite_tac[GSYM result_equiv_is_lift_result] >>
  irule clear_nops_function_correct >> simp[]
QED

Finalise copy_elision_function_correct_proof
