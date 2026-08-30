(*
 * Remove Unused Variables — Correctness proof helpers
 *
 * All intermediate lemmas used by removeUnusedCorrectnessScript.
 * Includes: monotonicity, structural helpers, cross-context equivalence.
 *)

Theory removeUnusedCorrectnessProofs
Ancestors
  removeUnusedDefs removeUnusedProofs removeUnusedFnProofs
  removeUnusedStructProofs
  passSharedDefs passSharedProps passSimulationDefs passSimulationProps
  venomState venomInst venomExecSemantics venomExecProps venomWf
  stateEquiv stateEquivProps
  crossBlockSimDefs crossBlockSimProps execEquivParamProps pointerConfinedDefs

(* ===== Monotonicity: larger excluded set is weaker ===== *)

Theorem execution_equiv_mono:
  !V1 V2 s1 s2. V1 SUBSET V2 /\ execution_equiv V1 s1 s2 ==>
    execution_equiv V2 s1 s2
Proof
  rw[execution_equiv_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem state_equiv_mono:
  !V1 V2 s1 s2. V1 SUBSET V2 /\ state_equiv V1 s1 s2 ==>
    state_equiv V2 s1 s2
Proof
  rw[state_equiv_def, execution_equiv_def, pred_setTheory.SUBSET_DEF] >>
  metis_tac[]
QED

Theorem lift_result_mono:
  !V1 V2 r1 r2.
    V1 SUBSET V2 /\
    lift_result (state_equiv V1) (execution_equiv V1) (execution_equiv V1) r1 r2 ==>
    lift_result (state_equiv V2) (execution_equiv V2) (execution_equiv V2) r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> gvs[lift_result_def] >>
  metis_tac[state_equiv_mono, execution_equiv_mono]
QED

Theorem result_equiv_mono:
  !V1 V2 r1 r2.
    V1 SUBSET V2 /\ result_equiv V1 r1 r2 ==>
    result_equiv V2 r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> gvs[result_equiv_def] >>
  metis_tac[state_equiv_mono, execution_equiv_mono]
QED

(* Each function's eliminated vars are a subset of the context-wide union *)
Theorem elim_subset_all_elim:
  !ctx fn. MEM fn ctx.ctx_functions ==>
    remove_unused_eliminated_vars fn SUBSET remove_unused_all_eliminated ctx
Proof
  rw[remove_unused_all_eliminated_def, pred_setTheory.SUBSET_DEF,
     pred_setTheory.IN_BIGUNION] >>
  rpt strip_tac >>
  qexists_tac `remove_unused_eliminated_vars fn` >> simp[] >>
  simp[listTheory.MEM_MAP] >> metis_tac[]
QED

(* ===== Bridge lemmas for precondition derivation ===== *)

Theorem fn_inst_wf_nop_outputs_empty:
  !fn. fn_inst_wf fn ==> nop_outputs_empty fn
Proof
  rw[fn_inst_wf_def, nop_outputs_empty_def] >>
  rpt strip_tac >> res_tac >>
  gvs[inst_wf_def]
QED

(* ===== Function-level correctness (same context) ===== *)

Theorem remove_unused_function_correct:
  !fuel ctx fn s.
    venom_wf ctx /\ wf_function fn /\ fn_inst_wf fn /\
    wf_ssa fn /\ alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    let elim = remove_unused_eliminated_vars fn in
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (remove_unused_function fn) s)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  mp_tac (SIMP_RULE std_ss [LET_THM]
    removeUnusedFnProofsTheory.remove_unused_function_correct_ssa) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `fn`, `s`] mp_tac) >>
  (impl_tac >- (
    fs[wf_ssa_def] >>
    metis_tac[fn_inst_wf_nop_outputs_empty])) >>
  simp[]
QED

(* ===== Structural helpers ===== *)

Theorem rusp_fn_name:
  !fn. (remove_unused_single_pass fn).fn_name = fn.fn_name
Proof
  rw[remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def, function_map_transform_def]
QED

Theorem ru_function_fn_name:
  !fn. (remove_unused_function fn).fn_name = fn.fn_name
Proof
  rw[remove_unused_function_def] >>
  Cases_on `remove_unused_iterate fn` >> simp[] >>
  rename1 `SOME r` >>
  fs[remove_unused_iterate_def] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`r`, `fn`] >>
  ho_match_mp_tac WhileTheory.OWHILE_IND >> rpt strip_tac >>
  gvs[rusp_fn_name]
QED

Theorem rusp_entry_label:
  !fn. fn_entry_label (remove_unused_single_pass fn) = fn_entry_label fn
Proof
  simp[removeUnusedStructProofsTheory.rusp_preserves_entry_label]
QED

Theorem ru_function_entry_label:
  !fn. fn_entry_label (remove_unused_function fn) = fn_entry_label fn
Proof
  rw[remove_unused_function_def] >>
  Cases_on `remove_unused_iterate fn` >> simp[] >>
  rename1 `SOME r` >>
  fs[remove_unused_iterate_def] >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`r`, `fn`] >>
  ho_match_mp_tac WhileTheory.OWHILE_IND >> rpt strip_tac >>
  gvs[rusp_entry_label]
QED

Theorem lookup_function_ru_context:
  !name ctx.
    lookup_function name (remove_unused_context ctx).ctx_functions =
    OPTION_MAP remove_unused_function
      (lookup_function name ctx.ctx_functions)
Proof
  rw[remove_unused_context_def, lookup_function_def] >>
  qspec_tac (`ctx.ctx_functions`, `fns`) >>
  Induct_on `fns` >> simp[listTheory.FIND_thm] >>
  rpt strip_tac >> simp[ru_function_fn_name] >> rw[]
QED

Theorem lookup_function_ru_none:
  !name ctx.
    lookup_function name ctx.ctx_functions = NONE ==>
    lookup_function name (remove_unused_context ctx).ctx_functions = NONE
Proof
  simp[lookup_function_ru_context]
QED

(* state_equiv_empty_eq: now in stateEquivPropsTheory *)
(* step_inst_ctx_irrel: now in venomExecPropsTheory *)

(* remove_unused_function preserves setup_callee (entry label unchanged) *)
Theorem setup_callee_ru:
  !fn args s.
    setup_callee (remove_unused_function fn) args s = setup_callee fn args s
Proof
  rw[setup_callee_def, fn_entry_label_def, entry_block_def] >>
  pop_assum mp_tac >>
  `fn_entry_label (remove_unused_function fn) = fn_entry_label fn`
    by simp[ru_function_entry_label] >>
  fs[fn_entry_label_def, entry_block_def] >>
  Cases_on `NULL fn.fn_blocks` >> fs[]
QED

(* execution_equiv implies merge_callee_state equality *)
Theorem merge_callee_execution_equiv:
  !V s1 s2 caller.
    execution_equiv V s1 s2 ==>
    merge_callee_state caller s1 = merge_callee_state caller s2
Proof
  rw[execution_equiv_def, merge_callee_state_def,
     venom_state_component_equality]
QED


(* setup_callee_props: now in venomExecPropsTheory *)

Triviality run_blocks_tail_ctx_change_or_error:
  !fuel ctx fn_t s.
    ((?e. run_blocks fuel ctx fn_t s = Error e) \/
     lift_result (state_equiv (remove_unused_all_eliminated ctx))
                 (execution_equiv (remove_unused_all_eliminated ctx))
                 (execution_equiv (remove_unused_all_eliminated ctx))
       (run_blocks fuel ctx fn_t s)
       (run_blocks fuel (remove_unused_context ctx) fn_t s)) ==>
    ((?e. (if s.vs_halted then Halt s else run_blocks fuel ctx fn_t s) = Error e) \/
     lift_result (state_equiv (remove_unused_all_eliminated ctx))
                 (execution_equiv (remove_unused_all_eliminated ctx))
                 (execution_equiv (remove_unused_all_eliminated ctx))
       (if s.vs_halted then Halt s else run_blocks fuel ctx fn_t s)
       (if s.vs_halted then Halt s else run_blocks fuel (remove_unused_context ctx) fn_t s))
Proof
  rpt strip_tac >> Cases_on `s.vs_halted` >> gvs[lift_result_def, execution_equiv_refl]
QED

Triviality run_blocks_tail_ctx_change_from_ih:
  !fuel ctx fn_t s.
    s.vs_inst_idx = 0 /\
    (!tail_s.
       tail_s.vs_inst_idx = 0 ==>
       (?e. run_blocks fuel ctx fn_t tail_s = Error e) \/
       lift_result (state_equiv (remove_unused_all_eliminated ctx))
                   (execution_equiv (remove_unused_all_eliminated ctx))
                   (execution_equiv (remove_unused_all_eliminated ctx))
         (run_blocks fuel ctx fn_t tail_s)
         (run_blocks fuel (remove_unused_context ctx) fn_t tail_s)) ==>
    ((?e. (if s.vs_halted then Halt s else run_blocks fuel ctx fn_t s) = Error e) \/
     lift_result (state_equiv (remove_unused_all_eliminated ctx))
                 (execution_equiv (remove_unused_all_eliminated ctx))
                 (execution_equiv (remove_unused_all_eliminated ctx))
       (if s.vs_halted then Halt s else run_blocks fuel ctx fn_t s)
       (if s.vs_halted then Halt s else run_blocks fuel (remove_unused_context ctx) fn_t s))
Proof
  rpt strip_tac >> irule run_blocks_tail_ctx_change_or_error >>
  first_x_assum irule >> simp[]
QED

(* Block-level ctx change. Strong conclusion:
   - Error on original, OR
   - Equal results (OK, IntRet, Error same on both sides), OR
   - Halt with execution_equiv all_elim, OR
   - Abort with execution_equiv all_elim.
   The OK-equality is needed so run_blocks can recurse with same state. *)
Theorem exec_block_cross_ctx_change_ru:
  !n fuel ctx bb s.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    (!f callee_s.
      MEM f ctx.ctx_functions /\
      callee_s.vs_inst_idx = 0 /\
      FDOM callee_s.vs_vars = {} /\
      fn_entry_label f = SOME callee_s.vs_current_bb ==>
      (?e. run_blocks fuel ctx f callee_s = Error e) \/
      lift_result (state_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
        (run_blocks fuel ctx f callee_s)
        (run_blocks fuel (remove_unused_context ctx)
                           (remove_unused_function f) callee_s)) ==>
    (?e. exec_block fuel ctx bb s = Error e) \/
    (exec_block fuel ctx bb s =
     exec_block fuel (remove_unused_context ctx) bb s) \/
    (?v v'. exec_block fuel ctx bb s = Halt v /\
            exec_block fuel (remove_unused_context ctx) bb s = Halt v' /\
            execution_equiv (remove_unused_all_eliminated ctx) v v') \/
    (?a v v'. exec_block fuel ctx bb s = Abort a v /\
              exec_block fuel (remove_unused_context ctx) bb s = Abort a v' /\
              execution_equiv (remove_unused_all_eliminated ctx) v v')
Proof
  Induct
  >- (
    (* Base case: n = 0 *)
    rpt gen_tac >> strip_tac >>
    `s.vs_inst_idx >= LENGTH bb.bb_instructions` by simp[] >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def])
  >>
  (* Inductive step: n = SUC n *)
  rpt gen_tac >> strip_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by simp[] >>
  simp[get_instruction_def] >>
  (* Non-INVOKE: ctx-independent, same step result *)
  reverse (Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = INVOKE`)
  >- (
    `step_inst fuel (remove_unused_context ctx)
       (EL s.vs_inst_idx bb.bb_instructions) s =
     step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` by
      metis_tac[step_inst_ctx_irrel] >>
    pop_assum (fn eq => PURE_REWRITE_TAC[eq]) >>
    Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
    simp[]
    >- (
      Cases_on `is_terminator
        (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >> simp[] >>
      Cases_on `v.vs_halted` >> simp[] >>
      first_x_assum irule >>
      qexists_tac `LENGTH bb.bb_instructions - v.vs_inst_idx` >>
      simp[])
    >> simp[])
  >>
  (* INVOKE case — keep callee hyp via qpat_assum *)
  ONCE_REWRITE_TAC[step_inst_def] >> simp[] >>
  Cases_on `decode_invoke (EL s.vs_inst_idx bb.bb_instructions)` >>
  simp[] >> (
    rename1 `SOME cn_args` >> Cases_on `cn_args` >>
    rename1 `SOME (callee_name, arg_ops)` >>
    Cases_on `lookup_function callee_name ctx.ctx_functions` >- (
      imp_res_tac lookup_function_ru_none >> simp[]) >>
    rename1 `_ = SOME callee_fn` >>
    simp[lookup_function_ru_context] >>
    Cases_on `eval_operands arg_ops s` >> simp[] >> (
      rename1 `SOME args` >>
      `MEM callee_fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
      simp[setup_callee_ru] >>
      Cases_on `setup_callee callee_fn args s` >> simp[] >> (
      rename1 `_ = SOME cs` >>
      imp_res_tac setup_callee_props >>
      (* Apply callee hypothesis (non-destructive — needed for IH) *)
      qpat_assum `!f cs'. MEM f _ /\ _ ==> _`
        (fn th => assume_tac th >>
                  mp_tac (Q.SPECL [`callee_fn`, `cs`] th)) >>
      (impl_tac >- simp[]) >> strip_tac >- (DISJ1_TAC >> gvs[]) >>
      (* Callee: lift_result *)
      Cases_on `run_blocks fuel ctx callee_fn cs` >>
      Cases_on `run_blocks fuel (remove_unused_context ctx)
                  (remove_unused_function callee_fn) cs` >>
      fs[lift_result_def] >> (
        (* IntRet / IntRet -> merge equal -> same result *)
        `merge_callee_state s v = merge_callee_state s v'` by
          metis_tac[merge_callee_execution_equiv] >>
        pop_assum (fn eq => PURE_REWRITE_TAC[eq]) >>
        simp[is_terminator_def] >>
        Cases_on `bind_outputs
          (EL s.vs_inst_idx bb.bb_instructions).inst_outputs
          i'.iret_values
          (adopt_return_fmp i' (merge_callee_state s v'))` >> simp[]))))
QED

(* ===== Cross-context function equivalence ===== *)
(*
 * Proves two properties simultaneously by fuel induction:
 *   Part A (cross-ctx): Error ∨ lift_result all_elim for fn vs fn' in ctx vs ctx'
 *   Part B (ctx-change): Error ∨ lift_result all_elim for fn_t in ctx vs ctx'
 *
 * Part B at SUC fuel uses: callee from Part A at fuel (for INVOKE),
 *   recursion from Part B at fuel (for OK continuation after block).
 * Part A at SUC fuel uses: same-ctx function_correct, then
 *   Part B at SUC fuel, composed via lift_result transitivity.
 *)
Theorem remove_unused_cross_ctx_fn_equiv:
  !fuel ctx.
    venom_wf ctx /\
    (!f. MEM f ctx.ctx_functions ==>
         wf_ssa f /\ alloca_pointer_confined f) ==>
    (* Part A: cross-ctx for functions starting at entry *)
    (!fn s.
      MEM fn ctx.ctx_functions /\
      s.vs_inst_idx = 0 /\
      fn_entry_label fn = SOME s.vs_current_bb ==>
      let all_elim = remove_unused_all_eliminated ctx in
      let ctx' = remove_unused_context ctx in
      let fn' = remove_unused_function fn in
      (?e. run_blocks fuel ctx fn s = Error e) \/
      lift_result (state_equiv all_elim) (execution_equiv all_elim) (execution_equiv all_elim)
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx' fn' s)) /\
    (* Part B: ctx-change for any function, any starting block *)
    (!fn_t s.
      s.vs_inst_idx = 0 ==>
      (?e. run_blocks fuel ctx fn_t s = Error e) \/
      lift_result (state_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
        (run_blocks fuel ctx fn_t s)
        (run_blocks fuel (remove_unused_context ctx) fn_t s))
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (
    (* Base: fuel = 0 — both Error *)
    conj_tac >> rpt strip_tac >> simp_tac std_ss [LET_THM] >>
    DISJ1_TAC >> simp[run_blocks_def])
  >>
  (* Inductive step: extract IH *)
  `(!fn s.
      MEM fn ctx.ctx_functions /\
      s.vs_inst_idx = 0 /\
      fn_entry_label fn = SOME s.vs_current_bb ==>
      (?e. run_blocks fuel ctx fn s = Error e) \/
      lift_result (state_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
        (run_blocks fuel ctx fn s)
        (run_blocks fuel (remove_unused_context ctx)
                           (remove_unused_function fn) s)) /\
   (!fn_t s.
      s.vs_inst_idx = 0 ==>
      (?e. run_blocks fuel ctx fn_t s = Error e) \/
      lift_result (state_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
        (run_blocks fuel ctx fn_t s)
        (run_blocks fuel (remove_unused_context ctx) fn_t s))`
    by (first_x_assum (qspec_then `ctx` mp_tac) >> simp[]) >>
  (* Prove Part B at SUC fuel first (needed by Part A) *)
  `!fn_t s.
    s.vs_inst_idx = 0 ==>
    (?e. run_blocks (SUC fuel) ctx fn_t s = Error e) \/
    lift_result (state_equiv (remove_unused_all_eliminated ctx))
                (execution_equiv (remove_unused_all_eliminated ctx))
                  (execution_equiv (remove_unused_all_eliminated ctx))
      (run_blocks (SUC fuel) ctx fn_t s)
      (run_blocks (SUC fuel) (remove_unused_context ctx) fn_t s)`
    by (
      rpt strip_tac >>
      ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[] >>
      Cases_on `lookup_block s.vs_current_bb fn_t.fn_blocks`
      >- simp[lift_result_def]
      >>
      rename1 `_ = SOME bb` >> fs[] >>
      ONCE_REWRITE_TAC[run_block_def] >>
      qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
      >- (
      qpat_x_assum `eval_phis s bb.bb_instructions = OK _`
        (fn eval_ok_th => PURE_REWRITE_TAC[eval_ok_th]) >>
      simp[] >>
      qmatch_goalsub_abbrev_tac `exec_block fuel ctx bb s_run` >>
      `!f callee_s.
          MEM f ctx.ctx_functions /\
          callee_s.vs_inst_idx = 0 /\
          FDOM callee_s.vs_vars = {} /\
          fn_entry_label f = SOME callee_s.vs_current_bb ==>
          (?e. run_blocks fuel ctx f callee_s = Error e) \/
          lift_result (state_equiv (remove_unused_all_eliminated ctx))
                      (execution_equiv (remove_unused_all_eliminated ctx))
                      (execution_equiv (remove_unused_all_eliminated ctx))
            (run_blocks fuel ctx f callee_s)
            (run_blocks fuel (remove_unused_context ctx)
                               (remove_unused_function f) callee_s)` by (
        rpt strip_tac >> metis_tac[]) >>
      `!tail_s.
          tail_s.vs_inst_idx = 0 ==>
          (?e. run_blocks fuel ctx fn_t tail_s = Error e) \/
          lift_result (state_equiv (remove_unused_all_eliminated ctx))
                      (execution_equiv (remove_unused_all_eliminated ctx))
                      (execution_equiv (remove_unused_all_eliminated ctx))
            (run_blocks fuel ctx fn_t tail_s)
            (run_blocks fuel (remove_unused_context ctx) fn_t tail_s)` by (
        rpt strip_tac >> metis_tac[]) >>
      mp_tac exec_block_cross_ctx_change_ru >>
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s_run.vs_inst_idx`,
         `fuel`, `ctx`, `bb`, `s_run`] mp_tac) >>
      (impl_tac >- simp[]) >>
      strip_tac
      >- (DISJ1_TAC >> gvs[])
      >- (
        pop_assum (fn eq => PURE_REWRITE_TAC[eq]) >>
        Cases_on `exec_block fuel (remove_unused_context ctx) bb s_run` >>
        fs[lift_result_def, execution_equiv_refl]
        >- (
          rename1 `if s_exec.vs_halted then _ else _` >>
          `s_exec.vs_inst_idx = 0` by (
            imp_res_tac exec_block_OK_inst_idx_0) >>
          irule run_blocks_tail_ctx_change_from_ih >>
          simp[] >>
          qpat_assum `!tail_s. tail_s.vs_inst_idx = 0 ==> _`
            (fn th => mp_tac (Q.SPEC `s_exec` th)) >>
          simp[]))
      >- (
        DISJ2_TAC >> fs[] >> simp[lift_result_def])
      >- (
        DISJ2_TAC >> fs[] >> simp[lift_result_def]))
      >- (
        rename1 `eval_phis s bb.bb_instructions = Error e` >>
        qpat_x_assum `eval_phis s bb.bb_instructions = Error e`
          (fn eval_err_th => PURE_REWRITE_TAC[eval_err_th]) >>
        DISJ1_TAC >> qexists_tac `e` >> simp[])) >>
  qabbrev_tac `all_elim = remove_unused_all_eliminated ctx` >>
  qabbrev_tac `ctx' = remove_unused_context ctx` >>
  conj_tac
  >- (
    (* Part A at SUC fuel *)
    rpt strip_tac >> simp_tac std_ss [LET_THM] >>
    `wf_function fn /\ fn_inst_wf fn` by fs[venom_wf_def] >>
    `wf_ssa fn /\ alloca_pointer_confined fn` by metis_tac[] >>
    (* Same-ctx equivalence: Error ∨ lift_result fn_elim *)
    mp_tac (SIMP_RULE std_ss [LET_THM] remove_unused_function_correct) >>
    disch_then (qspecl_then [`SUC fuel`, `ctx`, `fn`, `s`] mp_tac) >>
    (impl_tac >- fs[]) >>
    strip_tac >- metis_tac[] >>
    (* Weaken same-ctx result from fn_elim to all_elim *)
    `lift_result (state_equiv all_elim) (execution_equiv all_elim) (execution_equiv all_elim)
       (run_blocks (SUC fuel) ctx fn s)
       (run_blocks (SUC fuel) ctx (remove_unused_function fn) s)` by (
      irule lift_result_mono >>
      qexists_tac `remove_unused_eliminated_vars fn` >>
      simp[Abbr `all_elim`, elim_subset_all_elim]) >>
    (* Cross-ctx transition: Part B gives Error ∨ lift_result all_elim *)
    first_x_assum (qspec_then `remove_unused_function fn` mp_tac) >>
    disch_then (qspec_then `s` mp_tac) >> simp[] >>
    strip_tac
    >- (
      DISJ1_TAC >>
      Cases_on `run_blocks (SUC fuel) ctx fn s` >>
      Cases_on `run_blocks (SUC fuel) ctx (remove_unused_function fn) s` >>
      gvs[lift_result_def])
    >>
    (* Both phases give lift_result all_elim — compose *)
    DISJ2_TAC >>
    irule lift_result_trans >>
    conj_tac >- (rpt strip_tac >> metis_tac[state_equiv_trans]) >>
    conj_tac >- (rpt strip_tac >> metis_tac[execution_equiv_trans]) >>
    qexists_tac `run_blocks (SUC fuel) ctx (remove_unused_function fn) s` >>
    simp[Abbr `all_elim`, Abbr `ctx'`])
  >- (
    (* Part B at SUC fuel — already proved above *)
    simp[Abbr `all_elim`, Abbr `ctx'`])
QED

(* ===== Pass correctness: remove_unused preserves behavior on non-eliminated vars ===== *)

Theorem remove_unused_pass_correct:
  !ctx entry.
    venom_wf ctx /\
    (!fn. MEM fn ctx.ctx_functions ==>
          wf_ssa fn /\ alloca_pointer_confined fn) /\
    lookup_function entry ctx.ctx_functions <> NONE ==>
    let ctx' = remove_unused_context ctx in
    let all_elim = remove_unused_all_eliminated ctx in
    ?fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' /\
      !s. s.vs_inst_idx = 0 /\ fn_entry_label fn = SOME s.vs_current_bb /\
          (?f. terminates (run_blocks f ctx fn s)) ==>
          pass_correct (state_equiv all_elim) (execution_equiv all_elim) (execution_equiv all_elim)
            (\fuel. run_blocks fuel ctx fn s)
            (\fuel. run_blocks fuel ctx' fn' s)
Proof
  rpt gen_tac >> strip_tac >> simp[LET_THM] >>
  Cases_on `lookup_function entry ctx.ctx_functions` >> fs[] >>
  rename1 `_ = SOME fn` >>
  qexists_tac `remove_unused_function fn` >>
  conj_tac >- simp[lookup_function_ru_context] >>
  rpt strip_tac >>
  `MEM fn ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `wf_function fn /\ fn_inst_wf fn` by fs[venom_wf_def] >>
  `wf_ssa fn /\ alloca_pointer_confined fn` by metis_tac[] >>
  qabbrev_tac `all_elim = remove_unused_all_eliminated ctx` >>
  qabbrev_tac `ctx' = remove_unused_context ctx` >>
  qabbrev_tac `fn' = remove_unused_function fn` >>
  `!fuel.
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv all_elim) (execution_equiv all_elim) (execution_equiv all_elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx' fn' s)` by (
    gen_tac >>
    mp_tac remove_unused_cross_ctx_fn_equiv >>
    disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (fn th => assume_tac (CONJUNCT1 th)) >>
    first_x_assum (qspecl_then [`fn`, `s`] mp_tac) >>
    simp_tac std_ss [LET_THM] >>
    simp[Abbr `all_elim`, Abbr `ctx'`, Abbr `fn'`]) >>
  `!fuel. terminates (run_blocks fuel ctx fn s) ==>
    lift_result (state_equiv all_elim) (execution_equiv all_elim) (execution_equiv all_elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx' fn' s)` by (
    rpt strip_tac >>
    first_x_assum (qspec_then `fuel` strip_assume_tac) >>
    fs[terminates_def]) >>
  simp[pass_correct_def] >> conj_tac >| [
    eq_tac >> strip_tac
    >- (first_x_assum drule >> strip_tac >>
        qexists_tac `fuel` >>
        Cases_on `run_blocks fuel ctx fn s` >>
        Cases_on `run_blocks fuel ctx' fn' s` >>
        fs[lift_result_def, terminates_def])
    >- metis_tac[],
    rpt strip_tac >>
    `lift_result (state_equiv all_elim) (execution_equiv all_elim) (execution_equiv all_elim)
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx' fn' s)` by
      metis_tac[] >>
    `terminates (run_blocks fuel ctx' fn' s)` by (
      Cases_on `run_blocks fuel ctx fn s` >>
      Cases_on `run_blocks fuel ctx' fn' s` >>
      fs[lift_result_def, terminates_def]) >>
    `run_blocks fuel ctx' fn' s =
     run_blocks fuel' ctx' fn' s` by (
      simp_tac std_ss [Abbr `ctx'`, Abbr `fn'`] >>
      irule run_blocks_deterministic >> simp[]) >>
    fs[]]
QED

