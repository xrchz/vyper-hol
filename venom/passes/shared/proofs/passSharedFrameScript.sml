(*
 * Pass Shared Frame Properties
 *
 * Effect-independence and commutativity theorems for instruction execution.
 *
 * TOP-LEVEL:
 *   effects_independent_commute — independent instructions commute
 *)

Theory passSharedFrame
Ancestors
  passSharedVarFrame passSharedTransfer passSharedField

open venomStateTheory venomInstTheory venomExecSemanticsTheory
     venomEffectsTheory venomInstPropsTheory
     passSharedVarFrameTheory passSharedTransferTheory
     passSharedFieldTheory
     execEquivProofsTheory
     stateEquivTheory stateEquivProofsTheory
     vfmStateTheory;

(* ===================================================================== *)
(* ===== Targeted step_inst_preserves_all tactic ======================= *)
(* ===================================================================== *)

(* spa N = metis_tac using conjunct N of step_inst_preserves_all.
   ~100x faster than metis_tac[step_inst_preserves_all].
   Conjunct map: 1-prev_bb 2-current_bb 3-inst_idx 4-halted
   5-call_ctx 6-tx_ctx 7-block_ctx 8-data_section
   9-labels 10-code 11-params 12-prev_hashes 13-memory 14-immutables
   15-returndata 16-transient 17-accounts 18-logs *)
(* fast_conj: solve a conjunction goal where each conjunct is in assumptions.
   Much faster than fs[]/gvs[] when assumption count is high. *)
val fast_conj = rpt conj_tac >> first_assum ACCEPT_TAC;

(* spa: try fast drule_all first, fall back to metis (for chains) *)
fun spa n =
  (drule_all (cj n step_inst_preserves_all) >> simp[])
  ORELSE metis_tac[cj n step_inst_preserves_all];
fun spa_e n extras = metis_tac (cj n step_inst_preserves_all :: extras);

(* spa_assume_a: for unconditional conjuncts 1-12 (group A fields, including labels).
   Single impl_tac since there's only one antecedent. *)
fun spa_assume_a n inst_q s_q s'_q =
  mp_tac (Q.SPECL [`fuel`, `ctx`, inst_q, s_q, s'_q]
          (cj n step_inst_preserves_all)) >>
  (impl_tac >- fast_conj) >>
  strip_tac;

(* spa_assume: for conditional conjuncts 13-18 (group B fields, including memory).
   Two impl_tacs: main precondition + field-specific condition. *)
fun spa_assume n inst_q s_q s'_q =
  mp_tac (Q.SPECL [`fuel`, `ctx`, inst_q, s_q, s'_q]
          (cj n step_inst_preserves_all)) >>
  (impl_tac >- fast_conj) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac;

(* ===================================================================== *)
(* ===== Non-terminator result type elimination ======================== *)
(* ===================================================================== *)

Triviality exec_result_helpers_no_halt_abort[simp]:
  (!f inst s s'. exec_pure1 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure1 f inst s <> Abort a s') /\
  (!f inst s s'. exec_pure2 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure2 f inst s <> Abort a s') /\
  (!f inst s s'. exec_pure3 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure3 f inst s <> Abort a s') /\
  (!f inst s s'. exec_read0 f inst s <> Halt s') /\
  (!f inst s a s'. exec_read0 f inst s <> Abort a s') /\
  (!f inst s s'. exec_read1 f inst s <> Halt s') /\
  (!f inst s a s'. exec_read1 f inst s <> Abort a s') /\
  (!f inst s s'. exec_write2 f inst s <> Halt s') /\
  (!f inst s a s'. exec_write2 f inst s <> Abort a s') /\
  (!inst s alloc_size s'. exec_alloca inst s alloc_size <> Halt s') /\
  (!inst s alloc_size a s'. exec_alloca inst s alloc_size <> Abort a s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_result_helpers_not_intret[simp]:
  (!f inst s vs s'. exec_pure1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure2 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure3 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read0 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_write2 f inst s <> IntRet vs s') /\
  (!inst s alloc_size vs s'. exec_alloca inst s alloc_size <> IntRet vs s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_not_intret[simp]:
  (!inst s g a v ao as_ ro rs is_s vs s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> IntRet vs s') /\
  (!inst s g a ao as_ ro rs vs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> IntRet vs s') /\
  (!inst s v off sz salt vs s'.
     exec_create inst s v off sz salt <> IntRet vs s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_no_halt_abort[simp]:
  (!inst s g a v ao as_ ro rs is_s s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Halt s') /\
  (!inst s g a v ao as_ ro rs is_s ab s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Abort ab s') /\
  (!inst s g a ao as_ ro rs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Halt s') /\
  (!inst s g a ao as_ ro rs ab s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Abort ab s') /\
  (!inst s v off sz salt s'.
     exec_create inst s v off sz salt <> Halt s') /\
  (!inst s v off sz salt ab s'.
     exec_create inst s v off sz salt <> Abort ab s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

val step_base_result_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def];

Theorem step_inst_base_no_halt[local]:
  !inst s s'.
    step_inst_base inst s = Halt s' ==>
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  drule opcodeClassTheory.step_inst_base_halt_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem step_inst_base_no_intret[local]:
  !inst s vs s'.
    step_inst_base inst s = IntRet vs s' ==>
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  drule opcodeClassTheory.step_inst_base_intret_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

(* Non-INVOKE non-terminator step_inst can't produce Halt *)
Theorem step_inst_no_halt[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = Halt s' /\
    ~is_terminator inst.inst_opcode ==>
    inst.inst_opcode = INVOKE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
  gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_no_halt]
QED

(* Non-terminator step_inst can't produce IntRet *)
Theorem step_inst_no_intret[local]:
  !fuel ctx inst s vs s'.
    step_inst fuel ctx inst s = IntRet vs s' ==>
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[Once step_inst_def, AllCaseEqs()])
  >> (gvs[step_inst_non_invoke] >> metis_tac[step_inst_base_no_intret])
QED

(* ===================================================================== *)
(* ===== commute_equiv definition and helpers ============================ *)
(* ===================================================================== *)

(* State equivalence ignoring vs_allocas and specified variables.
 * vs_allocas is internal ALLOCA bookkeeping: concrete offsets depend
 * on allocation order but don't affect observable behaviour because
 * ALLOCA output vars are already excluded via the vars parameter.
 * This is state_equiv without the vs_allocas conjunct. *)
Definition commute_equiv_def:
  commute_equiv vars s1 s2 <=>
    (!w. w NOTIN vars ==> lookup_var w s1 = lookup_var w s2) /\
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    s1.vs_prev_hashes = s2.vs_prev_hashes
End

Theorem state_equiv_imp_commute_equiv[local]:
  !vars s1 s2. state_equiv vars s1 s2 ==> commute_equiv vars s1 s2
Proof
  rw[state_equiv_def, execution_equiv_def, commute_equiv_def]
QED

(* ===================================================================== *)
(* ===== step_inst_result_equiv for full step_inst ===================== *)
(* ===================================================================== *)

(* FOLDL update_var preserves state_equiv *)
Theorem foldl_update_var_state_equiv[local]:
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
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[]
QED

(* eval_operands on state_equiv states with operand vars outside vars *)
Theorem eval_operands_state_equiv[local]:
  !ops s1 s2 vars.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> rw[eval_operands_def] >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  Cases_on `h` >> gvs[eval_operand_def]
  >- (`lookup_var s s1 = lookup_var s s2` by
        gvs[state_equiv_def, execution_equiv_def] >>
      gvs[])
  >- (`s1.vs_labels = s2.vs_labels` by
        gvs[state_equiv_def, execution_equiv_def] >>
      gvs[])
QED

(* setup_callee on state_equiv states gives same result *)
Theorem setup_callee_state_equiv[local]:
  !fn args s1 s2 vars.
    state_equiv vars s1 s2 ==>
    setup_callee fn args s1 = setup_callee fn args s2
Proof
  rw[setup_callee_def] >>
  gvs[state_equiv_def, execution_equiv_def] >>
  rw[venomStateTheory.venom_state_component_equality]
QED

(* merge_callee_state on state_equiv callers gives state_equiv result *)
Theorem merge_callee_state_equiv[local]:
  !s1 s2 callee vars.
    state_equiv vars s1 s2 ==>
    state_equiv vars (merge_callee_state s1 callee)
                     (merge_callee_state s2 callee)
Proof
  rw[state_equiv_def, execution_equiv_def, merge_callee_state_def] >>
  gvs[lookup_var_def]
QED

(* Updating the returned FMP in the same way preserves state equivalence. *)
Theorem adopt_return_fmp_state_equiv[local]:
  !vars ir s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (adopt_return_fmp ir s1)
                     (adopt_return_fmp ir s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, state_equiv_def, execution_equiv_def,
      lookup_var_def]
QED

(* Extends execEquivProofs.step_inst_result_equiv (which only covers
   step_inst_base) to handle INVOKE via step_inst. *)
Theorem execution_equiv_refl[local]:
  !vars s. execution_equiv vars s s
Proof
  rw[execution_equiv_def]
QED

Theorem step_inst_result_equiv_full[local]:
  !vars fuel ctx inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~is_terminator inst.inst_opcode ==>
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
      irule eval_operands_state_equiv >> qexists_tac `vars` >> gvs[] >>
      rpt strip_tac >> first_x_assum irule >> gvs[]) >>
    Cases_on `lookup_function callee_name ctx.ctx_functions`
    >> gvs[result_equiv_def] >>
    Cases_on `eval_operands arg_ops s2` >> gvs[result_equiv_def] >>
    rename1 `SOME args` >>
    `setup_callee x args s1 = setup_callee x args s2`
      by (irule setup_callee_state_equiv >> metis_tac[]) >>
    Cases_on `setup_callee x args s2` >> gvs[result_equiv_def] >>
    Cases_on `run_blocks fuel ctx x x'` >> simp[] >>
    gvs[result_equiv_def, execution_equiv_refl] >>
    (* Only IntRet case remains *)
    `state_equiv vars (merge_callee_state s1 v)
                      (merge_callee_state s2 v)` by
      (irule merge_callee_state_equiv >> gvs[]) >>
    simp[bind_outputs_def] >>
    IF_CASES_TAC >> gvs[result_equiv_def]
    >- (`state_equiv vars
          (adopt_return_fmp i (merge_callee_state s1 v))
          (adopt_return_fmp i (merge_callee_state s2 v))` by
          (irule adopt_return_fmp_state_equiv >> gvs[]) >>
        irule foldl_update_var_state_equiv >> gvs[])
    >> irule adopt_return_fmp_state_equiv >> gvs[])
  >> (gvs[step_inst_non_invoke] >> irule step_inst_result_equiv >> gvs[])
QED

(* ===================================================================== *)
(* ===== Helpers for effects_independent_commute ======================= *)
(* ===================================================================== *)

(* inst_defs = inst_outputs, inst_uses = operand_vars *)

(* MEM (Var x) ops ==> MEM x (operand_vars ops) *)
Theorem mem_var_operand_vars[local]:
  !ops x. MEM (Var x) ops ==> MEM x (operand_vars ops)
Proof
  Induct >> rw[operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_var_def]
QED

(* operand vars of inst are a subset of inst_uses *)
Theorem operand_var_in_uses[local]:
  !x inst. MEM (Var x) inst.inst_operands ==> MEM x (inst_uses inst)
Proof
  rw[inst_uses_def] >> irule mem_var_operand_vars >> gvs[]
QED

(* commute_equiv is weaker than state_equiv *)
Theorem commute_equiv_subset[local]:
  !v1 v2 s1 s2. commute_equiv v1 s1 s2 /\ v1 SUBSET v2 ==>
    commute_equiv v2 s1 s2
Proof
  rw[commute_equiv_def] >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

(* state_equiv ⇒ commute_equiv (already proved, re-stated for reference)
   (see state_equiv_imp_commute_equiv above) *)

(* result_equiv for OK gives state_equiv *)
Theorem result_equiv_ok_state_equiv[local]:
  !vars s1 s2 r1 r2.
    result_equiv vars (OK s1) (OK s2) ==> state_equiv vars s1 s2
Proof
  rw[result_equiv_def]
QED

(* ===================================================================== *)
(* ===== Helpers for effects_independent_commute ======================= *)
(* ===================================================================== *)

(* ASSERT/ASSERT_UNREACHABLE with OK result leave state unchanged *)
Theorem step_inst_base_assert_ok[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) ==>
    s' = s
Proof
  rw[step_inst_base_def] >> gvs[AllCaseEqs()]
QED

(* For non-terminator non-alloca OK results with empty write_effects:
   state_equiv on outputs. Covers is_effect_free_op + ASSERT/ASSERT_UNREACHABLE. *)
Theorem step_inst_ok_state_equiv[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    write_effects inst.inst_opcode = {} ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  Cases_on `is_effect_free_op inst.inst_opcode`
  >- metis_tac[step_effect_free_state_equiv]
  >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[] >>
     qpat_x_assum `write_effects _ = _` mp_tac >> EVAL_TAC) >>
  gvs[step_inst_non_invoke] >>
  imp_res_tac step_inst_base_assert_ok >>
  gvs[state_equiv_def, execution_equiv_def] >>
  Cases_on `inst.inst_opcode` >> gvs[is_effect_free_op_def, is_terminator_def,
    is_alloca_op_def] >>
  gvs[write_effects_def, all_effects_def, empty_effects_def]
QED

(* effects_independent with all_effects implies empty effects on other side *)
Theorem effects_independent_all_effects[local]:
  !op1 op2. effects_independent op1 op2 /\
    write_effects op1 = all_effects ==>
    write_effects op2 = {} /\ read_effects op2 = {}
Proof
  rw[effects_independent_def, all_effects_def] >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  rw[pred_setTheory.EXTENSION] >>
  Cases_on `x` >> gvs[] >> metis_tac[]
QED

Theorem effects_independent_sym[local]:
  !a b. effects_independent a b <=> effects_independent b a
Proof
  rw[effects_independent_def] >> metis_tac[pred_setTheory.DISJOINT_SYM]
QED

(* If effects_independent with INVOKE on either side, the other has
   empty read and write effects. Symmetric — works regardless of position. *)
Theorem effects_independent_invoke_empty[local]:
  (!op. effects_independent INVOKE op ==>
        write_effects op = {} /\ read_effects op = {}) /\
  (!op. effects_independent op INVOKE ==>
        write_effects op = {} /\ read_effects op = {})
Proof
  rw[] >>
  imp_res_tac effects_independent_sym >>
  imp_res_tac effects_independent_all_effects >>
  gvs[EVAL ``write_effects INVOKE``, EVAL ``all_effects``]
QED

Theorem effects_independent_ext_call_empty[local]:
  !op1 op2. is_ext_call_op op1 /\ effects_independent op1 op2 ==>
            write_effects op2 = {}
Proof
  Cases_on `op1` >> gvs[is_ext_call_op_def]
  >- (Cases_on `op2` >> EVAL_TAC)
  >- (Cases_on `op2` >> EVAL_TAC)
  >- (Cases_on `op2` >> EVAL_TAC)
  >- (Cases_on `op2` >> EVAL_TAC)
  >- (Cases_on `op2` >> EVAL_TAC)
QED

(* Non-terminator non-INVOKE step_inst_base can only Abort from
   ASSERT (Revert_abort), ASSERT_UNREACHABLE (ExHalt_abort),
   RETURNDATACOPY (ExHalt_abort). All set returndata to []. *)
Theorem step_inst_base_abort_opcode[local]:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode ==>
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY
Proof
  step_base_result_tac
QED

Theorem step_inst_base_abort_returndata[local]:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_returndata = []
Proof
  rpt strip_tac >>
  imp_res_tac step_inst_base_abort_opcode >> gvs[]
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      rw[step_inst_base_def, set_returndata_def,
         revert_state_def, is_terminator_def,
         venom_state_component_equality, AllCaseEqs()])
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      rw[step_inst_base_def, set_returndata_def,
         halt_state_def, is_terminator_def,
         venom_state_component_equality, AllCaseEqs()])
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      rw[step_inst_base_def, set_returndata_def,
         halt_state_def, is_terminator_def,
         venom_state_component_equality, AllCaseEqs()])
QED

Theorem step_inst_base_abort_type[local]:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode ==>
    (inst.inst_opcode = ASSERT ==> a = Revert_abort) /\
    (inst.inst_opcode = ASSERT_UNREACHABLE ==> a = ExHalt_abort) /\
    (inst.inst_opcode = RETURNDATACOPY ==> a = ExHalt_abort)
Proof
  rpt strip_tac >>
  gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  rw[step_inst_base_def, is_terminator_def, AllCaseEqs()]
QED

(* Non-INVOKE aborters (ASSERT, ASSERT_UNREACHABLE, RETURNDATACOPY) are all
   abort_incompatible with INVOKE. So step_inst_base can't abort for a
   non-INVOKE instruction that is abort_compatible with INVOKE. *)
Theorem no_abort_with_invoke[local]:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode /\
    abort_compatible INVOKE inst.inst_opcode ==> F
Proof
  rpt strip_tac >>
  `inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE \/
   inst.inst_opcode = RETURNDATACOPY` by
    metis_tac[step_inst_base_abort_opcode] >>
  gvs[] >> qpat_x_assum `abort_compatible _ _` mp_tac >> EVAL_TAC
QED

Theorem no_abort_with_invoke2[local]:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode /\
    abort_compatible inst.inst_opcode INVOKE ==> F
Proof
  rpt strip_tac >>
  `inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE \/
   inst.inst_opcode = RETURNDATACOPY` by
    metis_tac[step_inst_base_abort_opcode] >>
  gvs[] >> qpat_x_assum `abort_compatible _ _` mp_tac >> EVAL_TAC
QED

(* KEY CROSS-CASE LEMMA: If inst_a has empty effects (from effects_independent)
   and returns OK, then inst_b gives the same result on s as on v (= step inst_a s).
   Combines effects_independent_all_effects + step_inst_ok_state_equiv +
   operand vars outside defs + step_inst_result_equiv_full. *)
Theorem cross_case_result_equiv[local]:
  !fuel ctx inst_a inst_b s v.
    step_inst fuel ctx inst_a s = OK v /\
    write_effects inst_a.inst_opcode = {} /\
    DISJOINT (set (inst_defs inst_a)) (set (inst_uses inst_b)) /\
    ~is_terminator inst_a.inst_opcode /\
    ~is_terminator inst_b.inst_opcode /\
    ~is_alloca_op inst_a.inst_opcode ==>
    result_equiv (set inst_a.inst_outputs)
      (step_inst fuel ctx inst_b s) (step_inst fuel ctx inst_b v)
Proof
  rpt strip_tac >>
  `state_equiv (set inst_a.inst_outputs) s v` by (
    irule step_inst_ok_state_equiv >> gvs[] >> metis_tac[]) >>
  irule step_inst_result_equiv_full >> gvs[] >>
  rpt strip_tac >>
  imp_res_tac operand_var_in_uses >>
  gvs[inst_defs_def] >>
  metis_tac[pred_setTheory.IN_DISJOINT]
QED

(* If a non-terminator aborts, it must be ASSERT/ASSERT_UNREACHABLE/RETURNDATACOPY.
   These only read operand values (+ returndata for RETURNDATACOPY).
   If those agree, the same Abort is produced on any state. *)
Theorem step_inst_base_abort_input_equiv:
  !inst s1 s2 a s1'.
    step_inst_base inst s1 = Abort a s1' /\
    ~is_terminator inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_labels = s2.vs_labels ==>
    ?s2'. step_inst_base inst s2 = Abort a s2'
Proof
  rpt strip_tac >>
  `inst.inst_opcode = ASSERT \/
   inst.inst_opcode = ASSERT_UNREACHABLE \/
   inst.inst_opcode = RETURNDATACOPY` by
    metis_tac[step_inst_base_abort_opcode] >>
  gvs[] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  rw[step_inst_base_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  rpt (first_x_assum (fn th => mp_tac (REWRITE_RULE [eval_operand_def] th))) >>
  rpt (CHANGED_TAC (
    TRY (Cases_on `cond_op` >> gvs[eval_operand_def]) >>
    TRY (Cases_on `op_destOffset` >> gvs[eval_operand_def]) >>
    TRY (Cases_on `op_offset` >> gvs[eval_operand_def]) >>
    TRY (Cases_on `op_size` >> gvs[eval_operand_def])))
QED

(* CROSS-CASE ABORT LEMMA: If inst_b is a non-INVOKE aborter on s,
   and inst_a returns OK with DISJOINT defs/uses and independent effects,
   then inst_b also aborts (same type) on v = step inst_a s.
   Returndata is [] in both abort states. *)
Theorem cross_case_abort_equiv[local]:
  !fuel ctx inst_a inst_b s v a s_abort.
    step_inst fuel ctx inst_a s = OK v /\
    inst_b.inst_opcode <> INVOKE /\
    step_inst_base inst_b s = Abort a s_abort /\
    effects_independent inst_a.inst_opcode inst_b.inst_opcode /\
    DISJOINT (set (inst_defs inst_a)) (set (inst_uses inst_b)) /\
    ~is_terminator inst_a.inst_opcode /\
    ~is_terminator inst_b.inst_opcode /\
    ~is_alloca_op inst_a.inst_opcode ==>
    ?v_abort. step_inst_base inst_b v = Abort a v_abort /\
              v_abort.vs_returndata = [] /\ s_abort.vs_returndata = []
Proof
  rpt strip_tac >>
  (* Operand values unchanged *)
  `!x. MEM (Var x) inst_b.inst_operands ==>
       lookup_var x s = lookup_var x v` by (
    rpt strip_tac >>
    imp_res_tac operand_var_in_uses >>
    `~MEM x (inst_defs inst_a)` by
      metis_tac[pred_setTheory.IN_DISJOINT] >>
    gvs[inst_defs_def] >>
    irule (GSYM step_preserves_non_output_vars) >> metis_tac[]) >>
  `v.vs_labels = s.vs_labels` by
    metis_tac[step_preserves_labels] >>
  imp_res_tac step_inst_base_abort_opcode >> gvs[]
  >- (
    (* ASSERT *)
    qpat_x_assum `step_inst_base inst_b s = _` mp_tac >>
    simp[step_inst_base_def] >>
    gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
    `eval_operand cond_op v = SOME 0w` by (
      Cases_on `cond_op` >> gvs[eval_operand_def]) >>
    gvs[revert_state_def, set_returndata_def])
  >- (
    (* ASSERT_UNREACHABLE *)
    qpat_x_assum `step_inst_base inst_b s = _` mp_tac >>
    simp[step_inst_base_def] >>
    gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
    `eval_operand cond_op v = SOME 0w` by (
      Cases_on `cond_op` >> gvs[eval_operand_def]) >>
    gvs[halt_state_def, set_returndata_def])
  >> (
    (* RETURNDATACOPY: need returndata agreement *)
    `Eff_RETURNDATA NOTIN write_effects inst_a.inst_opcode` by (
      gvs[effects_independent_def] >>
      `Eff_RETURNDATA IN read_effects RETURNDATACOPY` by EVAL_TAC >>
      metis_tac[pred_setTheory.IN_DISJOINT, pred_setTheory.IN_UNION]) >>
    `v.vs_returndata = s.vs_returndata` by
      metis_tac[write_effects_sound_returndata] >>
    qpat_x_assum `step_inst_base inst_b s = _` mp_tac >>
    simp[step_inst_base_def] >>
    gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
    `eval_operand op_destOffset v = SOME destOffset` by (
      Cases_on `op_destOffset` >> gvs[eval_operand_def]) >>
    `eval_operand op_offset v = SOME offset` by (
      Cases_on `op_offset` >> gvs[eval_operand_def]) >>
    `eval_operand op_size v = SOME size_val` by (
      Cases_on `op_size` >> gvs[eval_operand_def]) >>
    gvs[halt_state_def, set_returndata_def])
QED

(* Lifted version: all step_inst, no step_inst_base.
   The aborting instruction must be non-INVOKE (all aborters are). *)
Theorem cross_case_abort[local]:
  !fuel ctx inst_a inst_b s v a s_abort.
    step_inst fuel ctx inst_a s = OK v /\
    inst_b.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst_b s = Abort a s_abort /\
    effects_independent inst_a.inst_opcode inst_b.inst_opcode /\
    DISJOINT (set (inst_defs inst_a)) (set (inst_uses inst_b)) /\
    ~is_terminator inst_a.inst_opcode /\
    ~is_terminator inst_b.inst_opcode /\
    ~is_alloca_op inst_a.inst_opcode ==>
    ?v_abort. step_inst fuel ctx inst_b v = Abort a v_abort /\
              v_abort.vs_returndata = [] /\ s_abort.vs_returndata = []
Proof
  rpt strip_tac >>
  imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO] step_inst_non_invoke) >>
  full_simp_tac std_ss [] >>
  drule_all cross_case_abort_equiv >> strip_tac >>
  qexists_tac `v_abort` >> simp[]
QED

(* ===================================================================== *)
(* ===== OK×OK helpers ================================================= *)
(* ===================================================================== *)

(* If two states are both state_equiv to a common mid, they're commute_equiv *)
Theorem commute_equiv_from_state_equivs[local]:
  !defs vars mid s1 s2.
    state_equiv vars mid s1 /\
    state_equiv vars mid s2 /\
    vars SUBSET defs ==>
    commute_equiv defs s1 s2
Proof
  rw[state_equiv_def, execution_equiv_def, commute_equiv_def] >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED



(* When write_effects = {} and operand values agree, step returns OK on
   any state and produces state_equiv outputs.
   Key: write_effects = {} means is_effect_free_op or ASSERT/ASSERT_UNREACHABLE.
   All of these return OK iff operands evaluate (+ condition nonzero for ASSERT). *)
(* Helper: eval_operand agrees when lookup_var agrees on Var operands *)
Theorem eval_operand_agree[local]:
  !op s s'.
    (!x. MEM (Var x) [op] ==> lookup_var x s = lookup_var x s') /\
    s.vs_labels = s'.vs_labels ==>
    eval_operand op s = eval_operand op s'
Proof
  Cases >> rw[eval_operand_def]
QED

(* eval_operands agrees when all Var operands have same lookup *)
Theorem eval_operands_agree[local]:
  !ops s s'.
    (!x. MEM (Var x) ops ==> lookup_var x s = lookup_var x s') /\
    s.vs_labels = s'.vs_labels ==>
    eval_operands ops s = eval_operands ops s'
Proof
  Induct >> rw[eval_operands_def] >>
  `eval_operand h s = eval_operand h s'` by (
    Cases_on `h` >> gvs[eval_operand_def]) >>
  `eval_operands ops s = eval_operands ops s'` by (
    first_x_assum irule >> rw[]) >>
  simp[]
QED

(* When state_equiv holds between s and s', step returns OK on s' too.
   This is a simple wrapper around step_inst_result_equiv_full. *)
Theorem step_inst_transfer_via_equiv[local]:
  !fuel ctx inst s v s' vars.
    step_inst fuel ctx inst s = OK v /\
    state_equiv vars s s' /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    ~is_terminator inst.inst_opcode ==>
    ?v'. step_inst fuel ctx inst s' = OK v' /\
         state_equiv vars v v'
Proof
  rpt strip_tac >>
  `result_equiv vars (step_inst fuel ctx inst s) (step_inst fuel ctx inst s')` by (
    irule step_inst_result_equiv_full >> gvs[]) >>
  qpat_x_assum `step_inst _ _ _ s = OK _` (fn th => gvs[th]) >>
  Cases_on `step_inst fuel ctx inst s'` >>
  gvs[result_equiv_def]
QED

(* Helper: derive eval_operand agreement from lookup_var agreement *)
(* Helper: derive that non-terminator OK step preserves context fields needed
   for step_inst_base_ok_transfer *)
Theorem step_preserves_transfer_ctx[local]:
  !fuel ctx inst s v.
    step_inst fuel ctx inst s = OK v /\
    ~is_terminator inst.inst_opcode ==>
    v.vs_prev_bb = s.vs_prev_bb /\
    v.vs_params = s.vs_params
Proof
  metis_tac[step_preserves_control_flow, step_preserves_params]
QED

(* Empty write_effects implies not ext_call *)
Theorem empty_write_not_ext_call[local]:
  !op. write_effects op = {} ==> ~is_ext_call_op op
Proof
  Cases >> rw[write_effects_def, is_ext_call_op_def, all_effects_def,
              empty_effects_def] >>
  gvs[pred_setTheory.EXTENSION]
QED

(* When inst_a has empty write_effects and both return OK,
   both compositions return OK and commute_equiv holds.
   Strategy: inst_a only writes output vars (state_equiv), so inst_b sees
   the same inputs on v_a as on s. For inst_a on v_b: inst_a has empty
   write_effects so is not ext_call; use ok_transfer with operand/context
   preservation from effects_independent. Both results are state_equiv
   to v_b, giving commute_equiv via commute_equiv_from_state_equivs. *)
Theorem ok_ok_case_a[local]:
  !fuel ctx inst_a inst_b s v_a v_b.
    step_inst fuel ctx inst_a s = OK v_a /\
    step_inst fuel ctx inst_b s = OK v_b /\
    write_effects inst_a.inst_opcode = {} /\
    effects_independent inst_a.inst_opcode inst_b.inst_opcode /\
    DISJOINT (set (inst_defs inst_a)) (set (inst_uses inst_b)) /\
    DISJOINT (set (inst_defs inst_b)) (set (inst_uses inst_a)) /\
    DISJOINT (set (inst_defs inst_a)) (set (inst_defs inst_b)) /\
    inst_a.inst_opcode <> INVOKE /\
    ~is_terminator inst_a.inst_opcode /\
    ~is_terminator inst_b.inst_opcode /\
    ~is_alloca_op inst_a.inst_opcode /\
    ~is_alloca_op inst_b.inst_opcode ==>
    ?s_ab s_ba.
      step_inst fuel ctx inst_b v_a = OK s_ab /\
      step_inst fuel ctx inst_a v_b = OK s_ba /\
      commute_equiv
        (set (inst_defs inst_a) UNION set (inst_defs inst_b)) s_ab s_ba
Proof
  rpt strip_tac >>
  (* Step 1: inst_b on v_a returns OK via cross_case_result_equiv *)
  `result_equiv (set inst_a.inst_outputs)
     (step_inst fuel ctx inst_b s) (step_inst fuel ctx inst_b v_a)` by (
    irule cross_case_result_equiv >> metis_tac[]) >>
  gvs[] >>
  Cases_on `step_inst fuel ctx inst_b v_a` >>
  gvs[result_equiv_def] >>
  (* We have: state_equiv (set inst_a.inst_outputs) v_b v
     where v = step_inst inst_b v_a *)
  `~is_ext_call_op inst_a.inst_opcode` by
    metis_tac[empty_write_not_ext_call] >>
  `step_inst_base inst_a s = OK v_a` by gvs[step_inst_non_invoke] >>
  (* operand agreement: inst_b preserves inst_a's operand vars *)
  `!x. MEM x (inst_uses inst_a) ==> lookup_var x v_b = lookup_var x s` by (
    rpt strip_tac >>
    `~MEM x inst_b.inst_outputs` by (
      gvs[inst_defs_def] >>
      metis_tac[pred_setTheory.IN_DISJOINT]) >>
    metis_tac[step_preserves_non_output_vars]) >>
  `v_b.vs_labels = s.vs_labels` by
    metis_tac[step_preserves_labels] >>
  `!op. MEM op inst_a.inst_operands ==>
        eval_operand op s = eval_operand op v_b` by (
    rpt strip_tac >>
    Cases_on `op` >> gvs[eval_operand_def] >>
    `MEM s' (inst_uses inst_a)` by
      (gvs[inst_uses_def] >> irule mem_var_operand_vars >> gvs[]) >>
    res_tac >> gvs[]) >>
  (* context field preservation *)
  `v_b.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[step_preserves_control_flow] >>
  `v_b.vs_params = s.vs_params` by
    metis_tac[step_preserves_params] >>
  `inst_a.inst_opcode = RETURNDATACOPY ==>
   s.vs_returndata = v_b.vs_returndata` by (
    strip_tac >> gvs[] >>
    `Eff_RETURNDATA NOTIN write_effects inst_b.inst_opcode` by (
      `Eff_RETURNDATA IN read_effects RETURNDATACOPY` by EVAL_TAC >>
      gvs[effects_independent_def] >>
      metis_tac[pred_setTheory.IN_DISJOINT, pred_setTheory.IN_UNION]) >>
    irule (GSYM write_effects_sound_returndata) >> metis_tac[]) >>
  `?s_ba. step_inst_base inst_a v_b = OK s_ba` by (
    irule step_inst_base_ok_transfer >>
    rpt conj_tac >> gvs[] >>
    qexistsl_tac [`s`, `v_a`] >>
    gvs[] >> rpt strip_tac >> res_tac >> gvs[]) >>
  `step_inst fuel ctx inst_a v_b = OK s_ba` by gvs[step_inst_non_invoke] >>
  qexists_tac `s_ba` >> gvs[] >>
  `state_equiv (set inst_a.inst_outputs) v_b s_ba` by
    metis_tac[step_inst_ok_state_equiv] >>
  irule commute_equiv_from_state_equivs >>
  qexists_tac `v_b` >> qexists_tac `set inst_a.inst_outputs` >>
  gvs[inst_defs_def, pred_setTheory.SUBSET_UNION]
QED

(* Eff_MSIZE no longer exists (MSIZE→MEMTOP, upstream #4909).
   The *_implies_msize theorems are deleted because their conclusion
   references a non-existent effect. *)

(* sstore only modifies .storage sub-field of accounts *)
Theorem sstore_preserves_code[local]:
  !k v s addr.
    (lookup_account addr (sstore k v s).vs_accounts).code =
    (lookup_account addr s.vs_accounts).code
Proof
  simp[venomStateTheory.sstore_def, lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, LET_THM, COND_RAND, COND_RATOR]
QED

(* Eligible instructions preserve account codes.
   SSTORE only modifies the storage sub-field, not code.
   All other eligible ops that touch vs_accounts don't change code either. *)
Theorem step_inst_base_preserves_account_code[local]:
  !inst s s' addr.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    (lookup_account addr s'.vs_accounts).code =
    (lookup_account addr s.vs_accounts).code
Proof
  rpt strip_tac >>
  Cases_on `Eff_STORAGE IN write_effects inst.inst_opcode`
  >- (
    (* SSTORE case: only eligible op with Eff_STORAGE IN write *)
    `inst.inst_opcode = SSTORE` by (
      Cases_on `inst.inst_opcode` >>
      gvs[write_effects_def, is_terminator_def, is_alloca_op_def,
          is_ext_call_op_def, all_effects_def, empty_effects_def] >>
      gvs[pred_setTheory.EXTENSION]) >>
    gvs[step_inst_base_def, AllCaseEqs(), exec_write2_def] >>
    gvs[AllCaseEqs()] >>
    metis_tac[sstore_preserves_code])
  >- (
    (* Non-SSTORE: accounts fully preserved *)
    `Eff_BALANCE NOTIN write_effects inst.inst_opcode` by
      metis_tac[eligible_no_write_balance_extcode] >>
    `s'.vs_accounts = s.vs_accounts` by
      metis_tac[step_base_preserves_tracked] >>
    gvs[])
QED

(* EXTCODECOPY produces the same memory when operands agree, code agrees,
   and current memory agrees. Used for EXTCODECOPY×SSTORE case. *)
Theorem extcodecopy_memory_determined[local]:
  !inst s1 s2 v1 v2.
    inst.inst_opcode = EXTCODECOPY /\
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!addr. (lookup_account addr s1.vs_accounts).code =
            (lookup_account addr s2.vs_accounts).code) /\
    s1.vs_memory = s2.vs_memory ==>
    v1.vs_memory = v2.vs_memory
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s1 = OK v1` mp_tac >>
  qpat_x_assum `step_inst_base inst s2 = OK v2` mp_tac >>
  PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  strip_tac >> strip_tac >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `eval_operand h s1` >> gvs[] >>
  Cases_on `eval_operand h' s1` >> gvs[] >>
  Cases_on `eval_operand h'' s1` >> gvs[] >>
  Cases_on `eval_operand h''' s1` >> gvs[] >>
  gvs[write_memory_with_expansion_def, LET_THM]
QED

(* --- odc_tac: prove v1.F = s21.F when inst writes field F ---
   Uses step_inst_base_output_determined_fields directly.
   conj_n selects which conclusion conjunct to extract (1-6):
     1=memory, 2=transient, 3=accounts, 4=immutables, 5=returndata, 6=logs
   After discharging preconditions, extracts ONE conjunct via disch_then/cj,
   discharges its 2-3 sub-preconditions, then adds ONE bare equality.
   NEVER dumps the full 6-conjunct conditional into assumptions.
*)
(* odc_conj_tac: discharge a single precondition of output_determined_fields.
   Handles 3 kinds:
   1. Direct assumptions (step_inst_base, negations, operand agreement)
   2. Reversed equalities (s.field = v.field when v.field = s.field in asm)
   3. Read-effect conditionals (Eff_X IN read ==> s.F = v.F)
      - If field equality in asm: consequent holds
      - If Eff_X NOTIN read (e.g. EXTCODE via eligible_writer_no_read_extcode):
        antecedent false, contradiction
      - If Eff_X IN read: res_tac derives NOTIN write, then use preserves_all
   NEVER uses gvs[] — that hangs with 50+ assumptions. *)
val eq_tac =
  first_assum ACCEPT_TAC ORELSE
  first_assum (ACCEPT_TAC o GSYM);

(* odc_conj_tac: discharge one precondition of output_determined_fields.
   Four strategies, tried in order:
   1. eq_tac: direct/reversed equality in assumptions (group A via bulk_a)
   2. strip_tac >> eq_tac: conditional preconditions (PHI, PARAM, OFFSET)
   3. strip_tac >> first_assum CONTR_TAC: antecedent contradicts assumptions *)
(* derive_field_eq: derive s.FIELD = v.FIELD via step_inst_preserves_all.
   spa_n: conjunct number (14-18)
   For spa_n=17 (accounts): impl_tac is a conjunction, handle with conj_tac *)
fun derive_field_eq spa_n other_inst other_s other_s' =
  mp_tac (Q.SPECL [`fuel`, `ctx`, other_inst, other_s, other_s']
          (cj spa_n step_inst_preserves_all)) >>
  (impl_tac >- fast_conj) >>
  (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                (conj_tac >> first_assum ACCEPT_TAC))) >>
  disch_then (fn th => ACCEPT_TAC (GSYM th) ORELSE ACCEPT_TAC th);

(* Eligible write constraints: for non-term, non-alloca, non-ext-call, non-INVOKE:
   - BALANCE, EXTCODE, RETURNDATA never written
   - IMMUTABLES write implies MEMORY write (only ISTORE writes IMMUTABLES)
   - LOG write implies MEMORY read (LOG reads memory for data) *)
Theorem eligible_write_constraints[local]:
  !op. ~is_terminator op /\ ~is_alloca_op op /\
       ~is_ext_call_op op /\ op <> INVOKE ==>
       Eff_BALANCE NOTIN write_effects op /\
       Eff_EXTCODE NOTIN write_effects op /\
       Eff_RETURNDATA NOTIN write_effects op /\
       (Eff_IMMUTABLES IN write_effects op ==> Eff_MEMORY IN write_effects op) /\
       (Eff_LOG IN write_effects op ==> Eff_MEMORY IN read_effects op)
Proof
  Cases >> EVAL_TAC
QED

(* Non-EXTCODECOPY eligible writers don't read EXTCODE. *)
Theorem eligible_writer_no_read_extcode[local]:
  !op. write_effects op <> {} /\
       ~is_terminator op /\ ~is_alloca_op op /\
       ~is_ext_call_op op /\ op <> INVOKE /\ op <> EXTCODECOPY ==>
       Eff_EXTCODE NOTIN read_effects op
Proof
  Cases >> EVAL_TAC
QED

(* For an eligible writer of a non-EXTCODECOPY effect:
   the writer can't be EXTCODECOPY, has non-empty write, and doesn't read EXTCODE.
   This eliminates the 3-step EXTCODECOPY check in each field proof. *)
Theorem non_extcodecopy_writer[local]:
  !op eff. eff IN write_effects op /\
           eff NOTIN write_effects EXTCODECOPY /\
           ~is_terminator op /\ ~is_alloca_op op /\
           ~is_ext_call_op op /\ op <> INVOKE ==>
           op <> EXTCODECOPY /\
           write_effects op <> {} /\
           Eff_EXTCODE NOTIN read_effects op
Proof
  Cases >> simp[write_effects_def, read_effects_def, is_terminator_def,
                is_alloca_op_def, is_ext_call_op_def,
                empty_effects_def, all_effects_def] >>
  metis_tac[]
QED

(* Eligible writers never read BALANCE, STORAGE, or TRANSIENT.
   Enables CONTR_TAC for ODF read-effect preconditions. *)
Theorem eligible_writer_no_read_bst[local]:
  !op. ~is_terminator op /\ ~is_alloca_op op /\ ~is_ext_call_op op /\
       op <> INVOKE /\ write_effects op <> {} ==>
       Eff_BALANCE NOTIN read_effects op /\
       Eff_STORAGE NOTIN read_effects op /\
       Eff_TRANSIENT NOTIN read_effects op
Proof
  Cases >> EVAL_TAC
QED

(* Per-effect NOTIN write EXTCODECOPY facts (precomputed for field_commute_tac). *)
val extcodecopy_write_excl = prove(
  ``Eff_TRANSIENT NOTIN write_effects EXTCODECOPY /\
    Eff_STORAGE NOTIN write_effects EXTCODECOPY /\
    Eff_IMMUTABLES NOTIN write_effects EXTCODECOPY /\
    Eff_LOG NOTIN write_effects EXTCODECOPY``,
  EVAL_TAC);

(* odf_preconds_tac: discharge ALL 23 preconditions of
   step_inst_base_output_determined_fields in one shot.
   REQUIRES in assumptions:
   - step_inst_base facts, flags (~is_terminator etc)
   - operand agreement, group A equalities (from bulk_a)
   - read/write disjointness (forall e. e IN read ==> e NOTIN write)
   - eligible write constraints for the other inst
   other_inst/other_s/other_s': the OTHER instruction for field derivation *)
fun odf_preconds_tac other_inst other_s other_s' =
  rpt conj_tac >> (
    eq_tac ORELSE
    (strip_tac >> eq_tac) ORELSE
    (strip_tac >> first_assum CONTR_TAC) ORELSE
    (strip_tac >> res_tac >>
     FIRST (List.map (fn n => derive_field_eq n other_inst other_s other_s')
            [13,14,15,16,17,18])));

(* odf_close_tac: discharge sub-preconditions of a single ODF conjunct.
   For conjuncts needing memory equality (4,5,6), the caller must
   pre-establish Eff_MEMORY NOTIN write_effects other_inst. *)
fun odf_close_tac other_inst other_s other_s' =
  rpt conj_tac >> (
    eq_tac ORELSE
    (DISJ1_TAC >> first_assum ACCEPT_TAC) ORELSE
    (DISJ2_TAC >> first_assum ACCEPT_TAC) ORELSE
    (res_tac >>
     FIRST (List.map (fn n => derive_field_eq n other_inst other_s other_s')
            [13,14,15,16,17,18])));

(* odc_tac: prove v1.F = s21.F when inst writes field F.
   Uses step_inst_base_output_determined_fields directly.
   conj_n: 1=memory 2=transient 3=accounts 4=immutables 5=returndata 6=logs *)
fun odc_tac conj_n inst_q s_q v_q vr_q vcr_q other_inst =
  mp_tac (Q.SPECL [inst_q, s_q, v_q, vr_q, vcr_q]
          step_inst_base_output_determined_fields) >>
  (impl_tac >- odf_preconds_tac other_inst s_q v_q) >>
  disch_then (fn th => mp_tac (cj conj_n th)) >>
  (impl_tac >- odf_close_tac other_inst s_q v_q) >>
  strip_tac;


(* bulk_a: establish group A (1-11) field preservation facts for inst on s→s'.
   Unconditional — always succeed. Adds 11 assumptions of the form s'.field = s.field.
   Required by odc_conj_tac to discharge context field preconditions of odf. *)
fun bulk_a inst_q s_q s'_q =
  EVERY (List.map (fn n => spa_assume_a n inst_q s_q s'_q)
         [1,2,3,4,5,6,7,8,9,10,11,12]);

(* bulk_b: establish group B (12-17) field preservation facts for inst on s→s'.
   Conditional on Eff_X NOTIN write_effects. TRY each — if the effect IS in write,
   the fact can't be established, and we skip it. *)
fun bulk_b inst_q s_q s'_q =
  EVERY (List.map (fn n => TRY (spa_assume n inst_q s_q s'_q))
         [13,14,15,16,17,18]);

(* bulk_all: establish all 17 field preservation facts for inst on s→s'. *)
fun bulk_all inst_q s_q s'_q =
  bulk_a inst_q s_q s'_q >> bulk_b inst_q s_q s'_q;


(* ===================================================================== *)
(* field_commute_tac: prove s12.F = s21.F for one field.                 *)
(* ===================================================================== *)

(* field_nonmem_tac: 3-way case split for a non-memory field.
   Goal: s12.FIELD = s21.FIELD
   Assumes: w-w and r-w disjointness, eligible constraints, bulk_a,
            step_inst/step_inst_base facts, flag conditions all in assumptions.
   Parameters:
     spa_n    : conjunct of step_inst_preserves_all (14/16/17/18)
     odf_n    : conjunct of output_determined_fields (2/3/4/6)
     eff_q    : write-effect term to case-split on (HOL term)
     ecc_cj_n : conjunct number of extcodecopy_write_excl (1-4)
     pre1/pre2: extra setup before odc_tac for inst1/inst2 writer cases
                (e.g. deriving Eff_MEMORY NOTIN write for immutables/logs) *)
fun field_nonmem_tac spa_n odf_n eff_q ecc_cj_n pre1 pre2 =
  let val not_ecc_thm = cj ecc_cj_n extcodecopy_write_excl in
  Cases_on `^eff_q IN write_effects inst1.inst_opcode`
  >- ( (* inst1 writes this field *)
    `^eff_q NOTIN write_effects inst2.inst_opcode` by res_tac >>
    pre1 >>
    `inst1.inst_opcode <> EXTCODECOPY /\
     write_effects inst1.inst_opcode <> {} /\
     Eff_EXTCODE NOTIN read_effects inst1.inst_opcode` by
      metis_tac[non_extcodecopy_writer, not_ecc_thm] >>
    imp_res_tac eligible_writer_no_read_bst >>
    odc_tac odf_n `inst1` `s` `v2` `v1` `s21` `inst2` >>
    metis_tac[cj spa_n step_inst_preserves_all])
  >> Cases_on `^eff_q IN write_effects inst2.inst_opcode`
  >- ( (* inst2 writes this field *)
    `^eff_q NOTIN write_effects inst1.inst_opcode` by res_tac >>
    pre2 >>
    `inst2.inst_opcode <> EXTCODECOPY /\
     write_effects inst2.inst_opcode <> {} /\
     Eff_EXTCODE NOTIN read_effects inst2.inst_opcode` by
      metis_tac[non_extcodecopy_writer, not_ecc_thm] >>
    imp_res_tac eligible_writer_no_read_bst >>
    odc_tac odf_n `inst2` `s` `v1` `v2` `s12` `inst1` >>
    metis_tac[cj spa_n step_inst_preserves_all])
  >> (* neither writes this field *)
    metis_tac[cj spa_n step_inst_preserves_all]
  end;

(* memory_ecc_tac: EXTCODECOPY path for memory writer.
   Uses extcodecopy_memory_determined + step_inst_base_preserves_account_code.
   All params are Q.tmquote (term frag list). *)
fun memory_ecc_tac writer_q other_q s_q v_other_q v_writer_q s_cross_q =
  mp_tac (Q.SPECL [writer_q, s_q, v_other_q, v_writer_q, s_cross_q]
          extcodecopy_memory_determined) >>
  impl_tac >- (
    rpt conj_tac >> (
      eq_tac ORELSE
      (* Precondition 5: account code preserved by the other instruction *)
      (gen_tac >>
       mp_tac (Q.SPECL [other_q, s_q, v_other_q, `addr`]
               step_inst_base_preserves_account_code) >>
       (impl_tac >- fast_conj) >>
       disch_then (ACCEPT_TAC o GSYM)) ORELSE
      (* Precondition 6: memory preserved by the other instruction *)
      (mp_tac (Q.SPECL [`fuel`, `ctx`, other_q, s_q, v_other_q]
               (cj 13 step_inst_preserves_all)) >>
       (impl_tac >- fast_conj) >>
       (impl_tac >- first_assum ACCEPT_TAC) >>
       disch_then (ACCEPT_TAC o GSYM)))) >>
  strip_tac;

Theorem group_b_fields[local]:
  !fuel ctx inst1 inst2 s v1 v2 s12 s21.
    step_inst fuel ctx inst1 s = OK v1 /\
    step_inst fuel ctx inst2 s = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    step_inst_base inst1 s = OK v1 /\
    step_inst_base inst2 s = OK v2 /\
    step_inst_base inst2 v1 = OK s12 /\
    step_inst_base inst1 v2 = OK s21 /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    (!op. MEM op inst1.inst_operands ==>
          eval_operand op s = eval_operand op v2) /\
    (!op. MEM op inst2.inst_operands ==>
          eval_operand op s = eval_operand op v1) /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\ inst2.inst_opcode <> INVOKE ==>
    s12.vs_memory = s21.vs_memory /\
    s12.vs_transient = s21.vs_transient /\
    s12.vs_accounts = s21.vs_accounts /\
    s12.vs_immutables = s21.vs_immutables /\
    s12.vs_returndata = s21.vs_returndata /\
    s12.vs_logs = s21.vs_logs
Proof
  rpt strip_tac >>
  (* Phase 1: Establish disjointness from effects_independent *)
  `!e. e IN write_effects inst1.inst_opcode ==>
       e NOTIN write_effects inst2.inst_opcode` by (
    gvs[effects_independent_def] >>
    metis_tac[pred_setTheory.IN_DISJOINT]) >>
  `!e. e IN write_effects inst2.inst_opcode ==>
       e NOTIN write_effects inst1.inst_opcode` by (
    gvs[effects_independent_def] >>
    metis_tac[pred_setTheory.IN_DISJOINT]) >>
  `!e. e IN read_effects inst1.inst_opcode ==>
       e NOTIN write_effects inst2.inst_opcode` by (
    gvs[effects_independent_def] >>
    metis_tac[pred_setTheory.IN_DISJOINT, pred_setTheory.IN_UNION]) >>
  `!e. e IN read_effects inst2.inst_opcode ==>
       e NOTIN write_effects inst1.inst_opcode` by (
    gvs[effects_independent_def] >>
    metis_tac[pred_setTheory.IN_DISJOINT, pred_setTheory.IN_UNION]) >>
  (* Phase 1b: Eligible write constraints for both instructions *)
  `Eff_BALANCE NOTIN write_effects inst1.inst_opcode /\
   Eff_EXTCODE NOTIN write_effects inst1.inst_opcode /\
   Eff_RETURNDATA NOTIN write_effects inst1.inst_opcode /\
   (Eff_IMMUTABLES IN write_effects inst1.inst_opcode ==>
    Eff_MEMORY IN write_effects inst1.inst_opcode) /\
   (Eff_LOG IN write_effects inst1.inst_opcode ==>
    Eff_MEMORY IN read_effects inst1.inst_opcode)` by
    metis_tac[eligible_write_constraints] >>
  `Eff_BALANCE NOTIN write_effects inst2.inst_opcode /\
   Eff_EXTCODE NOTIN write_effects inst2.inst_opcode /\
   Eff_RETURNDATA NOTIN write_effects inst2.inst_opcode /\
   (Eff_IMMUTABLES IN write_effects inst2.inst_opcode ==>
    Eff_MEMORY IN write_effects inst2.inst_opcode) /\
   (Eff_LOG IN write_effects inst2.inst_opcode ==>
    Eff_MEMORY IN read_effects inst2.inst_opcode)` by
    metis_tac[eligible_write_constraints] >>
  (* Phase 2: Establish group A preservation for both instructions *)
  bulk_a `inst1` `s` `v1` >>
  bulk_a `inst2` `s` `v2` >>
  (* Phase 3: Per-field equality *)
  (* --- Memory: case split on Eff_MEMORY IN write, EXTCODECOPY sub-case --- *)
  `s12.vs_memory = s21.vs_memory` by (
    Cases_on `Eff_MEMORY IN write_effects inst1.inst_opcode`
    >- ( (* inst1 writes memory *)
      `Eff_MEMORY NOTIN write_effects inst2.inst_opcode` by res_tac >>
      Cases_on `inst1.inst_opcode = EXTCODECOPY`
      >- ( (* EXTCODECOPY path *)
        memory_ecc_tac `inst1` `inst2` `s` `v2` `v1` `s21` >>
        metis_tac[cj 13 step_inst_preserves_all])
      >> ( (* non-EXTCODECOPY *)
        `write_effects inst1.inst_opcode <> {} /\
         Eff_EXTCODE NOTIN read_effects inst1.inst_opcode` by
          metis_tac[eligible_writer_no_read_extcode,
                    pred_setTheory.MEMBER_NOT_EMPTY] >>
        imp_res_tac eligible_writer_no_read_bst >>
        `v2.vs_memory = s.vs_memory` by
          metis_tac[cj 13 step_inst_preserves_all] >>
        odc_tac 1 `inst1` `s` `v2` `v1` `s21` `inst2` >>
        metis_tac[cj 13 step_inst_preserves_all]))
    >> Cases_on `Eff_MEMORY IN write_effects inst2.inst_opcode`
    >- ( (* inst2 writes memory *)
      `Eff_MEMORY NOTIN write_effects inst1.inst_opcode` by res_tac >>
      Cases_on `inst2.inst_opcode = EXTCODECOPY`
      >- ( (* EXTCODECOPY path *)
        memory_ecc_tac `inst2` `inst1` `s` `v1` `v2` `s12` >>
        metis_tac[cj 13 step_inst_preserves_all])
      >> ( (* non-EXTCODECOPY *)
        `write_effects inst2.inst_opcode <> {} /\
         Eff_EXTCODE NOTIN read_effects inst2.inst_opcode` by
          metis_tac[eligible_writer_no_read_extcode,
                    pred_setTheory.MEMBER_NOT_EMPTY] >>
        imp_res_tac eligible_writer_no_read_bst >>
        `v1.vs_memory = s.vs_memory` by
          metis_tac[cj 13 step_inst_preserves_all] >>
        odc_tac 1 `inst2` `s` `v1` `v2` `s12` `inst1` >>
        metis_tac[cj 13 step_inst_preserves_all]))
    >> (* neither writes Eff_MEMORY *)
    metis_tac[cj 13 step_inst_preserves_all]) >>
  (* --- Transient: field_nonmem_tac 16 2 Eff_TRANSIENT ecc_cj 1 --- *)
  `s12.vs_transient = s21.vs_transient` by
    field_nonmem_tac 16 2 ``Eff_TRANSIENT`` 1 all_tac all_tac >>
  (* --- Accounts: only Eff_STORAGE matters (BALANCE/EXTCODE never written) --- *)
  `s12.vs_accounts = s21.vs_accounts` by
    field_nonmem_tac 17 3 ``Eff_STORAGE`` 2 all_tac all_tac >>
  (* --- Immutables: ODF conjunct 4 needs memory eq as sub-precond.
         eligible_write_constraints: IMMUTABLES write => MEMORY write.
         pre1/pre2 derive memory preservation by the OTHER instruction. --- *)
  `s12.vs_immutables = s21.vs_immutables` by
    field_nonmem_tac 14 4 ``Eff_IMMUTABLES`` 3
      (`Eff_MEMORY IN write_effects inst1.inst_opcode` by res_tac >>
       `Eff_MEMORY NOTIN write_effects inst2.inst_opcode` by res_tac >>
       `v2.vs_memory = s.vs_memory` by
         metis_tac[cj 13 step_inst_preserves_all])
      (`Eff_MEMORY IN write_effects inst2.inst_opcode` by res_tac >>
       `Eff_MEMORY NOTIN write_effects inst1.inst_opcode` by res_tac >>
       `v1.vs_memory = s.vs_memory` by
         metis_tac[cj 13 step_inst_preserves_all]) >>
  (* --- Returndata: never written --- *)
  `s12.vs_returndata = s21.vs_returndata` by
    metis_tac[cj 15 step_inst_preserves_all] >>
  (* --- Logs: ODF conjunct 6 needs memory eq as sub-precond.
         eligible_write_constraints: LOG write => MEMORY read.
         The writer reads MEMORY, so effects_independent means MEMORY not in
         write of the other instruction. --- *)
  `s12.vs_logs = s21.vs_logs` by
    field_nonmem_tac 18 6 ``Eff_LOG`` 4
      (`Eff_MEMORY IN read_effects inst1.inst_opcode` by metis_tac[] >>
       `Eff_MEMORY NOTIN write_effects inst2.inst_opcode` by res_tac >>
       `v2.vs_memory = s.vs_memory` by
         metis_tac[cj 13 step_inst_preserves_all])
      (`Eff_MEMORY IN read_effects inst2.inst_opcode` by metis_tac[] >>
       `Eff_MEMORY NOTIN write_effects inst1.inst_opcode` by res_tac >>
       `v1.vs_memory = s.vs_memory` by
         metis_tac[cj 13 step_inst_preserves_all])
QED

(* Frame/FMP commutation boundary for the four base executions in the
   general OK x OK case. *)
Theorem ok_ok_frame_fields[local]:
  !inst1 inst2 s v1 v2 s12 s21.
    step_inst_base inst1 s = OK v1 /\
    step_inst_base inst2 s = OK v2 /\
    step_inst_base inst2 v1 = OK s12 /\
    step_inst_base inst1 v2 = OK s21 /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\
    ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\
    ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\
    ~is_ext_call_op inst2.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    inst2.inst_opcode <> INVOKE /\
    (!op. MEM op inst2.inst_operands ==>
          eval_operand op s = eval_operand op v1) /\
    (!op. MEM op inst1.inst_operands ==>
          eval_operand op s = eval_operand op v2) ==>
    s12.vs_fmp = s21.vs_fmp /\
    s12.vs_call_entry_fmp = s21.vs_call_entry_fmp /\
    s12.vs_initial_fmp = s21.vs_initial_fmp /\
    s12.vs_return_pc_token = s21.vs_return_pc_token
Proof
  rpt strip_tac >>
  `v1.vs_call_entry_fmp = s.vs_call_entry_fmp /\
   v1.vs_initial_fmp = s.vs_initial_fmp /\
   v1.vs_return_pc_token = s.vs_return_pc_token` by
    metis_tac[step_inst_base_preserves_stable_frame_metadata] >>
  `v2.vs_call_entry_fmp = s.vs_call_entry_fmp /\
   v2.vs_initial_fmp = s.vs_initial_fmp /\
   v2.vs_return_pc_token = s.vs_return_pc_token` by
    metis_tac[step_inst_base_preserves_stable_frame_metadata] >>
  `s12.vs_call_entry_fmp = v1.vs_call_entry_fmp /\
   s12.vs_initial_fmp = v1.vs_initial_fmp /\
   s12.vs_return_pc_token = v1.vs_return_pc_token` by
    metis_tac[step_inst_base_preserves_stable_frame_metadata] >>
  `s21.vs_call_entry_fmp = v2.vs_call_entry_fmp /\
   s21.vs_initial_fmp = v2.vs_initial_fmp /\
   s21.vs_return_pc_token = v2.vs_return_pc_token` by
    metis_tac[step_inst_base_preserves_stable_frame_metadata] >>
  (Cases_on `Eff_FMP IN write_effects inst1.inst_opcode`
   >- (`Eff_FMP NOTIN write_effects inst2.inst_opcode` by
         (gvs[effects_independent_def] >>
          metis_tac[pred_setTheory.IN_DISJOINT, pred_setTheory.IN_UNION]) >>
       `v2.vs_fmp = s.vs_fmp` by
         metis_tac[step_inst_base_preserves_fmp_no_write] >>
       `s12.vs_fmp = v1.vs_fmp` by
         metis_tac[step_inst_base_preserves_fmp_no_write] >>
       `v1.vs_fmp = s21.vs_fmp` by
         metis_tac[step_inst_base_ordinary_fmp_agreement] >>
       metis_tac[])
   >- (Cases_on `Eff_FMP IN write_effects inst2.inst_opcode`
       >- (`Eff_FMP NOTIN write_effects inst1.inst_opcode` by
             (gvs[effects_independent_def] >>
              metis_tac[pred_setTheory.IN_DISJOINT,
                        pred_setTheory.IN_UNION]) >>
           `v1.vs_fmp = s.vs_fmp` by
             metis_tac[step_inst_base_preserves_fmp_no_write] >>
           `s21.vs_fmp = v2.vs_fmp` by
             metis_tac[step_inst_base_preserves_fmp_no_write] >>
           `v2.vs_fmp = s12.vs_fmp` by
             metis_tac[step_inst_base_ordinary_fmp_agreement] >>
           metis_tac[])
       >- (`v1.vs_fmp = s.vs_fmp` by
             metis_tac[step_inst_base_preserves_fmp_no_write] >>
           `v2.vs_fmp = s.vs_fmp` by
             metis_tac[step_inst_base_preserves_fmp_no_write] >>
           `s12.vs_fmp = v1.vs_fmp` by
             metis_tac[step_inst_base_preserves_fmp_no_write] >>
           `s21.vs_fmp = v2.vs_fmp` by
             metis_tac[step_inst_base_preserves_fmp_no_write] >>
           metis_tac[])))
QED

(* General OK×OK case: neither INVOKE nor ext_call.
   Both run, both produce OK on the other's output, commute_equiv holds. *)
Theorem ok_ok_case_general[local]:
  !fuel ctx inst1 inst2 s v1 v2.
    step_inst fuel ctx inst1 s = OK v1 /\
    step_inst fuel ctx inst2 s = OK v2 /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\ inst2.inst_opcode <> INVOKE ==>
    ?s12 s21.
      step_inst fuel ctx inst2 v1 = OK s12 /\
      step_inst fuel ctx inst1 v2 = OK s21 /\
      commute_equiv
        (set (inst_defs inst1) UNION set (inst_defs inst2)) s12 s21
Proof
  rpt strip_tac >>
  (* Convert to step_inst_base *)
  `step_inst_base inst1 s = OK v1` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst2 s = OK v2` by gvs[step_inst_non_invoke] >>
  (* Labels preserved by step *)
  `v1.vs_labels = s.vs_labels` by metis_tac[step_preserves_labels] >>
  `v2.vs_labels = s.vs_labels` by metis_tac[step_preserves_labels] >>
  (* Operand agreement: inst2 on v1 vs s *)
  `!op. MEM op inst2.inst_operands ==>
        eval_operand op s = eval_operand op v1` by (
    rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
    `MEM s' (inst_uses inst2)` by
      (gvs[inst_uses_def] >> irule mem_var_operand_vars >> gvs[]) >>
    `~MEM s' inst1.inst_outputs` by (
      gvs[inst_defs_def] >> metis_tac[pred_setTheory.IN_DISJOINT]) >>
    metis_tac[step_preserves_non_output_vars]) >>
  (* Operand agreement: inst1 on v2 vs s *)
  `!op. MEM op inst1.inst_operands ==>
        eval_operand op s = eval_operand op v2` by (
    rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
    `MEM s' (inst_uses inst1)` by
      (gvs[inst_uses_def] >> irule mem_var_operand_vars >> gvs[]) >>
    `~MEM s' inst2.inst_outputs` by (
      gvs[inst_defs_def] >> metis_tac[pred_setTheory.IN_DISJOINT]) >>
    metis_tac[step_preserves_non_output_vars]) >>
  (* Context field preservation *)
  `v1.vs_prev_bb = s.vs_prev_bb /\ v2.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[step_preserves_control_flow] >>
  `v1.vs_params = s.vs_params /\ v2.vs_params = s.vs_params` by
    metis_tac[step_preserves_params] >>
  (* Returndata agreement (needed for RETURNDATACOPY) *)
  `inst2.inst_opcode = RETURNDATACOPY ==>
   s.vs_returndata = v1.vs_returndata` by (
    strip_tac >>
    `Eff_RETURNDATA NOTIN write_effects inst1.inst_opcode` by (
      `Eff_RETURNDATA IN read_effects RETURNDATACOPY` by EVAL_TAC >>
      gvs[effects_independent_def] >>
      metis_tac[pred_setTheory.IN_DISJOINT, pred_setTheory.IN_UNION]) >>
    metis_tac[write_effects_sound_returndata]) >>
  `inst1.inst_opcode = RETURNDATACOPY ==>
   s.vs_returndata = v2.vs_returndata` by (
    strip_tac >>
    `Eff_RETURNDATA NOTIN write_effects inst2.inst_opcode` by (
      `Eff_RETURNDATA IN read_effects RETURNDATACOPY` by EVAL_TAC >>
      gvs[effects_independent_def] >>
      metis_tac[pred_setTheory.IN_DISJOINT, pred_setTheory.IN_UNION]) >>
    metis_tac[write_effects_sound_returndata]) >>
  (* ok_transfer: inst2 on v1 produces OK *)
  `?s12. step_inst_base inst2 v1 = OK s12` by (
    irule step_inst_base_ok_transfer >>
    rpt conj_tac >> gvs[] >>
    qexistsl_tac [`s`, `v2`] >>
    gvs[] >> rpt strip_tac >> res_tac >> gvs[]) >>
  (* ok_transfer: inst1 on v2 produces OK *)
  `?s21. step_inst_base inst1 v2 = OK s21` by (
    irule step_inst_base_ok_transfer >>
    rpt conj_tac >> gvs[] >>
    qexistsl_tac [`s`, `v1`] >>
    gvs[] >> rpt strip_tac >> res_tac >> gvs[]) >>
  `step_inst fuel ctx inst2 v1 = OK s12` by gvs[step_inst_non_invoke] >>
  `step_inst fuel ctx inst1 v2 = OK s21` by gvs[step_inst_non_invoke] >>
  qexistsl_tac [`s12`, `s21`] >> gvs[] >>
  (* === Now prove commute_equiv === *)
  (* Establish all group A field facts for all 4 step_inst directions.
     This gives s12.F = v1.F, v1.F = s.F, s21.F = v2.F, v2.F = s.F
     for each group A field F. Explicit instantiation avoids drule_all
     multi-match and simp[] performance issues with 50+ assumptions. *)
  bulk_a `inst1` `s` `v1` >>
  bulk_a `inst2` `s` `v2` >>
  bulk_a `inst2` `v1` `s12` >>
  bulk_a `inst1` `v2` `s21` >>
  (* Group C: lookup_var *)
  `!w. w NOTIN set (inst_defs inst1) /\ w NOTIN set (inst_defs inst2) ==>
       lookup_var w s12 = lookup_var w s21` by (
    rpt strip_tac >> fs[inst_defs_def] >>
    metis_tac[step_preserves_non_output_vars]) >>
  (* Group B: use group_b_fields helper *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`,
                    `v1`, `v2`, `s12`, `s21`] group_b_fields) >>
  (impl_tac >- fast_conj) >>
  strip_tac >>
  drule_all ok_ok_frame_fields >> strip_tac >>
  (* Close commute_equiv — all needed equalities are in assumptions.
     Each field is s12.F = X = ... = s21.F via transitivity of 2-4 equalities.
     metis_tac[] handles this since all equalities are in assumptions. *)
  rw[commute_equiv_def] >>
  rpt conj_tac >> (
    TRY (first_assum ACCEPT_TAC) >>
    TRY (first_assum (ACCEPT_TAC o GSYM)) >>
    TRY (metis_tac[]) >>
    (* lookup_var case *)
    rpt strip_tac >> first_x_assum irule >>
    rpt conj_tac >> first_assum ACCEPT_TAC)
QED

(* ===================================================================== *)
(* ===== effects_independent_commute =================================== *)
(* ===================================================================== *)

Theorem abort_compatible_sym[local]:
  !a b. abort_compatible a b <=> abort_compatible b a
Proof
  rw[abort_compatible_def] >> metis_tac[]
QED

(* If inst_a returns OK and inst_b aborts on s, then inst_b also aborts on
   the state after inst_a, with the same abort type. Both abort states have
   empty returndata. Works at step_inst level (not step_inst_base). *)
(* Rewrite step_inst to step_inst_base in all assumptions for non-INVOKE *)
val step_inst_to_base =
  imp_res_tac (REWRITE_RULE [GSYM AND_IMP_INTRO] step_inst_non_invoke) >>
  full_simp_tac std_ss [];

(* If both instructions abort on s (non-INVOKE, non-terminator), and they
   are abort_compatible, they have the same abort type and both set
   returndata to []. *)
Theorem abort_abort_commute[local]:
  !fuel ctx inst1 inst2 s a1 s1 a2 s2.
    step_inst fuel ctx inst1 s = Abort a1 s1 /\
    step_inst fuel ctx inst2 s = Abort a2 s2 /\
    inst1.inst_opcode <> INVOKE /\
    inst2.inst_opcode <> INVOKE /\
    ~is_terminator inst1.inst_opcode /\
    ~is_terminator inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode ==>
    a1 = a2 /\ s1.vs_returndata = s2.vs_returndata
Proof
  rpt strip_tac >> (
    step_inst_to_base >>
    imp_res_tac step_inst_base_abort_returndata >> simp[] >>
    imp_res_tac step_inst_base_abort_opcode >>
    imp_res_tac step_inst_base_abort_type >> gvs[] >>
    qpat_x_assum `abort_compatible _ _` mp_tac >> EVAL_TAC)
QED

(* Comprehensive case 4c: neither INVOKE nor ext_call.
   Handles ALL result pairs in one lemma — eliminates >- chains. *)
Theorem commute_base_case[local]:
  !fuel ctx inst1 inst2 s.
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\ inst2.inst_opcode <> INVOKE ==>
    let r1 = (case step_inst fuel ctx inst1 s of
                OK s1 => step_inst fuel ctx inst2 s1
              | other => other) in
    let r2 = (case step_inst fuel ctx inst2 s of
                OK s2 => step_inst fuel ctx inst1 s2
              | other => other) in
    let defs = set (inst_defs inst1) UNION set (inst_defs inst2) in
    case (r1, r2) of
      (OK s12, OK s21) => commute_equiv defs s12 s21
    | (Abort a1 s1, Abort a2 s2) =>
        a1 = a2 /\ s1.vs_returndata = s2.vs_returndata
    | (Halt s1, Halt s2) => s1.vs_returndata = s2.vs_returndata
    | (IntRet v1 _, IntRet v2 _) => v1 = v2
    | (Error _, _) => T
    | (_, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[] >>
  Cases_on `step_inst fuel ctx inst1 s` >> simp[]
  (* inst1=OK *)
  >- (
    Cases_on `step_inst fuel ctx inst2 s` >> simp[]
    (* OK×OK *)
    >- (
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`, `v`, `v'`]
              ok_ok_case_general) >>
      impl_tac >- simp[] >> strip_tac >> simp[])
    (* OK×Halt: impossible *)
    >- (imp_res_tac step_inst_no_halt >> gvs[])
    (* OK×Abort *)
    >- (drule_all cross_case_abort >> strip_tac >> simp[])
    (* OK×IntRet: impossible *)
    >- (imp_res_tac step_inst_no_intret >> gvs[])
    (* OK×Error *)
    >> (Cases_on `step_inst fuel ctx inst2 v` >> simp[]))
  (* inst1=Halt: impossible *)
  >- (imp_res_tac step_inst_no_halt >> gvs[])
  (* inst1=Abort *)
  >- (
    Cases_on `step_inst fuel ctx inst2 s` >> simp[]
    (* Abort×OK *)
    >- (
      `effects_independent inst2.inst_opcode inst1.inst_opcode` by
        metis_tac[effects_independent_sym] >>
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst2`, `inst1`, `s`, `v'`, `a`, `v`]
              cross_case_abort) >>
      impl_tac >- simp[] >>
      strip_tac >> simp[])
    (* Abort×Halt: impossible *)
    >- (imp_res_tac step_inst_no_halt >> gvs[])
    (* Abort×Abort *)
    >- (drule_all abort_abort_commute >> simp[])
    (* Abort×IntRet: impossible *)
    >- (imp_res_tac step_inst_no_intret >> gvs[])
    (* Abort×Error *)
    >> (Cases_on `step_inst fuel ctx inst1 v` >> simp[]))
  (* inst1=IntRet: impossible *)
  >- (imp_res_tac step_inst_no_intret >> gvs[])
  (* inst1=Error *)
  >> simp[]
QED

(* When inst1 has empty write_effects and is not INVOKE, the full commutation
   conclusion holds. inst2 can be anything (including INVOKE or ext_call).
   Covers all remaining cases not handled by commute_base_case. *)
Theorem commute_one_empty_write[local]:
  !fuel ctx inst1 inst2 s.
    write_effects inst1.inst_opcode = {} /\
    inst1.inst_opcode <> INVOKE /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\
    ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\
    ~is_alloca_op inst2.inst_opcode ==>
    let r1 = (case step_inst fuel ctx inst1 s of
                OK s1 => step_inst fuel ctx inst2 s1
              | other => other) in
    let r2 = (case step_inst fuel ctx inst2 s of
                OK s2 => step_inst fuel ctx inst1 s2
              | other => other) in
    let defs = set (inst_defs inst1) UNION set (inst_defs inst2) in
    case (r1, r2) of
      (OK s12, OK s21) => commute_equiv defs s12 s21
    | (Abort a1 s1, Abort a2 s2) =>
        a1 = a2 /\ s1.vs_returndata = s2.vs_returndata
    | (Halt s1, Halt s2) => s1.vs_returndata = s2.vs_returndata
    | (IntRet v1 _, IntRet v2 _) => v1 = v2
    | (Error _, _) => T
    | (_, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[] >>
  (* inst1 results: OK, Abort, Error (not Halt since ≠INVOKE, not IntRet) *)
  Cases_on `step_inst fuel ctx inst1 s` >> simp[]
  (* inst1=OK *)
  >- (
    Cases_on `step_inst fuel ctx inst2 s` >> simp[]
    (* OK×OK *)
    >- (
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`, `v`, `v'`]
              ok_ok_case_a) >>
      impl_tac >- simp[] >> strip_tac >> simp[])
    (* OK×Halt *)
    >- (
      `result_equiv (set inst1.inst_outputs)
         (step_inst fuel ctx inst2 s) (step_inst fuel ctx inst2 v)` by (
        irule cross_case_result_equiv >> metis_tac[]) >>
      simp[] >> Cases_on `step_inst fuel ctx inst2 v` >>
      gvs[result_equiv_def, execution_equiv_def, revert_equiv_def])
    (* OK×Abort: use cross_case_result_equiv (works for INVOKE too) *)
    >- (
      `result_equiv (set inst1.inst_outputs)
         (step_inst fuel ctx inst2 s) (step_inst fuel ctx inst2 v)` by (
        irule cross_case_result_equiv >> metis_tac[]) >>
      simp[] >> Cases_on `step_inst fuel ctx inst2 v` >>
      gvs[result_equiv_def, execution_equiv_def, revert_equiv_def])
    (* OK×IntRet *)
    >- (imp_res_tac step_inst_no_intret >> gvs[])
    (* OK×Error *)
    >> (Cases_on `step_inst fuel ctx inst2 v` >> simp[]))
  (* inst1=Halt: impossible — inst1 ≠ INVOKE, ¬is_terminator *)
  >- (imp_res_tac step_inst_no_halt >> gvs[])
  (* inst1=Abort *)
  >- (
    `step_inst_base inst1 s = Abort a v` by gvs[step_inst_non_invoke] >>
    Cases_on `step_inst fuel ctx inst2 s` >> simp[]
    (* Abort×OK: cross_case_abort (reversed) *)
    >- (
      `effects_independent inst2.inst_opcode inst1.inst_opcode` by
        metis_tac[effects_independent_sym] >>
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst2`, `inst1`, `s`, `v'`, `a`, `v`]
              cross_case_abort) >>
      impl_tac >- (gvs[] >> metis_tac[pred_setTheory.DISJOINT_SYM]) >>
      strip_tac >> simp[])
    (* Abort×Halt: impossible — no_abort_with_invoke2 *)
    >- (
      imp_res_tac step_inst_no_halt >> gvs[] >>
      metis_tac[no_abort_with_invoke2])
    (* Abort×Abort: inst2 ≠ INVOKE (else no_abort_with_invoke2 contradicts) *)
    >- (
      `inst2.inst_opcode <> INVOKE` by (
        strip_tac >> gvs[] >> metis_tac[no_abort_with_invoke2]) >>
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`, `a`, `v`,
                        `a'`, `v'`] abort_abort_commute) >>
      simp[])
    (* Abort×IntRet *)
    >- (imp_res_tac step_inst_no_intret >> gvs[])
    (* Abort×Error *)
    >> simp[])
  (* inst1=IntRet: impossible *)
  >- (imp_res_tac step_inst_no_intret >> gvs[])
  (* inst1=Error *)
  >> simp[]
QED

(* Symmetric version: same conclusion but inst2 has empty write. *)
Theorem commute_one_empty_write_sym[local]:
  !fuel ctx inst1 inst2 s.
    write_effects inst2.inst_opcode = {} /\
    inst2.inst_opcode <> INVOKE /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\
    ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\
    ~is_alloca_op inst2.inst_opcode ==>
    let r1 = (case step_inst fuel ctx inst1 s of
                OK s1 => step_inst fuel ctx inst2 s1
              | other => other) in
    let r2 = (case step_inst fuel ctx inst2 s of
                OK s2 => step_inst fuel ctx inst1 s2
              | other => other) in
    let defs = set (inst_defs inst1) UNION set (inst_defs inst2) in
    case (r1, r2) of
      (OK s12, OK s21) => commute_equiv defs s12 s21
    | (Abort a1 s1, Abort a2 s2) =>
        a1 = a2 /\ s1.vs_returndata = s2.vs_returndata
    | (Halt s1, Halt s2) => s1.vs_returndata = s2.vs_returndata
    | (IntRet v1 _, IntRet v2 _) => v1 = v2
    | (Error _, _) => T
    | (_, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[] >>
  (* Apply commute_one_empty_write with inst1↔inst2 swapped *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst2`, `inst1`, `s`]
          commute_one_empty_write) >>
  impl_tac >- (
    simp[] >> metis_tac[effects_independent_sym, abort_compatible_sym,
                        pred_setTheory.DISJOINT_SYM]) >>
  simp[] >>
  (* The swapped version has r1'=case inst2 then inst1, r2'=case inst1 then inst2
     which is our r2 and r1. Need to match (r1,r2) from (r2',r1'). *)
  Cases_on `step_inst fuel ctx inst1 s` >>
  Cases_on `step_inst fuel ctx inst2 s` >>
  simp[] >>
  TRY (Cases_on `step_inst fuel ctx inst1 v'` >> simp[] >> NO_TAC) >>
  TRY (Cases_on `step_inst fuel ctx inst2 v` >> simp[] >> NO_TAC) >>
  TRY (
    Cases_on `step_inst fuel ctx inst2 v` >>
    Cases_on `step_inst fuel ctx inst1 v'` >> simp[] >>
    rw[commute_equiv_def] >> metis_tac[pred_setTheory.UNION_COMM]) >>
  simp[]
QED

Theorem effects_independent_commute:
  !fuel ctx inst1 inst2 s.
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\
    ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\
    ~is_alloca_op inst2.inst_opcode ==>
    let r1 = (case step_inst fuel ctx inst1 s of
                OK s1 => step_inst fuel ctx inst2 s1
              | other => other) in
    let r2 = (case step_inst fuel ctx inst2 s of
                OK s2 => step_inst fuel ctx inst1 s2
              | other => other) in
    let defs = set (inst_defs inst1) UNION set (inst_defs inst2) in
    case (r1, r2) of
      (OK s12, OK s21) => commute_equiv defs s12 s21
    | (Abort a1 s1, Abort a2 s2) =>
        a1 = a2 /\ s1.vs_returndata = s2.vs_returndata
    | (Halt s1, Halt s2) => s1.vs_returndata = s2.vs_returndata
    | (IntRet v1 _, IntRet v2 _) => v1 = v2
    | (Error _, _) => T
    | (_, Error _) => T
    | _ => F
Proof
  rpt strip_tac >> simp[] >>
  Cases_on `inst1.inst_opcode = INVOKE` >>
  Cases_on `inst2.inst_opcode = INVOKE`
  >- ( (* Both INVOKE: effects_independent INVOKE INVOKE = F *)
    `effects_independent INVOKE INVOKE` by gvs[] >>
    pop_assum mp_tac >> EVAL_TAC)
  >- ( (* inst1=INVOKE, inst2≠INVOKE *)
    `write_effects inst2.inst_opcode = {}` by
      metis_tac[effects_independent_invoke_empty] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`]
            commute_one_empty_write_sym) >>
    simp[])
  >- ( (* inst1≠INVOKE, inst2=INVOKE *)
    `write_effects inst1.inst_opcode = {}` by
      metis_tac[effects_independent_sym, effects_independent_invoke_empty] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`]
            commute_one_empty_write) >>
    simp[])
  >> ( (* Neither INVOKE *)
    Cases_on `is_ext_call_op inst1.inst_opcode`
    >- ( (* inst1=ext_call *)
      `write_effects inst2.inst_opcode = {}` by
        metis_tac[effects_independent_ext_call_empty] >>
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`]
              commute_one_empty_write_sym) >>
      simp[])
    >> Cases_on `is_ext_call_op inst2.inst_opcode`
    >- ( (* inst2=ext_call *)
      `write_effects inst1.inst_opcode = {}` by
        metis_tac[effects_independent_sym, effects_independent_ext_call_empty] >>
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`]
              commute_one_empty_write) >>
      simp[])
    >> ( (* Neither INVOKE nor ext_call: use commute_base_case *)
      mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `s`]
              commute_base_case) >>
      simp[]))
QED

val _ = export_theory();
