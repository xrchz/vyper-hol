(*
 * Remove Unused Variables — Proofs
 *
 * Proof strategy:
 *   1. Per-instruction: effect-free instruction only modifies vs_vars at
 *      outputs. step_effect_free_state_equiv gives state_equiv (set outputs).
 *      NOP is identity (step_nop_identity). So orig and NOP'd differ only
 *      on outputs.
 *
 *   2. Block-level: induction over instruction index. At each step:
 *      - Kept instruction: same code, operands don't read dead vars
 *        (liveness soundness) → step_inst_result_equiv_full preserves
 *        state_equiv
 *      - NOP'd instruction: step_effect_free_state_equiv on original,
 *        step_nop_identity on NOP'd → accumulate dead outputs
 *
 *   3. Function-level: block_sim_function framework. Operand condition
 *      holds because eliminated vars are globally dead — no instruction
 *      anywhere in the function reads them (liveness is global).
 *      Composed with clear_nops_function_correct.
 *
 *   4. OWHILE iteration: each pass strictly decreases instruction count
 *      (or is fixpoint). Compose single-pass results.
 *
 * Preconditions:
 * - wf_function fn — for liveness soundness
 * - fn_inst_wf fn — for step_inst well-formedness
 * - venom_wf ctx — for step_inst semantics
 * - no ALLOCA instructions — ALLOCA modifies vs_allocas (side effect
 *   not tracked by state_equiv). This is the only removable opcode
 *   that is not effect-free.
 *)

Theory removeUnusedProofs
Ancestors
  removeUnusedDefs passSimulationProps analysisSimProps venomInstProps venomWf
  opcodeClass execEquivProps livenessProofs passSharedDefs passSharedProps venomInst
  stateEquiv stateEquivProofs venomExecProofs venomExecProps
  venomState venomExecSemantics indexedLists cfgTransform cfgAnalysisProps pointerConfinedDefs
Libs
  pairLib

(* ===== Per-instruction: effect-free removable → state_equiv ===== *)

(* Every removable opcode outside the pass-owned must-preserve boundary is
   effect-free (pure computation, state reads, or SSA bookkeeping). *)
Theorem removable_not_preserved_effect_free[local]:
  !inst. is_removable inst /\
         ~remove_unused_must_preserve_op inst.inst_opcode ==>
         is_effect_free_op inst.inst_opcode
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_removable_def, remove_unused_must_preserve_op_def,
      is_volatile_def, is_terminator_def, is_effect_free_op_def]
QED

(* Per-instruction NOP correctness: if an effect-free instruction
   steps to OK s', then s and s' agree on everything except outputs. *)
Theorem nop_removable_state_equiv:
  !fuel ctx inst s s'.
    is_effect_free_op inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  metis_tac[step_effect_free_state_equiv]
QED

(* ===== state_equiv helpers for INVOKE handling ===== *)

(* FOLDL update_var preserves state_equiv *)
Theorem foldl_update_var_state_equiv:
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
      lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* eval_operands on state_equiv states with operand vars outside vars *)
Theorem eval_operands_state_equiv:
  !ops s1 s2 vars.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> rw[eval_operands_def] >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> gvs[] >> metis_tac[]) >>
  `eval_operand h s1 = eval_operand h s2` by
    (irule eval_operand_equiv >> qexists_tac `vars` >> simp[] >>
     metis_tac[]) >>
  gvs[]
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

Theorem execution_equiv_refl[local]:
  !vars s. execution_equiv vars s s
Proof
  rw[execution_equiv_def]
QED

(* step_inst result_equiv for ALL non-terminator instructions including INVOKE.
   Extends the base step_inst_result_equiv which only covers step_inst_base. *)
Theorem step_inst_result_equiv_full:
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
    `state_equiv vars (adopt_return_fmp i (merge_callee_state s1 v))
                      (adopt_return_fmp i (merge_callee_state s2 v))` by
      (Cases_on `i.iret_adopt_fmp` >>
       gvs[adopt_return_fmp_def, state_equiv_def, execution_equiv_def,
           lookup_var_def]) >>
    simp[bind_outputs_def] >>
    IF_CASES_TAC >> gvs[result_equiv_def] >>
    irule foldl_update_var_state_equiv >> gvs[])
  >> (irule step_inst_result_equiv >> gvs[])
QED

(* ===== state_equiv composition for NOP'd instruction case ===== *)

(* When s1≈s2 on vars, and s1≈s1' on outs where outs⊆vars,
   then s1'≈s2 on vars. Used when NOP'ing: s1' is original post-state
   (only outputs changed), s2 is NOP'd post-state (unchanged). *)
Theorem state_equiv_effect_free_compose:
  !vars outs s1 s1' s2.
    state_equiv vars s1 s2 /\
    state_equiv outs s1 s1' /\
    outs SUBSET vars ==>
    state_equiv vars s1' s2
Proof
  rpt strip_tac >>
  `state_equiv vars s1 s1'` by metis_tac[state_equiv_subset] >>
  `state_equiv vars s1' s1` by metis_tac[state_equiv_sym] >>
  metis_tac[state_equiv_trans]
QED

(* When s1≈s2 on V, and s1≈s1' on W (e.g. effect-free step outputs),
   then s1'≈s2 on V∪W. For any x ∉ V∪W: x ∉ V so s1(x)=s2(x), and
   x ∉ W so s1(x)=s1'(x), hence s1'(x)=s2(x). *)
Theorem state_equiv_union_compose:
  !V W s1 s1' s2.
    state_equiv V s1 s2 /\
    state_equiv W s1 s1' ==>
    state_equiv (V UNION W) s1' s2
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  metis_tac[lookup_var_def]
QED

(* ===== Block-level ===== *)

(* Outputs NOP'd by remove_unused_block *)
Definition block_nop_outputs_def:
  block_nop_outputs lr bb =
    set (FLAT (MAPi (\idx inst.
      let live = live_after_at lr bb.bb_label idx
                   (LENGTH bb.bb_instructions) in
      if ~remove_unused_must_preserve_op inst.inst_opcode /\
         is_removable inst /\
         EVERY (\v. ~MEM v live) inst.inst_outputs
      then inst.inst_outputs
      else [])
      bb.bb_instructions))
End

(* Helper: get_instruction on transformed block *)
Theorem get_instruction_remove_unused:
  !lr bb idx.
    get_instruction (remove_unused_block lr bb) idx =
    if idx < LENGTH bb.bb_instructions then
      SOME (remove_unused_inst
              (live_after_at lr bb.bb_label idx
                (LENGTH bb.bb_instructions))
              (EL idx bb.bb_instructions))
    else NONE
Proof
  rw[get_instruction_def, remove_unused_block_def, LENGTH_MAPi] >>
  simp[EL_MAPi]
QED

(* Helper: NOP'd instruction outputs are in block_nop_outputs *)
Theorem nop_outputs_in_block_nop_outputs[local]:
  !lr bb idx inst.
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    remove_unused_inst
      (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions))
      inst = mk_nop_inst inst ==>
    set inst.inst_outputs SUBSET block_nop_outputs lr bb
Proof
  rpt strip_tac >>
  simp[block_nop_outputs_def, pred_setTheory.SUBSET_DEF,
       listTheory.MEM_FLAT, MEM_MAPi] >>
  rpt strip_tac >>
  qexists_tac `inst.inst_outputs` >> simp[] >>
  qexists_tac `idx` >> simp[] >>
  gvs[remove_unused_inst_def, mk_nop_inst_def] >>
  rpt (pop_assum mp_tac) >>
  rpt IF_CASES_TAC >> simp[instruction_component_equality] >> gvs[]
QED

(* Helper: remove_unused_inst either returns inst or mk_nop_inst inst *)
Theorem remove_unused_inst_cases:
  !live inst.
    remove_unused_inst live inst = inst \/
    remove_unused_inst live inst = mk_nop_inst inst
Proof
  rw[remove_unused_inst_def] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Triviality remove_unused_nop_outputs_subset:
  !lr fence bb V idx.
    block_nop_outputs lr bb SUBSET V /\
    idx < LENGTH bb.bb_instructions /\
    remove_unused_inst
      (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions))
      (EL idx bb.bb_instructions) =
      mk_nop_inst (EL idx bb.bb_instructions) ==>
    set (EL idx bb.bb_instructions).inst_outputs SUBSET V
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`lr`, `bb`, `idx`,
    `EL idx bb.bb_instructions`] nop_outputs_in_block_nop_outputs) >>
  impl_tac >- simp[] >>
  strip_tac >>
  metis_tac[pred_setTheory.SUBSET_TRANS]
QED

Triviality state_equiv_update_var_left_in_vars:
  !vars x v s1 s2.
    x IN vars /\ state_equiv vars s1 s2 ==>
    state_equiv vars (update_var x v s1) s2
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def, lookup_var_def,
     finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[]
QED

Triviality resolve_phi_MEM:
  !prev ops op. resolve_phi prev ops = SOME op ==> MEM op ops
Proof
  recInduct resolve_phi_ind >> rw[resolve_phi_def] >> metis_tac[]
QED

Triviality eval_one_phi_state_equiv:
  !vars s1 s2 inst out v.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    eval_one_phi s1 inst = SOME (out,v) ==>
    eval_one_phi s2 inst = SOME (out,v)
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def, AllCaseEqs()] >>
  rename1 `resolve_phi prev inst.inst_operands = SOME op` >>
  `MEM op inst.inst_operands` by metis_tac[resolve_phi_MEM] >>
  sg `eval_operand op s1 = eval_operand op s2`
  >- (irule stateEquivProofsTheory.eval_operand_equiv >>
      qexists_tac `vars` >> simp[] >> Cases_on `op` >> gvs[]) >>
  gvs[state_equiv_def] >> metis_tac[]
QED

(* NOP'd instruction is effect-free: either it was already NOP,
   or it was removable and not ALLOCA. *)
Theorem remove_unused_inst_nop_effect_free:
  !live inst.
    remove_unused_inst live inst = mk_nop_inst inst ==>
    is_effect_free_op inst.inst_opcode
Proof
  rw[remove_unused_inst_def] >>
  rpt (pop_assum mp_tac) >>
  rpt IF_CASES_TAC >> gvs[mk_nop_inst_def,
    instruction_component_equality] >>
  gvs[is_removable_def, is_volatile_def]
  >- simp[is_effect_free_op_def]
  >- simp[is_effect_free_op_def]
  >- (rpt strip_tac >>
      irule removable_not_preserved_effect_free >>
      simp[is_removable_def, remove_unused_must_preserve_op_def])
QED

(* NOP'd instruction is not a terminator *)
Theorem remove_unused_inst_nop_not_terminator[local]:
  !live inst.
    remove_unused_inst live inst = mk_nop_inst inst ==>
    ~is_terminator inst.inst_opcode
Proof
  rw[remove_unused_inst_def] >>
  rpt (pop_assum mp_tac) >>
  rpt IF_CASES_TAC >> gvs[mk_nop_inst_def,
    instruction_component_equality, is_removable_def] >>
  simp[is_terminator_def]
QED

(* Helper: removable ⟹ not terminator *)
Theorem removable_not_terminator[local]:
  !inst. is_removable inst ==> ~is_terminator inst.inst_opcode
Proof
  rw[is_removable_def]
QED

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
  !inst s s'. step_inst_base inst s = Halt s' ==>
              is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  drule opcodeClassTheory.step_inst_base_halt_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

Theorem step_inst_base_no_intret[local]:
  !inst s vs s'. step_inst_base inst s = IntRet vs s' ==>
                 is_terminator inst.inst_opcode
Proof
  step_base_result_tac
QED

Theorem step_inst_base_no_abort[local]:
  !inst s a s'. step_inst_base inst s = Abort a s' /\
                ~is_terminator inst.inst_opcode ==>
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY
Proof
  rpt strip_tac >>
  drule opcodeClassTheory.step_inst_base_abort_opcodes >>
  strip_tac >> gvs[is_terminator_def]
QED

(* Effect-free non-INVOKE step_inst can only return OK or Error. *)
Theorem effect_free_step_ok_or_error:
  !fuel ctx inst s.
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  `~is_terminator inst.inst_opcode`
    by metis_tac[is_effect_free_not_terminator] >>
  Cases_on `step_inst_base inst s` >> gvs[]
  >- (imp_res_tac step_inst_base_no_halt >> gvs[])
  >- (imp_res_tac step_inst_base_no_abort >>
      gvs[is_effect_free_op_def])
  >- (imp_res_tac step_inst_base_no_intret >> gvs[])
QED

(* result_equiv is exactly lift_result with the standard relations *)
Theorem result_equiv_is_lift_result[local]:
  !vars r1 r2.
    result_equiv vars r1 r2 ==>
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[result_equiv_def, lift_result_def]
QED

(* Shared tactic: apply block_sim IH with given V and s2 term *)
fun apply_block_ih_tac s2_term =
  first_x_assum (qspec_then
    `LENGTH bb.bb_instructions - SUC s1.vs_inst_idx` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `lr`, `V`, `bb`,
    `s1' with vs_inst_idx := SUC s1.vs_inst_idx`,
    s2_term] mp_tac) >>
  simp[] >>
  (impl_tac >- (
    conj_tac >- gvs[] >>
    gvs[state_equiv_def, execution_equiv_def] >>
    rw[] >> gvs[lookup_var_def])) >>
  simp[];

(* Block-level simulation parameterized over divergent set V.
   V must contain the NOP'd outputs (block_nop_outputs ⊆ V) and
   operand vars must not be in V. V is preserved through the block.
   
   WHY TRUE: At each instruction position:
   - Kept instruction: same code, operands ∉ V (by hypothesis) →
     step_inst_result_equiv gives result_equiv V.
   - NOP'd instruction: original runs effect-free inst, outputs ⊆ V.
     NOP identity on transformed. Compose via state_equiv_effect_free_compose. *)
Theorem remove_unused_block_sim[local]:
  !n fuel ctx lr V bb s1 s2.
    n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    block_nop_outputs lr bb SUBSET V /\
    (!inst v. MEM inst bb.bb_instructions /\
              MEM (Var v) inst.inst_operands ==>
              v NOTIN V) /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    state_equiv V s1 s2 ==>
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (remove_unused_block lr bb) s2)
Proof
  completeInduct_on `n` >>
  rpt strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  simp[get_instruction_remove_unused, get_instruction_def] >>
  reverse (Cases_on `s1.vs_inst_idx < LENGTH bb.bb_instructions`)
  >- (gvs[] >> DISJ1_TAC >> simp[]) >>
  simp[] >>
  (* Unify indices *)
  qpat_x_assum `s1.vs_inst_idx = s2.vs_inst_idx`
    (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq]) >> assume_tac eq) >>
  qabbrev_tac `idx = s2.vs_inst_idx` >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `MEM inst bb.bb_instructions` by metis_tac[listTheory.MEM_EL] >>
  (* Case split: NOP'd or kept *)
  Cases_on `remove_unused_inst
    (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions))
    inst = mk_nop_inst inst`
  >| [
    (* === NOP'd instruction === *)
    `is_effect_free_op inst.inst_opcode`
      by metis_tac[remove_unused_inst_nop_effect_free] >>
    `~is_terminator inst.inst_opcode`
      by metis_tac[is_effect_free_not_terminator] >>
    `inst.inst_opcode <> INVOKE`
      by (strip_tac >> gvs[is_effect_free_op_def]) >>
    `set inst.inst_outputs SUBSET V` by (
      `set inst.inst_outputs SUBSET block_nop_outputs lr bb` by (
        mp_tac (Q.SPECL [`lr`, `bb`, `idx`, `inst`]
          nop_outputs_in_block_nop_outputs) >>
        gvs[Abbr `inst`]) >>
      metis_tac[pred_setTheory.SUBSET_TRANS]) >>
    `step_inst fuel ctx (mk_nop_inst inst) s2 = OK s2`
      by (irule step_nop_identity >> simp[mk_nop_inst_def]) >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s1`]
      effect_free_step_ok_or_error) >>
    (impl_tac >- gvs[]) >> strip_tac >> (
    `~is_terminator NOP` by EVAL_TAC >>
    gvs[mk_nop_inst_def] >>
    TRY (DISJ1_TAC >> simp[] >> NO_TAC) >>
    (* Only OK case remains *)
    rename1 `step_inst fuel ctx inst s1 = OK s1'` >>
    `state_equiv (set inst.inst_outputs) s1 s1'` by
      metis_tac[step_effect_free_state_equiv] >>
    `state_equiv V s1' s2` by
      metis_tac[state_equiv_effect_free_compose] >>
    (* Non-terminator: apply IH *)
    apply_block_ih_tac `s2 with vs_inst_idx := SUC s1.vs_inst_idx`),
    (* === Kept instruction === *)
    `remove_unused_inst
       (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions))
       inst = inst` by
      metis_tac[remove_unused_inst_cases] >>
    gvs[] >>
    `result_equiv V
       (step_inst fuel ctx inst s1)
       (step_inst fuel ctx inst s2)` by (
      Cases_on `is_terminator inst.inst_opcode`
      >- (`inst.inst_opcode <> INVOKE`
            by (CCONTR_TAC >> gvs[is_terminator_def]) >>
          gvs[step_inst_non_invoke] >>
          irule execEquivProofsTheory.step_inst_result_equiv >>
          gvs[] >> rpt strip_tac >> res_tac)
      >- (irule step_inst_result_equiv_full >> gvs[] >>
          rpt strip_tac >> res_tac)) >>
    (* Case split on both results; cross-cases eliminated by result_equiv *)
    Cases_on `step_inst fuel ctx inst s1` >>
    Cases_on `step_inst fuel ctx inst s2` >>
    gvs[result_equiv_def] >>
    (* Close all non-OK-OK cases uniformly *)
    TRY (simp[lift_result_def] >> NO_TAC) >>
    TRY (DISJ1_TAC >> simp[] >> NO_TAC) >>
    (* Only OK-OK remains *)
    rename1 `step_inst fuel ctx inst s1 = OK s1'` >>
    rename1 `step_inst fuel ctx inst s2 = OK s2'` >>
    IF_CASES_TAC >> gvs[] >>
    TRY (
      `s1'.vs_halted <=> s2'.vs_halted`
        by gvs[state_equiv_def, execution_equiv_def] >>
      IF_CASES_TAC >> gvs[] >>
      simp[lift_result_def] >>
      gvs[state_equiv_def, execution_equiv_def] >> NO_TAC) >>
    (* Non-terminator OK: apply IH *)
    apply_block_ih_tac `s2' with vs_inst_idx := SUC s1.vs_inst_idx`
  ]
QED

(* Same-starting-state wrapper for backward compat *)
Theorem remove_unused_block_correct_proof:
  !fuel ctx lr bb s.
    (!inst v. MEM inst bb.bb_instructions /\
              MEM (Var v) inst.inst_operands ==>
              v NOTIN block_nop_outputs lr bb) /\
    s.vs_inst_idx = 0 ==>
    let nop_outs = block_nop_outputs lr bb in
    (?e. exec_block fuel ctx bb s = Error e) \/
    lift_result (state_equiv nop_outs) (execution_equiv nop_outs) (execution_equiv nop_outs)
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (remove_unused_block lr bb) s)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  mp_tac (Q.SPECL [`LENGTH bb.bb_instructions`,
                    `fuel`, `ctx`, `lr`,
                    `block_nop_outputs lr bb`,
                    `bb`, `s`, `s`]
                   remove_unused_block_sim) >>
  simp[state_equiv_refl, pred_setTheory.SUBSET_REFL] >> metis_tac[]
QED

(* ===== Function-level building blocks ===== *)

(* Writing the same value to both states shrinks the divergent set *)
Theorem update_var_shrinks_state_equiv[local]:
  !vars x v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv (vars DELETE x) (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_def, execution_equiv_def, update_var_def,
     lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> rpt strip_tac >> gvs[] >>
  first_x_assum irule >> gvs[]
QED

(* FOLDL update_var with same (var,val) pairs shrinks by all written vars *)
Theorem foldl_update_var_shrinks[local]:
  !pairs s1 s2 vars.
    state_equiv vars s1 s2 ==>
    state_equiv (vars DIFF set (MAP FST pairs))
      (FOLDL (\s' (out,val). update_var out val s') s1 pairs)
      (FOLDL (\s' (out,val). update_var out val s') s2 pairs)
Proof
  Induct
  >- (rw[] >> gvs[pred_setTheory.DIFF_EMPTY])
  >> rpt gen_tac >> strip_tac >>
  PairCases_on `h` >> gvs[] >>
  first_x_assum (qspecl_then
    [`update_var h0 h1 s1`, `update_var h0 h1 s2`,
     `vars DELETE h0`] mp_tac) >>
  (impl_tac >- metis_tac[update_var_shrinks_state_equiv]) >>
  `(vars DELETE h0) DIFF set (MAP FST pairs) SUBSET
   vars DIFF (h0 INSERT set (MAP FST pairs))` by
    (simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  metis_tac[state_equiv_subset]
QED

(* Weakening lift_result — copied from assignElimProofs *)
Theorem lift_result_weaken[local]:
  !R1_ok R2_ok R1_term R2_term r1 r2.
    (!s1 s2. R1_ok s1 s2 ==> R2_ok s1 s2) /\
    (!s1 s2. R1_term s1 s2 ==> R2_term s1 s2) /\
    lift_result R1_ok R1_term R1_term r1 r2 ==>
    lift_result R2_ok R2_term R2_term r1 r2
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def]
QED

(* Compose lift_result with result_equiv: if r1 ~ r2 via lift_result
   and r2 ~ r3 via result_equiv (subset), then r1 ~ r3 via lift_result.
   Key pattern: NOP-insertion phase (lift_result) + NOP-cleanup (result_equiv). *)
Theorem lift_result_compose_result_equiv[local]:
  !vars r1 r2 r3.
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars) r1 r2 /\
    result_equiv {} r2 r3 ==>
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars) r1 r3
Proof
  rpt strip_tac >>
  irule (REWRITE_RULE [AND_IMP_INTRO]
    passSimulationPropsTheory.lift_result_trans) >>
  rpt conj_tac
  >- metis_tac[stateEquivPropsTheory.state_equiv_trans]
  >- metis_tac[stateEquivPropsTheory.execution_equiv_trans] >>
  qexists_tac `r2` >> conj_tac >- first_assum ACCEPT_TAC >>
  irule lift_result_weaken >>
  qexistsl_tac [`state_equiv {}`, `execution_equiv {}`] >>
  rpt conj_tac
  >- (rpt strip_tac >>
      irule stateEquivPropsTheory.state_equiv_subset >>
      qexists_tac `{}` >> simp[])
  >- (rpt strip_tac >>
      irule stateEquivPropsTheory.execution_equiv_subset >>
      qexists_tac `{}` >> simp[])
  >- gvs[stateEquivPropsTheory.result_equiv_is_lift_result]
QED

(* ===== Function-level ===== *)

(* ALL_DISTINCT outputs in fn_insts_blocks implies same for each block *)
Theorem all_distinct_outputs_block[local]:
  !bbs bb. MEM bb bbs ==>
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs)
                            (fn_insts_blocks bbs))) ==>
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs)
                            bb.bb_instructions))
Proof
  Induct >> rw[fn_insts_blocks_def] >>
  gvs[listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
      listTheory.ALL_DISTINCT_APPEND]
QED

(* Within a block with ALL_DISTINCT outputs, positions define same var ⟹ same *)
Theorem all_distinct_outputs_unique_pos[local]:
  !insts v i k.
    ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) insts)) /\
    i < LENGTH insts /\ k < LENGTH insts /\
    MEM v (EL i insts).inst_outputs /\
    MEM v (EL k insts).inst_outputs ==>
    i = k
Proof
  Induct >> rw[] >>
  Cases_on `i` >> Cases_on `k` >> gvs[] >>
  gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT,
      listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM_EL]
QED

(* ssa_form implies: if v is output at position i in block bb,
   then no other position in bb has v as output. *)
Theorem ssa_form_no_dup_in_block:
  !fn bb v i k.
    ssa_form fn /\
    MEM bb fn.fn_blocks /\
    i < LENGTH bb.bb_instructions /\
    k < LENGTH bb.bb_instructions /\
    MEM v (EL i bb.bb_instructions).inst_outputs /\
    MEM v (EL k bb.bb_instructions).inst_outputs ==>
    i = k
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))` by (
    irule all_distinct_outputs_block >>
    qexists_tac `fn.fn_blocks` >> gvs[] >>
    gvs[ssa_form_def, fn_insts_def]) >>
  irule all_distinct_outputs_unique_pos >>
  qexistsl_tac [`bb.bb_instructions`, `v`] >> gvs[]
QED

(* All NOP'd outputs across all blocks in one pass *)
Definition single_pass_nop_outputs_def:
  single_pass_nop_outputs fn =
    let lr = liveness_analyze fn in
    BIGUNION (set (MAP (\bb.
      block_nop_outputs lr bb)
      fn.fn_blocks))
End

(* Label preservation for remove_unused_block *)
Theorem remove_unused_block_label:
  !lr bb. (remove_unused_block lr bb).bb_label = bb.bb_label
Proof
  rw[remove_unused_block_def]
QED

(* Block NOP outputs are subset of single_pass_nop_outputs *)
Theorem block_nop_outputs_subset_single_pass[local]:
  !fn bb.
    MEM bb fn.fn_blocks ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    block_nop_outputs lr bb SUBSET single_pass_nop_outputs fn
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  simp[single_pass_nop_outputs_def, LET_THM] >>
  irule pred_setTheory.SUBSET_BIGUNION_I >>
  simp[listTheory.MEM_MAP] >> qexists_tac `bb` >> simp[]
QED

(* Helper: MEM (Var v) in a list implies MEM v (operand_vars list) *)
Theorem mem_var_operand_vars[local]:
  !ops v. MEM (Var v) ops ==> MEM v (operand_vars ops)
Proof
  Induct >> rw[operand_vars_def] >>
  Cases_on `operand_var h` >> gvs[operand_var_def]
QED

(* Helper: MEM (Var v) operands implies MEM v (inst_uses inst) *)
Theorem operand_var_in_inst_uses[local]:
  !inst v. MEM (Var v) inst.inst_operands ==>
           MEM v (inst_uses inst)
Proof
  rw[inst_uses_def] >> irule mem_var_operand_vars >> gvs[]
QED

(* Helper: NOP'd instruction means outputs not live after *)
Theorem nop_inst_outputs_not_live_after[local]:
  !lr bb idx inst v.
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    remove_unused_inst
      (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions))
      inst = mk_nop_inst inst /\
    MEM v inst.inst_outputs ==>
    ~MEM v (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions))
Proof
  rpt strip_tac >>
  gvs[remove_unused_inst_def] >>
  rpt (pop_assum mp_tac) >>
  rpt IF_CASES_TAC >> gvs[mk_nop_inst_def, instruction_component_equality] >>
  rpt strip_tac >>
  gvs[listTheory.EVERY_MEM]
QED

(* live_after_at at position idx equals live_vars_at at SUC idx *)
Theorem live_after_at_suc:
  !lr lbl idx n. idx < n ==>
    live_after_at lr lbl idx n = live_vars_at lr lbl (SUC idx)
Proof
  rw[live_after_at_def, arithmeticTheory.ADD1] >>
  `idx + 1 = n` by simp[] >> gvs[]
QED

(* ===== Growing V block simulation with SSA + liveness ===== *)


(* Block instructions are in fn_insts *)
Theorem mem_block_fn_insts[local]:
  !bbs bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
                MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> rw[fn_insts_blocks_def, listTheory.MEM_APPEND] >> metis_tac[]
QED

(* ALL_DISTINCT inst_ids for a single block in a wf_function *)
Theorem block_inst_ids_distinct[local]:
  !bbs bb. MEM bb bbs /\
    ALL_DISTINCT (FLAT (MAP (\bb. MAP (\i. i.inst_id)
                                      bb.bb_instructions) bbs)) ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  Induct >> rw[] >> gvs[listTheory.ALL_DISTINCT_APPEND]
QED

(* Weaken result_equiv V to lift_result V_out when V ⊆ V_out.
   Factors out the terminator dispatch pattern: either Error or lift_result. *)
Theorem result_equiv_weaken_lift_result[local]:
  !V V_out r1 r2.
    result_equiv V r1 r2 /\ V SUBSET V_out ==>
    (?e. r1 = Error e) \/
    lift_result (state_equiv V_out) (execution_equiv V_out) (execution_equiv V_out) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[result_equiv_def, lift_result_def] >>
  rpt strip_tac >>
  TRY (irule state_equiv_subset >> qexists_tac `V` >> gvs[] >> NO_TAC) >>
  irule execution_equiv_subset >> qexists_tac `V` >> gvs[]
QED

(* One-step liveness forward: if v is not live at idx and not in the
   outputs of instruction idx, then v is not live at SUC idx.
   Wraps not_live_forward_in_block (i=idx, j=SUC idx) with LET_THM
   and inst_defs eliminated. *)
Theorem not_live_one_step[local]:
  !fn bb idx v.
    wf_function fn /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label idx) /\
    ~MEM v (EL idx bb.bb_instructions).inst_outputs ==>
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC idx))
Proof
  rpt strip_tac >>
  drule (SIMP_RULE std_ss [LET_THM, inst_defs_def]
    not_live_forward_in_block) >>
  disch_then (qspecl_then [`bb.bb_label`, `bb`, `idx`, `SUC idx`, `v`]
    mp_tac) >>
  simp[] >>
  rpt strip_tac >> `k = idx` by simp[] >> gvs[]
QED

(* Advance both invariants (liveness + no-def) for V-only (Kept case).
   V stays the same. *)
Theorem inv_advance_V_only[local]:
  !fn bb idx V.
    wf_function fn /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    (!v. v IN V ==> ~MEM v (live_vars_at (liveness_analyze fn)
                                          bb.bb_label idx)) /\
    (!v k. v IN V /\ idx <= k /\ k < LENGTH bb.bb_instructions ==>
           ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
    (!v. v IN V ==>
         ~MEM v (live_vars_at (liveness_analyze fn)
                              bb.bb_label (SUC idx))) /\
    (!v k. v IN V /\ SUC idx <= k /\ k < LENGTH bb.bb_instructions ==>
           ~MEM v (EL k bb.bb_instructions).inst_outputs)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >> rpt gen_tac >> strip_tac
  >- (irule not_live_one_step >> simp[] >>
      first_x_assum (qspecl_then [`v`, `idx`] mp_tac) >> simp[])
  >- (first_x_assum (qspecl_then [`v`, `k`] mp_tac) >> simp[])
QED

(* Advance liveness for NOP'd outputs: outputs not live at SUC idx. *)
Theorem inv_advance_liveness_outputs[local]:
  !fn bb idx v.
    idx < LENGTH bb.bb_instructions /\
    MEM v (EL idx bb.bb_instructions).inst_outputs /\
    (!v. MEM v (EL idx bb.bb_instructions).inst_outputs ==>
         ~MEM v (live_after_at (liveness_analyze fn)
                   bb.bb_label idx (LENGTH bb.bb_instructions))) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label (SUC idx))
Proof
  rpt gen_tac >> strip_tac >>
  `live_after_at (liveness_analyze fn) bb.bb_label idx
     (LENGTH bb.bb_instructions) =
   live_vars_at (liveness_analyze fn) bb.bb_label (SUC idx)` by
    (irule live_after_at_suc >> simp[]) >>
  metis_tac[]
QED

(* Advance no-def for NOP'd outputs: SSA uniqueness prevents redefinition. *)
Theorem inv_advance_nodef_outputs[local]:
  !fn bb idx k v.
    ssa_form fn /\
    MEM bb fn.fn_blocks /\
    MEM v (EL idx bb.bb_instructions).inst_outputs /\
    idx < LENGTH bb.bb_instructions /\
    SUC idx <= k /\ k < LENGTH bb.bb_instructions ==>
    ~MEM v (EL k bb.bb_instructions).inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  spose_not_then strip_assume_tac >>
  `idx = k` by metis_tac[ssa_form_no_dup_in_block] >>
  gvs[]
QED

(* Advance no-def invariant for V ∪ outputs at idx:
   If V vars are not defined from idx onward, and SSA ensures outputs at idx
   are unique, then V ∪ outputs(idx) vars are not defined from SUC idx onward. *)
Theorem inv_advance_nodef_union[local]:
  !fn bb idx V.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    idx < LENGTH bb.bb_instructions /\
    (!v k. v IN V /\ idx <= k /\ k < LENGTH bb.bb_instructions ==>
           ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
    (!v k. v IN (V UNION set (EL idx bb.bb_instructions).inst_outputs) /\
           SUC idx <= k /\ k < LENGTH bb.bb_instructions ==>
           ~MEM v (EL k bb.bb_instructions).inst_outputs)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `v IN V`
  >- (first_x_assum (qspecl_then [`v`, `k`] mp_tac) >> simp[])
  >> (fs[pred_setTheory.IN_UNION] >>
      irule inv_advance_nodef_outputs >> simp[] >>
      conj_tac >- metis_tac[] >>
      qexists_tac `idx` >> simp[])
QED

(* Block simulation with growing divergent set.
   Generalized with V (current excluded set) and two invariants:
   (1) V vars not live at current position
   (2) V vars not defined from current position onward
   The output is V_in ∪ block_nop_outputs (the full set for the block).
   V_in tracks vars from prior blocks (not defined in this block). *)
Theorem remove_unused_block_sim_ssa:
  !n fuel ctx fn bb s1 s2 V_in V.
    n = LENGTH bb.bb_instructions - s1.vs_inst_idx /\
    wf_function fn /\ fn_inst_wf fn /\ ssa_form fn /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
    EVERY (\inst. inst.inst_opcode <> ALLOCA) bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = NOP ==>
                  inst.inst_outputs = []) bb.bb_instructions /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    state_equiv V s1 s2 /\
    V_in SUBSET V /\
    V SUBSET (V_in UNION
      block_nop_outputs (liveness_analyze fn) bb) /\
    (* Inv 1: V vars not live at current position *)
    (!v. v IN V ==>
         ~MEM v (live_vars_at (liveness_analyze fn)
                              bb.bb_label s1.vs_inst_idx)) /\
    (* Inv 2: V vars not defined from current position onward *)
    (!v k. v IN V /\ s1.vs_inst_idx <= k /\
           k < LENGTH bb.bb_instructions ==>
           ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
    let lr = liveness_analyze fn in
    let V_out = V_in UNION block_nop_outputs lr bb in
    (?e. exec_block fuel ctx bb s1 = Error e) \/
    lift_result (state_equiv V_out) (execution_equiv V_out) (execution_equiv V_out)
      (exec_block fuel ctx bb s1)
      (exec_block fuel ctx (remove_unused_block lr bb) s2)
Proof
  completeInduct_on `n` >>
  rpt strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC [exec_block_def] >>
  simp[get_instruction_remove_unused, get_instruction_def] >>
  reverse (Cases_on `s1.vs_inst_idx < LENGTH bb.bb_instructions`)
  >- (gvs[] >> DISJ1_TAC >> simp[]) >>
  simp[] >>
  qpat_x_assum `s1.vs_inst_idx = s2.vs_inst_idx`
    (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq]) >> assume_tac eq) >>
  qabbrev_tac `idx = s2.vs_inst_idx` >>
  qabbrev_tac `inst = EL idx bb.bb_instructions` >>
  `MEM inst bb.bb_instructions` by metis_tac[listTheory.MEM_EL] >>
  `inst.inst_opcode <> ALLOCA` by (
    gvs[listTheory.EVERY_MEM] >> res_tac) >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  (* Discharge operand condition for V at current instruction *)
  `!v. v IN V /\ MEM (Var v) inst.inst_operands ==> F` by (
    rpt strip_tac >>
    `MEM v (inst_uses inst)` by (
      simp[inst_uses_def] >> irule mem_var_operand_vars >> simp[]) >>
    `MEM v (live_vars_at (liveness_analyze fn) bb.bb_label idx)` by (
      mp_tac (Q.SPECL [`fn`, `bb.bb_label`, `bb`, `idx`, `v`]
                       live_vars_at_uses) >>
      simp[LET_THM] >> disch_then irule >> gvs[Abbr `inst`]) >>
    `~MEM v (live_vars_at (liveness_analyze fn) bb.bb_label idx)` by (
      first_x_assum irule >> simp[]) >>
    metis_tac[]) >>
  (* Reformulate operand condition for step_inst_result_equiv *)
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN V` by metis_tac[] >>
  (* V SUBSET V_out for weakening *)
  qabbrev_tac `V_out = V_in UNION block_nop_outputs (liveness_analyze fn) bb` >>
  `V SUBSET V_out` by gvs[Abbr `V_out`] >>
  Cases_on `remove_unused_inst
    (live_after_at (liveness_analyze fn) bb.bb_label idx
                   (LENGTH bb.bb_instructions))
    inst = mk_nop_inst inst`
  >| [
    (* === NOP'd instruction === *)
    `is_effect_free_op inst.inst_opcode`
      by metis_tac[remove_unused_inst_nop_effect_free] >>
    `~is_terminator inst.inst_opcode`
      by metis_tac[is_effect_free_not_terminator] >>
    `inst.inst_opcode <> INVOKE`
      by (strip_tac >> gvs[is_effect_free_op_def]) >>
    `step_inst fuel ctx (mk_nop_inst inst) s2 = OK s2`
      by (irule step_nop_identity >> simp[mk_nop_inst_def]) >>
    (* Establish subset BEFORE gvs[mk_nop_inst_def] rewrites it away *)
    `set inst.inst_outputs SUBSET
      block_nop_outputs (liveness_analyze fn) bb` by (
      mp_tac (Q.SPECL [`liveness_analyze fn`,
        `bb`, `idx`, `inst`]
        nop_outputs_in_block_nop_outputs) >>
      gvs[Abbr `inst`]) >>
    (* Establish liveness BEFORE gvs[mk_nop_inst_def] destroys mk_nop_inst *)
    `!v. MEM v inst.inst_outputs ==>
         ~MEM v (live_after_at (liveness_analyze fn)
                   bb.bb_label idx (LENGTH bb.bb_instructions))`
      by (rpt strip_tac >>
          mp_tac (Q.SPECL [`liveness_analyze fn`,
            `bb`, `idx`, `inst`, `v`]
            nop_inst_outputs_not_live_after) >>
          simp[Abbr `inst`]) >>
    (* Resolve abbreviations now — all mk_nop_inst-dependent facts established *)
    qunabbrev_tac `inst` >> qunabbrev_tac `idx` >>
    (* Original side: effect-free → OK or Error *)
    mp_tac (Q.SPECL [`fuel`, `ctx`,
      `EL s2.vs_inst_idx bb.bb_instructions`, `s1`]
      effect_free_step_ok_or_error) >>
    (impl_tac >- gvs[]) >> strip_tac >| [
      (* OK case *)
      rename1 `step_inst _ _ (EL _ bb.bb_instructions) s1 = OK s1'` >>
      `~is_terminator NOP` by EVAL_TAC >>
      fs[mk_nop_inst_def] >>
      `state_equiv (set (EL s2.vs_inst_idx bb.bb_instructions).inst_outputs)
                   s1 s1'`
        by metis_tac[step_effect_free_state_equiv] >>
      `state_equiv (V UNION set (EL s2.vs_inst_idx bb.bb_instructions).inst_outputs) s1' s2`
        by metis_tac[state_equiv_union_compose] >>
      `s1'.vs_inst_idx = s1.vs_inst_idx`
        by gvs[state_equiv_def] >>
      (* Establish IH preconditions explicitly *)
      `V_in SUBSET (V UNION set (EL s2.vs_inst_idx bb.bb_instructions).inst_outputs)` by
        (irule pred_setTheory.SUBSET_TRANS >> qexists_tac `V` >> gvs[]) >>
      `(V UNION set (EL s2.vs_inst_idx bb.bb_instructions).inst_outputs) SUBSET V_out` by (
        gvs[pred_setTheory.UNION_SUBSET, Abbr `V_out`] >>
        irule pred_setTheory.SUBSET_TRANS >>
        qexists_tac `block_nop_outputs (liveness_analyze fn) bb` >> gvs[]) >>
      (* Liveness: v IN V ∪ outputs ⇒ not live at SUC s2.vs_inst_idx *)
      `!v. v IN (V UNION set (EL s2.vs_inst_idx bb.bb_instructions).inst_outputs) ==>
           ~MEM v (live_vars_at (liveness_analyze fn)
                                bb.bb_label (SUC s2.vs_inst_idx))` by (
        rpt gen_tac >> strip_tac >>
        Cases_on `v IN V`
        >- (irule not_live_one_step >> simp[] >>
            first_x_assum (qspecl_then [`v`, `s2.vs_inst_idx`] mp_tac) >>
            simp[])
        >- (gvs[pred_setTheory.IN_UNION] >>
            `live_after_at (liveness_analyze fn) bb.bb_label s2.vs_inst_idx
               (LENGTH bb.bb_instructions) =
             live_vars_at (liveness_analyze fn) bb.bb_label (SUC s2.vs_inst_idx)` by
              (irule live_after_at_suc >> simp[]) >>
            metis_tac[])) >>
      (* No-def: v IN V ∪ outputs, SUC s2.vs_inst_idx ≤ k ⇒ not in outputs at k *)
      `!v k. v IN (V UNION set (EL s2.vs_inst_idx bb.bb_instructions).inst_outputs) /\
             SUC s2.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
             ~MEM v (EL k bb.bb_instructions).inst_outputs` by
        (mp_tac (Q.SPECL [`fn`, `bb`, `s2.vs_inst_idx`, `V`]
           inv_advance_nodef_union) >> simp[]) >>
      (* state_equiv through inst_idx update *)
      `state_equiv (V UNION set (EL s2.vs_inst_idx bb.bb_instructions).inst_outputs)
         (s1' with vs_inst_idx := SUC s2.vs_inst_idx)
         (s2 with vs_inst_idx := SUC s2.vs_inst_idx)` by
        gvs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
      (* Apply IH *)
      first_x_assum (qspec_then
        `LENGTH bb.bb_instructions - SUC s2.vs_inst_idx` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspecl_then [`fuel`, `ctx`, `fn`, `bb`,
        `s1' with vs_inst_idx := SUC s2.vs_inst_idx`,
        `s2 with vs_inst_idx := SUC s2.vs_inst_idx`,
        `V_in`, `V UNION set (EL s2.vs_inst_idx bb.bb_instructions).inst_outputs`] mp_tac) >>
      simp[Abbr `V_out`] >>
      disch_then irule >> simp[],
      (* Error case *)
      DISJ1_TAC >> simp[]
    ],
    (* === Kept instruction === *)
    `remove_unused_inst
       (live_after_at (liveness_analyze fn) bb.bb_label idx
                      (LENGTH bb.bb_instructions))
       inst = inst` by
      metis_tac[remove_unused_inst_cases] >>
    qunabbrev_tac `inst` >> qunabbrev_tac `idx` >>
    gvs[] >>
    `result_equiv V
       (step_inst fuel ctx (EL s2.vs_inst_idx bb.bb_instructions) s1)
       (step_inst fuel ctx (EL s2.vs_inst_idx bb.bb_instructions) s2)` by (
      Cases_on `is_terminator (EL s2.vs_inst_idx bb.bb_instructions).inst_opcode`
      >- (`(EL s2.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE`
            by (CCONTR_TAC >> gvs[is_terminator_def]) >>
          gvs[step_inst_non_invoke] >>
          irule execEquivProofsTheory.step_inst_result_equiv >>
          gvs[] >> rpt strip_tac >> first_x_assum irule >> simp[])
      >- (irule step_inst_result_equiv_full >> gvs[] >>
          rpt strip_tac >> first_x_assum irule >> simp[])) >>
    Cases_on `step_inst fuel ctx (EL s2.vs_inst_idx bb.bb_instructions) s1` >>
    Cases_on `step_inst fuel ctx (EL s2.vs_inst_idx bb.bb_instructions) s2` >>
    (* Name OK values BEFORE fs[result_equiv_def] consumes OK constructors *)
    TRY (rename1 `result_equiv V (OK s1') _`) >>
    TRY (rename1 `result_equiv V _ (OK s2')`) >>
    fs[result_equiv_def] >> (
    (* Close non-OK-OK: Halt/Abort/IntRet need weakening V→V_out *)
    TRY (
      simp[lift_result_def] >>
      TRY (irule state_equiv_subset >> qexists_tac `V` >> gvs[]) >>
      TRY (irule execution_equiv_subset >> qexists_tac `V` >> gvs[]) >>
      NO_TAC) >>
    TRY (DISJ1_TAC >> simp[] >> NO_TAC)) >>
    (* Only OK-OK remains. state_equiv V s1' s2' in assumptions *)
    Cases_on `is_terminator (EL s2.vs_inst_idx bb.bb_instructions).inst_opcode`
    >- (
      (* Terminator kept OK-OK: exec_block returns Halt or OK based on vs_halted *)
      gvs[] >>
      (* vs_halted equivalence from state_equiv V via execution_equiv *)
      `s1'.vs_halted <=> s2'.vs_halted` by
        gvs[state_equiv_def, execution_equiv_def] >>
      IF_CASES_TAC >> gvs[] >>
      simp[lift_result_def] >>
      TRY (irule state_equiv_subset >> qexists_tac `V` >> gvs[]) >>
      TRY (irule execution_equiv_subset >> qexists_tac `V` >>
           gvs[state_equiv_def]))
    >- (
      (* Non-terminator kept OK-OK: apply IH with same V *)
      gvs[] >>
      (* Advance both invariants *)
      drule_all inv_advance_V_only >> strip_tac >>
      (* state_equiv through inst_idx update *)
      `state_equiv V
         (s1' with vs_inst_idx := SUC s2.vs_inst_idx)
         (s2' with vs_inst_idx := SUC s2.vs_inst_idx)` by
        gvs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
      (* Apply IH *)
      first_x_assum (qspec_then
        `LENGTH bb.bb_instructions - SUC s2.vs_inst_idx` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspecl_then [`fuel`, `ctx`, `fn`, `bb`,
        `s1' with vs_inst_idx := SUC s2.vs_inst_idx`,
        `s2' with vs_inst_idx := SUC s2.vs_inst_idx`,
        `V_in`, `V`] mp_tac) >>
      simp[Abbr `V_out`] >>
      disch_then irule >> simp[])
  ]
QED

(* ===== SSA dead variable propagation ===== *)

(* If v is dead after definition and not defined elsewhere in def_bb
   (SSA), then v is dead at def_bb's exit. *)
Theorem not_live_at_def_block_exit[local]:
  !fn def_lbl def_bb def_idx v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM def_lbl cfg.cfg_dfs_pre /\
    lookup_block def_lbl fn.fn_blocks = SOME def_bb /\
    def_idx < LENGTH def_bb.bb_instructions /\
    ~MEM v (live_vars_at lr def_lbl (SUC def_idx)) /\
    (* v not defined at any position after def_idx *)
    (!k. SUC def_idx <= k /\ k < LENGTH def_bb.bb_instructions ==>
         ~MEM v (inst_defs (EL k def_bb.bb_instructions))) ==>
    ~MEM v (live_vars_at lr def_lbl (LENGTH def_bb.bb_instructions))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >> strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM] not_live_forward_in_block) >>
  disch_then (qspecl_then [`fn`, `def_lbl`, `def_bb`,
    `SUC def_idx`, `LENGTH def_bb.bb_instructions`, `v`] mp_tac) >>
  simp[]
QED

(* If v is dead at block entry and not defined in the block,
   then v is dead at block exit. *)
Theorem not_live_through_block[local]:
  !fn lbl bb v.
    wf_function fn ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    MEM lbl cfg.cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    ~MEM v (live_vars_at lr lbl 0) /\
    (!k. k < LENGTH bb.bb_instructions ==>
         ~MEM v (inst_defs (EL k bb.bb_instructions))) ==>
    ~MEM v (live_vars_at lr lbl (LENGTH bb.bb_instructions))
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >> strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM] not_live_forward_in_block) >>
  disch_then (qspecl_then [`fn`, `lbl`, `bb`,
    `0`, `LENGTH bb.bb_instructions`, `v`] mp_tac) >>
  simp[]
QED

(* ===== Path / dominance infrastructure ===== *)

(* is_fn_path is preserved by appending when last element connects *)
Theorem is_fn_path_append[local]:
  !fn p1 p2.
    is_fn_path fn p1 /\ is_fn_path fn p2 /\
    (p1 <> [] /\ p2 <> [] ==> fn_cfg_edge fn (LAST p1) (HD p2)) ==>
    is_fn_path fn (p1 ++ p2)
Proof
  gen_tac >>
  `!n p1 p2. LENGTH p1 = n ==>
    is_fn_path fn p1 /\ is_fn_path fn p2 /\
    (p1 <> [] /\ p2 <> [] ==> fn_cfg_edge fn (LAST p1) (HD p2)) ==>
    is_fn_path fn (p1 ++ p2)` suffices_by metis_tac[] >>
  Induct >> rpt strip_tac
  >- (fs[listTheory.LENGTH_NIL] >> simp[])
  >> Cases_on `p1` >> fs[] >>
  Cases_on `t`
  >- (simp[] >> Cases_on `p2` >> simp[is_fn_path_def] >>
      Cases_on `t` >> fs[is_fn_path_def, listTheory.LAST_DEF])
  >> simp[] >> fs[is_fn_path_def, listTheory.LAST_DEF] >>
  first_x_assum (qspecl_then [`h'::t'`, `p2`] mp_tac) >> simp[] >>
  disch_then irule >> simp[] >>
  Cases_on `p2` >> fs[] >>
  Cases_on `t'` >> fs[listTheory.LAST_DEF]
QED

(* Converting RTC to is_fn_path *)
Theorem rtc_to_is_fn_path[local]:
  !fn a b. RTC (fn_cfg_edge fn) a b ==>
    ?path. is_fn_path fn path /\ path <> [] /\ HD path = a /\ LAST path = b
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >>
  rpt strip_tac
  >- (qexists_tac `[a]` >> simp[is_fn_path_def])
  >> qexists_tac `a::path` >>
  Cases_on `path` >> fs[is_fn_path_def]
QED

(* Converting is_fn_path to RTC *)
Theorem is_fn_path_to_rtc[local]:
  !fn path. is_fn_path fn path /\ path <> [] ==>
    RTC (fn_cfg_edge fn) (HD path) (LAST path)
Proof
  gen_tac >>
  `!n path. LENGTH path = n ==>
    is_fn_path fn path /\ path <> [] ==>
    RTC (fn_cfg_edge fn) (HD path) (LAST path)` suffices_by metis_tac[] >>
  Induct >> rpt strip_tac
  >- fs[listTheory.LENGTH_NIL]
  >> Cases_on `path` >> fs[] >>
  Cases_on `t`
  >- simp[listTheory.LAST_DEF, relationTheory.RTC_REFL]
  >> fs[is_fn_path_def, listTheory.LAST_DEF] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists_tac `h'` >> simp[] >>
  first_x_assum (qspec_then `h'::t'` mp_tac) >>
  simp[listTheory.LAST_DEF]
QED

(* Suffix extraction: if d is MEM of a path, extract suffix starting at d *)
Theorem is_fn_path_mem_suffix[local]:
  !fn path d. is_fn_path fn path /\ MEM d path ==>
    ?suffix. is_fn_path fn (d :: suffix) /\ LAST (d :: suffix) = LAST path /\
             !x. MEM x (d :: suffix) ==> MEM x path
Proof
  gen_tac >> Induct >> simp[] >>
  rpt strip_tac
  >- (qexists_tac `path` >> Cases_on `path`
      >- simp[is_fn_path_def, listTheory.LAST_DEF]
      >> fs[is_fn_path_def, listTheory.LAST_DEF] >>
      rpt strip_tac >> fs[])
  >> fs[] >>
  Cases_on `path`
  >- fs[]
  >> fs[is_fn_path_def] >>
  first_x_assum (qspec_then `d` mp_tac) >> simp[] >>
  strip_tac >> qexists_tac `suffix` >> simp[] >>
  fs[listTheory.LAST_DEF] >> rpt strip_tac >> fs[]
QED

(* Dominance bridge: if d dominates succ and l->succ is an edge,
   and l is reachable, then either d=succ or d reaches l. *)
Theorem dominates_predecessor_rtc[local]:
  !fn d succ l.
    fn_dominates fn d succ /\
    fn_cfg_edge fn l succ /\
    fn_reachable fn l ==>
    d = succ \/ RTC (fn_cfg_edge fn) d l
Proof
  rpt strip_tac >>
  gvs[fn_dominates_def, fn_reachable_def] >>
  (* path: entry ->* l *)
  drule rtc_to_is_fn_path >> strip_tac >>
  (* Extend: entry ->* l -> succ *)
  (SUBGOAL_THEN ``is_fn_path fn (path ++ [succ])`` assume_tac
   >- (irule is_fn_path_append >> simp[is_fn_path_def] >>
       rpt strip_tac >> fs[listTheory.LAST_DEF])) >>
  (* Dominance: d in path ++ [succ] *)
  first_x_assum (qspec_then `path ++ [succ]` mp_tac) >>
  simp[listTheory.LAST_APPEND_CONS] >>
  (impl_tac >- (Cases_on `path` >> fs[] >> metis_tac[])) >>
  strip_tac >>
  gvs[listTheory.MEM_APPEND] >>
  (* d in path: extract suffix d -> l *)
  disj2_tac >>
  drule_at (Pos (el 2)) is_fn_path_mem_suffix >> disch_then drule >>
  strip_tac >>
  metis_tac[is_fn_path_to_rtc, listTheory.NOT_NIL_CONS, listTheory.HD]
QED

(* ===== cfg_exec_path infrastructure for operand condition ===== *)

(* Within-block path: GENLIST produces a valid cfg_exec_path *)
Theorem cfg_exec_path_intra[local]:
  !n lbl s cfg.
    cfg_exec_path cfg (GENLIST (\i. (lbl:string, s + i)) (SUC n))
Proof
  Induct >- simp[listTheory.GENLIST_CONS, livenessDefsTheory.cfg_exec_path_def] >>
  rpt gen_tac >>
  simp[Once listTheory.GENLIST_CONS, combinTheory.o_DEF] >>
  `GENLIST (\x. (lbl:string, s + SUC x)) (SUC n) =
   GENLIST (\i. (lbl, SUC s + i)) (SUC n)` by (
    irule listTheory.GENLIST_CONG >> simp[]) >>
  pop_assum SUBST1_TAC >>
  first_x_assum (qspecl_then [`lbl`, `SUC s`, `cfg`] mp_tac) >>
  Cases_on `GENLIST (\i. (lbl:string, SUC s + i)) (SUC n)` >- fs[listTheory.GENLIST] >>
  strip_tac >>
  `h = (lbl, SUC s)` by (
    qpat_x_assum `_ = h::t` (mp_tac o SYM) >>
    simp[listTheory.GENLIST_CONS, combinTheory.o_DEF]) >>
  rw[livenessDefsTheory.cfg_exec_path_def]
QED

(* Extend a cfg_exec_path with a compatible continuation *)
Theorem cfg_exec_path_extend[local]:
  !path lbl2 idx2 suffix cfg.
    cfg_exec_path cfg path /\ path <> [] /\
    ((lbl2 = FST (LAST path) /\ idx2 = SND (LAST path) + 1) \/
     (MEM lbl2 (cfg_succs_of cfg (FST (LAST path))) /\ idx2 = 0)) /\
    cfg_exec_path cfg ((lbl2, idx2) :: suffix) ==>
    cfg_exec_path cfg (path ++ (lbl2, idx2) :: suffix)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> strip_tac >>
  Cases_on `path`
  >- (gvs[livenessDefsTheory.cfg_exec_path_def]) >>
  gvs[livenessDefsTheory.cfg_exec_path_def] >>
  PairCases_on `h` >> gvs[livenessDefsTheory.cfg_exec_path_def]
QED

(* PHI instructions don't count as var_defined_at *)
Theorem not_var_defined_at_phi[local]:
  !bbs lbl idx v bb.
    lookup_block lbl bbs = SOME bb /\
    idx < LENGTH bb.bb_instructions /\
    (EL idx bb.bb_instructions).inst_opcode = PHI ==>
    ~var_defined_at bbs lbl idx v
Proof
  rw[livenessDefsTheory.var_defined_at_def]
QED

(* used_before_defined_prepend: no defs on prefix + ubd on suffix → ubd on whole *)
Theorem used_before_defined_prepend[local]:
  !prefix bbs v suffix.
    used_before_defined bbs v suffix /\
    (!j. j < LENGTH prefix ==>
       ~var_defined_at bbs (FST (EL j prefix)) (SND (EL j prefix)) v) ==>
    used_before_defined bbs v (prefix ++ suffix)
Proof
  rw[livenessDefsTheory.used_before_defined_def] >>
  qexists_tac `LENGTH prefix + k` >>
  simp[rich_listTheory.EL_APPEND2, rich_listTheory.EL_APPEND1] >>
  rpt strip_tac >>
  Cases_on `j < LENGTH prefix`
  >- (res_tac >> gvs[rich_listTheory.EL_APPEND1]) >>
  `j - LENGTH prefix < k` by simp[] >>
  `LENGTH prefix <= j` by simp[] >>
  gvs[rich_listTheory.EL_APPEND2]
QED

(* fn_cfg_edge implies cfg_succs_of membership under wf_function *)
Theorem fn_cfg_edge_cfg_succs[local]:
  !fn a b.
    wf_function fn /\ fn_cfg_edge fn a b ==>
    MEM b (cfg_succs_of (cfg_analyze fn) a)
Proof
  rw[fn_cfg_edge_def] >>
  irule (SIMP_RULE (srw_ss()) [LET_THM]
    cfgHelpersTheory.bb_succs_in_cfg_succs) >>
  fs[wf_function_def]
QED

(* Build cfg_exec_path along block-level is_fn_path, mapping each label to idx 0 *)
Theorem fn_path_to_cfg_exec_path_zeros[local]:
  !fn path cfg.
    wf_function fn /\ cfg = cfg_analyze fn /\
    is_fn_path fn path ==>
    cfg_exec_path cfg (MAP (\lbl. (lbl, 0:num)) path)
Proof
  gen_tac >> Induct >- simp[livenessDefsTheory.cfg_exec_path_def] >>
  rpt strip_tac >>
  Cases_on `path` >- simp[livenessDefsTheory.cfg_exec_path_def] >>
  fs[is_fn_path_def, livenessDefsTheory.cfg_exec_path_def] >>
  metis_tac[fn_cfg_edge_cfg_succs]
QED

(* Helper: ALL_DISTINCT on FLAT of list of lists means no element appears
   in two different sublists *)
Theorem all_distinct_flat_no_share[local]:
  !ls (x:'a) l1 l2.
    ALL_DISTINCT (FLAT ls) /\
    MEM l1 ls /\ MEM l2 ls /\ l1 <> l2 /\
    MEM x (l1:'a list) /\ MEM x l2 ==> F
Proof
  Induct >> simp[] >> rpt strip_tac >>
  fs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT] >>
  metis_tac[]
QED

(* Helper: ALL_DISTINCT labels + MEM bb → lookup finds bb *)
Theorem lookup_block_all_distinct_mem[local]:
  !bbs bb. ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
           MEM bb bbs ==>
    lookup_block bb.bb_label bbs = SOME bb
Proof
  Induct >> simp[lookup_block_def, listTheory.FIND_thm] >>
  rpt strip_tac >> gvs[] >>
  `bb.bb_label <> h.bb_label` by (
    spose_not_then strip_assume_tac >>
    `MEM bb.bb_label (MAP (\b. b.bb_label) bbs)` by
      (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
    gvs[]) >>
  fs[lookup_block_def]
QED

(* If ALL_DISTINCT (FLAT (MAP f ls)) and x in f(a) and x in f(b), then a = b *)
Theorem all_distinct_flat_map_inj[local]:
  !f (ls:'b list) (a:'b) (b:'b) (x:'a).
    ALL_DISTINCT (FLAT (MAP f ls)) /\
    MEM a ls /\ MEM b ls /\
    MEM x (f a) /\ MEM x (f b) ==> a = b
Proof
  Induct_on `ls` >> simp[] >> rpt strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* fn_insts_blocks = FLAT of per-block instructions *)
Theorem fn_insts_blocks_flat[local]:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* ALL_DISTINCT outputs → ALL_DISTINCT per-block flattened outputs *)
Theorem ssa_form_per_block[local]:
  !fn. ssa_form fn ==>
    ALL_DISTINCT (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs)
      bb.bb_instructions)) fn.fn_blocks))
Proof
  rpt strip_tac >>
  fs[ssa_form_def, fn_insts_def] >>
  pop_assum mp_tac >>
  ONCE_REWRITE_TAC [fn_insts_blocks_flat] >>
  simp[listTheory.MAP_FLAT, rich_listTheory.FLAT_FLAT,
       listTheory.MAP_MAP_o, combinTheory.o_DEF]
QED

(* Under ssa_form, v in outputs of two instructions → same instruction *)
Theorem ssa_outputs_same_inst:
  !fn inst1 inst2 v.
    ssa_form fn /\
    MEM inst1 (fn_insts_blocks fn.fn_blocks) /\
    MEM inst2 (fn_insts_blocks fn.fn_blocks) /\
    MEM v inst1.inst_outputs /\ MEM v inst2.inst_outputs ==>
    inst1 = inst2
Proof
  rpt strip_tac >>
  fs[ssa_form_def, fn_insts_def] >>
  mp_tac (Q.ISPECL [
    `\(i:instruction). i.inst_outputs`,
    `fn_insts_blocks fn.fn_blocks`,
    `inst1:instruction`, `inst2:instruction`, `v:string`
  ] all_distinct_flat_map_inj) >>
  simp[]
QED

Theorem lookup_block_label[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  Induct_on `bbs` >> rw[lookup_block_def, listTheory.FIND_thm] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Under ssa_form, var_defined_at for v determines the block and index *)
Theorem ssa_unique_var_defined_at[local]:
  !fn def_bb def_idx v lbl idx.
    wf_function fn /\ ssa_form fn /\
    MEM def_bb fn.fn_blocks /\
    def_idx < LENGTH def_bb.bb_instructions /\
    MEM v (EL def_idx def_bb.bb_instructions).inst_outputs /\
    var_defined_at fn.fn_blocks lbl idx v ==>
    lbl = def_bb.bb_label /\ idx = def_idx
Proof
  rpt gen_tac >> strip_tac >>
  fs[livenessDefsTheory.var_defined_at_def, inst_defs_def] >>
  (* bb = def_bb via all_distinct_flat_map_inj on per-block outputs *)
  mp_tac (Q.ISPECL [
    `\(bb:basic_block). FLAT (MAP (\(i:instruction). i.inst_outputs) bb.bb_instructions)`,
    `fn.fn_blocks`, `bb:basic_block`, `def_bb:basic_block`, `v:string`
  ] all_distinct_flat_map_inj) >>
  (impl_tac >- (
    drule ssa_form_per_block >> simp[] >> strip_tac >>
    simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
    metis_tac[venomExecPropsTheory.lookup_block_MEM, listTheory.MEM_EL])) >>
  disch_then (fn th => FULL_SIMP_TAC (srw_ss()) [th]) >>
  (* idx = def_idx via all_distinct_outputs_unique_pos *)
  mp_tac (Q.SPECL [`fn.fn_blocks`, `def_bb`] all_distinct_outputs_block) >>
  (impl_tac >- fs[ssa_form_def, fn_insts_def]) >>
  strip_tac >>
  conj_tac >- metis_tac[lookup_block_label] >>
  fs[ssa_form_def, fn_insts_def] >>
  metis_tac[all_distinct_outputs_unique_pos]
QED

(* ===== Operand condition from wf_ssa ===== *)

(* Extract definition info from single_pass_nop_outputs membership *)
Theorem nop_output_has_def[local]:
  !fn v.
    v IN single_pass_nop_outputs fn ==>
    ?def_bb def_idx.
      MEM def_bb fn.fn_blocks /\
      def_idx < LENGTH def_bb.bb_instructions /\
      MEM v (EL def_idx def_bb.bb_instructions).inst_outputs /\
      is_removable (EL def_idx def_bb.bb_instructions) /\
      ~MEM v (live_after_at (liveness_analyze fn) def_bb.bb_label def_idx
                (LENGTH def_bb.bb_instructions))
Proof
  rpt strip_tac >>
  gvs[single_pass_nop_outputs_def, LET_THM, block_nop_outputs_def] >>
  gvs[listTheory.MEM_MAP] >>
  rename1 `MEM def_bb fn.fn_blocks` >>
  gvs[listTheory.MEM_FLAT, indexedListsTheory.MEM_MAPi] >>
  rename1 `n < LENGTH def_bb.bb_instructions` >>
  pop_assum mp_tac >> BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  strip_tac >>
  qexistsl_tac [`def_bb`, `n`] >>
  gvs[listTheory.EVERY_MEM]
QED

(* Helper: v ∉ live_after_at implies v ∉ live_vars_at at SUC idx *)
Theorem nop_output_not_live_suc[local]:
  !fn def_bb def_idx v.
    def_idx < LENGTH def_bb.bb_instructions /\
    ~MEM v (live_after_at (liveness_analyze fn) def_bb.bb_label def_idx
              (LENGTH def_bb.bb_instructions)) ==>
    ~MEM v (live_vars_at (liveness_analyze fn) def_bb.bb_label (SUC def_idx))
Proof
  rpt strip_tac >>
  fs[live_after_at_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[arithmeticTheory.ADD1] >>
  `def_idx + 1 = LENGTH def_bb.bb_instructions` by simp[] >> gvs[]
QED

(* SSA: v not defined at positions other than its unique def *)
Theorem ssa_no_other_def[local]:
  !fn def_bb def_idx v lbl idx.
    wf_function fn /\ ssa_form fn /\
    MEM def_bb fn.fn_blocks /\
    def_idx < LENGTH def_bb.bb_instructions /\
    MEM v (EL def_idx def_bb.bb_instructions).inst_outputs /\
    (lbl <> def_bb.bb_label \/ idx <> def_idx) ==>
    ~var_defined_at fn.fn_blocks lbl idx v
Proof
  rpt strip_tac >>
  drule_all ssa_unique_var_defined_at >> gvs[]
QED

(* Split a list at the LAST occurrence of an element *)
Theorem last_occurrence_split[local]:
  !(l:'a list) d.
    MEM d l ==>
    ?prefix suffix. l = prefix ++ [d] ++ suffix /\ ~MEM d suffix
Proof
  Induct >> rw[] >-
   (Cases_on `MEM d l` >-
     (res_tac >> qexistsl_tac [`d::prefix`, `suffix`] >> gvs[]) >>
    qexistsl_tac [`[]`, `l`] >> gvs[]) >>
  res_tac >> qexistsl_tac [`h::prefix`, `suffix`] >> gvs[]
QED

(* Suffix of an is_fn_path is still an is_fn_path *)
Theorem is_fn_path_suffix[local]:
  !fn prefix suffix.
    is_fn_path fn (prefix ++ suffix) ==>
    is_fn_path fn suffix
Proof
  gen_tac >> Induct >- simp[] >>
  rpt strip_tac >>
  Cases_on `prefix` >- (
    gvs[] >> Cases_on `suffix` >> gvs[is_fn_path_def]) >>
  gvs[] >>
  Cases_on `t ++ suffix` >- (
    gvs[is_fn_path_def] >> Cases_on `suffix` >> gvs[is_fn_path_def]) >>
  gvs[is_fn_path_def]
QED

(* From dominance + reachability: path from d to n not revisiting d (except at start) *)
Theorem dominates_path_no_revisit[local]:
  !fn d n.
    wf_function fn /\ fn_dominates fn d n ==>
    ?path. is_fn_path fn (d :: path) /\ LAST (d :: path) = n /\ ~MEM d path
Proof
  rpt strip_tac >>
  fs[fn_dominates_def, fn_reachable_def] >>
  drule_then strip_assume_tac rtc_to_is_fn_path >>
  `MEM d path` by (
    first_x_assum (qspec_then `path` mp_tac) >> simp[]) >>
  drule_then strip_assume_tac last_occurrence_split >>
  `is_fn_path fn ([d] ++ suffix)` by (
    irule is_fn_path_suffix >> qexists_tac `prefix` >> fs[]) >>
  qexists_tac `suffix` >> gvs[] >>
  Cases_on `suffix` >>
  gvs[listTheory.LAST_DEF, listTheory.LAST_APPEND_CONS] >>
  `prefix ++ [d;h] ++ t = prefix ++ d :: h :: t` by simp[] >>
  simp[listTheory.LAST_APPEND_CONS, listTheory.LAST_DEF]
QED



(* Main bridge: NOP'd outputs are never used as operands in reachable blocks.
   Proof outline:
     - nop_output_has_def: v is output of removable inst at (def_bb, def_idx), not live after
     - nop_output_not_live_suc: v ∉ live_vars_at at (def_lbl, SUC def_idx)
     - live_vars_at_uses: v ∈ live_vars_at at (use_lbl, use_idx) from MEM (Var v) inst.inst_operands
     - Contrapositive of liveness_sound_proof: v ∉ live at p → ∀ cfg_exec_path from p: ¬ubd
     - Construct cfg_exec_path from (def_lbl, SUC def_idx) to (use_lbl, use_idx)
     - Show used_before_defined on this path (SSA unique def ≠ PHI excluded by var_defined_at)
     - Contradiction *)

(* ===== Function-level correctness ===== *)

(* ----- CFG reachability helpers ----- *)

(* Entry block label is in cfg_dfs_pre *)
Theorem entry_in_cfg_dfs_pre[local]:
  !fn. fn.fn_blocks <> [] ==>
    MEM (HD fn.fn_blocks).bb_label (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  simp[cfgHelpersTheory.cfg_analyze_dfs_pre, venomInstTheory.entry_block_def,
       listTheory.NULL_EQ] >>
  `SND (dfs_pre_walk (build_succs fn.fn_blocks) []
      (HD fn.fn_blocks).bb_label) <> [] /\
   HD (SND (dfs_pre_walk (build_succs fn.fn_blocks) []
      (HD fn.fn_blocks).bb_label)) = (HD fn.fn_blocks).bb_label` by
    simp[cfgHelpersTheory.dfs_pre_walk_entry_hd] >>
  Cases_on `SND (dfs_pre_walk (build_succs fn.fn_blocks) []
    (HD fn.fn_blocks).bb_label)` >> fs[]
QED

Theorem wf_lookup_block[local]:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==>
    lookup_block bb.bb_label fn.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  irule lookup_block_all_distinct_mem >> simp[] >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[venomWfTheory.wf_function_def] >>
  gvs[venomInstTheory.fn_labels_def]
QED

(* Wrapper: wf_function + fn_inst_wf → run_block successor stays in cfg_dfs_pre *)
Triviality wf_successor_in_cfg_dfs_pre:
  !fn bb fuel ctx s v.
    wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_current_bb = bb.bb_label /\ run_block fuel ctx bb s = OK v ==>
    MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  `!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> CCONTR_TAC >>
    `bb_well_formed bb'` by metis_tac[venomWfTheory.wf_function_def] >>
    fs[venomWfTheory.bb_well_formed_def] >>
    `i = PRE (LENGTH bb'.bb_instructions)` by
      (first_x_assum irule >> simp[]) >>
    fs[]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[venomWfTheory.fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `bb.bb_instructions <> []` by
    metis_tac[venomExecPropsTheory.run_block_ok_nonempty] >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecPropsTheory.run_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze fn) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs] >>
  imp_res_tac analysisSimPropsTheory.cfg_dfs_pre_succs_closed >>
  gvs[listTheory.EVERY_MEM]
QED

(* Two-state block sim for function, restricted to reachable blocks.
   Unlike block_sim_function / two_state_block_sim_function, the per-block
   hypothesis is only required for blocks whose label is in cfg_dfs_pre.
   This is needed because NOP'd variables in unreachable blocks may appear
   as operands in other unreachable blocks, breaking the operand condition.
   The proof maintains an invariant that vs_current_bb ∈ cfg_dfs_pre
   through the fuel induction. *)
Theorem two_state_block_sim_reachable[local]:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    wf_function fn /\ fn_inst_wf fn /\
    valid_state_rel R_ok R_term /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks /\
          MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre ==>
      !fuel ctx s1 s2.
        R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
        (?e. run_block fuel ctx bb s1 = Error e) \/
        lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                                 (run_block fuel ctx (bt bb) s2))
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      fn_entry_label fn = SOME s.vs_current_bb ==>
      (?e. run_blocks fuel ctx fn s = Error e) \/
      lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
                 (run_blocks fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    metis_tac[execEquivParamBaseTheory.vsr_R_ok_R_term] >>
  `!s1 s2. R_ok s1 s2 ==>
     (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by (
    rpt gen_tac >> disch_tac >>
    drule_all (REWRITE_RULE [GSYM AND_IMP_INTRO]
      execEquivParamBaseTheory.vsr_R_ok_fields) >>
    simp[]) >>
  `!fuel ctx s1 s2.
     R_ok s1 s2 /\ s1.vs_inst_idx = 0 /\
     MEM s1.vs_current_bb (cfg_analyze fn).cfg_dfs_pre ==>
     (?e. run_blocks fuel ctx fn s1 = Error e) \/
     lift_result R_ok R_term R_term (run_blocks fuel ctx fn s1)
       (run_blocks fuel ctx (function_map_transform bt fn) s2)`
  suffices_by (
    rpt strip_tac >>
    `R_ok s s` by
      (irule execEquivParamBaseTheory.vsr_R_ok_refl >> metis_tac[]) >>
    `MEM s.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by (
      `fn.fn_blocks <> []` by
        gvs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
      `s.vs_current_bb = (HD fn.fn_blocks).bb_label` by
        gvs[venomInstTheory.fn_entry_label_def,
            venomInstTheory.entry_block_def] >>
      metis_tac[entry_in_cfg_dfs_pre]) >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
    simp[]) >>
  Induct_on `fuel`
  >- (rw[] >> DISJ1_TAC >> qexists_tac `"out of fuel"` >>
      simp[venomExecSemanticsTheory.run_blocks_def]) >>
  rw[] >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.run_blocks_unfold] >>
  simp[passSimulationDefsTheory.function_map_transform_def,
       passSimulationPropsTheory.lookup_block_map] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- (DISJ1_TAC >> gvs[]) >>
  gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `bb.bb_label = s2.vs_current_bb` by metis_tac[lookup_block_label] >>
  `MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre` by gvs[] >>
  first_x_assum (qspec_then `bb` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s1`, `s2`] mp_tac) >> simp[] >>
  strip_tac
  >- (DISJ1_TAC >> qexists_tac `e` >> simp[]) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >- (
    `v'.vs_halted <=> v.vs_halted` by metis_tac[] >>
    Cases_on `v.vs_halted`
    >- (fs[] >> gvs[lift_result_def] >> metis_tac[]) >>
    fs[] >>
    gvs[lift_result_def,
        passSimulationDefsTheory.function_map_transform_def] >>
    `v.vs_inst_idx = 0` by
      metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
    `v'.vs_inst_idx = 0` by
      metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
    `MEM v.vs_current_bb (cfg_analyze fn).cfg_dfs_pre` by
      metis_tac[wf_successor_in_cfg_dfs_pre] >>
    first_x_assum irule >> metis_tac[])
QED


Triviality eval_phis_no_phi:
  !s l.
    (!i. i < LENGTH l ==> (EL i l).inst_opcode <> PHI) ==>
    eval_phis s l = OK s
Proof
  Induct_on `l` >- simp[eval_phis_def] >>
  rpt strip_tac >>
  `h.inst_opcode <> PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[eval_phis_def]
QED

Triviality eval_phis_filter_no_phi:
  !s P l.
    (!i. i < LENGTH l ==> (EL i l).inst_opcode <> PHI) ==>
    eval_phis s (FILTER P l) = OK s
Proof
  Induct_on `l` >- simp[eval_phis_def] >>
  rpt strip_tac >>
  Cases_on `P h` >> gvs[] >>
  `h.inst_opcode <> PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[eval_phis_def] >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Triviality eval_phis_remove_unused:
  !lr insts V s1 s2 s1'.
    state_equiv V s1 s2 /\
    (!inst v. MEM inst insts /\ MEM (Var v) inst.inst_operands ==> v NOTIN V) /\
    (!idx. idx < LENGTH insts /\
       remove_unused_inst (lr idx) (EL idx insts) =
       mk_nop_inst (EL idx insts) ==>
       set (EL idx insts).inst_outputs SUBSET V) /\
    (!i j. i < j /\ j < LENGTH insts /\
       (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) /\
    eval_phis s1 insts = OK s1' ==>
    ?s2'. eval_phis s2
       (FILTER (\inst. inst.inst_opcode <> NOP)
          (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)) = OK s2' /\
      state_equiv V s1' s2'
Proof
  rpt gen_tac >>
  MAP_EVERY qid_spec_tac [`s1'`, `s2`, `s1`, `V`, `lr`] >>
  Induct_on `insts`
  >- (rpt strip_tac >> qexists_tac `s2` >> gvs[eval_phis_def]) >>
  rpt strip_tac >>
  rename1 `h::t` >>
  simp[MAPi_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    fs[eval_phis_def] >>
    Cases_on `eval_one_phi s1 h` >> gvs[] >>
    PairCases_on `x` >> gvs[] >>
    Cases_on `eval_phis s1 t` >> gvs[] >>
    rename1 `eval_phis s1 t = OK s1_tail` >>
    `eval_one_phi s2 h = SOME (x0,x1)` by (
      irule eval_one_phi_state_equiv >> gvs[] >>
      rpt strip_tac >> metis_tac[]) >>
    qpat_x_assum `!lr0 V0 ss1 ss2 ss1'. _`
      (fn th => ASSUME_TAC th >> ASSUME_TAC th) >>
    Cases_on `remove_unused_inst (lr 0) h = h`
    >- (
      (* kept PHI *)
      `(!inst v. MEM inst t /\ MEM (Var v) inst.inst_operands ==> v NOTIN V)` by
        metis_tac[] >>
      `(!idx. idx < LENGTH t /\
          remove_unused_inst (lr (SUC idx)) (EL idx t) =
          mk_nop_inst (EL idx t) ==>
          set (EL idx t).inst_outputs SUBSET V)` by (
        rpt strip_tac >>
        qpat_x_assum `!idx. _ ==> set _ SUBSET V`
          (qspec_then `SUC idx` mp_tac) >> simp[]) >>
      `(!i j. i < j /\ j < LENGTH t /\ (EL j t).inst_opcode = PHI ==>
          (EL i t).inst_opcode = PHI)` by (
        rpt strip_tac >>
        qpat_x_assum `!i j. _ ==> _`
          (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      qpat_x_assum `!lr0 V0 ss1 ss2 ss1'. _`
        (fn th => mp_tac (Q.SPECL
          [`\idx. lr (SUC idx)`, `V`, `s1`, `s2`, `s1_tail`] th)) >>
      impl_tac >- (
        rpt conj_tac
        >- (qpat_x_assum `state_equiv V s1 s2` ACCEPT_TAC)
        >- (qpat_x_assum `!inst v. MEM inst t /\ _ ==> _` ACCEPT_TAC)
        >- (simp[] >> qpat_x_assum `!idx. idx < LENGTH t /\ _ ==> _` ACCEPT_TAC)
        >- (qpat_x_assum `!i j. i < j /\ j < LENGTH t /\ _ ==> _` ACCEPT_TAC)
        >- (qpat_x_assum `eval_phis s1 t = OK s1_tail` ACCEPT_TAC)) >>
      strip_tac >>
      `MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t =
       MAPi (\idx inst. remove_unused_inst (lr (SUC idx)) inst) t` by
        simp[combinTheory.o_DEF] >>
      gvs[mk_nop_inst_def] >>
      rename1 `eval_phis s2 _ = OK s2_tail` >>
      qexists_tac `update_var x0 x1 s2_tail` >>
      simp[eval_phis_def] >>
      rpt (conj_tac >- gvs[]) >>
      gvs[state_equiv_def, execution_equiv_def, update_var_def,
          lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rw[] >> gvs[]) >>
    (* removed PHI: its output is in V, so only original updates it *)
    `remove_unused_inst (lr 0) h = mk_nop_inst h` by
      metis_tac[remove_unused_inst_cases] >>
    `set h.inst_outputs SUBSET V` by (
      qpat_x_assum `!idx. idx < SUC (LENGTH t) /\ _ ==> _`
        (qspec_then `0` mp_tac) >> simp[]) >>
    `(!inst v. MEM inst t /\ MEM (Var v) inst.inst_operands ==> v NOTIN V)` by
      metis_tac[] >>
    `(!idx. idx < LENGTH t /\
        remove_unused_inst (lr (SUC idx)) (EL idx t) =
        mk_nop_inst (EL idx t) ==>
        set (EL idx t).inst_outputs SUBSET V)` by (
      rpt strip_tac >>
      qpat_x_assum `!idx. _ ==> set _ SUBSET V`
        (qspec_then `SUC idx` mp_tac) >> simp[]) >>
    `(!i j. i < j /\ j < LENGTH t /\ (EL j t).inst_opcode = PHI ==>
        (EL i t).inst_opcode = PHI)` by (
      rpt strip_tac >>
      qpat_x_assum `!i j. _ ==> _`
        (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
    qpat_x_assum `!lr0 V0 ss1 ss2 ss1'. _`
      (fn th => mp_tac (Q.SPECL
        [`\idx. lr (SUC idx)`, `V`, `s1`, `s2`, `s1_tail`] th)) >>
    impl_tac >- (BETA_TAC >> gvs[] >> metis_tac[]) >>
    strip_tac >>
    `MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t =
     MAPi (\idx inst. remove_unused_inst (lr (SUC idx)) inst) t` by
      simp[combinTheory.o_DEF] >>
    gvs[mk_nop_inst_def] >>
    rename1 `eval_phis s2 _ = OK s2_tail` >>
    fs[eval_one_phi_def, AllCaseEqs(), state_equiv_def,
       execution_equiv_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE, pred_setTheory.SUBSET_DEF] >>
    rw[] >> gvs[] >> metis_tac[]) >>
  (* h is not PHI: eval_phis stops on both sides; if h is removed, the tail
     has no PHIs by the prefix invariant, so transformed-tail eval_phis is OK. *)
  fs[eval_phis_def] >>
  qspecl_then [`lr 0`, `h`] strip_assume_tac
    remove_unused_inst_cases >> gvs[mk_nop_inst_def]
  >- (
    qexists_tac `s2` >>
    Cases_on `h.inst_opcode = NOP` >> gvs[eval_phis_def] >>
    irule eval_phis_filter_no_phi >> rpt strip_tac >>
    gvs[LENGTH_MAPi, EL_MAPi, combinTheory.o_DEF] >>
    qspecl_then [`lr (SUC i)`, `EL i t`]
      strip_assume_tac remove_unused_inst_cases >> gvs[mk_nop_inst_def] >>
    qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH t) /\ _ ==> _`
      (qspecl_then [`0`, `SUC i`] mp_tac) >> simp[]) >>
  last_x_assum (qspecl_then
    [`\idx. lr (SUC idx)`, `V`, `s1`, `s2`, `s1`] mp_tac) >>
  impl_tac >- (
    BETA_TAC >>
    rpt conj_tac
    >- (qpat_x_assum `state_equiv V s1 s2` ACCEPT_TAC)
    >- (rpt strip_tac >> metis_tac[])
    >- (rpt strip_tac >>
        qpat_x_assum `!idx. idx < SUC (LENGTH t) /\ _ ==> _`
          (qspec_then `SUC idx` mp_tac) >> simp[])
    >- (rpt strip_tac >>
        qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH t) /\ _ ==> _`
          (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
    >- (
      irule eval_phis_no_phi >> rpt strip_tac >>
      CCONTR_TAC >>
      qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH t) /\ _ ==> _`
        (qspecl_then [`0`, `SUC i`] mp_tac) >> simp[])) >>
  strip_tac >>
  qexists_tac `s2'` >> BETA_TAC >>
  `MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t =
   MAPi (\idx inst. remove_unused_inst (lr (SUC idx)) inst) t` by
    simp[combinTheory.o_DEF] >>
  gvs[]
QED

Triviality phi_prefix_length_no_phi:
  !l. (!i. i < LENGTH l ==> (EL i l).inst_opcode <> PHI) ==>
      phi_prefix_length l = 0
Proof
  Induct_on `l` >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  `h.inst_opcode <> PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[phi_prefix_length_def]
QED

Triviality phi_prefix_length_remove_unused_clear:
  !lr insts.
    (!i j. i < j /\ j < LENGTH insts /\ (EL j insts).inst_opcode = PHI ==>
       (EL i insts).inst_opcode = PHI) ==>
    phi_prefix_length (FILTER (\inst. inst.inst_opcode <> NOP)
      (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)) =
    LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
      (TAKE (phi_prefix_length insts)
        (MAPi (\idx inst. remove_unused_inst (lr idx) inst) insts)))
Proof
  rpt gen_tac >> qid_spec_tac `lr` >>
  Induct_on `insts` >- simp[phi_prefix_length_def] >>
  rpt strip_tac >> rename1 `h::t` >> simp[MAPi_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    simp[phi_prefix_length_def] >>
    `(!i j. i < j /\ j < LENGTH t /\ (EL j t).inst_opcode = PHI ==>
        (EL i t).inst_opcode = PHI)` by (
      rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
    first_x_assum (qspecl_then [`\idx. lr (SUC idx)`] mp_tac) >>
    impl_tac >- (qpat_x_assum `!i j. i < j /\ j < LENGTH t /\ _ ==> _` ACCEPT_TAC) >>
    strip_tac >>
    `MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t =
     MAPi (\idx inst. remove_unused_inst (lr (SUC idx)) inst) t` by
      simp[combinTheory.o_DEF] >>
    qspecl_then [`lr 0`, `h`] strip_assume_tac remove_unused_inst_cases >>
    gvs[mk_nop_inst_def, phi_prefix_length_def]) >>
  simp[phi_prefix_length_def] >>
  `(!i. i < LENGTH t ==> (EL i t).inst_opcode <> PHI)` by (
    rpt strip_tac >> CCONTR_TAC >>
    first_x_assum (qspecl_then [`0`, `SUC i`] mp_tac) >> simp[]) >>
  `(!i. i < LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
           (MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t)) ==>
        (EL i (FILTER (\inst. inst.inst_opcode <> NOP)
           (MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t))).inst_opcode <> PHI)` by (
    rpt strip_tac >>
    `MEM (EL i (FILTER (\inst. inst.inst_opcode <> NOP)
           (MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t)))
       (FILTER (\inst. inst.inst_opcode <> NOP)
           (MAPi ((\idx inst. remove_unused_inst (lr idx) inst) o SUC) t))` by
      metis_tac[listTheory.MEM_EL] >>
    gvs[listTheory.MEM_FILTER, MEM_MAPi] >>
    qspecl_then [`lr (SUC n)`, `EL n t`]
      strip_assume_tac remove_unused_inst_cases >> gvs[mk_nop_inst_def] >>
    first_x_assum (qspec_then `n` mp_tac) >> simp[]) >>
  qspecl_then [`lr 0`, `h`] strip_assume_tac remove_unused_inst_cases >>
  gvs[mk_nop_inst_def, phi_prefix_length_def] >>
  irule phi_prefix_length_no_phi >> rpt strip_tac >>
  Cases_on `h.inst_opcode = NOP` >> gvs[] >>
  Cases_on `i` >> gvs[] >> metis_tac[]
QED

Triviality clear_nops_block_label:
  !bb. (clear_nops_block bb).bb_label = bb.bb_label
Proof
  simp[passSharedDefsTheory.clear_nops_block_def]
QED

Theorem remove_unused_run_block_clear_sim[local]:
  !fuel ctx lr fence V bb s1 s2.
    bb_well_formed bb /\
    block_nop_outputs lr bb SUBSET V /\
    (!inst v. MEM inst bb.bb_instructions /\
              MEM (Var v) inst.inst_operands ==>
              v NOTIN V) /\
    s1.vs_inst_idx = 0 /\ state_equiv V s1 s2 ==>
    (?e. run_block fuel ctx bb s1 = Error e) \/
    lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
      (run_block fuel ctx bb s1)
      (run_block fuel ctx (clear_nops_block (remove_unused_block lr bb)) s2)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_TAC (Q.SPECL [`s1`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (
    pop_assum (qx_choose_then `s1_phi` (fn eval_ok_th =>
      ASSUME_TAC eval_ok_th >>
      mp_tac (Q.SPECL
        [`\idx. live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions)`,
         `bb.bb_instructions`, `V`, `s1`, `s2`, `s1_phi`]
        eval_phis_remove_unused) >>
      impl_tac >- (
        conj_tac >- metis_tac[] >>
        conj_tac >- (rpt strip_tac >> metis_tac[]) >>
        conj_tac >- (rpt strip_tac >> metis_tac[remove_unused_nop_outputs_subset]) >>
        conj_tac >- gvs[bb_well_formed_def] >>
        ACCEPT_TAC eval_ok_th) >>
      disch_then (qx_choose_then `s2_phi` strip_assume_tac))) >>
    gvs[passSharedDefsTheory.clear_nops_block_def, remove_unused_block_def] >>
    ASM_REWRITE_TAC[] >> simp[] >>
    mp_tac (Q.SPECL
      [`LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions`,
       `fuel`, `ctx`, `lr`, `V`, `bb`,
       `s1_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
       `s2_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
      remove_unused_block_sim) >>
    impl_tac >- (
      conj_tac >- simp[] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- (rpt strip_tac >> metis_tac[]) >>
      conj_tac >- simp[] >>
      metis_tac[execEquivProofsTheory.state_equiv_inst_idx]) >>
    strip_tac
    >- (DISJ1_TAC >> metis_tac[]) >>
    `LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
       (TAKE (phi_prefix_length bb.bb_instructions)
          (remove_unused_block lr bb).bb_instructions)) =
     phi_prefix_length (clear_nops_block (remove_unused_block lr bb)).bb_instructions` by (
      simp[passSharedDefsTheory.clear_nops_block_def, remove_unused_block_def] >>
      mp_tac (Q.SPECL
        [`\idx. live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions)`,
         `bb.bb_instructions`] phi_prefix_length_remove_unused_clear) >>
      impl_tac >- gvs[bb_well_formed_def] >>
      simp[]) >>
    `result_equiv {}
       (exec_block fuel ctx (remove_unused_block lr bb)
          (s2_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions))
       (exec_block fuel ctx (clear_nops_block (remove_unused_block lr bb))
          (s2_phi with vs_inst_idx :=
             phi_prefix_length (clear_nops_block (remove_unused_block lr bb)).bb_instructions))` by (
      mp_tac (Q.SPECL [`fuel`, `ctx`, `remove_unused_block lr bb`,
        `s2_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
        passSharedPropsTheory.clear_nops_block_gen) >>
      simp[]) >>
    DISJ2_TAC >>
    irule lift_result_compose_result_equiv >>
    qexists_tac `exec_block fuel ctx (remove_unused_block lr bb)
      (s2_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
    gvs[passSharedDefsTheory.clear_nops_block_def, remove_unused_block_def]) >>
  qpat_x_assum `?e. eval_phis s1 bb.bb_instructions = Error e` strip_assume_tac >>
  ASM_REWRITE_TAC[] >> DISJ1_TAC >> qexists_tac `e` >> simp[]
QED

(* Phase 1: function_map_transform preserves semantics up to
   state_equiv (single_pass_nop_outputs fn).
   Uses remove_unused_block_sim (non-SSA, fixed V) with the operand
   condition as a precondition. *)
Theorem remove_unused_phase1_correct[local]:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (* Operand condition: NOP'd outputs not used as operands *)
    (!bb inst v.
       MEM bb fn.fn_blocks /\
       MEM inst bb.bb_instructions /\
       MEM (Var v) inst.inst_operands ==>
       v NOTIN single_pass_nop_outputs fn) ==>
    let lr = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    let bt = \bb. remove_unused_block lr bb in
    let elim = single_pass_nop_outputs fn in
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (clear_nops_function (function_map_transform bt fn)) s)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  simp[passSharedDefsTheory.clear_nops_function_def,
       passSimulationDefsTheory.function_map_transform_def, listTheory.MAP_MAP_o,
       combinTheory.o_DEF] >>
  simp[GSYM passSimulationDefsTheory.function_map_transform_def] >>
  irule two_state_block_sim_reachable >>
  simp[remove_unused_block_label, clear_nops_block_label,
       execEquivParamProofsTheory.state_equiv_execution_equiv_valid_state_rel_proof] >>
  rpt strip_tac >>
  irule remove_unused_run_block_clear_sim >>
  rpt conj_tac
  >- metis_tac[]
  >- (gvs[wf_function_def] >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[])
  >- (mp_tac (SIMP_RULE std_ss [LET_THM]
        block_nop_outputs_subset_single_pass) >>
      disch_then (qspecl_then [`fn`, `bb`] mp_tac) >> simp[])
  >> first_assum ACCEPT_TAC
QED

(* Single-pass correctness: compose Phase 1 (NOP insertion) with
   Phase 2 (NOP cleanup via clear_nops_function_correct).
   The operand condition (NOP'd outputs not used as operands) is required
   as a precondition. It follows from SSA dominance + liveness soundness,
   but SSA dominance is not yet formalized. *)
Theorem remove_unused_single_pass_correct_proof:
  !fuel ctx fn s.
    venom_wf ctx /\ wf_function fn /\ fn_inst_wf fn /\
    alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!bb inst v.
       MEM bb fn.fn_blocks /\
       MEM inst bb.bb_instructions /\
       MEM (Var v) inst.inst_operands ==>
       v NOTIN single_pass_nop_outputs fn) ==>
    let elim = single_pass_nop_outputs fn in
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (remove_unused_single_pass fn) s)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  simp[remove_unused_single_pass_def, LET_THM] >>
  mp_tac (SPEC_ALL (SIMP_RULE std_ss [LET_THM] remove_unused_phase1_correct)) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac
  >- (DISJ1_TAC >> metis_tac[]) >>
  DISJ2_TAC >>
  first_assum ACCEPT_TAC
QED

(* lift_result reflexivity *)
Theorem lift_result_refl_state_equiv:
  !vars r.
    lift_result (state_equiv vars) (execution_equiv vars) (execution_equiv vars) r r
Proof
  gen_tac >> Cases >> simp[lift_result_def] >>
  metis_tac[stateEquivPropsTheory.state_equiv_refl,
            stateEquivPropsTheory.execution_equiv_refl]
QED

(* lift_result weakening for state_equiv/execution_equiv *)
Theorem lift_result_weaken_vars:
  !V1 V2 r1 r2.
    V1 SUBSET V2 /\
    lift_result (state_equiv V1) (execution_equiv V1) (execution_equiv V1) r1 r2 ==>
    lift_result (state_equiv V2) (execution_equiv V2) (execution_equiv V2) r1 r2
Proof
  rpt strip_tac >> irule lift_result_weaken >>
  qexistsl_tac [`state_equiv V1`, `execution_equiv V1`] >>
  rpt conj_tac
  >- (rpt strip_tac >> irule stateEquivPropsTheory.state_equiv_subset >>
      qexists_tac `V1` >> simp[])
  >- (rpt strip_tac >> irule stateEquivPropsTheory.execution_equiv_subset >>
      qexists_tac `V1` >> simp[])
  >- first_assum ACCEPT_TAC
QED

(* Helper: lift_result with Error on right forces Error on left *)
Theorem lift_result_error_right[local]:
  !R_ok R_term r e.
    lift_result R_ok R_term R_term r (Error e) ==> ?e'. r = Error e'
Proof
  Cases_on `r` >> simp[lift_result_def]
QED

(* General OWHILE + lift_result composition.
   Proves that if each step of an OWHILE loop either produces an error
   or refines the result via lift_result, then the full iteration does too.
   Isolates the OWHILE_IND induction to avoid variable shadowing issues.
   The caller should bake any OWHILE-reachability conditions into P. *)
Theorem owhile_lift_result_compose:
  !G f R_ok R_term Q P.
    (!x. R_ok x x) /\
    (!x. R_term x x) /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!x. G x /\ P x ==>
      (?e. Q x = Error e) \/
      lift_result R_ok R_term R_term (Q x) (Q (f x))) /\
    (!x. G x /\ P x ==> P (f x)) ==>
    !x y. OWHILE G f x = SOME y ==> P x ==>
      (?e. Q x = Error e) \/
      lift_result R_ok R_term R_term (Q x) (Q y)
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac WhileTheory.OWHILE_IND >> rpt conj_tac
  >- ((* Base case: ~G x, so y = x *)
    rpt gen_tac >> ntac 2 strip_tac >> DISJ2_TAC >>
    Cases_on `Q x` >> simp[lift_result_def])
  >> (* Step case: G x, IH for f x, need to compose *)
    rpt gen_tac >>
    disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
    strip_tac >>
    `(∃e. Q x = Error e) ∨ lift_result R_ok R_term R_term (Q x) (Q (f x))` by metis_tac[] >>
    `P (f x)` by metis_tac[] >>
    fs[]
    >- metis_tac[lift_result_error_right]
    >- (DISJ2_TAC >>
        Cases_on `Q (x:'a)` >> Cases_on `Q (f x)` >> Cases_on `Q (y:'a)` >>
        fs[lift_result_def] >> metis_tac[])
QED

(* Helper: step condition — each single pass step gives lift_result *)
Theorem owhile_step_condition[local]:
  !fuel ctx s elim x fn'.
    venom_wf ctx /\
    s.vs_inst_idx = 0 /\
    Abbrev (elim = remove_unused_eliminated_vars fn) /\
    remove_unused_single_pass x <> x /\
    OWHILE (\fn'. remove_unused_single_pass fn' <> fn')
      remove_unused_single_pass x = SOME fn' /\
    wf_function x /\ fn_inst_wf x /\ alloca_pointer_confined x /\
    fn_entry_label x = SOME s.vs_current_bb /\
    (!bb inst v.
       MEM bb x.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var v) inst.inst_operands ==>
       v NOTIN single_pass_nop_outputs x) /\
    single_pass_nop_outputs x SUBSET elim ==>
    (?e. run_blocks fuel ctx x s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_blocks fuel ctx x s)
      (run_blocks fuel ctx (remove_unused_single_pass x) s)
Proof
  rpt strip_tac >>
  mp_tac (SIMP_RULE std_ss [LET_THM]
            remove_unused_single_pass_correct_proof) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `x`, `s`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac
  >- (DISJ1_TAC >> metis_tac[]) >>
  DISJ2_TAC >> irule lift_result_weaken_vars >>
  qexists_tac `single_pass_nop_outputs x` >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Helper: one step of OWHILE *)
Theorem owhile_step[local]:
  !G f x r. G x /\ OWHILE G f x = SOME r ==> OWHILE G f (f x) = SOME r
Proof
  rpt strip_tac >>
  qpat_x_assum `OWHILE _ _ _ = _` mp_tac >>
  simp[Once WhileTheory.OWHILE_THM]
QED

(* Helper: preservation condition — invariant preserved by single pass *)
Theorem owhile_pres_condition[local]:
  !fn fn' elim s x.
    Abbrev (elim = remove_unused_eliminated_vars fn) /\
    (!fn_i. OWHILE (\fn'. remove_unused_single_pass fn' <> fn')
                    remove_unused_single_pass fn_i = SOME fn' ==>
      wf_function fn_i /\ fn_inst_wf fn_i /\ alloca_pointer_confined fn_i /\
      fn_entry_label fn_i = SOME s.vs_current_bb /\
      (!bb inst v.
         MEM bb fn_i.fn_blocks /\
         MEM inst bb.bb_instructions /\
         MEM (Var v) inst.inst_operands ==>
         v NOTIN single_pass_nop_outputs fn_i) /\
      single_pass_nop_outputs fn_i SUBSET elim) /\
    remove_unused_single_pass x <> x /\
    OWHILE (\fn'. remove_unused_single_pass fn' <> fn')
      remove_unused_single_pass x = SOME fn' ==>
    OWHILE (\fn'. remove_unused_single_pass fn' <> fn')
      remove_unused_single_pass (remove_unused_single_pass x) = SOME fn' /\
    wf_function (remove_unused_single_pass x) /\
    fn_inst_wf (remove_unused_single_pass x) /\
    alloca_pointer_confined (remove_unused_single_pass x) /\
    fn_entry_label (remove_unused_single_pass x) = SOME s.vs_current_bb /\
    (!bb inst v.
       MEM bb (remove_unused_single_pass x).fn_blocks /\
       MEM inst bb.bb_instructions /\
       MEM (Var v) inst.inst_operands ==>
       v NOTIN single_pass_nop_outputs (remove_unused_single_pass x)) /\
    single_pass_nop_outputs (remove_unused_single_pass x) SUBSET elim
Proof
  rpt gen_tac >> strip_tac >>
  (* Get OWHILE G f (f x) = SOME fn' from OWHILE G f x + G(x) *)
  (* Establish OWHILE G f (f x) = SOME fn' *)
  mp_tac (Q.ISPECL [
    `\g. remove_unused_single_pass g <> g`,
    `remove_unused_single_pass`,
    `x:ir_function`, `fn':ir_function`] owhile_step) >>
  (impl_tac >- (simp_tac std_ss [BETA_THM] >> fs[])) >>
  simp_tac std_ss [BETA_THM] >>
  strip_tac >>
  (* Apply extern assumption to f(x) *)
  qpat_x_assum `!fn_i. OWHILE _ _ fn_i = SOME _ ==> _`
    (qspec_then `remove_unused_single_pass x` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> fs[] >> first_assum ACCEPT_TAC
QED

(* Full iteration correctness via OWHILE_IND.
   Preconditions: the operand condition and structural invariants must hold
   for all intermediate functions reachable through OWHILE iteration.
   wf_function/fn_inst_wf/alloca_pointer_confined/fn_entry_label preservation is
   provable; the operand condition follows from SSA + liveness (the bridge
   requires SSA dominance, not yet formalized). *)
Theorem remove_unused_function_correct_proof:
  !fuel ctx fn s.
    venom_wf ctx /\ wf_function fn /\ fn_inst_wf fn /\
    alloca_pointer_confined fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    (!fn_i. OWHILE (\fn. remove_unused_single_pass fn <> fn)
                    remove_unused_single_pass fn_i =
            remove_unused_iterate fn ==>
      wf_function fn_i /\ fn_inst_wf fn_i /\ alloca_pointer_confined fn_i /\
      fn_entry_label fn_i = SOME s.vs_current_bb /\
      (!bb inst v.
         MEM bb fn_i.fn_blocks /\
         MEM inst bb.bb_instructions /\
         MEM (Var v) inst.inst_operands ==>
         v NOTIN single_pass_nop_outputs fn_i) /\
      single_pass_nop_outputs fn_i SUBSET
        remove_unused_eliminated_vars fn) ==>
    let elim = remove_unused_eliminated_vars fn in
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (remove_unused_function fn) s)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  simp[remove_unused_function_def] >>
  (Cases_on `remove_unused_iterate fn`
   >- simp[lift_result_refl_state_equiv]) >>
  (* SOME x: OWHILE G f fn = SOME x *)
  rename1 `remove_unused_iterate fn = SOME fn'` >>
  simp[] >>
  qabbrev_tac `elim = remove_unused_eliminated_vars fn` >>
  (* Apply owhile_lift_result_compose with explicit instantiation *)
  mp_tac (BETA_RULE (Q.ISPECL [
    `\fn'. remove_unused_single_pass fn' <> fn'`,
    `remove_unused_single_pass`,
    `state_equiv elim`,
    `execution_equiv elim`,
    `\fn_i. run_blocks fuel ctx fn_i s`
  ] owhile_lift_result_compose)) >>
  disch_then (qspec_then
    `\fn_i. OWHILE (\fn'. remove_unused_single_pass fn' <> fn')
                    remove_unused_single_pass fn_i = SOME fn' /\
            wf_function fn_i /\ fn_inst_wf fn_i /\ alloca_pointer_confined fn_i /\
            fn_entry_label fn_i = SOME s.vs_current_bb /\
            (!bb inst v. MEM bb fn_i.fn_blocks /\ MEM inst bb.bb_instructions /\
               MEM (Var v) inst.inst_operands ==>
               v NOTIN single_pass_nop_outputs fn_i) /\
            single_pass_nop_outputs fn_i SUBSET elim` mp_tac) >>
  simp_tac std_ss [BETA_THM] >>
  simp[stateEquivPropsTheory.state_equiv_refl,
       stateEquivPropsTheory.execution_equiv_refl] >>
  (* Discharge transitivity *)
  (SUBGOAL_THEN
    ``(!s1 s2 s3. state_equiv elim s1 s2 /\ state_equiv elim s2 s3 ==>
                  state_equiv elim s1 s3) /\
     (!s1 s2 s3. execution_equiv elim s1 s2 /\ execution_equiv elim s2 s3 ==>
                  execution_equiv elim s1 s3)``
    (fn th => REWRITE_TAC [th])
  >- metis_tac[stateEquivPropsTheory.state_equiv_trans,
               stateEquivPropsTheory.execution_equiv_trans]) >>
  strip_tac >>
  (* Step condition as standalone subgoal *)
  (SUBGOAL_THEN ``!x. remove_unused_single_pass x <> x /\
       OWHILE (\fn'. remove_unused_single_pass fn' <> fn')
         remove_unused_single_pass x = SOME fn' /\
       wf_function x /\ fn_inst_wf x /\ alloca_pointer_confined x /\
       fn_entry_label x = SOME s.vs_current_bb /\
       (!bb inst v. MEM bb x.fn_blocks /\ MEM inst bb.bb_instructions /\
          MEM (Var v) inst.inst_operands ==> v NOTIN single_pass_nop_outputs x) /\
       single_pass_nop_outputs x SUBSET elim ==>
       (?e. run_blocks fuel ctx x s = Error e) \/
       lift_result (state_equiv elim) (execution_equiv elim) (execution_equiv elim)
         (run_blocks fuel ctx x s)
         (run_blocks fuel ctx (remove_unused_single_pass x) s)``
    assume_tac
  >- (rpt strip_tac >> irule owhile_step_condition >>
      rpt conj_tac >> fs[] >> qexists_tac `fn` >> fs[])) >>
  (* Preservation condition as standalone subgoal *)
  (SUBGOAL_THEN ``!x. remove_unused_single_pass x <> x /\
       OWHILE (\fn'. remove_unused_single_pass fn' <> fn')
         remove_unused_single_pass x = SOME fn' /\
       wf_function x /\ fn_inst_wf x /\ alloca_pointer_confined x /\
       fn_entry_label x = SOME s.vs_current_bb /\
       (!bb inst v. MEM bb x.fn_blocks /\ MEM inst bb.bb_instructions /\
          MEM (Var v) inst.inst_operands ==> v NOTIN single_pass_nop_outputs x) /\
       single_pass_nop_outputs x SUBSET elim ==>
       OWHILE (\fn'. remove_unused_single_pass fn' <> fn')
         remove_unused_single_pass (remove_unused_single_pass x) = SOME fn' /\
       wf_function (remove_unused_single_pass x) /\
       fn_inst_wf (remove_unused_single_pass x) /\
       alloca_pointer_confined (remove_unused_single_pass x) /\
       fn_entry_label (remove_unused_single_pass x) = SOME s.vs_current_bb /\
       (!bb inst v. MEM bb (remove_unused_single_pass x).fn_blocks /\
          MEM inst bb.bb_instructions /\ MEM (Var v) inst.inst_operands ==>
          v NOTIN single_pass_nop_outputs (remove_unused_single_pass x)) /\
       single_pass_nop_outputs (remove_unused_single_pass x) SUBSET elim``
    assume_tac
  >- (rpt gen_tac >> strip_tac >>
      irule owhile_pres_condition >> fs[] >> metis_tac[])) >>
  (* Feed both to owhile implication *)
  qpat_x_assum `(_ /\ _) ==> _` mp_tac >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  (* Use the conclusion: specialize to fn *)
  disch_then (qspec_then `fn` mp_tac) >>
  (impl_tac >- fs[remove_unused_iterate_def]) >>
  (impl_tac >- (
    qpat_x_assum `!fn_i. OWHILE _ _ fn_i = SOME _ ==> wf_function _ /\ _`
      (qspec_then `fn` mp_tac) >>
    (impl_tac >- fs[remove_unused_iterate_def]) >>
    strip_tac >> fs[])) >>
  simp[]
QED

(* ===== Forward-preservation variant (no false universal) ===== *)

(* block_nop_outputs are a subset of the block's instruction outputs *)
Theorem block_nop_outputs_subset_block_outputs[local]:
  !lr bb.
    block_nop_outputs lr bb SUBSET
    set (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
  gvs[block_nop_outputs_def, LET_THM,
      listTheory.MEM_FLAT, indexedListsTheory.MEM_MAPi] >>
  pop_assum mp_tac >> IF_CASES_TAC >> gvs[] >>
  strip_tac >>
  simp[listTheory.MEM_MAP] >>
  metis_tac[listTheory.EL_MEM]
QED

(* single_pass_nop_outputs are a subset of fn_all_outputs *)
Theorem nop_outputs_subset_all_outputs:
  !fn. single_pass_nop_outputs fn SUBSET fn_all_outputs fn
Proof
  rw[single_pass_nop_outputs_def, fn_all_outputs_def, LET_THM,
     pred_setTheory.SUBSET_DEF] >>
  gvs[pred_setTheory.IN_BIGUNION, listTheory.MEM_MAP] >>
  rename1 `MEM bb fn.fn_blocks` >>
  mp_tac (Q.SPECL [`liveness_analyze fn`, `bb`]
    block_nop_outputs_subset_block_outputs) >>
  rw[pred_setTheory.SUBSET_DEF] >>
  first_x_assum drule >> strip_tac >>
  gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM_FLAT, listTheory.MEM_MAP]
QED

(* remove_unused_inst outputs: either same or empty *)
Theorem remove_unused_inst_outputs[local]:
  !live inst.
    (remove_unused_inst live inst).inst_outputs = inst.inst_outputs \/
    (remove_unused_inst live inst).inst_outputs = []
Proof
  rw[remove_unused_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  simp[mk_nop_inst_def]
QED

(* remove_unused_block outputs are subset of original block outputs *)
Theorem remove_unused_block_outputs_subset[local]:
  !lr bb.
    set (FLAT (MAP (\inst. inst.inst_outputs)
      (remove_unused_block lr bb).bb_instructions)) SUBSET
    set (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  rpt gen_tac >>
  simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
  gvs[remove_unused_block_def, LET_THM,
      listTheory.MEM_FLAT, listTheory.MEM_MAP,
      indexedListsTheory.MEM_MAPi] >>
  rename1 `n < LENGTH bb.bb_instructions` >>
  qpat_x_assum `MEM x _` mp_tac >>
  simp[remove_unused_inst_def] >>
  rpt (IF_CASES_TAC >> simp[mk_nop_inst_def]) >>
  metis_tac[listTheory.EL_MEM]
QED

(* clear_nops_block outputs are subset of original block outputs *)
Theorem clear_nops_block_outputs_subset[local]:
  !bb.
    set (FLAT (MAP (\inst. inst.inst_outputs)
      (clear_nops_block bb).bb_instructions)) SUBSET
    set (FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
Proof
  rw[clear_nops_block_def, pred_setTheory.SUBSET_DEF,
     listTheory.MEM_FLAT, listTheory.MEM_MAP, listTheory.MEM_FILTER] >>
  metis_tac[]
QED

(* rusp outputs are subset of original outputs *)
Theorem rusp_all_outputs_subset:
  !fn. fn_all_outputs (remove_unused_single_pass fn) SUBSET fn_all_outputs fn
Proof
  gen_tac >>
  simp[fn_all_outputs_def, pred_setTheory.SUBSET_DEF] >>
  rpt strip_tac >>
  fs[remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def,
     passSimulationDefsTheory.function_map_transform_def,
     listTheory.MEM_FLAT, listTheory.MEM_MAP, listTheory.MAP_MAP_o,
     combinTheory.o_DEF] >>
  rename1 `MEM bbo _.fn_blocks` >>
  `MEM x (FLAT (MAP (\inst. inst.inst_outputs) bbo.bb_instructions))` by (
    gvs[] >>
    imp_res_tac (SRULE [pred_setTheory.SUBSET_DEF] clear_nops_block_outputs_subset) >>
    imp_res_tac (SRULE [pred_setTheory.SUBSET_DEF] remove_unused_block_outputs_subset)) >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

(* SSA outputs uniqueness: same output variable → same (block, position).
   Combines all_distinct_flat_map_inj (cross-block) with
   all_distinct_outputs_unique_pos (within-block). *)
Theorem ssa_form_position[local]:
  !fn bb1 n bb2 m v.
    ssa_form fn /\
    MEM bb1 fn.fn_blocks /\ n < LENGTH bb1.bb_instructions /\
    MEM v (EL n bb1.bb_instructions).inst_outputs /\
    MEM bb2 fn.fn_blocks /\ m < LENGTH bb2.bb_instructions /\
    MEM v (EL m bb2.bb_instructions).inst_outputs ==>
    bb1 = bb2 /\ n = m
Proof
  rpt gen_tac >> strip_tac >>
  (* Cross-block: bb1 = bb2 *)
  `bb1 = bb2` by (
    mp_tac (Q.ISPECL [
      `\(bb:basic_block). FLAT (MAP (\(i:instruction). i.inst_outputs) bb.bb_instructions)`,
      `fn.fn_blocks`, `bb1:basic_block`, `bb2:basic_block`, `v:string`
    ] all_distinct_flat_map_inj) >>
    (impl_tac >- (
      drule ssa_form_per_block >> simp[] >> strip_tac >>
      simp[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
      metis_tac[listTheory.EL_MEM])) >>
    simp[]) >>
  fs[] >>
  (* Within-block: n = m *)
  irule all_distinct_outputs_unique_pos >>
  qexistsl_tac [`bb1.bb_instructions`, `v`] >> simp[] >>
  irule all_distinct_outputs_block >>
  qexists_tac `fn.fn_blocks` >> simp[] >>
  fs[ssa_form_def, fn_insts_def]
QED

(* NOP'd instruction outputs are removed by rusp.
   Key insight: SSA uniqueness means each variable is defined at exactly one
   (block, position). If that position is NOP'd, no other instruction defines
   the variable, so it disappears from all outputs. *)
Theorem nop_outputs_not_in_rusp:
  !fn v. wf_function fn /\ ssa_form fn /\
         v IN single_pass_nop_outputs fn ==>
         v NOTIN fn_all_outputs (remove_unused_single_pass fn)
Proof
  rpt gen_tac >> strip_tac >>
  (* Step 1: Extract NOP'd position (bb, n) from single_pass_nop_outputs *)
  fs[single_pass_nop_outputs_def, LET_THM] >>
  gvs[pred_setTheory.IN_BIGUNION, listTheory.MEM_MAP] >>
  rename1 `MEM bb _.fn_blocks` >>
  fs[block_nop_outputs_def, LET_THM] >>
  gvs[listTheory.MEM_FLAT, indexedListsTheory.MEM_MAPi] >>
  qpat_x_assum `MEM v _` mp_tac >> IF_CASES_TAC >> gvs[] >> strip_tac >>
  rename1 `n < LENGTH bb.bb_instructions` >>
  (* Step 2: Proof by contradiction — assume v ∈ fn_all_outputs(rusp fn) *)
  SPOSE_NOT_THEN ASSUME_TAC >>
  fs[fn_all_outputs_def, remove_unused_single_pass_def, LET_THM,
     clear_nops_function_def,
     passSimulationDefsTheory.function_map_transform_def,
     listTheory.MAP_MAP_o, combinTheory.o_DEF,
     listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rename1 `MEM bb' _.fn_blocks` >>
  (* Step 3: v appears in some transformed block outputs — extract position m *)
  gvs[clear_nops_block_def, listTheory.MEM_FILTER,
      remove_unused_block_def, LET_THM,
      indexedListsTheory.MEM_MAPi, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rename1 `m < LENGTH bb'.bb_instructions` >>
  (* Step 4: Outputs of transformed inst are either original or [].
     Since v ∈ outputs, must be original. *)
  `(remove_unused_inst
      (live_after_at (liveness_analyze fn) bb'.bb_label m
         (LENGTH bb'.bb_instructions))
      (EL m bb'.bb_instructions)).inst_outputs =
    (EL m bb'.bb_instructions).inst_outputs` by (
    mp_tac (Q.SPECL [
      `live_after_at (liveness_analyze fn) bb'.bb_label m
         (LENGTH bb'.bb_instructions)`,
      `EL m bb'.bb_instructions`] remove_unused_inst_outputs) >>
    strip_tac >> gvs[]) >>
  (* So v ∈ (EL m bb'.bb_instructions).inst_outputs *)
  fs[] >>
  (* Step 5: Position uniqueness — bb = bb' ∧ n = m *)
  (`bb = bb' /\ n = m` by
    metis_tac[ssa_form_position]) >>
  gvs[] >>
  (* Step 6: Contradiction — same remove_unused_inst call, but NOP'd (step 1)
     says is_removable ∧ dead, while kept (step 4) says it returns original. *)
  qpat_x_assum `_ = (EL n bb.bb_instructions).inst_outputs` mp_tac >>
  simp[remove_unused_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[mk_nop_inst_def]) >>
  simp[mk_nop_inst_def] >>
  metis_tac[listTheory.MEM]
QED


(* Two functions that differ only by NOP replacement of a dead ASSIGN.
   This demonstrates that pass_correct {} (which requires ALL variables
   to agree at termination) is too strong for remove_unused, because
   NOP'd variables retain their old values in the transformed program. *)

(* Original: ASSIGN v1 := 42, then STOP *)
Definition cx_ru_fn1_def:
  cx_ru_fn1 = mk_raw_function "test_fn"
    [basic_block "entry"
      [instruction 0 ASSIGN [Lit 42w] ["v1"];
       instruction 1 STOP [] []]]
End

(* Transformed: NOP (v1 assignment removed), then STOP *)
Definition cx_ru_fn2_def:
  cx_ru_fn2 = mk_raw_function "test_fn"
    [basic_block "entry"
      [instruction 0 NOP [] [];
       instruction 1 STOP [] []]]
End

(* Both functions satisfy wf_ssa (vacuously: no variable uses) *)
Theorem cx_ru_fn1_wf_ssa[local]:
  wf_ssa cx_ru_fn1
Proof
  simp[venomWfTheory.wf_ssa_def, cx_ru_fn1_def,
       venomWfTheory.ssa_form_def,
       venomWfTheory.def_dominates_uses_def] >>
  EVAL_TAC >> simp[] >> rpt strip_tac >> gvs[]
QED

(* pass_correct {} is FALSE between fn1 and fn2.
   Original halts with vs_vars("v1") = 42w.
   Transformed halts with vs_vars("v1") unchanged.
   execution_equiv {} requires all vars equal => fails on "v1". *)
(* pass_correct {} is FALSE: original halts with v1=42w,
   transformed halts with v1 unchanged => execution_equiv {} fails on "v1" *)
Theorem pass_correct_empty_false_for_nop[local]:
  ~pass_correct (state_equiv {}) (execution_equiv {}) (execution_equiv {})
    (\fuel. run_blocks fuel ARB cx_ru_fn1
       ((init_venom_state "entry") with <|vs_vars := FEMPTY;
                   vs_current_bb := "entry"; vs_inst_idx := 0; vs_halted := F|>))
    (\fuel. run_blocks fuel ARB cx_ru_fn2
       ((init_venom_state "entry") with <|vs_vars := FEMPTY;
                   vs_current_bb := "entry"; vs_inst_idx := 0; vs_halted := F|>))
Proof
  simp[passSimulationDefsTheory.pass_correct_def,
       cx_ru_fn1_def, cx_ru_fn2_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  simp[passSimulationDefsTheory.terminates_def] >>
  strip_tac >>
  qexistsl_tac [`SUC 0`, `SUC 0`] >>
  EVAL_TAC >>
  simp[stateEquivTheory.lift_result_def,
       stateEquivTheory.execution_equiv_def]
QED

