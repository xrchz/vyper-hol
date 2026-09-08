(*
 * DFT Block Simulation — Infrastructure
 *
 * Key lemma: independent_commute_eq — bilateral-independent non-terminator
 * instructions produce identical final states when executed in either order.
 *)

Theory dftBlockSim
Ancestors
  dftDefs dftCommutation passSharedProps passSharedTransfer
  passSharedField venomExecSemantics venomExecProps venomEffects venomInstProofs
  venomMemProofs venomState finite_map venomInst stateEquiv stateEquivProps
  passSimulationDefs venomInstProps pred_set sorting passSharedFrame
  vfmState venomWf

(* ================================================================
   1. step_inst preserves vs_allocas and vs_alloca_next for
      non-terminator, non-alloca, non-ext_call instructions
      (including INVOKE)
   ================================================================ *)

Theorem step_inst_preserves_allocas:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE case: merge_callee_state keeps caller's allocas,
       bind_outputs only does update_var which preserves allocas *)
    gvs[step_inst_def, AllCaseEqs()] >>
    `!pairs ss. (FOLDL (\s' (out,val). update_var out val s') ss pairs
      ).vs_allocas = ss.vs_allocas` by
      (Induct >> rw[] >> Cases_on `h` >> simp[update_var_def]) >>
    gvs[bind_outputs_def, AllCaseEqs(), merge_callee_state_def,
        adopt_return_fmp_allocas])
  >>
  gvs[step_inst_non_invoke] >>
  `inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  qspecl_then [`inst`, `s`, `s'`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_allocas >>
  impl_tac >- simp[] >>
  simp[]
QED

Theorem step_inst_preserves_alloca_next:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    s'.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  `inst.inst_opcode <> ALLOCA` by
    (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]) >>
  qspecl_then [`inst`, `s`, `s'`] mp_tac
    venomMemProofsTheory.step_inst_base_preserves_alloca_next >>
  impl_tac >- simp[] >>
  simp[]
QED

(* ================================================================
   2. commute_equiv + allocas + alloca_next + vars → full equality
   ================================================================ *)

(* Two states that are commute_equiv on a defs set and also agree on
   vs_allocas, vs_alloca_next, and all variables in defs are equal. *)
Theorem commute_equiv_allocas_vars_eq:
  !defs s1 s2.
    commute_equiv defs s1 s2 /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    (!w. w IN defs ==> lookup_var w s1 = lookup_var w s2) ==>
    s1 = s2
Proof
  rw[commute_equiv_def, venom_state_component_equality, fmap_eq_flookup] >>
  simp[GSYM lookup_var_def] >> rename1 `lookup_var w` >>
  Cases_on `w IN defs` >> metis_tac[]
QED

(* ================================================================
   3. Operand variables membership
   ================================================================ *)

(* If Var x appears in an operand list, then x is in operand_vars of that list. *)
Theorem mem_var_operand_vars:
  !x ops. MEM (Var x) ops ==> MEM x (operand_vars ops)
Proof
  Induct_on `ops` >> rw[operand_vars_def] >>
  gvs[operand_var_def] >>
  Cases_on `h` >> gvs[operand_var_def]
QED

(* ================================================================
   4. eval_operand preserved by step on non-output vars
   ================================================================ *)

Theorem eval_operand_step_pres:
  !fuel ctx inst s s' op.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (!x. op = Var x ==> ~MEM x inst.inst_outputs) ==>
    eval_operand op s' = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def]
  >- metis_tac[step_preserves_non_output_vars]
  >> metis_tac[step_preserves_labels]
QED

(* ================================================================
   5. Effect field preservation from effects_independent
   ================================================================ *)

(* effects_independent implies three-way disjointness of effects:
   write(a) ∩ read(b) = ∅, write(b) ∩ read(a) = ∅, write(a) ∩ write(b) = ∅ *)
Theorem effects_independent_write_read_disjoint:
  !op1 op2.
    effects_independent op1 op2 ==>
    DISJOINT (write_effects op1) (read_effects op2) /\
    DISJOINT (write_effects op2) (read_effects op1) /\
    DISJOINT (write_effects op1) (write_effects op2)
Proof
  simp[effects_independent_def] >> rpt strip_tac >>
  metis_tac[DISJOINT_SYM, SUBSET_DEF, IN_UNION, DISJOINT_DEF, EXTENSION]
QED

(* ================================================================
   6. Eligible step_inst preserves structural and effect-conditional fields
   ================================================================ *)

(* A non-terminator, non-alloca, non-ext_call, non-INVOKE step preserves all
   structural state fields; effect-conditional fields (memory, transient,
   accounts, etc.) are preserved when the corresponding effect is not written. *)
Theorem step_inst_preserves_eligible_fields:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_code = s.vs_code /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
      s'.vs_memory = s.vs_memory) /\
    (Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
      s'.vs_transient = s.vs_transient) /\
    (Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
     Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
      s'.vs_accounts = s.vs_accounts) /\
    (Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
      s'.vs_immutables = s.vs_immutables) /\
    (Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
      s'.vs_returndata = s.vs_returndata) /\
    (Eff_LOG NOTIN write_effects inst.inst_opcode ==>
      s'.vs_logs = s.vs_logs)
Proof
  rpt strip_tac >>
  drule_all step_inst_preserves_all >> strip_tac >> gvs[]
QED

(* ================================================================
   7. Eligible write constraints — certain effects are never written
      by non-terminator, non-alloca, non-ext_call, non-INVOKE ops.
   ================================================================ *)

Theorem eligible_write_constraints[local]:
  !op. ~is_terminator op /\ ~is_alloca_op op /\
       ~is_ext_call_op op /\ op <> INVOKE ==>
       Eff_BALANCE NOTIN write_effects op /\
       Eff_EXTCODE NOTIN write_effects op /\
       Eff_RETURNDATA NOTIN write_effects op
Proof
  Cases >> EVAL_TAC
QED

(* ================================================================
   7b. Account sub-field preservation for eligible instructions.
       SSTORE is the only eligible op that writes Eff_STORAGE,
       and it only modifies .storage — balance, nonce, code are
       always preserved by eligible ops.
   ================================================================ *)

Theorem step_inst_preserves_account_bnc[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    !addr. (s'.vs_accounts addr).balance = (s.vs_accounts addr).balance /\
           (s'.vs_accounts addr).nonce = (s.vs_accounts addr).nonce /\
           (s'.vs_accounts addr).code = (s.vs_accounts addr).code
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  Cases_on `Eff_STORAGE IN write_effects inst.inst_opcode`
  >- (
    (* Only SSTORE writes STORAGE among eligible ops *)
    `inst.inst_opcode = SSTORE` by (
      Cases_on `inst.inst_opcode` >>
      gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
          write_effects_def, all_effects_def, empty_effects_def]) >>
    gvs[step_inst_non_invoke, step_inst_base_def, exec_write2_def,
        AllCaseEqs()] >>
    simp[sstore_def, lookup_account_def, LET_THM,
         combinTheory.APPLY_UPDATE_THM] >>
    rw[])
  >- (
    (* No STORAGE write: full vs_accounts preserved *)
    `Eff_BALANCE NOTIN write_effects inst.inst_opcode` by
      metis_tac[eligible_write_constraints] >>
    imp_res_tac step_inst_preserves_eligible_fields >> gvs[])
QED

(* Effect-free account-reading ops: exactly BALANCE/SELFBALANCE/EXTCODESIZE/EXTCODEHASH *)
Triviality effect_free_account_read_opcodes[local]:
  !op. is_effect_free_op op /\
    (Eff_BALANCE IN read_effects op \/ Eff_EXTCODE IN read_effects op) ==>
    op = BALANCE \/ op = SELFBALANCE \/ op = EXTCODESIZE \/ op = EXTCODEHASH
Proof Cases >> EVAL_TAC
QED

(* Account-reading opcodes: output values depend only on
   account sub-fields (balance/nonce/code) and call_ctx,
   NOT on full vs_accounts record equality. *)
Triviality account_read_output_agree[local]:
  !inst s1 s2 r1 r2 w.
    step_inst_base inst s1 = OK r1 /\
    step_inst_base inst s2 = OK r2 /\
    (inst.inst_opcode = BALANCE \/ inst.inst_opcode = SELFBALANCE \/
     inst.inst_opcode = EXTCODESIZE \/ inst.inst_opcode = EXTCODEHASH) /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!addr. (s1.vs_accounts addr).balance =
            (s2.vs_accounts addr).balance /\
            (s1.vs_accounts addr).nonce =
            (s2.vs_accounts addr).nonce /\
            (s1.vs_accounts addr).code =
            (s2.vs_accounts addr).code) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    MEM w inst.inst_outputs ==>
    lookup_var w r1 = lookup_var w r2
Proof
  rpt strip_tac >>
  (Cases_on `inst.inst_opcode` >> gvs[])
  >- (qpat_x_assum `step_inst_base inst s1 = OK r1` mp_tac >>
      qpat_x_assum `step_inst_base inst s2 = OK r2` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[exec_read1_def] >>
      rpt strip_tac >>
      gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          lookup_account_def] >> metis_tac[])
  >- (qpat_x_assum `step_inst_base inst s1 = OK r1` mp_tac >>
      qpat_x_assum `step_inst_base inst s2 = OK r2` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[exec_read0_def] >>
      rpt strip_tac >>
      gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          lookup_account_def] >> metis_tac[])
  >- (qpat_x_assum `step_inst_base inst s1 = OK r1` mp_tac >>
      qpat_x_assum `step_inst_base inst s2 = OK r2` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[exec_read1_def] >>
      rpt strip_tac >>
      gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE,
          lookup_account_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base inst s1 = OK r1` mp_tac >>
  qpat_x_assum `step_inst_base inst s2 = OK r2` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[exec_read1_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      lookup_account_def, account_empty_def] >> metis_tac[]
QED

Triviality account_read_step_output_agree[local]:
  !fuel ctx inst ss vb va sba w.
    step_inst fuel ctx inst ss = OK va /\
    step_inst fuel ctx inst vb = OK sba /\
    is_effect_free_op inst.inst_opcode /\
    (Eff_BALANCE IN read_effects inst.inst_opcode \/
     Eff_EXTCODE IN read_effects inst.inst_opcode) /\
    inst.inst_opcode <> INVOKE /\
    (!op. MEM op inst.inst_operands ==> eval_operand op ss = eval_operand op vb) /\
    (!addr. (vb.vs_accounts addr).balance =
            (ss.vs_accounts addr).balance /\
            (vb.vs_accounts addr).nonce =
            (ss.vs_accounts addr).nonce /\
            (vb.vs_accounts addr).code =
            (ss.vs_accounts addr).code) /\
    vb.vs_call_ctx = ss.vs_call_ctx /\
    MEM w inst.inst_outputs ==>
    lookup_var w va = lookup_var w sba
Proof
  rpt strip_tac >>
  `step_inst_base inst ss = OK va` by metis_tac[step_inst_non_invoke] >>
  `step_inst_base inst vb = OK sba` by metis_tac[step_inst_non_invoke] >>
  `!addr. (ss.vs_accounts addr).balance =
          (vb.vs_accounts addr).balance /\
          (ss.vs_accounts addr).nonce =
          (vb.vs_accounts addr).nonce /\
          (ss.vs_accounts addr).code =
          (vb.vs_accounts addr).code` by metis_tac[] >>
  `ss.vs_call_ctx = vb.vs_call_ctx` by metis_tac[] >>
  `inst.inst_opcode = BALANCE \/ inst.inst_opcode = SELFBALANCE \/
   inst.inst_opcode = EXTCODESIZE \/ inst.inst_opcode = EXTCODEHASH` by
    (irule effect_free_account_read_opcodes >> ASM_REWRITE_TAC[]) >>
  gvs[] >>
  qspecl_then [`inst`, `ss`, `vb`, `va`, `sba`, `w`] mp_tac
    account_read_output_agree >>
  ASM_REWRITE_TAC[]
QED

(* Non-effect-free eligible ops other than DALLOCA preserve all vars.
   Side-effect-only ops (MSTORE, SSTORE, MCOPY, LOG, ASSERT, etc.) leave
   vs_vars untouched; DALLOCA returns the old FMP via its declared output and
   is handled separately by dalloca_step_output_agree. *)
Triviality side_effect_lookup_var[local]:
  (!off bytes s v.
     lookup_var v (write_memory_with_expansion off bytes s) = lookup_var v s) /\
  (!off val s v. lookup_var v (mstore off val s) = lookup_var v s) /\
  (!off val s v. lookup_var v (istore off val s) = lookup_var v s) /\
  (!off val s v. lookup_var v (mstore8 off val s) = lookup_var v s) /\
  (!dst src sz s v. lookup_var v (mcopy dst src sz s) = lookup_var v s) /\
  (!key val s v. lookup_var v (sstore key val s) = lookup_var v s) /\
  (!key val s v. lookup_var v (tstore key val s) = lookup_var v s) /\
  (!s v. lookup_var v (halt_state s) = lookup_var v s) /\
  (!s v. lookup_var v (revert_state s) = lookup_var v s) /\
  (!rd s v. lookup_var v (set_returndata rd s) = lookup_var v s)
Proof
  rw[write_memory_with_expansion_def, mstore_def, istore_def, mstore8_def,
     mcopy_def, sstore_def, tstore_def, halt_state_def,
     revert_state_def, set_returndata_def, lookup_var_def]
QED

(* A successful DALLOCA writes the input free-memory pointer to its sole output. *)
Triviality dalloca_base_output_lookup[local]:
  !inst s r w.
    inst.inst_opcode = DALLOCA /\
    step_inst_base inst s = OK r /\
    MEM w inst.inst_outputs ==>
    lookup_var w r = SOME s.vs_fmp
Proof
  rpt strip_tac >>
  gvs[Once step_inst_base_def, AllCaseEqs(), update_var_def,
      lookup_var_def, FLOOKUP_UPDATE]
QED

Triviality dalloca_step_output_agree[local]:
  !fuel ctx inst s1 s2 r1 r2 w.
    step_inst fuel ctx inst s1 = OK r1 /\
    step_inst fuel ctx inst s2 = OK r2 /\
    inst.inst_opcode = DALLOCA /\
    s1.vs_fmp = s2.vs_fmp /\
    MEM w inst.inst_outputs ==>
    lookup_var w r1 = lookup_var w r2
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `step_inst_base inst s1 = OK r1` by metis_tac[step_inst_non_invoke] >>
  `step_inst_base inst s2 = OK r2` by metis_tac[step_inst_non_invoke] >>
  metis_tac[dalloca_base_output_lookup]
QED

Theorem step_non_effect_free_preserves_all_vars[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_effect_free_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> DALLOCA ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_effect_free_op_def, is_terminator_def,
      is_alloca_op_def, is_ext_call_op_def] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = op`
    (fn th => PURE_REWRITE_TAC[th]) >>
  simp[] >>
  simp[exec_write2_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  simp[side_effect_lookup_var, lookup_var_def]
QED

(* ================================================================
   8. Output var agreement across independent instructions
      If inst_a writes w, and inst_b is independent from inst_a,
      then lookup_var w agrees in both execution orders.
   ================================================================ *)

Theorem output_var_agree_across_independent:
  !fuel ctx inst_a inst_b ss va vb sab sba w.
    step_inst fuel ctx inst_a ss = OK va /\
    step_inst fuel ctx inst_b ss = OK vb /\
    step_inst fuel ctx inst_b va = OK sab /\
    step_inst fuel ctx inst_a vb = OK sba /\
    DISJOINT (set inst_a.inst_outputs) (set inst_b.inst_outputs) /\
    DISJOINT (set inst_b.inst_outputs)
             (set (operand_vars inst_a.inst_operands)) /\
    effects_independent inst_a.inst_opcode inst_b.inst_opcode /\
    ~is_terminator inst_a.inst_opcode /\ ~is_terminator inst_b.inst_opcode /\
    ~is_alloca_op inst_a.inst_opcode /\ ~is_alloca_op inst_b.inst_opcode /\
    ~is_ext_call_op inst_a.inst_opcode /\ ~is_ext_call_op inst_b.inst_opcode /\
    inst_a.inst_opcode <> INVOKE /\ inst_b.inst_opcode <> INVOKE /\
    MEM w inst_a.inst_outputs ==>
    lookup_var w sab = lookup_var w sba
Proof
  rpt strip_tac >>
  (* Step 1: lookup_var w sab = lookup_var w va
     (inst_b doesn't write w, so it preserves w) *)
  `~MEM w inst_b.inst_outputs` by (
    gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `lookup_var w sab = lookup_var w va` by
    metis_tac[step_preserves_non_output_vars] >>
  (* Step 2: lookup_var w va = lookup_var w sba
     Both are inst_a applied to states that agree on inst_a's inputs *)
  `step_inst_base inst_a ss = OK va` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst_a vb = OK sba` by gvs[step_inst_non_invoke] >>
  `lookup_var w va = lookup_var w sba` suffices_by simp[] >>
  (* Establish all prerequisites for output_determined_vars *)
  `!op. MEM op inst_a.inst_operands ==>
        eval_operand op ss = eval_operand op vb` by (
    rpt strip_tac >>
    Cases_on `op` >> gvs[eval_operand_def]
    >- (rename1 `lookup_var vn` >>
      `~MEM vn inst_b.inst_outputs` by (
        `MEM vn (operand_vars inst_a.inst_operands)` by
          metis_tac[mem_var_operand_vars] >>
        gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      metis_tac[step_preserves_non_output_vars])
    >> metis_tac[step_preserves_labels]) >>
  `!w'. MEM w' inst_a.inst_outputs ==>
        lookup_var w' ss = lookup_var w' vb` by (
    rpt strip_tac >>
    `~MEM w' inst_b.inst_outputs` by (
      gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
    metis_tac[step_preserves_non_output_vars]) >>
  (* Get field preservation for inst_b step specifically *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst_b`, `ss`, `vb`]
            step_inst_preserves_eligible_fields) >>
  simp[] >> strip_tac >>
  imp_res_tac effects_independent_write_read_disjoint >>
  `!e. e IN read_effects inst_a.inst_opcode ==>
       e NOTIN write_effects inst_b.inst_opcode` by
    (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
  `step_inst_base inst_b ss = OK vb` by gvs[step_inst_non_invoke] >>
  `Eff_FMP NOTIN write_effects inst_b.inst_opcode ==>
   vb.vs_fmp = ss.vs_fmp` by
    metis_tac[step_inst_base_preserves_fmp_no_write] >>
  `vb.vs_call_entry_fmp = ss.vs_call_entry_fmp /\
   vb.vs_initial_fmp = ss.vs_initial_fmp /\
   vb.vs_return_pc_token = ss.vs_return_pc_token` by
    metis_tac[step_inst_base_preserves_stable_frame_metadata] >>
  `inst_a.inst_opcode = GETFMP ==> ss.vs_fmp = vb.vs_fmp` by (
    strip_tac >>
    `Eff_FMP IN read_effects inst_a.inst_opcode` by
      gvs[read_effects_def] >>
    `Eff_FMP NOTIN write_effects inst_b.inst_opcode` by res_tac >>
    gvs[]) >>
  (* Account sub-field preservation: inst_b always preserves
     balance, nonce, code even when it writes STORAGE *)
  `!addr. (vb.vs_accounts addr).balance =
          (ss.vs_accounts addr).balance /\
          (vb.vs_accounts addr).nonce =
          (ss.vs_accounts addr).nonce /\
          (vb.vs_accounts addr).code =
          (ss.vs_accounts addr).code` by
    metis_tac[step_inst_preserves_account_bnc] >>
  (* Storage sub-field: if STORAGE read by inst_a, then
     STORAGE not written by inst_b, so full accounts preserved *)
  `Eff_STORAGE IN read_effects inst_a.inst_opcode ==>
   !addr. (ss.vs_accounts addr).storage =
          (vb.vs_accounts addr).storage` by (
    strip_tac >>
    `Eff_STORAGE NOTIN write_effects inst_b.inst_opcode` by res_tac >>
    `Eff_BALANCE NOTIN write_effects inst_b.inst_opcode` by
      metis_tac[eligible_write_constraints] >>
    `vb.vs_accounts = ss.vs_accounts` by gvs[] >> gvs[]) >>
  (* Memory: if read by inst_a, not written by inst_b *)
  `Eff_MEMORY IN read_effects inst_a.inst_opcode ==>
   ss.vs_memory = vb.vs_memory` by (strip_tac >> res_tac >> gvs[]) >>
  (* Case split: effect-free uses output_determined_vars,
     non-effect-free eligible ops don't modify vs_vars *)
  (* NOP: step returns state unchanged, so trivially equal *)
  Cases_on `inst_a.inst_opcode = NOP`
  >- (
    `step_inst fuel ctx inst_a ss = OK ss` by
      metis_tac[step_nop_identity] >>
    `step_inst fuel ctx inst_a vb = OK vb` by
      metis_tac[step_nop_identity] >>
    gvs[]) >>
  Cases_on `is_effect_free_op inst_a.inst_opcode`
  >- (
    (* Account-reading opcodes need special handling because SSTORE
       modifies .storage but preserves .balance/.nonce/.code.
       The generic theorem demands full vs_accounts equality which
       fails for BALANCE × SSTORE pairs. *)
    Cases_on `Eff_BALANCE IN read_effects inst_a.inst_opcode \/
              Eff_EXTCODE IN read_effects inst_a.inst_opcode`
    >- (
      (* inst_a ∈ {BALANCE, SELFBALANCE, EXTCODESIZE, EXTCODEHASH}.
         Prove output agreement directly from sub-field preservation. *)
      qspecl_then [`fuel`, `ctx`, `inst_a`, `ss`, `vb`, `va`, `sba`, `w`]
        mp_tac account_read_step_output_agree >>
      ASM_REWRITE_TAC[])
    >- (
      (* No account-reading effects: generic theorem applies *)
      `inst_a.inst_opcode <> PHI` by
        (Cases_on `inst_a.inst_opcode` >> simp[] >>
         qpat_x_assum `inst_a.inst_opcode = PHI`
           (fn op_th =>
             qpat_x_assum `step_inst_base inst_a ss = OK va`
               (fn ok_th =>
                 mp_tac ok_th >>
                 mp_tac (MATCH_MP
                   (Q.SPECL [`inst_a`, `ss`]
                     venomExecProofsTheory.step_inst_base_phi_error)
                   op_th))) >>
         simp[]) >>
      irule step_inst_base_effect_free_output_determined_vars >>
      qexistsl_tac [`inst_a`, `ss`, `vb`] >>
      rpt conj_tac >> gvs[] >>
      TRY (res_tac >> gvs[] >> NO_TAC) >>
      Cases_on `Eff_STORAGE IN read_effects inst_a.inst_opcode`
      >- (
        `Eff_STORAGE NOTIN write_effects inst_b.inst_opcode` by res_tac >>
        `Eff_BALANCE NOTIN write_effects inst_b.inst_opcode` by
          metis_tac[eligible_write_constraints] >>
        `vb.vs_accounts = ss.vs_accounts` by gvs[] >> gvs[])
      >- gvs[]))
  >> (
    Cases_on `inst_a.inst_opcode = DALLOCA`
    >- (
      `Eff_FMP IN read_effects inst_a.inst_opcode` by
        gvs[read_effects_def] >>
      `Eff_FMP NOTIN write_effects inst_b.inst_opcode` by res_tac >>
      `ss.vs_fmp = vb.vs_fmp` by gvs[] >>
      irule dalloca_step_output_agree >>
      qexistsl_tac [`ctx`, `fuel`, `inst_a`, `ss`, `vb`] >>
      ASM_REWRITE_TAC[])
    >- (
      (* Remaining non-effect-free eligible instructions are side-effect-only. *)
      `!v. lookup_var v va = lookup_var v ss` by
        metis_tac[step_non_effect_free_preserves_all_vars] >>
      `!v. lookup_var v sba = lookup_var v vb` by
        metis_tac[step_non_effect_free_preserves_all_vars] >>
      gvs[]))
QED

(* ================================================================
   9. Independent instructions commute with state equality
   ================================================================ *)

Theorem independent_commute_eq:
  !fuel ctx inst1 inst2 ss v1 v2 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\ inst2.inst_opcode <> INVOKE ==>
    s12 = s21
Proof
  rpt strip_tac >>
  (* A: commute_equiv *)
  `commute_equiv (set (inst_defs inst1) UNION set (inst_defs inst2)) s12 s21` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `ss`]
                      effects_independent_commute) >> simp[LET_THM]) >>
  (* B: vs_allocas *)
  `s12.vs_allocas = s21.vs_allocas` by (
    `v1.vs_allocas = ss.vs_allocas` by metis_tac[step_inst_preserves_allocas] >>
    `s12.vs_allocas = ss.vs_allocas` by metis_tac[step_inst_preserves_allocas] >>
    `v2.vs_allocas = ss.vs_allocas` by metis_tac[step_inst_preserves_allocas] >>
    `s21.vs_allocas = ss.vs_allocas` by metis_tac[step_inst_preserves_allocas] >>
    simp[]) >>
  (* B2: vs_alloca_next *)
  `s12.vs_alloca_next = s21.vs_alloca_next` by (
    `v1.vs_alloca_next = ss.vs_alloca_next` by metis_tac[step_inst_preserves_alloca_next] >>
    `s12.vs_alloca_next = ss.vs_alloca_next` by metis_tac[step_inst_preserves_alloca_next] >>
    `v2.vs_alloca_next = ss.vs_alloca_next` by metis_tac[step_inst_preserves_alloca_next] >>
    `s21.vs_alloca_next = ss.vs_alloca_next` by metis_tac[step_inst_preserves_alloca_next] >>
    simp[]) >>
  (* C: vars in defs agree *)
  `!w. w IN (set (inst_defs inst1) UNION set (inst_defs inst2)) ==>
       lookup_var w s12 = lookup_var w s21` by (
    rw[IN_UNION] >> gvs[inst_defs_def]
    >- ((* w in inst1.inst_outputs — use output_var_agree with inst_a=inst1 *)
      irule output_var_agree_across_independent >>
      MAP_EVERY qexists_tac [`ctx`, `fuel`, `inst1`, `inst2`, `ss`, `v1`, `v2`] >>
      gvs[inst_defs_def, inst_uses_def])
    >- ((* w in inst2.inst_outputs — use output_var_agree with inst_a=inst2, inst_b=inst1
           Note: sab=s21, sba=s12 in the swapped version *)
      `lookup_var w s21 = lookup_var w s12` suffices_by simp[] >>
      irule output_var_agree_across_independent >>
      MAP_EVERY qexists_tac [`ctx`, `fuel`, `inst2`, `inst1`, `ss`, `v2`, `v1`] >>
      gvs[inst_defs_def, inst_uses_def] >>
      metis_tac[effects_independent_def, DISJOINT_SYM])) >>
  (* D: Assemble *)
  irule commute_equiv_allocas_vars_eq >>
  simp[] >>
  qexists_tac `set (inst_defs inst1) UNION set (inst_defs inst2)` >>
  simp[]
QED

(* ================================================================
   10. Extended commutation: allows INVOKE on one side.
       Key helpers for INVOKE × pure commutation.
   ================================================================ *)

(* FOLDL update_var preserves all non-vs_vars fields *)
Theorem foldl_update_var_field[local]:
  !pairs (ss:venom_state).
    (FOLDL (\s' (out,val). update_var out val s') ss pairs).vs_alloca_next =
    ss.vs_alloca_next /\
    (FOLDL (\s' (out,val). update_var out val s') ss pairs).vs_allocas =
    ss.vs_allocas
Proof
  Induct >> rw[] >> Cases_on `h` >> simp[update_var_def]
QED

Triviality exec_pure1_structure[local]:
  !f inst s s'.
    exec_pure1 f inst s = OK s' ==>
    ?out val. inst.inst_outputs = [out] /\ s' = update_var out val s
Proof
  rw[exec_pure1_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Triviality exec_pure2_structure[local]:
  !f inst s s'.
    exec_pure2 f inst s = OK s' ==>
    ?out val. inst.inst_outputs = [out] /\ s' = update_var out val s
Proof
  rw[exec_pure2_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Triviality exec_pure3_structure[local]:
  !f inst s s'.
    exec_pure3 f inst s = OK s' ==>
    ?out val. inst.inst_outputs = [out] /\ s' = update_var out val s
Proof
  rw[exec_pure3_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Triviality exec_read0_structure[local]:
  !f inst s s'.
    exec_read0 f inst s = OK s' ==>
    ?out val. inst.inst_outputs = [out] /\ s' = update_var out val s
Proof
  rw[exec_read0_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Triviality exec_read1_structure[local]:
  !f inst s s'.
    exec_read1 f inst s = OK s' ==>
    ?out val. inst.inst_outputs = [out] /\ s' = update_var out val s
Proof
  rw[exec_read1_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Triviality direct_single_output_step_structure[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PARAM \/
     inst.inst_opcode = GETFMP \/ inst.inst_opcode = INITIAL_FMP \/
     inst.inst_opcode = FMP_PARAM \/ inst.inst_opcode = RETPC_PARAM) ==>
    ?out val. inst.inst_outputs = [out] /\ s' = update_var out val s
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  gvs[] >> PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

Triviality bump_step_structure[local]:
  !inst s s'.
    inst.inst_opcode = BUMP /\ step_inst_base inst s = OK s' ==>
    ?out1 val1 out2 val2.
      inst.inst_outputs = [out1; out2] /\
      s' = update_var out2 val2 (update_var out1 val1 s)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  gvs[AllCaseEqs()] >> metis_tac[]
QED

fun pure_step_finish_tac () =
  gvs[inst_wf_def] >>
  FIRST [
    drule exec_pure1_structure >> strip_tac >> gvs[] >>
      qexists_tac `[(out,val)]` >> simp[],
    drule exec_pure2_structure >> strip_tac >> gvs[] >>
      qexists_tac `[(out,val)]` >> simp[],
    drule exec_pure3_structure >> strip_tac >> gvs[] >>
      qexists_tac `[(out,val)]` >> simp[],
    drule exec_read0_structure >> strip_tac >> gvs[] >>
      qexists_tac `[(out,val)]` >> simp[],
    drule exec_read1_structure >> strip_tac >> gvs[] >>
      qexists_tac `[(out,val)]` >> simp[],
    drule direct_single_output_step_structure >> strip_tac >> gvs[] >>
      qexists_tac `[(out,val)]` >> simp[],
    drule bump_step_structure >> strip_tac >> gvs[] >>
      qexists_tac `[(out1,val1); (out2,val2)]` >> simp[],
    gvs[AllCaseEqs()] >>
      FIRST [
        qexists_tac `[]` >> simp[],
        qexists_tac `[(out,val)]` >> simp[]]]

(* A pure (empty read/write effects), eligible step_inst_base changes only its
   declared outputs, represented uniformly as a finite update_var sequence. *)
Theorem pure_step_structure:
  !inst ss v2.
    step_inst_base inst ss = OK v2 /\
    inst_wf inst /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    write_effects inst.inst_opcode = {} /\
    read_effects inst.inst_opcode = {} ==>
    ?pairs.
      MAP FST pairs = inst.inst_outputs /\
      v2 = FOLDL (\s' (out,val). update_var out val s') ss pairs
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def] >>
  FIRST [
    qspecl_then [`inst`, `ss`, `v2`] mp_tac
      direct_single_output_step_structure >>
      (impl_tac >- ASM_REWRITE_TAC[]) >> strip_tac >>
      qexists_tac `[(out,val)]` >> simp[],
    qspecl_then [`inst`, `ss`, `v2`] mp_tac bump_step_structure >>
      (impl_tac >- ASM_REWRITE_TAC[]) >> strip_tac >>
      qexists_tac `[(out1,val1); (out2,val2)]` >> simp[],
    qpat_x_assum `step_inst_base inst ss = OK v2` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> strip_tac >>
      pure_step_finish_tac ()]
QED

Triviality empty_effect_non_effect_free_opcode_cases[local]:
  !op.
    ~is_terminator op /\ ~is_alloca_op op /\ ~is_ext_call_op op /\
    op <> INVOKE /\ write_effects op = {} /\ read_effects op = {} /\
    ~is_effect_free_op op ==>
    op = ASSERT \/ op = ASSERT_UNREACHABLE
Proof
  Cases >> EVAL_TAC
QED

Triviality foldl_update_var_lookup_nonmember[local]:
  !pairs s w.
    ~MEM w (MAP FST pairs) ==>
    lookup_var w (FOLDL (\s' (out,v). update_var out v s') s pairs) =
    lookup_var w s
Proof
  Induct
  >- simp[]
  >> rpt gen_tac >> PairCases_on `h` >> simp[] >> strip_tac >>
     first_x_assum (qspec_then `update_var h0 h1 s` mp_tac) >>
     simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Triviality foldl_update_var_lookup_shadowed[local]:
  !pairs s1 s2 w v.
    ~MEM w (MAP FST pairs) ==>
    lookup_var w
      (FOLDL (\s' (out,v). update_var out v s') (update_var w v s1) pairs) =
    lookup_var w
      (FOLDL (\s' (out,v). update_var out v s') (update_var w v s2) pairs)
Proof
  rpt strip_tac >>
  simp[foldl_update_var_lookup_nonmember, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]
QED

Triviality foldl_update_var_lookup_member_determined[local]:
  !pairs s1 s2 w.
    MEM w (MAP FST pairs) ==>
    lookup_var w
      (FOLDL (\s' (out,v). update_var out v s') s1 pairs) =
    lookup_var w
      (FOLDL (\s' (out,v). update_var out v s') s2 pairs)
Proof
  Induct
  >- simp[]
  >> pop_assum $ mk_asm "ih" >>
     rpt gen_tac >> PairCases_on `h` >> simp[] >> disch_tac >>
     Cases_on `MEM w (MAP FST pairs)`
     >- (asm_x "ih" irule >> ASM_REWRITE_TAC[])
     >> `w = h0` by
          (qpat_x_assum `w = h0 \/ MEM w (MAP FST pairs)` mp_tac >>
           ASM_REWRITE_TAC[]) >>
        gvs[] >> irule foldl_update_var_lookup_shadowed >> simp[]
QED

Triviality foldl_update_var_lookup_cong[local]:
  !pairs s1 s2.
    (!w. MEM w (MAP FST pairs) ==> lookup_var w s1 = lookup_var w s2) ==>
    !w. MEM w (MAP FST pairs) ==>
      lookup_var w
        (FOLDL (\s' (out,v). update_var out v s') s1 pairs) =
      lookup_var w
        (FOLDL (\s' (out,v). update_var out v s') s2 pairs)
Proof
  rpt strip_tac >> irule foldl_update_var_lookup_member_determined >> simp[]
QED

Triviality step_inst_ok_frame_foldl[local]:
  !pairs fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    EVERY (\p. (!y. MEM (Var y) inst.inst_operands ==> FST p <> y) /\
                ~MEM (FST p) inst.inst_outputs) pairs ==>
    step_inst fuel ctx inst
      (FOLDL (\st (out,v). update_var out v st) s pairs) =
    OK (FOLDL (\st (out,v). update_var out v st) s' pairs)
Proof
  Induct
  >- simp[]
  >> rpt gen_tac >> PairCases_on `h` >> simp[] >> strip_tac >>
     `step_inst fuel ctx inst (update_var h0 h1 s) =
      OK (update_var h0 h1 s')` by metis_tac[step_inst_ok_frame] >>
     first_x_assum irule >> simp[]
QED

(* Output agreement for pure, empty-effect, non-INVOKE opcodes.
   Generalizes step_inst_base_effect_free_output_determined_vars to
   also cover ASSERT, ASSERT_UNREACHABLE, NOP (which are not effect_free). *)
Theorem pure_step_output_agree[local]:
  !inst s1 s2 r1 r2.
    step_inst_base inst s1 = OK r1 /\
    step_inst_base inst s2 = OK r2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    write_effects inst.inst_opcode = {} /\
    read_effects inst.inst_opcode = {} /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s1 = eval_operand op s2) /\
    (!w. MEM w inst.inst_outputs ==> lookup_var w s1 = lookup_var w s2) /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_params = s2.vs_params /\
    s1.vs_call_ctx = s2.vs_call_ctx /\ s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_code = s2.vs_code /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    (inst.inst_opcode = GETFMP ==> s1.vs_fmp = s2.vs_fmp) /\
    (inst.inst_opcode = INITIAL_FMP ==>
      s1.vs_initial_fmp = s2.vs_initial_fmp) /\
    (inst.inst_opcode = RETPC_PARAM ==>
      s1.vs_return_pc_token = s2.vs_return_pc_token) ==>
    !w. MEM w inst.inst_outputs ==> lookup_var w r1 = lookup_var w r2
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = NOP`
  >- (gvs[] >>
      qpat_x_assum `step_inst_base inst s1 = OK r1` mp_tac >>
      qpat_x_assum `step_inst_base inst s2 = OK r2` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      rpt strip_tac >> gvs[] >>
      first_x_assum irule >> simp[]) >>
  Cases_on `is_effect_free_op inst.inst_opcode`
  >- (`inst.inst_opcode <> PHI` by
        (Cases_on `inst.inst_opcode` >> simp[] >>
         gvs[step_inst_base_def]) >>
      irule step_inst_base_effect_free_output_determined_vars >>
      MAP_EVERY qexists_tac [`inst`, `s1`, `s2`] >>
      gvs[empty_effects_def]) >>
  drule_all empty_effect_non_effect_free_opcode_cases >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s1 = OK r1` mp_tac >>
  qpat_x_assum `step_inst_base inst s2 = OK r2` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum irule >> simp[]
QED

(* effects_independent INVOKE op ==> op is pure with empty effects *)
Theorem invoke_independent_empty_effects[local]:
  !op. effects_independent INVOKE op ==>
    op <> INVOKE /\ write_effects op = {} /\ read_effects op = {}
Proof Cases >> EVAL_TAC
QED

(* FOLDL update_var only modifies vs_vars *)
Triviality foldl_update_var_only_vars:
  !pairs s. ?f.
    FOLDL (\s' (out,v). update_var out v s') s pairs = s with vs_vars := f
Proof
  Induct
  >- (rw[] >> qexists_tac `s.vs_vars` >> simp[venom_state_component_equality])
  >> gen_tac >> PairCases_on `h` >> simp[] >> gen_tac >>
     first_x_assum (qspec_then `update_var h0 h1 s` strip_assume_tac) >>
     qexists_tac `f` >> simp[] >> gvs[update_var_def]
QED

(* INVOKE preserves structural fields (prev_bb, params, contexts, etc.) *)
Theorem invoke_preserves_structural:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = INVOKE ==>
    s'.vs_prev_bb = s.vs_prev_bb /\
    s'.vs_params = s.vs_params /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\

    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_code = s.vs_code /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  rpt strip_tac >>
  gvs[Once step_inst_def, AllCaseEqs(), bind_outputs_def] >>
  qspecl_then [`ZIP (inst.inst_outputs, ret.iret_values)`,
               `adopt_return_fmp ret (merge_callee_state s callee_s')`]
    strip_assume_tac foldl_update_var_only_vars >>
  Cases_on `ret.iret_adopt_fmp` >>
  gvs[merge_callee_state_def, adopt_return_fmp_def]
QED

Triviality invoke_commute_case_foldl[local]:
  !fuel ctx inst1 inst2 ss v1 pairs s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss =
      OK (FOLDL (\s' (out,v). update_var out v s') ss pairs) /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1
      (FOLDL (\s' (out,v). update_var out v s') ss pairs) = OK s21 /\
    inst_wf inst1 /\ inst_wf inst2 /\
    inst1.inst_opcode = INVOKE /\
    MAP FST pairs = inst2.inst_outputs /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode /\
    commute_equiv (set (inst_defs inst1) UNION set (inst_defs inst2)) s12 s21 /\
    s12.vs_allocas = v1.vs_allocas /\
    s12.vs_alloca_next = v1.vs_alloca_next /\
    (!w. MEM w (inst_defs inst1) ==> lookup_var w s12 = lookup_var w v1) /\
    (!w. MEM w inst2.inst_outputs ==>
      lookup_var w s12 =
      lookup_var w (FOLDL (\s' (out,v). update_var out v s') ss pairs)) ==>
    s12 = s21
Proof
  rpt strip_tac >>
  `EVERY (\p. (!y. MEM (Var y) inst1.inst_operands ==> FST p <> y) /\
               ~MEM (FST p) inst1.inst_outputs) pairs` by (
    rw[listTheory.EVERY_MEM] >> PairCases_on `p` >> simp[] >>
    `MEM p0 inst2.inst_outputs` by (
      qpat_x_assum `MAP FST pairs = _` (fn th => rewrite_tac[GSYM th]) >>
      simp[listTheory.MEM_MAP] >> qexists `(p0,p1)` >> simp[]) >>
    `~MEM (Var p0) inst1.inst_operands` by (
      strip_tac >>
      `MEM p0 (inst_uses inst1)` by
        (gvs[inst_uses_def] >> metis_tac[mem_var_operand_vars]) >>
      `MEM p0 (inst_defs inst2)` by gvs[inst_defs_def] >>
      gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
    `~MEM p0 inst1.inst_outputs` by (
      strip_tac >>
      `MEM p0 (inst_defs inst1)` by gvs[inst_defs_def] >>
      `MEM p0 (inst_defs inst2)` by gvs[inst_defs_def] >>
      gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
    simp[]) >>
  `step_inst fuel ctx inst1
      (FOLDL (\s' (out,v). update_var out v s') ss pairs) =
    OK (FOLDL (\s' (out,v). update_var out v s') v1 pairs)` by
      metis_tac[step_inst_ok_frame_foldl] >>
  gvs[] >>
  qspecl_then [`pairs`, `v1`] strip_assume_tac foldl_update_var_only_vars >>
  irule commute_equiv_allocas_vars_eq >>
  simp[] >>
  qexists_tac `set (inst_defs inst1) UNION set (inst_defs inst2)` >>
  simp[] >> rpt strip_tac >> gvs[IN_UNION]
  >- (
    `~MEM w (MAP FST pairs)` by (
      qpat_x_assum `MAP FST pairs = inst2.inst_outputs`
        (fn th => rewrite_tac[th]) >>
      gvs[DISJOINT_DEF, EXTENSION, inst_defs_def] >> metis_tac[]) >>
    `lookup_var w
       (FOLDL (\s' (out,v). update_var out v s') v1 pairs) =
     lookup_var w v1` by
      metis_tac[foldl_update_var_lookup_nonmember] >>
    metis_tac[])
  >> (
    `MEM w (MAP FST pairs)` by
      (qpat_x_assum `MAP FST pairs = inst2.inst_outputs`
         (fn th => rewrite_tac[th]) >> gvs[inst_defs_def]) >>
    `lookup_var w s12 =
     lookup_var w
       (FOLDL (\s' (out,v). update_var out v s') ss pairs)` by
      metis_tac[inst_defs_def] >>
    `lookup_var w
       (FOLDL (\s' (out,v). update_var out v s') ss pairs) =
     lookup_var w
       (FOLDL (\s' (out,v). update_var out v s') v1 pairs)` by
      metis_tac[foldl_update_var_lookup_member_determined] >>
    metis_tac[])
QED

(* Standalone invoke commutation: INVOKE × pure-empty-effect.
   Delegates to case_nil and case_cons trivialities. *)
Theorem invoke_commute_eq[local]:
  !fuel ctx inst1 inst2 ss v1 v2 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    inst_wf inst1 /\ inst_wf inst2 /\
    inst1.inst_opcode = INVOKE /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode ==>
    s12 = s21
Proof
  rpt strip_tac >>
  (* 1: inst2 pure with empty effects *)
  `inst2.inst_opcode <> INVOKE /\
   write_effects inst2.inst_opcode = {} /\
   read_effects inst2.inst_opcode = {}` by
    (irule invoke_independent_empty_effects >> gvs[]) >>
  (* 2: structural fields preserved by INVOKE *)
  `v1.vs_prev_bb = ss.vs_prev_bb /\ v1.vs_params = ss.vs_params /\
   v1.vs_call_ctx = ss.vs_call_ctx /\ v1.vs_tx_ctx = ss.vs_tx_ctx /\
   v1.vs_block_ctx = ss.vs_block_ctx /\ v1.vs_data_section = ss.vs_data_section /\
   v1.vs_code = ss.vs_code /\ v1.vs_prev_hashes = ss.vs_prev_hashes /\
   v1.vs_labels = ss.vs_labels /\
   v1.vs_initial_fmp = ss.vs_initial_fmp /\
   v1.vs_return_pc_token = ss.vs_return_pc_token` by
    (irule invoke_preserves_structural >> simp[] >> metis_tac[]) >>
  (* 3: commute_equiv *)
  `commute_equiv (set (inst_defs inst1) UNION set (inst_defs inst2))
     s12 s21` by (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `inst1`, `inst2`, `ss`]
                      effects_independent_commute) >> simp[LET_THM]) >>
  (* 4-5: step_inst_base reductions *)
  `step_inst_base inst2 ss = OK v2` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst2 v1 = OK s12` by gvs[step_inst_non_invoke] >>
  (* 6-7: allocas preserved *)
  `s12.vs_allocas = v1.vs_allocas` by
    metis_tac[step_inst_preserves_allocas] >>
  `s12.vs_alloca_next = v1.vs_alloca_next` by
    metis_tac[step_inst_preserves_alloca_next] >>
  (* 8: operand agreement *)
  `!op. MEM op inst2.inst_operands ==>
        eval_operand op v1 = eval_operand op ss` by (
    rpt strip_tac >>
    qspecl_then [`fuel`, `ctx`, `inst1`, `ss`, `v1`, `op`]
      mp_tac eval_operand_step_pres >>
    (impl_tac >- (simp[] >>
      gvs[DISJOINT_DEF, EXTENSION, inst_uses_def, inst_defs_def] >>
      metis_tac[mem_var_operand_vars])) >> simp[]) >>
  (* 9: output var agreement (inst1 preserves inst2's outputs) *)
  `!w. MEM w inst2.inst_outputs ==>
        lookup_var w v1 = lookup_var w ss` by (
    rpt strip_tac >>
    qspecl_then [`fuel`, `ctx`, `inst1`, `ss`, `v1`]
      mp_tac step_preserves_non_output_vars >>
    simp[] >>
    gvs[DISJOINT_DEF, EXTENSION, inst_defs_def] >> metis_tac[]) >>
  `inst2.inst_opcode = GETFMP ==> v1.vs_fmp = ss.vs_fmp` by
    (strip_tac >> gvs[read_effects_def]) >>
  (* 10: inst2 output vars agree between s12 and v2 *)
  `!w. MEM w inst2.inst_outputs ==> lookup_var w s12 = lookup_var w v2` by (
    rpt strip_tac >> irule pure_step_output_agree >>
    MAP_EVERY qexists_tac [`inst2`, `v1`, `ss`] >> simp[]) >>
  (* 11: inst1 defs preserved through inst2 *)
  `!w. MEM w (inst_defs inst1) ==> lookup_var w s12 = lookup_var w v1` by (
    rpt strip_tac >>
    qspecl_then [`fuel`, `ctx`, `inst2`, `v1`, `s12`]
      mp_tac step_preserves_non_output_vars >>
    simp[] >>
    gvs[DISJOINT_DEF, EXTENSION, inst_defs_def] >> metis_tac[]) >>
  (* 12: Use the finite output-update sequence from pure_step_structure. *)
  qspecl_then [`inst2`, `ss`, `v2`] mp_tac pure_step_structure >>
  simp[] >> strip_tac >> gvs[] >>
  irule invoke_commute_case_foldl >>
  simp[] >> metis_tac[]
QED

(* Extended commutativity: two data-independent, abort-compatible,
   non-terminator, non-alloca, non-ext_call instructions produce identical
   states in either execution order, including the case where one is INVOKE. *)
Theorem independent_commute_eq_ext:
  !fuel ctx inst1 inst2 ss v1 v2 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    inst_wf inst1 /\ inst_wf inst2 /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    effects_independent inst1.inst_opcode inst2.inst_opcode /\
    abort_compatible inst1.inst_opcode inst2.inst_opcode /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    ~is_alloca_op inst1.inst_opcode /\ ~is_alloca_op inst2.inst_opcode /\
    ~is_ext_call_op inst1.inst_opcode /\ ~is_ext_call_op inst2.inst_opcode ==>
    s12 = s21
Proof
  rpt strip_tac >>
  Cases_on `inst1.inst_opcode = INVOKE`
  >- (
    qspecl_then [`fuel`, `ctx`, `inst1`, `inst2`, `ss`, `v1`, `v2`, `s12`, `s21`]
      mp_tac invoke_commute_eq >> simp[])
  >> Cases_on `inst2.inst_opcode = INVOKE`
  >- (
    `effects_independent inst2.inst_opcode inst1.inst_opcode` by (
      gvs[effects_independent_def]) >>
    `abort_compatible inst2.inst_opcode inst1.inst_opcode` by (
      gvs[abort_compatible_def]) >>
    `s21 = s12` suffices_by simp[] >>
    qspecl_then [`fuel`, `ctx`, `inst2`, `inst1`, `ss`, `v2`, `v1`, `s21`, `s12`]
      mp_tac invoke_commute_eq >>
    simp[DISJOINT_SYM])
  >> (
    qspecl_then [`fuel`, `ctx`, `inst1`, `inst2`, `ss`, `v1`, `v2`, `s12`, `s21`]
      mp_tac independent_commute_eq >> simp[])
QED

(* ================================================================
   11. Effect-free commutativity: effect-free instructions with
       disjoint data deps produce identical states in either order.
       Handles memory-only-read pairs ({MLOAD,ILOAD,SHA3,MEMTOP}^2) that are
       NOT effects_independent but still commute.
   ================================================================ *)

(* Key insight: is_effect_free_op instructions only modify output variables
   (step_effect_free_state_equiv). So two such instructions commute when
   data-independent, because:
   (1) Each reads the same operand values regardless of order
   (2) Each preserves all state fields
   (3) update_var calls commute when outputs are disjoint *)

(*
 * Helper: extract field equalities from state_equiv without
 * expanding the whole definition (avoids fs explosion).
 *)
Triviality state_equiv_fields:
  !vars s1 s2. state_equiv vars s1 s2 ==>
    s1.vs_memory = s2.vs_memory /\
    s1.vs_transient = s2.vs_transient /\
    (s1.vs_halted <=> s2.vs_halted) /\
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
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_allocas = s2.vs_allocas /\
    s1.vs_alloca_next = s2.vs_alloca_next /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2)
Proof
  rw[state_equiv_def, execution_equiv_def]
QED

(* effect-free ops are not INVOKE, so step_inst = step_inst_base *)
Triviality effect_free_step_eq_base[local]:
  !inst. is_effect_free_op inst.inst_opcode ==>
    !fuel ctx s. step_inst fuel ctx inst s = step_inst_base inst s
Proof
  rpt strip_tac >> simp[Once step_inst_def] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[is_effect_free_op_def]) >>
  simp[]
QED

Triviality effect_free_step_preserves_hidden_fields[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    s'.vs_fmp = s.vs_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  rpt strip_tac >>
  `~is_terminator inst.inst_opcode` by
    metis_tac[is_effect_free_not_terminator] >>
  `~is_alloca_op inst.inst_opcode /\
   ~is_ext_call_op inst.inst_opcode /\
   inst.inst_opcode <> INVOKE /\
   Eff_FMP NOTIN write_effects inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >>
     gvs[is_effect_free_op_def, is_alloca_op_def, is_ext_call_op_def,
         write_effects_def, empty_effects_def]) >>
  `step_inst_base inst s = OK s'` by
    metis_tac[effect_free_step_eq_base] >>
  `s'.vs_fmp = s.vs_fmp` by (
    qspecl_then [`inst`, `s`, `s'`] mp_tac
      step_inst_base_preserves_fmp_no_write >>
    simp[]) >>
  `s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
   s'.vs_initial_fmp = s.vs_initial_fmp /\
   s'.vs_return_pc_token = s.vs_return_pc_token` by (
    qspecl_then [`inst`, `s`, `s'`] mp_tac
      step_inst_base_preserves_stable_frame_metadata >>
    simp[]) >>
  simp[]
QED

(* If two states are state_equiv on some variable set and also agree on all
   variables in that set, then they are fully equivalent (state_equiv {}). *)
Theorem state_equiv_fill_vars:
  !vars s1 s2.
    state_equiv vars s1 s2 /\
    (!v. v IN vars ==> lookup_var v s1 = lookup_var v s2) ==>
    state_equiv {} s1 s2
Proof
  rw[state_equiv_def, execution_equiv_def] >> metis_tac[]
QED

(* Effect-free step output is determined by state_equiv-preserved state.
   For non-NOP effect-free inst, if s1 and s2 agree on everything except
   some vars disjoint from inst_uses, then output values agree. *)
Triviality effect_free_output_determined[local]:
  !fuel ctx inst s1 s2 r1 r2 excl.
    step_inst fuel ctx inst s1 = OK r1 /\
    step_inst fuel ctx inst s2 = OK r2 /\
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> NOP /\
    (inst.inst_opcode = GETFMP ==> s1.vs_fmp = s2.vs_fmp) /\
    (inst.inst_opcode = INITIAL_FMP ==>
      s1.vs_initial_fmp = s2.vs_initial_fmp) /\
    (inst.inst_opcode = RETPC_PARAM ==>
      s1.vs_return_pc_token = s2.vs_return_pc_token) /\
    state_equiv excl s1 s2 /\
    DISJOINT excl (set (inst_uses inst)) ==>
    !v. MEM v inst.inst_outputs ==> lookup_var v r1 = lookup_var v r2
Proof
  rpt strip_tac >>
  imp_res_tac effect_free_step_eq_base >> gvs[] >>
  `inst.inst_opcode <> PHI` by
    (CCONTR_TAC >>
     qpat_x_assum `~(inst.inst_opcode <> PHI)` mp_tac >> simp[] >> strip_tac >>
     qpat_x_assum `step_inst_base inst s1 = OK r1` mp_tac >>
     ASM_REWRITE_TAC[step_inst_base_def] >> simp[]) >>
  qspecl_then [`inst`, `s1`, `s2`, `r1`, `r2`] mp_tac
    step_inst_base_effect_free_output_determined_vars >>
  impl_tac >- (
    imp_res_tac state_equiv_fields >>
    rpt conj_tac >> gvs[]
    >- (rpt strip_tac >> irule eval_operand_equiv >>
        qexists_tac `excl` >> simp[] >>
        rpt strip_tac >> gvs[DISJOINT_DEF, EXTENSION, inst_uses_def] >>
        metis_tac[mem_var_operand_vars])
    >> metis_tac[]) >>
  metis_tac[]
QED

Theorem effect_free_commute_eq:
  !fuel ctx inst1 inst2 ss v1 v2 s12 s21.
    step_inst fuel ctx inst1 ss = OK v1 /\
    step_inst fuel ctx inst2 ss = OK v2 /\
    step_inst fuel ctx inst2 v1 = OK s12 /\
    step_inst fuel ctx inst1 v2 = OK s21 /\
    is_effect_free_op inst1.inst_opcode /\
    is_effect_free_op inst2.inst_opcode /\
    DISJOINT (set (inst_defs inst1)) (set (inst_uses inst2)) /\
    DISJOINT (set (inst_defs inst2)) (set (inst_uses inst1)) /\
    DISJOINT (set (inst_defs inst1)) (set (inst_defs inst2)) /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode ==>
    s12 = s21
Proof
  rpt strip_tac >>
  (* Step 1: Get state_equiv from each effect-free step *)
  `state_equiv (set inst1.inst_outputs) ss v1` by
    metis_tac[step_effect_free_state_equiv] >>
  `state_equiv (set inst2.inst_outputs) ss v2` by
    metis_tac[step_effect_free_state_equiv] >>
  `state_equiv (set inst2.inst_outputs) v1 s12` by
    metis_tac[step_effect_free_state_equiv] >>
  `state_equiv (set inst1.inst_outputs) v2 s21` by
    metis_tac[step_effect_free_state_equiv] >>
  (* Handle NOP: identity step, so trivially commutes *)
  Cases_on `inst1.inst_opcode = NOP`
  >- (imp_res_tac step_nop_identity >> gvs[]) >>
  Cases_on `inst2.inst_opcode = NOP`
  >- (imp_res_tac step_nop_identity >> gvs[]) >>
  `v1.vs_fmp = ss.vs_fmp /\
   v1.vs_initial_fmp = ss.vs_initial_fmp /\
   v1.vs_return_pc_token = ss.vs_return_pc_token` by
    metis_tac[effect_free_step_preserves_hidden_fields] >>
  `v2.vs_fmp = ss.vs_fmp /\
   v2.vs_initial_fmp = ss.vs_initial_fmp /\
   v2.vs_return_pc_token = ss.vs_return_pc_token` by
    metis_tac[effect_free_step_preserves_hidden_fields] >>
  (* Step 2: Chain state_equivs to get state_equiv (outs1 ∪ outs2) s12 s21 *)
  qabbrev_tac `both = set inst1.inst_outputs UNION set inst2.inst_outputs` >>
  `state_equiv both ss s12` by
    (irule state_equiv_trans >> qexists_tac `v1` >>
     metis_tac[state_equiv_subset, SUBSET_UNION]) >>
  `state_equiv both ss s21` by
    (irule state_equiv_trans >> qexists_tac `v2` >>
     metis_tac[state_equiv_subset, SUBSET_UNION]) >>
  `state_equiv both s12 s21` by
    metis_tac[state_equiv_sym, state_equiv_trans] >>
  (* Step 3: Strengthen to state_equiv {} by filling in excluded vars *)
  irule state_equiv_empty_eq >>
  irule state_equiv_fill_vars >>
  qexists_tac `both` >> simp[] >>
  rpt strip_tac >> gvs[inst_defs_def, Abbr `both`]
  (* v in inst1.outs *)
  >- (`v NOTIN set inst2.inst_outputs` by
        (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      (* lookup_var v s12 = lookup_var v v1 *)
      `lookup_var v s12 = lookup_var v v1` by
        (qpat_x_assum `state_equiv (set inst2.inst_outputs) v1 s12` mp_tac >>
         simp[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
      (* lookup_var v v1 = lookup_var v s21 via output_determined *)
      `lookup_var v v1 = lookup_var v s21` by
        (qspecl_then [`fuel`, `ctx`, `inst1`, `ss`, `v2`, `v1`, `s21`,
                      `set inst2.inst_outputs`] mp_tac
           effect_free_output_determined >>
         simp[] >> metis_tac[DISJOINT_SYM]) >>
      simp[])
  (* v in inst2.outs: symmetric *)
  >> (`v NOTIN set inst1.inst_outputs` by
        (gvs[DISJOINT_DEF, EXTENSION] >> metis_tac[]) >>
      `lookup_var v s21 = lookup_var v v2` by
        (qpat_x_assum `state_equiv (set inst1.inst_outputs) v2 s21` mp_tac >>
         simp[state_equiv_def, execution_equiv_def] >> metis_tac[]) >>
      `lookup_var v v2 = lookup_var v s12` by
        (qspecl_then [`fuel`, `ctx`, `inst2`, `ss`, `v1`, `v2`, `s12`,
                      `set inst1.inst_outputs`] mp_tac
           effect_free_output_determined >>
         simp[] >> metis_tac[DISJOINT_SYM]) >>
      simp[])
QED


