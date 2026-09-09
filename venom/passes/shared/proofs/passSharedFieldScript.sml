(*
 * Field preservation for non-ext-call instructions.
 *)

Theory passSharedField
Ancestors
  passSharedDefs venomExecSemantics venomEffects venomInstProps
  venomState venomInst

(* Upstream-style tactic *)
val field_tac =
  rw[step_inst_base_def] >>
  gvs[AllCaseEqs(), is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, all_effects_def, empty_effects_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     contract_storage_def, contract_transient_def];

Theorem step_base_preserves_transient[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[step_inst_base_def]) >>
  `step_inst ARB ARB inst s = OK s'` by simp[Once step_inst_def] >>
  drule_all write_effects_sound_transient >> simp[]
QED

Theorem step_base_preserves_accounts[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[step_inst_base_def]) >>
  `step_inst ARB ARB inst s = OK s'` by simp[Once step_inst_def] >>
  drule_all write_effects_sound_accounts >> simp[]
QED

Theorem step_base_preserves_logs[local]:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode ==>
    s'.vs_logs = s.vs_logs
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[step_inst_base_def]) >>
  `step_inst ARB ARB inst s = OK s'` by simp[Once step_inst_def] >>
  drule_all write_effects_sound_log >> simp[]
QED

Theorem step_base_preserves_tracked:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    (Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
      s'.vs_transient = s.vs_transient) /\
    (Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
     Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
      s'.vs_accounts = s.vs_accounts) /\
    (Eff_LOG NOTIN write_effects inst.inst_opcode ==>
      s'.vs_logs = s.vs_logs)
Proof
  metis_tac[step_base_preserves_transient,
            step_base_preserves_accounts,
            step_base_preserves_logs]
QED

Theorem step_inst_base_preserves_stable_frame_metadata:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  rpt strip_tac >>
  drule venomInstProofs1Theory.step_inst_base_preserves_all >> simp[]
QED

Theorem step_inst_base_preserves_fmp_no_write:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    Eff_FMP NOTIN write_effects inst.inst_opcode ==>
    s'.vs_fmp = s.vs_fmp
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> SETFMP` by
    (strip_tac >> gvs[write_effects_def]) >>
  `inst.inst_opcode <> DALLOCA` by
    (strip_tac >> gvs[write_effects_def]) >>
  metis_tac[venomInstProofs1Theory.step_inst_base_preserves_fmp_ordinary]
QED

Theorem step_inst_base_ordinary_fmp_agreement:
  !inst s1 s2 v1 v2.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    s1.vs_fmp = s2.vs_fmp ==>
    v1.vs_fmp = v2.vs_fmp
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >> simp[update_var_def]) >>
  imp_res_tac venomInstProofs1Theory.step_inst_base_preserves_fmp_ordinary >>
  metis_tac[]
QED

Theorem step_inst_base_ordinary_frame_agreement:
  !inst s1 s2 v1 v2.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token ==>
    v1.vs_fmp = v2.vs_fmp /\
    v1.vs_call_entry_fmp = v2.vs_call_entry_fmp /\
    v1.vs_initial_fmp = v2.vs_initial_fmp /\
    v1.vs_return_pc_token = v2.vs_return_pc_token
Proof
  rpt strip_tac >>
  `v1.vs_call_entry_fmp = s1.vs_call_entry_fmp /\
   v1.vs_initial_fmp = s1.vs_initial_fmp /\
   v1.vs_return_pc_token = s1.vs_return_pc_token` by
    metis_tac[step_inst_base_preserves_stable_frame_metadata] >>
  `v2.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
   v2.vs_initial_fmp = s2.vs_initial_fmp /\
   v2.vs_return_pc_token = s2.vs_return_pc_token` by
    metis_tac[step_inst_base_preserves_stable_frame_metadata] >>
  Cases_on `inst.inst_opcode = SETFMP`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = DALLOCA`
  >- (gvs[step_inst_base_def, AllCaseEqs()] >> simp[update_var_def]) >>
  imp_res_tac venomInstProofs1Theory.step_inst_base_preserves_fmp_ordinary >>
  metis_tac[]
QED

(* Combined preservation theorem: all field preservation facts in one.
   Use with targeted qpat_x_assum to avoid metis search with multiple
   step_inst assumptions. *)
Theorem step_inst_preserves_all:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    (* Always preserved (Group A) *)
    s'.vs_prev_bb = s.vs_prev_bb /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_code = s.vs_code /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    (* Conditionally preserved (Group B) *)
    (Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
      s'.vs_memory = s.vs_memory) /\
    (Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
      s'.vs_immutables = s.vs_immutables) /\
    (Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
      s'.vs_returndata = s.vs_returndata) /\
    (Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
      s'.vs_transient = s.vs_transient) /\
    (Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
     Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
      s'.vs_accounts = s.vs_accounts) /\
    (Eff_LOG NOTIN write_effects inst.inst_opcode ==>
      s'.vs_logs = s.vs_logs)
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
  metis_tac[step_preserves_control_flow, step_preserves_halted,
            step_preserves_call_ctx, step_preserves_tx_ctx,
            step_preserves_block_ctx, step_preserves_data_section,
            step_preserves_code, step_preserves_labels,
            step_preserves_params, step_preserves_prev_hashes,
            write_effects_sound_memory, write_effects_sound_immutables,
            write_effects_sound_returndata,
            step_base_preserves_tracked]
QED

(* ----------------------------------------------------------------
   Memory Frame Lemma
   
   Non-volatile-memory instructions produce the same result when
   vs_memory is replaced.  "Non-volatile-memory" means no Eff_MEMORY
   in read_effects or write_effects.
   
   Why: eval_operand only reads vs_vars, update_var only writes
   vs_vars, and the state-reader functions for non-memory opcodes
   (sload, tload, calldataload, dload, etc.) don't access vs_memory.
   ---------------------------------------------------------------- *)

(* Building blocks *)
Theorem eval_operand_mem[local,simp]:
  !op s m. eval_operand op (s with vs_memory := m) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operands_mem[local,simp]:
  !ops s m. eval_operands ops (s with vs_memory := m) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >>
  rw[] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem update_var_mem[local,simp]:
  !x v s m. update_var x v (s with vs_memory := m) =
             (update_var x v s) with vs_memory := m
Proof
  simp[update_var_def]
QED

(* State-access functions: memory independence.
   Read-only functions return the same value when vs_memory changes.
   Write functions commute with vs_memory update. *)
Theorem sload_mem[local,simp]:
  !key (s:venom_state) m. sload key (s with vs_memory := m) = sload key s
Proof
  simp[sload_def, contract_storage_def]
QED

Theorem tload_mem[local,simp]:
  !key (s:venom_state) m. tload key (s with vs_memory := m) = tload key s
Proof
  simp[tload_def, contract_transient_def]
QED

Theorem sstore_mem[local,simp]:
  !key val (s:venom_state) m.
    sstore key val (s with vs_memory := m) =
    (sstore key val s) with vs_memory := m
Proof
  simp[sstore_def, LET_THM, vfmStateTheory.lookup_account_def]
QED

Theorem tstore_mem[local,simp]:
  !key val (s:venom_state) m.
    tstore key val (s with vs_memory := m) =
    (tstore key val s) with vs_memory := m
Proof
  simp[tstore_def, LET_THM, contract_transient_def]
QED

(* Frame tactic: like field_tac but rewrites eval_operand/update_var
   plus state-access functions that don't depend on vs_memory *)
val mem_frame_finish_tac =
  fs[step_inst_base_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, vfmStateTheory.lookup_account_def];

val mem_frame_tac =
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def] >>
  mem_frame_finish_tac;

Theorem step_inst_base_mem_frame[local]:
  !inst s s' m.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode
    ==>
    step_inst_base inst (s with vs_memory := m) =
    OK (s' with vs_memory := m)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def]
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
QED

(* Lift to step_inst (adds INVOKE + ALLOCA exclusions).
   ALLOCA uses vs_alloca_next as bump pointer;
   it does not read LENGTH vs_memory. *)
Theorem step_inst_mem_frame:
  !fuel ctx inst s s' m.
    step_inst fuel ctx inst s = OK s' /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE
    ==>
    step_inst fuel ctx inst (s with vs_memory := m) =
    OK (s' with vs_memory := m)
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst (s with vs_memory := m) =
   OK (s' with vs_memory := m)` by metis_tac[step_inst_base_mem_frame] >>
  gvs[step_inst_non_invoke]
QED

(* Error results from pure binary operations are memory-independent. *)
Theorem exec_pure2_mem_error[local]:
  !f inst s e m.
    exec_pure2 f inst s = Error e ==>
    exec_pure2 f inst (s with vs_memory := m) = Error e
Proof
  rpt strip_tac >>
  qpat_x_assum `exec_pure2 f inst s = Error e` mp_tac >>
  simp[exec_pure2_def, AllCaseEqs()]
QED

(* Error case: same error regardless of memory replacement *)
Theorem step_inst_base_mem_error_frame[local]:
  !inst s e m.
    step_inst_base inst s = Error e /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode
    ==>
    step_inst_base inst (s with vs_memory := m) = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def]
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- (qpat_x_assum `step_inst_base inst s = Error e` mp_tac >>
      PURE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      simp[exec_pure2_mem_error])
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
  >- mem_frame_finish_tac
QED

Theorem step_inst_mem_error_frame:
  !fuel ctx inst s e m.
    step_inst fuel ctx inst s = Error e /\
    Eff_MEMORY NOTIN read_effects inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE
    ==>
    step_inst fuel ctx inst (s with vs_memory := m) = Error e
Proof
  rpt strip_tac >>
  `step_inst_base inst s = Error e` by gvs[step_inst_non_invoke] >>
  `step_inst_base inst (s with vs_memory := m) = Error e`
    by metis_tac[step_inst_base_mem_error_frame] >>
  gvs[step_inst_non_invoke]
QED

(* No eligible opcode writes Eff_BALANCE or Eff_EXTCODE.
   These effects only appear in write_effects of ext_call ops
   (CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2) and SELFDESTRUCT
   (a terminator). This is critical for the accounts field in
   output_determined: preserves_all for accounts needs BOTH
   Eff_BALANCE and Eff_STORAGE to not be in write_effects. *)
Theorem eligible_no_write_balance_extcode:
  !op. ~is_terminator op /\ ~is_alloca_op op /\
       ~is_ext_call_op op /\ op <> INVOKE ==>
       Eff_BALANCE NOTIN write_effects op /\
       Eff_EXTCODE NOTIN write_effects op
Proof
  Cases >> simp[is_terminator_def, is_alloca_op_def,
                is_ext_call_op_def, write_effects_def,
                all_effects_def, empty_effects_def]
QED

(* ----------------------------------------------------------------
   Transient Frame Lemma

   Non-transient instructions produce the same result when
   vs_transient is replaced.  "Non-transient" means no Eff_TRANSIENT
   in read_effects or write_effects.
   ---------------------------------------------------------------- *)

Theorem eval_operand_trans[local,simp]:
  !op s t. eval_operand op (s with vs_transient := t) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operands_trans[local,simp]:
  !ops s t. eval_operands ops (s with vs_transient := t) =
            eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >>
  rw[] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem update_var_trans[local,simp]:
  !x v s t. update_var x v (s with vs_transient := t) =
             (update_var x v s) with vs_transient := t
Proof
  simp[update_var_def]
QED

Theorem sload_trans[local,simp]:
  !key (s:venom_state) t.
    sload key (s with vs_transient := t) = sload key s
Proof
  simp[sload_def, contract_storage_def]
QED

Theorem mload_trans[local,simp]:
  !addr (s:venom_state) t.
    mload addr (s with vs_transient := t) = mload addr s
Proof
  simp[mload_def]
QED

Theorem sstore_trans[local,simp]:
  !key val (s:venom_state) t.
    sstore key val (s with vs_transient := t) =
    (sstore key val s) with vs_transient := t
Proof
  simp[sstore_def, LET_THM, vfmStateTheory.lookup_account_def]
QED

Theorem mstore_trans[local,simp]:
  !addr val (s:venom_state) t.
    mstore addr val (s with vs_transient := t) =
    (mstore addr val s) with vs_transient := t
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED


Theorem istore_trans[local,simp]:
  !addr val (s:venom_state) t.
    istore addr val (s with vs_transient := t) =
    (istore addr val s) with vs_transient := t
Proof
  simp[istore_def, mstore_trans]
QED
Theorem mstore8_trans[local,simp]:
  !addr val (s:venom_state) t.
    mstore8 addr val (s with vs_transient := t) =
    (mstore8 addr val s) with vs_transient := t
Proof
  simp[mstore8_def, write_memory_with_expansion_def]
QED

val trans_frame_finish_tac =
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_alloca_def, extract_venom_result_def] >>
  strip_tac >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, vfmStateTheory.lookup_account_def,
     mstore_def, mstore8_def, sstore_def,
     write_memory_with_expansion_def, mcopy_def,
     contract_storage_def];

val trans_frame_tac =
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def] >>
  trans_frame_finish_tac;

Theorem step_inst_base_trans_frame:
  !inst s s' t.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_TRANSIENT NOTIN read_effects inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode
    ==>
    step_inst_base inst (s with vs_transient := t) =
    OK (s' with vs_transient := t)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def]
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
QED

Theorem step_inst_base_trans_error_frame:
  !inst s e t.
    step_inst_base inst s = Error e /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_TRANSIENT NOTIN read_effects inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode
    ==>
    step_inst_base inst (s with vs_transient := t) = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def]
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
  >- trans_frame_finish_tac
QED

(* ----------------------------------------------------------------
   Account Storage-Only Frame Lemma

   If Eff_STORAGE is NOT in read/write effects, replacing only the
   .storage field of every account preserves step_inst_base results.
   Other account fields (nonce, balance, code) are untouched, so
   BALANCE, SELFBALANCE, EXTCODESIZE, EXTCODECOPY still work.
   ---------------------------------------------------------------- *)

(* Helper: replace storage in all accounts *)
Definition replace_account_storage_def:
  replace_account_storage (new_storage : 160 word -> 256 word -> 256 word) accts =
    \addr. (accts addr) with storage := new_storage addr
End

Theorem eval_operand_acct_stor[local,simp]:
  !op s f. eval_operand op (s with vs_accounts updated_by f) =
           eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_operands_acct_stor[local,simp]:
  !ops s f. eval_operands ops (s with vs_accounts updated_by f) =
            eval_operands ops s
Proof
  Induct >> simp[eval_operands_def] >>
  rw[] >> CASE_TAC >> simp[] >> CASE_TAC >> simp[]
QED

Theorem update_var_acct_stor[local,simp]:
  !x v s f. update_var x v (s with vs_accounts updated_by f) =
             (update_var x v s) with vs_accounts updated_by f
Proof
  simp[update_var_def]
QED

(* balance/code lookups see through storage replacement *)
Theorem lookup_account_replace_storage_balance:
  !addr new_st accts.
    (replace_account_storage new_st accts addr).balance =
    (accts addr).balance
Proof
  simp[replace_account_storage_def]
QED

Theorem lookup_account_replace_storage_code:
  !addr new_st accts.
    (replace_account_storage new_st accts addr).code =
    (accts addr).code
Proof
  simp[replace_account_storage_def]
QED

Theorem lookup_account_replace_storage_nonce:
  !addr new_st accts.
    (replace_account_storage new_st accts addr).nonce =
    (accts addr).nonce
Proof
  simp[replace_account_storage_def]
QED

(* mload/sload don't depend on vs_accounts at all *)
Theorem mload_acct[local,simp]:
  !addr (s:venom_state) f. mload addr (s with vs_accounts updated_by f) = mload addr s
Proof
  simp[mload_def]
QED

(* tload doesn't depend on vs_accounts *)
Theorem tload_acct[local,simp]:
  !key (s:venom_state) f. tload key (s with vs_accounts updated_by f) = tload key s
Proof
  simp[tload_def, contract_transient_def]
QED

(* mstore/mstore8 don't change vs_accounts *)
Theorem mstore_acct[local,simp]:
  !addr val (s:venom_state) f.
    mstore addr val (s with vs_accounts updated_by f) =
    (mstore addr val s) with vs_accounts updated_by f
Proof
  simp[mstore_def, write_memory_with_expansion_def]
QED


Theorem istore_acct[local,simp]:
  !addr val (s:venom_state) f.
    istore addr val (s with vs_accounts updated_by f) =
    (istore addr val s) with vs_accounts updated_by f
Proof
  simp[istore_def, mstore_acct]
QED
Theorem mstore8_acct[local,simp]:
  !addr val (s:venom_state) f.
    mstore8 addr val (s with vs_accounts updated_by f) =
    (mstore8 addr val s) with vs_accounts updated_by f
Proof
  simp[mstore8_def, write_memory_with_expansion_def]
QED

(* tstore doesn't change vs_accounts *)
Theorem tstore_acct[local,simp]:
  !key val (s:venom_state) f.
    tstore key val (s with vs_accounts updated_by f) =
    (tstore key val s) with vs_accounts updated_by f
Proof
  simp[tstore_def, LET_THM, contract_transient_def]
QED

val acct_frame_finish_tac =
  fs[step_inst_base_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def, extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, vfmStateTheory.lookup_account_def,
     mstore_def, mstore8_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     contract_storage_def, contract_transient_def] >>
  TRY (gvs[vfmStateTheory.account_empty_def] >> NO_TAC);

val acct_frame_tac =
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def] >>
  acct_frame_finish_tac;

(* f : (160 word -> account_state) -> (160 word -> account_state)
   must preserve balance, code, nonce for all addresses.
   Typical use: f = \accts addr. accts addr with storage := other addr *)
Theorem step_inst_base_acct_frame:
  !inst s s' (f : (160 word -> account_state) -> 160 word -> account_state).
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_STORAGE NOTIN read_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode /\
    (!addr. (f s.vs_accounts addr).balance = (s.vs_accounts addr).balance) /\
    (!addr. (f s.vs_accounts addr).code = (s.vs_accounts addr).code) /\
    (!addr. (f s.vs_accounts addr).nonce = (s.vs_accounts addr).nonce)
    ==>
    step_inst_base inst (s with vs_accounts := f s.vs_accounts) =
    OK (s' with vs_accounts := f s'.vs_accounts)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def]
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
QED

Theorem step_inst_base_acct_error_frame:
  !inst s e (f : (160 word -> account_state) -> 160 word -> account_state).
    step_inst_base inst s = Error e /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    Eff_STORAGE NOTIN read_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode /\
    (!addr. (f s.vs_accounts addr).balance = (s.vs_accounts addr).balance) /\
    (!addr. (f s.vs_accounts addr).nonce = (s.vs_accounts addr).nonce) /\
    (!addr. (f s.vs_accounts addr).code = (s.vs_accounts addr).code)
    ==>
    step_inst_base inst (s with vs_accounts := f s.vs_accounts) = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      write_effects_def, read_effects_def, all_effects_def, empty_effects_def]
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
  >- acct_frame_finish_tac
QED

val _ = export_theory();
