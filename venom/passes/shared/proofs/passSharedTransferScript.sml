(*
 * Pass Shared Transfer Properties
 *
 * Transfer lemma: if step_inst_base returns OK on state s1, and state s2
 * agrees on operand values, key context fields, and tracked state fields,
 * then step_inst_base also returns OK on s2 AND the results agree on
 * output variables and all written state fields.
 *
 * Isolated in its own file because expanding step_inst_base_def over
 * all ~90 opcodes is expensive (~25s).
 *
 * TOP-LEVEL EXPORTS:
 *   step_inst_base_ok_transfer - OK transfers across agreeing states
 *   step_inst_base_output_determined_fields - per-field output determinism
 *   step_inst_base_scalar_agree - all 17 scalar fields agree
 *   step_inst_base_output_vars_agree - output vars agree (all non-term/alloca/ext_call ops)
 *   step_inst_base_effect_free_output_determined_vars - effect-free ops: output vars determined by operands + read state
 *)

Theory passSharedTransfer
Ancestors
  passSharedDefs venomExecSemantics venomEffects venomState venomInst
  venomInstProps

(* Helper: eval_operands agreement from pointwise eval_operand agreement *)
Theorem eval_operands_agree_lem[local]:
  !ops s s'.
    (!op. MEM op ops ==> eval_operand op s = eval_operand op s') ==>
    eval_operands ops s = eval_operands ops s'
Proof
  Induct >> rw[eval_operands_def] >>
  `eval_operand h s = eval_operand h s'` by gvs[] >>
  `eval_operands ops s = eval_operands ops s'` by
    (first_x_assum irule >> rw[]) >>
  simp[]
QED

(* Helper: resolve_phi result is a member of the operand list *)
Theorem resolve_phi_mem[local]:
  !prev ops val_op.
    resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  recInduct resolve_phi_ind >>
  rw[resolve_phi_def, AllCaseEqs()] >> gvs[] >>
  res_tac >> gvs[]
QED

Theorem mem_drop_subset[local]:
  !n l x. MEM x (DROP n l) ==> MEM x l
Proof
  Induct >> rw[] >> Cases_on `l` >> gvs[] >> res_tac >> gvs[]
QED

(* State-accessing function defs used by step_inst_base helpers.
   Needed so gvs can rewrite through field equalities (e.g.
   s1.vs_memory = s2.vs_memory ==> mload x s1 = mload x s2). *)
val state_fn_defs = [mload_def, mstore_def, istore_def, mstore8_def, sload_def, sstore_def,
  tload_def, tstore_def, contract_storage_def, contract_transient_def,
  write_memory_with_expansion_def, write_memory_def, expand_memory_def,
  read_memory_def, mcopy_def];

(* Shared tactic for output_determined: close goals after opcode case split.
   After Cases_on opcode and gvs, handles:
   - PHI (resolve_phi_mem + operand agreement)
   - LOG (eval_operands_agree_lem on sublists)
   - General cases (res_tac + update_var/lookup_var + state fn expansion) *)
val transfer_close_tac =
  TRY (imp_res_tac resolve_phi_mem >> res_tac >> gvs[] >>
       gvs[update_var_def, lookup_var_def,
            finite_mapTheory.FLOOKUP_UPDATE] >> NO_TAC) >>
  TRY (gvs (update_var_def :: lookup_var_def ::
            finite_mapTheory.FLOOKUP_UPDATE :: state_fn_defs) >>
       res_tac >> gvs[] >> NO_TAC) >>
  TRY (
    `eval_operands (DROP 2 rest) s1 = eval_operands (DROP 2 rest) s2` by (
      irule eval_operands_agree_lem >> rpt strip_tac >>
      first_x_assum irule >>
      imp_res_tac mem_drop_subset >> gvs[]) >>
    `eval_operand (HD rest) s1 = eval_operand (HD rest) s2` by (
      first_x_assum irule >> Cases_on `rest` >> gvs[]) >>
    `eval_operand (EL 1 rest) s1 = eval_operand (EL 1 rest) s2` by (
      first_x_assum irule >>
      Cases_on `rest` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    gvs[] >> NO_TAC) >>
  rpt strip_tac >>
  res_tac >> gvs (update_var_def :: lookup_var_def ::
                  finite_mapTheory.FLOOKUP_UPDATE :: state_fn_defs);

Triviality exec_pure1_ok_transfer[local]:
  !f inst s v s'.
    exec_pure1 f inst s = OK v /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s' = eval_operand op s) ==>
    ?v'. exec_pure1 f inst s' = OK v'
Proof
  rw[exec_pure1_def] >> gvs[AllCaseEqs()] >> res_tac >> gvs[]
QED

Triviality exec_pure2_ok_transfer[local]:
  !f inst s v s'.
    exec_pure2 f inst s = OK v /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s' = eval_operand op s) ==>
    ?v'. exec_pure2 f inst s' = OK v'
Proof
  rw[exec_pure2_def] >> gvs[AllCaseEqs()] >> res_tac >> gvs[]
QED

Triviality exec_pure3_ok_transfer[local]:
  !f inst s v s'.
    exec_pure3 f inst s = OK v /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s' = eval_operand op s) ==>
    ?v'. exec_pure3 f inst s' = OK v'
Proof
  rw[exec_pure3_def] >> gvs[AllCaseEqs()] >> res_tac >> gvs[]
QED

Triviality exec_read0_ok_transfer[local]:
  !f inst s v s'.
    exec_read0 f inst s = OK v ==>
    ?v'. exec_read0 f inst s' = OK v'
Proof
  rw[exec_read0_def] >> gvs[AllCaseEqs()]
QED

Triviality exec_read1_ok_transfer[local]:
  !f inst s v s'.
    exec_read1 f inst s = OK v /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s' = eval_operand op s) ==>
    ?v'. exec_read1 f inst s' = OK v'
Proof
  rw[exec_read1_def] >> gvs[AllCaseEqs()] >> res_tac >> gvs[]
QED

Triviality exec_write2_ok_transfer[local]:
  !f inst s v s'.
    exec_write2 f inst s = OK v /\
    (!op. MEM op inst.inst_operands ==> eval_operand op s' = eval_operand op s) ==>
    ?v'. exec_write2 f inst s' = OK v'
Proof
  rw[exec_write2_def] >> gvs[AllCaseEqs()] >> res_tac >> gvs[]
QED

val exec_ok_transfer_thms =
  [exec_pure1_ok_transfer, exec_pure2_ok_transfer, exec_pure3_ok_transfer,
   exec_read0_ok_transfer, exec_read1_ok_transfer, exec_write2_ok_transfer];

val exec_ok_transfer_tac =
  FIRST (map (fn th => drule_all th >> simp[]) exec_ok_transfer_thms);

val ok_transfer_finish_tac =
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  rpt strip_tac >>
  TRY (exec_ok_transfer_tac >> NO_TAC) >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  TRY (imp_res_tac resolve_phi_mem >> res_tac >> gvs[] >> NO_TAC) >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  `eval_operands (DROP 2 rest) s' = eval_operands (DROP 2 rest) s` by (
    irule eval_operands_agree_lem >> rpt strip_tac >>
    first_x_assum irule >>
    imp_res_tac mem_drop_subset >> gvs[]) >>
  `eval_operand (HD rest) s' = eval_operand (HD rest) s` by (
    first_x_assum irule >> Cases_on `rest` >> gvs[]) >>
  `eval_operand (EL 1 rest) s' = eval_operand (EL 1 rest) s` by (
    first_x_assum irule >>
    Cases_on `rest` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  gvs[];

val transfer_determined_finish_tac =
  qpat_x_assum `step_inst_base _ s1 = _` mp_tac >>
  qpat_x_assum `step_inst_base _ s2 = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def] >>
  ntac 2 strip_tac >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  transfer_close_tac;

val output_vars_finish_tac =
  qpat_x_assum `step_inst_base _ s1 = _` mp_tac >>
  qpat_x_assum `step_inst_base _ s2 = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  TRY (imp_res_tac resolve_phi_mem >> res_tac >> gvs[] >>
       gvs[update_var_def, lookup_var_def,
            finite_mapTheory.FLOOKUP_UPDATE] >> NO_TAC) >>
  TRY (gvs (update_var_def :: lookup_var_def ::
            finite_mapTheory.FLOOKUP_UPDATE :: state_fn_defs) >>
       NO_TAC) >>
  TRY (
    `eval_operands (DROP 2 rest) s1 = eval_operands (DROP 2 rest) s2` by (
      irule eval_operands_agree_lem >> rpt strip_tac >>
      first_x_assum irule >>
      imp_res_tac mem_drop_subset >> gvs[]) >>
    `eval_operand (HD rest) s1 = eval_operand (HD rest) s2` by (
      first_x_assum irule >> Cases_on `rest` >> gvs[]) >>
    `eval_operand (EL 1 rest) s1 = eval_operand (EL 1 rest) s2` by (
      first_x_assum irule >>
      Cases_on `rest` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    gvs[] >> NO_TAC) >>
  res_tac >> gvs (update_var_def :: lookup_var_def ::
                  finite_mapTheory.FLOOKUP_UPDATE :: state_fn_defs);

(* OK transfer: if step_inst_base returns OK on s, it also returns OK on s'
   when operands agree and the conditional context fields match
   (PHI → vs_prev_bb, PARAM/FMP_PARAM → vs_params,
    RETURNDATACOPY → vs_returndata). *)
Theorem step_inst_base_ok_transfer:
  !inst s v s'.
    step_inst_base inst s = OK v /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s = eval_operand op s') /\
    (inst.inst_opcode = PHI ==> s.vs_prev_bb = s'.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s.vs_params = s'.vs_params) /\
    (inst.inst_opcode = FMP_PARAM ==> s.vs_params = s'.vs_params) /\
    (inst.inst_opcode = RETURNDATACOPY ==>
       s.vs_returndata = s'.vs_returndata) ==>
    ?v'. step_inst_base inst s' = OK v'
Proof
  rpt gen_tac >> strip_tac >>
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s' = eval_operand op s` by
    (rpt strip_tac >> res_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def]
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >- ok_transfer_finish_tac
  >> ok_transfer_finish_tac
QED

(* Per-field output determinism: for each written state field (memory,
   transient, accounts, immutables, returndata, logs), the output value
   is determined by operand agreement and the corresponding read-state
   field agreement. Accounts uses individual effect conditions
   (Eff_STORAGE, Eff_BALANCE) rather than a disjunction, matching the
   per-effect disjointness provided by effects_independent. *)
Theorem step_inst_base_output_determined_fields:
  !inst s1 s2 v1 v2.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s1.vs_params = s2.vs_params) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    (* Read-field agreements: individual effect conditions (not grouped) *)
    (Eff_MEMORY IN read_effects inst.inst_opcode ==>
       s1.vs_memory = s2.vs_memory) /\
    (Eff_TRANSIENT IN read_effects inst.inst_opcode ==>
       s1.vs_transient = s2.vs_transient) /\
    (Eff_STORAGE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_BALANCE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_IMMUTABLES IN read_effects inst.inst_opcode ==>
       s1.vs_immutables = s2.vs_immutables) /\
    (Eff_RETURNDATA IN read_effects inst.inst_opcode ==>
       s1.vs_returndata = s2.vs_returndata) /\
    (Eff_LOG IN read_effects inst.inst_opcode ==>
       s1.vs_logs = s2.vs_logs) ==>
    (* Memory *)
    (Eff_MEMORY IN write_effects inst.inst_opcode /\
     s1.vs_memory = s2.vs_memory ==>
       v1.vs_memory = v2.vs_memory) /\
    (* Transient *)
    (Eff_TRANSIENT IN write_effects inst.inst_opcode /\
     s1.vs_transient = s2.vs_transient ==>
       v1.vs_transient = v2.vs_transient) /\
    (* Accounts *)
    ((Eff_STORAGE IN write_effects inst.inst_opcode \/
      Eff_BALANCE IN write_effects inst.inst_opcode) /\
     s1.vs_accounts = s2.vs_accounts ==>
       v1.vs_accounts = v2.vs_accounts) /\
    (* Immutables *)
    (Eff_IMMUTABLES IN write_effects inst.inst_opcode /\
     s1.vs_immutables = s2.vs_immutables /\
     s1.vs_memory = s2.vs_memory ==>
       v1.vs_immutables = v2.vs_immutables) /\
    (* Returndata *)
    (Eff_RETURNDATA IN write_effects inst.inst_opcode /\
     s1.vs_returndata = s2.vs_returndata /\
     s1.vs_memory = s2.vs_memory ==>
       v1.vs_returndata = v2.vs_returndata) /\
    (* Logs *)
    (Eff_LOG IN write_effects inst.inst_opcode /\
     s1.vs_logs = s2.vs_logs /\
     s1.vs_memory = s2.vs_memory ==>
       v1.vs_logs = v2.vs_logs)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      read_effects_def, write_effects_def,
      all_effects_def, empty_effects_def]
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
QED

(* Combined scalar field agreement: given matching inputs (operands,
   scalar fields, conditional memory), ALL scalar fields of v1 and v2
   agree unconditionally. This combines step_inst_preserves_all (fields
   not written are preserved) with output_determined (fields written are
   determined by inputs). Proved by the same opcode case split. *)
Theorem step_inst_base_scalar_agree:
  !inst s1 s2 v1 v2.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s1.vs_params = s2.vs_params) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_params = s2.vs_params /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    (s1.vs_halted <=> s2.vs_halted) /\
    s1.vs_returndata = s2.vs_returndata /\
    (Eff_MEMORY IN read_effects inst.inst_opcode ==>
      s1.vs_memory = s2.vs_memory) ==>
    (v1.vs_halted <=> v2.vs_halted) /\
    v1.vs_returndata = v2.vs_returndata /\
    v1.vs_accounts = v2.vs_accounts /\
    v1.vs_transient = v2.vs_transient /\
    v1.vs_call_ctx = v2.vs_call_ctx /\
    v1.vs_tx_ctx = v2.vs_tx_ctx /\
    v1.vs_block_ctx = v2.vs_block_ctx /\
    v1.vs_logs = v2.vs_logs /\
    v1.vs_immutables = v2.vs_immutables /\
    v1.vs_data_section = v2.vs_data_section /\
    v1.vs_labels = v2.vs_labels /\
    v1.vs_code = v2.vs_code /\
    v1.vs_params = v2.vs_params /\
    v1.vs_fmp = v2.vs_fmp /\
    v1.vs_call_entry_fmp = v2.vs_call_entry_fmp /\
    v1.vs_initial_fmp = v2.vs_initial_fmp /\
    v1.vs_return_pc_token = v2.vs_return_pc_token /\
    v1.vs_prev_bb = v2.vs_prev_bb /\
    v1.vs_current_bb = v2.vs_current_bb /\
    v1.vs_inst_idx = v2.vs_inst_idx /\
    v1.vs_prev_hashes = v2.vs_prev_hashes
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      read_effects_def, write_effects_def,
      all_effects_def, empty_effects_def]
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- (qpat_x_assum `step_inst_base _ s1 = _` mp_tac >>
      qpat_x_assum `step_inst_base _ s2 = _` mp_tac >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
           exec_read0_def, exec_read1_def, exec_write2_def] >>
      ntac 2 strip_tac >>
      gvs[AllCaseEqs()] >>
      rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
      transfer_close_tac)
  >- (qpat_x_assum `step_inst_base _ s1 = _` mp_tac >>
      qpat_x_assum `step_inst_base _ s2 = _` mp_tac >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
           exec_read0_def, exec_read1_def, exec_write2_def] >>
      ntac 2 strip_tac >>
      gvs[AllCaseEqs()] >>
      rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
      transfer_close_tac)
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- transfer_determined_finish_tac
  >- (qpat_x_assum `step_inst_base _ s1 = _` mp_tac >>
      qpat_x_assum `step_inst_base _ s2 = _` mp_tac >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
           exec_read0_def, exec_read1_def, exec_write2_def] >>
      ntac 2 strip_tac >>
      gvs[AllCaseEqs()] >>
      rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
      transfer_close_tac)
  >> transfer_determined_finish_tac
QED


(* Output variable agreement: for non-term/non-alloca/non-ext-call ops,
   if operands agree, scalar fields + conditional memory agree, AND
   output var lookups agree on the INPUT states, then output var lookups
   agree on the RESULT states. The input agreement precondition is:
   - Automatically satisfied for effect-free ops (output determined by computation)
   - Needed for write-only ops (MSTORE etc) where lookup falls through to input state
   - INVOKE: step_inst_base returns Error, contradicts OK precondition *)
Theorem step_inst_base_output_vars_agree:
  !inst s1 s2 v1 v2.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s1.vs_params = s2.vs_params) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_params = s2.vs_params /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    (s1.vs_halted <=> s2.vs_halted) /\
    s1.vs_returndata = s2.vs_returndata /\
    LENGTH s1.vs_memory = LENGTH s2.vs_memory /\
    (Eff_MEMORY IN read_effects inst.inst_opcode ==>
      s1.vs_memory = s2.vs_memory) /\
    (!v. MEM v inst.inst_outputs ==>
         lookup_var v s1 = lookup_var v s2) ==>
    !v. MEM v inst.inst_outputs ==> lookup_var v v1 = lookup_var v v2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      read_effects_def, write_effects_def,
      all_effects_def, empty_effects_def]
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >- output_vars_finish_tac
  >> output_vars_finish_tac
QED

(* Output variable determinism for effect-free ops: if operands and
   read-state agree, the output variable values agree.
   Restricted to is_effect_free_op because write-only ops (MSTORE etc)
   don't write to vs_vars, so the conclusion is not provable for them. *)
Theorem step_inst_base_effect_free_output_determined_vars:
  !inst s1 s2 v1 v2.
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> NOP /\
    inst.inst_opcode <> PHI /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (inst.inst_opcode = PHI ==> s1.vs_prev_bb = s2.vs_prev_bb) /\
    (inst.inst_opcode = PARAM ==> s1.vs_params = s2.vs_params) /\
    (inst.inst_opcode = FMP_PARAM ==> s1.vs_params = s2.vs_params) /\
    (inst.inst_opcode = GETFMP ==> s1.vs_fmp = s2.vs_fmp) /\
    (inst.inst_opcode = INITIAL_FMP ==>
       s1.vs_initial_fmp = s2.vs_initial_fmp) /\
    (inst.inst_opcode = RETPC_PARAM ==>
       s1.vs_return_pc_token = s2.vs_return_pc_token) /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    (Eff_MEMORY IN read_effects inst.inst_opcode ==>
       s1.vs_memory = s2.vs_memory) /\
    (Eff_TRANSIENT IN read_effects inst.inst_opcode ==>
       s1.vs_transient = s2.vs_transient) /\
    (Eff_STORAGE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_BALANCE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
       s1.vs_accounts = s2.vs_accounts) /\
    (Eff_IMMUTABLES IN read_effects inst.inst_opcode ==>
       s1.vs_immutables = s2.vs_immutables) /\
    (Eff_RETURNDATA IN read_effects inst.inst_opcode ==>
       s1.vs_returndata = s2.vs_returndata) /\
    (Eff_LOG IN read_effects inst.inst_opcode ==>
       s1.vs_logs = s2.vs_logs) ==>
    !v. MEM v inst.inst_outputs ==> lookup_var v v1 = lookup_var v v2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_effect_free_op_def, is_terminator_def,
      read_effects_def, write_effects_def,
      all_effects_def, empty_effects_def]
  >- transfer_determined_finish_tac  (* ADD *)
  >- transfer_determined_finish_tac  (* SUB *)
  >- transfer_determined_finish_tac  (* MUL *)
  >- transfer_determined_finish_tac  (* Div *)
  >- transfer_determined_finish_tac  (* SDIV *)
  >- transfer_determined_finish_tac  (* Mod *)
  >- transfer_determined_finish_tac  (* SMOD *)
  >- transfer_determined_finish_tac  (* Exp *)
  >- transfer_determined_finish_tac  (* ADDMOD *)
  >- transfer_determined_finish_tac  (* MULMOD *)
  >- transfer_determined_finish_tac  (* EQ *)
  >- transfer_determined_finish_tac  (* LT *)
  >- transfer_determined_finish_tac  (* GT *)
  >- transfer_determined_finish_tac  (* SLT *)
  >- transfer_determined_finish_tac  (* SGT *)
  >- transfer_determined_finish_tac  (* ISZERO *)
  >- transfer_determined_finish_tac  (* AND *)
  >- transfer_determined_finish_tac  (* OR *)
  >- transfer_determined_finish_tac  (* XOR *)
  >- transfer_determined_finish_tac  (* NOT *)
  >- transfer_determined_finish_tac  (* SHL *)
  >- transfer_determined_finish_tac  (* SHR *)
  >- transfer_determined_finish_tac  (* SAR *)
  >- transfer_determined_finish_tac  (* SIGNEXTEND *)
  >- transfer_determined_finish_tac  (* BYTE *)
  >- transfer_determined_finish_tac  (* MLOAD *)
  >- transfer_determined_finish_tac  (* SLOAD *)
  >- transfer_determined_finish_tac  (* TLOAD *)
  >- transfer_determined_finish_tac  (* ILOAD *)
  >- transfer_determined_finish_tac  (* DLOAD *)
  >- transfer_determined_finish_tac  (* MEMTOP *)
  >- transfer_determined_finish_tac  (* SHA3 *)
  >- transfer_determined_finish_tac  (* CALLER *)
  >- transfer_determined_finish_tac  (* ADDRESS *)
  >- transfer_determined_finish_tac  (* CALLVALUE *)
  >- transfer_determined_finish_tac  (* GAS *)
  >- transfer_determined_finish_tac  (* ORIGIN *)
  >- transfer_determined_finish_tac  (* GASPRICE *)
  >- transfer_determined_finish_tac  (* CHAINID *)
  >- transfer_determined_finish_tac  (* COINBASE *)
  >- transfer_determined_finish_tac  (* TIMESTAMP *)
  >- transfer_determined_finish_tac  (* NUMBER *)
  >- transfer_determined_finish_tac  (* PREVRANDAO *)
  >- transfer_determined_finish_tac  (* GASLIMIT *)
  >- transfer_determined_finish_tac  (* BASEFEE *)
  >- transfer_determined_finish_tac  (* BLOBBASEFEE *)
  >- transfer_determined_finish_tac  (* BLOCKHASH *)
  >- transfer_determined_finish_tac  (* BLOBHASH *)
  >- transfer_determined_finish_tac  (* BALANCE *)
  >- transfer_determined_finish_tac  (* SELFBALANCE *)
  >- transfer_determined_finish_tac  (* CALLDATASIZE *)
  >- transfer_determined_finish_tac  (* CALLDATALOAD *)
  >- transfer_determined_finish_tac  (* RETURNDATASIZE *)
  >- transfer_determined_finish_tac  (* CODESIZE *)
  >- transfer_determined_finish_tac  (* EXTCODESIZE *)
  >- transfer_determined_finish_tac  (* EXTCODEHASH *)
  >- transfer_determined_finish_tac  (* ASSIGN *)
  >- transfer_determined_finish_tac  (* PARAM *)
  >> transfer_determined_finish_tac  (* remaining effect-free opcodes *)
QED


