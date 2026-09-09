(*
 * Per-Opcode State Preservation Lemmas (Part 1: Core)
 *
 * Opcode classification, helper preservation, main preservation,
 * write-opcode field preservation, and mega-lemma infrastructure.
 *
 * Split from venomInstProofsScript.sml for build timeout reasons.
 *)

Theory venomInstProofs1
Ancestors
  venomExecSemantics venomEffects stateEquiv stateEquivProofs
  vfmStaticCalls finite_map venomState venomInst pred_set

(* ===================================================================== *)
(* ===== Section 1: Opcode Classification Properties ================== *)
(* ===================================================================== *)

Theorem is_effect_free_not_terminator:
  !op. is_effect_free_op op ==> ~is_terminator op
Proof
  Cases >> EVAL_TAC
QED

(* ===================================================================== *)
(* ===== Section 2: Helper-Level Preservation ========================== *)
(* ===================================================================== *)

Theorem update_var_state_equiv:
  !out v s. state_equiv {out} s (update_var out v s)
Proof
  rw[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

val exec_state_equiv_tac =
  gvs[AllCaseEqs()] >>
  irule state_equiv_subset >>
  qexists_tac `{out}` >>
  simp[update_var_state_equiv, SUBSET_DEF];

Theorem exec_pure1_state_equiv:
  !f inst s s'.
    exec_pure1 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_pure1_def] >> exec_state_equiv_tac
QED

Theorem exec_pure2_state_equiv:
  !f inst s s'.
    exec_pure2 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_pure2_def] >> exec_state_equiv_tac
QED

Theorem exec_pure3_state_equiv:
  !f inst s s'.
    exec_pure3 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_pure3_def] >> exec_state_equiv_tac
QED

Theorem exec_read0_state_equiv:
  !f inst s s'.
    exec_read0 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_read0_def] >> exec_state_equiv_tac
QED

Theorem exec_read1_state_equiv:
  !f inst s s'.
    exec_read1 f inst s = OK s' ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rw[exec_read1_def] >> exec_state_equiv_tac
QED

Triviality state_equiv_step_base_concl:
  !inst s s'.
    state_equiv (set inst.inst_outputs) s s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s) /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_fmp = s.vs_fmp /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  rw[state_equiv_def, execution_equiv_def] >>
  first_x_assum drule >> simp[]
QED

val exec_write2_tac =
  rw[exec_write2_def, AllCaseEqs()] >> gvs[];

Theorem exec_write2_preserves_vars:
  !f inst s s'.
    exec_write2 f inst s = OK s' /\
    (!v1 v2 s0. (f v1 v2 s0).vs_vars = s0.vs_vars) ==>
    (!v. lookup_var v s' = lookup_var v s)
Proof
  exec_write2_tac >> rw[lookup_var_def]
QED

Theorem exec_write2_preserves_control_flow:
  !f inst s s'.
    exec_write2 f inst s = OK s' /\
    (!v1 v2 s0. (f v1 v2 s0).vs_current_bb = s0.vs_current_bb /\
                (f v1 v2 s0).vs_inst_idx = s0.vs_inst_idx /\
                (f v1 v2 s0).vs_prev_bb = s0.vs_prev_bb) ==>
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  exec_write2_tac
QED

(* ===================================================================== *)
(* ===== Section 3: Main Preservation Theorems ========================= *)
(* ===================================================================== *)

(* NOP is identity: produces OK with unchanged state *)
val reduce_to_base_tac =
  rw[Once step_inst_def] >> simp[step_inst_base_def];

Theorem step_nop_identity:
  !fuel ctx inst s. inst.inst_opcode = NOP ==> step_inst fuel ctx inst s = OK s
Proof
  reduce_to_base_tac
QED

Theorem step_assert_identity:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ASSERT ==>
    s' = s
Proof
  rw[Once step_inst_def, step_inst_base_def] >> gvs[AllCaseEqs()]
QED

Theorem step_assert_unreachable_identity:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst.inst_opcode = ASSERT_UNREACHABLE ==>
    s' = s
Proof
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum `step_inst_base` mp_tac >>
  simp[Once step_inst_base_def] >> gvs[AllCaseEqs()] >> metis_tac[]
QED

(* ===================================================================== *)
(* ===== Section 5: Write-Opcode Field Preservation ==================== *)
(* ===================================================================== *)

Theorem step_mstore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = MSTORE ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[mstore_def, lookup_var_def]
QED

Theorem step_mstore8_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = MSTORE8 ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[mstore8_def, lookup_var_def]
QED

Theorem step_sstore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = SSTORE ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[sstore_def, lookup_var_def]
QED

Theorem step_tstore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = TSTORE ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[tstore_def, lookup_var_def]
QED

Theorem step_istore_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = ISTORE ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[istore_def, mstore_def, lookup_var_def]
QED

Theorem step_log_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ inst.inst_opcode = LOG ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  simp[Once step_inst_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qhdtm_x_assum`step_inst_base`mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >> gvs[exec_write2_def,AllCaseEqs()] >>
  simp[lookup_var_def]
QED

(* ===================================================================== *)
(* ===== Mega-Lemma Infrastructure ===================================== *)
(* ===================================================================== *)

(* FOLDL of update_var preserves any field that update_var preserves *)
Theorem foldl_update_var_preserves:
  !f. (!k v s. f (update_var k v s) = f s) ==>
      !kvs s. f (FOLDL (\s' (k,v). update_var k v s') s kvs) = f s
Proof
  strip_tac >> strip_tac >> Induct >>
  simp[pairTheory.FORALL_PROD]
QED

(* bind_outputs preserves any field that update_var preserves *)
Theorem bind_outputs_preserves:
  !f. (!k v s. f (update_var k v s) = f s) ==>
      !outs vals s s'. bind_outputs outs vals s = SOME s' ==> f s' = f s
Proof
  rw[bind_outputs_def] >> gvs[] >> metis_tac[foldl_update_var_preserves]
QED

(* Tactic: prove step_inst_base preserves a field for non-terminators.
   Includes write_effects/is_alloca_op for conditional preservation. *)
val step_base_field_finish_tac =
  gvs[AllCaseEqs(), is_terminator_def,
      write_effects_def, all_effects_def, empty_effects_def,
      is_alloca_op_def] >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     istore_def, write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def,
     lookup_var_def, FLOOKUP_UPDATE];

val step_base_field_tac =
  rw[step_inst_base_def] >> step_base_field_finish_tac;

Triviality nonterminator_opcode_class:
  !op. ~is_terminator op ==>
    is_effect_free_op op \/
    is_mem_write_op op \/
    is_alloca_op op \/
    is_ext_call_op op \/
    op = SSTORE \/ op = TSTORE \/ op = ISTORE \/ op = LOG \/
    op = SETFMP \/ op = DALLOCA \/
    op = ASSERT \/ op = ASSERT_UNREACHABLE \/ op = INVOKE
Proof
  Cases >> EVAL_TAC
QED

val effect_free_opcode_tac =
  fs[step_inst_base_def] >>
  FIRST [
    drule exec_pure1_state_equiv >> simp[],
    drule exec_pure2_state_equiv >> simp[],
    drule exec_pure3_state_equiv >> simp[],
    drule exec_read0_state_equiv >> simp[],
    drule exec_read1_state_equiv >> simp[],
    gvs[AllCaseEqs()] >>
    TRY (rename1 `state_equiv {ptr_out; next_out} _ _` >>
         simp[state_equiv_def, execution_equiv_def, update_var_def,
              lookup_var_def, FLOOKUP_UPDATE]) >>
    TRY (irule state_equiv_refl) >>
    TRY (irule state_equiv_subset >> qexists_tac `{out}` >>
         simp[update_var_state_equiv, SUBSET_DEF])
  ];

Triviality step_inst_base_effect_free_state_equiv_local:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_effect_free_op_def]
  (* 1--10 *)
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  (* 11--20 *)
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  (* 21--30 *)
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  (* 31--40 *)
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  (* 41--50 *)
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  (* 51--60 *)
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  (* 61--66 *)
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
QED

Theorem pack_dret_dynamic_preserves_non_memory:
  !pairs cursor s ptrs final_cursor s'.
    pack_dret_dynamic cursor pairs s = (ptrs,final_cursor,s') ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_vars = s.vs_vars /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Once pack_dret_dynamic_def] >>
  pairarg_tac >> gvs[] >>
  first_x_assum drule >>
  simp[mcopy_def, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[]
QED

val mem_write_opcode_tac =
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  fs[exec_write2_def] >>
  gvs[AllCaseEqs()] >>
  fs[mstore_def, mstore8_def, mcopy_def, write_memory_with_expansion_def,
     lookup_var_def, update_var_def, contract_storage_def,
     write_effects_def, is_alloca_op_def] >>
  TRY (pairarg_tac >> gvs[] >>
       drule pack_dret_dynamic_preserves_non_memory >> simp[]);

Triviality step_inst_base_mem_write_preserves_all:
  !inst s s'. step_inst_base inst s = OK s' /\
    is_mem_write_op inst.inst_opcode ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s) /\
    (~is_alloca_op inst.inst_opcode /\
     Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
     s'.vs_immutables = s.vs_immutables) /\
    (~is_alloca_op inst.inst_opcode /\
     Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
     s'.vs_returndata = s.vs_returndata) /\
    s'.vs_fmp = s.vs_fmp /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_mem_write_op_def]
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
QED

Triviality step_inst_base_mem_write_preserves_static_fields:
  !inst s s'. step_inst_base inst s = OK s' /\
    is_mem_write_op inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_accounts = s.vs_accounts /\
    contract_storage s' = contract_storage s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_mem_write_op_def]
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
  >- mem_write_opcode_tac
QED

(* Single mega-lemma: all fields preserved by step_inst_base for
   non-terminators. One 94-opcode case split instead of 11 separate ones.
   Also includes non-output variable preservation and conditional
   write-effects preservation (for fields not in write_effects). *)
Theorem step_inst_base_preserves_all:
  !inst s s'. step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s) /\
    (~is_alloca_op inst.inst_opcode /\
     Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
     s'.vs_immutables = s.vs_immutables) /\
    (~is_alloca_op inst.inst_opcode /\
     Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
     s'.vs_returndata = s.vs_returndata) /\
    (inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> DALLOCA /\
     ~is_alloca_op inst.inst_opcode ==> s'.vs_fmp = s.vs_fmp) /\
    s'.vs_call_entry_fmp = s.vs_call_entry_fmp /\
    s'.vs_initial_fmp = s.vs_initial_fmp /\
    s'.vs_return_pc_token = s.vs_return_pc_token
Proof
  rpt gen_tac >> strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- (drule_all step_inst_base_effect_free_state_equiv_local >>
      strip_tac >> drule state_equiv_step_base_concl >> simp[])
  >- (drule_all step_inst_base_mem_write_preserves_all >> simp[])
  >- (Cases_on `inst.inst_opcode` >>
      gvs[is_alloca_op_def] >>
      gvs[step_inst_base_def] >>
      step_base_field_finish_tac)
  >- suspend"g1"
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- (gvs[step_inst_base_def] >> step_base_field_finish_tac)
  >- gvs[step_inst_base_def]
QED

Resume step_inst_base_preserves_all[g1]:
      Cases_on `inst.inst_opcode` >>
      gvs[is_ext_call_op_def, is_terminator_def, is_alloca_op_def,
          write_effects_def, all_effects_def] >>
      qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
      PURE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[opcode_case_def] >>
      gvs[exec_ext_call_def, exec_delegatecall_def, AllCaseEqs(),
          extract_venom_result_def, update_var_def,
          pairTheory.UNCURRY, lookup_var_def] >>
      strip_tac >>
      gvs[FLOOKUP_UPDATE]
      >- (
        gvs[exec_create_def, AllCaseEqs(),
            extract_venom_result_def, update_var_def,
            pairTheory.UNCURRY, FLOOKUP_UPDATE])
      >- (
        gvs[exec_create_def, AllCaseEqs(),
            extract_venom_result_def, update_var_def,
            pairTheory.UNCURRY, FLOOKUP_UPDATE]) >>
      Cases_on `result` >> gvs[] >>
      Cases_on `y` >> gvs[]
QED

Finalise step_inst_base_preserves_all

Theorem step_inst_base_preserves_fmp_ordinary:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> SETFMP /\
    inst.inst_opcode <> DALLOCA ==>
    s'.vs_fmp = s.vs_fmp
Proof
  rpt strip_tac >>
  drule step_inst_base_preserves_all >> simp[]
QED

(* Generic lift: from step_inst_base mega-lemma to step_inst for any field *)
fun step_inst_lift_from_all_tac field_fn =
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  (gvs[bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def] >>
   qspecl_then [field_fn] mp_tac foldl_update_var_preserves >>
   simp[update_var_def]) >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def];
