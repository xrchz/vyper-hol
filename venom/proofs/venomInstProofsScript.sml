(*
 * Per-Opcode State Preservation Lemmas (Part 3: Write-Effects + Derived)
 *
 * Write-effects soundness, context field preservation, non-output
 * variable preservation, and derived equivalences.
 *
 * Split from venomInstProofsScript.sml for build timeout reasons.
 *)

Theory venomInstProofs
Ancestors
  venomInstProofs3 stateEquiv stateEquivProofs finite_map venomState
  venomExecSemantics venomInst venomEffects pred_set
  venomInstProofs1 venomInstProofs2

(* MERGE NOTE: resolved in favor of the eval-phis branch's split-file
   structure. origin/main had the older monolithic preservation proofs here;
   this branch moved those pieces into venomInstProofs1/2/3 for build-time
   reasons. If a theorem is missing after the merge, port only the needed
   lemma from origin/main into the appropriate split file. *)

(* Duplicate val bindings needed from Part 1 for tactic definitions *)
val reduce_to_base_tac =
  rw[Once step_inst_def] >> simp[step_inst_base_def];

val step_inst_lift_from_all_tac =
  fn field_fn =>
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  (Cases_on `ret.iret_adopt_fmp` >>
   gvs[bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def] >>
   qspecl_then [field_fn] mp_tac foldl_update_var_preserves >>
   simp[update_var_def]) >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def];

val write_finish_tac =
  gvs[AllCaseEqs(), exec_write2_def, exec_alloca_def, exec_ext_call_def,
      exec_delegatecall_def, exec_create_def,
      extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  simp[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
       write_memory_with_expansion_def, mcopy_def,
       contract_storage_def, revert_state_def,
       lookup_var_def, FLOOKUP_UPDATE, eval_operands_def];

(* ===================================================================== *)
(* ===== Write-Effects Soundness ======================================= *)
(* ===================================================================== *)

(* INVOKE is vacuously excluded (write_effects INVOKE = all_effects).
   Non-INVOKE reduces to step_inst_base via step_inst_non_invoke. *)

val write_effects_invoke_tac =
  gvs[write_effects_def, all_effects_def, empty_effects_def];

Theorem write_effects_sound_storage:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    contract_storage s' = contract_storage s
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_storage
QED

Theorem write_effects_sound_transient:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_TRANSIENT NOTIN write_effects inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_transient
QED

Theorem write_effects_sound_memory:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_memory >> gvs[is_terminator_def]
QED

Theorem write_effects_sound_immutables:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_IMMUTABLES NOTIN write_effects inst.inst_opcode ==>
    s'.vs_immutables = s.vs_immutables
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def]
QED

Theorem write_effects_sound_returndata:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_RETURNDATA NOTIN write_effects inst.inst_opcode ==>
    s'.vs_returndata = s.vs_returndata
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_all >> gvs[is_terminator_def]
QED

Theorem write_effects_sound_log:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_LOG NOTIN write_effects inst.inst_opcode ==>
    s'.vs_logs = s.vs_logs
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_log
QED

Theorem write_effects_sound_accounts:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    Eff_BALANCE NOTIN write_effects inst.inst_opcode /\
    Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
    s'.vs_accounts = s.vs_accounts
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  write_effects_invoke_tac >>
  imp_res_tac step_inst_base_preserves_accounts
QED

(* ===================================================================== *)
(* ===== Section 7: Context Field Preservation ========================= *)
(* ===================================================================== *)

Theorem step_preserves_call_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_call_ctx = s.vs_call_ctx
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_call_ctx`
QED

Theorem step_preserves_tx_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_tx_ctx = s.vs_tx_ctx
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_tx_ctx`
QED

Theorem step_preserves_block_ctx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_block_ctx = s.vs_block_ctx
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_block_ctx`
QED

Theorem step_preserves_code:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_code = s.vs_code
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_code`
QED

Theorem step_preserves_data_section:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_data_section = s.vs_data_section
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_data_section`
QED

Theorem step_preserves_labels:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_labels = s.vs_labels
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_labels`
QED

Theorem step_preserves_params:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_params = s.vs_params
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_params`
QED

Theorem step_preserves_prev_hashes:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_prev_hashes = s.vs_prev_hashes
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_prev_hashes`
QED

Theorem step_preserves_halted:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_halted = s.vs_halted
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_halted`
QED

Theorem step_preserves_current_bb[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_current_bb = s.vs_current_bb
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_current_bb`
QED

Theorem step_preserves_prev_bb[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==> s'.vs_prev_bb = s.vs_prev_bb
Proof
  step_inst_lift_from_all_tac `\s:venom_state. s.vs_prev_bb`
QED

Theorem step_preserves_control_flow:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  metis_tac[step_preserves_current_bb, step_inst_preserves_inst_idx,
            step_preserves_prev_bb]
QED

(* ===================================================================== *)
(* ===== Section 5b: Write-Opcode Class Preservation =================== *)
(* ===================================================================== *)

Theorem is_mem_write_not_terminator[local]:
  !op. is_mem_write_op op /\ op <> DRET ==> ~is_terminator op
Proof
  Cases >> EVAL_TAC
QED

Theorem is_alloca_not_terminator[local]:
  !op. is_alloca_op op ==> ~is_terminator op
Proof
  Cases >> EVAL_TAC
QED

Theorem is_ext_call_not_terminator[local]:
  !op. is_ext_call_op op ==> ~is_terminator op
Proof
  Cases >> EVAL_TAC
QED

(* Full tactic for opcode-class theorems *)
val step_class_write_tac =
  rw[Once step_inst_def, step_inst_base_def] >>
  gvs[AllCaseEqs(), is_mem_write_op_def, is_alloca_op_def,
      is_ext_call_op_def, is_terminator_def] >>
  write_finish_tac;

val mem_write_class_opcode_tac =
  gvs[Once step_inst_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  simp[Once step_inst_base_def] >>
  strip_tac >>
  gvs[exec_write2_def, AllCaseEqs()] >>
  gvs[mstore_def, mstore8_def, mcopy_def,
      write_memory_with_expansion_def,
      update_var_def, lookup_var_def] >>
  TRY (pairarg_tac >> gvs[] >>
       drule pack_dret_dynamic_preserves_non_memory >> simp[lookup_var_def]);

val alloca_class_opcode_tac =
  fs[Once step_inst_def] >>
  fs[Once step_inst_base_def] >>
  gvs[exec_alloca_def, AllCaseEqs(), update_var_def, lookup_var_def];

val ext_call_class_opcode_tac =
  qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
  simp[Once step_inst_def, Once step_inst_base_def] >>
  strip_tac >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
      extract_venom_result_def, AllCaseEqs(),
      update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  TRY (Cases_on `result` >> gvs[]) >>
  TRY (Cases_on `y` >> gvs[]);

Theorem step_mem_write_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ is_mem_write_op inst.inst_opcode ==>
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. lookup_var v s' = lookup_var v s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_mem_write_op_def]
  >- mem_write_class_opcode_tac
  >- mem_write_class_opcode_tac
  >- mem_write_class_opcode_tac
  >- mem_write_class_opcode_tac
  >- mem_write_class_opcode_tac
  >- mem_write_class_opcode_tac
  >- mem_write_class_opcode_tac
  >- mem_write_class_opcode_tac
  >- mem_write_class_opcode_tac
QED

Theorem step_alloca_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ is_alloca_op inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_transient = s.vs_transient /\
    s'.vs_accounts = s.vs_accounts /\
    s'.vs_logs = s.vs_logs /\
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_returndata = s.vs_returndata /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def]
  >- (qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
      simp[Once step_inst_def, step_inst_base_def] >>
      strip_tac >>
      gvs[exec_alloca_def, AllCaseEqs(), update_var_def, lookup_var_def,
          FLOOKUP_UPDATE])
QED

Theorem step_ext_call_preserves:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ is_ext_call_op inst.inst_opcode ==>
    s'.vs_immutables = s.vs_immutables /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_halted = s.vs_halted /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx /\
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels /\
    s'.vs_params = s.vs_params /\
    s'.vs_prev_hashes = s.vs_prev_hashes /\
    s'.vs_current_bb = s.vs_current_bb /\
    s'.vs_inst_idx = s.vs_inst_idx /\
    s'.vs_prev_bb = s.vs_prev_bb /\
    (!v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_ext_call_op_def]
  >- ext_call_class_opcode_tac
  >- ext_call_class_opcode_tac
  >- ext_call_class_opcode_tac
  >- ext_call_class_opcode_tac
  >- ext_call_class_opcode_tac
QED

(* ===================================================================== *)
(* ===== Section 4: Non-Output Variable Preservation =================== *)
(* ===================================================================== *)

Theorem foldl_update_var_lookup[local]:
  !kvs s v. ~MEM v (MAP FST kvs) ==>
    lookup_var v (FOLDL (\s' (k,w). update_var k w s') s kvs) = lookup_var v s
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >>
  rw[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem step_preserves_non_output_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    !v. ~MEM v inst.inst_outputs ==> lookup_var v s' = lookup_var v s
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  (* INVOKE case *)
  (Cases_on `ret.iret_adopt_fmp` >>
   gvs[bind_outputs_def, adopt_return_fmp_def, merge_callee_state_def] >>
   `~MEM v (MAP FST (ZIP (inst.inst_outputs, ret.iret_values)))` by
     simp[listTheory.MAP_ZIP] >>
   drule foldl_update_var_lookup >> simp[lookup_var_def]) >>
  (* Non-INVOKE: use mega-lemma *)
  metis_tac[step_inst_base_preserves_all, is_terminator_def]
QED

Theorem step_write2_preserves_all_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    (inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8 \/
     inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE) ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac step_mstore_preserves >> gvs[] >>
  imp_res_tac step_mstore8_preserves >> gvs[] >>
  imp_res_tac step_sstore_preserves >> gvs[] >>
  imp_res_tac step_tstore_preserves >> gvs[]
QED

(* ===================================================================== *)
(* ===== Section 3b: step_effect_free_state_equiv ====================== *)
(* ===================================================================== *)

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

Theorem step_inst_base_effect_free_state_equiv:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_effect_free_op_def]
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
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
  >- effect_free_opcode_tac
QED

Theorem step_effect_free_state_equiv:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    state_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (CCONTR_TAC >> gvs[is_effect_free_op_def]) >>
  `step_inst_base inst s = OK s'` by metis_tac[step_inst_non_invoke] >>
  metis_tac[step_inst_base_effect_free_state_equiv]
QED

(* ===================================================================== *)
(* ===== Section 8: Derived Equivalences =============================== *)
(* ===================================================================== *)

Theorem step_effect_free_execution_equiv:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    execution_equiv (set inst.inst_outputs) s s'
Proof
  rpt strip_tac >>
  imp_res_tac step_effect_free_state_equiv >>
  gvs[state_equiv_def]
QED

Theorem step_effect_free_same_value:
  !fuel ctx inst1 inst2 s s1 s2.
    step_inst fuel ctx inst1 s = OK s1 /\
    step_inst fuel ctx inst2 s = OK s2 /\
    is_effect_free_op inst1.inst_opcode /\
    is_effect_free_op inst2.inst_opcode /\
    inst1.inst_outputs = inst2.inst_outputs /\
    (!v. MEM v inst1.inst_outputs ==>
         lookup_var v s1 = lookup_var v s2) ==>
    state_equiv {} s1 s2
Proof
  rpt strip_tac >>
  `state_equiv (set inst1.inst_outputs) s s1`
    by metis_tac[step_effect_free_state_equiv] >>
  `state_equiv (set inst2.inst_outputs) s s2`
    by metis_tac[step_effect_free_state_equiv] >>
  gvs[state_equiv_def, execution_equiv_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `MEM v (inst1.inst_outputs)` >> gvs[] >>
  metis_tac[]
QED
