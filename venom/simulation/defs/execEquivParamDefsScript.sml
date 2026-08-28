(*
 * Parameterized Execution Equivalence — Definitions
 *
 * Closure conditions on a (R_ok, R_term) relation pair that enable
 * step_inst_preserves_R (the master theorem).
 *
 * (state_equiv vars, execution_equiv vars) satisfies valid_state_rel.
 * This eliminates per-pass boilerplate (~800 LOC each for RTA, phi-elim, etc.)
 *
 * TOP-LEVEL:
 *   valid_state_rel — closure conditions on (R_ok, R_term) pair
 *)

Theory execEquivParamDefs
Ancestors
  stateEquiv venomExecSemantics venomState venomInst

(* Closure conditions on a (R_ok, R_term) relation pair.
   Any pair satisfying these supports step_inst_preserves_R.

   R_ok: used for OK results (continuation). Must preserve all state fields
         including control flow (needed for block_sim_function fuel induction).
   R_term: used for Halt/Revert results (terminal). May omit control flow
           fields since execution has stopped.

   Both must be closed under update_var, preserve eval_operand, and support
   reconstruction (non-vars field updates applied to both sides preserve the
   relation). *)
Definition valid_state_rel_def:
  valid_state_rel
    (R_ok : venom_state -> venom_state -> bool)
    (R_term : venom_state -> venom_state -> bool) <=>
    (* R_ok preserves all execution-relevant state fields including control flow *)
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_call_ctx = s2.vs_call_ctx /\
      s1.vs_tx_ctx = s2.vs_tx_ctx /\
      s1.vs_block_ctx = s2.vs_block_ctx /\
      s1.vs_accounts = s2.vs_accounts /\
      s1.vs_memory = s2.vs_memory /\
      s1.vs_transient = s2.vs_transient /\
      s1.vs_returndata = s2.vs_returndata /\
      s1.vs_halted = s2.vs_halted /\
      s1.vs_prev_bb = s2.vs_prev_bb /\
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      s1.vs_params = s2.vs_params /\
      s1.vs_fmp = s2.vs_fmp /\
      s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
      s1.vs_initial_fmp = s2.vs_initial_fmp /\
      s1.vs_return_pc_token = s2.vs_return_pc_token /\
      s1.vs_logs = s2.vs_logs /\
      s1.vs_immutables = s2.vs_immutables /\
      s1.vs_data_section = s2.vs_data_section /\
      s1.vs_labels = s2.vs_labels /\
      s1.vs_code = s2.vs_code /\
      s1.vs_prev_hashes = s2.vs_prev_hashes /\
      s1.vs_allocas = s2.vs_allocas /\
      s1.vs_alloca_next = s2.vs_alloca_next) /\
    (* R_term preserves execution-relevant fields (may omit control flow) *)
    (!s1 s2. R_term s1 s2 ==>
      s1.vs_call_ctx = s2.vs_call_ctx /\
      s1.vs_tx_ctx = s2.vs_tx_ctx /\
      s1.vs_block_ctx = s2.vs_block_ctx /\
      s1.vs_accounts = s2.vs_accounts /\
      s1.vs_memory = s2.vs_memory /\
      s1.vs_transient = s2.vs_transient /\
      s1.vs_returndata = s2.vs_returndata /\
      s1.vs_halted = s2.vs_halted /\
      s1.vs_params = s2.vs_params /\
      s1.vs_fmp = s2.vs_fmp /\
      s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
      s1.vs_initial_fmp = s2.vs_initial_fmp /\
      s1.vs_return_pc_token = s2.vs_return_pc_token /\
      s1.vs_logs = s2.vs_logs /\
      s1.vs_immutables = s2.vs_immutables /\
      s1.vs_data_section = s2.vs_data_section /\
      s1.vs_labels = s2.vs_labels /\
      s1.vs_code = s2.vs_code /\
      s1.vs_prev_hashes = s2.vs_prev_hashes /\
      s1.vs_allocas = s2.vs_allocas /\
      s1.vs_alloca_next = s2.vs_alloca_next) /\
    (* Both closed under var update *)
    (!s1 s2 x v. R_ok s1 s2 ==>
                  R_ok (update_var x v s1) (update_var x v s2)) /\
    (!s1 s2 x v. R_term s1 s2 ==>
                  R_term (update_var x v s1) (update_var x v s2)) /\
    (* Both preserve eval_operand when operand var agrees *)
    (!s1 s2 op. R_ok s1 s2 /\
       (!x. op = Var x ==> lookup_var x s1 = lookup_var x s2) ==>
       eval_operand op s1 = eval_operand op s2) /\
    (!s1 s2 op. R_term s1 s2 /\
       (!x. op = Var x ==> lookup_var x s1 = lookup_var x s2) ==>
       eval_operand op s1 = eval_operand op s2) /\
    (* R_ok implies R_term *)
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (* Both reflexive *)
    (!s. R_ok s s) /\
    (!s. R_term s s) /\
    (* Reconstruction: R_ok is determined by vs_vars given non-vars field agreement.
       If R_ok s1 s2 holds (constraining vs_vars), then any t1, t2 with the same
       vs_vars and agreeing non-vars fields are also R_ok-related.
       This enables closure under halt_state, jump_to, write_memory, etc. *)
    (!s1 s2 t1 t2. R_ok s1 s2 /\
      t1.vs_vars = s1.vs_vars /\ t2.vs_vars = s2.vs_vars /\
      t1.vs_call_ctx = t2.vs_call_ctx /\
      t1.vs_tx_ctx = t2.vs_tx_ctx /\
      t1.vs_block_ctx = t2.vs_block_ctx /\
      t1.vs_accounts = t2.vs_accounts /\
      t1.vs_memory = t2.vs_memory /\
      t1.vs_transient = t2.vs_transient /\
      t1.vs_returndata = t2.vs_returndata /\
      t1.vs_halted = t2.vs_halted /\
      t1.vs_prev_bb = t2.vs_prev_bb /\
      t1.vs_current_bb = t2.vs_current_bb /\
      t1.vs_inst_idx = t2.vs_inst_idx /\
      t1.vs_params = t2.vs_params /\
      t1.vs_fmp = t2.vs_fmp /\
      t1.vs_call_entry_fmp = t2.vs_call_entry_fmp /\
      t1.vs_initial_fmp = t2.vs_initial_fmp /\
      t1.vs_return_pc_token = t2.vs_return_pc_token /\
      t1.vs_logs = t2.vs_logs /\
      t1.vs_immutables = t2.vs_immutables /\
      t1.vs_data_section = t2.vs_data_section /\
      t1.vs_labels = t2.vs_labels /\
      t1.vs_code = t2.vs_code /\
      t1.vs_prev_hashes = t2.vs_prev_hashes /\
      t1.vs_allocas = t2.vs_allocas /\
      t1.vs_alloca_next = t2.vs_alloca_next
      ==> R_ok t1 t2) /\
    (* Reconstruction for R_term (same but R_term-tracked fields only) *)
    (!s1 s2 t1 t2. R_term s1 s2 /\
      t1.vs_vars = s1.vs_vars /\ t2.vs_vars = s2.vs_vars /\
      t1.vs_call_ctx = t2.vs_call_ctx /\
      t1.vs_tx_ctx = t2.vs_tx_ctx /\
      t1.vs_block_ctx = t2.vs_block_ctx /\
      t1.vs_accounts = t2.vs_accounts /\
      t1.vs_memory = t2.vs_memory /\
      t1.vs_transient = t2.vs_transient /\
      t1.vs_returndata = t2.vs_returndata /\
      t1.vs_halted = t2.vs_halted /\
      t1.vs_params = t2.vs_params /\
      t1.vs_fmp = t2.vs_fmp /\
      t1.vs_call_entry_fmp = t2.vs_call_entry_fmp /\
      t1.vs_initial_fmp = t2.vs_initial_fmp /\
      t1.vs_return_pc_token = t2.vs_return_pc_token /\
      t1.vs_logs = t2.vs_logs /\
      t1.vs_immutables = t2.vs_immutables /\
      t1.vs_data_section = t2.vs_data_section /\
      t1.vs_labels = t2.vs_labels /\
      t1.vs_code = t2.vs_code /\
      t1.vs_prev_hashes = t2.vs_prev_hashes /\
      t1.vs_allocas = t2.vs_allocas /\
      t1.vs_alloca_next = t2.vs_alloca_next
      ==> R_term t1 t2)
End
