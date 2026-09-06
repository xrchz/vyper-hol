Theory vyperCall

Ancestors
  vyperInterpreter

Definition extcall_call_def:
  extcall_call cx is_static (func_name, arg_types, ret_type) vs
               (accounts : evm_accounts) (tStorage : transient_storage) =
    case vs of
    | [] => NONE
    | target_v :: rest =>
    case dest_AddressV target_v of
    | NONE => NONE
    | SOME target_addr =>
    case (if is_static then SOME (NONE : num option, rest)
          else case rest of
               | [] => NONE
               | val_v :: rest' =>
                 case dest_NumV val_v of
                 | NONE => NONE
                 | SOME amount => SOME (SOME amount, rest')) of
    | NONE => NONE
    | SOME (value_opt, arg_vals) =>
    case build_ext_calldata (get_tenv cx) func_name arg_types arg_vals of
    | NONE => NONE
    | SOME calldata =>
    case run_ext_call cx.txn.target target_addr calldata value_opt
                      accounts tStorage (vyper_to_tx_params cx.txn) of
    | NONE => NONE
    | SOME (success, returnData, accounts', tStorage', emitted_logs) =>
      if ¬success then NONE
      else SOME (returnData, accounts', tStorage', emitted_logs)
End

Definition extcall_result_def:
  extcall_result cx is_static (func_name, arg_types, ret_type) vs
                 (accounts : evm_accounts) (tStorage : transient_storage) =
    case extcall_call cx is_static (func_name, arg_types, ret_type) vs
                      accounts tStorage of
    | NONE => NONE
    | SOME (returnData, accounts', tStorage', emitted_logs) =>
      case evaluate_abi_decode_return (get_tenv cx) ret_type returnData of
      | INR _ => NONE
      | INL ret_val =>
        SOME (ret_val, accounts', tStorage', emitted_logs)
End

Theorem eval_expr_intcall_drv:
  ∀cx ty nsid es drv.
    eval_expr cx (Call ty (IntCall nsid) es drv) =
    eval_expr cx (Call ty (IntCall nsid) es NONE)
Proof
  rpt gen_tac >>
  PairCases_on `nsid` >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [evaluate_def])) >>
  simp[]
QED

Theorem bind_arguments_length:
  ∀tenv args vs env.
    bind_arguments tenv args vs = SOME env ⇒ LENGTH args = LENGTH vs
Proof
  Induct_on `args` >> simp[bind_arguments_def] >>
  Cases_on `vs` >> simp[bind_arguments_def] >>
  rpt gen_tac >> PairCases_on `h'` >>
  simp[bind_arguments_def] >>
  Cases_on `evaluate_type tenv h'1` >> simp[] >>
  Cases_on `safe_cast x h` >> simp[] >>
  Cases_on `bind_arguments tenv args t` >> simp[] >>
  strip_tac >> res_tac
QED

(* ===== Log Lifecycle Boundaries (issue #439) ===== *)

Theorem push_log_logs[simp]:
  push_log ev st = (INL (), st with logs := st.logs ++ [ev])
Proof
  simp[push_log_def, vyperStateTheory.return_def]
QED

Theorem append_logs_logs[simp]:
  append_logs events st = (INL (), st with logs := st.logs ++ events)
Proof
  simp[append_logs_def, vyperStateTheory.return_def]
QED

Theorem extract_call_result_success_logs:
  final_state.contexts = [(ctxt, rollback)] ⇒
  extract_call_result orig_accounts orig_tStorage (INR NONE, final_state) =
    SOME (T, ctxt.returnData, final_state.rollback.accounts,
          final_state.rollback.tStorage, ctxt.logs)
Proof
  simp[extract_call_result_def]
QED

Theorem extract_call_result_reverted_logs:
  final_state.contexts = [(ctxt, rollback)] ⇒
  extract_call_result orig_accounts orig_tStorage
    (INR (SOME Reverted), final_state) =
    SOME (F, ctxt.returnData, orig_accounts, orig_tStorage, [])
Proof
  simp[extract_call_result_def]
QED

Theorem initial_state_logs[simp]:
  (initial_state am scopes).logs = am.logs
Proof
  simp[initial_state_def]
QED

Theorem clear_machine_logs_logs[simp]:
  (clear_machine_logs am).logs = []
Proof
  simp[clear_machine_logs_def]
QED

Theorem clear_machine_logs_preserves_machine:
  (clear_machine_logs am).sources = am.sources ∧
  (clear_machine_logs am).exports = am.exports ∧
  (clear_machine_logs am).immutables = am.immutables ∧
  (clear_machine_logs am).accounts = am.accounts ∧
  (clear_machine_logs am).layouts = am.layouts ∧
  (clear_machine_logs am).tStorage = am.tStorage
Proof
  simp[clear_machine_logs_def]
QED

Theorem call_external_transaction_clears_input_logs:
  call_external_transaction (am with logs := logs) tx =
  call_external_transaction am tx
Proof
  simp[call_external_transaction_def, clear_machine_logs_def]
QED

(* ===== Error Rollback Properties (issue #180) ===== *)

Theorem call_external_function_error_rollback:
  call_external_function am cx nr mut ts all_mods args dflts vals body ret = (INR e, am') ⇒
  am' = am
Proof
  simp[Once call_external_function_def, vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def] >>
  rpt strip_tac >>
  gvs[pairTheory.ELIM_UNCURRY, AllCaseEqs()]
QED

Theorem call_external_error_rollback:
  call_external am tx = (INR e, am') ⇒
  am' = am
Proof
  simp[Once call_external_def] >> strip_tac >> gvs[AllCaseEqs()] >> imp_res_tac call_external_function_error_rollback
QED

Theorem call_external_transaction_error_logs_empty:
  call_external_transaction am tx = (INR e, am') ⇒ am'.logs = []
Proof
  rw[call_external_transaction_def] >>
  drule call_external_error_rollback >>
  simp[]
QED

Theorem call_external_error_no_state_change:
  call_external am tx = (INR e, am') ⇒
  am'.accounts = am.accounts ∧
  am'.tStorage = am.tStorage ∧
  am'.immutables = am.immutables
Proof
  strip_tac >> imp_res_tac call_external_error_rollback >> gvs[]
QED
