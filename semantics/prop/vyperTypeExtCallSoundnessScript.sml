(*
 * External-call and low-level call helper lemmas for Vyper statement soundness.
 *
 * This theory factors the extcall/raw-call/create/selfdestruct helper cluster out
 * of vyperTypeStmtSoundness so it can be built/debugged independently.
 *)

Theory vyperTypeExtCallSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperCreate vyperInterpreter vyperState vyperContext vyperStorage vyperTyping
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult
  vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperAssignTarget vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
Libs
  wordsLib markerLib intLib

val _ = Parse.hide "from"

Theorem transfer_value_zero[simp]:
  transfer_value from to 0 st = (INL (), st)
Proof
  simp[transfer_value_def, return_def]
QED

Theorem transfer_value_same_address[simp]:
  transfer_value addr addr amount st = (INL (), st)
Proof
  simp[transfer_value_def, return_def]
QED

Theorem transfer_value_recipient_overflow_regression:
  let from = (0w:address) in
  let to = (1w:address) in
  let sender = empty_account_state with balance := 1 in
  let recipient = empty_account_state with balance := 2 ** 256 - 1 in
  let st = empty_state with accounts :=
             update_account from sender (update_account to recipient empty_accounts) in
    accounts_well_typed st.accounts /\
    FST (transfer_value from to 1 st) <> INL () /\
    accounts_well_typed (SND (transfer_value from to 1 st)).accounts
Proof
  EVAL_TAC >> gen_tac >>
  Cases_on `addr = 0w` >> gvs[] >>
  Cases_on `addr = 1w` >> gvs[]
QED

Theorem make_ext_call_state_value_transfer_can_break_accounts_well_typed:
  let caller = (0w:address) in
  let callee = (1w:address) in
  let caller_acct = empty_account_state with balance := 1 in
  let callee_acct = empty_account_state with balance := 2 ** 256 - 1 in
  let accounts = update_account caller caller_acct
                   (update_account callee callee_acct empty_accounts) in
  let st0 = make_ext_call_state caller callee [] [] (SOME 1)
              accounts empty_transient_storage (vyper_to_tx_params empty_call_txn) in
    accounts_well_typed accounts /\
    ~accounts_well_typed st0.rollback.accounts
Proof
  EVAL_TAC >> conj_tac
  >- (gen_tac >>
      Cases_on `addr = 0w` >> gvs[] >>
      Cases_on `addr = 1w` >> gvs[]) >>
  strip_tac >>
  first_x_assum (qspec_then `1w:address` mp_tac) >> EVAL_TAC
QED
Theorem extract_call_result_success_exposes_bad_accounts:
  let caller = (0w:address) in
  let callee = (1w:address) in
  let caller_acct = empty_account_state with balance := 1 in
  let callee_acct = empty_account_state with balance := 2 ** 256 - 1 in
  let good_accounts = update_account caller caller_acct
                        (update_account callee callee_acct empty_accounts) in
  let bad_accounts = (make_ext_call_state caller callee [] [] (SOME 1)
                        good_accounts empty_transient_storage
                        (vyper_to_tx_params empty_call_txn)).rollback.accounts in
  let final_state = (make_ext_call_state caller callee [] [] (SOME 1)
                       good_accounts empty_transient_storage
                       (vyper_to_tx_params empty_call_txn)) with
                      rollback updated_by (\rb. rb with accounts := bad_accounts) in
    accounts_well_typed good_accounts /\
    ~accounts_well_typed bad_accounts /\
    ?retData tStorage' emitted_logs.
      extract_call_result good_accounts empty_transient_storage
        (INR NONE, final_state) =
        SOME (T, retData, bad_accounts, tStorage', emitted_logs)
Proof
  EVAL_TAC >> conj_tac
  >- (gen_tac >>
      Cases_on `addr = 0w` >> gvs[] >>
      Cases_on `addr = 1w` >> gvs[]) >>
  conj_tac
  >- (strip_tac >>
      first_x_assum (qspec_then `1w:address` mp_tac) >> EVAL_TAC) >>
  qexists_tac `[]` >>
  qexists_tac `empty_transient_storage` >>
  qexists_tac `[]` >>
  EVAL_TAC
QED

Theorem run_ext_call_overflowing_value_transfer_rejected:
  let caller = (0w:address) in
  let callee = (1w:address) in
  let caller_acct = empty_account_state with balance := 1 in
  let callee_acct = empty_account_state with balance := 2 ** 256 - 1 in
  let accounts = update_account caller caller_acct
                   (update_account callee callee_acct empty_accounts) in
    run_ext_call caller callee [] (SOME 1) accounts empty_transient_storage
      (vyper_to_tx_params empty_call_txn) = NONE
Proof
  EVAL_TAC
QED

Theorem accounts_runtime_well_typed_accounts_well_typed:
  !acc. accounts_runtime_well_typed acc <=> accounts_well_typed acc
Proof
  simp[accounts_runtime_well_typed_def, accounts_well_typed_def,
       account_runtime_well_typed_def, account_well_typed_def]
QED

Theorem ext_call_success_accounts_ok_imp_extract_premise:
  !outcome.
    ext_call_success_accounts_ok outcome ==>
    (case FST outcome of
     | INR NONE => accounts_well_typed (SND outcome).rollback.accounts
     | _ => T)
Proof
  Cases >> rename1 `(result, final_state)` >>
  Cases_on `result` >>
  simp[ext_call_success_accounts_ok_def, ext_call_success_accounts_ok_aux_def,
       accounts_runtime_well_typed_accounts_well_typed] >>
  Cases_on `y` >> simp[]
QED

Theorem extract_call_result_accounts_well_typed:
  !orig_accounts orig_tStorage result final_state
   success retData accounts' tStorage' emitted_logs.
    accounts_well_typed orig_accounts /\
    (case result of
     | INR NONE => accounts_well_typed final_state.rollback.accounts
     | _ => T) /\
    extract_call_result orig_accounts orig_tStorage (result, final_state) =
      SOME (success, retData, accounts', tStorage', emitted_logs) ==>
    accounts_well_typed accounts'
Proof
  rw[extract_call_result_def] >>
  gvs[AllCaseEqs()]
QED

Theorem run_ext_call_accounts_well_typed:
  !caller callee calldata value_opt accounts tStorage txParams
   success retData accounts' tStorage' emitted_logs.
    accounts_well_typed accounts /\
    run_ext_call caller callee calldata value_opt accounts tStorage txParams =
      SOME (success, retData, accounts', tStorage', emitted_logs) ==>
    accounts_well_typed accounts'
Proof
  rw[run_ext_call_def] >>
  gvs[AllCaseEqs()] >>
  qmatch_asmsub_abbrev_tac `extract_call_result _ _ outcome = SOME _` >>
  PairCases_on `outcome` >>
  drule ext_call_success_accounts_ok_imp_extract_premise >>
  strip_tac >>
  qspecl_then [`accounts`, `tStorage`, `outcome0`, `outcome1`,
               `success`, `retData`, `accounts'`, `tStorage'`]
    mp_tac extract_call_result_accounts_well_typed >>
  simp[] >>
  gvs[]
QED

Theorem vfm_transfer_value_accounts_well_typed:
  !from to amount accounts.
    accounts_well_typed accounts /\
    amount <= (lookup_account from accounts).balance /\
    (lookup_account to accounts).balance + amount < 2 ** 256 ==>
    accounts_well_typed (vfmExecution$transfer_value from to amount accounts)
Proof
  rw[vfmExecutionTheory.transfer_value_def] >>
  gvs[accounts_well_typed_def, account_well_typed_def,
      vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  first_x_assum (qspec_then `addr` mp_tac) >> decide_tac
QED

Theorem guarded_make_ext_call_state_accounts_well_typed:
  !caller callee code calldata value_opt accounts tStorage txParams.
    accounts_well_typed accounts /\
    ext_call_value_transfer_ok caller callee value_opt accounts ==>
    accounts_well_typed
      (make_ext_call_state caller callee code calldata value_opt
         accounts tStorage txParams).rollback.accounts
Proof
  rw[make_ext_call_state_def, ext_call_value_transfer_ok_def] >>
  Cases_on `value_opt` >> gvs[]
  >- simp[vfmExecutionTheory.transfer_value_def] >>
  irule vfm_transfer_value_accounts_well_typed >>
  simp[] >>
  decide_tac
QED

Theorem transfer_value_no_type_error:
  !from to amount st s.
    FST (transfer_value from to amount st) <> INR (Error (TypeError s))
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem transfer_value_accounts_well_typed:
  !from to amount st.
    accounts_well_typed st.accounts ==>
    accounts_well_typed (SND (transfer_value from to amount st)).accounts
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  gvs[accounts_well_typed_def, account_well_typed_def,
      vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  first_x_assum (qspec_then `addr` mp_tac) >>
  simp[vfmStateTheory.update_account_def, combinTheory.APPLY_UPDATE_THM] >>
  rpt (IF_CASES_TAC >> gvs[]) >> decide_tac
QED

Theorem transfer_value_runtime_consistent:
  !env cx fromAddr toAddr amount st.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (SND (transfer_value fromAddr toAddr amount st))
Proof
  rpt strip_tac >>
  Cases_on `transfer_value fromAddr toAddr amount st` >>
  rename1 `transfer_value fromAddr toAddr amount st = (res,st')` >>
  gvs[runtime_consistent_def] >>
  `st'.scopes = st.scopes` by metis_tac[transfer_value_scopes] >>
  `st'.immutables = st.immutables` by metis_tac[transfer_value_immutables] >>
  gvs[env_consistent_def, env_scopes_consistent_def,
      env_immutables_consistent_def, state_well_typed_def] >>
  rpt conj_tac >- metis_tac[] >- metis_tac[] >- metis_tac[] >>
  qspecl_then [`fromAddr`, `toAddr`, `amount`, `st`] mp_tac
    transfer_value_accounts_well_typed >>
  simp[]
QED

Theorem evaluate_abi_decode_return_well_typed:
  !tenv ret_type bs v tv.
    evaluate_abi_decode_return tenv ret_type bs = INL v /\
    evaluate_type tenv ret_type = SOME tv ==>
    value_has_type tv v
Proof
  rpt strip_tac >>
  gvs[evaluate_abi_decode_return_def, AllCaseEqs(), LET_THM] >>
  TRY (metis_tac[evaluate_abi_decode_well_typed]) >>
  `evaluate_type tenv (TupleT [ret_type]) = SOME (TupleTV [tv])` by (
    imp_res_tac (cj 1 evaluate_type_well_formed) >>
    imp_res_tac well_formed_type_value_slot_size >>
    gvs[evaluate_type_def, OPT_MMAP_def, type_slot_size_def,
        wordsTheory.dimword_def]) >>
  drule_all evaluate_abi_decode_well_typed >> strip_tac >>
  gvs[value_has_type_inv, value_has_type_def]
QED

Theorem update_accounts_transient_runtime_consistent:
  runtime_consistent env cx st /\ accounts_well_typed accounts' ==>
  runtime_consistent env cx (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  rw[runtime_consistent_def, state_well_typed_def, env_consistent_def] >>
  gvs[env_scopes_consistent_def, env_immutables_consistent_def] >>
  metis_tac[]
QED


Theorem extcall_return_tail_sound:
  !env cx es drv ret_type ret_tv returnData st res st'.
    runtime_consistent env cx st /\ functions_well_typed cx /\
    well_typed_opt env drv /\
    evaluate_type env.type_defs ret_type = SOME ret_tv /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
     else do
       ret_val <- lift_sum_runtime (evaluate_abi_decode_return env.type_defs ret_type returnData);
       return (Value ret_val)
     od) st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall stat fsig) es drv) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `returnData = [] /\ IS_SOME drv` >> gvs[]
  >- (
    Cases_on `drv` >> gvs[Once well_typed_expr_def, runtime_consistent_def] >>
    qpat_x_assum `!env0 st0 res0 st0'. _`
      (qspecl_then [`env`, `st`, `res`, `st'`] mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on `res` >> gvs[expr_result_typed_def, expr_runtime_typed_def, expr_type_def] >>
    metis_tac[well_typed_expr_not_hashmap_place]) >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[lift_sum_runtime_def, bind_def, return_def, raise_def] >>
  Cases_on `evaluate_abi_decode_return env.type_defs ret_type returnData` >>
  gvs[return_def, raise_def, no_type_error_result_def,
      expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
      toplevel_value_typed_def, is_HashMapRef_def] >>
  strip_tac >> gvs[is_HashMapRef_def, runtime_consistent_def] >>
  qspecl_then [`env.type_defs`, `ret_type`, `returnData`, `x`, `ret_tv`]
    mp_tac evaluate_abi_decode_return_well_typed >>
  simp[toplevel_value_typed_def]
QED

Theorem runtime_consistent_logs_append:
  !env cx st ls.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (st with logs := st.logs ++ ls)
Proof
  rw[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED

Theorem append_logs_runtime_consistent:
  !env cx logs st res st'.
    runtime_consistent env cx st /\
    append_logs logs st = (res,st') ==>
    runtime_consistent env cx st'
Proof
  rw[append_logs_def, return_def] >>
  metis_tac[runtime_consistent_logs_append]
QED

Theorem extcall_after_state_update_tail_sound:
  !env cx es stat func_name arg_types ret_type ret_tv drv returnData
   base_st accounts' tStorage' res st'.
    runtime_consistent env cx base_st /\ functions_well_typed cx /\
    accounts_well_typed accounts' /\ well_typed_opt env drv /\
    evaluate_type env.type_defs ret_type = SOME ret_tv /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
     else do
       ret_val <- lift_sum_runtime (evaluate_abi_decode_return env.type_defs ret_type returnData);
       return (Value ret_val)
     od) (base_st with <| accounts := accounts'; tStorage := tStorage' |>) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_consistent env cx
     (base_st with <| accounts := accounts'; tStorage := tStorage' |>)` by
    metis_tac[update_accounts_transient_runtime_consistent] >>
  irule extcall_return_tail_sound >>
  metis_tac[]
QED


Theorem extcall_after_state_update_tail_sound_cond_driver_ih:
  !env cx es stat func_name arg_types ret_type drv returnData
   base_st accounts' tStorage' res st'.
    runtime_consistent env cx base_st /\ functions_well_typed cx /\
    accounts_well_typed accounts' /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (returnData = [] /\ IS_SOME drv ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\
        context_well_typed cx /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
        (well_typed_expr env0 (THE drv) ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
     else do
       ret_val <- lift_sum_runtime (evaluate_abi_decode_return env.type_defs ret_type returnData);
       return (Value ret_val)
     od) (base_st with <| accounts := accounts'; tStorage := tStorage' |>) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_formed_type env.type_defs ret_type` mp_tac >>
  simp[well_formed_type_def, IS_SOME_EXISTS] >> strip_tac >>
  rename1 `evaluate_type env.type_defs ret_type = SOME ret_tv` >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  Cases_on `returnData = [] /\ IS_SOME drv` >> gvs[]
  >- (
    Cases_on `drv` >> gvs[Once well_typed_expr_def] >>
    qpat_x_assum `!env0 st0 res0 st0'. _`
      (qspecl_then [`env`, `base_st with <| accounts := accounts'; tStorage := tStorage' |>`, `res`, `st'`] mp_tac) >>
    simp[update_accounts_transient_runtime_consistent] >> strip_tac >>
    strip_tac >>
    strip_tac >>
    qpat_x_assum `env_consistent _ _ _ /\ state_well_typed _ /\ context_well_typed _ /\ eval_expr _ _ _ = _ ==> _` mp_tac >>
    (impl_tac >- (simp[] >> metis_tac[update_accounts_transient_runtime_consistent, runtime_consistent_def])) >>
    strip_tac >>
    Cases_on `res` >> gvs[expr_result_typed_def, expr_runtime_typed_def, expr_type_def] >>
    metis_tac[well_typed_expr_not_hashmap_place]) >>
  `runtime_consistent env cx (base_st with <| accounts := accounts'; tStorage := tStorage' |>)` by
    metis_tac[update_accounts_transient_runtime_consistent] >>
  gvs[runtime_consistent_def] >>
  gvs[lift_sum_runtime_def, bind_def, return_def, raise_def] >>
  Cases_on `evaluate_abi_decode_return env.type_defs ret_type returnData` >>
  gvs[return_def, raise_def, no_type_error_result_def,
      expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
      toplevel_value_typed_def, is_HashMapRef_def] >>
  qspecl_then [`env.type_defs`, `ret_type`, `returnData`, `x`, `ret_tv`]
    mp_tac evaluate_abi_decode_return_well_typed >>
  simp[toplevel_value_typed_def] >> strip_tac >> strip_tac >>
  Cases_on `returnData = []` >>
  gvs[lift_sum_runtime_def, bind_def, return_def, raise_def,
      no_type_error_result_def, expr_result_typed_def, expr_runtime_typed_def,
      expr_type_def, toplevel_value_typed_def, is_HashMapRef_def]
QED
Theorem env_consistent_get_tenv:
  env_consistent env cx st ==> get_tenv cx = env.type_defs
Proof
  rw[env_consistent_def, env_context_consistent_def]
QED

Theorem runtime_consistent_get_tenv:
  runtime_consistent env cx st ==> get_tenv cx = env.type_defs
Proof
  rw[runtime_consistent_def, env_consistent_def, env_context_consistent_def]
QED

Theorem extcall_after_state_update_tail_sound_cond_driver_ih_get_tenv:
  !env cx es stat func_name arg_types ret_type drv returnData
   base_st accounts' tStorage' res st'.
    runtime_consistent env cx base_st /\ functions_well_typed cx /\
    accounts_well_typed accounts' /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (returnData = [] /\ IS_SOME drv ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\
        context_well_typed cx /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
        (well_typed_expr env0 (THE drv) ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
     else do
       ret_val <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
       return (Value ret_val)
     od) (base_st with <| accounts := accounts'; tStorage := tStorage' |>) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  `get_tenv cx = env.type_defs` by metis_tac[runtime_consistent_get_tenv] >>
  gvs[] >>
  qspecl_then [`env`, `cx`, `es`, `stat`, `func_name`, `arg_types`, `ret_type`,
                `drv`, `returnData`, `base_st`, `accounts'`, `tStorage'`, `res`, `st'`]
    mp_tac extcall_after_state_update_tail_sound_cond_driver_ih >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- metis_tac[] >>
    first_assum ACCEPT_TAC) >>
  simp[]
QED

Theorem extcall_nonstatic_success_tail_sound_cond_driver_ih:
  !env cx es func_name arg_types ret_type drv args_st pr1 pr2 pr3 res st'.
    runtime_consistent env cx args_st /\ functions_well_typed cx /\
    accounts_well_typed pr2 /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (pr1 = [] /\ IS_SOME drv ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\
        context_well_typed cx /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
        (well_typed_expr env0 (THE drv) ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (if pr1 = [] /\ IS_SOME drv then eval_expr cx (THE drv)
     else do
       ret_val <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type pr1);
       return (Value ret_val)
     od) (args_st with <|accounts := pr2; tStorage := pr3|>) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`env`, `cx`, `es`, `F`, `func_name`, `arg_types`, `ret_type`,
               `drv`, `pr1`, `args_st`, `pr2`, `pr3`, `res`, `st'`]
    mp_tac extcall_after_state_update_tail_sound_cond_driver_ih_get_tenv >>
  disch_then irule >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED


Theorem extcall_success_continuation_sound:
  !env cx args_st accounts' tStorage' returnData res st'
   is_static func_name arg_types ret_type es drv.
    runtime_consistent env cx args_st /\ functions_well_typed cx /\
    accounts_well_typed accounts' /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (do
       _ <- assert T (Error (RuntimeError "ExtCall reverted"));
       _ <- update_accounts (K accounts');
       _ <- update_transient (K tStorage');
       if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
       else do
         ret_val <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
         return (Value ret_val)
       od
     od) args_st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  gvs[assert_def, bind_def, return_def, update_accounts_def, update_transient_def] >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  rename1 `evaluate_type env.type_defs ret_type = SOME ret_tv` >>
  `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv, runtime_consistent_def] >>
  gvs[] >>
  irule extcall_after_state_update_tail_sound >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`accounts'`, `args_st`, `returnData`, `tStorage'`] >>
  simp[IS_SOME_EXISTS]
QED


Theorem extcall_success_continuation_sound_cond_driver_ih:
  !env cx args_st accounts' tStorage' returnData res st'
   is_static func_name arg_types ret_type es drv.
    runtime_consistent env cx args_st /\ functions_well_typed cx /\
    accounts_well_typed accounts' /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (returnData = [] /\ IS_SOME drv ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\
        context_well_typed cx /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
        (well_typed_expr env0 (THE drv) ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (do
       _ <- assert T (Error (RuntimeError "ExtCall reverted"));
       _ <- update_accounts (K accounts');
       _ <- update_transient (K tStorage');
       if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
       else do
         ret_val <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
         return (Value ret_val)
       od
     od) args_st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(do _ od) args_st = (res,st')` mp_tac >>
  simp[assert_def, bind_def, return_def, update_accounts_def, update_transient_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `well_formed_type env.type_defs ret_type` mp_tac >>
  simp[well_formed_type_def, IS_SOME_EXISTS] >> strip_tac >>
  rename1 `evaluate_type env.type_defs ret_type = SOME ret_tv` >>
  `get_tenv cx = env.type_defs` by (
    drule runtime_consistent_get_tenv >>
    simp[]) >>
  gvs[] >>
  Cases_on `returnData = [] /\ IS_SOME drv` >> gvs[]
  >- (
    Cases_on `drv` >> gvs[Once well_typed_expr_def] >>
    qpat_x_assum `!env0 st0 res0 st0'. _`
      (qspecl_then [`env`, `args_st with <| accounts := accounts'; tStorage := tStorage' |>`, `res`, `st'`] mp_tac) >>
    simp[update_accounts_transient_runtime_consistent] >> strip_tac >>
    qpat_x_assum `env_consistent _ _ _ /\ state_well_typed _ /\ context_well_typed _ ==> _` mp_tac >>
    (impl_tac >- metis_tac[update_accounts_transient_runtime_consistent, runtime_consistent_def]) >>
    strip_tac >>
    Cases_on `res` >> gvs[expr_result_typed_def, expr_runtime_typed_def, expr_type_def] >>
    metis_tac[well_typed_expr_not_hashmap_place]) >>
  `runtime_consistent env cx (args_st with <| accounts := accounts'; tStorage := tStorage' |>)` by
    metis_tac[update_accounts_transient_runtime_consistent] >>
  gvs[runtime_consistent_def] >>
  gvs[lift_sum_runtime_def, bind_def, return_def, raise_def] >>
  Cases_on `evaluate_abi_decode_return env.type_defs ret_type returnData` >>
  gvs[return_def, raise_def, no_type_error_result_def,
      expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
      toplevel_value_typed_def, is_HashMapRef_def] >>
  qspecl_then [`env.type_defs`, `ret_type`, `returnData`, `x`, `ret_tv`]
    mp_tac evaluate_abi_decode_return_well_typed >>
  simp[toplevel_value_typed_def]
QED

Theorem extcall_success_continuation_state_well_typed:
  !env cx args_st accounts' tStorage' returnData res st'
   is_static func_name arg_types ret_type es drv.
    runtime_consistent env cx args_st /\ functions_well_typed cx /\
    accounts_well_typed accounts' /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    (returnData = [] /\ IS_SOME drv ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\
        context_well_typed cx /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
        (well_typed_expr env0 (THE drv) ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    (do
       _ <- assert T (Error (RuntimeError "ExtCall reverted"));
       _ <- update_accounts (K accounts');
       _ <- update_transient (K tStorage');
       if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
       else do
         ret_val <- lift_sum_runtime (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
         return (Value ret_val)
       od
     od) args_st = (res,st') ==>
    state_well_typed st'
Proof
  rpt strip_tac >>
  drule_all extcall_success_continuation_sound_cond_driver_ih >>
  simp[]
QED







Theorem extcall_static_args_runtime_typed_dest:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: arg_tys ==>
  ?target_addr. dest_AddressV (HD vs) = SOME target_addr
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def]
QED

Theorem values_have_types_LIST_REL_extcall[local]:
  !tvs vs. values_have_types tvs vs <=> LIST_REL value_has_type tvs vs
Proof
  Induct >> Cases_on `vs` >> simp[Once value_has_type_def]
QED

Theorem LIST_REL_evaluate_expr_types[local]:
  !es tvs.
    LIST_REL (\e tv. evaluate_type tenv (expr_type e) = SOME tv) es tvs ==>
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) (MAP expr_type es) tvs
Proof
  Induct >> Cases_on `tvs` >> simp[]
QED

Theorem extcall_static_args_runtime_typed_tail:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: arg_tys ==>
  ?tvs.
    LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv) arg_tys tvs /\
    values_have_types tvs (TL vs)
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> Cases_on `vs` >>
  gvs[values_have_types_LIST_REL_extcall] >>
  metis_tac[LIST_REL_evaluate_expr_types]
QED

Theorem extcall_static_args_runtime_typed_nonempty:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: arg_tys ==>
  vs <> []
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `vs` >> gvs[listTheory.LIST_REL_EL_EQN]
QED

Theorem extcall_nonstatic_args_runtime_typed_dest:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: BaseT (UintT 256) :: arg_tys ==>
  ?target_addr amount. dest_AddressV (HD vs) = SOME target_addr /\
                       dest_NumV (HD (TL vs)) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> gvs[] >>
  Cases_on `t` >> gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  rename1 `value_has_type (BaseTV (UintT 256)) v_amt` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `v_amt` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED


Theorem extcall_nonstatic_args_runtime_typed_tail:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: BaseT (UintT 256) :: arg_tys ==>
  ?tvs.
    LIST_REL (\ty tv. evaluate_type env.type_defs ty = SOME tv) arg_tys tvs /\
    values_have_types tvs (TL (TL vs))
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> Cases_on `vs` >>
  gvs[values_have_types_LIST_REL_extcall] >>
  Cases_on `t` >> Cases_on `t'` >>
  gvs[values_have_types_LIST_REL_extcall] >>
  metis_tac[LIST_REL_evaluate_expr_types]
QED

Theorem extcall_nonstatic_args_runtime_typed_nonempty:
  exprs_runtime_typed env args vs /\
  MAP expr_type args = BaseT AddressT :: BaseT (UintT 256) :: arg_tys ==>
  vs <> [] /\ TL vs <> []
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `args` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `vs` >> gvs[listTheory.LIST_REL_EL_EQN] >>
  Cases_on `t` >> gvs[listTheory.LIST_REL_EL_EQN]
QED


Theorem extcall_static_projected_state_well_typed:
  !env cx st res st' args_st vs func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    well_typed_exprs env es /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    MAP expr_type es = BaseT AddressT::arg_types /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    eval_exprs cx es st = (INL vs,args_st) /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ exprs_runtime_typed env es vs /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T))
    ==> state_well_typed st'
Proof
  rpt strip_tac >>
  drule_all extcall_static_args_runtime_typed_dest >> strip_tac >>
  `vs <> []` by (drule_all extcall_static_args_runtime_typed_nonempty >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       check_def, type_check_def, assert_def, return_def, raise_def,
                       lift_option_type_def, lift_option_def,
                       get_accounts_def, get_transient_storage_def,
                       update_accounts_def, update_transient_def,
                       no_type_error_result_def] >>
  qpat_x_assum `eval_exprs cx es st = (INL vs,args_st)` (fn th => rewrite_tac[th]) >>
  rewrite_tac[] >>
  Cases_on `build_ext_calldata (get_tenv cx) func_name arg_types (TL vs)` >>
  gvs[return_def, raise_def]
  >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def,
                         get_accounts_def, get_transient_storage_def,
                         no_type_error_result_def]) >>
  Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >>
  gvs[return_def, raise_def]
  >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def,
                         get_accounts_def, get_transient_storage_def,
                         no_type_error_result_def]) >>
  strip_tac >>
  gvs[bind_def, return_def, raise_def, assert_def,
      get_accounts_def, get_transient_storage_def] >>
  Cases_on `run_ext_call cx.txn.target target_addr x NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >>
  gvs[return_def, raise_def] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >>
  gvs[assert_def, bind_def, return_def, raise_def,
      update_accounts_def, update_transient_def] >>
  `accounts_well_typed x'2` by (
    drule_all run_ext_call_accounts_well_typed >>
    simp[]) >>
  `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
  qpat_x_assum `well_formed_type env.type_defs ret_type` mp_tac >>
  simp[well_formed_type_def] >> strip_tac >>
  Cases_on `evaluate_type env.type_defs ret_type` >> gvs[] >>
  `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv] >>
  gvs[] >>
  `runtime_consistent env cx
     (args_st with logs := args_st.logs ++ x'4)` by
    metis_tac[runtime_consistent_logs_append] >>
  `state_well_typed st' /\ env_consistent env cx st' /\
   accounts_well_typed st'.accounts /\ no_type_error_result res /\
   case res of
   | INL tv => expr_result_typed env (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) tv
   | INR _ => T` by (
    irule extcall_after_state_update_tail_sound >>
    simp[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexistsl [`x'2`, `args_st with logs := args_st.logs ++ x'4`,
              `x'1`, `x'3`] >>
    gvs[append_logs_def, return_def]) >>
  simp[]
QED

Theorem extcall_static_projected_sound:
  !env cx st res st' args_st vs func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    well_typed_exprs env es /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    MAP expr_type es = BaseT AddressT::arg_types /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    eval_exprs cx es st = (INL vs,args_st) /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ exprs_runtime_typed env es vs /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T))
    ==> state_well_typed st' /\ env_consistent env cx st' /\
        accounts_well_typed st'.accounts /\ no_type_error_result res /\
        case res of
        | INL tv => expr_result_typed env (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) tv
        | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!env0 st0 res0 st0'. _` $ mk_asm "drv_ih" >>
  drule_all extcall_static_args_runtime_typed_dest >> strip_tac >>
  `vs <> []` by (drule_all extcall_static_args_runtime_typed_nonempty >> simp[]) >>
  `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv] >>
  drule_all extcall_static_args_runtime_typed_tail >> strip_tac >>
  `?calldata.
     build_ext_calldata env.type_defs func_name arg_types (TL vs) = SOME calldata` by
    (drule_all build_ext_calldata_typed >> simp[]) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       check_def, type_check_def, assert_def, return_def, raise_def,
                       lift_option_type_def, lift_option_def,
                       get_accounts_def, get_transient_storage_def,
                       update_accounts_def, update_transient_def,
                       no_type_error_result_def] >>
  qpat_x_assum `eval_exprs cx es st = (INL vs,args_st)` (fn th => rewrite_tac[th]) >>
  simp[return_def] >>
  qpat_x_assum `build_ext_calldata _ _ _ _ = SOME _` (fn th => rewrite_tac[th]) >>
  rewrite_tac[return_def, raise_def] >>
  Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >>
  rewrite_tac[return_def, raise_def]
  >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def,
                         get_accounts_def, get_transient_storage_def,
                         no_type_error_result_def]) >>
  strip_tac >>
  pop_assum mp_tac >>
  asm_rewrite_tac[bind_def, return_def, raise_def, assert_def,
                  get_accounts_def, get_transient_storage_def] >>
  strip_tac >>
  Cases_on `run_ext_call cx.txn.target target_addr calldata NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >>
  gvs[return_def, raise_def]
  >- (qpat_x_assum `(do _ od) args_st = (res,st')` mp_tac >>
      simp[bind_def, return_def, raise_def, assert_def,
           get_accounts_def, get_transient_storage_def] >>
      strip_tac >> gvs[]) >>
  rename1 `SOME result` >>
  qpat_x_assum `(do _ od) args_st = (res,st')` mp_tac >>
  simp[bind_def, return_def, raise_def, assert_def,
       get_accounts_def, get_transient_storage_def] >>
  strip_tac >>
  Cases_on `result` >> gvs[] >>
  Cases_on `r` >> gvs[] >>
  Cases_on `r''` >> gvs[] >>
  Cases_on `r` >> gvs[] >>
  Cases_on `q` >>
  gvs[assert_def, bind_def, return_def, raise_def,
      update_accounts_def, update_transient_def] >>
  rename1 `run_ext_call _ _ _ _ _ _ _ =
             SOME (T, returnData, accounts', tStorage', emitted_logs)` >>
  `accounts_well_typed accounts'` by (
    drule_all run_ext_call_accounts_well_typed >>
    simp[]) >>
  `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
  `runtime_consistent env cx
     (args_st with logs := args_st.logs ++ emitted_logs)` by
    metis_tac[runtime_consistent_logs_append] >>
  qpat_x_assum `well_formed_type env.type_defs ret_type` mp_tac >>
  simp[well_formed_type_def] >> strip_tac >>
  Cases_on `evaluate_type env.type_defs ret_type` >> gvs[] >>
  rename1 `evaluate_type env.type_defs ret_type = SOME ret_tv` >>
  `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv] >>
  gvs[] >>
  `!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\
      accounts_well_typed st0.accounts /\
      eval_expr cx (THE drv) st0 = (res0,st0') ==>
      well_typed_expr env0 (THE drv) ==>
      state_well_typed st0' /\ env_consistent env0 cx st0' /\
      accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
      case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T` by (
    rpt strip_tac >>
    asm "drv_ih" (qspecl_then [`env0`, `st0`, `res0`, `st0'`] mp_tac) >>
    simp[]) >>
  qspecl_then [`env`, `cx`, `es`, `T`, `func_name`, `arg_types`, `ret_type`,
               `ret_tv`, `drv`, `returnData`,
               `args_st with logs := args_st.logs ++ emitted_logs`,
               `accounts'`, `tStorage'`, `res`, `st'`]
    mp_tac extcall_after_state_update_tail_sound >>
  gvs[append_logs_def, return_def] >>
  strip_tac >>
  metis_tac[no_type_error_result_def]
QED

Theorem extcall_nonstatic_projected_state_well_typed:
  !env cx st res st' args_st vs func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    eval_expr cx (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) st = (res,st') /\
    well_typed_exprs env es /\ well_typed_opt env drv /\
    well_formed_type env.type_defs ret_type /\
    MAP expr_type es = BaseT AddressT::BaseT (UintT 256)::arg_types /\
    (!e. drv = SOME e ==> expr_type e = ret_type) /\
    eval_exprs cx es st = (INL vs,args_st) /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ exprs_runtime_typed env es vs /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T))
    ==> state_well_typed st'
Proof
  rpt strip_tac >>
  drule_all extcall_nonstatic_args_runtime_typed_dest >> strip_tac >>
  `vs <> [] /\ TL vs <> []` by (drule_all extcall_nonstatic_args_runtime_typed_nonempty >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       check_def, type_check_def, assert_def, return_def, raise_def,
                       lift_option_type_def, lift_option_def,
                       get_accounts_def, get_transient_storage_def,
                       update_accounts_def, update_transient_def,
                       no_type_error_result_def] >>
  qpat_x_assum `eval_exprs cx es st = (INL vs,args_st)` (fn th => rewrite_tac[th]) >>
  rewrite_tac[] >>
  Cases_on `build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL vs))` >>
  gvs[return_def, raise_def]
  >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def,
                         get_accounts_def, get_transient_storage_def,
                         no_type_error_result_def]) >>
  Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >>
  gvs[return_def, raise_def]
  >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def,
                         get_accounts_def, get_transient_storage_def,
                         no_type_error_result_def]) >>
  strip_tac >>
  gvs[bind_def, return_def, raise_def, assert_def,
      get_accounts_def, get_transient_storage_def] >>
  Cases_on `run_ext_call cx.txn.target target_addr x (SOME amount) args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >>
  gvs[return_def, raise_def] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >>
  gvs[assert_def, bind_def, return_def, raise_def,
      update_accounts_def, update_transient_def] >>
  `accounts_well_typed x'2` by (
    drule_all run_ext_call_accounts_well_typed >>
    simp[]) >>
  `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
  `runtime_consistent env cx
     (args_st with logs := args_st.logs ++ x'4)` by
    metis_tac[runtime_consistent_logs_append] >>
  irule extcall_success_continuation_state_well_typed >>
  qexistsl [`x'2`, `args_st with logs := args_st.logs ++ x'4`,
            `cx`, `drv`, `env`, `res`, `ret_type`, `x'1`, `x'3`] >>
  simp[assert_def, bind_def, return_def,
       update_accounts_def, update_transient_def]
  >> gvs[append_logs_def, return_def] >>
  rpt strip_tac >>
  qpat_x_assum `!env0 st0 res0 st0'. _`
    (qspecl_then [`env0`, `st0`, `res0`, `st0'`] mp_tac) >>
  simp[]
QED

Theorem extcall_nonstatic_runtime_error_sound:
  !env cx cur_st st' res msg ret_type func_name arg_types es drv.
    state_well_typed cur_st /\ env_consistent env cx cur_st /\
    accounts_well_typed cur_st.accounts /\
    res = INR (Error (RuntimeError msg)) /\ st' = cur_st ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall F (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rw[no_type_error_result_def]
QED

Theorem eval_extcall_args_error:
  !cx es st y args_st ret_type stat func_name arg_types drv.
    eval_exprs cx es st = (INR y,args_st) ==>
    eval_expr cx (Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (INR y,args_st)
Proof
  rpt strip_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       check_def, assert_def, return_def, raise_def,
                       lift_option_type_def, lift_option_def,
                       get_accounts_def, get_transient_storage_def,
                       update_accounts_def, update_transient_def] >>
  gvs[]
QED

Theorem eval_extcall_args_error_sound:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ no_type_error_result (INR y) ==>
    state_well_typed st' /\ env_consistent env cx st' /\


    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error >> strip_tac >>
  first_x_assum (qspecl_then [`ret_type`, `is_static'`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[] >>
  Cases_on `y` >> gvs[no_type_error_result_def]
QED

Theorem eval_extcall_args_error_state_well_typed:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    state_well_typed args_st ==>
    state_well_typed st'
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error >> strip_tac >>
  first_x_assum (qspecl_then [`ret_type`, `is_static'`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED

Theorem eval_extcall_args_error_env_consistent:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    env_consistent env cx args_st ==>
    env_consistent env cx st'
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error >> strip_tac >>
  first_x_assum (qspecl_then [`ret_type`, `is_static'`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED

Theorem eval_extcall_args_error_accounts_well_typed:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    accounts_well_typed args_st.accounts ==>
    accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error >> strip_tac >>
  first_x_assum (qspecl_then [`ret_type`, `is_static'`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED

Theorem eval_extcall_args_error_no_type_error:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    no_type_error_result (INR y) ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error >> strip_tac >>
  first_x_assum (qspecl_then [`ret_type`, `is_static'`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[] >>
  Cases_on `y` >> gvs[no_type_error_result_def]
QED

Theorem eval_extcall_args_error_expr_result_typed:
  !cx env st args_st y res st' is_static func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
      (res,st') ==>
    (case res of
     | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error >> strip_tac >>
  first_x_assum (qspecl_then [`ret_type`, `is_static'`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED

Theorem eval_extcall_args_error_any_call_ty:
  !cx es st y args_st call_ty ret_type stat func_name arg_types drv.
    eval_exprs cx es st = (INR y,args_st) ==>
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (INR y,args_st)
Proof
  rpt strip_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       check_def, assert_def, return_def, raise_def,
                       lift_option_type_def, lift_option_def,
                       get_accounts_def, get_transient_storage_def,
                       update_accounts_def, update_transient_def] >>
  gvs[]
QED
Theorem eval_extcall_args_error_any_call_ty_result_eq:
  !cx es st y args_st call_ty stat func_name arg_types ret_type drv res st'.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (res,st') ==>
    res = INR y /\ st' = args_st
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error_any_call_ty >> strip_tac >>
  first_x_assum (qspecl_then [`call_ty`, `ret_type`, `stat`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED


Theorem eval_extcall_args_error_any_call_ty_state_well_typed:
  !cx env st args_st y res st' call_ty stat func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    state_well_typed args_st ==>
    state_well_typed st'
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error_any_call_ty >> strip_tac >>
  first_x_assum (qspecl_then [`call_ty`, `ret_type`, `stat`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED

Theorem eval_extcall_args_error_any_call_ty_env_consistent:
  !cx env st args_st y res st' call_ty stat func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    env_consistent env cx args_st ==>
    env_consistent env cx st'
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error_any_call_ty >> strip_tac >>
  first_x_assum (qspecl_then [`call_ty`, `ret_type`, `stat`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED

Theorem eval_extcall_args_error_any_call_ty_accounts_well_typed:
  !cx env st args_st y res st' call_ty stat func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    accounts_well_typed args_st.accounts ==>
    accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error_any_call_ty >> strip_tac >>
  first_x_assum (qspecl_then [`call_ty`, `ret_type`, `stat`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED

Theorem eval_extcall_args_error_any_call_ty_no_type_error:
  !cx env st args_st y res st' call_ty stat func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    no_type_error_result (INR y) ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error_any_call_ty >> strip_tac >>
  first_x_assum (qspecl_then [`call_ty`, `ret_type`, `stat`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[] >>
  Cases_on `y` >> gvs[no_type_error_result_def]
QED

Theorem eval_extcall_args_error_any_call_ty_expr_result_typed:
  !cx env st args_st y res st' call_ty stat func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (res,st') ==>
    (case res of
     | INL tv => expr_result_typed env (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error_any_call_ty >> strip_tac >>
  first_x_assum (qspecl_then [`call_ty`, `ret_type`, `stat`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[]
QED

Theorem eval_extcall_args_error_any_call_ty_postcondition:
  !cx env st args_st y res st' call_ty stat func_name arg_types ret_type es drv.
    eval_exprs cx es st = (INR y,args_st) /\
    eval_expr cx (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) st =
      (res,st') /\
    state_well_typed args_st /\ env_consistent env cx args_st /\
    accounts_well_typed args_st.accounts /\ no_type_error_result (INR y) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of
     | INL tv => expr_result_typed env (Call call_ty (ExtCall stat (func_name,arg_types,ret_type)) es drv) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  drule eval_extcall_args_error_any_call_ty >> strip_tac >>
  first_x_assum (qspecl_then [`call_ty`, `ret_type`, `stat`, `func_name`, `arg_types`, `drv`] assume_tac) >>
  gvs[] >>
  Cases_on `y` >> gvs[no_type_error_result_def]
QED

Theorem well_typed_opt_THE:
  !env drv. well_typed_opt env drv /\ IS_SOME drv ==> well_typed_expr env (THE drv)
Proof
  rpt strip_tac >>
  Cases_on `drv` >- gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `SOME drv_expr` >>
  qpat_x_assum `well_typed_opt env (SOME drv_expr)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >>
  simp[]
QED

Theorem extcall_expr_sound_from_generated_ih:
  !cx env st res st' is_static func_name arg_types ret_type es drv.
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    well_typed_expr env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) /\
    (!env0 st0 res0 st0'.
       well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\
       state_well_typed st0 /\ context_well_typed cx /\
       accounts_well_typed st0.accounts /\ functions_well_typed cx /\
       eval_exprs cx es st0 = (res0,st0') ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T) /\
    (!env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx (THE drv) st0 = (res0,st0') ==>
       (well_typed_expr env0 (THE drv) ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 (THE drv) tv | INR _ => T)) /\
    eval_expr cx (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) st =
      (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       check_def, type_check_def, assert_def, return_def, raise_def,
                       lift_option_type_def, lift_option_def,
                       get_accounts_def, get_transient_storage_def,
                       update_accounts_def, update_transient_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
       well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\
       state_well_typed st0 /\ context_well_typed cx /\
       accounts_well_typed st0.accounts /\ functions_well_typed cx /\
       eval_exprs cx es st0 = (res0,st0') ==> _`
    (qspecl_then [`env`, `st`, `args_res`, `args_st`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `args_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `exprs_runtime_typed env es vs` >>
    Cases_on `is_static'` >> gvs[]
    >- (
      drule_all extcall_static_args_runtime_typed_dest >> strip_tac >> gvs[] >>
      `vs <> []` by (Cases_on `vs` >> gvs[exprs_runtime_typed_def]) >>
      `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv] >>
      drule_all extcall_static_args_runtime_typed_tail >> strip_tac >>
      `?calldata_static.
         build_ext_calldata env.type_defs func_name arg_types (TL vs) =
           SOME calldata_static` by
        (drule_all build_ext_calldata_typed >> simp[]) >>
      pop_assum strip_assume_tac >>
      qpat_x_assum `build_ext_calldata _ _ _ _ = SOME _` $
        mk_asm "static_calldata_eq" >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, check_def, type_check_def,
                           assert_def, return_def, raise_def, lift_option_def,
                           get_accounts_def, get_transient_storage_def,
                           no_type_error_result_def] >>
      asm "static_calldata_eq"
        (fn th => simp[th, return_def, raise_def]) >>
      Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >> gvs[return_def, raise_def]
      >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def, get_accounts_def, get_transient_storage_def, no_type_error_result_def]) >>
      Cases_on `run_ext_call cx.txn.target target_addr calldata_static NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >> gvs[return_def, raise_def]
      >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def, get_accounts_def, get_transient_storage_def, no_type_error_result_def]) >>
      rename1 `run_ext_call _ _ _ _ _ _ _ = SOME call_result` >>
      PairCases_on `call_result` >> gvs[] >>
      Cases_on `call_result0` >> gvs[return_def, raise_def]
      >- (
        `accounts_well_typed call_result2` by (drule_all run_ext_call_accounts_well_typed >> simp[]) >>
        `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
        `runtime_consistent env cx
           (args_st with logs := args_st.logs ++ call_result4)` by
          metis_tac[runtime_consistent_logs_append] >>
        strip_tac >>
        qpat_x_assum `(do _ od) args_st = (res,st')` mp_tac >>
        simp[bind_def, ignore_bind_def, return_def, assert_def,
             update_accounts_def, update_transient_def] >>
        strip_tac >>
        rewrite_tac[GSYM no_type_error_result_def] >>
        irule extcall_success_continuation_sound >>
        (conj_tac >-
          metis_tac[runtime_consistent_logs_append, runtime_consistent_def]) >>
        (conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[no_type_error_result_def])) >>
        (conj_tac >- (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
        (conj_tac >- (qpat_assum `well_formed_type env.type_defs ret_type` ACCEPT_TAC)) >>
        (conj_tac >- (qpat_assum `well_typed_opt env drv` ACCEPT_TAC)) >>
        qexistsl [`call_result2`,
                   `args_st with logs := args_st.logs ++ call_result4`,
                   `call_result1`, `call_result3`] >>
        gvs[runtime_consistent_def, assert_def, bind_def, ignore_bind_def,
            return_def, append_logs_def,
            update_accounts_def, update_transient_def]) >>
      strip_tac >> gvs[assert_def, bind_def, return_def, raise_def, get_accounts_def, get_transient_storage_def, no_type_error_result_def]) >>
    drule_all extcall_nonstatic_args_runtime_typed_dest >> strip_tac >> gvs[] >>
    `vs <> [] /\ TL vs <> []` by (Cases_on `vs` >> gvs[exprs_runtime_typed_def] >> Cases_on `t` >> gvs[exprs_runtime_typed_def]) >>
    `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv] >>
    drule_all extcall_nonstatic_args_runtime_typed_tail >> strip_tac >>
    `?calldata_nonstatic.
       build_ext_calldata env.type_defs func_name arg_types (TL (TL vs)) =
         SOME calldata_nonstatic` by
      (drule_all build_ext_calldata_typed >> simp[]) >>
    pop_assum strip_assume_tac >>
    qpat_x_assum `build_ext_calldata _ _ _ _ = SOME _` $
      mk_asm "nonstatic_calldata_eq" >>
    simp_tac(srw_ss())[bind_def, ignore_bind_def, check_def, type_check_def,
                         assert_def, return_def, raise_def, lift_option_def,
                         get_accounts_def, get_transient_storage_def,
                         no_type_error_result_def] >>
    asm "nonstatic_calldata_eq"
      (fn th => simp[th, return_def, raise_def]) >>
    Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >> gvs[return_def, raise_def]
    >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def, get_accounts_def, get_transient_storage_def, no_type_error_result_def]) >>
    Cases_on `run_ext_call cx.txn.target target_addr calldata_nonstatic (SOME amount) args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >> gvs[return_def, raise_def]
    >- (strip_tac >> gvs[assert_def, bind_def, return_def, raise_def, get_accounts_def, get_transient_storage_def, no_type_error_result_def]) >>
    rename1 `run_ext_call _ _ _ _ _ _ _ = SOME call_result` >>
    PairCases_on `call_result` >> gvs[] >>
    Cases_on `call_result0` >> gvs[return_def, raise_def]
    >- (
      `accounts_well_typed call_result2` by (drule_all run_ext_call_accounts_well_typed >> simp[]) >>
      `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
      `runtime_consistent env cx
         (args_st with logs := args_st.logs ++ call_result4)` by
        metis_tac[runtime_consistent_logs_append] >>
      strip_tac >>
      qpat_x_assum `(do calldata <- return calldata_nonstatic; _ od) args_st = (res,st')` mp_tac >>
      simp[bind_def, return_def, get_accounts_def, get_transient_storage_def, assert_def] >>
      strip_tac >>
      gvs[update_accounts_def, update_transient_def, bind_def, return_def] >>
      rewrite_tac[GSYM no_type_error_result_def] >>
      irule extcall_success_continuation_sound >>
      (conj_tac >-
        metis_tac[runtime_consistent_logs_append, runtime_consistent_def]) >>
      (conj_tac >- (rpt strip_tac >> first_x_assum drule_all >> simp[no_type_error_result_def])) >>
      (conj_tac >- (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
      (conj_tac >- (qpat_assum `well_formed_type env.type_defs ret_type` ACCEPT_TAC)) >>
      (conj_tac >- (qpat_assum `well_typed_opt env drv` ACCEPT_TAC)) >>
      qexistsl [`call_result2`,
                 `args_st with logs := args_st.logs ++ call_result4`,
                 `call_result1`, `call_result3`] >>
      gvs[runtime_consistent_def, assert_def, bind_def, return_def,
          append_logs_def, update_accounts_def, update_transient_def]) >>
    strip_tac >> gvs[assert_def, bind_def, return_def, raise_def, get_accounts_def, get_transient_storage_def, no_type_error_result_def]) >>
  strip_tac >> gvs[]
QED



Theorem send_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es = 2 /\
  HD (MAP expr_type es) = BaseT AddressT /\
  EL 1 (MAP expr_type es) = BaseT (UintT 256) ==>
  ?toAddr amount. dest_AddressV (HD vs) = SOME toAddr /\
                  dest_NumV (EL 1 vs) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  rename1 `value_has_type (BaseTV (UintT 256)) v_amt` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `v_amt` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED

Theorem selfdestruct_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es = 1 /\
  HD (MAP expr_type es) = BaseT AddressT ==>
  ?target_addr. LENGTH vs = 1 /\
                dest_AddressV (HD vs) = SOME target_addr
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[] >>
  gvs[evaluate_type_def] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def]
QED

Theorem create_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es >= 2 /\
  HD (MAP expr_type es) = BaseT AddressT /\
  LAST (MAP expr_type es) = BaseT (UintT 256) ==>
  ?target_addr amount. vs <> [] /\
                       dest_AddressV (HD vs) = SOME target_addr /\
                       dest_NumV (LAST vs) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  `LENGTH vs = LENGTH es` by metis_tac[LIST_REL_LENGTH] >>
  `es <> [] /\ vs <> [] /\ tvs <> []` by (Cases_on `es` >> gvs[] >> metis_tac[LIST_REL_LENGTH]) >>
  gvs[LIST_REL_EL_EQN] >>
  `HD tvs = BaseTV AddressT` by (
    qpat_x_assum `!n. n < LENGTH tvs ==> evaluate_type _ _ = SOME _`
      (qspec_then `0` mp_tac) >>
    Cases_on `es` >> Cases_on `tvs` >> gvs[evaluate_type_def]) >>
  `value_has_type (HD tvs) (HD vs)` by (
    qpat_x_assum `!n. n < LENGTH tvs ==> value_has_type _ _`
      (qspec_then `0` mp_tac) >>
    Cases_on `tvs` >> Cases_on `vs` >> gvs[]) >>
  `LAST tvs = BaseTV (UintT 256)` by (
    qpat_x_assum `!n. n < LENGTH tvs ==> evaluate_type _ _ = SOME _`
      (qspec_then `PRE (LENGTH tvs)` mp_tac) >>
    Cases_on `es` >> Cases_on `tvs` >> gvs[LAST_MAP, LAST_EL, evaluate_type_def]) >>
  `value_has_type (LAST tvs) (LAST vs)` by (
    qpat_x_assum `!n. n < LENGTH tvs ==> value_has_type _ _`
      (qspec_then `PRE (LENGTH tvs)` mp_tac) >>
    Cases_on `tvs` >> Cases_on `vs` >> gvs[LAST_EL]) >>
  Cases_on `HD vs` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `LAST vs` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED

Theorem raw_call_bytes_slot_size_bound:
  n < dimword(:256) ==>
   type_slot_size (BaseTV (BytesT (Dynamic n))) <= dimword(:256) /\
   type_slot_size_list [BaseTV BoolT; BaseTV (BytesT (Dynamic n))] <= dimword(:256) /\
   type_slot_size (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))]) <= dimword(:256)
Proof
  strip_tac >>
  `type_slot_size (BaseTV (BytesT (Dynamic n))) + 2 <= dimword(:256)` by (
    `type_slot_size (BaseTV (BytesT (Dynamic n))) = 1 + (n + 31) DIV 32`
      by EVAL_TAC >>
    `(n + 31) DIV 32 <= (dimword(:256) - 1 + 31) DIV 32` by
      (irule DIV_LE_MONOTONE >> DECIDE_TAC) >>
    `(dimword(:256) - 1 + 31) DIV 32 + 3 <= dimword(:256)` by EVAL_TAC >>
    DECIDE_TAC) >>
  `type_slot_size_list [BaseTV BoolT; BaseTV (BytesT (Dynamic n))] =
   1 + type_slot_size (BaseTV (BytesT (Dynamic n)))` by EVAL_TAC >>
  `type_slot_size (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))]) =
   1 + type_slot_size (BaseTV (BytesT (Dynamic n)))` by
     simp[type_slot_size_def] >>
  DECIDE_TAC
QED

Theorem raw_call_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es = 3 /\
  EL 0 (MAP expr_type es) = BaseT AddressT /\
  EL 1 (MAP expr_type es) = BaseT (BytesT bd) /\
  EL 2 (MAP expr_type es) = BaseT (UintT 256) ==>
  ?target_addr data amount. dest_AddressV (HD vs) = SOME target_addr /\
                            dest_BytesV (EL 1 vs) = SOME data /\
                            dest_NumV (EL 2 vs) = SOME amount
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  gvs[evaluate_type_def] >>
  Cases_on `bd` >> gvs[] >>
  rename1 `value_has_type (BaseTV AddressT) v_addr` >>
  rename1 `value_has_type (BaseTV (BytesT bd_data)) v_data` >>
  rename1 `value_has_type (BaseTV (UintT 256)) v_amt` >>
  Cases_on `v_addr` >> gvs[value_has_type_def, dest_AddressV_def] >>
  Cases_on `v_data` >> gvs[value_has_type_def, dest_BytesV_def] >>
  Cases_on `v_amt` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED

Theorem raw_log_args_runtime_typed_dest:
  exprs_runtime_typed env es vs /\
  LENGTH es = 2 /\
  EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
  EL 1 (MAP expr_type es) = BaseT (BytesT bd') /\
  bound_at_most bd 4 ==>
  ?topics data. LENGTH vs = 2 /\
                dest_ArrayV (EL 0 vs) = SOME topics /\
                dest_BytesV (EL 1 vs) = SOME data /\
                LENGTH (case topics of
                  TupleV vs => vs | DynArrayV vs => vs | _ => []) <= 4
Proof
  rw[exprs_runtime_typed_def] >>
  Cases_on `es` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  gvs[evaluate_type_def] >>
  Cases_on `bd'` >> gvs[] >>
  rename1 `value_has_type (ArrayTV (BaseTV (BytesT (Fixed 32))) bd) v_topics` >>
  rename1 `value_has_type (BaseTV (BytesT bd_data)) v_data` >>
  Cases_on `v_topics` >>
  gvs[value_has_type_def, dest_ArrayV_def] >>
  Cases_on `a` >> Cases_on `bd` >>
  gvs[value_has_type_def, bound_at_most_def, compatible_bound_def] >>
  Cases_on `v_data` >> gvs[value_has_type_def, dest_BytesV_def]
QED

Theorem accounts_well_typed_increment_nonce:
  !addr accounts.
    accounts_well_typed accounts ==>
    accounts_well_typed (vfmExecution$increment_nonce addr accounts)
Proof
  rw[accounts_well_typed_def, account_well_typed_def,
     vfmExecutionTheory.increment_nonce_def,
     vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
     combinTheory.APPLY_UPDATE_THM] >>
  IF_CASES_TAC >> gvs[]
QED

Theorem runtime_consistent_increment_nonce:
  !env cx st addr.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (SND (update_accounts (vfmExecution$increment_nonce addr) st))
Proof
  rw[update_accounts_def, return_def, runtime_consistent_def,
     env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[accounts_well_typed_increment_nonce]
QED

Theorem runtime_consistent_logs_updated_by:
  !env cx st f.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (st with logs updated_by f)
Proof
  rw[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED

Theorem runtime_consistent_logs_cons:
  !env cx st l.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (st with logs updated_by CONS l)
Proof
  rw[runtime_consistent_def, env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED
Theorem state_well_typed_logs_append:
  !st ls. state_well_typed st ==>
          state_well_typed (st with logs := st.logs ++ ls)
Proof
  simp[state_well_typed_def]
QED

Theorem env_consistent_logs_append:
  !env cx st ls. env_consistent env cx st ==>
                 env_consistent env cx (st with logs := st.logs ++ ls)
Proof
  rw[env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def] >>
  metis_tac[]
QED


Theorem push_log_runtime_consistent:
  !env cx l st.
    runtime_consistent env cx st ==>
    runtime_consistent env cx (SND (push_log l st))
Proof
  rw[push_log_def, return_def] >>
  metis_tac[runtime_consistent_logs_updated_by]
QED

Theorem selfdestruct_tail_sound:
  !env cx es vs st.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 1 /\
    HD (MAP expr_type es) = BaseT AddressT ==>
    runtime_consistent env cx
      (SND ((do
               type_check (LENGTH vs = 1) "selfdestruct args";
               target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "selfdestruct target";
               accounts <- get_accounts;
               self_acct <<- lookup_account cx.txn.target accounts;
               balance <<- self_acct.balance;
               transfer_value cx.txn.target target_addr balance;
               return (Value NoneV)
             od) st)) /\
    (!s. FST ((do
                 type_check (LENGTH vs = 1) "selfdestruct args";
                 target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "selfdestruct target";
                 accounts <- get_accounts;
                 self_acct <<- lookup_account cx.txn.target accounts;
                 balance <<- self_acct.balance;
                 transfer_value cx.txn.target target_addr balance;
                 return (Value NoneV)
               od) st) <> INR (Error (TypeError s)))
Proof
  rpt strip_tac >>
  drule_all selfdestruct_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, get_accounts_def]
  >- (Cases_on `transfer_value cx.txn.target target_addr
          (lookup_account cx.txn.target st.accounts).balance st` >>
      gvs[return_def] >> Cases_on `q` >> gvs[] >>
      qspecl_then [`env`, `cx`, `cx.txn.target`, `target_addr`,
                   `(lookup_account cx.txn.target st.accounts).balance`, `st`]
        mp_tac transfer_value_runtime_consistent >> simp[])
  >- (qpat_x_assum `FST _ = INR (Error (TypeError s))` mp_tac >>
      rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
         raise_def, return_def, lift_option_type_def, get_accounts_def] >>
      Cases_on `transfer_value cx.txn.target target_addr
          (lookup_account cx.txn.target st.accounts).balance st` >> gvs[return_def] >>
      Cases_on `q` >> gvs[] >>
      qspecl_then [`cx.txn.target`, `target_addr`,
                   `(lookup_account cx.txn.target st.accounts).balance`, `st`, `s`]
        mp_tac transfer_value_no_type_error >> simp[])
QED

Theorem selfdestruct_tail_result_sound_simp:
  !env cx es vs st res st'.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 1 /\
    HD (MAP expr_type es) = BaseT AddressT /\
    ((case type_check (LENGTH vs = 1) "selfdestruct args" st of
        (INL x,s'') =>
          (case
             (case dest_AddressV (HD vs) of
                NONE => raise (Error (TypeError "selfdestruct target"))
              | SOME v => return v) s''
           of
             (INL target_addr,s'') =>
               do
                 x <-
                   transfer_value cx.txn.target target_addr
                     (lookup_account cx.txn.target s''.accounts).balance;
                 return (Value NoneV)
               od s''
           | (INR e,s'') => (INR e,s''))
      | (INR e,s'') => (INR e,s'')) = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv => expr_result_typed env (Call NoneT SelfDestructTarget es NONE) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  qspecl_then [`env`, `cx`, `es`, `vs`, `st`]
    mp_tac selfdestruct_tail_sound >>
  impl_tac >- simp[] >>
  strip_tac >>
  qpat_x_assum `(case type_check _ _ _ of _ => _) = _` mp_tac >>
  drule_all selfdestruct_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, get_accounts_def,
     no_type_error_result_def,
     expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_def, value_has_type_def,
     evaluate_type_def, is_HashMapRef_def] >>
  qpat_x_assum `(case transfer_value _ _ _ _ of _ => _) = _` mp_tac >>
  Cases_on `transfer_value cx.txn.target target_addr
      (lookup_account cx.txn.target st.accounts).balance st` >>
  Cases_on `q` >>
  rw[return_def] >>
  gvs[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
      raise_def, return_def, lift_option_type_def, get_accounts_def,
      runtime_consistent_def,
      toplevel_value_typed_def, value_has_type_def]
QED

(* ===== Shared creation helper soundness ===== *)

Theorem LIST_REL_source_value_compose[local]:
  !tys tvs.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    !vs. LIST_REL value_has_type tvs vs ==>
      LIST_REL
        (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
        tys vs
Proof
  Induct >> Cases_on `tvs` >> simp[] >> rpt strip_tac >>
  Cases_on `vs` >> gvs[] >> metis_tac[]
QED

Theorem LIST_REL_APPEND_SINGLETON[local]:
  LIST_REL R (xs ++ [x]) ys ==>
  ?y ys'. ys = ys' ++ [y] /\ LIST_REL R xs ys' /\ R x y
Proof
  simp[GSYM SNOC_APPEND, LIST_REL_SNOC]
QED

Theorem exprs_runtime_typed_LIST_REL_source_value[local]:
  exprs_runtime_typed env es vs ==>
  LIST_REL
    (\ty v. ?tv. evaluate_type env.type_defs ty = SOME tv /\
                   value_has_type tv v)
    (MAP expr_type es) vs
Proof
  rw[exprs_runtime_typed_def, values_have_types_LIST_REL_extcall] >>
  drule LIST_REL_evaluate_expr_types >> strip_tac >>
  drule_all LIST_REL_source_value_compose >> simp[]
QED

Theorem source_value_LIST_REL_runtime_types[local]:
  !tys vs.
    LIST_REL
      (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
      tys vs ==>
    ?tvs.
      LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs /\
      values_have_types tvs vs
Proof
  Induct_on `tys` >> Cases_on `vs` >>
  simp[values_have_types_LIST_REL_extcall, PULL_EXISTS] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `tvs` >> gvs[values_have_types_LIST_REL_extcall]
QED

Theorem value_has_type_Address_dest[local]:
  value_has_type (BaseTV AddressT) v ==>
  ?a. dest_AddressV v = SOME a
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def, dest_AddressV_def]
QED

Theorem value_has_type_Uint256_dest[local]:
  value_has_type (BaseTV (UintT 256)) v ==>
  ?n. dest_NumV v = SOME n
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def, dest_NumV_def] >>
  rename1 `0 <= i` >>
  `~(i < 0:int)` by intLib.ARITH_TAC >>
  qexists_tac `Num i` >> simp[]
QED

Theorem value_has_type_Bytes_dest[local]:
  value_has_type (BaseTV (BytesT bd)) v ==>
  ?bs. dest_BytesV v = SOME bs
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def, dest_BytesV_def]
QED

Theorem value_has_type_Bytes32_dest[local]:
  value_has_type (BaseTV (BytesT (Fixed 32))) v ==>
  ?bs. dest_BytesV v = SOME bs /\ LENGTH bs = 32
Proof
  strip_tac >> Cases_on `v` >> gvs[value_has_type_def, dest_BytesV_def]
QED

Theorem create_args_runtime_typed_decode:
  create_arg_types_ok kind has_salt tys /\
  LIST_REL
    (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    tys vs ==>
  ?ops ctor_tys.
    dest_create_args kind has_salt vs = SOME ops /\
    create_arg_ctor_types kind has_salt tys = SOME ctor_tys /\
    LIST_REL
      (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
      ctor_tys ops.co_ctor_args
Proof
  rpt strip_tac >>
  Cases_on `kind` >> Cases_on `has_salt` >>
  gvs[create_arg_types_ok_def, dest_create_args_def,
      create_arg_ctor_types_def, make_create_operands_def,
      dest_optional_num_def, dest_optional_salt_def, dest_create_salt_def,
      evaluate_type_def, value_has_type_def, AllCaseEqs()] >>
  TRY (imp_res_tac value_has_type_Address_dest) >>
  TRY (imp_res_tac value_has_type_Uint256_dest) >>
  TRY (imp_res_tac value_has_type_Bytes32_dest) >>
  TRY (imp_res_tac value_has_type_Bytes_dest) >>
  gvs[dest_create_args_def, create_arg_ctor_types_def,
      make_create_operands_def, dest_optional_num_def,
      dest_optional_salt_def, dest_create_salt_def, AllCaseEqs()] >>
  imp_res_tac LIST_REL_APPEND_SINGLETON >>
  gvs[evaluate_type_def] >>
  qpat_x_assum `value_has_type (BaseTV (BytesT (Fixed 32))) y`
    (strip_assume_tac o MATCH_MP value_has_type_Bytes32_dest) >>
  TRY (imp_res_tac value_has_type_Bytes_dest) >>
  gvs[dest_create_args_def, create_arg_ctor_types_def,
      make_create_operands_def, dest_optional_num_def,
      dest_optional_salt_def, dest_create_salt_def,
      evaluate_type_def, value_has_type_def, GSYM SNOC_APPEND,
      AllCaseEqs()]
QED

Theorem encode_create_ctor_args_total:
  LIST_REL
    (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    tys vs ==>
  ?bytes. encode_create_ctor_args tenv tys vs = SOME bytes
Proof
  strip_tac >> drule source_value_LIST_REL_runtime_types >> strip_tac >>
  drule_all (cj 2 vyper_to_abi_total) >> strip_tac >>
  simp[encode_create_ctor_args_def]
QED

Theorem build_create_code_total:
  create_arg_types_ok kind has_salt tys /\
  dest_create_args kind has_salt vs = SOME ops /\
  create_arg_ctor_types kind has_salt tys = SOME ctor_tys /\
  LIST_REL
    (\ty v. ?tv. evaluate_type tenv ty = SOME tv /\ value_has_type tv v)
    ctor_tys ops.co_ctor_args ==>
  ?code_info. build_create_code tenv kind ops accounts ctor_tys = SOME code_info
Proof
  rpt strip_tac >>
  drule encode_create_ctor_args_total >> strip_tac >>
  Cases_on `kind` >> Cases_on `has_salt` >>
  gvs[create_arg_types_ok_def, dest_create_args_def,
      create_arg_ctor_types_def, make_create_operands_def,
      dest_optional_num_def, dest_optional_salt_def, dest_create_salt_def,
      build_create_code_def, encode_create_ctor_args_def,
      evaluate_type_def, value_has_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `b` >>
  gvs[build_create_code_def, encode_create_ctor_args_def,
      evaluate_type_def, value_has_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

Theorem build_create_code_runtime_code_bound:
  accounts_well_typed accounts /\
  build_create_code tenv kind ops accounts ctor_tys = SOME code_info ==>
  !code. code_info.cc_runtime_code = SOME code ==>
         LENGTH code <= max_code_size
Proof
  rpt strip_tac >>
  Cases_on `kind` >>
  gvs[build_create_code_def, AllCaseEqs(), LET_THM,
      accounts_well_typed_def, account_well_typed_def,
      vfmConstantsTheory.max_code_size_def] >>
  first_x_assum (qspec_then `a` mp_tac) >> simp[]
QED

Theorem install_created_code_accounts_well_typed:
  accounts_well_typed accounts /\
  (!code. runtime_code = SOME code ==> LENGTH code <= max_code_size) ==>
  accounts_well_typed
    (install_created_code address runtime_code accounts)
Proof
  Cases_on `runtime_code` >>
  gvs[install_created_code_def, accounts_well_typed_def,
      account_well_typed_def, vfmConstantsTheory.max_code_size_def,
      vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
      combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `addr = address` >> gvs[]
QED

Theorem lookup_account_increment_nonce_balance[simp]:
  (lookup_account a (vfmExecution$increment_nonce b accounts)).balance =
  (lookup_account a accounts).balance
Proof
  simp[vfmExecutionTheory.increment_nonce_def,
       vfmStateTheory.lookup_account_def, vfmStateTheory.update_account_def,
       combinTheory.APPLY_UPDATE_THM] >>
  Cases_on `a = b` >> simp[]
QED

Theorem proceed_create_accounts_well_typed:
  accounts_well_typed accounts /\
  amount <= (lookup_account sender accounts).balance /\
  (lookup_account address accounts).balance + amount < 2 ** 256 /\
  (!code. runtime_code = SOME code ==> LENGTH code <= max_code_size) ==>
  accounts_well_typed
    (proceed_create_accounts sender address amount runtime_code accounts)
Proof
  rpt strip_tac >>
  simp[proceed_create_accounts_def] >>
  irule install_created_code_accounts_well_typed >>
  simp[] >>
  irule vfm_transfer_value_accounts_well_typed >>
  simp[accounts_well_typed_increment_nonce] >>
  qpat_x_assum `(lookup_account address accounts).balance + amount < 2 ** 256`
    mp_tac >> simp[ADD_COMM]
QED

Theorem eval_create_accounts_well_typed:
  accounts_well_typed st.accounts /\
  dest_create_args kind has_salt vs = SOME ops /\
  create_arg_ctor_types kind has_salt arg_tys = SOME ctor_tys /\
  build_create_code (get_tenv cx) kind ops st.accounts ctor_tys = SOME code_info /\
  eval_create cx kind has_salt rof arg_tys vs st = (res, st') ==>
  accounts_well_typed st'.accounts
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_create _ _ _ _ _ _ _ = _` mp_tac >>
  simp[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
       get_accounts_def, update_accounts_def, check_def, assert_def,
       create_soft_failure_def, return_def, raise_def] >>
  rpt (IF_CASES_TAC >>
       gvs[bind_def, ignore_bind_def, update_accounts_def,
           check_def, assert_def, create_soft_failure_def,
           return_def, raise_def]) >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  simp[update_accounts_def] >>
  FIRST
    [FIRST_ASSUM ACCEPT_TAC,
     irule accounts_well_typed_increment_nonce >> FIRST_ASSUM ACCEPT_TAC,
     irule proceed_create_accounts_well_typed >>
     simp[] >>
     rpt strip_tac >>
     imp_res_tac build_create_code_runtime_code_bound]
QED

Theorem create_tail_result_sound_simp:
  !env cx es vs st res st' kind has_salt rof.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    create_arg_types_ok kind has_salt (MAP expr_type es) /\
    eval_create cx kind has_salt rof (MAP expr_type es) vs st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv => expr_result_typed env
         (Call (BaseT AddressT) (CreateTarget kind has_salt rof) es NONE) tv
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `get_tenv cx = env.type_defs` by metis_tac[runtime_consistent_get_tenv] >>
  drule exprs_runtime_typed_LIST_REL_source_value >> strip_tac >>
  drule_all create_args_runtime_typed_decode >> strip_tac >>
  `?code_info.
      build_create_code (get_tenv cx) kind ops st.accounts ctor_tys =
        SOME code_info` by (
    qpat_x_assum `get_tenv cx = env.type_defs` (fn th => rewrite_tac[th]) >>
    irule build_create_code_total >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  `accounts_well_typed st'.accounts` by (
    irule eval_create_accounts_well_typed >>
    metis_tac[runtime_consistent_def]) >>
  drule eval_create_preserves_non_accounts >> strip_tac >>
  `runtime_consistent env cx st'` by (
    gvs[runtime_consistent_def, state_well_typed_def, env_consistent_def,
        env_scopes_consistent_def, env_immutables_consistent_def] >>
    rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC) >>
  gvs[runtime_consistent_def] >>
  qpat_x_assum `eval_create _ _ _ _ _ _ _ = _` mp_tac >>
  simp[eval_create_def, bind_def, ignore_bind_def, lift_option_type_def,
       get_accounts_def, update_accounts_def, check_def, assert_def,
       create_soft_failure_def, return_def, raise_def] >>
  rpt (IF_CASES_TAC >>
       gvs[bind_def, ignore_bind_def, update_accounts_def,
           check_def, assert_def, create_soft_failure_def,
           return_def, raise_def, expr_result_typed_def,
           expr_runtime_typed_def, expr_type_def, evaluate_type_def,
           toplevel_value_typed_def, value_has_type_def, is_HashMapRef_def]) >>
  rpt strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  gvs[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
      evaluate_type_def, toplevel_value_typed_def, value_has_type_def,
      is_HashMapRef_def]
QED

Theorem raw_revert_tail_sound:
  !env cx vs st.
    runtime_consistent env cx st /\ LENGTH vs = 1 ==>
    runtime_consistent env cx
      (SND ((do
               type_check (LENGTH vs = 1) "raw_revert args";
               raise (Error (RuntimeError "raw_revert"))
             od) st)) /\
    (!s. FST ((do
                 type_check (LENGTH vs = 1) "raw_revert args";
                 raise (Error (RuntimeError "raw_revert"))
               od) st) <> INR (Error (TypeError s)))
Proof
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def] >>
  gvs[runtime_consistent_def]
QED

Theorem raw_log_tail_sound:
  !env cx es vs st bd bd'.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 2 /\
    EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
    EL 1 (MAP expr_type es) = BaseT (BytesT bd') /\
    bound_at_most bd 4 ==>
    runtime_consistent env cx
      (SND ((do
               type_check (LENGTH vs = 2) "raw_log args";
               topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
               data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
               topic_vals <<- (case topics of
                  TupleV vs => vs | DynArrayV vs => vs | _ => []);
               type_check (LENGTH topic_vals <= 4) "raw_log too many topics";
               push_log (encode_raw_event_values cx.txn.target topic_vals data);
               return (Value NoneV)
             od) st)) /\
    (!s. FST ((do
                 type_check (LENGTH vs = 2) "raw_log args";
                 topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
                 data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
                 topic_vals <<- (case topics of
                    TupleV vs => vs | DynArrayV vs => vs | _ => []);
                 type_check (LENGTH topic_vals <= 4) "raw_log too many topics";
                 push_log (encode_raw_event_values cx.txn.target topic_vals data);
                 return (Value NoneV)
               od) st) <> INR (Error (TypeError s)))
Proof
  rpt strip_tac >>
  drule_all raw_log_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  Cases_on `topics` >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, push_log_def] >>
  TRY (irule runtime_consistent_logs_append >> simp[]) >>
  qpat_x_assum `FST _ = INR (Error (TypeError s))` mp_tac >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, push_log_def]
QED

Theorem raw_log_tail_result_sound:
  !env cx es vs st res st' bd bd'.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 2 /\
    EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
    EL 1 (MAP expr_type es) = BaseT (BytesT bd') /\
    bound_at_most bd 4 /\
    ((do
        type_check (LENGTH vs = 2) "raw_log args";
        topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
        data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
        topic_vals <<- (case topics of
           TupleV vs => vs | DynArrayV vs => vs | _ => []);
        type_check (LENGTH topic_vals <= 4) "raw_log too many topics";
        push_log (encode_raw_event_values cx.txn.target topic_vals data);
        return (Value NoneV)
      od) st = (res, st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv => expr_result_typed env (Call NoneT RawLog es NONE) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  qspecl_then [`env`, `cx`, `es`, `vs`, `st`, `bd`, `bd'`]
    mp_tac raw_log_tail_sound >>
  simp[] >> strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  drule_all raw_log_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  Cases_on `topics` >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def, lift_option_type_def, push_log_def,
     no_type_error_result_def,
     expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_def, value_has_type_def,
     evaluate_type_def, is_HashMapRef_def] >>
  gvs[runtime_consistent_def]
QED

Theorem raw_log_tail_result_sound_simp:
  !env cx es vs st topics data res st' bd bd'.
    runtime_consistent env cx st /\
    exprs_runtime_typed env es vs /\
    LENGTH es = 2 /\
    EL 0 (MAP expr_type es) = ArrayT (BaseT (BytesT (Fixed 32))) bd /\
    EL 1 (MAP expr_type es) = BaseT (BytesT bd') /\
    bound_at_most bd 4 /\
    dest_ArrayV (EL 0 vs) = SOME topics /\
    dest_BytesV (EL 1 vs) = SOME data /\
    ((case type_check (LENGTH vs = 2) "raw_log args" st of
        (INL x,s'') =>
          (case return topics s'' of
             (INL topics',s'') =>
               (case return data s'' of
                  (INL data,s'') =>
                    do
                      x <- type_check
                        (LENGTH
                           (case topics' of
                            | TupleV vs => vs
                            | DynArrayV vs' => vs'
                            | _ => []) <= 4) "raw_log too many topics";
                      x <- push_log
                        (encode_raw_event_values cx.txn.target
                          (case topics' of
                           | TupleV vs => vs
                           | DynArrayV vs' => vs'
                           | _ => []) data);
                      return (Value NoneV)
                    od s''
                | (INR e,s'') => (INR e,s''))
           | (INR e,s'') => (INR e,s''))
      | (INR e,s'') => (INR e,s'')) = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv => expr_result_typed env (Call NoneT RawLog es NONE) tv
     | INR _ => T)
Proof
  rpt strip_tac >>
  qpat_x_assum `(case type_check _ _ _ of _ => _) = _` mp_tac >>
  drule_all raw_log_args_runtime_typed_dest >> strip_tac >> gvs[] >>
  Cases_on `topics` >>
  rw[bind_def, ignore_bind_def, type_check_def, check_def, assert_def,
     raise_def, return_def,
     lift_option_type_def, push_log_def, no_type_error_result_def,
     expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_def, value_has_type_def,
     evaluate_type_def, is_HashMapRef_def] >>
  fs[type_check_def, bind_def, ignore_bind_def, assert_def, return_def,
     push_log_def] >>
  TRY (irule runtime_consistent_logs_append >> simp[]) >>
  TRY (irule state_well_typed_logs_append >> simp[]) >>
  TRY (irule env_consistent_logs_append >> simp[]) >>
  gvs[runtime_consistent_def] >>
  qpat_x_assum `(case check _ _ _ of _ => _) = _` mp_tac >>
  rw[bind_def, ignore_bind_def, check_def, assert_def, raise_def, return_def,
     lift_option_type_def, push_log_def]
QED


