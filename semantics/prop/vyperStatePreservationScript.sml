Theory vyperStatePreservation
Ancestors
  vyperAST vyperValue vyperState vyperStorageBackend vyperInterpreter vyperLookup vyperImmutablesPreservation

(* ===== Lemmas about state preservation ===== *)

(* Basic monad operations preserve scopes *)
Theorem return_state:
  !x st res st'. return x st = (res, st') ==> st' = st
Proof
  rw[return_def]
QED

Theorem raise_state:
  !e st res st'. raise e st = (res, st') ==> st' = st
Proof
  rw[raise_def]
QED

Theorem check_state:
  !b s st res st'. check b s st = (res, st') ==> st' = st
Proof
  rw[check_def, type_check_def, assert_def]
QED

Theorem type_check_state:
  !b s st res st'. type_check b s st = (res, st') ==> st' = st
Proof
  rw[type_check_def, assert_def]
QED

Theorem lift_option_type_state:
  !x s st res st'. lift_option_type x s st = (res, st') ==> st' = st
Proof
  rw[lift_option_type_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_option_state:
  !x s st res st'. lift_option x s st = (res, st') ==> st' = st
Proof
  rw[lift_option_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_sum_state:
  !x st res st'. lift_sum x st = (res, st') ==> st' = st
Proof
  rw[lift_sum_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem get_Value_state:
  !tv st res st'. get_Value tv st = (res, st') ==> st' = st
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem get_accounts_state:
  !st res st'. get_accounts st = (res, st') ==> st' = st
Proof
  rw[get_accounts_def, return_def]
QED

Theorem get_address_immutables_state:
  !cx st res st'. get_address_immutables cx st = (res, st') ==> st' = st
Proof
  rw[get_address_immutables_def, lift_option_type_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem get_transient_storage_state:
  !st res st'. get_transient_storage st = (res, st') ==> st' = st
Proof
  rw[get_transient_storage_def, return_def]
QED

Theorem read_storage_slot_state:
  !cx is_trans slot tv st res st'. read_storage_slot cx is_trans slot tv st = (res, st') ==> st' = st
Proof
  Cases_on `is_trans` >>
  rw[read_storage_slot_def, bind_def, get_storage_backend_def,
     get_transient_storage_def, get_accounts_def, return_def, lift_option_def] >>
  qpat_x_assum `_ = _` mp_tac >> CASE_TAC >> gvs[raise_def, return_def]
QED

Theorem get_immutables_state:
  !cx src st res st'. get_immutables cx src st = (res, st') ==> st' = st
Proof
  rw[get_immutables_def, bind_def, return_def, get_address_immutables_def, lift_option_type_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem lookup_global_state:
  !cx src n st res st'. lookup_global cx src n st = (res, st') ==> st' = st
Proof
  rw[lookup_global_def, bind_def, return_def, lift_option_def, lift_option_type_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  Cases_on `find_var_decl_by_num n x` >> gvs[return_def, raise_def] >-
  (qpat_x_assum `_ = (res, st')` mp_tac >>
   simp[get_immutables_def, get_address_immutables_def, bind_def,
        lift_option_def, lift_option_type_def, return_def, raise_def] >>
   CASE_TAC >> gvs[return_def, raise_def] >>
   CASE_TAC >> gvs[return_def, raise_def]) >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `x'0` >> gvs[bind_def, return_def, raise_def] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  CASE_TAC >> gvs[return_def, raise_def, bind_def] >>
  CASE_TAC >> gvs[return_def, raise_def, bind_def] >>
  CASE_TAC >> gvs[return_def, raise_def, bind_def] >>
  CASE_TAC >> gvs[return_def, raise_def] >>
  CASE_TAC >> gvs[return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  drule read_storage_slot_state >> simp[]
QED

Theorem lookup_flag_mem_state:
  !cx nsid mid st res st'. lookup_flag_mem cx nsid mid st = (res, st') ==> st' = st
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  rpt CASE_TAC >> simp[return_def, raise_def]
QED

Theorem switch_BoolV_state:
  ∀v f g st res st'.
    switch_BoolV v f g st = (res, st') ∧
    (∀st1 res1 st1'. f st1 = (res1, st1') ⇒ st1' = st1) ∧
    (∀st1 res1 st1'. g st1 = (res1, st1') ⇒ st1' = st1) ⇒
    st' = st
Proof
  rw[switch_BoolV_def, raise_def]
QED

Theorem assign_result_state:
  !tv ao v subs st res st'. assign_result tv ao v subs st = (res, st') ==> st' = st
Proof
  Cases_on `ao` >> rw[assign_result_def, return_def, bind_def, lift_sum_def] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem resolve_array_element_state:
  !cx b base tv subs st res st'.
    resolve_array_element cx b base tv subs st = (res, st') ==> st' = st
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, type_check_def, assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[assert_def, bind_def, ignore_bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  imp_res_tac get_storage_backend_state >> gvs[] >>
  FIRST [first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
         disch_then drule >> simp[],
         first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
         disch_then drule >> simp[]]
QED

Theorem materialise_state:
  !cx tv st res st'. materialise cx tv st = (res, st') ==> st' = st
Proof
  Cases_on `tv` >>
  rw[materialise_def, return_def, raise_def] >>
  gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_storage_slot_state
QED

Theorem check_array_bounds_state:
  !cx tv v st res st'. check_array_bounds cx tv v st = (res, st') ==> st' = st
Proof
  rpt gen_tac >> strip_tac >>
  gvs[oneline check_array_bounds_def, return_def, raise_def,
      bind_def, ignore_bind_def, check_def, type_check_def, assert_def,
      AllCaseEqs(), toplevel_value_CASE_rator, value_CASE_rator,
      bound_CASE_rator] >>
  imp_res_tac get_storage_backend_state
QED

Theorem toplevel_array_length_state:
  !cx tv st res st'. toplevel_array_length cx tv st = (res, st') ==> st' = st
Proof
  rpt gen_tac >> strip_tac >>
  gvs[oneline toplevel_array_length_def, return_def, raise_def,
      bind_def, ignore_bind_def, check_def, type_check_def, assert_def,
      AllCaseEqs(), toplevel_value_CASE_rator, value_CASE_rator,
      bound_CASE_rator] >>
  imp_res_tac get_storage_backend_state >> gvs[] >>
  Cases_on `v16` >> gvs[return_def, raise_def]
QED

Theorem handle_loop_exception_state:
  handle_loop_exception e s = (r, s') ==> s' = s
Proof
  rw[handle_loop_exception_def, return_def, raise_def]
QED

Theorem update_accounts_immutables:
  !f st res st'. update_accounts f st = (res, st') ==> st'.immutables = st.immutables
Proof
  rw[update_accounts_def, return_def] >> gvs[]
QED

Theorem update_transient_immutables:
  !f st res st'. update_transient f st = (res, st') ==> st'.immutables = st.immutables
Proof
  rw[update_transient_def, return_def] >> gvs[]
QED

Theorem transfer_value_immutables:
  !f t a st res st'.
    transfer_value f t a st = (res, st') ==> st'.immutables = st.immutables
Proof
  rw[transfer_value_def, bind_def, get_accounts_def, return_def,
     check_def, raise_def, update_accounts_def, ignore_bind_def,
     assert_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem push_log_immutables:
  !l st res st'. push_log l st = (res, st') ==> st'.immutables = st.immutables
Proof
  rw[push_log_def, return_def] >> gvs[]
QED

Theorem append_logs_immutables:
  ∀logs st res st'.
    append_logs logs st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  rw[append_logs_def, return_def] >> gvs[]
QED

Theorem append_logs_accounts:
  ∀logs st res st'. append_logs logs st = (res, st') ⇒ st'.accounts = st.accounts
Proof
  rw[append_logs_def, return_def] >> gvs[]
QED

Theorem append_logs_tStorage:
  ∀logs st res st'. append_logs logs st = (res, st') ⇒ st'.tStorage = st.tStorage
Proof
  rw[append_logs_def, return_def] >> gvs[]
QED

Theorem acquire_nonreentrant_lock_immutables:
  !addr slot is_view st res st'.
    acquire_nonreentrant_lock addr slot is_view st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem release_nonreentrant_lock_immutables:
  !addr slot st res st'.
    release_nonreentrant_lock addr slot st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem lift_sum_runtime_state:
  !x st res st'. lift_sum_runtime x st = (res, st') ==> st' = st
Proof
  rw[lift_sum_runtime_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem new_variable_immutables:
  !id tv v st res st'.
    new_variable id tv v st = (res, st') ==>
    st'.immutables = st.immutables
Proof
  rw[new_variable_def, bind_def, get_scopes_def, return_def,
     type_check_def, assert_def, set_scopes_def, raise_def,
     ignore_bind_def, AllCaseEqs()] >>
  Cases_on `st.scopes` >> gvs[raise_def, return_def, set_scopes_def]
QED

(* === Monadic chain preservation lemmas === *)
(* These allow proving that a property P is preserved through a monadic chain
   by composing preservation of each operation in the chain. *)

Theorem bind_preserves:
  !f g st res st' (P : evaluation_state -> bool).
    monad_bind f g st = (res, st') /\
    (!st res st'. f st = (res, st') ==> P st ==> P st') /\
    (!v st res st'. g v st = (res, st') ==> P st ==> P st') /\
    P st ==>
    P st'
Proof
  rpt gen_tac >> strip_tac
  >> Cases_on `f st`
  >> Cases_on `q`
  >> gvs[bind_def]
  >- (
    first_x_assum (qspecl_then [`st`, `INL x`, `r`] mp_tac) >> rw[]
    >> first_x_assum (qspecl_then [`x`, `r`, `res`, `st'`] mp_tac) >> rw[])
  >> first_x_assum (qspecl_then [`st`, `INR y`, `r`] mp_tac) >> rw[]
QED

Theorem ignore_bind_preserves:
  !ff gg st res st' (P : evaluation_state -> bool).
    (do ff; gg od) st = (res, st') /\
    (!st res st'. ff st = (res, st') ==> P st ==> P st') /\
    (!st res st'. gg st = (res, st') ==> P st ==> P st') /\
    P st ==>
    P st'
Proof
  rpt gen_tac >> strip_tac
  >> gvs[ignore_bind_apply, CaseEq"prod", CaseEq"sum"]
  >- (res_tac >> res_tac)
  >> res_tac
QED

Theorem bind_split:
  !f g st res st'.
    monad_bind f g st = (res, st') ==>
    (?x st_mid. f st = (INL x, st_mid) /\ g x st_mid = (res, st')) \/
    (?e. f st = (INR e, st') /\ res = INR e)
Proof
  rw[bind_def] >> Cases_on `f st` >> Cases_on `q` >> gvs[]
QED

Theorem case_bind_split:
  !f g st res st'.
    (case f st of (INL x, s) => g x s | (INR e, s) => (INR e, s)) =
    (res, st') ==>
    (?x st_mid. f st = (INL x, st_mid) /\ g x st_mid = (res, st')) \/
    (?e. f st = (INR e, st') /\ res = INR e)
Proof
  rpt gen_tac >> Cases_on `f st` >> Cases_on `q` >> simp[]
QED

Theorem ignore_bind_split:
  !f g st res st'.
    (do f; g od) st = (res, st') ==>
    (?x st_mid. f st = (INL x, st_mid) /\ g st_mid = (res, st')) \/
    (?e. f st = (INR e, st') /\ res = INR e)
Proof
  rw[ignore_bind_apply, CaseEq"prod", CaseEq"sum"]
  >- (disj1_tac >> metis_tac[])
  >> disj2_tac >> metis_tac[]
QED

Theorem return_preserves:
  !x st res st' (P : evaluation_state -> bool).
    return x st = (res, st') ==> P st ==> P st'
Proof
  rw[return_def] >> gvs[]
QED

Theorem raise_preserves:
  !e st res st' (P : evaluation_state -> bool).
    raise e st = (res, st') ==> P st ==> P st'
Proof
  rw[raise_def] >> gvs[]
QED

Theorem check_preserves:
  !b s st res st' (P : evaluation_state -> bool).
    check b s st = (res, st') ==> P st ==> P st'
Proof
  rw[check_def, type_check_def, assert_def] >> gvs[]
QED

Theorem lift_option_type_preserves:
  !x s st res st' (P : evaluation_state -> bool).
    lift_option_type x s st = (res, st') ==> P st ==> P st'
Proof
  rw[lift_option_type_def] >> Cases_on `x` >> gvs[return_def, raise_def]
QED

Theorem lift_sum_preserves:
  !x st res st' (P : evaluation_state -> bool).
    lift_sum x st = (res, st') ==> P st ==> P st'
Proof
  rw[lift_sum_def] >> Cases_on `x` >> gvs[return_def, raise_def]
QED
