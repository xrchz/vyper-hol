Theory vyperScopePreservation
Ancestors
  vyperAST vyperMisc vyperState vyperStorageBackend vyperValue vyperInterpreter vyperImmutablesPreservation
  vyperStatePreservation

(* ===== Lemmas about scopes preservation ===== *)

(* Basic monad operations preserve scopes *)
Theorem return_scopes:
  !x st res st'. return x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[return_def]
QED

Theorem raise_scopes:
  !e st res st'. raise e st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[raise_def]
QED

Theorem get_scopes_scopes:
  ∀st res st'. get_scopes st = (res, st') ⇒ st.scopes = st'.scopes
Proof
  rw[get_scopes_def, return_def]
QED

Theorem check_scopes:
  !b s st res st'. check b s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[check_def, type_check_def, assert_def]
QED

Theorem type_check_scopes:
  !b s st res st'. type_check b s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[type_check_def, assert_def]
QED

Theorem lift_option_scopes:
  !x s st res st'. lift_option x s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_option_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_option_type_scopes:
  !x s st res st'. lift_option_type x s st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_option_type_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_sum_scopes:
  !x st res st'. lift_sum x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_sum_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem lift_sum_runtime_scopes:
  !x st res st'. lift_sum_runtime x st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[lift_sum_runtime_def] >> Cases_on `x` >> fs[return_def, raise_def]
QED

Theorem get_Value_scopes:
  !tv st res st'. get_Value tv st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem get_scopes_id:
  !st res st'. get_scopes st = (res, st') ==> st' = st
Proof
  rw[get_scopes_def, return_def]
QED

Theorem get_accounts_scopes:
  !st res st'. get_accounts st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_accounts_def, return_def]
QED

Theorem get_address_immutables_scopes:
  !cx st res st'. get_address_immutables cx st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_address_immutables_def, lift_option_type_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem set_address_immutables_scopes:
  !cx imms st res st'. set_address_immutables cx imms st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_address_immutables_def, return_def] >> simp[]
QED

Theorem get_transient_storage_scopes:
  !st res st'. get_transient_storage st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_transient_storage_def, return_def]
QED

Theorem update_transient_scopes:
  !f st res st'. update_transient f st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[update_transient_def, return_def] >> simp[]
QED

Theorem update_accounts_scopes:
  !f st res st'. update_accounts f st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[update_accounts_def, return_def] >> simp[]
QED

Theorem read_storage_slot_scopes:
  !cx is_trans slot tv st res st'. read_storage_slot cx is_trans slot tv st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `is_trans` >>
  rw[read_storage_slot_def, bind_def, get_storage_backend_def,
     get_transient_storage_def, get_accounts_def, return_def, lift_option_def] >>
  qpat_x_assum `_ = _` mp_tac >> CASE_TAC >> gvs[raise_def, return_def]
QED

Theorem write_storage_slot_scopes:
  !cx is_trans slot tv v st res st'. write_storage_slot cx is_trans slot tv v st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `is_trans` >>
  rw[write_storage_slot_def, bind_def, ignore_bind_def, lift_option_def, lift_option_type_def,
     get_storage_backend_def, set_storage_backend_def,
     get_transient_storage_def, update_transient_def,
     get_accounts_def, update_accounts_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `encode_value tv v` >> gvs[return_def, raise_def]
QED

Theorem get_immutables_scopes:
  !cx src st res st'. get_immutables cx src st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[get_immutables_def, bind_def, return_def, get_address_immutables_def,
     lift_option_type_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> fs[return_def, raise_def]
QED

Theorem lookup_global_scopes:
  !cx src n st res st'. lookup_global cx src n st = (res, st') ==> st'.scopes = st.scopes
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
  CASE_TAC >> gvs[return_def, raise_def, bind_def] >>
  CASE_TAC >> gvs[return_def, raise_def, bind_def] >>
  rpt strip_tac >> gvs[] >>
  drule read_storage_slot_scopes >> simp[]
QED

Theorem set_global_scopes:
  !cx src n v st res st'. set_global cx src n v st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_global_def, bind_def, return_def, lift_option_def, lift_option_type_def] >>
  Cases_on `get_module_code cx src` >> gvs[return_def, raise_def] >>
  rename1 `SOME ts` >>
  Cases_on `find_var_decl_by_num n ts` >> gvs[return_def, raise_def] >>
  rename1 `SOME decl_id` >> PairCases_on `decl_id` >> gvs[] >>
  Cases_on `decl_id0` >> gvs[return_def, raise_def, bind_def] >>
  rename1 `StorageVarDecl is_tr typ` >>
  imp_res_tac lift_option_scopes >> gvs[] >>
  Cases_on `lookup_var_slot_from_layout cx is_tr src decl_id1` >>
  gvs[return_def, raise_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[return_def, raise_def] >>
  imp_res_tac write_storage_slot_scopes
QED

Theorem set_immutable_scopes:
  !cx src n tv v st res st'. set_immutable cx src n tv v st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[set_immutable_def, bind_def, return_def, get_address_immutables_def,
     set_address_immutables_def, lift_option_type_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[raise_def, return_def]
QED

Theorem push_log_scopes:
  !l st res st'. push_log l st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[push_log_def, return_def] >> simp[]
QED

Theorem transfer_value_scopes:
  !f t a st res st'. transfer_value f t a st = (res, st') ==> st'.scopes = st.scopes
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def, check_def, type_check_def, assert_def, update_accounts_def] >>
  gvs[raise_def]
QED

Theorem lookup_flag_mem_scopes:
  !cx nsid mid st res st'. lookup_flag_mem cx nsid mid st = (res, st') ==> st'.scopes = st.scopes
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  rpt CASE_TAC >> simp[return_def, raise_def]
QED

(* switch_BoolV preserves scopes if both branches preserve scopes. *)
Theorem switch_BoolV_scopes:
  ∀v f g st res st'.
    switch_BoolV v f g st = (res, st') ∧
    (∀st1 res1 st1'. f st1 = (res1, st1') ⇒ st1'.scopes = st1.scopes) ∧
    (∀st1 res1 st1'. g st1 = (res1, st1') ⇒ st1'.scopes = st1.scopes) ⇒
    st'.scopes = st.scopes
Proof
  rw[switch_BoolV_def, raise_def]
QED

Theorem finally_pop_function_scopes:
  ∀f prev st res st'.
    finally f (pop_function prev) st = (res, st') ⇒
    st'.scopes = prev
Proof
  rpt strip_tac >>
  fs[pop_function_def, finally_def, set_scopes_def, AllCaseEqs(),
     ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

Theorem finally_set_scopes:
  ∀f prev st res st'.
    finally f (set_scopes prev) st = (res, st') ⇒
    st'.scopes = prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(),
     ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

Theorem finally_pop_function_then_scopes:
  !f g prev st res st'.
    finally f (do pop_function prev; g od) st = (res, st') /\
    (!st0 res0 st0'. g st0 = (res0, st0') ==> st0'.scopes = st0.scopes) ==>
    st'.scopes = prev
Proof
  rpt gen_tac >> strip_tac >>
  fs[finally_def, AllCaseEqs(), ignore_bind_def, bind_def,
     pop_function_def, set_scopes_def, return_def, raise_def] >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem find_containing_scope_map_fdom[local]:
  ∀id sc pre env entry rest a'.
    find_containing_scope id sc = SOME (pre, env, entry, rest) ⇒
    MAP FDOM (pre ++ env |+ (id, a') :: rest) = MAP FDOM sc
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  rpt gen_tac >> simp[find_containing_scope_def] >>
  Cases_on `FLOOKUP h id` >> simp[] >-
  (strip_tac >> PairCases_on `z` >> gvs[] >>
   first_x_assum drule >> simp[]) >>
  Cases_on `x` >> strip_tac >> gvs[] >>
  `id ∈ FDOM env` by gvs[finite_mapTheory.FLOOKUP_DEF] >>
  gvs[pred_setTheory.ABSORPTION_RWT]
QED

Theorem materialise_scopes:
  !cx tv st res st'. materialise cx tv st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `tv` >>
  rw[materialise_def, return_def, raise_def] >>
  gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac read_storage_slot_scopes
QED

Theorem assign_result_scopes:
  !tv ao v subs st res st'. assign_result tv ao v subs st = (res, st') ==> st'.scopes = st.scopes
Proof
  Cases_on `ao` >> rw[assign_result_def, return_def, bind_def, lift_sum_def] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem resolve_array_element_scopes:
  !cx b base tv subs st res st'.
    resolve_array_element cx b base tv subs st = (res, st') ==> st'.scopes = st.scopes
Proof
  ho_match_mp_tac resolve_array_element_ind >> rw[] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[Once resolve_array_element_def, bind_def, return_def, raise_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, type_check_def, assert_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  rpt (TRY (first_x_assum drule >>
            gvs[check_def, type_check_def, assert_def, return_def, raise_def, bind_def,
                ignore_bind_def, AllCaseEqs()] >>
            TRY (imp_res_tac get_storage_backend_scopes >> gvs[]) >> NO_TAC) >>
       gvs[check_def, type_check_def, assert_def, return_def, raise_def, bind_def,
           ignore_bind_def, AllCaseEqs()] >>
       TRY (imp_res_tac get_storage_backend_scopes >> gvs[]))
QED

Theorem bind_scopes:
  ∀f g st res st'.
    bind f g st = (res, st') ∧
    (∀r s s'. f s = (INL r, s') ⇒ s'.scopes = s.scopes) ∧
    (∀r s s'. f s = (INR r, s') ⇒ s'.scopes = s.scopes) ∧
    (∀x s r s'. g x s = (r, s') ⇒ s'.scopes = s.scopes) ⇒
    st'.scopes = st.scopes
Proof
  rpt gen_tac
  >> strip_tac
  >> gvs[bind_def]
  >> Cases_on `f st`
  >> Cases_on `q`
  >> gvs[]
  >> res_tac
  >> gvs[]
QED

Theorem hashmap_branch_scopes:
  ∀cx b c t v is ao r res st'.
    do
      (first_sub,rest_subs) <-
        lift_option_type
          (case REVERSE is of x::xs => SOME (x,xs) | [] => NONE)
          "assign_target hashmap needs subscript";
      (final_type,key_types,remaining_subs) <-
        lift_option_type (split_hashmap_subscripts v rest_subs)
          "assign_target split_hashmap_subscripts";
      hashmap_subs <<- first_sub :: TAKE (LENGTH rest_subs − LENGTH remaining_subs) rest_subs;
      all_key_types <<- t :: key_types;
      final_slot <-
        lift_option_type
          (compute_hashmap_slot c all_key_types hashmap_subs)
          "assign_target compute_hashmap_slot";
      final_tv <-
        lift_option_type (evaluate_type (get_tenv cx) final_type)
          "assign_target evaluate_type";
      current_val <- read_storage_slot cx b final_slot final_tv;
      new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
      write_storage_slot cx b final_slot final_tv new_val;
      assign_result final_tv ao current_val remaining_subs
    od r = (res, st') ⇒
    st'.scopes = r.scopes
Proof
  rpt gen_tac
  >> strip_tac
  >> qpat_x_assum `_ = _` mp_tac
  >> simp[bind_def, ignore_bind_def, return_def, raise_def,
          lift_option_def, lift_option_type_def, lift_sum_def, check_def, type_check_def, assert_def,
          pairTheory.UNCURRY_DEF]
  >> rpt (CASE_TAC >> simp[return_def, raise_def])
  >> rpt strip_tac >> gvs[]
  (* NONE case: raise => trivial *)
  >- gvs[bind_def, raise_def]
  (* SOME case: decompose pair and continue *)
  >> PairCases_on `x` >> gvs[]
  >> qpat_x_assum `_ = (res, st')` mp_tac
  >> simp[bind_def, ignore_bind_def, return_def, raise_def,
          lift_option_def, lift_option_type_def, lift_sum_def, check_def, type_check_def, assert_def]
  >> rpt (CASE_TAC >> simp[return_def, raise_def])
  >> rpt strip_tac >> gvs[]
  >> imp_res_tac read_storage_slot_scopes
  >> imp_res_tac write_storage_slot_scopes
  >> imp_res_tac assign_result_scopes
  >> gvs[]
QED

val monad_defs = [bind_def, ignore_bind_def, return_def, raise_def,
  lift_sum_def, lift_option_def, lift_option_type_def, check_def, type_check_def, assert_def];
val scopes_thms = [
  lookup_global_scopes, set_global_scopes,
  resolve_array_element_scopes, read_storage_slot_scopes,
  write_storage_slot_scopes, assign_result_scopes,
  get_storage_backend_scopes, check_scopes];
val peel_tac =
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def]) >>
  MAP_EVERY (fn th => TRY (imp_res_tac th)) scopes_thms >> gvs[] >>
  gvs(AllCaseEqs() :: PULL_EXISTS :: pairTheory.UNCURRY_DEF :: monad_defs) >>
  MAP_EVERY (fn th => TRY (imp_res_tac th)) scopes_thms >> gvs[];

Theorem assign_target_toplevel_scopes_immutables:
  ∀cx src_id_opt id is ao st res st'.
    assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) is) ao st = (res, st') ⇒
    st'.scopes = st.scopes ∧ st'.immutables = st.immutables
Proof
  rpt gen_tac >> strip_tac
  >> gvs(Once assign_target_def :: pairTheory.UNCURRY_DEF ::
         AllCaseEqs() :: PULL_EXISTS :: monad_defs)
  >> imp_res_tac lookup_global_scopes
  >> imp_res_tac lookup_global_immutables
  >> gvs[option_CASE_rator, CaseEq"option", raise_def, return_def,
         toplevel_value_CASE_rator, type_value_CASE_rator,
         CaseEq"toplevel_value", CaseEq"type_value", bind_def,
         CaseEq"sum", ignore_bind_def, CaseEq"prod", sum_CASE_rator,
         CaseEq"var_decl_info"]
  >> imp_res_tac assign_result_scopes
  >> imp_res_tac set_global_scopes
  >> imp_res_tac set_global_immutables
  >> imp_res_tac resolve_array_element_scopes
  >> imp_res_tac resolve_array_element_state
  >> imp_res_tac assign_result_state
  >> gvs[]
  >> pairarg_tac
  >> gvs[bind_def, AllCaseEqs(), option_CASE_rator, raise_def, return_def,
         type_value_CASE_rator, sum_CASE_rator, bound_CASE_rator,
         assign_operation_CASE_rator, assert_def]
  >> imp_res_tac write_storage_slot_scopes
  >> imp_res_tac write_storage_slot_immutables
  >> imp_res_tac read_storage_slot_scopes
  >> imp_res_tac read_storage_slot_immutables
  >> imp_res_tac assign_result_scopes
  >> imp_res_tac assign_result_state
  >> imp_res_tac get_storage_backend_state
  >> gvs[]
  >> pairarg_tac
  >> gvs[bind_def, AllCaseEqs(), sum_CASE_rator, option_CASE_rator,
         return_def, raise_def]
  >> imp_res_tac assign_result_scopes
  >> imp_res_tac assign_result_state
  >> imp_res_tac write_storage_slot_scopes
  >> imp_res_tac write_storage_slot_immutables
  >> imp_res_tac read_storage_slot_scopes
  >> imp_res_tac read_storage_slot_immutables
  >> gvs[]
QED

Theorem assign_target_preserves_scopes_dom:
  (∀cx gv ao st res st'. assign_target cx gv ao st = (res, st') ⇒ MAP FDOM st'.scopes = MAP FDOM st.scopes) ∧
  (∀cx gvs vs st res st'. assign_targets cx gvs vs st = (res, st') ⇒ MAP FDOM st'.scopes = MAP FDOM st.scopes)
Proof
  ho_match_mp_tac assign_target_ind
  (* ScopedVar *)
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >>
    gvs[assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
    Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[return_def, raise_def] >>
    PairCases_on `x` >>
    gvs[assign_target_def, bind_def, get_scopes_def, return_def, raise_def,
        lift_option_def, type_check_def, assert_def, lift_sum_def,
        ignore_bind_def, set_scopes_def, AllCaseEqs(), sum_CASE_rator] >>
    imp_res_tac assign_result_scopes >> gvs[] >>
    drule find_containing_scope_map_fdom >> simp[])
  (* TopLevelVar *)
  >> conj_tac >- (
    rpt gen_tac >> strip_tac >>
    imp_res_tac assign_target_toplevel_scopes_immutables >> gvs[]
    )
  (* remaining cases: ImmutableVar, TupleTargetV, assign_targets *)
  >> rpt conj_tac
  >> rpt gen_tac
  >> TRY (strip_tac >> imp_res_tac assign_target_toplevel_scopes_immutables >> gvs[] >> NO_TAC)
  >> simp[Once assign_target_def, bind_def, return_def, raise_def, check_def, type_check_def, assert_def,
          ignore_bind_def, lift_option_def, lift_option_type_def, lift_sum_def, get_scopes_def, set_scopes_def,
          get_immutables_def, get_address_immutables_def, set_immutable_def,
          set_address_immutables_def, AllCaseEqs()]
  >> rpt strip_tac >> gvs[]
  >> TRY (res_tac >> gvs[] >> NO_TAC)
  >> TRY (imp_res_tac assign_result_scopes >> gvs[] >>
          drule find_containing_scope_map_fdom >> simp[] >> NO_TAC)
  >> TRY (first_x_assum drule >> gvs[] >> NO_TAC)
  >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
  >> imp_res_tac assign_result_scopes >> gvs[]
QED

Theorem new_variable_scope_property:
  ∀id tv v st res st'.
    new_variable id tv v st = (res, st') ∧ st.scopes ≠ [] ⇒
    st'.scopes ≠ [] ∧
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    TL st'.scopes = TL st.scopes
Proof
  rpt strip_tac >> Cases_on `st.scopes` >> gvs[] >>
  gvs[new_variable_def, bind_def, get_scopes_def, return_def, check_def, type_check_def, assert_def, set_scopes_def, AllCaseEqs(), raise_def, ignore_bind_def] >>
  simp[pred_setTheory.SUBSET_DEF]
QED

Theorem push_scope_creates_empty_hd:
  ∀st res st'.
    push_scope st = (INL (), st') ⇒
    HD st'.scopes = FEMPTY ∧
    TL st'.scopes = st.scopes
Proof
  rw[push_scope_def, return_def] >> simp[]
QED

Theorem push_scope_with_var_creates_singleton_hd:
  ∀nm tv v st res st'.
    push_scope_with_var nm tv v st = (INL (), st') ⇒
    HD st'.scopes = FEMPTY |+ (nm, <| assignable := F; type := tv; value := v |>) ∧
    TL st'.scopes = st.scopes
Proof
  rw[push_scope_with_var_def, return_def] >> simp[]
QED

Theorem finally_pop_scope_preserves_tl_dom:
  ∀body st res st'.
    finally body pop_scope st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM (TL st.scopes)
Proof
  rpt strip_tac >>
  gvs[finally_def, AllCaseEqs()] >>
  gvs[pop_scope_def, AllCaseEqs(), bind_def, ignore_bind_def, return_def, raise_def] >>
  first_x_assum drule >> simp[]
QED

Theorem push_scope_finally_pop_preserves_dom:
  ∀body st res st'.
    do push_scope; finally body pop_scope od st = (res, st') ∧
    (∀st1 res1 st1'. body st1 = (res1, st1') ⇒
       MAP FDOM (TL st1.scopes) = MAP FDOM (TL st1'.scopes)) ⇒
    MAP FDOM st'.scopes = MAP FDOM st.scopes
Proof
  rpt strip_tac >>
  gvs[push_scope_def, bind_def, ignore_bind_def, return_def] >>
  gvs[finally_def, AllCaseEqs()] >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  gvs[pop_scope_def, AllCaseEqs(), bind_def, ignore_bind_def, return_def, raise_def]
QED

Theorem finally_set_scopes_dom:
  ∀f prev s res s'. finally f (set_scopes prev) s = (res, s') ⇒ MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(), ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[]
QED

(* Generalization: handler = do set_scopes prev; g od, where g preserves scopes *)
Theorem finally_set_scopes_then_dom:
  ∀f g prev s res s'.
    finally f (do set_scopes prev; g od) s = (res, s') ⇒
    (∀s res s'. g s = (res, s') ⇒ s'.scopes = s.scopes) ⇒
    MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rpt strip_tac >>
  fs[finally_def, set_scopes_def, AllCaseEqs(),
     ignore_bind_def, return_def, raise_def, bind_def] >>
  gvs[] >> first_x_assum drule >> gvs[]
QED

Theorem acquire_nonreentrant_lock_scopes:
  ∀addr slot is_view st res st'.
    acquire_nonreentrant_lock addr slot is_view st = (res, st') ⇒
    st'.scopes = st.scopes
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem release_nonreentrant_lock_scopes:
  ∀addr slot st res st'.
    release_nonreentrant_lock addr slot st = (res, st') ⇒
    st'.scopes = st.scopes
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED
