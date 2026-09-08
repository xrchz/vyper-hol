(* Storage preservation for the mutually recursive evaluator. *)

Theory vyperTypeEvalStoragePreservation
Ancestors
  pair vyperCreate vyperInterpreter vyperState vyperStorageBackend vyperStorageLayoutSafety
  vyperTypeSystem vyperTypeEnv vyperTypeInvariants vyperTypeValues vyperTypeCallGraph
  vyperEvalMisc vyperStatePreservation vyperScopePreservation
  vyperTypeCallStackSoundness vyperValue
  vyperTypeBuiltins vyperTypeExprResult vyperTypeExprSoundness vyperTypeEvalSoundness
  vyperTypeExtCallSoundness vyperTypeABI vyperTypeEnvPreservation vyperTypeStatePreservation
  vyperTypeStmtSoundness vyperTypeAssignContext vyperTypeStoragePreservation
  vyperTypeBindArguments
Libs
  wordsLib markerLib

(* Primitive nonreentrant-lock boundary facts.  These expose the exact
   transient write before the evaluator proof uses layout separation. *)
Theorem acquire_nonreentrant_lock_eq:
  acquire_nonreentrant_lock addr slot is_view st =
    if lookup_storage (n2w slot)
         (lookup_transient_storage addr st.tStorage) = 1w then
      (INR (Error (RuntimeError "nonreentrant lock")),st)
    else if is_view then (INL (),st)
    else
      (INL (),
       st with tStorage updated_by
         update_transient_storage addr
           (update_storage (n2w slot) 1w
             (lookup_transient_storage addr st.tStorage)))
Proof
  Cases_on `lookup_storage (n2w slot)
    (lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_def, bind_def, get_transient_storage_def,
       update_transient_def, return_def, raise_def]
QED

Theorem release_nonreentrant_lock_eq:
  release_nonreentrant_lock addr slot st =
    (INL (),
     st with tStorage updated_by
       update_transient_storage addr
         (update_storage (n2w slot) 0w
           (lookup_transient_storage addr st.tStorage)))
Proof
  simp[release_nonreentrant_lock_def, bind_def, get_transient_storage_def,
       update_transient_def, return_def]
QED

Theorem acquire_nonreentrant_lock_frame:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  st'.accounts = st.accounts /\
  (!read_addr read_slot.
     read_addr <> addr \/ read_slot <> n2w slot ==>
     lookup_storage read_slot
       (lookup_transient_storage read_addr st'.tStorage) =
     lookup_storage read_slot
       (lookup_transient_storage read_addr st.tStorage))
Proof
  Cases_on `lookup_storage (n2w slot)
    (lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `addr = read_addr` >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem release_nonreentrant_lock_frame:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  st'.accounts = st.accounts /\
  (!read_addr read_slot.
     read_addr <> addr \/ read_slot <> n2w slot ==>
     lookup_storage read_slot
       (lookup_transient_storage read_addr st'.tStorage) =
     lookup_storage read_slot
       (lookup_transient_storage read_addr st.tStorage))
Proof
  simp[release_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >> Cases_on `addr = read_addr` >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem acquire_nonreentrant_lock_result:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  ((?err. res = INR err) ==>
     res = INR (Error (RuntimeError "nonreentrant lock")) /\ st' = st) /\
  (res = INL () /\ is_view ==> st' = st) /\
  (res = INL () /\ ~is_view ==>
     lookup_storage (n2w slot)
       (lookup_transient_storage addr st'.tStorage) = 1w)
Proof
  Cases_on `lookup_storage (n2w slot)
    (lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[acquire_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem release_nonreentrant_lock_result:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  res = INL () /\
  lookup_storage (n2w slot)
    (lookup_transient_storage addr st'.tStorage) = 0w
Proof
  simp[release_nonreentrant_lock_eq,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmExecutionTheory.update_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM] >>
  rpt strip_tac >>
  gvs[vfmExecutionTheory.update_transient_storage_def,
      vfmStateTheory.update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem reserved_transient_write_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME lock ==>
  contract_storage_well_formed cx
    (st with tStorage updated_by
       update_transient_storage cx.txn.target
         (update_storage (n2w lock) value
           (lookup_transient_storage cx.txn.target st.tStorage)))
Proof
  rpt strip_tac >>
  simp[contract_storage_well_formed_def] >> conj_tac
  >- (simp[vyperLookupStorageTheory.well_formed_storage_def,
           vyperLookupStorageTheory.storage_var_in_range_def] >>
      rpt strip_tac >>
      `declared_storage_region cx mid n [] =
         SOME (is_transient,n2w off,tv)` by
        metis_tac[declared_storage_region_ordinary] >>
      `slots_in_range (get_storage cx st is_transient) off tv` by
        metis_tac[contract_storage_well_formed_storage,
                  vyperLookupStorageTheory.well_formed_storage_def,
                  vyperLookupStorageTheory.storage_var_in_range_def,
                  vyperStorageBackendTheory.get_storage_backend_eq] >>
      Cases_on `is_transient` >>
      gvs[vyperStorageBackendTheory.get_storage_backend_eq,
          vyperStorageBackendTheory.get_storage_def,
          vfmExecutionTheory.lookup_transient_storage_def,
          vfmExecutionTheory.update_transient_storage_def,
          combinTheory.APPLY_UPDATE_THM] >>
      `lock + 1 <= dimword(:256)` by
        metis_tac[storage_layout_safe_nonreentrant_slot_nonoverflow] >>
      `lock < dimword(:256)` by decide_tac >>
      `off + type_slot_size tv <= dimword(:256)` by (
        drule storage_layout_safe_layout >>
        simp[vyperLookupStorageTheory.well_formed_layout_def] >>
        metis_tac[]) >>
      Cases_on `off < dimword(:256)`
      >- (`ranges_disjoint lock 1 off (type_slot_size tv)` by (
            drule_all storage_layout_safe_nonreentrant_slot_separation >>
            simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
          `update_storage (n2w lock) value (st.tStorage cx.txn.target) =
           apply_writes (n2w lock) [(0,value)] (st.tStorage cx.txn.target)` by
            simp[vyperStorageTheory.apply_writes_def,
                 arithmeticTheory.MOD_LESS] >>
          pop_assum SUBST1_TAC >>
          irule vyperLookupStorageTheory.slots_in_range_disjoint_apply_writes >>
          simp[] >>
          qexists `1` >> simp[] >>
          conj_tac
          >- (qpat_assum `lock + 1 <= dimword(:256)` mp_tac >> EVAL_TAC) >>
          qpat_x_assum `ranges_disjoint lock 1 off (type_slot_size tv)` mp_tac >>
          simp[vyperStorageFrameTheory.ranges_disjoint_def]) >>
      `off = dimword(:256) /\ type_slot_size tv = 0` by decide_tac >>
      irule (CONJUNCT1
        vyperStorageWritePreservationTheory.zero_slot_size_slots_in_range) >>
      simp[]) >>
  qpat_x_assum `contract_storage_well_formed cx st` mp_tac >>
  simp[contract_storage_well_formed_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `slots_in_range (get_storage cx st b) (w2n slot) tv` by (
    qpat_assum `!mid n subs b slot tv storage st'. _`
      (qspecl_then
        [`mid`, `n`, `subs`, `b`, `slot`, `tv`, `get_storage cx st b`, `st`]
        mp_tac) >>
    simp[vyperStorageBackendTheory.get_storage_backend_eq]) >>
  Cases_on `b` >>
  gvs[vyperStorageBackendTheory.get_storage_backend_eq,
      vyperStorageBackendTheory.get_storage_def,
      vfmExecutionTheory.lookup_transient_storage_def,
      vfmExecutionTheory.update_transient_storage_def,
      combinTheory.APPLY_UPDATE_THM] >>
  `lock + 1 <= dimword(:256)` by
    metis_tac[storage_layout_safe_nonreentrant_slot_nonoverflow] >>
  `lock < dimword(:256)` by decide_tac >>
  `ranges_disjoint lock 1 (w2n slot) (type_slot_size tv)` by
    metis_tac[storage_layout_safe_nonreentrant_slot_separation] >>
  `update_storage (n2w lock) value (st.tStorage cx.txn.target) =
   apply_writes (n2w lock) [(0,value)] (st.tStorage cx.txn.target)` by
    simp[vyperStorageTheory.apply_writes_def, arithmeticTheory.MOD_LESS] >>
  pop_assum SUBST1_TAC >>
  irule vyperLookupStorageTheory.slots_in_range_disjoint_apply_writes >>
  simp[] >>
  conj_tac
  >- (drule_all storage_layout_safe_region_nonoverflow >>
      simp[arithmeticTheory.ADD_COMM]) >>
  qexists `1` >> simp[] >>
  conj_tac
  >- (qpat_assum `lock + 1 <= dimword(:256)` mp_tac >> EVAL_TAC) >>
  qpat_x_assum
    `ranges_disjoint lock 1 (w2n slot) (type_slot_size tv)` mp_tac >>
  simp[vyperStorageFrameTheory.ranges_disjoint_def]
QED

Theorem acquire_nonreentrant_lock_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME lock /\
  acquire_nonreentrant_lock cx.txn.target lock is_view st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `lookup_storage (n2w lock)
    (lookup_transient_storage cx.txn.target st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  gvs[acquire_nonreentrant_lock_eq] >>
  metis_tac[reserved_transient_write_preserves_contract_storage_well_formed]
QED

Theorem release_nonreentrant_lock_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  cx.nonreentrant_slot = SOME lock /\
  release_nonreentrant_lock cx.txn.target lock st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  gvs[release_nonreentrant_lock_eq] >>
  metis_tac[reserved_transient_write_preserves_contract_storage_well_formed]
QED

Theorem get_storage_stk_scopes[local]:
  get_storage (cx with stk updated_by f) (st with scopes := scopes) b =
  get_storage cx st b
Proof
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem contract_storage_well_formed_stk_scopes[local]:
  contract_storage_well_formed
    (cx with stk updated_by f) (st with scopes := scopes) <=>
  contract_storage_well_formed cx st
Proof
  simp[contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq,
       vyperStorageBackendTheory.get_storage_def,
       get_storage_stk_scopes]
QED

Theorem push_function_preserves_storage_context:
  push_function src_fn sc cx st = (INL cx',st') ==>
  cx'.txn.target = cx.txn.target /\
  cx'.nonreentrant_slot = cx.nonreentrant_slot /\
  (storage_layout_safe cx' <=> storage_layout_safe cx) /\
  (contract_storage_well_formed cx' st' <=>
   contract_storage_well_formed cx st)
Proof
  simp[push_function_def, return_def] >>
  rpt strip_tac >> gvs[] >>
  simp[contract_storage_well_formed_stk_scopes]
QED

Theorem push_function_preserves_runtime_storage_boundaries:
  storage_layout_safe cx /\
  contract_storage_well_formed cx st /\
  push_function src_fn sc cx st = (INL cx',st') ==>
  storage_layout_safe cx' /\
  contract_storage_well_formed cx' st' /\
  cx'.txn.target = cx.txn.target /\
  cx'.nonreentrant_slot = cx.nonreentrant_slot
Proof
  metis_tac[push_function_preserves_storage_context]
QED

Theorem eval_target_preserves_runtime_consistent[local]:
  well_typed_atarget env tgt ty /\
  runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_atarget tgt) /\
  eval_target cx tgt st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 4 eval_all_type_sound_mutual]
QED

Theorem eval_iterator_preserves_runtime_consistent[local]:
  well_typed_iterator env ty it /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_iterator it) /\
  eval_iterator cx it st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 3 eval_all_type_sound_mutual]
QED

Theorem eval_base_target_preserves_runtime_consistent[local]:
  type_place_target env bt = SOME vt /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_target cx bt st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 6 eval_all_type_sound_mutual]
QED


Theorem eval_base_target_success_runtime_typed[local]:
  type_place_target env bt = SOME (Type ty) /\
  runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_target cx bt st = (INL (loc,sbs),st') ==>
  target_runtime_typed env cx st' (BaseTarget bt) ty (BaseTargetV loc sbs)
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  `base_target_value_shape env bt loc sbs /\
   ?loc_vt. location_runtime_typed env cx st' loc loc_vt /\
            target_path_type env loc_vt sbs (Type ty)` by (
    drule_all (cj 6 eval_all_type_sound_mutual) >> simp[]) >>
  simp[target_runtime_typed_def, target_value_shape_def,
       well_typed_atarget_def, well_typed_target_def] >>
  metis_tac[]
QED
Theorem eval_expr_preserves_runtime_consistent[local]:
  well_typed_expr env e /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 8 eval_all_type_sound_mutual]
QED

Theorem eval_exprs_success_runtime_typed[local]:
  well_typed_exprs env es /\
  runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  eval_exprs cx es st = (INL vs,st') ==>
  exprs_runtime_typed env es vs
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 9 eval_all_type_sound_mutual) >> simp[]
QED
Theorem eval_exprs_success_runtime_typed_from_eval[local]:
  eval_exprs cx es st = (INL vs,st') /\
  well_typed_exprs env es /\
  runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) ==>
  exprs_runtime_typed env es vs
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`env` |-> `env`, `es` |-> `es`, `cx` |-> `cx`,
                  `st` |-> `st`, `vs` |-> `vs`, `st'` |-> `st'`]
            eval_exprs_success_runtime_typed) >>
  (impl_tac >- simp[]) >> simp[]
QED


Theorem eval_target_success_runtime_typed[local]:
  well_typed_atarget env tgt ty /\
  runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_atarget tgt) /\
  eval_target cx tgt st = (INL gv,st') ==>
  target_runtime_typed env cx st' tgt ty gv
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 4 eval_all_type_sound_mutual) >> simp[]
QED

Theorem eval_expr_success_result_typed[local]:
  well_typed_expr env e /\
  runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (INL tv,st') ==>
  expr_result_typed env e tv
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 8 eval_all_type_sound_mutual) >> simp[]
QED

Theorem eval_exprs_preserves_runtime_consistent[local]:
  well_typed_exprs env es /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  eval_exprs cx es st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 9 eval_all_type_sound_mutual]
QED
Theorem eval_exprs_preserves_runtime_consistent_from_eval[local]:
  eval_exprs cx es st = (res,st') /\
  well_typed_exprs env es /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) ==>
  runtime_consistent env cx st'
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`env` |-> `env`, `es` |-> `es`, `cx` |-> `cx`,
                  `st` |-> `st`, `res` |-> `res`, `st'` |-> `st'`]
            eval_exprs_preserves_runtime_consistent) >>
  simp[]
QED


Theorem eval_for_preserves_runtime_consistent[local]:
  evaluate_type env.type_defs ty = SOME tyv /\
  EVERY (value_has_type tyv) vs /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
  runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts body_stmts) /\
  eval_for cx tyv id body_stmts vs st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >>
  metis_tac[cj 7 eval_all_type_sound_mutual]
QED

Theorem get_storage_logs[local]:
  get_storage cx (st with logs updated_by f) b = get_storage cx st b
Proof
  Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]
QED

Theorem contract_storage_well_formed_logs[local]:
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx (st with logs updated_by f)
Proof
  simp[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq,
       get_storage_logs]
QED

Theorem contract_storage_well_formed_scopes[local]:
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx (st with scopes := scopes)
Proof
  strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[get_storage_scopes]
QED

Theorem push_scope_preserves_runtime_storage_consistent[local]:
  runtime_storage_consistent env cx st /\
  push_scope st = (res,st') ==>
  runtime_storage_consistent env cx st'
Proof
  rpt strip_tac >>
  qpat_x_assum `push_scope _ = _` mp_tac >>
  simp[push_scope_def, return_def] >> strip_tac >> gvs[] >>
  `runtime_consistent env cx
     (st with scopes updated_by CONS FEMPTY)` by (
    simp[runtime_consistent_def] >>
    conj_tac
    >- (irule push_scope_env_consistent >>
        metis_tac[runtime_storage_consistent_runtime, runtime_consistent_def]) >>
    conj_tac
    >- (irule push_scope_preserves_state_well_typed >>
        qexistsl_tac [`st`, `()`] >> simp[push_scope_def, return_def] >>
        metis_tac[runtime_storage_consistent_runtime, runtime_consistent_def]) >>
    metis_tac[runtime_storage_consistent_runtime, runtime_consistent_def]) >>
  `contract_storage_well_formed cx
     (st with scopes updated_by CONS FEMPTY)` by (
    irule contract_storage_well_formed_storage_frame >>
    qexists_tac `st` >>
    conj_tac
    >- (gen_tac >> Cases_on `b` >>
        simp[vyperStorageBackendTheory.get_storage_def]) >>
    metis_tac[runtime_storage_consistent_storage]) >>
  metis_tac[runtime_storage_consistent_intro,
            runtime_storage_consistent_layout]
QED
Theorem pop_scope_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  pop_scope st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  qpat_x_assum `pop_scope _ = _` mp_tac >>
  Cases_on `st.scopes` >>
  simp[pop_scope_def, return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >>
  conj_tac
  >- (gen_tac >> Cases_on `b` >>
      simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[]
QED


Theorem new_variable_storage_frame[local]:
  new_variable id tv v st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[new_variable_def, bind_apply, ignore_bind_apply, get_scopes_def,
       type_check_def, assert_def, return_def, raise_def, set_scopes_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `st.scopes` >>
  gvs[raise_def, set_scopes_def, return_def] >>
  simp[get_storage_scopes]
QED

Theorem new_variable_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  new_variable id tv v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[new_variable_storage_frame]
QED

Theorem finally_preserves_state_predicate[local]:
  !P f g st res st'.
  (!r s. f st = (r,s) ==> P s) /\
  (!s r s'. P s /\ g s = (r,s') ==> P s') /\
  finally f g st = (res,st') ==>
  P st'
Proof
  rpt strip_tac >>
  Cases_on `f st` >> rename1 `f st = (main_res,main_st)` >>
  Cases_on `main_res` >>
  Cases_on `g main_st` >>
  rename1 `g main_st = (cleanup_res,cleanup_st)` >>
  Cases_on `cleanup_res` >>
  gvs[finally_def, ignore_bind_apply, return_def, raise_def] >>
  metis_tac[]
QED

Theorem default_scope_finally_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  (!r s.
     m (st with scopes := [FEMPTY]) = (r,s) ==>
     contract_storage_well_formed cx s) /\
  finally (do set_scopes [FEMPTY]; m od) (set_scopes prev) st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `!r s.
     (do set_scopes [FEMPTY]; m od) st = (r,s) ==>
     contract_storage_well_formed cx s` by (
    rpt strip_tac >>
    qpat_x_assum `(do set_scopes [FEMPTY]; m od) st = _` mp_tac >>
    simp[ignore_bind_apply, set_scopes_def, return_def] >>
    metis_tac[]) >>
  `!s r s'.
     contract_storage_well_formed cx s /\
     set_scopes prev s = (r,s') ==>
     contract_storage_well_formed cx s'` by (
    rpt strip_tac >>
    qpat_x_assum `set_scopes prev _ = _` mp_tac >>
    simp[set_scopes_def, return_def] >>
    rpt strip_tac >> gvs[] >>
    irule contract_storage_well_formed_scopes >> simp[]) >>
  qspecl_then
    [`contract_storage_well_formed cx`,
     `ignore_bind (set_scopes [FEMPTY]) m`, `set_scopes prev`,
     `st`, `res`, `st'`] mp_tac finally_preserves_state_predicate >>
  simp[] >> metis_tac[]
QED

Theorem default_eval_exprs_finally_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  (!r s.
     eval_exprs cxd needed (st with scopes := [FEMPTY]) = (r,s) ==>
     contract_storage_well_formed cx s) /\
  finally
    (do set_scopes [FEMPTY]; eval_exprs cxd needed od)
    (set_scopes prev) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[default_scope_finally_preserves_contract_storage_well_formed]
QED

Theorem default_eval_exprs_finally_success[local]:
  finally
    (do set_scopes [FEMPTY]; eval_exprs cxd needed od)
    (set_scopes prev) st = (INL vs,st') ==>
  ?pre.
    eval_exprs cxd needed (st with scopes := [FEMPTY]) = (INL vs,pre) /\
    st' = pre with scopes := prev
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, bind_apply, ignore_bind_apply, set_scopes_def,
       return_def, raise_def] >>
  Cases_on `eval_exprs cxd needed (st with scopes := [FEMPTY])` >>
  Cases_on `q` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[] >>
  qexists_tac `r` >> simp[]
QED

Theorem try_eval_stmts_handle_function_preserves_contract_storage_well_formed[local]:
  !cx cxf stmts st res st'.
  (!r s.
     eval_stmts cxf stmts st = (r,s) ==>
     contract_storage_well_formed cx s) /\
  try (do eval_stmts cxf stmts; return NoneV od) handle_function st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `eval_stmts cxf stmts st` >>
  rename1 `eval_stmts cxf stmts st = (body_res,body_st)` >>
  `contract_storage_well_formed cx body_st` by metis_tac[] >>
  Cases_on `body_res` >>
  gvs[try_def, ignore_bind_apply, return_def, raise_def] >>
  Cases_on `y` >>
  gvs[handle_function_def, return_def, raise_def]
QED

Theorem intcall_lock_state_preserves_runtime_frame_storage[local]:
  !cx nr is_view st lock_st.
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) st = (INL (),lock_st) ==>
    lock_st.scopes = st.scopes /\
    lock_st.immutables = st.immutables /\
    lock_st.accounts = st.accounts
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
  drule acquire_nonreentrant_lock_scopes >>
  drule acquire_nonreentrant_lock_immutables >>
  drule acquire_nonreentrant_lock_frame >>
  simp[]
QED

Theorem env_scopes_consistent_stk_irrelevant_storage[local]:
  !env cx f st.
    env_scopes_consistent env (cx with stk updated_by f) st <=>
    env_scopes_consistent env cx st
Proof
  simp[env_scopes_consistent_def, vyperContextTheory.get_tenv_def]
QED

Theorem runtime_consistent_env_immutables_storage[local]:
  runtime_consistent env cx st ==>
  env_immutables_consistent env cx st
Proof
  simp[runtime_consistent_def, env_consistent_def]
QED

Theorem runtime_consistent_scopes_well_typed_storage[local]:
  runtime_consistent env cx st ==> EVERY scope_well_typed st.scopes
Proof
  simp[runtime_consistent_def, state_well_typed_def]
QED

Theorem runtime_consistent_context_storage[local]:
  runtime_consistent env cx st ==> context_well_typed cx
Proof
  simp[runtime_consistent_def]
QED

Theorem runtime_consistent_state_accounts_storage[local]:
  runtime_consistent env cx st ==>
  state_well_typed st /\ accounts_well_typed st.accounts
Proof
  simp[runtime_consistent_def]
QED

Theorem state_accounts_scopes_storage[local]:
  state_well_typed st /\ accounts_well_typed st.accounts /\
  EVERY scope_well_typed scopes ==>
  state_well_typed (st with scopes := scopes) /\
  accounts_well_typed (st with scopes := scopes).accounts
Proof
  simp[state_well_typed_def]
QED

Theorem env_immutables_consistent_defaults_scopes_storage[local]:
  env_immutables_consistent (defaults_env env) cx st ==>
  env_immutables_consistent env cx (st with scopes := scopes)
Proof
  simp[env_immutables_consistent_def, defaults_env_def] >> metis_tac[]
QED

Theorem intcall_cleanup_preserves_contract_storage_well_formed[local]:
  !cx prev nr is_view st res st'.
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  (do
     pop_function prev;
     if nr /\ ~is_view then
       case cx.nonreentrant_slot of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()
   od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `nr /\ ~is_view` >>
  gvs[pop_function_def, ignore_bind_apply, set_scopes_def, return_def]
  >- (Cases_on `cx.nonreentrant_slot` >> gvs[return_def]
      >- (irule contract_storage_well_formed_scopes >> simp[]) >>
      `contract_storage_well_formed cx (st with scopes := prev)` by
        metis_tac[contract_storage_well_formed_scopes] >>
      metis_tac[
        release_nonreentrant_lock_preserves_contract_storage_well_formed]) >>
  irule contract_storage_well_formed_scopes >> simp[]
QED

Theorem intcall_post_push_suffix_preserves_contract_storage_well_formed[local]:
  !cx cxf fn_stmts body_st prev nr is_view rtv res st'.
    contract_storage_well_formed cx body_st /\
    storage_layout_safe cx /\
    (!bres bst.
       eval_stmts cxf fn_stmts body_st = (bres,bst) ==>
       contract_storage_well_formed cx bst) /\
    (do
       rv <- finally
         (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
         (do
            pop_function prev;
            if nr /\ ~is_view then
              case cx.nonreentrant_slot of
                NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) body_st = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on
    `finally
       (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
       (do
          pop_function prev;
          if nr /\ ~is_view then
            case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
        od)
       body_st` >>
  rename1 `_ = (body_final_res,body_final_st)` >>
  `!r s.
     try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function body_st =
       (r,s) ==>
     contract_storage_well_formed cx s` by
    metis_tac[
      try_eval_stmts_handle_function_preserves_contract_storage_well_formed] >>
  `!s r s'.
     contract_storage_well_formed cx s /\
     (do
        pop_function prev;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
      od) s = (r,s') ==>
     contract_storage_well_formed cx s'` by
    metis_tac[intcall_cleanup_preserves_contract_storage_well_formed] >>
  `contract_storage_well_formed cx body_final_st` by (
    qspecl_then
      [`contract_storage_well_formed cx`,
       `try (ignore_bind (eval_stmts cxf fn_stmts) (return NoneV))
          handle_function`,
       `ignore_bind (pop_function prev)
          (if nr /\ ~is_view then
             case cx.nonreentrant_slot of
               NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ())`,
       `body_st`, `body_final_res`, `body_final_st`]
      mp_tac finally_preserves_state_predicate >>
    simp[] >> metis_tac[]) >>
  Cases_on `body_final_res` >>
  gvs[bind_apply, lift_option_type_def, return_def, raise_def] >>
  Cases_on `safe_cast rtv x` >>
  gvs[lift_option_type_def, return_def, raise_def]
QED

Theorem intcall_post_push_expanded_suffix_preserves_contract_storage_well_formed[local]:
  !cx cxf fn_stmts body_st prev nr is_view rtv res st'.
    contract_storage_well_formed cx body_st /\
    storage_layout_safe cx /\
    (!bres bst.
       eval_stmts cxf fn_stmts body_st = (bres,bst) ==>
       contract_storage_well_formed cx bst) /\
    (case
       finally
         (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
         (do
            pop_function prev;
            if nr /\ ~is_view then
              case cx.nonreentrant_slot of
                NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ()
          od)
         body_st
     of
       (INL rv,s) =>
         (case
            (case safe_cast rtv rv of
               NONE => raise (Error (TypeError "IntCall cast ret"))
             | SOME v => return v) s
          of
            (INL crv,s') => (INL (Value crv),s')
          | (INR e,s') => (INR e,s'))
     | (INR e,s) => (INR e,s)) = (res,st') ==>
    contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  qspecl_then
    [`cx`, `cxf`, `fn_stmts`, `body_st`, `prev`, `nr`, `is_view`,
     `rtv`, `res`, `st'`]
    mp_tac intcall_post_push_suffix_preserves_contract_storage_well_formed >>
  impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     Cases_on
       `finally
          (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
          (do
             pop_function prev;
             if nr /\ ~is_view then
               case cx.nonreentrant_slot of
                 NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
           od)
          body_st` >>
     rename1 `_ = (body_final_res,body_final_st)` >>
     Cases_on `body_final_res` >>
     gvs[bind_apply, lift_option_type_def, return_def, raise_def] >>
     Cases_on `safe_cast rtv x` >>
     gvs[lift_option_type_def, return_def, raise_def]) >>
  simp[]
QED

Theorem intcall_post_defaults_preserves_contract_storage_well_formed[local]:
  !cx src_id_opt fn args vs dflt_vs ret mut nr fn_stmts prev st res st'.
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  (!cxf s r s'.
     contract_storage_well_formed cx s /\
     eval_stmts cxf fn_stmts s = (r,s') ==>
     contract_storage_well_formed cx s') /\
  (do
     env <- lift_option_type
       (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
       "IntCall bind_arguments";
     rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
       "IntCall eval ret";
     is_view <<- (mut = View \/ mut = Pure);
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot =>
            acquire_nonreentrant_lock cx.txn.target slot is_view
      else return ());
     cxf <- push_function (src_id_opt,fn) env cx;
     rv <- finally
       (try (do eval_stmts cxf fn_stmts; return NoneV od) handle_function)
       (do
          pop_function prev;
          if nr /\ ~is_view then
            case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot =>
                release_nonreentrant_lock cx.txn.target slot
          else return ()
        od);
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
   od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `bind_arguments (get_tenv cx) args (vs ++ dflt_vs)` >>
  gvs[lift_option_type_def, bind_apply, return_def, raise_def] >>
  rename1 `bind_arguments (get_tenv cx) args (vs ++ dflt_vs) = SOME env` >>
  Cases_on `evaluate_type (get_tenv cx) ret` >>
  gvs[lift_option_type_def, bind_apply, return_def, raise_def] >>
  rename1 `evaluate_type (get_tenv cx) ret = SOME rtv` >>
  `!lock_res lock_st.
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
            (mut = View \/ mut = Pure)
      else return ()) st = (lock_res,lock_st) ==>
     contract_storage_well_formed cx lock_st` by (
    rpt strip_tac >>
    Cases_on `nr` >> gvs[return_def, raise_def] >>
    Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
    metis_tac[
      acquire_nonreentrant_lock_preserves_contract_storage_well_formed]) >>
  Cases_on
    `(if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
            (mut = View \/ mut = Pure)
      else return ()) st` >>
  rename1 `_ st = (lock_res,lock_st)` >>
  `contract_storage_well_formed cx lock_st` by metis_tac[] >>
  Cases_on `lock_res` >>
  gvs[ignore_bind_apply, bind_apply, push_function_def, return_def, raise_def] >>
  `contract_storage_well_formed cx (lock_st with scopes := [env])` by
    metis_tac[contract_storage_well_formed_scopes] >>
  Cases_on
    `finally
       (try
          (do
             eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) fn_stmts;
             return NoneV
           od)
          handle_function)
       (do
          pop_function prev;
          if nr /\ ~(mut = View \/ mut = Pure) then
            case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot =>
                release_nonreentrant_lock cx.txn.target slot
          else return ()
        od)
       (lock_st with scopes := [env])` >>
  rename1 `_ = (body_final_res,body_final_st)` >>
  `!r s.
     try
       (do
          eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) fn_stmts;
          return NoneV
        od)
       handle_function (lock_st with scopes := [env]) = (r,s) ==>
     contract_storage_well_formed cx s` by
    metis_tac[
      try_eval_stmts_handle_function_preserves_contract_storage_well_formed] >>
  `!s r s'.
     contract_storage_well_formed cx s /\
     (do
        pop_function prev;
        if nr /\ ~(mut = View \/ mut = Pure) then
          case cx.nonreentrant_slot of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
      od) s = (r,s') ==>
     contract_storage_well_formed cx s'` by
    metis_tac[intcall_cleanup_preserves_contract_storage_well_formed] >>
  `contract_storage_well_formed cx body_final_st` by (
    qspecl_then
      [`contract_storage_well_formed cx`,
       `try
          (ignore_bind
             (eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) fn_stmts)
             (return NoneV))
          handle_function`,
       `ignore_bind (pop_function prev)
          (if nr /\ ~(mut = View \/ mut = Pure) then
             case cx.nonreentrant_slot of
               NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ())`,
       `lock_st with scopes := [env]`, `body_final_res`, `body_final_st`]
      mp_tac finally_preserves_state_predicate >>
    simp[] >> strip_tac >>
    qpat_x_assum `_ ==> contract_storage_well_formed cx body_final_st` irule >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum
      `!s r s'. contract_storage_well_formed cx s /\
         do pop_function prev; _ od s = (r,s') ==>
         contract_storage_well_formed cx s'`
      (qspecl_then [`s`, `r`, `s'`] mp_tac) >>
    ASM_REWRITE_TAC[] >> strip_tac >>
    qpat_x_assum `_ ==> contract_storage_well_formed cx s'` irule >>
    simp[]) >>
  Cases_on `body_final_res` >>
  gvs[] >>
  rename1 `safe_cast rtv rv` >>
  Cases_on `safe_cast rtv rv` >>
  gvs[lift_option_type_def, return_def, raise_def]
QED

Theorem eval_all_storage_preservation_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    protected_storage_calls_preserve cx /\
    eval_stmt cx s st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    protected_storage_calls_preserve cx /\
    eval_stmts cx ss st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    protected_storage_calls_preserve cx /\
    eval_iterator cx it st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tgt. !env ty st res st'.
    well_typed_atarget env tgt ty /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    protected_storage_calls_preserve cx /\
    eval_target cx tgt st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tgts. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    protected_storage_calls_preserve cx /\
    eval_targets cx tgts st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    protected_storage_calls_preserve cx /\
    eval_base_target cx bt st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\
    EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    protected_storage_calls_preserve cx /\
    eval_for cx tyv id body vs st = (res,st') ==>
    contract_storage_well_formed cx st') /\
  (!cx e. !env st res st'.
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    protected_storage_calls_preserve cx /\
    eval_expr cx e st = (res,st') ==>
    ((well_typed_expr env e ==> contract_storage_well_formed cx st') /\
     (!vt. type_place_expr env e = SOME vt ==>
       contract_storage_well_formed cx st'))) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\
    runtime_storage_consistent env cx st /\
    functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    protected_storage_calls_preserve cx /\
    eval_exprs cx es st = (res,st') ==>
    contract_storage_well_formed cx st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >>
  TRY(rename1 `Pass` >> suspend "Pass") >>
  TRY(rename1 `Continue` >> suspend "Continue") >>
  TRY(rename1 `Break` >> suspend "Break") >>
  TRY(rename1 `Return NONE` >> suspend "Return_NONE") >>
  TRY(rename1 `Return (SOME _)` >> suspend "Return_SOME") >>
  TRY(rename1 `Raise RaiseBare` >> suspend "RaiseBare") >>
  TRY(rename1 `Raise RaiseUnreachable` >> suspend "RaiseUnreachable") >>
  TRY(rename1 `Raise (RaiseReason _)` >> suspend "RaiseReason") >>
  TRY(rename1 `AssertBare` >> suspend "AssertBare") >>
  TRY(rename1 `AssertUnreachable` >> suspend "AssertUnreachable") >>
  TRY(rename1 `AssertReason` >> suspend "AssertReason") >>
  TRY(rename1 `Log` >> suspend "Log") >>
  TRY(rename1 `AnnAssign` >> suspend "AnnAssign") >>
  TRY(rename1 `Append` >> suspend "Append") >>
  TRY(rename1 `Assign` >> suspend "Assign") >>
  TRY(rename1 `AugAssign` >> suspend "AugAssign") >>
  TRY(rename1 `If` >> suspend "If") >>
  TRY(rename1 `For` >> suspend "For") >>
  TRY(rename1 `Expr` >> suspend "Expr") >>
  TRY(rename1 `eval_stmts _ []` >> suspend "Stmts_nil") >>
  TRY(rename1 `eval_stmts _ (_::_)` >> suspend "Stmts_cons") >>
  TRY(rename1 `eval_for _ _ _ _ []` >> suspend "For_nil") >>
  TRY(rename1 `eval_for _ _ _ _ (_::_)` >> suspend "For_cons") >>
  TRY(rename1 `Array` >> suspend "Iterator_Array") >>
  TRY(rename1 `Range` >> suspend "Iterator_Range") >>
  TRY(rename1 `BaseTarget` >> suspend "Target_Base") >>
  TRY(rename1 `TupleTarget` >> suspend "Target_Tuple") >>
  TRY(rename1 `eval_targets _ []` >> suspend "Targets_nil") >>
  TRY(rename1 `eval_targets _ (_::_)` >> suspend "Targets_cons") >>
  TRY(rename1 `NameTarget` >> suspend "BaseTarget_Name") >>
  TRY(rename1 `TopLevelNameTarget` >> suspend "BaseTarget_TopLevel") >>
  TRY(rename1 `SubscriptTarget` >> suspend "BaseTarget_Subscript") >>
  TRY(rename1 `AttributeTarget` >> suspend "BaseTarget_Attribute") >>
  TRY(rename1 `Name` >> suspend "Expr_Name") >>
  TRY(rename1 `TopLevelName` >> suspend "Expr_TopLevelName") >>
  TRY(rename1 `FlagMember` >> suspend "Expr_FlagMember") >>
  TRY(rename1 `IfExp` >> suspend "Expr_IfExp") >>
  TRY(rename1 `Literal` >> suspend "Expr_Literal") >>
  TRY(rename1 `StructLit` >> suspend "Expr_StructLit") >>
  TRY(rename1 `Subscript` >> suspend "Expr_Subscript") >>
  TRY(rename1 `Attribute` >> suspend "Expr_Attribute") >>
  TRY(rename1 `Builtin` >> suspend "Expr_Builtin") >>
  TRY(rename1 `TypeBuiltin` >> suspend "Expr_TypeBuiltin") >>
  TRY(rename1 `Pop` >> suspend "Expr_Pop") >>
  TRY(rename1 `IntCall` >> suspend "Expr_Call_IntCall") >>
  TRY(rename1 `ExtCall` >> suspend "Expr_Call_ExtCall") >>
  TRY(rename1 `Send` >> suspend "Expr_Call_Send") >>
  TRY(rename1 `RawCallTarget` >> suspend "Expr_Call_RawCallTarget") >>
  TRY(rename1 `RawLog` >> suspend "Expr_Call_RawLog") >>
  TRY(rename1 `RawRevert` >> suspend "Expr_Call_RawRevert") >>
  TRY(rename1 `SelfDestructTarget` >> suspend "Expr_Call_SelfDestructTarget") >>
  TRY(rename1 `CreateTarget` >> suspend "Expr_Call_CreateTarget") >>
  TRY(rename1 `eval_exprs _ []` >> suspend "Exprs_nil") >>
  TRY(rename1 `eval_exprs _ (_::_)` >> suspend "Exprs_cons")
QED

Resume eval_all_storage_preservation_mutual[For_nil]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Return_SOME]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_apply] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (er,s1)` >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Return (SOME e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_expr_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx s1` by metis_tac[] >>
  Cases_on `er` >> gvs[]
  >- (
    Cases_on `materialise cx x s1` >>
    `r = s1` by metis_tac[materialise_state] >> gvs[] >>
    Cases_on `q` >> gvs[raise_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Return_NONE]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Pass]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Continue]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Break]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[RaiseBare]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[RaiseUnreachable]:
  gvs[evaluate_def, raise_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Stmts_nil]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Targets_nil]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Exprs_nil]:
  gvs[evaluate_def, return_def, runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Expr_FlagMember]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_flag_mem_state >>
  gvs[runtime_storage_consistent_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Expr_Literal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >> gvs[runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Expr_Name]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, get_scopes_def,
    lift_option_type_def] >>
  Cases_on `lookup_scopes_val (string_to_num id) st.scopes` >>
  gvs[bind_def, return_def, raise_def, runtime_storage_consistent_def] >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Expr_TopLevelName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >>
  imp_res_tac lookup_global_state >> gvs[runtime_storage_consistent_def]
QED

Resume eval_all_storage_preservation_mutual[Stmts_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmts (s::ss))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmt s)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_stmts ss` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_stmt s` >> simp[]) >>
  qpat_x_assum `type_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def, AllCaseEqs()] >> strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, ignore_bind_apply] >>
  Cases_on `eval_stmt cx s st` >>
  rename1 `eval_stmt cx s st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `r1` >> gvs[]
  >- (
    qpat_x_assum `runtime_storage_consistent env cx st` mp_tac >>
    simp[runtime_storage_consistent_def, runtime_consistent_def] >>
    strip_tac >>
    drule_all eval_stmt_type_preservation_success >> strip_tac >>
    `runtime_storage_consistent env'' cx st1` by
      simp[runtime_storage_consistent_def, runtime_consistent_def] >>
    Cases_on `eval_stmts cx ss st1` >>
    first_x_assum drule_all >> strip_tac >>
    gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
  gvs[bind_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[BaseTarget_Subscript]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (SubscriptTarget bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> simp[]) >>
  qpat_x_assum `type_place_target _ (SubscriptTarget _ _) = _` mp_tac >>
  rewrite_tac[type_place_target_SubscriptTarget] >> strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (bt_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_base_target_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `bt_res` >> gvs[return_def]
  >- (
    PairCases_on `x` >> gvs[bind_def, return_def] >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    `contract_storage_well_formed cx st2` by metis_tac[] >>
    Cases_on `expr_res` >> gvs[bind_def, return_def]
    >- (
      Cases_on `get_Value x st2` >>
      imp_res_tac get_Value_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[BaseTarget_Attribute]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_target (AttributeTarget bt id))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  CONV_TAC(LAND_CONV(LAND_CONV(ONCE_REWRITE_CONV[well_typed_expr_def]))) >>
  simp[AllCaseEqs(), PULL_EXISTS] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx bt st` >>
  simp[AllCaseEqs(), return_def, EXISTS_PROD] >>
  ntac 3 strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[BaseTarget_TopLevel]:
  rpt gen_tac >>
  imp_res_tac eval_base_target_TopLevelNameTarget_preserves_state >>
  gvs[] >> metis_tac[runtime_storage_consistent_storage]
QED

Resume eval_all_storage_preservation_mutual[BaseTarget_Name]:
  rpt gen_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, assert_def, ignore_bind_def,
       get_scopes_def, type_check_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num id) st.scopes)` >>
  gvs[return_def, raise_def] >> rpt strip_tac >>
  metis_tac[runtime_storage_consistent_storage]
QED

Resume eval_all_storage_preservation_mutual[Target_Base]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_atarget (BaseTarget bt))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  gvs[well_typed_atarget_def, well_typed_target_def] >>
  Cases_on `eval_base_target cx bt st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[]
  >- (PairCases_on `x` >> gvs[return_def] >> rpt strip_tac >> gvs[]) >>
  gvs[return_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Target_Tuple]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_atarget (TupleTarget tgts))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  gvs[well_typed_atarget_def] >>
  Cases_on `eval_targets cx tgts st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[return_def] >> rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Exprs_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_exprs (e::es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_exprs es` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx st1` by metis_tac[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `r1` >> gvs[]
  >- (
    Cases_on `materialise cx x st1` >>
    rename1 `materialise cx x st1 = (mr,stm)` >>
    `stm = st1` by metis_tac[materialise_state] >> gvs[] >>
    Cases_on `mr` >> gvs[]
    >- (
      Cases_on `eval_exprs cx es st1` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `q` >> gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Targets_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_atargets (tgt::tgts))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_atarget tgt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_atargets tgts` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_atargets tgts)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_atarget tgt` >> simp[]) >>
  Cases_on `tys` >- fs[] >>
  qpat_x_assum `LIST_REL _ (tgt::tgts) (h::t)` mp_tac >>
  simp_tac(srw_ss())[listTheory.LIST_REL_CONS1] >> strip_tac >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target cx tgt st` >>
  rename1 `eval_target cx tgt st = (target_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_target_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `target_res` >> gvs[return_def]
  >- (
    Cases_on `eval_targets cx tgts st1` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `q` >> gvs[bind_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[RaiseReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def]
  >- (
    Cases_on `get_Value x st1` >>
    imp_res_tac get_Value_state >> gvs[] >>
    Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
    Cases_on `lift_option_type (dest_StringV x') "not StringV" r` >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    Cases_on `q` >> gvs[return_def, raise_def] >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[AssertBare]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertBare))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def,
    listTheory.APPEND_NIL] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def] >>
  Cases_on `get_Value x st1` >> imp_res_tac get_Value_state >> gvs[] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
  strip_tac >>
  `st' = r` by
    (qspecl_then [`x`, `return ()`, `raise (AssertException "")`,
                  `r`, `res`, `st'`] mp_tac switch_BoolV_state >>
     simp[return_def, raise_def] >> metis_tac[]) >>
  qpat_x_assum `st' = r` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Resume eval_all_storage_preservation_mutual[AssertUnreachable]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertUnreachable))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def,
    listTheory.APPEND_NIL] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def] >>
  Cases_on `get_Value x st1` >> imp_res_tac get_Value_state >> gvs[] >>
  Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
  strip_tac >>
  `st' = r` by
    (qspecl_then [`x`, `return ()`, `raise (AssertException "UNREACHABLE")`,
                  `r`, `res`, `st'`] mp_tac switch_BoolV_state >>
     simp[return_def, raise_def] >> metis_tac[]) >>
  qpat_x_assum `st' = r` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Resume eval_all_storage_preservation_mutual[Log]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Log id es))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `exprs_res` >> gvs[bind_def, return_def, push_log_def] >>
  Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id x` >>
  gvs[lift_option_def, raise_def, return_def, push_log_def] >>
  rpt strip_tac >>
  pop_assum (SUBST1_TAC o SYM) >>
  metis_tac[contract_storage_well_formed_logs]
QED

Resume eval_all_storage_preservation_mutual[Iterator_Array]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Array e))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[bind_def, return_def]
  >- (
    Cases_on `materialise cx x st1` >>
    rename1 `materialise cx x st1 = (mat_res,stm)` >>
    imp_res_tac materialise_state >> gvs[] >>
    Cases_on `mat_res` >> gvs[bind_def, return_def] >>
    strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
    imp_res_tac lift_option_type_state >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Expr_Attribute]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Attribute ty e id))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (Attribute _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `base_res` >> gvs[bind_def, return_def, raise_def]
  >- (
    Cases_on `get_Value x st1` >> imp_res_tac get_Value_state >> gvs[] >>
    Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
    Cases_on `lift_sum (evaluate_attribute x' id) r` >>
    imp_res_tac lift_sum_state >> gvs[] >>
    Cases_on `q` >> gvs[return_def, raise_def] >>
    rpt strip_tac >>
    gvs[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]
QED

Resume eval_all_storage_preservation_mutual[Expr_TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (TypeBuiltin ty tb typ es))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `well_typed_exprs env es` by
      (qpat_x_assum `well_typed_expr env (TypeBuiltin ty tb typ es)` mp_tac >>
       simp_tac(srw_ss())[Once well_typed_expr_def]) >>
    `type_builtin_args_length_ok tb (LENGTH es)` by
      (qpat_assum `well_typed_expr env (TypeBuiltin v11 tb typ es)` mp_tac >>
       CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
       strip_tac >> drule well_typed_type_builtin_args_length >> simp[]) >>
    qpat_x_assum `eval_expr _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      return_def, raise_def, type_check_def, assert_def] >>
    qpat_assum `type_builtin_args_length_ok tb (LENGTH es)`
      (fn th => rewrite_tac[th]) >>
    simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
      type_check_def, assert_def] >>
    qpat_x_assum `!s'' x t. type_check _ _ _ = _ ==> _`
      (qspecl_then [`st`, `()`, `st`] mp_tac) >>
    (impl_tac >- simp[type_check_def, assert_def, return_def]) >> strip_tac >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (exprs_res,st1)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `exprs_res` >> gvs[bind_def, return_def, raise_def]
    >- (
      Cases_on `lift_sum (evaluate_type_builtin cx tb typ x) st1` >>
      imp_res_tac lift_sum_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_expr env (TypeBuiltin ty tb typ es) = SOME vt` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Resume eval_all_storage_preservation_mutual[Expr_Call_RawRevert]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Call ty RawRevert es extra))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call ty RawRevert es extra)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def]
    >- (Cases_on `LENGTH x = 1` >> gvs[] >> rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_all_storage_preservation_mutual[Expr_Call_RawLog]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Call ty RawLog es extra))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call ty RawLog es extra)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def, push_log_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[bind_def, ignore_bind_def, type_check_def,
      assert_def, return_def, raise_def, push_log_def]
    >- (
      strip_tac >> gvs[AllCaseEqs()] >>
      imp_res_tac lift_option_type_state >> gvs[] >>
      metis_tac[contract_storage_well_formed_logs]) >>
    rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED


Resume eval_all_storage_preservation_mutual[Expr_Pop]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Pop v11 bt))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> simp[]) >>
  conj_tac
  >- (
    strip_tac >>
    drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
    qpat_x_assum `eval_expr cx (Pop v11 bt) st = (res,st')` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
    Cases_on `eval_base_target cx bt st` >>
    rename1 `eval_base_target cx bt st = (bt_res,st1)` >>
    first_x_assum drule_all >> strip_tac >>
    `runtime_consistent env cx st1` by
      metis_tac[eval_base_target_preserves_runtime_consistent,
                runtime_storage_consistent_runtime] >>
    `runtime_storage_consistent env cx st1` by
      metis_tac[runtime_storage_consistent_intro,
                runtime_storage_consistent_layout] >>
    Cases_on `bt_res`
    >- (
      PairCases_on `x` >> gvs[] >>
      rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
      strip_tac >>
      qpat_x_assum `do _ od st1 = (res,st')` mp_tac >>
      simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
      Cases_on `assign_target cx (BaseTargetV x0 x1) PopOp st1` >>
      rename1 `assign_target cx (BaseTargetV loc sbs) PopOp st1 = (assign_res,st2)` >>
      `target_runtime_typed env cx st1 (BaseTarget bt)
         (ArrayT elem_ty (Dynamic n)) (BaseTargetV loc sbs)` by (
        irule eval_base_target_success_runtime_typed >> simp[] >>
        metis_tac[runtime_storage_consistent_runtime]) >>
      `?elem_tv. evaluate_type env.type_defs elem_ty = SOME elem_tv` by (
        `?vt final_tv.
           location_runtime_typed env cx st1 loc vt /\
           target_path_type env vt sbs (Type (ArrayT elem_ty (Dynamic n))) /\
           place_leaf_typed env vt sbs (ArrayT elem_ty (Dynamic n)) final_tv` by
          metis_tac[target_runtime_typed_place_leaf_typed] >>
        `evaluate_type env.type_defs (ArrayT elem_ty (Dynamic n)) = SOME final_tv` by
          metis_tac[place_leaf_typed_evaluate_type] >>
        Cases_on `evaluate_type env.type_defs elem_ty` >> gvs[evaluate_type_def]) >>
      `assign_operation_runtime_typed env (ArrayT elem_ty (Dynamic n)) PopOp` by
        metis_tac[stmt_assign_operation_runtime_typed_Pop_from_dynamic_array] >>
      `assign_operation_matches_target_shape (BaseTargetV loc sbs) PopOp` by
        simp[assign_operation_matches_target_shape_def] >>
      `assign_target_assignable_context cx (BaseTargetV loc sbs) st1` by
        metis_tac[target_runtime_typed_imp_assignable_context,
                  runtime_consistent_def] >>
      `runtime_storage_consistent env cx st2` by
        metis_tac[assign_target_preserves_runtime_storage_consistent_result] >>
      strip_tac >> Cases_on `assign_res` >> gvs[return_def, raise_def]
      >- (
        Cases_on `lift_option_type x "Pop returned NONE" st2` >>
        imp_res_tac lift_option_type_state >>
        Cases_on `q` >> gvs[return_def, raise_def] >>
        metis_tac[runtime_storage_consistent_storage]) >>
      metis_tac[runtime_storage_consistent_storage]) >>
    rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[Once well_typed_expr_def]
QED


Resume eval_all_storage_preservation_mutual[Expr_Call_RawCallTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `call_evaluation_safe cx
      (int_calls_expr (Call _ (RawCallTarget _) es _))` mp_tac >>
    simp[int_calls_expr_def] >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (RawCallTarget _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, raise_def,
      lift_option_type_def] >> simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    `runtime_consistent env cx args_st` by
      metis_tac[eval_exprs_preserves_runtime_consistent,
                runtime_storage_consistent_runtime] >>
    `runtime_storage_consistent env cx args_st` by
      metis_tac[runtime_storage_consistent_intro,
                runtime_storage_consistent_layout] >>
    Cases_on `args_res` >> gvs[]
    >- (
      rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      `exprs_runtime_typed env es vs` by (
        irule eval_exprs_success_runtime_typed >> simp[] >>
        metis_tac[runtime_storage_consistent_runtime]) >>
      `LENGTH vs = 3` by (
        gvs[exprs_runtime_typed_def] >>
        metis_tac[listTheory.LIST_REL_LENGTH]) >>
      mp_tac raw_call_args_runtime_typed_dest >>
      impl_tac >- simp[] >> strip_tac >> gvs[] >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, check_def, assert_def,
        return_def, raise_def, lift_option_def, get_accounts_def,
        get_transient_storage_def, update_accounts_def, update_transient_def] >>
      Cases_on `flags.rcf_is_delegate` >> gvs[return_def, raise_def] >>
      Cases_on `run_ext_call cx.txn.target target_addr data
                  (if flags.rcf_is_static then NONE else SOME amount)
                  args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >>
      gvs[return_def, raise_def]
      >- (rpt strip_tac >> gvs[] >>
          metis_tac[runtime_storage_consistent_storage]) >>
      PairCases_on `x` >> gvs[] >>
      `contract_storage_well_formed cx
         (args_st with <|accounts := x2; tStorage := x3|>)` by
        metis_tac[protected_storage_calls_preserve_run_ext_call,
                  runtime_storage_consistent_storage] >>
      `contract_storage_well_formed cx
         ((args_st with <|accounts := x2; tStorage := x3|>) with
            logs := args_st.logs ++ x4)` by
        metis_tac[contract_storage_well_formed_logs] >>
      strip_tac >>
      gvs[update_accounts_def, update_transient_def, bind_def, return_def] >>
      Cases_on `x0` >> Cases_on `flags.rcf_revert_on_failure` >>
      Cases_on `flags.rcf_max_outsize = 0` >>
      gvs[check_def, assert_def, bind_def, return_def, raise_def,
          append_logs_def]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED


Resume eval_all_storage_preservation_mutual[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `get_tenv cx = env.type_defs` by
    fs[runtime_consistent_def, env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type env.type_defs typ = SOME tyv` by (
    drule assignable_type_well_formed >>
    simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  asm_rewrite_tac[] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  qpat_x_assum `!tenv s'' tyv t. _`
    (qspecl_then [`env.type_defs`, `st`, `tyv`, `st`] mp_tac) >>
  simp[lift_option_type_def, return_def] >>
  disch_then drule_all >> strip_tac >>
  simp[bind_apply, return_def] >>
  Cases_on `expr_res` >> gvs[raise_def]
  >- (
    Cases_on `materialise cx x st1` >>
    rename1 `materialise cx x st1 = (mat_res,stm)` >>
    imp_res_tac materialise_state >> gvs[] >>
    Cases_on `mat_res` >> gvs[return_def, raise_def]
    >- (
      strip_tac >>
      metis_tac[new_variable_preserves_contract_storage_well_formed]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED


Resume eval_all_storage_preservation_mutual[Assign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assign tgt e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_atarget tgt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_atarget tgt` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_target cx tgt st` >>
  rename1 `eval_target cx tgt st = (target_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  strip_tac >> Cases_on `target_res`
  >- (
    rename1 `eval_target cx tgt st = (INL gv,st1)` >>
    qpat_x_assum `case (INL _,_) of _ => _ | _ => _` mp_tac >>
    rewrite_tac[] >> strip_tac >>
    `runtime_consistent env cx st1` by
      metis_tac[eval_target_preserves_runtime_consistent,
                runtime_storage_consistent_runtime] >>
    `runtime_storage_consistent env cx st1` by
      metis_tac[runtime_storage_consistent_intro,
                runtime_storage_consistent_layout] >>
    `target_runtime_typed env cx st1 tgt (expr_type e) gv` by (
      irule eval_target_success_runtime_typed >> simp[] >>
      metis_tac[runtime_storage_consistent_runtime]) >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    `runtime_consistent env cx st2` by
      metis_tac[eval_expr_preserves_runtime_consistent] >>
    `runtime_storage_consistent env cx st2` by
      metis_tac[runtime_storage_consistent_intro,
                runtime_storage_consistent_layout] >>
    Cases_on `expr_res` >> gvs[]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl,st2)` >>
      `expr_result_typed env e tvl` by
        metis_tac[eval_expr_success_result_typed] >>
      Cases_on `materialise cx tvl st2` >>
      rename1 `materialise cx tvl st2 = (mat_res,stm)` >>
      imp_res_tac materialise_state >> gvs[] >>
      Cases_on `mat_res` >> gvs[return_def, raise_def]
      >- (
        rename1 `materialise cx tvl st2 = (INL v,st2)` >>
        Cases_on `assign_target cx gv (Replace v) st2` >>
        rename1 `assign_target cx gv (Replace v) st2 = (assign_res,st4)` >>
        `?tv. evaluate_type env.type_defs (expr_type e) = SOME tv` by (
          drule assignable_type_well_formed >>
          simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
        `value_has_type tv v` by
          metis_tac[expr_result_typed_materialise_preserves_value_type,
                    runtime_consistent_def] >>
        `value_runtime_typed env (expr_type e) v` by
          (simp[value_runtime_typed_def] >> qexists_tac `tv` >> simp[]) >>
        `target_runtime_typed env cx st2 tgt (expr_type e) gv` by
          metis_tac[target_runtime_typed_rebuild, runtime_consistent_def] >>
        `assign_operation_runtime_typed env (expr_type e) (Replace v)` by
          simp[assign_operation_runtime_typed_def] >>
        `assign_operation_matches_target_shape gv (Replace v)` by
          metis_tac[assign_operation_matches_target_shape_Replace_from_typed] >>
        `assign_target_assignable_context cx gv st2` by
          metis_tac[target_runtime_typed_imp_assignable_context,
                    runtime_consistent_def] >>
        `runtime_storage_consistent env cx st4` by
          metis_tac[assign_target_preserves_runtime_storage_consistent_result] >>
        qpat_x_assum `do _ od _ = _` mp_tac >>
        simp[bind_apply, return_def] >>
        Cases_on `assign_res` >> gvs[ignore_bind_apply, return_def] >>
        rpt strip_tac >>
        metis_tac[runtime_storage_consistent_storage]) >>
      rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED


Resume eval_all_storage_preservation_mutual[Append]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Append bt e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >>
  Cases_on `type_place_target env bt` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME vt` >>
  Cases_on `vt` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type ty)` >>
  Cases_on `ty` >> simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty bd))` >>
  Cases_on `bd` >- simp[NoAsms] >>
  simp[NoAsms] >>
  rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
  strip_tac >>
  qpat_x_assum `env = env'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `expr_type e = elem_ty` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (bt_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_base_target_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `bt_res`
  >- (
    PairCases_on `x` >>
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >>
    rewrite_tac[] >> strip_tac >>
    rename1 `eval_base_target cx bt st = (INL (loc,sbs),st1)` >>
    `target_runtime_typed env cx st1 (BaseTarget bt)
       (ArrayT (expr_type e) (Dynamic n)) (BaseTargetV loc sbs)` by (
      irule eval_base_target_success_runtime_typed >> simp[] >>
      metis_tac[runtime_storage_consistent_runtime]) >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    `runtime_consistent env cx st2` by
      metis_tac[eval_expr_preserves_runtime_consistent] >>
    `runtime_storage_consistent env cx st2` by
      metis_tac[runtime_storage_consistent_intro,
                runtime_storage_consistent_layout] >>
    Cases_on `expr_res` >> gvs[]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl,st2)` >>
      `expr_result_typed env e tvl` by
        metis_tac[eval_expr_success_result_typed] >>
      Cases_on `materialise cx tvl st2` >>
      rename1 `materialise cx tvl st2 = (mat_res,stm)` >>
      imp_res_tac materialise_state >> gvs[] >>
      Cases_on `mat_res` >> gvs[return_def, raise_def]
      >- (
        rename1 `materialise cx tvl st2 = (INL v,st2)` >>
        Cases_on `assign_target cx (BaseTargetV loc sbs) (AppendOp v) st2` >>
        rename1 `assign_target cx (BaseTargetV loc sbs) (AppendOp v) st2 =
                   (assign_res,st4)` >>
        `?elem_tv. evaluate_type env.type_defs (expr_type e) = SOME elem_tv` by (
          drule assignable_type_well_formed >>
          simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
        `value_has_type elem_tv v` by
          metis_tac[expr_result_typed_materialise_preserves_value_type,
                    runtime_consistent_def] >>
        `target_runtime_typed env cx st2 (BaseTarget bt)
           (ArrayT (expr_type e) (Dynamic n)) (BaseTargetV loc sbs)` by
          metis_tac[target_runtime_typed_rebuild, runtime_consistent_def] >>
        `assign_operation_runtime_typed env
           (ArrayT (expr_type e) (Dynamic n)) (AppendOp v)` by
          metis_tac[stmt_assign_operation_runtime_typed_Append_from_value_has_type] >>
        `assign_operation_matches_target_shape (BaseTargetV loc sbs) (AppendOp v)` by
          simp[stmt_assign_operation_matches_target_shape_Append_BaseTargetV] >>
        `assign_target_assignable_context cx (BaseTargetV loc sbs) st2` by
          metis_tac[target_runtime_typed_imp_assignable_context,
                    runtime_consistent_def] >>
        `assignable_type env.type_defs (ArrayT (expr_type e) (Dynamic n))` by (
          simp[assignable_type_def, well_formed_type_def] >>
          drule_at(Pat`target_runtime_typed`) target_runtime_typed_place_leaf_typed >>
          simp[] >> strip_tac >>
          drule place_leaf_typed_evaluate_type >>
          simp[optionTheory.IS_SOME_EXISTS]) >>
        `runtime_storage_consistent env cx st4` by
          metis_tac[assign_target_preserves_runtime_storage_consistent_result] >>
        qpat_x_assum `do _ od _ = _` mp_tac >>
        simp[bind_apply, return_def] >>
        Cases_on `assign_res` >> gvs[ignore_bind_apply, return_def] >>
        rpt strip_tac >>
        metis_tac[runtime_storage_consistent_storage]) >>
      qpat_x_assum `do _ od _ = _` mp_tac >>
      simp[bind_apply, bind_def, return_def] >>
      rpt strip_tac >> gvs[]) >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, bind_def, return_def] >>
    rpt strip_tac >> gvs[]) >>
  qpat_x_assum `case (INR _,_) of _ => _ | _ => _` mp_tac >>
  rewrite_tac[] >> rpt strip_tac >> gvs[]
QED


Resume eval_all_storage_preservation_mutual[AugAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (AugAssign ty bt bop e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_target bt` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (target_res,st1)` >>
  `type_place_target env bt = SOME (Type ty)` by
    fs[well_typed_target_def] >>
  qpat_x_assum `!env vt st res st'. _ /\ _ /\ _ /\ _ /\ _ /\
                  eval_base_target _ _ _ = _ ==> _`
    (qspecl_then [`env`, `Type ty`, `st`, `target_res`, `st1`] mp_tac) >>
  simp[] >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_base_target_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `target_res`
  >- (
    PairCases_on `x` >>
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >>
    rewrite_tac[] >> strip_tac >>
    rename1 `eval_base_target cx bt st = (INL (loc,sbs),st1)` >>
    `type_place_target env bt = SOME (Type ty)` by
      fs[well_typed_target_def] >>
    `target_runtime_typed env cx st1 (BaseTarget bt) ty
       (BaseTargetV loc sbs)` by (
      irule eval_base_target_success_runtime_typed >> simp[] >>
      metis_tac[runtime_storage_consistent_runtime]) >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    `runtime_consistent env cx st2` by
      metis_tac[eval_expr_preserves_runtime_consistent] >>
    `runtime_storage_consistent env cx st2` by
      metis_tac[runtime_storage_consistent_intro,
                runtime_storage_consistent_layout] >>
    Cases_on `expr_res` >> gvs[]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl,st2)` >>
      `expr_result_typed env e tvl` by
        metis_tac[eval_expr_success_result_typed] >>
      Cases_on `get_Value tvl st2` >>
      rename1 `get_Value tvl st2 = (val_res,st3)` >>
      imp_res_tac get_Value_state >> gvs[] >>
      Cases_on `val_res` >> gvs[return_def, raise_def]
      >- (
        rename1 `get_Value tvl st2 = (INL v,st2)` >>
        `tvl = Value v` by (
          qpat_x_assum `get_Value _ _ = _` mp_tac >>
          Cases_on `tvl` >> simp[get_Value_def, return_def, raise_def]) >>
        `target_runtime_typed env cx st2 (BaseTarget bt) ty
           (BaseTargetV loc sbs)` by
          metis_tac[target_runtime_typed_rebuild, runtime_consistent_def] >>
        `assign_operation_runtime_typed env ty (Update ty bop v)` by (
          simp[assign_operation_runtime_typed_def] >>
          qexists_tac `expr_type e` >>
          gvs[expr_result_typed_def, expr_runtime_typed_def,
              value_runtime_typed_def, toplevel_value_typed_def]) >>
        `assign_operation_matches_target_shape (BaseTargetV loc sbs)
           (Update ty bop v)` by
          simp[assign_operation_matches_target_shape_def] >>
        `assign_target_assignable_context cx (BaseTargetV loc sbs) st2` by
          metis_tac[target_runtime_typed_imp_assignable_context,
                    runtime_consistent_def] >>
        Cases_on `assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st2` >>
        rename1 `assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st2 =
                   (assign_res,st4)` >>
        `runtime_storage_consistent env cx st4` by
          metis_tac[assign_target_preserves_runtime_storage_consistent_result] >>
        qpat_x_assum `do _ od _ = _` mp_tac >>
        simp[bind_apply, return_def] >>
        Cases_on `assign_res` >> gvs[ignore_bind_apply, return_def] >>
        rpt strip_tac >>
        metis_tac[runtime_storage_consistent_storage]) >>
      qpat_x_assum `do _ od _ = _` mp_tac >>
      simp[bind_apply, bind_def, return_def] >>
      rpt strip_tac >> gvs[]) >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, bind_def, return_def] >>
    rpt strip_tac >> gvs[]) >>
  qpat_x_assum `case (INR _,_) of _ => _ | _ => _` mp_tac >>
  rewrite_tac[] >> rpt strip_tac >> gvs[]
QED


Resume eval_all_storage_preservation_mutual[Expr]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Expr e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, type_check_def,
    assert_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx e st` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q` >> gvs[] >>
  rpt strip_tac >> gvs[]
QED


Resume eval_all_storage_preservation_mutual[If]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (If e ss ss'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts ss')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_stmts ss ++ int_calls_stmts ss'` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (cond_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `cond_res`
  >- (
    rename1 `eval_expr cx e st = (INL tv,st1)` >>
    `expr_result_typed env e tv` by (
      irule eval_expr_success_result_typed >> simp[] >>
      metis_tac[runtime_storage_consistent_runtime]) >>
    gvs[expr_result_typed_def, expr_runtime_typed_def, evaluate_type_def] >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    `runtime_storage_consistent env cx
       (st1 with scopes updated_by CONS FEMPTY)` by (
      irule push_scope_preserves_runtime_storage_consistent >>
      qexistsl_tac [`INL ()`, `st1`] >>
      simp[push_scope_def, return_def]) >>
    Cases_on `b` >>
    simp[bind_apply, push_scope_def, return_def, switch_BoolV_def]
    >- (
      qpat_x_assum `IS_SOME (type_stmts env ret_ty ss)` mp_tac >>
      simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      Cases_on `eval_stmts cx ss (st1 with scopes updated_by CONS FEMPTY)` >>
      rename1 `eval_stmts cx ss (st1 with scopes updated_by CONS FEMPTY) =
                 (body_res,stb)` >>
      `push_scope st1 =
         (INL (),st1 with scopes updated_by CONS FEMPTY)` by
        simp[push_scope_def, return_def] >>
      first_x_assum drule_all >> strip_tac >>
      `contract_storage_well_formed cx stb` by simp[] >>
      qpat_x_assum `do _ od _ = _` mp_tac >>
      simp[bind_apply, push_scope_def, return_def, finally_def,
           ignore_bind_apply] >>
      Cases_on `body_res` >> gvs[] >>
      Cases_on `pop_scope stb` >>
      rename1 `pop_scope stb = (pop_res,stpop)` >>
      `contract_storage_well_formed cx stpop` by (
        irule pop_scope_preserves_contract_storage_well_formed >>
        qexistsl_tac [`pop_res`, `stb`] >> simp[]) >>
      Cases_on `pop_res` >> gvs[] >>
      rpt strip_tac >> gvs[raise_def]) >>
    qpat_x_assum `IS_SOME (type_stmts env ret_ty ss')` mp_tac >>
    simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
    Cases_on `eval_stmts cx ss' (st1 with scopes updated_by CONS FEMPTY)` >>
    rename1 `eval_stmts cx ss' (st1 with scopes updated_by CONS FEMPTY) =
               (body_res,stb)` >>
    `push_scope st1 =
       (INL (),st1 with scopes updated_by CONS FEMPTY)` by
      simp[push_scope_def, return_def] >>
    first_x_assum drule_all >> strip_tac >>
    `contract_storage_well_formed cx stb` by simp[] >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, push_scope_def, return_def, finally_def,
         ignore_bind_apply] >>
    Cases_on `body_res` >> gvs[] >>
    Cases_on `pop_scope stb` >>
    rename1 `pop_scope stb = (pop_res,stpop)` >>
    `contract_storage_well_formed cx stpop` by (
      irule pop_scope_preserves_contract_storage_well_formed >>
      qexistsl_tac [`pop_res`, `stb`] >> simp[]) >>
    Cases_on `pop_res` >> gvs[] >>
    rpt strip_tac >> gvs[raise_def]) >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[bind_apply, bind_def] >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[AssertReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx
    (int_calls_stmt (Assert e (AssertReason e')))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `expr_res` >> gvs[bind_def, return_def, raise_def]
  >- (
    `expr_result_typed env e x` by (
      irule eval_expr_success_result_typed >> simp[] >>
      metis_tac[runtime_storage_consistent_runtime]) >>
    gvs[expr_result_typed_def, expr_runtime_typed_def, evaluate_type_def] >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def] >>
    Cases_on `eval_expr cx e' st1` >>
    rename1 `eval_expr cx e' st1 = (reason_res,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `reason_res` >> gvs[bind_def, return_def, raise_def] >>
    Cases_on `get_Value x st2` >> imp_res_tac get_Value_state >> gvs[] >>
    Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
    Cases_on `lift_option_type (dest_StringV x') "not StringV" r` >>
    imp_res_tac lift_option_type_state >> gvs[] >>
    Cases_on `q` >> gvs[return_def, raise_def] >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Iterator_Range]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Range e e'))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr1_res,st1)` >>
  last_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `expr1_res` >> gvs[bind_def, return_def, raise_def]
  >- (
    Cases_on `get_Value x st1` >>
    imp_res_tac get_Value_state >> gvs[] >>
    Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
    qpat_x_assum `∀s'' tv1 t s''' s t'. _`
      (qspecl_then [`st`, `x`, `r`, `r`, `x'`, `r`] mp_tac) >>
    simp[] >> strip_tac >>
    pop_assum mp_tac >>
    Cases_on `eval_expr cx e' r` >>
    rename1 `eval_expr cx e' r = (expr2_res,st2)` >>
    simp[] >> strip_tac >>
    Cases_on `expr2_res` >> gvs[bind_def, return_def, raise_def]
    >- (
      Cases_on `get_Value x'' st2` >>
      imp_res_tac get_Value_state >> gvs[] >>
      Cases_on `q` >> gvs[bind_def, return_def, raise_def] >>
      Cases_on `lift_sum (get_range_limits x' x''') r'` >>
      imp_res_tac lift_sum_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> metis_tac[]) >>
    rpt strip_tac >> metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED

Resume eval_all_storage_preservation_mutual[Expr_IfExp]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx
    (int_calls_expr (IfExp ty e e' e''))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e'')` by
    (irule call_evaluation_safe_mono >>
     qexists_tac `int_calls_expr e ++ int_calls_expr e' ++ int_calls_expr e''` >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (IfExp _ _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  disch_then mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (cond_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_preserves_runtime_consistent,
              runtime_storage_consistent_runtime] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `cond_res`
  >- (
    rename1 `eval_expr cx e st = (INL tv,st1)` >>
    `expr_result_typed env e tv` by (
      irule eval_expr_success_result_typed >> simp[] >>
      metis_tac[runtime_storage_consistent_runtime]) >>
    `toplevel_value_typed tv (BaseTV BoolT)` by (
      gvs[expr_result_typed_def, expr_runtime_typed_def, evaluate_type_def]) >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    BasicProvers.VAR_EQ_TAC >>
    Cases_on `b` >> gvs[switch_BoolV_def]
    >- (qpat_x_assum
          `∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
             ∀env' st' res st''. _ ∧ eval_expr cx e' st' = (res,st'') ⇒ _`
          (qspecl_then [`st`, `Value (BoolV T)`, `st1`] mp_tac) >>
        simp[] >> strip_tac >> metis_tac[]) >>
    qpat_x_assum
      `∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
         ∀env' st' res st''. _ ∧ eval_expr cx e'' st' = (res,st'') ⇒ _`
      (qspecl_then [`st`, `Value (BoolV F)`, `st1`] mp_tac) >>
    simp[] >> strip_tac >> metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem int_calls_exprs_MAP_SND_storage[local]:
  !kes. int_calls_exprs (MAP SND kes) = int_calls_named_exprs kes
Proof
  Induct >> simp[int_calls_expr_def] >> gen_tac >> PairCases_on `h` >>
  simp[int_calls_expr_def]
QED

Theorem well_typed_named_exprs_MAP_SND_storage[local]:
  !env kes. well_typed_named_exprs env kes ==>
            well_typed_exprs env (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

Resume eval_all_storage_preservation_mutual[Expr_StructLit]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx
    (int_calls_expr (StructLit ty callee kes))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def, GSYM int_calls_exprs_MAP_SND_storage] >> strip_tac >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (StructLit _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_storage >> simp[]) >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,st1)` >>
  qpat_x_assum `∀ks. ks = MAP FST kes ⇒ _`
    (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >> disch_then drule_all >> strip_tac >>
  Cases_on `exprs_res` >> gvs[bind_def, return_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem call_evaluation_safe_int_calls_exprs_HD_storage[local]:
  es <> [] /\ call_evaluation_safe cx (int_calls_exprs es) ==>
  call_evaluation_safe cx (int_calls_expr (HD es))
Proof
  Cases_on `es` >> simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Resume eval_all_storage_preservation_mutual[Expr_Builtin]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Builtin ty bt es))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >> simp[]) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Builtin _ _ _) = SOME _` mp_tac >>
      simp[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (Builtin ty bt es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
    type_check_def, assert_def] >>
  Cases_on `bt = Len`
  >- (
    `es <> []` by (
      Cases_on `es` >> simp[] >>
      qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type [])` mp_tac >>
      qpat_x_assum `bt = Len` (fn th => rewrite_tac[th]) >>
      simp[well_typed_builtin_app_def]) >>
    `call_evaluation_safe cx (int_calls_expr (HD es))` by
      metis_tac[call_evaluation_safe_int_calls_exprs_HD_storage] >>
    `well_typed_expr env (HD es)` by
      (Cases_on `es` >> gvs[well_typed_expr_def]) >>
    qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
    qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
    simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
      type_check_def, assert_def] >>
    Cases_on `eval_expr cx (HD es) st` >>
    rename1 `eval_expr cx (HD es) st = (arg_res,arg_st)` >>
    qpat_x_assum `∀s'' x t. _ ∧ bt = Len ⇒ _`
      (qspecl_then [`st`, `()`, `st`] mp_tac) >>
    simp[type_check_def, assert_def] >> strip_tac >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `arg_res` >> gvs[bind_def, return_def, raise_def]
    >- (
      Cases_on `toplevel_array_length cx x arg_st` >>
      imp_res_tac toplevel_array_length_state >> gvs[] >>
      Cases_on `q` >> gvs[return_def, raise_def] >>
      rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
    type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `∀s'' x t. _ ∧ bt ≠ Len ⇒ _`
    (qspecl_then [`st`, `()`, `st`] mp_tac) >>
  (impl_tac >- (simp[type_check_def, assert_def] >> metis_tac[])) >>
  strip_tac >> first_x_assum drule_all >> strip_tac >>
  Cases_on `args_res` >> gvs[bind_def, return_def, raise_def,
    get_accounts_def, lift_sum_def]
  >- (Cases_on `evaluate_builtin cx args_st.accounts ty bt x` >>
      gvs[return_def, raise_def] >> rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem transfer_value_storage_frame[local]:
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `transfer_value _ _ _ _ = _` mp_tac >>
  Cases_on `amount = 0 ∨ fromAddr = toAddr`
  >- gvs[transfer_value_def, return_def] >>
  simp[transfer_value_def, bind_apply, ignore_bind_apply,
       get_accounts_def, check_def, assert_def, update_accounts_def,
       return_def, raise_def] >>
  rpt IF_CASES_TAC >> gvs[return_def] >> rpt strip_tac >> gvs[] >>
  Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem transfer_value_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[transfer_value_storage_frame]
QED

Resume eval_all_storage_preservation_mutual[Expr_Call_Send]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `call_evaluation_safe cx (int_calls_exprs es)` by
      (qpat_x_assum `call_evaluation_safe cx (int_calls_expr (Call _ Send es _))`
         mp_tac >> simp[int_calls_expr_def]) >>
    qpat_x_assum `well_typed_expr env (Call _ Send _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    strip_tac >>
    qpat_x_assum `!s'' x t. type_check (LENGTH es = 2) "Send args" s'' = (INL x,t) ==> _`
      (qspecl_then [`st`, `()`, `st`] mp_tac) >>
    (impl_tac >- simp[type_check_def, assert_def]) >>
    strip_tac >> first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[]
    >- (
      Cases_on `dest_AddressV (HD x)` >> gvs[return_def, raise_def] >>
      Cases_on `dest_NumV (x❲1❳)` >> gvs[return_def, raise_def] >>
      Cases_on `transfer_value cx.txn.target x' x'' args_st` >>
      rename1 `transfer_value cx.txn.target x' x'' args_st =
                 (transfer_res,transfer_st)` >>
      drule_all transfer_value_preserves_contract_storage_well_formed >>
      Cases_on `transfer_res` >> gvs[return_def, raise_def]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr env (Call _ Send _ _) = SOME vt` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Resume eval_all_storage_preservation_mutual[Expr_Call_SelfDestructTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `call_evaluation_safe cx (int_calls_exprs es)` by
      (qpat_x_assum `call_evaluation_safe cx
          (int_calls_expr (Call _ SelfDestructTarget es _))` mp_tac >>
       simp[int_calls_expr_def]) >>
    qpat_x_assum `well_typed_expr env (Call _ SelfDestructTarget _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, get_accounts_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[]
    >- (
      Cases_on `LENGTH x = 1` >>
      gvs[type_check_def, assert_def, return_def, raise_def]
      >- (
        Cases_on `dest_AddressV (HD x)` >> gvs[return_def, raise_def]
        >- (rpt strip_tac >> gvs[]) >>
        Cases_on `transfer_value cx.txn.target x'
            (lookup_account cx.txn.target args_st.accounts).balance args_st` >>
        rename1 `transfer_value cx.txn.target x'
            (lookup_account cx.txn.target args_st.accounts).balance args_st =
            (transfer_res,transfer_st)` >>
        drule_all transfer_value_preserves_contract_storage_well_formed >>
        Cases_on `transfer_res` >>
        gvs[bind_apply, ignore_bind_apply, return_def, raise_def] >>
        rpt strip_tac >> gvs[]) >>
      rpt strip_tac >> gvs[]) >>
    rpt strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Theorem increment_nonce_storage_frame[local]:
  update_accounts (vfmExecution$increment_nonce addr) st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `update_accounts _ _ = _` mp_tac >>
  simp[update_accounts_def, return_def] >> strip_tac >> gvs[] >>
  Cases_on `b` >>
  simp[vyperStorageBackendTheory.get_storage_def,
       vfmExecutionTheory.increment_nonce_def,
       vfmStateTheory.update_account_def, vfmStateTheory.lookup_account_def,
       combinTheory.APPLY_UPDATE_THM, AllCaseEqs()] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem increment_nonce_preserves_contract_storage_well_formed[local]:
  contract_storage_well_formed cx st /\
  update_accounts (vfmExecution$increment_nonce addr) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists_tac `st` >> simp[] >>
  metis_tac[increment_nonce_storage_frame]
QED

Resume eval_all_storage_preservation_mutual[Expr_Call_CreateTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    `call_evaluation_safe cx (int_calls_exprs es)` by
      (qpat_x_assum `call_evaluation_safe cx
          (int_calls_expr (Call _ (CreateTarget _ _ _) es _))` mp_tac >>
       simp[int_calls_expr_def]) >>
    qpat_x_assum `well_typed_expr env
        (Call _ (CreateTarget _ _ _) es _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[] >> strip_tac >>
    imp_res_tac eval_create_preserves_non_accounts >>
    imp_res_tac eval_create_preserves_storage >>
    irule contract_storage_well_formed_storage_frame >>
    qexists_tac `args_st` >> simp[] >>
    Cases_on `b` >>
    simp[vyperStorageBackendTheory.get_storage_def] >>
    qpat_x_assum `!address. _` (qspec_then `cx.txn.target` mp_tac) >>
    simp[vfmStateTheory.lookup_account_def]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Theorem eval_iterator_success_values_typed[local]:
  well_typed_iterator env ty it /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_iterator it) /\
  eval_iterator cx it st = (INL vs,st') ==>
  ?tyv. evaluate_type env.type_defs ty = SOME tyv /\
        EVERY (value_has_type tyv) vs
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 3 eval_all_type_sound_mutual) >> simp[]
QED

Resume eval_all_storage_preservation_mutual[For]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx
      (int_calls_stmt (For id typ it n body'))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_iterator it)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_stmts body'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_stmts body')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_iterator it` >> simp[]) >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `env.type_defs = get_tenv cx` by
    (qpat_x_assum `runtime_storage_consistent env cx st` mp_tac >>
     simp[runtime_storage_consistent_def, runtime_consistent_def,
          env_consistent_def, env_context_consistent_def]) >>
  `?env_after. type_stmts (extend_local env (string_to_num id) typ F)
       ret_ty body' = SOME env_after` by
    (qpat_x_assum `IS_SOME (type_stmts _ _ _)` mp_tac >>
     rewrite_tac[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
                       check_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `evaluate_type (get_tenv cx) typ` >> gvs[]
  >- (rpt strip_tac >>
      gvs[bind_apply, return_def, raise_def, runtime_storage_consistent_def]) >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME iter_tyv` >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (iter_res,st1)` >>
  strip_tac >>
  qpat_x_assum `!env' ty' st' res' st''. _` drule_all >> strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_iterator_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `iter_res` >> gvs[bind_apply, return_def, raise_def]
  >- (
    drule_all eval_iterator_success_values_typed >> strip_tac >> gvs[] >>
    Cases_on `compatible_bound (Dynamic n) (LENGTH x)` >>
    gvs[bind_apply, check_def, assert_def, return_def, raise_def]
    >- (
      qpat_x_assum `!s'' vs t. _`
        (qspecl_then [`st`, `x`, `st1`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then
        [`env`, `ret_ty`, `typ`, `env_after`, `st1`, `res`, `st'`] mp_tac) >>
      simp[] >> strip_tac >>
      first_x_assum irule >>
      qpat_x_assum `do assert T _; eval_for _ _ _ _ _ od _ = _` mp_tac >>
      rw[bind_def, ignore_bind_def, assert_def, return_def] ) >>
    rpt strip_tac >>
    gvs[bind_def, ignore_bind_def, assert_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem for_body_decompose_storage[local]:
  stp.scopes <> [] /\
  finally (try do x <- eval_stmts cx body_stmts; return F od handle_loop_exception)
    pop_scope stp = (res,st') ==>
  ?res_body st_body.
    eval_stmts cx body_stmts stp = (res_body,st_body) /\
    st' = st_body with scopes := TL st_body.scopes /\
    ((?x. res_body = INL x) ==> res = INL F) /\
    (res_body = INR ContinueException ==> res = INL F) /\
    (res_body = INR BreakException ==> res = INL T) /\
    (!e. res_body = INR e /\ e <> ContinueException /\ e <> BreakException ==>
         res = INR e) /\
    (!e. res = INR e ==> res_body = INR e)
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def, bind_apply, ignore_bind_apply,
    try_def, return_def, pop_scope_def, raise_def,
    handle_loop_exception_def] >>
  Cases_on `eval_stmts cx body_stmts stp` >>
  `?hd tl. r.scopes = hd::tl` by (
    imp_res_tac vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_len >>
    Cases_on `r.scopes` >> gvs[]) >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y = ContinueException` >> gvs[return_def] >>
  Cases_on `y = BreakException` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[]
QED

Theorem push_scope_with_var_preserves_runtime_storage_consistent[local]:
  runtime_storage_consistent env cx st /\
  evaluate_type env.type_defs ty = SOME tyv /\
  value_has_type tyv v /\ well_formed_type_value tyv /\
  id NOTIN FDOM env.var_types /\
  push_scope_with_var id tyv v st = (INL (),st') ==>
  runtime_storage_consistent (extend_local env id ty F) cx st'
Proof
  rpt strip_tac >>
  qpat_x_assum `push_scope_with_var _ _ _ _ = _` mp_tac >>
  simp[push_scope_with_var_def, return_def] >> strip_tac >> gvs[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `env_consistent env cx st` by gvs[runtime_consistent_def] >>
  `env.type_defs = get_tenv cx` by
    fs[env_consistent_def, env_context_consistent_def] >>
  `env_consistent (extend_local env id ty F) cx
     (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)))` by (
    irule push_scope_with_var_env_consistent >>
    metis_tac[]) >>
  `state_well_typed
     (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)))` by (
    gvs[runtime_storage_consistent_def, runtime_consistent_def,
        state_well_typed_def, scope_well_typed_def,
        finite_mapTheory.FLOOKUP_UPDATE]) >>
  `runtime_consistent (extend_local env id ty F) cx
     (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)))` by
    (simp[runtime_consistent_def] >> metis_tac[runtime_consistent_def]) >>
  `contract_storage_well_formed cx st` by
    metis_tac[runtime_storage_consistent_storage] >>
  `contract_storage_well_formed cx
     (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)))` by (
    irule contract_storage_well_formed_storage_frame >>
    qexists_tac `st` >> simp[] >>
    gen_tac >> Cases_on `b` >>
    simp[vyperStorageBackendTheory.get_storage_def]) >>
  metis_tac[runtime_storage_consistent_intro,
            runtime_storage_consistent_layout]
QED


Resume eval_all_storage_preservation_mutual[For_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ (_::_) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       push_scope_with_var_def, return_def] >>
  qmatch_goalsub_abbrev_tac `finally loop_body pop_scope stp` >>
  Cases_on `finally loop_body pop_scope stp` >>
  rename1 `finally loop_body pop_scope stp = (loop_res, st_after)` >>
  strip_tac >>
  `stp =
    st with scopes updated_by
      CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))` by
    simp[Abbr`stp`] >>
  `stp.scopes <> []` by simp[Abbr`stp`] >>
  qunabbrev_tac `loop_body` >>
  rewrite_tac[ignore_bind_def] >>
  drule for_body_decompose_storage >>
  disch_then (qspecl_then [`st_after`, `loop_res`, `cx`, `body'`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  `push_scope_with_var id tyv v st = (INL (),stp)` by
    simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
  `well_formed_type_value tyv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  `value_has_type tyv v` by fs[] >>
  `runtime_storage_consistent (extend_local env id ty F) cx stp` by (
    irule push_scope_with_var_preserves_runtime_storage_consistent >>
    conj_tac >- (qpat_assum `id NOTIN FDOM env.var_types` ACCEPT_TAC) >>
    qexistsl_tac [`st`, `tyv`, `v`] >>
    rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!s'' x t. push_scope_with_var id tyv v s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `stp`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qspecl_then [`extend_local env id ty F`, `ret_ty`, `env_after`,
                           `stp`, `res_body`, `st_body`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  `contract_storage_well_formed cx st_after` by (
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    irule contract_storage_well_formed_storage_frame >>
    qexists_tac `st_body` >> simp[] >>
    gen_tac >> Cases_on `b` >>
    simp[vyperStorageBackendTheory.get_storage_def]) >>
  `eval_for cx tyv id body' [v] st =
     ((case loop_res of INL broke => INL () | INR e => INR e), st_after)` by (
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         push_scope_with_var_def, return_def, Abbr`stp`] >>
    qpat_assum `finally _ _ stp = (loop_res,st_after)`
      (fn th => rewrite_tac[th]) >>
    Cases_on `loop_res` >>
    simp[Once evaluate_def, return_def]) >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st_after` by (
    irule eval_for_preserves_runtime_consistent >>
    conj_tac >- (qpat_assum `functions_well_typed cx` ACCEPT_TAC) >>
    qexistsl_tac [`body'`, `env_after`, `id`,
      `case loop_res of INL broke => INL () | INR e => INR e`,
      `ret_ty`, `st`, `ty`, `tyv`, `[v]`] >>
    conj_tac >- (qpat_assum `id NOTIN FDOM env.var_types` ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `evaluate_type env.type_defs ty = SOME tyv` ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `type_stmts _ _ _ = SOME env_after` ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `eval_for cx tyv id body' [v] st = _` ACCEPT_TAC) >>
    conj_tac >- simp[] >>
    conj_tac >- (qpat_assum `call_evaluation_safe cx (int_calls_stmts body')` ACCEPT_TAC) >>
    qpat_assum `runtime_consistent env cx st` ACCEPT_TAC) >>
  `runtime_storage_consistent env cx st_after` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `loop_res`
  >- (Cases_on `x`
      >- (`st' = st_after` by (
            qpat_x_assum `(case (INL T,st_after) of _ => _ | _ => _) = (res,st')` mp_tac >>
            simp[return_def]) >>
          qpat_x_assum `st' = st_after` SUBST_ALL_TAC >>
          qpat_assum `contract_storage_well_formed cx st_after` ACCEPT_TAC)
      >- (
        `eval_for cx tyv id body' vs st_after = (res,st')` by (
          qpat_x_assum `(case (INL F,st_after) of _ => _ | _ => _) = (res,st')` mp_tac >>
          simp[return_def]) >>
        qpat_x_assum `!s'' x t s''' broke t'. _`
          (qspecl_then [`st`, `()`, `stp`, `stp`, `F`, `st_after`] mp_tac) >>
        impl_tac >- (
          conj_tac >- (qpat_assum `push_scope_with_var id tyv v st = (INL (),stp)` ACCEPT_TAC) >>
          conj_tac >- (rewrite_tac[ignore_bind_def] >> first_assum ACCEPT_TAC) >>
          simp[]) >>
        disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                                 `st_after`, `res`, `st'`] mp_tac) >>
        impl_tac >- (
          conj_tac >- (qpat_assum `evaluate_type env.type_defs ty = SOME tyv` ACCEPT_TAC) >>
          conj_tac >- fs[] >>
          conj_tac >- (qpat_assum `id NOTIN FDOM env.var_types` ACCEPT_TAC) >>
          conj_tac >- (qpat_assum `type_stmts _ _ _ = SOME env_after` ACCEPT_TAC) >>
          conj_tac >- (qpat_assum `runtime_storage_consistent env cx st_after` ACCEPT_TAC) >>
          conj_tac >- (qpat_assum `functions_well_typed cx` ACCEPT_TAC) >>
          conj_tac >- (qpat_assum `call_evaluation_safe cx (int_calls_stmts body')` ACCEPT_TAC) >>
          conj_tac >- (qpat_assum `protected_storage_calls_preserve cx` ACCEPT_TAC) >>
          qpat_assum `eval_for cx tyv id body' vs st_after = (res,st')` ACCEPT_TAC) >>
        simp[]))
  >- (`st' = st_after` by (
        qpat_x_assum `(case (INR y,st_after) of _ => _ | _ => _) = (res,st')` mp_tac >>
        simp[]) >>
      qpat_x_assum `st' = st_after` SUBST_ALL_TAC >>
      qpat_assum `contract_storage_well_formed cx st_after` ACCEPT_TAC)
QED


Theorem expr_subscript_tail_state[local]:
  (do
     arr_tv <- lift_option_type arr_opt msg;
     check_array_bounds cx base_tv idx;
     sub_res <- lift_sum (evaluate_subscript (get_tenv cx) arr_tv base_tv idx);
     case sub_res of
       INL v => return v
     | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
   od st = (res,st')) ==>
  st' = st
Proof
  rpt strip_tac >>
  qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = _` mp_tac >>
  simp[bind_def, ignore_bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, ignore_bind_def]) >>
  imp_res_tac check_array_bounds_state >>
  imp_res_tac read_storage_slot_state >>
  gvs[]
QED

Theorem eval_expr_place_preserves_runtime_consistent[local]:
  type_place_expr env e = SOME vt /\ runtime_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  eval_expr cx e st = (res,st') ==>
  runtime_consistent env cx st'
Proof
  simp[runtime_consistent_def] >> rpt strip_tac >>
  drule_all (cj 8 eval_all_type_sound_mutual) >> simp[]
QED

Resume eval_all_storage_preservation_mutual[Expr_Subscript]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v8 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v8 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_right]) >>
  conj_tac
  >- (strip_tac >>
      `well_typed_expr env e' /\
       (well_typed_expr env e \/ ?base_vt. type_place_expr env e = SOME base_vt)` by (
        qpat_x_assum `well_typed_expr env (Subscript v8 e e')` mp_tac >>
        simp_tac(srw_ss())[Once well_typed_expr_def] >> metis_tac[]) >>
      qpat_x_assum `eval_expr cx (Subscript v8 e e') st = (res,st')` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_expr cx e st` >>
      rename1 `eval_expr cx e st = (base_res,st1)` >>
      first_x_assum drule_all >> strip_tac >>
      `contract_storage_well_formed cx st1` by metis_tac[] >>
      `runtime_consistent env cx st` by
        metis_tac[runtime_storage_consistent_runtime] >>
      `runtime_consistent env cx st1` by
        metis_tac[eval_expr_preserves_runtime_consistent,
                  eval_expr_place_preserves_runtime_consistent] >>
      `runtime_storage_consistent env cx st1` by
        metis_tac[runtime_storage_consistent_intro,
                  runtime_storage_consistent_layout] >>
      Cases_on `base_res` >> gvs[return_def, raise_def] >>
      TRY (rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
          Cases_on `eval_expr cx e' st1` >>
          rename1 `eval_expr cx e' st1 = (index_res,st2)` >>
          first_x_assum drule_all >> strip_tac >>
          `contract_storage_well_formed cx st2` by metis_tac[] >>
          `runtime_consistent env cx st2` by
            metis_tac[eval_expr_preserves_runtime_consistent] >>
          `runtime_storage_consistent env cx st2` by
            metis_tac[runtime_storage_consistent_intro,
                      runtime_storage_consistent_layout] >>
          Cases_on `index_res` >> gvs[return_def, raise_def] >>
          Cases_on `get_Value x st2` >>
          rename1 `get_Value x st2 = (value_res,st3)` >>
          `st3 = st2` by metis_tac[get_Value_state] >>
          gvs[] >>
          Cases_on `value_res` >> gvs[return_def, raise_def] >>
          metis_tac[expr_subscript_tail_state]) >>
      (strip_tac >> gvs[])) >>
  gen_tac >> strip_tac >>
  `well_typed_expr env e' /\ ?base_vt. type_place_expr env e = SOME base_vt` by (
    qpat_x_assum `type_place_expr env (Subscript v8 e e') = SOME vt` mp_tac >>
    simp_tac(srw_ss())[Once well_typed_expr_def, AllCaseEqs()] >> metis_tac[]) >>
  qpat_x_assum `eval_expr cx (Subscript v8 e e') st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  `contract_storage_well_formed cx st1` by metis_tac[] >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  `runtime_consistent env cx st1` by
    metis_tac[eval_expr_place_preserves_runtime_consistent] >>
  `runtime_storage_consistent env cx st1` by
    metis_tac[runtime_storage_consistent_intro,
              runtime_storage_consistent_layout] >>
  Cases_on `base_res` >> gvs[return_def, raise_def] >>
  TRY (rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
      Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (index_res,st2)` >>
      first_x_assum drule_all >> strip_tac >>
      `contract_storage_well_formed cx st2` by metis_tac[] >>
      `runtime_consistent env cx st2` by
        metis_tac[eval_expr_preserves_runtime_consistent] >>
      `runtime_storage_consistent env cx st2` by
        metis_tac[runtime_storage_consistent_intro,
                  runtime_storage_consistent_layout] >>
      Cases_on `index_res` >> gvs[return_def, raise_def] >>
      Cases_on `get_Value x st2` >>
      rename1 `get_Value x st2 = (value_res,st3)` >>
      `st3 = st2` by metis_tac[get_Value_state] >>
      gvs[] >>
      Cases_on `value_res` >> gvs[return_def, raise_def] >>
      metis_tac[expr_subscript_tail_state]) >>
  (strip_tac >> gvs[])
QED


Theorem extcall_return_tail_preserves_contract_storage[local]:
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  protected_storage_calls_preserve cx /\
  well_typed_opt env drv /\
  (returnData = [] /\ IS_SOME drv ==>
    call_evaluation_safe cx (int_calls_expr (THE drv))) /\
  (returnData = [] /\ IS_SOME drv ==>
    !env0 st0 res0 st0'.
      runtime_storage_consistent env0 cx st0 /\
      functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr (THE drv)) /\
      protected_storage_calls_preserve cx /\
      eval_expr cx (THE drv) st0 = (res0,st0') ==>
      (well_typed_expr env0 (THE drv) ==>
       contract_storage_well_formed cx st0') /\
      (!vt. type_place_expr env0 (THE drv) = SOME vt ==>
       contract_storage_well_formed cx st0')) /\
  (if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
   else do
     ret_val <- lift_sum_runtime
       (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
     return (Value ret_val)
   od) st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `returnData = [] /\ IS_SOME drv` >> gvs[]
  >- (Cases_on `drv` >> gvs[Once well_typed_expr_def] >>
      first_x_assum drule_all >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `(do _ od) st = (res,st')` mp_tac >>
  simp[lift_sum_runtime_def, bind_def, return_def, raise_def] >>
  Cases_on `evaluate_abi_decode_return (get_tenv cx) ret_type returnData` >>
  gvs[return_def, raise_def] >>
  metis_tac[runtime_storage_consistent_storage]
QED

Resume eval_all_storage_preservation_mutual[Expr_Call_ExtCall]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (strip_tac >>
      `call_evaluation_safe cx (int_calls_exprs es)` by (
        qpat_assum `call_evaluation_safe cx
          (int_calls_expr (Call v14 (ExtCall is_static' (func_name,arg_types,ret_type)) es drv))`
          mp_tac >> pure_rewrite_tac[int_calls_expr_def] >> strip_tac >>
        irule call_evaluation_safe_append_left >>
        qexists_tac `int_calls_opt drv` >> simp[]) >>
      qpat_x_assum `well_typed_expr env
        (Call v14 (ExtCall is_static' (func_name,arg_types,ret_type)) es drv)` mp_tac >>
      rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
      Cases_on `eval_exprs cx es st` >>
      rename1 `eval_exprs cx es st = (args_res,args_st)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `args_res`
      >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
          `exprs_runtime_typed env es vs` by (
            irule eval_exprs_success_runtime_typed >> simp[] >>
            metis_tac[runtime_storage_consistent_runtime]) >>
          `runtime_consistent env cx args_st` by
            metis_tac[eval_exprs_preserves_runtime_consistent,
                      runtime_storage_consistent_runtime] >>
          `runtime_storage_consistent env cx args_st` by
            metis_tac[runtime_storage_consistent_intro,
                      runtime_storage_consistent_layout] >>
          Cases_on `is_static'`
          >- (qpat_x_assum
                `if T then MAP expr_type es = BaseT AddressT::arg_types else _`
                mp_tac >> simp[] >> strip_tac >>
              drule_all extcall_static_args_runtime_typed_dest >> strip_tac >>
              `vs <> []` by
                (drule_all extcall_static_args_runtime_typed_nonempty >> simp[]) >>
              `get_tenv cx = env.type_defs` by
                metis_tac[env_consistent_get_tenv, runtime_consistent_def] >>
              drule_all extcall_static_args_runtime_typed_tail >> strip_tac >>
              `?calldata.
                 build_ext_calldata env.type_defs func_name arg_types (TL vs) =
                   SOME calldata` by
                (drule_all build_ext_calldata_typed >> simp[]) >>
              pop_assum strip_assume_tac >>
              qpat_x_assum `eval_expr cx (Call _ (ExtCall T _) _ _) st = (res,st')`
                mp_tac >>
              simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                check_def, type_check_def, assert_def, return_def, raise_def,
                lift_option_type_def, lift_option_def, get_accounts_def,
                get_transient_storage_def, update_accounts_def, update_transient_def] >>
              qpat_assum `eval_exprs cx es st = (INL vs,args_st)`
                (fn th => rewrite_tac[th]) >>
              simp[return_def] >>
              qpat_assum `dest_AddressV (HD vs) = SOME target_addr`
                (fn th => rewrite_tac[th]) >>
              qpat_assum `get_tenv cx = env.type_defs` (fn th => rewrite_tac[th]) >>
              qpat_assum `build_ext_calldata env.type_defs _ _ _ = SOME calldata`
                (fn th => rewrite_tac[th]) >>
              rewrite_tac[return_def, raise_def] >>
              Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >>
              rewrite_tac[return_def, raise_def]
              >- (strip_tac >>
                  qpat_x_assum `_ args_st = (res,st')` mp_tac >>
                  simp[assert_def, bind_def, return_def, raise_def,
                       get_accounts_def, get_transient_storage_def] >>
                  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
                  metis_tac[runtime_storage_consistent_storage]) >>
              simp_tac(srw_ss())[return_def, get_accounts_def, assert_def,
                                 get_transient_storage_def, raise_def, bind_def] >>
              asm_rewrite_tac[] >> simp_tac(srw_ss())[] >>
              Cases_on `run_ext_call cx.txn.target target_addr calldata NONE
                args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >>
              rewrite_tac[return_def, raise_def]
              >- (simp[raise_def] >> strip_tac >> gvs[] >>
                  metis_tac[runtime_storage_consistent_storage]) >>
              rename1 `SOME result` >> PairCases_on `result` >>
              simp_tac(srw_ss())[assert_def, bind_def, return_def] >>
              reverse (Cases_on `result0`) >> simp_tac(srw_ss())[]
              >- (strip_tac >> gvs[] >>
                  metis_tac[runtime_storage_consistent_storage]) >>
              simp_tac(srw_ss())[update_accounts_def, update_transient_def,
                                 return_def] >>
              qmatch_abbrev_tac `GG` >>
              first_x_assum drule >>
              simp[type_check_def, check_def, assert_def, raise_def, return_def,
                   lift_option_type_def, lift_option_def, get_accounts_def,
                   get_transient_storage_def, update_accounts_def,
                   update_transient_def] >>
              disch_then drule >>
              disch_then (qspec_then `args_st` mp_tac) >>
              simp[raise_def, return_def] >> strip_tac >>
              unabbrev_all_tac >>
              `accounts_well_typed args_st.accounts` by
                metis_tac[runtime_consistent_def] >>
              `accounts_well_typed result2` by (
                drule_all run_ext_call_accounts_well_typed >> simp[]) >>
              `contract_storage_well_formed cx
                 (args_st with <| accounts := result2; tStorage := result3 |>)` by
                metis_tac[protected_storage_calls_preserve_run_ext_call,
                          runtime_storage_consistent_storage] >>
              `runtime_consistent env cx
                 (args_st with <| accounts := result2; tStorage := result3 |>)` by
                metis_tac[update_accounts_transient_runtime_consistent] >>
              `runtime_storage_consistent env cx
                 (args_st with <| accounts := result2; tStorage := result3 |>)` by
                metis_tac[runtime_storage_consistent_intro,
                          runtime_storage_consistent_layout] >>
              `runtime_consistent env cx
                 ((args_st with <|accounts := result2; tStorage := result3|>) with
                    logs := args_st.logs ++ result4)` by (
                qspecl_then [`env`, `cx`,
                  `args_st with <|accounts := result2; tStorage := result3|>`,
                  `result4`] mp_tac runtime_consistent_logs_append >>
                simp[]) >>
              `contract_storage_well_formed cx
                 ((args_st with <|accounts := result2; tStorage := result3|>) with
                    logs := args_st.logs ++ result4)` by
                metis_tac[contract_storage_well_formed_logs] >>
              `runtime_storage_consistent env cx
                 ((args_st with <|accounts := result2; tStorage := result3|>) with
                    logs := args_st.logs ++ result4)` by
                metis_tac[runtime_storage_consistent_intro,
                          runtime_storage_consistent_layout] >>
              Cases_on `result1 = [] /\ IS_SOME drv` >> gvs[]
              >- (Cases_on `drv` >> gvs[Once well_typed_expr_def] >> strip_tac >>
                  `call_evaluation_safe cx (int_calls_expr x)` by (
                    qpat_assum `call_evaluation_safe cx
                      (int_calls_expr (Call _ (ExtCall T _) es (SOME x)))` mp_tac >>
                    pure_rewrite_tac[int_calls_expr_def] >>
                    metis_tac[call_evaluation_safe_append_right]) >>
                  qpat_x_assum `!s0 t0 env' st'' res' st'''. _`
                    (qspecl_then
                      [`args_st with <|accounts := result2; tStorage := result3|>`,
                       `(args_st with <|accounts := result2; tStorage := result3|>) with
                          logs := args_st.logs ++ result4`,
                       `env`,
                       `(args_st with <|accounts := result2; tStorage := result3|>) with
                          logs := args_st.logs ++ result4`,
                       `res`, `st'`] mp_tac) >>
                  simp[append_logs_def, return_def] >>
                  qpat_x_assum `_ = (res,st')` mp_tac >>
                  simp[append_logs_def, return_def] >>
                  metis_tac[]) >>
              strip_tac >> Cases_on `drv` >> gvs[] >>
              qpat_x_assum `(do _ od) _ = (res,st')` mp_tac >>
              simp[lift_sum_runtime_def, bind_def, return_def, raise_def] >>
              qmatch_goalsub_rename_tac
                `evaluate_abi_decode_return env.type_defs decode_ty result1` >>
              Cases_on
                `evaluate_abi_decode_return env.type_defs decode_ty result1` >>
              gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
              qpat_x_assum `_ = (res,st')` mp_tac >>
              simp[append_logs_def, return_def] >>
              metis_tac[runtime_storage_consistent_storage]) >>
          qpat_x_assum
            `if F then _ else MAP expr_type es =
              BaseT AddressT::BaseT (UintT 256)::arg_types`
            mp_tac >> simp[] >> strip_tac >>
          drule_all extcall_nonstatic_args_runtime_typed_dest >> strip_tac >>
          `vs <> [] /\ TL vs <> []` by
            (drule_all extcall_nonstatic_args_runtime_typed_nonempty >> simp[]) >>
          `get_tenv cx = env.type_defs` by
            metis_tac[env_consistent_get_tenv, runtime_consistent_def] >>
          drule_all extcall_nonstatic_args_runtime_typed_tail >> strip_tac >>
          `?calldata.
             build_ext_calldata env.type_defs func_name arg_types (TL (TL vs)) =
               SOME calldata` by
            (drule_all build_ext_calldata_typed >> simp[]) >>
          pop_assum strip_assume_tac >>
          qpat_x_assum `eval_expr cx (Call _ (ExtCall F _) _ _) st = (res,st')`
            mp_tac >>
          simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
            check_def, type_check_def, assert_def, return_def, raise_def,
            lift_option_type_def, lift_option_def, get_accounts_def,
            get_transient_storage_def, update_accounts_def, update_transient_def] >>
          qpat_assum `eval_exprs cx es st = (INL vs,args_st)`
            (fn th => rewrite_tac[th]) >>
          simp_tac(srw_ss())[] >> asm_rewrite_tac[] >>
          simp_tac(srw_ss()++boolSimps.LET_ss)[return_def] >>
          qpat_assum `get_tenv cx = env.type_defs` (fn th => rewrite_tac[th]) >>
          qpat_assum `build_ext_calldata env.type_defs _ _ _ = SOME calldata`
            (fn th => rewrite_tac[th]) >>
          rewrite_tac[return_def, raise_def] >>
          Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >>
          rewrite_tac[return_def, raise_def]
          >- (qpat_x_assum `!s'' vs t. _` kall_tac >> strip_tac >>
              gvs[assert_def, bind_def, return_def, raise_def,
                  get_accounts_def, get_transient_storage_def] >>
              metis_tac[runtime_storage_consistent_storage]) >>
          simp_tac(srw_ss())[return_def, get_accounts_def, assert_def,
                             get_transient_storage_def, raise_def, bind_def] >>
          asm_rewrite_tac[] >> simp_tac(srw_ss())[] >>
          Cases_on `run_ext_call cx.txn.target target_addr calldata (SOME amount)
            args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >>
          rewrite_tac[return_def, raise_def]
          >- (simp[raise_def] >> strip_tac >> gvs[] >>
              metis_tac[runtime_storage_consistent_storage]) >>
          rename1 `SOME result` >> PairCases_on `result` >>
          simp_tac(srw_ss())[assert_def, bind_def, return_def] >>
          reverse (Cases_on `result0`) >> simp_tac(srw_ss())[]
          >- (strip_tac >> gvs[] >>
              metis_tac[runtime_storage_consistent_storage]) >>
          simp_tac(srw_ss())[update_accounts_def, update_transient_def,
                             return_def] >>
          `!s0 err.
             (do
                assert T err;
                v <- return amount;
                return (SOME v, TL (TL vs))
              od) s0 = (INL (SOME amount, TL (TL vs)), s0)` by
            (rpt gen_tac >> EVAL_TAC) >>
          `!s0 err.
             (case build_ext_calldata env.type_defs func_name arg_types
                     (TL (TL vs)) of
                NONE => raise err
              | SOME v => return v) s0 = (INL calldata, s0)` by (
            rpt gen_tac >>
            qpat_assum
              `build_ext_calldata env.type_defs func_name arg_types
                 (TL (TL vs)) = SOME calldata`
              (fn th => rewrite_tac[th]) >>
            simp[return_def]) >>
          qmatch_abbrev_tac `GG` >>
          first_x_assum drule >>
          simp[type_check_def, check_def, assert_def, raise_def, return_def,
               lift_option_type_def, lift_option_def, get_accounts_def,
               get_transient_storage_def, update_accounts_def,
               update_transient_def] >>
          strip_tac >>
          `(result1 = [] /\ IS_SOME drv) ==>
           !env0 st0 res0 st0'.
             runtime_storage_consistent env0 cx st0 /\
             call_evaluation_safe cx (int_calls_expr (THE drv)) /\
             eval_expr cx (THE drv) st0 = (res0,st0') ==>
             (well_typed_expr env0 (THE drv) ==>
              contract_storage_well_formed cx st0') /\
             (!vt. type_place_expr env0 (THE drv) = SOME vt ==>
              contract_storage_well_formed cx st0')` by (
            rpt strip_tac >>
            qpat_x_assum `!s' value_opt arg_vals. _`
              (qspecl_then
                [`args_st`, `SOME amount`, `TL (TL vs)`, `args_st`,
                 `args_st`, `calldata`, `args_st`, `args_st`, `args_st`,
                 `args_st`, `args_st`, `result2`, `result3`, `result4`,
                 `args_st with <|accounts := result2; tStorage := result3|>`,
                 `(args_st with <|accounts := result2; tStorage := result3|>) with
                    logs := args_st.logs ++ result4`,
                 `env0`, `st0`, `res0`, `st0'`] mp_tac) >>
            simp[assert_def, bind_def, return_def, raise_def, append_logs_def] >>
            (impl_tac >- EVAL_TAC) >> strip_tac >> metis_tac[]) >>
          qpat_x_assum `!s' value_opt arg_vals. _` kall_tac >>
          unabbrev_all_tac >>
          `accounts_well_typed args_st.accounts` by
            metis_tac[runtime_consistent_def] >>
          `accounts_well_typed result2` by (
            drule_all run_ext_call_accounts_well_typed >> simp[]) >>
          `contract_storage_well_formed cx
             (args_st with <| accounts := result2; tStorage := result3 |>)` by
            metis_tac[protected_storage_calls_preserve_run_ext_call,
                      runtime_storage_consistent_storage] >>
          `runtime_consistent env cx
             (args_st with <| accounts := result2; tStorage := result3 |>)` by
            metis_tac[update_accounts_transient_runtime_consistent] >>
          `runtime_storage_consistent env cx
             (args_st with <| accounts := result2; tStorage := result3 |>)` by
            metis_tac[runtime_storage_consistent_intro,
                      runtime_storage_consistent_layout] >>
          `runtime_consistent env cx
             ((args_st with <|accounts := result2; tStorage := result3|>) with
                logs := args_st.logs ++ result4)` by (
            qspecl_then [`env`, `cx`,
              `args_st with <|accounts := result2; tStorage := result3|>`,
              `result4`] mp_tac runtime_consistent_logs_append >>
            simp[]) >>
          `contract_storage_well_formed cx
             ((args_st with <|accounts := result2; tStorage := result3|>) with
                logs := args_st.logs ++ result4)` by
            metis_tac[contract_storage_well_formed_logs] >>
          `runtime_storage_consistent env cx
             ((args_st with <|accounts := result2; tStorage := result3|>) with
                logs := args_st.logs ++ result4)` by
            metis_tac[runtime_storage_consistent_intro,
                      runtime_storage_consistent_layout] >>
          Cases_on `result1 = [] /\ IS_SOME drv` >> gvs[]
          >- (Cases_on `drv` >> gvs[Once well_typed_expr_def] >> strip_tac >>
              `call_evaluation_safe cx (int_calls_expr x)` by (
                qpat_assum `call_evaluation_safe cx
                  (int_calls_expr (Call _ (ExtCall F _) es (SOME x)))` mp_tac >>
                pure_rewrite_tac[int_calls_expr_def] >>
                metis_tac[call_evaluation_safe_append_right]) >>
              qpat_x_assum `!env0 st0 res0 st0'. _`
                (qspecl_then
                  [`env`,
                   `(args_st with <|accounts := result2; tStorage := result3|>) with
                      logs := args_st.logs ++ result4`,
                   `res`, `st'`] mp_tac) >>
              simp[append_logs_def, return_def] >>
              qpat_x_assum `_ = (res,st')` mp_tac >>
              simp[append_logs_def, return_def] >>
              metis_tac[]) >>
          strip_tac >> Cases_on `drv` >> gvs[] >>
          qpat_x_assum `(do _ od) _ = (res,st')` mp_tac >>
          simp[lift_sum_runtime_def, bind_def, return_def, raise_def] >>
          qmatch_goalsub_rename_tac
            `evaluate_abi_decode_return env.type_defs decode_ty result1` >>
          Cases_on
            `evaluate_abi_decode_return env.type_defs decode_ty result1` >>
          gvs[return_def, raise_def] >> strip_tac >> gvs[] >>
          qpat_x_assum `_ = (res,st')` mp_tac >>
          simp[append_logs_def, return_def] >>
          metis_tac[runtime_storage_consistent_storage]) >>
      qpat_x_assum `!s'' vs t. _` kall_tac >>
      gvs[] >>
      drule eval_extcall_args_error >> strip_tac >>
      first_x_assum
        (qspecl_then [`ret_type`, `is_static'`, `func_name`, `arg_types`, `drv`]
          assume_tac) >>
      gvs[] >> metis_tac[runtime_storage_consistent_storage]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Theorem lift_option_type_INL_eq_storage[local]:
  lift_option_type opt msg st = (INL v,st') <=> opt = SOME v /\ st' = st
Proof
  Cases_on `opt` >> simp[lift_option_type_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem fn_sigs_consistent_FLOOKUP_storage[local]:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src_id_opt,fn) = SOME sig ==>
  ?ts fm nr params dflts body.
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (fm,nr,params,dflts,sig.ret_ty,body) /\
    sig.param_types = MAP SND params /\
    sig.num_defaults = LENGTH dflts
Proof
  simp[fn_sigs_consistent_def]
QED

Theorem intcall_call_evaluation_safe_args_storage[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall callee) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `int_calls_expr (Call loc (IntCall callee) es extra)` >>
  simp[int_calls_expr_def]
QED

Theorem intcall_call_evaluation_safe_needed_defaults_storage[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,fn_body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS (src_id_opt,fn))
    (int_calls_exprs (DROP n dflts))
Proof
  rpt strip_tac >> gvs[int_calls_expr_def] >>
  irule call_evaluation_safe_push_needed_defaults >>
  conj_tac
  >- (qexistsl_tac [`args`, `fn_body`, `fn`, `mut`, `nr`, `ret`,
                    `src_id_opt`, `ts`] >> simp[]) >>
  qexists_tac `int_calls_exprs es` >> simp[int_calls_expr_def]
QED

Theorem intcall_call_evaluation_safe_body_storage[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (mut,nr,args,dflts,ret,fn_body) ==>
  call_evaluation_safe
    (cx with stk updated_by CONS (src_id_opt,fn))
    (int_calls_stmts fn_body)
Proof
  rpt strip_tac >> gvs[int_calls_expr_def] >>
  irule call_evaluation_safe_push_body >>
  conj_tac
  >- (qexistsl_tac [`args`, `dflts`, `fn`, `mut`, `nr`, `ret`,
                    `src_id_opt`, `ts`] >> simp[]) >>
  qexists_tac `int_calls_exprs es` >> simp[int_calls_expr_def]
QED

Theorem contract_storage_well_formed_stk[local]:
  contract_storage_well_formed (cx with stk updated_by f) st <=>
  contract_storage_well_formed cx st
Proof
  `st with scopes := st.scopes = st` by
    gvs[evaluation_state_component_equality] >>
  mp_tac (Q.INST [`scopes` |-> `st.scopes`]
    contract_storage_well_formed_stk_scopes) >>
  asm_rewrite_tac[]
QED


Theorem protected_storage_calls_preserve_stk[local]:
  protected_storage_calls_preserve (cx with stk updated_by f) <=>
  protected_storage_calls_preserve cx
Proof
  simp[protected_storage_calls_preserve_def,
       contract_storage_well_formed_stk]
QED


Theorem intcall_defaults_runtime_storage_consistent[local]:
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  env_body.current_src = src_id_opt /\
  env_body.type_defs = get_tenv cx /\
  env_body.fn_sigs = env.fn_sigs /\
  env_body.bare_globals = env.bare_globals /\
  env_body.bare_global_assignable = env.bare_global_assignable /\
  env_body.toplevel_vtypes = env.toplevel_vtypes /\
  env_body.flag_members = env.flag_members ==>
  runtime_storage_consistent (defaults_env env_body)
    (cx with stk updated_by CONS (src_id_opt,fn))
    (st with scopes := [FEMPTY]) /\
  functions_well_typed (cx with stk updated_by CONS (src_id_opt,fn))
Proof
  rpt strip_tac >>
  `runtime_consistent env cx st` by
    metis_tac[runtime_storage_consistent_runtime] >>
  qpat_assum `runtime_consistent env cx st` (fn th =>
    map_every assume_tac
      (CONJUNCTS (REWRITE_RULE [runtime_consistent_def] th))) >>
  qspecl_then [`env`, `env_body`, `cx`, `st`, `src_id_opt`, `fn`] mp_tac
    intcall_default_env_side_conditions >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `env_consistent (defaults_env env_body)
     (cx with stk updated_by CONS (src_id_opt,fn))
     (st with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  `state_well_typed (st with scopes := [FEMPTY])` by
    gvs[state_well_typed_def, scope_well_typed_def] >>
  `contract_storage_well_formed cx st` by
    qpat_assum `runtime_storage_consistent env cx st` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th)) >>
  `contract_storage_well_formed
     (cx with stk updated_by CONS (src_id_opt,fn))
     (st with scopes := [FEMPTY])` by
    simp[contract_storage_well_formed_stk_scopes] >>
  `storage_layout_safe cx` by
    qpat_assum `runtime_storage_consistent env cx st` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_layout th)) >>
  `storage_layout_safe (cx with stk updated_by CONS (src_id_opt,fn))` by
    simp[] >>
  simp[runtime_storage_consistent_def, runtime_consistent_def]
QED



Theorem type_place_expr_Call_IntCall_NONE_storage[local]:
  !env ty src_id_opt fn es drv.
    type_place_expr env (Call ty (IntCall (src_id_opt,fn)) es drv) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_all_storage_preservation_mutual[Expr_Call_IntCall]:
  rpt gen_tac >> strip_tac >> all_tac >>
  reverse conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` mp_tac >>
    simp[type_place_expr_Call_IntCall_NONE_storage]) >>
  strip_tac >>
  qpat_x_assum
    `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5.
        _ ==>
        !env0 st0 res0 st0'.
          well_typed_exprs env0 es /\
          runtime_storage_consistent env0 cx st0 /\
          functions_well_typed cx /\
          call_evaluation_safe cx (int_calls_exprs es) /\
          protected_storage_calls_preserve cx /\
          eval_exprs cx es st0 = (res0,st0') ==> _`
    (mk_asm "actual_ih") >>
  qpat_x_assum
    `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 es0 cx0 s7 prev0 t7 s8 x8 t8.
        _ ==>
        !env0 st0 res0 st0'.
          well_typed_exprs env0 es0 /\
          runtime_storage_consistent env0 cx0 st0 /\
          functions_well_typed cx0 /\
          call_evaluation_safe cx0 (int_calls_exprs es0) /\
          protected_storage_calls_preserve cx0 /\
          eval_exprs cx0 es0 st0 = (res0,st0') ==> _`
    (mk_asm "default_ih") >>
  qpat_x_assum
    `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
        _ ==>
        !env1 ret_ty1 env2 st0 res0 st0'.
          type_stmts env1 ret_ty1 body0 = SOME env2 /\
          runtime_storage_consistent env1 cx0 st0 /\
          functions_well_typed cx0 /\
          call_evaluation_safe cx0 (int_calls_stmts body0) /\
          protected_storage_calls_preserve cx0 /\
          eval_stmts cx0 body0 st0 = (res0,st0') ==> _`
    (mk_asm "body_ih") >>
  suspend "intcall_storage"
QED

Resume eval_all_storage_preservation_mutual[intcall_storage]:
  qhdtm_assum `call_evaluation_safe` (mk_asm "call_safe") >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    asm "call_safe" (fn th =>
      ACCEPT_TAC (MATCH_MP intcall_call_evaluation_safe_args_storage th)) >>
  qpat_assum `runtime_storage_consistent env cx st` (fn th => (
    assume_tac (MATCH_MP runtime_storage_consistent_runtime th);
    mk_asm "wf0" (MATCH_MP runtime_storage_consistent_storage th);
    mk_asm "runtime0"
      (MATCH_MP runtime_storage_consistent_runtime th))) >>
  qpat_x_assum `well_typed_expr env (Call _ (IntCall _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >>
  simp_tac(srw_ss())[bind_apply, ignore_bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[type_check_def, assert_def] >>
    qpat_assum `runtime_storage_consistent _ cx _` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th))) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[] >>
    qpat_assum `runtime_storage_consistent _ cx _` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th))) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[] >>
    qpat_assum `runtime_storage_consistent _ cx _` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th))) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[] >>
    qpat_assum `runtime_storage_consistent _ cx _` (fn th =>
      ACCEPT_TAC (MATCH_MP runtime_storage_consistent_storage th))) >>
  simp_tac(srw_ss())[bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `eval_exprs cx es r = (args_res,args_st)` >>
  asm_x "actual_ih" mp_tac >> simp[] >>
  disch_then (qspecl_then
    [`r`, `r`, `r`, `x'`, `r`, `r`, `x''`, `r''`, `r`, `r`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `args_res` >> gvs[]
  >- (
    rename1 `eval_exprs cx es r = (INL actual_vs,args_st)` >>
    qpat_assum
      `lift_option_type (get_module_code cx src_id_opt)
         "IntCall get_module_code" r = (INL x',r)`
      (fn th => mp_tac (MATCH_MP (iffLR lift_option_type_INL_eq_storage) th)) >>
    strip_tac >>
    qpat_assum
      `lift_option_type (lookup_callable_function cx.in_deploy fn x')
         "IntCall lookup_function" r = (INL x'',r)`
      (fn th => mp_tac (MATCH_MP (iffLR lift_option_type_INL_eq_storage) th)) >>
    strip_tac >>
    PairCases_on `x''` >> gvs[] >>
    qpat_assum `get_module_code cx src_id_opt = SOME x'`
      (mk_asm "module_ok") >>
    qpat_assum `lookup_callable_function cx.in_deploy fn x' =
                  SOME (x''0,x''1,x''2,x''3,x''4,x''5)`
      (mk_asm "lookup_ok") >>
    `runtime_consistent env cx args_st` by (
      irule eval_exprs_preserves_runtime_consistent >> simp[] >>
      qexistsl_tac [`es`, `INL actual_vs`, `r`] >> simp[] >>
      asm "runtime0" ACCEPT_TAC) >>
    `env_consistent env cx args_st` by
      qpat_assum `runtime_consistent env cx args_st` (fn th =>
        ACCEPT_TAC (cj 1 (REWRITE_RULE [runtime_consistent_def] th))) >>
    mp_tac (Q.INST [`st` |-> `args_st`, `ts` |-> `x'`,
                    `fm` |-> `x''0`, `nr` |-> `x''1`,
                    `args` |-> `x''2`, `dflts` |-> `x''3`,
                    `ret` |-> `x''4`, `fn_body` |-> `x''5`]
             callable_body_typing_from_env_consistent) >>
    simp[] >>
    disch_then (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `env_body` (qx_choose_then `ret_tv`
        (qx_choose_then `env_after`
          (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
    qpat_x_assum `!id typ. MEM (id,typ) x''2 ==> _`
      (mk_asm "args_forward") >>
    qpat_x_assum `!n ty. FLOOKUP env_body.var_types n = SOME ty ==> _`
      (mk_asm "args_var_types") >>
    qpat_x_assum `!n b. FLOOKUP env_body.var_assignable n = SOME b ==> _`
      (mk_asm "args_var_assignable") >>
    `env.type_defs = get_tenv cx` by (
      qpat_x_assum `env_consistent env cx args_st` mp_tac >>
      simp[env_consistent_def, env_context_consistent_def]) >>
    `sig.param_types = MAP SND x''2 /\ sig.num_defaults = LENGTH x''3` by (
      `fn_sigs_consistent env.fn_sigs cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      drule_all fn_sigs_consistent_FLOOKUP_storage >> strip_tac >> gvs[]) >>
    `storage_layout_safe cx` by
      qpat_assum `runtime_storage_consistent env cx r` (fn th =>
        ACCEPT_TAC (MATCH_MP runtime_storage_consistent_layout th)) >>
    `runtime_storage_consistent env cx args_st` by
      simp[runtime_storage_consistent_def] >>
    asm "call_safe" (fn call_th =>
      asm "module_ok" (fn module_th =>
        asm "lookup_ok" (fn lookup_th =>
          assume_tac (Q.INST
            [`n` |-> `LENGTH x''3 - (LENGTH x''2 - LENGTH es)`]
            (MATCH_MP intcall_call_evaluation_safe_needed_defaults_storage
              (LIST_CONJ [call_th,module_th,lookup_th])))))) >>
    asm "call_safe" (fn call_th =>
      asm "module_ok" (fn module_th =>
        asm "lookup_ok" (fn lookup_th =>
          assume_tac (MATCH_MP intcall_call_evaluation_safe_body_storage
            (LIST_CONJ [call_th,module_th,lookup_th]))))) >>
    simp[get_scopes_def, return_def] >>
    BasicProvers.TOP_CASE_TAC >>
    qmatch_asmsub_rename_tac
      `finally _ _ args_st = (default_res,default_st)` >>
    asm_x "default_ih" mp_tac >>
    simp[get_scopes_def, set_scopes_def, return_def] >> strip_tac >>
    first_x_assum (qspecl_then
      [`r`, `r`, `r`, `r`, `r`, `actual_vs`, `args_st`] mp_tac) >>
    simp[] >> strip_tac >>
    `well_typed_exprs (defaults_env env_body)
       (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)` by
      (irule well_typed_exprs_DROP >> first_assum ACCEPT_TAC) >>
    `runtime_storage_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (src_id_opt,fn))
       (args_st with scopes := [FEMPTY]) /\
     functions_well_typed
       (cx with stk updated_by CONS (src_id_opt,fn))` by
      (irule (Q.INST [`env` |-> `env`, `cx` |-> `cx`,
                      `st` |-> `args_st`, `env_body` |-> `env_body`,
                      `src_id_opt` |-> `src_id_opt`, `fn` |-> `fn`]
               intcall_defaults_runtime_storage_consistent) >>
       simp[] >> qexists_tac `env` >> simp[]) >>
    `protected_storage_calls_preserve
       (cx with stk updated_by CONS (src_id_opt,fn))` by
      simp[protected_storage_calls_preserve_stk] >>
    `!r1 s1.
       eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
         (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)
         (args_st with scopes := [FEMPTY]) = (r1,s1) ==>
       contract_storage_well_formed cx s1` by (
      rpt strip_tac >>
      qpat_assum `!env' st0 res0 st0'. _`
        (qspecl_then
          [`defaults_env env_body`, `args_st with scopes := [FEMPTY]`,
           `r1`, `s1`] mp_tac) >>
      simp[contract_storage_well_formed_stk]) >>
    `contract_storage_well_formed cx default_st` by (
      qpat_assum `contract_storage_well_formed cx args_st` (fn wf_th =>
        qpat_assum `!r1 s1. eval_exprs _ _ _ = (r1,s1) ==> _`
          (fn step_th =>
            qpat_assum `finally _ _ args_st = (default_res,default_st)`
              (fn fin_th =>
                ACCEPT_TAC (MATCH_MP
                  default_eval_exprs_finally_preserves_contract_storage_well_formed
                  (LIST_CONJ [wf_th,step_th,fin_th])))))) >>
    reverse (Cases_on `default_res`) >- (rpt strip_tac >> gvs[]) >>
    rename1 `_ = (INL dflt_vs,default_st)` >>
    gvs[] >> strip_tac >>
    drule default_eval_exprs_finally_success >> strip_tac >>
    `exprs_runtime_typed env es actual_vs` by (
      mp_tac (Q.INST [`env` |-> `env`, `es` |-> `es`, `cx` |-> `cx`,
                      `st` |-> `r`, `vs` |-> `actual_vs`,
                      `st'` |-> `args_st`]
        eval_exprs_success_runtime_typed) >>
      simp[] >> disch_then irule >> asm "runtime0" ACCEPT_TAC) >>
    `runtime_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (args_st with scopes := [FEMPTY])` by
      first_assum (fn th =>
        ACCEPT_TAC (MATCH_MP runtime_storage_consistent_runtime th)) >>
    `exprs_runtime_typed (defaults_env env_body)
       (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3)
       dflt_vs` by (
      drule eval_exprs_success_runtime_typed_from_eval >> simp[]) >>
    Cases_on
      `bind_arguments (get_tenv cx) x''2 (actual_vs ++ dflt_vs)` >>
    gvs[Excl "evaluate_type_def", lift_option_type_def, bind_apply,
        return_def, raise_def] >>
    `LENGTH x''2 - LENGTH es <= LENGTH x''3 /\ LENGTH es <= LENGTH x''2` by (
      qpat_x_assum `type_check _ "IntCall args length" r = _` mp_tac >>
      simp[type_check_def, assert_def] >>
      IF_CASES_TAC >> gvs[] >> decide_tac) >>
    qspecl_then
      [`cx`, `env`, `env_body`, `x''2`, `x''3`, `es`, `actual_vs`,
       `dflt_vs`, `DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3`,
       `pre`]
      mp_tac intcall_bind_arguments_from_runtime_typed >>
    (impl_tac >- (
      rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
       asm "args_forward" ACCEPT_TAC ORELSE
       asm "args_var_types" ACCEPT_TAC ORELSE
       asm "args_var_assignable" ACCEPT_TAC ORELSE
       (asm "args_var_assignable" mp_tac >> simp[]) ORELSE
       simp[env_consistent_def, env_context_consistent_def]))) >>
    disch_then (qx_choose_then `call_env` strip_assume_tac) >>
    qpat_assum `bind_arguments (get_tenv cx) x''2
                    (actual_vs ++ dflt_vs) = SOME call_env`
      (mk_asm "bind_call_env") >>
    `call_env = x` by (
      asm "bind_call_env" mp_tac >>
      qpat_x_assum `bind_arguments (get_tenv cx) x''2
                       (actual_vs ++ dflt_vs) = SOME x` mp_tac >>
      simp[]) >>
    gvs[] >>
    `!lock_res lock_st.
       (if x''1 then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
              (x''0 = View \/ x''0 = Pure)
        else return ()) (pre with scopes := args_st.scopes) = (lock_res,lock_st) ==>
       contract_storage_well_formed cx lock_st` by (
      rpt strip_tac >>
      Cases_on `x''1` >> gvs[return_def, raise_def] >>
      Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
      drule_all acquire_nonreentrant_lock_preserves_contract_storage_well_formed >>
      simp[]) >>
    Cases_on
      `(if x''1 then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
              (x''0 = View \/ x''0 = Pure)
        else return ()) (pre with scopes := args_st.scopes)` >>
    rename1 `_ (pre with scopes := args_st.scopes) = (lock_res,lock_st)` >>
    `contract_storage_well_formed cx lock_st` by (
      qpat_assum `!lock_res lock_st. _`
        (qspecl_then [`lock_res`, `lock_st`] irule) >>
      simp[]) >>
    Cases_on `lock_res` >>
    gvs[ignore_bind_apply, bind_apply, return_def, raise_def] >>
    `runtime_consistent (defaults_env env_body)
       (cx with stk updated_by CONS (env_body.current_src,fn)) pre` by (
      drule eval_exprs_preserves_runtime_consistent_from_eval >> simp[]) >>
    `lock_st.scopes = args_st.scopes /\
     lock_st.immutables = pre.immutables /\
     lock_st.accounts = pre.accounts` by (
      drule intcall_lock_state_preserves_runtime_frame_storage >>
      simp[]) >>
    `env_immutables_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (pre with scopes := args_st.scopes)` by (
      irule env_immutables_consistent_defaults_scopes_storage >>
      irule runtime_consistent_env_immutables_storage >>
      qpat_assum
        `runtime_consistent (defaults_env env_body) _ pre` ACCEPT_TAC) >>
    `env_scopes_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (pre with scopes := [call_env])` by (
      qpat_assum
        `env_scopes_consistent env_body cx (pre with scopes := [call_env])`
        mp_tac >>
      simp[env_scopes_consistent_stk_irrelevant_storage]) >>
    `state_well_typed pre /\ accounts_well_typed pre.accounts` by (
      qpat_assum
        `runtime_consistent (defaults_env env_body) _ pre` (fn th =>
          ACCEPT_TAC (MATCH_MP runtime_consistent_state_accounts_storage th))) >>
    `EVERY scope_well_typed args_st.scopes` by (
      qpat_assum `runtime_consistent env cx args_st` (fn th =>
        ACCEPT_TAC (MATCH_MP runtime_consistent_scopes_well_typed_storage th))) >>
    `state_well_typed (pre with scopes := args_st.scopes) /\
     accounts_well_typed (pre with scopes := args_st.scopes).accounts` by (
      irule state_accounts_scopes_storage >> simp[]) >>
    `env_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (lock_st with scopes := [call_env]) /\
     state_well_typed (lock_st with scopes := [call_env]) /\
     accounts_well_typed (lock_st with scopes := [call_env]).accounts` by (
      qspecl_then
        [`env`, `env_body`, `cx`, `args_st`,
         `pre with scopes := args_st.scopes`, `lock_st`, `call_env`,
         `fn`, `x''1`, `x''0 = View \/ x''0 = Pure`]
        mp_tac intcall_live_pushed_body_preconditions >>
      (impl_tac >- simp[]) >> simp[]) >>
    `context_well_typed
       (cx with stk updated_by CONS (env_body.current_src,fn))` by (
      qpat_assum
        `runtime_consistent (defaults_env env_body) _ pre` (fn th =>
          ACCEPT_TAC (MATCH_MP runtime_consistent_context_storage th))) >>
    `runtime_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (lock_st with scopes := [call_env])` by (
      simp[runtime_consistent_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
    Cases_on
      `push_function (env_body.current_src,fn) call_env cx lock_st` >>
    rename1 `_ lock_st = (push_res,push_st)` >>
    Cases_on `push_res` >>
    gvs[ignore_bind_apply, bind_apply, push_function_def,
        return_def, raise_def] >>
    `runtime_storage_consistent env_body
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (lock_st with scopes := [call_env])` by
      simp[runtime_storage_consistent_def,
           contract_storage_well_formed_stk_scopes] >>
    asm_x "body_ih" mp_tac >> simp[] >> strip_tac >>
    `!body_res body_st.
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn))
         x''5 (lock_st with scopes := [call_env]) = (body_res,body_st) ==>
       contract_storage_well_formed cx body_st` by (
      rpt strip_tac >>
      qpat_x_assum `!s'' t s5 t3 s6 vs t4 s7 prev t5 s8 dvals t6
                       s9 callenv t7 s11 t9 s12 pushed t10. _`
        (qspecl_then
          [`r`, `r`, `r`, `r`, `r`, `actual_vs`, `args_st`, `args_st`,
           `args_st.scopes`, `args_st`, `args_st`, `dflt_vs`,
           `pre with scopes := args_st.scopes`,
           `pre with scopes := args_st.scopes`, `call_env`,
           `pre with scopes := args_st.scopes`,
           `pre with scopes := args_st.scopes`, `lock_st`, `lock_st`,
           `cx with stk updated_by CONS (env_body.current_src,fn)`,
           `lock_st with scopes := [call_env]`] mp_tac) >>
      simp[get_scopes_def, lift_option_type_def, push_function_def,
           return_def] >> strip_tac >>
      qpat_x_assum `!env' ret_ty env'' bst bres bst'. _` drule_all >>
      simp[contract_storage_well_formed_stk]) >>
    (qpat_assum `_ = (res,st')` (mk_asm "suffix_eq") >>
     qmatch_asmsub_abbrev_tac `safe_cast actual_rtv _` >>
     qspecl_then
       [`cx`, `cx with stk updated_by CONS (env_body.current_src,fn)`, `x''5`,
        `lock_st with scopes := [call_env]`, `args_st.scopes`, `x''1`,
        `x''0 = View \/ x''0 = Pure`, `actual_rtv`, `res`, `st'`]
       mp_tac
       intcall_post_push_expanded_suffix_preserves_contract_storage_well_formed >>
     (impl_tac >-
       (conj_tac >-
          (irule contract_storage_well_formed_scopes >>
           first_assum ACCEPT_TAC) >>
        conj_tac >- first_assum ACCEPT_TAC >>
        conj_tac >- first_assum ACCEPT_TAC >>
        asm "suffix_eq" mp_tac >> simp[])) >>
     simp[])) >>
  strip_tac >> gvs[] >> first_assum ACCEPT_TAC
QED


Finalise eval_all_storage_preservation_mutual

Theorem eval_stmt_preserves_contract_storage_well_formed:
  type_stmt env ret_ty s = SOME env' /\
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmt s) /\
  protected_storage_calls_preserve cx /\
  eval_stmt cx s st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[cj 1 eval_all_storage_preservation_mutual]
QED

Theorem eval_stmts_preserves_contract_storage_well_formed:
  type_stmts env ret_ty ss = SOME env' /\
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_stmts ss) /\
  protected_storage_calls_preserve cx /\
  eval_stmts cx ss st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[cj 2 eval_all_storage_preservation_mutual]
QED

Theorem eval_expr_preserves_contract_storage_well_formed:
  well_typed_expr env e /\
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_expr e) /\
  protected_storage_calls_preserve cx /\
  eval_expr cx e st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[cj 8 eval_all_storage_preservation_mutual]
QED

Theorem eval_exprs_preserves_contract_storage_well_formed:
  well_typed_exprs env es /\
  runtime_storage_consistent env cx st /\
  functions_well_typed cx /\
  call_evaluation_safe cx (int_calls_exprs es) /\
  protected_storage_calls_preserve cx /\
  eval_exprs cx es st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[cj 9 eval_all_storage_preservation_mutual]
QED
