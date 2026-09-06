(*
 * Typed storage preservation for assign_target and assign_targets.
 *
 * The transparent contract-storage invariant covers ordinary declarations and
 * resolved hashmap regions on both persistent and transient backends.  Layout
 * safety supplies nonoverflow and separation for those regions and reserves the
 * nonreentrant transient lock slot.  Result-form preservation is intentional:
 * sequential tuple assignment, append, and pop may retain an earlier successful
 * write when a later operation returns an error.
 *
 * Whole-value writes reuse update_toplevel_name preservation.  ArrayRef and
 * HashMapRef branches use typed resolved-region writes, including nested paths,
 * dynamic-array length updates, append, and pop.  The combined
 * runtime_storage_consistent predicate adds storage decodability and layout
 * safety without changing runtime_consistent or state_well_typed.
 *
 * Constructor introduction requires explicit zero-read premises because
 * load_contract does not allocate fresh storage.  External-call preservation is
 * separately parameterized by protected_storage_calls_preserve, which constrains
 * every returned persistent/transient state for the protected caller.
 *)

Theory vyperTypeStoragePreservation
Ancestors
  vyperTypeStatePreservation vyperHashMapPreservation vyperStorageFrame
  vyperStorageLayoutSafety vyperStorageReadSoundness vyperState
  vyperStorageBackend
Libs
  wordsLib markerLib

(* Additive combined invariant: the established runtime invariant is unchanged,
   and storage decodability/layout safety are carried as explicit conjuncts. *)
Definition runtime_storage_consistent_def:
  runtime_storage_consistent env cx st <=>
    runtime_consistent env cx st /\
    contract_storage_well_formed cx st /\
    storage_layout_safe cx
End

Theorem runtime_storage_consistent_runtime:
  runtime_storage_consistent env cx st ==> runtime_consistent env cx st
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_storage:
  runtime_storage_consistent env cx st ==>
  contract_storage_well_formed cx st
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_layout:
  runtime_storage_consistent env cx st ==> storage_layout_safe cx
Proof
  simp[runtime_storage_consistent_def]
QED

Theorem runtime_storage_consistent_intro:
  runtime_consistent env cx st /\
  contract_storage_well_formed cx st /\
  storage_layout_safe cx ==>
  runtime_storage_consistent env cx st
Proof
  simp[runtime_storage_consistent_def]
QED

(* Scope updates are transparent to both protected storage backends. *)
Theorem set_scopes_storage_frame:
  set_scopes scopes st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rw[set_scopes_def, return_def] >>
  simp[get_storage_scopes]
QED

Theorem assign_target_scoped_storage_frame:
  assign_target cx (BaseTargetV (ScopedVar id) sbs) op st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_sum_def, type_check_def, assert_def,
       ignore_bind_def, set_scopes_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope (string_to_num id) st.scopes` >>
  simp[return_def, raise_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `assign_subscripts x2.type x2.value (REVERSE sbs) op` >>
  simp[return_def, raise_def] >>
  Cases_on `x2.assignable` >>
  simp[return_def, raise_def, bind_def, assert_def, set_scopes_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  simp[get_storage_scopes]
QED

Theorem assign_target_scoped_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  assign_target cx (BaseTargetV (ScopedVar id) sbs) op st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists `st` >> simp[] >>
  metis_tac[assign_target_scoped_storage_frame]
QED

(* Immutable-map updates change neither protected storage backend. *)
Theorem set_immutable_storage_frame:
  set_immutable cx src_id n tv v st = (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `set_immutable _ _ _ _ _ _ = _` mp_tac >>
  simp[set_immutable_def, bind_def, get_address_immutables_def,
       lift_option_type_def, set_address_immutables_def, return_def, raise_def,
       AllCaseEqs()] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  gvs[return_def, raise_def] >>
  rpt strip_tac >> gvs[] >> Cases_on `b` >> simp[get_storage_def]
QED

Theorem assign_target_immutable_storage_frame:
  assign_target cx (BaseTargetV (ImmutableVar src_id id) sbs) op st =
    (res,st') ==>
  !b. get_storage cx st' b = get_storage cx st b
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def, get_immutables_def,
       get_address_immutables_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  imp_res_tac set_immutable_storage_frame >>
  imp_res_tac assign_result_preserves_state >>
  gvs[]
QED

Theorem assign_target_immutable_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  assign_target cx (BaseTargetV (ImmutableVar src_id id) sbs) op st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  irule contract_storage_well_formed_storage_frame >>
  qexists `st` >> simp[] >>
  metis_tac[assign_target_immutable_storage_frame]
QED

(* A typed zero-width encoding cannot change either storage backend. *)
Theorem zero_slot_write_storage_frame:
  value_has_type tv v /\
  type_slot_size tv = 0 /\
  write_storage_slot cx b slot tv v st = (res,st') ==>
  !b'. get_storage cx st' b' = get_storage cx st b'
Proof
  rpt strip_tac >>
  drule (CONJUNCT1 vyperTypingTheory.value_has_type_equiv) >> strip_tac >>
  Cases_on `encode_value tv v` >> gvs[] >>
  `x = []` by
    (Cases_on `x` >> simp[] >>
     qpat_x_assum `encode_value _ _ = SOME _` mp_tac >>
     simp[] >> strip_tac >>
     drule (CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded) >>
     simp[] >> metis_tac[]) >>
  gvs[vyperStorageBackendTheory.write_storage_slot_eq,
      vyperStorageTheory.apply_writes_def] >>
  Cases_on `b = b'` >> gvs[]
  >- simp[vyperStorageBackendTheory.get_storage_after_set] >>
  simp[vyperStorageBackendTheory.get_storage_after_set_other]
QED

(* Whole-value TopLevelVar writes reach exactly the existing top-level update
   endpoint; all pre-write errors have the same second projection. *)
Theorem set_global_preserves_contract_storage_well_formed:
  contract_storage_well_formed cx st /\
  storage_layout_safe cx /\
  storable_value cx src id v /\
  var_in_storage cx src id /\
  set_global cx src (string_to_num id) v st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `st' = update_toplevel_name cx st src id v` by
    (simp[vyperLookupStorageTheory.update_toplevel_name_def] >>
     qpat_x_assum `set_global _ _ _ _ _ = _` (fn th => simp[th])) >>
  gvs[] >>
  irule vyperStorageWritePreservationTheory.update_toplevel_name_preserves_contract_storage_well_formed >>
  simp[]
QED

Theorem storage_var_info_lt_var_in_storage:
  storage_var_info cx mid n = SOME (b,off,tv) /\
  well_formed_type_value tv /\
  off < dimword(:256) ==>
  var_in_storage cx mid n
Proof
  simp[vyperLookupStorageTheory.storage_var_info_def,
       vyperLookupStorageTheory.var_in_storage_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED
Theorem set_global_typed_result_success:
  get_module_code cx src = SOME code /\
  find_var_decl_by_num n code = SOME (StorageVarDecl b typ,id) /\
  lookup_var_slot_from_layout cx b src id = SOME off /\
  evaluate_type (get_tenv cx) typ = SOME tv /\
  value_has_type tv v ==>
  ?st'. set_global cx src n v st = (INL (),st')
Proof
  rpt strip_tac >>
  drule (CONJUNCT1 vyperTypingTheory.value_has_type_equiv) >> strip_tac >>
  Cases_on `encode_value tv v` >> gvs[] >>
  qexists `set_storage cx st b
    (apply_writes (n2w off) x (get_storage cx st b))` >>
  simp[Once set_global_def, bind_def, lift_option_type_def, return_def, raise_def,
       vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()]
QED


Theorem assign_target_toplevel_value_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  target_runtime_typed env cx st tgt ty
    (BaseTargetV (TopLevelVar src id) sbs) /\
  assign_operation_runtime_typed env ty op /\
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  lookup_global cx src (string_to_num id) st = (INL (Value old_v),st) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st = (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  gvs[runtime_storage_consistent_def] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  qpat_x_assum `assign_target_assignable_context _ _ _` mp_tac >>
  simp[assign_target_assignable_context_def, assign_target_assignable_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  PairCases_on `p` >> gvs[] >>
  Cases_on `lookup_var_slot_from_layout cx v5 src p1` >> gvs[] >>
  `storage_var_info cx src id = SOME (v5,x'³',x')` by
    simp[vyperLookupStorageTheory.storage_var_info_def, AllCaseEqs()] >>
  `well_formed_type_value x'` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type x' old_v` by
    metis_tac[lookup_global_storage_Value_typed] >>
  `evaluate_type env.type_defs ty = SOME (leaf_type x' (REVERSE sbs))` by
    metis_tac[top_level_storage_value_leaf_evaluate_type] >>
  `value_has_type x' x''` by
    metis_tac[assign_subscripts_preserves_type_runtime_typed] >>
  `?sg. set_global cx src (string_to_num id) x'' st = (INL (),sg)` by
    metis_tac[set_global_typed_result_success] >>
  gvs[] >>
  `x'³' + type_slot_size x' <= dimword(:256)` by
    (qpat_x_assum `storage_layout_safe cx` mp_tac >>
     simp[storage_layout_safe_def,
          vyperLookupStorageTheory.well_formed_layout_def] >>
     metis_tac[]) >>
  Cases_on `x'³' < dimword(:256)`
  >- (qpat_x_assum `x'³' < dimword(:256)` mp_tac >> simp[] >> strip_tac >>
      `var_in_storage cx src id` by
        (rw[vyperLookupStorageTheory.var_in_storage_def] >> metis_tac[]) >>
      `storable_value cx src id x''` by
        simp[vyperLookupStorageTheory.storable_value_def,
             vyperLookupStorageTheory.storage_type_of_def] >>
      metis_tac[set_global_preserves_contract_storage_well_formed]) >>
  `type_slot_size x' = 0` by decide_tac >>
  `write_storage_slot cx v5 (n2w x'³') x' x'' st = (INL (),s'³')` by
    (qpat_x_assum `set_global _ _ _ _ _ = _` mp_tac >>
     simp[Once set_global_def, bind_def, lift_option_type_def, return_def,
          raise_def, AllCaseEqs()]) >>
  `!b'. get_storage cx s'³' b' = get_storage cx st b'` by
    metis_tac[zero_slot_write_storage_frame] >>
  irule contract_storage_well_formed_storage_frame >>
  qexists `st` >> simp[]
QED
Theorem lookup_global_ArrayRef_declared_region:
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot elem_tv bd),st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (StorageVarDecl b typ,decl_id) ==>
  declared_storage_region cx src id [] =
    SOME (b,root_slot,ArrayTV elem_tv bd)
Proof
  rpt strip_tac >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, declared_storage_region_def, bind_def,
       lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()])
QED

Theorem array_ref_ordinary_write_endpoint_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot elem_tv bd),st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (StorageVarDecl b typ,decl_id) /\
  evaluate_type (get_tenv cx) typ = SOME (ArrayTV elem_tv bd) /\
  resolve_array_element cx b root_slot (ArrayTV elem_tv bd) subs st =
    (INL (slot,final_tv,remaining),st_res) /\
  read_storage_slot cx b slot final_tv st_res = (INL current_v,st_res) /\
  assign_subscripts final_tv current_v remaining op = INL new_v /\
  evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) /\
  assign_operation_runtime_typed env ty op /\
  write_storage_slot cx b slot final_tv new_v st_res = (INL (),st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  imp_res_tac vyperStatePreservationTheory.resolve_array_element_state >> gvs[] >>
  `declared_storage_region cx src id [] =
     SOME (b,root_slot,ArrayTV elem_tv bd)` by
    metis_tac[lookup_global_ArrayRef_declared_region] >>
  `well_formed_type_value (ArrayTV elem_tv bd)` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `well_formed_type_value final_tv` by
    metis_tac[vyperStorageWritePreservationTheory.resolve_array_element_preserves_well_formed_type] >>
  `value_has_type final_tv current_v` by
    metis_tac[read_storage_slot_success_type] >>
  `value_has_type final_tv new_v` by
    metis_tac[assign_subscripts_preserves_type_runtime_typed] >>
  `w2n root_slot + type_slot_size (ArrayTV elem_tv bd) <= dimword(:256)` by
    metis_tac[runtime_storage_consistent_layout,
              storage_layout_safe_region_nonoverflow] >>
  `slots_in_range (get_storage cx st b) (w2n root_slot)
     (ArrayTV elem_tv bd)` by
    (gvs[runtime_storage_consistent_def] >>
     `get_storage_backend cx b st = (INL (get_storage cx st b),st)` by
       simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
     metis_tac[contract_storage_well_formed_region]) >>
  `slots_in_range (get_storage cx st' b) (w2n root_slot)
     (ArrayTV elem_tv bd)` by
    (irule vyperStorageWritePreservationTheory.resolve_array_element_typed_write_preserves_root_residual >>
     simp[] >>
     conj_tac >- (qexistsl [`get_tenv cx`, `typ`] >> simp[]) >>
     qexistsl [`final_tv`, `remaining`, `slot`, `st`, `st`, `subs`,
                `new_v`] >> simp[]) >>
  `w2n root_slot <= w2n slot /\
   w2n slot + type_slot_size final_tv <=
     w2n root_slot + type_slot_size (ArrayTV elem_tv bd)` by
    metis_tac[vyperStorageWritePreservationTheory.resolve_array_element_region_bounds] >>
  gvs[runtime_storage_consistent_def] >>
  irule vyperStorageWritePreservationTheory.contained_ordinary_write_preserves_contract_storage_well_formed >>
  conj_tac >- simp[] >>
  qexistsl [`b`, `src`, `id`, `root_slot`, `st`,
             `ArrayTV elem_tv bd`, `slot`, `final_tv`, `new_v`] >>
  simp[]
QED
Theorem array_ref_dynamic_append_final_endpoint_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (StorageVarDecl b typ,decl_id) /\
  evaluate_type (get_tenv cx) typ = SOME (ArrayTV root_elem_tv root_bd) /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd) subs st =
    (INL (slot,ArrayTV elem_tv (Dynamic max),[]),st) /\
  w2n (read_slot (get_storage cx st b) (w2n slot)) = len /\
  len < max /\
  0 < type_slot_size elem_tv /\
  value_has_type elem_tv v /\
  write_storage_slot cx b
    (n2w (w2n slot + 1 + len * type_slot_size elem_tv))
    elem_tv v st = (INL (),st1) /\
  write_storage_slot cx b slot (BaseTV (UintT 256))
    (IntV (&(len + 1))) st1 = (INL (),st2) ==>
  contract_storage_well_formed cx st2
Proof
  rpt strip_tac >>
  `declared_storage_region cx src id [] =
     SOME (b,root_slot,ArrayTV root_elem_tv root_bd)` by
    metis_tac[lookup_global_ArrayRef_declared_region] >>
  `well_formed_type_value (ArrayTV root_elem_tv root_bd)` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `well_formed_type_value (ArrayTV elem_tv (Dynamic max))` by
    metis_tac[vyperStorageWritePreservationTheory.resolve_array_element_preserves_well_formed_type] >>
  `w2n root_slot + type_slot_size (ArrayTV root_elem_tv root_bd) <=
     dimword(:256)` by
    metis_tac[runtime_storage_consistent_layout,
              storage_layout_safe_region_nonoverflow] >>
  `slots_in_range (get_storage cx st b) (w2n root_slot)
     (ArrayTV root_elem_tv root_bd)` by
    (`get_storage_backend cx b st = (INL (get_storage cx st b),st)` by
       simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
     metis_tac[runtime_storage_consistent_storage,
               contract_storage_well_formed_region]) >>
  `w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
     dimword(:256)` by
    metis_tac[vyperStorageWritePreservationTheory.resolve_array_element_region_bounds] >>
  `slots_in_range (get_storage cx st b) (w2n slot)
     (ArrayTV elem_tv (Dynamic max))` by
    (irule vyperStorageReadSoundnessTheory.resolve_array_element_current_region >>
     qexistsl [`root_slot`, `[]`, `st`, `subs`, `get_tenv cx`,
                `ArrayTV root_elem_tv root_bd`, `typ`] >> simp[]) >>
  `well_formed_type_value elem_tv /\ max < dimword(:256)` by
    gvs[vyperTypingTheory.well_formed_type_value_def] >>
  `w2n slot + 1 + len * type_slot_size elem_tv =
   w2n slot + (type_slot_size elem_tv * len + 1)` by
    (once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
  gvs[runtime_storage_consistent_def] >>
  irule vyperStorageWritePreservationTheory.resolve_array_element_dynamic_append_final_write_preserves_contract_storage_well_formed >>
  conj_tac >- simp[] >>
  qexistsl [`b`, `elem_tv`,
             `w2n (read_slot (get_storage cx st b) (w2n slot))`, `max`,
             `src`, `id`, `root_slot`, `slot`, `st`, `st1`, `st`, `subs`,
             `get_tenv cx`, `ArrayTV root_elem_tv root_bd`, `typ`, `v`] >>
  simp[]
QED
Theorem array_ref_dynamic_pop_final_endpoint_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (StorageVarDecl b typ,decl_id) /\
  evaluate_type (get_tenv cx) typ = SOME (ArrayTV root_elem_tv root_bd) /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd) subs st =
    (INL (slot,ArrayTV elem_tv (Dynamic max),[]),st) /\
  w2n (read_slot (get_storage cx st b) (w2n slot)) = len /\
  0 < len /\
  0 < type_slot_size elem_tv /\
  value_has_type elem_tv v /\
  write_storage_slot cx b
    (n2w (w2n slot + 1 + (len - 1) * type_slot_size elem_tv))
    elem_tv v st = (INL (),st1) /\
  write_storage_slot cx b slot (BaseTV (UintT 256))
    (IntV (&(len - 1))) st1 = (INL (),st2) ==>
  contract_storage_well_formed cx st2
Proof
  rpt strip_tac >>
  `declared_storage_region cx src id [] =
     SOME (b,root_slot,ArrayTV root_elem_tv root_bd)` by
    metis_tac[lookup_global_ArrayRef_declared_region] >>
  `well_formed_type_value (ArrayTV root_elem_tv root_bd)` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `well_formed_type_value (ArrayTV elem_tv (Dynamic max))` by
    metis_tac[vyperStorageWritePreservationTheory.resolve_array_element_preserves_well_formed_type] >>
  `w2n root_slot + type_slot_size (ArrayTV root_elem_tv root_bd) <=
     dimword(:256)` by
    metis_tac[runtime_storage_consistent_layout,
              storage_layout_safe_region_nonoverflow] >>
  `slots_in_range (get_storage cx st b) (w2n root_slot)
     (ArrayTV root_elem_tv root_bd)` by
    (`get_storage_backend cx b st = (INL (get_storage cx st b),st)` by
       simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
     metis_tac[runtime_storage_consistent_storage,
               contract_storage_well_formed_region]) >>
  `w2n slot + type_slot_size (ArrayTV elem_tv (Dynamic max)) <=
     dimword(:256)` by
    metis_tac[vyperStorageWritePreservationTheory.resolve_array_element_region_bounds] >>
  `slots_in_range (get_storage cx st b) (w2n slot)
     (ArrayTV elem_tv (Dynamic max))` by
    (irule vyperStorageReadSoundnessTheory.resolve_array_element_current_region >>
     qexistsl [`root_slot`, `[]`, `st`, `subs`, `get_tenv cx`,
                `ArrayTV root_elem_tv root_bd`, `typ`] >> simp[]) >>
  `well_formed_type_value elem_tv` by
    gvs[vyperTypingTheory.well_formed_type_value_def] >>
  `w2n slot + 1 + (len - 1) * type_slot_size elem_tv =
   w2n slot + (type_slot_size elem_tv * (len - 1) + 1)` by
    (once_rewrite_tac [arithmeticTheory.MULT_COMM] >> decide_tac) >>
  gvs[runtime_storage_consistent_def] >>
  irule vyperStorageWritePreservationTheory.resolve_array_element_dynamic_pop_final_write_preserves_contract_storage_well_formed >>
  conj_tac >- simp[] >>
  qexistsl [`b`, `elem_tv`,
             `w2n (read_slot (get_storage cx st b) (w2n slot))`, `max`,
             `src`, `id`, `root_slot`, `slot`, `st`, `st1`, `st`, `subs`,
             `get_tenv cx`, `ArrayTV root_elem_tv root_bd`, `typ`, `v`] >>
  simp[]
QED
Theorem assignable_context_ArrayRef_metadata:
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot elem_tv bd),st) ==>
  ?code typ decl_id.
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code =
      SOME (StorageVarDecl b typ,decl_id) /\
    evaluate_type (get_tenv cx) typ = SOME (ArrayTV elem_tv bd)
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target_assignable_context _ _ _` mp_tac >>
  simp[assign_target_assignable_context_def, assign_target_assignable_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  PairCases_on `p` >> gvs[] >>
  Cases_on `p0` >> gvs[]
  >- (qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
      simp[lookup_global_def, bind_def, lift_option_type_def, return_def,
           raise_def, AllCaseEqs()] >>
      rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()])) >>
  drule lookup_global_ArrayRef_not_HashMapVarDecl >>
  disch_then drule >> disch_then drule >> simp[]
QED

Theorem assignable_context_HashMapRef_metadata:
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  lookup_global cx src (string_to_num id) st =
    (INL (HashMapRef b root_slot kt vt),st) ==>
  ?code decl_id off.
    get_module_code cx src = SOME code /\
    find_var_decl_by_num (string_to_num id) code =
      SOME (HashMapVarDecl b kt vt,decl_id) /\
    lookup_var_slot_from_layout cx b src decl_id = SOME off /\
    root_slot = n2w off
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target_assignable_context _ _ _` mp_tac >>
  simp[assign_target_assignable_context_def, assign_target_assignable_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  PairCases_on `p` >> gvs[] >>
  Cases_on `p0` >> gvs[]
  >- (drule lookup_global_HashMapRef_not_StorageVarDecl >>
      disch_then drule >> disch_then drule >> simp[]) >>
  qpat_x_assum `lookup_global _ _ _ _ = _` mp_tac >>
  simp[lookup_global_def, bind_def, lift_option_type_def, return_def,
       raise_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED
Theorem assign_target_ArrayRef_dynamic_append_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (StorageVarDecl b typ,decl_id) /\
  evaluate_type (get_tenv cx) typ = SOME (ArrayTV root_elem_tv root_bd) /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st =
    (INL (slot,ArrayTV elem_tv (Dynamic max),[]),st) /\
  evaluate_type env.type_defs ty = SOME (ArrayTV elem_tv (Dynamic max)) /\
  assign_operation_runtime_typed env ty (AppendOp v) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) (AppendOp v) st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `0 < type_slot_size elem_tv` by
    metis_tac[vyperStorageWritePreservationTheory.evaluate_type_ArrayTV_inv] >>
  `value_has_type elem_tv v` by
    (drule vyperTypeStatePreservationTheory.assign_operation_leaf_type_append >>
     disch_then drule >> strip_tac >> gvs[]) >>
  `IS_SOME (encode_value elem_tv v)` by
    metis_tac[vyperTypingTheory.value_has_type_equiv] >>
  `IS_SOME (encode_value (BaseTV (UintT 256))
      (IntV (&(w2n (lookup_storage slot (get_storage cx st b)) + 1))))` by
    simp[vyperStorageTheory.encode_value_def,
         vyperStorageTheory.encode_base_to_slot_def] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def, check_def,
       assert_def, pairTheory.PAIR, AllCaseEqs(),
       vyperStorageBackendTheory.get_storage_backend_eq] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, assert_def,
                       AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  gvs[vyperStorageTheory.read_slot_def] >>
  FIRST
    [qpat_x_assum `encode_value elem_tv v = NONE` mp_tac >>
       gvs[vyperTypingTheory.value_has_type_equiv],
     (qpat_x_assum `write_storage_slot cx b _ elem_tv v _ = (INR _,_)` mp_tac >>
      simp[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()] >>
      strip_tac >> gvs[]),
     (qpat_x_assum `write_storage_slot cx b slot (BaseTV (UintT 256)) _ _ = (INR _,_)` mp_tac >>
      simp[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()] >>
      strip_tac >> gvs[]),
     (`slot + n2w (type_slot_size elem_tv *
          w2n (lookup_storage slot (get_storage cx st b)) + 1) =
        n2w (w2n slot +
          (type_slot_size elem_tv *
           w2n (lookup_storage slot (get_storage cx st b)) + 1))` by
        rewrite_tac[GSYM wordsTheory.word_add_n2w,
                    wordsTheory.n2w_w2n] >>
      `w2n slot +
          (type_slot_size elem_tv *
           w2n (lookup_storage slot (get_storage cx st b)) + 1) =
        w2n slot + 1 +
          w2n (lookup_storage slot (get_storage cx st b)) *
          type_slot_size elem_tv` by
        (once_rewrite_tac[arithmeticTheory.MULT_COMM] >> decide_tac) >>
      `write_storage_slot cx b
          (n2w (w2n slot + 1 +
             w2n (lookup_storage slot (get_storage cx st b)) *
             type_slot_size elem_tv)) elem_tv v st = (INL (),s'')` by
        metis_tac[] >>
      `w2n (read_slot (get_storage cx st b) (w2n slot)) =
       w2n (lookup_storage slot (get_storage cx st b))` by
        simp[vyperStorageTheory.read_slot_def] >>
      metis_tac[array_ref_dynamic_append_final_endpoint_preserves_contract_storage_well_formed]),
     gvs[runtime_storage_consistent_def]]
QED



Theorem assign_target_ArrayRef_dynamic_pop_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (StorageVarDecl b typ,decl_id) /\
  evaluate_type (get_tenv cx) typ = SOME (ArrayTV root_elem_tv root_bd) /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st =
    (INL (slot,ArrayTV elem_tv (Dynamic max),[]),st) /\
  evaluate_type env.type_defs ty = SOME (ArrayTV elem_tv (Dynamic max)) /\
  assign_operation_runtime_typed env ty PopOp /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) PopOp st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  `0 < type_slot_size elem_tv` by
    metis_tac[vyperStorageWritePreservationTheory.evaluate_type_ArrayTV_inv] >>
  `well_formed_type_value elem_tv` by
    (drule vyperStorageWritePreservationTheory.evaluate_type_ArrayTV_inv >>
     strip_tac >>
     metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]) >>
  `?elem_ty. evaluate_type env.type_defs elem_ty = SOME elem_tv` by
    metis_tac[vyperStorageWritePreservationTheory.evaluate_type_ArrayTV_inv] >>
  `value_has_type elem_tv (default_value elem_tv)` by
    metis_tac[vyperTypeDefaultsTheory.default_value_has_type_thm] >>
  `IS_SOME (encode_value elem_tv (default_value elem_tv))` by
    metis_tac[vyperTypingTheory.value_has_type_equiv] >>
  `IS_SOME (encode_value (BaseTV (UintT 256))
      (IntV (&(w2n (lookup_storage slot (get_storage cx st b)) - 1))))` by
    simp[vyperStorageTheory.encode_value_def,
         vyperStorageTheory.encode_base_to_slot_def] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def, check_def,
       assert_def, pairTheory.PAIR, AllCaseEqs(),
       vyperStorageBackendTheory.get_storage_backend_eq] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, check_def, assert_def,
                       AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.read_storage_slot_state >> gvs[] >>
  gvs[vyperStorageTheory.read_slot_def] >>
  FIRST
    [qpat_x_assum `encode_value elem_tv (default_value elem_tv) = NONE` mp_tac >>
       gvs[vyperTypingTheory.value_has_type_equiv],
     (qpat_x_assum `write_storage_slot cx b _ elem_tv (default_value elem_tv) _ = (INR _,_)` mp_tac >>
      simp[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()] >>
      strip_tac >> gvs[]),
     (qpat_x_assum `write_storage_slot cx b slot (BaseTV (UintT 256)) _ _ = (INR _,_)` mp_tac >>
      simp[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()] >>
      strip_tac >> gvs[]),
     (`slot + n2w (type_slot_size elem_tv *
          (w2n (lookup_storage slot (get_storage cx s'' b)) - 1) + 1) =
        n2w (w2n slot +
          (type_slot_size elem_tv *
           (w2n (lookup_storage slot (get_storage cx s'' b)) - 1) + 1))` by
        rewrite_tac[GSYM wordsTheory.word_add_n2w,
                    wordsTheory.n2w_w2n] >>
      `w2n slot +
          (type_slot_size elem_tv *
           (w2n (lookup_storage slot (get_storage cx s'' b)) - 1) + 1) =
        w2n slot + 1 +
          (w2n (lookup_storage slot (get_storage cx s'' b)) - 1) *
          type_slot_size elem_tv` by
        (once_rewrite_tac[arithmeticTheory.MULT_COMM] >> decide_tac) >>
      `write_storage_slot cx b
          (n2w (w2n slot + 1 +
             (w2n (lookup_storage slot (get_storage cx s'' b)) - 1) *
             type_slot_size elem_tv)) elem_tv (default_value elem_tv) s'' =
          (INL (),s'³')` by metis_tac[] >>
      `w2n (read_slot (get_storage cx s'' b) (w2n slot)) =
       w2n (lookup_storage slot (get_storage cx s'' b))` by
        simp[vyperStorageTheory.read_slot_def] >>
      `runtime_storage_consistent env cx s''` by
        simp[runtime_storage_consistent_def] >>
      irule array_ref_dynamic_pop_final_endpoint_preserves_contract_storage_well_formed >>
      qexistsl [`b`, `code`, `decl_id`, `elem_tv`, `env`, `id`,
                `w2n (lookup_storage slot (get_storage cx s'' b))`, `max`,
                `root_bd`, `root_elem_tv`, `root_slot`, `slot`, `src`, `s''`,
                `s'³'`, `REVERSE sbs`, `typ`, `default_value elem_tv`] >>
      simp[vyperStorageTheory.read_slot_def]),
     gvs[runtime_storage_consistent_def]]
QED





Theorem write_storage_slot_error_state[local]:
  write_storage_slot cx b slot tv v st = (INR e,st') ==> st' = st
Proof
  simp[vyperStorageBackendTheory.write_storage_slot_eq, AllCaseEqs()]
QED

Theorem assign_target_ArrayRef_replace_transition_cases:
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st = (INL (slot,final_tv,remaining),st) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) (Replace v) st =
    (res,st') ==>
  st' = st \/
  ?current_v new_v.
    read_storage_slot cx b slot final_tv st = (INL current_v,st) /\
    assign_subscripts final_tv current_v remaining (Replace v) = INL new_v /\
    write_storage_slot cx b slot final_tv new_v st = (INL (),st')
Proof
  rpt strip_tac >>
  Cases_on `final_tv` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.resolve_array_element_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.read_storage_slot_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  imp_res_tac write_storage_slot_error_state >> gvs[] >>
  qpat_x_assum `lift_sum _ _ = (INL _,_)` mp_tac >>
  simp[lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

Theorem assign_target_ArrayRef_update_transition_cases:
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st = (INL (slot,final_tv,remaining),st) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs)
    (Update upd_ty bop nv) st = (res,st') ==>
  st' = st \/
  ?current_v new_v.
    read_storage_slot cx b slot final_tv st = (INL current_v,st) /\
    assign_subscripts final_tv current_v remaining (Update upd_ty bop nv) =
      INL new_v /\
    write_storage_slot cx b slot final_tv new_v st = (INL (),st')
Proof
  rpt strip_tac >>
  Cases_on `final_tv` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.resolve_array_element_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.read_storage_slot_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  imp_res_tac write_storage_slot_error_state >> gvs[] >>
  qpat_x_assum `lift_sum _ _ = (INL _,_)` mp_tac >>
  simp[lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  metis_tac[]
QED



Theorem assign_target_ArrayRef_append_ordinary_transition_cases:
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st = (INL (slot,final_tv,remaining),st) /\
  ~(?et n. final_tv = ArrayTV et (Dynamic n)) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) (AppendOp v) st =
    (res,st') ==>
  st' = st \/
  ?current_v new_v.
    read_storage_slot cx b slot final_tv st = (INL current_v,st) /\
    assign_subscripts final_tv current_v remaining (AppendOp v) = INL new_v /\
    write_storage_slot cx b slot final_tv new_v st = (INL (),st')
Proof
  rpt strip_tac >>
  Cases_on `final_tv` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.resolve_array_element_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.read_storage_slot_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  imp_res_tac write_storage_slot_error_state >> gvs[] >>
  qpat_x_assum `lift_sum _ _ = (INL _,_)` mp_tac >>
  simp[lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  metis_tac[]
QED

(* Storage-aware read adapters carry the combined invariant directly. *)
Theorem assign_target_ArrayRef_pop_ordinary_transition_cases:
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st = (INL (slot,final_tv,remaining),st) /\
  ~(?et n. final_tv = ArrayTV et (Dynamic n)) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) PopOp st =
    (res,st') ==>
  st' = st \/
  ?current_v new_v.
    read_storage_slot cx b slot final_tv st = (INL current_v,st) /\
    assign_subscripts final_tv current_v remaining PopOp = INL new_v /\
    write_storage_slot cx b slot final_tv new_v st = (INL (),st')
Proof
  rpt strip_tac >>
  Cases_on `final_tv` >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.resolve_array_element_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.read_storage_slot_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  imp_res_tac write_storage_slot_error_state >> gvs[] >>
  qpat_x_assum `lift_sum _ _ = (INL _,_)` mp_tac >>
  simp[lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  metis_tac[]
QED
Theorem assign_target_ArrayRef_ordinary_transition_cases:
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  get_module_code cx src = SOME code /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st = (INL (slot,final_tv,remaining),st) /\
  ~(?v et n. op = AppendOp v /\ final_tv = ArrayTV et (Dynamic n)) /\
  ~(?et n. op = PopOp /\ final_tv = ArrayTV et (Dynamic n)) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st =
    (res,st') ==>
  st' = st \/
  ?current_v new_v.
    read_storage_slot cx b slot final_tv st = (INL current_v,st) /\
    assign_subscripts final_tv current_v remaining op = INL new_v /\
    write_storage_slot cx b slot final_tv new_v st = (INL (),st')
Proof
  rpt strip_tac >>
  Cases_on `op`
  >- metis_tac[assign_target_ArrayRef_replace_transition_cases]
  >- metis_tac[assign_target_ArrayRef_update_transition_cases]
  >- metis_tac[assign_target_ArrayRef_append_ordinary_transition_cases]
  >> metis_tac[assign_target_ArrayRef_pop_ordinary_transition_cases]
QED
Theorem assign_target_ArrayRef_ordinary_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st = (INL (slot,final_tv,remaining),st) /\
  evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining) /\
  assign_operation_runtime_typed env ty op /\
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  ~(?v et n. op = AppendOp v /\ final_tv = ArrayTV et (Dynamic n)) /\
  ~(?et n. op = PopOp /\ final_tv = ArrayTV et (Dynamic n)) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  imp_res_tac assignable_context_ArrayRef_metadata >>
  `st' = st \/
   ?current_v new_v.
     read_storage_slot cx b slot final_tv st = (INL current_v,st) /\
     assign_subscripts final_tv current_v remaining op = INL new_v /\
     write_storage_slot cx b slot final_tv new_v st = (INL (),st')` by
    metis_tac[assign_target_ArrayRef_ordinary_transition_cases] >>
  metis_tac[array_ref_ordinary_write_endpoint_preserves_contract_storage_well_formed,
            runtime_storage_consistent_def]
QED

Theorem assign_target_ArrayRef_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  target_runtime_typed env cx st tgt ty
    (BaseTargetV (TopLevelVar src id) sbs) /\
  assign_operation_runtime_typed env ty op /\
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  lookup_global cx src (string_to_num id) st =
    (INL (ArrayRef b root_slot root_elem_tv root_bd),st) /\
  resolve_array_element cx b root_slot (ArrayTV root_elem_tv root_bd)
    (REVERSE sbs) st = (INL (slot,final_tv,remaining),st) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  imp_res_tac assignable_context_ArrayRef_metadata >>
  `runtime_consistent env cx st` by
    gvs[runtime_storage_consistent_def] >>
  `evaluate_type env.type_defs ty =
     SOME (leaf_type (ArrayTV root_elem_tv root_bd) (REVERSE sbs))` by
    metis_tac[top_level_storage_value_leaf_evaluate_type] >>
  `leaf_type (ArrayTV root_elem_tv root_bd) (REVERSE sbs) =
     leaf_type final_tv remaining` by
    metis_tac[vyperStorageWritePreservationTheory.resolve_array_element_leaf_type] >>
  `evaluate_type env.type_defs ty = SOME (leaf_type final_tv remaining)` by
    metis_tac[] >>
  Cases_on `op`
  >- (drule assign_target_ArrayRef_ordinary_preserves_contract_storage_well_formed >>
      disch_then drule >> disch_then drule >> disch_then drule >>
      disch_then drule >> disch_then drule >>
      disch_then (qspecl_then [`st'`, `res`] irule) >> simp[])
  >- (drule assign_target_ArrayRef_ordinary_preserves_contract_storage_well_formed >>
      disch_then drule >> disch_then drule >> disch_then drule >>
      disch_then drule >> disch_then drule >>
      disch_then (qspecl_then [`st'`, `res`] irule) >> simp[])
  >- (Cases_on `?et n. final_tv = ArrayTV et (Dynamic n)`
      >- (pop_assum strip_assume_tac >>
          `remaining = []` by
            metis_tac[resolve_array_element_ArrayTV_empty_rsubs_sc] >>
          gvs[vyperTypingTheory.leaf_type_def] >>
          irule assign_target_ArrayRef_dynamic_append_preserves_contract_storage_well_formed >>
          simp[] >> metis_tac[])
      >> irule assign_target_ArrayRef_ordinary_preserves_contract_storage_well_formed >>
      simp[] >> metis_tac[])
  >> Cases_on `?et n. final_tv = ArrayTV et (Dynamic n)`
  >- (pop_assum strip_assume_tac >>
      `remaining = []` by
        metis_tac[resolve_array_element_ArrayTV_empty_rsubs_sc] >>
      gvs[vyperTypingTheory.leaf_type_def] >>
      irule assign_target_ArrayRef_dynamic_pop_preserves_contract_storage_well_formed >>
      simp[] >> metis_tac[])
  >> irule assign_target_ArrayRef_ordinary_preserves_contract_storage_well_formed >>
  simp[] >> metis_tac[]
QED



Theorem split_hashmap_subscripts_consumed_prefix[local]:
  !vt subs final_type kts remaining.
    split_hashmap_subscripts vt subs = SOME (final_type,kts,remaining) ==>
    split_hashmap_subscripts vt
      (TAKE (LENGTH subs - LENGTH remaining) subs) =
      SOME (final_type,kts,[])
Proof
  Induct_on `vt`
  >- simp[split_hashmap_subscripts_def] >>
  Cases_on `subs` >> simp[split_hashmap_subscripts_def] >>
  rpt gen_tac >>
  Cases_on `split_hashmap_subscripts vt t` >> simp[] >>
  PairCases_on `x` >> simp[] >> strip_tac >> gvs[] >>
  drule split_hashmap_subscripts_some_imp >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `LENGTH t - LENGTH remaining = LENGTH x1` by decide_tac >>
  `SUC (LENGTH t) - (LENGTH remaining + 1) = LENGTH x1` by decide_tac >>
  `TAKE (SUC (LENGTH t) - (LENGTH remaining + 1)) t =
   TAKE (LENGTH x1) t` by simp[] >>
  gvs[split_hashmap_subscripts_def]
QED

Theorem assign_target_HashMapRef_transition_cases:
  lookup_global cx src (string_to_num id) st =
    (INL (HashMapRef b root_slot kt vt),st) /\
  REVERSE sbs = first_sub :: rest_subs /\
  split_hashmap_subscripts vt rest_subs =
    SOME (final_type,kts,remaining) /\
  compute_hashmap_slot root_slot (kt::kts)
    (first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining) rest_subs) =
    SOME final_slot /\
  evaluate_type (get_tenv cx) final_type = SOME final_tv /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st =
    (res,st') ==>
  st' = st \/
  ?current_v new_v.
    read_storage_slot cx b final_slot final_tv st = (INL current_v,st) /\
    assign_subscripts final_tv current_v remaining op = INL new_v /\
    write_storage_slot cx b final_slot final_tv new_v st = (INL (),st')
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def, type_check_def,
       assert_def, check_def, pairTheory.PAIR, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def, bind_def, type_check_def,
                       assert_def, check_def, AllCaseEqs()]) >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.read_storage_slot_state >> gvs[] >>
  imp_res_tac vyperStatePreservationTheory.lift_sum_state >> gvs[] >>
  imp_res_tac assign_result_preserves_state >> gvs[] >>
  imp_res_tac write_storage_slot_error_state >> gvs[] >>
  qpat_x_assum `lift_sum _ _ = (INL _,_)` mp_tac >>
  simp[lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  CASE_TAC >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  metis_tac[]
QED


Theorem target_runtime_typed_HashMapRef_path[local]:
  runtime_consistent env cx st /\
  target_runtime_typed env cx st tgt ty
    (BaseTargetV (TopLevelVar src id) sbs) /\
  get_module_code cx src = SOME code /\
  find_var_decl_by_num (string_to_num id) code =
    SOME (HashMapVarDecl b kt vt,decl_id) ==>
  well_formed_vtype env.type_defs (HashMapT kt vt) /\
  target_path_type env (HashMapT kt vt) sbs (Type ty)
Proof
  rpt strip_tac >>
  Cases_on `tgt` >>
  gvs[vyperTypeExprSoundnessTheory.target_runtime_typed_def,
      vyperTypeExprSoundnessTheory.location_runtime_typed_def] >>
  `vt' = HashMapT kt vt` by
    (Cases_on `vt'`
     >- (metis_tac[top_level_Type_not_hashmap_decl])
     >- (drule_all top_level_HashMap_decl >> strip_tac >>
         gvs[optionTheory.SOME_11, pairTheory.PAIR_EQ, var_decl_info_11])) >>
  gvs[] >>
  metis_tac[top_level_vtype_well_formed]
QED

Theorem assign_target_HashMapRef_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  target_runtime_typed env cx st tgt ty
    (BaseTargetV (TopLevelVar src id) sbs) /\
  assignable_type env.type_defs ty /\
  assign_operation_runtime_typed env ty op /\
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  lookup_global cx src (string_to_num id) st =
    (INL (HashMapRef b root_slot kt vt),st) /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  imp_res_tac assignable_context_HashMapRef_metadata >>
  `runtime_consistent env cx st` by
    gvs[runtime_storage_consistent_def] >>
  `env.type_defs = get_tenv cx` by
    fs[vyperTypeExprSoundnessTheory.runtime_consistent_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >>
  `well_formed_vtype env.type_defs (HashMapT kt vt) /\
   target_path_type env (HashMapT kt vt) sbs (Type ty)` by
    metis_tac[target_runtime_typed_HashMapRef_path] >>
  `well_formed_vtype (get_tenv cx) (HashMapT kt vt)` by metis_tac[] >>
  drule_all target_path_type_HashMapT_assign_target_decomp >> strip_tac >>
  qpat_x_assum `first_sub = LAST sbs` SUBST_ALL_TAC >>
  qpat_x_assum `rest_subs = TL (REVERSE sbs)` SUBST_ALL_TAC >>
  `split_hashmap_subscripts vt
      (TAKE (LENGTH (TL (REVERSE sbs)) - LENGTH remaining)
            (TL (REVERSE sbs))) =
    SOME (final_type,kts,[])` by
    metis_tac[split_hashmap_subscripts_consumed_prefix] >>
  `assignable_type (get_tenv cx) ty` by metis_tac[] >>
  qspecl_then [`env`, `cx`, `st`, `kt`, `vt`, `sbs`, `ty`,
               `TL (REVERSE sbs)`, `final_type`, `kts`, `remaining`]
    mp_tac target_path_type_HashMapT_split_leaf_runtime >>
  impl_tac >- first_assum ACCEPT_TAC >>
  impl_tac >- first_assum ACCEPT_TAC >>
  impl_tac >- first_assum ACCEPT_TAC >>
  impl_tac >- simp[] >>
  impl_tac >- first_assum ACCEPT_TAC >>
  impl_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  `compute_hashmap_slot root_slot (kt::kts)
      (LAST sbs :: TAKE (LENGTH (TL (REVERSE sbs)) - LENGTH remaining)
                         (TL (REVERSE sbs))) <> NONE` by
    metis_tac[compute_hashmap_slot_prefix_some] >>
  (Cases_on `compute_hashmap_slot root_slot (kt::kts)
     (LAST sbs :: TAKE (LENGTH (TL (REVERSE sbs)) - LENGTH remaining)
                        (TL (REVERSE sbs)))`
   >- (gvs[])) >>
  rename1 `compute_hashmap_slot root_slot (kt::kts) _ = SOME final_slot` >>
  `st' = st \/
   ?current_v new_v.
     read_storage_slot cx b final_slot final_tv st = (INL current_v,st) /\
     assign_subscripts final_tv current_v remaining op = INL new_v /\
     write_storage_slot cx b final_slot final_tv new_v st = (INL (),st')` by
    (irule assign_target_HashMapRef_transition_cases >>
     qexistsl [`final_type`, `LAST sbs`, `id`, `kt`, `kts`, `res`,
               `TL (REVERSE sbs)`, `root_slot`, `sbs`, `src`, `vt`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum strip_assume_tac
  >- (gvs[runtime_storage_consistent_def]) >>
  `value_has_type final_tv current_v` by
    metis_tac[read_storage_slot_success_type] >>
  `value_has_type final_tv new_v` by
    metis_tac[assign_subscripts_preserves_type_runtime_typed] >>
  irule vyperStorageWritePreservationTheory.hashmapref_leaf_write_preserves_contract_storage_well_formed >>
  conj_tac >- gvs[runtime_storage_consistent_def] >>
  qexistsl [`b`, `code`, `final_slot`, `final_tv`, `final_type`, `LAST sbs`,
            `decl_id`, `kt`, `kts`, `src`, `id`, `off`,
            `TAKE (LENGTH sbs - (LENGTH remaining + 1)) (TL (REVERSE sbs))`,
            `st`, `new_v`, `vt`] >>
  gvs[runtime_storage_consistent_def]
QED

(* Constructor-free TopLevelVar boundary: lookup dispatch is the only remaining
   case split.  Each successful constructor is handled by its reviewed adapter;
   lookup failure propagates before any storage mutation. *)
Theorem assign_target_TopLevelVar_preserves_contract_storage_well_formed:
  runtime_storage_consistent env cx st /\
  target_runtime_typed env cx st tgt ty
    (BaseTargetV (TopLevelVar src id) sbs) /\
  assignable_type env.type_defs ty /\
  assign_operation_runtime_typed env ty op /\
  assign_target_assignable_context cx
    (BaseTargetV (TopLevelVar src id) sbs) st /\
  assign_target cx (BaseTargetV (TopLevelVar src id) sbs) op st =
    (res,st') ==>
  contract_storage_well_formed cx st'
Proof
  rpt strip_tac >>
  Cases_on `lookup_global cx src (string_to_num id) st` >>
  Cases_on `q` >>
  imp_res_tac vyperStatePreservationTheory.lookup_global_state >>
  pop_assum SUBST_ALL_TAC
  >- (Cases_on `x`
      >- metis_tac[vyperStatePreservationTheory.lookup_global_state,
                    assign_target_toplevel_value_preserves_contract_storage_well_formed]
      >- metis_tac[vyperStatePreservationTheory.lookup_global_state,
                    assign_target_HashMapRef_preserves_contract_storage_well_formed]
      >> (Cases_on `resolve_array_element cx b c (ArrayTV t b0)
            (REVERSE sbs) st` >>
          Cases_on `q` >>
          imp_res_tac vyperStatePreservationTheory.resolve_array_element_state >>
          pop_assum SUBST_ALL_TAC
          >- (PairCases_on `x` >>
              metis_tac[vyperStatePreservationTheory.lookup_global_state,
                        vyperStatePreservationTheory.resolve_array_element_state,
                        assign_target_ArrayRef_preserves_contract_storage_well_formed]) >>
          `lookup_global cx src (string_to_num id) st =
             (INL (ArrayRef b c t b0),st)` by
            metis_tac[vyperStatePreservationTheory.lookup_global_state] >>
          `resolve_array_element cx b c (ArrayTV t b0) (REVERSE sbs) st =
             (INR y,st)` by
            metis_tac[vyperStatePreservationTheory.resolve_array_element_state] >>
          imp_res_tac assignable_context_ArrayRef_metadata >>
          qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
          simp[Once assign_target_def, bind_def, ignore_bind_def, return_def,
               raise_def, LET_THM, pairTheory.PAIR] >>
          strip_tac >> gvs[runtime_storage_consistent_def])) >>
  imp_res_tac vyperStatePreservationTheory.lookup_global_state >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, return_def, LET_THM,
       pairTheory.PAIR] >>
  strip_tac >> gvs[runtime_storage_consistent_def]
QED
Theorem runtime_storage_consistent_declared_region_read_typed:
  runtime_storage_consistent env cx st /\
  declared_storage_region cx mid n subs = SOME (b,slot,tv) ==>
  ?v. read_storage_slot cx b slot tv st = (INL v,st) /\
      value_has_type tv v
Proof
  simp[runtime_storage_consistent_def] >>
  metis_tac[current_declared_storage_region_read_typed]
QED

Theorem runtime_storage_consistent_hashmap_leaf_read_typed:
  runtime_storage_consistent env cx st /\
  get_module_code cx mid = SOME code /\
  find_var_decl_by_num (string_to_num n) code =
    SOME (HashMapVarDecl b kt vt,id) /\
  lookup_var_slot_from_layout cx b mid id = SOME off /\
  split_hashmap_subscripts vt rest_subs = SOME (final_type,kts,[]) /\
  compute_hashmap_slot (n2w off) (kt::kts) (first_sub::rest_subs) =
    SOME final_slot /\
  evaluate_type (get_tenv cx) final_type = SOME final_tv ==>
  ?v. read_storage_slot cx b final_slot final_tv st = (INL v,st) /\
      value_has_type final_tv v
Proof
  simp[runtime_storage_consistent_def] >>
  metis_tac[current_hashmap_leaf_read_typed]
QED

Theorem runtime_storage_consistent_declared_leaf_read_hashmap_typed:
  runtime_storage_consistent env cx st /\
  declared_storage_region cx mid n [ValueSubscript kv] =
    SOME (b,hashmap_slot_for root_slot kt kv,tv) /\
  evaluate_type (get_tenv cx) typ = SOME tv ==>
  ?v. read_hashmap cx st (HashMapRef b root_slot kt (Type typ)) kv = SOME v /\
      value_has_type tv v
Proof
  simp[runtime_storage_consistent_def] >>
  metis_tac[current_declared_leaf_read_hashmap_typed]
QED


Theorem assign_target_preserves_contract_storage_well_formed_mutual:
  (!cx gv op st res st'.
    assign_target cx gv op st = (res,st') ==>
    !env tgt ty.
      runtime_storage_consistent env cx st /\
      target_runtime_typed env cx st tgt ty gv /\
      assignable_type env.type_defs ty /\
      assign_operation_runtime_typed env ty op /\
      assign_operation_matches_target_shape gv op /\
      assign_target_assignable_context cx gv st ==>
      contract_storage_well_formed cx st') /\
  (!cx gvs vs st res st'.
    assign_targets cx gvs vs st = (res,st') ==>
    !env tgts.
      runtime_storage_consistent env cx st /\
      target_assignment_values_assignable env cx st tgts gvs vs /\
      EVERY (\gv. assign_target_assignable_context cx gv st) gvs ==>
      contract_storage_well_formed cx st')
Proof
  ho_match_mp_tac assign_target_ind >>
  conj_tac >- suspend "storage_ScopedVar" >>
  conj_tac >- suspend "storage_TopLevelVar" >>
  conj_tac >- suspend "storage_ImmutableVar" >>
  conj_tac >- suspend "storage_TupleTargetV" >>
  rpt (conj_tac >-
    (rpt strip_tac >>
     gvs[Once assign_target_def, raise_def,
         runtime_storage_consistent_def])) >>
  conj_tac >-
    (rpt strip_tac >>
     gvs[Once assign_target_def, return_def,
         runtime_storage_consistent_def]) >>
  conj_tac >- suspend "storage_assign_targets_cons" >>
  rpt strip_tac >>
  gvs[Once assign_target_def, raise_def,
      target_assignment_values_assignable_def, LIST_REL3_def,
      runtime_storage_consistent_def]
QED
(* Definitions and proofs follow in the invariant components. *)

Resume assign_target_preserves_contract_storage_well_formed_mutual[storage_ScopedVar]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  metis_tac[assign_target_scoped_preserves_contract_storage_well_formed,
            runtime_storage_consistent_def]
QED

Resume assign_target_preserves_contract_storage_well_formed_mutual[storage_TopLevelVar]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  metis_tac[assign_target_TopLevelVar_preserves_contract_storage_well_formed]
QED

Resume assign_target_preserves_contract_storage_well_formed_mutual[storage_ImmutableVar]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  metis_tac[assign_target_immutable_preserves_contract_storage_well_formed,
            runtime_storage_consistent_def]
QED

Resume assign_target_preserves_contract_storage_well_formed_mutual[storage_TupleTargetV]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rename1 `assign_target cx (TupleTargetV gvs)
    (Replace (ArrayV (TupleV vs))) st = (res,st')` >>
  gvs[assign_target_assignable_context_def] >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_def, lift_option_type_def, lift_sum_def, type_check_def,
      assert_def, check_def, AllCaseEqs(),
      assign_operation_matches_target_shape_def] >>
  Cases_on `tgt` >>
  gvs[vyperTypeExprSoundnessTheory.target_runtime_typed_def,
      vyperTypeExprSoundnessTheory.target_value_shape_def,
      vyperTypeSystemTheory.well_typed_atarget_def] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  first_x_assum (drule_at Any) >> simp[] >> strip_tac >>
  qpat_assum `!tgts. target_assignment_values_assignable env cx st
                 tgts gvs vs ==> _`
    (qspec_then `l` mp_tac) >>
  (impl_tac >-
    (simp[target_assignment_values_assignable_def] >>
     gvs[vyperTypeExprSoundnessTheory.assign_operation_runtime_typed_def,
         vyperTypeExprSoundnessTheory.value_runtime_typed_def] >>
     drule vyperTypeValuesTheory.evaluate_type_TupleT_cases >>
     strip_tac >> gvs[] >>
     gvs[vyperTypingTheory.value_has_type_def,
         vyperTypeDefaultsTheory.values_have_types_LIST_REL] >>
     irule LIST_REL3_from_LIST_REL2 >> simp[] >>
     gvs[listTheory.LIST_REL_EL_EQN] >> rw[] >>
     simp[listTheory.EL_ZIP] >>
     first_x_assum drule >> strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[] >>
     qexists_tac `EL n tys` >>
     qexists_tac `EL n tvs` >>
     simp[] >>
     gvs[target_values_runtime_typed_LIST_REL3] >>
     drule LIST_REL3_EL >> simp[] >>
     gvs[vyperTypeSystemTheory.assignable_type_def, listTheory.EVERY_EL] >>
     first_x_assum drule >> simp[])) >>
  simp[]
QED

Theorem assign_target_assignable_context_rebuild_EVERY_storage[local]:
  !cx st st' gvs.
    preserves_tv cx st st' ==>
    MAP FDOM st'.scopes = MAP FDOM st.scopes ==>
    EVERY (\gv. assign_target_assignable_context cx gv st) gvs ==>
    EVERY (\gv. assign_target_assignable_context cx gv st') gvs
Proof
  rpt strip_tac >> Induct_on `gvs` >> simp[] >>
  rpt strip_tac >>
  drule_all assign_target_assignable_context_rebuild >> simp[]
QED

Resume assign_target_preserves_contract_storage_well_formed_mutual[storage_assign_targets_cons]:
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  gvs[target_assignment_values_assignable_def] >>
  Cases_on `tgts` >> gvs[LIST_REL3_def] >>
  `target_assignment_values_assignable env cx st t gvs vs` by
    simp[target_assignment_values_assignable_def] >>
  Cases_on `assign_target cx gv (Replace v) st` >>
  Cases_on `q`
  >- (rename1 `assign_target cx gv (Replace v) st = (INL ar,s1)` >>
      `runtime_consistent env cx s1` by
        metis_tac[assign_target_preserves_runtime_consistent_result,
                  assign_operation_runtime_typed_Replace_from_value_has_type,
                  assign_operation_matches_target_shape_Replace_from_typed,
                  runtime_storage_consistent_def] >>
      `contract_storage_well_formed cx s1` by
        (qpat_assum `!st res st'. assign_target cx gv (Replace v) st =
                       (res,st') ==> _`
           (qspecl_then [`st`, `INL ar`, `s1`] mp_tac) >>
         simp[] >>
         disch_then (qspecl_then [`env`, `h`, `ty`] mp_tac) >>
         metis_tac[assign_operation_runtime_typed_Replace_from_value_has_type,
                   assign_operation_matches_target_shape_Replace_from_typed]) >>
      `runtime_storage_consistent env cx s1` by
        gvs[runtime_storage_consistent_def] >>
      `target_assignment_values_assignable env cx s1 t gvs vs` by
        metis_tac[target_assignment_values_assignable_rebuild] >>
      `preserves_tv cx st s1 /\
       MAP FDOM s1.scopes = MAP FDOM st.scopes` by
        metis_tac[vyperEvalPreservesScopesTheory.assign_target_preserves_tv,
                  vyperScopePreservationTheory.assign_target_preserves_scopes_dom] >>
      `EVERY (\gv. assign_target_assignable_context cx gv s1) gvs` by
        metis_tac[assign_target_assignable_context_rebuild_EVERY_storage] >>
      gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def,
          raise_def, lift_option_def, lift_option_type_def, lift_sum_def,
          AllCaseEqs()] >>
      qpat_x_assum `!a b c. assign_target _ _ _ _ = _ ==> _` kall_tac >>
      first_x_assum drule >>
      disch_tac >>
      pop_assum (qspecl_then [`env`, `t`] mp_tac) >>
      metis_tac[target_assignment_values_assignable_def]) >>
  rename1 `assign_target cx gv (Replace v) st = (INR exc,s1)` >>
  qpat_x_assum `!a b c. assign_targets _ _ _ _ = _ ==> _` kall_tac >>
  `contract_storage_well_formed cx s1` by
    (qpat_assum `!st res st'. assign_target cx gv (Replace v) st =
                    (res,st') ==> _`
       (qspecl_then [`st`, `INR exc`, `s1`] mp_tac) >>
     simp[] >>
     disch_then (qspecl_then [`env`, `h`, `ty`] mp_tac) >>
     metis_tac[assign_operation_runtime_typed_Replace_from_value_has_type,
               assign_operation_matches_target_shape_Replace_from_typed]) >>
  gvs[Once assign_target_def, bind_def, ignore_bind_def, return_def,
      raise_def, lift_option_def, lift_option_type_def, lift_sum_def,
      AllCaseEqs()]
QED

Finalise assign_target_preserves_contract_storage_well_formed_mutual

Theorem assign_target_preserves_contract_storage_well_formed:
  assign_target cx gv op st = (res,st') /\
  runtime_storage_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\
  assignable_type env.type_defs ty /\
  assign_operation_runtime_typed env ty op /\
  assign_operation_matches_target_shape gv op /\
  assign_target_assignable_context cx gv st ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[assign_target_preserves_contract_storage_well_formed_mutual]
QED

Theorem assign_targets_preserves_contract_storage_well_formed:
  assign_targets cx gvs vs st = (res,st') /\
  runtime_storage_consistent env cx st /\
  target_assignment_values_assignable env cx st tgts gvs vs /\
  EVERY (\gv. assign_target_assignable_context cx gv st) gvs ==>
  contract_storage_well_formed cx st'
Proof
  metis_tac[assign_target_preserves_contract_storage_well_formed_mutual]
QED


Theorem assign_target_preserves_runtime_storage_consistent_result:
  runtime_storage_consistent env cx st /\
  target_runtime_typed env cx st tgt ty gv /\
  assignable_type env.type_defs ty /\
  assign_operation_runtime_typed env ty op /\
  assign_operation_matches_target_shape gv op /\
  assign_target_assignable_context cx gv st /\
  assign_target cx gv op st = (res,st') ==>
  runtime_storage_consistent env cx st' /\ no_type_error_result res
Proof
  metis_tac[assign_target_sound_mutual,
            assign_target_preserves_contract_storage_well_formed,
            runtime_storage_consistent_def]
QED

Theorem assign_targets_preserves_runtime_storage_consistent_result:
  runtime_storage_consistent env cx st /\
  target_assignment_values_assignable env cx st tgts gvs vs /\
  EVERY (\gv. assign_target_assignable_context cx gv st) gvs /\
  assign_targets cx gvs vs st = (res,st') ==>
  runtime_storage_consistent env cx st' /\ no_type_error_result res
Proof
  metis_tac[assign_target_sound_mutual,
            assign_targets_preserves_contract_storage_well_formed,
            runtime_storage_consistent_def]
QED


(* Constructor entry inherits both storage backends from the abstract machine.
   These lemmas therefore require the exact semantic freshness condition: every
   slot read from the target account and target transient backend is zero. *)
Theorem zero_read_slots_in_range_mutual[local]:
  (!storage off tv.
     (!n. read_slot storage n = 0w) ==>
     slots_in_range storage off tv) /\
  (!storage off tvs.
     (!n. read_slot storage n = 0w) ==>
     tuple_slots_in_range storage off tvs) /\
  (!storage off tv n.
     (!m. read_slot storage m = 0w) ==>
     static_slots_in_range storage off tv n) /\
  (!storage off tv n.
     (!m. read_slot storage m = 0w) ==>
     dyn_slots_in_range storage off tv n) /\
  (!storage off fields.
     (!n. read_slot storage n = 0w) ==>
     struct_slots_in_range storage off fields)
Proof
  ho_match_mp_tac vyperLookupStorageTheory.slots_in_range_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  PURE_ONCE_REWRITE_TAC[vyperLookupStorageTheory.slots_in_range_def] >>
  gvs[] >>
  metis_tac[]
QED

Theorem zero_read_storage_contract_storage_well_formed:
  (!b n. read_slot (get_storage cx st b) n = 0w) ==>
  contract_storage_well_formed cx st
Proof
  simp[contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq] >>
  metis_tac[zero_read_slots_in_range_mutual]
QED

Theorem constructor_entry_contract_storage_well_formed:
  (!n. read_slot (am.tStorage cx.txn.target) n = 0w) /\
  (!n. read_slot ((am.accounts cx.txn.target).storage) n = 0w) ==>
  contract_storage_well_formed cx (initial_state am [scope])
Proof
  strip_tac >> irule zero_read_storage_contract_storage_well_formed >>
  Cases >>
  gvs[vyperStorageBackendTheory.get_storage_def,
      vyperInterpreterTheory.initial_state_def]
QED

Theorem constructor_entry_runtime_storage_consistent:
  (!n. read_slot (am.tStorage cx.txn.target) n = 0w) /\
  (!n. read_slot ((am.accounts cx.txn.target).storage) n = 0w) /\
  storage_layout_safe cx /\
  runtime_consistent env cx (initial_state am [scope]) ==>
  runtime_storage_consistent env cx (initial_state am [scope])
Proof
  simp[runtime_storage_consistent_def] >>
  metis_tac[constructor_entry_contract_storage_well_formed]
QED

Theorem constructor_assign_targets_preserves_runtime_storage_consistent_result:
  (!n. read_slot (am.tStorage cx.txn.target) n = 0w) /\
  (!n. read_slot ((am.accounts cx.txn.target).storage) n = 0w) /\
  storage_layout_safe cx /\
  runtime_consistent env cx (initial_state am [scope]) /\
  target_assignment_values_assignable env cx (initial_state am [scope])
    tgts gvs vs /\
  EVERY (\gv. assign_target_assignable_context cx gv
    (initial_state am [scope])) gvs /\
  assign_targets cx gvs vs (initial_state am [scope]) = (res,st') ==>
  runtime_storage_consistent env cx st' /\ no_type_error_result res
Proof
  metis_tac[constructor_entry_runtime_storage_consistent,
            assign_targets_preserves_runtime_storage_consistent_result]
QED



(* This is independent of call_evaluation_safe: it constrains the exact
   external transition returned to the protected transaction target. *)
Definition protected_storage_calls_preserve_def:
  protected_storage_calls_preserve cx <=>
    !callee calldata value_opt st txp success returndata accounts' tStorage' emitted_logs.
      run_ext_call cx.txn.target callee calldata value_opt
        st.accounts st.tStorage txp =
        SOME (success,returndata,accounts',tStorage',emitted_logs) /\
      contract_storage_well_formed cx st ==>
      contract_storage_well_formed cx
        (st with <| accounts := accounts'; tStorage := tStorage' |>)
End

Theorem protected_storage_calls_preserve_run_ext_call:
  protected_storage_calls_preserve cx /\
  run_ext_call cx.txn.target callee calldata value_opt
    st.accounts st.tStorage txp =
    SOME (success,returndata,accounts',tStorage',emitted_logs) /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  simp[protected_storage_calls_preserve_def] >> metis_tac[]
QED

Theorem protected_storage_calls_preserve_success:
  protected_storage_calls_preserve cx /\
  run_ext_call cx.txn.target callee calldata value_opt
    st.accounts st.tStorage txp =
    SOME (T,returndata,accounts',tStorage',emitted_logs) /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  metis_tac[protected_storage_calls_preserve_run_ext_call]
QED

Theorem protected_storage_calls_preserve_revert:
  protected_storage_calls_preserve cx /\
  run_ext_call cx.txn.target callee calldata value_opt
    st.accounts st.tStorage txp =
    SOME (F,returndata,accounts',tStorage',emitted_logs) /\
  contract_storage_well_formed cx st ==>
  contract_storage_well_formed cx
    (st with <| accounts := accounts'; tStorage := tStorage' |>)
Proof
  metis_tac[protected_storage_calls_preserve_run_ext_call]
QED

Theorem protected_storage_call_output_persistent_region:
  protected_storage_calls_preserve cx /\
  run_ext_call cx.txn.target callee calldata value_opt
    st.accounts st.tStorage txp =
    SOME (success,returndata,accounts',tStorage',emitted_logs) /\
  contract_storage_well_formed cx st /\
  declared_storage_region cx mid n subs = SOME (F,slot,tv) /\
  get_storage_backend cx F
    (st with <| accounts := accounts'; tStorage := tStorage' |>) =
    (INL storage,st'') ==>
  slots_in_range storage (w2n slot) tv
Proof
  metis_tac[protected_storage_calls_preserve_run_ext_call,
            contract_storage_well_formed_region]
QED

Theorem protected_storage_call_output_transient_region:
  protected_storage_calls_preserve cx /\
  run_ext_call cx.txn.target callee calldata value_opt
    st.accounts st.tStorage txp =
    SOME (success,returndata,accounts',tStorage',emitted_logs) /\
  contract_storage_well_formed cx st /\
  declared_storage_region cx mid n subs = SOME (T,slot,tv) /\
  get_storage_backend cx T
    (st with <| accounts := accounts'; tStorage := tStorage' |>) =
    (INL storage,st'') ==>
  slots_in_range storage (w2n slot) tv
Proof
  metis_tac[protected_storage_calls_preserve_run_ext_call,
            contract_storage_well_formed_region]
QED
