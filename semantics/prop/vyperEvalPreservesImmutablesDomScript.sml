Theory vyperEvalPreservesImmutablesDom
Ancestors
  vyperMisc vyperAST vyperValue vyperContext vyperState vyperStorageBackend vyperCreate vyperInterpreter
  vyperLookup vyperScopePreservation vyperStatePreservation
  vyperAssignTarget vyperEvalExprPreservesScopesDom
  vyperImmutablesPreservation

(* ========================================================================
   Preservation of immutables domain through eval_expr / eval_stmts.

   TOP-LEVEL:
     eval_expr_preserves_immutables_addr_dom
     eval_expr_preserves_immutables_dom
     eval_base_target_preserves_immutables_addr_dom
     eval_base_target_preserves_immutables_dom
     eval_exprs_preserves_immutables_addr_dom
     eval_stmts_preserves_immutables_addr_dom
     eval_stmts_preserves_immutables_dom
   ======================================================================== *)

(* ===== Predicate bundling both domain properties ===== *)

Definition preserves_immutables_dom_def:
  preserves_immutables_dom cx (st:evaluation_state) (st':evaluation_state) ⇔
    (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔
           IS_SOME (ALOOKUP st'.immutables tgt)) ∧
    (∀src n imms imms'.
       ALOOKUP st.immutables cx.txn.target = SOME imms ∧
       ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
       (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
        IS_SOME (FLOOKUP (get_source_immutables src imms') n)))
End

Theorem preserves_immutables_dom_refl[local]:
  ∀cx st. preserves_immutables_dom cx st st
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

Theorem preserves_immutables_dom_trans[local]:
  ∀cx st1 st2 st3.
    preserves_immutables_dom cx st1 st2 ∧
    preserves_immutables_dom cx st2 st3 ⇒
    preserves_immutables_dom cx st1 st3
Proof
  rw[preserves_immutables_dom_def] >>
  gvs[optionTheory.IS_SOME_EXISTS]
QED

Theorem preserves_immutables_dom_eq[local]:
  ∀cx st st'.
    st'.immutables = st.immutables ⇒ preserves_immutables_dom cx st st'
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

(* ===== Trivial monad helpers ===== *)

Theorem get_Value_immutables[local]:
  ∀tv st res st'. get_Value tv st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  Cases_on `tv` >> rw[get_Value_def, return_def, raise_def]
QED

Theorem transfer_value_immutables[local]:
  ∀f t a st res st'.
    transfer_value f t a st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, type_check_def, assert_def, update_accounts_def] >> gvs[raise_def]
QED

Theorem lookup_flag_mem_immutables[local]:
  ∀cx nsid mid st res st'.
    lookup_flag_mem cx nsid mid st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  rpt gen_tac >> PairCases_on `nsid` >>
  simp[lookup_flag_mem_def, return_def, raise_def] >>
  rpt CASE_TAC >> simp[return_def, raise_def]
QED

(* ===== assign_target preserves immutables domain for any result ===== *)

Theorem assign_target_imm_dom_ScopedVar[local]:
  ∀cx id is ao st res st'.
    assign_target cx (BaseTargetV (ScopedVar id) is) ao st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = (_, _)` mp_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def,
       type_check_def, assert_def, sum_CASE_rator,
       AllCaseEqs(), raise_def, LET_THM,
       ignore_bind_def, set_scopes_def] >>
  rpt CASE_TAC >> gvs[return_def, raise_def, set_scopes_def, bind_def] >>
  PairCases_on `x` >>
  simp[bind_def, type_check_def, assert_def, sum_CASE_rator,
       AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
  rpt CASE_TAC >> gvs[return_def, raise_def, set_scopes_def] >>
  rpt strip_tac >>
  gvs[oneline assign_result_def, return_def, bind_def, lift_sum_def, raise_def,
      AllCaseEqs(), assign_operation_CASE_rator, sum_CASE_rator]
QED

(* Helper: the HashMap do-block in assign_target preserves immutables *)
Theorem hashmap_do_block_immutables[local]:
  ∀cx b c t' tenv key_types remaining_subs final_type h t ao r res st'.
    (λ(final_type,key_types,remaining_subs).
       do
         final_slot <-
           case
             compute_hashmap_slot c (t'::key_types)
               (h::TAKE (LENGTH t − LENGTH remaining_subs) t)
           of
             NONE => raise (Error (TypeError "assign_target compute_hashmap_slot"))
           | SOME v => return v;
         final_tv <-
           case evaluate_type tenv final_type of
             NONE => raise (Error (TypeError "assign_target evaluate_type"))
           | SOME v => return v;
         current_val <- read_storage_slot cx b final_slot final_tv;
         new_val <-
           case assign_subscripts final_tv current_val remaining_subs ao of
             INL v => return v
           | INR e => raise (Error e);
         x <- write_storage_slot cx b final_slot final_tv new_val;
         assign_result final_tv ao current_val remaining_subs
       od) (final_type,key_types,remaining_subs) r = (res,st') ⇒
    st'.immutables = r.immutables
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `_ = (res, st')` mp_tac >>
  simp[bind_def, return_def, raise_def] >> strip_tac >>
  (* Step 1: compute_hashmap_slot *)
  Cases_on `compute_hashmap_slot c (t'::key_types)
              (h::TAKE (LENGTH t − LENGTH remaining_subs) t)` >>
  gvs[return_def, raise_def] >>
  rename1 `compute_hashmap_slot _ _ _ = SOME slot` >>
  (* Step 2: evaluate_type *)
  Cases_on `evaluate_type tenv final_type` >>
  gvs[return_def, raise_def] >>
  rename1 `evaluate_type _ _ = SOME tv` >>
  (* Step 3: read_storage_slot *)
  `∃rr sr. read_storage_slot cx b slot tv r = (rr, sr)` by
    metis_tac[pairTheory.PAIR] >>
  Cases_on `rr` >> gvs[] >>
  imp_res_tac read_storage_slot_immutables >>
  (* Step 4: assign_subscripts *)
  Cases_on `assign_subscripts tv x remaining_subs ao` >>
  gvs[return_def, raise_def] >>
  rename1 `assign_subscripts _ _ _ _ = INL new_val` >>
  (* Step 5: write_storage_slot *)
  `∃rw sw. write_storage_slot cx b slot tv new_val sr = (rw, sw)` by
    metis_tac[pairTheory.PAIR] >>
  Cases_on `rw` >> gvs[] >>
  imp_res_tac write_storage_slot_immutables >> gvs[] >>
  (* Step 6: assign_result *)
  imp_res_tac assign_result_state >> gvs[]
QED

Theorem lift_option_same_state[local]:
  lift_option v msg s = (r, s') ⇒ s' = s
Proof
  rw[lift_option_def, lift_option_type_def] >> Cases_on `v` >> gvs[return_def, raise_def]
QED

Theorem lift_option_type_same_state[local]:
  lift_option_type v msg s = (r, s') ⇒ s' = s
Proof
  rw[lift_option_type_def] >> Cases_on `v` >> gvs[return_def, raise_def]
QED

Theorem assign_target_imm_dom_TopLevelVar[local]:
  ∀cx src_id_opt id is ao st res st'.
    assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) is) ao st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rw[assign_target_def, bind_def, ignore_bind_def, AllCaseEqs(),
     toplevel_value_CASE_rator, sum_CASE_rator, prod_CASE_rator,
     type_value_CASE_rator] >>
  imp_res_tac lookup_global_immutables >>
  imp_res_tac lift_option_same_state >> imp_res_tac lift_option_type_same_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac assign_result_state >>
  imp_res_tac set_global_immutables >>
  imp_res_tac resolve_array_element_state >>
  gvs[] >>
  pairarg_tac >>
  gvs[bind_def, AllCaseEqs(), type_value_CASE_rator,
      assign_operation_CASE_rator, bound_CASE_rator,
      return_def, raise_def, check_def, type_check_def, assert_def] >>
  imp_res_tac lift_option_same_state >> imp_res_tac lift_option_type_same_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac read_storage_slot_immutables >>
  imp_res_tac write_storage_slot_immutables >>
  imp_res_tac assign_result_state >>
  imp_res_tac resolve_array_element_state >>
  imp_res_tac get_storage_backend_state >>
  gvs[] >>
  pairarg_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  imp_res_tac lift_option_same_state >> imp_res_tac lift_option_type_same_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac read_storage_slot_immutables >>
  imp_res_tac write_storage_slot_immutables >>
  imp_res_tac assign_result_state >>
  gvs[]
QED

Theorem assign_target_imm_dom_ImmutableVar[local]:
  ∀cx src_id_opt id is ao st res st'.
    assign_target cx (BaseTargetV (ImmutableVar src_id_opt id) is) ao st = (res, st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = (_, _)` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_def, lift_option_type_def,
       return_def, raise_def, LET_THM, AllCaseEqs()] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >>
  simp[return_def, raise_def] >-
  (strip_tac >> gvs[preserves_immutables_dom_refl]) >>
  Cases_on `FLOOKUP (get_source_immutables src_id_opt x) (string_to_num id)` >>
  simp[return_def, raise_def] >-
  (strip_tac >> gvs[preserves_immutables_dom_refl]) >>
  PairCases_on `x'` >> simp[] >>
  Cases_on `assign_subscripts x'0 x'1 (REVERSE is) ao` >>
  simp[lift_sum_def, return_def, raise_def] >>
  strip_tac >> gvs[preserves_immutables_dom_refl] >>
  TRY (qpat_x_assum `lift_option_type (SOME _) _ _ = (INR _,_)` mp_tac >>
       simp[lift_option_type_def, return_def, raise_def] >> NO_TAC) >>
  Cases_on `set_immutable cx src_id_opt (string_to_num id) x'0 x' st` >>
  Cases_on `q` >> gvs[lift_option_type_def, return_def, raise_def] >-
  (TRY (qpat_x_assum `lift_option_type (SOME x) _ _ = (INR _,_)` mp_tac >>
        simp[lift_option_type_def, return_def, raise_def] >> NO_TAC) >>
   imp_res_tac assign_result_state >> gvs[] >>
   gvs[set_immutable_def, bind_def, get_address_immutables_def,
       lift_option_type_def, lift_option_def, set_address_immutables_def,
       return_def, raise_def, LET_THM,
       AllCaseEqs()] >>
   simp[preserves_immutables_dom_def] >> conj_tac
   >- (rpt strip_tac >>
       Cases_on `cx.txn.target = tgt` >>
       gvs[alistTheory.ALOOKUP_ADELKEY])
   >> simp[set_source_immutables_def, get_source_immutables_def,
           alistTheory.ALOOKUP_ADELKEY,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt gen_tac >>
      TRY (rename1 `IS_SOME (FLOOKUP (get_source_immutables src _) n)`) >>
      TRY (Cases_on `src = src_id_opt` >> gvs[]) >>
      Cases_on `n = string_to_num id` >>
      gvs[get_source_immutables_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  gvs[set_immutable_def, bind_def, get_address_immutables_def,
      lift_option_type_def, lift_option_def, set_address_immutables_def,
      return_def, raise_def, LET_THM,
      AllCaseEqs(), preserves_immutables_dom_refl]
QED

Theorem assign_target_imm_dom_TupleV[local]:
  ∀cx gvs vs st res st'.
    (∀st res st'.
       assign_targets cx gvs vs st = (res, st') ⇒
       preserves_immutables_dom cx st st') ⇒
    assign_target cx (TupleTargetV gvs) (Replace (ArrayV (TupleV vs))) st =
    (res, st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, check_def, type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl]
QED

Theorem assign_targets_imm_dom_cons[local]:
  ∀cx av v gvs vs st res st'.
    (∀st res st'.
       assign_target cx av (Replace v) st = (res, st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀st res st'.
       assign_targets cx gvs vs st = (res, st') ⇒
       preserves_immutables_dom cx st st') ⇒
    assign_targets cx (av::gvs) (v::vs) st = (res, st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `assign_targets _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, ignore_bind_def,
       AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> metis_tac[]
QED

Theorem assign_target_imm_dom_any[local]:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (res, st') ⇒ preserves_immutables_dom cx st st')
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac
  (* ScopedVar *)
  >- (rpt strip_tac >> irule preserves_immutables_dom_eq >>
      imp_res_tac assign_target_imm_dom_ScopedVar >> simp[])
  (* TopLevelVar *)
  >- (rpt strip_tac >> irule preserves_immutables_dom_eq >>
      imp_res_tac assign_target_imm_dom_TopLevelVar >> simp[])
  (* ImmutableVar *)
  >- (rpt strip_tac >> imp_res_tac assign_target_imm_dom_ImmutableVar)
  (* TupleTargetV + TupleV *)
  >- (rpt strip_tac >> irule assign_target_imm_dom_TupleV >> metis_tac[])
  (* All remaining 16 subgoals: TupleTargetV raise cases, assign_targets *)
  >> rpt strip_tac
  >> TRY (irule assign_targets_imm_dom_cons >> metis_tac[])
  >> gvs[Once assign_target_def, raise_def, return_def,
         preserves_immutables_dom_refl]
QED

(* ===== IntCall helper ===== *)

Theorem handle_function_immutables[local]:
  ∀exc st res st'.
    handle_function exc st = (res, st') ⇒ st'.immutables = st.immutables
Proof
  Cases_on `exc` >> simp[handle_function_def, return_def, raise_def]
QED

Theorem acquire_nonreentrant_lock_immutables[local]:
  ∀addr slot is_view st res st'.
    acquire_nonreentrant_lock addr slot is_view st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem release_nonreentrant_lock_immutables[local]:
  ∀addr slot st res st'.
    release_nonreentrant_lock addr slot st = (res, st') ⇒
    st'.immutables = st.immutables
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem lock_acquire_cond_immutables[local]:
  ∀nr slot_opt addr is_view s res s'.
    (if nr then
       case slot_opt of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock addr slot is_view
     else return ()) s = (res, s') ⇒
    s'.immutables = s.immutables
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[raise_def]
  \\ imp_res_tac acquire_nonreentrant_lock_immutables
QED

Theorem finally_lock_release_immutables[local]:
  ∀nr mut slot_opt addr s res s'.
    (if nr ∧ mut ≠ View ∧ mut ≠ Pure then
       case slot_opt of
         NONE => return ()
       | SOME slot => release_nonreentrant_lock addr slot
     else return ()) s = (res, s') ⇒
    s'.immutables = s.immutables
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr ∧ mut ≠ View ∧ mut ≠ Pure` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[return_def]
  \\ imp_res_tac release_nonreentrant_lock_immutables
QED

Theorem preserves_immutables_dom_txn_eq[local]:
  ∀cx cx' st st'.
    cx'.txn = cx.txn ⇒
    (preserves_immutables_dom cx' st st' ⇔ preserves_immutables_dom cx st st')
Proof
  simp[preserves_immutables_dom_def]
QED

Theorem intcall_default_frame_imm_dom[local]:
  (∀st res st'.
     eval_exprs cxd needed_dflts st = (res,st') ⇒
     preserves_immutables_dom cxd st st') ⇒
  finally
    (do
       set_scopes [FEMPTY];
       eval_exprs cxd needed_dflts
     od)
    (set_scopes prev) sget = (res,st1) ⇒
  preserves_immutables_dom cxd sget st1
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, bind_def, ignore_bind_def, set_scopes_def, return_def] >>
  Cases_on `eval_exprs cxd needed_dflts (sget with scopes := [FEMPTY])` >>
  Cases_on `q` >> simp[return_def, raise_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `∀st res st'. eval_exprs cxd needed_dflts st = (res,st') ⇒ _`
    (drule_then assume_tac) >>
  gvs[preserves_immutables_dom_def]
QED

Theorem case_IntCall_imm_dom_inner[local]:
  ∀cx src_id_opt fname body env st0 vs sevl dflt_vs sdfl
   fres sfnl es needed_dflts prev.
    (∀st res st'.
       eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ∧
    (∀st res st'.
       eval_exprs (cx with stk updated_by CONS (src_id_opt,fname))
         needed_dflts st = (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    (∀st res st'.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fname)) body st =
       (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    eval_exprs cx es st0 = (INL vs, sevl) ∧
    eval_exprs (cx with stk updated_by CONS (src_id_opt,fname))
      needed_dflts sevl = (INL dflt_vs, sdfl) ∧
    finally
      (try (bind (eval_stmts (cx with stk updated_by CONS (src_id_opt,fname))
         body) (λx. return NoneV)) handle_function)
      (pop_function prev)
      (sdfl with scopes := [env]) = (fres, sfnl) ⇒
    preserves_immutables_dom cx st0 sfnl
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >> conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl` >> conj_tac
  >- (irule (iffLR preserves_immutables_dom_txn_eq) >>
      qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >>
      simp[] >> gvs[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl with scopes := [env]` >>
  gvs[preserves_immutables_dom_eq] >>
  irule (iffLR preserves_immutables_dom_txn_eq) >>
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >> simp[] >>
  qpat_x_assum `try _ _ _ = _` mp_tac >>
  simp[try_def, bind_def, AllCaseEqs(), return_def, raise_def,
       handle_function_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, preserves_immutables_dom_eq] >>
  first_x_assum drule >> gvs[preserves_immutables_dom_eq] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[handle_function_def, return_def, raise_def, preserves_immutables_dom_eq] >>
  first_x_assum drule >> gvs[preserves_immutables_dom_eq] >>
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >>
  gvs[handle_function_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac handle_function_immutables
QED

Definition post_default_intcall_tail_def:
  post_default_intcall_tail cx src_id_opt fn mut nr args ret ss vs dflt_vs prev sdfl =
    (do
       all_tenv <<- get_tenv cx;
       env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
                "IntCall bind_arguments";
       rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
       is_view <<- (mut = View ∨ mut = Pure);
       (if nr then
          case cx.nonreentrant_slot of
          | NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
        else return ());
       cxf <- push_function (src_id_opt,fn) env cx;
       rv <- finally
         (try (do eval_stmts cxf ss; return NoneV od) handle_function)
         (do
            pop_function prev;
            if nr ∧ ¬is_view then
              case cx.nonreentrant_slot of
              | NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) sdfl
End

Theorem post_default_intcall_tail_unfold[local]:
  post_default_intcall_tail cx src_id_opt fn mut nr args ret ss vs dflt_vs prev sdfl =
    (do
       all_tenv <<- get_tenv cx;
       env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs))
                "IntCall bind_arguments";
       rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
       is_view <<- (mut = View ∨ mut = Pure);
       (if nr then
          case cx.nonreentrant_slot of
          | NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
        else return ());
       cxf <- push_function (src_id_opt,fn) env cx;
       rv <- finally
         (try (do eval_stmts cxf ss; return NoneV od) handle_function)
         (do
            pop_function prev;
            if nr ∧ ¬is_view then
              case cx.nonreentrant_slot of
              | NONE => return ()
              | SOME slot => release_nonreentrant_lock cx.txn.target slot
            else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) sdfl
Proof
  rw[post_default_intcall_tail_def]
QED

Definition intcall_tail_body_provider_def:
  intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl =
    ∀env s_bind rtv s_eval lk s_lock cx' s_push.
      lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments" sdfl = (INL env,s_bind) ∧
      lift_option_type (evaluate_type (get_tenv cx) ret)
        "IntCall eval ret" s_bind = (INL rtv,s_eval) ∧
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View ∨ mut = Pure)
       else return ()) s_eval = (INL lk,s_lock) ∧
      push_function (src_id_opt,fn) env cx s_lock = (INL cx',s_push) ⇒
      ∀st res st'. eval_stmts cx' ss st = (res,st') ⇒
        preserves_immutables_dom cx' st st'
End

Theorem intcall_tail_body_provider_unfold[local]:
  intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl =
    ∀env s_bind rtv s_eval lk s_lock cx' s_push.
      lift_option_type (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
        "IntCall bind_arguments" sdfl = (INL env,s_bind) ∧
      lift_option_type (evaluate_type (get_tenv cx) ret)
        "IntCall eval ret" s_bind = (INL rtv,s_eval) ∧
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View ∨ mut = Pure)
       else return ()) s_eval = (INL lk,s_lock) ∧
      push_function (src_id_opt,fn) env cx s_lock = (INL cx',s_push) ⇒
      ∀st res st'. eval_stmts cx' ss st = (res,st') ⇒
        preserves_immutables_dom cx' st st'
Proof
  rw[intcall_tail_body_provider_def]
QED

Theorem intcall_post_default_eq_imm_dom[local]:
  ∀cx cxd st0 sevl sdfl st'.
    cxd.txn = cx.txn ⇒
    preserves_immutables_dom cx st0 sevl ⇒
    preserves_immutables_dom cxd sevl sdfl ⇒
    st'.immutables = sdfl.immutables ⇒
    preserves_immutables_dom cx st0 st'
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >>
  conj_tac >- simp[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl` >>
  conj_tac
  >- (irule (iffLR preserves_immutables_dom_txn_eq) >>
      qexists_tac `cxd` >> simp[]) >>
  irule preserves_immutables_dom_eq >> simp[]
QED

Theorem case_IntCall_imm_dom_inner_pres[local]:
  ∀cx src_id_opt fname body st0 sevl sdfl fres sfnl env prev.
    preserves_immutables_dom cx st0 sevl ∧
    preserves_immutables_dom
      (cx with stk updated_by CONS (src_id_opt,fname)) sevl sdfl ∧
    (∀st res st'.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fname)) body st =
       (res,st') ⇒
       preserves_immutables_dom
         (cx with stk updated_by CONS (src_id_opt,fname)) st st') ∧
    finally
      (try (bind (eval_stmts (cx with stk updated_by CONS (src_id_opt,fname))
         body) (λx. return NoneV)) handle_function)
      (pop_function prev)
      (sdfl with scopes := [env]) = (fres,sfnl) ⇒
    preserves_immutables_dom cx st0 sfnl
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `sevl` >> conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl` >> conj_tac
  >- (irule (iffLR preserves_immutables_dom_txn_eq) >>
      qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >>
      simp[] >> gvs[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `sdfl with scopes := [env]` >>
  gvs[preserves_immutables_dom_eq] >>
  irule (iffLR preserves_immutables_dom_txn_eq) >>
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fname)` >> simp[] >>
  qpat_x_assum `try _ _ _ = _` mp_tac >>
  simp[try_def, bind_def, AllCaseEqs(), return_def, raise_def,
       handle_function_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, preserves_immutables_dom_eq] >>
  qpat_assum `∀st res st'. eval_stmts _ _ st = (res,st') ⇒ _`
    drule >> gvs[preserves_immutables_dom_eq] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[handle_function_def, return_def, raise_def, preserves_immutables_dom_eq] >>
  qpat_assum `∀st res st'. eval_stmts _ _ st = (res,st') ⇒ _`
    drule >> gvs[preserves_immutables_dom_eq] >>
  rpt strip_tac >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- simp[] >>
       irule preserves_immutables_dom_eq >> simp[] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       conj_tac >- simp[] >>
       irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- (irule preserves_immutables_dom_eq >>
                     imp_res_tac handle_function_immutables >> simp[]) >>
       irule preserves_immutables_dom_eq >> simp[] >> NO_TAC) >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >>
  gvs[handle_function_def, return_def, raise_def, AllCaseEqs()] >>
  imp_res_tac handle_function_immutables
QED


Theorem intcall_body_finally_release_imm_dom[local]:
  ∀cx src_id_opt fn mut nr ss prev env st res st'.
    (∀st0 res0 st1.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss st0 = (res0,st1) ⇒
       preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) st0 st1) ∧
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss;
               return NoneV od) handle_function)
      (do pop_function prev;
          if nr ∧ mut ≠ View ∧ mut ≠ Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return () od)
      (st with scopes := [env]) = (res,st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_function_def, set_scopes_def,
       return_def, ignore_bind_def, bind_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_eq, preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `st with scopes := [env]` >>
  conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
  irule (iffLR preserves_immutables_dom_txn_eq) >>
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fn)` >> simp[] >>
  qpat_x_assum `try _ _ _ = _` mp_tac >>
  simp[try_def, bind_def, AllCaseEqs(), return_def, raise_def,
       handle_function_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, preserves_immutables_dom_eq] >>
  qpat_assum `∀st0 res0 st1. eval_stmts _ _ st0 = (res0,st1) ⇒ _`
    drule >> gvs[preserves_immutables_dom_eq] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[handle_function_def, return_def, raise_def, preserves_immutables_dom_eq] >>
  qpat_assum `∀st0 res0 st1. eval_stmts _ _ st0 = (res0,st1) ⇒ _`
    drule >> gvs[preserves_immutables_dom_eq] >>
  rpt strip_tac >>
  qpat_assum `∀st0 res0 st1. eval_stmts _ _ st0 = (res0,st1) ⇒ _`
    drule >> strip_tac >>
  imp_res_tac handle_function_immutables >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  imp_res_tac finally_lock_release_immutables >>
  irule preserves_immutables_dom_trans >>
  first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >> gvs[]
QED

Theorem intcall_body_finally_release_imm_dom_use[local]:
  ∀cx src_id_opt fn mut nr ss prev env st q st'.
    (∀st0 res0 st1.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss st0 = (res0,st1) ⇒
       preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) st0 st1) ⇒
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss;
               return NoneV od) handle_function)
      (do pop_function prev;
          if nr ∧ mut ≠ View ∧ mut ≠ Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return () od)
      (st with scopes := [env]) = (q,st') ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  irule intcall_body_finally_release_imm_dom >>
  qexistsl [`env`, `fn`, `mut`, `nr`, `prev`, `q`, `src_id_opt`, `ss`] >>
  simp[]
QED

(* ----- Case 5: Return (SOME e) ----- *)
Theorem case_Return_SOME_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Return (SOME e)) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[]
QED

(* ----- Case 6: Raise reason ----- *)
(* ----- Case 8: Log id es ----- *)
Theorem case_Log_imm_dom[local]:
  ∀cx id es.
    (∀st res st'. eval_exprs cx es st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Log id es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def, push_log_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq]
QED

(* ----- Case 9: AnnAssign id typ e ----- *)
Theorem case_AnnAssign_imm_dom[local]:
  ∀cx id typ e.
    (∀tenv s'' tyv t.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s'' =
       (INL tyv, t) ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (AnnAssign id typ e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       new_variable_def, LET_THM, get_scopes_def, check_def, type_check_def, assert_def,
       set_scopes_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac lift_option_type_same_state >> gvs[preserves_immutables_dom_refl] >>
  (* Discharge IH guard using lift_option_type assumption *)
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `s'³'` >>
  conj_tac >- gvs[] >>
  irule preserves_immutables_dom_eq >>
  qpat_x_assum `_ s'³' = (res, st')` mp_tac >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, assert_def, return_def, raise_def, set_scopes_def,
       AllCaseEqs()] >>
  Cases_on `s'³'.scopes` >>
  simp[raise_def, set_scopes_def, return_def] >>
  rpt strip_tac >> gvs[]
QED

(* ----- Case 10: Append bt e ----- *)
Theorem case_Append_imm_dom[local]:
  ∀cx bt e.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' loc sbs t'. eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Append bt e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, lift_option_def, lift_option_type_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  first_x_assum (qspecl_then [`st`, `q`, `r`, `s''`] mp_tac) >> simp[] >>
  strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
        gvs[preserves_immutables_dom_eq])
    >> gvs[] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       gvs[preserves_immutables_dom_eq] >> NO_TAC) >>
  gvs[]
QED

(* ----- Case 11: Assign g e ----- *)
(* Eval order: eval_target → eval_expr → materialise → assign_target *)
Theorem case_Assign_imm_dom[local]:
  ∀cx g e.
    (∀st res st'. eval_target cx g st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' gv t'.
       eval_target cx g s'' = (INL gv,t') ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Assign g e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac materialise_state >> gvs[] >>
  (* Derive unconditional eval_expr IH from eval_target success *)
  first_x_assum drule >> strip_tac >>
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  (* Chain: st →(eval_target) s'' →(eval_expr) s'³' →(assign) s'⁵' *)
  metis_tac[preserves_immutables_dom_trans]
QED

(* ----- Case 12: AugAssign bt bop e ----- *)
Theorem case_AugAssign_imm_dom[local]:
  ∀cx ty bt bop e.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' loc sbs t'. eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (AugAssign ty bt bop e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, lift_option_def, lift_option_type_def,
       lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  first_x_assum (qspecl_then [`st`, `q`, `r`, `s''`] mp_tac) >> simp[] >>
  strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'⁵'` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >> conj_tac
        >- (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
            gvs[preserves_immutables_dom_eq])
        >> gvs[preserves_immutables_dom_eq])
    >> gvs[] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
        gvs[preserves_immutables_dom_eq])
    >> gvs[preserves_immutables_dom_eq] >> NO_TAC) >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       gvs[preserves_immutables_dom_eq] >> NO_TAC) >>
  gvs[]
QED

(* ----- Case 13: If e ss1 ss2 ----- *)
Theorem case_If_imm_dom[local]:
  ∀cx e ss1 ss2.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' x t'.
       eval_expr cx e s'' = (INL tv,t) ∧ push_scope s'³' = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss1 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' x t'.
       eval_expr cx e s'' = (INL tv,t) ∧ push_scope s'³' = (INL x,t') ⇒
       ∀st res st'. eval_stmts cx ss2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (If e ss1 ss2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, push_scope_def,
       switch_BoolV_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Simplify push_scope conditions and derive unconditional IHs *)
  RULE_ASSUM_TAC (REWRITE_RULE [push_scope_def, return_def]) >> gvs[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  last_x_assum (drule_then strip_assume_tac) >>
  first_x_assum (drule_then strip_assume_tac) >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `s''` >> conj_tac >- gvs[] >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `s'' with scopes updated_by CONS FEMPTY` >>
  conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
       bind_def, ignore_bind_def] >>
  rpt strip_tac >> gvs[] >>
  irule preserves_immutables_dom_trans >>
  rename1 `_ (s'' with scopes updated_by CONS FEMPTY) = (_, s_body)` >>
  qexists_tac `s_body` >>
  (conj_tac
   >- (Cases_on `tv = Value (BoolV T)` >> gvs[raise_def, preserves_immutables_dom_refl] >>
       Cases_on `tv = Value (BoolV F)` >> gvs[raise_def, preserves_immutables_dom_refl])
   >> irule preserves_immutables_dom_eq >> gvs[])
QED

(* ----- Case 14: For id typ it n body ----- *)
Theorem case_For_imm_dom[local]:
  ∀cx id typ it n body.
    (∀tenv s'' tyv t.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ)
         "For evaluate_type" s'' = (INL tyv, t) ⇒
       ∀st res st'. eval_iterator cx it st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀tenv s'' tyv t s'³' vs t' s'⁴' x t''.
       tenv = get_tenv cx ∧
       lift_option_type (evaluate_type tenv typ)
         "For evaluate_type" s'' = (INL tyv, t) ∧
       eval_iterator cx it s'³' = (INL vs, t') ∧
       check (compatible_bound (Dynamic n) (LENGTH vs))
             "For too long" s'⁴' = (INL x, t'') ⇒
       ∀st res st'. eval_for cx tyv (string_to_num id) body vs st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (For id typ it n body) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac lift_option_type_same_state >> gvs[preserves_immutables_dom_refl] >>
  (* Discharge iterator IH guard: tenv = get_tenv cx ∧ lift_option_type *)
  `∀st res st'. eval_iterator cx it st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by
    (first_x_assum match_mp_tac >> metis_tac[]) >>
  imp_res_tac check_state >> gvs[preserves_immutables_dom_refl] >>
  (* iterator error: IH directly *)
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  (* Success: chain through iterator then eval_for *)
  irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
  conj_tac >- (first_x_assum drule >> simp[]) >>
  first_x_assum drule_all >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

(* ----- Case 15: Expr e ----- *)
Theorem case_Expr_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmt cx (Expr e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  imp_res_tac check_state >> imp_res_tac type_check_state >>
  gvs[preserves_immutables_dom_eq]
QED

(* ----- Case 17: eval_stmts (s::ss) ----- *)
Theorem case_eval_stmts_cons_imm_dom[local]:
  ∀cx s ss.
    (∀st res st'. eval_stmt cx s st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' x t. eval_stmt cx s s'' = (INL x,t) ⇒
       ∀st res st'. eval_stmts cx ss st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_stmts cx (s::ss) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- (last_x_assum irule >> metis_tac[]) >>
  first_x_assum irule >> first_assum (irule_at Any) >> metis_tac[]
QED

(* ----- Case 18: eval_iterator (Array e) ----- *)
Theorem case_Array_imm_dom[local]:
  ∀cx e.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_iterator cx (Array e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def,
       lift_option_def, lift_option_type_def] >>
  simp[option_CASE_rator] >>
  simp[AllCaseEqs()] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl, return_def, raise_def] >>
  imp_res_tac get_Value_immutables >>
  imp_res_tac materialise_state >> gvs[]
QED

(* ----- Case 19: eval_iterator (Range e1 e2) ----- *)
Theorem case_Range_imm_dom[local]:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv1 t s'³' s t'.
       eval_expr cx e1 s'' = (INL tv1,t) ∧ get_Value tv1 s'³' = (INL s,t') ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_iterator cx (Range e1 e2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_sum_def, LET_THM] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  (* Derive unconditional IH for e2 from the conditional one *)
  TRY (
    `∀st res st'. eval_expr cx e2 st = (res,st') ⇒
       preserves_immutables_dom cx st st'` by (
      rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
    (* get_range_limits cases: prove final immutables equality *)
    TRY (
      `s'⁶'.immutables = s'⁵'.immutables` by (
        qpat_x_assum `(case _ of _ => _ | _ => _) _ = _` mp_tac >>
        BasicProvers.EVERY_CASE_TAC >>
        gvs[return_def, raise_def])) >>
    (* Chain transitions: st -> s'' -> s'³' -> s'⁴' -> ... *)
    irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
    conj_tac >- gvs[] >>
    irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
    conj_tac >- (irule preserves_immutables_dom_eq >> gvs[]) >>
    TRY (
      irule preserves_immutables_dom_trans >> qexists_tac `s'⁴'` >>
      conj_tac >- gvs[] >>
      irule preserves_immutables_dom_eq >> gvs[]) >>
    gvs[] >> NO_TAC) >>
  (* get_Value tv1 error: chain st -> s'' -> s'³' *)
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq]
QED

(* ----- Case 23: eval_targets (g::gs) ----- *)
Theorem case_eval_targets_cons_imm_dom[local]:
  ∀cx g gs.
    (∀st res st'. eval_target cx g st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' gv t. eval_target cx g s'' = (INL gv,t) ⇒
       ∀st res st'. eval_targets cx gs st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_targets cx (g::gs) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> disch_then drule >> simp[]
QED

(* ----- Case 27: eval_base_target (SubscriptTarget bt e) ----- *)
Theorem case_SubscriptTarget_imm_dom[local]:
  ∀cx bt e.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' loc sbs t'. eval_base_target cx bt s'' = (INL (loc,sbs),t') ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_base_target cx (SubscriptTarget bt e) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `x` >> gvs[] >>
  first_x_assum (qspecl_then [`st`, `q`, `r`, `s''`] mp_tac) >> simp[] >>
  strip_tac >>
  qpat_x_assum `_ s'' = (res, st')` mp_tac >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  qpat_x_assum `!st res st'. eval_expr cx e st = (res,st') ==> _` drule >>
  simp[preserves_immutables_dom_def]
QED

(* ----- Case 29: eval_for (v::vs) ----- *)
Theorem case_eval_for_cons_imm_dom[local]:
  ∀cx nm body v vs.
    (∀s'' x t. push_scope_with_var nm tyv v s'' = (INL x,t) ⇒
       ∀st res st'. eval_stmts cx body st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' x t s'³' broke t'.
       push_scope_with_var nm tyv v s'' = (INL x,t) ∧
       finally
         (try do eval_stmts cx body; return F od handle_loop_exception)
         pop_scope s'³' = (INL broke,t') ∧ ¬broke ⇒
       ∀st res st'. eval_for cx tyv nm body vs st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_for cx tyv nm body (v::vs) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  (* Simplify IHs: push_scope_with_var always succeeds *)
  RULE_ASSUM_TAC (REWRITE_RULE [push_scope_with_var_def, return_def]) >>
  gvs[] >>
  (* Unfold eval_for (v::vs) *)
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, push_scope_with_var_def, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >|
  [ (* Success case: finally returned INL broke *)
    irule preserves_immutables_dom_trans >>
    qexists_tac `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>))` >>
    conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
    qpat_x_assum `finally _ _ _ = _` mp_tac >>
    simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
         bind_def, ignore_bind_def] >>
    rpt strip_tac >> gvs[] >>
    rename1 `try _ _ _ = (_, s_try)` >>
    irule preserves_immutables_dom_trans >>
    qexists_tac `s_try with scopes := tl` >> conj_tac
    >- (irule preserves_immutables_dom_trans >> qexists_tac `s_try` >> conj_tac
        >- (qpat_x_assum `try _ _ _ = _` mp_tac >>
            PURE_REWRITE_TAC [ignore_bind_def] >>
            simp[try_def, bind_def, return_def, AllCaseEqs(),
                 handle_loop_exception_def, raise_def] >>
            rpt strip_tac >> gvs[return_def, raise_def] >>
            TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
            first_x_assum drule >> simp[] >> strip_tac >>
            BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def])
        >- (irule preserves_immutables_dom_eq >> simp[]))
    >- (Cases_on `broke` >> gvs[return_def, preserves_immutables_dom_refl] >>
        first_x_assum (qspecl_then [
            `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>))`,
            `s_try with scopes := tl`] mp_tac) >>
        simp[finally_def, ignore_bind_def, bind_def,
             pop_scope_def, return_def] >>
        disch_then drule >> simp[]),
    (* Error case: finally returned INR e *)
    irule preserves_immutables_dom_trans >>
    qexists_tac `st with scopes updated_by CONS (FEMPTY |+ (nm,<| assignable := F; type := tyv; value := v |>))` >>
    conj_tac >- (irule preserves_immutables_dom_eq >> simp[]) >>
    qpat_x_assum `finally _ _ _ = _` mp_tac >>
    simp[finally_def, AllCaseEqs(), pop_scope_def, return_def, raise_def,
         bind_def, ignore_bind_def] >>
    rpt strip_tac >> gvs[] >>
    TRY (rename1 `try _ _ _ = (_, s_try)` >>
         irule preserves_immutables_dom_trans >> qexists_tac `s_try` >>
         conj_tac
         >- (qpat_x_assum `try _ _ _ = _` mp_tac >>
             PURE_REWRITE_TAC [ignore_bind_def] >>
             simp[try_def, bind_def, return_def, AllCaseEqs(),
                  handle_loop_exception_def, raise_def] >>
             rpt strip_tac >> gvs[return_def, raise_def] >>
             TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
             first_x_assum drule >> simp[] >> strip_tac >>
             BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def])
         >- (irule preserves_immutables_dom_eq >> simp[]) >> NO_TAC) >>
    qpat_x_assum `try _ _ _ = _` mp_tac >>
    PURE_REWRITE_TAC [ignore_bind_def] >>
    simp[try_def, bind_def, return_def, AllCaseEqs(),
         handle_loop_exception_def, raise_def] >>
    rpt strip_tac >> gvs[return_def, raise_def] >>
    TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
    first_x_assum drule >> simp[] >> strip_tac >>
    BasicProvers.EVERY_CASE_TAC >> gvs[return_def, raise_def]
  ]
QED

(* ----- Case 33: eval_expr (IfExp e e' e'') ----- *)
Theorem case_IfExp_imm_dom[local]:
  ∀cx e e' e''.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'. eval_expr cx e'' st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' tv t. eval_expr cx e s'' = (INL tv,t) ⇒
       ∀st res st'. eval_expr cx e' st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (IfExp _ e e' e'') st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       switch_BoolV_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  (* Derive unconditional IHs for e' and e'' *)
  `∀st res st'. eval_expr cx e' st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by metis_tac[] >>
  `∀st res st'. eval_expr cx e'' st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by metis_tac[] >>
  Cases_on `tv = Value (BoolV T)` >>
  gvs[raise_def, preserves_immutables_dom_refl] >>
  Cases_on `tv = Value (BoolV F)` >>
  gvs[raise_def, preserves_immutables_dom_refl]
QED

(* ----- Subscript helper lemmas ----- *)

(* Subgoal 1: success path - res' branches into value or storage read.
   Need to show preserves_immutables_dom cx s_e2 st'
   where s_e2 is the state after eval_expr e2. *)
Theorem subscript_helper_success_path[local]:
  ∀cx s_cab s_es st' tv1 v2 res' res.
    s_cab.immutables = s_es.immutables ⇒
    lift_sum (evaluate_subscript (get_tenv cx) arr_tv tv1 v2) s_cab = (INL res', s_es) ⇒
    (case res' of
       INL v => return v
     | INR (is_transient,slot,tv) =>
       do
         v <- read_storage_slot cx is_transient slot tv;
         return (Value v)
       od) s_es = (res, st') ⇒
    preserves_immutables_dom cx s_cab st'
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_eq >>
  gvs[lift_sum_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `res'` >> gvs[return_def] >>
  rename1 `INR trip` >> PairCases_on `trip` >>
  gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac read_storage_slot_immutables
QED

(* Subgoal 2: evaluate_subscript returns INR (error) -
   need preserves_immutables_dom cx st s_e2
   (chaining st → s_e1 → s_e2 via e1 and e2 IHs) *)
Theorem subscript_helper_eval_sub_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 tv2 v2 s_gv s_es e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    s_gv.immutables = s_e2.immutables ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INL tv2, s_e2) ⇒
    get_Value tv2 s_e2 = (INL v2, s_gv) ⇒
    (case evaluate_subscript (get_tenv cx) arr_tv tv1 v2 of
       INL v => return v
     | INR e => raise (Error e)) s_gv = (INR e', s_es) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Subgoal 3: evaluate_subscript returns INR (error) -
   need preserves_immutables_dom cx s_e2 s_es *)
Theorem subscript_helper_eval_sub_err_bwd[local]:
  ∀cx s_e2 s_gv s_es tv1 tv2 v2 e'.
    s_gv.immutables = s_e2.immutables ⇒
    get_Value tv2 s_e2 = (INL v2, s_gv) ⇒
    (case evaluate_subscript (get_tenv cx) arr_tv tv1 v2 of
       INL v => return v
     | INR e => raise (Error e)) s_gv = (INR e', s_es) ⇒
    preserves_immutables_dom cx s_e2 s_es
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_eq >>
  Cases_on `evaluate_subscript (get_tenv cx) arr_tv tv1 v2` >> gvs[raise_def, return_def]
QED

(* Subgoal 6: get_Value returns INR (error) -
   need preserves_immutables_dom cx st s_e2 *)
Theorem subscript_helper_get_value_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 tv2 s_gv e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    s_gv.immutables = s_e2.immutables ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INL tv2, s_e2) ⇒
    get_Value tv2 s_e2 = (INR e', s_gv) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* Subgoal 7: get_Value returns INR (error) -
   need preserves_immutables_dom cx s_e2 s_gv *)
Theorem subscript_helper_get_value_err_bwd[local]:
  ∀cx s_e2 s_gv tv2 e'.
    s_gv.immutables = s_e2.immutables ⇒
    get_Value tv2 s_e2 = (INR e', s_gv) ⇒
    preserves_immutables_dom cx s_e2 s_gv
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >> gvs[]
QED

(* Subgoal 8: eval_expr e2 returns INR (error) -
   need preserves_immutables_dom cx st s_e2 *)
Theorem subscript_helper_e2_err_fwd[local]:
  ∀cx e1 e2 st s_e1 s_e2 tv1 e'.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    (∀st' res st''. eval_expr cx e2 st' = (res,st'') ⇒
       preserves_immutables_dom cx st' st'') ⇒
    preserves_immutables_dom cx st s_e1 ⇒
    eval_expr cx e1 st = (INL tv1, s_e1) ⇒
    eval_expr cx e2 s_e1 = (INR e', s_e2) ⇒
    preserves_immutables_dom cx st s_e2
Proof
  rpt strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s_e1` >>
  conj_tac >- gvs[] >>
  first_x_assum drule >> simp[]
QED

(* ----- Case 36: eval_expr (Subscript e1 e2) ----- *)
Theorem case_Subscript_imm_dom[local]:
  ∀cx e1 e2.
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv1 t. eval_expr cx e1 s'' = (INL tv1,t) ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Subscript _ e1 e2) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def,
       lift_option_def, lift_sum_def, sum_CASE_rator] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >>
  imp_res_tac lift_option_type_same_state >>
  imp_res_tac check_array_bounds_state >>
  imp_res_tac lift_sum_state >>
  imp_res_tac read_storage_slot_immutables >>
  gvs[] >>
  (* Derive unconditional e2 IH *)
  `∀st res st'. eval_expr cx e2 st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by metis_tac[] >>
  (* All remaining goals: chain st → s'' → s'³' with IHs, rest by eq *)
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- gvs[] >>
       irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       conj_tac >- gvs[] >>
       irule preserves_immutables_dom_eq >> gvs[] >> NO_TAC) >>
  (* Storage read case: decompose the triple v2' and chain *)
  TRY (PairCases_on `v2'` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
       imp_res_tac read_storage_slot_immutables >> gvs[]) >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s'³'` >>
       conj_tac >- gvs[] >>
       irule preserves_immutables_dom_eq >> gvs[] >> NO_TAC) >>
  gvs[]
QED

(* ----- Case 37: eval_expr (Attribute e id) ----- *)
Theorem case_Attribute_imm_dom[local]:
  ∀cx e id.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Attribute _ e id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[preserves_immutables_dom_eq] >>
  Cases_on `evaluate_attribute sv id` >>
  gvs[return_def, raise_def, preserves_immutables_dom_eq]
QED

(* ----- Case 39: eval_expr (Pop bt) ----- *)
Theorem case_Pop_imm_dom[local]:
  ∀cx bt.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Pop _ bt) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       lift_option_def, lift_option_type_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Chain through eval_base_target state s'' *)
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  conj_tac >- gvs[] >>
  (* Now case-split on x = (loc, sbs) and unfold the do block *)
  PairCases_on `x` >>
  gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  (* assign_target: s'' -> s_at *)
  imp_res_tac (cj 1 assign_target_imm_dom_any) >>
  imp_res_tac get_Value_immutables >> imp_res_tac materialise_state >> gvs[] >>
  irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
  irule preserves_immutables_dom_eq >>
  gvs[] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[return_def, raise_def]
QED

(* ----- Case 41: eval_expr (Call Send es drv) ----- *)
Theorem case_Send_imm_dom[local]:
  ∀cx es drv.
    (∀s'' x t. type_check (LENGTH es = 2) "Send args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Call _ Send es drv) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def, check_def, type_check_def, assert_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  (* Simplify conditional IH *)
  RULE_ASSUM_TAC (REWRITE_RULE [check_def, type_check_def, assert_def, return_def]) >>
  gvs[] >>
  (* Resolve case expressions on dest_AddressV/dest_NumV *)
  TRY BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def] >>
  TRY BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def] >>
  imp_res_tac transfer_value_immutables >> gvs[] >>
  first_x_assum drule >>
  metis_tac[preserves_immutables_dom_trans, preserves_immutables_dom_eq]
QED

(* ----- Case 45: eval_exprs (e::es) ----- *)
Theorem case_eval_exprs_cons_imm_dom[local]:
  ∀cx e es.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       preserves_immutables_dom cx st st') ∧
    (∀s'' tv t s'³' v t'.
       eval_expr cx e s'' = (INL tv,t) ∧ materialise cx tv s'³' = (INL v,t') ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_exprs cx (e::es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  imp_res_tac materialise_state >> gvs[] >>
  (* materialise succeeded: chain st -> s'' -> s'⁴' *)
  TRY (irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       conj_tac >- gvs[] >> NO_TAC) >>
  qpat_x_assum `∀s''. _` (qspecl_then [`st`, `tv`, `s''`, `s''`, `v''`, `s''`] mp_tac) >>
  simp[] >> disch_then drule >> strip_tac >>
  irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
  gvs[]
QED

(* ----- Case: eval_target (BaseTarget bt) ----- *)
Theorem case_BaseTarget_imm_dom[local]:
  ∀cx bt.
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_target cx (BaseTarget bt) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  PairCases_on `x` >>
  gvs[return_def]
QED

(* ----- Case: eval_base_target (NameTarget id) ----- *)
Theorem case_NameTarget_imm_dom[local]:
  ∀cx id.
    ∀st res st'.
      eval_base_target cx (NameTarget id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def, raise_def] >>
  rpt strip_tac >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num id) st.scopes)` >>
  gvs[return_def, raise_def]
QED

(* ----- Case: eval_base_target (TopLevelNameTarget id) ----- *)
Theorem case_TopLevelNameTarget_imm_dom[local]:
  ∀cx src_id_opt id.
    ∀st res st'.
      eval_base_target cx (TopLevelNameTarget (src_id_opt,id)) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  Cases_on `get_module_code cx src_id_opt` >> simp[return_def, raise_def] >>
  Cases_on `is_immutable_decl (string_to_num id) x` >> simp[return_def]
QED

(* ----- Case: eval_base_target (AttributeTarget bt id) ----- *)
Theorem case_AttributeTarget_imm_dom[local]:
  ∀cx bt id.
    (∀st res st'.
       eval_base_target cx bt st = (res,st') ⇒
       preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_base_target cx (AttributeTarget bt id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl]
QED

(* ----- Case: eval_expr (Name id) ----- *)
Theorem case_Name_imm_dom[local]:
  ∀cx id.
    ∀st res st'.
      eval_expr cx (Name _ id) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >>
  Cases_on `lookup_scopes_val (string_to_num id) st.scopes` >>
  gvs[return_def, raise_def]
QED

(* ----- Case: eval_expr (Builtin bt es) ----- *)
Theorem case_Builtin_imm_dom[local]:
  ∀cx ty bt es.
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) ∧ bt ≠ Len ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ∧
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' =
       (INL x,t) ∧ bt = Len ⇒
       ∀st res st'.
         eval_expr cx (HD es) st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (Builtin ty bt es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  Cases_on `bt = Len` >> gvs[] >>
  (* bt = Len branch: eval_expr (HD es) then toplevel_array_length *)
  TRY (gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
       imp_res_tac toplevel_array_length_state >> gvs[] >>
       irule preserves_immutables_dom_trans >> qexists_tac `s''` >>
       gvs[preserves_immutables_dom_eq] >>
       first_x_assum (qspec_then `st` mp_tac) >>
       simp[check_def, type_check_def, assert_def, return_def] >> NO_TAC) >>
  (* bt ≠ Len branch *)
  `∀st res st'. eval_exprs cx es st = (res,st') ⇒
     preserves_immutables_dom cx st st'` by
    (first_x_assum (qspec_then `st` mp_tac) >>
     simp[check_def, type_check_def, assert_def, return_def]) >>
  gvs[bind_def, AllCaseEqs(), return_def, raise_def, get_accounts_def] >>
  Cases_on `evaluate_builtin cx s'³'.accounts ty bt vs` >>
  gvs[return_def, raise_def]
QED

(* ----- Case: eval_expr (TypeBuiltin tb typ es) ----- *)
Theorem case_TypeBuiltin_imm_dom[local]:
  ∀cx tb typ es.
    (∀s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es))
         "TypeBuiltin args" s'' = (INL x,t) ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    ∀st res st'.
      eval_expr cx (TypeBuiltin _ tb typ es) st = (res, st') ⇒
      preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >>
  PURE_REWRITE_TAC [ignore_bind_def] >>
  simp[bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, lift_sum_def] >>
  rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >>
       gvs[return_def, raise_def]) >>
  first_x_assum (qspec_then `st` mp_tac) >>
  simp[check_def, type_check_def, assert_def, return_def]
QED

Theorem check_same_state[local]:
  check b msg s = (r, s') ⇒ s' = s
Proof
  rw[check_def, type_check_def, assert_def]
QED

Theorem type_check_same_state[local]:
  type_check b msg s = (r, s') ⇒ s' = s
Proof
  rw[type_check_def, assert_def]
QED

(* Helper: inner pipeline after run_ext_call result destructuring *)
Theorem extcall_inner_pipeline_imm_dom[local]:
  ∀cx drv tenv ret_type success returnData accounts' tStorage' s res s'.
    (success ∧ returnData = [] ∧ IS_SOME drv ⇒
       ∀st res st'. eval_expr cx (THE drv) st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    do
      x <- check success "ExtCall reverted";
      x <- update_accounts (K accounts');
      x <- update_transient (K tStorage');
      if returnData = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
      else
        do
          ret_val <-
            lift_sum_runtime (evaluate_abi_decode_return tenv ret_type returnData);
          return (Value ret_val)
        od
    od s = (res, s') ⇒
    preserves_immutables_dom cx s s'
Proof
  rw[bind_def, ignore_bind_def, check_def, type_check_def, assert_def,
     update_accounts_def, update_transient_def, return_def,
     raise_def, lift_sum_def, lift_sum_runtime_def]
  \\ rpt strip_tac \\ gvs[AllCaseEqs(), preserves_immutables_dom_refl]
  \\ TRY (irule preserves_immutables_dom_eq
          >> Cases_on `evaluate_abi_decode_return tenv ret_type returnData`
          >> gvs[return_def, raise_def] >> NO_TAC)
  \\ irule preserves_immutables_dom_trans
  \\ qmatch_asmsub_abbrev_tac `eval_expr cx (THE drv) s_mid`
  \\ qexists_tac `s_mid`
  \\ conj_tac
  \\ TRY (irule preserves_immutables_dom_eq >> simp[Abbr`s_mid`] >> NO_TAC)
  \\ first_x_assum match_mp_tac \\ metis_tac[]
QED

(* Helper: full ExtCall pipeline preserves immutables dom *)
Theorem extcall_pipeline_preserves_imm_dom[local]:
  ∀cx drv func_name arg_types ret_type target_addr value_opt arg_vals
     caller txParams s res s'.
    (∀ts calldata accounts tStorage success returnData accounts' tStorage'.
       get_self_code cx = SOME ts ⇒
       build_ext_calldata (type_env ts) func_name arg_types arg_vals =
         SOME calldata ⇒
       run_ext_call caller target_addr calldata value_opt accounts tStorage
         txParams = SOME (success, returnData, accounts', tStorage') ⇒
       success ∧ returnData = [] ∧ IS_SOME drv ⇒
       ∀st res st'. eval_expr cx (THE drv) st = (res,st') ⇒
         preserves_immutables_dom cx st st') ⇒
    do
      ts <- lift_option (get_self_code cx) "ExtCall get_self_code";
      calldata <-
        lift_option
          (build_ext_calldata (type_env ts) func_name arg_types arg_vals)
          "ExtCall build_calldata";
      accounts <- get_accounts;
      tStorage <- get_transient_storage;
      result <-
        lift_option
          (run_ext_call caller target_addr calldata value_opt accounts
             tStorage txParams) "ExtCall run failed";
      (λ(success,returnData,accounts',tStorage').
           do
             x <- check success "ExtCall reverted";
             x <- update_accounts (K accounts');
             x <- update_transient (K tStorage');
             if returnData = [] ∧ IS_SOME drv then eval_expr cx (THE drv)
             else
               do
                 ret_val <-
                   lift_sum_runtime
                     (evaluate_abi_decode_return (type_env ts) ret_type
                        returnData);
                 return (Value ret_val)
               od
           od) result
    od s = (res, s') ⇒
    preserves_immutables_dom cx s s'
Proof
  rpt strip_tac
  \\ qpat_x_assum `do _ od _ = _` mp_tac
  \\ simp[bind_def, ignore_bind_def, lift_option_def, lift_option_type_def,
          get_accounts_def, get_transient_storage_def,
          return_def, raise_def]
  \\ Cases_on `get_self_code cx`
  \\ simp[return_def, raise_def, preserves_immutables_dom_refl]
  \\ Cases_on `build_ext_calldata (type_env x) func_name arg_types arg_vals`
  \\ simp[return_def, raise_def, preserves_immutables_dom_refl]
  \\ Cases_on `run_ext_call caller target_addr x' value_opt s.accounts
                 s.tStorage txParams`
  \\ simp[return_def, raise_def, preserves_immutables_dom_refl]
  \\ PairCases_on `x''` \\ simp[]
  \\ strip_tac
  \\ irule extcall_inner_pipeline_imm_dom
  \\ first_assum (irule_at Any)
  \\ rpt strip_tac
  \\ first_x_assum irule \\ simp[]
  \\ qexists_tac `s.accounts` \\ qexists_tac `x''2`
  \\ qexists_tac `s.tStorage` \\ qexists_tac `x''3`
  \\ gvs[]
QED


Theorem intcall_args_length_sub[local]:
  ∀given expected defaults.
    given ≤ expected ⇒
    (expected − given ≤ defaults ⇔ expected ≤ given + defaults)
Proof
  decide_tac
QED

Theorem intcall_default_frame_imm_dom_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd prev res sdfl.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut stup nr stup2
        args sstup dflts sstup2 ret body s3 x1 t3 s4 vs0 t4 es0 cx0.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut = FST tup0 ∧ stup = SND tup0 ∧ (nr ⇔ FST stup) ∧
      stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
      dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
      body = SND sstup2 ∧
      type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      es0 = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
      cx0 = cx with stk updated_by CONS (src_id_opt,fn) ⇒
      ∀st res st'. eval_exprs cx0 es0 st = (res,st') ⇒
        preserves_immutables_dom cx0 st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    type_check
      (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
       LENGTH (FST (SND (SND tup))) ≤
         LENGTH es + LENGTH (FST (SND (SND (SND tup)))))
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts =
      DROP (LENGTH (FST (SND (SND (SND tup)))) −
            (LENGTH (FST (SND (SND tup))) − LENGTH es))
           (FST (SND (SND (SND tup)))) ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (res,sdfl) ⇒
    preserves_immutables_dom cxd sevl sdfl
Proof
  rpt strip_tac \\
  irule intcall_default_frame_imm_dom \\
  qexists_tac `needed_dflts` \\
  qexists_tac `prev` \\
  qexists_tac `res` \\
  simp[] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
      LENGTH (FST (SND (SND tup))) − LENGTH es ≤
        LENGTH (FST (SND (SND (SND tup)))))
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (`(LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
       LENGTH (FST (SND (SND tup))) − LENGTH es ≤
         LENGTH (FST (SND (SND (SND tup))))) =
      (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
       LENGTH (FST (SND (SND tup))) ≤
         LENGTH es + LENGTH (FST (SND (SND (SND tup)))))` by
       simp[intcall_args_length_sub] \\
     pop_assum SUBST1_TAC \\
     qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` ACCEPT_TAC) \\
  first_assum (qspecl_then
    [`ih_check_s`, `xrec`, `srec`,
     `ih_mod_s`, `ts`, `smod`,
     `ih_fun_s`, `tup`, `sfun`,
     `FST tup`, `SND tup`, `FST (SND tup)`,
     `SND (SND tup)`, `FST (SND (SND tup))`,
     `SND (SND (SND tup))`, `FST (SND (SND (SND tup)))`,
     `SND (SND (SND (SND tup)))`,
     `FST (SND (SND (SND (SND tup))))`,
     `SND (SND (SND (SND (SND tup))))`,
     `ih_len_s`, `xlen`, `slen`,
     `ih_args_s`, `vs`, `sevl`,
     `needed_dflts`, `cxd`] mp_tac) \\
  simp[] \\
  disch_then drule \\
  simp[]
QED

Theorem intcall_tail_body_provider_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     default_s dflt_vs sdfl get_scope_s prev get_scope_t mut stup nr stup2
     args sstup dflts sstup2 ret ss.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env t6 s7 prev0 t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      eval_exprs cxd0 needed_dflts0 s5 = (INL dflt_vs0,t5) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s6 = (INL env,t6) ∧
      get_scopes s7 = (INL prev0,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 =
        (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st res st'. eval_stmts cx0 ss0 st = (res,st') ⇒
        preserves_immutables_dom cx0 st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
    ss = SND sstup2 ∧
    type_check
      (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    eval_exprs cxd needed_dflts default_s = (INL dflt_vs,sdfl) ∧
    get_scopes get_scope_s = (INL prev,get_scope_t) ⇒
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt strip_tac \\
  simp[intcall_tail_body_provider_def] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (`(LENGTH es ≤ LENGTH args ∧
       LENGTH args − LENGTH es ≤ LENGTH dflts) =
      (LENGTH es ≤ LENGTH args ∧
       LENGTH args ≤ LENGTH es + LENGTH dflts)` by
       simp[intcall_args_length_sub] \\
     pop_assum SUBST1_TAC \\
     qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` ACCEPT_TAC) \\
  qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
                  args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
                  needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env0 t6
                  s7 prev0 t7 s8 rtv0 t8 is_view s9 lk0 t9 s10 cx0 t10.
                  type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
                  _ ⇒ ∀st0 res0 st1.
                    eval_stmts cx0 ss0 st0 = (res0,st1) ⇒
                    preserves_immutables_dom cx0 st0 st1`
    (qspecl_then
      [`ih_check_s`, `xrec`, `srec`,
       `ih_mod_s`, `ts`, `smod`,
       `ih_fun_s`, `tup`, `sfun`,
       `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
       `ret`, `ss`, `ih_len_s`, `xlen`, `slen`,
       `ih_args_s`, `vs`, `sevl`, `needed_dflts`, `cxd`,
       `default_s`, `dflt_vs`, `sdfl`, `get_tenv cx`, `sdfl`, `env`, `s_bind`,
       `get_scope_s`, `prev`, `get_scope_t`, `s_bind`, `rtv`, `s_eval`,
       `mut = View ∨ mut = Pure`, `s_eval`, `lk`, `s_lock`, `s_lock`, `cx'`,
       `s_push`] mp_tac) \\
  simp[] \\
  disch_then irule \\
  simp[]
QED

Theorem intcall_post_default_setup_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     default_s dflt_vs sdfl get_scope_s prev get_scope_t mut stup nr stup2
     args sstup dflts sstup2 ret ss.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ⇒
      ∀st res st'. eval_exprs cxd0 needed_dflts0 st = (res,st') ⇒
        preserves_immutables_dom cxd0 st st') ∧
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env t6 s7 prev0 t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      eval_exprs cxd0 needed_dflts0 s5 = (INL dflt_vs0,t5) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s6 = (INL env,t6) ∧
      get_scopes s7 = (INL prev0,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 =
        (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st res st'. eval_stmts cx0 ss0 st = (res,st') ⇒
        preserves_immutables_dom cx0 st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
    ss = SND sstup2 ∧
    type_check
      (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (INL dflt_vs,sdfl) ∧
    eval_exprs cxd needed_dflts default_s = (INL dflt_vs,sdfl) ∧
    get_scopes get_scope_s = (INL prev,get_scope_t) ⇒
    preserves_immutables_dom cxd sevl sdfl ∧
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt gen_tac \\
  strip_tac \\
  conj_tac
  >- (match_mp_tac (Q.SPECL
        [`cx`, `src_id_opt`, `fn`, `es`,
         `ih_check_s`, `ih_mod_s`, `ih_fun_s`, `ih_len_s`, `ih_args_s`,
         `xrec`, `srec`, `ts`, `smod`, `tup`, `sfun`, `xlen`, `slen`,
         `vs`, `sevl`, `needed_dflts`, `cxd`, `prev`, `INL dflt_vs`, `sdfl`]
        intcall_default_frame_imm_dom_from_generated_ih) \\
      conj_tac >- FIRST_ASSUM ACCEPT_TAC \\
      qpat_x_assum
        `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
            args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4
            needed_dflts0 cxd0. _` kall_tac \\
      simp[] \\
      gvs[type_check_def, assert_def] \\
      qhdtm_x_assum`type_check`mp_tac >>
      simp_tac(srw_ss())[type_check_def, assert_def] >>
      strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
      decide_tac) \\
  qspecl_then
    [`cx`, `src_id_opt`, `fn`, `es`,
     `ih_check_s`, `ih_mod_s`, `ih_fun_s`, `ih_len_s`, `ih_args_s`,
     `xrec`, `srec`, `ts`, `smod`, `tup`, `sfun`, `xlen`, `slen`,
     `vs`, `sevl`, `needed_dflts`, `cxd`,
     `default_s`, `dflt_vs`, `sdfl`, `get_scope_s`, `prev`, `get_scope_t`,
     `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
     `ret`, `ss`]
    mp_tac intcall_tail_body_provider_from_generated_ih \\
  simp[] \\
  disch_then irule \\
  simp[] \\
  rpt strip_tac \\
  qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
                  args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
                  needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env0 t6
                  s7 prev0 t7 s8 rtv0 t8 is_view s9 lk0 t9 s10 cx0 t10.
                  _ ⇒ ∀st0 res0 st1.
                    eval_stmts cx0 ss0 st0 = (res0,st1) ⇒
                    preserves_immutables_dom cx0 st0 st1`
    (qspecl_then
      [`s0`, `()`, `t0`, `s1`, `ts0`, `t1`, `s2`, `tup0`, `t2`,
       `FST tup0`, `SND tup0`, `FST (SND tup0)`, `SND (SND tup0)`,
       `FST (SND (SND tup0))`, `SND (SND (SND tup0))`,
       `FST (SND (SND (SND tup0)))`, `SND (SND (SND (SND tup0)))`,
       `FST (SND (SND (SND (SND tup0))))`,
       `SND (SND (SND (SND (SND tup0))))`, `s3`, `()`, `t3`,
       `s4`, `vs0`, `t4`,
       `DROP
          (LENGTH (FST (SND (SND (SND tup0)))) −
           (LENGTH (FST (SND (SND tup0))) − LENGTH es))
          (FST (SND (SND (SND tup0))))`,
       `cx with stk updated_by CONS (src_id_opt,fn)`,
       `s5`, `dflt_vs0`, `t5`, `get_tenv cx`, `s6`, `env`, `t6`,
       `s7`, `prev0`, `t7`, `s8`, `rtv`, `t8`,
       `FST tup0 = View ∨ FST tup0 = Pure`, `s9`, `()`, `t9`,
       `s10`, `cx0`, `t10`] mp_tac) \\
  simp[] \\
  disch_then irule \\
  simp[]
QED

Theorem finally_set_scopes_eval_exprs_success[local]:
  ∀cxd es prev sevl vs sdfl.
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd es
       od)
      (set_scopes prev) sevl = (INL vs,sdfl) ⇒
    ∃pre.
      eval_exprs cxd es (sevl with scopes := [FEMPTY]) = (INL vs,pre) ∧
      sdfl = pre with scopes := prev ∧
      get_scopes sdfl = (INL prev,sdfl)
Proof
  rpt strip_tac \\
  qpat_x_assum `finally _ _ _ = _` mp_tac \\
  simp[finally_def, bind_def, ignore_bind_def, set_scopes_def,
       return_def, raise_def, get_scopes_def] \\
  Cases_on `eval_exprs cxd es (sevl with scopes := [FEMPTY])` \\
  Cases_on `q` \\
  simp[return_def, raise_def, get_scopes_def] \\
  rpt strip_tac \\
  gvs[] \\
  qexists_tac `r` \\
  simp[get_scopes_def, return_def]
QED

Theorem type_check_intcall_args_length_sub[local]:
  type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
    msg s = (INL x,t) ==>
  type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
    msg s = (INL x,t)
Proof
  simp[type_check_def, assert_def] \\
  IF_CASES_TAC \\ simp[] \\
  decide_tac
QED

Theorem intcall_live_post_default_setup_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     dflt_vs sdfl prev mut stup nr stup2 args sstup dflts sstup2 ret ss.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ⇒
      ∀st res st'. eval_exprs cxd0 needed_dflts0 st = (res,st') ⇒
        preserves_immutables_dom cxd0 st st') ∧
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
        needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env t6 s7 prev0 t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      eval_exprs cxd0 needed_dflts0 s5 = (INL dflt_vs0,t5) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s6 = (INL env,t6) ∧
      get_scopes s7 = (INL prev0,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 =
        (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st res st'. eval_stmts cx0 ss0 st = (res,st') ⇒
        preserves_immutables_dom cx0 st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
    ss = SND sstup2 ∧
    type_check
      (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (INL dflt_vs,sdfl) ⇒
    preserves_immutables_dom cxd sevl sdfl ∧
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt gen_tac \\ strip_tac \\
  drule finally_set_scopes_eval_exprs_success \\
  disch_then (qx_choose_then `pre_sdfl` strip_assume_tac) \\
  conj_tac
  >- (qspecl_then
        [`cx`, `src_id_opt`, `fn`, `es`,
         `ih_check_s`, `ih_mod_s`, `ih_fun_s`, `ih_len_s`, `ih_args_s`,
         `xrec`, `srec`, `ts`, `smod`, `tup`, `sfun`, `xlen`, `slen`,
         `vs`, `sevl`, `needed_dflts`, `cxd`, `prev`, `INL dflt_vs`, `sdfl`]
        irule intcall_default_frame_imm_dom_from_generated_ih \\
      MAP_EVERY qexists_tac
        [`cx`, `dflt_vs`, `es`, `fn`, `ih_args_s`, `ih_check_s`, `ih_fun_s`,
         `ih_len_s`, `ih_mod_s`, `needed_dflts`, `prev`, `sfun`, `slen`,
         `smod`, `src_id_opt`, `srec`, `ts`, `tup`, `vs`, `xlen`, `xrec`] \\
      rpt conj_tac \\
      FIRST [first_assum ACCEPT_TAC,
        qpat_x_assum `stup = SND tup` (fn h_stup =>
        qpat_x_assum `stup2 = SND stup` (fn h_stup2 =>
        qpat_x_assum `args = FST stup2` (fn h_args =>
        qpat_x_assum `sstup = SND stup2` (fn h_sstup =>
        qpat_x_assum `dflts = FST sstup` (fn h_dflts =>
        qpat_x_assum `needed_dflts = DROP _ _` (fn h_needed =>
          PURE_REWRITE_TAC [GSYM h_stup, GSYM h_stup2, GSYM h_args,
                            GSYM h_sstup, GSYM h_dflts] \\
          FIRST [ACCEPT_TAC h_needed, first_assum ACCEPT_TAC]))))))]) \\
  simp[intcall_tail_body_provider_def] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac \\
     simp[type_check_def, assert_def] \\
     IF_CASES_TAC \\ simp[] \\
     decide_tac) \\
  qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20
                  args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4
                  needed_dflts0 cxd0 s5 dflt_vs0 t5 all_tenv s6 env0 t6
                  s7 prev0 t7 s8 rtv0 t8 is_view s9 lk0 t9 s10 cx0 t10.
                  type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
                  _ ⇒ ∀st0 res0 st1.
                    eval_stmts cx0 ss0 st0 = (res0,st1) ⇒
                    preserves_immutables_dom cx0 st0 st1`
    (qspecl_then
      [`ih_check_s`, `xrec`, `srec`,
       `ih_mod_s`, `ts`, `smod`,
       `ih_fun_s`, `tup`, `sfun`,
       `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
       `ret`, `ss`, `ih_len_s`, `xlen`, `slen`,
       `ih_args_s`, `vs`, `sevl`, `needed_dflts`, `cxd`,
       `sevl with scopes := [FEMPTY]`, `dflt_vs`, `pre_sdfl`, `get_tenv cx`,
       `sdfl`, `env`, `s_bind`, `sdfl`, `prev`, `sdfl`, `s_bind`, `rtv`,
       `s_eval`, `mut = View ∨ mut = Pure`, `s_eval`, `lk`, `s_lock`,
       `s_lock`, `cx'`, `s_push`] mp_tac) \\
  simp[] \\
  disch_then irule \\
  simp[]
QED

Theorem intcall_case_live_post_default_setup_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     dflt_vs sdfl prev mut stup nr stup2 args sstup dflts sstup2 ret ss.
    (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
        body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
      (INL ts,t') ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts)
        "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
      stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
      args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
      sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
      type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
        "IntCall args length" s'⁵' = (INL x',t'³') ∧
      eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
      es' = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
      cx' = cx with stk updated_by CONS (src_id_opt,fn) ⇒
      ∀st res st'.
        eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
    (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
        ss s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵'
        all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹'
        s'¹²' cx' t'¹⁰'.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
      (INL ts,t') ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts)
        "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
      stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
      args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
      sstup2 = SND sstup ∧ ret = FST sstup2 ∧ ss = SND sstup2 ∧
      type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
        "IntCall args length" s'⁵' = (INL x',t'³') ∧
      eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
      needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
      cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
      eval_exprs cxd needed_dflts s'⁷' = (INL dflt_vs,t'⁵') ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args (vs ⧺ dflt_vs))
        "IntCall bind_arguments" s'⁸' = (INL env,t'⁶') ∧
      get_scopes s'⁹' = (INL prev,t'⁷') ∧
      lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'¹⁰' =
      (INL rtv,t'⁸') ∧ (is_view ⇔ mut = View ∨ mut = Pure) ∧
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot =>
           acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s'¹¹' = (INL lk,t'⁹') ∧
      push_function (src_id_opt,fn) env cx s'¹²' = (INL cx',t'¹⁰') ⇒
      ∀st res st'.
        eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
    (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧ ss = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (INL dflt_vs,sdfl) ⇒
    preserves_immutables_dom cxd sevl sdfl ∧
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt gen_tac \\
  strip_tac \\
  pop_assum $ mk_asm "default_case_ih" \\
  strip_tac \\
  pop_assum $ mk_asm "body_case_ih" \\
  strip_tac \\
  qspecl_then
    [`cx`, `src_id_opt`, `fn`, `es`,
     `ih_check_s`, `ih_mod_s`, `ih_fun_s`, `ih_len_s`, `ih_args_s`,
     `xrec`, `srec`, `ts`, `smod`, `tup`, `sfun`, `xlen`, `slen`,
     `vs`, `sevl`, `needed_dflts`, `cxd`, `dflt_vs`, `sdfl`, `prev`,
     `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
     `ret`, `ss`]
    mp_tac intcall_live_post_default_setup_from_generated_ih \\
  (impl_tac >-
     (conj_tac >- (asm "default_case_ih" mp_tac \\ simp[]) \\
      conj_tac >- (asm "body_case_ih" mp_tac \\ simp[]) \\
      simp[])) \\
  simp[]
QED

Theorem intcall_default_frame_to_caller_imm_dom[local]:
  ∀cx src_id_opt fn st0 sevl sdfl.
    preserves_immutables_dom cx st0 sevl ∧
    preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) sevl sdfl ⇒
    preserves_immutables_dom cx st0 sdfl
Proof
  rpt strip_tac \\
  irule preserves_immutables_dom_trans \\
  qexists_tac `sevl` \\
  conj_tac >- simp[] \\
  irule (iffLR preserves_immutables_dom_txn_eq) \\
  qexists_tac `cx with stk updated_by CONS (src_id_opt,fn)` \\
  simp[]
QED

Theorem intcall_tail_after_finally_cast_imm_dom[local]:
  !cx src_id_opt fn mut nr ss prev env st0 sevl r r2 q r' retv res st'.
    preserves_immutables_dom cx st0 sevl /\
    preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) sevl r /\
    r2.immutables = r.immutables /\
    (!st res st'.
       eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss st = (res,st') ==>
       preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) st st') /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) ss;
               return NoneV od) handle_function)
      (do pop_function prev;
          if nr /\ mut <> View /\ mut <> Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return () od)
      (r2 with scopes := [env]) = (q,r') /\
    (case q of
     | INL v =>
         do crv <- lift_option_type (safe_cast retv v) "IntCall cast ret";
            return (Value crv) od r'
     | INR e => (INR e,r')) = (res,st') ==>
    preserves_immutables_dom cx st0 st'
Proof
  rpt strip_tac >>
  `preserves_immutables_dom cx r2 r'` by
    (qspecl_then [`cx`, `src_id_opt`, `fn`, `mut`, `nr`, `ss`, `prev`, `env`, `r2`, `q`, `r'`]
       mp_tac intcall_body_finally_release_imm_dom_use >>
     simp[] >>
     disch_then irule >>
     simp[]) >>
  `preserves_immutables_dom cx st0 r2` by
    (irule preserves_immutables_dom_trans >>
     qexists_tac `r` >>
     conj_tac >- metis_tac[intcall_default_frame_to_caller_imm_dom] >>
     irule preserves_immutables_dom_eq >> simp[]) >>
  Cases_on `q` >> gvs[bind_def, return_def] >-
    (Cases_on `lift_option_type (safe_cast retv x) "IntCall cast ret" r'` >>
     gvs[] >>
     imp_res_tac lift_option_type_same_state >>
     gvs[return_def, raise_def] >>
     Cases_on `q` >> gvs[] >>
     irule preserves_immutables_dom_trans >>
     qexists_tac `r2` >> simp[]) >>
  irule preserves_immutables_dom_trans >>
  qexists_tac `r2` >> simp[]
QED

Theorem post_default_intcall_tail_imm_dom[local]:
  ∀cx src_id_opt fn mut nr args ret ss vs dflt_vs st0 sevl sdfl prev res st'.
    preserves_immutables_dom cx st0 sevl ∧
    preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) sevl sdfl ∧
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl ∧
    post_default_intcall_tail cx src_id_opt fn mut nr args ret ss vs dflt_vs prev sdfl = (res,st') ⇒
    preserves_immutables_dom cx st0 st'
Proof
  rpt strip_tac \\
  qpat_x_assum `post_default_intcall_tail _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac \\
  simp[post_default_intcall_tail_unfold, bind_def] \\
  BasicProvers.TOP_CASE_TAC \\
  FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac \\
  reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ gvs[] \\
      metis_tac[intcall_default_frame_to_caller_imm_dom]) \\
  BasicProvers.TOP_CASE_TAC \\
  FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac \\
  reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ gvs[] \\
      metis_tac[intcall_default_frame_to_caller_imm_dom]) \\
  rewrite_tac[bind_def, ignore_bind_def, COND_RATOR] \\
  BasicProvers.TOP_CASE_TAC \\
  `r''.immutables = sdfl.immutables` by
    (Cases_on `nr` \\ gvs[return_def, raise_def] \\
     Cases_on `cx.nonreentrant_slot` \\ gvs[return_def, raise_def] \\
     imp_res_tac acquire_nonreentrant_lock_immutables \\ gvs[]) \\
  reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ gvs[] \\
      irule preserves_immutables_dom_trans \\
      qexists_tac `r` \\
      conj_tac
      >- (irule preserves_immutables_dom_trans \\
          qexists_tac `sevl` \\
          conj_tac >- simp[] \\
          irule (iffLR preserves_immutables_dom_txn_eq) \\
          qexists_tac `cx with stk updated_by CONS (src_id_opt,fn)` \\
          simp[]) \\
      irule preserves_immutables_dom_eq \\ simp[]) \\
  rewrite_tac[bind_def] \\
  BasicProvers.TOP_CASE_TAC \\
  gvs[push_function_def, return_def] \\
  qpat_x_assum `intcall_tail_body_provider _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o SRULE[intcall_tail_body_provider_def]) \\
  disch_then (qspecl_then
    [`x`, `r`, `x'`, `r`, `r''`,
     `cx with stk updated_by CONS (src_id_opt,fn)`, `r'' with scopes := [x]`]
    mp_tac) \\
  simp[push_function_def, return_def] \\
  strip_tac \\
  BasicProvers.TOP_CASE_TAC \\
  gvs[] \\
  strip_tac \\
  qpat_x_assum `_ ⇒ ∀st res st'. eval_stmts _ _ st = (res,st') ⇒ _` mp_tac \\
  (impl_tac >- (Cases_on `nr` \\ gvs[return_def, raise_def] \\ Cases_on `cx.nonreentrant_slot` \\ gvs[return_def, raise_def])) \\
  strip_tac \\
  qspecl_then [`cx`, `src_id_opt`, `fn`, `mut`, `nr`, `ss`, `prev`, `x`,
                `st0`, `sevl`, `r`, `r''`, `q`, `r'`, `x'`, `res`, `st'`]
    mp_tac intcall_tail_after_finally_cast_imm_dom \\
  simp[] \\
  disch_then irule \\
  simp[ignore_bind_def]
QED
(* ===== Helper lemmas for ExtCall/IntCall cases ===== *)

Theorem case_IntCall_imm_dom[local]:
  ∀cx src_id_opt fn es vs st res st'.
  eval_expr cx (Call _ (IntCall (src_id_opt,fn)) es vs) st = (res,st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
      body' s'⁵' x' t'³'.
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
    stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
    args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ⇒
    ∀st res st'.
      eval_exprs cx es st = (res,st') ⇒ preserves_immutables_dom cx st st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
      body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
    stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
    args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ body' = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ∧
    eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
    es' = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cx' = cx with stk updated_by CONS (src_id_opt,fn) ⇒
    ∀st res st'.
      eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
  (∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret
      ss s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵'
      all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹'
      s'¹²' cx' t'¹⁰'.
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
    (INL ts,t') ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" s'⁴' = (INL tup,t'') ∧ mut = FST tup ∧
    stup = SND tup ∧ (nr ⇔ FST stup) ∧ stup2 = SND stup ∧
    args = FST stup2 ∧ sstup = SND stup2 ∧ dflts = FST sstup ∧
    sstup2 = SND sstup ∧ ret = FST sstup2 ∧ ss = SND sstup2 ∧
    type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
      "IntCall args length" s'⁵' = (INL x',t'³') ∧
    eval_exprs cx es s'⁶' = (INL vs,t'⁴') ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    eval_exprs cxd needed_dflts s'⁷' = (INL dflt_vs,t'⁵') ∧
    all_tenv = get_tenv cx ∧
    lift_option_type (bind_arguments all_tenv args (vs ⧺ dflt_vs))
      "IntCall bind_arguments" s'⁸' = (INL env,t'⁶') ∧
    get_scopes s'⁹' = (INL prev,t'⁷') ∧
    lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret" s'¹⁰' =
    (INL rtv,t'⁸') ∧ (is_view ⇔ mut = View ∨ mut = Pure) ∧
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot =>
         acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) s'¹¹' = (INL lk,t'⁹') ∧
    push_function (src_id_opt,fn) env cx s'¹²' = (INL cx',t'¹⁰') ⇒
    ∀st res st'.
      eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st') ⇒
  preserves_immutables_dom cx st st'
Proof
  rpt strip_tac
  \\ qpat_x_assum `eval_expr _ _ _ = _` mp_tac
  \\ simp[Once evaluate_def, bind_def, LET_THM]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  (* Peel: check recursion *)
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ rw[preserves_immutables_dom_refl])
  (* Peel: lift_option get_module_code *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  (* Peel: lift_option lookup_callable_function *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ gvs[preserves_immutables_dom_refl])
  (* Peel: check args length *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac))
      \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  (* eval_exprs cx es: specialize first IH using drule_all *)
  \\ BasicProvers.TOP_CASE_TAC
  \\ last_x_assum $ funpow 2 drule_then drule
  \\ simp_tac std_ss []
  \\ disch_then $ drule_then drule
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ strip_tac \\ gvs[])
  (* eval_exprs cx es succeeded *)
  \\ simp[get_scopes_def, return_def]
  \\ strip_tac
  \\ qpat_x_assum `bind _ _ _ = _` mp_tac
  \\ simp[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt strip_tac \\
      qpat_x_assum `r'⁵' = st'` (SUBST1_TAC o SYM) \\
      irule preserves_immutables_dom_trans \\
      qexists_tac `r'⁴'` \\
      conj_tac >- first_assum ACCEPT_TAC \\
      irule (iffLR preserves_immutables_dom_txn_eq) \\
      qexists_tac `cx with stk updated_by CONS (src_id_opt,fn)` \\ simp[] \\
      irule intcall_default_frame_imm_dom \\
      qexists_tac `DROP (LENGTH (FST (SND (SND (SND x'')))) -
                       (LENGTH (FST (SND (SND x''))) - LENGTH es))
                      (FST (SND (SND (SND x''))))` \\
      qexists_tac `r'⁴'.scopes` \\
      qexists_tac `INR y` \\
      simp[] \\
      conj_tac
      >- (rpt strip_tac \\
          drule type_check_intcall_args_length_sub \\
          strip_tac \\
          qpat_x_assum `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
                           _ ⇒ ∀st res st'.
                             eval_exprs cx' es' st = (res,st') ⇒ _`
            (qspecl_then
              [`st`, `x`, `r`, `st`, `x'`, `r'`, `st`, `x''`, `r''`,
               `FST x''`, `SND x''`, `FST (SND x'')`, `SND (SND x'')`,
               `FST (SND (SND x''))`, `SND (SND (SND x''))`,
               `FST (SND (SND (SND x'')))`,
               `SND (SND (SND (SND x'')))`,
               `FST (SND (SND (SND (SND x''))))`,
               `SND (SND (SND (SND (SND x''))))`,
               `st`, `x'³'`, `r'³'`, `st`, `x'⁴'`, `r'⁴'`,
               `DROP (LENGTH (FST (SND (SND (SND x'')))) −
                      (LENGTH (FST (SND (SND x''))) − LENGTH es))
                     (FST (SND (SND (SND x''))))`,
               `cx with stk updated_by CONS (src_id_opt,fn)`] mp_tac) \\
          impl_tac >-
            (rpt conj_tac \\
             FIRST [REFL_TAC, first_assum ACCEPT_TAC]) \\
          disch_then drule \\
          strip_tac \\
          first_assum ACCEPT_TAC) \\
      qpat_x_assum `finally _ _ _ = _` mp_tac \\
      simp[ignore_bind_def])
  (* INL branch: fold remaining pipeline through post_default_intcall_tail *)
  \\ qpat_assum
       `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
          _ ⇒ ∀st res st'. eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st'`
       (mk_asm "default_imm_ih")
  \\ qpat_assum
       `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret ss s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵' all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹' s'¹²' cx' t'¹⁰'.
          _ ⇒ ∀st res st'. eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st'`
       (mk_asm "body_imm_ih")
  \\ qspecl_then
       [`cx`, `src_id_opt`, `fn`, `es`,
        `st`, `st`, `st`, `st`, `st`,
        `x`, `r`, `x'`, `r'`, `x''`, `r''`, `x'³'`, `r'³'`,
        `x'⁴'`, `r'⁴'`,
        `DROP (LENGTH (FST (SND (SND (SND x'')))) -
               (LENGTH (FST (SND (SND x''))) - LENGTH es))
              (FST (SND (SND (SND x''))))`,
        `cx with stk updated_by CONS (src_id_opt,fn)`,
        `x'⁵'`, `r'⁵'`, `r'⁴'.scopes`,
        `FST x''`, `SND x''`, `FST (SND x'')`, `SND (SND x'')`,
        `FST (SND (SND x''))`, `SND (SND (SND x''))`,
        `FST (SND (SND (SND x'')))`, `SND (SND (SND (SND x'')))`,
        `FST (SND (SND (SND (SND x''))))`,
        `SND (SND (SND (SND (SND x''))))`]
       mp_tac intcall_case_live_post_default_setup_from_generated_ih
  \\ (impl_tac >- (asm "default_imm_ih" mp_tac \\ simp[]))
  \\ (impl_tac >- (asm "body_imm_ih" mp_tac \\ simp[]))
  \\ strip_tac
  \\ qpat_x_assum `default_imm_ih :- _` kall_tac
  \\ qpat_x_assum `body_imm_ih :- _` kall_tac
  \\ TRY (qpat_x_assum
       `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret body' s'⁵' x' t'³' s'⁶' vs t'⁴' es' cx'.
          _ ⇒ ∀st res st'. eval_exprs cx' es' st = (res,st') ⇒ preserves_immutables_dom cx' st st'`
       kall_tac)
  \\ TRY (qpat_x_assum
       `∀s'' x t s'³' ts t' s'⁴' tup t'' mut stup nr stup2 args sstup dflts sstup2 ret ss s'⁵' x' t'³' s'⁶' vs t'⁴' needed_dflts cxd s'⁷' dflt_vs t'⁵' all_tenv s'⁸' env t'⁶' s'⁹' prev t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹' s'¹²' cx' t'¹⁰'.
          _ ⇒ ∀st res st'. eval_stmts cx' ss st = (res,st') ⇒ preserves_immutables_dom cx' st st'`
       kall_tac)
  \\ `preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) r'⁴' r'⁵' ∧
       intcall_tail_body_provider cx src_id_opt fn (FST x'') (FST (SND x''))
         (FST (SND (SND x''))) (FST (SND (SND (SND (SND x'')))))
         (SND (SND (SND (SND (SND x''))))) x'⁴' x'⁵' r'⁵'` by
       (first_x_assum irule \\ rpt conj_tac \\ simp[ignore_bind_def])
  \\ simp[GSYM post_default_intcall_tail_unfold]
  \\ rpt strip_tac
  \\ qspecl_then
       [`cx`, `src_id_opt`, `fn`, `FST x''`, `FST (SND x'')`,
        `FST (SND (SND x''))`, `FST (SND (SND (SND (SND x''))))`,
        `SND (SND (SND (SND (SND x''))))`, `x'⁴'`, `x'⁵'`,
        `st`, `r'⁴'`, `r'⁵'`, `r'⁴'.scopes`, `res`, `st'`]
       mp_tac post_default_intcall_tail_imm_dom
  \\ simp[]
  \\ disch_then irule
  \\ simp[post_default_intcall_tail_unfold, bind_def, ignore_bind_def]
QED

(* ===== Main Mutual Induction ===== *)

Theorem intcall_mutual_default_frame_imm_dom_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd prev res sdfl.
    (∀s'' x t s'³' ts0 t' s'⁴' tup0 t'' mut stup nr stup2 args sstup dflts sstup2 ret
        body' s'⁵' x' t'³' s'⁶' vs0 t'⁴' es' cx' s'⁷' prev0 t'⁵' s'⁸' x'' t'⁶'.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
        (INL ts0,t') ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s'⁴' = (INL tup0,t'') ∧
      mut = FST tup0 ∧ stup = SND tup0 ∧ (nr ⇔ FST stup) ∧
      stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
      dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
      body' = SND sstup2 ∧
      type_check (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
        "IntCall args length" s'⁵' = (INL x',t'³') ∧
      eval_exprs cx es s'⁶' = (INL vs0,t'⁴') ∧
      es' = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
      cx' = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s'⁷' = (INL prev0,t'⁵') ∧
      set_scopes [FEMPTY] s'⁸' = (INL x'',t'⁶') ⇒
      ∀st res st'. eval_exprs cx' es' st = (res,st') ⇒
        preserves_immutables_dom cx' st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    type_check
      (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
       LENGTH (FST (SND (SND tup))) ≤
         LENGTH es + LENGTH (FST (SND (SND (SND tup)))))
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts =
      DROP (LENGTH (FST (SND (SND (SND tup)))) −
            (LENGTH (FST (SND (SND tup))) − LENGTH es))
           (FST (SND (SND (SND tup)))) ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    get_scopes sevl = (INL prev,sevl) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (res,sdfl) ⇒
    preserves_immutables_dom cxd sevl sdfl
Proof
  rpt strip_tac \\
  irule intcall_default_frame_imm_dom \\
  qexists_tac `needed_dflts` \\
  qexists_tac `prev` \\
  qexists_tac `res` \\
  simp[] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH (FST (SND (SND tup))) ∧
      LENGTH (FST (SND (SND tup))) − LENGTH es ≤
        LENGTH (FST (SND (SND (SND tup)))))
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac \\
     simp[type_check_def, assert_def] \\
     IF_CASES_TAC \\ simp[] \\
     decide_tac) \\
  first_assum (qspecl_then
    [`ih_check_s`, `xrec`, `srec`,
     `ih_mod_s`, `ts`, `smod`,
     `ih_fun_s`, `tup`, `sfun`,
     `FST tup`, `SND tup`, `FST (SND tup)`,
     `SND (SND tup)`, `FST (SND (SND tup))`,
     `SND (SND (SND tup))`, `FST (SND (SND (SND tup)))`,
     `SND (SND (SND (SND tup)))`,
     `FST (SND (SND (SND (SND tup))))`,
     `SND (SND (SND (SND (SND tup))))`,
     `ih_len_s`, `xlen`, `slen`,
     `ih_args_s`, `vs`, `sevl`,
     `needed_dflts`, `cxd`,
     `sevl`, `prev`, `sevl`, `sevl`, `()`,
     `sevl with scopes := [FEMPTY]`] mp_tac) \\
  simp[get_scopes_def, set_scopes_def, return_def] \\
  disch_then drule \\
  simp[]
QED

Theorem intcall_mutual_tail_body_provider_from_generated_ih[local]:
  ∀cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
     xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd
     dflt_vs sdfl prev mut stup nr stup2 args sstup dflts sstup2 ret ss.
    (∀s'' x t s'³' ts0 t' s'⁴' tup0 t'' mut0 stup0 nr0 stup20
        args0 sstup0 dflts0 sstup20 ret0 ss0 s'⁵' x' t'³' s'⁶' vs0 t'⁴'
        needed_dflts0 cxd0 s'⁷' prev0 t'⁵' s'⁸' dflt_vs0 t'⁶'
        all_tenv s'⁹' env t'⁷' s'¹⁰' rtv t'⁸' is_view s'¹¹' lk t'⁹'
        s'¹²' cx' t'¹⁰'.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s'³' =
        (INL ts0,t') ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s'⁴' = (INL tup0,t'') ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧
      stup20 = SND stup0 ∧ args0 = FST stup20 ∧ sstup0 = SND stup20 ∧
      dflts0 = FST sstup0 ∧ sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧
      ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s'⁵' = (INL x',t'³') ∧
      eval_exprs cx es s'⁶' = (INL vs0,t'⁴') ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s'⁷' = (INL prev0,t'⁵') ∧
      finally
        (do
           set_scopes [FEMPTY];
           eval_exprs cxd0 needed_dflts0
         od)
        (set_scopes prev0) s'⁸' = (INL dflt_vs0,t'⁶') ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s'⁹' = (INL env,t'⁷') ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s'¹⁰' =
        (INL rtv,t'⁸') ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s'¹¹' = (INL lk,t'⁹') ∧
      push_function (src_id_opt,fn) env cx s'¹²' = (INL cx',t'¹⁰') ⇒
      ∀st res st'. eval_stmts cx' ss0 st = (res,st') ⇒
        preserves_immutables_dom cx' st st') ∧
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) ∧
    mut = FST tup ∧ stup = SND tup ∧ (nr ⇔ FST stup) ∧
    stup2 = SND stup ∧ args = FST stup2 ∧ sstup = SND stup2 ∧
    dflts = FST sstup ∧ sstup2 = SND sstup ∧ ret = FST sstup2 ∧
    ss = SND sstup2 ∧
    type_check
      (LENGTH es ≤ LENGTH args ∧ LENGTH args ≤ LENGTH es + LENGTH dflts)
      "IntCall args length" ih_len_s = (INL xlen,slen) ∧
    eval_exprs cx es ih_args_s = (INL vs,sevl) ∧
    needed_dflts = DROP (LENGTH dflts − (LENGTH args − LENGTH es)) dflts ∧
    cxd = cx with stk updated_by CONS (src_id_opt,fn) ∧
    get_scopes sevl = (INL prev,sevl) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (INL dflt_vs,sdfl) ⇒
    intcall_tail_body_provider cx src_id_opt fn mut nr args ret ss vs dflt_vs sdfl
Proof
  rpt strip_tac \\
  simp[intcall_tail_body_provider_def] \\
  rpt strip_tac \\
  `type_check
     (LENGTH es ≤ LENGTH args ∧ LENGTH args − LENGTH es ≤ LENGTH dflts)
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac \\
     simp[type_check_def, assert_def] \\
     IF_CASES_TAC \\ simp[] \\
     decide_tac) \\
  qpat_assum `∀s'' x t s'³' ts0 t' s'⁴' tup0 t'' mut0 stup0 nr0 stup20
                  args0 sstup0 dflts0 sstup20 ret0 ss0 s'⁵' x' t'³'
                  s'⁶' vs0 t'⁴' needed_dflts0 cxd0 s'⁷' prev0 t'⁵'
                  s'⁸' dflt_vs0 t'⁶' all_tenv s'⁹' env0 t'⁷' s'¹⁰'
                  rtv0 t'⁸' is_view s'¹¹' lk0 t'⁹' s'¹²' cx0 t'¹⁰'.
                  type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) ∧
                  _ ⇒ ∀st0 res0 st1.
                    eval_stmts cx0 ss0 st0 = (res0,st1) ⇒
                    preserves_immutables_dom cx0 st0 st1`
    (qspecl_then
      [`ih_check_s`, `xrec`, `srec`,
       `ih_mod_s`, `ts`, `smod`,
       `ih_fun_s`, `tup`, `sfun`,
       `mut`, `stup`, `nr`, `stup2`, `args`, `sstup`, `dflts`, `sstup2`,
       `ret`, `ss`, `ih_len_s`, `xlen`, `slen`,
       `ih_args_s`, `vs`, `sevl`, `needed_dflts`, `cxd`,
       `sevl`, `prev`, `sevl`, `sevl`, `dflt_vs`, `sdfl`, `get_tenv cx`,
       `sdfl`, `env`, `s_bind`, `s_bind`, `rtv`, `s_eval`,
       `mut = View ∨ mut = Pure`, `s_eval`, `lk`, `s_lock`, `s_lock`, `cx'`,
       `s_push`] mp_tac) \\
  simp[get_scopes_def, return_def] \\
  disch_then irule \\
  simp[]
QED


Theorem intcall_mutual_live_default_frame_imm_dom[local]:
  ∀cx src_id_opt fn es check_res mod_code fn_tup len_res arg_vs default_vs
     st0 s_args sdfl.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0
        s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      es0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s5 = (INL prev0,t5) ∧
      set_scopes [FEMPTY] s6 = (INL x2,t6) ⇒
      ∀st0 res0 st1. eval_exprs cxd0 es0 st0 = (res0,st1) ⇒ preserves_immutables_dom cxd0 st0 st1) ⇒
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" st0 = (INL check_res,st0) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" st0 = (INL mod_code,st0) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn mod_code) "IntCall lookup_function" st0 =
      (INL fn_tup,st0) ∧
    type_check
      (LENGTH es ≤ LENGTH (FST (SND (SND fn_tup))) ∧
       LENGTH (FST (SND (SND fn_tup))) ≤ LENGTH es + LENGTH (FST (SND (SND (SND fn_tup)))))
      "IntCall args length" st0 = (INL len_res,st0) ∧
    eval_exprs cx es st0 = (INL arg_vs,s_args) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
           (DROP (LENGTH (FST (SND (SND (SND fn_tup)))) −
                  (LENGTH (FST (SND (SND fn_tup))) − LENGTH es))
                 (FST (SND (SND (SND fn_tup)))))
       od)
      (set_scopes s_args.scopes) s_args = (INL default_vs,sdfl) ⇒
    preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) s_args sdfl
Proof
  rpt strip_tac \\
  qspecl_then
    [`cx`, `src_id_opt`, `fn`, `es`,
     `st0`, `st0`, `st0`, `st0`, `st0`,
     `check_res`, `st0`, `mod_code`, `st0`, `fn_tup`, `st0`, `len_res`, `st0`,
     `arg_vs`, `s_args`,
     `DROP (LENGTH (FST (SND (SND (SND fn_tup)))) −
            (LENGTH (FST (SND (SND fn_tup))) − LENGTH es))
           (FST (SND (SND (SND fn_tup))))`,
     `cx with stk updated_by CONS (src_id_opt,fn)`,
     `s_args.scopes`, `INL default_vs`, `sdfl`]
    irule intcall_mutual_default_frame_imm_dom_from_generated_ih \\
  conj_tac
  >- REFL_TAC \\
  conj_tac
  >- simp[get_scopes_def, return_def] \\
  MAP_EVERY qexists_tac
    [`arg_vs`, `check_res`, `default_vs`, `es`, `fn_tup`, `len_res`,
     `mod_code`, `st0`] \\
  rpt conj_tac \\
  FIRST [REFL_TAC, first_assum ACCEPT_TAC]
QED

Theorem intcall_mutual_live_tail_body_provider[local]:
  ∀cx src_id_opt fn es check_res mod_code fn_tup len_res arg_vs default_vs
     st0 s_args sdfl.
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0
        s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s5 = (INL prev0,t5) ∧
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed_dflts0 od) (set_scopes prev0) s6 = (INL dflt_vs0,t6) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0)) "IntCall bind_arguments" s7 = (INL env,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 = (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then case cx.nonreentrant_slot of NONE => raise (Error (TypeError "nonreentrant slot missing"))
                 | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st0 res0 st1. eval_stmts cx0 ss0 st0 = (res0,st1) ⇒ preserves_immutables_dom cx0 st0 st1) ⇒
    type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" st0 = (INL check_res,st0) ∧
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" st0 = (INL mod_code,st0) ∧
    lift_option_type (lookup_callable_function cx.in_deploy fn mod_code) "IntCall lookup_function" st0 =
      (INL fn_tup,st0) ∧
    type_check
      (LENGTH es ≤ LENGTH (FST (SND (SND fn_tup))) ∧
       LENGTH (FST (SND (SND fn_tup))) ≤ LENGTH es + LENGTH (FST (SND (SND (SND fn_tup)))))
      "IntCall args length" st0 = (INL len_res,st0) ∧
    eval_exprs cx es st0 = (INL arg_vs,s_args) ∧
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
           (DROP (LENGTH (FST (SND (SND (SND fn_tup)))) −
                  (LENGTH (FST (SND (SND fn_tup))) − LENGTH es))
                 (FST (SND (SND (SND fn_tup)))))
       od)
      (set_scopes s_args.scopes) s_args = (INL default_vs,sdfl) ⇒
    intcall_tail_body_provider cx src_id_opt fn (FST fn_tup) (FST (SND fn_tup))
      (FST (SND (SND fn_tup))) (FST (SND (SND (SND (SND fn_tup)))))
      (SND (SND (SND (SND (SND fn_tup))))) arg_vs default_vs sdfl
Proof
  rpt strip_tac \\
  qspecl_then
    [`cx`, `src_id_opt`, `fn`, `es`,
     `st0`, `st0`, `st0`, `st0`, `st0`,
     `check_res`, `st0`, `mod_code`, `st0`, `fn_tup`, `st0`, `len_res`, `st0`,
     `arg_vs`, `s_args`,
     `DROP (LENGTH (FST (SND (SND (SND fn_tup)))) −
            (LENGTH (FST (SND (SND fn_tup))) − LENGTH es))
           (FST (SND (SND (SND fn_tup))))`,
     `cx with stk updated_by CONS (src_id_opt,fn)`,
     `default_vs`, `sdfl`, `s_args.scopes`,
     `FST fn_tup`, `SND fn_tup`, `FST (SND fn_tup)`, `SND (SND fn_tup)`,
     `FST (SND (SND fn_tup))`, `SND (SND (SND fn_tup))`,
     `FST (SND (SND (SND fn_tup)))`, `SND (SND (SND (SND fn_tup)))`,
     `FST (SND (SND (SND (SND fn_tup))))`,
     `SND (SND (SND (SND (SND fn_tup))))`]
    mp_tac intcall_mutual_tail_body_provider_from_generated_ih \\
  simp[get_scopes_def] \\
  PURE_REWRITE_TAC[return_def] \\
  (impl_tac >-
     (qpat_x_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7 s8 rtv t8 is_view s9 lk t9 s10 cx0 t10. _ ⇒ ∀st0 res0 st1. eval_stmts cx0 ss0 st0 = (res0,st1) ⇒ preserves_immutables_dom cx0 st0 st1`
        mp_tac \\
      PURE_REWRITE_TAC[get_scopes_def, return_def] \\
      simp[])) \\
  simp[]
QED

Theorem case_IntCall_imm_dom_from_mutual_ih[local]:
  ∀cx src_id_opt fn es vs st res st'.
    eval_expr cx (Call _ (IntCall (src_id_opt,fn)) es vs) st = (res,st') ⇒
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ⇒
      ∀st0 res0 st1. eval_exprs cx es st0 = (res0,st1) ⇒ preserves_immutables_dom cx st0 st1) ⇒
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0
        s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ body0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      es0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s5 = (INL prev0,t5) ∧
      set_scopes [FEMPTY] s6 = (INL x2,t6) ⇒
      ∀st0 res0 st1. eval_exprs cxd0 es0 st0 = (res0,st1) ⇒ preserves_immutables_dom cxd0 st0 st1) ⇒
    (∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0
        s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7
        s8 rtv t8 is_view s9 lk t9 s10 cx0 t10.
      type_check (¬MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) ∧
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 = (INL ts0,t1) ∧
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0) "IntCall lookup_function" s2 = (INL tup0,t2) ∧
      mut0 = FST tup0 ∧ stup0 = SND tup0 ∧ (nr0 ⇔ FST stup0) ∧ stup20 = SND stup0 ∧
      args0 = FST stup20 ∧ sstup0 = SND stup20 ∧ dflts0 = FST sstup0 ∧
      sstup20 = SND sstup0 ∧ ret0 = FST sstup20 ∧ ss0 = SND sstup20 ∧
      type_check (LENGTH es ≤ LENGTH args0 ∧ LENGTH args0 − LENGTH es ≤ LENGTH dflts0)
        "IntCall args length" s3 = (INL x1,t3) ∧
      eval_exprs cx es s4 = (INL vs0,t4) ∧
      needed_dflts0 = DROP (LENGTH dflts0 − (LENGTH args0 − LENGTH es)) dflts0 ∧
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) ∧
      get_scopes s5 = (INL prev0,t5) ∧
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed_dflts0 od) (set_scopes prev0) s6 = (INL dflt_vs0,t6) ∧
      all_tenv = get_tenv cx ∧
      lift_option_type (bind_arguments all_tenv args0 (vs0 ++ dflt_vs0)) "IntCall bind_arguments" s7 = (INL env,t7) ∧
      lift_option_type (evaluate_type all_tenv ret0) "IntCall eval ret" s8 = (INL rtv,t8) ∧
      (is_view ⇔ mut0 = View ∨ mut0 = Pure) ∧
      (if nr0 then case cx.nonreentrant_slot of NONE => raise (Error (TypeError "nonreentrant slot missing"))
                 | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ()) s9 = (INL lk,t9) ∧
      push_function (src_id_opt,fn) env cx s10 = (INL cx0,t10) ⇒
      ∀st0 res0 st1. eval_stmts cx0 ss0 st0 = (res0,st1) ⇒ preserves_immutables_dom cx0 st0 st1) ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac
  \\ qpat_x_assum `eval_expr _ _ _ = _` mp_tac
  \\ simp[Once evaluate_def, bind_def, LET_THM]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ rw[preserves_immutables_dom_refl])
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ gvs[preserves_immutables_dom_refl])
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule type_check_same_state, drule check_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ rw[] \\ gvs[preserves_immutables_dom_refl])
  \\ BasicProvers.TOP_CASE_TAC
  \\ qpat_x_assum
       `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3.
          _ ⇒ ∀st0 res0 st1. eval_exprs cx es st0 = (res0,st1) ⇒ preserves_immutables_dom cx st0 st1`
       (funpow 2 drule_then drule)
  \\ simp_tac std_ss []
  \\ disch_then $ drule_then drule
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(last_x_assum(qspec_then`ARB`kall_tac)) \\ strip_tac \\ gvs[])
  \\ simp[get_scopes_def, return_def]
  \\ strip_tac
  \\ qpat_x_assum `bind _ _ _ = _` mp_tac
  \\ simp[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt strip_tac \\
      rpt (qpat_x_assum `_ = st` SUBST_ALL_TAC) \\
      irule intcall_default_frame_to_caller_imm_dom \\
      qexists_tac `fn` \\
      qexists_tac `r'⁴'` \\
      qexists_tac `src_id_opt` \\
      simp[] \\
      qspecl_then
        [`cx`, `src_id_opt`, `fn`, `es`,
         `st`, `st`, `st`, `st`, `st`,
         `()`, `st`, `x'`, `st`, `x''`, `st`, `()`, `st`, `x'⁴'`, `r'⁴'`,
         `DROP (LENGTH (FST (SND (SND (SND x'')))) -
                (LENGTH (FST (SND (SND x''))) - LENGTH es))
               (FST (SND (SND (SND x''))))`,
         `cx with stk updated_by CONS (src_id_opt,fn)`, `r'⁴'.scopes`,
         `INR y`, `r'⁵'`]
        mp_tac intcall_mutual_default_frame_imm_dom_from_generated_ih \\
      (impl_tac >-
         (conj_tac >- (qpat_x_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6. _ ⇒ ∀st0 res0 st1. eval_exprs cxd0 es0 st0 = (res0,st1) ⇒ preserves_immutables_dom cxd0 st0 st1` mp_tac \\ simp[]) \\
          TRY (qpat_x_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6. _` kall_tac) \\
          TRY (qpat_x_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7 s8 rtv t8 is_view s9 lk t9 s10 cx0 t10. _` kall_tac) \\
          rpt conj_tac \\ simp[get_scopes_def, set_scopes_def, return_def,
                                type_check_def, assert_def, ignore_bind_def] \\
          TRY decide_tac)) \\
      simp[])
  \\ `preserves_immutables_dom (cx with stk updated_by CONS (src_id_opt,fn)) r'⁴' r'⁵'` by
       (qspecl_then
          [`cx`, `src_id_opt`, `fn`, `es`, `()`, `x'`, `x''`, `()`, `x'⁴'`,
           `x'⁵'`, `st`, `r'⁴'`, `r'⁵'`]
          mp_tac intcall_mutual_live_default_frame_imm_dom \\
        (impl_tac >-
           (qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 body0 s3 x1 t3 s4 vs0 t4 es0 cxd0 s5 prev0 t5 s6 x2 t6. _ ⇒ ∀st0 res0 st1. eval_exprs cxd0 es0 st0 = (res0,st1) ⇒ preserves_immutables_dom cxd0 st0 st1`
              mp_tac \\
            simp[])) \\
        (impl_tac >-
           (simp[get_scopes_def, return_def, type_check_def, assert_def,
                 ignore_bind_def] \\
            TRY decide_tac)) \\
        simp[])
  \\ `intcall_tail_body_provider cx src_id_opt fn (FST x'') (FST (SND x''))
        (FST (SND (SND x''))) (FST (SND (SND (SND (SND x'')))))
        (SND (SND (SND (SND (SND x''))))) x'⁴' x'⁵' r'⁵'` by
       (qspecl_then
          [`cx`, `src_id_opt`, `fn`, `es`, `()`, `x'`, `x''`, `()`, `x'⁴'`,
           `x'⁵'`, `st`, `r'⁴'`, `r'⁵'`]
          mp_tac intcall_mutual_live_tail_body_provider \\
        (impl_tac >-
           (qpat_assum `∀s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0 sstup0 dflts0 sstup20 ret0 ss0 s3 x1 t3 s4 vs0 t4 needed_dflts0 cxd0 s5 prev0 t5 s6 dflt_vs0 t6 all_tenv s7 env t7 s8 rtv t8 is_view s9 lk t9 s10 cx0 t10. _ ⇒ ∀st0 res0 st1. eval_stmts cx0 ss0 st0 = (res0,st1) ⇒ preserves_immutables_dom cx0 st0 st1`
              mp_tac \\
            simp[])) \\
        (impl_tac >-
           (simp[get_scopes_def, return_def, type_check_def, assert_def,
                 ignore_bind_def] \\
            TRY decide_tac)) \\
        simp[])
  \\ simp[GSYM post_default_intcall_tail_unfold]
  \\ rpt strip_tac
  \\ qspecl_then
       [`cx`, `src_id_opt`, `fn`, `FST x''`, `FST (SND x'')`,
        `FST (SND (SND x''))`, `FST (SND (SND (SND (SND x''))))`,
        `SND (SND (SND (SND (SND x''))))`, `x'⁴'`, `x'⁵'`,
        `st`, `r'⁴'`, `r'⁵'`, `r'⁴'.scopes`, `res`, `st'`]
       mp_tac post_default_intcall_tail_imm_dom
  \\ simp[]
  \\ disch_then irule
  \\ simp[post_default_intcall_tail_unfold, bind_def, ignore_bind_def]
QED

Theorem raw_call_callback_preserves_immutables_dom[local]:
  ∀cx flags result st res st'.
    ((λ(success,returnData,accounts',tStorage').
        do
          x <- update_accounts (K accounts');
          x <- update_transient (K tStorage');
          if flags.rcf_revert_on_failure then
            do
              x <- assert success (Error (RuntimeError "raw_call reverted"));
              if flags.rcf_max_outsize = 0 then return (Value NoneV)
              else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData)))
            od
          else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
          else
            return
              (Value
                 (ArrayV (TupleV [BoolV success; BytesV (TAKE flags.rcf_max_outsize returnData)])))
        od) result st = (res,st')) ⇒
    preserves_immutables_dom cx st st'
Proof
  rpt strip_tac >>
  PairCases_on `result` >>
  qpat_x_assum `_ = (res,st')` mp_tac >>
  simp[update_accounts_def, update_transient_def, bind_def, ignore_bind_def,
      return_def, raise_def, assert_def, check_def, type_check_def,
      AllCaseEqs()] >>
  rpt IF_CASES_TAC >>
  simp[update_accounts_def, update_transient_def, bind_def, ignore_bind_def,
      return_def, raise_def, assert_def, check_def, type_check_def,
      AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  irule preserves_immutables_dom_eq >> gvs[]
QED

Theorem immutables_dom_mutual[local]:
  (∀cx s st res st'. eval_stmt cx s st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx ss st res st'. eval_stmts cx ss st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx it st res st'. eval_iterator cx it st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx g st res st'. eval_target cx g st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx gs st res st'. eval_targets cx gs st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒ preserves_immutables_dom cx st st')
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt strip_tac
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  >- (drule_all case_Return_SOME_imm_dom >> simp[])
  (* Raise RaiseBare *)
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  (* Raise RaiseUnreachable *)
  >- gvs[evaluate_def, raise_def, preserves_immutables_dom_refl]
  (* Raise (RaiseReason e): only eval_expr changes state *)
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), raise_def, return_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      imp_res_tac get_Value_state >> imp_res_tac lift_option_type_state >> gvs[])
  (* Assert e AssertBare / AssertUnreachable: only eval_expr changes state *)
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
      simp[switch_BoolV_def, return_def, raise_def] >>
      rpt IF_CASES_TAC >> simp[return_def, raise_def] >>
      rpt strip_tac >> gvs[])
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
      simp[switch_BoolV_def, return_def, raise_def] >>
      rpt IF_CASES_TAC >> simp[return_def, raise_def] >>
      rpt strip_tac >> gvs[])
  (* Assert e (AssertReason se): chain eval_expr e → eval_expr se *)
  >- (qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
      imp_res_tac get_Value_state >> gvs[] >>
      qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
      simp[switch_BoolV_def, return_def, raise_def] >>
      rpt IF_CASES_TAC >> simp[return_def, raise_def, bind_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      TRY (imp_res_tac get_Value_state >> imp_res_tac lift_option_type_state >> gvs[]) >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      first_x_assum drule_all >> strip_tac >>
      first_x_assum drule >> simp[])
  >- (drule_all case_Log_imm_dom >> simp[])
  >- (drule_all case_AnnAssign_imm_dom >> simp[])
  >- (drule_all case_Append_imm_dom >> simp[])
  >- (drule_all case_Assign_imm_dom >> simp[])
  >- (drule_all case_AugAssign_imm_dom >> simp[])
  >- (drule_all case_If_imm_dom >> simp[])
  >- (drule_all case_For_imm_dom >> simp[])
  >- (drule_all case_Expr_imm_dom >> simp[])
  >- (gvs[evaluate_def, return_def, preserves_immutables_dom_refl])
  >- (drule_all case_eval_stmts_cons_imm_dom >> simp[])
  >- (drule_all case_Array_imm_dom >> simp[])
  >- (drule_all case_Range_imm_dom >> simp[])
  >- (drule_all case_BaseTarget_imm_dom >> simp[])
  >- (qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
       rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
       first_x_assum irule >> first_assum (irule_at Any))
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (drule_all case_eval_targets_cons_imm_dom >> simp[])
  >- (drule_all case_NameTarget_imm_dom >> simp[])
  >- (drule_all case_TopLevelNameTarget_imm_dom >> simp[])
  >- (drule_all case_AttributeTarget_imm_dom >> simp[])
  >- (drule_all case_SubscriptTarget_imm_dom >> simp[])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (drule_all case_eval_for_cons_imm_dom >> simp[])
  >- (drule_all case_Name_imm_dom >> simp[])
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def] >> strip_tac >>
       imp_res_tac lookup_global_immutables >>
       irule preserves_immutables_dom_eq >> gvs[])
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def] >> strip_tac >>
       imp_res_tac lookup_flag_mem_immutables >>
       irule preserves_immutables_dom_eq >> gvs[])
  >- (drule_all case_IfExp_imm_dom >> simp[])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
       simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
            get_scopes_def, get_immutables_def, get_address_immutables_def,
            lift_option_def, lift_option_type_def, lift_sum_def, LET_THM, check_def, type_check_def, assert_def,
            ignore_bind_def, get_accounts_def, lift_sum_def,
            get_transient_storage_def, update_accounts_def, update_transient_def] >>
       rpt strip_tac >> gvs[preserves_immutables_dom_refl] >>
       first_x_assum irule >> first_assum (irule_at Any) >>
            simp[check_def, type_check_def, assert_def])
  >- (drule_all case_Subscript_imm_dom >> simp[])
  >- (drule_all case_Attribute_imm_dom >> simp[])
  >- (drule_all case_Builtin_imm_dom >> simp[])
  >- (drule_all case_Pop_imm_dom >> simp[])
  >- (drule_all case_TypeBuiltin_imm_dom >> simp[])
  >- (drule_all case_Send_imm_dom >> simp[])
  >- suspend "ExtCall"
  >- (drule_all case_IntCall_imm_dom_from_mutual_ih >> simp[])
  (* ===== Chain interaction builtins (unguarded eval_exprs IH) ===== *)
  (* All 5 cases: eval_exprs first, then pure/state ops that preserve immutables.
     Pattern: unfold, case-split, apply IH via drule, close failure paths,
     use transitivity + _eq for success path. *)
  (* RawCallTarget *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def,
           get_accounts_def, get_transient_storage_def, option_CASE_rator] >>
      rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      first_x_assum drule >> strip_tac >>
      TRY (gvs[] >> NO_TAC) >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule raw_call_callback_preserves_immutables_dom >>
      first_assum (irule_at Any))
  (* RawLog *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def,
           push_log_def, option_CASE_rator] >>
      rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      first_x_assum drule >> strip_tac >>
      TRY (gvs[] >> NO_TAC) >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule preserves_immutables_dom_eq >> gvs[])
  (* RawRevert *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, type_check_def, assert_def] >>
      rpt strip_tac >> gvs[] >>
      first_x_assum drule >> gvs[])
  (* SelfDestructTarget *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
           check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def,
           get_accounts_def, option_CASE_rator] >>
      rpt strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
      first_x_assum drule >> strip_tac >>
      TRY (gvs[] >> NO_TAC) >>
      imp_res_tac transfer_value_immutables >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule preserves_immutables_dom_eq >> gvs[])
  (* CreateTarget *)
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def] >>
      Cases_on `eval_exprs cx es st` >> Cases_on `q` >> simp[] >>
      strip_tac >>
      first_x_assum drule >> strip_tac >>
      drule eval_create_preserves_non_accounts >> strip_tac >>
      irule preserves_immutables_dom_trans >> first_assum (irule_at Any) >>
      irule preserves_immutables_dom_eq >> gvs[])
  >- gvs[evaluate_def, return_def, preserves_immutables_dom_refl]
  >- (drule_all case_eval_exprs_cons_imm_dom >> simp[])
QED

Resume immutables_dom_mutual[ExtCall]:
  rpt strip_tac
  \\ qpat_x_assum `eval_expr _ _ _ = _` mp_tac
  \\ simp[Once evaluate_def, bind_def, LET_THM]
  \\ Cases_on `eval_exprs cx es st` \\ Cases_on `q`
  \\ simp[return_def, raise_def, preserves_immutables_dom_refl]
  \\ strip_tac
  \\ irule preserves_immutables_dom_trans \\ qexists_tac `r`
  \\ conj_tac >- (last_x_assum match_mp_tac \\ simp[])
  \\ qpat_x_assum `do _ od _ = _` mp_tac
  \\ last_x_assum drule \\ strip_tac
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ drule type_check_same_state \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rw[] \\ rw[preserves_immutables_dom_refl])
  \\ BasicProvers.TOP_CASE_TAC
  \\ FIRST [drule lift_option_type_same_state, drule lift_option_same_state] \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[] \\ gvs[preserves_immutables_dom_refl] )
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ qmatch_asmsub_rename_tac`_ s1 = (_, s2)`
  \\ sg `s1 = s2`
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ gvs[CaseEq"bool", return_def, COND_RATOR, bind_def]
    \\ gvs[CaseEq"sum"]
    \\ gvs[CaseEq"prod"]
    \\ Cases_on `v` \\ gvs[]
    \\ TRY BasicProvers.FULL_CASE_TAC \\ gvs[]
    \\ TRY BasicProvers.FULL_CASE_TAC \\ gvs[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ gvs[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ gvs[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ gvs[]
    \\ TRY BasicProvers.TOP_CASE_TAC \\ gvs[]
    \\ imp_res_tac type_check_same_state
    \\ imp_res_tac lift_option_same_state
    \\ imp_res_tac lift_option_type_same_state
    \\ gvs[] )
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- rw[preserves_immutables_dom_refl]
  >> qmatch_asmsub_rename_tac`_ = (INL p,_)`
  \\ PairCases_on`p`
  \\ asm_simp_tac std_ss []
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ drule lift_option_type_same_state
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[] \\ gvs[preserves_immutables_dom_refl] )
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ qmatch_asmsub_rename_tac`_ s2 = (_, s3)`
  \\ sg `s2 = s3`
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ gvs[get_accounts_def, return_def] )
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- rw[preserves_immutables_dom_refl]
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ imp_res_tac check_state
  \\ rpt BasicProvers.VAR_EQ_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- ( rw[] \\ rw[preserves_immutables_dom_refl] )
  \\ BasicProvers.TOP_CASE_TAC
  \\ qmatch_asmsub_rename_tac`_ s3 = (_, s4)`
  \\ sg `s3 = s4`
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ gvs[get_transient_storage_def, return_def] )
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- rw[preserves_immutables_dom_refl]
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ drule lift_option_same_state
  \\ strip_tac
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    last_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[] \\ gvs[preserves_immutables_dom_refl] )
  >> qmatch_goalsub_rename_tac`_ p _ = _`
  >> PairCases_on`p`
  \\ asm_simp_tac std_ss []
  \\ last_x_assum drule \\ strip_tac
  \\ strip_tac
  \\ irule extcall_inner_pipeline_imm_dom
  \\ first_assum (irule_at Any)
  \\ rpt strip_tac
  \\ first_x_assum $ drule_then drule
  \\ gvs[ignore_bind_def]
  \\ disch_then $ funpow 5 drule_then drule
  \\ gvs[bind_def, CaseEq"prod", CaseEq"sum"]
  \\ gvs[update_accounts_def, update_transient_def, return_def,
         check_def, type_check_def, raise_def, assert_def]
QED

Finalise immutables_dom_mutual

(* ===== Main theorems ===== *)

Theorem eval_expr_preserves_immutables_addr_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED

Theorem eval_expr_preserves_immutables_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 8 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_base_target_preserves_immutables_addr_dom:
  ∀cx bt st res st'.
    eval_base_target cx bt st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED

Theorem eval_base_target_preserves_immutables_dom:
  ∀cx bt st res st'.
    eval_base_target cx bt st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 6 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_exprs_preserves_immutables_dom:
  ∀cx es st res st'.
    eval_exprs cx es st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 9 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_exprs_preserves_immutables_addr_dom:
  ∀cx es st res st'.
    eval_exprs cx es st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED

Theorem eval_stmts_preserves_immutables_addr_dom:
  ∀cx ss st res st'.
    eval_stmts cx ss st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_mutual, preserves_immutables_dom_def]
QED

Theorem eval_stmts_preserves_immutables_dom:
  ∀cx ss st res st'.
    eval_stmts cx ss st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 2 immutables_dom_mutual) >>
  rw[preserves_immutables_dom_def]
QED
