Theory vyperLogPreservation

Ancestors
  vyperCall vyperStatePreservation

Definition log_extends_def:
  log_extends (st:evaluation_state) (st':evaluation_state) <=>
    isPREFIX st.logs st'.logs
End

Theorem log_extends_refl:
  log_extends st st
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_extends_trans:
  log_extends st st1 /\ log_extends st1 st2 ==> log_extends st st2
Proof
  simp[log_extends_def] >> metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem log_extends_eq_logs:
  st.logs = st'.logs ==> log_extends st st'
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem log_extends_append:
  log_extends st (st with logs := st.logs ++ events)
Proof
  simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem return_log_extends[local]:
  return x st = (res,st') ==> log_extends st st'
Proof
  simp[vyperStateTheory.return_def, log_extends_refl]
QED

Theorem raise_log_extends[local]:
  raise e st = (res,st') ==> log_extends st st'
Proof
  simp[vyperStateTheory.raise_def, log_extends_refl]
QED

Theorem push_log_log_extends[local]:
  push_log ev st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> gvs[push_log_logs] >> simp[log_extends_append]
QED

Theorem append_logs_log_extends[local]:
  append_logs events st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> gvs[append_logs_logs] >> simp[log_extends_append]
QED

Theorem bind_log_extends[local]:
  (!r st1. f st = (r,st1) ==> log_extends st st1) /\
  (!x st1 r st2.
     f st = (INL x,st1) /\ g x st1 = (r,st2) ==>
     log_extends st1 st2) /\
  bind f g st = (res,st') ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  Cases_on `f st` >>
  gvs[vyperStateTheory.bind_def] >>
  Cases_on `q` >> gvs[] >>
  metis_tac[log_extends_trans]
QED

Theorem bind_log_extends_forward[local]:
  bind f g st = (res,st') ==>
  (!r st1. f st = (r,st1) ==> log_extends st st1) ==>
  (!x st1 r st2.
     f st = (INL x,st1) /\ g x st1 = (r,st2) ==>
     log_extends st1 st2) ==>
  log_extends st st'
Proof
  metis_tac[bind_log_extends]
QED

Theorem type_check_guard_specialize[local]:
  type_check p msg st = (INL (),st1) ==>
  (!s0 s1. type_check p msg s0 = (INL (),s1) ==> P) ==>
  P
Proof
  metis_tac[]
QED

Theorem equality_guard_specialize[local]:
  (!x. x = a ==> P) ==> P
Proof
  metis_tac[]
QED

Theorem case_eval_stmts_nil_logs[local]:
  eval_stmts cx [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def, log_extends_refl]
QED

Theorem case_eval_stmts_cons_logs[local]:
  (!s0 x s1. eval_stmt cx s s0 = (INL x,s1) ==>
     !s2 r s3. eval_stmts cx ss s2 = (r,s3) ==> log_extends s2 s3) /\
  (!s0 r s1. eval_stmt cx s s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmts cx (s::ss) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmts _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[log_extends_trans]
QED

Theorem case_eval_targets_nil_logs[local]:
  eval_targets cx [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def, log_extends_refl]
QED

Theorem case_eval_targets_cons_logs[local]:
  (!s0 r s1. eval_target cx g s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 gv s1. eval_target cx g s0 = (INL gv,s1) ==>
     !s2 r s3. eval_targets cx gs s2 = (r,s3) ==> log_extends s2 s3) ==>
  !st res st'. eval_targets cx (g::gs) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  metis_tac[log_extends_trans]
QED

Theorem case_target_base_logs[local]:
  (!s0 r s1. eval_base_target cx bt s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_target cx (BaseTarget bt) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `x` >> gvs[vyperStateTheory.return_def] >>
  first_x_assum drule >> simp[]
QED

Theorem case_target_tuple_logs[local]:
  (!s0 r s1. eval_targets cx gs s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_target cx (TupleTarget gs) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def, AllCaseEqs(),
       vyperStateTheory.return_def] >>
  metis_tac[]
QED
Theorem case_iterator_array_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_iterator cx (Array e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs(), log_extends_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac materialise_state >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  qpat_x_assum `log_extends _ _` mp_tac >>
  simp[log_extends_def]
QED

Theorem case_iterator_range_logs[local]:
  (!s0 tv s1 s2 v s3.
     eval_expr cx e1 s0 = (INL tv,s1) /\
     get_Value tv s2 = (INL v,s3) ==>
     !st res st'. eval_expr cx e2 st = (res,st') ==> log_extends st st') /\
  (!s0 r s1. eval_expr cx e1 s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_iterator cx (Range e1 e2) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac lift_sum_state >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem case_eval_for_nil_logs[local]:
  eval_for cx tyv nm body [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def,
       log_extends_refl]
QED

Theorem push_scope_with_var_log_extends[local]:
  push_scope_with_var nm ty v st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  gvs[vyperStateTheory.push_scope_with_var_def, vyperStateTheory.return_def] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem pop_scope_log_extends[local]:
  pop_scope st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  gvs[vyperStateTheory.pop_scope_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem try_body_log_extends[local]:
  (!s0 x s1. push_scope_with_var nm tyv v s0 = (INL x,s1) ==>
     !st res st'. eval_stmts cx body st = (res,st') ==>
       log_extends st st') /\
  push_scope_with_var nm tyv v st0 = (INL (),st1) /\
  (try (do eval_stmts cx body; return F od) handle_loop_exception) st1 =
    (res1,st1') ==>
  log_extends st1 st1'
Proof
  rpt strip_tac >>
  qpat_x_assum `(try _ _) _ = _` mp_tac >>
  simp[vyperStateTheory.try_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac handle_loop_exception_state >> gvs[]
QED

Theorem finally_pop_scope_log_extends[local]:
  (!r s1. f st = (r,s1) ==> log_extends st s1) /\
  finally f pop_scope st = (res,st') ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac pop_scope_log_extends >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum ACCEPT_TAC
QED

Theorem finally_try_body_log_extends[local]:
  !cx body st1 res1 st1'.
    finally (try (do x <- eval_stmts cx body; return F od) handle_loop_exception)
            pop_scope st1 = (res1,st1') ==>
    (!st res st'. eval_stmts cx body st = (res,st') ==>
       log_extends st st') ==>
    log_extends st1 st1'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.try_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac handle_loop_exception_state >> gvs[] >>
  imp_res_tac pop_scope_log_extends >>
  irule log_extends_trans >>
  qexists_tac `s''` >> simp[]
QED

Theorem case_eval_for_cons_logs[local]:
  (!s0 x s1 s2 broke s3.
     push_scope_with_var nm tyv v s0 = (INL x,s1) /\
     finally (try (do eval_stmts cx body; return F od)
                    handle_loop_exception) pop_scope s2 = (INL broke,s3) /\
     ~broke ==>
     !st res st'. eval_for cx tyv nm body vs st = (res,st') ==>
       log_extends st st') /\
  (!s0 x s1. push_scope_with_var nm tyv v s0 = (INL x,s1) ==>
     !st res st'. eval_stmts cx body st = (res,st') ==>
       log_extends st st') ==>
  !st res st'. eval_for cx tyv nm body (v::vs) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac push_scope_with_var_log_extends >>
  `!sb rb sb'. eval_stmts cx body sb = (rb,sb') ==>
               log_extends sb sb'` by
    (rpt strip_tac >>
     qpat_x_assum `!s0 s1. push_scope_with_var _ _ _ s0 = _ ==> _`
       (qspecl_then [`st`, `s''`] mp_tac) >>
     simp[] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `log_extends s'' s'³'` by
    (drule finally_try_body_log_extends >>
     disch_then drule >> simp[]) >>
  `log_extends st s'³'` by
    (irule log_extends_trans >> qexists_tac `s''` >> simp[]) >>
  Cases_on `broke` >> gvs[vyperStateTheory.return_def] >>
  qpat_x_assum `!s0 s1 s2 s3. _`
    (qspecl_then [`st`, `s''`, `s''`, `s'³'`] mp_tac) >>
  simp[vyperStateTheory.ignore_bind_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> qexists_tac `s'³'` >> simp[]
QED


Theorem update_accounts_logs[local]:
  update_accounts f st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.update_accounts_def, vyperStateTheory.return_def]
QED

Theorem update_transient_logs[local]:
  update_transient f st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.update_transient_def, vyperStateTheory.return_def]
QED

Theorem set_scopes_logs[local]:
  set_scopes env st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.set_scopes_def, vyperStateTheory.return_def]
QED

Theorem set_address_immutables_logs[local]:
  set_address_immutables cx imms st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  gvs[vyperStateTheory.set_address_immutables_def,
      vyperStateTheory.return_def]
QED

Theorem set_storage_backend_logs[local]:
  set_storage_backend cx is_transient storage st = (res,st') ==>
    st'.logs = st.logs
Proof
  Cases_on `is_transient` >> rpt strip_tac >>
  gvs[vyperStateTheory.set_storage_backend_def, vyperStateTheory.bind_def,
      vyperStateTheory.update_transient_def,
      vyperStateTheory.update_accounts_def,
      vyperStateTheory.get_accounts_def, vyperStateTheory.return_def,
      AllCaseEqs()]
QED

Theorem write_storage_slot_logs[local]:
  write_storage_slot cx is_transient slot tv v st = (res,st') ==>
    st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.write_storage_slot_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac set_storage_backend_logs >> gvs[]
QED

Theorem set_immutable_logs[local]:
  set_immutable cx src n tv v st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `set_immutable _ _ _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.set_immutable_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_address_immutables_state >> gvs[] >>
  imp_res_tac set_address_immutables_logs >> gvs[]
QED
Theorem set_global_logs[local]:
  set_global cx src n v st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `set_global _ _ _ _ _ = _` mp_tac >>
  simp[Once vyperStateTheory.set_global_def, vyperStateTheory.bind_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  Cases_on `find_var_decl_by_num n ts` >>
  gvs[vyperStateTheory.raise_def] >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.raise_def,
      AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> gvs[]
QED


Theorem subscript_terminal_logs[local]:
  (do v2 <- get_Value tv2;
      tenv <<- get_tenv cx;
      arr_tv <- lift_option_type (evaluate_type tenv (expr_type e1))
                   "Subscript array type";
      check_array_bounds cx tv1 v2;
      r <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
      case r of
        INL v => return v
      | INR (is_transient,slot,tv) => do
          v <- read_storage_slot cx is_transient slot tv;
          return (Value v)
        od
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac check_array_bounds_state >> imp_res_tac lift_sum_state >> gvs[] >>
  Cases_on `r` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  PairCases_on `y` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_storage_slot_state >> imp_res_tac return_state >> gvs[]
QED

Theorem subscript_terminal_normalized_logs[local]:
  (do v2 <- get_Value tv2;
      arr_tv <- lift_option_type
        (evaluate_type (get_tenv cx) (expr_type e1))
        "Subscript array type";
      check_array_bounds cx tv1 v2;
      r <- lift_sum
        (evaluate_subscript (get_tenv cx) arr_tv tv1 v2);
      case r of
        INL v => return v
      | INR (is_transient,slot,tv) => do
          v <- read_storage_slot cx is_transient slot tv;
          return (Value v)
        od
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac check_array_bounds_state >> imp_res_tac lift_sum_state >> gvs[] >>
  Cases_on `r` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  PairCases_on `y` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_storage_slot_state >> imp_res_tac return_state >> gvs[]
QED


Theorem subscript_after_e1_logs[local]:
  (!s0 r s1. eval_expr cx e2 s0 = (r,s1) ==> log_extends s0 s1) /\
  (do tv2 <- eval_expr cx e2;
      v2 <- get_Value tv2;
      tenv <<- get_tenv cx;
      arr_tv <- lift_option_type (evaluate_type tenv (expr_type e1))
                   "Subscript array type";
      check_array_bounds cx tv1 v2;
      r <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
      case r of
        INL v => return v
      | INR (is_transient,slot,tv) => do
          v <- read_storage_slot cx is_transient slot tv;
          return (Value v)
        od
   od) st = (res,st') ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule bind_log_extends_forward >>
  disch_then irule >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[] >>
  irule log_extends_eq_logs >>
  imp_res_tac subscript_terminal_normalized_logs >>
  sym_tac >> first_assum ACCEPT_TAC
QED

Theorem subscript_after_e1_logs_forward[local]:
  (do tv2 <- eval_expr cx e2;
      v2 <- get_Value tv2;
      arr_tv <- lift_option_type
        (evaluate_type (get_tenv cx) (expr_type e1))
        "Subscript array type";
      check_array_bounds cx tv1 v2;
      r <- lift_sum
        (evaluate_subscript (get_tenv cx) arr_tv tv1 v2);
      case r of
        INL v => return v
      | INR (is_transient,slot,tv) => do
          v <- read_storage_slot cx is_transient slot tv;
          return (Value v)
        od
   od) st = (res,st') ==>
  (!s0 r s1. eval_expr cx e2 s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule bind_log_extends_forward >>
  disch_then irule >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[] >>
  irule log_extends_eq_logs >>
  imp_res_tac subscript_terminal_normalized_logs >>
  sym_tac >> first_assum ACCEPT_TAC
QED

Theorem case_expr_subscript_logs[local]:
  (!s0 tv1 s1. eval_expr cx e1 s0 = (INL tv1,s1) ==>
     !s2 r s3. eval_expr cx e2 s2 = (r,s3) ==> log_extends s2 s3) /\
  (!s0 r s1. eval_expr cx e1 s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'.
    eval_expr cx (Subscript ty e1 e2) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  strip_tac >>
  drule bind_log_extends_forward >>
  disch_then irule >>
  conj_tac
  >- metis_tac[] >>
  rpt strip_tac >> gvs[] >>
  drule subscript_after_e1_logs_forward >>
  disch_then irule >>
  qpat_x_assum `!s0 tv1 s1. eval_expr _ e1 s0 = (INL tv1,s1) ==> _` drule >>
  simp[]
QED
Theorem new_variable_logs[local]:
  new_variable id tv v st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `new_variable _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.new_variable_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.get_scopes_def,
       vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `st.scopes` >>
  gvs[vyperStateTheory.set_scopes_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def]
QED

Theorem storage_assignment_tail_logs[local]:
  (do current_val <- read_storage_slot cx tr slot tv;
      new_val <- lift_sum (assign_subscripts tv current_val subs ao);
      write_storage_slot cx tr slot tv new_val;
      assign_result tv ao current_val subs
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac read_storage_slot_state >> imp_res_tac lift_sum_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >>
  imp_res_tac assign_result_state >> gvs[]
QED


Theorem array_pop_tail_logs[local]:
  (do storage <- get_storage_backend cx is_transient;
      stored_len <<- w2n (lookup_storage elem_slot storage);
      check (stored_len > 0) "pop empty storage array";
      last_idx <<- stored_len - 1;
      last_slot <<- elem_slot + n2w (1 + last_idx * type_slot_size pop_elem_tv);
      popped <- read_storage_slot cx is_transient last_slot pop_elem_tv;
      write_storage_slot cx is_transient last_slot pop_elem_tv
        (default_value pop_elem_tv);
      write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
        (IntV &last_idx);
      return (SOME popped)
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac check_state >> imp_res_tac read_storage_slot_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> imp_res_tac return_state >> gvs[]
QED

Theorem array_append_tail_logs[local]:
  (do storage <- get_storage_backend cx is_transient;
      stored_len <<- w2n (lookup_storage elem_slot storage);
      check (stored_len < n) "append full storage array";
      new_slot <<- elem_slot + n2w (1 + stored_len * type_slot_size app_elem_tv);
      write_storage_slot cx is_transient new_slot app_elem_tv v;
      write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
        (IntV &(stored_len + 1));
      return NONE
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac check_state >> imp_res_tac write_storage_slot_logs >>
  imp_res_tac return_state >> gvs[]
QED

Theorem arrayref_assignment_suffix_logs[local]:
  (do (elem_slot,final_tv,remaining_subs) <-
        resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) subs;
      case (ao,final_tv) of
        (PopOp,ArrayTV pop_elem_tv (Dynamic n)) => do
          storage <- get_storage_backend cx is_transient;
          stored_len <<- w2n (lookup_storage elem_slot storage);
          check (stored_len > 0) "pop empty storage array";
          last_idx <<- stored_len - 1;
          last_slot <<- elem_slot + n2w (1 + last_idx * type_slot_size pop_elem_tv);
          popped <- read_storage_slot cx is_transient last_slot pop_elem_tv;
          write_storage_slot cx is_transient last_slot pop_elem_tv
            (default_value pop_elem_tv);
          write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
            (IntV &last_idx);
          return (SOME popped)
        od
      | (AppendOp v,ArrayTV app_elem_tv (Dynamic n)) => do
          storage <- get_storage_backend cx is_transient;
          stored_len <<- w2n (lookup_storage elem_slot storage);
          check (stored_len < n) "append full storage array";
          new_slot <<- elem_slot + n2w (1 + stored_len * type_slot_size app_elem_tv);
          write_storage_slot cx is_transient new_slot app_elem_tv v;
          write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
            (IntV &(stored_len + 1));
          return NONE
        od
      | _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  once_rewrite_tac [vyperStateTheory.bind_def] >>
  qabbrev_tac `rr = resolve_array_element cx is_transient base_slot
                    (ArrayTV elem_tv bd) subs st` >>
  PairCases_on `rr` >> Cases_on `rr0` >>
  qpat_x_assum `Abbrev _` mp_tac >>
  simp[markerTheory.Abbrev_def] >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `(_,_) = resolve_array_element _ _ _ _ _ _`
    (assume_tac o SYM) >>
  imp_res_tac resolve_array_element_state >> gvs[] >>
  Cases_on `final_tv` >> gvs[] >>
  TRY (Cases_on `b` >> gvs[]) >>
  Cases_on `ao` >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac storage_assignment_tail_logs >>
  imp_res_tac array_pop_tail_logs >>
  imp_res_tac array_append_tail_logs >>
  pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac check_state >> imp_res_tac read_storage_slot_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> imp_res_tac return_state >> gvs[]
QED

Theorem arrayref_assignment_normal_logs[local]:
  (do (elem_slot,final_tv,remaining_subs) <-
        resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) subs;
      case final_tv of
        BaseTV _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | TupleTV _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | ArrayTV pop_elem_tv (Fixed _) => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | ArrayTV pop_elem_tv (Dynamic n) =>
          (case ao of
             Replace _ => do
               current_val <- read_storage_slot cx is_transient elem_slot final_tv;
               new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
               write_storage_slot cx is_transient elem_slot final_tv new_val;
               assign_result final_tv ao current_val remaining_subs
             od
           | Update _ _ _ => do
               current_val <- read_storage_slot cx is_transient elem_slot final_tv;
               new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
               write_storage_slot cx is_transient elem_slot final_tv new_val;
               assign_result final_tv ao current_val remaining_subs
             od
           | AppendOp v => do
               storage <- get_storage_backend cx is_transient;
               check (w2n (lookup_storage elem_slot storage) < n)
                 "append full storage array";
               write_storage_slot cx is_transient
                 (elem_slot + n2w (type_slot_size pop_elem_tv *
                                    w2n (lookup_storage elem_slot storage) + 1))
                 pop_elem_tv v;
               write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
                 (IntV (&(w2n (lookup_storage elem_slot storage) + 1)));
               return NONE
             od
           | PopOp => do
               storage <- get_storage_backend cx is_transient;
               check (w2n (lookup_storage elem_slot storage) > 0)
                 "pop empty storage array";
               popped <- read_storage_slot cx is_transient
                 (elem_slot + n2w (type_slot_size pop_elem_tv *
                                    (w2n (lookup_storage elem_slot storage) - 1) + 1))
                 pop_elem_tv;
               write_storage_slot cx is_transient
                 (elem_slot + n2w (type_slot_size pop_elem_tv *
                                    (w2n (lookup_storage elem_slot storage) - 1) + 1))
                 pop_elem_tv (default_value pop_elem_tv);
               write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
                 (IntV (&(w2n (lookup_storage elem_slot storage) - 1)));
               return (SOME popped)
             od)
      | StructTV _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | FlagTV _ => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
      | NoneTV => do
          current_val <- read_storage_slot cx is_transient elem_slot final_tv;
          new_val <- lift_sum (assign_subscripts final_tv current_val remaining_subs ao);
          write_storage_slot cx is_transient elem_slot final_tv new_val;
          assign_result final_tv ao current_val remaining_subs
        od
   od) st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >> pop_assum mp_tac >>
  once_rewrite_tac [vyperStateTheory.bind_def] >>
  qabbrev_tac `rr = resolve_array_element cx is_transient base_slot
                    (ArrayTV elem_tv bd) subs st` >>
  PairCases_on `rr` >> Cases_on `rr0` >>
  qpat_x_assum `Abbrev _` mp_tac >>
  simp[markerTheory.Abbrev_def] >> strip_tac >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  qpat_x_assum `(_,_) = resolve_array_element _ _ _ _ _ _`
    (assume_tac o SYM) >>
  imp_res_tac resolve_array_element_state >> gvs[] >>
  Cases_on `final_tv` >> gvs[] >>
  TRY (Cases_on `b` >> gvs[]) >>
  Cases_on `ao` >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac storage_assignment_tail_logs >>
  imp_res_tac array_pop_tail_logs >>
  imp_res_tac array_append_tail_logs >>
  pop_assum mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  imp_res_tac vyperStorageBackendTheory.get_storage_backend_state >>
  imp_res_tac check_state >> imp_res_tac read_storage_slot_state >> gvs[] >>
  imp_res_tac write_storage_slot_logs >> imp_res_tac return_state >> gvs[]
QED

Theorem assign_target_toplevel_logs[local]:
  assign_target cx (BaseTargetV (TopLevelVar src id) subs) ao st = (res,st') ==>
  st'.logs = st.logs
Proof
  rpt strip_tac >>
  Cases_on `lookup_global cx src (string_to_num id) st` >>
  Cases_on `q` >>
  imp_res_tac lookup_global_state >>
  pop_assum SUBST_ALL_TAC
  >- (Cases_on `x`
      >- (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
          simp[Once vyperStateTheory.assign_target_def,
               vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.return_def, vyperStateTheory.raise_def,
               LET_THM, pairTheory.PAIR, AllCaseEqs()] >>
          rpt strip_tac >> gvs[] >>
          imp_res_tac lift_option_type_state >> imp_res_tac lift_sum_state >>
          imp_res_tac set_global_logs >> imp_res_tac assign_result_state >> gvs[])
      >- (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
          simp[Once vyperStateTheory.assign_target_def,
               vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.return_def, vyperStateTheory.raise_def,
               LET_THM, pairTheory.PAIR, AllCaseEqs()] >>
          rpt strip_tac >> gvs[] >>
          rpt (pairarg_tac >> gvs[]) >>
          pop_assum mp_tac >>
          simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               AllCaseEqs()] >>
          rpt strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
          pop_assum mp_tac >>
          simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               AllCaseEqs()] >>
          rpt strip_tac >> gvs[] >>
          imp_res_tac lift_option_type_state >>
          imp_res_tac read_storage_slot_state >> imp_res_tac lift_sum_state >>
          imp_res_tac write_storage_slot_logs >>
          imp_res_tac assign_result_state >> gvs[])
      >> (Cases_on `lift_option_type (get_module_code cx src)
                       "assign_target get_module_code" st` >>
          Cases_on `q` >>
          imp_res_tac lift_option_type_state >>
          pop_assum SUBST_ALL_TAC
          >- (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
              simp[Once vyperStateTheory.assign_target_def,
                   LET_THM, pairTheory.PAIR] >>
              strip_tac >>
              pop_assum mp_tac >>
              once_rewrite_tac [vyperStateTheory.bind_def] >>
              strip_tac >>
              gvs[Once vyperStateTheory.bind_def] >>
              drule arrayref_assignment_normal_logs >>
              simp[])
          >> (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
              simp[Once vyperStateTheory.assign_target_def,
                   vyperStateTheory.bind_def, vyperStateTheory.return_def,
                   vyperStateTheory.raise_def, LET_THM, pairTheory.PAIR] >>
              strip_tac >> gvs[])))
  >> (qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
      simp[Once vyperStateTheory.assign_target_def,
           vyperStateTheory.bind_def, vyperStateTheory.return_def,
           vyperStateTheory.raise_def, LET_THM, pairTheory.PAIR] >>
      strip_tac >> gvs[])
QED

Theorem assign_target_logs_mutual[local]:
  (!cx gv ao st res st'.
     assign_target cx gv ao st = (res,st') ==> st'.logs = st.logs) /\
  (!cx gvs vs st res st'.
     assign_targets cx gvs vs st = (res,st') ==> st'.logs = st.logs)
Proof
  ho_match_mp_tac vyperStateTheory.assign_target_ind >> rpt conj_tac >> rpt gen_tac
  (* ScopedVar *)
  >- (rpt strip_tac >>
      gvs[vyperStateTheory.assign_target_def, vyperStateTheory.bind_def,
          vyperStateTheory.get_scopes_def, vyperStateTheory.return_def,
          vyperStateTheory.lift_option_def] >>
      Cases_on `find_containing_scope (string_to_num id) st.scopes` >>
      gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
      PairCases_on `x` >>
      Cases_on `assign_subscripts x2.type x2.value (REVERSE is) ao` >>
      gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
      gvs[vyperStateTheory.assign_target_def, vyperStateTheory.bind_def,
          vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
          vyperStateTheory.raise_def, vyperStateTheory.lift_option_def,
          vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
          vyperStateTheory.lift_sum_def, vyperStateTheory.set_scopes_def,
          AllCaseEqs()] >>
      imp_res_tac lift_sum_state >> imp_res_tac assign_result_state >> gvs[])
  (* TopLevelVar *)
  >- (rpt strip_tac >> imp_res_tac assign_target_toplevel_logs)
  (* ImmutableVar *)
  >- (rpt strip_tac >>
      qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
      simp[Once vyperStateTheory.assign_target_def,
           vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.return_def, vyperStateTheory.raise_def,
           AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac get_immutables_state >> imp_res_tac lift_option_type_state >>
      imp_res_tac lift_sum_state >> gvs[] >>
      imp_res_tac set_immutable_logs >> imp_res_tac assign_result_state >> gvs[])
  (* TupleTargetV success *)
  >- (rpt strip_tac >>
      qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
      simp[Once vyperStateTheory.assign_target_def,
           vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.return_def, vyperStateTheory.raise_def,
           AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac type_check_state >> gvs[] >>
      first_x_assum drule >> imp_res_tac return_state >> gvs[])
  (* Constructor mismatch, base, cons, and fallback cases. *)
  >> rpt strip_tac
  >> pop_assum mp_tac
  >> simp[Once vyperStateTheory.assign_target_def,
          vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
          vyperStateTheory.return_def, vyperStateTheory.raise_def,
          AllCaseEqs()]
  >> rpt strip_tac >> gvs[]
  >> TRY (first_x_assum drule >> gvs[] >> NO_TAC)
  >> imp_res_tac return_state >> gvs[]
QED

Theorem assign_target_logs[local]:
  assign_target cx gv ao st = (res,st') ==> st'.logs = st.logs
Proof
  metis_tac[cj 1 assign_target_logs_mutual]
QED

Theorem assign_targets_logs[local]:
  assign_targets cx gvs vs st = (res,st') ==> st'.logs = st.logs
Proof
  metis_tac[cj 2 assign_target_logs_mutual]
QED

Theorem case_stmt_annassign_logs[local]:
  (!tenv s0 tyv s1.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type" s0 =
       (INL tyv,s1) ==>
     !st res st'. eval_expr cx e st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_stmt cx (AnnAssign id typ e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  TRY (imp_res_tac lift_option_type_state >> gvs[log_extends_refl] >> NO_TAC) >>
  qpat_x_assum `!s0 tyv s1. _`
    (qspecl_then [`st`, `tyv`, `s''`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  qpat_x_assum `!st res st'. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  imp_res_tac lift_option_type_state >> imp_res_tac materialise_state >> gvs[] >>
  imp_res_tac new_variable_logs >> gvs[log_extends_def]
QED

Theorem case_stmt_append_logs[local]:
  (!st res st'. eval_base_target cx bt st = (res,st') ==>
     log_extends st st') /\
  (!s0 loc sbs s1. eval_base_target cx bt s0 = (INL (loc,sbs),s1) ==>
     !st res st'. eval_expr cx e st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_stmt cx (Append bt e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac materialise_state >> imp_res_tac assign_target_logs >>
  imp_res_tac return_state >> gvs[] >>
  qpat_x_assum `!st res st'. eval_base_target _ _ _ = _ ==> _` drule >>
  strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac materialise_state >> imp_res_tac assign_target_logs >>
  imp_res_tac return_state >> gvs[] >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!st' res st''. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_eq_logs >> gvs[]
QED

Theorem case_stmt_assign_logs[local]:
  (!st res st'. eval_target cx g st = (res,st') ==> log_extends st st') /\
  (!s0 gv s1. eval_target cx g s0 = (INL gv,s1) ==>
     !st res st'. eval_expr cx e st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_stmt cx (Assign g e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac materialise_state >> imp_res_tac assign_target_logs >>
  imp_res_tac return_state >> gvs[] >>
  qpat_x_assum `!st res st'. eval_target _ _ _ = _ ==> _` drule >>
  strip_tac >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!st res st'. eval_target _ _ _ = _ ==> _` drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_eq_logs >> gvs[]
QED

Theorem case_stmt_augassign_logs[local]:
  (!st res st'. eval_base_target cx bt st = (res,st') ==>
     log_extends st st') /\
  (!s0 loc sbs s1. eval_base_target cx bt s0 = (INL (loc,sbs),s1) ==>
     !st res st'. eval_expr cx e st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_stmt cx (AugAssign ty bt bop e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac get_Value_state >> imp_res_tac assign_target_logs >>
  imp_res_tac return_state >> gvs[] >>
  qpat_x_assum `!st res st'. eval_base_target _ _ _ = _ ==> _` drule >>
  strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac get_Value_state >> imp_res_tac assign_target_logs >>
  imp_res_tac return_state >> gvs[] >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `!st' res st''. eval_expr _ _ _ = _ ==> _` drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_eq_logs >> gvs[]
QED


Theorem case_expr_pop_logs[local]:
  (!st res st'. eval_base_target cx bt st = (res,st') ==>
     log_extends st st') ==>
  !st res st'. eval_expr cx (Pop ty bt) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  qpat_x_assum `!st res st'. eval_base_target _ _ _ = _ ==> _` drule >>
  strip_tac >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac assign_target_logs >> imp_res_tac lift_option_type_state >>
  imp_res_tac return_state >> gvs[] >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_eq_logs >> gvs[]
QED

Theorem case_expr_builtin_logs[local]:
  (!s0 x s1.
     type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s0 =
       (INL x,s1) /\ bt <> Len ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') /\
  (!s0 x s1.
     type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s0 =
       (INL x,s1) /\ bt = Len ==>
     !st res st'. eval_expr cx (HD es) st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_expr cx (Builtin ty bt es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def, vyperStateTheory.lift_sum_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  Cases_on `bt = Len` >> gvs[] >>
  TRY (gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def,
           vyperStateTheory.raise_def, AllCaseEqs()] >>
       imp_res_tac toplevel_array_length_state >> gvs[] >>
       first_x_assum (qspec_then `st` mp_tac) >>
       simp[vyperStateTheory.check_def, vyperStateTheory.type_check_def,
            vyperStateTheory.assert_def, vyperStateTheory.return_def] >> NO_TAC)
  >> `!st res st'. eval_exprs cx es st = (res,st') ==>
        log_extends st st'` by
       (first_x_assum (qspec_then `st` mp_tac) >>
        simp[vyperStateTheory.check_def, vyperStateTheory.type_check_def,
             vyperStateTheory.assert_def, vyperStateTheory.return_def])
  >> gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def,
         vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
         AllCaseEqs()]
  >> BasicProvers.FULL_CASE_TAC
  >> gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]
  >> first_x_assum drule >> simp[]
QED

Theorem case_stmt_return_some_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Return (SOME e)) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac materialise_state >>
  imp_res_tac raise_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem case_stmt_expr_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Expr e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac type_check_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem push_scope_log_extends[local]:
  push_scope st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  gvs[vyperStateTheory.push_scope_def, vyperStateTheory.return_def] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem finally_switch_BoolV_log_extends[local]:
  finally (switch_BoolV tv f g) pop_scope st = (res,st') ==>
  (!s0 r s1. f s0 = (r,s1) ==> log_extends s0 s1) ==>
  (!s0 r s1. g s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperInterpreterTheory.switch_BoolV_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  rpt IF_CASES_TAC >> gvs[vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac pop_scope_log_extends >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  TRY (irule log_extends_trans >> goal_assum drule >>
       first_assum MATCH_ACCEPT_TAC)
QED

Theorem case_stmt_if_logs[local]:
  (!s0 tv s1 s2 x s3.
     eval_expr cx e s0 = (INL tv,s1) /\ push_scope s2 = (INL x,s3) ==>
     !st res st'. eval_stmts cx ss1 st = (res,st') ==> log_extends st st') /\
  (!s0 tv s1 s2 x s3.
     eval_expr cx e s0 = (INL tv,s1) /\ push_scope s2 = (INL x,s3) ==>
     !st res st'. eval_stmts cx ss2 st = (res,st') ==> log_extends st st') /\
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (If e ss1 ss2) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs(),
       vyperStateTheory.push_scope_def, vyperStateTheory.return_def] >>
  strip_tac >> gvs[] >>
  rename1 `eval_expr cx e st = (INL tv,s_expr)` >>
  `log_extends st s_expr` by
    (qpat_x_assum `!s0 r s1. eval_expr _ _ _ = _ ==> _` drule >> simp[]) >>
  `!sb rb sb'. eval_stmts cx ss1 sb = (rb,sb') ==>
                log_extends sb sb'` by
    (rpt strip_tac >>
     qpat_x_assum `!s0 tv s1 s2 s3. _ ==> !st res st'. eval_stmts _ ss1 _ = _ ==> _`
       (qspecl_then [`st`, `tv`, `s_expr`, `s_expr`,
                     `s_expr with scopes updated_by CONS FEMPTY`] mp_tac) >>
     simp[vyperStateTheory.push_scope_def, vyperStateTheory.return_def]) >>
  `!sb rb sb'. eval_stmts cx ss2 sb = (rb,sb') ==>
                log_extends sb sb'` by
    (rpt strip_tac >>
     qpat_x_assum `!s0 tv s1 s2 s3. _ ==> !st res st'. eval_stmts _ ss2 _ = _ ==> _`
       (qspecl_then [`st`, `tv`, `s_expr`, `s_expr`,
                     `s_expr with scopes updated_by CONS FEMPTY`] mp_tac) >>
     simp[vyperStateTheory.push_scope_def, vyperStateTheory.return_def]) >>
  `log_extends (s_expr with scopes updated_by CONS FEMPTY) st'` by
    (drule finally_switch_BoolV_log_extends >>
     disch_then drule >> disch_then drule >> simp[]) >>
  `log_extends s_expr (s_expr with scopes updated_by CONS FEMPTY)` by
    (irule log_extends_eq_logs >> simp[]) >>
  `log_extends s_expr st'` by
    (irule log_extends_trans >>
     qexists_tac `s_expr with scopes updated_by CONS FEMPTY` >> simp[]) >>
  irule log_extends_trans >> qexists_tac `s_expr` >> simp[]
QED
Theorem case_stmt_for_logs[local]:
  (!tenv s0 tyv s1 s2 vs s3 s4 x s5.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s0 =
       (INL tyv,s1) /\
     eval_iterator cx it s2 = (INL vs,s3) /\
     check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s4 =
       (INL x,s5) ==>
     !st res st'. eval_for cx tyv (string_to_num id) body vs st = (res,st') ==>
       log_extends st st') /\
  (!tenv s0 tyv s1.
     tenv = get_tenv cx /\
     lift_option_type (evaluate_type tenv typ) "For evaluate_type" s0 =
       (INL tyv,s1) ==>
     !st res st'. eval_iterator cx it st = (res,st') ==>
       log_extends st st') ==>
  !st res st'. eval_stmt cx (For id typ it n body) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac lift_option_type_state >> gvs[log_extends_refl] >> NO_TAC) >>
  first_x_assum drule_all >> strip_tac >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  imp_res_tac check_state >> imp_res_tac type_check_state >> gvs[] >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  first_x_assum drule_all >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED


Theorem case_stmt_raise_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Raise (RaiseReason e)) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac lift_option_state >>
  imp_res_tac lift_option_type_state >> imp_res_tac raise_state >> gvs[] >>
  TRY (simp[log_extends_refl] >> NO_TAC) >>
  first_x_assum drule >> simp[]
QED

Theorem case_stmt_assert_logs[local]:
  (!s0 tv s1. eval_expr cx e s0 = (INL tv,s1) ==>
     !st res st'. eval_expr cx se st = (res,st') ==> log_extends st st') /\
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Assert e (AssertReason se)) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> gvs[] >>
  qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.switch_BoolV_def] >>
  rpt IF_CASES_TAC >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.bind_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac get_Value_state >> imp_res_tac lift_option_state >>
       imp_res_tac lift_option_type_state >> imp_res_tac raise_state >> gvs[]) >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem case_stmt_assert_bare_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Assert e AssertBare) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperInterpreterTheory.switch_BoolV_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
  Cases_on `tv = Value (BoolV T)` >>
  Cases_on `tv = Value (BoolV F)` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem case_stmt_assert_unreachable_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Assert e AssertUnreachable) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperInterpreterTheory.switch_BoolV_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule >> strip_tac >>
  Cases_on `tv = Value (BoolV T)` >>
  Cases_on `tv = Value (BoolV F)` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def]
QED

Theorem case_stmt_log_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_stmt cx (Log id es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_state >> gvs[] >>
  imp_res_tac push_log_log_extends >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  simp[log_extends_append]
QED


Theorem case_base_target_name_logs[local]:
  eval_base_target cx (NameTarget id) st = (res,st') ==> log_extends st st'
Proof
  strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.return_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl]
QED

Theorem case_base_target_toplevel_logs[local]:
  eval_base_target cx (TopLevelNameTarget sid) st = (res,st') ==>
    log_extends st st'
Proof
  PairCases_on `sid` >> strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  Cases_on `is_immutable_decl (string_to_num sid1) ts` >>
  gvs[vyperStateTheory.return_def, log_extends_refl]
QED

Theorem case_base_target_attribute_logs[local]:
  (!s0 r s1. eval_base_target cx bt s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_base_target cx (AttributeTarget bt id) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `x` >> gvs[vyperStateTheory.return_def] >>
  first_x_assum drule >> simp[]
QED

Theorem case_base_target_subscript_logs[local]:
  (!s0 loc sbs s1.
     eval_base_target cx bt s0 = (INL (loc,sbs),s1) ==>
     !s2 r s3. eval_expr cx e s2 = (r,s3) ==> log_extends s2 s3) /\
  (!s0 r s1. eval_base_target cx bt s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_base_target cx (SubscriptTarget bt e) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  PairCases_on `x` >> gvs[vyperStateTheory.bind_def,
                           vyperStateTheory.return_def, AllCaseEqs()] >>
  imp_res_tac get_Value_state >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem case_expr_name_logs[local]:
  eval_expr cx (Name ty id) st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.get_scopes_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> imp_res_tac lift_option_type_state >>
  gvs[log_extends_refl]
QED

Theorem lookup_global_log_extends[local]:
  lookup_global cx src id st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> imp_res_tac lookup_global_state >>
  gvs[log_extends_refl]
QED

Theorem lookup_flag_mem_log_extends[local]:
  lookup_flag_mem cx nsid mid st = (res,st') ==> log_extends st st'
Proof
  strip_tac >> imp_res_tac lookup_flag_mem_state >>
  gvs[log_extends_refl]
QED

Theorem case_expr_toplevel_name_logs[local]:
  eval_expr cx (TopLevelName ty (src,id)) st = (res,st') ==>
  log_extends st st'
Proof
  strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  metis_tac[lookup_global_log_extends]
QED

Theorem case_expr_flag_member_logs[local]:
  eval_expr cx (FlagMember ty nsid mid) st = (res,st') ==>
  log_extends st st'
Proof
  strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  metis_tac[lookup_flag_mem_log_extends]
QED

Theorem switch_BoolV_log_extends[local]:
  switch_BoolV tv f g st = (res,st') ==>
  (!s0 r s1. f s0 = (r,s1) ==> log_extends s0 s1) ==>
  (!s0 r s1. g s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `switch_BoolV _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.switch_BoolV_def] >>
  rpt IF_CASES_TAC >> simp[vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  first_x_assum drule >> simp[]
QED

Theorem case_expr_if_logs[local]:
  (!s0 tv s1. eval_expr cx e1 s0 = (INL tv,s1) ==>
     !st res st'. eval_expr cx e2 st = (res,st') ==> log_extends st st') /\
  (!s0 tv s1. eval_expr cx e1 s0 = (INL tv,s1) ==>
     !st res st'. eval_expr cx e3 st = (res,st') ==> log_extends st st') /\
  (!s0 r s1. eval_expr cx e1 s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (IfExp ty e1 e2 e3) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `!sb rb sb'. eval_expr cx e2 sb = (rb,sb') ==> log_extends sb sb'` by
    (qpat_x_assum `!s0 tv s1. _ ==> !st res st'. eval_expr _ e2 _ = _ ==> _`
       drule >> simp[]) >>
  `!sb rb sb'. eval_expr cx e3 sb = (rb,sb') ==> log_extends sb sb'` by
    (qpat_x_assum `!s0 tv s1. _ ==> !st res st'. eval_expr _ e3 _ = _ ==> _`
       drule >> simp[]) >>
  `log_extends s'' st'` by
    (drule switch_BoolV_log_extends >>
     disch_then drule >> disch_then drule >> simp[]) >>
  `log_extends st s''` by
    (qpat_x_assum `!s0 r s1. eval_expr _ e1 _ = _ ==> _` drule >> simp[]) >>
  irule log_extends_trans >> qexists_tac `s''` >> simp[]
QED

Theorem case_expr_struct_lit_logs[local]:
  (!ks. ks = MAP FST kes ==>
     !s0 r s1. eval_exprs cx (MAP SND kes) s0 = (r,s1) ==>
       log_extends s0 s1) ==>
  !st res st'. eval_expr cx (StructLit ty sid kes) st = (res,st') ==>
    log_extends st st'
Proof
  PairCases_on `sid` >> rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> imp_res_tac equality_guard_specialize >>
  first_x_assum drule >> simp[]
QED

Theorem transfer_value_logs[local]:
  transfer_value fromAddr toAddr amount st = (res,st') ==>
  st'.logs = st.logs
Proof
  rw[vyperInterpreterTheory.transfer_value_def, vyperStateTheory.bind_def,
     vyperStateTheory.ignore_bind_def, vyperStateTheory.get_accounts_def,
     vyperStateTheory.update_accounts_def, vyperStateTheory.check_def,
     vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
     vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  gvs[AllCaseEqs(), vyperStateTheory.return_def,
      vyperStateTheory.raise_def]
QED

Theorem case_expr_send_logs[local]:
  (!s0 s1. type_check (LENGTH es = 2) "Send args" s0 = (INL (),s1) ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_expr cx (Call ty Send es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac type_check_guard_specialize >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac transfer_value_logs >> gvs[] >>
  metis_tac[log_extends_trans, log_extends_eq_logs]
QED

Theorem case_expr_selfdestruct_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty SelfDestructTarget es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.get_accounts_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >>
  imp_res_tac transfer_value_logs >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_eq_logs >> gvs[]
QED

Theorem case_expr_create_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'.
    eval_expr cx (Call ty (CreateTarget kind has_salt rof) es drv) st =
      (res,st') ==> log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac vyperCreateTheory.eval_create_preserves_non_accounts >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  irule log_extends_eq_logs >> gvs[]
QED

Theorem finally_log_extends[local]:
  finally f g st = (res,st') ==>
  (!r s1. f st = (r,s1) ==> log_extends st s1) ==>
  (!s0 r s1. g s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[log_extends_trans]
QED

Theorem set_scopes_log_extends[local]:
  set_scopes scopes st = (res,st') ==> log_extends st st'
Proof
  simp[vyperStateTheory.set_scopes_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem acquire_nonreentrant_lock_log_extends[local]:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  log_extends st st'
Proof
  Cases_on
    `lookup_storage (n2w slot)
       (vfmExecution$lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  simp[vyperInterpreterTheory.acquire_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem release_nonreentrant_lock_log_extends[local]:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  log_extends st st'
Proof
  simp[vyperInterpreterTheory.release_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[] >>
  irule log_extends_eq_logs >> simp[]
QED

Theorem intcall_cleanup_log_extends[local]:
  (do pop_function prev;
      if nr /\ ~is_view then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()
   od) st = (res,st') ==>
  log_extends st st'
Proof
  Cases_on `nr` >> Cases_on `is_view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperInterpreterTheory.pop_function_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac set_scopes_log_extends >>
  imp_res_tac release_nonreentrant_lock_log_extends >>
  imp_res_tac return_state >> gvs[] >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED


Theorem handle_function_log_extends[local]:
  handle_function ex st = (res,st') ==> log_extends st st'
Proof
  Cases_on `ex` >>
  simp[oneline vyperInterpreterTheory.handle_function_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  rpt strip_tac >> gvs[log_extends_refl]
QED

Theorem intcall_try_body_log_extends[local]:
  (try (do eval_stmts cxf body; return NoneV od) handle_function) st =
    (res,st') ==>
  (!s0 r s1. eval_stmts cxf body s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(try _ _) _ = _` mp_tac >>
  simp[vyperStateTheory.try_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac handle_function_log_extends >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem intcall_defaults_log_extends[local]:
  finally (do set_scopes [FEMPTY]; eval_exprs cxd needed_dflts od)
          (set_scopes prev) st = (res,st') ==>
  (!s0 r s1. eval_exprs cxd needed_dflts s0 = (r,s1) ==>
     log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.set_scopes_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `log_extends (st with scopes := [FEMPTY]) s''` mp_tac >>
  simp[log_extends_def]
QED


Theorem intcall_defaults_exact_log_extends[local]:
  finally (do x <- set_scopes [FEMPTY];
              eval_exprs cxd needed_dflts
           od)
          (set_scopes prev) st = (res,st') ==>
  (!s0 r s1. eval_exprs cxd needed_dflts s0 = (r,s1) ==>
     log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.finally_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.bind_def, vyperStateTheory.set_scopes_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `log_extends (st with scopes := [FEMPTY]) s''` mp_tac >>
  simp[log_extends_def]
QED
Theorem intcall_scoped_defaults_bind_log_extends[local]:
  (do prev <- get_scopes;
      dflt_vs <- finally
        (do set_scopes [FEMPTY]; eval_exprs cxd needed_dflts od)
        (set_scopes prev);
      k prev dflt_vs
   od) st = (res,st') ==>
  (!s0 r s1. eval_exprs cxd needed_dflts s0 = (r,s1) ==>
             log_extends s0 s1) ==>
  (!prev dflt_vs s0 r s1. k prev dflt_vs s0 = (r,s1) ==>
                          log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> gvs[] >>
     drule bind_log_extends_forward >> disch_then irule >>
     conj_tac >-
       (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     rpt strip_tac >>
     drule intcall_defaults_log_extends >> simp[]) >>
  rpt strip_tac >>
  irule log_extends_eq_logs >>
  gvs[vyperStateTheory.get_scopes_def, vyperStateTheory.return_def]
QED

Theorem sum_result_case_log_extends[local]:
  (case q of INL x => k x st | INR e => (INR e,st)) = (res,st') ==>
  (!x res st'. k x st = (res,st') ==> log_extends st st') ==>
  log_extends st st'
Proof
  Cases_on `q` >> simp[log_extends_refl] >> metis_tac[]
QED

Theorem intcall_body_finally_log_extends[local]:
  finally (try (do eval_stmts cxf body; return NoneV od) handle_function)
    (do pop_function prev;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st = (res,st') ==>
  (!s0 r s1. eval_stmts cxf body s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule finally_log_extends >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> drule intcall_cleanup_log_extends >> simp[]) >>
  rpt strip_tac >>
  drule intcall_try_body_log_extends >> disch_then irule >>
  first_assum MATCH_ACCEPT_TAC
QED

Theorem intcall_cleanup_exact_log_extends[local]:
  (do x <- pop_function prev;
      if nr /\ mut <> View /\ mut <> Pure then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()
   od) st = (res,st') ==>
  log_extends st st'
Proof
  Cases_on `nr` >> Cases_on `mut` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperInterpreterTheory.pop_function_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac set_scopes_log_extends >>
  imp_res_tac release_nonreentrant_lock_log_extends >>
  imp_res_tac return_state >> gvs[log_extends_refl] >>
  TRY (first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED


Theorem intcall_try_body_exact_log_extends[local]:
  (try (do x <- eval_stmts cxf body; return NoneV od) handle_function) st =
    (res,st') ==>
  (!s0 r s1. eval_stmts cxf body s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(try _ _) _ = _` mp_tac >>
  simp[vyperStateTheory.try_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac handle_function_log_extends >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED
Theorem intcall_body_finally_exact_log_extends[local]:
  finally (try (do x <- eval_stmts cxf body; return NoneV od) handle_function)
    (do x <- pop_function prev;
        if nr /\ mut <> View /\ mut <> Pure then
          case cx.nonreentrant_slot of
            NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st = (res,st') ==>
  (!s0 r s1. eval_stmts cxf body s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule finally_log_extends >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> drule intcall_cleanup_exact_log_extends >> simp[]) >>
  rpt strip_tac >>
  drule intcall_try_body_exact_log_extends >> disch_then irule >>
  first_assum MATCH_ACCEPT_TAC
QED
Theorem intcall_needed_dflts_index[local]:
  e <= a /\ a <= e + d ==> d - (a - e) = e + d - a
Proof
  decide_tac
QED

Theorem push_function_logs[local]:
  push_function src_fn sc cx st = (res,st') ==>
  st'.logs = st.logs
Proof
  simp[vyperInterpreterTheory.push_function_def,
       vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[]
QED


Theorem intcall_post_defaults_log_extends[local]:
  (do env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot =>
                 acquire_nonreentrant_lock cx.txn.target slot
                   (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) st = (res,st') ==>
  (!s0 r s1.
     eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) body s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperInterpreterTheory.push_function_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac lift_option_type_state >>
  gvs[log_extends_refl] >>
  `log_extends s'' s'⁴'` by
    (qpat_x_assum `(if nr then _ else _) _ = _` mp_tac >>
     Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
     simp[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
     rpt strip_tac >>
     imp_res_tac acquire_nonreentrant_lock_log_extends >>
     gvs[log_extends_refl]) >>
  `log_extends (s'⁴' with scopes := [env]) s'⁵'` by
    (qpat_x_assum `finally _ _ _ = _` mp_tac >>
     strip_tac >>
     drule intcall_body_finally_exact_log_extends >>
     simp[]) >>
  irule log_extends_trans >>
  qexists `s'⁴'` >> simp[] >>
  irule log_extends_trans >>
  qexists `s'⁴' with scopes := [env]` >>
  simp[log_extends_eq_logs]
QED

Theorem intcall_post_defaults_guarded_log_extends[local]:
  (do env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot =>
                 acquire_nonreentrant_lock cx.txn.target slot
                   (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) sg2 = (res,st') ==>
  (!env sg3 rtv sg4 sg5 cxf sg6.
     lift_option_type
       (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
       "IntCall bind_arguments" sg2 = (INL env,sg3) ==>
     lift_option_type (evaluate_type (get_tenv cx) ret)
       "IntCall eval ret" sg3 = (INL rtv,sg4) ==>
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ()) sg4 = (INL (),sg5) ==>
     push_function (src_id_opt,fn) env cx sg5 = (INL cxf,sg6) ==>
     !s0 r s1. eval_stmts cxf body s0 = (r,s1) ==>
                log_extends s0 s1) ==>
  log_extends sg2 st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac lift_option_type_state >>
  gvs[log_extends_refl] >>
  `log_extends s'' s'⁴'` by
    (qpat_x_assum `(if nr then _ else _) _ = _` mp_tac >>
     Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
     simp[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
     rpt strip_tac >>
     imp_res_tac acquire_nonreentrant_lock_log_extends >>
     gvs[log_extends_refl]) >>
  `log_extends s'⁴' s'⁵'` by
    (irule log_extends_eq_logs >>
     imp_res_tac push_function_logs >> sym_tac >>
     first_assum MATCH_ACCEPT_TAC) >>
  TRY (irule log_extends_trans >> goal_assum drule >>
       first_assum MATCH_ACCEPT_TAC >> NO_TAC) >>
  `log_extends s'⁵' s'⁶'` by
    (qpat_x_assum `finally _ _ _ = _` mp_tac >>
     strip_tac >>
     drule intcall_body_finally_exact_log_extends >> simp[]) >>
  metis_tac[log_extends_trans]
QED


Theorem intcall_success_continuation_guarded_log_extends[local]:
  (do prev <- get_scopes;
      dflt_vs <- finally
        (do x <- set_scopes [FEMPTY];
            eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
              (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         od) (set_scopes prev);
      env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                                (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) st = (res,st') ==>
  (!s0 r s1.
     eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  (!sg prev sg1 dflt_vs sg2 env sg3 rtv sg4 sg5 cxf sg6.
     get_scopes sg = (INL prev,sg1) ==>
     finally
       (do x <- set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od) (set_scopes prev) sg1 = (INL dflt_vs,sg2) ==>
     lift_option_type
       (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
       "IntCall bind_arguments" sg2 = (INL env,sg3) ==>
     lift_option_type (evaluate_type (get_tenv cx) ret)
       "IntCall eval ret" sg3 = (INL rtv,sg4) ==>
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ()) sg4 = (INL (),sg5) ==>
     push_function (src_id_opt,fn) env cx sg5 = (INL cxf,sg6) ==>
     !s0 r s1. eval_stmts cxf body s0 = (r,s1) ==>
                log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `!sg prev sg1 dflt_vs sg2 env sg3 rtv sg4 sg5 cxf sg6. _`
    (mk_asm "guarded") >>
  drule bind_log_extends_forward >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> gvs[] >>
     drule bind_log_extends_forward >> disch_then irule >>
     conj_tac >-
       (rpt strip_tac >> gvs[] >>
        asm "guarded" drule >> disch_then drule >>
        disch_then assume_tac >>
        drule intcall_post_defaults_guarded_log_extends >> simp[]) >>
     rpt strip_tac >>
     drule intcall_defaults_exact_log_extends >> simp[]) >>
  rpt strip_tac >>
  irule log_extends_eq_logs >>
  gvs[vyperStateTheory.get_scopes_def, vyperStateTheory.return_def]
QED

Theorem intcall_guarded_continuation_application_probe[local]:
  (do prev <- get_scopes;
      dflt_vs <- finally
        (do x <- set_scopes [FEMPTY];
            eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
              (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         od) (set_scopes prev);
      env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                                (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) st = (res,st') ==>
  (!s0 r s1.
     eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  (!sg prev sg1 dflt_vs sg2 env sg3 rtv sg4 sg5 cxf sg6.
     get_scopes sg = (INL prev,sg1) ==>
     finally
       (do x <- set_scopes [FEMPTY];
           eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
             (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
        od) (set_scopes prev) sg1 = (INL dflt_vs,sg2) ==>
     lift_option_type
       (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
       "IntCall bind_arguments" sg2 = (INL env,sg3) ==>
     lift_option_type (evaluate_type (get_tenv cx) ret)
       "IntCall eval ret" sg3 = (INL rtv,sg4) ==>
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                         (mut = View \/ mut = Pure)
      else return ()) sg4 = (INL (),sg5) ==>
     push_function (src_id_opt,fn) env cx sg5 = (INL cxf,sg6) ==>
     !s0 r s1. eval_stmts cxf body s0 = (r,s1) ==>
                log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule intcall_success_continuation_guarded_log_extends >>
  disch_then drule >>
  disch_then drule >>
  simp[]
QED

Theorem intcall_success_continuation_log_extends[local]:
  (do prev <- get_scopes;
      dflt_vs <- finally
        (do x <- set_scopes [FEMPTY];
            eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
              (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
         od) (set_scopes prev);
      env <- lift_option_type
               (bind_arguments (get_tenv cx) args (vs ++ dflt_vs))
               "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type (get_tenv cx) ret)
               "IntCall eval ret";
      x <- if nr then
             case cx.nonreentrant_slot of
               NONE => raise (Error (TypeError "nonreentrant slot missing"))
             | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                                (mut = View \/ mut = Pure)
           else return ();
      cxf <- push_function (src_id_opt,fn) env cx;
      rv <- finally
              (try (do x <- eval_stmts cxf body; return NoneV od)
                   handle_function)
              (do x <- pop_function prev;
                  if nr /\ mut <> View /\ mut <> Pure then
                    case cx.nonreentrant_slot of
                      NONE => return ()
                    | SOME slot =>
                        release_nonreentrant_lock cx.txn.target slot
                  else return ()
               od);
      crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
      return (Value crv)
   od) st = (res,st') ==>
  (!s0 r s1.
     eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
       (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  (!s0 r s1.
     eval_stmts (cx with stk updated_by CONS (src_id_opt,fn)) body s0 =
       (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  drule bind_log_extends_forward >> disch_then irule >>
  conj_tac >-
    (rpt strip_tac >> gvs[] >>
     drule bind_log_extends_forward >> disch_then irule >>
     conj_tac >-
       (rpt strip_tac >> gvs[] >>
        drule intcall_post_defaults_log_extends >> simp[]) >>
     rpt strip_tac >>
     drule intcall_defaults_exact_log_extends >> simp[]) >>
  rpt strip_tac >>
  irule log_extends_eq_logs >>
  gvs[vyperStateTheory.get_scopes_def, vyperStateTheory.return_def]
QED



Theorem ext_call_tail_log_extends[local]:
  (do x <- assert success (Error (RuntimeError "ExtCall reverted"));
      x <- update_accounts (K accounts');
      x <- update_transient (K tStorage');
      x <- append_logs emitted_logs;
      if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
      else do
        ret_val <- lift_sum_runtime
          (evaluate_abi_decode_return tenv ret_type returnData);
        return (Value ret_val)
      od
   od) st = (res,st') ==>
  (!e. drv = SOME e ==>
     !s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  Cases_on `success` >> Cases_on `drv` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
       vyperInterpreterTheory.append_logs_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_append] >>
  Cases_on `returnData = []` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  TRY (imp_res_tac lift_sum_runtime_state >> gvs[] >>
       simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> NO_TAC) >>
  qpat_x_assum `!s0 r s1. eval_expr cx x s0 = (r,s1) ==> _`
    (qspecl_then [`st with <|logs := st.logs ++ emitted_logs;
                    accounts := accounts'; tStorage := tStorage'|>`,
                  `res`, `st'`] mp_tac) >>
  simp[] >> strip_tac >>
  irule log_extends_trans >> qexists_tac `st with <|logs := st.logs ++ emitted_logs;
    accounts := accounts'; tStorage := tStorage'|>` >>
  simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED
Theorem ext_call_result_tail_log_extends[local]:
  (!e. drv = SOME e ==>
     !s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) /\
  (if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
   else do
     ret_val <- lift_sum_runtime
       (evaluate_abi_decode_return tenv ret_type returnData);
     return (Value ret_val)
   od)
    (st with <|logs := st.logs ++ emitted_logs;
               accounts := accounts'; tStorage := tStorage'|>) = (res,st') ==>
  log_extends st st'
Proof
  Cases_on `drv` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `returnData = []` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  TRY (imp_res_tac lift_sum_runtime_state >> gvs[] >>
       simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND] >> NO_TAC) >>
  qpat_x_assum `!s0 r s1. eval_expr cx x s0 = (r,s1) ==> _`
    (qspecl_then [`st with <|logs := st.logs ++ emitted_logs;
                    accounts := accounts'; tStorage := tStorage'|>`,
                  `res`, `st'`] mp_tac) >>
  simp[] >> strip_tac >>
  irule log_extends_trans >>
  qexists_tac `st with <|logs := st.logs ++ emitted_logs;
    accounts := accounts'; tStorage := tStorage'|>` >>
  simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Definition ext_call_finish_def:
  ext_call_finish cx drv ret_type tenv result =
    (\(success,returnData,accounts',tStorage',emitted_logs).
      do
        x <- assert success (Error (RuntimeError "ExtCall reverted"));
        x <- update_accounts (K accounts');
        x <- update_transient (K tStorage');
        x <- append_logs emitted_logs;
        if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
        else do
          ret_val <- lift_sum_runtime
            (evaluate_abi_decode_return tenv ret_type returnData);
          return (Value ret_val)
        od
      od) result
End

Theorem ext_call_finish_fold[local]:
  (\(success,returnData,accounts',tStorage',emitted_logs).
    do
      x <- assert success (Error (RuntimeError "ExtCall reverted"));
      x <- update_accounts (K accounts');
      x <- update_transient (K tStorage');
      x <- append_logs emitted_logs;
      if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
      else do
        ret_val <- lift_sum_runtime
          (evaluate_abi_decode_return tenv ret_type returnData);
        return (Value ret_val)
      od
    od) result = ext_call_finish cx drv ret_type tenv result
Proof
  PairCases_on `result` >> simp[ext_call_finish_def]
QED

Theorem ext_call_finish_check_fold[local]:
  (\(success,returnData,accounts',tStorage',emitted_logs).
    do
      check success "ExtCall reverted";
      update_accounts (K accounts');
      update_transient (K tStorage');
      append_logs emitted_logs;
      if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
      else do
        ret_val <- lift_sum_runtime
          (evaluate_abi_decode_return tenv ret_type returnData);
        return (Value ret_val)
      od
    od) result = ext_call_finish cx drv ret_type tenv result
Proof
  PairCases_on `result` >>
  simp[ext_call_finish_def, vyperStateTheory.check_def,
       vyperStateTheory.ignore_bind_def]
QED

Theorem ext_call_finish_log_extends[local]:
  ext_call_finish cx drv ret_type tenv result st = (res,st') ==>
  (!e. drv = SOME e ==>
     !s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  PairCases_on `result` >> simp[ext_call_finish_def] >>
  metis_tac[ext_call_tail_log_extends]
QED

Theorem ext_call_result_log_extends[local]:
  ((\(success,returnData,accounts',tStorage',emitted_logs).
      do
        x <- assert success (Error (RuntimeError "ExtCall reverted"));
        x <- update_accounts (K accounts');
        x <- update_transient (K tStorage');
        x <- append_logs emitted_logs;
        if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
        else do
          ret_val <- lift_sum_runtime
            (evaluate_abi_decode_return tenv ret_type returnData);
          return (Value ret_val)
        od
      od) result st = (res,st')) ==>
  (!e. drv = SOME e ==>
     !s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rewrite_tac[ext_call_finish_fold] >>
  metis_tac[ext_call_finish_log_extends]
QED

Theorem run_ext_call_lift_option_state[local]:
  lift_option
    (run_ext_call caller target calldata value_opt accounts tStorage params)
    msg st = (res,st') ==>
  st' = st
Proof
  metis_tac[lift_option_state]
QED

Theorem bind_state_preserving_log_extends[local]:
  (!out s1. m st = (out,s1) ==> s1 = st) /\
  (!x r s1. k x st = (r,s1) ==> log_extends st s1) /\
  (do x <- m; k x od) st = (res,st') ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  Cases_on `m st` >>
  gvs[vyperStateTheory.bind_def] >>
  Cases_on `q` >> gvs[log_extends_refl] >>
  metis_tac[]
QED

Definition ext_call_after_args_with_def:
  ext_call_after_args_with cx isc func_name arg_types vs k =
    do
      type_check (vs <> []) "ExtCall no target";
      target_addr <- lift_option_type (dest_AddressV (HD vs))
                       "ExtCall target not address";
      (value_opt,arg_vals) <- if (isc:bool) then return (NONE,TL vs)
        else do
          type_check (TL vs <> []) "ExtCall no value";
          v <- lift_option_type (dest_NumV (HD (TL vs)))
                 "ExtCall value not int";
          return (SOME v,TL (TL vs))
        od;
      tenv <<- get_tenv cx;
      calldata <- lift_option_type
        (build_ext_calldata tenv func_name arg_types arg_vals)
        "ExtCall build_calldata";
      accounts <- get_accounts;
      check (~NULL (lookup_account target_addr accounts).code)
        "ExtCall target has no code";
      tStorage <- get_transient_storage;
      result <- lift_option
        (run_ext_call cx.txn.target target_addr calldata value_opt accounts
           tStorage (vyper_to_tx_params cx.txn)) "ExtCall run failed";
      k tenv result
    od
End

Theorem ext_call_generated_success_certificate[local]:
  type_check (vs <> []) "ExtCall no target" s = (INL (),s) /\
  lift_option_type (dest_AddressV (HD vs)) "ExtCall target not address"
    s = (INL target_addr,s) /\
  (if static then return (NONE,TL vs)
   else do
     type_check (TL vs <> []) "ExtCall no value";
     v <- lift_option_type (dest_NumV (HD (TL vs)))
            "ExtCall value not int";
     return (SOME v,TL (TL vs))
   od) s = (INL (value_opt,arg_vals),s) /\
  lift_option_type
    (build_ext_calldata (get_tenv cx) func_name arg_types arg_vals)
    "ExtCall build_calldata" s = (INL calldata,s) /\
  get_accounts s = (INL accounts,s) /\
  check (~NULL (lookup_account target_addr accounts).code)
    "ExtCall target has no code" s = (INL (),s) /\
  get_transient_storage s = (INL tStorage,s) /\
  lift_option
    (run_ext_call cx.txn.target target_addr calldata value_opt accounts
       tStorage (vyper_to_tx_params cx.txn))
    "ExtCall run failed" s =
      (INL (T,[],accounts',tStorage',emitted_logs),s) ==>
  ext_call_after_args_with cx static func_name arg_types vs
    (\tenv result. return (tenv,result)) s =
    (INL (get_tenv cx,(T,[],accounts',tStorage',emitted_logs)),s)
Proof
  rpt strip_tac >>
  simp[ext_call_after_args_with_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def,
      vyperStateTheory.check_def, vyperStateTheory.type_check_def,
      vyperStateTheory.assert_def, vyperStateTheory.get_accounts_def,
      vyperStateTheory.get_transient_storage_def, AllCaseEqs()]
QED

Theorem ext_call_generated_success_certificate_elim[local]:
  ext_call_after_args_with cx static func_name arg_types vs
    (\tenv result. return (tenv,result)) s =
    (INL (get_tenv cx,(T,[],accounts',tStorage',emitted_logs)),s) ==>
  ?target_addr value_opt arg_vals calldata accounts tStorage.
    type_check (vs <> []) "ExtCall no target" s = (INL (),s) /\
    lift_option_type (dest_AddressV (HD vs)) "ExtCall target not address" s =
      (INL target_addr,s) /\
    (if static then return (NONE,TL vs)
     else do
       type_check (TL vs <> []) "ExtCall no value";
       v <- lift_option_type (dest_NumV (HD (TL vs)))
              "ExtCall value not int";
       return (SOME v,TL (TL vs))
     od) s = (INL (value_opt,arg_vals),s) /\
    lift_option_type
      (build_ext_calldata (get_tenv cx) func_name arg_types arg_vals)
      "ExtCall build_calldata" s = (INL calldata,s) /\
    get_accounts s = (INL accounts,s) /\
    check (~NULL (lookup_account target_addr accounts).code)
      "ExtCall target has no code" s = (INL (),s) /\
    get_transient_storage s = (INL tStorage,s) /\
    lift_option
      (run_ext_call cx.txn.target target_addr calldata value_opt accounts
         tStorage (vyper_to_tx_params cx.txn))
      "ExtCall run failed" s =
        (INL (T,[],accounts',tStorage',emitted_logs),s)
Proof
  simp[ext_call_after_args_with_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  rpt strip_tac >>
  imp_res_tac lift_option_type_state >>
  imp_res_tac run_ext_call_lift_option_state >>
  pairarg_tac >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def,
      vyperStateTheory.check_def, vyperStateTheory.type_check_def,
      vyperStateTheory.assert_def, vyperStateTheory.get_accounts_def,
      vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  imp_res_tac lift_option_type_state >>
  imp_res_tac run_ext_call_lift_option_state >>
  gvs[] >>
  metis_tac[]
QED

Theorem ext_call_generated_success_certificate_tenv[local]:
  ext_call_after_args_with cx static func_name arg_types vs
    (\tenv result. return (tenv,result)) s = (INL (tenv,result),s) ==>
  tenv = get_tenv cx
Proof
  simp[ext_call_after_args_with_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  rpt strip_tac >>
  pairarg_tac >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def,
      vyperStateTheory.check_def, vyperStateTheory.type_check_def,
      vyperStateTheory.assert_def, vyperStateTheory.get_accounts_def,
      vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  metis_tac[]
QED


Theorem ext_call_after_args_with_log_extends_snd[local]:
  (!tenv result s0.
     log_extends s0 (SND (k tenv result s0))) ==>
  !st. log_extends st
    (SND (ext_call_after_args_with cx isc func_name arg_types vs k st))
Proof
  Cases_on `isc` >> rpt strip_tac >>
  simp[ext_call_after_args_with_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[log_extends_refl]) >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[log_extends_refl]) >>
  imp_res_tac lift_option_type_state >>
  imp_res_tac run_ext_call_lift_option_state >>
  gvs[log_extends_refl]
QED

Theorem ext_call_after_args_with_guarded_log_extends_snd[local]:
  (!tenv result.
     ext_call_after_args_with cx isc func_name arg_types vs
       (\tenv result. return (tenv,result)) st =
       (INL (tenv,result),st) ==>
     log_extends st (SND (k tenv result st))) ==>
  log_extends st
    (SND (ext_call_after_args_with cx isc func_name arg_types vs k st))
Proof
  Cases_on `isc` >> rpt strip_tac >>
  simp[ext_call_after_args_with_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[log_extends_refl]) >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       vyperStateTheory.check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  rpt (CASE_TAC >> gvs[log_extends_refl]) >>
  imp_res_tac lift_option_type_state >>
  imp_res_tac run_ext_call_lift_option_state >>
  gvs[log_extends_refl] >>
  first_x_assum irule >>
  simp[ext_call_after_args_with_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()]
QED

Theorem lift_sum_runtime_return_after_append_log_extends[local]:
  log_extends st
    (SND
      (case lift_sum_runtime decoded
              (st with <|logs := st.logs ++ emitted_logs;
                         accounts := accounts'; tStorage := tStorage'|>) of
         (INL ret_val,s'') => (INL (Value ret_val),s'')
       | (INR err,s'') => (INR err,s'')))
Proof
  Cases_on `lift_sum_runtime decoded
    (st with <|logs := st.logs ++ emitted_logs;
               accounts := accounts'; tStorage := tStorage'|>)` >>
  imp_res_tac lift_sum_runtime_state >>
  Cases_on `q` >>
  gvs[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem eval_expr_after_append_log_extends[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st
    (SND (eval_expr cx e
      (st with <|logs := st.logs ++ emitted_logs;
                 accounts := accounts'; tStorage := tStorage'|>)))
Proof
  strip_tac >>
  Cases_on `eval_expr cx e
    (st with <|logs := st.logs ++ emitted_logs;
               accounts := accounts'; tStorage := tStorage'|>)` >>
  simp[] >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >>
  qexists_tac `st with <|logs := st.logs ++ emitted_logs;
    accounts := accounts'; tStorage := tStorage'|>` >>
  simp[log_extends_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem ext_call_after_args_finish_guarded_log_extends[local]:
  (!tenv accounts' tStorage' emitted_logs e.
     drv = SOME e /\
     ext_call_after_args_with cx isc func_name arg_types vs
       (\tenv result. return (tenv,result)) st =
       (INL (tenv,(T,[],accounts',tStorage',emitted_logs)),st) ==>
     !s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st
    (SND (ext_call_after_args_with cx isc func_name arg_types vs
      (\tenv result. ext_call_finish cx drv ret_type tenv result) st))
Proof
  strip_tac >>
  irule ext_call_after_args_with_guarded_log_extends_snd >>
  rpt strip_tac >>
  PairCases_on `result` >>
  Cases_on `result0` >> Cases_on `drv` >>
  simp[ext_call_finish_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def,
       vyperStateTheory.update_accounts_def,
       vyperStateTheory.update_transient_def,
       vyperInterpreterTheory.append_logs_def,
       vyperStateTheory.check_def, vyperStateTheory.type_check_def,
       vyperStateTheory.assert_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_append] >>
  Cases_on `result1 = []` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.return_def, AllCaseEqs()] >>
  simp[lift_sum_runtime_return_after_append_log_extends,
       eval_expr_after_append_log_extends, log_extends_refl]
QED

Theorem ext_call_after_args_fold[local]:
  (do type_check (vs <> []) "ExtCall no target";
      target_addr <- lift_option_type (dest_AddressV (HD vs))
                       "ExtCall target not address";
      (value_opt,arg_vals) <- if (isc:bool) then return (NONE,TL vs)
        else do
          type_check (TL vs <> []) "ExtCall no value";
          v <- lift_option_type (dest_NumV (HD (TL vs)))
                 "ExtCall value not int";
          return (SOME v,TL (TL vs))
        od;
      calldata <- lift_option_type
        (build_ext_calldata (get_tenv cx) func_name arg_types arg_vals)
        "ExtCall build_calldata";
      accounts <- get_accounts;
      check (~NULL (lookup_account target_addr accounts).code)
        "ExtCall target has no code";
      tStorage <- get_transient_storage;
      result <- lift_option
        (run_ext_call cx.txn.target target_addr calldata value_opt accounts
           tStorage (vyper_to_tx_params cx.txn)) "ExtCall run failed";
      (\(success,returnData,accounts',tStorage',emitted_logs).
        do
          check success "ExtCall reverted";
          update_accounts (K accounts');
          update_transient (K tStorage');
          append_logs emitted_logs;
          if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
          else do
            ret_val <- lift_sum_runtime
              (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
            return (Value ret_val)
          od
        od) result
   od) =
  ext_call_after_args_with cx isc func_name arg_types vs
    (\tenv result. ext_call_finish cx drv ret_type tenv result)
Proof
  simp[ext_call_after_args_with_def, ext_call_finish_def,
       vyperStateTheory.check_def, vyperStateTheory.ignore_bind_def]
QED

Theorem ext_call_after_args_log_extends[local]:
  (do type_check (vs <> []) "ExtCall no target";
      target_addr <- lift_option_type (dest_AddressV (HD vs))
                       "ExtCall target not address";
      (value_opt,arg_vals) <- if (isc:bool) then return (NONE,TL vs)
        else do
          type_check (TL vs <> []) "ExtCall no value";
          v <- lift_option_type (dest_NumV (HD (TL vs)))
                 "ExtCall value not int";
          return (SOME v,TL (TL vs))
        od;
      calldata <- lift_option_type
        (build_ext_calldata (get_tenv cx) func_name arg_types arg_vals)
        "ExtCall build_calldata";
      accounts <- get_accounts;
      check (~NULL (lookup_account target_addr accounts).code)
        "ExtCall target has no code";
      tStorage <- get_transient_storage;
      result <- lift_option
        (run_ext_call cx.txn.target target_addr calldata value_opt accounts
           tStorage (vyper_to_tx_params cx.txn)) "ExtCall run failed";
      (\(success,returnData,accounts',tStorage',emitted_logs).
        do
          check success "ExtCall reverted";
          update_accounts (K accounts');
          update_transient (K tStorage');
          append_logs emitted_logs;
          if returnData = [] /\ IS_SOME drv then eval_expr cx (THE drv)
          else do
            ret_val <- lift_sum_runtime
              (evaluate_abi_decode_return (get_tenv cx) ret_type returnData);
            return (Value ret_val)
          od
        od) result
   od) st = (res,st') ==>
  (!e. drv = SOME e ==>
     !s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  `!tenv result s0.
     log_extends s0
       (SND (ext_call_finish cx drv ret_type tenv result s0))` by
    (rpt gen_tac >>
     Cases_on `ext_call_finish cx drv ret_type tenv result s0` >>
     simp[] >>
     drule ext_call_finish_log_extends >>
     disch_then irule >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  pure_rewrite_tac[ext_call_finish_check_fold, ext_call_after_args_fold] >>
  strip_tac >>
  `log_extends st
     (SND (ext_call_after_args_with cx isc func_name arg_types vs
       (\tenv result. ext_call_finish cx drv ret_type tenv result) st))` by
    (irule ext_call_after_args_with_log_extends_snd >> simp[]) >>
  gvs[]
QED


Theorem case_expr_ext_call_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 vs s1 tenv accounts' tStorage' emitted_logs e.
     eval_exprs cx es s0 = (INL vs,s1) /\
     drv = SOME e /\
     ext_call_after_args_with cx static func_name arg_types vs
       (\tenv result. return (tenv,result)) s1 =
       (INL (tenv,(T,[],accounts',tStorage',emitted_logs)),s1) ==>
     !u0 r u1. eval_expr cx e u0 = (r,u1) ==> log_extends u0 u1) ==>
  !st res st'.
    eval_expr cx (Call ty (ExtCall static (func_name,arg_types,ret_type))
                         es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def,
       vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  qpat_x_assum `!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> _`
    drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  qpat_x_assum `(do _ od) _ = _` mp_tac >>
  pure_rewrite_tac[ext_call_finish_check_fold, ext_call_after_args_fold] >>
  strip_tac >>
  `log_extends s''
     (SND (ext_call_after_args_with cx static func_name arg_types vs
       (\tenv result. ext_call_finish cx drv ret_type tenv result) s''))` by
    (irule ext_call_after_args_finish_guarded_log_extends >>
     rpt strip_tac >>
     first_x_assum irule >>
     metis_tac[]) >>
  gvs[]
QED

Theorem raw_call_tail_log_extends[local]:
  (do x <- update_accounts (K accounts');
      x <- update_transient (K tStorage');
      x <- append_logs emitted_logs;
      if flags.rcf_revert_on_failure then do
        x <- check success "raw_call reverted";
        if flags.rcf_max_outsize = 0 then return (Value NoneV)
        else return (Value (BytesV (TAKE flags.rcf_max_outsize returnData)))
      od else if flags.rcf_max_outsize = 0 then return (Value (BoolV success))
      else return (Value (ArrayV (TupleV
        [BoolV success; BytesV (TAKE flags.rcf_max_outsize returnData)])))
   od) st = (res,st') ==> log_extends st st'
Proof
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `success` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       vyperStateTheory.update_accounts_def, vyperStateTheory.update_transient_def,
       vyperInterpreterTheory.append_logs_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       log_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem case_expr_raw_call_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty (RawCallTarget flags) es drv) st =
    (res,st') ==> log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.evaluate_def] >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, vyperStateTheory.check_def,
       vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
       vyperStateTheory.get_accounts_def,
       vyperStateTheory.get_transient_storage_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[log_extends_refl] >>
  imp_res_tac lift_option_type_state >> imp_res_tac lift_option_state >> gvs[] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac raw_call_tail_log_extends >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  irule raw_call_tail_log_extends >>
  simp[vyperStateTheory.check_def] >>
  qexistsl [`accounts'`, `emitted_logs`, `flags`, `res`, `returnData`,
            `success`, `tStorage'`] >>
  first_assum ACCEPT_TAC
QED

Theorem case_expr_raw_log_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty RawLog es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac type_check_state >> imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac push_log_log_extends >> imp_res_tac return_state >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  irule log_extends_trans >> goal_assum drule >>
  simp[log_extends_append]
QED

Theorem case_expr_raw_revert_logs[local]:
  (!s0 r s1. eval_exprs cx es s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Call ty RawRevert es drv) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac type_check_state >> imp_res_tac raise_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem case_expr_attribute_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) ==>
  !st res st'. eval_expr cx (Attribute ty e id) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac get_Value_state >> imp_res_tac lift_sum_state >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem case_expr_type_builtin_logs[local]:
  (!s0 s1.
     type_check (type_builtin_args_length_ok tb (LENGTH es))
       "TypeBuiltin args" s0 = (INL (),s1) ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_expr cx (TypeBuiltin ty tb typ es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac type_check_guard_specialize >>
  imp_res_tac type_check_state >> imp_res_tac lift_sum_state >> gvs[] >>
  TRY (simp[log_extends_refl] >> NO_TAC) >>
  first_x_assum drule >> simp[]
QED


Theorem case_eval_exprs_nil_logs[local]:
  eval_exprs cx [] st = (res,st') ==> log_extends st st'
Proof
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.return_def,
       log_extends_refl]
QED

Theorem case_eval_exprs_cons_logs[local]:
  (!s0 r s1. eval_expr cx e s0 = (r,s1) ==> log_extends s0 s1) /\
  (!s0 tv s1 s2 v s3.
     eval_expr cx e s0 = (INL tv,s1) /\
     materialise cx tv s2 = (INL v,s3) ==>
     !st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st') ==>
  !st res st'. eval_exprs cx (e::es) st = (res,st') ==>
    log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.evaluate_def, vyperStateTheory.bind_def,
       vyperStateTheory.return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac materialise_state >> gvs[] >>
  rpt (first_x_assum drule >> strip_tac >> gvs[]) >>
  irule log_extends_trans >> goal_assum drule >>
  first_assum MATCH_ACCEPT_TAC
QED


local
  fun last_imp_ante tm =
    let
      val (_,body) = boolSyntax.strip_forall tm
      val (ante,conseq) = boolSyntax.dest_imp body
      val (_,next) = boolSyntax.strip_forall conseq
    in
      if boolSyntax.is_imp next then
        let val (depth,last) = last_imp_ante conseq in (depth + 1,last) end
      else (1,ante)
    end

  fun is_guarded_eval_ih name tm =
    let
      val (depth,ante) = last_imp_ante tm
      val (lhs,_) = boolSyntax.dest_eq ante
      val (head,_) = boolSyntax.dest_strip_comb lhs
    in
      depth > 1 andalso head = name
    end handle _ => false

  fun specialize_guard_then 0 ttac th = ttac th
    | specialize_guard_then n ttac th =
        first_assum (fn ath =>
          specialize_guard_then (n - 1) ttac
            (MATCH_MP (PURE_REWRITE_RULE [GSYM AND_IMP_INTRO] th) ath))
in
  val specialize_guard_then = specialize_guard_then
  val is_guarded_eval_expr_ih =
    is_guarded_eval_ih "vyperInterpreter$eval_expr"
  val is_guarded_eval_exprs_ih =
    is_guarded_eval_ih "vyperInterpreter$eval_exprs"
  val is_guarded_eval_stmts_ih =
    is_guarded_eval_ih "vyperInterpreter$eval_stmts"
  fun TOP_CASE_IF_PRESENT_TAC g =
    ((BasicProvers.TOP_CASE_TAC ORELSE ALL_TAC) g)
  fun unfold_last_eval_ante_conv tm =
    if boolSyntax.is_forall tm then
      QUANT_CONV unfold_last_eval_ante_conv tm
    else if boolSyntax.is_imp tm then
      let
        val (_,conseq) = boolSyntax.dest_imp tm
        val (_,body) = boolSyntax.strip_forall conseq
      in
        if boolSyntax.is_imp body then
          RAND_CONV unfold_last_eval_ante_conv tm
        else
          LAND_CONV
            (LAND_CONV
              (SCONV [Once vyperInterpreterTheory.evaluate_def,
                      vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def,
                      vyperStateTheory.return_def,
                      vyperStateTheory.raise_def])) tm
      end
    else raise ERR "unfold_last_eval_ante_conv" "expected guarded implication"
  fun commute_outer_ante_conv tm =
    if boolSyntax.is_forall tm then
      QUANT_CONV commute_outer_ante_conv tm
    else if boolSyntax.is_imp tm then
      LAND_CONV (REWR_CONV CONJ_COMM) tm
    else raise ERR "commute_outer_ante_conv" "expected implication"
  fun APPLY_CASE_HELPER_TAC th =
    FIRST_PROVE
      [MATCH_ACCEPT_TAC th,
       rpt gen_tac >> disch_tac >> ho_match_mp_tac th >>
       TRY (qpat_x_assum `_ /\ _` strip_assume_tac) >>
       rpt conj_tac >> first_assum MATCH_ACCEPT_TAC]
  fun APPLY_NORMALIZED_CASE_HELPER_TAC th =
    APPLY_CASE_HELPER_TAC (CONV_RULE unfold_last_eval_ante_conv th)
  val eval_case_helpers =
    [case_iterator_array_logs, case_iterator_range_logs,
     case_target_base_logs, case_target_tuple_logs,
     case_eval_targets_nil_logs, case_eval_targets_cons_logs,
     case_eval_for_nil_logs, case_eval_for_cons_logs,
     case_eval_stmts_nil_logs, case_eval_stmts_cons_logs,
     case_stmt_annassign_logs, case_stmt_append_logs, case_stmt_assign_logs,
     case_stmt_augassign_logs, case_stmt_return_some_logs,
     case_stmt_expr_logs, case_stmt_if_logs, case_stmt_for_logs,
     case_stmt_raise_logs, case_stmt_assert_logs,
     case_stmt_assert_bare_logs, case_stmt_assert_unreachable_logs,
     case_stmt_log_logs,
     case_base_target_name_logs, case_base_target_toplevel_logs,
     case_base_target_attribute_logs, case_base_target_subscript_logs,
     case_expr_name_logs, case_expr_toplevel_name_logs,
     case_expr_flag_member_logs, lookup_global_log_extends,
     lookup_flag_mem_log_extends, case_expr_subscript_logs, case_expr_pop_logs,
     case_expr_builtin_logs, case_expr_if_logs, case_expr_struct_lit_logs,
     case_expr_send_logs, case_expr_selfdestruct_logs, case_expr_create_logs,
     case_expr_ext_call_logs, case_expr_raw_call_logs,
     case_expr_raw_log_logs, case_expr_raw_revert_logs,
     case_expr_attribute_logs, case_expr_type_builtin_logs,
     case_eval_exprs_nil_logs, case_eval_exprs_cons_logs]
end

Theorem conjunction_guard_specialize_probe[local]:
  (!x y. f x = a /\ g y = b ==> P x y) ==>
  f u = a ==>
  g v = b ==>
  P u v
Proof
  rpt strip_tac >>
  first_x_assum (specialize_guard_then 2 MATCH_ACCEPT_TAC)
QED

val REST_ATOMIC_DISPATCH_TAC =
  FIRST
    ([rpt gen_tac >> disch_tac >>
      ho_match_mp_tac
        (CONV_RULE commute_outer_ante_conv case_stmt_assign_logs) >>
      first_assum MATCH_ACCEPT_TAC,
      rpt gen_tac >> strip_tac >>
      ho_match_mp_tac case_eval_targets_cons_logs >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC,
      rpt gen_tac >> strip_tac >>
      ho_match_mp_tac case_stmt_append_logs >>
      rpt conj_tac >> first_assum MATCH_ACCEPT_TAC,
      rpt gen_tac >> strip_tac >>
      ho_match_mp_tac case_expr_ext_call_logs >>
      conj_tac >- first_assum MATCH_ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >>
      drule ext_call_generated_success_certificate_tenv >>
      strip_tac >> gvs[] >>
      drule ext_call_generated_success_certificate_elim >>
      strip_tac >>
      `check T "ExtCall reverted" s1 = (INL (),s1)` by
        simp[vyperStateTheory.check_def, vyperStateTheory.type_check_def,
             vyperStateTheory.assert_def, vyperStateTheory.return_def] >>
      `update_accounts (K accounts') s1 =
       (INL (),s1 with accounts := accounts')` by
        simp[vyperStateTheory.update_accounts_def,
             vyperStateTheory.return_def] >>
      `update_transient (K tStorage') s1 =
       (INL (),s1 with tStorage := tStorage')` by
        simp[vyperStateTheory.update_transient_def,
             vyperStateTheory.return_def] >>
      PRED_ASSUM is_guarded_eval_expr_ih
        (specialize_guard_then 12 MATCH_ACCEPT_TAC)] @
     map APPLY_CASE_HELPER_TAC eval_case_helpers @
     map APPLY_NORMALIZED_CASE_HELPER_TAC eval_case_helpers @
     [simp[Once vyperInterpreterTheory.evaluate_def,
           vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
           vyperStateTheory.return_def, vyperStateTheory.raise_def,
           log_extends_refl]]) >>
  simp[]

Theorem eval_mutual_log_extends[local]:
  (!cx s st res st'. eval_stmt cx s st = (res,st') ==> log_extends st st') /\
  (!cx ss st res st'. eval_stmts cx ss st = (res,st') ==> log_extends st st') /\
  (!cx bt st res st'. eval_base_target cx bt st = (res,st') ==>
     log_extends st st') /\
  (!cx e st res st'. eval_expr cx e st = (res,st') ==> log_extends st st') /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==> log_extends st st')
Proof
  MP_TAC (CONV_RULE (DEPTH_CONV BETA_CONV)
    (SPECL
      [``\cx s. !st res st'. eval_stmt cx s st = (res,st') ==>
           log_extends st st'``,
       ``\cx ss. !st res st'. eval_stmts cx ss st = (res,st') ==>
           log_extends st st'``,
       ``\cx it. !st res st'. eval_iterator cx it st = (res,st') ==>
           log_extends st st'``,
       ``\cx g. !st res st'. eval_target cx g st = (res,st') ==>
           log_extends st st'``,
       ``\cx gs. !st res st'. eval_targets cx gs st = (res,st') ==>
           log_extends st st'``,
       ``\cx bt. !st res st'. eval_base_target cx bt st = (res,st') ==>
           log_extends st st'``,
       ``\cx tyv nm body vs. !st res st'.
           eval_for cx tyv nm body vs st = (res,st') ==> log_extends st st'``,
       ``\cx e. !st res st'. eval_expr cx e st = (res,st') ==>
           log_extends st st'``,
       ``\cx es. !st res st'. eval_exprs cx es st = (res,st') ==>
           log_extends st st'``]
      vyperInterpreterTheory.evaluate_ind)) >>
  impl_tac >-
    (rpt conj_tac >> TRY (simp[] >> NO_TAC) >~
       [`_ ==> !st res st'.
           eval_expr _ (Call _ (IntCall _) _ _) st = (res,st') ==>
           log_extends st st'`] >-
         (rpt gen_tac >> strip_tac >>
          rewrite_tac[Once vyperInterpreterTheory.evaluate_def] >>
          rewrite_tac[vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def] >>
          rpt gen_tac >>
          BasicProvers.TOP_CASE_TAC >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> imp_res_tac type_check_state >>
             gvs[log_extends_refl]) >>
          rewrite_tac[vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def] >>
          BasicProvers.TOP_CASE_TAC >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> imp_res_tac type_check_state >>
             imp_res_tac lift_option_type_state >> gvs[log_extends_refl]) >>
          rewrite_tac[vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def] >>
          BasicProvers.TOP_CASE_TAC >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> imp_res_tac type_check_state >>
             imp_res_tac lift_option_type_state >> gvs[log_extends_refl]) >>
          BasicProvers.LET_ELIM_TAC >>
          qpat_x_assum `_ = _` mp_tac >>
          rewrite_tac[vyperStateTheory.bind_def,
                      vyperStateTheory.ignore_bind_def] >>
          BasicProvers.TOP_CASE_TAC >>
          reverse BasicProvers.TOP_CASE_TAC >-
            (rpt strip_tac >> imp_res_tac type_check_state >>
             imp_res_tac lift_option_type_state >> gvs[log_extends_refl]) >>
          pop_assum mp_tac >>
          first_x_assum $ funpow 2 drule_then drule >>
          simp[] >> ntac 2 strip_tac >>
          first_x_assum drule >> strip_tac >>
          pop_assum $ mk_asm "args_ext" >>
          BasicProvers.TOP_CASE_TAC >>
          TRY (rename1 `eval_exprs cx es _ = (INR _,_)` >>
               asm "args_ext" drule >> simp[] >> NO_TAC) >>
          asm "args_ext" drule >> strip_tac >>
          pop_assum $ mk_asm "explicit_ext" >>
          PRED_ASSUM is_guarded_eval_exprs_ih
            (mk_asm "defaults_guarded") >>
          PRED_ASSUM is_guarded_eval_stmts_ih (mk_asm "body_guarded") >>
          asm "body_guarded" mp_tac >>
          simp[] >> strip_tac >>
          pop_assum $ mk_asm "body_after_explicit" >>
          qpat_x_assum `type_check _ "IntCall args length" _ = _` mp_tac >>
          simp[vyperStateTheory.type_check_def,
               vyperStateTheory.assert_def] >>
          strip_tac >>
          `type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" st =
             (INL (),r)` by
            (qpat_x_assum `type_check _ "recursion" st = _` mp_tac >>
             simp[vyperStateTheory.type_check_def,
                  vyperStateTheory.assert_def]) >>
          `type_check
             (LENGTH es <= LENGTH (FST (SND (SND x''))) /\
              LENGTH (FST (SND (SND x''))) <=
                LENGTH es + LENGTH (FST (SND (SND (SND x'')))))
             "IntCall args length" r' = (INL (),r')` by
            simp[vyperStateTheory.type_check_def,
                 vyperStateTheory.assert_def] >>
          asm "body_after_explicit"
            (specialize_guard_then 4 (mk_asm "body_callback")) >>
          Cases_on `q` >~
            [`eval_exprs cx es _ = (INR _,_)`] >-
              (simp[] >> rpt strip_tac >>
               irule log_extends_trans >>
               qexists `r'³'` >>
               conj_tac >-
                 (imp_res_tac type_check_state >>
                  imp_res_tac lift_option_type_state >>
                  gvs[log_extends_eq_logs]) >>
               asm "explicit_ext" mp_tac >> simp[]) >>
          simp[] >>
          asm "body_callback"
            (specialize_guard_then 1 (mk_asm "body_callback6")) >>
          asm "defaults_guarded" mp_tac >>
          simp[] >> strip_tac >>
          pop_assum $ mk_asm "defaults_ext" >>
          asm "defaults_ext"
            (specialize_guard_then 5 (mk_asm "defaults_admin")) >>
          `get_scopes r'⁴' = (INL r'⁴'.scopes,r'⁴')` by
            simp[vyperStateTheory.get_scopes_def,
                 vyperStateTheory.return_def] >>
          `set_scopes [FEMPTY] r'⁴' =
             (INL (),r'⁴' with scopes := [FEMPTY])` by
            simp[vyperStateTheory.set_scopes_def,
                 vyperStateTheory.return_def] >>
          asm "defaults_admin"
            (specialize_guard_then 2 (mk_asm "defaults_preserves")) >>
          asm_x "defaults_guarded" kall_tac >>
          asm_x "defaults_ext" kall_tac >>
          asm_x "defaults_admin" kall_tac >>
          asm_x "body_guarded" kall_tac >>
          asm_x "body_after_explicit" kall_tac >>
          asm_x "body_callback" kall_tac >>
          simp[] >> strip_tac >>
          pop_assum $ mk_asm "continuation_eq" >>
          `LENGTH dflts + LENGTH es - LENGTH args =
           LENGTH dflts - (LENGTH args - LENGTH es)` by decide_tac >>
          pop_assum $ mk_asm "drop_eq" >>
          asm_x "continuation_eq" mp_tac >>
          asm "drop_eq" (once_rewrite_tac o single) >>
          unabbrev_all_tac >>
          strip_tac >>
          pop_assum $ mk_asm "continuation_eq" >>
          `log_extends r'⁴' st'` by
            (asm_x "body_callback6" mp_tac >>
             asm_x "defaults_preserves" mp_tac >>
             asm_x "continuation_eq" mp_tac >>
             POP_ASSUM_LIST (K all_tac) >>
             rpt strip_tac >>
             drule intcall_guarded_continuation_application_probe >>
             disch_then drule >>
             disch_then irule >>
             rpt strip_tac >>
             gvs[vyperStateTheory.bind_def,
                 vyperStateTheory.ignore_bind_def] >>
             PRED_ASSUM is_guarded_eval_stmts_ih
               (specialize_guard_then 7 MATCH_ACCEPT_TAC)) >>
          irule log_extends_trans >>
          qexists `r'³'` >>
          conj_tac >-
            (imp_res_tac type_check_state >>
             imp_res_tac lift_option_type_state >>
             gvs[log_extends_eq_logs]) >>
          irule log_extends_trans >>
          qexists `r'⁴'` >>
          conj_tac >- asm "explicit_ext" MATCH_ACCEPT_TAC >>
          first_assum MATCH_ACCEPT_TAC) >>
     REST_ATOMIC_DISPATCH_TAC) >>
  strip_tac >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem eval_stmt_log_extends:
  !cx s st res st'.
    eval_stmt cx s st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_expr_log_extends:
  !cx e st res st'.
    eval_expr cx e st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_exprs_log_extends:
  !cx es st res st'.
    eval_exprs cx es st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED

Theorem eval_stmts_log_extends:
  !cx ss st res st'.
    eval_stmts cx ss st = (res,st') ==> log_extends st st'
Proof
  metis_tac[eval_mutual_log_extends]
QED


Definition machine_log_extends_def:
  machine_log_extends (am:abstract_machine) (am':abstract_machine) <=>
    isPREFIX am.logs am'.logs
End

Theorem machine_log_extends_refl:
  machine_log_extends am am
Proof
  simp[machine_log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem machine_log_extends_trans:
  machine_log_extends am am1 /\ machine_log_extends am1 am2 ==>
  machine_log_extends am am2
Proof
  simp[machine_log_extends_def] >>
  metis_tac[rich_listTheory.IS_PREFIX_TRANS]
QED

Theorem machine_log_extends_eq_logs:
  am.logs = am'.logs ==> machine_log_extends am am'
Proof
  simp[machine_log_extends_def, rich_listTheory.IS_PREFIX_REFL]
QED

Theorem abstract_machine_from_state_logs[simp]:
  (abstract_machine_from_state srcs exps layouts st).logs = st.logs
Proof
  simp[vyperInterpreterTheory.abstract_machine_from_state_def]
QED

Theorem merge_constants_logs[local]:
  (merge_constants addr src_id_opt cenv am).logs = am.logs
Proof
  simp[vyperInterpreterTheory.merge_constants_def]
QED

Theorem evaluate_all_constants_logs:
  evaluate_all_constants cx am addr mods = SOME am' ==> am'.logs = am.logs
Proof
  qid_spec_tac `am` >> Induct_on `mods` >-
    simp[vyperInterpreterTheory.evaluate_all_constants_def] >>
  gen_tac >> PairCases_on `h` >> gen_tac >>
  simp[vyperInterpreterTheory.evaluate_all_constants_def, AllCaseEqs()] >>
  rpt strip_tac >>
  first_x_assum drule >>
  simp[merge_constants_logs]
QED

Theorem acquire_nonreentrant_lock_logs[local]:
  acquire_nonreentrant_lock addr slot is_view st = (res,st') ==>
  st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.acquire_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
       vyperStateTheory.raise_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `lookup_storage (n2w slot)
              (vfmExecution$lookup_transient_storage addr st.tStorage) = 1w` >>
  Cases_on `is_view` >>
  gvs[vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def]
QED

Theorem release_nonreentrant_lock_logs[local]:
  release_nonreentrant_lock addr slot st = (res,st') ==>
  st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.release_nonreentrant_lock_def,
       vyperStateTheory.bind_def, vyperStateTheory.get_transient_storage_def,
       vyperStateTheory.update_transient_def, vyperStateTheory.return_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

Theorem send_call_value_logs[local]:
  send_call_value mut cx st = (res,st') ==> st'.logs = st.logs
Proof
  rpt strip_tac >>
  qpat_x_assum `send_call_value _ _ _ = _` mp_tac >>
  simp[vyperInterpreterTheory.send_call_value_def, vyperStateTheory.bind_def,
       vyperStateTheory.ignore_bind_def, vyperStateTheory.check_def,
       vyperStateTheory.return_def, vyperStateTheory.raise_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `cx.txn.value = 0` >> Cases_on `mut = Payable` >>
  gvs[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
      vyperStateTheory.check_def, vyperStateTheory.assert_def,
      vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  imp_res_tac transfer_value_logs >> gvs[]
QED


Theorem entry_lock_action_logs[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot =>
         acquire_nonreentrant_lock cx.txn.target slot is_view
   else return ()) st = (res,st') ==>
  st'.logs = st.logs
Proof
  Cases_on `nr` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  metis_tac[acquire_nonreentrant_lock_logs]
QED

Theorem exit_unlock_action_logs[local]:
  (if nr /\ ~is_view then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.logs = st.logs
Proof
  Cases_on `nr` >> Cases_on `is_view` >> Cases_on `cx.nonreentrant_slot` >>
  simp[vyperStateTheory.return_def] >>
  metis_tac[release_nonreentrant_lock_logs]
QED

Theorem external_unlock_action_logs[local]:
  (if nr /\ mut <> View /\ mut <> Pure then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.logs = st.logs
Proof
  Cases_on `nr` >> Cases_on `mut = View` >> Cases_on `mut = Pure` >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[vyperStateTheory.return_def] >>
  metis_tac[release_nonreentrant_lock_logs]
QED

Theorem call_body_pipeline_log_extends[local]:
  (do lock_action; send_call_value mut cx; eval_stmts cx body od) st =
    (res,st') ==>
  (!s0 r s1. lock_action s0 = (r,s1) ==> s1.logs = s0.logs) ==>
  log_extends st st'
Proof
  rpt strip_tac >>
  qpat_x_assum `(do lock_action; send_call_value _ _; eval_stmts _ _ od) _ = _`
    mp_tac >>
  simp[vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac send_call_value_logs >>
  imp_res_tac eval_stmts_log_extends >>
  metis_tac[log_extends_eq_logs, log_extends_trans]
QED
Theorem call_external_function_success_log_extends:
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v,am') ==>
  machine_log_extends am am'
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.call_external_function_def,
       AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `(do
               if nr then
                 case cx.nonreentrant_slot of
                   NONE => raise (Error (TypeError "nonreentrant slot missing"))
                 | SOME slot =>
                     acquire_nonreentrant_lock cx.txn.target slot
                       (mut = View \/ mut = Pure)
               else return ();
               send_call_value mut cx;
               eval_stmts cx body
             od) (initial_state am_c [env])` >>
  Cases_on `q` >> gvs[AllCaseEqs()] >>
  Cases_on `(if nr /\ mut <> View /\ mut <> Pure then
               case cx.nonreentrant_slot of
                 NONE => return ()
               | SOME slot =>
                   release_nonreentrant_lock cx.txn.target slot
             else return ()) r` >>
  Cases_on `q` >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `y` >> gvs[AllCaseEqs()]) >>
  TRY (Cases_on `evaluate_type (type_env_all_modules all_mods) ret` >>
       gvs[AllCaseEqs()]) >>
  TRY (Cases_on `safe_cast x v'` >> gvs[AllCaseEqs()]) >>
  drule call_body_pipeline_log_extends >>
  (impl_tac >-
     (rpt strip_tac >> imp_res_tac entry_lock_action_logs)) >>
  strip_tac >>
  imp_res_tac external_unlock_action_logs >>
  imp_res_tac evaluate_all_constants_logs >>
  gvs[machine_log_extends_def, log_extends_def]
QED

Theorem call_external_success_log_extends:
  call_external am tx = (INL v,am') ==> machine_log_extends am am'
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external _ _ = _` mp_tac >>
  simp[Once vyperInterpreterTheory.call_external_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac call_external_function_success_log_extends
QED

Theorem call_external_function_error_logs_rollback:
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INR e,am') ==>
  am'.logs = am.logs
Proof
  strip_tac >> imp_res_tac call_external_function_error_rollback >> gvs[]
QED

Theorem call_external_error_logs_rollback:
  call_external am tx = (INR e,am') ==> am'.logs = am.logs
Proof
  strip_tac >> imp_res_tac call_external_error_rollback >> gvs[]
QED

Theorem call_external_log_extends:
  call_external am tx = (res,am') ==> machine_log_extends am am'
Proof
  Cases_on `res` >> strip_tac >-
    (imp_res_tac call_external_success_log_extends) >>
  imp_res_tac call_external_error_logs_rollback >>
  simp[machine_log_extends_eq_logs]
QED

Theorem call_external_transaction_log_extends_empty:
  call_external_transaction am tx = (res,am') ==>
  isPREFIX [] am'.logs
Proof
  simp[]
QED

Theorem call_external_transaction_success_fresh:
  call_external_transaction am tx = (INL v,am') ==>
  call_external (clear_machine_logs am) tx = (INL v,am') /\
  machine_log_extends (clear_machine_logs am) am'
Proof
  simp[vyperInterpreterTheory.call_external_transaction_def] >>
  metis_tac[call_external_log_extends]
QED

val _ = export_theory();
