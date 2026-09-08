(*
 * Main mutual evaluator type-soundness proof for the executable Vyper type
 * system.
 *
 * This file contains the helper lemmas and proof of eval_all_type_sound_mutual,
 * covering statements, statement lists, iterators, assignment targets, base
 * targets, for-loop bodies, and expressions.  Statement/list consequences are
 * stated separately in vyperTypeStmtSoundness.
 *)

Theory vyperTypeEvalSoundness
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair sum
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping vyperLookup
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeEnvExtension vyperTypeEnvPreservation vyperTypeScopePop
  vyperTypeABI vyperTypeBindArguments vyperTypeExprResult vyperTypeStmtResult
  vyperTypeExtCallSoundness vyperTypeGlobalLookupSoundness vyperTypeAssignContext vyperTypeBuiltins vyperTypeExprSoundness vyperTypeAssignSoundness
  vyperAssignTarget vyperExprNoControl vyperScopePreservation vyperEvalPreservesScopes
  vyperEvalMisc vyperStatePreservation vyperAssignPreservesType vyperTypeStatePreservation
  vyperTypeCallGraph vyperTypeCallStackSoundness
Libs
  wordsLib markerLib intLib

(* ===== Generic exception/result typing helpers ===== *)

Theorem lift_option_type_INL_eq[local]:
  lift_option_type opt msg st = (INL v,st') <=> opt = SOME v /\ st' = st
Proof
  Cases_on `opt` >> simp[lift_option_type_def, return_def, raise_def] >>
  metis_tac[]
QED

Theorem fn_sigs_consistent_FLOOKUP[local]:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src_id_opt, fn) = SOME sig ==>
  ?ts fm nr params dflts body.
    get_module_code cx src_id_opt = SOME ts /\
    lookup_callable_function cx.in_deploy fn ts =
      SOME (fm, nr, params, dflts, sig.ret_ty, body) /\
    sig.param_types = MAP SND params /\
    sig.num_defaults = LENGTH dflts
Proof
  simp[fn_sigs_consistent_def]
QED

Theorem intcall_lookup_function_not_INR[local]:
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts = SOME v /\
  get_module_code cx src_id_opt = SOME ts' ==>
  lift_option_type (lookup_callable_function cx.in_deploy fn ts') msg st <> (INR e,st')
Proof
  rpt strip_tac >> gvs[lift_option_type_def, return_def]
QED

Theorem intcall_args_length_condition[local]:
  fn_sigs_consistent fn_sigs cx /\
  FLOOKUP fn_sigs (src_id_opt,fn) = SOME sig /\
  lift_option_type (get_module_code cx src_id_opt) msg1 st1 = (INL ts,st1') /\
  lift_option_type (lookup_callable_function cx.in_deploy fn ts) msg2 st2 = (INL tup,st2') /\
  LENGTH es <= LENGTH sig.param_types /\
  LENGTH sig.param_types - sig.num_defaults <= LENGTH es ==>
  LENGTH es <= LENGTH (FST (SND (SND tup))) /\
  LENGTH (FST (SND (SND tup))) <=
    LENGTH es + LENGTH (FST (SND (SND (SND tup))))
Proof
  rpt strip_tac >>
  drule_all fn_sigs_consistent_FLOOKUP >> strip_tac >>
  qpat_x_assum `lift_option_type (get_module_code cx src_id_opt) _ _ = _`
    (fn th => assume_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
  qpat_x_assum `lift_option_type (lookup_callable_function cx.in_deploy fn ts) _ _ = _`
    (fn th => assume_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
  gvs[]
QED

Theorem intcall_call_evaluation_safe_target_not_mem[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) ==>
  ~MEM (src_id_opt,fn) cx.stk
Proof
  simp[int_calls_expr_def] >> strip_tac >>
  irule call_evaluation_safe_target_not_mem >>
  qexists_tac `int_calls_exprs es` >> simp[]
QED

Theorem intcall_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (IntCall callee) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  strip_tac >> irule call_evaluation_safe_mono >>
  qexists_tac `int_calls_expr (Call loc (IntCall callee) es extra)` >>
  simp[int_calls_expr_def]
QED

Theorem intcall_call_evaluation_safe_needed_defaults[local]:
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

Theorem intcall_call_evaluation_safe_body[local]:
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



Theorem int_calls_exprs_MAP_SND[local]:
  !kes. int_calls_exprs (MAP SND kes) = int_calls_named_exprs kes
Proof
  Induct >> simp[int_calls_expr_def] >> gen_tac >> PairCases_on `h` >>
  simp[int_calls_expr_def]
QED

Theorem call_evaluation_safe_int_calls_exprs_HD[local]:
  es <> [] /\ call_evaluation_safe cx (int_calls_exprs es) ==>
  call_evaluation_safe cx (int_calls_expr (HD es))
Proof
  Cases_on `es` >> simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem extcall_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr
      (Call loc (ExtCall is_static' (func_name,arg_types,ret_type)) es drv)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem extcall_call_evaluation_safe_driver[local]:
  call_evaluation_safe cx
    (int_calls_expr
      (Call loc (ExtCall is_static' (func_name,arg_types,ret_type)) es
        (SOME drv))) ==>
  call_evaluation_safe cx (int_calls_expr drv)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem send_call_evaluation_safe_args[local]:
  call_evaluation_safe cx (int_calls_expr (Call loc Send es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawcall_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (RawCallTarget flags) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawlog_call_evaluation_safe_args[local]:
  call_evaluation_safe cx (int_calls_expr (Call loc RawLog es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem rawrevert_call_evaluation_safe_args[local]:
  call_evaluation_safe cx (int_calls_expr (Call loc RawRevert es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem selfdestruct_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc SelfDestructTarget es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem create_call_evaluation_safe_args[local]:
  call_evaluation_safe cx
    (int_calls_expr (Call loc (CreateTarget kind has_salt rof) es extra)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def]
QED

Theorem exprs_cons_call_evaluation_safe_head[local]:
  call_evaluation_safe cx (int_calls_exprs (e::es)) ==>
  call_evaluation_safe cx (int_calls_expr e)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_left]
QED

Theorem exprs_cons_call_evaluation_safe_tail[local]:
  call_evaluation_safe cx (int_calls_exprs (e::es)) ==>
  call_evaluation_safe cx (int_calls_exprs es)
Proof
  simp[int_calls_expr_def] >>
  metis_tac[call_evaluation_safe_append_right]
QED

Theorem well_typed_exprs_DROP:
  !env es n. well_typed_exprs env es ==> well_typed_exprs env (DROP n es)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  rpt strip_tac >> Cases_on `n` >> simp[well_typed_expr_def]
QED

Theorem get_tenv_stk_irrelevant[local]:
  !cx f. get_tenv (cx with stk updated_by f) = get_tenv cx
Proof
  simp[get_tenv_def]
QED

Theorem get_module_code_stk_irrelevant[local]:
  !cx f src. get_module_code (cx with stk updated_by f) src = get_module_code cx src
Proof
  simp[get_module_code_def]
QED

Theorem fn_sigs_consistent_stk_irrelevant[local]:
  !sigs cx f. fn_sigs_consistent sigs (cx with stk updated_by f) <=>
              fn_sigs_consistent sigs cx
Proof
  simp[fn_sigs_consistent_def, get_module_code_def]
QED

Theorem fn_sigs_declared_complete_stk_irrelevant[local]:
  !sigs cx f. fn_sigs_declared_complete sigs (cx with stk updated_by f) <=>
              fn_sigs_declared_complete sigs cx
Proof
  simp[fn_sigs_declared_complete_def, get_module_code_def]
QED

Theorem toplevel_vtypes_complete_stk_irrelevant[local]:
  !toplevel_vtypes cx f.
    toplevel_vtypes_complete toplevel_vtypes (cx with stk updated_by f) <=>
    toplevel_vtypes_complete toplevel_vtypes cx
Proof
  simp[toplevel_vtypes_complete_def, get_module_code_stk_irrelevant]
QED

Theorem bare_globals_complete_stk_irrelevant[local]:
  !bare_globals cx f.
    bare_globals_complete bare_globals (cx with stk updated_by f) <=>
    bare_globals_complete bare_globals cx
Proof
  simp[bare_globals_complete_def, get_module_code_stk_irrelevant]
QED

Theorem bare_global_assignable_complete_stk_irrelevant[local]:
  !bare_global_assignable cx f.
    bare_global_assignable_complete bare_global_assignable (cx with stk updated_by f) <=>
    bare_global_assignable_complete bare_global_assignable cx
Proof
  simp[bare_global_assignable_complete_def, get_module_code_stk_irrelevant]
QED

Theorem flag_members_complete_stk_irrelevant[local]:
  !flag_members cx f.
    flag_members_complete flag_members (cx with stk updated_by f) <=>
    flag_members_complete flag_members cx
Proof
  simp[flag_members_complete_def, get_module_code_stk_irrelevant]
QED

Theorem functions_well_typed_stk_irrelevant[local]:
  !cx f. functions_well_typed (cx with stk updated_by f) <=>
         functions_well_typed cx
Proof
  simp[functions_well_typed_def, get_module_code_def,
       get_tenv_stk_irrelevant, fn_sigs_consistent_stk_irrelevant,
       fn_sigs_declared_complete_stk_irrelevant,
       toplevel_vtypes_complete_stk_irrelevant,
       bare_globals_complete_stk_irrelevant,
       bare_global_assignable_complete_stk_irrelevant,
       flag_members_complete_stk_irrelevant,
       well_formed_type_def]
QED

Theorem context_well_typed_stk_irrelevant[local]:
  !cx f. context_well_typed (cx with stk updated_by f) <=>
         context_well_typed cx
Proof
  simp[context_well_typed_def]
QED
Theorem env_scopes_consistent_stk_irrelevant[local]:
  !env cx f st.
    env_scopes_consistent env (cx with stk updated_by f) st <=>
    env_scopes_consistent env cx st
Proof
  simp[env_scopes_consistent_def, get_tenv_stk_irrelevant]
QED

Theorem type_place_expr_Call_ExtCall_NONE[local]:
  !env ty is_static func_name arg_types ret_type es drv.
    type_place_expr env (Call ty (ExtCall is_static (func_name,arg_types,ret_type)) es drv) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Theorem expr_result_typed_materialise_no_type_error:
  well_typed_expr env e /\
  expr_result_typed env e tv /\
  materialise cx tv st = (INR err, st') ==>
  !msg. err <> Error (TypeError msg)
Proof
  rw[] >>
  spose_not_then assume_tac >>
  gvs[] >>
  drule_then assume_tac materialise_type_error_imp_HashMapRef >>
  gvs[expr_result_typed_def] >>
  metis_tac[well_typed_expr_not_hashmap_place]
QED

Theorem eval_expr_exception_return_typed:
  eval_expr cx e st = (INR exn, st') ==> return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule (cj 1 eval_expr_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Theorem eval_exprs_exception_return_typed:
  eval_exprs cx es st = (INR exn, st') ==> return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  drule (cj 2 eval_expr_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Theorem eval_target_no_control:
  (!tgt cx st exn st'.
    eval_target cx tgt st = (INR exn, st') ==> no_control_exc exn) /\
  (!tgts cx st exn st'.
    eval_targets cx tgts st = (INR exn, st') ==> no_control_exc exn) /\
  (!cx bt st exn st'.
    eval_base_target cx bt st = (INR exn, st') ==> no_control_exc exn)
Proof
  rewrite_tac[CONJ_ASSOC] >>
  reverse conj_asm2_tac >- (
    rpt strip_tac >>
    drule_then irule (cj 1 eval_expr_no_control_with_bt)  ) >>
  ho_match_mp_tac (TypeBase.induction_of``:assignment_target``) >>
  simp[evaluate_def, bind_apply, ignore_bind_apply, AllCaseEqs(),
       EXISTS_PROD, bind_def] >>
  rpt strip_tac >> gvs[return_def] >>
  metis_tac[]
QED

Theorem eval_iterator_no_control:
  !cx it st exn st'.
    eval_iterator cx it st = (INR exn, st') ==> no_control_exc exn
Proof
  Cases_on `it` >>
  rw[evaluate_def, bind_def, return_def, raise_def, lift_option_type_def,
     lift_sum_def, option_CASE_rator, sum_CASE_rator, AllCaseEqs()] >>
  TRY (drule (cj 1 eval_expr_no_control) >> simp[] >> NO_TAC) >>
  TRY (drule materialise_no_control >> simp[] >> NO_TAC) >>
  TRY (drule get_Value_no_control >> simp[] >> NO_TAC) >>
  gvs[AllCaseEqs(), option_CASE_rator, sum_CASE_rator,
      return_def, raise_def, no_control_exc_def]
QED


Theorem value_runtime_typed_env_static:
  env'.type_defs = env.type_defs /\ value_runtime_typed env' ty v ==>
  value_runtime_typed env ty v
Proof
  rw[value_runtime_typed_def] >> metis_tac[]
QED

Theorem materialise_preserves_value_type:
  state_well_typed st /\ toplevel_value_typed tvl tv /\ well_formed_type_value tv /\
  materialise cx tvl st = (INL v, st') ==>
  value_has_type tv v
Proof
  metis_tac[materialise_preserves_type]
QED

Theorem expr_result_typed_runtime_typed:
  expr_result_typed env e tv ==> expr_runtime_typed env e tv
Proof
  rw[expr_result_typed_def]
QED

Theorem expr_result_typed_materialise_preserves_value_type:
  state_well_typed st /\ expr_result_typed env e tvl /\
  evaluate_type env.type_defs (expr_type e) = SOME tyv /\
  materialise cx tvl st = (INL v, st') ==>
  value_has_type tyv v
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def] >> gvs[] >>
  irule materialise_preserves_value_type >> simp[] >>
  metis_tac[evaluate_type_well_formed_type_value]
QED
Theorem annassign_new_variable_after_materialise_sound[local]:
  env_consistent env cx st /\ state_well_typed st /\ accounts_well_typed st.accounts /\
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  expr_type e = typ /\ expr_result_typed env e tvl /\
  string_to_num id NOTIN FDOM env.var_types /\
  materialise cx tvl st = (INL v, st1) /\
  new_variable id tyv v st1 = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL u => env_consistent (extend_local env (string_to_num id) typ T) cx st'
  | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  drule materialise_state >> strip_tac >> gvs[] >>
  `value_has_type tyv v` by
    metis_tac[expr_result_typed_materialise_preserves_value_type] >>
  conj_tac
  >- metis_tac[new_variable_preserves_state_well_typed_result] >>
  conj_tac >- (drule new_variable_accounts >> rw[]) >>
  Cases_on `res` >> gvs[no_type_error_result_def]
  >- metis_tac[extend_local_env_consistent_after_new_variable] >>
  conj_asm1_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_at(Pat`new_variable`) new_variable_no_type_error >>
      simp[] >> goal_assum drule_all) >>
  gvs[new_variable_def, bind_apply, AllCaseEqs(),
      ignore_bind_apply, list_CASE_rator, raise_def,
      get_scopes_def, return_def, type_check_def,
      assert_def, set_scopes_def]
QED
Theorem annassign_statement_sound_from_expr_ih[local]:
  (!env st res st'.
     env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
     accounts_well_typed st.accounts /\ functions_well_typed cx /\
     eval_expr cx e st = (res, st') ==>
     well_typed_expr env e ==>
     state_well_typed st' /\ env_consistent env cx st' /\
     accounts_well_typed st'.accounts /\ no_type_error_result res /\
     case res of INL tv => expr_result_typed env e tv | INR v1 => T) /\
  env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
  accounts_well_typed st.accounts /\ functions_well_typed cx /\
  well_typed_expr env e /\ assignable_type env.type_defs typ /\ expr_type e = typ /\
  string_to_num id NOTIN FDOM env.var_types /\
  get_tenv cx = env.type_defs /\ evaluate_type env.type_defs typ = SOME tyv /\
  eval_stmt cx (AnnAssign id typ e) st = (res, st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
  | INL u => env_consistent (extend_local env (string_to_num id) typ T) cx st'
  | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_stmt cx (AnnAssign id typ e) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
                       return_def, raise_def] >>
  asm_rewrite_tac[] >>
  Cases_on `eval_expr cx e st` >> rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tvl, st1)` >>
    Cases_on `materialise cx tvl st1` >> rename1 `materialise cx tvl st1 = (mat_res, st2)` >>
    Cases_on `mat_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `materialise cx tvl st1 = (INL v, st2)` >>
      strip_tac >>
      `new_variable id tyv v st2 = (res,st')` by (
        qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- materialise cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
        simp[bind_def, return_def, pairTheory.UNCURRY]) >>
      metis_tac[annassign_new_variable_after_materialise_sound,
                no_type_error_result_def]) >>
    rename1 `materialise cx tvl st1 = (INR exn, st2)` >>
    strip_tac >>
    `res = INR exn /\ st' = st2` by (
      qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- materialise cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
      simp[bind_def, return_def, raise_def, pairTheory.UNCURRY]) >>
    gvs[no_type_error_result_def] >>
    `!msg. exn <> Error (TypeError msg)` by
      metis_tac[expr_result_typed_materialise_no_type_error] >>
    drule materialise_state >> strip_tac >> gvs[] >>
    drule materialise_no_control >>
    rw[no_control_exc_return_exception_typed]) >>
  rename1 `eval_expr cx e st = (INR exn, st1)` >>
  strip_tac >>
  `res = INR exn /\ st' = st1` by (
    qpat_x_assum `do tyv <- return tyv; tv <- eval_expr cx e; v <- materialise cx tv; new_variable id tyv v od st = (res,st')` mp_tac >>
    simp[bind_def, return_def, raise_def, pairTheory.UNCURRY]) >>
  gvs[no_type_error_result_def] >>
  drule eval_expr_exception_return_typed >> rw[]
QED

Theorem callable_body_typing_from_env_consistent:
  functions_well_typed cx /\
  env_consistent env cx st /\
  get_module_code cx src_id_opt = SOME ts /\
  lookup_callable_function cx.in_deploy fn ts =
    SOME (fm,nr,args,dflts,ret,fn_body) ==>
  (nr ==> cx.nonreentrant_slot <> NONE) /\
  ?env_body ret_tv env_after.
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args)
Proof
  rw[env_consistent_def, env_context_consistent_def, env_immutables_consistent_def,
     functions_well_typed_def] >>
  first_x_assum
    (qspecl_then [`env.fn_sigs`, `env.bare_globals`,
                  `env.bare_global_assignable`,
                  `env.toplevel_vtypes`, `env.flag_members`] mp_tac) >>
  simp[] >>
  impl_tac
  >- (rpt strip_tac >>
      Cases_on `vt` >> gvs[]
      >- (rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` >>
          rename1 `get_module_code cx src = SOME ts0` >>
          qpat_x_assum
            `!src id ty ts. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ get_module_code cx src = SOME ts ==> _`
            (qspecl_then [`src`,`id`,`ty`,`ts0`] mp_tac) >>
          simp[] >> strip_tac >> simp[] >>
          Cases_on `FLOOKUP env.bare_globals (src,id)`
          >- (qpat_x_assum
                `!src id ty. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP env.bare_globals (src,id) = NONE ==> _`
                (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
              simp[] >> rw[] >> metis_tac[]) >>
          rename1 `FLOOKUP env.bare_globals (src,id) = SOME bare_ty` >>
          `bare_ty = ty` by (
            qpat_x_assum
              `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> ?ts. _`
              (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
            simp[] >> rw[]) >>
          qpat_x_assum
            `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> IS_SOME _`
            (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
          simp[IS_SOME_EXISTS] >> strip_tac >> PairCases_on `x` >>
          qpat_x_assum
            `!src id ty tv v. FLOOKUP env.bare_globals (src,id) = SOME ty /\ FLOOKUP _ id = SOME (tv,v) ==> _`
            (qspecl_then [`src`,`id`,`bare_ty`,`x0`,`x1`] mp_tac) >>
          simp[]) >>
      rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt hv)` >>
      qpat_x_assum
        `!src id kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==> _`
        (qspecl_then [`src`,`id`,`kt`,`hv`] mp_tac) >>
      simp[] >> rw[] >> metis_tac[]) >>
  rw[] >>
  first_x_assum drule_all >> simp[] >>
  rpt strip_tac >>
  Cases_on `vt` >> gvs[]
  >- (rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty)` >>
      rename1 `get_module_code cx src = SOME ts0` >>
      qpat_x_assum
        `!src id ty ts. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ get_module_code cx src = SOME ts ==> _`
        (qspecl_then [`src`,`id`,`ty`,`ts0`] mp_tac) >>
      simp[] >> strip_tac >> simp[] >>
      Cases_on `FLOOKUP env.bare_globals (src,id)`
      >- (qpat_x_assum
            `!src id ty. FLOOKUP env.toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP env.bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
          simp[] >> rw[] >> metis_tac[]) >>
      rename1 `FLOOKUP env.bare_globals (src,id) = SOME bare_ty` >>
      `bare_ty = ty` by (
        qpat_x_assum
          `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> ?ts. _`
          (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
        simp[] >> rw[]) >>
      qpat_x_assum
        `!src id ty. FLOOKUP env.bare_globals (src,id) = SOME ty ==> IS_SOME _`
        (qspecl_then [`src`,`id`,`bare_ty`] mp_tac) >>
      simp[IS_SOME_EXISTS] >> strip_tac >> PairCases_on `x` >>
      qpat_x_assum
        `!src id ty tv v. FLOOKUP env.bare_globals (src,id) = SOME ty /\ FLOOKUP _ id = SOME (tv,v) ==> _`
        (qspecl_then [`src`,`id`,`bare_ty`,`x0`,`x1`] mp_tac) >>
      simp[]) >>
  rename1 `FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt hv)` >>
  qpat_x_assum
    `!src id kt vt. FLOOKUP env.toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==> _`
    (qspecl_then [`src`,`id`,`kt`,`hv`] mp_tac) >>
  simp[] >> rw[] >> metis_tac[]
QED

Theorem intcall_env_body_consistency_for_defaults[local]:
  !env env_body cx st src_id_opt fn.
    env_consistent env cx st /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members ==>
    env_context_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st
Proof
  rw[env_consistent_def]
  >- (gvs[env_context_consistent_def] >>
      rw[env_context_consistent_def, get_tenv_stk_irrelevant,
         fn_sigs_consistent_stk_irrelevant,
         fn_sigs_declared_complete_stk_irrelevant,
         toplevel_vtypes_complete_stk_irrelevant,
         bare_globals_complete_stk_irrelevant,
         bare_global_assignable_complete_stk_irrelevant,
         flag_members_complete_stk_irrelevant,
         get_module_code_stk_irrelevant, current_module_def] >>
      first_x_assum drule_all >> simp[lookup_var_slot_from_layout_def])
  >- (gvs[env_immutables_consistent_def] >>
      rw[env_immutables_consistent_def, get_tenv_stk_irrelevant,
         get_module_code_stk_irrelevant] >>
      first_x_assum drule_all >> simp[])
QED

Theorem intcall_default_env_side_conditions:
  !env env_body cx st src_id_opt fn.
    env_consistent env cx st /\
    state_well_typed st /\
    context_well_typed cx /\
    accounts_well_typed st.accounts /\
    functions_well_typed cx /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members ==>
    env_context_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st /\
    state_well_typed st /\
    context_well_typed (cx with stk updated_by CONS (src_id_opt,fn)) /\
    accounts_well_typed st.accounts /\
    functions_well_typed (cx with stk updated_by CONS (src_id_opt,fn))
Proof
  rpt strip_tac >>
  qspecl_then [`env`, `env_body`, `cx`, `st`, `src_id_opt`, `fn`] mp_tac
    intcall_env_body_consistency_for_defaults >>
  impl_tac >- simp[] >>
  strip_tac >>
  simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]
QED
Theorem no_fallthrough_eval_no_success:
  (!s cx st st'.
      stmt_no_fallthrough s ==>
      eval_stmt cx s st <> (INL (), st')) /\
  (!ss cx st st'.
      stmts_no_fallthrough ss ==>
      eval_stmts cx ss st <> (INL (), st'))
Proof
  ho_match_mp_tac stmt_induction >>
  rw[stmt_no_fallthrough_def, evaluate_def, bind_def, return_def, raise_def,
     pairTheory.UNCURRY, finally_def, ignore_bind_def, switch_BoolV_def, AllCaseEqs()] >>
  TRY (rename1 `eval_stmt cx (Raise reason) st <> _` >>
       Cases_on `reason` >>
       gvs[evaluate_def, bind_def, return_def, raise_def,
           pairTheory.UNCURRY, AllCaseEqs()]) >>
  TRY (rename1 `eval_stmt cx (Return opt_e) st <> _` >>
       Cases_on `opt_e` >>
       gvs[evaluate_def, bind_def, return_def, raise_def,
           pairTheory.UNCURRY, AllCaseEqs()]) >>
  TRY (rename1 `eval_expr cx e st = (INL tv,_)` >>
       Cases_on `tv = Value (BoolV T)` >> gvs[] >>
       Cases_on `tv = Value (BoolV F)` >> gvs[raise_def]) >>
  metis_tac[]
QED
Theorem no_control_exc_no_loop_control[local]:
  no_control_exc exn ==> exn <> BreakException /\ exn <> ContinueException
Proof
  Cases_on `exn` >> rw[no_control_exc_def]
QED
Theorem push_scope_no_control[local]:
  push_scope st = (INR exn,st') ==> no_control_exc exn
Proof
  rw[push_scope_def, return_def, no_control_exc_def]
QED

Theorem pop_scope_no_control[local]:
  pop_scope st = (INR exn,st') ==> no_control_exc exn
Proof
  Cases_on `st.scopes` >> rw[pop_scope_def, return_def, raise_def, no_control_exc_def]
QED

Theorem new_variable_no_control[local]:
  new_variable id tv v st = (INR exn,st') ==> no_control_exc exn
Proof
  rw[new_variable_def, bind_def, ignore_bind_def, type_check_def, assert_def,
     get_scopes_def, AllCaseEqs()] >>
  Cases_on `s''.scopes` >>
  gvs[set_scopes_def, return_def, raise_def, no_control_exc_def]
QED


Theorem eval_for_no_loop_control[local]:
  !vs cx tyv nm body st exn st'.
    eval_for cx tyv nm body vs st = (INR exn,st') ==>
    exn <> BreakException /\ exn <> ContinueException
Proof
  Induct >>
  rw[Once evaluate_def, bind_def, ignore_bind_def, try_def, finally_def,
     push_scope_with_var_def, pop_scope_def, handle_loop_exception_def,
     return_def, raise_def, AllCaseEqs()] >>
  gvs[return_def] >>
  TRY (Cases_on `e` >> gvs[handle_loop_exception_def, return_def, raise_def]) >>
  res_tac >>
  gvs[]
QED
Theorem eval_stmt_assert_no_loop_control[local]:
  !a e cx st exn st'.
    eval_stmt cx (Assert e a) st = (INR exn,st') ==>
    exn <> BreakException /\ exn <> ContinueException
Proof
  Cases >>
  rw[Once evaluate_def, bind_def, switch_BoolV_def, return_def, raise_def,
     AllCaseEqs(), no_control_exc_def] >>
  TRY (drule (cj 1 eval_expr_no_control) >>
       metis_tac[no_control_exc_no_loop_control]) >>
  TRY (rename1 `(if tv = Value (BoolV T) then _ else _) _ = _` >>
       Cases_on `tv = Value (BoolV T)` >>
       gvs[bind_def, return_def, raise_def, AllCaseEqs(), no_control_exc_def] >>
       Cases_on `tv = Value (BoolV F)` >>
       gvs[bind_def, return_def, raise_def, AllCaseEqs(), no_control_exc_def] >>
       TRY (imp_res_tac get_Value_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
       TRY (imp_res_tac lift_option_type_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
       TRY (drule (cj 1 eval_expr_no_control) >>
            metis_tac[no_control_exc_no_loop_control]) >>
       NO_TAC)
QED
Theorem eval_stmt_raise_no_loop_control[local]:
  !r cx st exn st'.
    eval_stmt cx (Raise r) st = (INR exn,st') ==>
    exn <> BreakException /\ exn <> ContinueException
Proof
  Cases >>
  rw[Once evaluate_def, bind_def, return_def, raise_def,
     AllCaseEqs(), no_control_exc_def] >>
  TRY (imp_res_tac get_Value_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac lift_option_type_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (drule (cj 1 eval_expr_no_control) >>
       metis_tac[no_control_exc_no_loop_control])
QED

Theorem eval_stmt_return_no_loop_control[local]:
  !opt_e cx st exn st'.
    eval_stmt cx (Return opt_e) st = (INR exn,st') ==>
    exn <> BreakException /\ exn <> ContinueException
Proof
  Cases >>
  rw[Once evaluate_def, bind_def, return_def, raise_def,
     AllCaseEqs(), no_control_exc_def] >>
  TRY (imp_res_tac materialise_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (drule (cj 1 eval_expr_no_control) >>
       metis_tac[no_control_exc_no_loop_control])
QED



Theorem stmt_no_control_escape_eval_no_loop_control:
  (!s cx st exn st'.
     stmt_no_control_escape s /\
     eval_stmt cx s st = (INR exn,st') ==>
     exn <> BreakException /\ exn <> ContinueException) /\
  (!ss cx st exn st'.
     stmts_no_control_escape ss /\
     eval_stmts cx ss st = (INR exn,st') ==>
     exn <> BreakException /\ exn <> ContinueException)
Proof
  ho_match_mp_tac stmt_induction >>
  rw[stmt_no_control_escape_def, evaluate_def, bind_def, ignore_bind_def,
     finally_def, try_def, switch_BoolV_def, return_def, raise_def,
     pairTheory.UNCURRY, AllCaseEqs()] >>
  TRY (imp_res_tac no_control_exc_no_loop_control >> NO_TAC) >>
  TRY (imp_res_tac check_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac type_check_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac lift_option_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac lift_option_type_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac lift_sum_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac push_scope_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac pop_scope_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac new_variable_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac get_Value_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac materialise_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac push_log_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac assign_target_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac eval_iterator_no_control >> gvs[no_control_exc_def] >> NO_TAC) >>
  TRY (imp_res_tac eval_for_no_loop_control >> NO_TAC) >>
  TRY (imp_res_tac eval_stmt_assert_no_loop_control >> NO_TAC) >>
  TRY (imp_res_tac eval_stmt_raise_no_loop_control >> NO_TAC) >>
  TRY (imp_res_tac eval_stmt_return_no_loop_control >> NO_TAC) >>
  TRY (drule (cj 1 eval_expr_no_control) >> simp[no_control_exc_no_loop_control] >> NO_TAC) >>
  TRY (drule (cj 2 eval_expr_no_control) >> simp[no_control_exc_no_loop_control] >> NO_TAC) >>
  TRY (drule (cj 1 eval_target_no_control) >> simp[no_control_exc_no_loop_control] >> NO_TAC) >>
  TRY (drule (cj 3 eval_target_no_control) >> simp[no_control_exc_no_loop_control] >> NO_TAC) >>
  TRY (first_x_assum drule_all >> simp[] >> NO_TAC) >>
  TRY (rename1 `if tv = Value (BoolV T) then _ else _` >>
       Cases_on `tv = Value (BoolV T)` >> gvs[raise_def, no_control_exc_def] >>
       Cases_on `tv = Value (BoolV F)` >> gvs[raise_def, no_control_exc_def] >>
       res_tac >> gvs[] >> NO_TAC) >>
  TRY (rename1 `eval_stmt cx (Assert e a) st = _` >>
       Cases_on `a` >>
       gvs[evaluate_def, bind_def, switch_BoolV_def, return_def, raise_def,
           AllCaseEqs(), no_control_exc_def] >>
       TRY (drule (cj 1 eval_expr_no_control) >> simp[no_control_exc_def] >> NO_TAC) >>
       TRY (rename1 `(if tv = Value (BoolV T) then _ else _) _ = _` >>
            Cases_on `tv = Value (BoolV T)` >> gvs[return_def, raise_def, no_control_exc_def] >>
            Cases_on `tv = Value (BoolV F)` >> gvs[return_def, raise_def, no_control_exc_def] >>
            NO_TAC) >>
       NO_TAC) >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  TRY (metis_tac[no_fallthrough_eval_no_success])
QED

Theorem stmts_no_control_escape_eval_stmts_no_loop_control:
  stmts_no_control_escape ss /\ eval_stmts cx ss st = (INR exn,st') ==>
  exn <> BreakException /\ exn <> ContinueException
Proof
  metis_tac[stmt_no_control_escape_eval_no_loop_control]
QED



Theorem intcall_pushed_body_preconditions[local]:
  !env_body pushed_cx dflt_st lock_st call_env.
    env_context_consistent env_body pushed_cx /\
    env_immutables_consistent env_body pushed_cx dflt_st /\
    env_scopes_consistent env_body pushed_cx (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    lock_st.scopes = dflt_st.scopes /\
    lock_st.immutables = dflt_st.immutables /\
    lock_st.accounts = dflt_st.accounts ==>
    env_consistent env_body pushed_cx (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rw[env_consistent_def, state_well_typed_def] >>
  gvs[env_scopes_consistent_def, env_immutables_consistent_def] >>
  metis_tac[]
QED

Theorem acquire_nonreentrant_lock_accounts[local]:
  !addr slot is_view st res st'.
    acquire_nonreentrant_lock addr slot is_view st = (res, st') ==>
    st'.accounts = st.accounts
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED
Theorem release_nonreentrant_lock_accounts[local]:
  !addr slot st res st'.
    release_nonreentrant_lock addr slot st = (res, st') ==>
    st'.accounts = st.accounts
Proof
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, LET_THM]
  \\ rpt (BasicProvers.TOP_CASE_TAC \\ gvs[]) \\ simp[]
QED

Theorem intcall_unlock_state_preserves_frame[local]:
  !cx nr is_view st res st'.
    (if nr /\ ~is_view then
       case cx.nonreentrant_slot of
       | NONE => return ()
       | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return ()) st = (res,st') ==>
    st'.scopes = st.scopes /\
    st'.immutables = st.immutables /\
    st'.accounts = st.accounts
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def] >>
  Cases_on `is_view` >> gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  imp_res_tac release_nonreentrant_lock_scopes >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  imp_res_tac release_nonreentrant_lock_accounts >>
  gvs[]
QED

Theorem intcall_cleanup_after_pop_preserves_frame[local]:
  !cx nr is_view prev st res st'.
    (do pop_function prev;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st = (res,st') ==>
    st'.scopes = prev /\
    st'.immutables = st.immutables /\
    st'.accounts = st.accounts
Proof
  rpt strip_tac >>
  gvs[pop_function_def, set_scopes_def, bind_def, ignore_bind_def,
      return_def] >>
  drule intcall_unlock_state_preserves_frame >>
  simp[]
QED

Theorem intcall_lock_state_preserves_frame[local]:
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
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac acquire_nonreentrant_lock_accounts >>
  gvs[]
QED

Theorem intcall_pushed_body_preconditions_from_lock[local]:
  !env_body cx pushed_cx dflt_st lock_st call_env nr is_view.
    env_context_consistent env_body pushed_cx /\
    env_immutables_consistent env_body pushed_cx dflt_st /\
    env_scopes_consistent env_body pushed_cx (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body pushed_cx (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rpt strip_tac >>
  qspecl_then [`cx`, `nr`, `is_view`, `dflt_st`, `lock_st`] mp_tac
    intcall_lock_state_preserves_frame >>
  simp[] >> strip_tac >>
  qspecl_then [`env_body`, `pushed_cx`, `dflt_st`, `lock_st`, `call_env`] mp_tac
    intcall_pushed_body_preconditions >>
  (impl_tac >- simp[]) >>
  simp[]
QED
Theorem intcall_pushed_body_preconditions_for_defaults_from_lock[local]:
  !env_body cx dflt_st lock_st call_env src_id_opt fn nr is_view.
    env_context_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn)) /\
    env_immutables_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn))
      (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rpt strip_tac >>
  qspecl_then [`env_body`, `cx`, `cx with stk updated_by CONS (src_id_opt,fn)`,
               `dflt_st`, `lock_st`, `call_env`, `nr`, `is_view`] mp_tac
    intcall_pushed_body_preconditions_from_lock >>
  (impl_tac >- simp[]) >>
  simp[]
QED

Theorem intcall_pushed_body_preconditions_live_from_defaults[local]:
  !env env_body cx args_st dflt_st lock_st call_env src_id_opt fn nr is_view.
    env_consistent env cx args_st /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn))
      (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body (cx with stk updated_by CONS (src_id_opt,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rpt strip_tac >>
  qspecl_then [`env`, `env_body`, `cx`, `args_st`, `src_id_opt`, `fn`] mp_tac
    intcall_env_body_consistency_for_defaults >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  qspecl_then [`env_body`, `cx`, `dflt_st`, `lock_st`, `call_env`,
               `src_id_opt`, `fn`, `nr`, `is_view`] mp_tac
    intcall_pushed_body_preconditions_for_defaults_from_lock >>
  (impl_tac >- simp[]) >>
  simp[]
QED

Theorem intcall_live_pushed_body_preconditions:
  !env env_body cx args_st dflt_st lock_st call_env fn nr is_view.
    env_consistent env cx args_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    scope_well_typed call_env /\
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (INL (),lock_st) ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts
Proof
  rpt strip_tac >>
  qspecl_then
    [`env`, `env_body`, `cx`, `args_st`, `dflt_st`, `lock_st`, `call_env`,
     `env_body.current_src`, `fn`, `nr`, `is_view`]
    mp_tac intcall_pushed_body_preconditions_live_from_defaults >>
  (impl_tac >- simp[]) >>
  simp[]
QED

Theorem location_runtime_typed_rebuild[local]:
  !env cx st loc vt st'.
    location_runtime_typed env cx st loc vt /\
    runtime_consistent env cx st' ==>
    location_runtime_typed env cx st' loc vt
Proof
  rw[] >> Cases_on `loc` >> gvs[location_runtime_typed_def, runtime_consistent_def,
                                     env_consistent_def, env_scopes_consistent_def,
                                     env_immutables_consistent_def]
  >- (
    rename1 `FLOOKUP env.var_types (string_to_num s) = SOME var_ty` >>
    `?entry'. lookup_scopes (string_to_num s) st'.scopes = SOME entry'` by metis_tac[IS_SOME_EXISTS] >>
    `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
    `evaluate_type (get_tenv cx) var_ty = SOME entry'.type` by metis_tac[] >>
    `entry'.type = entry.type` by gvs[] >>
    qexists_tac `entry'` >> simp[]) >>
  rename1 `FLOOKUP env.bare_globals (src_id_opt,string_to_num s) = SOME imm_ty` >>
  `?pair. FLOOKUP (get_source_immutables src_id_opt
      (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME m => m))
      (string_to_num s) = SOME pair` by metis_tac[IS_SOME_EXISTS] >>
  PairCases_on `pair` >>
  `env.type_defs = get_tenv cx` by fs[env_context_consistent_def] >>
  `evaluate_type (get_tenv cx) imm_ty = SOME pair0` by metis_tac[] >>
  qexists_tac `get_source_immutables src_id_opt
      (case ALOOKUP st'.immutables cx.txn.target of NONE => [] | SOME m => m)` >>
  qexists_tac `pair1` >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >>
  Cases_on `ALOOKUP x src_id_opt` >>
  gvs[get_immutables_def, get_address_immutables_def, bind_def, return_def,
      lift_option_type_def, lift_option_def, get_source_immutables_def,
      AllCaseEqs()]
QED

Theorem subscript_vtype_index_get_Value_no_type_error[local]:
  !base_vt idx_ty result_vt env e tv st res st'.
    subscript_vtype base_vt idx_ty = SOME result_vt /\
    expr_result_typed env e tv /\ expr_type e = idx_ty /\
    get_Value tv st = (res, st') ==>
    no_type_error_result res
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def] >>
  irule get_Value_no_type_error >>
  qexistsl_tac [`st`, `st'`, `tv`, `tv'`] >> simp[] >>
  Cases_on `base_vt` >> gvs[subscript_vtype_def]
  >- (Cases_on `t` >> gvs[subscript_vtype_def] >>
      Cases_on `expr_type e` >> gvs[is_int_type_def, evaluate_type_def, AllCaseEqs()]) >>
  Cases_on `expr_type e` >> gvs[hashmap_key_type_def, evaluate_type_def, AllCaseEqs(), LET_THM]
QED
Theorem get_Value_INR_no_type_error[local]:
  !tv tyv st y st'.
    toplevel_value_typed tv tyv /\ tyv <> NoneTV /\
    (!t b. tyv <> ArrayTV t b) /\
    get_Value tv st = (INR y, st') ==>
    !msg. y <> Error (TypeError msg)
Proof
  rw[] >>
  drule_all get_Value_no_type_error >>
  gvs[no_type_error_result_def]
QED

Theorem subscript_vtype_value_step_type[local]:
  !base_vt idx_ty result_vt env e tv st st' v loc_vt sbs.
    subscript_vtype base_vt idx_ty = SOME result_vt /\
    expr_result_typed env e tv /\ expr_type e = idx_ty /\
    get_Value tv st = (INL v, st') /\
    target_path_type env loc_vt sbs base_vt ==>
    target_path_type env loc_vt (ValueSubscript v::sbs) result_vt
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def] >>
  irule target_path_type_subscript_cons >>
  qexistsl_tac [`expr_type e`, `base_vt`] >> simp[] >>
  Cases_on `base_vt` >> gvs[subscript_vtype_def]
  >- (Cases_on `t` >> gvs[subscript_vtype_def] >>
      Cases_on `expr_type e` >> gvs[is_int_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `tv` >> gvs[get_Value_def, return_def, toplevel_value_typed_def] >>
      Cases_on `v` >> gvs[value_has_type_def]) >>
  Cases_on `expr_type e` >> gvs[hashmap_key_type_def, evaluate_type_def, AllCaseEqs(), LET_THM] >>
  Cases_on `tv` >> gvs[get_Value_def, return_def, toplevel_value_typed_def] >>
  Cases_on `v` >> gvs[value_has_type_def]
QED

(* ===== C5.2 Bridge lemmas: derive shape and assignable context for statement
   assignment branches from evaluation/target-typing/runtime-consistency facts
   actually available at the call site. ===== *)

Theorem env_extends_return_exception_typed:
  env_extends env env' /\ return_exception_typed env' ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  Cases_on `exn` >> gvs[return_exception_typed_def] >>
  metis_tac[value_runtime_typed_env_static, env_extends_def]
QED

(* Generic scope-pop env-consistency facts moved to vyperTypeScopePop. *)

Theorem extend_local_F_env_extends:
  env_maps_wf env /\
  id NOTIN FDOM env.var_types ==>
  env_extends env (extend_local env id ty F)
Proof
  rw[env_extends_def, extend_local_def, FLOOKUP_UPDATE] >>
  Cases_on `id = id'` >> gvs[TO_FLOOKUP] >>
  fs[env_maps_wf_def] >>
  first_x_assum (qspec_then `id` mp_tac) >> simp[]
QED

Theorem return_exception_typed_extend_local_env_extends:
  env_extends (extend_local env id ty assignable) env_exn /\
  return_exception_typed env_exn ret_ty exn ==>
  return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> simp[return_exception_typed_def] >>
  strip_tac >>
  irule value_runtime_typed_env_static >>
  qexists_tac `env_exn` >>
  gvs[env_extends_def, extend_local_def]
QED

Theorem for_cons_ordinary_exception_conclusion:
  state_well_typed stpopped ==>
  accounts_well_typed stpopped.accounts ==>
  env_consistent env cx stpopped ==>
  no_type_error_result (INR exn) ==>
  (env_extends (extend_local env id ty F) env_exn /\
   return_exception_typed env_exn ret_ty exn) ==>
  state_well_typed stpopped /\
  accounts_well_typed stpopped.accounts /\
  env_consistent env cx stpopped /\
  no_type_error_result (INR exn) /\
  return_exception_typed env ret_ty exn
Proof
  rpt gen_tac >>
  strip_tac >> strip_tac >> strip_tac >> strip_tac >> strip_tac >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- asm_rewrite_tac[] >>
  conj_tac >- fs[no_type_error_result_def] >>
  irule return_exception_typed_extend_local_env_extends >>
  qexists_tac `F` >>
  qexists_tac `env_exn` >>
  qexists_tac `id` >>
  qexists_tac `ty` >>
  fs[]
QED

Theorem for_cons_non_loop_exception_suffix_projected_explicit:
  !env cx id ty ret_ty st_body exn env_exn.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    env_extends (extend_local env id ty F) env_exn /\
    env_consistent env_exn cx st_body /\
    return_exception_typed env_exn ret_ty exn ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  metis_tac[for_cons_ordinary_exception_conclusion, sum_case_def]
QED

Theorem for_cons_non_loop_exception_suffix_projected:
  !env env_after cx id ty ret_ty st_body exn.
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL u => env_consistent env_after cx st_body
     | INR exn0 =>
         ?env_exn.
           env_extends (extend_local env id ty F) env_exn /\
           env_consistent env_exn cx st_body /\
           return_exception_typed env_exn ret_ty exn0) ==>
    state_well_typed (st_body with scopes := TL st_body.scopes) /\
    accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts /\
    env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
    no_type_error_result (INR exn) /\
    (case (INR exn : unit + vyperState$exception) of
     | INL _ => T
     | INR exn0 => return_exception_typed env ret_ty exn0)
Proof
  rpt strip_tac >>
  gvs[sum_case_def] >>
  qspecl_then [`env`,`cx`,`id`,`ty`,`ret_ty`,`st_body`,`exn`,`env_exn`] mp_tac
    for_cons_non_loop_exception_suffix_projected_explicit >>
  simp[]
QED

Theorem for_body_env_extends_consistent_after_pop:
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  env_extends (extend_local env id ty F) env_body /\
  env_consistent env_body cx st_body /\
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (res, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  strip_tac >>
  Cases_on `st_body.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[] >>
      fs[env_consistent_def, env_scopes_consistent_def]) >>
  rename1 `st_body.scopes = h::tl` >>
  irule env_extends_env_consistent_after_pop >> simp[] >>
  conj_tac >- (
    drule eval_stmts_preserves_scopes_len >> simp[] >> strip_tac >>
    fs[env_consistent_def, env_scopes_consistent_def] >>
    Cases_on `st.scopes` >> gvs[] >>
    Cases_on `tl` >> gvs[]) >>
  conj_tac >- (
    conj_tac >> rpt strip_tac
    >- (irule scope_bracket_var_type_head_none >>
        qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `res` >>
        qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
        qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >>
        qexists_tac `tl` >> qexists_tac `ty'` >>
        simp[FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
    `IS_SOME (FLOOKUP env.var_types id')` by fs[env_maps_wf_def] >>
    Cases_on `FLOOKUP env.var_types id'` >> gvs[] >>
    irule scope_bracket_var_type_head_none >>
    qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `res` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
    qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >>
    qexists_tac `tl` >> qexists_tac `x` >>
    simp[FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
  conj_tac >- (
    qexists_tac `env_body` >> simp[] >>
    conj_tac >- (
      rpt strip_tac >>
      irule scope_bracket_new_var_tail_none >>
      qexists_tac `cx` >> qexists_tac `env` >> qexists_tac `h` >>
      qexists_tac `res` >>
      qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
      qexists_tac `body_stmts` >> qexists_tac `st` >> qexists_tac `st_body` >> simp[]) >>
    irule env_extends_trans >>
    qexists_tac `extend_local env id ty F` >> simp[] >>
    irule extend_local_F_env_extends >> simp[]) >>
  qexists_tac `st` >> simp[] >>
  `st_body with scopes := tl =
   st_body with scopes := TL st_body.scopes` by simp[] >>
  pop_assum SUBST1_TAC >>
  irule eval_stmts_scope_bracket_gen_preserves_tv >> simp[] >>
  qexists_tac `res` >>
  qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
  qexists_tac `body_stmts` >> simp[] >>
  irule (cj 2 eval_preserves_tv) >>
  qexists_tac `res` >> qexists_tac `body_stmts` >> simp[]
QED


Theorem for_cons_popped_env_consistent_from_stmt_case:
  (case (INR exn : unit + vyperState$exception) of
   | INL u => inl_post u
   | INR exn0 =>
       ?env_exn.
         env_extends (extend_local env id ty F) env_exn /\
         env_consistent env_exn cx st_body /\
         return_exception_typed env_exn ret_ty exn0) ==>
  env_consistent env cx st ==>
  id NOTIN FDOM env.var_types ==>
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (INR exn, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  simp[] >> rpt strip_tac >>
  irule for_body_env_extends_consistent_after_pop >> simp[] >>
  conj_tac >- metis_tac[env_consistent_env_maps_wf] >>
  qexists_tac `body_stmts` >> qexists_tac `env_exn` >>
  qexists_tac `id` >> qexists_tac `INR exn` >> qexists_tac `st` >>
  qexists_tac `ty` >> qexists_tac `tyv` >> qexists_tac `v` >> simp[]
QED
Theorem for_body_env_consistent_after_pop:
  env_maps_wf env /\
  env_consistent env cx st /\
  id NOTIN FDOM env.var_types /\
  type_stmts (extend_local env id ty F) ret_ty body_stmts = SOME env_after /\
  env_consistent env_after cx st_body /\
  eval_stmts cx body_stmts
    (st with scopes updated_by CONS
       (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>))) =
    (res, st_body) ==>
  env_consistent env cx (st_body with scopes := TL st_body.scopes)
Proof
  strip_tac >>
  irule for_body_env_extends_consistent_after_pop >> simp[] >>
  qexists_tac `body_stmts` >> qexists_tac `env_after` >>
  qexists_tac `id` >> qexists_tac `res` >> qexists_tac `st` >>
  qexists_tac `ty` >> qexists_tac `tyv` >> qexists_tac `v` >> simp[] >>
  irule type_stmts_env_extends >> simp[] >>
  conj_tac >- (irule extend_local_env_maps_wf >> simp[]) >>
  qexists_tac `ret_ty` >> qexists_tac `body_stmts` >> simp[]
QED

(* ===== Mutual theorem skeleton and statement/target cases ===== *)

(* TOP-LEVEL WORKHORSE: mutual type-soundness proof for statements, statement
 * lists, iterators, targets, and expressions.  The main theorem uses
 * suspend/Resume extensively; keep the theorem, all Resume blocks, and the
 * Finalise in this theory unless deliberately redesigning the proof. *)

(* ===== Scope-bracket helpers for block statements ===== *)

Theorem scope_bracket_decompose:
  (!q st_body. body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==> st_body.scopes <> []) /\
  (do push_scope; finally body_fun pop_scope od) st = (res, st') ==>
  ?q st_body.
    body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
    st' = st_body with scopes := TL st_body.scopes /\
    (((?x. q = INL x) ==> ?u. res = INL u) /\
     (!e. q = INR e ==> res = INR e))
Proof
  rpt strip_tac >>
  gvs[push_scope_def, finally_def, pop_scope_def,
      return_def, raise_def, bind_def, ignore_bind_def,
      AllCaseEqs()] >>
  Cases_on `body_fun (st with scopes updated_by CONS FEMPTY)` >>
  Cases_on `q` >>
  gvs[AllCaseEqs(), pop_scope_def, return_def, raise_def] >>
  imp_res_tac eval_stmts_preserves_scopes_len >>
  Cases_on `r.scopes` >> gvs[return_def, raise_def,
    evaluation_state_component_equality]
QED

Theorem scope_bracket_preserves:
  env_maps_wf env /\
  env_consistent env cx st /\
  type_stmts env ret_ty ss = SOME env_after /\
  eval_stmts cx ss (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
  state_well_typed st_body /\
  env_consistent env_after cx st_body /\
  accounts_well_typed st_body.accounts ==>
  state_well_typed (st_body with scopes := TL st_body.scopes) /\
  env_consistent env cx (st_body with scopes := TL st_body.scopes) /\
  accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts
Proof
  strip_tac
  >> conj_tac >- (drule scope_bracket_preserves_swt >> simp[])
  >> conj_tac >- (irule scope_bracket_preserves_ec >>
      conj_tac >- rw[] >>
      goal_assum(drule_at(Pat`type_stmts`)) >>
      goal_assum(drule_at(Pat`eval_stmts`)) >>
      simp[])
  >> simp[evaluation_state_component_equality]
QED

Theorem for_body_decompose_any[local]:
  !cx body_stmts stp res st'.
    stp.scopes <> [] /\
    finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
      pop_scope stp = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body_stmts stp = (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `finally _ _ _ = _` mp_tac >>
  simp_tac (srw_ss()) [finally_def, bind_apply, ignore_bind_apply,
    try_def, return_def, pop_scope_def, raise_def,
    handle_loop_exception_def] >>
  Cases_on `eval_stmts cx body_stmts stp` >>
  `?hd tl. r.scopes = hd :: tl` by (
    imp_res_tac eval_stmts_preserves_scopes_len >>
    Cases_on `r.scopes` >> gvs[]) >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y = ContinueException` >> gvs[return_def] >>
  Cases_on `y = BreakException` >> gvs[return_def, raise_def] >>
  strip_tac >> gvs[]
QED
Theorem for_body_decompose_for_cons_pushed[local]:
  !cx body_stmts st id tyv v res st' stp.
    stp =
      st with scopes updated_by
        CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)) /\
    finally (try do eval_stmts cx body_stmts; return F od handle_loop_exception)
      pop_scope stp = (res, st') ==>
    ?res_body st_body.
      eval_stmts cx body_stmts stp = (res_body, st_body) /\
      st' = st_body with scopes := TL st_body.scopes /\
      ((?x. res_body = INL x) ==> res = INL F) /\
      (res_body = INR ContinueException ==> res = INL F) /\
      (res_body = INR BreakException ==> res = INL T) /\
      (!e. res_body = INR e /\
           e <> ContinueException /\ e <> BreakException ==>
           res = INR e) /\
      (!e. res = INR e ==> res_body = INR e)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `body_stmts`, `stp`, `res`, `st'`]
    mp_tac for_body_decompose_any >>
  impl_tac >- (
    conj_tac >- gvs[] >>
    qpat_assum `finally _ _ _ = _` ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED
Theorem is_int_type_evaluate_type_not_None_Array[local]:
  !tdefs ty tv.
    is_int_type ty /\ evaluate_type tdefs ty = SOME tv ==>
    tv <> NoneTV /\ (!t bd. tv <> ArrayTV t bd)
Proof
  rw[] >>
  Cases_on `ty` >> gvs[is_int_type_def, evaluate_type_def, AllCaseEqs()] >>
  Cases_on `b` >> gvs[is_int_type_def, evaluate_type_def]
QED


Theorem for_cons_pushed_state_well_typed[local]:
  state_well_typed st /\ value_has_type tyv v /\ well_formed_type_value tyv ==>
  state_well_typed
    (st with scopes updated_by
       CONS (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)))
Proof
  rw[state_well_typed_def, scope_well_typed_def, FLOOKUP_UPDATE]
QED

Theorem scope_bracket_post:
  env_maps_wf env /\
  env_consistent env cx st /\
  (!q st_body. body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==> st_body.scopes <> []) /\
  (do push_scope; finally body_fun pop_scope od) st = (res, st_final) /\
  (!q st_body.
     body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) ==>
     state_well_typed st_body /\ accounts_well_typed st_body.accounts /\
     no_type_error_result q /\
     case q of
     | INL _ => env_consistent env cx (st_body with scopes := TL st_body.scopes)
     | INR exn => env_consistent env cx (st_body with scopes := TL st_body.scopes) /\ return_exception_typed env ret_ty exn) ==>
  state_well_typed st_final /\ accounts_well_typed st_final.accounts /\ no_type_error_result res /\
  case res of
  | INL _ => env_consistent env cx st_final
  | INR exn => env_consistent env cx st_final /\ return_exception_typed env ret_ty exn
Proof
  strip_tac >>
  qpat_x_assum `do push_scope; finally body_fun pop_scope od st = (res,st_final)` mp_tac >>
  qpat_x_assum `!q st_body. body_fun _ = _ ==> st_body.scopes <> []` mp_tac >>
  strip_tac >> strip_tac >>
  `?q st_body.
     body_fun (st with scopes updated_by CONS FEMPTY) = (q, st_body) /\
     st_final = st_body with scopes := TL st_body.scopes /\
     (((?x. q = INL x) ==> ?u. res = INL u) /\
      (!e. q = INR e ==> res = INR e))` by
    (irule scope_bracket_decompose >> simp[]) >>
  gvs[] >>
  qmatch_assum_rename_tac`no_type_error_result r1` >>
  Cases_on `st_body.scopes` >> gvs[] >>
  `state_well_typed (st_body with scopes := t)` by (
    drule pop_scope_preserves_state_well_typed >>
    simp[pop_scope_def, return_def, raise_def]) >>
  Cases_on`r1` >> gvs[no_type_error_result_def]
QED
Theorem target_runtime_typed_imp_shape[local]:
  !env cx st tgt ty gv.
    target_runtime_typed env cx st tgt ty gv ==>
    target_value_shape env tgt gv
Proof
  Cases_on `tgt` >> Cases_on `gv` >>
  rw[target_runtime_typed_def, target_value_shape_def]
QED

Theorem target_values_runtime_typed_imp_shape[local]:
  !env cx st tgts tys gvs.
    target_values_runtime_typed env cx st tgts tys gvs ==>
    target_values_shape env tgts gvs
Proof
  Induct_on `tgts` >> Cases_on `tys` >> Cases_on `gvs` >>
  simp[target_runtime_typed_def, target_value_shape_def] >>
  metis_tac[target_runtime_typed_imp_shape]
QED

Theorem extract_elements_well_typed[local]:
  !arr_tv av elem_tv bd vs.
    value_has_type (ArrayTV elem_tv bd) (ArrayV av) /\
    well_formed_type_value (ArrayTV elem_tv bd) /\
    extract_elements (ArrayTV elem_tv bd) (ArrayV av) = SOME vs ==>
    EVERY (value_has_type elem_tv) vs
Proof
  rpt gen_tac >>
  simp[extract_elements_def] >>
  Cases_on `av` >> simp[value_has_type_inv]
  >- (rpt strip_tac >> gvs[array_elements_def, all_have_type_EVERY])
  >- (rpt strip_tac >> gvs[] >>
      fs[array_elements_def, LET_THM, EVERY_GENLIST] >>
      rpt strip_tac >>
      Cases_on `ALOOKUP l i` >> simp[]
      >- (match_mp_tac default_value_well_typed >> fs[well_formed_type_value_def]) >>
      metis_tac[ALOOKUP_sparse_has_type])
QED

Theorem Num_pos_le[local]:
  !x (m:num). 0 <= x ==> (Num x <= m <=> x <= &m)
Proof
  rpt strip_tac >>
  `&(Num x) = x` by metis_tac[integerTheory.INT_OF_NUM] >>
  pop_assum (fn th => REWRITE_TAC[GSYM integerTheory.INT_LE, th])
QED

Theorem within_int_bound_convex[local]:
  !b n1 n2 k.
    within_int_bound b n1 /\ within_int_bound b n2 /\
    n1 <= n2 /\ &k < n2 - n1 ==>
    within_int_bound b (n1 + &k)
Proof
  Cases_on `b` >> simp[within_int_bound_def] >> rpt strip_tac
  >- (
    Cases_on `n = 0` >- gvs[] >>
    gvs[] >>
    Cases_on `n1 + &k < 0` >> simp[]
    >- (
      `n1 < 0` by intLib.ARITH_TAC >> fs[] >>
      `0 <= -(n1 + &k)` by intLib.ARITH_TAC >>
      `0 <= -n1` by intLib.ARITH_TAC >>
      `-(n1 + &k) <= -n1` by intLib.ARITH_TAC >>
      fs[Num_pos_le] >> intLib.ARITH_TAC) >>
    Cases_on `n2 < 0`
    >- (`n1 + &k < n2` by intLib.ARITH_TAC >> intLib.ARITH_TAC) >>
    fs[] >>
    `0 <= n1 + &k` by intLib.ARITH_TAC >>
    `0 <= n2` by intLib.ARITH_TAC >>
    `n1 + &k < n2` by intLib.ARITH_TAC >>
    `Num (n1 + &k) < Num n2` by simp[integerTheory.NUM_LT] >>
    simp[]) >>
  `0 <= n1 + &k` by intLib.ARITH_TAC >>
  `0 <= n2` by intLib.ARITH_TAC >>
  `n1 + &k < n2` by intLib.ARITH_TAC >>
  `Num (n1 + &k) < Num n2` by simp[integerTheory.NUM_LT] >>
  simp[]
QED

Theorem range_values_well_typed[local]:
  !n1 n2 count tyv.
    value_has_type tyv (IntV n1) /\
    value_has_type tyv (IntV n2) /\
    get_range_limits (IntV n1) (IntV n2) = INL (n1, count) ==>
    EVERY (value_has_type tyv) (GENLIST (\n. IntV (n1 + &n)) count)
Proof
  rpt gen_tac >> strip_tac >>
  gvs[get_range_limits_def] >>
  simp[EVERY_GENLIST] >> rpt strip_tac >>
  `0 <= n2 - n1` by intLib.ARITH_TAC >>
  `&n < n2 - n1` by (
    `&(Num (n2 - n1)) = n2 - n1` by metis_tac[integerTheory.INT_OF_NUM] >>
    intLib.ARITH_TAC) >>
  Cases_on `tyv` >> gvs[value_has_type_def] >>
  Cases_on `b` >> gvs[value_has_type_def]
  >- (
    `0 <= n1 + &n` by intLib.ARITH_TAC >>
    `0 <= n2` by intLib.ARITH_TAC >>
    `n1 + &n < n2` by intLib.ARITH_TAC >>
    `Num (n1 + &n) < Num n2` by simp[integerTheory.NUM_LT] >>
    simp[]) >>
  metis_tac[within_int_bound_convex]
QED

Theorem iterator_range_tail_sound[local]:
  !tv i1 i2 rl st.
    value_has_type tv (IntV i1) /\
    value_has_type tv (IntV i2) /\
    lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (INL rl,st) ==>
    no_type_error_result (INL (GENLIST (\n. IntV (FST rl + &n)) (SND rl))) /\
    EVERY (value_has_type tv) (GENLIST (\n. IntV (FST rl + &n)) (SND rl))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `lift_sum _ _ = _` mp_tac >>
  simp[lift_sum_def, get_range_limits_def] >>
  COND_CASES_TAC >> simp[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  conj_tac >- simp[no_type_error_result_def] >>
  irule range_values_well_typed >>
  conj_tac >- simp[] >>
  qexists_tac `i2` >> simp[get_range_limits_def]
QED
Theorem iterator_range_tail_eval_sound[local]:
  !type_defs expr_ty tyv i1 i2 range_res st st_tail res st_final.
    evaluate_type type_defs expr_ty = SOME tyv /\
    value_has_type tyv (IntV i1) /\
    value_has_type tyv (IntV i2) /\
    lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (range_res, st_tail) /\
    (case range_res of
     | INL rl => return (GENLIST (\n. IntV (FST rl + &n)) (SND rl)) st_tail
     | INR err => raise err st_tail) = (res, st_final) ==>
    st_final = st /\
    no_type_error_result res /\
    (case res of
     | INL vs => ?tyv'. evaluate_type type_defs expr_ty = SOME tyv' /\ EVERY (value_has_type tyv') vs
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  drule lift_sum_state >> strip_tac >> gvs[] >>
  Cases_on `range_res` >> gvs[return_def, raise_def]
  >- (
    rename1 `lift_sum (get_range_limits (IntV i1) (IntV i2)) st = (INL rl,st)` >>
    qspecl_then [`tyv`, `i1`, `i2`, `rl`, `st`] mp_tac iterator_range_tail_sound >>
    simp[]) >>
  qpat_x_assum `lift_sum _ _ = _` mp_tac >>
  simp[lift_sum_def, get_range_limits_def, return_def, raise_def] >>
  Cases_on `i1 <= i2` >> gvs[return_def, raise_def, no_type_error_result_def]
QED


Theorem iterator_range_first_get_value_error_eq[local]:
  !cx e' tv1 st1 y res st'.
    get_Value tv1 st1 = (INR y, st1) /\
    (case (INL tv1,st1) of
       (INL tv1,s'') =>
         (case get_Value tv1 s'' of
            (INL v1,s'') =>
              (case eval_expr cx e' s'' of
                 (INL tv2,s'') =>
                   (case get_Value tv2 s'' of
                      (INL v2,s'') =>
                        (case lift_sum (get_range_limits v1 v2) s'' of
                           (INL rl,s'') =>
                             (let n1 = FST rl; n2 = SND rl in
                                return (GENLIST (\n. IntV (n1 + &n)) n2)) s''
                         | (INR err,s'') => (INR err,s''))
                    | (INR err,s'') => (INR err,s''))
               | (INR err,s'') => (INR err,s''))
          | (INR err,s'') => (INR err,s''))
     | (INR err,s'') => (INR err,s'')) = (res,st') ==>
    res = INR y /\ st' = st1
Proof
  rpt strip_tac >>
  qpat_x_assum `(case (INL tv1,st1) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[]
QED

Theorem iterator_range_expr_error_eq[local]:
  !cx e' y st1 res st'.
    (case (INR y,st1) of
       (INL tv1,s'') =>
         (case get_Value tv1 s'' of
            (INL v1,s'') =>
              (case eval_expr cx e' s'' of
                 (INL tv2,s'') =>
                   (case get_Value tv2 s'' of
                      (INL v2,s'') =>
                        (case lift_sum (get_range_limits v1 v2) s'' of
                           (INL rl,s'') =>
                             (let n1 = FST rl; n2 = SND rl in
                                return (GENLIST (\n. IntV (n1 + &n)) n2)) s''
                         | (INR err,s'') => (INR err,s''))
                    | (INR err,s'') => (INR err,s''))
               | (INR err,s'') => (INR err,s''))
          | (INR err,s'') => (INR err,s''))
     | (INR err,s'') => (INR err,s'')) = (res,st') ==>
    res = INR y /\ st' = st1
Proof
  rpt strip_tac >>
  qpat_x_assum `(case (INR y,st1) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[]
QED

Theorem int_expr_get_Value_INR_no_type_error[local]:
  !env e tv ty st y st'.
    expr_result_typed env e tv /\ expr_type e = ty /\ is_int_type ty /\
    get_Value tv st = (INR y, st') ==>
    no_type_error_result (INR y)
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def, no_type_error_result_def] >>
  irule get_Value_INR_no_type_error >>
  qexistsl_tac [`st`, `st'`, `tv`, `tv'`] >> simp[] >>
  drule_all is_int_type_evaluate_type_not_None_Array >> simp[]
QED


Theorem eval_all_type_sound_mutual:
  (!cx s. !env ret_ty env' st res st'.
    type_stmt env ret_ty s = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmt s) /\
    eval_stmt cx s st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => env_consistent env cx st' /\ return_exception_typed env ret_ty exn) /\
  (!cx ss. !env ret_ty env' st res st'.
    type_stmts env ret_ty ss = SOME env' /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts ss) /\
    eval_stmts cx ss st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL _ => env_consistent env' cx st'
    | INR exn => ?env_exn. env_extends env env_exn /\ env_consistent env_exn cx st' /\
                           return_exception_typed env_exn ret_ty exn) /\
  (!cx it. !env ty st res st'.
    well_typed_iterator env ty it /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_iterator it) /\
    eval_iterator cx it st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => ?tyv. evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs
    | INR _ => T) /\
  (!cx tgt. !env ty st res st'.
    well_typed_atarget env tgt ty /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atarget tgt) /\
    eval_target cx tgt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL gv => target_runtime_typed env cx st' tgt ty gv
    | INR _ => T) /\
  (!cx tgts. !env tys st res st'.
    LIST_REL (\t ty. well_typed_atarget env t ty) tgts tys /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_atargets tgts) /\
    eval_targets cx tgts st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL gvs => LIST_REL3 (\t ty gv. target_runtime_typed env cx st' t ty gv) tgts tys gvs
    | INR _ => T) /\
  (!cx bt. !env vt st res st'.
    type_place_target env bt = SOME vt /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_target bt) /\
    eval_base_target cx bt st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL (loc,sbs) =>
        base_target_value_shape env bt loc sbs /\
        ?loc_vt. location_runtime_typed env cx st' loc loc_vt /\
          target_path_type env loc_vt sbs vt
    | INR _ => T) /\
  (!cx tyv id body vs. !env ret_ty ty env_after st res st'.
    evaluate_type env.type_defs ty = SOME tyv /\ EVERY (value_has_type tyv) vs /\
    id NOTIN FDOM env.var_types /\
    type_stmts (extend_local env id ty F) ret_ty body = SOME env_after /\
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_stmts body) /\
    eval_for cx tyv id body vs st = (res, st') ==>
    state_well_typed st' /\ accounts_well_typed st'.accounts /\ env_consistent env cx st' /\
    no_type_error_result res /\
    case res of
    | INR exn => return_exception_typed env ret_ty exn
    | INL _ => T) /\
  (!cx e. !env st res st'.
    env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    eval_expr cx e st = (res, st') ==>
    ((well_typed_expr env e ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of
      | INL tv => expr_result_typed env e tv
      | INR _ => T) /\
     (!vt. type_place_expr env e = SOME vt ==>
      state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
      no_type_error_result res /\
      case res of
      | INL tv => place_expr_result_typed env tv vt
      | INR _ => T))) /\
  (!cx es. !env st res st'.
    well_typed_exprs env es /\ env_consistent env cx st /\ state_well_typed st /\
    context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_exprs es) /\
    eval_exprs cx es st = (res, st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\ accounts_well_typed st'.accounts /\
    no_type_error_result res /\
    case res of
    | INL vs => exprs_runtime_typed env es vs
    | INR _ => T)
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
  TRY(rename1 `ExtCall` >> (
    rpt gen_tac >> strip_tac >>
    reverse conj_tac >- (
      rpt gen_tac >> strip_tac >>
      qpat_x_assum `type_place_expr _ (Call _ (ExtCall _ _) _ _) = SOME _` mp_tac >>
      simp[type_place_expr_Call_ExtCall_NONE]) >>
    suspend "Expr_Call_ExtCall_result")) >>
  TRY(rename1 `Send` >> suspend "Expr_Call_Send") >>
  TRY(rename1 `RawCallTarget` >> suspend "Expr_Call_RawCallTarget") >>
  TRY(rename1 `RawLog` >> suspend "Expr_Call_RawLog") >>
  TRY(rename1 `RawRevert` >> suspend "Expr_Call_RawRevert") >>
  TRY(rename1 `SelfDestructTarget` >> suspend "Expr_Call_SelfDestructTarget") >>
  TRY(rename1 `CreateTarget` >> suspend "Expr_Call_CreateTarget") >>
  TRY(rename1 `eval_exprs _ []` >> suspend "Exprs_nil") >>
  TRY(rename1 `eval_exprs _ (_::_)` >> suspend "Exprs_cons")
QED

Resume eval_all_type_sound_mutual[Pass]:
  gvs[evaluate_def, return_def, no_type_error_result_def, type_stmt_def]
QED

Resume eval_all_type_sound_mutual[Continue]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[Break]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[Return_NONE]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def, value_runtime_typed_def, value_has_type_def,
      evaluate_type_def]
QED

Resume eval_all_type_sound_mutual[Return_SOME]:
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
  Cases_on `er` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tv,s1)` >>
    Cases_on `materialise cx tv s1` >>
    rename1 `materialise cx tv s1 = (mr,s2)` >>
    Cases_on `mr` >> gvs[raise_def, no_type_error_result_def]
    >- (
      drule materialise_state >> strip_tac >> gvs[] >>
      strip_tac >> gvs[] >>
      gvs[expr_result_typed_def, expr_runtime_typed_def, return_exception_typed_def,
          value_runtime_typed_def] >>
      irule materialise_preserves_value_type >>
      simp[] >>
      metis_tac[evaluate_type_well_formed_type_value]) >>
    drule materialise_state >> strip_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    conj_tac >- (
      gvs[expr_result_typed_def, expr_runtime_typed_def] >>
      drule_all evaluate_type_not_NoneT_imp_not_NoneTV >> strip_tac >>
      drule_all materialise_typed_non_none_no_type_error >> simp[]) >>
    drule materialise_no_control >> strip_tac >>
    Cases_on `y` >> gvs[no_control_exc_def, return_exception_typed_def]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[RaiseBare]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[RaiseUnreachable]:
  gvs[evaluate_def, raise_def, no_type_error_result_def, type_stmt_def,
      return_exception_typed_def]
QED

Resume eval_all_type_sound_mutual[RaiseReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Raise (RaiseReason e)))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_raise_reason_def] >> strip_tac >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  rpt gen_tac >> reverse strip_tac >- (
    rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule_all >> simp[] >>
    drule_all eval_expr_exception_return_typed >>
    rw[] >> gvs[no_type_error_result_def]) >>
  BasicProvers.VAR_EQ_TAC >>
  first_x_assum drule_all >> simp[] >> strip_tac >>
  qhdtm_x_assum `expr_result_typed` mp_tac >>
  asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
  simp[evaluate_type_def] >> strip_tac >>
  drule toplevel_value_typed_StringTV >> strip_tac >> gvs[] >>
  gvs[get_Value_def, return_def, dest_StringV_def,
      lift_option_type_def, no_type_error_result_def, return_exception_typed_def] >>
  imp_res_tac raise_state >> gvs[]
QED

Resume eval_all_type_sound_mutual[AssertBare]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertBare))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    qhdtm_x_assum `expr_result_typed` mp_tac >>
    asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
    simp[evaluate_type_def] >> strip_tac >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def,
        no_type_error_result_def, return_exception_typed_def] >>
    metis_tac[return_state, raise_state]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[AssertUnreachable]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e AssertUnreachable))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def, APPEND_NIL] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    qhdtm_x_assum `expr_result_typed` mp_tac >>
    asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
    simp[evaluate_type_def] >> strip_tac >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    Cases_on `b` >> gvs[switch_BoolV_def, return_def, raise_def,
        no_type_error_result_def, return_exception_typed_def] >>
    metis_tac[return_state, raise_state]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[AssertReason]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Assert e (AssertReason e')))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def, int_calls_assert_reason_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_expr e'` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_expr e` >> simp[]) >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >>
  strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, raise_def,
       AllCaseEqs(), PULL_EXISTS] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `well_typed_expr env e ==> _` (drule_then strip_assume_tac) >>
  Cases_on `expr_res` >> rewrite_tac[no_type_error_result_def]
  >- (
    `expr_result_typed env e x` by (
      qpat_x_assum `case INL x of INL tv => expr_result_typed env e tv | INR v1 => T` mp_tac >>
      simp[]) >>
    qhdtm_x_assum `expr_result_typed` mp_tac >>
    asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
    rewrite_tac[Once evaluate_type_def] >> strip_tac >>
    `tv = BaseTV BoolT` by
      (qpat_x_assum `_ = SOME tv` mp_tac >>
       rewrite_tac[Once evaluate_type_def] >> simp[]) >>
    qpat_x_assum `tv = BaseTV BoolT` SUBST_ALL_TAC >>
    drule toplevel_value_typed_BoolTV >> strip_tac >>
    qpat_x_assum `x = Value (BoolV b)` SUBST_ALL_TAC >>
    Cases_on `b` >> rewrite_tac[switch_BoolV_def, return_def]
    >- (
      qpat_x_assum `!s'' tv t. _` kall_tac >>
      qpat_x_assum `!vt. _` kall_tac >>
      rpt strip_tac >> gvs[return_def, no_type_error_result_def]) >>
    Cases_on `eval_expr cx e' st1` >>
    rename1 `eval_expr cx e' st1 = (reason_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `reason_res` >> gvs[no_type_error_result_def]
    >- (
      qhdtm_x_assum `expr_result_typed` mp_tac >>
      asm_rewrite_tac[expr_result_typed_def, expr_runtime_typed_def] >>
      simp[evaluate_type_def] >> strip_tac >>
      drule toplevel_value_typed_StringTV >> strip_tac >>
      gvs[bind_def, get_Value_def, return_def, dest_StringV_def,
          lift_option_type_def, raise_def, no_type_error_result_def,
          return_exception_typed_def] >>
      rw[] >> gvs[]) >>
    gvs[bind_def, no_type_error_result_def] >>
    rw[] >>
    drule eval_expr_exception_return_typed >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!s'' tv t. _` kall_tac >>
  qpat_x_assum `!vt. _` kall_tac >>
  gvs[no_type_error_result_def] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[Log]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (Log id es))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qhdtm_x_assum `type_stmt` mp_tac >>
  simp_tac(srw_ss())[type_stmt_def] >> strip_tac >> BasicProvers.VAR_EQ_TAC >>
  qhdtm_x_assum `eval_stmt` mp_tac >>
  simp_tac(srw_ss())[evaluate_def, bind_def, return_def, push_log_def,
       no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (exprs_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `exprs_res` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> gvs[state_well_typed_def, accounts_well_typed_def] >>
    Cases_on `encode_source_event (get_tenv cx) cx.sources cx.txn.target id x` >>
    gvs[lift_option_def, return_def, raise_def] >>
    drule_all env_consistent_logs_append >>
    simp[return_exception_typed_def]) >>
  strip_tac >> gvs[] >>
  drule eval_exprs_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[AnnAssign]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (AnnAssign id typ e))` mp_tac >>
  pure_rewrite_tac[int_calls_stmt_def] >> strip_tac >>
  qpat_x_assum `type_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once type_stmt_def] >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  `get_tenv cx = env.type_defs` by fs[env_consistent_def, env_context_consistent_def] >>
  `?tyv. evaluate_type env.type_defs typ = SOME tyv` by
    (qspecl_then [`env.type_defs`,`typ`] mp_tac assignable_type_well_formed >>
     simp[] >> rewrite_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  pop_assum strip_assume_tac >>
  irule annassign_statement_sound_from_expr_ih >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (qexists_tac `tyv` >> simp[]) >>
  conj_tac >- simp[] >>
  qexists_tac `e` >> qexists_tac `st` >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!tenv s'' tyv t. _`
        (qspecl_then [`env.type_defs`, `st`, `tyv`, `st`] mp_tac) >>
      simp[lift_option_type_def, return_def] >>
      disch_then drule_all >> strip_tac >>
      qpat_x_assum `well_typed_expr env' e ==> _` (drule_then strip_assume_tac) >>
      simp[]) >>
  rpt conj_tac >> asm_rewrite_tac[]
QED

Resume eval_all_type_sound_mutual[Append]:
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
  rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `bt_res`
  >- (
    PairCases_on `x` >>
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `expr_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl, st2)` >>
      Cases_on `materialise cx tvl st2` >>
      rename1 `materialise cx tvl st2 = (mat_res, st3)` >>
      Cases_on `mat_res` >> gvs[no_type_error_result_def]
      >- (
        rename1 `materialise cx tvl st2 = (INL v, st3)` >>
        qpat_x_assum `do _ od _ = _` mp_tac >>
        simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
        Cases_on `assign_target cx (BaseTargetV x0 x1) (AppendOp v) st3` >>
        rename1 `assign_target cx (BaseTargetV loc sbs) (AppendOp v) st3 = (assign_res, st4)` >>
        Cases_on `assign_res` >> simp[return_def, ignore_bind_apply, no_type_error_result_def] >>
        strip_tac >> gvs[] >>
        imp_res_tac materialise_state >> gvs[] >>
        `?elem_tv. evaluate_type env.type_defs (expr_type e) = SOME elem_tv` by (
          drule assignable_type_well_formed >>
          rw[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
        `well_formed_type_value elem_tv` by
          metis_tac[evaluate_type_well_formed_type_value] >>
        `value_has_type elem_tv v` by (
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule_at(Pat`materialise`) materialise_preserves_value_type >>
          simp[] >> disch_then irule >> simp[]) >>
        `target_runtime_typed env cx st1 (BaseTarget bt)
           (ArrayT (expr_type e) (Dynamic n)) (BaseTargetV loc sbs)` by (
          rw[target_runtime_typed_def, target_value_shape_def,
             well_typed_atarget_def, well_typed_target_def] >>
          metis_tac[]) >>
        `runtime_consistent env cx st2` by simp[runtime_consistent_def] >>
        `target_runtime_typed env cx st2 (BaseTarget bt)
           (ArrayT (expr_type e) (Dynamic n)) (BaseTargetV loc sbs)` by (
          irule target_runtime_typed_rebuild >> simp[] >> goal_assum drule) >>
        `assign_operation_runtime_typed env (ArrayT (expr_type e) (Dynamic n)) (AppendOp v)` by
          metis_tac[stmt_assign_operation_runtime_typed_Append_from_value_has_type] >>
        `assign_operation_matches_target_shape (BaseTargetV loc sbs) (AppendOp v)` by
          simp[stmt_assign_operation_matches_target_shape_Append_BaseTargetV] >>
        `assign_target_assignable_context cx (BaseTargetV loc sbs) st2` by
          metis_tac[target_runtime_typed_imp_assignable_context, runtime_consistent_def] >>
        rpt strip_tac >> gvs[] >>
        `assignable_type env.type_defs (ArrayT (expr_type e) (Dynamic n))` by (
          simp[assignable_type_def, well_formed_type_def] >>
          drule_at(Pat`target_runtime_typed`) target_runtime_typed_place_leaf_typed >>
          simp[] >> strip_tac >>
          drule place_leaf_typed_evaluate_type >>
          simp[optionTheory.IS_SOME_EXISTS]) >>
        drule_at(Pat`assign_target`) assign_target_preserves_runtime_consistent_result >>
        disch_then $ drule_at(Pat`target_runtime_typed`) >> simp[] >>
        strip_tac >> gvs[runtime_consistent_def, no_type_error_result_def] >>
        qspecl_then [`cx`, `BaseTargetV loc sbs`, `st2`,
          `INR (Error (TypeError msg))`, `st'`, `env`, `BaseTarget bt`,
          `expr_type e`, `elem_tv`, `n`, `v`] mp_tac
          assign_target_append_no_type_error >>
        simp[no_type_error_result_def, runtime_consistent_def] >>
        strip_tac >> drule (cj 1 assign_target_no_control) >>
        rw[no_control_exc_return_exception_typed]) >>
      strip_tac >> gvs[] >>
      qpat_x_assum `do _ od _ = _` mp_tac >>
      simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
      strip_tac >> gvs[] >>
      drule materialise_state >> strip_tac >> gvs[] >>
      conj_tac
      >- (rpt strip_tac >> gvs[] >>
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule_at_then Any drule
            materialise_typed_non_none_no_type_error >>
          simp[] >>
          `expr_type e ≠ NoneT` by metis_tac[assignable_type_not_NoneT] >>
          metis_tac[evaluate_type_not_NoneT_imp_not_NoneTV]) >>
      drule materialise_no_control >>
      rw[no_control_exc_return_exception_typed]) >>
    strip_tac >> gvs[] >>
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
    strip_tac >> gvs[] >>
    drule eval_expr_exception_return_typed >> rw[]) >>
  strip_tac >>
  qpat_x_assum `case (INR _,_) of _ => _ | _ => _` mp_tac >>
  pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `(INR y,st1) = (res,st')` mp_tac >>
  pure_rewrite_tac[pairTheory.PAIR_EQ] >> strip_tac >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `st1 = st'` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- qpat_assum `state_well_typed st1` ACCEPT_TAC >>
  conj_tac >- qpat_assum `accounts_well_typed st1.accounts` ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `!s'' loc sbs t'. _` kall_tac >>
                qpat_x_assum `case INR _ of _ => _ | _ => _` kall_tac >>
                fs[no_type_error_result_def]) >>
  drule (cj 3 eval_target_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Resume eval_all_type_sound_mutual[Assign]:
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
  rename1 `eval_target cx tgt st = (target_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `target_res`
  >- (
    rename1 `eval_target cx tgt st = (INL gv, st1)` >>
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    Cases_on `eval_expr cx e st1` >>
    rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `expr_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `eval_expr cx e st1 = (INL tvl, st2)` >>
      Cases_on `materialise cx tvl st2` >>
      rename1 `materialise cx tvl st2 = (mat_res, st3)` >>
      Cases_on `mat_res` >> gvs[no_type_error_result_def]
      >- (
        rename1 `materialise cx tvl st2 = (INL v, st3)` >>
        Cases_on `assign_target cx gv (Replace v) st3` >>
        rename1 `assign_target cx gv (Replace v) st3 = (assign_res, st4)` >>
        Cases_on `assign_res` >> gvs[return_def, bind_apply, no_type_error_result_def]
        >- (
          imp_res_tac materialise_state >> gvs[] >>
          simp[bind_apply, ignore_bind_apply, return_def] >>
          strip_tac >> gvs[] >>
          drule_at(Pat`assign_target`)
            assign_target_preserves_state_well_typed_no_ctx >>
          simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
          disch_then drule >>
          simp[value_runtime_typed_def, expr_runtime_typed_def, PULL_EXISTS] >>
          drule_at(Pat`materialise`) materialise_preserves_value_type >>
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule evaluate_type_well_formed_type_value >>
          strip_tac >>
          disch_then drule_all >> strip_tac >>
          disch_then $ drule_at Any >>
          disch_then $ drule_at Any >>
          strip_tac >>
          `target_runtime_typed env cx st2 tgt (expr_type e) gv` by (
            irule target_runtime_typed_rebuild >>
            simp[runtime_consistent_def] >>
            goal_assum drule) >>
          first_x_assum drule >> strip_tac >>
          conj_tac >- simp[] >>
          conj_tac >- simp[] >>
          drule_at(Pat`assign_target`) assign_target_preserves_runtime_consistent_no_ctx >>
          simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
          disch_then drule >>
          simp[value_runtime_typed_def, expr_runtime_typed_def] >>
          strip_tac >> first_x_assum irule >> simp[] >>
          qexists_tac `tgt` >> qexists_tac `expr_type e` >> simp[] >>
          qexists_tac `tv` >> simp[]) >>
        qpat_x_assum `do _ od _ = _` mp_tac >> simp[bind_apply, return_def] >>
        Cases_on `res` >> gvs[ignore_bind_apply] >>
        strip_tac >> gvs[] >>
        strip_tac >> gvs[] >>
        imp_res_tac materialise_state >> gvs[] >>
        `?tv. evaluate_type env.type_defs (expr_type e) = SOME tv` by (
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule evaluate_type_well_formed_type_value >> simp[]) >>
        `well_formed_type_value tv` by (
          drule evaluate_type_well_formed_type_value >> simp[]) >>
        `toplevel_value_typed tvl tv` by (
          gvs[expr_result_typed_def, expr_runtime_typed_def]) >>
        `value_has_type tv v` by metis_tac[materialise_preserves_type] >>
        `target_runtime_typed env cx st2 tgt (expr_type e) gv` by (
          irule target_runtime_typed_rebuild >>
          simp[runtime_consistent_def] >> goal_assum drule) >>
        drule_at(Pat`assign_target`)
          assign_target_preserves_state_well_typed_no_ctx >>
        simp[assign_operation_runtime_typed_def, value_runtime_typed_def] >>
        simp[runtime_consistent_def] >>
        strip_tac >>
        drule_all eval_expr_preserves_ec >> strip_tac >>
        conj_asm1_tac
        >- (rpt strip_tac >> gvs[] >>
            first_x_assum (qspecl_then [`env`,`tgt`,`expr_type e`] mp_tac) >>
            simp[]) >>
        drule_at(Pat`assign_target`)
          assign_target_preserves_runtime_consistent_no_ctx >>
        simp[runtime_consistent_def, assign_operation_runtime_typed_def] >>
        simp[value_runtime_typed_def, PULL_EXISTS] >>
        disch_then(drule_at(Pat`target_runtime_typed`)) >> simp[] >>
        strip_tac >>
        Cases_on `y` >> rw[return_exception_typed_def]
        >- (
          (* Error case: need e' ≠ TypeError msg *)
          `runtime_consistent env cx st2` by (
            simp[runtime_consistent_def] >> goal_assum drule >> simp[]) >>
          `value_runtime_typed env (expr_type e) v` by (
            simp[value_runtime_typed_def] >>
            qexists `tv` >> simp[]) >>
          `assign_operation_runtime_typed env (expr_type e) (Replace v)` by
            simp[assign_operation_runtime_typed_def] >>
          `assign_operation_matches_target_shape gv (Replace v)` by
            metis_tac[assign_operation_matches_target_shape_Replace_from_typed] >>
          `assign_target_assignable_context cx gv st2` by
            metis_tac[target_runtime_typed_imp_assignable_context] >>
          drule assign_target_no_type_error >>
          simp[no_type_error_result_def] >> metis_tac[])
        >- (
          (* ReturnException case: assign_target never returns ReturnException *)
          drule (cj 1 assign_target_no_return) >> simp[])) >>
      strip_tac >> gvs[] >>
      drule materialise_state >> strip_tac >> gvs[] >>
      conj_tac
      >- (rpt strip_tac >> gvs[] >>
          (* materialise TypeError sub-case: contradiction from typed non-None expr *)
          gvs[expr_result_typed_def, expr_runtime_typed_def] >>
          drule_at_then Any drule
            materialise_typed_non_none_no_type_error >>
          simp[] >>
          `expr_type e ≠ NoneT` by metis_tac[assignable_type_not_NoneT] >>
          metis_tac[evaluate_type_not_NoneT_imp_not_NoneTV]) >>
      drule materialise_no_control >> rw[no_control_exc_return_exception_typed]) >>
    rw[] >> drule eval_expr_exception_return_typed >> rw[]) >>
  strip_tac >>
  qpat_x_assum `case (INR _,_) of _ => _ | _ => _` mp_tac >>
  pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `(INR y,st1) = (res,st')` mp_tac >>
  pure_rewrite_tac[pairTheory.PAIR_EQ] >> strip_tac >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `st1 = st'` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- qpat_assum `state_well_typed st1` ACCEPT_TAC >>
  conj_tac >- qpat_assum `accounts_well_typed st1.accounts` ACCEPT_TAC >>
  conj_tac >- (qpat_x_assum `!s'' gv t. _` kall_tac >>
                qpat_x_assum `case INR _ of _ => _ | _ => _` kall_tac >>
                fs[no_type_error_result_def]) >>
  drule (cj 1 eval_target_no_control) >>
  rw[no_control_exc_return_exception_typed]
QED

Resume eval_all_type_sound_mutual[AugAssign]:
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
  rename1 `eval_base_target cx bt st = (target_res, st1)` >>
  (* Apply base-target IH *)
  `type_place_target env bt = SOME (Type ty)` by fs[well_typed_target_def] >>
  qpat_x_assum `!env vt st res st'. _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ eval_base_target _ _ _ = _ ==> _`
    (qspecl_then [`env`, `Type ty`, `st`, `target_res`, `st1`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  Cases_on `target_res`
  >- (
    (* INL: base target evaluation succeeded *)
    PairCases_on `x` >>
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    pure_rewrite_tac[pairTheory.pair_case_def] >> BETA_TAC >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >>
    rename1 `eval_base_target cx bt st = (INL (loc,sbs), st1)` >>
    suspend "AugAssign_base_inl")
  >- (
    (* INR: base target evaluation returned exception *)
    fs[no_type_error_result_def] >>
    strip_tac >>
    qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
    qpat_x_assum `st1 = st'` (SUBST_ALL_TAC o SYM) >>
    conj_tac >- qpat_assum `state_well_typed st1` ACCEPT_TAC >>
    conj_tac >- qpat_assum `accounts_well_typed st1.accounts` ACCEPT_TAC >>
    conj_tac >- (rpt strip_tac >>
                  qpat_x_assum `!msg. y <> Error (TypeError msg)`
                    (qspec_then `msg` mp_tac) >>
                  qpat_x_assum `INR y = INR (Error (TypeError msg))` mp_tac >>
                  simp[]) >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >>
    conj_tac >- qpat_assum `env_consistent env cx st1` ACCEPT_TAC >>
    drule (cj 3 eval_target_no_control) >>
    rw[no_control_exc_return_exception_typed])
QED

Resume eval_all_type_sound_mutual[AugAssign_base_inl]:
  Cases_on `eval_expr cx e st1` >>
  rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
  (* Apply expr IH *)
  first_x_assum (qspecl_then [`st`, `loc`, `sbs`, `st1`] mp_tac) >> simp[] >>
  disch_then (qspecl_then [`env`, `st1`, `expr_res`, `st2`] mp_tac) >> simp[] >>
  `state_well_typed st1 /\ env_consistent env cx st1 /\ accounts_well_typed st1.accounts` by
    simp[] >>
  simp[] >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    (* INL: expression evaluation succeeded *)
    rename1 `eval_expr cx e st1 = (INL tvl, st2)` >>
    suspend "AugAssign_expr_inl")
  >- (
    (* INR: expression evaluation returned exception *)
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, bind_def] >>
    strip_tac >> gvs[] >>
    drule eval_expr_exception_return_typed >> strip_tac >>
    strip_tac >> gvs[])
QED

Resume eval_all_type_sound_mutual[AugAssign_expr_inl]:
  Cases_on `get_Value tvl st2` >>
  rename1 `get_Value tvl st2 = (val_res, st3)` >>
  Cases_on `val_res` >> gvs[no_type_error_result_def]
  >- (
    (* INL get_Value: got a plain value *)
    rename1 `get_Value tvl st2 = (INL v, st3)` >>
    suspend "AugAssign_get_value_inl")
  >- (
    (* INR get_Value: get_Value failed *)
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_apply, bind_def] >>
    strip_tac >> gvs[] >>
    imp_res_tac get_Value_state >> gvs[] >>
    drule get_Value_no_control >> strip_tac >>
    `!msg. y <> Error (TypeError msg)` by (
      gvs[expr_result_typed_def, expr_runtime_typed_def] >>
      drule_all well_typed_binop_not_In_second_type >> strip_tac >>
      drule_all evaluate_type_not_ArrayT_imp_not_ArrayTV >> strip_tac >>
      drule_all evaluate_type_not_NoneT_imp_not_NoneTV >> strip_tac >>
      drule_all get_Value_no_type_error >>
      simp[no_type_error_result_def]) >>
    drule no_control_exc_return_exception_typed >> strip_tac >>
    strip_tac >> gvs[no_type_error_result_def])
QED

Resume eval_all_type_sound_mutual[AugAssign_get_value_inl]:
  imp_res_tac get_Value_state >> gvs[] >>
  `tvl = Value v` by (
    qpat_x_assum `get_Value _ _ = _` mp_tac >>
    Cases_on `tvl` >> simp[get_Value_def, return_def, raise_def]) >>
  `target_runtime_typed env cx st1 (BaseTarget bt) ty (BaseTargetV loc sbs)` by (
    simp[target_runtime_typed_def, well_typed_atarget_def,
         target_value_shape_def] >>
    qexists `loc_vt` >> simp[]) >>
  `target_runtime_typed env cx st2 (BaseTarget bt) ty (BaseTargetV loc sbs)` by
    metis_tac[target_runtime_typed_rebuild, runtime_consistent_def] >>
  `assign_operation_runtime_typed env ty (Update ty bop v)` by (
    simp[assign_operation_runtime_typed_def] >>
    qexists_tac `expr_type e` >>
    gvs[expr_result_typed_def, expr_runtime_typed_def, value_runtime_typed_def,
        toplevel_value_typed_def]) >>
  `assign_operation_matches_target_shape (BaseTargetV loc sbs) (Update ty bop v)` by
    simp[assign_operation_matches_target_shape_def] >>
  `assign_target_assignable_context cx (BaseTargetV loc sbs) st2` by
    metis_tac[target_runtime_typed_imp_assignable_context] >>
  simp[bind_apply, return_def] >>
  Cases_on `assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st2` >>
  rename1 `assign_target _ _ _ _ = (assign_res, st4)` >>
  Cases_on `assign_res` >> simp[return_def, ignore_bind_def, no_type_error_result_def]
  >- suspend "AugAssign_assign_inl"
  >- suspend "AugAssign_assign_inr"
QED

Resume eval_all_type_sound_mutual[AugAssign_assign_inl]:
  (* INL assign_target: update succeeded *)
  strip_tac >> gvs[] >>
  drule_at(Pat`assign_target`)
    assign_target_preserves_runtime_consistent >>
  disch_then $ drule_at(Pat`target_runtime_typed`) >>
  simp[] >>
  impl_keep_tac >- simp[runtime_consistent_def] >>
  strip_tac >> gvs[runtime_consistent_def, bind_def, return_def]
QED

Resume eval_all_type_sound_mutual[AugAssign_assign_inr]:
  (* INR assign_target: update returned exception *)
  strip_tac >> gvs[] >>
  drule_at(Pat`assign_target`)
    assign_target_preserves_runtime_consistent_result >>
  disch_then $ drule_at(Pat`target_runtime_typed`) >>
  simp[] >>
  impl_keep_tac >- simp[runtime_consistent_def] >>
  strip_tac >> gvs[runtime_consistent_def] >>
  `res = INR y /\ st' = st4` by (
    qpat_x_assum `do _ od _ = _` mp_tac >>
    simp[bind_def, return_def]) >>
  gvs[] >>
  Cases_on `y` >> rw[return_exception_typed_def]
  >- (
    (* Error sub-case: derive no-TypeError from updated bridges *)
    `runtime_consistent env cx st2` by (
      simp[runtime_consistent_def] >> goal_assum drule >> simp[]) >>
    `well_typed_binop ty bop ty (expr_type e)` by (
      gvs[expr_result_typed_def, expr_runtime_typed_def,
          value_runtime_typed_def, toplevel_value_typed_def]) >>
    `value_runtime_typed env (expr_type e) v` by (
      gvs[expr_result_typed_def, expr_runtime_typed_def,
          value_runtime_typed_def, toplevel_value_typed_def]) >>
    drule assign_target_update_no_type_error >>
    simp[no_type_error_result_def, assign_operation_matches_target_shape_def] >>
    disch_then drule >> disch_then drule >>
    simp[] >> metis_tac[])
  >- (
    (* ReturnException sub-case: assign_target never returns ReturnException *)
    drule (cj 1 assign_target_no_return) >> simp[] >>
    disch_then drule >> simp[])
QED

Resume eval_all_type_sound_mutual[If]:
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
  first_x_assum drule_all >> strip_tac >>
  simp_tac (srw_ss()) [] >>
  rename1 `eval_expr cx e st = (cond_res, st1)` >>
  reverse(Cases_on `cond_res`)
  >- (
    simp_tac(srw_ss())[] >>
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    simp_tac(srw_ss())[] >>
    first_x_assum drule >>
    simp_tac(srw_ss())[no_type_error_result_def] >>
    strip_tac >>
    drule_all eval_expr_exception_return_typed >> simp[]
  ) >>
  simp_tac(srw_ss())[ignore_bind_def, bind_def] >>
  CASE_TAC >>
  reverse CASE_TAC >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    qpat_x_assum `push_scope st1 = (INR _,_)` mp_tac >>
    simp_tac(srw_ss())[push_scope_def,return_def]
  ) >>
  rename1 `eval_expr cx e st = (INL tv, st1)` >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
  qpat_x_assum `expr_result_typed env e tv`
    (strip_assume_tac o
     REWRITE_RULE [expr_result_typed_def, expr_runtime_typed_def,
                   evaluate_type_def]) >>
  qpat_x_assum `evaluate_type env.type_defs (expr_type e) = SOME tv'` mp_tac >>
  ASM_REWRITE_TAC[evaluate_type_def, vyperASTTheory.base_type_case_def] >> strip_tac >>
  qpat_x_assum `SOME (BaseTV BoolT) = SOME tv'` mp_tac >>
  disch_then (assume_tac o REWRITE_RULE [optionTheory.SOME_11]) >>
  BasicProvers.VAR_EQ_TAC >>
  drule toplevel_value_typed_BoolTV >> strip_tac >>
  BasicProvers.VAR_EQ_TAC >>
  strip_tac >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss)`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (type_stmts env ret_ty ss')`
    (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
  irule scope_bracket_post >>
  conj_asm1_tac >- (
    irule env_consistent_env_maps_wf >> simp[] >>
    goal_assum drule >> simp[]
  ) >>
  qmatch_asmsub_abbrev_tac`finally body_fun pop_scope sf` >>
  qexistsl_tac[`body_fun`,`st1`] >>
  PURE_REWRITE_TAC[bind_def, ignore_bind_def] >>
  ASM_REWRITE_TAC[] >>
  first_x_assum (drule_then drule) >> strip_tac >>
  last_x_assum (drule_then drule) >> strip_tac >>
  qpat_x_assum `push_scope st1 = (INL x',sf)`
    (strip_assume_tac o
     SIMP_RULE (srw_ss()) [push_scope_def, return_def]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  pure_rewrite_tac[pairTheory.pair_case_def, sumTheory.sum_case_def] >>
  BETA_TAC >> ASM_REWRITE_TAC[] >>
  qmatch_goalsub_abbrev_tac`body_fun st2` >>
  Cases_on`body_fun st2` >>
  simp_tac std_ss [pairTheory.PAIR_EQ, sumTheory.sum_case_def] >>
  qmatch_assum_rename_tac`body_fun st2 = (rf,sf)` >>
  qho_match_abbrev_tac`P rf sf` >>
  irule switch_BoolV_post >>
  qunabbrev_tac`body_fun` >>
  goal_assum $ drule_at(Pat`switch_BoolV`) >>
  simp[] >>
  `accounts_well_typed st2.accounts` by simp[Abbr`st2`] >>
  `env_consistent env cx st2` by (simp[Abbr`st2`] >> irule push_scope_env_consistent >> simp[]) >>
  conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qunabbrev_tac`P` >> BETA_TAC >>
    `state_well_typed st2` by (
      irule push_scope_preserves_state_well_typed >>
      qexists_tac `st1` >> qexists_tac `()` >>
      simp[push_scope_def, return_def, Abbr`st2`]) >>
    first_x_assum drule_all >> strip_tac >>
    simp[] >>
    `st2 = st1 with scopes := FEMPTY::st1.scopes`
      by simp[evaluation_state_component_equality, Abbr`st2`] >>
    conj_tac >- (
      strip_tac >> gvs[] >>
      drule eval_stmts_preserves_scopes_len >> simp[]) >>
    Cases_on `res1` >> gvs[]
    >- (
      Cases_on `st1'.scopes` >> gvs[]
      >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
      irule type_stmts_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
        simp[] >> disch_then irule >>
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      conj_tac >- (
        qexists_tac `x''` >>
        qexists_tac `ret_ty` >>
        qexists_tac `ss'` >> simp[] >>
        rpt strip_tac >> fs[] >>
        drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
        strip_tac >> gvs[FDOM_FEMPTY] >>
        drule lookup_scopes_is_some_same_fdoms >> simp[] >>
        disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
        qpat_x_assum `env_consistent env cx st1` mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
        strip_tac >> strip_tac >>
        Cases_on `lookup_scopes id t` >> gvs[] >>
        qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
          (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INL ()`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >>
      disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INL ()` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    conj_tac >- (
      irule env_extends_env_consistent_after_pop >> simp[] >>
      conj_tac >- (
        drule eval_stmts_preserves_scopes_len >> simp[] >>
        strip_tac >>
        `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
        Cases_on `st1.scopes` >> gvs[] >>
        Cases_on `t` >> gvs[]) >>


      conj_tac >- (
        conj_tac >- (
          rpt strip_tac >> fs[] >>
          `?entry. lookup_scopes id st1.scopes = SOME entry` by (
            qpat_x_assum`env_consistent _ _ st1`mp_tac >>
            simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
          `FLOOKUP h id = NONE` suffices_by simp[] >>
          drule lookup_scopes_not_in_new_head >>
          disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
          simp[] >>
          disch_then irule >> simp[]) >>
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >>
        disch_then irule >> simp[]) >>
      conj_tac >- (
        qexists_tac `env_exn` >> simp[] >>
        rpt strip_tac >> fs[] >>
        `lookup_scopes id st1.scopes = NONE` by (
          qpat_x_assum`env_consistent env cx st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
          Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
          metis_tac[optionTheory.IS_SOME_DEF]) >>
        qspecl_then [`cx`, `ss'`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
          mp_tac eval_stmts_preserves_tail_lookup_none >>
        simp[]) >>
      qexists_tac `st1` >> simp[] >>
      qspecl_then [`cx`, `ss'`, `FEMPTY`, `st1`, `INR y`, `st1'`]
        mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
      simp[] >> disch_then irule >>
      qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
      `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
      pop_assum SUBST1_TAC >>
      irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
      qexists_tac `INR y` >> qexists_tac `ss'` >> simp[] >>
      gvs[Abbr`stp`]) >>
    irule env_extends_return_exception_typed >>
    qexists_tac `env_exn` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qunabbrev_tac`P` >> BETA_TAC >>
  `state_well_typed st2` by (
    irule push_scope_preserves_state_well_typed >>
    qexists_tac `st1` >> qexists_tac `()` >>
    simp[push_scope_def, return_def, Abbr`st2`]) >>
  first_x_assum drule_all >> strip_tac >>
  simp[] >>
  `st2 = st1 with scopes := FEMPTY::st1.scopes`
    by simp[evaluation_state_component_equality, Abbr`st2`] >>
  conj_tac >- (
    strip_tac >> gvs[] >>
    drule eval_stmts_preserves_scopes_len >> simp[]) >>
  Cases_on `res1` >> gvs[]
  >- (
    Cases_on `st1'.scopes` >> gvs[]
    >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
    irule type_stmts_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      rpt strip_tac >> fs[] >>
      drule_at(Pat`eval_stmts`)lookup_scopes_not_in_new_head >>
      simp[] >> disch_then irule >>
      qpat_x_assum`env_consistent _ _ st1`mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
    conj_tac >- (
      qexists_tac `x` >>
      qexists_tac `ret_ty` >>
      qexists_tac `ss` >> simp[] >>
      rpt strip_tac >> fs[] >>
      drule eval_stmts_preserves_scopes_dom >> simp[preserves_scopes_dom_def] >>
      strip_tac >> gvs[FDOM_FEMPTY] >>
      drule lookup_scopes_is_some_same_fdoms >> simp[] >>
      disch_then (qspec_then `id` mp_tac) >> simp[optionTheory.IS_SOME_EXISTS] >>
      qpat_x_assum `env_consistent env cx st1` mp_tac >>
      simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS] >>
      strip_tac >> strip_tac >>
      Cases_on `lookup_scopes id t` >> gvs[] >>
      qpat_x_assum `!id entry. lookup_scopes id st1.scopes = SOME entry ==> _`
        (qspec_then `id` mp_tac) >> simp[] >> metis_tac[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INL ()`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >>
    disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INL ()` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  Cases_on `st1'.scopes` >> gvs[]
  >- (drule eval_stmts_preserves_scopes_len >> simp[]) >>
  conj_tac >- (
    irule env_extends_env_consistent_after_pop >> simp[] >>
    conj_tac >- (
      drule eval_stmts_preserves_scopes_len >> simp[] >>
      strip_tac >>
      `st1.scopes <> []` by fs[env_consistent_def, env_scopes_consistent_def] >>
      Cases_on `st1.scopes` >> gvs[] >>
      Cases_on `t` >> gvs[]) >>
    conj_tac >- (
      conj_tac >- (
        rpt strip_tac >> fs[] >>
        `?entry. lookup_scopes id st1.scopes = SOME entry` by (
          qpat_x_assum`env_consistent _ _ st1`mp_tac >>
          simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
        `FLOOKUP h id = NONE` suffices_by simp[] >>
        drule lookup_scopes_not_in_new_head >>
        disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
        simp[] >> disch_then irule >> simp[]) >>
      rpt strip_tac >> fs[] >>
      `?entry. lookup_scopes id st1.scopes = SOME entry` by (
        qpat_x_assum`env_consistent _ _ st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def, IS_SOME_EXISTS]) >>
      `FLOOKUP h id = NONE` suffices_by simp[] >>
      drule lookup_scopes_not_in_new_head >>
      disch_then(qspecl_then [`id`, `entry`] mp_tac) >>
      simp[] >> disch_then irule >> simp[]) >>
    conj_tac >- (
      qexists_tac `env_exn` >> simp[] >>
      rpt strip_tac >> fs[] >>
      `lookup_scopes id st1.scopes = NONE` by (
        qpat_x_assum`env_consistent env cx st1`mp_tac >>
        simp[env_consistent_def, env_scopes_consistent_def] >> strip_tac >>
        Cases_on `lookup_scopes id st1.scopes` >> gvs[] >>
        metis_tac[optionTheory.IS_SOME_DEF]) >>
      qspecl_then [`cx`, `ss`, `st1`, `FEMPTY`, `st1.scopes`, `INR y`, `st1'`, `id`, `h`, `t`]
        mp_tac eval_stmts_preserves_tail_lookup_none >>
      simp[]) >>
    qexists_tac `st1` >> simp[] >>
    qspecl_then [`cx`, `ss`, `FEMPTY`, `st1`, `INR y`, `st1'`]
      mp_tac (GEN_ALL eval_stmts_scope_bracket_gen_preserves_tv) >>
    simp[] >> disch_then irule >>
    qmatch_goalsub_abbrev_tac `preserves_tv cx stp st1'` >>
    `stp = st1 with scopes updated_by CONS FEMPTY` by simp[Abbr`stp`] >>
    pop_assum SUBST1_TAC >>
    irule(CONJUNCT1(CONJUNCT2 eval_preserves_tv)) >>
    qexists_tac `INR y` >> qexists_tac `ss` >> simp[] >>
    gvs[Abbr`stp`]) >>
  irule env_extends_return_exception_typed >>
  qexists_tac `env_exn` >> simp[]
QED

Resume eval_all_type_sound_mutual[Expr]:
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
  Cases_on `q` >> gvs[no_type_error_result_def]
  >- (
    strip_tac >> gvs[expr_result_typed_def] >>
    metis_tac[]) >>
  strip_tac >> gvs[] >>
  drule_all eval_expr_exception_return_typed >> simp[]
QED

Resume eval_all_type_sound_mutual[Stmts_nil]:
  rpt gen_tac >> strip_tac >>
  gvs[Once type_stmt_def, Once evaluate_def,
      return_def, no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Stmts_cons]:
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
    Cases_on `eval_stmts cx ss st1` >>
    rename1 `eval_stmts cx ss st1 = (r2,st2)` >>
    first_x_assum drule_all >> strip_tac >>
    strip_tac >> fs[bind_def] >> gvs[] >>
    Cases_on `r2` >> gvs[no_type_error_result_def]
    >- (
      qexists_tac `env_exn` >> simp[] >>
      irule env_extends_trans >>
      qexists_tac `env''` >> simp[] >>
      irule type_stmt_env_extends >> simp[] >>
      conj_tac >- (irule env_consistent_env_maps_wf >> goal_assum drule >> simp[]) >>
      qexists_tac `ret_ty` >> qexists_tac `s` >> simp[]) >>
    simp[]) >>
  strip_tac >> gvs[] >>
  qexists_tac `env` >> simp[env_extends_refl]
QED

Resume eval_all_type_sound_mutual[For]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_stmt (For id typ it n body'))` mp_tac >>
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
  `env.type_defs = get_tenv cx` by (
    qpat_x_assum `env_consistent env cx st` mp_tac >>
    rewrite_tac[env_consistent_def, env_context_consistent_def] >>
    strip_tac >> simp[]) >>
  `?env_after. type_stmts (extend_local env (string_to_num id) typ F) ret_ty body' = SOME env_after` by (
    qpat_x_assum `IS_SOME (type_stmts (extend_local env (string_to_num id) typ F) ret_ty body')` mp_tac >>
    rewrite_tac[optionTheory.IS_SOME_EXISTS]) >>
  `well_formed_type env.type_defs typ` by metis_tac[assignable_type_well_formed] >>
  qpat_x_assum `well_formed_type env.type_defs typ` mp_tac >>
  qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >>
  rewrite_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  strip_tac >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME iter_tyv` >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, lift_option_type_def,
       check_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `eval_iterator cx it st` >>
  rename1 `eval_iterator cx it st = (iter_res, st1)` >>
  qpat_x_assum `!tenv s'' tyv t. _`
    (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`] mp_tac) >>
  impl_tac >- simp[lift_option_type_def, return_def] >>
  disch_then (qspecl_then [`env`, `typ`, `st`, `iter_res`, `st1`] mp_tac) >>
  impl_tac >- metis_tac[] >>
  strip_tac >>
  Cases_on `iter_res`
  >- (
    rename1 `eval_iterator cx it st = (INL vs, st1)` >>
    qpat_x_assum `case INL vs of INL vs => _ | INR v1 => _`
      (mp_tac o SIMP_RULE (srw_ss()) []) >>
    strip_tac >>
    `tyv = iter_tyv` by (
      qpat_x_assum `evaluate_type env.type_defs typ = SOME tyv` mp_tac >>
      qpat_assum `env.type_defs = get_tenv cx` (fn th => rewrite_tac[th]) >>
      qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
      simp[]) >>
    qpat_x_assum `EVERY (value_has_type tyv) vs` mp_tac >>
    qpat_x_assum `tyv = iter_tyv` (fn th => rewrite_tac[th]) >>
    strip_tac >>
    Cases_on `compatible_bound (Dynamic n) (LENGTH vs)`
    >- (
      qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
      qpat_assum `eval_iterator cx it st = (INL vs, st1)` (fn th => rewrite_tac[th]) >>
      rewrite_tac[bind_def, return_def, raise_def, assert_def, check_def, lift_option_type_def] >>
      Cases_on `eval_for cx iter_tyv (string_to_num id) body' vs st1` >>
      rename1 `eval_for cx iter_tyv (string_to_num id) body' vs st1 = (for_res, st2)` >>
      qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _`
        (qspecl_then [`get_tenv cx`, `st`, `iter_tyv`, `st`, `st`, `vs`, `st1`, `st1`, `()`, `st1`] mp_tac) >>
      impl_tac >- simp[lift_option_type_def, return_def, check_def, assert_def] >>
      disch_then (qspecl_then [`env`, `ret_ty`, `typ`, `env_after`, `st1`, `for_res`, `st2`] mp_tac) >>
      simp[bind_def, ignore_bind_def, return_def, assert_def] >> strip_tac >>
      strip_tac >> gvs[no_type_error_result_def]) >>
    strip_tac >>
    qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _` kall_tac >>
    qpat_x_assum `(let tenv = get_tenv cx in _) st = (res,st')` mp_tac >>
    qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
    qpat_assum `eval_iterator cx it st = (INL vs, st1)` (fn th => rewrite_tac[th]) >>
    simp[LET_THM, bind_def, ignore_bind_def, return_def, assert_def, raise_def,
        check_def, lift_option_type_def, no_type_error_result_def,
        return_exception_typed_def] >> strip_tac >> gvs[]) >>
  strip_tac >>
  qpat_x_assum `!tenv s'' tyv t s1 vs' t' s2 x t''. _` kall_tac >>
  qpat_x_assum `(let tenv = get_tenv cx in _) st = (res,st')` mp_tac >>
  qpat_assum `evaluate_type (get_tenv cx) typ = SOME iter_tyv` (fn th => rewrite_tac[th]) >>
  qpat_assum `eval_iterator cx it st = (INR y, st1)` (fn th => rewrite_tac[th]) >>
  simp[LET_THM, bind_def, ignore_bind_def, return_def, raise_def,
      lift_option_type_def] >>
  strip_tac >> gvs[] >>
  conj_tac >- (
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def]) >>
  irule no_control_exc_return_exception_typed >>
  drule eval_iterator_no_control >> simp[]
QED

Resume eval_all_type_sound_mutual[For_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_for _ _ _ _ [] _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >> gvs[no_type_error_result_def]
QED


Resume eval_all_type_sound_mutual[For_cons]:
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
  qunabbrev_tac `loop_body` >>
  drule for_body_decompose_for_cons_pushed >>
  rewrite_tac[ignore_bind_def] >>
  disch_then drule >>
  strip_tac >>
  `env.type_defs = get_tenv cx` by fs[env_consistent_def, env_context_consistent_def] >>
  `state_well_typed stp` by (
    `value_has_type tyv v` by fs[] >>
    `well_formed_type_value tyv` by (
      qpat_assum `evaluate_type env.type_defs ty = SOME tyv`
        (ACCEPT_TAC o MATCH_MP evaluate_type_well_formed_type_value)) >>
    qpat_x_assum `stp = _` SUBST1_TAC >>
    irule for_cons_pushed_state_well_typed >>
    simp[]) >>
  `accounts_well_typed stp.accounts` by (
    qpat_x_assum `stp = _` SUBST1_TAC >>
    simp[NoAsms, evaluation_state_component_equality] >>
    qpat_assum `accounts_well_typed st.accounts` ACCEPT_TAC) >>
  `env_consistent (extend_local env id ty F) cx stp` by (
    qunabbrev_tac `stp` >>
    metis_tac[push_scope_with_var_env_consistent]) >>
  qpat_x_assum `!s'' x t. push_scope_with_var id tyv v s'' = (INL x,t) ==> _`
    (qspecl_then [`st`, `()`, `stp`] mp_tac) >>
  impl_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
  disch_then (qspecl_then [`extend_local env id ty F`, `ret_ty`, `env_after`,
                           `stp`, `res_body`, `st_body`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  Cases_on `res_body` >> simp[NoAsms]
  >- (
    `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
      irule scope_bracket_preserves_swt >> simp[] >>
      qexists_tac `cx` >> qexists_tac `INL x` >>
      qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
      qexists_tac `body'` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
    `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
      simp[evaluation_state_component_equality] >>
    `env_consistent env cx (st_body with scopes := TL st_body.scopes)` by (
      `env_consistent env_after cx st_body` by (
        qpat_x_assum `case (INL x : unit + vyperState$exception) of INL u => _ | INR exn => _` mp_tac >>
        simp[NoAsms]) >>
      qpat_x_assum `stp = _` SUBST_ALL_TAC >>
      metis_tac[for_body_env_consistent_after_pop, env_consistent_env_maps_wf]) >>
    qpat_x_assum `!s'' x' t s''' broke t'. _`
      (qspecl_then [`st`, `()`, `stp`, `stp`, `F`,
                    `st_body with scopes := TL st_body.scopes`] mp_tac) >>
    impl_tac >- (
      conj_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
      conj_tac >- (
        `loop_res = INL F` by (
          qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
          simp[]) >>
        qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
        qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
        qpat_x_assum `stp = _` SUBST_ALL_TAC >>
        qpat_x_assum `finally _ _ _ = (INL F, _)` mp_tac >>
        strip_tac >>
        pop_assum mp_tac >>
        simp[NoAsms, bind_def, ignore_bind_def]) >>
      simp[]) >>
    `loop_res = INL F` by (
      qpat_x_assum `(∃x'. INL x = INL x') ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body' vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                             `st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    (impl_tac >- fs[]) >>
    simp[]) >>
  `state_well_typed (st_body with scopes := TL st_body.scopes)` by (
    irule scope_bracket_preserves_swt >> simp[] >>
    qexists_tac `cx` >> qexists_tac `INR y` >>
    qexists_tac `FEMPTY |+ (id, <|assignable := F; type := tyv; value := v|>)` >>
    qexists_tac `body'` >> qexists_tac `st` >> simp[Abbr`stp`]) >>
  `accounts_well_typed (st_body with scopes := TL st_body.scopes).accounts` by
    simp[evaluation_state_component_equality] >>
  SUBGOAL_THEN ``env_consistent env cx (st_body with scopes := TL st_body.scopes)`` assume_tac >- (
    irule for_cons_popped_env_consistent_from_stmt_case >>
    qexists_tac `body'` >> qexists_tac `y` >> qexists_tac `id` >>
    qexists_tac `\u. env_consistent env_after cx st_body` >>
    qexists_tac `ret_ty` >> qexists_tac `st` >> qexists_tac `ty` >>
    qexists_tac `tyv` >> qexists_tac `v` >>
    conj_tac >- simp[] >>
    conj_tac >- simp[Abbr`stp`] >>
    conj_tac >- simp[] >>
    asm_rewrite_tac[]) >>
  Cases_on `y = ContinueException`
  >- (
    qpat_x_assum `y = ContinueException` SUBST_ALL_TAC >>
    qpat_x_assum `!s'' x t s'³' broke t'. _`
      (qspecl_then [`st`, `()`, `stp`, `stp`, `F`,
                    `st_body with scopes := TL st_body.scopes`] mp_tac) >>
    impl_tac >- (
      conj_tac >- simp[push_scope_with_var_def, return_def, Abbr`stp`] >>
      conj_tac >- (
        `loop_res = INL F` by (
          qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
          simp[]) >>
        qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
        qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
        qpat_x_assum `stp = _` SUBST_ALL_TAC >>
        qpat_x_assum `finally _ pop_scope _ = (INL F, _)` mp_tac >>
        strip_tac >>
        pop_assum mp_tac >>
        simp[NoAsms, bind_def, ignore_bind_def]) >>
      simp[]) >>
    `loop_res = INL F` by (
      qpat_x_assum `INR ContinueException = INR ContinueException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL F` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    `eval_for cx tyv id body' vs (st_body with scopes := TL st_body.scopes) = (res,st')` by (
      qpat_x_assum `(case (INL F,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
      simp[return_def]) >>
    disch_then (qspecl_then [`env`, `ret_ty`, `ty`, `env_after`,
                             `st_body with scopes := TL st_body.scopes`, `res`, `st'`] mp_tac) >>
    (impl_tac >- fs[]) >>
    simp[]) >>
  Cases_on `y = BreakException`
  >- (
    qpat_x_assum `y = BreakException` SUBST_ALL_TAC >>
    `loop_res = INL T` by (
      qpat_x_assum `INR BreakException = INR BreakException ==> _` irule >>
      simp[]) >>
    qpat_x_assum `loop_res = INL T` SUBST_ALL_TAC >>
    qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
    qpat_x_assum `(case (INL T,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
    simp[NoAsms, return_def] >>
    strip_tac >>
    qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
    simp[no_type_error_result_def]) >>
  `loop_res = INR y` by (
    qpat_x_assum `!e. INR y = INR e /\ e <> ContinueException /\ e <> BreakException ==> _`
      (qspec_then `y` irule) >>
    simp[]) >>
  qpat_x_assum `loop_res = INR y` SUBST_ALL_TAC >>
  qpat_x_assum `st_after = _` SUBST_ALL_TAC >>
  qpat_x_assum `(case (INR y,_) of _ => _ | _ => _) = (res,st')` mp_tac >>
  simp[NoAsms] >>
  strip_tac >>
  qpat_x_assum `_ = st'` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `INR y = res` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!s'' x t s'³' broke t'. _` kall_tac >>
  qmatch_goalsub_abbrev_tac `state_well_typed stfinal` >>
  qunabbrev_tac `stfinal` >>
  irule for_cons_non_loop_exception_suffix_projected >>
  simp[] >>
  conj_tac >- (
    simp[no_type_error_result_def] >> strip_tac >>
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def] >>
    disch_then (qspec_then `msg` mp_tac) >> simp[]) >>
  fs[] >>
  qexists_tac `id` >> qexists_tac `ty` >>
  qexists_tac `env_exn` >> simp[]
QED

Resume eval_all_type_sound_mutual[Iterator_Array]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_iterator (Array e))` mp_tac >>
  pure_rewrite_tac[int_calls_iterator_def] >> strip_tac >>
  qpat_x_assum `well_typed_iterator _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [well_typed_iterator_def]) >>
  qpat_x_assum `eval_iterator _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `expr_res` >> gvs[no_type_error_result_def]
  >- (
    rename1 `eval_expr cx e st = (INL tvl, st1)` >>
    Cases_on `materialise cx tvl st1` >>
    rename1 `materialise cx tvl st1 = (mat_res, st2)` >>
    Cases_on `mat_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `materialise cx tvl st1 = (INL v, st2)` >>
      drule materialise_state >> strip_tac >> gvs[] >>
      gvs[expr_result_typed_def, expr_runtime_typed_def] >>
      `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
      gvs[] >>
      drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
      `value_has_type (ArrayTV elem_tv bd) v` by
        metis_tac[materialise_preserves_value_type,
                  evaluate_type_well_formed_type_value] >>
      Cases_on `lift_option_type (extract_elements (ArrayTV elem_tv bd) v) "For not ArrayV" st2` >>
      rename1 `lift_option_type _ _ st2 = (lift_res, st3)` >>
      drule lift_option_type_state >> strip_tac >> gvs[] >>
      Cases_on `lift_res` >> gvs[return_def, no_type_error_result_def]
      >- (
        rename1 `lift_option_type (extract_elements (ArrayTV elem_tv bd) v) _ st2 = (INL vs, st2)` >>
        strip_tac >> gvs[lift_option_type_def] >>
        Cases_on `extract_elements (ArrayTV elem_tv bd) v` >>
        gvs[raise_def, return_def] >>
        Cases_on `v` >> gvs[extract_elements_def] >>
        rename1 `ArrayV av` >>
        irule extract_elements_well_typed >>
        qexists_tac `av` >> qexists_tac `bd` >> simp[] >>
        conj_tac >- metis_tac[evaluate_type_well_formed_type_value] >>
        simp[extract_elements_def]) >>
      Cases_on `extract_elements (ArrayTV elem_tv bd) v` >>
      gvs[lift_option_type_def, raise_def, return_def] >>
      Cases_on `v` >> gvs[extract_elements_def, value_has_type_def]) >>
    drule materialise_state >> strip_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    gvs[expr_result_typed_def, expr_runtime_typed_def] >>
    `env.type_defs = get_tenv cx` by gvs[env_consistent_def, env_context_consistent_def] >>
    gvs[] >>
    drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[] >>
    irule materialise_typed_non_none_no_type_error >>
    qexists_tac `cx` >> qexists_tac `st'` >> qexists_tac `st'` >>
    qexists_tac `tvl` >> qexists_tac `ArrayTV elem_tv bd` >> simp[]) >>
  strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Iterator_Range]:
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
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (expr1_res, st1)` >>
  last_x_assum drule_all >> strip_tac >>
  Cases_on `expr1_res`
  >- (
    qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
    rename1 `eval_expr cx e st = (INL tv1, st1)` >>
    Cases_on `get_Value tv1 st1` >>
    rename1 `get_Value tv1 st1 = (val1_res, st2)` >>
    Cases_on `val1_res`
    >- (
      rename1 `get_Value tv1 st1 = (INL v1, st2)` >>
      drule get_Value_state >> strip_tac >>
      qpat_x_assum `st2 = st1` SUBST_ALL_TAC >>
      qpat_x_assum `!s'' tv1 t s''' s t'. _`
        (qspecl_then [`st`, `tv1`, `st1`, `st1`, `v1`, `st1`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `eval_expr cx e' st1` >>
      rename1 `eval_expr cx e' st1 = (expr2_res, st3)` >>
      qpat_x_assum `!env' st' res st''. _`
        (qspecl_then [`env`, `st1`, `expr2_res`, `st3`] mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
      impl_tac >- simp[] >> strip_tac >>
      Cases_on `expr2_res`
      >- (
        qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
        rename1 `eval_expr cx e' st1 = (INL tv2, st3)` >>
        Cases_on `get_Value tv2 st3` >>
        rename1 `get_Value tv2 st3 = (val2_res, st4)` >>
        Cases_on `val2_res`
        >- (
          qpat_x_assum `case INL _ of _ => _ | _ => _` mp_tac >> rewrite_tac[] >> strip_tac >>
          rename1 `get_Value tv2 st3 = (INL v2, st4)` >>
          drule get_Value_state >> strip_tac >>
          qpat_x_assum `st4 = st3` SUBST_ALL_TAC >>
          `tv1 = Value v1` by (
            qpat_x_assum `get_Value tv1 _ = _` mp_tac >>
            Cases_on `tv1` >> simp[get_Value_def, return_def, raise_def]) >>
          `tv2 = Value v2` by (
            qpat_x_assum `get_Value tv2 _ = _` mp_tac >>
            Cases_on `tv2` >> simp[get_Value_def, return_def, raise_def]) >>
          gvs[expr_result_typed_def, expr_runtime_typed_def, toplevel_value_typed_def] >>
          `?i1. v1 = IntV i1` by metis_tac[int_typed_value_is_IntV] >>
          `?i2. v2 = IntV i2` by metis_tac[int_typed_value_is_IntV] >>
          gvs[] >>
          Cases_on `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3` >>
          rename1 `lift_sum (get_range_limits (IntV i1) (IntV i2)) st3 = (range_res, st5)` >>
          strip_tac >>
          qspecl_then [`env.type_defs`, `expr_type e`, `tv`, `i1`, `i2`,
                       `range_res`, `st3`, `st5`, `res`, `st'`]
            mp_tac iterator_range_tail_eval_sound >>
          impl_tac >- (
            simp[] >>
            qpat_x_assum `case (range_res,st5) of _ => _ | _ => _` mp_tac >>
            Cases_on `range_res` >> simp[return_def, raise_def]) >>
          strip_tac >> gvs[]) >>
        imp_res_tac get_Value_state >> gvs[] >>
        strip_tac >> gvs[] >>
        gvs[expr_result_typed_def, expr_runtime_typed_def] >>
        qspecl_then [`env.type_defs`, `expr_type e`, `tv`] mp_tac
          is_int_type_evaluate_type_not_None_Array >>
        impl_tac >- simp[] >> strip_tac >>
        simp[no_type_error_result_def] >>
        irule get_Value_INR_no_type_error >>
        qexistsl_tac [`st'`, `st'`, `tv2`, `tv`] >> simp[]) >>
      strip_tac >> gvs[return_def, no_type_error_result_def] >> metis_tac[]) >>
    drule get_Value_state >> strip_tac >>
    qpat_x_assum `st2 = st1` SUBST_ALL_TAC >>
    strip_tac >>
    drule_all iterator_range_first_get_value_error_eq >> strip_tac >>
    qpat_x_assum `res = INR y` SUBST_ALL_TAC >>
    qpat_x_assum `st' = st1` SUBST_ALL_TAC >>
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
    impl_tac >- simp[] >> strip_tac >>
    qpat_x_assum `case INL tv1 of _ => _ | _ => _` mp_tac >>
    rewrite_tac[] >> strip_tac >>
    rpt conj_tac >> simp[] >>
    irule int_expr_get_Value_INR_no_type_error >>
    qexistsl_tac [`e`, `env`, `st1`, `st1`, `tv1`, `ty`] >>
    simp[] >>
    qpat_x_assum `case INL tv1 of _ => _ | _ => _` mp_tac >>
    simp[sum_case_def]) >>
  strip_tac >>
  drule_all iterator_range_expr_error_eq >> strip_tac >>
  qpat_x_assum `res = INR y` SUBST_ALL_TAC >>
  qpat_x_assum `st' = st1` SUBST_ALL_TAC >>
  qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
  impl_tac >- simp[] >> strip_tac >>
  qpat_x_assum `case INR y of _ => _ | _ => _` mp_tac >>
  simp[sum_case_def] >>
  qpat_x_assum `(case (INR y,st1) of _ => _ | _ => _) = (INR y,st1)` kall_tac >>
  fs[no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Target_Base]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_atarget (BaseTarget bt))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  gvs[well_typed_atarget_def, well_typed_target_def] >>
  Cases_on `eval_base_target cx bt st` >>
  rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `bt_res` >> gvs[no_type_error_result_def]
  >- (Cases_on `x` >> gvs[return_def] >> strip_tac >> gvs[] >>
      simp[target_runtime_typed_def, target_value_shape_def,
           well_typed_atarget_def, well_typed_target_def] >> metis_tac[]) >>
  simp[return_def] >> strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Target_Tuple]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_atarget (TupleTarget tgts))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  qpat_x_assum `eval_target _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  gvs[well_typed_atarget_def] >>
  Cases_on `eval_targets cx tgts st` >>
  rename1 `eval_targets cx tgts st = (tgts_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `tgts_res` >> gvs[no_type_error_result_def, return_def]
  >- (strip_tac >> gvs[target_runtime_typed_def] >>
      conj_tac >- gvs[well_typed_atarget_def] >>
      simp[target_value_shape_def] >>
      conj_tac
      >- metis_tac[target_values_runtime_typed_imp_shape,
                   target_values_runtime_typed_LIST_REL3] >>
      simp[target_values_runtime_typed_LIST_REL3]) >>
  strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Targets_nil]:
  rpt gen_tac >> strip_tac >>
  gvs[Once evaluate_def, return_def, no_type_error_result_def, LIST_REL3_def]
QED

Resume eval_all_type_sound_mutual[Targets_cons]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_atargets (tgt::tgts))` mp_tac >>
  pure_rewrite_tac[int_calls_atarget_def] >> strip_tac >>
  `call_evaluation_safe cx (int_calls_atarget tgt)` by
    (irule call_evaluation_safe_append_left >>
     qexists_tac `int_calls_atargets tgts` >> simp[]) >>
  `call_evaluation_safe cx (int_calls_atargets tgts)` by
    (irule call_evaluation_safe_append_right >>
     qexists_tac `int_calls_atarget tgt` >> simp[]) >>
  qpat_x_assum `eval_targets _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
  Cases_on `tys` >- fs[] >>
  qpat_x_assum `LIST_REL _ (tgt::tgts) (h::t)` mp_tac >>
  simp_tac(srw_ss())[listTheory.LIST_REL_CONS1] >> strip_tac >>
  Cases_on `eval_target cx tgt st` >>
  rename1 `eval_target cx tgt st = (target_res, st1)` >>
  qpat_x_assum `!env ty st res st'. well_typed_atarget env tgt ty /\ _ ==> _` drule_all >> strip_tac >>
  Cases_on `target_res` >> gvs[no_type_error_result_def]
  >- (Cases_on `eval_targets cx tgts st1` >>
      rename1 `eval_targets cx tgts st1 = (targets_res, st2)` >>
      first_x_assum (qspecl_then [`st`, `x`, `st1`] mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`env`, `t`, `st1`, `targets_res`, `st2`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `targets_res` >> gvs[no_type_error_result_def, return_def]
      >- (strip_tac >> gvs[LIST_REL3_def] >>
          metis_tac[target_runtime_typed_rebuild, runtime_consistent_def]) >>
      strip_tac >> gvs[]) >>
  simp[return_def] >> strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[BaseTarget_Name]:
  rpt gen_tac >>
  `∃ty. vt = Type ty` by gvs[well_typed_expr_def,AllCaseEqs()] >>
  gvs[] >>
  drule_all NameTarget_sound >>
  strip_tac >>
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, assert_def, ignore_bind_def,
    get_scopes_def, type_check_def, assert_def] >>
  strip_tac >> gvs[] >>
  simp[no_type_error_result_def, base_target_value_shape_def] >>
  qexists_tac `Type ty` >> simp[location_runtime_typed_def] >>
  conj_tac >- (
    gvs[well_typed_expr_def, AllCaseEqs(), LET_THM,
        env_consistent_def, env_scopes_consistent_def,
        env_context_consistent_def] >>
    first_x_assum (qspecl_then [`string_to_num id`, `ty`, `entry`] mp_tac) >>
    simp[]) >>
  simp[target_path_type_refl]
QED

Theorem is_immutable_decl_MEM_Immutable_exists[local]:
  !n ts. is_immutable_decl n ts ==>
  ?vis id ty init. MEM (VariableDecl vis Immutable id ty init) ts /\ string_to_num id = n
Proof
  Induct_on `ts` >> rw[is_immutable_decl_def] >>
  Cases_on `h` >> gvs[is_immutable_decl_def] >>
  Cases_on `v0` >> gvs[is_immutable_decl_def] >>
  metis_tac[]
QED

Theorem nonbare_toplevel_not_immutable[local]:
  env_consistent env cx st /\
  FLOOKUP env.bare_globals (src,n) = NONE /\
  get_module_code cx src = SOME ts /\
  is_immutable_decl n ts ==>
  F
Proof
  rpt strip_tac >>
  drule_all is_immutable_decl_MEM_Immutable_exists >> strip_tac >>
  gvs[env_consistent_def, env_context_consistent_def,
      bare_globals_complete_def] >>
  qpat_x_assum `!src ts vis mut id ty init. _`
    (qspecl_then [`src`, `ts`, `vis`, `Immutable`, `id`, `ty`, `init`] mp_tac) >>
  gvs[]
QED

Theorem bare_global_immutable_value_and_type[local]:
  (!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==>
     ?tv v. FLOOKUP (get_source_immutables src imms) id = SOME (tv,v)) /\
  (!src id ty tv v. FLOOKUP bare_globals (src,id) = SOME ty /\
     FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) ==>
     evaluate_type tenv ty = SOME tv) /\
  FLOOKUP bare_globals (src,n) = SOME ty ==>
  ?tv v. FLOOKUP (get_source_immutables src imms) n = SOME (tv,v) /\
         evaluate_type tenv ty = SOME tv
Proof
  rpt strip_tac >>
  qpat_x_assum `!src id ty. FLOOKUP bare_globals (src,id) = SOME ty ==> ?tv v. _`
    (drule_then strip_assume_tac) >>
  goal_assum drule >> simp[] >>
  qpat_x_assum `!src id ty tv v. _` drule_all >> simp[]
QED

Resume eval_all_type_sound_mutual[BaseTarget_TopLevel]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `type_place_target _ (TopLevelNameTarget _) = _` mp_tac >>
  simp[type_place_target_TopLevelNameTarget] >> strip_tac >> gvs[] >>
  TRY (drule eval_base_target_TopLevelNameTarget_preserves_state >> simp[]) >|
  [
    `FLOOKUP env.bare_globals (src_id_opt,string_to_num id) = SOME ty /\
     ?ts. get_module_code cx src_id_opt = SOME ts /\
          is_immutable_decl (string_to_num id) ts /\
          IS_SOME (FLOOKUP (get_source_immutables src_id_opt
            (case ALOOKUP st.immutables cx.txn.target of NONE => [] | SOME m => m))
            (string_to_num id))` by (
      gvs[env_consistent_def, env_context_consistent_def,
          env_immutables_consistent_def] >>
      qpat_x_assum `!src id ty. FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==> _`
        drule >> simp[] >> strip_tac >>
      first_x_assum drule >> simp[]) >>
    qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, lift_option_type_def, return_def, raise_def] >>
    strip_tac >> gvs[no_type_error_result_def, base_target_value_shape_def,
                     location_runtime_typed_def, target_path_type_refl,
                     optionTheory.IS_SOME_EXISTS] >>
    gvs[IS_SOME_EXISTS, get_immutables_def, get_address_immutables_def,
        lift_option_type_def, lift_option_def, return_def,
        get_source_immutables_def, AllCaseEqs()] >>
    Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
    PairCases_on `x` >> gvs[] >>
    qexists_tac `Type ty` >> simp[target_path_type_refl] >>
    qexists_tac `case ALOOKUP x' src_id_opt of NONE => FEMPTY | SOME imm => imm` >>
    qexists_tac `x1` >> qexists_tac `x0` >>
    gvs[env_consistent_def, env_context_consistent_def, env_immutables_consistent_def,
        get_immutables_def, get_address_immutables_def, lift_option_type_def,
        lift_option_def, bind_def, return_def, get_source_immutables_def] >>
    qpat_x_assum `!src id ty' tv v. _`
      (qspecl_then [`src_id_opt`, `string_to_num id`, `ty`, `x0`, `x1`] mp_tac) >>
    simp[base_target_value_shape_def, optionTheory.IS_SOME_EXISTS] >>
    strip_tac >> gvs[],

    `?code. get_module_code cx src_id_opt = SOME code` by (
      gvs[env_consistent_def, env_context_consistent_def] >>
      Cases_on `vt` >> gvs[] >> metis_tac[]) >>
    qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, lift_option_type_def, return_def, raise_def,
         get_immutables_def, get_address_immutables_def] >>
    Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def] >>
    Cases_on `is_immutable_decl (string_to_num id) code` >- (
      drule_all nonbare_toplevel_not_immutable >> simp[]) >>
    gvs[return_def] >>
    simp[no_type_error_result_def, base_target_value_shape_def] >>
    simp[location_runtime_typed_def] >>
    gvs[place_leaf_typed_def, leaf_type_def] >>
    rw[] >> gvs[env_consistent_def] >>
    gvs[env_context_consistent_def] >>
    first_x_assum drule >>
    rw[well_formed_vtype_def, well_formed_type_def] >>
    gvs[IS_SOME_EXISTS, target_path_type_refl, base_target_value_shape_def] >>
    TRY (qexists_tac `vt` >> simp[location_runtime_typed_def, target_path_type_refl]) >>
    TRY (rw[lift_option_type_def, return_def])
  ]
QED

Resume eval_all_type_sound_mutual[BaseTarget_Subscript]:
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
  rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `bt_res`
  >- (PairCases_on `x` >> rewrite_tac[bind_def, return_def] >>
      qpat_x_assum `!s'' loc sbs t'. _`
        (qspecl_then [`st`, `x0`, `x1`, `st1`] mp_tac) >> simp[] >>
      strip_tac >>
      Cases_on `eval_expr cx e st1` >>
      rename1 `eval_expr cx e st1 = (expr_res, st2)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `expr_res` >> gvs[no_type_error_result_def, bind_def, return_def]
      >- (Cases_on `get_Value x st2` >>
          rename1 `get_Value tv st2 = (value_res, st3)` >>
          `no_type_error_result value_res` by
            metis_tac[subscript_vtype_index_get_Value_no_type_error] >>
          Cases_on `value_res` >> gvs[no_type_error_result_def, return_def] >>
          Cases_on `tv` >> gvs[get_Value_def, return_def, raise_def] >>
          strip_tac >> gvs[base_target_value_shape_def] >> simp[] >>
          qexists_tac `loc_vt` >> simp[] >>
          conj_tac >- (
            irule location_runtime_typed_rebuild >>
            simp[runtime_consistent_def] >>
            qexists_tac `st1` >> simp[]) >>
          irule subscript_vtype_value_step_type >>
          qexistsl_tac [`vt'`, `e`, `expr_type e`, `st'`, `st'`, `Value v`] >>
          simp[get_Value_def, return_def]) >>
      strip_tac >> gvs[]) >>
  strip_tac >> pop_assum mp_tac >>
  simp_tac(srw_ss())[] >>
  strip_tac >>
  qpat_x_assum `INR y = res` (fn th => SUBST_ALL_TAC (SYM th)) >>
  qpat_x_assum `st1 = st'` (fn th => SUBST_ALL_TAC (SYM th)) >>
  simp[no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[BaseTarget_Attribute]:
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
  rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
  simp[AllCaseEqs(),return_def,EXISTS_PROD] >>
  ntac 3 strip_tac >> gvs[] >>
  first_x_assum drule_all >> strip_tac >>
  gvs[no_type_error_result_def, base_target_value_shape_def] >>
  goal_assum drule >>
  Cases_on`tgt_ty` >> gvs[attribute_type_def, AllCaseEqs()] >>
  simp[target_path_type_def] >>
  goal_assum drule >>
  simp[target_path_step_type_def] >>
  simp[attribute_type_def]
QED

Resume eval_all_type_sound_mutual[Expr_Name]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, get_scopes_def,
      lift_option_type_def, return_def, raise_def, no_type_error_result_def,
      AllCaseEqs()] >>
  strip_tac >> gvs[]
  >- (strip_tac >>
      drule_all well_typed_Name_lookup >> strip_tac >>
      `lookup_scopes_val (string_to_num id) st.scopes = SOME entry.value` by
        simp[lookup_scopes_val_SOME] >>
      gvs[bind_def, return_def, expr_result_typed_def, expr_runtime_typed_def,
          well_typed_expr_def, expr_type_def, toplevel_value_typed_Value]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_TopLevelName]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> gvs[]
  >- (strip_tac >>
      imp_res_tac lookup_global_state >> gvs[] >>
      drule_all lookup_global_TopLevelName_sound >>
      strip_tac >> gvs[]) >>
  rpt strip_tac >>
  imp_res_tac lookup_global_state >> gvs[] >>
  drule_all lookup_global_TopLevelName_place_sound >>
  strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Expr_FlagMember]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def] >> strip_tac >> gvs[]
  >- (strip_tac >>
      drule_all flag_member_sound >> strip_tac >>
      imp_res_tac lookup_flag_mem_state >> gvs[] >>
      PairCases_on `nsid` >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      qpat_x_assum `!src fid ls. FLOOKUP env.flag_members (src,fid) = SOME ls ==> _`
        (drule_then strip_assume_tac) >>
      `LENGTH members <= 256` by (
        qpat_x_assum `well_typed_expr env (FlagMember _ _ _)` mp_tac >>
        gvs[well_typed_expr_def, well_formed_type_def, evaluate_type_def] >>
        decide_tac) >>
      qpat_x_assum `lookup_flag_mem _ _ _ _ = _` mp_tac >>
      simp[lookup_flag_mem_def, return_def, raise_def] >>
      Cases_on `INDEX_OF mid members` >> strip_tac >>
      gvs[return_def, no_type_error_result_def, expr_result_typed_def,
          expr_runtime_typed_def, expr_type_def, toplevel_value_typed_Value,
          evaluate_type_def, value_has_type_def, INDEX_OF_eq_NONE,
          INDEX_OF_eq_SOME] >>
      irule bitTheory.TWOEXP_MONO >> simp[]) >>
  rpt strip_tac >> gvs[well_typed_expr_def]
QED


(* ===== If-expression helpers and Resume block ===== *)

Theorem evaluate_type_BaseT_BoolT[local]:
  evaluate_type tenv (BaseT BoolT) = SOME (BaseTV BoolT)
Proof
  simp[evaluate_type_def]
QED

Theorem expr_result_typed_BaseT_BoolT_value[local]:
  expr_result_typed env e tv /\ expr_type e = BaseT BoolT ==>
  toplevel_value_typed tv (BaseTV BoolT)
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def] >>
  gvs[evaluate_type_BaseT_BoolT]
QED

Theorem expr_result_typed_IfExp_branch[local]:
  well_typed_expr env branch /\ expr_type branch = ty /\
  expr_result_typed env branch tv ==>
  expr_result_typed env (IfExp ty cond e1 e2) tv
Proof
  rw[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
      well_typed_expr_def] >>
  metis_tac[well_typed_expr_not_hashmap_place]
QED

Theorem ifexp_branch_from_cond_ih[local]:
  (!s0 tv0 t0.
     eval_expr cx cond s0 = (INL tv0,t0) ==>
     !env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx branch st0 = (res0,st0') ==>
       (well_typed_expr env0 branch ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 branch tv | INR exn => T) /\
       !vt. type_place_expr env0 branch = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR exn => T) /\
  eval_expr cx cond cond_st = (INL cond_tv,branch_st) /\
  well_typed_expr env branch /\ expr_type branch = ty /\
  env_consistent env cx branch_st /\ state_well_typed branch_st /\
  context_well_typed cx /\ accounts_well_typed branch_st.accounts /\
  functions_well_typed cx /\ eval_expr cx branch branch_st = (res,st') ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
    INL tv => expr_result_typed env (IfExp ty cond e_true e_false) tv
  | INR exn => T
Proof
  strip_tac >>
  qpat_x_assum `!s0 tv0 t0. eval_expr cx cond s0 = (INL tv0,t0) ==> _`
    (qspecl_then [`cond_st`,`cond_tv`,`branch_st`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then [`env`,`branch_st`,`res`,`st'`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  Cases_on `res` >> gvs[] >>
  irule expr_result_typed_IfExp_branch >> simp[] >>
  qexists `branch` >> simp[]
QED

Theorem ifexp_switch_from_branch_ihs[local]:
  toplevel_value_typed cond_tv (BaseTV BoolT) /\
  eval_expr cx cond cond_st = (INL cond_tv,branch_st) /\
  switch_BoolV cond_tv (eval_expr cx e_true) (eval_expr cx e_false) branch_st = (res,st') /\
  (!s0 tv0 t0.
     eval_expr cx cond s0 = (INL tv0,t0) ==>
     !env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx e_true st0 = (res0,st0') ==>
       (well_typed_expr env0 e_true ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 e_true tv | INR exn => T) /\
       !vt. type_place_expr env0 e_true = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR exn => T) /\
  (!s0 tv0 t0.
     eval_expr cx cond s0 = (INL tv0,t0) ==>
     !env0 st0 res0 st0'.
       env_consistent env0 cx st0 /\ state_well_typed st0 /\
       context_well_typed cx /\ accounts_well_typed st0.accounts /\
       functions_well_typed cx /\ eval_expr cx e_false st0 = (res0,st0') ==>
       (well_typed_expr env0 e_false ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => expr_result_typed env0 e_false tv | INR exn => T) /\
       !vt. type_place_expr env0 e_false = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR exn => T) /\
  well_typed_expr env e_true /\ expr_type e_true = ty /\
  well_typed_expr env e_false /\ expr_type e_false = ty /\
  env_consistent env cx branch_st /\ state_well_typed branch_st /\
  context_well_typed cx /\ accounts_well_typed branch_st.accounts /\
  functions_well_typed cx ==>
  state_well_typed st' /\ env_consistent env cx st' /\
  accounts_well_typed st'.accounts /\ no_type_error_result res /\
  case res of
    INL tv => expr_result_typed env (IfExp ty cond e_true e_false) tv
  | INR exn => T
Proof
  strip_tac >>
  qho_match_abbrev_tac `P res st'` >>
  irule switch_BoolV_post >>
  goal_assum $ drule_at (Pat `switch_BoolV`) >>
  simp[] >>
  rpt strip_tac
  >- (qunabbrev_tac `P` >> BETA_TAC >>
      irule ifexp_branch_from_cond_ih >>
      conj_tac >- simp[] >>
      conj_tac >- simp[] >>
      qexistsl [`e_false`,`branch_st`,`cond_st`,`cond_tv`] >>
      conj_tac >- (
        qpat_assum `!s0 tv0 t0. eval_expr cx cond s0 = (INL tv0,t0) ==> !env0 st0 res0 st0'. _`
          ACCEPT_TAC) >>
      asm_rewrite_tac[])
  >- (qunabbrev_tac `P` >> BETA_TAC >>
      irule ifexp_branch_from_cond_ih >>
      conj_tac >- simp[] >>
      conj_tac >- simp[] >>
      qexistsl [`e_true`,`branch_st`,`cond_st`,`cond_tv`] >>
      conj_tac >- (
        qpat_assum `!s0 tv0 t0. eval_expr cx cond s0 = (INL tv0,t0) ==> !env0 st0 res0 st0'. _`
          ACCEPT_TAC) >>
      asm_rewrite_tac[])
QED

Theorem type_place_expr_IfExp_NONE[local]:
  !env ty cond e_true e_false.
    type_place_expr env (IfExp ty cond e_true e_false) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_IfExp]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (IfExp ty e e' e''))` mp_tac >>
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
  reverse conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (IfExp _ _ _ _) = SOME _` mp_tac >>
    simp[type_place_expr_IfExp_NONE]) >>
  disch_then mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
      qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_expr cx e st` >>
      rename1 `eval_expr cx e st = (cond_res, st1)` >>
      qpat_x_assum `!env st res st'. env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e) /\ eval_expr cx e st = (res,st') ==> _`
        (qspecl_then [`env`,`st`,`cond_res`,`st1`] mp_tac) >>
      impl_tac >- simp[] >>
      strip_tac >>
      qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      impl_tac >- simp[] >>
      strip_tac >>
      Cases_on `cond_res`
      >- (
        simp_tac bool_ss [] >>
        qpat_x_assum `case INL x of INL tv => expr_result_typed env e tv | INR v1 => T`
          (assume_tac o SIMP_RULE (srw_ss()) []) >>
        `toplevel_value_typed x (BaseTV BoolT)` by
          metis_tac[expr_result_typed_BaseT_BoolT_value] >>
        qpat_x_assum `(case (INL _,_) of _ => _ | _ => _) = _` mp_tac >>
        simp_tac bool_ss [] >> strip_tac >>
        strip_tac >>
        `switch_BoolV x (eval_expr cx e') (eval_expr cx e'') st1 = (res,st')` by (
          qpat_x_assum `(case (INL x,st1) of
                           (INL tv,s'') => switch_BoolV tv (eval_expr cx e') (eval_expr cx e'') s''
                         | (INR exn,s'') => (INR exn,s'')) = (res,st')` mp_tac >>
          simp_tac(srw_ss())[]) >>
        irule ifexp_switch_from_branch_ihs >>
        conj_tac >- (
          rpt strip_tac >>
          qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> !env st res st'. env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e'') /\ eval_expr cx e'' st = (res,st') ==> _`
            (qspecl_then [`s0`,`tv0`,`t0`] mp_tac) >>
          (impl_tac >- asm_rewrite_tac[]) >>
          strip_tac >>
          qpat_x_assum `!env st res st'. _`
            (qspecl_then [`env0`,`st0`,`res0`,`st0'`] mp_tac) >>
          (impl_tac >- simp[]) >>
          strip_tac >>
          metis_tac[]) >>
        conj_tac >- (
          rpt strip_tac >>
          qpat_x_assum `!s'' tv t. eval_expr cx e s'' = (INL tv,t) ==> !env st res st'. env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\ accounts_well_typed st.accounts /\ functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e') /\ eval_expr cx e' st = (res,st') ==> _`
            (qspecl_then [`s0`,`tv0`,`t0`] mp_tac) >>
          (impl_tac >- asm_rewrite_tac[]) >>
          strip_tac >>
          qpat_x_assum `!env st res st'. _`
            (qspecl_then [`env0`,`st0`,`res0`,`st0'`] mp_tac) >>
          (impl_tac >- simp[]) >>
          strip_tac >>
          metis_tac[]) >>
        asm_rewrite_tac[] >>
        qexistsl [`st1`,`st`,`x`] >>
        asm_rewrite_tac[])
      >- (
        simp_tac bool_ss [] >>
        strip_tac >>
        qpat_x_assum `(case (INR y,st1) of
                         (INL tv,s'') => switch_BoolV tv (eval_expr cx e') (eval_expr cx e'') s''
                       | (INR exn,s'') => (INR exn,s'')) = (res,st')` mp_tac >>
        simp_tac(srw_ss())[] >>
        strip_tac >>
        qpat_x_assum `INR y = res` (assume_tac o GSYM) >>
        qpat_x_assum `st1 = st'` (assume_tac o GSYM) >>
        qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
        strip_tac >>
        asm_rewrite_tac[] >>
        simp_tac(srw_ss())[])
QED

Resume eval_all_type_sound_mutual[Expr_Literal]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >>
  gvs[no_type_error_result_def, well_typed_expr_def, well_formed_type_def,
      expr_type_def, optionTheory.IS_SOME_EXISTS] >>
  rw[expr_result_typed_def, expr_runtime_typed_def, expr_type_def] >>
  metis_tac[literal_toplevel_value_typed]
QED


(* ===== Struct literal helpers and Resume block ===== *)

Theorem well_typed_named_exprs_MAP_SND_stmt[local]:
  !env kes. well_typed_named_exprs env kes ==> well_typed_exprs env (MAP SND kes)
Proof
  gen_tac >> Induct >> simp[well_typed_expr_def] >>
  Cases >> simp[well_typed_expr_def]
QED

Theorem struct_has_type_zip_same_names_stmt[local]:
  !names tvs vs.
    LENGTH names = LENGTH tvs /\ LENGTH tvs = LENGTH vs /\
    LIST_REL value_has_type tvs vs ==>
    struct_has_type (ZIP (names,tvs)) (ZIP (names,vs))
Proof
  Induct >> simp[Once value_has_type_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `tvs` >> Cases_on `vs` >> gvs[Once value_has_type_def]
QED


Theorem OPT_MMAP_from_LIST_REL_evaluate_type_stmt[local]:
  !tys tvs tenv.
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
    OPT_MMAP (evaluate_type tenv) tys = SOME tvs
Proof
  Induct >> Cases_on `tvs` >> simp[OPT_MMAP_def]
QED

Theorem OPT_MMAP_evaluate_type_mono_stmt[local]:
  !types tenv nid tvs.
    OPT_MMAP (evaluate_type (tenv \\ nid)) types = SOME tvs ==>
    OPT_MMAP (evaluate_type tenv) types = SOME tvs
Proof
  Induct >> simp[OPT_MMAP_def] >>
  rpt gen_tac >>
  Cases_on `evaluate_type (tenv \\ nid) h` >> simp[] >>
  Cases_on `OPT_MMAP (evaluate_type (tenv \\ nid)) types` >> simp[] >>
  strip_tac >> gvs[] >>
  imp_res_tac evaluate_type_mono >> simp[] >>
  first_x_assum (qspecl_then [`tenv`, `nid`] mp_tac) >> simp[]
QED
Theorem struct_lit_expr_result_typed[local]:
  well_formed_type env.type_defs (StructT nsid) /\
  FLOOKUP env.type_defs (type_key nsid) = SOME (StructArgs args) /\
  MAP FST kes = MAP FST args /\
  MAP (expr_type o SND) kes = MAP SND args /\
  exprs_runtime_typed env (MAP SND kes) vs ==>
  expr_result_typed env (StructLit (StructT nsid) nsid kes)
    (Value (StructV (ZIP (MAP FST args,vs))))
Proof
  rw[exprs_runtime_typed_def, expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_def] >>
  qexists_tac `StructTV (ZIP (MAP FST args,tvs))` >>
  gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qpat_x_assum `evaluate_type _ (StructT _) = SOME _` mp_tac >>
  simp[Once evaluate_type_def, AllCaseEqs(), evaluate_types_OPT_MMAP] >>
  strip_tac >> gvs[value_has_type_def] >>
  qpat_x_assum `MAP (expr_type o SND) kes = MAP SND args` (assume_tac o GSYM) >>
  gvs[] >>
  `OPT_MMAP (evaluate_type env.type_defs) (MAP (expr_type o SND) kes) = SOME tvs` by
    (irule OPT_MMAP_from_LIST_REL_evaluate_type_stmt >>
     gvs[LIST_REL_EL_EQN, EL_MAP]) >>
  `OPT_MMAP (evaluate_type env.type_defs) (MAP (expr_type o SND) kes) = SOME tvs'` by
    metis_tac[OPT_MMAP_evaluate_type_mono_stmt] >>
  gvs[] >>
  irule struct_has_type_zip_same_names_stmt >>
  imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_MAP] >>
  metis_tac[LENGTH_MAP]
QED

Theorem type_place_expr_StructLit_NONE_stmt[local]:
  !env ty sid kes.
    type_place_expr env (StructLit ty sid kes) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_StructLit]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_evaluation_safe cx (int_calls_expr (StructLit ty callee kes))` mp_tac >>
  pure_rewrite_tac[int_calls_expr_def, GSYM int_calls_exprs_MAP_SND] >> strip_tac >>
  reverse conj_tac >- (
    rpt strip_tac >>
    qpat_x_assum `type_place_expr _ (StructLit _ _ _) = SOME _` mp_tac >>
    simp[type_place_expr_StructLit_NONE_stmt]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr _ (StructLit _ _ _)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_expr _ (StructLit _ _ _) _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_exprs cx (MAP SND kes) st` >>
  rename1 `eval_exprs cx (MAP SND kes) st = (exprs_res,st1)` >>
  qpat_x_assum `!ks. ks = MAP FST kes ==> _` (qspec_then `MAP FST kes` mp_tac) >>
  simp_tac bool_ss [] >>
  `well_typed_exprs env (MAP SND kes)` by
    (irule well_typed_named_exprs_MAP_SND_stmt >> first_assum ACCEPT_TAC) >>
  disch_then drule_all >> strip_tac >>
  Cases_on `exprs_res` >> simp_tac(srw_ss())[]
  >- (
    strip_tac >>
    qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
    asm_simp_tac(srw_ss())[bind_def, return_def, LET_THM] >>
    strip_tac >> gvs[no_type_error_result_def] >>
    irule struct_lit_expr_result_typed >>
    asm_rewrite_tac[])
  >- (
    strip_tac >>
    qpat_x_assum `eval_exprs cx (MAP SND kes) st = (INR y,st1)` (fn ev_th =>
      qpat_x_assum `(let ks = MAP FST kes in do vs <- eval_exprs cx (MAP SND kes); return (Value (StructV (ZIP (ks,vs)))) od) st = (res,st')` mp_tac >>
      asm_simp_tac(srw_ss())[Once bind_def, return_def, LET_THM, ev_th]) >>
    strip_tac >>
    gvs[] >>
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    simp[no_type_error_result_def])
QED


(* ===== Subscript expression helpers and Resume block ===== *)

Theorem subscript_type_ok_evaluate_stmt[local]:
  !ct it rt tenv atv.
    subscript_type_ok ct it rt /\
    evaluate_type tenv ct = SOME atv ==>
    ?rtv. evaluate_type tenv rt = SOME rtv
Proof
  Cases >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[Once evaluate_type_def, AllCaseEqs()] >>
  gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
  Cases_on `l` >> gvs[IS_SOME_EXISTS]
QED

Theorem evaluate_subscript_success_not_HashMapRef_stmt[local]:
  !tenv tv_ty tv idx res.
    evaluate_subscript tenv tv_ty tv idx = INL (INL res) /\ ~is_HashMapRef tv ==>
    ~is_HashMapRef res
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `tv` >> gvs[is_HashMapRef_def]
  >- (Cases_on `v` >> Cases_on `idx` >>
      gvs[evaluate_subscript_def, AllCaseEqs(), is_HashMapRef_def])
  >- (Cases_on `idx` >>
      gvs[evaluate_subscript_def, AllCaseEqs(), is_HashMapRef_def])
QED

Theorem values_have_types_LIST_REL_stmt[local]:
  !tys tvs. values_have_types tys tvs = LIST_REL value_has_type tys tvs
Proof
  Induct >> rw[value_has_type_def] >>
  Cases_on `tvs` >> gvs[value_has_type_def]
QED

Theorem evaluate_subscript_value_well_typed_stmt[local]:
  !tenv arr_tv av idx v ct it ty rtv.
    subscript_type_ok ct it ty /\
    evaluate_type tenv ct = SOME arr_tv /\
    evaluate_type tenv ty = SOME rtv /\
    value_has_type arr_tv (ArrayV av) /\
    array_index arr_tv av idx = SOME v ==>
    value_has_type rtv v
Proof
  rpt gen_tac >>
  Cases_on `ct` >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[]
  >- (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF] >>
      Cases_on `av` >> gvs[value_has_type_inv] >>
      gvs[array_index_def, AllCaseEqs()] >>
      gvs[oEL_EQ_EL] >>
      gvs[values_have_types_LIST_REL_stmt, LIST_REL_EL_EQN] >>
      first_x_assum (qspec_then `Num idx` mp_tac) >> simp[EL_MAP] >>
      `EL (Num idx) l = ty` by (gvs[EVERY_EL] >> res_tac) >>
      gvs[])
  >> (gvs[Once evaluate_type_def, AllCaseEqs()] >>
      imp_res_tac (cj 1 evaluate_type_well_formed) >>
      metis_tac[array_index_has_type])
QED

Theorem evaluate_subscript_typed_stmt[local]:
  !tenv arr_tv x idx x' ct it result_ty.
    evaluate_subscript tenv arr_tv x idx = INL x' /\
    toplevel_value_typed x arr_tv /\
    ~is_HashMapRef x /\
    subscript_type_ok ct it result_ty /\
    evaluate_type tenv ct = SOME arr_tv ==>
    ?rtv. evaluate_type tenv result_ty = SOME rtv /\
          (case x' of
           | INL tv => toplevel_value_typed tv rtv
           | INR (is_trans, slot, tv) => tv = rtv)
Proof
  rpt gen_tac >> Cases_on `x` >>
  simp[toplevel_value_typed_def, is_HashMapRef_def]
  >- (Cases_on `v` >> Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      imp_res_tac subscript_type_ok_evaluate_stmt >>
      Cases_on `evaluate_type tenv result_ty` >> gvs[toplevel_value_typed_def] >>
      irule evaluate_subscript_value_well_typed_stmt >>
      qexistsl [`arr_tv`,`a`,`ct`,`i`,`it`,`tenv`,`result_ty`] >>
      asm_rewrite_tac[])
  >> (Cases_on `idx` >>
      simp[evaluate_subscript_def, AllCaseEqs(), LET_THM] >>
      rpt strip_tac >> gvs[] >>
      Cases_on `ct` >> gvs[subscript_type_ok_def] >>
      gvs[Once evaluate_type_def, AllCaseEqs()] >>
      simp[toplevel_value_typed_def])
QED

Theorem value_has_type_TupleTV_dest_stmt[local]:
  !tvs v. value_has_type (TupleTV tvs) v ==>
          ?vs. v = ArrayV (TupleV vs) /\ values_have_types tvs vs
Proof
  Cases_on `v` >> gvs[value_has_type_inv] >>
  Cases_on `a` >> gvs[value_has_type_inv]
QED

Theorem value_has_type_ArrayTV_dest_stmt[local]:
  !tv bd v. value_has_type (ArrayTV tv bd) v ==> ?av. v = ArrayV av
Proof
  Cases_on `v` >> gvs[value_has_type_inv] >>
  Cases_on `a` >> gvs[value_has_type_inv]
QED

Theorem check_array_bounds_error_not_TypeError_stmt[local]:
  !cx tv v st y st'.
    check_array_bounds cx tv v st = (INR y, st') ==>
    !msg. y <> Error (TypeError msg)
Proof
  rw[oneline check_array_bounds_def, bind_def, return_def, raise_def,
     check_def, assert_def, AllCaseEqs(), toplevel_value_CASE_rator,
     value_CASE_rator, bound_CASE_rator] >>
  gvs[get_storage_backend_no_error]
QED

Theorem evaluate_subscript_error_not_TypeError_stmt[local]:
  !tenv arr_tv x idx err ct it result_ty idx_tv.
    evaluate_subscript tenv arr_tv x idx = INR err /\
    toplevel_value_typed x arr_tv /\
    ~is_HashMapRef x /\
    subscript_type_ok ct it result_ty /\
    evaluate_type tenv ct = SOME arr_tv /\
    evaluate_type tenv it = SOME idx_tv /\
    value_has_type idx_tv idx ==>
    !msg. err <> TypeError msg
Proof
  rpt gen_tac >> Cases_on `ct` >> simp[subscript_type_ok_def] >>
  rpt strip_tac >> gvs[Once evaluate_type_def, AllCaseEqs()] >>
  Cases_on `it` >> gvs[is_int_type_def, Once evaluate_type_def, AllCaseEqs()] >>
  TRY (Cases_on `b` >> gvs[is_int_type_def, Once evaluate_type_def]) >>
  Cases_on `x` >> gvs[toplevel_value_typed_def, is_HashMapRef_def] >>
  TRY (drule value_has_type_TupleTV_dest_stmt >> strip_tac >> gvs[]) >>
  TRY (drule value_has_type_ArrayTV_dest_stmt >> strip_tac >> gvs[]) >>
  Cases_on `idx` >>
  gvs[value_has_type_inv, evaluate_subscript_def, array_index_def,
      AllCaseEqs(), LET_THM, value_has_type_def]
QED

Theorem expr_subscript_storage_tail_sound_stmt[local]:
  !cx env e e' v9 x x'' y rtv bounds_st res st'.
    state_well_typed bounds_st /\
    env_consistent env cx bounds_st /\
    accounts_well_typed bounds_st.accounts /\
    evaluate_type (get_tenv cx) v9 = SOME rtv /\
    (case y of (is_trans,slot,tv') => tv' = rtv) /\
    well_formed_type_value rtv /\
    check_array_bounds cx x x'' bounds_st = (INL (),bounds_st) /\
    (do
       check_array_bounds cx x x'';
       res <- return (INR y);
       case res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
         do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od bounds_st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\
    (!msg. res <> INR (Error (TypeError msg))) /\
    (case res of
     | INL tv =>
         (?tv'. evaluate_type (get_tenv cx) (expr_type (Subscript v9 e e')) = SOME tv' /\
                toplevel_value_typed tv tv') /\
         (is_HashMapRef tv ==> ?kt vt. type_place_expr env (Subscript v9 e e') = SOME (HashMapT kt vt))
     | INR v1 => T)
Proof
  rpt gen_tac >> PairCases_on `y` >> simp[] >> rpt strip_tac >>
  qpat_x_assum `do check_array_bounds cx x x''; _ od bounds_st = (res,st')` mp_tac >>
  simp[bind_def, ignore_bind_def, return_def] >> strip_tac >>
  Cases_on `read_storage_slot cx y0 y1 rtv bounds_st` >>
  rename1 `read_storage_slot cx y0 y1 rtv bounds_st = (read_res,read_st)` >>
  `read_st = bounds_st` by metis_tac[read_storage_slot_state] >> gvs[] >>
  Cases_on `read_res` >> gvs[return_def, raise_def]
  >- (drule read_storage_slot_error >> strip_tac >> gvs[])
  >- (`value_has_type rtv x'` by metis_tac[read_storage_slot_success_type] >>
      qexists_tac `rtv` >>
      simp[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
           toplevel_value_typed_def, is_HashMapRef_def]) >>
  simp[toplevel_value_typed_def, is_HashMapRef_def]
QED
Theorem vtype_annotation_ok_well_formed_type_stmt[local]:
  !tenv vt ty.
    well_formed_vtype tenv vt /\ vtype_annotation_ok vt ty ==>
    well_formed_type tenv ty
Proof
  Cases_on `vt` >> simp[vtype_annotation_ok_def, well_formed_vtype_def] >>
  strip_tac >> simp[well_formed_type_def, evaluate_type_def]
QED

Theorem subscript_vtype_well_formed_stmt[local]:
  !tenv base_vt idx_ty result_vt.
    well_formed_vtype tenv base_vt /\
    subscript_vtype base_vt idx_ty = SOME result_vt ==>
    well_formed_vtype tenv result_vt
Proof
  Cases_on `base_vt` >>
  simp[subscript_vtype_def, well_formed_vtype_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (Cases_on `t` >>
      gvs[subscript_vtype_def, well_formed_vtype_def,
          well_formed_type_def, evaluate_type_def, AllCaseEqs()] >>
      Cases_on `evaluate_type tenv t'` >> gvs[]) >>
  gvs[]
QED

Theorem type_place_expr_well_formed_vtype_stmt[local]:
  !env cx st e vt.
    env_consistent env cx st /\ type_place_expr env e = SOME vt ==>
    well_formed_vtype env.type_defs vt
Proof
  measureInduct_on `expr_size e` >>
  rpt strip_tac >>
  Cases_on `e` >>
  gvs[Once well_typed_expr_def, AllCaseEqs()]
  >- (PairCases_on `p` >>
      qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
      simp[well_typed_expr_def, AllCaseEqs()] >> strip_tac >>
      gvs[env_consistent_def, env_context_consistent_def] >>
      first_x_assum drule >> simp[]) >>
  qpat_x_assum `!y. expr_size y < _ ==> _` (qspec_then `e'` mp_tac) >>
  (impl_tac >- simp[expr_size_def]) >>
  disch_then (qspecl_then [`env`,`cx`,`st`,`vt'`] mp_tac) >>
  simp[] >> strip_tac >>
  metis_tac[subscript_vtype_well_formed_stmt]
QED

Theorem type_place_expr_annotation_ok_stmt[local]:
  !env e vt. type_place_expr env e = SOME vt ==> vtype_annotation_ok vt (expr_type e)
Proof
  Cases_on `e` >> simp[expr_type_def] >> rpt strip_tac >>
  TRY (PairCases_on `p`) >>
  qpat_x_assum `type_place_expr _ _ = SOME _` mp_tac >>
  simp[Once well_typed_expr_def, vtype_annotation_ok_def, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem place_expr_result_typed_expr_result_typed_stmt[local]:
  !env e tv vt.
    type_place_expr env e = SOME vt /\
    place_expr_result_typed env tv vt ==>
    expr_result_typed env e tv
Proof
  rw[place_expr_result_typed_def, expr_result_typed_def,
     expr_runtime_typed_def] >>
  `vtype_annotation_ok vt (expr_type e)` by
    metis_tac[type_place_expr_annotation_ok_stmt] >>
  Cases_on `vt` >>
  gvs[vtype_annotation_ok_def, evaluate_type_def,
      toplevel_value_typed_def, is_HashMapRef_def] >>
  metis_tac[]
QED

Theorem check_array_bounds_hashmap_stmt[local]:
  !cx is_t slot kt vt kv st.
    check_array_bounds cx (HashMapRef is_t slot kt vt) kv st = (INL (), st)
Proof
  Cases_on `kv` >> rw[check_array_bounds_def, return_def]
QED


Theorem expr_subscript_place_projection_tail_sound_stmt[local]:
  !cx env e e' v9 base_vt result_vt base_tv idx_tv idx st res st'.
    state_well_typed st /\
    env_consistent env cx st /\
    accounts_well_typed st.accounts /\
    well_formed_type env.type_defs v9 /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME result_vt /\
    vtype_annotation_ok result_vt v9 /\
    place_expr_result_typed env base_tv base_vt /\
    expr_result_typed env e' idx_tv /\
    get_Value idx_tv st = (INL idx,st) /\
    (do
       arr_tv <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e))
                   "Subscript array type";
       check_array_bounds cx base_tv idx;
       res <- lift_sum (evaluate_subscript (get_tenv cx) arr_tv base_tv idx);
       case res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => place_expr_result_typed env tv result_vt | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  Cases_on `base_vt`
  >- (
    `vtype_annotation_ok (Type t) (expr_type e)` by
      metis_tac[type_place_expr_annotation_ok_stmt] >>
    gvs[vtype_annotation_ok_def, place_expr_result_typed_def] >>
    Cases_on `expr_type e` >> gvs[subscript_vtype_def, subscript_type_ok_def] >>
    qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
    simp[bind_def, lift_option_type_def, return_def, lift_sum_def] >>
    Cases_on `check_array_bounds cx base_tv idx st` >>
    rename1 `check_array_bounds cx base_tv idx st = (bounds_res,bounds_st)` >>
    `bounds_st = st` by metis_tac[check_array_bounds_state] >> gvs[] >>
    Cases_on `bounds_res` >> gvs[return_def, raise_def]
    >- (
      Cases_on `evaluate_subscript (get_tenv cx) tyv base_tv idx` >> gvs[return_def, raise_def]
      >- (
        rename1 `evaluate_subscript (get_tenv cx) tyv base_tv idx = INL sub_res` >>
        `subscript_type_ok (ArrayT t b) (expr_type e') t` by
          simp[subscript_type_ok_def] >>
        drule_all evaluate_subscript_typed_stmt >> strip_tac >>
        Cases_on `sub_res` >> gvs[return_def, bind_def]
        >- (
          `~is_HashMapRef x` by
            (drule_all evaluate_subscript_success_not_HashMapRef_stmt >> simp[]) >>
          strip_tac >>
          qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
          simp[bind_def, ignore_bind_def, return_def] >> strip_tac >>
          gvs[no_type_error_result_def, place_expr_result_typed_def]) >>
        strip_tac >> PairCases_on `y` >> gvs[] >>
        qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
        simp[bind_def, ignore_bind_def, return_def] >> strip_tac >> gvs[] >>
        Cases_on `read_storage_slot cx y0 y1 rtv bounds_st` >>
        rename1 `read_storage_slot cx y0 y1 rtv bounds_st = (read_res,read_st)` >>
        `read_st = bounds_st` by metis_tac[read_storage_slot_state] >> gvs[] >>
        Cases_on `read_res` >> gvs[return_def, raise_def, no_type_error_result_def]
        >- (`well_formed_type_value rtv` by metis_tac[evaluate_type_well_formed_type_value] >>
            `value_has_type rtv x` by metis_tac[read_storage_slot_success_type] >>
            gvs[place_expr_result_typed_def, toplevel_value_typed_def, is_HashMapRef_def]) >>
        drule read_storage_slot_error >> strip_tac >> simp[]) >>
      strip_tac >>
      qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
      simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
      `?idx_tyv. evaluate_type (get_tenv cx) (expr_type e') = SOME idx_tyv /\
                 value_has_type idx_tyv idx` by (
        qpat_x_assum `expr_result_typed env e' idx_tv` mp_tac >>
        simp[expr_result_typed_def, expr_runtime_typed_def] >> strip_tac >>
        Cases_on `idx_tv` >>
        gvs[get_Value_def, return_def, raise_def, toplevel_value_typed_def]) >>
      `subscript_type_ok (ArrayT t b) (expr_type e') t` by
        simp[subscript_type_ok_def] >>
      drule_all evaluate_subscript_error_not_TypeError_stmt >>
      strip_tac >> simp[no_type_error_result_def]) >>
    strip_tac >>
    qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
    simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
    drule_all check_array_bounds_error_not_TypeError_stmt >>
    strip_tac >> simp[no_type_error_result_def])
  >- (
    `vtype_annotation_ok (HashMapT t v) (expr_type e)` by
      metis_tac[type_place_expr_annotation_ok_stmt] >>
    Cases_on `result_vt` >>
    gvs[vtype_annotation_ok_def, place_expr_result_typed_def, subscript_vtype_def]
    >- (
      `?rtv. evaluate_type (get_tenv cx) t' = SOME rtv` by
        gvs[well_formed_type_def, IS_SOME_EXISTS] >>
      qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
      simp[bind_def, lift_option_type_def, return_def, lift_sum_def,
           evaluate_type_def, check_array_bounds_hashmap_stmt, evaluate_subscript_def] >>
      strip_tac >>
      Cases_on `read_storage_slot cx is_t (hashmap_slot slot (encode_hashmap_key (expr_type e') idx)) rtv st` >>
      rename1 `read_storage_slot cx is_t (hashmap_slot slot (encode_hashmap_key kt idx)) rtv st = (read_res,read_st)` >>
      `read_st = st` by metis_tac[read_storage_slot_state] >> gvs[] >>
      Cases_on `read_res` >> gvs[return_def, raise_def, no_type_error_result_def]
      >- (gvs[bind_def, ignore_bind_def, return_def, check_array_bounds_hashmap_stmt] >>
          `well_formed_type_value rtv` by metis_tac[evaluate_type_well_formed_type_value] >>
          `value_has_type rtv x` by metis_tac[read_storage_slot_success_type] >>
          gvs[place_expr_result_typed_def, toplevel_value_typed_def, is_HashMapRef_def]) >>
      gvs[bind_def, ignore_bind_def, return_def, check_array_bounds_hashmap_stmt] >>
      drule read_storage_slot_error >> strip_tac >> simp[]) >>
    qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
    simp[bind_def, ignore_bind_def, lift_option_type_def, return_def, lift_sum_def,
         evaluate_type_def, check_array_bounds_hashmap_stmt, evaluate_subscript_def] >>
    strip_tac >> gvs[return_def, no_type_error_result_def, place_expr_result_typed_def])
QED

Theorem expr_subscript_place_projection_branch_sound_stmt[local]:
  !cx env e e' v9 base_vt result_vt base_tv st1 res st'.
    state_well_typed st1 /\
    env_consistent env cx st1 /\
    context_well_typed cx /\
    accounts_well_typed st1.accounts /\
    functions_well_typed cx /\
    well_formed_type env.type_defs v9 /\
    well_typed_expr env e' /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME result_vt /\
    vtype_annotation_ok result_vt v9 /\
    place_expr_result_typed env base_tv base_vt /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e' st0 = (res0,st0') ==>
      (well_typed_expr env0 e' ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e' = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) ==>
    (case (INL base_tv,st1) of
       (INL tv1,s'') =>
         (case eval_expr cx e' s'' of
            (INL tv2,s'') =>
              (case get_Value tv2 s'' of
                 (INL v2,s'') =>
                   (let
                      tenv = get_tenv cx
                    in
                      do
                        arr_tv <- lift_option_type (evaluate_type tenv (expr_type e))
                          "Subscript array type";
                        check_array_bounds cx tv1 v2;
                        res <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
                        case res of
                          INL v => return v
                        | INR (is_transient,slot,tv) =>
                          do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
                      od) s''
               | (INR e,s'') => (INR e,s''))
          | (INR e,s'') => (INR e,s''))
     | (INR e,s'') => (INR e,s'')) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => place_expr_result_typed env tv result_vt | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_expr cx e'' st1` >>
  rename1 `eval_expr cx e'' st1 = (idx_res,st2)` >>
  qpat_x_assum `!env0 st0 res0 st0'. _ ==> _`
    (qspecl_then [`env`,`st1`,`idx_res`,`st2`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `well_typed_expr env e'' ==> _` mp_tac >>
  (impl_tac >- simp[]) >> strip_tac >>
  simp_tac(srw_ss())[] >>
  Cases_on `idx_res` >> gvs[]
  >- (
    Cases_on `get_Value x st2` >>
    rename1 `get_Value x st2 = (val_res,st3)` >>
    Cases_on `val_res` >> gvs[]
    >- (
      strip_tac >>
      drule get_Value_state >> strip_tac >> gvs[] >>
      qspecl_then [`cx`,`env`,`e'`,`e''`,`v9`,`base_vt`,`result_vt`,`base_tv`,`x`,`x'`,`st2`,`res`,`st'`]
        mp_tac expr_subscript_place_projection_tail_sound_stmt >>
      (impl_tac >- simp[]) >>
      simp[]) >>
    strip_tac >>
    drule get_Value_state >> strip_tac >> gvs[] >>
    qspecl_then [`base_vt`,`expr_type e''`,`result_vt`,`env`,`e''`,`x`,`st'`,`INR y`,`st'`]
      mp_tac subscript_vtype_index_get_Value_no_type_error >>
    simp[] >> strip_tac >> gvs[no_type_error_result_def]) >>
  strip_tac >> gvs[]
QED


Theorem expr_subscript_ordinary_tail_sound_stmt[local]:
  !cx env e e' v9 base_tv idx_tv idx st res st'.
    state_well_typed st /\
    env_consistent env cx st /\
    accounts_well_typed st.accounts /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    expr_result_typed env e base_tv /\
    expr_result_typed env e' idx_tv /\
    get_Value idx_tv st = (INL idx,st) /\
    (do
       arr_tv <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e))
                   "Subscript array type";
       check_array_bounds cx base_tv idx;
       sub_res <- lift_sum (evaluate_subscript (get_tenv cx) arr_tv base_tv idx);
       case sub_res of
         INL v => return v
       | INR (is_transient,slot,tv) =>
           do v <- read_storage_slot cx is_transient slot tv; return (Value v) od
     od st = (res,st')) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def, env_context_consistent_def] >>
  qpat_x_assum `expr_result_typed env e base_tv` mp_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def] >> strip_tac >>
  qpat_x_assum `expr_result_typed env e' idx_tv` mp_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def] >> strip_tac >>
  `~is_HashMapRef base_tv` by (
    Cases_on `base_tv` >>
    gvs[is_HashMapRef_def, toplevel_value_typed_def] >>
    Cases_on `expr_type e` >>
    gvs[subscript_type_ok_def, Once evaluate_type_def, AllCaseEqs()]) >>
  `value_has_type tv' idx` by (
    qpat_x_assum `get_Value idx_tv st = (INL idx,st)` mp_tac >>
    Cases_on `idx_tv` >>
    gvs[get_Value_def, return_def, raise_def, toplevel_value_typed_def] >>
    metis_tac[]) >>
  qpat_x_assum `do arr_tv <- lift_option_type _ _; _ od st = (res,st')` mp_tac >>
  simp[bind_def, lift_option_type_def, return_def, lift_sum_def] >>
  Cases_on `check_array_bounds cx base_tv idx st` >>
  rename1 `check_array_bounds cx base_tv idx st = (bounds_res,bounds_st)` >>
  `bounds_st = st` by metis_tac[check_array_bounds_state] >> gvs[] >>
  Cases_on `bounds_res` >> gvs[return_def, raise_def]
  >- (
    Cases_on `evaluate_subscript (get_tenv cx) tv base_tv idx` >> gvs[return_def, raise_def]
    >- (
      rename1 `evaluate_subscript (get_tenv cx) tv base_tv idx = INL sub_res` >>
      drule_all evaluate_subscript_typed_stmt >> strip_tac >>
      Cases_on `sub_res` >> gvs[return_def, bind_def]
      >- (
        `~is_HashMapRef x` by
          (drule_all evaluate_subscript_success_not_HashMapRef_stmt >> simp[]) >>
        strip_tac >>
        qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
        simp[bind_def, ignore_bind_def, return_def] >> strip_tac >>
        gvs[no_type_error_result_def, expr_result_typed_def, expr_runtime_typed_def, expr_type_def]) >>
      strip_tac >>
      simp[no_type_error_result_def, expr_result_typed_def, expr_runtime_typed_def] >>
      irule expr_subscript_storage_tail_sound_stmt >>
      qexistsl [`bounds_st`,`rtv`,`base_tv`,`idx`,`y`] >>
      simp[] >>
      `well_formed_type_value rtv` by metis_tac[evaluate_type_well_formed_type_value] >>
      simp[]) >>
    strip_tac >>
    qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
    simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
    drule_all evaluate_subscript_error_not_TypeError_stmt >>
    strip_tac >> simp[no_type_error_result_def]) >>
  strip_tac >>
  qpat_x_assum `do check_array_bounds cx base_tv idx; _ od bounds_st = (res,st')` mp_tac >>
  simp[bind_def, ignore_bind_def, return_def, raise_def] >> strip_tac >> gvs[] >>
  drule_all check_array_bounds_error_not_TypeError_stmt >>
  strip_tac >> simp[no_type_error_result_def]
QED

Theorem subscript_type_ok_index_is_int_stmt[local]:
  !base_ty idx_ty result_ty.
    subscript_type_ok base_ty idx_ty result_ty ==> is_int_type idx_ty
Proof
  Cases >> simp[subscript_type_ok_def]
QED

Theorem expr_subscript_index_get_Value_INR_no_type_error_stmt[local]:
  !env e e' v9 tv st y st'.
    expr_result_typed env e' tv /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    get_Value tv st = (INR y, st') ==>
    no_type_error_result (INR y)
Proof
  rpt strip_tac >>
  qspecl_then [`env`,`e'`,`tv`,`expr_type e'`,`st`,`y`,`st'`]
    mp_tac int_expr_get_Value_INR_no_type_error >>
  (impl_tac >- (
    simp[] >>
    drule subscript_type_ok_index_is_int_stmt >> simp[])) >>
  simp[]
QED

Theorem expr_subscript_ordinary_base_success_sound_stmt[local]:
  !cx env e e' v9 base_tv st st1 res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    well_typed_expr env e' /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    eval_expr cx e st = (INL base_tv,st1) /\
    state_well_typed st1 /\ env_consistent env cx st1 /\
    accounts_well_typed st1.accounts /\
    expr_result_typed env e base_tv /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      eval_expr cx e' st0 = (res0,st0') ==>
      (well_typed_expr env0 e' ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e' = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) /\
    eval_expr cx (Subscript v9 e e') st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  qpat_x_assum `eval_expr cx e st = (INL base_tv,st1)`
    (fn th => simp_tac(srw_ss())[th]) >>
  Cases_on `eval_expr cx e' st1` >>
  rename1 `eval_expr cx e' st1 = (idx_res,st2)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
    accounts_well_typed st0.accounts /\ functions_well_typed cx /\
    eval_expr cx e' st0 = (res0,st0') ==> _`
    (qspecl_then [`env`,`st1`,`idx_res`,`st2`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `idx_res`
  >- (
    simp_tac(srw_ss())[] >> strip_tac >>
    qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `case INL x of INL tv => expr_result_typed env e' tv | INR v1 => T` mp_tac >>
    simp_tac(srw_ss())[] >> strip_tac >>
    qpat_x_assum `(case get_Value x st2 of _ => _) = (res,st')` mp_tac >>
    Cases_on `get_Value x st2` >>
    rename1 `get_Value x st2 = (val_res,st3)` >>
    Cases_on `val_res`
    >- (
      simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
      rename1 `get_Value x st2 = (INL idx,st3)` >>
      drule get_Value_state >> strip_tac >> gvs[] >>
      qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`base_tv`,`x`,`idx`,`st2`,`res`,`st'`]
        mp_tac expr_subscript_ordinary_tail_sound_stmt >>
      (impl_tac >- simp[]) >>
      simp[]) >>
    simp_tac(srw_ss())[] >> strip_tac >> gvs[] >>
    rename1 `get_Value x st2 = (INR val_err,st3)` >>
    drule get_Value_state >> strip_tac >> gvs[] >>
    irule expr_subscript_index_get_Value_INR_no_type_error_stmt >>
    qexistsl [`e`,`e'`,`env`,`st2`,`st2`,`x`,`v9`] >>
    simp[])
  >- (
    simp_tac(srw_ss())[] >> strip_tac >>
    qpat_x_assum `well_typed_expr env e' ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >>
    gvs[])
QED

Theorem expr_subscript_ordinary_static_branch_sound_stmt[local]:
  !cx env e e' v9 st res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr (Subscript v9 e e')) /\
    well_typed_expr env e /\ well_typed_expr env e' /\
    well_formed_type env.type_defs v9 /\
    subscript_type_ok (expr_type e) (expr_type e') v9 /\
    eval_expr cx (Subscript v9 e e') st = (res,st') /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      eval_expr cx e st0 = (res0,st0') ==>
      (well_typed_expr env0 e ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) /\
    (!s'' tv1 t.
      eval_expr cx e s'' = (INL tv1,t) ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx /\
        call_evaluation_safe cx (int_calls_expr e') /\
        eval_expr cx e' st0 = (res0,st0') ==>
        (well_typed_expr env0 e' ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
        !vt.
          type_place_expr env0 e' = SOME vt ==>
          state_well_typed st0' /\ env_consistent env0 cx st0' /\
          accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
          case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
Proof
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_right]) >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
    accounts_well_typed st0.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    eval_expr cx e st0 = (res0,st0') ==> _`
    (qspecl_then [`env`,`st`,`base_res`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `base_res`
  >- (
    rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `!s'' tv1 t. eval_expr cx e s'' = (INL tv1,t) ==> _`
      (qspecl_then [`st`,`base_tv`,`st1`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `case INL base_tv of INL tv => expr_result_typed env e tv | INR v1 => T` mp_tac >>
    simp_tac(srw_ss())[] >> strip_tac >>
    qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`base_tv`,`st`,`st1`,`res`,`st'`]
      mp_tac expr_subscript_ordinary_base_success_sound_stmt >>
    disch_then irule >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt gen_tac >> strip_tac >>
    qpat_assum `!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e') /\
      eval_expr cx e' st0 = (res0,st0') ==> _` irule >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists `st0` >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (
    qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
    qpat_x_assum `eval_expr cx e st = (INR y,st1)`
      (fn th => simp_tac(srw_ss())[th]) >>
    strip_tac >>
    qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `INR y = res` (fn th => rewrite_tac[GSYM th]) >>
    qpat_x_assum `st1 = st'` (fn th => rewrite_tac[GSYM th]) >>
    rewrite_tac[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    simp_tac(srw_ss())[])
QED

Theorem expr_subscript_place_as_ordinary_branch_sound_stmt[local]:
  !cx env e e' v9 base_vt st res st'.
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr (Subscript v9 e e')) /\
    well_typed_expr env e' /\
    type_place_expr env e = SOME base_vt /\
    subscript_vtype base_vt (expr_type e') = SOME (Type v9) /\
    eval_expr cx (Subscript v9 e e') st = (res,st') /\
    (!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      eval_expr cx e st0 = (res0,st0') ==>
      (well_typed_expr env0 e ==>
       state_well_typed st0' /\ env_consistent env0 cx st0' /\
       accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
       case res0 of INL tv => expr_result_typed env0 e tv | INR v1 => T) /\
      !vt.
        type_place_expr env0 e = SOME vt ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) /\
    (!s'' tv1 t.
      eval_expr cx e s'' = (INL tv1,t) ==>
      !env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx /\
        call_evaluation_safe cx (int_calls_expr e') /\
        eval_expr cx e' st0 = (res0,st0') ==>
        (well_typed_expr env0 e' ==>
         state_well_typed st0' /\ env_consistent env0 cx st0' /\
         accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
         case res0 of INL tv => expr_result_typed env0 e' tv | INR v1 => T) /\
        !vt.
          type_place_expr env0 e' = SOME vt ==>
          state_well_typed st0' /\ env_consistent env0 cx st0' /\
          accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
          case res0 of INL tv => place_expr_result_typed env0 tv vt | INR v1 => T) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of INL tv => expr_result_typed env (Subscript v9 e e') tv | INR v1 => T
Proof
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_right]) >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
    accounts_well_typed st0.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    eval_expr cx e st0 = (res0,st0') ==> _`
    (qspecl_then [`env`,`st`,`base_res`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `base_res`
  >- (
    rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> state_well_typed st1 /\ _`
      (qspec_then `base_vt` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `case INL base_tv of INL tv => place_expr_result_typed env tv base_vt | INR v1 => T`
      mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
    `well_formed_type env.type_defs v9` by (
      `well_formed_vtype env.type_defs base_vt` by
        metis_tac[type_place_expr_well_formed_vtype_stmt] >>
      `well_formed_vtype env.type_defs (Type v9)` by
        metis_tac[subscript_vtype_well_formed_stmt] >>
      `vtype_annotation_ok (Type v9) v9` by simp[vtype_annotation_ok_def] >>
      metis_tac[vtype_annotation_ok_well_formed_type_stmt]) >>
    qpat_x_assum `!s'' tv1 t. eval_expr cx e s'' = (INL tv1,t) ==> _`
      (qspecl_then [`st`,`base_tv`,`st1`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`base_vt`,`Type v9`,`base_tv`,`st1`,`res`,`st'`]
      mp_tac expr_subscript_place_projection_branch_sound_stmt >>
    (impl_tac >- (
      rpt conj_tac
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- first_assum ACCEPT_TAC
      >- simp[vtype_annotation_ok_def]
      >- first_assum ACCEPT_TAC
      >> (rpt gen_tac >> strip_tac >>
          qpat_assum `!env0 st0 res0 st0'.
            env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
            accounts_well_typed st0.accounts /\ functions_well_typed cx /\
            call_evaluation_safe cx (int_calls_expr e') /\
            eval_expr cx e' st0 = (res0,st0') ==> _` irule >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          qexists `st0` >> rpt conj_tac >> first_assum ACCEPT_TAC))) >>
    strip_tac >>
    `state_well_typed st' /\ env_consistent env cx st' /\
     accounts_well_typed st'.accounts /\ no_type_error_result res /\
     (case res of INL tv => place_expr_result_typed env tv (Type v9) | INR v1 => T)` by (
      first_x_assum irule >>
      qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
      qpat_x_assum `eval_expr cx e st = (INL base_tv,st1)`
        (fn th => simp_tac(srw_ss())[th])) >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    Cases_on `res` >> simp[] >>
    qpat_x_assum `case INL x of INL tv => place_expr_result_typed env tv (Type v9) | INR v1 => T`
      mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
    irule place_expr_result_typed_expr_result_typed_stmt >>
    qexists `Type v9` >> simp[Once well_typed_expr_def, vtype_annotation_ok_def])
  >- (
    qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
    qpat_x_assum `eval_expr cx e st = (INR y,st1)`
      (fn th => simp_tac(srw_ss())[th]) >>
    strip_tac >>
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> state_well_typed st1 /\ _`
      (qspec_then `base_vt` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qpat_x_assum `INR y = res` (fn th => rewrite_tac[GSYM th]) >>
    qpat_x_assum `st1 = st'` (fn th => rewrite_tac[GSYM th]) >>
    rewrite_tac[] >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    simp_tac(srw_ss())[])
QED

Resume eval_all_type_sound_mutual[Expr_Subscript]:
  (* C2.1.1.13.4 splits the ordinary Subscript static alternatives at this
     boundary and discharges them through the two proved local adapters above. *)
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_left]) >>
  `call_evaluation_safe cx (int_calls_expr e')` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Subscript v9 e e'))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    metis_tac[call_evaluation_safe_append_right]) >>
  conj_tac
  >- (
    strip_tac >>
    qpat_x_assum `well_typed_expr env (Subscript v9 e e')` mp_tac >>
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
    strip_tac
    >- (qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`st`,`res`,`st'`]
          match_mp_tac expr_subscript_ordinary_static_branch_sound_stmt >>
        asm_rewrite_tac[])
    >- (qmatch_asmsub_rename_tac `type_place_expr env e = SOME base_vt` >>
        qspecl_then [`cx`,`env`,`e`,`e'`,`v9`,`base_vt`,`st`,`res`,`st'`]
          match_mp_tac expr_subscript_place_as_ordinary_branch_sound_stmt >>
        asm_rewrite_tac[]))
  >> gen_tac >> strip_tac >>
  qpat_x_assum `type_place_expr env (Subscript v9 e e') = SOME vt` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `eval_expr cx (Subscript v9 e e') st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (base_res,st1)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
    accounts_well_typed st0.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx (int_calls_expr e) /\
    eval_expr cx e st0 = (res0,st0') ==> _`
    (qspecl_then [`env`,`st`,`base_res`,`st1`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `base_res`
  >- (
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> state_well_typed st1 /\ _`
      (qspec_then `vt'` mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    strip_tac >>
    qpat_x_assum `case INL x of INL tv => place_expr_result_typed env tv vt' | INR v1 => T` mp_tac >>
    simp_tac(srw_ss())[] >> strip_tac >>
    `well_formed_type env.type_defs v8`
      by (
        drule_at Any vtype_annotation_ok_well_formed_type_stmt >>
        disch_then irule >>
        irule subscript_vtype_well_formed_stmt >>
        goal_assum $ drule_at Any >>
        irule type_place_expr_well_formed_vtype_stmt >>
        metis_tac[] ) >>
    qpat_x_assum `!s'' tv1 t. eval_expr cx e s'' = (INL tv1,t) ==> _`
      (qspecl_then [`st`,`x`,`st1`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    qspecl_then [`cx`,`env`,`e`,`e'`,`v8`,`vt'`,`vt`,`x`,`st1`,`res`,`st'`]
      mp_tac expr_subscript_place_projection_branch_sound_stmt >>
    (impl_tac >- (
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!env0 st0 res0 st0'.
        env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx /\
        call_evaluation_safe cx (int_calls_expr e') /\
        eval_expr cx e' st0 = (res0,st0') ==> _` irule >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexists `st0` >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    (disch_then irule >> first_assum ACCEPT_TAC))
  >- (
    qpat_x_assum `!vt. type_place_expr env e = SOME vt ==> state_well_typed st1 /\ _`
      (qspec_then `vt'` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    strip_tac >>
    qpat_x_assum `(case (INR y,st1) of _ => _) = (res,st')` mp_tac >>
    simp_tac(srw_ss())[] >> strip_tac >>
    pop_assum (fn th => rewrite_tac[GSYM th]) >>
    pop_assum (fn th => rewrite_tac[GSYM th]) >>
    rpt conj_tac >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >- first_assum ACCEPT_TAC
    >> simp[])
QED


(* ===== Attribute expression helpers and Resume block ===== *)

Theorem struct_has_type_lookup_type_stmt[local]:
  !ftypes fields id field_tv.
    struct_has_type ftypes fields /\ ALOOKUP ftypes id = SOME field_tv ==>
    ?field_v. ALOOKUP fields id = SOME field_v /\ value_has_type field_tv field_v
Proof
  Induct >> Cases_on `fields` >> simp[Once value_has_type_def] >>
  Cases >> Cases_on `h` >> simp[Once value_has_type_def] >>
  rw[] >> gvs[] >> Cases_on `id = q` >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem evaluate_attribute_value_has_type[local]:
  !sv id ftypes field_tv.
    value_has_type (StructTV ftypes) sv /\
    ALOOKUP ftypes id = SOME field_tv ==>
    ?field_v. evaluate_attribute sv id = INL field_v /\
              value_has_type field_tv field_v
Proof
  Cases >> simp[evaluate_attribute_def, value_has_type_def] >>
  rpt strip_tac >>
  drule_all struct_has_type_lookup_type_stmt >> strip_tac >>
  qexists_tac `field_v` >> simp[]
QED

Theorem expr_attribute_success_tail_sound_stmt[local]:
  !cx env e id ty base_tv st st1 res st'.
    state_well_typed st1 /\ env_consistent env cx st1 /\
    accounts_well_typed st1.accounts /\
    expr_result_typed env e base_tv /\
    attribute_type env.type_defs (expr_type e) id = SOME ty /\
    eval_expr cx e st = (INL base_tv,st1) /\
    eval_expr cx (Attribute ty e id) st = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    (case res of
     | INL tv => expr_result_typed env (Attribute ty e id) tv
     | INR _ => T)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_expr cx (Attribute ty e id) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
  asm_rewrite_tac[] >>
  qhdtm_x_assum `expr_result_typed` mp_tac >>
  simp[expr_result_typed_def, expr_runtime_typed_def] >>
  strip_tac >>
  Cases_on `expr_type e` >> gvs[attribute_type_def, evaluate_type_def, AllCaseEqs()] >>
  strip_tac >>
  `?sv. base_tv = Value sv /\
        value_has_type (StructTV (ZIP (MAP FST fields,tvs))) sv` by
    (Cases_on `base_tv` >> gvs[toplevel_value_typed_def]) >>
  gvs[get_Value_def, return_def, bind_def] >>
  `?field_tv. evaluate_type env.type_defs ty = SOME field_tv /\
              ALOOKUP (ZIP (MAP FST fields,tvs)) id = SOME field_tv` by (
    qspecl_then [`env.type_defs`,`StructT p`,`id`,`ty`,
                 `ZIP (MAP FST fields,tvs)`] mp_tac attribute_type_evaluates >>
    simp[attribute_type_def, evaluate_type_def]) >>
  drule_all evaluate_attribute_value_has_type >> strip_tac >>
  gvs[lift_sum_def, return_def, no_type_error_result_def,
      expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
      toplevel_value_typed_def]
QED

Resume eval_all_type_sound_mutual[Expr_Attribute]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_expr e)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Attribute ty e id))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (
    strip_tac >>
    rename1 `well_typed_expr env (Attribute ty e id)` >>
    qpat_x_assum `well_typed_expr env (Attribute ty e id)` mp_tac >>
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [well_typed_expr_def])) >>
    strip_tac >>
    Cases_on `eval_expr cx e st` >>
    rename1 `eval_expr cx e st = (base_res,st1)` >>
    qpat_x_assum `!env0 st0 res0 st0'.
      env_consistent env0 cx st0 /\ state_well_typed st0 /\ context_well_typed cx /\
      accounts_well_typed st0.accounts /\ functions_well_typed cx /\
      call_evaluation_safe cx (int_calls_expr e) /\
      eval_expr cx e st0 = (res0,st0') ==> _`
      (qspecl_then [`env`,`st`,`base_res`,`st1`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    Cases_on `base_res`
    >- (
      rename1 `eval_expr cx e st = (INL base_tv,st1)` >>
      qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `case INL base_tv of INL tv => expr_result_typed env e tv | INR v1 => T`
        mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
      qspecl_then [`cx`,`env`,`e`,`id`,`ty`,`base_tv`,`st`,`st1`,`res`,`st'`]
        match_mp_tac expr_attribute_success_tail_sound_stmt >>
      qpat_x_assum `attribute_type_ok env.type_defs (expr_type e) id ty` mp_tac >>
      simp[attribute_type_ok_def])
    >- (
      qpat_x_assum `eval_expr cx (Attribute ty e id) st = (res,st')` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def] >>
      qpat_x_assum `eval_expr cx e st = (INR y,st1)`
        (fn th => simp_tac(srw_ss())[th]) >>
      strip_tac >>
      qpat_x_assum `well_typed_expr env e ==> _` mp_tac >>
      (impl_tac >- simp[]) >> strip_tac >>
      qpat_x_assum `INR y = res` (assume_tac o GSYM) >>
      qpat_x_assum `st1 = st'` (assume_tac o GSYM) >>
      simp[])) >>
  gen_tac >> strip_tac >>
  gvs[Once well_typed_expr_def]
QED

(* ===== Builtin, type-builtin, and pop expression cases ===== *)

Theorem nested_return_value_case[local]:
  ((case (case INL x of INL v => return v | INR e => raise (Error e)) st of
      (INL v,s'') => (INL (Value v),s'')
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INL (Value x) /\ st' = st
Proof
  simp[return_def] >> metis_tac[]
QED

Theorem nested_raise_error_case[local]:
  ((case (case INR x of INL v => return v | INR e => raise (Error e)) st of
      (INL v,s'') => (INL (Value v),s'')
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INR (Error x) /\ st' = st
Proof
  simp[raise_def] >> metis_tac[]
QED

Theorem eval_exprs_failure_builtin_case[local]:
  ((case
      case (INR x,st) of
        (INL vs,s'') =>
          (case evaluate_builtin cx s''.accounts ty bt vs of
             INL v => return v
           | INR e => raise (Error e)) s''
      | (INR e,s'') => (INR e,s'')
    of
      (INL v,s'') => (INL (Value v),s'')
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INR x /\ st' = st
Proof
  simp[] >> metis_tac[]
QED

Theorem eval_exprs_failure_type_builtin_case[local]:
  ((case (INR x,st) of
      (INL vs,s'') =>
        (case
           (case evaluate_type_builtin cx tb target_ty vs of
              INL v => return v
            | INR e => raise (Error e)) s''
         of
           (INL v,s'') => (INL (Value v),s'')
         | (INR e,s'') => (INR e,s''))
    | (INR e,s'') => (INR e,s'')) = (res,st')) <=>
  res = INR x /\ st' = st
Proof
  simp[] >> metis_tac[]
QED


Theorem type_builtin_exprs_runtime_no_type_error_stmt_adapter[local]:
  env.type_defs = get_tenv cx /\
  type_builtin_result_ok env.type_defs tb result_ty target_ty (MAP expr_type es) /\
  well_typed_type_builtin_args tb target_ty (MAP expr_type es) /\
  well_formed_type env.type_defs result_ty /\
  exprs_runtime_typed env es vs /\
  context_well_typed cx ==>
  !msg. evaluate_type_builtin cx tb target_ty vs <> INR (TypeError msg)
Proof
  rw[exprs_runtime_typed_def] >>
  `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
    gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  `?result_tv. evaluate_type (get_tenv cx) result_ty = SOME result_tv` by
    gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  irule well_typed_type_builtin_no_type_error >>
  simp[] >>
  qexistsl_tac [`result_tv`, `result_ty`, `MAP expr_type es`, `tvs`] >>
  gvs[]
QED

Theorem type_builtin_exprs_runtime_success_type_stmt_adapter[local]:
  env.type_defs = get_tenv cx /\
  type_builtin_result_ok env.type_defs tb result_ty target_ty (MAP expr_type es) /\
  well_typed_type_builtin_args tb target_ty (MAP expr_type es) /\
  well_formed_type env.type_defs result_ty /\
  exprs_runtime_typed env es vs /\
  context_well_typed cx /\
  evaluate_type_builtin cx tb target_ty vs = INL v ==>
  expr_result_typed env (TypeBuiltin result_ty tb target_ty es) (Value v)
Proof
  rw[exprs_runtime_typed_def, expr_result_typed_def, expr_runtime_typed_def,
     expr_type_def, toplevel_value_typed_Value] >>
  `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
    gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP] >>
  `?result_tv. evaluate_type (get_tenv cx) result_ty = SOME result_tv` by
    gvs[well_formed_type_def, IS_SOME_EXISTS] >>
  qexists_tac `result_tv` >> simp[] >>
  irule well_typed_type_builtin_success_type >>
  qexistsl_tac [`cx`, `result_ty`, `target_ty`, `tb`, `MAP expr_type es`, `tvs`, `vs`] >>
  gvs[]
QED

Resume eval_all_type_sound_mutual[Expr_Builtin]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Builtin ty bt es))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (Builtin _ _ _) = SOME _` mp_tac >>
      simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (Builtin ty bt es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_def, env_context_consistent_def] >>
  `builtin_args_length_ok bt (LENGTH es)` by
    (drule well_typed_builtin_app_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (Builtin ty bt es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
                       type_check_def, assert_def] >>
  Cases_on `bt = Len`
  >- (`es <> []` by (
        Cases_on `es` >> simp[] >>
        qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type [])` mp_tac >>
        qpat_x_assum `bt = Len` (fn th => rewrite_tac[th]) >>
        simp[well_typed_builtin_app_def]) >>
      `call_evaluation_safe cx (int_calls_expr (HD es))` by
        metis_tac[call_evaluation_safe_int_calls_exprs_HD] >>
      qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
      qpat_assum `bt = Len` (fn th => rewrite_tac[th]) >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                         type_check_def, assert_def] >>
      Cases_on `eval_expr cx (HD es) st` >>
      rename1 `eval_expr cx (HD es) st = (arg_res,arg_st)` >>
      qpat_x_assum `!s'' x t. _ /\ bt = Len ==> _`
        (qspecl_then [`st`,`()`,`st`] mp_tac) >>
      (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
      qpat_x_assum `!env st res st'. _`
        (qspecl_then [`env`,`st`,`arg_res`,`arg_st`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      Cases_on `arg_res`
      >- (rename1 `eval_expr cx (HD es) st = (INL arg_tv,arg_st)` >>
          qpat_x_assum `well_typed_expr env (HD es) ==> _` mp_tac >>
          (impl_tac >- (qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type es)` mp_tac >>
                        Cases_on `es` >> simp[well_typed_builtin_app_def] >>
                        Cases_on `t` >> gvs[well_typed_expr_def])) >>
          simp_tac(srw_ss())[] >> strip_tac >>
          Cases_on `toplevel_array_length cx arg_tv arg_st` >>
          rename1 `toplevel_array_length cx arg_tv arg_st = (len_res,len_st)` >>
          Cases_on `len_res`
          >- (rename1 `toplevel_array_length cx arg_tv arg_st = (INL len,len_st)` >>
              drule toplevel_array_length_state >> strip_tac >> gvs[] >>
              strip_tac >> gvs[expr_result_typed_def, expr_runtime_typed_def,
                               expr_type_def, toplevel_value_typed_Value] >>
              conj_tac >- simp[no_type_error_result_def] >>
              qexists_tac `BaseTV (UintT 256)` >>
              conj_tac
              >- (qpat_x_assum `well_typed_builtin_app ty Len (MAP expr_type es)` mp_tac >>
                  Cases_on `es` >> simp[well_typed_builtin_app_def, evaluate_type_def] >>
                  Cases_on `t` >> gvs[]) >>
              irule Len_builtin_sound >>
              qexistsl_tac [`tv`,`arg_tv`,`expr_type (HD es)`,`cx`,`arg_st`,`arg_st`,`get_tenv cx`,`ty`] >>
              simp[] >>
              qpat_x_assum `well_typed_builtin_app ty Len (MAP expr_type es)` mp_tac >>
              Cases_on `es` >> simp[well_typed_builtin_app_def, evaluate_type_def] >>
              Cases_on `t` >> gvs[]) >>
          rename1 `toplevel_array_length cx arg_tv arg_st = (INR len_exn,len_st)` >>
          drule toplevel_array_length_state >> strip_tac >> gvs[] >>
          strip_tac >> gvs[no_type_error_result_def,
                           expr_result_typed_def, expr_runtime_typed_def] >>
          strip_tac >> spose_not_then assume_tac >> gvs[] >>
          `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
          `well_typed_builtin_app ty Len [expr_type (HD es)]` by
            (qpat_x_assum `well_typed_builtin_app ty Len (MAP expr_type es)` mp_tac >>
             Cases_on `es` >> simp[well_typed_builtin_app_def] >>
             Cases_on `t` >> gvs[]) >>
          drule_all Len_toplevel_array_length_no_type_error >> simp[]) >>
      qpat_x_assum `well_typed_expr env (HD es) ==> _` mp_tac >>
      (impl_tac >- (qpat_x_assum `well_typed_builtin_app ty bt (MAP expr_type es)` mp_tac >>
                    Cases_on `es` >> simp[well_typed_builtin_app_def] >>
                    Cases_on `t` >> gvs[well_typed_expr_def])) >>
      strip_tac >> strip_tac >> gvs[]) >>
  qpat_assum `bt <> Len` (fn th => rewrite_tac[th]) >>
  qpat_assum `builtin_args_length_ok bt (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                     type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!s'' x t. _ /\ bt <> Len ==> _`
    (qspecl_then [`st`,`()`,`st`] mp_tac) >>
  (impl_tac >- (simp[type_check_def, assert_def] >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `!env st res st'. _`
    (qspecl_then [`env`,`st`,`args_res`,`args_st`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `args_res`
  >- (
    rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
    qpat_x_assum `case INL vs of INL vs => exprs_runtime_typed env es vs | INR v1 => T`
      mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
    qpat_x_assum `exprs_runtime_typed env es vs` mp_tac >>
    rewrite_tac[exprs_runtime_typed_def] >> strip_tac >>
    `MAP (evaluate_type (get_tenv cx)) (MAP expr_type es) = MAP SOME tvs` by
      (gvs[LIST_REL_EL_EQN, LIST_EQ_REWRITE, EL_MAP]) >>
    `?ret_tv. evaluate_type (get_tenv cx) ty = SOME ret_tv` by
      (gvs[well_formed_type_def, IS_SOME_EXISTS]) >>
    Cases_on `evaluate_builtin cx args_st.accounts ty bt vs` >>
    rename1 `evaluate_builtin cx args_st.accounts ty bt vs = builtin_res` >>
    Cases_on `builtin_res` >>
    FIRST [
      rename1 `evaluate_builtin cx args_st.accounts ty bt vs = INL builtin_v` >>
      strip_tac >>
      gvs[nested_return_value_case, no_type_error_result_def] >>
      gvs[expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
          toplevel_value_typed_Value] >>
      mp_tac (Q.INST [`blt` |-> `bt`, `ts` |-> `MAP expr_type es`,
                       `acc` |-> `(args_st:evaluation_state).accounts`,
                       `tv` |-> `ret_tv`, `v` |-> `builtin_v`,
                       `cx` |-> `cx`, `tvs` |-> `tvs`, `vs` |-> `vs`,
                       `ty` |-> `ty`]
                well_typed_builtin_app_success_type) >>
      simp[],
      strip_tac >>
      gvs[nested_raise_error_case, no_type_error_result_def] >>
      strip_tac >> spose_not_then assume_tac >> gvs[] >>
      `!item. bt = Env item ==> item <> MsgGas` by
        (rpt strip_tac >> gvs[well_typed_builtin_app_def]) >>
      drule_all well_typed_builtin_app_no_type_error >>
      disch_then (qspec_then `msg` mp_tac) >> gvs[]]) >>
  strip_tac >> gvs[eval_exprs_failure_builtin_case, no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Expr_TypeBuiltin]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_exprs es)` by (
    qpat_assum `call_evaluation_safe cx
      (int_calls_expr (TypeBuiltin result_ty tb target_ty es))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  reverse conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `type_place_expr _ (TypeBuiltin _ _ _ _) = SOME _` mp_tac >>
      simp_tac(srw_ss())[Once well_typed_expr_def]) >>
  strip_tac >>
  qpat_x_assum `well_typed_expr env (TypeBuiltin result_ty tb target_ty es)` mp_tac >>
  simp_tac(srw_ss())[Once well_typed_expr_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_def, env_context_consistent_def] >>
  `type_builtin_args_length_ok tb (LENGTH es)` by
    (drule well_typed_type_builtin_args_length >> simp[]) >>
  qpat_x_assum `eval_expr cx (TypeBuiltin result_ty tb target_ty es) st = (res,st')` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def, raise_def,
                       type_check_def, assert_def] >>
  qpat_assum `type_builtin_args_length_ok tb (LENGTH es)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[bind_def, ignore_bind_def, return_def, raise_def,
                     type_check_def, assert_def] >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!s'' x t. type_check _ _ _ = _ ==> _`
    (qspecl_then [`st`,`()`,`st`] mp_tac) >>
  (impl_tac >- simp[type_check_def, assert_def]) >> strip_tac >>
  qpat_x_assum `!env st res st'. _`
    (qspecl_then [`env`,`st`,`args_res`,`args_st`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `args_res`
  >- (rename1 `eval_exprs cx es st = (INL vs,args_st)` >>
      qpat_x_assum `case INL vs of INL vs => exprs_runtime_typed env es vs | INR v1 => T`
        mp_tac >> simp_tac(srw_ss())[] >> strip_tac >>
      Cases_on `evaluate_type_builtin cx tb typ vs`
      >- (rename1 `evaluate_type_builtin cx tb typ vs = INL builtin_v` >>
          strip_tac >>
          gvs[lift_sum_def, return_def, no_type_error_result_def] >>
          irule type_builtin_exprs_runtime_success_type_stmt_adapter >>
          simp[] >>
          qexistsl_tac [`cx`,`vs`] >>
          simp[]) >>
      rename1 `evaluate_type_builtin cx tb typ vs = INR type_exn` >>
      strip_tac >>
      gvs[lift_sum_def, raise_def, no_type_error_result_def] >>
      strip_tac >> spose_not_then assume_tac >> gvs[] >>
      metis_tac[type_builtin_exprs_runtime_no_type_error_stmt_adapter]) >>
  strip_tac >> gvs[eval_exprs_failure_type_builtin_case, no_type_error_result_def]
QED


Resume eval_all_type_sound_mutual[Expr_Pop]:
  rpt gen_tac >> strip_tac >>
  `call_evaluation_safe cx (int_calls_target bt)` by (
    qpat_assum `call_evaluation_safe cx (int_calls_expr (Pop v11 bt))` mp_tac >>
    pure_rewrite_tac[int_calls_expr_def] >>
    strip_tac >> first_assum ACCEPT_TAC) >>
  (reverse conj_tac
   >- (gen_tac >> strip_tac >>
       gvs[Once well_typed_expr_def]) >>
   strip_tac >>
   drule well_typed_expr_Pop_dynamic_target_assignable >> strip_tac >>
      qpat_x_assum `eval_expr cx (Pop v11 bt) st = (res,st')` mp_tac >>
      simp_tac(srw_ss())[Once evaluate_def, bind_def] >>
      Cases_on `eval_base_target cx bt st` >>
      rename1 `eval_base_target cx bt st = (bt_res, st1)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `bt_res`
      >- (gvs[no_type_error_result_def] >>
          PairCases_on `x` >>
          gvs[] >>
          rename1 `type_place_target env bt = SOME (Type (ArrayT elem_ty (Dynamic n)))` >>
          strip_tac >>
          qpat_x_assum `do _ od st1 = (res,st')` mp_tac >>
          simp[bind_apply, bind_def, return_def, ignore_bind_apply] >>
          Cases_on `assign_target cx (BaseTargetV x0 x1) PopOp st1` >>
          rename1 `assign_target cx (BaseTargetV loc sbs) PopOp st1 = (assign_res, st2)` >>
          `runtime_consistent env cx st1` by simp[runtime_consistent_def] >>
          `target_runtime_typed env cx st1 (BaseTarget bt)
             (ArrayT elem_ty (Dynamic n)) (BaseTargetV loc sbs)` by (
            simp[target_runtime_typed_def, target_value_shape_def,
                 well_typed_atarget_def, well_typed_target_def] >>
            qexists_tac `loc_vt` >> simp[]) >>
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
            metis_tac[target_runtime_typed_imp_assignable_context] >>
          Cases_on `assign_res` >> simp[return_def, raise_def, lift_option_type_def]
          >- suspend "Expr_Pop_assign_inl" >>
          suspend "Expr_Pop_assign_inr") >>
      strip_tac >> gvs[no_type_error_result_def])
QED

Resume eval_all_type_sound_mutual[Expr_Pop_assign_inl]:
  `runtime_consistent env cx st2` by (
    drule_at(Pat`assign_target`) assign_target_preserves_runtime_consistent >>
    disch_then $ drule_at(Pat`target_runtime_typed`) >>
    simp[]) >>
  `?v. x = SOME v /\ value_has_type elem_tv v` by
    metis_tac[assign_target_pop_success_some_typed] >>
  strip_tac >> gvs[return_def, expr_result_typed_def, expr_runtime_typed_def,
                   toplevel_value_typed_def, runtime_consistent_def, expr_type_def]
QED

Resume eval_all_type_sound_mutual[Expr_Pop_assign_inr]:
  strip_tac >> gvs[] >>
  `runtime_consistent env cx st'` by
    metis_tac[assign_target_preserves_runtime_consistent_result] >>
  gvs[runtime_consistent_def] >>
  qspecl_then [`cx`, `BaseTargetV loc sbs`, `PopOp`, `st1`,
               `INR y`, `st'`, `env`, `BaseTarget bt`,
               `ArrayT elem_ty (Dynamic n)`] mp_tac assign_target_no_type_error >>
  simp[no_type_error_result_def] >>
  impl_tac >- simp[runtime_consistent_def] >>
  simp[]
QED


(* ===== Internal call helpers and Resume block ===== *)

Theorem defaults_env_empty_frame_consistent:
  !env_body cx st.
    env_context_consistent env_body cx /\
    env_immutables_consistent env_body cx st ==>
    env_consistent (defaults_env env_body) cx (st with scopes := [FEMPTY])
Proof
  rw[defaults_env_def, env_consistent_def, env_context_consistent_def,
     env_scopes_consistent_def, env_immutables_consistent_def,
     lookup_scopes_def] >>
  gvs[] >>
  metis_tac[]
QED

Theorem default_frame_eval_result[local]:
  !cx es st prev res st'.
    finally
      (do set_scopes [FEMPTY]; eval_exprs cx es od)
      (set_scopes prev) st = (res,st') ==>
    ?framed_st.
      eval_exprs cx es (st with scopes := [FEMPTY]) = (res,framed_st) /\
      st' = (framed_st with scopes := prev)
Proof
  rw[finally_def, bind_def, ignore_bind_def, set_scopes_def,
     return_def, raise_def] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  Cases_on `q` >>
  gvs[ignore_bind_def, set_scopes_def, return_def, raise_def]
QED

Theorem intcall_default_exprs_sound_from_generated_ih[local]:
  !cx src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
    xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd prev res sdfl
    env_body.
    (!s'' x t s3 ts0 t1 s4 tup0 t2 mut stup nr stup2 args sstup dflts
        sstup2 ret body s5 x5 t5 s6 vs0 t6 es0 cx0 s7 prev0 t7 s8 x8 t8.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s3 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s4 = (INL tup0,t2) /\
      mut = FST tup0 /\ stup = SND tup0 /\ (nr <=> FST stup) /\
      stup2 = SND stup /\ args = FST stup2 /\ sstup = SND stup2 /\
      dflts = FST sstup /\ sstup2 = SND sstup /\ ret = FST sstup2 /\
      body = SND sstup2 /\
      type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      es0 = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
      cx0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      set_scopes [FEMPTY] s8 = (INL x8,t8) ==>
      !env0 st0 res0 st0'.
        well_typed_exprs env0 es0 /\ env_consistent env0 cx0 st0 /\
        state_well_typed st0 /\ context_well_typed cx0 /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_exprs es0) /\
        eval_exprs cx0 es0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ env_consistent env0 cx0 st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL vs1 => exprs_runtime_typed env0 es0 vs1 | INR _ => T) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) /\
    type_check
      (LENGTH es <= LENGTH (FST (SND (SND tup))) /\
       LENGTH (FST (SND (SND tup))) <=
         LENGTH es + LENGTH (FST (SND (SND (SND tup)))))
      "IntCall args length" ih_len_s = (INL xlen,slen) /\
    eval_exprs cx es ih_args_s = (INL vs,sevl) /\
    needed_dflts =
      DROP (LENGTH (FST (SND (SND (SND tup)))) -
            (LENGTH (FST (SND (SND tup))) - LENGTH es))
           (FST (SND (SND (SND tup)))) /\
    cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
    get_scopes sevl = (INL prev,sevl) /\
    well_typed_exprs (defaults_env env_body) needed_dflts /\
    env_context_consistent env_body cxd /\
    env_immutables_consistent env_body cxd sevl /\
    state_well_typed sevl /\
    context_well_typed cxd /\
    accounts_well_typed sevl.accounts /\
    functions_well_typed cxd /\
    call_evaluation_safe cxd (int_calls_exprs needed_dflts) /\
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (res,sdfl) ==>
    no_type_error_result res /\
    (case res of
       INL dflt_vs =>
         state_well_typed sdfl /\
         env_immutables_consistent env_body cxd sdfl /\
         accounts_well_typed sdfl.accounts /\
         exprs_runtime_typed (defaults_env env_body) needed_dflts dflt_vs
     | INR _ => T)
Proof
  rpt strip_tac >>
  drule default_frame_eval_result >>
  strip_tac >>
  `type_check
     (LENGTH es <= LENGTH (FST (SND (SND tup))) /\
      LENGTH (FST (SND (SND tup))) - LENGTH es <=
        LENGTH (FST (SND (SND (SND tup)))))
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac >>
     simp[type_check_def, assert_def] >>
     IF_CASES_TAC >> simp[] >>
     decide_tac) >>
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
     `sevl with scopes := [FEMPTY]`] mp_tac) >>
  (impl_tac >- (
     simp[get_scopes_def, set_scopes_def, return_def])) >>
  disch_then drule >>
  disch_then (qspecl_then
    [`sevl with scopes := [FEMPTY]`, `res`, `framed_st`] mp_tac) >>
  qpat_x_assum
    `!s'' x t s3 ts0 t1 s4 tup0 t2 mut stup nr stup2 args sstup dflts
        sstup2 ret body s5 x5 t5 s6 vs0 t6 es0 cx0 s7 prev0 t7 s8 x8 t8. _`
    kall_tac >>
  `env_consistent (defaults_env env_body) cxd (sevl with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  `state_well_typed (sevl with scopes := [FEMPTY])` by
    (gvs[state_well_typed_def, scope_well_typed_def]) >>
  impl_tac >- (
    conj_tac >- simp[] >>
    conj_tac >- simp[] >>
    conj_tac >- simp[] >>
    conj_tac >- simp[] >>
    conj_tac >- simp[] >>
    simp[]) >>
  strip_tac >>
  Cases_on `res` >>
  gvs[get_scopes_def, return_def, env_consistent_def, defaults_env_def,
      env_immutables_consistent_def, state_well_typed_def] >>
  metis_tac[]
QED


Theorem state_well_typed_restore_scopes[local]:
  !st scopes_src.
    state_well_typed st /\ state_well_typed scopes_src ==>
    state_well_typed (st with scopes := scopes_src.scopes)
Proof
  rw[state_well_typed_def]
QED


Theorem env_consistent_restore_intcall_default_frame[local]:
  !env env_body cx src_id_opt fn base_st framed_st.
    env_consistent env cx base_st /\
    env_consistent (defaults_env env_body)
      (cx with stk updated_by CONS (src_id_opt,fn)) framed_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    env_consistent env cx (framed_st with scopes := base_st.scopes)
Proof
  rw[env_consistent_def]
  >- (qpat_x_assum `env_scopes_consistent env cx base_st` mp_tac >>
      simp[env_scopes_consistent_def] >> metis_tac[]) >>
  gvs[env_immutables_consistent_def, defaults_env_def,
      get_tenv_stk_irrelevant, get_module_code_stk_irrelevant] >>
  metis_tac[]
QED

Theorem intcall_default_exprs_frame_sound_from_generated_ih[local]:
  !cx env src_id_opt fn es ih_check_s ih_mod_s ih_fun_s ih_len_s ih_args_s
    xrec srec ts smod tup sfun xlen slen vs sevl needed_dflts cxd prev res sdfl
    env_body.
    (!s'' x t s3 ts0 t1 s4 tup0 t2 mut stup nr stup2 args sstup dflts
        sstup2 ret body s5 x5 t5 s6 vs0 t6 es0 cx0 s7 prev0 t7 s8 x8 t8.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s'' = (INL x,t) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s3 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s4 = (INL tup0,t2) /\
      mut = FST tup0 /\ stup = SND tup0 /\ (nr <=> FST stup) /\
      stup2 = SND stup /\ args = FST stup2 /\ sstup = SND stup2 /\
      dflts = FST sstup /\ sstup2 = SND sstup /\ ret = FST sstup2 /\
      body = SND sstup2 /\
      type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      es0 = DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts /\
      cx0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      set_scopes [FEMPTY] s8 = (INL x8,t8) ==>
      !env0 st0 res0 st0'.
        well_typed_exprs env0 es0 /\ env_consistent env0 cx0 st0 /\
        state_well_typed st0 /\ context_well_typed cx0 /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_exprs es0) /\
        eval_exprs cx0 es0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ env_consistent env0 cx0 st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL vs1 => exprs_runtime_typed env0 es0 vs1 | INR _ => T) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" ih_check_s = (INL xrec,srec) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" ih_mod_s =
      (INL ts,smod) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" ih_fun_s = (INL tup,sfun) /\
    type_check
      (LENGTH es <= LENGTH (FST (SND (SND tup))) /\
       LENGTH (FST (SND (SND tup))) <=
         LENGTH es + LENGTH (FST (SND (SND (SND tup)))))
      "IntCall args length" ih_len_s = (INL xlen,slen) /\
    eval_exprs cx es ih_args_s = (INL vs,sevl) /\
    needed_dflts =
      DROP (LENGTH (FST (SND (SND (SND tup)))) -
            (LENGTH (FST (SND (SND tup))) - LENGTH es))
           (FST (SND (SND (SND tup)))) /\
    cxd = cx with stk updated_by CONS (src_id_opt,fn) /\
    get_scopes sevl = (INL prev,sevl) /\
    well_typed_exprs (defaults_env env_body) needed_dflts /\
    env_context_consistent env_body cxd /\
    env_immutables_consistent env_body cxd sevl /\
    env_consistent env cx sevl /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    state_well_typed sevl /\
    context_well_typed cxd /\
    accounts_well_typed sevl.accounts /\
    functions_well_typed cxd /\
    call_evaluation_safe cxd (int_calls_exprs needed_dflts) /\
    finally
      (do
         set_scopes [FEMPTY];
         eval_exprs cxd needed_dflts
       od)
      (set_scopes prev) sevl = (res,sdfl) ==>
    state_well_typed sdfl /\
    env_consistent env cx sdfl /\
    accounts_well_typed sdfl.accounts /\
    no_type_error_result res /\
    (case res of
       INL dflt_vs =>
         env_immutables_consistent env_body cxd sdfl /\
         exprs_runtime_typed (defaults_env env_body) needed_dflts dflt_vs
     | INR _ => T)
Proof
  rpt strip_tac >>
  drule default_frame_eval_result >>
  strip_tac >>
  `type_check
     (LENGTH es <= LENGTH (FST (SND (SND tup))) /\
      LENGTH (FST (SND (SND tup))) - LENGTH es <=
        LENGTH (FST (SND (SND (SND tup)))))
     "IntCall args length" ih_len_s = (INL xlen,slen)` by
    (qpat_x_assum `type_check _ "IntCall args length" ih_len_s = _` mp_tac >>
     simp[type_check_def, assert_def] >>
     IF_CASES_TAC >> simp[] >>
     decide_tac) >>
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
     `sevl with scopes := [FEMPTY]`] mp_tac) >>
  (impl_tac >- simp[get_scopes_def, set_scopes_def, return_def]) >>
  disch_then drule >>
  disch_then (qspecl_then
    [`sevl with scopes := [FEMPTY]`, `res`, `framed_st`] mp_tac) >>
  qpat_x_assum
    `!s'' x t s3 ts0 t1 s4 tup0 t2 mut stup nr stup2 args sstup dflts
        sstup2 ret body s5 x5 t5 s6 vs0 t6 es0 cx0 s7 prev0 t7 s8 x8 t8. _`
    kall_tac >>
  `env_consistent (defaults_env env_body) cxd (sevl with scopes := [FEMPTY])` by
    (irule defaults_env_empty_frame_consistent >> simp[]) >>
  `state_well_typed (sevl with scopes := [FEMPTY])` by
    (gvs[state_well_typed_def, scope_well_typed_def]) >>
  impl_tac >- simp[] >>
  strip_tac >>
  gvs[get_scopes_def, return_def] >>
  `state_well_typed (framed_st with scopes := sevl.scopes)` by
    (irule state_well_typed_restore_scopes >> simp[]) >>
  `env_consistent env cx (framed_st with scopes := sevl.scopes)` by
    (qspecl_then [`env`, `env_body`, `cx`, `env_body.current_src`, `fn`,
                  `sevl`, `framed_st`] mp_tac
       env_consistent_restore_intcall_default_frame >>
     simp[]) >>
  simp[] >>
  Cases_on `res` >>
  gvs[env_consistent_def, defaults_env_def, env_immutables_consistent_def,
      get_tenv_stk_irrelevant, get_module_code_stk_irrelevant] >>
  metis_tac[]
QED

Theorem intcall_safe_cast_NoneTV_NoneV[local]:
  safe_cast NoneTV NoneV = SOME NoneV
Proof
  simp[Once safe_cast_def]
QED

Theorem intcall_finally_try_handle_success_rv[local]:
  !fn_m cleanup pushed_st rv st_final.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INL rv,st_final) ==>
    (rv = NoneV /\ (?st_bdy. fn_m pushed_st = (INL (),st_bdy))) \/
    (?v st_bdy. rv = v /\ fn_m pushed_st = (INR (ReturnException v),st_bdy))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def])
  >- (Cases_on `y` >>
      gvs[handle_function_def, return_def, raise_def] >>
      Cases_on `fn_m pushed_st` >> Cases_on `q` >>
      gvs[return_def, raise_def, ignore_bind_apply])
QED

Theorem intcall_finally_try_handle_success_cleanup[local]:
  !fn_m cleanup pushed_st rv st_final.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INL rv,st_final) ==>
    (rv = NoneV /\
     (?st_bdy. fn_m pushed_st = (INL (),st_bdy) /\
               cleanup st_bdy = (INL (),st_final))) \/
    (?v st_bdy. rv = v /\ fn_m pushed_st = (INR (ReturnException v),st_bdy) /\
                cleanup st_bdy = (INL (),st_final))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def])
  >- (Cases_on `y` >>
      gvs[handle_function_def, return_def, raise_def] >>
      Cases_on `fn_m pushed_st` >> Cases_on `q` >>
      gvs[return_def, raise_def, ignore_bind_apply])
QED


Theorem intcall_finally_try_handle_inr_body_cleanup_cases[local]:
  !fn_m cleanup pushed_st y fin_st.
    finally (try (do fn_m; return NoneV od) handle_function)
      cleanup pushed_st = (INR y,fin_st) ==>
    (?st_bdy.
       fn_m pushed_st = (INL (),st_bdy) /\
       cleanup st_bdy = (INR y,fin_st)) \/
    (?body_exn st_bdy cleanup_res.
       fn_m pushed_st = (INR body_exn,st_bdy) /\
       cleanup st_bdy = (cleanup_res,fin_st))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[finally_def] >>
  Cases_on `try (do fn_m; return NoneV od) handle_function pushed_st` >>
  rename1 `_ = (try_res,try_st)` >>
  Cases_on `try_res` >> gvs[ignore_bind_apply] >>
  Cases_on `cleanup try_st` >> rename1 `_ = (cl_res,cl_st)` >>
  Cases_on `cl_res` >> gvs[return_def, raise_def] >>
  gvs[try_def] >>
  Cases_on `(do fn_m; return NoneV od) pushed_st` >>
  rename1 `_ = (inner_res,inner_st)` >>
  Cases_on `inner_res` >> gvs[return_def]
  >- (gvs[ignore_bind_apply, return_def] >>
      Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
      Cases_on `fn_res` >> gvs[return_def, raise_def]) >>
  Cases_on `fn_m pushed_st` >> rename1 `_ = (fn_res,fn_st)` >>
  Cases_on `fn_res` >>
  gvs[bind_apply, bind_def, return_def, raise_def, ignore_bind_apply] >>
  rename1 `handle_function body_exn _ = _` >>
  Cases_on `body_exn` >>
  gvs[handle_function_def, bind_apply, bind_def, return_def, raise_def,
      ignore_bind_apply]
QED
Theorem lift_safe_cast_value_has_type_no_type_error[local]:
  !tv v msg st res st'.
    value_has_type tv v /\
    lift_option_type (safe_cast tv v) msg st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  `safe_cast tv v = SOME v` by (irule safe_cast_well_typed >> simp[]) >>
  gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]
QED

Theorem env_consistent_restore_intcall_body_frame[local]:
  !env env_body cx src_id_opt fn base_st framed_st.
    env_consistent env cx base_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) framed_st /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    env_consistent env cx (framed_st with scopes := base_st.scopes)
Proof
  rw[env_consistent_def]
  >- (qpat_x_assum `env_scopes_consistent env cx base_st` mp_tac >>
      simp[env_scopes_consistent_def] >> metis_tac[]) >>
  gvs[env_immutables_consistent_def, get_tenv_stk_irrelevant,
      get_module_code_stk_irrelevant] >>
  metis_tac[]
QED

Theorem env_consistent_same_scopes_immutables[local]:
  !env cx st st'.
    env_consistent env cx st /\
    st'.scopes = st.scopes /\
    st'.immutables = st.immutables ==>
    env_consistent env cx st'
Proof
  rw[env_consistent_def, env_scopes_consistent_def,
     env_immutables_consistent_def] >> metis_tac[]
QED

Theorem intcall_cleanup_frame_restore_sound[local]:
  !env env_body cx src_id_opt fn args_st st_bdy fin_st.
    env_consistent env cx args_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st_bdy /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    state_well_typed args_st /\
    state_well_typed st_bdy /\
    accounts_well_typed st_bdy.accounts /\
    fin_st.scopes = args_st.scopes /\
    fin_st.immutables = st_bdy.immutables /\
    fin_st.accounts = st_bdy.accounts ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt strip_tac >>
  `state_well_typed fin_st` by gvs[state_well_typed_def] >>
  `env_consistent env cx (st_bdy with scopes := args_st.scopes)` by
    (qspecl_then [`env`, `env_body`, `cx`, `src_id_opt`, `fn`,
                  `args_st`, `st_bdy`] mp_tac
       env_consistent_restore_intcall_body_frame >> simp[]) >>
  `env_consistent env cx fin_st` by
    (qspecl_then [`env`, `cx`, `st_bdy with scopes := args_st.scopes`,
                  `fin_st`] mp_tac env_consistent_same_scopes_immutables >>
     simp[]) >>
  simp[]
QED

Theorem intcall_cleanup_after_body_preserves_caller_frame[local]:
  !env env_body cx src_id_opt fn args_st st_bdy cleanup_res fin_st nr is_view.
    env_consistent env cx args_st /\
    env_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) st_bdy /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    state_well_typed args_st /\
    state_well_typed st_bdy /\
    accounts_well_typed st_bdy.accounts /\
    (do pop_function args_st.scopes;
        if nr /\ ~is_view then
          case cx.nonreentrant_slot of
          | NONE => return ()
          | SOME slot => release_nonreentrant_lock cx.txn.target slot
        else return ()
     od) st_bdy = (cleanup_res,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt strip_tac >>
  drule intcall_cleanup_after_pop_preserves_frame >>
  simp[] >> strip_tac >>
  qspecl_then [`env`, `env_body`, `cx`, `src_id_opt`, `fn`,
                `args_st`, `st_bdy`, `fin_st`] mp_tac
    intcall_cleanup_frame_restore_sound >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED


Theorem intcall_default_finally_inr_preserves_frame[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
    accounts_well_typed (lock_st with scopes := [call_env]).accounts /\
    functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  drule intcall_finally_try_handle_inr_body_cleanup_cases >>
  strip_tac
  >- (
    first_x_assum (qspecl_then [`env_body`, `NoneT`, `env_after`,
                                 `lock_st with scopes := [call_env]`,
                                 `INL ()`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    drule type_stmts_env_preserved_static >> strip_tac >>
    qspecl_then [`env`, `env_after`, `cx`, `env_body.current_src`, `fn`,
                  `args_st`, `st_bdy`, `INR y`, `fin_st`, `nr`,
                  `fm = View \/ fm = Pure`] irule
      intcall_cleanup_after_body_preserves_caller_frame >>
    qexistsl [`args_st`, `env_after`, `env_body`, `fm`, `fn`, `nr`,
              `st_bdy`, `y`] >>
    gvs[]) >>
  first_x_assum (qspecl_then [`env_body`, `NoneT`, `env_after`,
                               `lock_st with scopes := [call_env]`,
                               `INR body_exn`, `st_bdy`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
  strip_tac >> gvs[] >>
  qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                `args_st`, `st_bdy`, `cleanup_res`, `fin_st`, `nr`,
                `fm = View \/ fm = Pure`] irule
    intcall_cleanup_after_body_preserves_caller_frame >>
  qexistsl [`args_st`, `cleanup_res`, `env_body`, `env_exn`, `fm`, `fn`,
            `nr`, `st_bdy`] >>
  gvs[env_extends_def]
QED

Theorem intcall_default_finally_inr_preserves_frame_from_caller_ctx[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed cx /\
    accounts_well_typed lock_st.accounts /\
    functions_well_typed cx /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_finally_inr_preserves_frame >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     (impl_tac >-
       (simp[context_well_typed_stk_irrelevant,
             functions_well_typed_stk_irrelevant] >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp[]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) /\
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed cx /\
    accounts_well_typed lock_st.accounts /\
    functions_well_typed cx /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_finally_inr_preserves_frame_from_caller_ctx >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     (impl_tac >-
       rw[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant]) >>
     simp[]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame_live[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    type_stmts env_body NoneT body = SOME env_after /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) /\
    state_well_typed (lock_st with scopes := [call_env]) /\
    context_well_typed cx /\
    accounts_well_typed lock_st.accounts /\
    functions_well_typed cx /\
    env_body.type_defs = get_tenv cx /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_success_post_push_outer_inr_frame >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame_apply[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) ==>
    type_stmts env_body NoneT body = SOME env_after ==>
    env_consistent env cx args_st ==>
    state_well_typed args_st ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) ==>
    state_well_typed (lock_st with scopes := [call_env]) ==>
    context_well_typed cx ==>
    accounts_well_typed lock_st.accounts ==>
    functions_well_typed cx ==>
    env_body.type_defs = get_tenv cx ==>
    env_body.bare_globals = env.bare_globals ==>
    env_body.bare_global_assignable = env.bare_global_assignable ==>
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> ntac 14 strip_tac >>
  qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                `y`, `fin_st`] mp_tac
    intcall_default_success_post_push_outer_inr_frame_live >>
  impl_tac >-
    (simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant] >>
     rpt strip_tac >>
     qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
       (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
     simp[context_well_typed_stk_irrelevant,
          functions_well_typed_stk_irrelevant]) >>
  simp[]
QED

Theorem intcall_default_success_post_push_outer_inr_frame_ret[local]:
  !cx env env_body args_st lock_st call_env fn fm nr body env_after ret y fin_st.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) ==>
    type_stmts env_body ret body = SOME env_after ==>
    (ret = NoneT \/ stmts_no_fallthrough body) ==>
    env_consistent env cx args_st ==>
    state_well_typed args_st ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn))
      (lock_st with scopes := [call_env]) ==>
    state_well_typed (lock_st with scopes := [call_env]) ==>
    context_well_typed cx ==>
    accounts_well_typed lock_st.accounts ==>
    functions_well_typed cx ==>
    env_body.type_defs = get_tenv cx ==>
    env_body.bare_globals = env.bare_globals ==>
    env_body.bare_global_assignable = env.bare_global_assignable ==>
    env_body.toplevel_vtypes = env.toplevel_vtypes ==>
    finally
      (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
               return NoneV od) handle_function)
      (do pop_function args_st.scopes;
          if nr /\ ~(fm = View \/ fm = Pure) then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od)
      (lock_st with scopes := [call_env]) = (INR y,fin_st) ==>
    state_well_typed fin_st /\ env_consistent env cx fin_st /\
    accounts_well_typed fin_st.accounts
Proof
  rpt gen_tac >> ntac 14 strip_tac >>
  gvs[]
  >- (
    qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                  `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                  `y`, `fin_st`] mp_tac
      intcall_default_success_post_push_outer_inr_frame_apply >>
    impl_tac >- first_assum ACCEPT_TAC >>
    rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                      simp[context_well_typed_stk_irrelevant,
                           functions_well_typed_stk_irrelevant])) >>
    simp[]) >>
  strip_tac >>
  drule intcall_finally_try_handle_inr_body_cleanup_cases >>
  strip_tac
  >- (
    drule (cj 2 no_fallthrough_eval_no_success) >>
    disch_then (qspecl_then [`cx with stk updated_by CONS (env_body.current_src,fn)`,
                             `lock_st with scopes := [call_env]`, `st_bdy`] mp_tac) >>
    simp[]) >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env_body`, `ret`, `env_after`,
                  `lock_st with scopes := [call_env]`,
                  `INR body_exn`, `st_bdy`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
  strip_tac >> gvs[] >>
  qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                `args_st`, `st_bdy`, `cleanup_res`, `fin_st`, `nr`,
                `fm = View \/ fm = Pure`] irule
    intcall_cleanup_after_body_preserves_caller_frame >>
  qexistsl [`args_st`, `cleanup_res`, `env_body`, `env_exn`, `fm`, `fn`,
            `nr`, `st_bdy`] >>
  gvs[env_extends_def]
QED

Theorem intcall_post_push_tail_no_type_error[local]:
  !cxf body pushed_st prev nr is_view cx rtv ret env_body env_after res st'.
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    (!res_body st_body.
       eval_stmts cxf body pushed_st = (res_body,st_body) ==>
       no_type_error_result res_body /\
       (case res_body of
        | INL _ => T
        | INR exn => return_exception_typed env_body ret exn)) /\
    (do
       rv <- finally
         (try (do eval_stmts cxf body; return NoneV od) handle_function)
         (do pop_function prev;
             if nr /\ ~is_view then
               case cx.nonreentrant_slot of
               | NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) pushed_st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  gvs[bind_apply] >>
  Cases_on
    `finally (try (do eval_stmts cxf body'; return NoneV od) handle_function)
       (do pop_function prev;
           if nr /\ ~is_view then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ()
        od) pushed_st` >>
  rename1 `_ = (fin_res,fin_st)` >>
  Cases_on `fin_res` >> gvs[]
  >- (
    rename1 `finally _ _ pushed_st = (INL rv,st_final)` >>
    `!v st_bdy. eval_stmts cxf body' pushed_st = (INR (ReturnException v),st_bdy) ==>
                value_has_type NoneTV v` by (
      rpt strip_tac >>
      qpat_x_assum `!res_body st_body. eval_stmts cxf body' pushed_st = (res_body,st_body) ==> _`
        (qspecl_then [`INR (ReturnException v)`, `st_bdy`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (fn th => assume_tac (CONJUNCT2 th)) >>
      gvs[return_exception_typed_def, value_runtime_typed_def]) >>
    drule intcall_finally_try_handle_success_rv >>
    strip_tac >>
    `value_has_type NoneTV rv` by gvs[] >>
    Cases_on `lift_option_type (safe_cast NoneTV rv) "IntCall cast ret" st_final` >>
    rename1 `_ = (cast_res,cast_st)` >>
    `no_type_error_result cast_res` by
      metis_tac[lift_safe_cast_value_has_type_no_type_error] >>
    Cases_on `cast_res` >> gvs[return_def, no_type_error_result_def]) >>
  gvs[finally_def, ignore_bind_def, bind_def, return_def, raise_def,
      prod_CASE_rator, sum_CASE_rator] >>
  gvs[AllCaseEqs(), no_type_error_result_def] >>
  Cases_on `eval_stmts cxf body' pushed_st` >>
  Cases_on `q` >>
  TRY (drule (cj 2 no_fallthrough_eval_no_success) >>
       disch_then (qspecl_then [`cxf`, `pushed_st`, `r`] mp_tac) >>
       simp[] >> NO_TAC) >>
  TRY (rename1 `eval_stmts cxf body' pushed_st = (INR y,_)` >>
       `y <> BreakException /\ y <> ContinueException` by
         metis_tac[stmts_no_control_escape_eval_stmts_no_loop_control] >>
       Cases_on `y`) >>
  gvs[try_def, handle_function_def, pop_function_def, set_scopes_def,
      release_nonreentrant_lock_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `nr /\ ~is_view` >>
  gvs[release_nonreentrant_lock_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[release_nonreentrant_lock_def, get_transient_storage_def, update_transient_def,
      bind_def, return_def, raise_def, no_type_error_result_def, AllCaseEqs()] >>
  `value_has_type rtv v` by
    gvs[return_exception_typed_def, value_runtime_typed_def] >>
  `safe_cast rtv v = SOME v` by
    (irule safe_cast_well_typed >> simp[]) >>
  gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]
QED

Theorem intcall_pushed_body_tail_no_type_error_from_body_ih[local]:
  (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body0 = SOME env2 /\
      env_consistent env1 cxf st0 /\ state_well_typed st0 /\
      context_well_typed cxf /\ accounts_well_typed st0.accounts /\
      functions_well_typed cxf /\ eval_stmts cxf body0 st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 cxf st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\ env_consistent env_exn cxf st0' /\
            return_exception_typed env_exn ret_ty1 exn) /\
  evaluate_type env_body.type_defs ret = SOME rtv /\
  type_stmts env_body ret body0 = SOME env_after /\
  (ret = NoneT \/ stmts_no_fallthrough body0) /\
  stmts_no_control_escape body0 /\
  env_consistent env_body cxf pushed_st /\ state_well_typed pushed_st /\
  context_well_typed cxf /\ accounts_well_typed pushed_st.accounts /\
  functions_well_typed cxf /\
  (do
     rv <- finally
       (try (do eval_stmts cxf body0; return NoneV od) handle_function)
       (do pop_function prev;
           if nr /\ ~is_view then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ()
        od);
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
   od) pushed_st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule intcall_post_push_tail_no_type_error >>
  qexistsl_tac [`body0`, `cx`, `cxf`, `env_after`, `env_body`, `is_view`,
                `nr`, `prev`, `pushed_st`, `ret`, `rtv`, `st'`] >>
  simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env_body`, `ret`, `env_after`, `pushed_st`,
                  `res_body`, `st_body`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `res_body` >> gvs[] >>
  metis_tac[env_extends_return_exception_typed]
QED


Theorem intcall_current_src_pushed_body_tail_no_type_error[local]:
  !cx env_body fn body ret rtv env_after pushed_st prev nr is_view res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn) /\
  evaluate_type env_body.type_defs ret = SOME rtv /\
  type_stmts env_body ret body = SOME env_after /\
  (ret = NoneT \/ stmts_no_fallthrough body) /\
  stmts_no_control_escape body /\
  env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn)) pushed_st /\
  state_well_typed pushed_st /\ context_well_typed cx /\
  accounts_well_typed pushed_st.accounts /\ functions_well_typed cx /\
  (do
     rv <- finally
       (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                return NoneV od) handle_function)
       (do pop_function prev;
           if nr /\ ~is_view then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ()
        od);
     crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
     return (Value crv)
   od) pushed_st = (res,st') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  irule intcall_pushed_body_tail_no_type_error_from_body_ih >>
  qexistsl_tac [`body'`, `cx`, `cx with stk updated_by CONS (env_body.current_src,fn)`,
                `env_after`, `env_body`, `is_view`, `nr`, `prev`,
                `pushed_st`, `ret`, `rtv`, `st'`] >>
  simp[context_well_typed_stk_irrelevant,
       functions_well_typed_stk_irrelevant] >>
  rpt strip_tac >>
  qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
    (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
  simp[context_well_typed_stk_irrelevant,
       functions_well_typed_stk_irrelevant]
QED

Theorem intcall_current_src_pushed_body_tail_no_type_error_irule[local]:
  !cx env_body fn body ret rtv env_after pushed_st prev nr is_view res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
        INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn) ==>
    evaluate_type env_body.type_defs ret = SOME rtv ==>
    type_stmts env_body ret body = SOME env_after ==>
    (ret = NoneT \/ stmts_no_fallthrough body) ==>
    stmts_no_control_escape body ==>
    env_consistent env_body (cx with stk updated_by CONS (env_body.current_src,fn)) pushed_st ==>
    state_well_typed pushed_st ==>
    context_well_typed cx ==>
    accounts_well_typed pushed_st.accounts ==>
    functions_well_typed cx ==>
    (do
       rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function)
         (do pop_function prev;
             if nr /\ ~is_view then
               case cx.nonreentrant_slot of
               | NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) pushed_st = (res,st') ==>
    no_type_error_result res
Proof
  rpt gen_tac >> disch_tac >>
  rpt (disch_tac ORELSE gen_tac) >>
  qspecl_then [`cx`, `env_body`, `fn`, `body'`, `ret`, `rtv`,
                `env_after`, `pushed_st`, `prev`, `nr`, `is_view`,
                `res`, `st'`] mp_tac
    intcall_current_src_pushed_body_tail_no_type_error >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  simp[]
QED
Theorem intcall_default_success_post_push_no_type_error[local]:
  !cx env env_body args_st dflt_st lock_st call_env fn fm nr ret body env_after rtv res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
         INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (INL (),lock_st) /\
    (do
       rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function)
         (do pop_function args_st.scopes;
             if nr /\ ~(fm = View \/ fm = Pure) then
               case cx.nonreentrant_slot of
               | NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) (lock_st with scopes := [call_env]) = (res,st') ==>
    no_type_error_result res
Proof
  rpt gen_tac >> strip_tac >>
  drule_all intcall_live_pushed_body_preconditions >>
  strip_tac >>
  qspecl_then [`cx`, `env_body`, `fn`, `body'`, `ret`, `rtv`,
                `env_after`, `lock_st with scopes := [call_env]`,
                `args_st.scopes`, `nr`, `fm = View \/ fm = Pure`, `res`, `st'`]
    mp_tac intcall_current_src_pushed_body_tail_no_type_error_irule >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >- (first_assum ACCEPT_TAC ORELSE simp[])) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >>
  first_x_assum irule >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Theorem intcall_safe_cast_expr_result_typed[local]:
  !env loc src_id_opt fn es extra ret_ty ret_tv rv crv.
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret_ty /\
    evaluate_type env.type_defs ret_ty = SOME ret_tv /\
    value_has_type ret_tv rv /\
    safe_cast ret_tv rv = SOME crv ==>
    expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) (Value crv)
Proof
  rpt strip_tac >>
  `value_has_type ret_tv crv` by
    (drule_all safe_cast_preserves_well_typed >> simp[]) >>
  simp[expr_result_typed_def, expr_runtime_typed_def,
       toplevel_value_typed_def] >>
  metis_tac[well_typed_expr_not_hashmap_place]
QED

Theorem intcall_default_success_post_push_sound[local]:
  !cx env loc src_id_opt es extra env_body args_st dflt_st lock_st call_env fn fm nr ret body env_after rtv res st'.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
       call_evaluation_safe
         (cx with stk updated_by CONS (env_body.current_src,fn))
         (int_calls_stmts body) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret /\
    evaluate_type env_body.type_defs ret = SOME rtv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts body) /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (INL (),lock_st) /\
    (do
       rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body;
                  return NoneV od) handle_function)
         (do pop_function args_st.scopes;
             if nr /\ ~(fm = View \/ fm = Pure) then
               case cx.nonreentrant_slot of
               | NONE => return ()
               | SOME slot => release_nonreentrant_lock cx.txn.target slot
             else return ()
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
     od) (lock_st with scopes := [call_env]) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  drule_all intcall_live_pushed_body_preconditions >>
  strip_tac >>
  `no_type_error_result res` by (
    irule intcall_default_success_post_push_no_type_error >>
    qexistsl_tac [`args_st`, `body'`, `call_env`, `cx`, `dflt_st`, `env`,
                  `env_after`, `env_body`, `fm`, `fn`, `lock_st`, `nr`,
                  `ret`, `rtv`, `st'`] >>
    simp[] >>
    rpt strip_tac >>
    qhdtm_assum `bool$!`
      (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  gvs[bind_apply] >>
  Cases_on
    `finally
       (try
          do
            eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body';
            return NoneV
          od handle_function)
       do
         pop_function args_st.scopes;
         if nr /\ ~(fm = View \/ fm = Pure) then
           (case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot)
         else return ()
       od (lock_st with scopes := [call_env])` >>
  rename1 `_ = (fin_res,fin_st)` >>
  Cases_on `fin_res` >> gvs[]
  >- (
    rename1 `finally _ _ _ = (INL rv,fin_st)` >>
    drule intcall_finally_try_handle_success_cleanup >>
    disch_then strip_assume_tac >>
    gvs[] >~ [`eval_stmts _ _ _ = (INL (),_)`] >- (
      qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env_body`, `NoneT`, `env_after`,
                      `lock_st with scopes := [call_env]`, `INL ()`, `st_bdy`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
      strip_tac >>
      qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
      qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                    `st_bdy`, `INL ()`, `fin_st`] mp_tac
        intcall_cleanup_after_pop_preserves_frame >>
      simp[] >> strip_tac >> strip_tac >>
      `env_after.type_defs = get_tenv cx /\
       env_after.bare_globals = env.bare_globals /\
       env_after.bare_global_assignable = env.bare_global_assignable /\
       env_after.toplevel_vtypes = env.toplevel_vtypes` by
        (drule type_stmts_env_preserved_static >> simp[]) >>
      `state_well_typed fin_st /\ env_consistent env cx fin_st /\
       accounts_well_typed fin_st.accounts` by (
        qspecl_then [`env`, `env_after`, `cx`, `env_body.current_src`, `fn`,
                      `args_st`, `st_bdy`, `fin_st`] mp_tac
          intcall_cleanup_frame_restore_sound >>
        (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
        strip_tac >> simp[]) >>
      gvs[intcall_safe_cast_NoneTV_NoneV, lift_option_type_def,
          return_def, raise_def, expr_result_typed_def, expr_runtime_typed_def,
          toplevel_value_typed_def, evaluate_type_def]) >>
    qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
      (qspecl_then [`env_body`, `NoneT`, `env_after`,
                    `lock_st with scopes := [call_env]`,
                    `INR (ReturnException rv)`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
    qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                  `st_bdy`, `INL ()`, `fin_st`] mp_tac
      intcall_cleanup_after_pop_preserves_frame >>
    simp[] >> strip_tac >> strip_tac >>
    gvs[] >>
    `env_exn.type_defs = get_tenv cx /\
     env_exn.bare_globals = env.bare_globals /\
     env_exn.bare_global_assignable = env.bare_global_assignable /\
     env_exn.toplevel_vtypes = env.toplevel_vtypes` by
      (gvs[env_extends_def]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by (
      qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                    `args_st`, `st_bdy`, `fin_st`] mp_tac
        intcall_cleanup_frame_restore_sound >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
      strip_tac >> simp[]) >>
    `rv = NoneV` by
      gvs[return_exception_typed_def, value_runtime_typed_def, evaluate_type_def] >>
    gvs[intcall_safe_cast_NoneTV_NoneV, lift_option_type_def,
        return_def, raise_def, expr_result_typed_def, expr_runtime_typed_def,
        toplevel_value_typed_def, evaluate_type_def])
  >- (
    `(!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body' = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body' st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
      case res0 of
      | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn)` by (
      rpt strip_tac >>
      qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by
      (qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                    `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                    `expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)`,
                    `y`, `fin_st`] mp_tac
         intcall_default_success_post_push_outer_inr_frame_ret >>
       impl_tac >- first_assum ACCEPT_TAC >>
       rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                         simp[context_well_typed_stk_irrelevant,
                              functions_well_typed_stk_irrelevant])) >>
       simp[]) >>
    gvs[] ) >>
  all_tac >~ [`finally _ _ _ = (INL _,_)`] >- (
    drule intcall_finally_try_handle_success_cleanup >>
    disch_then strip_assume_tac >> gvs[]
    >- (
      drule (cj 2 no_fallthrough_eval_no_success) >>
      disch_then (qspecl_then [`cx with stk updated_by CONS (env_body.current_src,fn)`,
                               `lock_st with scopes := [call_env]`, `st_bdy`] mp_tac) >>
      simp[]) >>
    qpat_x_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
      (qspecl_then [`env_body`, `expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)`, `env_after`,
                    `lock_st with scopes := [call_env]`,
                    `INR (ReturnException v)`, `st_bdy`] mp_tac) >>
    simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant] >>
    strip_tac >>
    qpat_x_assum `do pop_function args_st.scopes; _ od st_bdy = (INL (),fin_st)` mp_tac >>
    qspecl_then [`cx`, `nr`, `fm = View \/ fm = Pure`, `args_st.scopes`,
                  `st_bdy`, `INL ()`, `fin_st`] mp_tac
      intcall_cleanup_after_pop_preserves_frame >>
    simp[] >> strip_tac >> strip_tac >>
    gvs[] >>
    `env_exn.type_defs = get_tenv cx /\
     env_exn.bare_globals = env.bare_globals /\
     env_exn.bare_global_assignable = env.bare_global_assignable /\
     env_exn.toplevel_vtypes = env.toplevel_vtypes` by
      (gvs[env_extends_def]) >>
    `state_well_typed fin_st /\ env_consistent env cx fin_st /\
     accounts_well_typed fin_st.accounts` by (
      qspecl_then [`env`, `env_exn`, `cx`, `env_body.current_src`, `fn`,
                    `args_st`, `st_bdy`, `fin_st`] mp_tac
        intcall_cleanup_frame_restore_sound >>
      (impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[]))) >>
      strip_tac >> simp[]) >>
    `value_has_type rtv v` by
      gvs[return_exception_typed_def, value_runtime_typed_def] >>
    `safe_cast rtv v = SOME v` by
      (irule safe_cast_well_typed >> simp[]) >>
    gvs[lift_option_type_def, return_def, raise_def] >>
    `env.type_defs = get_tenv cx` by
      gvs[env_consistent_def, env_context_consistent_def] >>
    irule intcall_safe_cast_expr_result_typed >>
    simp[] >>
    qexists `v` >> simp[]) >>
  all_tac >~ [`finally _ _ _ = (INR _,_)`] >- (
    `(!env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 body' = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) body' st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
      case res0 of
      | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn)` by (
      rpt strip_tac >>
      qpat_assum `!env1 ret_ty1 env2 st0 res0 st0'. _`
        (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
      simp[context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]) >>
    qspecl_then [`cx`, `env`, `env_body`, `args_st`, `lock_st`,
                  `call_env`, `fn`, `fm`, `nr`, `body'`, `env_after`,
                  `expr_type (Call loc (IntCall (src_id_opt,fn)) es extra)`,
                  `y`, `fin_st`] mp_tac
      intcall_default_success_post_push_outer_inr_frame_ret >>
    impl_tac >- first_assum ACCEPT_TAC >>
    rpt (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                      simp[context_well_typed_stk_irrelevant,
                           functions_well_typed_stk_irrelevant])) >>
    simp[])
QED


Theorem intcall_lock_no_type_error_result[local]:
  !cx nr is_view st res st'.
    (nr ==> cx.nonreentrant_slot <> NONE) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) st = (res,st') ==>
    no_type_error_result res
Proof
  rpt strip_tac >>
  Cases_on `nr` >> gvs[return_def, raise_def, no_type_error_result_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[raise_def, no_type_error_result_def, acquire_nonreentrant_lock_def,
      get_transient_storage_def, update_transient_def, bind_def, ignore_bind_def,
      return_def, raise_def] >>
  Cases_on `lookup_storage (n2w x) (lookup_transient_storage cx.txn.target st.tStorage) = 1w` >>
  gvs[raise_def, return_def, update_transient_def, no_type_error_result_def] >>
  Cases_on `is_view` >>
  gvs[raise_def, return_def, update_transient_def, no_type_error_result_def]
QED

Theorem intcall_lock_attempt_sound_frame[local]:
  !env cx nr is_view dflt_st lock_res lock_st.
    env_consistent env cx dflt_st /\ state_well_typed dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    (nr ==> cx.nonreentrant_slot <> NONE) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ()) dflt_st = (lock_res,lock_st) ==>
    state_well_typed lock_st /\ accounts_well_typed lock_st.accounts /\
    no_type_error_result lock_res /\
    (case lock_res of INL _ => T | INR _ => env_consistent env cx lock_st)
Proof
  rpt strip_tac >>
  `no_type_error_result lock_res` by
    (irule intcall_lock_no_type_error_result >> goal_assum drule >> simp[]) >>
  Cases_on `lock_res`
  >- (Cases_on `x` >>
      drule intcall_lock_state_preserves_frame >>
      strip_tac >>
      gvs[state_well_typed_def]) >>
  gvs[no_type_error_result_def] >>
  Cases_on `nr` >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >>
  gvs[raise_def, acquire_nonreentrant_lock_def, get_transient_storage_def,
      update_transient_def, bind_def, ignore_bind_def, return_def,
      no_type_error_result_def] >>
  Cases_on `lookup_storage (n2w x) (lookup_transient_storage cx.txn.target dflt_st.tStorage) = 1w` >>
  gvs[raise_def, return_def, update_transient_def, state_well_typed_def] >>
  Cases_on `is_view` >>
  gvs[raise_def, return_def, update_transient_def, state_well_typed_def]
QED


Theorem lift_option_type_INL_SOME[local]:
  !opt msg st v st'.
    lift_option_type opt msg st = (INL v,st') ==> opt = SOME v
Proof
  Cases_on `opt` >> rw[lift_option_type_def, return_def, raise_def]
QED


Theorem env_consistent_type_defs_get_tenv[local]:
  !env cx st. env_consistent env cx st ==> env.type_defs = get_tenv cx
Proof
  simp[env_consistent_def, env_context_consistent_def]
QED



Theorem intcall_generated_body_ih_live_consumer_premise[local]:
  !cx src_id_opt fn es r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body dflt_vs dflt_st ret_tv.
    env_body.current_src = src_id_opt /\
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
        | INL v => env_consistent env2 cx0 st0'
        | INR exn => ?env_exn.
            env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
            return_exception_typed env_exn ret_ty1 exn) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (INL dflt_vs,dflt_st) ==>
    (!call_env' bind_st' ret_st' lock_st' cxf' pushed_st'.
       lift_option_type (bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs))
         "IntCall bind_arguments" dflt_st = (INL call_env',bind_st') /\
       lift_option_type (evaluate_type (get_tenv cx) ret)
         "IntCall eval ret" bind_st' = (INL ret_tv,ret_st') /\
       (if nr then
          case cx.nonreentrant_slot of
          | NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
        else return ()) ret_st' = (INL (),lock_st') /\
       push_function (env_body.current_src,fn) call_env' cx lock_st' =
         (INL cxf',pushed_st') ==>
       !env1 ret_ty1 env2 st0 res0 st0'.
         type_stmts env1 ret_ty1 fn_body = SOME env2 /\
         env_consistent env1 cxf' st0 /\ state_well_typed st0 /\
         context_well_typed cxf' /\ accounts_well_typed st0.accounts /\
         functions_well_typed cxf' /\
         call_evaluation_safe cxf' (int_calls_stmts fn_body) /\
         eval_stmts cxf' fn_body st0 = (res0,st0') ==>
         state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
         no_type_error_result res0 /\
         case res0 of
         | INL v => env_consistent env2 cxf' st0'
         | INR exn => ?env_exn.
             env_extends env1 env_exn /\ env_consistent env_exn cxf' st0' /\
             return_exception_typed env_exn ret_ty1 exn)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12. _` mp_tac >>
  disch_then (qspecl_then [`r`, `()`, `r`, `r`, `ts`, `r`, `r`,
                           `(fm,nr,args,dflts,ret,fn_body)`, `r`,
                           `fm`, `(nr,args,dflts,ret,fn_body)`, `nr`,
                           `(args,dflts,ret,fn_body)`, `args`,
                           `(dflts,ret,fn_body)`, `dflts`, `(ret,fn_body)`,
                           `ret`, `fn_body`, `r`, `tc_ok`, `r`, `r`,
                           `actual_vs`, `args_st`,
                           `DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts`,
                           `cx with stk updated_by CONS (src_id_opt,fn)`,
                           `args_st`, `dflt_vs`, `args_st`, `get_tenv cx`,
                           `args_st`, `call_env'`, `dflt_st`, `dflt_st`,
                           `args_st.scopes`, `bind_st'`, `bind_st'`, `ret_tv`,
                           `ret_st'`, `fm = View \/ fm = Pure`, `ret_st'`,
                           `()`, `lock_st'`, `lock_st'`, `cxf'`,
                           `pushed_st'`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (qpat_x_assum `type_check _ "IntCall args length" r = _` mp_tac >>
      simp[type_check_def, assert_def] >> IF_CASES_TAC >> gvs[] >> decide_tac) ORELSE
     gvs[get_scopes_def, set_scopes_def, return_def])) >>
  disch_then (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE gvs[])) >>
  simp[]
QED

Theorem intcall_defaults_result_package_from_generated_ih_general[local]:
  !cx env src_id_opt fn es r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_res dflt_st.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 es0 cx0
        s7 prev0 t7 s8 x8 t8.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      es0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cx0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      set_scopes [FEMPTY] s8 = (INL x8,t8) ==>
      !env0 st0 res0 st0'.
        well_typed_exprs env0 es0 /\ env_consistent env0 cx0 st0 /\
        state_well_typed st0 /\ context_well_typed cx0 /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_exprs es0) /\
        eval_exprs cx0 es0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ env_consistent env0 cx0 st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL vs => exprs_runtime_typed env0 es0 vs | INR _ => T) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    context_well_typed cx /\ accounts_well_typed args_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe (cx with stk updated_by CONS (src_id_opt,fn))
      (int_calls_exprs
        (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
    exprs_runtime_typed env es actual_vs /\
    MAP expr_type es = TAKE (LENGTH es) (MAP SND args) /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (dflt_res,dflt_st) ==>
    no_type_error_result dflt_res /\
    case dflt_res of
    | INL dflt_vs =>
        state_well_typed dflt_st /\
        env_immutables_consistent env_body
          (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
        accounts_well_typed dflt_st.accounts /\
        exprs_runtime_typed (defaults_env env_body)
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) dflt_vs /\
        ?call_env.
          bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
          scope_well_typed call_env /\
          env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  imp_res_tac lift_option_type_INL_SOME >>
  qpat_x_assum `!id typ. MEM (id,typ) args ==> _`
    (mk_asm "args_forward") >>
  qpat_x_assum `!n ty. FLOOKUP _.var_types n = SOME ty ==> _`
    (mk_asm "args_var_types") >>
  qpat_x_assum `!n b. FLOOKUP _.var_assignable n = SOME b ==> _`
    (mk_asm "args_var_assignable") >>
  `LENGTH es <= LENGTH args /\ LENGTH args <= LENGTH es + LENGTH dflts` by
    (qpat_x_assum `type_check _ "IntCall args length" r = _` mp_tac >>
     simp[type_check_def, assert_def] >>
     IF_CASES_TAC >> gvs[] >> decide_tac) >>
  `type_check (LENGTH es <= LENGTH args /\ LENGTH args <= LENGTH es + LENGTH dflts)
     "IntCall args length" r = (INL (),r)` by
    simp[type_check_def, assert_def] >>
  qspecl_then [`cx`, `src_id_opt`, `fn`, `es`,
               `r`, `r`, `r`, `r`, `r`,
               `()`, `r`, `ts`, `r`, `(fm,nr,args,dflts,ret,fn_body)`, `r`,
               `tc_ok`, `r`, `actual_vs`, `args_st`,
               `DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts`,
               `cx with stk updated_by CONS (src_id_opt,fn)`,
               `args_st.scopes`, `dflt_res`, `dflt_st`, `env_body`]
    mp_tac intcall_default_exprs_sound_from_generated_ih >>
  (impl_tac >- (
    conj_tac >- (first_assum ACCEPT_TAC) >>
    conj_tac >- (first_assum ACCEPT_TAC) >>
    conj_tac >- (first_assum ACCEPT_TAC) >>
    conj_tac >- (first_assum ACCEPT_TAC) >>
    conj_tac >- (
      qpat_assum `type_check (LENGTH es <= LENGTH args /\ LENGTH args <= LENGTH es + LENGTH dflts) "IntCall args length" r = (INL (),r)` mp_tac >>
      simp[type_check_def, assert_def] >> decide_tac) >>
    conj_tac >- (first_assum ACCEPT_TAC) >>
    conj_tac >- simp[] >>
    conj_tac >- simp[] >>
    conj_tac >- simp[get_scopes_def, return_def] >>
    conj_tac >- (irule well_typed_exprs_DROP >> first_assum ACCEPT_TAC) >>
    qspecl_then [`env`, `env_body`, `cx`, `args_st`,
                 `src_id_opt`, `fn`] mp_tac
      intcall_default_env_side_conditions >>
    (impl_tac >- simp[
      context_well_typed_stk_irrelevant,
      functions_well_typed_stk_irrelevant]) >>
    strip_tac >>
    rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     simp[get_scopes_def, set_scopes_def, return_def, lift_option_type_def,
          context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant]))) >>
  disch_then strip_assume_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Cases_on `dflt_res` >- (
    qpat_x_assum `case INL x of _ => _ | _ => _` mp_tac >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
    drule env_consistent_type_defs_get_tenv >> strip_tac >>
    `LENGTH args - LENGTH es <= LENGTH dflts` by
      (qpat_x_assum `type_check _ "IntCall args length" r = _` mp_tac >>
       simp[type_check_def, assert_def] >>
       IF_CASES_TAC >> gvs[] >> decide_tac) >>
    `LENGTH es <= LENGTH args` by
      (qpat_x_assum `type_check _ "IntCall args length" r = _` mp_tac >>
       simp[type_check_def, assert_def] >>
       IF_CASES_TAC >> gvs[] >> decide_tac) >>
    qspecl_then [`cx`, `env`, `env_body`, `args`, `dflts`, `es`,
                 `actual_vs`, `x`,
                 `DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts`,
                 `dflt_st`] mp_tac
      intcall_bind_arguments_from_runtime_typed >>
    (impl_tac >- (
      rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE
       asm "args_forward" ACCEPT_TAC ORELSE
       asm "args_var_types" ACCEPT_TAC ORELSE
       asm "args_var_assignable" ACCEPT_TAC ORELSE
       (asm "args_var_assignable" mp_tac >> simp[]) ORELSE
       simp[]))) >>
    strip_tac >>
    conj_tac >- (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `env_immutables_consistent env_body _ dflt_st` ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `exprs_runtime_typed (defaults_env env_body) _ x` ACCEPT_TAC) >>
    qexists_tac `call_env` >>
    conj_tac >- (qpat_assum `bind_arguments _ _ _ = SOME call_env` ACCEPT_TAC) >>
    conj_tac >- (qpat_assum `scope_well_typed call_env` ACCEPT_TAC) >>
    qpat_assum `env_scopes_consistent env_body cx _` ACCEPT_TAC) >>
  simp[NoAsms]
QED

Theorem intcall_defaults_result_frame_package_from_generated_ih_general[local]:
  !cx env src_id_opt fn es r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_res dflt_st.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 es0 cx0
        s7 prev0 t7 s8 x8 t8.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      es0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cx0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      set_scopes [FEMPTY] s8 = (INL x8,t8) ==>
      !env0 st0 res0 st0'.
        well_typed_exprs env0 es0 /\ env_consistent env0 cx0 st0 /\
        state_well_typed st0 /\ context_well_typed cx0 /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_exprs es0) /\
        eval_exprs cx0 es0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ env_consistent env0 cx0 st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL vs => exprs_runtime_typed env0 es0 vs | INR _ => T) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    context_well_typed cx /\ accounts_well_typed args_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe (cx with stk updated_by CONS (src_id_opt,fn))
      (int_calls_exprs
        (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
    exprs_runtime_typed env es actual_vs /\
    MAP expr_type es = TAKE (LENGTH es) (MAP SND args) /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (dflt_res,dflt_st) ==>
    state_well_typed dflt_st /\
    env_consistent env cx dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    no_type_error_result dflt_res /\
    case dflt_res of
    | INL dflt_vs =>
        exprs_runtime_typed (defaults_env env_body)
          (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts) dflt_vs /\
        ?call_env.
          bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
          scope_well_typed call_env /\
          env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
          env_immutables_consistent env_body
            (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `LENGTH es <= LENGTH args /\ LENGTH args <= LENGTH dflts + LENGTH es` by
    (qpat_x_assum `type_check _ "IntCall args length" r = _` mp_tac >>
     simp[type_check_def, assert_def] >>
     IF_CASES_TAC >> gvs[] >> decide_tac) >>
  `type_check (LENGTH es <= LENGTH args /\ LENGTH args <= LENGTH dflts + LENGTH es)
     "IntCall args length" r = (INL (),r)` by
    simp[type_check_def, assert_def] >>
  qspecl_then [`cx`, `env`, `src_id_opt`, `fn`, `es`,
               `r`, `r`, `r`, `r`, `r`,
               `()`, `r`, `ts`, `r`, `(fm,nr,args,dflts,ret,fn_body)`, `r`,
               `tc_ok`, `r`, `actual_vs`, `args_st`,
               `DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts`,
               `cx with stk updated_by CONS (src_id_opt,fn)`,
               `args_st.scopes`, `dflt_res`, `dflt_st`, `env_body`]
    mp_tac intcall_default_exprs_frame_sound_from_generated_ih >>
  impl_tac >- (
    qspecl_then [`env`, `env_body`, `cx`, `args_st`,
                 `src_id_opt`, `fn`] mp_tac
      intcall_default_env_side_conditions >>
    impl_tac >- simp[] >>
    strip_tac >>
    rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     (irule well_typed_exprs_DROP >> first_assum ACCEPT_TAC) ORELSE
     simp[get_scopes_def, set_scopes_def, return_def, lift_option_type_def,
          type_check_def, assert_def,
          context_well_typed_stk_irrelevant, functions_well_typed_stk_irrelevant])) >>
  strip_tac >>
  qspecl_then [`cx`, `env`, `src_id_opt`, `fn`, `es`, `r`, `ts`, `tc_ok`,
               `actual_vs`, `args_st`, `fm`, `nr`, `args`, `dflts`, `ret`,
               `fn_body`, `env_body`, `ret_tv`, `env_after`, `dflt_res`, `dflt_st`]
    mp_tac intcall_defaults_result_package_from_generated_ih_general >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  rpt conj_tac >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >-
    first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  Cases_on `dflt_res` >- (
    qpat_x_assum `case INL x of _ => _ | _ => _` mp_tac >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
    qpat_x_assum `case INL x of _ => _ | _ => _` mp_tac >>
    pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `call_env` >> simp[]) >>
  simp[sumTheory.sum_case_def]
QED

Theorem intcall_generated_body_post_push_ih[local]:
  !cx src_id_opt fn es r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv dflt_vs dflt_st
     call_env lock_st.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
          INL v => env_consistent env2 cx0 st0'
        | INR exn =>
            ?env_exn.
              env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
              return_exception_typed env_exn ret_ty1 exn) /\
    env_body.current_src = src_id_opt /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (INL dflt_vs,dflt_st) /\
    bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (INL (),lock_st) ==>
    !env1 ret_ty1 env2 st0 res0 st0'.
      type_stmts env1 ret_ty1 fn_body = SOME env2 /\
      env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
      state_well_typed st0 /\
      context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      accounts_well_typed st0.accounts /\
      functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
      call_evaluation_safe (cx with stk updated_by CONS (env_body.current_src,fn))
        (int_calls_stmts fn_body) /\
      eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) fn_body st0 = (res0,st0') ==>
      state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
      no_type_error_result res0 /\
      case res0 of
      | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
      | INR exn =>
          ?env_exn.
            env_extends env1 env_exn /\
            env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
            return_exception_typed env_exn ret_ty1 exn
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `!call_env' bind_st' ret_st' lock_st' cxf' pushed_st'.
     lift_option_type (bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs))
       "IntCall bind_arguments" dflt_st = (INL call_env',bind_st') /\
     lift_option_type (evaluate_type (get_tenv cx) ret)
       "IntCall eval ret" bind_st' = (INL ret_tv,ret_st') /\
     (if nr then
        case cx.nonreentrant_slot of
        | NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
      else return ()) ret_st' = (INL (),lock_st') /\
     push_function (env_body.current_src,fn) call_env' cx lock_st' =
       (INL cxf',pushed_st') ==>
     !env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 fn_body = SOME env2 /\
       env_consistent env1 cxf' st0 /\ state_well_typed st0 /\
       context_well_typed cxf' /\ accounts_well_typed st0.accounts /\
       functions_well_typed cxf' /\
       call_evaluation_safe cxf' (int_calls_stmts fn_body) /\
       eval_stmts cxf' fn_body st0 = (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 cxf' st0'
       | INR exn => ?env_exn.
           env_extends env1 env_exn /\ env_consistent env_exn cxf' st0' /\
           return_exception_typed env_exn ret_ty1 exn` by (
    ho_match_mp_tac intcall_generated_body_ih_live_consumer_premise >>
    qexistsl_tac [`src_id_opt`, `es`, `r`, `ts`, `tc_ok`, `args_st`, `dflts`] >>
    rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     simp[get_scopes_def, set_scopes_def, return_def,
          lift_option_type_def, evaluate_type_def])) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`call_env`, `dflt_st`, `dflt_st`, `lock_st`,
                              `cx with stk updated_by CONS (env_body.current_src,fn)`,
                              `lock_st with scopes := [call_env]`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >>
    (first_assum ACCEPT_TAC ORELSE
     qpat_assum `env_body.current_src = src_id_opt` (fn th =>
       simp[th, push_function_def, return_def, lift_option_type_def,
            evaluate_type_def]))) >>
  disch_then (qspecl_then [`env1`, `ret_ty1`, `env2`, `st0`, `res0`, `st0'`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE gvs[])) >>
  simp[]
QED

Theorem intcall_successful_defaults_lock_success_sound_from_body_ih[local]:
  !cx env loc res st' src_id_opt fn es extra env_body args_st dflt_st lock_st
     call_env fn_name fm nr ret body env_after ret_tv.
    (!env1 ret_ty1 env2 st0 res0 st0'.
       type_stmts env1 ret_ty1 body = SOME env2 /\
       env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0 /\
       state_well_typed st0 /\
       context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn_name)) /\
       accounts_well_typed st0.accounts /\
       functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn_name)) /\
       call_evaluation_safe
         (cx with stk updated_by CONS (env_body.current_src,fn_name))
         (int_calls_stmts body) /\
       eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn_name)) body st0 =
         (res0,st0') ==>
       state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
       no_type_error_result res0 /\
       case res0 of
       | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0'
       | INR exn =>
           ?env_exn.
             env_extends env1 env_exn /\
             env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn_name)) st0' /\
             return_exception_typed env_exn ret_ty1 exn) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn_name)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn_name)) es extra) = ret /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough body) /\
    stmts_no_control_escape body /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\ accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn_name))
      (int_calls_stmts body) /\ env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\ env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (env_body.current_src,fn_name)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (INL (),lock_st) /\
    (do rv <- finally
          (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn_name)) body;
                   return NoneV od) handle_function)
          (do pop_function args_st.scopes;
              if nr /\ ~(fm = View \/ fm = Pure) then
                case cx.nonreentrant_slot of
                | NONE => return ()
                | SOME slot => release_nonreentrant_lock cx.txn.target slot
              else return () od);
        crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
        return (Value crv) od) (lock_st with scopes := [call_env]) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn_name)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `src_id_opt`, `es`, `extra`,
                         `env_body`, `args_st`, `dflt_st`, `lock_st`,
                         `call_env`, `fn_name`, `fm`, `nr`, `ret`, `body'`,
                         `env_after`, `ret_tv`, `res`, `st'`]
    intcall_default_success_post_push_sound) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `well_typed_expr _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `expr_type _ = ret` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (
    qpat_assum `env_body.type_defs = get_tenv cx` (fn th =>
      simp[th] >> qpat_assum `evaluate_type (get_tenv cx) ret = SOME ret_tv` ACCEPT_TAC))) >>
  (CONJ_TAC THEN1 (qpat_assum `type_stmts _ _ _ = SOME _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `stmts_no_control_escape _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `context_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1
    (qpat_assum `call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn_name))
      (int_calls_stmts body')` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.type_defs = get_tenv cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.fn_sigs = env.fn_sigs` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_globals = env.bare_globals` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_global_assignable = env.bare_global_assignable` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.toplevel_vtypes = env.toplevel_vtypes` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.flag_members = env.flag_members` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_immutables_consistent _ _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `scope_well_typed call_env` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (
    qpat_assum `env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` mp_tac >>
    simp[env_scopes_consistent_stk_irrelevant])) >>
  (CONJ_TAC THEN1 (qpat_assum `(if _ then _ else _) dflt_st = _` mp_tac >> simp[])) >>
  first_assum ACCEPT_TAC
QED


Theorem intcall_successful_defaults_lock_success_sound_general[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_vs dflt_st
     call_env lock_st.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
          INL v => env_consistent env2 cx0 st0'
        | INR exn =>
            ?env_exn.
              env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
              return_exception_typed env_exn ret_ty1 exn) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (INL dflt_vs,dflt_st) /\
    bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (INL (),lock_st) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\
    accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts fn_body) /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
    (do rv <- finally
          (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) fn_body;
                   return NoneV od) handle_function)
          (do pop_function args_st.scopes;
              if nr /\ ~(fm = View \/ fm = Pure) then
                case cx.nonreentrant_slot of
                | NONE => return ()
                | SOME slot => release_nonreentrant_lock cx.txn.target slot
              else return () od);
        crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
        return (Value crv) od) (lock_st with scopes := [call_env]) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `!env1 ret_ty1 env2 st0 res0 st0'.
     type_stmts env1 ret_ty1 fn_body = SOME env2 /\
     env_consistent env1 (cx with stk updated_by CONS (env_body.current_src,fn)) st0 /\
     state_well_typed st0 /\
     context_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
     accounts_well_typed st0.accounts /\
     functions_well_typed (cx with stk updated_by CONS (env_body.current_src,fn)) /\
     call_evaluation_safe
       (cx with stk updated_by CONS (env_body.current_src,fn))
       (int_calls_stmts fn_body) /\
     eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) fn_body st0 = (res0,st0') ==>
     state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
     no_type_error_result res0 /\
     case res0 of
     | INL v => env_consistent env2 (cx with stk updated_by CONS (env_body.current_src,fn)) st0'
     | INR exn =>
         ?env_exn.
           env_extends env1 env_exn /\
           env_consistent env_exn (cx with stk updated_by CONS (env_body.current_src,fn)) st0' /\
           return_exception_typed env_exn ret_ty1 exn` by (
    MATCH_MP_TAC (Q.SPECL [`cx`, `src_id_opt`, `fn`, `es`, `r`, `ts`, `tc_ok`,
                           `actual_vs`, `args_st`, `fm`, `nr`, `args`, `dflts`,
                           `ret`, `fn_body`, `env_body`, `ret_tv`, `dflt_vs`,
                           `dflt_st`, `call_env`, `lock_st`]
      intcall_generated_body_post_push_ih) >>
    (CONJ_TAC THEN1 (qhdtm_x_assum `bool$!` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.current_src = src_id_opt` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `type_check _ "recursion" r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `lift_option_type (get_module_code _ _) _ r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `type_check _ "IntCall args length" r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `eval_exprs cx es r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `finally _ _ args_st = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `bind_arguments _ _ _ = SOME _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `evaluate_type _ _ = SOME _` ACCEPT_TAC)) >>
    qpat_assum `(if _ then _ else _) dflt_st = _` ACCEPT_TAC) >>
  MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `res`, `st'`, `src_id_opt`,
                         `fn`, `es`, `extra`, `env_body`, `args_st`, `dflt_st`,
                         `lock_st`, `call_env`, `fn`, `fm`, `nr`, `ret`,
                         `fn_body`, `env_after`, `ret_tv`]
    intcall_successful_defaults_lock_success_sound_from_body_ih) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `well_typed_expr _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `expr_type _ = ret` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `evaluate_type (get_tenv cx) ret = SOME ret_tv` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `type_stmts _ _ _ = SOME _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `stmts_no_control_escape _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `context_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1
    (qpat_assum `call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts fn_body)` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.type_defs = get_tenv cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.fn_sigs = env.fn_sigs` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_globals = env.bare_globals` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_global_assignable = env.bare_global_assignable` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.toplevel_vtypes = env.toplevel_vtypes` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.flag_members = env.flag_members` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (
    qpat_assum `env_body.current_src = src_id_opt` (fn th =>
      simp[th] >> qpat_assum `env_immutables_consistent _ _ _` ACCEPT_TAC))) >>
  (CONJ_TAC THEN1 (qpat_assum `scope_well_typed call_env` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` ACCEPT_TAC)) >>
  conj_tac >- (qpat_assum `(if _ then _ else _) dflt_st = _` ACCEPT_TAC) >>
  qpat_assum `(do rv <- finally _ _; crv <- lift_option_type _ _; return (Value crv) od) _ = _` ACCEPT_TAC
QED


Theorem intcall_successful_defaults_continuation_lock_success_case[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_vs dflt_st
     call_env lock_res lock_st.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
          INL v => env_consistent env2 cx0 st0'
        | INR exn =>
            ?env_exn.
              env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
              return_exception_typed env_exn ret_ty1 exn) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (INL dflt_vs,dflt_st) /\
    bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (lock_res,lock_st) /\
    lock_res = INL () /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env cx dflt_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\
    accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts fn_body) /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
    (case lock_res of
     | INL u =>
         (do rv <- finally
               (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) fn_body;
                        return NoneV od) handle_function)
               (do pop_function args_st.scopes;
                   if nr /\ ~(fm = View \/ fm = Pure) then
                     case cx.nonreentrant_slot of
                     | NONE => return ()
                     | SOME slot => release_nonreentrant_lock cx.txn.target slot
                   else return () od);
             crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
             return (Value crv) od) (lock_st with scopes := [call_env])
     | INR e => (INR e,lock_st)) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  qpat_x_assum `lock_res = INL ()` SUBST_ALL_TAC >>
  qpat_x_assum `(case INL () of INL u => _ | INR e => _) = (res,st')` mp_tac >>
  rewrite_tac[sum_case_def] >> strip_tac >>
  MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `res`, `st'`, `src_id_opt`,
                         `fn`, `es`, `extra`, `r`, `ts`, `tc_ok`,
                         `actual_vs`, `args_st`, `fm`, `nr`, `args`, `dflts`,
                         `ret`, `fn_body`, `env_body`, `ret_tv`, `env_after`,
                         `dflt_vs`, `dflt_st`, `call_env`, `lock_st`]
    intcall_successful_defaults_lock_success_sound_general) >>
  (CONJ_TAC THEN1 (qhdtm_x_assum `bool$!` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `type_check _ "recursion" r = _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `lift_option_type (get_module_code _ _) _ r = _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ r = _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `type_check _ "IntCall args length" r = _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `eval_exprs cx es r = _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `finally _ _ args_st = _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `bind_arguments _ _ _ = SOME _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `evaluate_type _ _ = SOME _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `(if _ then _ else _) dflt_st = _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `well_typed_expr _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `expr_type _ = ret` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `type_stmts _ _ _ = SOME _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
  (CONJ_TAC THEN1 (qpat_assum `stmts_no_control_escape _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed args_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `context_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1
    (qpat_assum `call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts fn_body)` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.current_src = src_id_opt` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.type_defs = get_tenv cx` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.fn_sigs = env.fn_sigs` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_globals = env.bare_globals` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.bare_global_assignable = env.bare_global_assignable` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.toplevel_vtypes = env.toplevel_vtypes` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_body.flag_members = env.flag_members` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_immutables_consistent _ _ _` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `scope_well_typed call_env` ACCEPT_TAC)) >>
  (CONJ_TAC THEN1 (qpat_assum `env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` ACCEPT_TAC)) >>
  first_assum ACCEPT_TAC
QED


Theorem intcall_successful_defaults_continuation_sound_general[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_vs dflt_st
     call_env lock_res lock_st.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
          INL v => env_consistent env2 cx0 st0'
        | INR exn =>
            ?env_exn.
              env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
              return_exception_typed env_exn ret_ty1 exn) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (INL dflt_vs,dflt_st) /\
    bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (lock_res,lock_st) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env cx dflt_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\
    accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts fn_body) /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
    (case lock_res of
     | INL u =>
         (do rv <- finally
               (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) fn_body;
                        return NoneV od) handle_function)
               (do pop_function args_st.scopes;
                   if nr /\ ~(fm = View \/ fm = Pure) then
                     case cx.nonreentrant_slot of
                     | NONE => return ()
                     | SOME slot => release_nonreentrant_lock cx.txn.target slot
                   else return () od);
             crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
             return (Value crv) od) (lock_st with scopes := [call_env])
     | INR e => (INR e,lock_st)) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `lift_option_type (bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs))
     "IntCall bind_arguments" dflt_st = (INL call_env,dflt_st)` by
    simp[lift_option_type_def, return_def] >>
  `lift_option_type (evaluate_type (get_tenv cx) ret)
     "IntCall eval ret" dflt_st = (INL ret_tv,dflt_st)` by
    simp[lift_option_type_def, return_def] >>
  (Cases_on `lock_res` >- (
    Cases_on `x` >>
    MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `res`, `st'`, `src_id_opt`,
                           `fn`, `es`, `extra`, `r`, `ts`, `tc_ok`,
                           `actual_vs`, `args_st`, `fm`, `nr`, `args`, `dflts`,
                           `ret`, `fn_body`, `env_body`, `ret_tv`, `env_after`,
                           `dflt_vs`, `dflt_st`, `call_env`, `INL ()`, `lock_st`]
      intcall_successful_defaults_continuation_lock_success_case) >>
    (CONJ_TAC THEN1 (qhdtm_x_assum `bool$!` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `type_check _ "recursion" r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `lift_option_type (get_module_code _ _) _ r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `lift_option_type (lookup_callable_function _ _ _) _ r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `type_check _ "IntCall args length" r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `eval_exprs cx es r = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `finally _ _ args_st = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `bind_arguments _ _ _ = SOME _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `evaluate_type _ _ = SOME _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `(if _ then _ else _) dflt_st = _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 simp[]) >>
    (CONJ_TAC THEN1 (qpat_assum `well_typed_expr _ _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `expr_type _ = ret` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `type_stmts _ _ _ = SOME _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 (qpat_assum `stmts_no_control_escape _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx args_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `state_well_typed args_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx dflt_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `context_well_typed cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1
      (qpat_assum `call_evaluation_safe
        (cx with stk updated_by CONS (env_body.current_src,fn))
        (int_calls_stmts fn_body)` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.current_src = src_id_opt` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.type_defs = get_tenv cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.fn_sigs = env.fn_sigs` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.bare_globals = env.bare_globals` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.bare_global_assignable = env.bare_global_assignable` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.toplevel_vtypes = env.toplevel_vtypes` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.flag_members = env.flag_members` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_immutables_consistent _ _ _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `scope_well_typed call_env` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` ACCEPT_TAC)) >>
    first_assum ACCEPT_TAC)) >>
  qpat_x_assum `(case INR y of INL u => _ | INR e => _) = (res,st')` mp_tac >>
  rewrite_tac[sum_case_def] >> strip_tac >>
  `nr ==> cx.nonreentrant_slot <> NONE` by (
    `get_module_code cx src_id_opt = SOME ts` by
      metis_tac[lift_option_type_INL_eq] >>
    `lookup_callable_function cx.in_deploy fn ts =
       SOME (fm,nr,args,dflts,ret,fn_body)` by
      metis_tac[lift_option_type_INL_eq] >>
    drule_all callable_body_typing_from_env_consistent >> simp[]) >>
  qspecl_then [`env`, `cx`, `nr`, `fm = View \/ fm = Pure`,
               `dflt_st`, `INR y`, `lock_st`] mp_tac intcall_lock_attempt_sound_frame >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  qpat_x_assum `(\e. (INR e,lock_st)) y = (res,st')` mp_tac >>
  BETA_TAC >> pure_rewrite_tac[PAIR_EQ] >> strip_tac >>
  qpat_x_assum `lock_st = st'` (fn th => SUBST1_TAC (SYM th)) >>
  qpat_x_assum `INR y = res` (fn th => SUBST1_TAC (SYM th)) >>
  qpat_x_assum `case INR y of INL v => T | INR v1 => env_consistent env cx lock_st` mp_tac >>
  rewrite_tac[sum_case_def] >> strip_tac >>
  conj_tac >- (qpat_assum `state_well_typed lock_st` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `env_consistent env cx lock_st` ACCEPT_TAC) >>
  conj_tac >- (qpat_assum `accounts_well_typed lock_st.accounts` ACCEPT_TAC) >>
  pop_assum kall_tac >>
  qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
  rewrite_tac[no_type_error_result_def] >> strip_tac >> strip_tac >>
  first_x_assum (qspec_then `msg` mp_tac) >> simp[]
QED

Theorem intcall_default_failure_tail_case_from_result[local]:
  !cx env loc res st' src_id_opt fn es extra dflt_res dflt_st success_tail.
    state_well_typed dflt_st /\
    env_consistent env cx dflt_st /\
    accounts_well_typed dflt_st.accounts /\
    no_type_error_result dflt_res /\
    (case dflt_res of
     | INL dflt_vs => success_tail dflt_vs
     | INR e => (INR e,dflt_st)) = (res,st') ==>
    (case dflt_res of
     | INL _ => T
     | INR _ =>
         state_well_typed st' /\ env_consistent env cx st' /\
         accounts_well_typed st'.accounts /\ no_type_error_result res /\
         case res of
         | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
         | INR _ => T)
Proof
  rpt strip_tac >>
  Cases_on `dflt_res` >>
  gvs[sumTheory.sum_case_def, pairTheory.PAIR_EQ, no_type_error_result_def]
QED

Theorem intcall_actual_args_success_default_success_branch[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_vs dflt_st
     call_env lock_res lock_st.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
          INL v => env_consistent env2 cx0 st0'
        | INR exn =>
            ?env_exn.
              env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
              return_exception_typed env_exn ret_ty1 exn) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (INL dflt_vs,dflt_st) /\
    bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = (lock_res,lock_st) /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env cx dflt_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\
    accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts fn_body) /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
    (case lock_res of
     | INL u =>
         (do rv <- finally
               (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) fn_body;
                        return NoneV od) handle_function)
               (do pop_function args_st.scopes;
                   if nr /\ ~(fm = View \/ fm = Pure) then
                     case cx.nonreentrant_slot of
                     | NONE => return ()
                     | SOME slot => release_nonreentrant_lock cx.txn.target slot
                   else return () od);
             crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
             return (Value crv) od) (lock_st with scopes := [call_env])
     | INR e => (INR e,lock_st)) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_tac >>
  MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `res`, `st'`, `src_id_opt`,
                         `fn`, `es`, `extra`, `r`, `ts`, `tc_ok`,
                         `actual_vs`, `args_st`, `fm`, `nr`, `args`, `dflts`,
                         `ret`, `fn_body`, `env_body`, `ret_tv`, `env_after`,
                         `dflt_vs`, `dflt_st`, `call_env`, `lock_res`, `lock_st`]
    intcall_successful_defaults_continuation_sound_general) >>
  first_assum ACCEPT_TAC
QED

Theorem intcall_actual_args_success_default_success_branch_pair[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_vs dflt_st
     call_env lock_pair.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
          INL v => env_consistent env2 cx0 st0'
        | INR exn =>
            ?env_exn.
              env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
              return_exception_typed env_exn ret_ty1 exn) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (INL dflt_vs,dflt_st) /\
    bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs) = SOME call_env /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
     else return ()) dflt_st = lock_pair /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    env_consistent env cx args_st /\
    state_well_typed args_st /\
    env_consistent env cx dflt_st /\
    state_well_typed dflt_st /\
    context_well_typed cx /\
    accounts_well_typed dflt_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts fn_body) /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    env_immutables_consistent env_body
      (cx with stk updated_by CONS (src_id_opt,fn)) dflt_st /\
    scope_well_typed call_env /\
    env_scopes_consistent env_body cx (dflt_st with scopes := [call_env]) /\
    (case lock_pair of
     | (INL u,lock_st) =>
         (do rv <- finally
               (try (do eval_stmts (cx with stk updated_by CONS (env_body.current_src,fn)) fn_body;
                        return NoneV od) handle_function)
               (do pop_function args_st.scopes;
                   if nr /\ ~(fm = View \/ fm = Pure) then
                     case cx.nonreentrant_slot of
                     | NONE => return ()
                     | SOME slot => release_nonreentrant_lock cx.txn.target slot
                   else return () od);
             crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
             return (Value crv) od) (lock_st with scopes := [call_env])
     | (INR e,lock_st) => (INR e,lock_st)) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> PairCases_on `lock_pair` >>
  rewrite_tac[pairTheory.FST, pairTheory.SND] >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `res`, `st'`, `src_id_opt`, `fn`,
                         `es`, `extra`, `r`, `ts`, `tc_ok`, `actual_vs`, `args_st`,
                         `fm`, `nr`, `args`, `dflts`, `ret`, `fn_body`,
                         `env_body`, `ret_tv`, `env_after`, `dflt_vs`, `dflt_st`,
                         `call_env`, `lock_pair0`, `lock_pair1`]
    intcall_actual_args_success_default_success_branch) >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   qpat_x_assum `(case (lock_pair0,lock_pair1) of _ => _ | _ => _) = (res,st')` mp_tac >>
   simp[])
QED

Theorem intcall_lift_evaluate_type_success[local]:
  evaluate_type tenv ret = SOME ret_tv ==>
  lift_option_type (evaluate_type tenv ret) msg st = (INL ret_tv,st)
Proof
  simp[lift_option_type_def, return_def]
QED


Theorem intcall_actual_args_success_sound_from_generated_ih_general[local]:
  !cx env loc res st' src_id_opt fn es extra r ts tc_ok actual_vs args_st
     fm nr args dflts ret fn_body env_body ret_tv env_after dflt_res dflt_st.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 es0 cx0
        s7 prev0 t7 s8 x8 t8.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      es0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cx0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      set_scopes [FEMPTY] s8 = (INL x8,t8) ==>
      !env0 st0 res0 st0'.
        well_typed_exprs env0 es0 /\ env_consistent env0 cx0 st0 /\
        state_well_typed st0 /\ context_well_typed cx0 /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_exprs es0) /\
        eval_exprs cx0 es0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ env_consistent env0 cx0 st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL vs => exprs_runtime_typed env0 es0 vs | INR _ => T) /\
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
          INL v => env_consistent env2 cx0 st0'
        | INR exn =>
            ?env_exn.
              env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
              return_exception_typed env_exn ret_ty1 exn) /\
    type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" r = (INL (),r) /\
    lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r =
      (INL ts,r) /\
    lift_option_type (lookup_callable_function cx.in_deploy fn ts)
      "IntCall lookup_function" r = (INL (fm,nr,args,dflts,ret,fn_body),r) /\
    type_check (LENGTH es <= LENGTH args /\ LENGTH args - LENGTH es <= LENGTH dflts)
      "IntCall args length" r = (INL tc_ok,r) /\
    eval_exprs cx es r = (INL actual_vs,args_st) /\
    env_consistent env cx args_st /\ state_well_typed args_st /\
    context_well_typed cx /\ accounts_well_typed args_st.accounts /\
    functions_well_typed cx /\
    call_evaluation_safe (cx with stk updated_by CONS (src_id_opt,fn))
      (int_calls_exprs
        (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)) /\
    call_evaluation_safe
      (cx with stk updated_by CONS (env_body.current_src,fn))
      (int_calls_stmts fn_body) /\
    exprs_runtime_typed env es actual_vs /\
    MAP expr_type es = TAKE (LENGTH es) (MAP SND args) /\
    env_body.current_src = src_id_opt /\
    env_body.type_defs = get_tenv cx /\
    env_body.fn_sigs = env.fn_sigs /\
    env_body.bare_globals = env.bare_globals /\
    env_body.bare_global_assignable = env.bare_global_assignable /\
    env_body.toplevel_vtypes = env.toplevel_vtypes /\
    env_body.flag_members = env.flag_members /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) /\
    expr_type (Call loc (IntCall (src_id_opt,fn)) es extra) = ret /\
    evaluate_type (get_tenv cx) ret = SOME ret_tv /\
    type_stmts env_body ret fn_body = SOME env_after /\
    (ret = NoneT \/ stmts_no_fallthrough fn_body) /\
    stmts_no_control_escape fn_body /\
    well_typed_exprs (defaults_env env_body) dflts /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T) /\
    MAP expr_type dflts = MAP SND (DROP (LENGTH args - LENGTH dflts) args) /\
    finally (do set_scopes [FEMPTY];
                eval_exprs (cx with stk updated_by CONS (src_id_opt,fn))
                  (DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts)
             od) (set_scopes args_st.scopes) args_st = (dflt_res,dflt_st) /\
    (case dflt_res of
     | INL dflt_vs =>
         (case lift_option_type (bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs))
                 "IntCall bind_arguments" dflt_st of
          | (INL call_env,bind_st) =>
              (case (if nr then
                       case cx.nonreentrant_slot of
                       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
                       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
                     else return ()) bind_st of
               | (INL u,lock_st) =>
                   (case push_function (src_id_opt,fn) call_env cx lock_st of
                    | (INL cxf,pushed_st) =>
                        (do rv <- finally
                              (try (do eval_stmts cxf fn_body; return NoneV od) handle_function)
                              (do pop_function args_st.scopes;
                                  if nr /\ fm <> View /\ fm <> Pure then
                                    case cx.nonreentrant_slot of
                                    | NONE => return ()
                                    | SOME slot => release_nonreentrant_lock cx.txn.target slot
                                  else return () od);
                            crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
                            return (Value crv) od) pushed_st
                    | (INR e,push_st) => (INR e,push_st))
               | (INR e,lock_st) => (INR e,lock_st))
          | (INR e,bind_st) => (INR e,bind_st))
     | INR e => (INR e,dflt_st)) = (res,st') ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
    | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  mp_tac (Q.SPECL [`cx`, `env`, `src_id_opt`, `fn`, `es`, `r`, `ts`, `tc_ok`,
                   `actual_vs`, `args_st`, `fm`, `nr`, `args`, `dflts`, `ret`,
                   `fn_body`, `env_body`, `ret_tv`, `env_after`, `dflt_res`, `dflt_st`]
    intcall_defaults_result_frame_package_from_generated_ih_general) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then strip_assume_tac >>
  qpat_assum `no_type_error_result dflt_res` (mk_asm "dflt_nte") >>
  `case dflt_res of
   | INL _ => T
   | INR _ =>
       state_well_typed st' /\ env_consistent env cx st' /\
       accounts_well_typed st'.accounts /\ no_type_error_result res /\
       case res of
       | INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
       | INR _ => T` by (
    MATCH_MP_TAC intcall_default_failure_tail_case_from_result >>
    qexists_tac `dflt_st` >>
    qexists_tac `(\dflt_vs.
      (case lift_option_type (bind_arguments (get_tenv cx) args (actual_vs ++ dflt_vs))
              "IntCall bind_arguments" dflt_st of
       | (INL call_env,bind_st) =>
           (case (if nr then
                    case cx.nonreentrant_slot of
                    | NONE => raise (Error (TypeError "nonreentrant slot missing"))
                    | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
                  else return ()) bind_st of
            | (INL u,lock_st) =>
                (case push_function (src_id_opt,fn) call_env cx lock_st of
                 | (INL cxf,pushed_st) =>
                     (do rv <- finally
                           (try (do eval_stmts cxf fn_body; return NoneV od) handle_function)
                           (do pop_function args_st.scopes;
                               if nr /\ fm <> View /\ fm <> Pure then
                                 case cx.nonreentrant_slot of
                                 | NONE => return ()
                                 | SOME slot => release_nonreentrant_lock cx.txn.target slot
                               else return () od);
                         crv <- lift_option_type (safe_cast ret_tv rv) "IntCall cast ret";
                         return (Value crv) od) pushed_st
                 | (INR e,push_st) => (INR e,push_st))
            | (INR e,lock_st) => (INR e,lock_st))
       | (INR e,bind_st) => (INR e,bind_st)))` >>
    (CONJ_TAC THEN1 (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx dflt_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (asm "dflt_nte" ACCEPT_TAC)) >>
    qpat_x_assum `(case dflt_res of INL dflt_vs => _ | INR e => (INR e,dflt_st)) = (res,st')` mp_tac >>
    BETA_TAC >> simp[]) >>
  pop_assum $ mk_asm "failure_tail" >>
  Cases_on `dflt_res` >- (
    qpat_x_assum `case INL x of INL dflt_vs => _ | INR _ => T` mp_tac >>
    rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >> strip_tac >>
    qabbrev_tac `lp =
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (fm = View \/ fm = Pure)
       else return ()) dflt_st` >>
    MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `loc`, `res`, `st'`, `src_id_opt`, `fn`,
                           `es`, `extra`, `r`, `ts`, `tc_ok`, `actual_vs`, `args_st`,
                           `fm`, `nr`, `args`, `dflts`, `ret`, `fn_body`,
                           `env_body`, `ret_tv`, `env_after`, `x`, `dflt_st`,
                           `call_env`, `lp`]
      intcall_actual_args_success_default_success_branch_pair) >>
    (CONJ_TAC THEN1 (qpat_assum
       `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
          sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
          s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
          is_view0 s11 x11 t11 s12 cx0 t12. _`
       ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 (qpat_x_assum `Abbrev (lp = _)` mp_tac >>
                      simp[markerTheory.Abbrev_def])) >>
    (CONJ_TAC THEN1 (qpat_assum `well_typed_expr _ _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 (qpat_assum `type_stmts env_body ret fn_body = SOME env_after` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 first_assum ACCEPT_TAC) >>
    (CONJ_TAC THEN1 (qpat_assum `stmts_no_control_escape _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx args_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `state_well_typed args_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx dflt_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `state_well_typed dflt_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `context_well_typed cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed dflt_st.accounts` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1
      (qpat_assum `call_evaluation_safe
        (cx with stk updated_by CONS (env_body.current_src,fn))
        (int_calls_stmts fn_body)` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.current_src = src_id_opt` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.type_defs = get_tenv cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.fn_sigs = env.fn_sigs` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.bare_globals = env.bare_globals` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.bare_global_assignable = env.bare_global_assignable` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.toplevel_vtypes = env.toplevel_vtypes` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.flag_members = env.flag_members` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_immutables_consistent _ _ _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `scope_well_typed call_env` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_scopes_consistent env_body cx (dflt_st with scopes := [call_env])` ACCEPT_TAC)) >>
    qpat_x_assum `(case INL x of _ => _ | _ => _) = (res,st')` mp_tac >>
    simp[Abbr `lp`, lift_option_type_def, return_def, bind_apply,
         push_function_def, pairTheory.PAIR]) >>
  asm "failure_tail" mp_tac >>
  rewrite_tac[sumTheory.sum_case_def] >>
  disch_then ACCEPT_TAC
QED

Theorem intcall_expr_sound_from_generated_ih[local]:
  !cx env st res st' loc src_id_opt fn es extra.
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) ==>
      !env0 st0 res0 st0'.
        well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\
        state_well_typed st0 /\ context_well_typed cx /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx /\
        call_evaluation_safe cx (int_calls_exprs es) /\
        eval_exprs cx es st0 = (res0,st0') ==>
        state_well_typed st0' /\ env_consistent env0 cx st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL vs => exprs_runtime_typed env0 es vs | INR _ => T) /\
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 es0 cx0
        s7 prev0 t7 s8 x8 t8.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      es0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cx0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      set_scopes [FEMPTY] s8 = (INL x8,t8) ==>
      !env0 st0 res0 st0'.
        well_typed_exprs env0 es0 /\ env_consistent env0 cx0 st0 /\
        state_well_typed st0 /\ context_well_typed cx0 /\
        accounts_well_typed st0.accounts /\ functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_exprs es0) /\
        eval_exprs cx0 es0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ env_consistent env0 cx0 st0' /\
        accounts_well_typed st0'.accounts /\ no_type_error_result res0 /\
        case res0 of INL vs => exprs_runtime_typed env0 es0 vs | INR _ => T) /\
    (!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 needed0 cxd0
        s7 dflt_vs0 t7 all_tenv0 s8 env0 t8 s9 prev0 t9 s10 rtv0 t10
        is_view0 s11 x11 t11 s12 cx0 t12.
      type_check (~MEM (src_id_opt,fn) cx.stk) "recursion" s0 = (INL x0,t0) /\
      lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" s1 =
        (INL ts0,t1) /\
      lift_option_type (lookup_callable_function cx.in_deploy fn ts0)
        "IntCall lookup_function" s2 = (INL tup0,t2) /\
      mut0 = FST tup0 /\ stup0 = SND tup0 /\ (nr0 <=> FST stup0) /\
      stup20 = SND stup0 /\ args0 = FST stup20 /\ sstup0 = SND stup20 /\
      dflts0 = FST sstup0 /\ sstup20 = SND sstup0 /\ ret0 = FST sstup20 /\
      body0 = SND sstup20 /\
      type_check (LENGTH es <= LENGTH args0 /\ LENGTH args0 - LENGTH es <= LENGTH dflts0)
        "IntCall args length" s5 = (INL x5,t5) /\
      eval_exprs cx es s6 = (INL vs0,t6) /\
      needed0 = DROP (LENGTH dflts0 - (LENGTH args0 - LENGTH es)) dflts0 /\
      cxd0 = cx with stk updated_by CONS (src_id_opt,fn) /\
      get_scopes s7 = (INL prev0,t7) /\
      finally (do set_scopes [FEMPTY]; eval_exprs cxd0 needed0 od) (set_scopes prev0) s8 =
        (INL dflt_vs0,t8) /\
      all_tenv0 = get_tenv cx /\
      lift_option_type (bind_arguments all_tenv0 args0 (vs0 ++ dflt_vs0))
        "IntCall bind_arguments" s9 = (INL env0,t9) /\
      lift_option_type (evaluate_type all_tenv0 ret0) "IntCall eval ret" s10 =
        (INL rtv0,t10) /\
      (is_view0 <=> mut0 = View \/ mut0 = Pure) /\
      (if nr0 then
         case cx.nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view0
       else return ()) s11 = (INL x11,t11) /\
      push_function (src_id_opt,fn) env0 cx s12 = (INL cx0,t12) ==>
      !env1 ret_ty1 env2 st0 res0 st0'.
        type_stmts env1 ret_ty1 body0 = SOME env2 /\
        env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
        context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
        functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==>
        state_well_typed st0' /\ accounts_well_typed st0'.accounts /\
        no_type_error_result res0 /\
        case res0 of
          INL v => env_consistent env2 cx0 st0'
        | INR exn =>
            ?env_exn.
              env_extends env1 env_exn /\ env_consistent env_exn cx0 st0' /\
              return_exception_typed env_exn ret_ty1 exn) /\
    env_consistent env cx st /\ state_well_typed st /\ context_well_typed cx /\
    accounts_well_typed st.accounts /\ functions_well_typed cx /\
    call_evaluation_safe cx
      (int_calls_expr (Call loc (IntCall (src_id_opt,fn)) es extra)) /\
    eval_expr cx (Call loc (IntCall (src_id_opt,fn)) es extra) st = (res,st') /\
    well_typed_expr env (Call loc (IntCall (src_id_opt,fn)) es extra) ==>
    state_well_typed st' /\ env_consistent env cx st' /\
    accounts_well_typed st'.accounts /\ no_type_error_result res /\
    case res of
      INL tv => expr_result_typed env (Call loc (IntCall (src_id_opt,fn)) es extra) tv
    | INR _ => T
Proof
  rpt gen_tac >> strip_tac >>
  qhdtm_x_assum `call_evaluation_safe` (mk_asm "call_safe") >>
  asm "call_safe" (fn th =>
    assume_tac (MATCH_MP intcall_call_evaluation_safe_target_not_mem th)) >>
  pop_assum $ mk_asm "recursion_guard" >>
  qpat_x_assum `well_typed_expr env (Call _ (IntCall _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum
    `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5.
        _ ==>
        !env0 st0 res0 st0'.
          well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\
          state_well_typed st0 /\ context_well_typed cx /\
          accounts_well_typed st0.accounts /\ functions_well_typed cx /\
          call_evaluation_safe cx (int_calls_exprs es) /\
          eval_exprs cx es st0 = (res0,st0') ==> _`
    (mk_asm "actual_ih") >>
  qpat_x_assum
    `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 es0 cx0 s7 prev0 t7 s8 x8 t8.
        _ ==>
        !env0 st0 res0 st0'.
          well_typed_exprs env0 es0 /\ env_consistent env0 cx0 st0 /\
          state_well_typed st0 /\ context_well_typed cx0 /\
          accounts_well_typed st0.accounts /\ functions_well_typed cx0 /\
          call_evaluation_safe cx0 (int_calls_exprs es0) /\
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
          env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
          context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
          functions_well_typed cx0 /\
        call_evaluation_safe cx0 (int_calls_stmts body0) /\
        eval_stmts cx0 body0 st0 = (res0,st0') ==> _`
    (mk_asm "body_ih") >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  rewrite_tac[Once evaluate_def] >>
  simp_tac(srw_ss())[bind_apply, ignore_bind_apply, LET_THM] >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
      gvs[L "recursion_guard", type_check_def, assert_def]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
      `fn_sigs_consistent env.fn_sigs cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      qpat_x_assum `fn_sigs_consistent env.fn_sigs cx` mp_tac >>
      simp[fn_sigs_consistent_def] >>
      disch_then (qspecl_then [`src_id_opt`, `fn`, `sig`] mp_tac) >>
      simp[] >> strip_tac >>
      gvs[lift_option_type_def, return_def, raise_def, no_type_error_result_def]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac lift_option_type_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
      `fn_sigs_consistent env.fn_sigs cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      qpat_x_assum `lift_option_type (get_module_code cx src_id_opt) _ r = (INL x',r)`
        (fn th => assume_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
      drule_all fn_sigs_consistent_FLOOKUP >> strip_tac >>
      qpat_x_assum `get_module_code cx src_id_opt = SOME x' /\ _` strip_assume_tac >>
      drule_all intcall_lookup_function_not_INR >> strip_tac >>
      qpat_x_assum `!st' st msg e. lift_option_type (lookup_callable_function cx.in_deploy fn x') msg st <> (INR e,st')`
        (qspecl_then [`r''`, `r`, `"IntCall lookup_function"`, `y`] mp_tac) >>
      simp[]) >>
  BasicProvers.TOP_CASE_TAC >>
  imp_res_tac type_check_state >> BasicProvers.VAR_EQ_TAC >>
  reverse BasicProvers.TOP_CASE_TAC >- (strip_tac >>
      `fn_sigs_consistent env.fn_sigs cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      drule_all intcall_args_length_condition >> strip_tac >>
      gvs[type_check_def, assert_def, return_def, raise_def,
          no_type_error_result_def]) >>
  simp_tac(srw_ss())[bind_apply] >>
  BasicProvers.TOP_CASE_TAC >>
  qmatch_asmsub_rename_tac `eval_exprs cx es r = (args_res,args_st)` >>
  qmatch_asmsub_rename_tac `type_check _ _ r = (INL tc_ok,r)` >>
  `call_evaluation_safe cx (int_calls_exprs es)` by
    asm "call_safe" (fn th =>
      ACCEPT_TAC (MATCH_MP intcall_call_evaluation_safe_args th)) >>
  asm_x "actual_ih" mp_tac >> simp[] >>
  disch_then (qspecl_then [`r`, `r`, `r`, `x'`, `r`, `r`, `x''`, `r''`, `r`, `r`] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `args_res` >> gvs[]
  >- (
    qpat_assum `lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code" r = (INL x',r)`
      (fn th => mp_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
    strip_tac >>
    qpat_assum `lift_option_type (lookup_callable_function cx.in_deploy fn x') "IntCall lookup_function" r = (INL x'',r)`
      (fn th => mp_tac (MATCH_MP (iffLR lift_option_type_INL_eq) th)) >>
    strip_tac >>
    PairCases_on `x''` >> gvs[] >>
    qpat_assum `get_module_code cx src_id_opt = SOME x'`
      (mk_asm "module_ok") >>
    qpat_assum `lookup_callable_function cx.in_deploy fn x' =
                  SOME (x''0,x''1,x''2,x''3,x''4,x''5)`
      (mk_asm "lookup_ok") >>
    mp_tac (Q.INST [`st` |-> `args_st`, `ts` |-> `x'`,
                    `fm` |-> `x''0`, `nr` |-> `x''1`,
                    `args` |-> `x''2`, `dflts` |-> `x''3`,
                    `ret` |-> `x''4`, `fn_body` |-> `x''5`]
             callable_body_typing_from_env_consistent) >>
    simp[] >>
    disch_then (CONJUNCTS_THEN2 assume_tac
      (qx_choose_then `env_body` (qx_choose_then `ret_tv` (qx_choose_then `env_after`
        (fn th => map_every assume_tac (CONJUNCTS th)))))) >>
    `sig.param_types = MAP SND x''2 /\ sig.num_defaults = LENGTH x''3` by (
      `fn_sigs_consistent env.fn_sigs cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      drule_all fn_sigs_consistent_FLOOKUP >> strip_tac >> gvs[]) >>
    simp[get_scopes_def, return_def] >>
    BasicProvers.TOP_CASE_TAC >>
    qmatch_asmsub_rename_tac `finally _ _ args_st = (dflt_res,dflt_st)` >>
    qmatch_asmsub_rename_tac `eval_exprs cx es r = (INL actual_vs,args_st)` >>
    asm "call_safe" (fn call_th =>
      asm "module_ok" (fn module_th =>
        asm "lookup_ok" (fn lookup_th =>
          assume_tac (Q.INST
            [`n` |-> `LENGTH x''3 - (LENGTH x''2 - LENGTH es)`]
            (MATCH_MP intcall_call_evaluation_safe_needed_defaults
              (LIST_CONJ [call_th, module_th, lookup_th])))))) >>
    asm "call_safe" (fn call_th =>
      asm "module_ok" (fn module_th =>
        asm "lookup_ok" (fn lookup_th =>
          assume_tac (MATCH_MP
            intcall_call_evaluation_safe_body
            (LIST_CONJ [call_th, module_th, lookup_th]))))) >>
    strip_tac >>
    MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `sig.ret_ty`, `res`, `st'`, `src_id_opt`, `fn`,
                           `es`, `extra`, `r`, `x'`, `tc_ok`, `actual_vs`, `args_st`,
                           `x''0`, `x''1`, `x''2`, `x''3`, `x''4`, `x''5`,
                           `env_body`, `ret_tv`, `env_after`, `dflt_res`, `dflt_st`]
      intcall_actual_args_success_sound_from_generated_ih_general) >>
    (CONJ_TAC THEN1 (asm "default_ih" (fn th => MATCH_ACCEPT_TAC th))) >>
    (CONJ_TAC THEN1 (asm "body_ih" (fn th => MATCH_ACCEPT_TAC th))) >>
    (CONJ_TAC THEN1 (qpat_assum `type_check _ _ r = (INL (),r)` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 simp[lift_option_type_def, return_def]) >>
    (CONJ_TAC THEN1 simp[lift_option_type_def, return_def]) >>
    (CONJ_TAC THEN1 (
      qpat_x_assum `type_check (LENGTH es <= LENGTH x''2 /\ LENGTH x''2 <= LENGTH es + LENGTH x''3) "IntCall args length" r = (INL (),r)` mp_tac >>
      simp[type_check_def, assert_def, return_def, raise_def] >> strip_tac >>
      simp[type_check_def, assert_def, return_def])) >>
    (CONJ_TAC THEN1 (qpat_assum `eval_exprs cx es r = (INL actual_vs,args_st)` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_consistent env cx args_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `state_well_typed args_st` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `context_well_typed cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `accounts_well_typed args_st.accounts` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `functions_well_typed cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (
      qpat_assum `call_evaluation_safe
        (cx with stk updated_by CONS (src_id_opt,fn))
        (int_calls_exprs
          (DROP (LENGTH x''3 - (LENGTH x''2 - LENGTH es)) x''3))`
        MATCH_ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (
      qpat_assum `env_body.current_src = src_id_opt`
        (fn th => rewrite_tac[th]) >>
      qpat_assum `call_evaluation_safe
        (cx with stk updated_by CONS (src_id_opt,fn))
        (int_calls_stmts x''5)` MATCH_ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `exprs_runtime_typed env es actual_vs` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 simp[]) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.current_src = src_id_opt` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.type_defs = get_tenv cx` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.fn_sigs = env.fn_sigs` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.bare_globals = env.bare_globals` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.bare_global_assignable = env.bare_global_assignable` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.toplevel_vtypes = env.toplevel_vtypes` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `env_body.flag_members = env.flag_members` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (simp[Once well_typed_expr_def] >> qexists `sig` >> simp[])) >>
    (CONJ_TAC THEN1 (
      `fn_sigs_consistent env.fn_sigs cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      drule_all fn_sigs_consistent_FLOOKUP >> strip_tac >>
      gvs[expr_type_def])) >>
    (CONJ_TAC THEN1 (qpat_assum `evaluate_type (get_tenv cx) x''4 = SOME ret_tv` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `type_stmts env_body x''4 x''5 = SOME env_after` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `x''4 = NoneT \/ stmts_no_fallthrough x''5` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `stmts_no_control_escape x''5` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `well_typed_exprs (defaults_env env_body) x''3` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `!id typ. MEM (id,typ) x''2 ==> _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `!n ty. FLOOKUP env_body.var_types n = SOME ty ==> _` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (
      rpt strip_tac >>
      qpat_x_assum `!n b. FLOOKUP env_body.var_assignable n = SOME b ==> _`
        (qspecl_then [`n`, `b`] mp_tac) >>
      simp[] >> strip_tac >> gvs[])) >>
    (CONJ_TAC THEN1 (qpat_assum `MAP expr_type x''3 = MAP SND (DROP (LENGTH x''2 - LENGTH x''3) x''2)` ACCEPT_TAC)) >>
    (CONJ_TAC THEN1 (qpat_assum `finally _ _ args_st = (dflt_res,dflt_st)` ACCEPT_TAC)) >>
    qpat_x_assum `(case dflt_res of INL _ => _ | INR _ => _) = (res,st')` mp_tac >>
    simp[get_scopes_def, set_scopes_def, return_def, lift_option_type_def,
         evaluate_type_def, bind_apply])
  >- (strip_tac >> gvs[no_type_error_result_def])
QED
(* ===== Internal call final placement helper ===== *)

Theorem type_place_expr_Call_IntCall_NONE[local]:
  !env ty src_id_opt fn es drv.
    type_place_expr env (Call ty (IntCall (src_id_opt,fn)) es drv) = NONE
Proof
  simp[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_IntCall]:
  rpt gen_tac >> strip_tac >>
  reverse conj_tac >- (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `type_place_expr _ (Call _ (IntCall _) _ _) = SOME _` mp_tac >>
    simp[type_place_expr_Call_IntCall_NONE]) >>
  strip_tac >>
  qpat_x_assum
    `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5.
        _ ==>
        !env0 st0 res0 st0'.
          well_typed_exprs env0 es /\ env_consistent env0 cx st0 /\
          state_well_typed st0 /\ context_well_typed cx /\
          accounts_well_typed st0.accounts /\ functions_well_typed cx /\
          call_evaluation_safe cx (int_calls_exprs es) /\
          eval_exprs cx es st0 = (res0,st0') ==> _`
    (mk_asm "actual_ih") >>
  qpat_x_assum
    `!s0 x0 t0 s1 ts0 t1 s2 tup0 t2 mut0 stup0 nr0 stup20 args0
        sstup0 dflts0 sstup20 ret0 body0 s5 x5 t5 s6 vs0 t6 es0 cx0 s7 prev0 t7 s8 x8 t8.
        _ ==>
        !env0 st0 res0 st0'.
          well_typed_exprs env0 es0 /\ env_consistent env0 cx0 st0 /\
          state_well_typed st0 /\ context_well_typed cx0 /\
          accounts_well_typed st0.accounts /\ functions_well_typed cx0 /\
          call_evaluation_safe cx0 (int_calls_exprs es0) /\
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
          env_consistent env1 cx0 st0 /\ state_well_typed st0 /\
          context_well_typed cx0 /\ accounts_well_typed st0.accounts /\
          functions_well_typed cx0 /\
          call_evaluation_safe cx0 (int_calls_stmts body0) /\
          eval_stmts cx0 body0 st0 = (res0,st0') ==> _`
    (mk_asm "body_ih") >>
  MATCH_MP_TAC (Q.SPECL [`cx`, `env`, `st`, `res`, `st'`, `v16`,
                         `src_id_opt`, `fn`, `es`, `v17`]
    intcall_expr_sound_from_generated_ih) >>
  rpt conj_tac >>
  (asm "actual_ih" (fn th => MATCH_ACCEPT_TAC th) ORELSE
   asm "default_ih" (fn th => MATCH_ACCEPT_TAC th) ORELSE
   asm "body_ih" (fn th => MATCH_ACCEPT_TAC th) ORELSE
   first_assum ACCEPT_TAC)
QED

(* ===== External and special call Resume blocks ===== *)

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]:
  rpt gen_tac >> strip_tac >>
  drule extcall_call_evaluation_safe_args >> strip_tac >>
  qpat_x_assum `well_typed_expr env (Call _ (ExtCall _ _) _ _)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  Cases_on `eval_exprs cx es st` >>
  rename1 `eval_exprs cx es st = (args_res,args_st)` >>
  qpat_x_assum `!env0 st0 res0 st0'.
    well_typed_exprs env0 es /\ _ ==> _` drule_all >> strip_tac >>
  Cases_on `args_res`
  >- (
    qpat_x_assum `case INL x of INL vs => exprs_runtime_typed env es vs | INR v1 => T` mp_tac >>
    rewrite_tac[sum_case_def] >> BETA_TAC >> strip_tac >>
    qpat_x_assum `v15 = ret_type` SUBST_ALL_TAC >>
    Cases_on `is_static'`
    >- suspend "Expr_Call_ExtCall_result_static" >>
    suspend "Expr_Call_ExtCall_result_nonstatic") >>
  first_x_assum kall_tac >>
  drule_all eval_extcall_args_error_any_call_ty_result_eq >>
  strip_tac >>
  qpat_x_assum `res = INR y` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `st' = args_st` (fn th => rewrite_tac[th]) >>
  conj_tac >- qpat_x_assum `state_well_typed args_st` ACCEPT_TAC >>
  conj_tac >- qpat_x_assum `env_consistent env cx args_st` ACCEPT_TAC >>
  conj_tac >- qpat_x_assum `accounts_well_typed args_st.accounts` ACCEPT_TAC >>
  conj_tac >- (
    qpat_x_assum `no_type_error_result (INR y)` mp_tac >>
    pure_rewrite_tac[no_type_error_result_def] >>
    rpt strip_tac >>
    first_x_assum (qspec_then `msg` mp_tac) >>
    qpat_x_assum `INR y = INR (Error (TypeError msg))` mp_tac >>
    rewrite_tac[sumTheory.INR_11]) >>
  rewrite_tac[sum_case_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_static]:
  rpt gen_tac >>
  qpat_x_assum `if T then _ else _` mp_tac >>
  pure_rewrite_tac[boolTheory.COND_CLAUSES] >> strip_tac >>
  drule_all extcall_static_args_runtime_typed_dest >> strip_tac >>
  `x <> []` by (drule_all extcall_static_args_runtime_typed_nonempty >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       type_check_def, check_def, assert_def, return_def, raise_def,
                       lift_option_type_def, lift_option_def,
                       get_accounts_def, get_transient_storage_def,
                       update_accounts_def, update_transient_def,
                       no_type_error_result_def] >>
  qpat_assum `eval_exprs cx es st = (INL x,args_st)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[] >>
  asm_rewrite_tac[] >>
  simp_tac(srw_ss()++boolSimps.LET_ss)[return_def] >>
  Cases_on `build_ext_calldata (get_tenv cx) func_name arg_types (TL x)` >>
  rewrite_tac[return_def, raise_def]
  >- (strip_tac >> suspend "Expr_Call_ExtCall_static_calldata_error") >>
  Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >>
  rewrite_tac[return_def, raise_def]
  >- (strip_tac >> suspend "Expr_Call_ExtCall_static_empty_code_error") >>
  simp_tac(srw_ss())[return_def,get_accounts_def,assert_def,
                     get_transient_storage_def,raise_def,bind_def] >>
  asm_rewrite_tac[] >> simp_tac(srw_ss())[] >>
  Cases_on `run_ext_call cx.txn.target target_addr x' NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)`
  >- suspend "Expr_Call_ExtCall_static_run_none" >>
  simp_tac(srw_ss())[return_def] >>
  qmatch_assum_rename_tac`_ = SOME pr` >>
  PairCases_on`pr` >>
  simp_tac(srw_ss())[assert_def,bind_def] >>
  reverse IF_CASES_TAC >>
  simp_tac(srw_ss())[] >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> simp[] ) >>
  simp_tac(srw_ss())[update_accounts_def,update_transient_def,return_def] >>
  qmatch_abbrev_tac`GG` >>
  first_x_assum drule >>
  simp[type_check_def, check_def, assert_def, raise_def, return_def,
       lift_option_type_def, lift_option_def, get_accounts_def,
       get_transient_storage_def, update_accounts_def, update_transient_def] >>
  disch_then drule >>
  disch_then(qspec_then`args_st`mp_tac) >>
  simp[raise_def, return_def] >>
  strip_tac >>
  unabbrev_all_tac >>
  `accounts_well_typed pr2` by (
    drule_all run_ext_call_accounts_well_typed >>
    simp[]) >>
  `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
  `runtime_consistent env cx
     (args_st with logs := args_st.logs ++ pr4)` by
    metis_tac[runtime_consistent_logs_append] >>
  `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv] >>
  qpat_x_assum `get_tenv cx = env.type_defs` (fn th => rewrite_tac[th]) >>
  strip_tac >>
  `state_well_typed st' /\ env_consistent env cx st' /\
   accounts_well_typed st'.accounts /\ no_type_error_result res /\
   case res of
   | INL tv => expr_result_typed env (Call ret_type (ExtCall T (func_name,arg_types,ret_type)) es drv) tv
   | INR v1 => T` suffices_by simp[no_type_error_result_def] >>
  qspecl_then [`env`, `cx`, `es`, `T`, `func_name`, `arg_types`, `ret_type`,
               `drv`, `pr1`, `args_st with logs := args_st.logs ++ pr4`,
               `pr2`, `pr3`, `res`, `st'`]
    mp_tac extcall_after_state_update_tail_sound_cond_driver_ih >>
  disch_then irule >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (pop_assum mp_tac >>
                simp[append_logs_def, return_def]) >>
  conj_tac >- (
    rpt strip_tac >>
    `call_evaluation_safe cx (int_calls_expr (THE drv))` by
      (qpat_x_assum `IS_SOME drv` mp_tac >>
       Cases_on `drv` >> simp[] >>
       drule extcall_call_evaluation_safe_driver >> simp[]) >>
    `append_logs pr4
       (args_st with <|accounts := pr2; tStorage := pr3|>) =
       (INL (), args_st with
          <|accounts := pr2; tStorage := pr3;
            logs := args_st.logs ++ pr4|>)` by
      simp[append_logs_def, return_def] >>
    first_x_assum drule_all >>
    strip_tac >>
    qpat_x_assum `well_typed_expr env0 (THE drv) ==> _` mp_tac >>
    simp[]) >>
  rpt conj_tac >>
  first_assum ACCEPT_TAC
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_calldata_error]:
  RESUME_TAC >>
  `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv] >>
  drule_all extcall_static_args_runtime_typed_tail >> strip_tac >>
  drule_all_then (qspec_then `func_name` strip_assume_tac)
    build_ext_calldata_typed >>
  qpat_x_assum `get_tenv cx = env.type_defs` (fn tenv_eq =>
    qpat_x_assum `build_ext_calldata (get_tenv cx) _ _ _ = NONE` (fn none_eq =>
      assume_tac (REWRITE_RULE [tenv_eq] none_eq))) >>
  `F` by
    (qpat_x_assum `build_ext_calldata env.type_defs _ _ _ = NONE` mp_tac >>
     qpat_x_assum `build_ext_calldata env.type_defs _ _ _ = SOME _`
       (fn th => rewrite_tac[th]) >>
     simp[]) >>
  simp[]
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_empty_code_error]:
  RESUME_TAC >>
  qpat_x_assum `(case (INL x,args_st) of _ => _) = (res,st')` mp_tac >>
  qpat_assum `x <> []` (fn th => rewrite_tac[th]) >>
  qpat_assum `dest_AddressV (HD x) = SOME target_addr` (fn th => rewrite_tac[th]) >>
  qpat_assum `build_ext_calldata (get_tenv cx) func_name arg_types (TL x) = SOME x'` (fn th => rewrite_tac[th]) >>
  qpat_assum `NULL (lookup_account target_addr args_st.accounts).code` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[pairTheory.pair_case_thm, sumTheory.sum_case_def,
                   bind_def, return_def, raise_def,
                   check_def, lift_option_type_def, lift_option_def,
                   assert_def, get_accounts_def,
                   LET_THM, boolTheory.COND_CLAUSES] >>
  BETA_TAC >> strip_tac >>
  qpat_x_assum `!s'' vs t s'³' x t' s'⁴' target_addr t'' s'⁵' value_opt arg_vals t'³' tenv s'⁶' calldata t'⁴' s'⁷' accounts t'⁵' s'⁸' x' t'⁶' s'⁹' tStorage t'⁷' txParams caller s'¹⁰' result t'⁸' success returnData accounts' tStorage' s'¹¹' x'' t'⁹' s'¹²' x'³' t'¹⁰' s'¹³' x'⁴' t'¹¹'. _` kall_tac >>
  qpat_x_assum `(case if x <> [] then _ else _ of _ => _) = (res,st')` mp_tac >>
  qpat_assum `x <> []` (fn th => rewrite_tac[th]) >>
  qpat_assum `dest_AddressV (HD x) = SOME target_addr` (fn th => rewrite_tac[th]) >>
  qpat_assum `build_ext_calldata (get_tenv cx) func_name arg_types (TL x) = SOME x'` (fn th => rewrite_tac[th]) >>
  qpat_assum `NULL (lookup_account target_addr args_st.accounts).code` (fn th => rewrite_tac[th]) >>
  disch_then (assume_tac o SIMP_RULE (srw_ss())
    [pairTheory.pair_case_thm, sumTheory.sum_case_def,
     bind_def, return_def, raise_def, assert_def, get_accounts_def,
     boolTheory.COND_CLAUSES]) >>
  qpat_x_assum `(case return target_addr args_st of _ => _) = (res,st')` mp_tac >>
  simp[no_type_error_result_def, pairTheory.pair_case_thm, sumTheory.sum_case_def,
       bind_def, return_def, raise_def, assert_def, boolTheory.COND_CLAUSES] >>
  strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_static_run_none]:
  qpat_assum `x <> []` (fn th => rewrite_tac[th]) >>
  qpat_assum `dest_AddressV (HD x) = SOME target_addr` (fn th => rewrite_tac[th]) >>
  qpat_assum `build_ext_calldata (get_tenv cx) func_name arg_types (TL x) = SOME x'` (fn th => rewrite_tac[th]) >>
  qpat_assum `~NULL (lookup_account target_addr args_st.accounts).code` (fn th => rewrite_tac[th]) >>
  qpat_assum `run_ext_call cx.txn.target target_addr x' NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn) = NONE` (fn th => rewrite_tac[th]) >>
  pure_rewrite_tac[pairTheory.pair_case_thm, sumTheory.sum_case_def,
                   bind_def, return_def, raise_def,
                   check_def, lift_option_type_def, lift_option_def,
                   assert_def, get_accounts_def, get_transient_storage_def,
                   LET_THM, boolTheory.COND_CLAUSES] >>
  BETA_TAC >> strip_tac >>
  qpat_x_assum `!s'' vs t s'³' x t' s'⁴' target_addr t'' s'⁵' value_opt arg_vals t'³' tenv s'⁶' calldata t'⁴' s'⁷' accounts t'⁵' s'⁸' x' t'⁶' s'⁹' tStorage t'⁷' txParams caller s'¹⁰' result t'⁸' success returnData accounts' tStorage' s'¹¹' x'' t'⁹' s'¹²' x'³' t'¹⁰' s'¹³' x'⁴' t'¹¹'. _` kall_tac >>
  qpat_x_assum `(case if x <> [] then _ else _ of _ => _) = (res,st')` mp_tac >>
  qpat_assum `x <> []` (fn th => rewrite_tac[th]) >>
  qpat_assum `dest_AddressV (HD x) = SOME target_addr` (fn th => rewrite_tac[th]) >>
  qpat_assum `build_ext_calldata (get_tenv cx) func_name arg_types (TL x) = SOME x'` (fn th => rewrite_tac[th]) >>
  qpat_assum `~NULL (lookup_account target_addr args_st.accounts).code` (fn th => rewrite_tac[th]) >>
  qpat_assum `run_ext_call cx.txn.target target_addr x' NONE args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn) = NONE` (fn th => rewrite_tac[th]) >>
  disch_then (assume_tac o SIMP_RULE (srw_ss())
    [pairTheory.pair_case_thm, sumTheory.sum_case_def,
     bind_def, return_def, raise_def, assert_def, get_accounts_def,
     get_transient_storage_def, lift_option_def, boolTheory.COND_CLAUSES]) >>
  simp[no_type_error_result_def, pairTheory.pair_case_thm, sumTheory.sum_case_def,
       bind_def, return_def, raise_def, assert_def, get_transient_storage_def,
       lift_option_def, boolTheory.COND_CLAUSES] >>
  strip_tac >> gvs[]
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result_nonstatic]:
  rpt gen_tac >>
  qpat_x_assum `if F then _ else _` mp_tac >>
  pure_rewrite_tac[boolTheory.COND_CLAUSES] >> strip_tac >>
  drule_all extcall_nonstatic_args_runtime_typed_dest >> strip_tac >>
  `x <> [] /\ TL x <> []` by (drule_all extcall_nonstatic_args_runtime_typed_nonempty >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                       type_check_def, check_def, assert_def, return_def, raise_def,
                       lift_option_type_def, lift_option_def,
                       get_accounts_def, get_transient_storage_def,
                       update_accounts_def, update_transient_def] >>
  qpat_assum `eval_exprs cx es st = (INL x,args_st)` (fn th => rewrite_tac[th]) >>
  simp_tac(srw_ss())[] >>
  asm_rewrite_tac[] >>
  simp_tac(srw_ss()++boolSimps.LET_ss)[return_def] >>
  Cases_on `build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL x))` >>
  rewrite_tac[return_def, raise_def]
  >- (strip_tac >> suspend "Expr_Call_ExtCall_nonstatic_calldata_error") >>
  Cases_on `NULL (lookup_account target_addr args_st.accounts).code` >>
  rewrite_tac[return_def, raise_def]
  >- (strip_tac >> suspend "Expr_Call_ExtCall_nonstatic_empty_code_error") >>
  simp_tac(srw_ss())[return_def,get_accounts_def,assert_def,
                     get_transient_storage_def,raise_def,bind_def] >>
  asm_rewrite_tac[] >> simp_tac(srw_ss())[] >>
  Cases_on `run_ext_call cx.txn.target target_addr x' (SOME amount) args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >>
  rewrite_tac[return_def, raise_def]
  >- (strip_tac >> suspend "Expr_Call_ExtCall_nonstatic_run_none") >>
  qmatch_assum_rename_tac`_ = SOME pr` >>
  PairCases_on`pr` >>
  simp_tac(srw_ss())[assert_def,bind_def,return_def] >>
  reverse IF_CASES_TAC >>
  simp_tac(srw_ss())[] >- (strip_tac >> suspend "Expr_Call_ExtCall_nonstatic_reverted") >>
  simp_tac(srw_ss())[update_accounts_def,update_transient_def,return_def] >>
  strip_tac >> suspend "Expr_Call_ExtCall_nonstatic_success"
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_calldata_error]:
  RESUME_TAC >>
  `get_tenv cx = env.type_defs` by metis_tac[env_consistent_get_tenv] >>
  drule_all extcall_nonstatic_args_runtime_typed_tail >> strip_tac >>
  drule_all_then (qspec_then `func_name` strip_assume_tac)
    build_ext_calldata_typed >>
  qpat_x_assum `get_tenv cx = env.type_defs` (fn tenv_eq =>
    qpat_x_assum `build_ext_calldata (get_tenv cx) _ _ _ = NONE` (fn none_eq =>
      assume_tac (REWRITE_RULE [tenv_eq] none_eq))) >>
  `F` by
    (qpat_x_assum `build_ext_calldata env.type_defs _ _ _ = NONE` mp_tac >>
     qpat_x_assum `build_ext_calldata env.type_defs _ _ _ = SOME _`
       (fn th => rewrite_tac[th]) >>
     simp[]) >>
  simp[]
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_empty_code_error]:
  RESUME_TAC >>
  qpat_x_assum `!s'' vs t. _` kall_tac >>
  qpat_x_assum `(do accounts <- _; x <- _; _ od) args_st = (res,st')` mp_tac >>
  simp[bind_def, return_def, raise_def, assert_def, get_accounts_def,
       pairTheory.pair_case_thm, sumTheory.sum_case_def, boolTheory.COND_CLAUSES] >>
  strip_tac >>
  gvs[no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_run_none]:
  RESUME_TAC >>
  qpat_x_assum `!s'' vs t. _` kall_tac >>
  qpat_x_assum `(case (case NONE of NONE => _ | SOME v => _) args_st of _ => _) = (res,st')` mp_tac >>
  simp[bind_def, return_def, raise_def, assert_def,
       pairTheory.pair_case_thm, sumTheory.sum_case_def, boolTheory.COND_CLAUSES] >>
  strip_tac >>
  gvs[no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_reverted]:
  RESUME_TAC >>
  qpat_x_assum `!s'' vs t. _` kall_tac >>
  gvs[no_type_error_result_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_nonstatic_success]:
  RESUME_TAC >>
  qmatch_abbrev_tac`GG` >>
  first_x_assum drule >>
  simp[check_def, assert_def, raise_def, return_def, lift_option_type_def,
       lift_option_def, get_accounts_def, get_transient_storage_def,
       update_accounts_def, update_transient_def] >>
  strip_tac >>
  unabbrev_all_tac >>
  `accounts_well_typed pr2` by (
    drule_all run_ext_call_accounts_well_typed >>
    simp[]) >>
  `runtime_consistent env cx args_st` by simp[runtime_consistent_def] >>
  `runtime_consistent env cx
     (args_st with logs := args_st.logs ++ pr4)` by (
    qspecl_then [`env`, `cx`, `args_st`, `pr4`]
      mp_tac runtime_consistent_logs_append >>
    simp[]) >>
  `runtime_consistent env cx
     (args_st with <|accounts := pr2; tStorage := pr3|>)` by
    metis_tac[update_accounts_transient_runtime_consistent] >>
  `runtime_consistent env cx
     ((args_st with <|accounts := pr2; tStorage := pr3|>) with
        logs := args_st.logs ++ pr4)` by (
    qspecl_then [`env`, `cx`,
                 `args_st with <|accounts := pr2; tStorage := pr3|>`, `pr4`]
      mp_tac runtime_consistent_logs_append >>
    simp[]) >>
  `!err.
     (do
        assert T err;
        v <- return amount;
        return (SOME v, TL (TL x))
      od) args_st = (INL (SOME amount, TL (TL x)), args_st)` by
    (gen_tac >> EVAL_TAC) >>
  `!err.
     (case build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL x)) of
        NONE => raise err
      | SOME v => return v) args_st = (INL x', args_st)` by (
    gen_tac >>
    qpat_assum `build_ext_calldata (get_tenv cx) func_name arg_types (TL (TL x)) = SOME x'` (fn th => rewrite_tac[th]) >>
    simp[return_def]) >>
  Cases_on `pr1 = [] /\ IS_SOME drv`
  >- (
    qpat_x_assum `pr1 = [] /\ IS_SOME drv` strip_assume_tac >>
    qpat_x_assum `_ = (res,st')` mp_tac >>
    qpat_assum `pr1 = []` (fn th => rewrite_tac[th]) >>
    qpat_assum `IS_SOME drv` (fn th => rewrite_tac[th]) >>
    pure_rewrite_tac[append_logs_def, return_def,
                     pairTheory.pair_case_thm, sumTheory.sum_case_def,
                     boolTheory.COND_CLAUSES] >>
    strip_tac >>
    `well_typed_expr env (THE drv)` by metis_tac[well_typed_opt_THE] >>
    `call_evaluation_safe cx (int_calls_expr (THE drv))` by
      (qpat_x_assum `IS_SOME drv` mp_tac >>
       Cases_on `drv` >> simp[] >>
       drule extcall_call_evaluation_safe_driver >> simp[]) >>
    qpat_x_assum `!s1 t1 s2 value_opt arg_vals t2 s3 calldata t3 s4 s5 s6 t4
                     accounts tStorage emitted_logs s7 t5 env0 st0 res0 st1. _`
      (qspecl_then [`args_st`, `args_st`, `args_st`, `SOME amount`,
                    `TL (TL x)`, `args_st`, `args_st`, `x'`, `args_st`,
                    `args_st`, `args_st`, `args_st`, `args_st`, `pr2`, `pr3`,
                    `pr4`, `args_st with <|accounts := pr2; tStorage := pr3|>`,
                    `(args_st with <|accounts := pr2; tStorage := pr3|>) with
                       logs := args_st.logs ++ pr4`,
                    `env`, `(args_st with <|accounts := pr2; tStorage := pr3|>) with
                              logs := args_st.logs ++ pr4`,
                    `res`, `st'`] mp_tac) >>
    impl_tac >- (
      conj_tac >-
        simp[type_check_def, assert_def, bind_def, ignore_bind_def,
             return_def, raise_def, append_logs_def] >>
      conj_tac >- (
        qpat_assum `runtime_consistent env cx
          (args_st with <|logs := args_st.logs ++ pr4;
                         accounts := pr2; tStorage := pr3|>)` mp_tac >>
        pure_rewrite_tac[runtime_consistent_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >- (
        qpat_assum `runtime_consistent env cx
          (args_st with <|logs := args_st.logs ++ pr4;
                         accounts := pr2; tStorage := pr3|>)` mp_tac >>
        pure_rewrite_tac[runtime_consistent_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
      qpat_x_assum `_ = (res,st')` mp_tac >>
      simp[]) >>
    strip_tac >>
    qpat_x_assum `well_typed_expr env (THE drv) ==> _` mp_tac >>
    simp[] >> strip_tac >>
    `expr_type (THE drv) = ret_type` by (Cases_on `drv` >> gvs[] >> metis_tac[]) >>
    Cases_on `res` >> gvs[expr_result_typed_def, expr_runtime_typed_def, expr_type_def] >>
    metis_tac[well_typed_expr_not_hashmap_place]) >>
  qspecl_then [`env`, `cx`, `es`, `func_name`, `arg_types`, `ret_type`,
               `drv`, `args_st with logs := args_st.logs ++ pr4`,
               `pr1`, `pr2`, `pr3`, `res`, `st'`]
    mp_tac extcall_nonstatic_success_tail_sound_cond_driver_ih >>
  impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- metis_tac[] >>
    conj_tac >- (strip_tac >> metis_tac[]) >>
    qpat_x_assum `_ = (res,st')` mp_tac >>
    pure_rewrite_tac[append_logs_def, return_def,
                     pairTheory.pair_case_thm, sumTheory.sum_case_def] >>
    simp[]) >>
  simp[]
QED

Resume eval_all_type_sound_mutual[Expr_Call_Send]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule send_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ Send _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    qpat_x_assum `!s'' x t. type_check (LENGTH es = 2) "Send args" s'' = (INL x,t) ==> _` mp_tac >>
    simp[type_check_def, assert_def] >>
    disch_then (qspecl_then [`env`, `st`, `args_res`, `args_st`] mp_tac) >>
    simp[] >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      drule_all send_args_runtime_typed_dest >> strip_tac >> gvs[] >>
      Cases_on `transfer_value cx.txn.target toAddr amount args_st` >>
      rename1 `transfer_value cx.txn.target toAddr amount args_st = (transfer_res,transfer_st)` >>
      Cases_on `transfer_res` >> gvs[return_def, no_type_error_result_def]
      >- (
        `runtime_consistent env cx transfer_st` by (
          qspecl_then [`env`, `cx`, `cx.txn.target`, `toAddr`, `amount`, `args_st`]
            mp_tac transfer_value_runtime_consistent >>
          simp[runtime_consistent_def]) >>
        strip_tac >>
        gvs[runtime_consistent_def, expr_result_typed_def, expr_runtime_typed_def,
            expr_type_def, toplevel_value_typed_def, value_has_type_def,
            evaluate_type_def, is_HashMapRef_def]) >>
      `runtime_consistent env cx transfer_st` by (
        qspecl_then [`env`, `cx`, `cx.txn.target`, `toAddr`, `amount`, `args_st`]
          mp_tac transfer_value_runtime_consistent >>
        simp[runtime_consistent_def]) >>
      `!s. y <> Error (TypeError s)` by (
        gen_tac >>
        qspecl_then [`cx.txn.target`, `toAddr`, `amount`, `args_st`, `s`]
          mp_tac transfer_value_no_type_error >>
        simp[]) >>
      strip_tac >> gvs[runtime_consistent_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >>
  qpat_x_assum `type_place_expr env (Call _ Send _ _) = SOME vt` mp_tac >>
  simp[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawCallTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawcall_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (RawCallTarget _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      mp_tac raw_call_args_runtime_typed_dest >>
      impl_tac >- simp[] >>
      strip_tac >> gvs[] >>
      `LENGTH vs = 3` by (gvs[exprs_runtime_typed_def] >> metis_tac[listTheory.LIST_REL_LENGTH]) >>
      simp_tac(srw_ss())[bind_def, ignore_bind_def, check_def, assert_def,
                           return_def, raise_def, lift_option_def,
                           get_accounts_def, get_transient_storage_def,
                           update_accounts_def, update_transient_def] >>
      Cases_on `flags.rcf_is_delegate` >> gvs[return_def, raise_def, no_type_error_result_def] >>
      Cases_on `run_ext_call cx.txn.target target_addr data
                  (if flags.rcf_is_static then NONE else SOME amount)
                  args_st.accounts args_st.tStorage (vyper_to_tx_params cx.txn)` >>
      gvs[return_def, raise_def, no_type_error_result_def]
      >- (strip_tac >> gvs[]) >>
      PairCases_on `x` >> gvs[] >>
      `accounts_well_typed x2` by (drule_all run_ext_call_accounts_well_typed >> simp[]) >>
      strip_tac >> gvs[update_accounts_def, update_transient_def, bind_def, return_def] >>
      `runtime_consistent env cx (args_st with <|accounts := x2; tStorage := x3|>)` by
        metis_tac[update_accounts_transient_runtime_consistent, runtime_consistent_def] >>
      `runtime_consistent env cx
         ((args_st with <|accounts := x2; tStorage := x3|>) with
            logs := args_st.logs ++ x4)` by (
        qspecl_then [`env`, `cx`,
                     `args_st with <|accounts := x2; tStorage := x3|>`, `x4`]
          mp_tac runtime_consistent_logs_append >>
        simp[]) >>
      Cases_on `x0` >> Cases_on `flags.rcf_revert_on_failure` >>
      Cases_on `flags.rcf_max_outsize = 0` >>
      gvs[check_def, assert_def, bind_def, return_def, raise_def,
          append_logs_def, runtime_consistent_def, no_type_error_result_def,
          expr_result_typed_def, expr_runtime_typed_def, expr_type_def,
          toplevel_value_typed_def, value_has_type_def, raw_call_return_type_def,
          evaluate_type_def, is_HashMapRef_def] >>
      mp_tac (Q.SPEC `flags.rcf_max_outsize` (GEN_ALL raw_call_bytes_slot_size_bound)) >>
      impl_tac >- simp[] >>
      TRY strip_tac >>
      gvs[listTheory.LENGTH_TAKE_EQ, value_has_type_def, evaluate_type_def,
          raw_call_return_type_def] >>
      decide_tac) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawLog]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawlog_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ RawLog _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, push_log_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      mp_tac raw_log_args_runtime_typed_dest >> simp[] >> strip_tac >> gvs[] >>
      strip_tac >>
      qpat_x_assum `LENGTH (case topics of _ => _) <= 4` $
        mk_asm "topics_bound" >>
      asm "topics_bound" (fn th =>
        fs[th, type_check_def, bind_def, ignore_bind_def, assert_def,
           return_def]) >>
      qspecl_then [`env`, `cx`, `es`, `vs`, `args_st`, `topics`, `data`, `res`, `st'`, `bd`, `bd'`]
        mp_tac raw_log_tail_result_sound_simp >>
      asm "topics_bound" (fn th =>
        simp[th, type_check_def, bind_def, ignore_bind_def, assert_def,
             return_def, runtime_consistent_def])) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_RawRevert]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule rawrevert_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ RawRevert _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      `LENGTH vs = 1` by
        (gvs[exprs_runtime_typed_def] >>
         metis_tac[listTheory.LIST_REL_LENGTH]) >>
      qspecl_then [`env`, `cx`, `vs`, `args_st`] mp_tac raw_revert_tail_sound >>
      simp[type_check_def, bind_def, ignore_bind_def, assert_def, raise_def,
           return_def, no_type_error_result_def, runtime_consistent_def] >>
      strip_tac >> gvs[]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_SelfDestructTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule selfdestruct_call_evaluation_safe_args >> strip_tac >>
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
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      strip_tac >>
      qspecl_then [`env`, `cx`, `es`, `vs`, `args_st`, `res`, `st'`]
        mp_tac selfdestruct_tail_result_sound_simp >>
      simp[type_check_def, assert_def, runtime_consistent_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Expr_Call_CreateTarget]:
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (
    strip_tac >>
    drule create_call_evaluation_safe_args >> strip_tac >>
    qpat_x_assum `well_typed_expr env (Call _ (CreateTarget _ _ _) _ _)` mp_tac >>
    rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp_tac(srw_ss())[Once evaluate_def, bind_def, ignore_bind_def,
                         type_check_def, assert_def, return_def, raise_def,
                         lift_option_type_def, get_accounts_def, update_accounts_def] >>
    simp[] >>
    Cases_on `eval_exprs cx es st` >>
    rename1 `eval_exprs cx es st = (args_res,args_st)` >>
    first_x_assum drule_all >> strip_tac >>
    Cases_on `args_res` >> gvs[no_type_error_result_def]
    >- (
      rename1 `exprs_runtime_typed env es vs` >>
      strip_tac >>
      qspecl_then [`env`, `cx`, `es`, `vs`, `args_st`, `res`, `st'`,
                   `kind`, `has_salt`, `rof`]
        mp_tac create_tail_result_sound_simp >>
      simp[runtime_consistent_def]) >>
    strip_tac >> gvs[]) >>
  rpt strip_tac >> gvs[Once well_typed_expr_def]
QED

Resume eval_all_type_sound_mutual[Exprs_nil]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, return_def] >>
  strip_tac >>
  gvs[no_type_error_result_def, exprs_runtime_typed_def]
QED

Resume eval_all_type_sound_mutual[Exprs_cons]:
  rpt gen_tac >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_head >> strip_tac >>
  drule exprs_cons_call_evaluation_safe_tail >> strip_tac >>
  qpat_x_assum `well_typed_exprs env (e::es)` mp_tac >>
  rewrite_tac[Once well_typed_expr_def] >> strip_tac >>
  qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
  simp_tac(srw_ss())[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx e st` >>
  rename1 `eval_expr cx e st = (r1,st1)` >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `r1`
  >- (
    Cases_on `materialise cx x st1` >>
    rename1 `materialise cx x st1 = (mr,stm)` >>
    Cases_on `mr`
    >- (
      `stm = st1` by metis_tac[materialise_state] >> gvs[] >>
      Cases_on `eval_exprs cx es st1` >>
      rename1 `eval_exprs cx es st1 = (r2,st2)` >>
      first_x_assum drule_all >> strip_tac >>
      Cases_on `r2` >> gvs[no_type_error_result_def]
      >- (
        strip_tac >> gvs[exprs_runtime_typed_def, expr_result_typed_def,
          expr_runtime_typed_def] >>
        drule_at(Pat`materialise`) materialise_preserves_value_type >>
        simp[] >> strip_tac >>
        qexists_tac `tv::tvs` >> simp[] >>
        metis_tac[evaluate_type_well_formed_type_value]) >>
      strip_tac >> gvs[]) >>
    strip_tac >> gvs[] >>
    `st' = st1` by metis_tac[materialise_state] >> gvs[] >>
    rw[no_type_error_result_def] >>
    drule_all expr_result_typed_materialise_no_type_error >> simp[]) >>
  strip_tac >> gvs[] >>
  rpt (pop_assum mp_tac) >> rpt strip_tac >>
  fs[no_type_error_result_def]
QED

Finalise eval_all_type_sound_mutual
