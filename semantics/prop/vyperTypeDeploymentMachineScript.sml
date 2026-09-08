(*
 * Machine-typing establishment for checked contract deployment.
 *
 * This theory composes typed initial immutables, deployment constants, and
 * constructor execution.  It is downstream of ordinary external-call machine
 * preservation so deployment and call reasoning remain separate.
 *
 * TOP-LEVEL:
 * - load_contract_establishes_machine_well_typed
 *)

Theory vyperTypeDeploymentMachine
Ancestors
  alist list rich_list vyperContext vyperState vyperInterpreter vyperTypeSystem vyperTypeInvariants
  vyperTypeInitialState vyperTypeEntryReadiness vyperTypeContract
  vyperTypeContractStaticMaps vyperTypeContractContext vyperTypeContractFunction
  vyperTypeBindArguments vyperTypeStmtSoundness vyperExprNoControl
  vyperTypeCallGraph vyperTypeCallGraphSoundness
  vyperTypeCallStackSoundness vyperTypeContractSoundness
  vyperTypeExternalCallMachine

val _ = Parse.hide "body";

(* ===== Deployment machine setup ===== *)

Theorem env_context_consistent_enter_deploy[local]:
  env_context_consistent env cx /\
  fn_sigs_consistent env.fn_sigs (cx with in_deploy := T) /\
  fn_sigs_declared_complete env.fn_sigs (cx with in_deploy := T) ==>
  env_context_consistent env (cx with in_deploy := T)
Proof
  rw[env_context_consistent_def] >>
  gvs[fn_sigs_consistent_def, toplevel_vtypes_complete_def,
      bare_globals_complete_def, bare_global_assignable_complete_def,
      flag_members_complete_def, get_module_code_def, get_tenv_def,
      current_module_def, lookup_var_slot_from_layout_def] >>
  metis_tac[]
QED

Theorem checked_deployment_env_context_consistent:
  check_contract T layouts addr mods = SOME deploy_art /\
  check_contract F layouts addr mods = SOME runtime_art /\
  ALOOKUP sources addr = SOME mods /\ tx.target = addr ==>
  env_context_consistent (artifact_env deploy_art mods NONE)
    (initial_evaluation_context sources layouts tx NONE with in_deploy := T)
Proof
  strip_tac >>
  `env_context_consistent (artifact_env runtime_art mods NONE)
     (initial_evaluation_context sources layouts tx NONE)` by
    (irule check_contract_env_context_consistent_initial_NONE >> simp[]) >>
  `fn_sigs_consistent deploy_art.cta_fn_sigs
     (initial_evaluation_context sources layouts tx NONE with in_deploy := T)` by
    (irule check_contract_fn_sigs_consistent_deploy >> simp[]) >>
  `fn_sigs_declared_complete deploy_art.cta_fn_sigs
     (initial_evaluation_context sources layouts tx NONE with in_deploy := T)` by
    (irule check_contract_fn_sigs_declared_complete_deploy >> simp[]) >>
  `deploy_art.cta_bare_globals = runtime_art.cta_bare_globals /\
   deploy_art.cta_bare_global_assignable = runtime_art.cta_bare_global_assignable /\
   deploy_art.cta_toplevel_vtypes = runtime_art.cta_toplevel_vtypes /\
   deploy_art.cta_flag_members = runtime_art.cta_flag_members` by
    (gvs[check_contract_def] >>
     metis_tac[build_contract_type_artifact_nonsig_mode_irrelevant]) >>
  gvs[env_context_consistent_def, artifact_env_def,
      get_module_code_def, get_tenv_def, current_module_def,
      initial_evaluation_context_def, lookup_var_slot_from_layout_def,
      fn_sigs_consistent_def, fn_sigs_declared_complete_def,
      toplevel_vtypes_complete_def, bare_globals_complete_def,
      bare_global_assignable_complete_def, flag_members_complete_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem checked_constructor_body_typing_package:
  check_contract T layouts addr mods = SOME art /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE fn Deploy ts = SOME (mut,nr,args,dflts,ret,body) ==>
  ?env_body env_after.
    env_body.current_src = NONE /\
    env_body.type_defs = type_env_all_modules mods /\
    env_body.fn_sigs = art.cta_fn_sigs /\
    env_body.bare_globals = art.cta_bare_globals /\
    env_body.bare_global_assignable = art.cta_bare_global_assignable /\
    env_body.toplevel_vtypes = art.cta_toplevel_vtypes /\
    env_body.flag_members = art.cta_flag_members /\
    type_stmts env_body ret body = SOME env_after /\
    (!id typ. MEM (id,typ) args ==>
       FLOOKUP env_body.var_types (string_to_num id) = SOME typ /\
       FLOOKUP env_body.var_assignable (string_to_num id) = SOME T) /\
    (!n ty. FLOOKUP env_body.var_types n = SOME ty ==>
       ?id. MEM (id,ty) args /\ n = string_to_num id) /\
    (!n b. FLOOKUP env_body.var_assignable n = SOME b ==>
       ?id typ. MEM (id,typ) args /\ n = string_to_num id /\ b = T)
Proof
  strip_tac >>
  drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[]
  >- (qexistsl [`artifact_env art mods NONE`, `artifact_env art mods NONE`] >>
      simp[artifact_env_def, Once type_stmt_def]) >>
  `check_function_body layouts addr mods art NONE mut nr args dflts ret body` by
    (irule check_contract_function_body_MEM >> metis_tac[]) >>
  gvs[check_function_body_def, optionTheory.IS_SOME_EXISTS] >>
  qexistsl [`function_entry_env art mods NONE args`, `x'`] >>
  gvs[function_entry_env_def, artifact_env_def,
      FOLDL_extend_local_args_static, params_ok_def] >>
  rpt conj_tac >>
  FIRST
    [rpt strip_tac >>
       drule_all FOLDL_extend_local_args_formal_lookup >> simp[],
     rpt strip_tac >>
       drule_all FOLDL_extend_local_args_var_types_range >> rw[] >> gvs[],
     rpt strip_tac >>
       drule_all FOLDL_extend_local_args_var_assignable_range >> rw[] >> gvs[]]
QED

Theorem checked_constructor_body_setup:
  check_contract T layouts tx.target mods = SOME deploy_art /\
  check_contract F layouts tx.target mods = SOME runtime_art /\
  ALOOKUP sources tx.target = SOME mods /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE
          with in_deploy := T) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  st.scopes = [scope] /\ state_well_typed st /\
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx st /\
  context_well_typed cx ==>
  ?env_body env_after.
    type_stmts env_body ret body = SOME env_after /\
    env_consistent env_body cx st /\
    context_well_typed cx /\ functions_well_typed cx /\
    state_well_typed st
Proof
  strip_tac >>
  `env_context_consistent (artifact_env deploy_art mods NONE) cx` by
    (gvs[] >> irule checked_deployment_env_context_consistent >> simp[]) >>
  `functions_well_typed cx` by
    (gvs[] >> irule check_contract_functions_well_typed_deploy >> simp[]) >>
  drule_all checked_constructor_body_typing_package >> strip_tac >>
  qexistsl [`env_body`,`env_after`] >> simp[] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env deploy_art mods NONE` >>
      gvs[artifact_env_def, get_tenv_def, initial_evaluation_context_def])
  >- (`(st with scopes := [scope]) = st` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`,`type_env_all_modules mods`,`vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[])
  >- (gvs[env_immutables_consistent_def, artifact_env_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
QED

Theorem checked_constructor_body_call_evaluation_safe:
  check_contract T layouts tx.target mods = SOME art /\
  ALOOKUP sources tx.target = SOME mods /\
  ALOOKUP mods NONE = SOME ts /\
  MEM (FunctionDecl Deploy mut nr raw tx.function_name args dflts ret body) ts ==>
  call_evaluation_safe
    (initial_evaluation_context sources layouts tx NONE with in_deploy := T)
    (int_calls_stmts body)
Proof
  rpt strip_tac >>
  `calls_follow_call_graph (contract_call_edges mods) (NONE,tx.function_name)
     (int_calls_stmts body)` by
    (rw[calls_follow_call_graph_def, EVERY_MEM, call_edge_rel_def] >>
     irule contract_call_edges_function >>
     qexistsl [`args`,`body`,`dflts`,`mut`,`nr`,`raw`,`ret`,`ts`,`Deploy`] >>
     simp[function_int_calls_def] >> metis_tac[ALOOKUP_MEM]) >>
  `(initial_evaluation_context sources layouts tx NONE with in_deploy := T) =
   ((initial_evaluation_context sources layouts tx NONE with in_deploy := T)
      with stk := [(NONE,tx.function_name)])` by
    simp[initial_evaluation_context_def] >>
  pop_assum SUBST1_TAC >>
  irule (INST_TYPE [``:'a`` |-> ``:num``]
    checked_contract_call_evaluation_safe_singleton) >>
  qexistsl [`art`,`layouts`,`mods`] >> simp[initial_evaluation_context_def]
QED

Theorem checked_constructor_body_preserves_components:
  check_contract T layouts tx.target mods = SOME deploy_art /\
  check_contract F layouts tx.target mods = SOME runtime_art /\
  ALOOKUP sources tx.target = SOME mods /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE
          with in_deploy := T) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  st.scopes = [scope] /\ state_well_typed st /\
  accounts_well_typed st.accounts /\
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx st /\
  context_well_typed cx /\ eval_stmts cx body st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all checked_constructor_body_setup >> strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[]
     >- (`(initial_evaluation_context sources layouts tx NONE
              with in_deploy := T) =
            ((initial_evaluation_context sources layouts tx NONE
                with in_deploy := T)
               with stk := [(NONE,tx.function_name)])` by
            simp[initial_evaluation_context_def] >>
         pop_assum SUBST1_TAC >>
         irule (INST_TYPE [``:'a`` |-> ``:num``]
           checked_contract_call_evaluation_safe_singleton) >>
         qexistsl [`deploy_art`,`layouts`,`mods`] >>
         simp[initial_evaluation_context_def, calls_follow_call_graph_def]) >>
     gvs[] >> irule checked_constructor_body_call_evaluation_safe >>
     qexistsl [`args`,`deploy_art`,`dflts`,`mods`,`mut`,`nr`,`raw`,`ret`,`ts`] >>
     simp[]) >>
  irule eval_stmts_preserves_state_and_accounts_well_typed >>
  qexistsl [`cx`,`env_body`,`env_after`,`res`,`ret`,`body`,`st`] >> simp[]
QED

Theorem checked_constructor_run_from_states_preserves_machine_well_typed:
  check_contract T layouts tx.target mods = SOME deploy_art /\
  check_contract F layouts tx.target mods = SOME runtime_art /\
  ALOOKUP sources tx.target = SOME mods /\ ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  cx = (initial_evaluation_context sources layouts tx NONE
          with in_deploy := T) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  body_st.scopes = [scope] /\ state_well_typed body_st /\
  accounts_well_typed body_st.accounts /\
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx body_st /\
  context_well_typed cx /\ eval_stmts cx body body_st = (res,body_st') /\
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) body_st' = (INL (),final_st) ==>
  machine_well_typed
    (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts final_st)
Proof
  strip_tac >>
  `state_well_typed body_st' /\ accounts_well_typed body_st'.accounts` by
    (irule checked_constructor_body_preserves_components >>
     qexistsl [`args`,`body`,`cx`,`deploy_art`,`dflts`,`layouts`,`mods`,`mut`,`nr`,
       `res`,`ret`,`runtime_art`,`scope`,`sources`,`body_st`,`ts`,`tx`,`vals`] >>
     simp[]) >>
  irule release_action_success_machine_well_typed >>
  qexistsl [`cx`,`mut = View \/ mut = Pure`,`nr`,`body_st'`] >> simp[]
QED

(* Checked constant evaluation establishes the complete immutable-readiness
 * boundary needed by the constructor's initial state. *)
Theorem checked_deployment_constants_establish_immutables_ready:
  check_contract F layouts target mods = SOME art /\
  ALOOKUP sources target = SOME mods /\ tx.target = target /\
  cx = (initial_evaluation_context sources layouts tx NONE
          with in_deploy := T) /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with immutables updated_by CONS (target,imms)) target mods = SOME am_c ==>
  immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes cx am_c.immutables
Proof
  strip_tac >>
  `(!src id ty.
      FLOOKUP art.cta_bare_globals (src,id) = SOME ty ==>
      IS_SOME (FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am_c.immutables target of SOME m => m | NONE => [])) id)) /\
   (!src id ty tv v.
      FLOOKUP art.cta_bare_globals (src,id) = SOME ty /\
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am_c.immutables target of SOME m => m | NONE => [])) id =
        SOME (tv,v) ==>
      evaluate_type (type_env_all_modules mods) ty = SOME tv)` by
    (drule deploy_constants_setup_bare_globals_ready >> strip_tac >>
     first_x_assum
       (qspecl_then [`tx`,`sources`,`imms`,`cx`,`am_c`,`am`] mp_tac) >>
     gvs[get_tenv_def, initial_evaluation_context_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `(!src id vt.
      FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype (type_env_all_modules mods) vt) /\
   (!src id ty.
      FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
      FLOOKUP art.cta_bare_globals (src,id) = NONE ==>
      ?ts is_transient typ id_str.
        get_module_code (initial_evaluation_context sources layouts tx src) src = SOME ts /\
        find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
        typ = ty /\
        IS_SOME (evaluate_type (type_env_all_modules mods) typ) /\
        IS_SOME (lookup_var_slot_from_layout
          (initial_evaluation_context sources layouts tx src)
          is_transient src id_str)) /\
   (!src id kt vt.
      FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
      ?ts is_transient id_str.
        get_module_code (initial_evaluation_context sources layouts tx src) src = SOME ts /\
        find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
        IS_SOME (lookup_var_slot_from_layout
          (initial_evaluation_context sources layouts tx src)
          is_transient src id_str))` by
    (irule check_contract_toplevel_vtypes_consistent_initial >> simp[]) >>
  rw[immutables_ready_def]
  >- (first_x_assum drule_all >> simp[initial_evaluation_context_def])
  >- (qpat_x_assum `!src id ty tv v. _`
        (qspecl_then [`src`,`id`,`ty`,`tv`,`v`] mp_tac) >>
      gvs[get_tenv_def, initial_evaluation_context_def])
  >- (Cases_on `FLOOKUP art.cta_bare_globals (src,id)` >> gvs[]
      >- (qpat_x_assum `!src id ty. FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP art.cta_bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
          simp[get_module_code_def, initial_evaluation_context_def] >>
          rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
      rename1 `FLOOKUP art.cta_bare_globals (src,id) = SOME bare_ty` >>
      drule check_contract_bare_globals_consistent_initial >>
      disch_then (qspecl_then [`tx`,`sources`,`src`,`id`,`bare_ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      rw[] >> gvs[get_module_code_def, initial_evaluation_context_def])
  >- (rpt strip_tac >>
      Cases_on `FLOOKUP art.cta_bare_globals (src,id)` >> gvs[]
      >- (qpat_x_assum `!src id ty. FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP art.cta_bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
          simp[get_module_code_def, initial_evaluation_context_def] >>
          rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
      rename1 `FLOOKUP art.cta_bare_globals (src,id) = SOME bare_ty` >>
      drule check_contract_bare_globals_consistent_initial >>
      disch_then (qspecl_then [`tx`,`sources`,`src`,`id`,`bare_ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      rw[] >> gvs[get_module_code_def, initial_evaluation_context_def])
  >> rpt strip_tac >>
     Cases_on `FLOOKUP art.cta_bare_globals (src,id)` >> gvs[]
     >- (qpat_x_assum `!src id ty. FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP art.cta_bare_globals (src,id) = NONE ==> _`
           (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
         simp[get_module_code_def, initial_evaluation_context_def] >>
         rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
     rename1 `FLOOKUP art.cta_bare_globals (src,id) = SOME bare_ty` >>
     `bare_ty = ty` by
       (drule check_contract_bare_globals_consistent_initial >>
        disch_then (qspecl_then [`tx`,`sources`,`src`,`id`,`bare_ty`] mp_tac) >>
        simp[get_module_code_def, initial_evaluation_context_def] >>
        rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
     gvs[get_tenv_def, initial_evaluation_context_def] >>
     qpat_x_assum `!src' id' ty' tv' v'. _`
       (qspecl_then [`src`,`id`,`bare_ty`,`tv`,`v`] mp_tac) >> simp[]
QED

Theorem checked_deployment_constants_establish_initial_env_immutables_consistent:
  check_contract T layouts target mods = SOME deploy_art /\
  check_contract F layouts target mods = SOME runtime_art /\
  ALOOKUP sources target = SOME mods /\ tx.target = target /\
  cx = (initial_evaluation_context sources layouts tx NONE
          with in_deploy := T) /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with immutables updated_by CONS (target,imms)) target mods = SOME am_c ==>
  env_immutables_consistent (artifact_env deploy_art mods NONE) cx
    (initial_state am_c [scope])
Proof
  strip_tac >>
  `deploy_art.cta_bare_globals = runtime_art.cta_bare_globals /\
   deploy_art.cta_bare_global_assignable = runtime_art.cta_bare_global_assignable /\
   deploy_art.cta_toplevel_vtypes = runtime_art.cta_toplevel_vtypes` by
    (gvs[check_contract_def] >>
     metis_tac[build_contract_type_artifact_nonsig_mode_irrelevant]) >>
  irule immutables_ready_env_immutables_consistent >>
  qexists `artifact_env runtime_art mods NONE` >>
  gvs[artifact_env_def] >>
  irule checked_deployment_constants_establish_immutables_ready >>
  qexistsl [`am`,`imms`,`layouts`,`mods`,`sources`,`tx.target`,`tx`] >> simp[]
QED

Theorem constructor_call_prefix_body_result_cases:
  (!exc st'. lock_action st = (INR exc,st') ==> no_control_exc exc) /\
  ((do
      lock_action;
      send_call_value mut cx;
      eval_stmts cx body
    od st) = (INL (),body_st') \/
   ?v. (do
         lock_action;
         send_call_value mut cx;
         eval_stmts cx body
       od st) = (INR (ReturnException v),body_st')) ==>
  ?lock_st body_st res.
    lock_action st = (INL (),lock_st) /\
    send_call_value mut cx lock_st = (INL (),body_st) /\
    eval_stmts cx body body_st = (res,body_st')
Proof
  rw[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs()] >>
  TRY (drule_all send_call_value_no_control_c53 >> gvs[no_control_exc_def]) >>
  gvs[no_control_exc_def]
QED

Theorem checked_constructor_prefix_run_preserves_machine_well_typed:
  check_contract T layouts target mods = SOME deploy_art /\
  check_contract F layouts target mods = SOME runtime_art /\
  ALOOKUP sources target = SOME mods /\ tx.target = target /\
  cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  installed_am = (am with immutables updated_by CONS (target,imms)) /\
  machine_well_typed installed_am /\ context_well_typed cx /\
  checked_deployment_constants_ready cx installed_am target mods /\
  evaluate_all_constants cx installed_am target mods = SOME am_c /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                      (mut = View \/ mut = Pure)
   else return ()) (initial_state am_c [scope]) = (INL (),lock_st) /\
  send_call_value mut cx lock_st = (INL (),body_st) /\
  eval_stmts cx body body_st = (res,body_st') /\
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) body_st' = (INL (),final_st) ==>
  machine_well_typed
    (abstract_machine_from_state am_c.sources am_c.exports am_c.layouts final_st)
Proof
  strip_tac >>
  `machine_well_typed am_c` by
    (gvs[checked_deployment_constants_ready_def] >>
     drule_all evaluate_all_constants_preserves_accounts >>
     gvs[machine_well_typed_def, deployment_constants_output_typed_def]) >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `body_st.scopes = [scope] /\ body_st.immutables = am_c.immutables /\
   state_well_typed body_st /\ accounts_well_typed body_st.accounts` by
    (irule call_lock_send_success_components >> simp[] >>
     qexistsl [`cx`,`lock_st`,`mut`,`nr`] >> simp[]) >>
  `env_immutables_consistent (artifact_env deploy_art mods NONE) cx
     (initial_state am_c [scope])` by
    (irule checked_deployment_constants_establish_initial_env_immutables_consistent >>
     qexistsl [`am`,`imms`,`layouts`,`runtime_art`,`sources`,`target`,`tx`] >> gvs[]) >>
  `env_immutables_consistent (artifact_env deploy_art mods NONE) cx body_st` by
    (irule (iffLR env_immutables_consistent_immutables_cong) >>
     qexists `initial_state am_c [scope]` >> simp[initial_state_def]) >>
  `ALL_DISTINCT (MAP (string_to_num o FST) args)` by
    (drule lookup_function_Deploy_SOME_cases >> strip_tac >> gvs[] >>
     `check_function_body layouts tx.target mods deploy_art NONE mut nr
        args dflts ret body` by
       (irule check_contract_function_body_MEM >> simp[] >>
        conj_tac >- (qexists `T` >> simp[]) >>
        qexistsl [`tx.function_name`,`raw`,`Deploy`] >> simp[]) >>
     gvs[check_function_body_def, params_ok_def]) >>
  irule checked_constructor_run_from_states_preserves_machine_well_typed >>
  qexistsl [`args`,`body`,`body_st`,`body_st'`,`cx`,`deploy_art`,`dflts`,`layouts`,
    `mods`,`mut`,`nr`,`res`,`ret`,`runtime_art`,`scope`,`sources`,`ts`,`tx`,`vals`] >>
  simp[]
QED

Theorem checked_constructor_call_success_preserves_machine_well_typed:
  check_contract T layouts target mods = SOME deploy_art /\
  check_contract F layouts target mods = SOME runtime_art /\
  ALOOKUP sources target = SOME mods /\ tx.target = target /\
  cx = (initial_evaluation_context sources layouts tx NONE with in_deploy := T) /\
  ALOOKUP mods NONE = SOME ts /\
  lookup_function NONE tx.function_name Deploy ts =
    SOME (mut,nr,args,dflts,ret,body) /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  installed_am = (am with immutables updated_by CONS (target,imms)) /\
  machine_well_typed installed_am /\ context_well_typed cx /\
  checked_deployment_constants_ready cx installed_am target mods /\
  call_external_function installed_am cx nr mut ts mods args dflts vals body ret =
    (INL v,am_out) ==>
  machine_well_typed am_out
Proof
  strip_tac >>
  drule checked_deployment_constants_ready_setup >> strip_tac >>
  `cx.in_deploy /\ cx.txn.target = target` by
    gvs[initial_evaluation_context_def] >>
  `evaluate_all_constants cx installed_am cx.txn.target mods = SOME am_c` by
    gvs[] >>
  drule_all call_external_function_deploy_success_cases >> strip_tac >>
  gvs[] >>
  `?lock_st body_st res.
      (if nr then
         case (initial_evaluation_context sources layouts tx NONE).nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock
             (initial_evaluation_context sources layouts tx NONE).txn.target slot
             (mut = View \/ mut = Pure)
       else return ()) (initial_state am_c [env]) = (INL (),lock_st) /\
      send_call_value mut
        (initial_evaluation_context sources layouts tx NONE with in_deploy := T)
        lock_st = (INL (),body_st) /\
      eval_stmts
        (initial_evaluation_context sources layouts tx NONE with in_deploy := T)
        body body_st = (res,st_body)` by
    (irule constructor_call_prefix_body_result_cases >>
     conj_tac
     >- (rpt strip_tac >> irule call_lock_action_no_control_c53 >>
         qexistsl
           [`initial_evaluation_context sources layouts tx NONE`,
            `mut = View \/ mut = Pure`,`nr`,
           `initial_state am_c [env]`,`st'`] >> first_assum ACCEPT_TAC) >>
     metis_tac[]) >>
  irule checked_constructor_prefix_run_preserves_machine_well_typed >>
  qexistsl [`am`,`args`,`body`,`body_st`,`st_body`,
    `initial_evaluation_context sources layouts tx NONE with in_deploy := T`,
    `deploy_art`,`dflts`,`imms`,
    `am with immutables updated_by CONS (tx.target,imms)`,
    `layouts`,`lock_st`,`mods`,`mut`,`nr`,`res`,`ret`,`runtime_art`,`env`,`sources`,
    `tx.target`,`ts`,`tx`,`vals ++ dflt_vs`] >>
  gvs[initial_evaluation_context_def]
QED

Theorem evaluate_all_constants_preserves_machine_static_components:
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  am_c.sources = am.sources /\ am_c.exports = am.exports /\
  am_c.layouts = am.layouts
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >> Induct_on `mods`
  >- rw[evaluate_all_constants_def] >>
  rpt gen_tac >> PairCases_on `h` >> rw[evaluate_all_constants_def] >>
  gvs[AllCaseEqs()] >> first_x_assum drule >>
  simp[merge_constants_def]
QED

Theorem deployment_initial_machine_well_typed:
  machine_well_typed am /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms ==>
  machine_well_typed
    (am with <| immutables updated_by CONS (addr,imms);
                exports updated_by CONS (addr,exps) |>)
Proof
  strip_tac >>
  gvs[machine_well_typed_def] >>
  metis_tac[initial_immutables_imms_well_typed]
QED

Theorem deployment_source_install_preserves_machine_well_typed:
  machine_well_typed am ==>
  machine_well_typed (am with sources updated_by CONS (addr,mods))
Proof
  simp[machine_well_typed_def]
QED

Theorem load_contract_establishes_machine_well_typed:
  machine_well_typed am /\
  check_contract T am.layouts tx.target mods = SOME deploy_art /\
  check_contract F am.layouts tx.target mods = SOME runtime_art /\
  ALOOKUP mods NONE = SOME ts /\
  context_well_typed
    (initial_evaluation_context ((tx.target,mods)::am.sources)
       am.layouts tx NONE with in_deploy := T) /\
  (!imms.
     initial_immutables (type_env_all_modules mods) mods = SOME imms ==>
     checked_deployment_constants_ready
       (initial_evaluation_context ((tx.target,mods)::am.sources)
          am.layouts tx NONE with in_deploy := T)
       (am with <|immutables updated_by CONS (tx.target,imms);
                  exports updated_by CONS (tx.target,exps)|>)
       tx.target mods) /\
  load_contract am tx mods exps = INL am_deployed ==>
  machine_well_typed am_deployed
Proof
  strip_tac >>
  drule load_contract_success_cases >> strip_tac >> gvs[] >>
  `machine_well_typed
     (am with <|immutables updated_by CONS (tx.target,imms);
                exports updated_by CONS (tx.target,exps)|>)` by
    (irule deployment_initial_machine_well_typed >> simp[] >>
     qexists `mods` >> simp[]) >>
  `machine_well_typed am_ctor` by
    (irule checked_constructor_call_success_preserves_machine_well_typed >>
     qexistsl
       [`am with exports updated_by CONS (tx.target,exps)`,`args`,`body`,
        `initial_evaluation_context ((tx.target,mods)::am.sources)
           am.layouts tx NONE with in_deploy := T`,
        `deploy_art`,`dflts`,`imms`,
        `am with <|immutables updated_by CONS (tx.target,imms);
                   exports updated_by CONS (tx.target,exps)|>`,
        `am.layouts`,`mods`,`mut`,`nr`,`ret`,`runtime_art`,
        `(tx.target,mods)::am.sources`,`tx.target`,`ts`,`tx`,`v`,`tx.args`] >>
     gvs[]) >>
  irule deployment_source_install_preserves_machine_well_typed >> simp[]
QED

val _ = export_theory();
