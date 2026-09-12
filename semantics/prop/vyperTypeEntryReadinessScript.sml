(*
 * Reusable input/setup readiness predicates for checked external entry.
 *
 * TOP-LEVEL:
 * - deployment_constants_output_typed
 * - checked_deployment_constants_ready
 * - provided_args_typed
 * - checked_defaults_ready
 * - checked_call_inputs_ready
 * - checked_external_call_inputs_ready
 * - checked_deployment_constants_ready_setup
 *)

Theory vyperTypeEntryReadiness
Ancestors
  list rich_list finite_map option pair
  vyperAST vyperValue vyperTyping vyperState vyperInterpreter vyperContext
  vyperTypeSystem vyperTypeInvariants vyperTypeExprSoundness
  vyperTypeInitialState vyperTypeEvalSoundness vyperTypeExprResult vyperTypeValues
  vyperTypeBindArguments

(* ===== Deployment Constant Readiness ===== *)

(* Every declared deployment constant is present in the resulting machine with
 * its evaluated declared type and a value of that type. *)
Definition deployment_constants_output_typed_def:
  deployment_constants_output_typed tenv addr mods (am:abstract_machine) <=>
    EVERY (\(stored_addr, imms). imms_well_typed imms) am.immutables /\
    !src ts vis e id ty init.
      MEM (src,ts) mods /\
      MEM (VariableDecl vis (Constant e) id ty init) ts ==>
      ?tv v.
        FLOOKUP
          (get_source_immutables src
            (case ALOOKUP am.immutables addr of
             | SOME imms => imms
             | NONE => []))
          (string_to_num id) = SOME (tv,v) /\
        evaluate_type tenv ty = SOME tv /\
        value_has_type tv v
End

(* Setup readiness is invocation-specific.  It records both that deployment
 * constant evaluation succeeds and that every successful output has the
 * public output-typing property above. *)
Definition checked_deployment_constants_ready_def:
  checked_deployment_constants_ready cx am addr mods <=>
    IS_SOME (evaluate_all_constants cx am addr mods) /\
    !am_c.
      evaluate_all_constants cx am addr mods = SOME am_c ==>
      deployment_constants_output_typed (get_tenv cx) addr mods am_c
End

Theorem evaluate_all_constants_preserves_accounts:
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  am_c.accounts = am.accounts
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >> Induct_on `mods`
  >- rw[evaluate_all_constants_def] >>
  rpt gen_tac >> PairCases_on `h` >> rw[evaluate_all_constants_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[merge_constants_def]
QED

Theorem checked_deployment_constants_ready_setup:
  checked_deployment_constants_ready cx am addr mods ==>
  ?am_c.
    evaluate_all_constants cx am addr mods = SOME am_c /\
    deployment_constants_output_typed (get_tenv cx) addr mods am_c
Proof
  rw[checked_deployment_constants_ready_def, IS_SOME_EXISTS] >>
  metis_tac[]
QED

Theorem checked_deployment_constants_establish_machine_well_typed:
  machine_well_typed am /\
  checked_deployment_constants_ready cx am addr mods ==>
  ?am_c.
    evaluate_all_constants cx am addr mods = SOME am_c /\
    machine_well_typed am_c /\
    deployment_constants_output_typed (get_tenv cx) addr mods am_c
Proof
  strip_tac >>
  drule checked_deployment_constants_ready_setup >> strip_tac >>
  qexists_tac `am_c` >> simp[] >>
  rw[machine_well_typed_def] >-
    metis_tac[machine_well_typed_accounts,
              evaluate_all_constants_preserves_accounts] >>
  fs[deployment_constants_output_typed_def]
QED

(* ===== Default and Argument Readiness ===== *)

(* The externally supplied values type-check against the corresponding prefix
 * of the selected function's parameter list. *)
Definition provided_args_typed_def:
  provided_args_typed tenv (args:argument list) vals <=>
    args_values_typed tenv (TAKE (LENGTH vals) args) vals
End

(* The selected default suffix exists and evaluates successfully.  Typing of
 * its successful result is derived from checked-function expression soundness,
 * rather than included as an input premise. *)
Definition checked_defaults_ready_def:
  checked_defaults_ready cx am (args:argument list) dflts vals <=>
    LENGTH vals <= LENGTH args /\
    LENGTH args - LENGTH vals <= LENGTH dflts /\
    IS_SOME
      (evaluate_defaults cx am
        (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts))
End

Definition checked_call_inputs_ready_def:
  checked_call_inputs_ready tenv cx am args dflts vals <=>
    provided_args_typed tenv args vals /\
    checked_defaults_ready cx am args dflts vals
End

(* Public-call wrapper: resolve the selected external entry exactly as
 * call_external does, then require readiness for that entry's parameters and
 * defaults. Lookup failures need no input readiness because they return the
 * original machine without executing a body. *)
Definition checked_external_call_inputs_ready_def:
  checked_external_call_inputs_ready (am:abstract_machine) (tx:call_txn) <=>
    let src = find_function_module am tx.target tx.function_name in
    let cx = initial_evaluation_context am.sources am.layouts tx src in
    case ALOOKUP am.sources tx.target of
    | NONE => T
    | SOME mods =>
        !mut nr params dflts ret stmts.
          lookup_exported_function cx am tx.function_name =
            SOME (mut,nr,params,dflts,ret,stmts) ==>
          checked_call_inputs_ready
            (type_env_all_modules mods) cx am params dflts tx.args
End

(* Successful evaluation of a well-typed default list returns values of the
 * defaults' expression types.  Each default is evaluated from the same entry
 * machine state by evaluate_defaults. *)
Theorem evaluate_defaults_success_values_typed:
  well_typed_exprs env es /\
  env_consistent env cx (initial_state am [FEMPTY]) /\
  state_well_typed (initial_state am [FEMPTY]) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  (!e. MEM e es ==> call_evaluation_safe cx (int_calls_expr e)) /\
  evaluate_defaults cx am es = SOME vs ==>
  LIST_REL
    (\v e. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
                  value_has_type tv v)
    vs es
Proof
  qid_spec_tac `vs` >> Induct_on `es`
  >- simp[evaluate_defaults_def] >>
  gen_tac >> rpt strip_tac >>
  gvs[well_typed_expr_def, evaluate_defaults_def, AllCaseEqs()] >>
  Cases_on `eval_expr cx h (initial_state am [FEMPTY])` >> gvs[] >>
  `accounts_well_typed (initial_state am [FEMPTY]).accounts` by
    simp[initial_state_def] >>
  `call_evaluation_safe cx (int_calls_expr h)` by metis_tac[] >>
  drule_all (cj 8 eval_all_type_sound_mutual) >>
  simp[expr_result_typed_def, expr_runtime_typed_def,
       toplevel_value_typed_Value]
QED

Theorem checked_defaults_ready_success:
  checked_defaults_ready cx am args dflts vals ==>
  LENGTH vals <= LENGTH args /\
  LENGTH args - LENGTH vals <= LENGTH dflts /\
  ?dflt_vs.
    evaluate_defaults cx am
      (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) =
      SOME dflt_vs
Proof
  rw[checked_defaults_ready_def, IS_SOME_EXISTS]
QED

Theorem checked_defaults_ready_values_typed:
  checked_defaults_ready cx am args dflts vals /\
  well_typed_exprs env
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) /\
  env_consistent env cx (initial_state am [FEMPTY]) /\
  state_well_typed (initial_state am [FEMPTY]) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  (!e.
    MEM e (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) ==>
    call_evaluation_safe cx (int_calls_expr e)) ==>
  ?dflt_vs.
    evaluate_defaults cx am
      (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) =
      SOME dflt_vs /\
    LIST_REL
      (\v e. ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
                    value_has_type tv v)
      dflt_vs
      (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts)
Proof
  rw[checked_defaults_ready_def, IS_SOME_EXISTS] >>
  `LENGTH dflts - (LENGTH args - LENGTH vals) =
   LENGTH vals + LENGTH dflts - LENGTH args` by decide_tac >>
  gvs[] >>
  drule_all evaluate_defaults_success_values_typed >> simp[]
QED

Theorem provided_args_defaults_bind_arguments:
  provided_args_typed tenv params vals /\
  (!arg. MEM arg params ==>
    ?tv. evaluate_type tenv (SND arg) = SOME tv) /\
  LIST_REL
    (\v e. ?tv. evaluate_type tenv (expr_type e) = SOME tv /\
                  value_has_type tv v)
    dflt_vs needed_dflts /\
  MAP expr_type needed_dflts = MAP SND (DROP (LENGTH vals) params) /\
  LENGTH vals + LENGTH needed_dflts = LENGTH params ==>
  ?scope.
    bind_arguments tenv params (vals ++ dflt_vs) = SOME scope /\
    args_values_typed tenv params (vals ++ dflt_vs)
Proof
  strip_tac >>
  `LENGTH dflt_vs = LENGTH needed_dflts` by
    metis_tac[LIST_REL_LENGTH] >>
  `LENGTH (vals ++ dflt_vs) = LENGTH params` by simp[] >>
  `!i. i < LENGTH params ==>
     ?tv. evaluate_type tenv (SND (EL i params)) = SOME tv /\
          value_has_type tv (EL i (vals ++ dflt_vs))` by (
    gen_tac >> strip_tac >> Cases_on `i < LENGTH vals`
    >- (qpat_x_assum `provided_args_typed _ _ _` mp_tac >>
        simp[provided_args_typed_def, args_values_typed_def] >> strip_tac >>
        `MEM (EL i params) params` by
          (simp[listTheory.MEM_EL] >> qexists_tac `i` >> simp[]) >>
        qpat_x_assum `!arg. MEM arg params ==> _` drule >> strip_tac >>
        qexists_tac `tv` >> simp[rich_listTheory.EL_APPEND1] >>
        first_x_assum irule >> simp[rich_listTheory.EL_TAKE]) >>
    qpat_x_assum `LIST_REL _ dflt_vs needed_dflts` mp_tac >>
    simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
    first_x_assum (qspec_then `i - LENGTH vals` mp_tac) >>
    impl_tac >- decide_tac >> strip_tac >>
    `expr_type (EL (i - LENGTH vals) needed_dflts) = SND (EL i params)` by (
      qpat_x_assum `MAP expr_type needed_dflts = _` mp_tac >>
      simp[listTheory.LIST_EQ_REWRITE, listTheory.EL_MAP, listTheory.EL_DROP] >>
      metis_tac[]) >>
    qexists_tac `tv` >>
    gvs[rich_listTheory.EL_APPEND2]) >>
  `?scope. bind_arguments tenv params (vals ++ dflt_vs) = SOME scope` by
    metis_tac[bind_arguments_succeeds_stmt] >>
  qexists_tac `scope` >> simp[args_values_typed_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem checked_external_call_inputs_ready_selected:
  checked_external_call_inputs_ready am tx /\
  ALOOKUP am.sources tx.target = SOME mods /\
  src = find_function_module am tx.target tx.function_name /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  lookup_exported_function cx am tx.function_name =
    SOME (mut,nr,params,dflts,ret,stmts) ==>
  checked_call_inputs_ready
    (type_env_all_modules mods) cx am params dflts tx.args
Proof
  rw[checked_external_call_inputs_ready_def] >> gvs[]
QED

Theorem checked_call_inputs_ready_bind_arguments:
  checked_call_inputs_ready tenv cx am params dflts vals /\
  env.type_defs = tenv /\
  well_typed_exprs env
    (DROP (LENGTH dflts - (LENGTH params - LENGTH vals)) dflts) /\
  env_consistent env cx (initial_state am [FEMPTY]) /\
  state_well_typed (initial_state am [FEMPTY]) /\
  context_well_typed cx /\
  accounts_well_typed am.accounts /\
  functions_well_typed cx /\
  (!e. MEM e (DROP (LENGTH dflts - (LENGTH params - LENGTH vals)) dflts) ==>
       call_evaluation_safe cx (int_calls_expr e)) /\
  (!arg. MEM arg params ==> ?tv. evaluate_type tenv (SND arg) = SOME tv) /\
  MAP expr_type dflts =
    MAP SND (DROP (LENGTH params - LENGTH dflts) params) ==>
  ?dflt_vs scope.
    evaluate_defaults cx am
      (DROP (LENGTH dflts - (LENGTH params - LENGTH vals)) dflts) =
      SOME dflt_vs /\
    bind_arguments tenv params (vals ++ dflt_vs) = SOME scope /\
    args_values_typed tenv params (vals ++ dflt_vs)
Proof
  strip_tac >>
  gvs[checked_call_inputs_ready_def] >>
  drule_all checked_defaults_ready_values_typed >> strip_tac >>
  qabbrev_tac `needed = DROP (LENGTH dflts - (LENGTH params - LENGTH vals)) dflts` >>
  `LENGTH vals <= LENGTH params /\
   LENGTH params - LENGTH vals <= LENGTH dflts` by
    fs[checked_defaults_ready_def] >>
  `LENGTH dflts <= LENGTH params` by
    metis_tac[intcall_defaults_map_param_types_length_le] >>
  `MAP expr_type needed = MAP SND (DROP (LENGTH vals) params)` by (
    simp[Abbr`needed`, listTheory.MAP_DROP, rich_listTheory.DROP_DROP_T] >>
    `LENGTH params - LENGTH dflts +
       (LENGTH dflts - (LENGTH params - LENGTH vals)) = LENGTH vals` by
      decide_tac >> simp[]) >>
  `LENGTH vals + LENGTH needed = LENGTH params` by
    (simp[Abbr`needed`, listTheory.LENGTH_DROP] >> decide_tac) >>
  drule_all provided_args_defaults_bind_arguments >> strip_tac >>
  qexistsl [`dflt_vs`, `scope`] >> simp[Abbr`needed`]
QED

Theorem checked_call_inputs_ready_components:
  checked_call_inputs_ready tenv cx am args dflts vals ==>
  provided_args_typed tenv args vals /\
  checked_defaults_ready cx am args dflts vals
Proof
  simp[checked_call_inputs_ready_def]
QED

