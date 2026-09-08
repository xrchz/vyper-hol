(*
 * Final checked-contract type-soundness theorems.
 *
 * This theory owns the public transaction/runtime-readiness predicates and the
 * final deployment/readiness and checked external-call no-TypeError theorems.
 *)

Theory vyperTypeContractSoundness
Ancestors
  list rich_list arithmetic finite_map alist option pair patricia_casts
  vyperAST vyperValue vyperMisc vyperContext vyperState vyperInterpreter
  vyperTypeSystem vyperTypeContract vyperTypeInvariants vyperTypeValues vyperTypeBindArguments
  vyperTypeStmtSoundness vyperTypeInitialState vyperPureExpr vyperEvalPreservesScopes vyperEvalExprPreservesScopesDom
  vyperEvalPreservesImmutablesDom vyperScopePreservation vyperStatePreservation
  vyperExprNoControl vyperTypeEvalSoundness vyperTypeCallGraph
  vyperTypeCallGraphSoundness vyperTypeCallStackSoundness
  vyperTypeContractStaticMaps vyperTypeContractContext
  vyperTypeContractFunction vyperTypeContractGetter vyperTypeEntryReadiness
Libs
  wordsLib

val _ = Parse.hide "body";

(* ===== Public transaction and runtime-readiness predicates ===== *)

Definition call_tx_well_typed_def:
  call_tx_well_typed tx <=>
    tx.value < 2 ** 256 /\
    tx.time_stamp < 2 ** 256 /\
    tx.block_number < 2 ** 256 /\
    tx.blob_base_fee < 2 ** 256 /\
    tx.gas_price < 2 ** 256 /\
    tx.chain_id < 2 ** 256 /\
    tx.gas_limit < 2 ** 256 /\
    tx.base_fee < 2 ** 256 /\
    tx.prev_randao < 2 ** 256
End

Theorem call_tx_well_typed_empty_zero_witness:
  ?tx. tx.args = [] /\ tx.value = 0 /\ call_tx_well_typed tx
Proof
  qexists `empty_call_txn` >>
  simp[empty_call_txn_def, call_tx_well_typed_def]
QED

Theorem call_tx_well_typed_initial_context[local]:
  call_tx_well_typed tx ==>
  context_well_typed (initial_evaluation_context sources layouts tx src)
Proof
  rw[call_tx_well_typed_def, context_well_typed_def,
     initial_evaluation_context_def]
QED

Theorem call_tx_well_typed_initial_context_stk[local]:
  call_tx_well_typed tx ==>
  context_well_typed
    ((initial_evaluation_context sources layouts tx src) with stk := [(src,fn)])
Proof
  rw[call_tx_well_typed_def, context_well_typed_def,
     initial_evaluation_context_def]
QED

Theorem call_external_args_defaults_bind_typed[local]:
  evaluate_defaults cx am (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts) = SOME dflt_vs /\
  bind_arguments (type_env_all_modules all_mods) args (vals ++ dflt_vs) = SOME scope /\
  LIST_REL
    (\v arg. ?tv. evaluate_type (type_env_all_modules all_mods) (SND arg) = SOME tv /\
                   value_has_type tv v)
    (vals ++ dflt_vs) args ==>
  args_values_typed (type_env_all_modules all_mods) args (vals ++ dflt_vs)
Proof
  rw[args_values_typed_def]
  >- (imp_res_tac LIST_REL_LENGTH >> gvs[LENGTH_APPEND] >> decide_tac) >>
  imp_res_tac LIST_REL_LENGTH >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  simp[listTheory.LIST_REL_EL_EQN] >>
  strip_tac >>
  first_x_assum drule >>
  simp[]
QED

Definition checked_contract_runtime_ready_def:
  checked_contract_runtime_ready art mods am tx <=>
    ALOOKUP am.sources tx.target = SOME mods /\
    immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
      (initial_evaluation_context am.sources am.layouts tx NONE)
      am.immutables
End

Theorem checked_contract_initial_context_functions_follow_call_graph[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods ==>
  functions_follow_call_graph (contract_call_edges mods)
    (initial_evaluation_context am.sources am.layouts tx src)
Proof
  rw[functions_follow_call_graph_def, initial_evaluation_context_def] >>
  gvs[get_module_code_def] >>
  drule ALOOKUP_MEM >>
  disch_then assume_tac >>
  drule lookup_callable_function_SOME_decompose >>
  strip_tac
  >- simp[function_int_calls_def, int_calls_expr_def, int_calls_stmt_def] >>
  rw[EVERY_MEM, call_edge_rel_def] >>
  irule contract_call_edges_function >>
  metis_tac[]
QED

Theorem checked_explicit_external_body_call_evaluation_safe[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts ==>
  call_evaluation_safe
    (initial_evaluation_context am.sources am.layouts tx src)
    (int_calls_stmts body)
Proof
  rpt strip_tac >>
  `calls_follow_call_graph (contract_call_edges mods) (src,tx.function_name)
     (int_calls_stmts body)` by (
    rw[calls_follow_call_graph_def, EVERY_MEM, call_edge_rel_def] >>
    irule contract_call_edges_function >>
    qexistsl [`args`, `body`, `dflts`, `mut`, `nr`, `raw`, `ret`, `ts`,
              `External`] >>
    simp[function_int_calls_def] >>
    metis_tac[ALOOKUP_MEM]) >>
  `(initial_evaluation_context am.sources am.layouts tx src) =
   ((initial_evaluation_context am.sources am.layouts tx src) with
      stk := [(src,tx.function_name)])` by
    simp[initial_evaluation_context_def] >>
  pop_assum SUBST1_TAC >>
  irule (INST_TYPE [``:'a`` |-> ``:num``]
    checked_contract_call_evaluation_safe_singleton) >>
  qexistsl [`art`, `am.layouts`, `mods`] >>
  simp[initial_evaluation_context_def]
QED

(* checked_call_external_no_type_error is proved near the end of this file,
   after its explicit-function and public-getter branch helpers. *)

(* ===== Deployment establishes runtime immutable readiness ===== *)

Theorem load_contract_success_cases:
  load_contract am tx mods exps = INL am_deployed ==>
  ?imms ts mut nr args dflts ret body v am_ctor.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE tx.function_name Deploy ts =
      SOME (mut,nr,args,dflts,ret,body) /\
    call_external_function
      (am with <| immutables updated_by CONS (tx.target,imms);
                 exports updated_by CONS (tx.target,exps) |>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources)
          am.layouts tx NONE) with in_deploy := T)
      nr mut ts mods args dflts tx.args body ret = (INL v, am_ctor) /\
    am_deployed = am_ctor with sources updated_by CONS (tx.target,mods)
Proof
  rw[load_contract_def] >>
  Cases_on `initial_immutables (type_env_all_modules mods) mods` >> gvs[] >>
  Cases_on `lookup_function NONE tx.function_name Deploy
              (case ALOOKUP mods NONE of SOME ts => ts | NONE => [])` >> gvs[] >>
  Cases_on `x'` >> gvs[] >>
  Cases_on `r` >> gvs[] >>
  Cases_on `r''` >> gvs[] >>
  Cases_on `r` >> gvs[] >>
  Cases_on `r''` >> gvs[] >>
  Cases_on `call_external_function
      (am with <|immutables updated_by CONS (tx.target,x);
                exports updated_by CONS (tx.target,exps)|>)
      ((initial_evaluation_context ((tx.target,mods)::am.sources) am.layouts tx NONE)
         with in_deploy := T)
      q' q (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods q'' q''' tx.args r q''''` >>
  gvs[] >>
  Cases_on `q'''''` >> gvs[] >>
  qexists `a` >> simp[]
QED

Theorem call_external_function_deploy_success_evaluate_all_constants[local]:
  !am cx nr mut ts all_mods args dflts vals body ret v am_out.
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) ==>
  ?am_c.
    evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c
Proof
  rw[call_external_function_def] >>
  gvs[AllCaseEqs()]
QED

Theorem deployed_check_contract_bare_globals_consistent[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
    ?ts.
      get_module_code
        (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx src) src = SOME ts /\
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
      is_bare_global_decl id ts /\
      find_var_decl_by_num id ts = NONE /\
      ty <> NoneT
Proof
  rw[] >>
  drule load_contract_success_cases >>
  strip_tac >> gvs[] >>
  drule check_contract_bare_globals_consistent_initial >>
  simp[] >>
  disch_then (qspecl_then [`src`, `id`, `ty`] mp_tac) >>
  simp[]
QED

Theorem constants_env_preserves_lookup_not_key[local]:
  constants_env cx am addr src ts acc = SOME cenv /\
  ~(MEM (src,id) (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))) /\
  FLOOKUP acc id = SOME x ==>
  FLOOKUP cenv id = SOME x
Proof
  qid_spec_tac `cenv` >> qid_spec_tac `acc` >>
  Induct_on `ts` >- (rw[constants_env_def] >> gvs[]) >>
  gen_tac >> gen_tac >> Cases_on `h` >>
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  TRY (Cases_on `v0` >>
       gvs[constants_env_def, toplevel_vtype_keys_toplevel_def]) >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE] >>
  TRY (first_x_assum (qspecl_then [`acc |+ (string_to_num s,(tv,v))`,`cenv`] mp_tac) >>
       simp[FLOOKUP_UPDATE] >> NO_TAC) >>
  first_x_assum (qspecl_then [`acc`,`cenv`] mp_tac) >> simp[]
QED


Theorem constants_env_head_constant_type[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src)
    ((VariableDecl vis (Constant e) id ty init)::ts))) /\
  constants_env cx am addr src
    ((VariableDecl vis (Constant e) id ty init)::ts) acc = SOME cenv ==>
  ?tv v. FLOOKUP cenv (string_to_num id) = SOME (tv,v) /\
         evaluate_type (get_tenv cx) ty = SOME tv
Proof
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  gvs[AllCaseEqs()] >>
  qexists `v` >> simp[] >>
  metis_tac[constants_env_preserves_lookup_not_key, FLOOKUP_UPDATE]
QED
Theorem constants_env_contains_constant_type[local]:
  ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
  constants_env cx am addr src ts acc = SOME cenv /\
  MEM (VariableDecl vis (Constant e) id ty init) ts ==>
  ?tv v. FLOOKUP cenv (string_to_num id) = SOME (tv,v) /\
         evaluate_type (get_tenv cx) ty = SOME tv
Proof
  qid_spec_tac `init` >> qid_spec_tac `ty` >> qid_spec_tac `id` >>
  qid_spec_tac `e` >> qid_spec_tac `vis` >>
  qid_spec_tac `cenv` >> qid_spec_tac `acc` >>
  qid_spec_tac `ts` >> qid_spec_tac `src` >> qid_spec_tac `addr` >>
  qid_spec_tac `am` >> qid_spec_tac `cx` >>
  recInduct constants_env_ind >>
  rw[constants_env_def, toplevel_vtype_keys_toplevel_def] >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE] >>
  metis_tac[constants_env_head_constant_type, constants_env_preserves_lookup_not_key,
            FLOOKUP_UPDATE]
QED

Theorem merge_constants_preserves_lookup_not_source[local]:
  src <> src' /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP (merge_constants addr src' cenv am).immutables addr of
     | SOME m => m
     | NONE => [])) id = SOME x
Proof
  rw[merge_constants_def, get_source_immutables_set_other,
     empty_immutables_def, alistTheory.ALOOKUP_ADELKEY]
QED

Theorem evaluate_all_constants_preserves_lookup_not_source[local]:
  ~(MEM src (MAP FST mods)) /\
  evaluate_all_constants cx am addr mods = SOME am_c /\
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am.immutables addr of SOME m => m | NONE => [])) id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) id = SOME x
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  Induct_on `mods` >- (rw[evaluate_all_constants_def] >> gvs[]) >>
  gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[evaluate_all_constants_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum irule >>
  simp[] >>
  qexists `merge_constants addr h0 cenv am` >>
  simp[] >>
  irule merge_constants_preserves_lookup_not_source >>
  simp[]
QED
Theorem evaluate_all_constants_preserves_merged_lookup_not_source[local]:
  ~(MEM src (MAP FST mods)) /\
  evaluate_all_constants cx (merge_constants addr src cenv am) addr mods = SOME am_c /\
  FLOOKUP cenv id = SOME x ==>
  FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => [])) id = SOME x
Proof
  rw[] >>
  drule evaluate_all_constants_preserves_lookup_not_source >>
  disch_then drule >>
  disch_then irule >>
  simp[merge_constants_def, get_source_immutables_set_same,
       empty_immutables_def, FLOOKUP_FUNION]
QED

Theorem evaluate_all_constants_contains_constant_type[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis (Constant e) id ty init) ts /\
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  ?tv v. FLOOKUP (get_source_immutables src
    (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
    (string_to_num id) = SOME (tv,v) /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  qid_spec_tac `ts` >> qid_spec_tac `src` >>
  Induct_on `mods` >- rw[evaluate_all_constants_def] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> PairCases_on `h` >>
  rw[evaluate_all_constants_def, alistTheory.ALOOKUP_def] >>
  gvs[AllCaseEqs()] >-
    (`ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel h0) h1))` by
       gvs[contract_namespaces_ok_def, contract_keys_def, ALL_DISTINCT_APPEND] >>
     drule constants_env_contains_constant_type >>
     disch_then drule >>
     disch_then drule >>
     strip_tac >>
     `FLOOKUP (get_source_immutables h0
        (case ALOOKUP am_c.immutables addr of SOME m => m | NONE => []))
        (string_to_num id) = SOME (tv,v)` by
       (gvs[contract_namespaces_ok_def] >>
        drule evaluate_all_constants_preserves_merged_lookup_not_source >>
        disch_then drule >>
        disch_then drule >>
        simp[]) >>
     qexistsl [`tv`,`v`] >>
     gvs[set_current_module_def, get_tenv_def]) >>
  first_x_assum irule >>
  gvs[contract_namespaces_ok_def] >>
  conj_tac >- metis_tac[] >>
  gvs[contract_keys_def, ALL_DISTINCT_APPEND]
QED

Theorem contract_toplevel_vtype_key_MEM_Variable[local]:
  MEM (src,ts) mods /\ MEM (VariableDecl vis mut id ty init) ts ==>
  MEM ((src : num option),string_to_num id)
    (contract_keys toplevel_vtype_keys_toplevel mods)
Proof
  rw[contract_keys_def, MEM_FLAT, MEM_MAP] >>
  qexists `FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)` >> simp[] >>
  conj_tac >- (qexists `(src,ts)` >> simp[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable]
QED
Theorem module_toplevel_vtype_key_MEM_Variable_any[local]:
  MEM (VariableDecl vis mut id ty init) ts ==>
  MEM (src,string_to_num id)
    (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))
Proof
  rw[MEM_FLAT, MEM_MAP] >>
  qexists `[(src,string_to_num id)]` >> simp[] >>
  qexists `VariableDecl vis mut id ty init` >>
  simp[toplevel_vtype_keys_toplevel_def]
QED


Theorem module_immutable_constant_string_nums_distinct[local]:
  !src ts visI idI tyI initI visC e idC tyC slotC.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI Immutable idI tyI initI) ts /\
    MEM (VariableDecl visC (Constant e) idC tyC slotC) ts ==>
    string_to_num idI <> string_to_num idC
Proof
  gen_tac >> Induct_on `ts` >- rw[] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  Cases_on `h` >>
  rw[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  gvs[toplevel_vtype_keys_toplevel_def] >>
  TRY (first_x_assum irule >> metis_tac[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED
Theorem module_immutable_string_num_type_unique[local]:
  !src ts visI idI tyI initI visJ idJ tyJ initJ.
    ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts)) /\
    MEM (VariableDecl visI Immutable idI tyI initI) ts /\
    MEM (VariableDecl visJ Immutable idJ tyJ initJ) ts /\
    string_to_num idJ = string_to_num idI ==>
    tyJ = tyI
Proof
  gen_tac >> Induct_on `ts` >- rw[] >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  gen_tac >> gen_tac >> gen_tac >> gen_tac >>
  Cases_on `h` >>
  rw[toplevel_vtype_keys_toplevel_def, ALL_DISTINCT_APPEND] >>
  gvs[toplevel_vtype_keys_toplevel_def] >>
  TRY (first_x_assum irule >> metis_tac[]) >>
  metis_tac[module_toplevel_vtype_key_MEM_Variable_any]
QED


Theorem constants_do_not_clobber_single_immutable[local]:
  contract_namespaces_ok F mods /\
  ALOOKUP mods src = SOME ts /\
  MEM (VariableDecl vis Immutable id_str ty init) ts ==>
  constants_do_not_clobber_bare_globals
    mods (FEMPTY |+ ((src,string_to_num id_str), ty))
Proof
  rw[constants_do_not_clobber_bare_globals_def, FLOOKUP_UPDATE] >>
  gvs[] >>
  rename1 `ALOOKUP mods src0 = SOME ts` >>
  `MEM (src0,ts) mods` by metis_tac[alistTheory.ALOOKUP_MEM] >>
  `ALOOKUP mods src0 = SOME ts'` by
    (irule alistTheory.ALOOKUP_ALL_DISTINCT_MEM >>
     gvs[contract_namespaces_ok_def]) >>
  gvs[] >>
  `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src0) ts))` by
    metis_tac[contract_namespaces_ok_module_toplevel_vtype_keys] >>
  irule module_immutable_constant_string_nums_distinct >>
  qexistsl [`e`,`init`,`slot`,`src0`,`ts`,`typ`,`ty`,`vis'`,`vis`] >>
  simp[]
QED

Theorem deploy_constants_setup_bare_globals_ready:
  check_contract F layouts target mods = SOME call_art /\
  ALOOKUP sources target = SOME mods /\
  tx.target = target /\
  get_tenv cx = type_env_all_modules mods /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants cx
    (am with immutables updated_by CONS (target,imms)) target mods = SOME am_c ==>
  (!src id ty.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
     IS_SOME (FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables target of SOME m => m | NONE => [])) id)) /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules mods) ty = SOME tv)
Proof
  rw[check_contract_def] >>
  gvs[]
  >- (rw[] >>
      drule build_contract_type_artifact_bare_globals_sound >>
      disch_then drule >>
      strip_tac >>
      gvs[]
      >- (`IS_SOME (FLOOKUP (get_source_immutables src imms) (string_to_num id_str))` by
            (irule initial_immutables_contains_decl >>
             qexists `mods` >> qexists `type_env_all_modules mods` >> qexists `ts` >>
             simp[] >>
             conj_tac
             >- (irule find_var_decl_by_num_NONE_Immutable >>
                 conj_tac
                 >- (qexists `src` >>
                     irule contract_namespaces_ok_module_toplevel_vtype_keys >>
                     metis_tac[alistTheory.ALOOKUP_MEM]) >>
                 metis_tac[]) >>
             metis_tac[is_immutable_decl_MEM]) >>
          gvs[IS_SOME_EXISTS] >>
          qexists `x` >>
          irule evaluate_all_constants_preserves_bare_global_lookup_type >>
          qexistsl [`am with immutables updated_by CONS (tx.target,imms)`,
                   `FEMPTY |+ ((src,string_to_num id_str),ty)`,
                   `cx`, `mods`, `ts`, `ty`] >>
          gvs[FLOOKUP_UPDATE, initial_target_immutables_lookup] >>
          gvs[] >>
          metis_tac[constants_do_not_clobber_single_immutable]) >>
      metis_tac[evaluate_all_constants_contains_constant_type, IS_SOME_EXISTS]) >>
  rw[] >>
  `(?ts vis id_str init.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis Immutable id_str ty init) ts /\
      id = string_to_num id_str) \/
   (?ts vis e id_str init.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis (Constant e) id_str ty init) ts /\
      id = string_to_num id_str)` by
    metis_tac[build_contract_type_artifact_bare_globals_sound] >>
  gvs[]
  >- (`IS_SOME (FLOOKUP (get_source_immutables src imms) (string_to_num id_str))` by
        (irule initial_immutables_contains_decl >>
         qexists `mods` >> qexists `type_env_all_modules mods` >> qexists `ts` >>
         simp[] >>
         conj_tac
         >- (irule find_var_decl_by_num_NONE_Immutable >>
             conj_tac
             >- (qexists `src` >>
                 irule contract_namespaces_ok_module_toplevel_vtype_keys >>
                 metis_tac[alistTheory.ALOOKUP_MEM]) >>
             metis_tac[]) >>
         metis_tac[is_immutable_decl_MEM]) >>
      gvs[IS_SOME_EXISTS] >>
      `FLOOKUP
         (get_source_immutables src
            (case ALOOKUP am_c.immutables tx.target of NONE => [] | SOME m => m))
         (string_to_num id_str) = SOME x` by
        (irule evaluate_all_constants_preserves_bare_global_lookup_type >>
         qexistsl [`am with immutables updated_by CONS (tx.target,imms)`,
                   `FEMPTY |+ ((src,string_to_num id_str),ty)`,
                   `cx`, `mods`, `ts`, `ty`] >>
         gvs[FLOOKUP_UPDATE, initial_target_immutables_lookup] >>
         metis_tac[constants_do_not_clobber_single_immutable]) >>
      gvs[] >>
      `ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel src) ts))` by
        (irule contract_namespaces_ok_module_toplevel_vtype_keys >>
         metis_tac[alistTheory.ALOOKUP_MEM]) >>
      `is_immutable_decl (string_to_num id_str) ts` by
        metis_tac[is_immutable_decl_MEM] >>
      irule initial_immutables_all_bare_global_type >>
      qexistsl [`string_to_num id_str`, `imms`, `mods`, `src`, `ts`, `v`] >>
      gvs[] >>
      metis_tac[module_immutable_string_num_type_unique]) >>
  drule evaluate_all_constants_contains_constant_type >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  strip_tac >>
      gvs[]
QED

Theorem send_call_value_preserves_tv[local]:
  send_call_value mut cx st = (res,st') ==>
  preserves_tv cx st st'
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     return_def, raise_def] >>
  gvs[AllCaseEqs(), preserves_tv_def] >>
  TRY (qpat_x_assum `assert _ _ _ = _` mp_tac >> rw[assert_def] >> gvs[]) >>
  imp_res_tac transfer_value_scopes >>
  imp_res_tac transfer_value_immutables >>
  gvs[preserves_tv_def]
QED
Theorem call_lock_action_preserves_tv[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  preserves_tv cx st st'
Proof
  rw[] >>
  gvs[return_def, raise_def, preserves_tv_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def, preserves_tv_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  gvs[preserves_tv_def]
QED

Theorem call_unlock_action_preserves_immutables[local]:
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[] >>
  gvs[return_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  gvs[]
QED

Theorem call_body_prefix_preserves_tv[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od st = (res,st')) ==>
  preserves_tv cx st st'
Proof
  rw[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac call_lock_action_preserves_tv >>
  imp_res_tac send_call_value_preserves_tv >>
  imp_res_tac (cj 2 eval_preserves_tv) >>
  `preserves_tv cx st s''` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, return_def, preserves_tv_def] >>
     imp_res_tac acquire_nonreentrant_lock_scopes >>
     imp_res_tac acquire_nonreentrant_lock_immutables >>
     gvs[preserves_tv_def]) >>
  gvs[preserves_tv_def] >>
  rpt strip_tac >>
  res_tac >> res_tac >>
  metis_tac[]
QED

Theorem call_body_prefix_lock_preserves_tv[local]:
  (do
     (case cx.nonreentrant_slot of
        NONE => raise (Error (TypeError "nonreentrant slot missing"))
      | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view);
     send_call_value mut cx;
     eval_stmts cx body
   od st = (res,st')) ==>
  preserves_tv cx st st'
Proof
  rw[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac send_call_value_preserves_tv >>
  imp_res_tac (cj 2 eval_preserves_tv) >>
  `preserves_tv cx st s''` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, return_def, preserves_tv_def] >>
     imp_res_tac acquire_nonreentrant_lock_scopes >>
     imp_res_tac acquire_nonreentrant_lock_immutables >>
     gvs[preserves_tv_def]) >>
  gvs[preserves_tv_def] >>
  rpt strip_tac >>
  res_tac >> res_tac >>
  metis_tac[]
QED

Theorem preserves_tv_initial_immutables_lookup[local]:
  !cx am_c env st src id tv x.
    preserves_tv cx (initial_state am_c [env]) st ==>
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
    ?y.
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP st.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[preserves_tv_def, initial_state_def] >>
  metis_tac[]
QED

Theorem preserves_tv_unlock_abstract_machine_immutables_lookup[local]:
  preserves_tv cx (initial_state am_c [env]) st_body /\
  st_unlocked.immutables = st_body.immutables /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[abstract_machine_from_state_def] >>
  drule preserves_tv_initial_immutables_lookup >>
  disch_then drule >>
  rw[] >>
  metis_tac[]
QED

Theorem call_external_function_deploy_normal_success_lookup_transport:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (INL (),st_body)) /\
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st_body = (INL u,st_unlocked) /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  `preserves_tv cx (initial_state am_c [env]) st_body` by
    metis_tac[call_body_prefix_lock_preserves_tv,
              call_body_prefix_preserves_tv, return_def, bind_def] >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  metis_tac[preserves_tv_unlock_abstract_machine_immutables_lookup]
QED


Theorem call_external_function_deploy_return_success_lookup_transport:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (INR (ReturnException v_ret),st_body)) /\
  (if nr /\ ~(mut = View \/ mut = Pure) then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st_body = (INL u,st_unlocked) /\
  am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  `preserves_tv cx (initial_state am_c [env]) st_body` by
    metis_tac[call_body_prefix_lock_preserves_tv,
              call_body_prefix_preserves_tv, return_def, bind_def] >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  metis_tac[preserves_tv_unlock_abstract_machine_immutables_lookup]
QED


Theorem call_external_function_success_result_cases[local]:
  (\(res,st). (res,st))
    (case body_res of
       (INL (), st) =>
         (case unlock st of
            (INL u, st') => (INL NoneV, abstract_machine_from_state srcs exps layouts st')
          | (INR e, st') => (INR e, am))
     | (INR (ReturnException v_ret), st) =>
         (case unlock st of
            (INL u, st') =>
              (case evaluate_type tenv ret of
                 NONE => (INR (Error (TypeError "eval ret")), am)
               | SOME tv =>
                   case safe_cast tv v_ret of
                     NONE => (INR (Error (TypeError "ext cast ret")), am)
                   | SOME v_cast =>
                       (INL v_cast, abstract_machine_from_state srcs exps layouts st'))
          | (INR e, st') => (INR e, am))
     | (INR e, st) => (INR e, am)) = (INL v, am_out) ==>
  ((?st_body st_unlocked u.
      body_res = (INL (), st_body) /\
      unlock st_body = (INL u, st_unlocked) /\
      am_out = abstract_machine_from_state srcs exps layouts st_unlocked) \/
   (?v_ret st_body st_unlocked u tv v_cast.
      body_res = (INR (ReturnException v_ret), st_body) /\
      unlock st_body = (INL u, st_unlocked) /\
      evaluate_type tenv ret = SOME tv /\
      safe_cast tv v_ret = SOME v_cast /\
      am_out = abstract_machine_from_state srcs exps layouts st_unlocked))
Proof
  PairCases_on `body_res` >>
  Cases_on `body_res0` >> gvs[] >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[]) >>
  metis_tac[]
QED

Theorem call_external_function_deploy_success_cases:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c ==>
  ?dflt_vs env.
    evaluate_defaults cx am (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts) = SOME dflt_vs /\
    bind_arguments (type_env_all_modules all_mods) args (vals ++ dflt_vs) = SOME env /\
    ((?st_body st_unlocked u.
        (do
           (if nr then
              case cx.nonreentrant_slot of
                NONE => raise (Error (TypeError "nonreentrant slot missing"))
              | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
            else return ());
           send_call_value mut cx;
           eval_stmts cx body
         od (initial_state am_c [env]) = (INL (), st_body)) /\
        (if nr /\ ~(mut = View \/ mut = Pure) then
           case cx.nonreentrant_slot of
             NONE => return ()
           | SOME slot => release_nonreentrant_lock cx.txn.target slot
         else return ()) st_body = (INL u, st_unlocked) /\
        am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked) \/
     (?v_ret st_body st_unlocked u tv v_cast.
        (do
           (if nr then
              case cx.nonreentrant_slot of
                NONE => raise (Error (TypeError "nonreentrant slot missing"))
              | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
            else return ());
           send_call_value mut cx;
           eval_stmts cx body
         od (initial_state am_c [env]) = (INR (ReturnException v_ret), st_body)) /\
        (if nr /\ ~(mut = View \/ mut = Pure) then
           case cx.nonreentrant_slot of
             NONE => return ()
           | SOME slot => release_nonreentrant_lock cx.txn.target slot
         else return ()) st_body = (INL u, st_unlocked) /\
        evaluate_type (type_env_all_modules all_mods) ret = SOME tv /\
        safe_cast tv v_ret = SOME v_cast /\
        am_out = abstract_machine_from_state am_c.sources am_c.exports am_c.layouts st_unlocked))
Proof
  rw[call_external_function_def] >>
  gvs[AllCaseEqs()] >>
  drule call_external_function_success_result_cases >>
  simp[]
QED

Theorem call_external_function_deploy_success_preserves_immutable_type_tags_from_constants[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,y)
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  strip_tac >>
  gvs[] >-
    (irule call_external_function_deploy_normal_success_lookup_transport >>
     qexistsl [`am_c`, `body`, `env`, `mut`, `nr`, `st_body`, `st_unlocked`, `()`, `x`] >>
     simp[]) >>
  irule call_external_function_deploy_return_success_lookup_transport >>
  qexistsl [`am_c`, `body`, `env`, `mut`, `nr`, `st_body`, `st_unlocked`, `()`, `v_ret`, `x`] >>
  simp[]
QED

Theorem send_call_value_preserves_immutables[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     type_check_def, assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_immutables >>
  gvs[]
QED

Theorem call_lock_action_preserves_immutables[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.immutables = st.immutables
Proof
  rw[] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  gvs[]
QED


Theorem bind_arguments_length_c53[local]:
  !tenv args vs env.
    bind_arguments tenv args vs = SOME env ==> LENGTH args = LENGTH vs
Proof
  Induct_on `args` >> simp[bind_arguments_def] >>
  Cases_on `vs` >> simp[bind_arguments_def] >>
  rpt gen_tac >> PairCases_on `h'` >>
  simp[bind_arguments_def] >>
  Cases_on `evaluate_type tenv h'1` >> simp[] >>
  Cases_on `safe_cast x h` >> simp[] >>
  Cases_on `bind_arguments tenv args t` >> simp[] >>
  strip_tac >> res_tac
QED

Theorem call_external_function_exact_args_rewrites_c53[local]:
  bind_arguments (type_env_all_modules all_mods) args vals = SOME scope ==>
  LENGTH vals = LENGTH args /\
  DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts = [] /\
  vals ++ [] = vals
Proof
  strip_tac >>
  `LENGTH vals = LENGTH args` by metis_tac[bind_arguments_length_c53] >>
  simp[]
QED

Theorem transfer_value_no_type_error_c53[local]:
  !from to amount st s.
    FST (transfer_value from to amount st) <> INR (Error (TypeError s))
Proof
  rw[transfer_value_def, bind_def, ignore_bind_def, get_accounts_def, return_def,
     check_def, assert_def, raise_def, update_accounts_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem transfer_value_accounts_well_typed_c53[local]:
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

Theorem send_call_value_no_control_c53:
  send_call_value mut cx st = (INR exc,st') ==> no_control_exc exc
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
  >- (irule transfer_value_no_control >>
      qexistsl [`cx.txn.value`, `cx.txn.sender`, `st`, `st'`, `cx.txn.target`] >>
      simp[]) >>
  simp[no_control_exc_def]
QED

Theorem send_call_value_no_type_error_c53[local]:
  no_type_error_eval (send_call_value mut cx st)
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def,
     vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs()] >>
  Cases_on `mut = Payable` >> gvs[return_def, raise_def] >>
  metis_tac[transfer_value_no_type_error_c53]
QED

Theorem send_call_value_preserves_scopes_c53[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_scopes >> gvs[]
QED

Theorem send_call_value_accounts_well_typed_c53:
  accounts_well_typed st.accounts /\
  send_call_value mut cx st = (res,st') ==>
  accounts_well_typed st'.accounts
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  `accounts_well_typed
     (SND (transfer_value cx.txn.sender cx.txn.target cx.txn.value st)).accounts` by
    metis_tac[transfer_value_accounts_well_typed_c53] >>
  gvs[]
QED

Theorem call_lock_action_preserves_accounts_c53:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.accounts = st.accounts
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def, return_def, raise_def,
     assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem call_lock_action_preserves_scopes_c53[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Theorem call_lock_send_prefix_body_state_ready_c53:
  machine_well_typed am /\
  scope_well_typed env /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [env]) = (INL (),st)) ==>
  st.scopes = [env] /\
  st.immutables = am.immutables /\
  state_well_typed st
Proof
  rw[bind_def, ignore_bind_def] >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def]) >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac send_call_value_preserves_scopes_c53 >>
  imp_res_tac send_call_value_preserves_immutables >>
  gvs[initial_state_def, state_well_typed_def, machine_well_typed_def]
QED

Theorem call_lock_action_no_control_c53:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
   else return ()) st = (INR exc,st') ==>
  no_control_exc exc
Proof
  Cases_on `nr` >> gvs[return_def, raise_def, no_control_exc_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, no_control_exc_def] >>
  strip_tac >> drule acquire_nonreentrant_lock_no_control >>
  simp[no_control_exc_def]
QED

Theorem call_lock_send_eval_no_loop_control_c53[local]:
  stmts_no_control_escape body /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od st) = (INR exc,st') ==>
  exc <> BreakException /\ exc <> ContinueException
Proof
  rw[bind_def, ignore_bind_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac call_lock_action_no_control_c53 >>
  imp_res_tac send_call_value_no_control_c53 >>
  imp_res_tac stmts_no_control_escape_eval_stmts_no_loop_control >>
  gvs[no_control_exc_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[raise_def, no_control_exc_def] >>
  imp_res_tac acquire_nonreentrant_lock_no_control >>
  gvs[no_control_exc_def]
QED

Theorem call_lock_action_no_type_error_c53[local]:
  (nr ==> cx.nonreentrant_slot <> NONE) ==>
  no_type_error_eval
    ((if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ()) st)
Proof
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem unlock_action_no_control_c53[local]:
  (if nr /\ mut <> View /\ mut <> Pure then
     case cx.nonreentrant_slot of
       NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
   else return ()) st = (INR exc,st') ==>
  no_control_exc exc
Proof
  rw[] >> gvs[return_def, no_control_exc_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, no_control_exc_def] >>
  qpat_x_assum `release_nonreentrant_lock _ _ _ = _` mp_tac >>
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def, no_control_exc_def]
QED

Theorem call_external_function_no_loop_control_c53[local]:
  stmts_no_control_escape body /\
  call_external_function am cx nr mut ts mods args dflts vals body ret =
    (INR exc,am') ==>
  exc <> BreakException /\ exc <> ContinueException
Proof
  strip_tac >>
  qpat_x_assum
    `call_external_function am cx nr mut ts mods args dflts vals body ret =
       (INR exc,am')` mp_tac >>
  rewrite_tac[call_external_function_def] >>
  strip_tac >>
  Cases_on `LENGTH vals > LENGTH args \/
            LENGTH args > LENGTH dflts + LENGTH vals` >>
  gvs[] >>
  Cases_on `evaluate_defaults cx am
    (DROP (LENGTH dflts + LENGTH vals - LENGTH args) dflts)` >>
  gvs[] >>
  Cases_on `bind_arguments (type_env_all_modules mods) args (vals ++ x)` >>
  gvs[] >>
  Cases_on
    `if cx.in_deploy then
       evaluate_all_constants cx am cx.txn.target mods
     else SOME am` >>
  gvs[] >>
  Cases_on
    `(do
        (if nr then
           case cx.nonreentrant_slot of
             NONE => raise (Error (TypeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock cx.txn.target slot
                            (mut = View \/ mut = Pure)
         else return ());
        send_call_value mut cx;
        eval_stmts cx body
      od (initial_state x'' [x']))` >>
  Cases_on `q`
  >- (gvs[] >>
      Cases_on
        `(if nr /\ mut <> View /\ mut <> Pure then
            case cx.nonreentrant_slot of
              NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()) r` >>
      Cases_on `q` >>
      gvs[] >>
      imp_res_tac unlock_action_no_control_c53 >>
      gvs[no_control_exc_def]) >>
  gvs[] >>
  imp_res_tac call_lock_send_eval_no_loop_control_c53 >>
  Cases_on `y` >>
  gvs[] >>
  Cases_on
    `(if nr /\ mut <> View /\ mut <> Pure then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()) r` >>
  Cases_on `q` >>
  gvs[] >>
  imp_res_tac unlock_action_no_control_c53 >>
  gvs[no_control_exc_def] >>
  Cases_on `evaluate_type (type_env_all_modules mods) ret` >>
  gvs[] >>
  rename1 `evaluate_type (type_env_all_modules mods) ret = SOME tv` >>
  Cases_on `safe_cast tv v` >>
  gvs[]
QED




Theorem unlock_action_no_type_error_c53[local]:

  no_type_error_eval
    ((if nr /\ mut <> View /\ mut <> Pure then
        case cx.nonreentrant_slot of
          NONE => return ()
        | SOME slot => release_nonreentrant_lock cx.txn.target slot
      else return ()) st)
Proof
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
     vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  rw[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def,
     return_def, raise_def, assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED

Theorem call_lock_send_eval_prefix_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  no_type_error_eval
    (do
       (if nr then
          case cx.nonreentrant_slot of
            NONE => raise (Error (TypeError "nonreentrant slot missing"))
          | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
        else return ());
       send_call_value mut cx;
       eval_stmts cx body
     od (initial_state am [scope]))
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `ALL_DISTINCT (MAP (string_to_num o FST) args)` by
    (`check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
       metis_tac[check_contract_function_body_MEM] >>
     gvs[check_function_body_def, params_ok_def]) >>
  `context_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    metis_tac[call_tx_well_typed_initial_context] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[checked_contract_runtime_ready_def,
              immutables_ready_initial_evaluation_context_source] >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  simp[vyperTypeExprSoundnessTheory.no_type_error_eval_def,
       bind_def, ignore_bind_def] >>
  Cases_on `(if nr then
               case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
                 NONE => raise (Error (TypeError "nonreentrant slot missing"))
               | SOME slot => acquire_nonreentrant_lock
                   (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
                   (mut = View \/ mut = Pure)
             else return ()) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `send_call_value mut (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[]
      >- (`r''.scopes = [scope] /\ r''.immutables = am.immutables /\ state_well_typed r''` by
            (irule call_lock_send_prefix_body_state_ready_c53 >>
             simp[bind_def, ignore_bind_def] >>
             qexistsl [`initial_evaluation_context am.sources am.layouts tx src`, `mut`, `nr`] >>
             simp[]) >>
          `accounts_well_typed r.accounts` by
            (imp_res_tac call_lock_action_preserves_accounts_c53 >>
             gvs[initial_state_accounts_well_typed]) >>
          `accounts_well_typed r''.accounts` by
            (imp_res_tac send_call_value_accounts_well_typed_c53 >> gvs[]) >>
          simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_eval_def] >>
          irule checked_explicit_external_post_prefix_body_no_type_error_selected >>
          simp[] >>
          conj_tac
          >- metis_tac[checked_explicit_external_body_call_evaluation_safe] >>
          qexistsl [`am`, `args`, `art`, `dflts`, `mods`, `mut`, `nr`, `raw`,
                    `ret`, `src`, `ts`, `tx`, `vals`] >>
          simp[]) >>
      `no_type_error_eval
         (send_call_value mut (initial_evaluation_context am.sources am.layouts tx src) r)` by
        simp[send_call_value_no_type_error_c53] >>
      gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def]) >>
  `nr ==> (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot <> NONE` by (
    strip_tac >>
    `check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
      metis_tac[check_contract_function_body_MEM] >>
    gvs[check_function_body_def, initial_evaluation_context_def,
        optionTheory.IS_SOME_EXISTS]) >>
  `no_type_error_eval
     ((if nr then
         case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
           NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock
             (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
             (mut = View \/ mut = Pure)
       else return ()) (initial_state am [scope]))` by (
    irule call_lock_action_no_type_error_c53 >>
    qpat_assum `nr ==> _` ACCEPT_TAC) >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED

Theorem call_lock_send_eval_return_typed_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (do
     (if nr then
        case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock tx.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut (initial_evaluation_context am.sources am.layouts tx src);
     eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
   od (initial_state am [scope]) = (INR (ReturnException v),st')) ==>
  ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
           value_has_type ret_tv v
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `context_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    metis_tac[call_tx_well_typed_initial_context] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[checked_contract_runtime_ready_def,
              immutables_ready_initial_evaluation_context_source] >>
  `ALOOKUP am.sources tx.target = SOME mods` by
    gvs[checked_contract_runtime_ready_def] >>
  qpat_x_assum `do _; _; _ od _ = _` mp_tac >>
  simp[bind_def, ignore_bind_def] >>
  Cases_on `(if nr then
               case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
                 NONE => raise (Error (TypeError "nonreentrant slot missing"))
               | SOME slot => acquire_nonreentrant_lock tx.target slot
                   (mut = View \/ mut = Pure)
             else return ()) (initial_state am [scope])` >>
  Cases_on `q` >> gvs[]
  >- (Cases_on `send_call_value mut
         (initial_evaluation_context am.sources am.layouts tx src) r` >>
      Cases_on `q` >> gvs[]
      >- (strip_tac >>
          `r''.scopes = [scope] /\ r''.immutables = am.immutables /\
           state_well_typed r''` by (
            irule call_lock_send_prefix_body_state_ready_c53 >>
            simp[] >>
            qexistsl [`initial_evaluation_context am.sources am.layouts tx src`,
                      `mut`, `nr`] >>
            gvs[bind_def, ignore_bind_def, initial_evaluation_context_def]) >>
          `r.accounts = (initial_state am [scope]).accounts` by (
            qpat_x_assum `(if nr then _ else _) _ = (INL (),r)` mp_tac >>
            simp[initial_evaluation_context_def] >>
            Cases_on `nr` >> gvs[return_def, raise_def] >>
            Cases_on `lookup_nonreentrant_slot am.layouts tx.target` >>
            gvs[return_def, raise_def] >> strip_tac >>
            qpat_x_assum `acquire_nonreentrant_lock _ _ _ _ = _` mp_tac >>
            rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
               get_transient_storage_def, update_transient_def, return_def,
               raise_def, assert_def, check_def] >>
            gvs[AllCaseEqs(), return_def, raise_def]) >>
          `accounts_well_typed r.accounts` by
            gvs[initial_state_accounts_well_typed] >>
          `accounts_well_typed r''.accounts` by (
            imp_res_tac send_call_value_accounts_well_typed_c53 >> gvs[]) >>
          `call_evaluation_safe
             (initial_evaluation_context am.sources am.layouts tx src)
             (int_calls_stmts body)` by
            metis_tac[checked_explicit_external_body_call_evaluation_safe] >>
          irule checked_explicit_external_post_prefix_body_return_typed_selected >>
          simp[] >> metis_tac[])
      >- (strip_tac >> drule send_call_value_no_control_c53 >>
          simp[no_control_exc_def]))
  >- (strip_tac >> gvs[] >>
      qpat_x_assum `(if nr then _ else _) _ = (INR (ReturnException v),st')` mp_tac >>
      simp[initial_evaluation_context_def] >>
      Cases_on `nr` >> gvs[return_def, raise_def, no_control_exc_def] >>
      Cases_on `lookup_nonreentrant_slot am.layouts tx.target` >>
      gvs[raise_def, no_control_exc_def] >> strip_tac >>
      drule acquire_nonreentrant_lock_no_control >> simp[no_control_exc_def])
QED

Theorem call_lock_send_eval_return_typed_case_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  (case (if nr then
           case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
             NONE => raise (Error (TypeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock tx.target slot (mut = View \/ mut = Pure)
         else return ()) (initial_state am [scope]) of
     (INL x,s'') =>
       (case send_call_value mut
          (initial_evaluation_context am.sources am.layouts tx src) s'' of
          (INL x,s'') =>
            eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body s''
        | (INR e,s'') => (INR e,s''))
   | (INR e,s'') => (INR e,s'')) = (INR (ReturnException v),st') ==>
  ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
           value_has_type ret_tv v
Proof
  strip_tac >>
  irule call_lock_send_eval_return_typed_c53 >>
  simp[bind_def, ignore_bind_def] >> metis_tac[]
QED

Theorem call_external_function_exact_selected_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts vals body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv` by (
    `check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
      metis_tac[check_contract_function_body_MEM] >>
    gvs[check_function_body_def, optionTheory.IS_SOME_EXISTS]) >>
  `no_type_error_eval
     (do
        (if nr then
           case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
             NONE => raise (Error (TypeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock
               (initial_evaluation_context am.sources am.layouts tx src).txn.target slot
               (mut = View \/ mut = Pure)
         else return ());
        send_call_value mut (initial_evaluation_context am.sources am.layouts tx src);
        eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
      od (initial_state am [scope]))` by
    metis_tac[call_lock_send_eval_prefix_no_type_error_c53,
              checked_contract_runtime_ready_def] >>
  drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def, evaluate_defaults_def,
       initial_evaluation_context_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      initial_evaluation_context_def] >>
  rpt strip_tac >> gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs(), return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_eval_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  qpat_x_assum `!msg. FST _ <> INR (Error (TypeError msg))`
    (qspec_then `msg` mp_tac) >>
  qpat_x_assum `(\(res,st). (res,st)) _ = _` mp_tac >>
  rpt (BasicProvers.TOP_CASE_TAC >> gvs[return_def, raise_def,
        vyperTypeExprSoundnessTheory.no_type_error_eval_def,
        vyperTypeExprSoundnessTheory.no_type_error_result_def]) >>
  gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  rpt strip_tac >>
  FIRST
    [qpat_x_assum `safe_cast ret_tv v = NONE` assume_tac >>
     `do
        (if nr then
           case (initial_evaluation_context am.sources am.layouts tx src).nonreentrant_slot of
             NONE => raise (Error (TypeError "nonreentrant slot missing"))
           | SOME slot => acquire_nonreentrant_lock tx.target slot (mut = View \/ mut = Pure)
         else return ());
        send_call_value mut (initial_evaluation_context am.sources am.layouts tx src);
        eval_stmts (initial_evaluation_context am.sources am.layouts tx src) body
      od (initial_state am [scope]) = (INR (ReturnException v),r)` by
       gvs[bind_def, ignore_bind_def, initial_evaluation_context_def] >>
     `value_has_type ret_tv v` by (
       drule_all call_lock_send_eval_return_typed_c53 >>
       strip_tac >> gvs[]) >>
     drule vyperTypingTheory.safe_cast_well_typed >> gvs[],
     qpat_x_assum
       `(if nr /\ mut <> View /\ mut <> Pure then
           case lookup_nonreentrant_slot am.layouts tx.target of
             NONE => return ()
           | SOME slot => release_nonreentrant_lock tx.target slot
         else return ()) r = (INR y,r'')` mp_tac >>
     Cases_on `lookup_nonreentrant_slot am.layouts tx.target` >>
     Cases_on `nr` >>
     Cases_on `mut` >>
     gvs[release_nonreentrant_lock_def, bind_def, ignore_bind_def,
         get_transient_storage_def, update_transient_def,
         return_def, raise_def, assert_def, check_def,
         vyperTypeExprSoundnessTheory.no_type_error_eval_def,
         vyperTypeExprSoundnessTheory.no_type_error_result_def]]
QED

Theorem checked_explicit_external_entry_no_type_error_selected[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  call_external_function am (initial_evaluation_context am.sources am.layouts tx src)
    nr mut ts mods args dflts vals body ret = (res,am') ==>
  no_type_error_result res
Proof
  metis_tac[call_external_function_exact_selected_no_type_error_c53]
QED
Theorem initial_state_immutables[local]:
  (initial_state am scs).immutables = am.immutables
Proof
  simp[initial_state_def]
QED

Theorem preserves_immutables_dom_same_initial_from_mid[local]:
  st0.immutables = am_c.immutables /\
  (?st_mid. st_mid.immutables = am_c.immutables /\
            preserves_immutables_dom cx st_mid st') ==>
  preserves_immutables_dom cx st0 st'
Proof
  rw[preserves_immutables_dom_def] >> metis_tac[]
QED

Theorem preserves_immutables_dom_eq_local[local]:
  st'.immutables = st.immutables ==> preserves_immutables_dom cx st st'
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

Theorem preserves_immutables_dom_trans_local[local]:
  preserves_immutables_dom cx st1 st2 /\
  preserves_immutables_dom cx st2 st3 ==>
  preserves_immutables_dom cx st1 st3
Proof
  rw[preserves_immutables_dom_def] >>
  `?imms2. ALOOKUP st2.immutables cx.txn.target = SOME imms2` by
    (gvs[IS_SOME_EXISTS] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem call_body_prefix_preserves_immutables_dom[local]:
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx;
     eval_stmts cx body
   od (initial_state am_c [env]) = (res,st')) ==>
  preserves_immutables_dom cx (initial_state am_c [env]) st'
Proof
  rw[bind_def, ignore_bind_def] >>
  imp_res_tac call_lock_action_preserves_immutables >>
  gvs[AllCaseEqs()] >>
  TRY (`s''.immutables = am_c.immutables` by
         (qpat_x_assum `(case cx.nonreentrant_slot of NONE => _ | SOME slot => _) _ = (INL (),s'')` mp_tac >>
          Cases_on `cx.nonreentrant_slot` >> rw[return_def, raise_def, initial_state_def] >>
          imp_res_tac acquire_nonreentrant_lock_immutables >> gvs[initial_state_def]) >>
       gvs[]) >>
  TRY (`s''.immutables = am_c.immutables` by
         (qpat_x_assum `(case cx.nonreentrant_slot of NONE => _ | SOME slot => _) _ = (INR e,s'')` mp_tac >>
          Cases_on `cx.nonreentrant_slot` >> rw[return_def, raise_def, initial_state_def] >>
          imp_res_tac acquire_nonreentrant_lock_immutables >> gvs[initial_state_def]) >>
       gvs[]) >>
  TRY (qpat_x_assum `return () _ = (INL (),s'')` mp_tac >>
       rw[return_def, initial_state_def]) >>
  imp_res_tac send_call_value_preserves_immutables >>
  imp_res_tac eval_stmts_preserves_immutables_addr_dom >>
  imp_res_tac eval_stmts_preserves_immutables_dom >>
  fs[preserves_immutables_dom_def, initial_state_immutables] >> rw[] >> gvs[]
QED

Theorem preserves_immutables_dom_final_lookup_exists_in_initial[local]:
  preserves_immutables_dom cx st0 st_body /\
  st0.immutables = am_c.immutables /\
  st_unlocked.immutables = st_body.immutables /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP st_unlocked.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?tv0 y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y)
Proof
  rw[preserves_immutables_dom_def] >>
  Cases_on `ALOOKUP am_c.immutables cx.txn.target` >>
  gvs[get_source_immutables_def]
  >- (Cases_on `ALOOKUP st_body.immutables cx.txn.target` >>
      gvs[get_source_immutables_def] >>
      qpat_x_assum `!tgt. _` (qspec_then `cx.txn.target` mp_tac) >>
      simp[IS_SOME_EXISTS]) >>
  rename1 `ALOOKUP am_c.immutables cx.txn.target = SOME imms0` >>
  Cases_on `ALOOKUP st_body.immutables cx.txn.target` >>
  gvs[get_source_immutables_def] >>
  rename1 `ALOOKUP st_body.immutables cx.txn.target = SOME imms1` >>
  qpat_x_assum `!src' n. _`
    (qspecl_then [`src`,`id`] mp_tac) >>
  simp[IS_SOME_EXISTS, EXISTS_PROD]
QED

Theorem call_external_function_deploy_success_final_lookup_source_exists_in_constants[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,x) ==>
  ?tv0 y.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y)
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  strip_tac >>
  gvs[]
  >- (imp_res_tac call_body_prefix_preserves_immutables_dom >>
      `st_unlocked.immutables = st_body.immutables` by
        (Cases_on `nr` >> gvs[return_def] >>
         Cases_on `mut = View` >> gvs[return_def] >>
         Cases_on `mut = Pure` >> gvs[return_def] >>
         Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
         imp_res_tac release_nonreentrant_lock_immutables) >>
      gvs[abstract_machine_from_state_def] >>
      irule preserves_immutables_dom_final_lookup_exists_in_initial >>
      qexists `initial_state am_c [env]` >>
      qexists `st_body` >>
      qexists `am_c with immutables := st_body.immutables` >>
      qexists `tv` >>
      qexists `x` >> simp[initial_state_def]) >>
  imp_res_tac call_body_prefix_preserves_immutables_dom >>
  `st_unlocked.immutables = st_body.immutables` by
    (Cases_on `nr` >> gvs[return_def] >>
     Cases_on `mut = View` >> gvs[return_def] >>
     Cases_on `mut = Pure` >> gvs[return_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[return_def] >>
     imp_res_tac release_nonreentrant_lock_immutables) >>
  gvs[abstract_machine_from_state_def] >>
  irule preserves_immutables_dom_final_lookup_exists_in_initial >>
      qexists `initial_state am_c [env]` >>
      qexists `st_body` >>
      qexists `am_c with immutables := st_body.immutables` >>
      qexists `tv` >>
      qexists `x` >> simp[initial_state_def]
QED

Theorem deploy_call_success_transports_bare_global_readiness_clause[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules all_mods) ty = SOME tv) ==>
  !src id ty tv v.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
    evaluate_type (type_env_all_modules all_mods) ty = SOME tv
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_final_lookup_source_exists_in_constants >>
  strip_tac >>
  drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
  strip_tac >>
  gvs[] >>
  first_x_assum irule >>
  first_assum (irule_at Any) >>
  first_assum (irule_at Any)
QED

Theorem deploy_context_constants_bare_globals_type_ready[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  `(((am:abstract_machine) with exports updated_by CONS (deploy_tx.target,exps)) with
      immutables updated_by CONS (deploy_tx.target,imms)) =
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
              exports updated_by CONS (deploy_tx.target,exps)|>)` by simp[] >>
  gvs[] >>
  drule deploy_constants_setup_bare_globals_ready >>
  strip_tac >>
  first_x_assum (qspecl_then [`deploy_tx`, `(deploy_tx.target,mods)::am.sources`, `imms`,
    `(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am_c`, `((am:abstract_machine) with exports updated_by CONS (deploy_tx.target,exps))`] mp_tac) >>
  gvs[get_tenv_def, initial_evaluation_context_def, alistTheory.ALOOKUP_def] >>
  strip_tac >>
  first_x_assum (qspecl_then [`src`,`id`,`ty`,`tv`,`v`] mp_tac) >>
  simp[]
QED

Theorem deploy_call_success_scalar_bare_global_type_from_constants[local]:
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret = (INL v_out,am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type (type_env_all_modules all_mods) ty = SOME tv) /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules all_mods) ty = SOME tv
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_final_lookup_source_exists_in_constants >>
  strip_tac >>
  gvs[] >>
  rename1 `FLOOKUP _ _ = SOME (tv0,y0)` >>
  `evaluate_type (type_env_all_modules all_mods) ty = SOME tv0` by
    (first_x_assum (qspecl_then [`src`,`id`,`ty`,`tv0`,`y0`] mp_tac) >>
     simp[]) >>
  `?y'.
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id = SOME (tv0,y')` by
    (drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
     simp[]) >>
  gvs[]
QED

Theorem deploy_constructor_success_bare_global_type_from_constants[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  call_external_function
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    nr mut ts mods args dflts deploy_tx.args body ret = (INL v',am_ctor) /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_ctor.immutables deploy_tx.target of SOME m => m | NONE => [])) id =
    SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  qabbrev_tac
    `cx0 = ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)` >>
  `cx0.in_deploy` by simp[Abbr `cx0`] >>
  `cx0.txn.target = deploy_tx.target` by
    simp[Abbr `cx0`, initial_evaluation_context_def] >>
  `call_external_function
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0 nr mut ts mods args dflts deploy_tx.args body ret = (INL v',am_ctor)` by
    simp[Abbr `cx0`] >>
  `evaluate_all_constants cx0
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0.txn.target mods = SOME am_c` by
    gvs[Abbr `cx0`, initial_evaluation_context_def] >>
  `!src id ty tv v.
      FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
      evaluate_type (type_env_all_modules mods) ty = SOME tv` by
    (rpt strip_tac >>
     irule deploy_context_constants_bare_globals_type_ready >>
     simp[] >>
     metis_tac[]) >>
  irule deploy_call_success_scalar_bare_global_type_from_constants >>
  simp[] >>
  qexistsl
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `am_c`, `am_ctor`, `args`, `body`, `call_art`, `cx0`, `dflts`,
     `id`, `mut`, `nr`, `ret`, `src`, `ts`, `v`, `v'`, `deploy_tx.args`] >>
  gvs[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`src'`,`id'`,`ty'`,`tv'`,`v''`] mp_tac) >>
  simp[]
QED

Theorem evaluate_all_constants_preserves_layouts[local]:
  evaluate_all_constants cx am addr mods = SOME am_c ==>
  am_c.layouts = am.layouts
Proof
  qid_spec_tac `am_c` >> qid_spec_tac `am` >>
  Induct_on `mods` >- rw[evaluate_all_constants_def] >>
  Cases_on `h` >>
  rw[evaluate_all_constants_def] >>
  gvs[AllCaseEqs(), merge_constants_def] >>
  first_x_assum drule >> simp[]
QED

Theorem call_external_function_deploy_success_preserves_layouts:
  !am cx nr mut ts all_mods args dflts vals body ret v am_out am_c.
  cx.in_deploy /\
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
    (INL v, am_out) /\
  evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c ==>
  am_out.layouts = am.layouts
Proof
  rw[] >>
  drule_all call_external_function_deploy_success_cases >>
  drule evaluate_all_constants_preserves_layouts >>
  strip_tac >>
  strip_tac >>
  gvs[abstract_machine_from_state_def]
QED

Theorem load_contract_success_constructor_constants_context:
  load_contract am deploy_tx mods exps = INL am_deployed ==>
  ?imms ts mut nr args dflts ret body v am_ctor am_c.
    initial_immutables (type_env_all_modules mods) mods = SOME imms /\
    ts = (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) /\
    lookup_function NONE deploy_tx.function_name Deploy ts = SOME (mut,nr,args,dflts,ret,body) /\
    call_external_function
      (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                 exports updated_by CONS (deploy_tx.target,exps)|>)
      ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE) with in_deploy := T)
      nr mut ts mods args dflts deploy_tx.args body ret = (INL v, am_ctor) /\
    evaluate_all_constants
      ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE) with in_deploy := T)
      (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                 exports updated_by CONS (deploy_tx.target,exps)|>)
      deploy_tx.target mods = SOME am_c /\
    am_ctor.layouts = am.layouts /\
    am_deployed = am_ctor with sources updated_by CONS (deploy_tx.target,mods)
Proof
  rw[] >>
  drule load_contract_success_cases >> strip_tac >> gvs[] >>
  qspecl_then
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `((initial_evaluation_context ((deploy_tx.target,mods)::am.sources)
          am.layouts deploy_tx NONE) with in_deploy := T)`,
     `nr`, `mut`, `(case ALOOKUP mods NONE of SOME ts => ts | NONE => [])`,
     `mods`, `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`]
    mp_tac call_external_function_deploy_success_evaluate_all_constants >>
  simp[] >> strip_tac >>
  qexists `am_c` >>
  gvs[initial_evaluation_context_def] >>
  qspecl_then
    [`am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>`,
     `<|stk := [(NONE,deploy_tx.function_name)]; txn := deploy_tx;
        sources := (deploy_tx.target,mods)::am.sources; layouts := am.layouts;
        in_deploy := T;
        nonreentrant_slot := lookup_nonreentrant_slot am.layouts deploy_tx.target|>`,
     `nr`, `mut`, `(case ALOOKUP mods NONE of SOME ts => ts | NONE => [])`,
     `mods`, `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`, `am_c`]
    mp_tac call_external_function_deploy_success_preserves_layouts >>
  gvs[initial_evaluation_context_def]
QED

Theorem load_contract_constructor_context_bare_global_type_from_constants[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  call_external_function
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    nr mut (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods args dflts
    deploy_tx.args body ret = (INL v',am_ctor) /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
  FLOOKUP
    (get_source_immutables src
      (case ALOOKUP am_ctor.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
  evaluate_type (type_env_all_modules mods) ty = SOME tv
Proof
  rw[] >>
  qabbrev_tac
    `cx0 = ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)` >>
  `cx0.in_deploy` by simp[Abbr `cx0`] >>
  `cx0.txn.target = deploy_tx.target` by
    simp[Abbr `cx0`, initial_evaluation_context_def] >>
  `call_external_function
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0 nr mut (case ALOOKUP mods NONE of SOME ts => ts | NONE => []) mods args dflts
     deploy_tx.args body ret = (INL v',am_ctor)` by
    simp[Abbr `cx0`] >>
  `evaluate_all_constants cx0
     (am with <|immutables updated_by CONS (deploy_tx.target,imms);
                exports updated_by CONS (deploy_tx.target,exps)|>)
     cx0.txn.target mods = SOME am_c` by
    gvs[Abbr `cx0`, initial_evaluation_context_def] >>
  `!src id ty tv v.
      FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
      FLOOKUP
        (get_source_immutables src
          (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
      evaluate_type (type_env_all_modules mods) ty = SOME tv` by
    (rpt strip_tac >>
     irule deploy_context_constants_bare_globals_type_ready >>
     simp[] >>
     metis_tac[]) >>
  metis_tac[deploy_call_success_scalar_bare_global_type_from_constants]
QED

Theorem load_contract_deployed_bare_globals_immutables_ready_clause[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty tv v.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
    evaluate_type
      (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
      ty = SOME tv
Proof
  rw[] >>
  drule load_contract_success_constructor_constants_context >>
  strip_tac >>
  gvs[] >>
  gvs[get_tenv_def, initial_evaluation_context_def] >>
  irule load_contract_constructor_context_bare_global_type_from_constants >>
  gvs[initial_evaluation_context_def] >>
  qexistsl
    [`am`, `am_c`, `am_ctor`, `args`, `body`, `call_art`, `deploy_tx`,
     `dflts`, `exps`, `id`, `mut`, `nr`, `ret`, `src`, `v`, `v'`] >>
  gvs[]
QED

Theorem deployed_toplevel_vtypes_immutables_ready_clause[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target /\
  (!src id ty tv v.
     FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty /\
     FLOOKUP
       (get_source_immutables src
         (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
     evaluate_type
       (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
       ty = SOME tv) ==>
  !src id ty ts.
    FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
    get_module_code
      (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE) src = SOME ts ==>
    (!is_transient typ id_str.
       find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) ==>
       typ = ty) /\
    (!is_transient kt vt id_str.
       find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) ==>
       F) /\
    (find_var_decl_by_num id ts = NONE ==>
     !tv v.
       FLOOKUP
         (get_source_immutables src
           (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id = SOME (tv,v) ==>
       evaluate_type
         (get_tenv (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE))
         ty = SOME tv)
Proof
  rw[] >>
  drule load_contract_success_cases >> strip_tac >> gvs[] >>
  `ALOOKUP ((deploy_tx.target,mods)::am_ctor.sources) call_tx.target = SOME mods` by
    simp[] >>
  `(!src id vt.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME vt ==>
      well_formed_vtype (type_env_all_modules mods) vt) /\
    (!src id ty.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\
      FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==>
      ?ts is_transient typ id_str.
        get_module_code
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) src = SOME ts /\
        find_var_decl_by_num id ts = SOME (StorageVarDecl is_transient typ,id_str) /\
        typ = ty /\
        IS_SOME (evaluate_type (type_env_all_modules mods) typ) /\
        IS_SOME (lookup_var_slot_from_layout
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) is_transient src id_str)) /\
    (!src id kt vt.
      FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (HashMapT kt vt) ==>
      ?ts is_transient id_str.
        get_module_code
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) src = SOME ts /\
        find_var_decl_by_num id ts = SOME (HashMapVarDecl is_transient kt vt,id_str) /\
        IS_SOME (lookup_var_slot_from_layout
          (initial_evaluation_context ((deploy_tx.target,mods)::am_ctor.sources)
             am_ctor.layouts call_tx src) is_transient src id_str))` by
    (irule check_contract_toplevel_vtypes_consistent_initial >> simp[]) >>
  rpt conj_tac
  >- (Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
      >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
      rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
      drule check_contract_bare_globals_consistent_initial >>
      disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      rw[] >> gvs[get_module_code_def, initial_evaluation_context_def])
  >- (rpt strip_tac >>
      Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
      >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
            (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
      rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
      drule check_contract_bare_globals_consistent_initial >>
      disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
      simp[get_module_code_def, initial_evaluation_context_def] >>
      rw[] >> gvs[get_module_code_def, initial_evaluation_context_def])
  >> rpt strip_tac >>
     Cases_on `FLOOKUP call_art.cta_bare_globals (src,id)` >> gvs[]
     >- (qpat_x_assum `!src id ty. FLOOKUP call_art.cta_toplevel_vtypes (src,id) = SOME (Type ty) /\ FLOOKUP call_art.cta_bare_globals (src,id) = NONE ==> _`
           (qspecl_then [`src`,`id`,`ty`] mp_tac) >>
            simp[get_module_code_def, initial_evaluation_context_def] >>
            rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
     rename1 `FLOOKUP call_art.cta_bare_globals (src,id) = SOME bare_ty` >>
     `bare_ty = ty` by
       (drule check_contract_bare_globals_consistent_initial >>
        disch_then (qspecl_then [`call_tx`,`(deploy_tx.target,mods)::am_ctor.sources`,`src`,`id`,`bare_ty`] mp_tac) >>
        simp[get_module_code_def, initial_evaluation_context_def] >>
        rw[] >> gvs[get_module_code_def, initial_evaluation_context_def]) >>
     gvs[] >>
     qpat_x_assum `!src' id' ty' tv' v'. FLOOKUP call_art.cta_bare_globals (src',id') = SOME ty' /\ FLOOKUP _ id' = SOME (tv',v') ==> _`
       (qspecl_then [`src`,`id`,`bare_ty`,`tv`,`v`] mp_tac) >>
     simp[]
QED

Theorem deploy_context_constants_bare_globals_lookup_exists[local]:
  check_contract F am.layouts deploy_tx.target mods = SOME call_art /\
  initial_immutables (type_env_all_modules mods) mods = SOME imms /\
  evaluate_all_constants
    ((initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE)
       with in_deploy := T)
    (am with <|immutables updated_by CONS (deploy_tx.target,imms);
               exports updated_by CONS (deploy_tx.target,exps)|>)
    deploy_tx.target mods = SOME am_c /\
  FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
  ?tv v.
    FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables deploy_tx.target of SOME m => m | NONE => [])) id =
    SOME (tv,v)
Proof
  rw[] >>
  drule deploy_constants_setup_bare_globals_ready >>
  simp[get_tenv_def, initial_evaluation_context_def, IS_SOME_EXISTS, EXISTS_PROD] >>
  disch_then (qspecl_then [`deploy_tx`, `(deploy_tx.target,mods)::am.sources`,
    `(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am_c`, `am with exports updated_by CONS (deploy_tx.target,exps)`] mp_tac) >>
  simp[get_tenv_def, initial_evaluation_context_def, IS_SOME_EXISTS, EXISTS_PROD] >>
  impl_tac >- gvs[initial_evaluation_context_def] >>
  rw[]
QED

Theorem call_external_function_deploy_success_final_lookup_exists_from_constants[local]:
  !cx am nr mut ts all_mods args dflts vals body ret v am_out am_c src id.
    cx.in_deploy /\
    call_external_function am cx nr mut ts all_mods args dflts vals body ret =
      (INL v, am_out) /\
    evaluate_all_constants cx am cx.txn.target all_mods = SOME am_c /\
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_c.immutables cx.txn.target of SOME m => m | NONE => [])) id) ==>
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_out.immutables cx.txn.target of SOME m => m | NONE => [])) id)
Proof
  rw[IS_SOME_EXISTS, EXISTS_PROD] >>
  drule_all call_external_function_deploy_success_preserves_immutable_type_tags_from_constants >>
  strip_tac >>
  simp[IS_SOME_EXISTS]
QED

Theorem load_contract_deployed_bare_globals_immutables_ready_exists_clause[local]:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  !src id ty.
    FLOOKUP call_art.cta_bare_globals (src,id) = SOME ty ==>
    IS_SOME (FLOOKUP
      (get_source_immutables src
        (case ALOOKUP am_deployed.immutables call_tx.target of SOME m => m | NONE => [])) id)
Proof
  rw[] >>
  drule load_contract_success_constructor_constants_context >>
  strip_tac >>
  gvs[] >>
  qspecl_then [`(initial_evaluation_context ((deploy_tx.target,mods)::am.sources) am.layouts deploy_tx NONE with in_deploy := T)`,
    `am with <|exports updated_by CONS (deploy_tx.target,exps);
              immutables updated_by CONS (deploy_tx.target,imms)|>`,
    `nr`, `mut`, `case ALOOKUP mods NONE of NONE => [] | SOME ts => ts`, `mods`,
    `args`, `dflts`, `deploy_tx.args`, `body`, `ret`, `v`, `am_ctor`, `am_c`, `src`, `id`]
    mp_tac call_external_function_deploy_success_final_lookup_exists_from_constants >>
  simp[initial_evaluation_context_def] >>
  disch_then irule >>
  conj_tac
  >- (simp[IS_SOME_EXISTS, EXISTS_PROD] >>
      irule deploy_context_constants_bare_globals_lookup_exists >>
      qexistsl [`am`,`call_art`,`exps`,`imms`,`mods`,`ty`] >>
      gvs[]) >>
  gvs[initial_evaluation_context_def]
QED

Theorem load_contract_establishes_immutables_ready:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME call_art /\
  call_tx.target = deploy_tx.target ==>
  immutables_ready call_art.cta_bare_globals call_art.cta_toplevel_vtypes
    (initial_evaluation_context am_deployed.sources am_deployed.layouts call_tx NONE)
    am_deployed.immutables
Proof
  rw[immutables_ready_def]
  >- (simp[initial_evaluation_context_def] >>
      irule load_contract_deployed_bare_globals_immutables_ready_exists_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `mods`, `ty`] >>
      gvs[])
  >- (irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `id`, `mods`, `src`, `v`] >>
      gvs[initial_evaluation_context_def])
  >- (irule (cj 1 deployed_toplevel_vtypes_immutables_ready_clause) >>
      qexistsl [`am`, `am_deployed`, `call_art`, `call_tx`, `deploy_tx`, `exps`,
                `id`, `id_str`, `is_transient`, `mods`, `src`, `ts`] >>
      simp[] >>
      rpt strip_tac >>
      rename1 `FLOOKUP call_art.cta_bare_globals (bg_src,bg_id) = SOME bg_ty` >>
      rename1 `FLOOKUP _ bg_id = SOME (bg_tv,bg_v)` >>
      irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `bg_id`, `mods`, `bg_src`, `bg_v`] >>
      gvs[initial_evaluation_context_def])
  >- (strip_tac >>
      irule (cj 2 deployed_toplevel_vtypes_immutables_ready_clause) >>
      qexistsl [`am`, `am_deployed`, `call_art`, `call_tx`, `deploy_tx`, `exps`,
                `id`, `id_str`, `is_transient`, `kt`, `mods`, `src`, `ts`, `ty`, `vt`] >>
      simp[] >>
      rpt strip_tac >>
      rename1 `FLOOKUP call_art.cta_bare_globals (bg_src,bg_id) = SOME bg_ty` >>
      rename1 `FLOOKUP _ bg_id = SOME (bg_tv,bg_v)` >>
      irule load_contract_deployed_bare_globals_immutables_ready_clause >>
      qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `bg_id`, `mods`, `bg_src`, `bg_v`] >>
      gvs[initial_evaluation_context_def])
  >> irule (cj 3 deployed_toplevel_vtypes_immutables_ready_clause) >>
     qexistsl [`am`, `call_art`, `deploy_tx`, `exps`, `id`, `mods`, `src`, `ts`, `v`] >>
     simp[] >>
     rpt strip_tac >>
     drule load_contract_deployed_bare_globals_immutables_ready_clause >>
     simp[] >>
     disch_then drule >>
     simp[] >>
     disch_then (qspecl_then [`src'`, `id'`, `ty'`, `tv'`, `v'`] mp_tac) >>
     simp[initial_evaluation_context_def] >>
     strip_tac >>
     gvs[initial_evaluation_context_def]
QED

Theorem load_contract_establishes_checked_contract_runtime_ready:
  load_contract am deploy_tx mods exps = INL am_deployed /\
  check_contract F am_deployed.layouts call_tx.target mods = SOME art /\
  call_tx.target = deploy_tx.target ==>
  checked_contract_runtime_ready art mods am_deployed call_tx
Proof
  rw[checked_contract_runtime_ready_def]
  >- (drule load_contract_success_cases >> strip_tac >> gvs[])
  >> irule load_contract_establishes_immutables_ready
  >> qexistsl [`am`, `deploy_tx`, `exps`, `mods`]
  >> simp[]
QED

(* The obsolete generated-getter materialisability pipeline formerly here
   tracked the pre-typed build_getter AST.  Selected getter soundness below
   now proceeds from checked_public_getter_body_typing_package and generic
   expression/statement preservation. *)

Definition getter_context_equiv_def[local]:
  getter_context_equiv cx1 cx2 <=>
    cx1.sources = cx2.sources /\
    cx1.layouts = cx2.layouts /\
    cx1.txn.target = cx2.txn.target
End

Theorem getter_context_equiv_initial_empty_tx[local]:
  getter_context_equiv
    (initial_evaluation_context sources layouts tx src)
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src)
Proof
  simp[getter_context_equiv_def, initial_evaluation_context_def]
QED

Theorem getter_context_equiv_get_tenv[local]:
  getter_context_equiv cx1 cx2 ==> get_tenv cx1 = get_tenv cx2
Proof
  rw[getter_context_equiv_def, get_tenv_def]
QED
Theorem getter_context_equiv_get_storage_backend[local]:
  getter_context_equiv cx1 cx2 ==>
  get_storage_backend cx1 is_transient = get_storage_backend cx2 is_transient
Proof
  Cases_on `is_transient` >>
  simp[getter_context_equiv_def, get_storage_backend_def,
       get_transient_storage_def, get_accounts_def, bind_def, return_def,
       FUN_EQ_THM]
QED

Theorem getter_context_equiv_read_storage_slot[local]:
  getter_context_equiv cx1 cx2 ==>
  read_storage_slot cx1 is_transient slot tv =
  read_storage_slot cx2 is_transient slot tv
Proof
  strip_tac >>
  drule getter_context_equiv_get_storage_backend >>
  disch_then (fn th => rewrite_tac[read_storage_slot_def, th])
QED

Theorem getter_context_equiv_check_array_bounds[local]:
  getter_context_equiv cx1 cx2 ==>
  check_array_bounds cx1 tvl v = check_array_bounds cx2 tvl v
Proof
  strip_tac >>
  `!tr. get_storage_backend cx1 tr = get_storage_backend cx2 tr` by
    metis_tac[getter_context_equiv_get_storage_backend] >>
  simp[oneline check_array_bounds_def, FUN_EQ_THM, AllCaseEqs()]
QED

Theorem getter_context_equiv_eval_Subscript[local]:
  getter_context_equiv cx1 cx2 /\
  eval_expr cx1 e1 = eval_expr cx2 e1 /\
  eval_expr cx1 e2 = eval_expr cx2 e2 ==>
  eval_expr cx1 (Subscript ty e1 e2) =
  eval_expr cx2 (Subscript ty e1 e2)
Proof
  rpt strip_tac >>
  `get_tenv cx1 = get_tenv cx2` by
    metis_tac[getter_context_equiv_get_tenv] >>
  `!tvl v. check_array_bounds cx1 tvl v = check_array_bounds cx2 tvl v` by
    metis_tac[getter_context_equiv_check_array_bounds] >>
  `!tr slot tv. read_storage_slot cx1 tr slot tv =
                read_storage_slot cx2 tr slot tv` by
    metis_tac[getter_context_equiv_read_storage_slot] >>
  simp[Ntimes evaluate_def 2]
QED

Theorem eval_Name_context_irrelevant[local]:
  eval_expr cx1 (Name kt s) = eval_expr cx2 (Name kt s)
Proof
  simp[Ntimes evaluate_def 2]
QED

Theorem build_getter_eval_context_equiv[local]:
  !e kt vt n args ret exp cx1 cx2.
    build_getter e kt vt n = (args,ret,exp) /\
    getter_context_equiv cx1 cx2 /\
    eval_expr cx1 e = eval_expr cx2 e ==>
    eval_expr cx1 exp = eval_expr cx2 exp
Proof
  recInduct build_getter_ind >> rpt strip_tac >>
  qpat_x_assum `build_getter _ _ _ _ = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `is_ArrayT vt` >> simp[] >>
  rpt (pairarg_tac >> gvs[]) >> rw[]
  >- (first_x_assum irule >>
      conj_tac >-
        (irule getter_context_equiv_eval_Subscript >>
         simp[Ntimes evaluate_def 2]) >>
      simp[])
  >- (`eval_expr cx1 (Name kt (toString n)) =
       eval_expr cx2 (Name kt (toString n))` by
        simp[eval_Name_context_irrelevant] >>
      metis_tac[getter_context_equiv_eval_Subscript])
  >> first_x_assum irule >>
  conj_tac >-
    (`eval_expr cx1 (Name kt (toString n)) =
      eval_expr cx2 (Name kt (toString n))` by
       simp[eval_Name_context_irrelevant] >>
     metis_tac[getter_context_equiv_eval_Subscript]) >>
  simp[] >>
  `eval_expr cx1 (Name kt (toString n)) =
   eval_expr cx2 (Name kt (toString n))` by
    simp[eval_Name_context_irrelevant] >>
  metis_tac[getter_context_equiv_eval_Subscript]
QED

Theorem getter_context_equiv_lookup_global[local]:
  getter_context_equiv cx1 cx2 ==>
  lookup_global cx1 src n = lookup_global cx2 src n
Proof
  strip_tac >>
  `get_module_code cx1 src = get_module_code cx2 src` by
    gvs[getter_context_equiv_def, get_module_code_def] >>
  `get_tenv cx1 = get_tenv cx2` by
    metis_tac[getter_context_equiv_get_tenv] >>
  `!tr src' id. lookup_var_slot_from_layout cx1 tr src' id =
                lookup_var_slot_from_layout cx2 tr src' id` by
    gvs[getter_context_equiv_def, lookup_var_slot_from_layout_def] >>
  `get_address_immutables cx1 = get_address_immutables cx2` by
    gvs[getter_context_equiv_def, get_address_immutables_def,
        FUN_EQ_THM] >>
  `!src'. get_immutables cx1 src' = get_immutables cx2 src'` by
    simp[get_immutables_def] >>
  `!tr slot tv. read_storage_slot cx1 tr slot tv =
                read_storage_slot cx2 tr slot tv` by
    metis_tac[getter_context_equiv_read_storage_slot] >>
  simp[lookup_global_def, bind_def, AllCaseEqs()]
QED

Theorem getter_context_equiv_eval_TopLevelName[local]:
  getter_context_equiv cx1 cx2 ==>
  eval_expr cx1 (TopLevelName ty key) =
  eval_expr cx2 (TopLevelName ty key)
Proof
  strip_tac >> PairCases_on `key` >>
  simp[Ntimes evaluate_def 2, getter_context_equiv_lookup_global]
QED

Theorem getter_context_equiv_materialise[local]:
  getter_context_equiv cx1 cx2 ==>
  materialise cx1 tv = materialise cx2 tv
Proof
  strip_tac >> Cases_on `tv` >> simp[materialise_def] >>
  metis_tac[getter_context_equiv_read_storage_slot]
QED

Theorem getter_context_equiv_eval_single_Return[local]:
  getter_context_equiv cx1 cx2 /\
  eval_expr cx1 exp = eval_expr cx2 exp ==>
  eval_stmts cx1 [Return (SOME exp)] =
  eval_stmts cx2 [Return (SOME exp)]
Proof
  rpt strip_tac >>
  `!tv. materialise cx1 tv = materialise cx2 tv` by
    metis_tac[getter_context_equiv_materialise] >>
  `eval_stmt cx1 (Return (SOME exp)) =
   eval_stmt cx2 (Return (SOME exp))` by
    simp[Ntimes evaluate_def 2, bind_def, AllCaseEqs()] >>
  once_rewrite_tac[evaluate_def] >>
  sym_tac >> once_rewrite_tac[evaluate_def] >> sym_tac >>
  simp[Ntimes evaluate_def 2, bind_def]
QED
Theorem build_getter_int_calls_empty[local]:
  !e kt vt n args ret exp.
    int_calls_expr e = [] /\
    build_getter e kt vt n = (args,ret,exp) ==>
    int_calls_expr exp = []
Proof
  recInduct build_getter_ind >> rpt strip_tac
  >- (Cases_on `is_ArrayT vt`
      >- (qpat_x_assum `build_getter e kt (Type vt) n = _` mp_tac >>
          simp[Once build_getter_def] >>
          Cases_on `build_getter (Subscript vt e (Name kt (toString n)))
                      (BaseT (UintT 256)) (Type (ArrayT_type vt)) (SUC n)` >>
          Cases_on `r` >> gvs[] >>
          rpt strip_tac >> gvs[] >>
          qpat_x_assum `int_calls_expr _ = [] ==> int_calls_expr _ = []` irule >>
          simp[int_calls_expr_def]) >>
      qpat_x_assum `build_getter e kt (Type vt) n = _` mp_tac >>
      simp[Once build_getter_def, int_calls_expr_def] >>
      rpt strip_tac >> gvs[int_calls_expr_def]) >>
  qpat_x_assum `build_getter e kt (HashMapT typ vtyp) n = _` mp_tac >>
  simp[Once build_getter_def] >>
  Cases_on `build_getter
    (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e
      (Name kt (toString n))) typ vtyp (SUC n)` >>
  Cases_on `r` >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `int_calls_expr _ = [] ==> int_calls_expr _ = []` irule >>
  simp[int_calls_expr_def]
QED

Theorem selected_public_getter_body_int_calls_empty:
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) ==>
  int_calls_stmts body = []
Proof
  rpt strip_tac >>
  Cases_on `decl` >>
  gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (drule_all array_public_getter_tuple_shape >> strip_tac >> gvs[] >>
          `int_calls_expr (TopLevelName t (src,s)) = []` by
            simp[int_calls_expr_def] >>
          `int_calls_expr exp = []` by
            metis_tac[build_getter_int_calls_empty] >>
          simp[int_calls_stmt_def, int_calls_expr_def]) >>
      gvs[external_getter_tuple_def, getter_def] >>
      simp[int_calls_expr_def, int_calls_stmt_def]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  `int_calls_expr (TopLevelName NoneT (src,fn)) = []` by
    simp[int_calls_expr_def] >>
  `int_calls_expr exp = []` by
    metis_tac[build_getter_int_calls_empty] >>
  simp[int_calls_expr_def, int_calls_stmt_def]
QED

Theorem selected_public_getter_body_eval_context_equiv:
  is_public_getter_decl fn decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  getter_context_equiv cx1 cx2 ==>
  ?exp. body = [Return (SOME exp)] /\
        eval_expr cx1 exp = eval_expr cx2 exp
Proof
  Cases_on `decl` >>
  gvs[is_public_getter_decl_def, external_getter_tuple_def]
  >- (Cases_on `v` >> gvs[] >>
      Cases_on `is_ArrayT t` >> gvs[]
      >- (rpt strip_tac >>
          drule_all array_public_getter_tuple_shape >> strip_tac >> gvs[] >>
          irule build_getter_eval_context_equiv >> simp[] >>
          metis_tac[getter_context_equiv_eval_TopLevelName]) >>
      rpt strip_tac >>
      gvs[external_getter_tuple_def] >>
      metis_tac[getter_context_equiv_eval_TopLevelName]) >>
  Cases_on `v` >> gvs[is_public_getter_decl_def] >>
  rpt strip_tac >>
  drule_all hashmap_public_getter_tuple_shape >> strip_tac >> gvs[] >>
  irule build_getter_eval_context_equiv >> simp[] >>
  metis_tac[getter_context_equiv_eval_TopLevelName]
QED


Theorem fn_sigs_consistent_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  cx1.in_deploy = cx2.in_deploy ==>
  (fn_sigs_consistent sigs cx1 <=> fn_sigs_consistent sigs cx2)
Proof
  simp[fn_sigs_consistent_def]
QED

Theorem fn_sigs_declared_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  cx1.in_deploy = cx2.in_deploy ==>
  (fn_sigs_declared_complete sigs cx1 <=>
   fn_sigs_declared_complete sigs cx2)
Proof
  simp[fn_sigs_declared_complete_def]
QED

Theorem toplevel_vtypes_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) ==>
  (toplevel_vtypes_complete vtypes cx1 <=>
   toplevel_vtypes_complete vtypes cx2)
Proof
  simp[toplevel_vtypes_complete_def]
QED

Theorem bare_globals_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) ==>
  (bare_globals_complete globals cx1 <=>
   bare_globals_complete globals cx2)
Proof
  simp[bare_globals_complete_def]
QED

Theorem bare_global_assignable_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) ==>
  (bare_global_assignable_complete globals cx1 <=>
   bare_global_assignable_complete globals cx2)
Proof
  simp[bare_global_assignable_complete_def]
QED

Theorem flag_members_complete_context_cong[local]:
  (!src. get_module_code cx1 src = get_module_code cx2 src) ==>
  (flag_members_complete members cx1 <=>
   flag_members_complete members cx2)
Proof
  simp[flag_members_complete_def]
QED

Theorem env_context_consistent_context_cong[local]:
  get_tenv cx1 = get_tenv cx2 /\
  current_module cx1 = current_module cx2 /\
  cx1.in_deploy = cx2.in_deploy /\
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  (!tr src id. lookup_var_slot_from_layout cx1 tr src id =
               lookup_var_slot_from_layout cx2 tr src id) ==>
  (env_context_consistent env cx1 <=> env_context_consistent env cx2)
Proof
  rpt strip_tac >>
  `fn_sigs_consistent env.fn_sigs cx1 <=>
   fn_sigs_consistent env.fn_sigs cx2` by
    (irule fn_sigs_consistent_context_cong >> simp[]) >>
  `fn_sigs_declared_complete env.fn_sigs cx1 <=>
   fn_sigs_declared_complete env.fn_sigs cx2` by
    (irule fn_sigs_declared_complete_context_cong >> simp[]) >>
  `toplevel_vtypes_complete env.toplevel_vtypes cx1 <=>
   toplevel_vtypes_complete env.toplevel_vtypes cx2` by
    (irule toplevel_vtypes_complete_context_cong >> simp[]) >>
  `bare_globals_complete env.bare_globals cx1 <=>
   bare_globals_complete env.bare_globals cx2` by
    (irule bare_globals_complete_context_cong >> simp[]) >>
  `bare_global_assignable_complete env.bare_global_assignable cx1 <=>
   bare_global_assignable_complete env.bare_global_assignable cx2` by
    (irule bare_global_assignable_complete_context_cong >> simp[]) >>
  `flag_members_complete env.flag_members cx1 <=>
   flag_members_complete env.flag_members cx2` by
    (irule flag_members_complete_context_cong >> simp[]) >>
  simp[env_context_consistent_def]
QED

Theorem initial_env_context_consistent_empty_tx[local]:
  env_context_consistent env
    (initial_evaluation_context sources layouts tx src) ==>
  env_context_consistent env
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src)
Proof
  strip_tac >>
  `env_context_consistent env
      (initial_evaluation_context sources layouts tx src) <=>
   env_context_consistent env
      (initial_evaluation_context sources layouts
        (empty_call_txn with target := tx.target) src)` by
    (irule env_context_consistent_context_cong >>
     simp[get_tenv_def, current_module_def, get_module_code_def,
          lookup_var_slot_from_layout_def, initial_evaluation_context_def,
          empty_call_txn_def]) >>
  metis_tac[]
QED

Theorem env_scopes_consistent_get_tenv_cong[local]:
  get_tenv cx1 = get_tenv cx2 /\
  env_scopes_consistent env cx1 st ==>
  env_scopes_consistent env cx2 st
Proof
  simp[env_scopes_consistent_def] >>
  metis_tac[]
QED

Theorem initial_env_scopes_consistent_empty_tx[local]:
  env_scopes_consistent env
    (initial_evaluation_context sources layouts tx src) st ==>
  env_scopes_consistent env
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src) st
Proof
  strip_tac >>
  `get_tenv (initial_evaluation_context sources layouts tx src) =
   get_tenv (initial_evaluation_context sources layouts
     (empty_call_txn with target := tx.target) src)` by
    simp[get_tenv_def, initial_evaluation_context_def, empty_call_txn_def] >>
  drule_all env_scopes_consistent_get_tenv_cong >>
  simp[]
QED

Theorem env_immutables_consistent_context_cong[local]:
  get_tenv cx1 = get_tenv cx2 /\
  (!src. get_module_code cx1 src = get_module_code cx2 src) /\
  cx1.txn.target = cx2.txn.target /\
  env_immutables_consistent env cx1 st ==>
  env_immutables_consistent env cx2 st
Proof
  simp[env_immutables_consistent_def] >>
  metis_tac[]
QED

Theorem initial_env_immutables_consistent_empty_tx[local]:
  env_immutables_consistent env
    (initial_evaluation_context sources layouts tx src) st ==>
  env_immutables_consistent env
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src) st
Proof
  strip_tac >>
  `get_tenv (initial_evaluation_context sources layouts tx src) =
   get_tenv (initial_evaluation_context sources layouts
     (empty_call_txn with target := tx.target) src)` by
    simp[get_tenv_def, initial_evaluation_context_def, empty_call_txn_def] >>
  `!src'. get_module_code
      (initial_evaluation_context sources layouts tx src) src' =
    get_module_code
      (initial_evaluation_context sources layouts
        (empty_call_txn with target := tx.target) src) src'` by
    simp[get_module_code_def, initial_evaluation_context_def,
         empty_call_txn_def] >>
  `(initial_evaluation_context sources layouts tx src).txn.target =
   (initial_evaluation_context sources layouts
     (empty_call_txn with target := tx.target) src).txn.target` by
    simp[initial_evaluation_context_def, empty_call_txn_def] >>
  drule_all env_immutables_consistent_context_cong >>
  simp[]
QED

Theorem initial_env_consistent_empty_tx[local]:
  env_consistent env
    (initial_evaluation_context sources layouts tx src) st ==>
  env_consistent env
    (initial_evaluation_context sources layouts
      (empty_call_txn with target := tx.target) src) st
Proof
  strip_tac >>
  rw[env_consistent_def]
  >- (irule initial_env_context_consistent_empty_tx >>
      gvs[env_consistent_def])
  >- (irule initial_env_scopes_consistent_empty_tx >>
      gvs[env_consistent_def])
  >> irule initial_env_immutables_consistent_empty_tx >>
  gvs[env_consistent_def]
QED

Theorem checked_public_getter_post_prefix_body_setup_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts ==>
  ?exp env_after.
    body = [Return (SOME exp)] /\
    type_stmts (function_entry_env art mods src args) ret body = SOME env_after /\
    context_well_typed
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) /\
    functions_well_typed
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) /\
    env_consistent (function_entry_env art mods src args)
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) st /\
    state_well_typed st /\ accounts_well_typed st.accounts /\
    (!st0. eval_stmts cx body st0 =
       eval_stmts
         (initial_evaluation_context am.sources am.layouts
           (empty_call_txn with target := tx.target) src) body st0)
Proof
  rpt strip_tac >>
  drule checked_public_getter_body_typing_package >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  disch_then drule >>
  strip_tac >>
  gvs[checked_contract_runtime_ready_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[immutables_ready_initial_evaluation_context_source] >>
  `env_consistent (function_entry_env art mods src args)
     (initial_evaluation_context am.sources am.layouts tx src) st` by
    (rw[env_consistent_def]
     >- (irule env_context_consistent_same_static_maps >>
         qexists `artifact_env art mods src` >>
         rpt (conj_tac >-
           simp[function_entry_env_def, artifact_env_def,
                FOLDL_extend_local_args_static, get_tenv_def,
                initial_evaluation_context_def]) >>
         irule check_contract_env_context_consistent_initial_src >> simp[])
     >- (`(st with scopes := [scope]) = st` by
           gvs[evaluation_state_component_equality] >>
         pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
         irule bind_arguments_env_scopes_consistent >>
         qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
         gvs[function_entry_env_def, get_tenv_def,
             initial_evaluation_context_def] >>
         metis_tac[])
     >- (gvs[env_immutables_consistent_def, function_entry_env_def,
              artifact_env_def, FOLDL_extend_local_args_static] >> rw[] >>
         qpat_x_assum
           `immutables_ready _ _
              (initial_evaluation_context am.sources am.layouts tx src) _`
           mp_tac >>
         simp[immutables_ready_def] >> strip_tac >>
         first_x_assum drule_all >> simp[])) >>
  `getter_context_equiv
     (initial_evaluation_context am.sources am.layouts tx src)
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src)` by
    simp[getter_context_equiv_initial_empty_tx] >>
  drule_all selected_public_getter_body_eval_context_equiv >> strip_tac >>
  gvs[] >>
  `!st0. eval_stmts
      (initial_evaluation_context am.sources am.layouts tx src)
      [Return (SOME exp)] st0 =
    eval_stmts
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src)
      [Return (SOME exp)] st0` by
    (gen_tac >> AP_THM_TAC >>
     metis_tac[getter_context_equiv_eval_single_Return]) >>
  `context_well_typed
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src)` by
    simp[context_well_typed_def, initial_evaluation_context_def,
         empty_call_txn_def] >>
  `functions_well_typed
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src)` by
    (irule check_contract_functions_well_typed_initial >> simp[]) >>
  `env_consistent (function_entry_env art mods src args)
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src) st` by
    (drule initial_env_consistent_empty_tx >> simp[]) >>
  simp[]
QED

Theorem checked_public_getter_post_prefix_body_execution_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts ==>
  no_type_error_eval (eval_stmts cx body st) /\
  (!v st'. eval_stmts cx body st = (INR (ReturnException v),st') ==>
     ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
              value_has_type ret_tv v)
Proof
  strip_tac >>
  drule_all checked_public_getter_post_prefix_body_setup_selected >>
  strip_tac >>
  `call_evaluation_safe
     (initial_evaluation_context am.sources am.layouts
       (empty_call_txn with target := tx.target) src)
     (int_calls_stmts body)` by (
    `int_calls_stmts body = []` by
      metis_tac[selected_public_getter_body_int_calls_empty] >>
    pop_assum SUBST1_TAC >>
    `ALOOKUP am.sources tx.target = SOME mods` by
      gvs[checked_contract_runtime_ready_def] >>
    `(initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) =
     ((initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) with
       stk := [(src,"")])` by
      simp[initial_evaluation_context_def, empty_call_txn_def] >>
    pop_assum SUBST1_TAC >>
    irule (INST_TYPE [``:'a`` |-> ``:num``]
      checked_contract_call_evaluation_safe_singleton) >>
    qexistsl [`art`, `am.layouts`, `mods`] >>
    simp[initial_evaluation_context_def, empty_call_txn_def,
         calls_follow_call_graph_def]) >>
  `no_type_error_eval
     (eval_stmts
       (initial_evaluation_context am.sources am.layouts
         (empty_call_txn with target := tx.target) src) body st)` by
    metis_tac[eval_stmts_no_type_error] >>
  `no_type_error_eval (eval_stmts cx body st)` by metis_tac[] >>
  `!rv rst. eval_stmts cx body st = (INR (ReturnException rv),rst) ==>
     ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
              value_has_type ret_tv rv` by
    (qx_gen_tac `rv` >> qx_gen_tac `rst` >> strip_tac >>
     `eval_stmts
        (initial_evaluation_context am.sources am.layouts
          (empty_call_txn with target := tx.target) src) body st =
        (INR (ReturnException rv),rst)` by metis_tac[] >>
     `state_well_typed rst /\
      stmt_error_ok (function_entry_env art mods src args) ret
        (INR (ReturnException rv))` by
       (irule eval_stmts_type_preservation_exception >>
        qexistsl
          [`initial_evaluation_context am.sources am.layouts
              (empty_call_txn with target := tx.target) src`,
           `env_after`, `body`, `st`] >>
        simp[]) >>
     gvs[vyperTypeStmtResultTheory.stmt_error_ok_def,
         vyperTypeStmtResultTheory.return_exception_typed_def,
         vyperTypeExprSoundnessTheory.value_runtime_typed_def,
         function_entry_env_def, artifact_env_def,
         FOLDL_extend_local_args_static]) >>
  simp[]
QED

Theorem checked_public_getter_body_preserves_machine_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all checked_public_getter_post_prefix_body_setup_selected >>
  strip_tac >>
  `int_calls_stmts body = []` by
    metis_tac[selected_public_getter_body_int_calls_empty] >>
  `eval_stmts
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) body st = (res,st')` by
    metis_tac[] >>
  `call_evaluation_safe
      (initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) []` by (
    `ALOOKUP am.sources tx.target = SOME mods` by
      gvs[checked_contract_runtime_ready_def] >>
    `(initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) =
     ((initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src) with
       stk := [(src,"")])` by
      simp[initial_evaluation_context_def, empty_call_txn_def] >>
    pop_assum SUBST1_TAC >>
    irule (INST_TYPE [``:'a`` |-> ``:num``]
      checked_contract_call_evaluation_safe_singleton) >>
    qexistsl [`art`, `am.layouts`, `mods`] >>
    simp[initial_evaluation_context_def, empty_call_txn_def,
         calls_follow_call_graph_def]) >>
  irule eval_stmts_preserves_state_and_accounts_well_typed >>
  qexistsl
    [`initial_evaluation_context am.sources am.layouts
        (empty_call_txn with target := tx.target) src`,
     `function_entry_env art mods src args`, `env_after`, `res`, `ret`,
     `body`, `st`] >>
  simp[]
QED


Theorem checked_public_getter_post_prefix_body_return_typed_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (INR (ReturnException v),st') ==>
  ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
           value_has_type ret_tv v
Proof
  rpt strip_tac >>
  drule_all checked_public_getter_post_prefix_body_execution_selected >>
  metis_tac[]
QED

Theorem checked_public_getter_initial_body_execution_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\ MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src ==>
  no_type_error_eval (eval_stmts cx body (initial_state am [scope])) /\
  (!v st'. eval_stmts cx body (initial_state am [scope]) =
      (INR (ReturnException v),st') ==>
    ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
             value_has_type ret_tv v)
Proof
  strip_tac >>
  `scope_well_typed scope` by
    metis_tac[bind_arguments_scope_well_typed_from_success] >>
  `accounts_well_typed (initial_state am [scope]).accounts` by
    metis_tac[initial_state_accounts_well_typed] >>
  `state_well_typed (initial_state am [scope])` by
    metis_tac[initial_state_single_scope_well_typed] >>
  `(initial_state am [scope]).scopes = [scope]` by simp[initial_state_def] >>
  `(initial_state am [scope]).immutables = am.immutables` by
    simp[initial_state_def] >>
  drule_all checked_public_getter_post_prefix_body_execution_selected >>
  simp[]
QED

Theorem call_external_function_exact_selected_getter_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts vals body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  `no_type_error_eval (eval_stmts cx body (initial_state am [scope])) /\
   (!v st'. eval_stmts cx body (initial_state am [scope]) =
       (INR (ReturnException v),st') ==>
     ?ret_tv. evaluate_type (type_env_all_modules mods) ret = SOME ret_tv /\
              value_has_type ret_tv v)` by
    (drule_all checked_public_getter_initial_body_execution_selected >> simp[]) >>
  `nr = F /\ mut = View /\ dflts = [] /\ ?exp. body = [Return (SOME exp)]` by
    (Cases_on `decl` >> gvs[is_public_getter_decl_def, external_getter_tuple_def]
     >- (Cases_on `v` >> gvs[] >> Cases_on `is_ArrayT t` >> gvs[]
         >- (drule_all array_public_getter_tuple_shape >> metis_tac[]) >>
         gvs[external_getter_tuple_def]) >>
     Cases_on `v` >> gvs[is_public_getter_decl_def] >>
     drule_all hashmap_public_getter_tuple_shape >> metis_tac[]) >>
  gvs[] >>
  drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[call_external_function_def, evaluate_defaults_def,
       initial_evaluation_context_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def] >>
  Cases_on `send_call_value View (initial_evaluation_context am.sources am.layouts tx src)
              (initial_state am [scope])` >>
  Cases_on `q` >> gvs[return_def, raise_def]
  >- (`r = initial_state am [scope]` by
        (qpat_x_assum `send_call_value View _ _ = _` mp_tac >>
         rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
            assert_def, return_def, raise_def] >>
         gvs[AllCaseEqs(), return_def, raise_def]) >>
      gvs[] >>
      strip_tac >>
      Cases_on `eval_stmts (initial_evaluation_context am.sources am.layouts tx src)
                  [Return (SOME exp)] (initial_state am [scope])` >>
      Cases_on `q` >>
      gvs[initial_evaluation_context_def,
          vyperTypeExprSoundnessTheory.no_type_error_eval_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      gvs[initial_evaluation_context_def,
          vyperTypeExprSoundnessTheory.no_type_error_eval_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      Cases_on `y` >>
      gvs[initial_evaluation_context_def, return_def, raise_def,
          vyperTypeExprSoundnessTheory.no_type_error_eval_def,
          vyperTypeExprSoundnessTheory.no_type_error_result_def,
          vyperTypingTheory.safe_cast_well_typed] >>
      rpt strip_tac >> gvs[vyperTypingTheory.safe_cast_well_typed]) >>
  qpat_x_assum `send_call_value View _ _ = _` mp_tac >>
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs(), initial_evaluation_context_def, return_def, raise_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def]
QED

Theorem bind_arguments_success_mem_zip_safe_cast:
  !tenv params vals scope id ty raw.
    bind_arguments tenv params vals = SOME scope /\
    MEM ((id,ty),raw) (ZIP (params, vals)) ==>
    ?tv cast_v.
      evaluate_type tenv ty = SOME tv /\
      safe_cast tv raw = SOME cast_v
Proof
  ho_match_mp_tac bind_arguments_ind >>
  rw[bind_arguments_def] >>
  gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem MEM_ZIP_FST[local]:
  !xs ys x y. MEM (x,y) (ZIP (xs,ys)) ==> MEM x xs
Proof
  Induct >> Cases_on `ys` >> rw[ZIP_def] >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem bind_arguments_success_flookup_safe_cast:
  !tenv params vals scope id ty raw sv.
    bind_arguments tenv params vals = SOME scope /\
    ALL_DISTINCT (MAP (string_to_num o FST) params) /\
    MEM ((id,ty),raw) (ZIP (params, vals)) /\
    FLOOKUP scope (string_to_num id) = SOME sv ==>
      sv.assignable /\
      ?tv.
        evaluate_type tenv ty = SOME tv /\
        safe_cast tv raw = SOME sv.value /\
        sv.type = tv
Proof
  ho_match_mp_tac bind_arguments_ind >>
  rw[bind_arguments_def] >>
  gvs[AllCaseEqs(), FLOOKUP_UPDATE, MEM_MAP] >>
  gvs[] >>
  imp_res_tac MEM_ZIP_FST >>
  gvs[] >>
  first_x_assum drule >>
  disch_then (qspec_then `sv` mp_tac) >>
  simp[]
QED

Theorem checked_explicit_external_body_no_control_escape_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts ==>
  stmts_no_control_escape body
Proof
  rpt strip_tac >>
  `check_function_body am.layouts tx.target mods art src mut nr args dflts ret body` by
    metis_tac[check_contract_function_body_MEM] >>
  gvs[check_function_body_def]
QED

Theorem checked_public_getter_body_no_control_escape_selected:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) ==>
  stmts_no_control_escape body
Proof
  rpt strip_tac >>
  `getter_context_equiv
     (initial_evaluation_context am.sources am.layouts tx src)
     (initial_evaluation_context am.sources am.layouts tx src)` by
    simp[getter_context_equiv_def] >>
  drule_all selected_public_getter_body_eval_context_equiv >>
  strip_tac >>
  gvs[stmt_no_control_escape_def]
QED


Theorem lookup_exported_function_checked_cases_current:
  check_contract F am.layouts tx.target mods = SOME art /\
  ALOOKUP am.sources tx.target = SOME mods /\
  src = find_function_module am tx.target tx.function_name /\
  get_module_code (initial_evaluation_context am.sources am.layouts tx src) src = SOME ts /\
  lookup_exported_function (initial_evaluation_context am.sources am.layouts tx src) am tx.function_name =
    SOME (mut,nr,args,dflts,ret,body) ==>
  (?raw.
     MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts) \/
  (?decl.
     MEM decl ts /\
     is_public_getter_decl tx.function_name decl /\
     external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body))
Proof
  metis_tac[lookup_exported_function_checked_cases_selected]
QED


Theorem send_call_value_preserves_scopes[local]:
  send_call_value mut cx st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[send_call_value_def, bind_def, ignore_bind_def, check_def,
     assert_def, return_def, raise_def] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac transfer_value_scopes >> gvs[]
QED

Theorem call_lock_action_preserves_scopes[local]:
  (if nr then
     case cx.nonreentrant_slot of
       NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
   else return ()) st = (res,st') ==>
  st'.scopes = st.scopes
Proof
  rw[] >> gvs[return_def, raise_def] >>
  Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def] >>
  imp_res_tac acquire_nonreentrant_lock_scopes >> gvs[]
QED

Theorem call_lock_send_prefix_body_state_ready[local]:
  machine_well_typed am /\
  scope_well_typed env /\
  (do
     (if nr then
        case cx.nonreentrant_slot of
          NONE => raise (Error (TypeError "nonreentrant slot missing"))
        | SOME slot => acquire_nonreentrant_lock cx.txn.target slot (mut = View \/ mut = Pure)
      else return ());
     send_call_value mut cx
   od (initial_state am [env]) = (INL (),st)) ==>
  st.scopes = [env] /\
  st.immutables = am.immutables /\
  state_well_typed st
Proof
  rw[bind_def, ignore_bind_def] >> gvs[AllCaseEqs()] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def, raise_def]) >>
  imp_res_tac acquire_nonreentrant_lock_scopes >>
  imp_res_tac acquire_nonreentrant_lock_immutables >>
  imp_res_tac send_call_value_preserves_scopes >>
  imp_res_tac send_call_value_preserves_immutables >>
  gvs[initial_state_def, state_well_typed_def, machine_well_typed_def]
QED

Theorem acquire_nonreentrant_lock_accounts[local]:
  acquire_nonreentrant_lock target slot ro st = (res,st') ==>
  st'.accounts = st.accounts
Proof
  rw[acquire_nonreentrant_lock_def, bind_def, ignore_bind_def,
     get_transient_storage_def, update_transient_def, return_def, raise_def,
     assert_def, check_def] >>
  gvs[AllCaseEqs(), return_def, raise_def]
QED


Theorem checked_explicit_external_body_setup:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts ==>
  ?env_body env_after.
    type_stmts env_body ret body = SOME env_after /\
    env_consistent env_body cx st /\
    context_well_typed cx /\
    functions_well_typed cx /\
    state_well_typed st /\
    accounts_well_typed st.accounts
Proof
  strip_tac >> gvs[checked_contract_runtime_ready_def] >>
  `immutables_ready art.cta_bare_globals art.cta_toplevel_vtypes
     (initial_evaluation_context am.sources am.layouts tx src) am.immutables` by
    metis_tac[immutables_ready_initial_evaluation_context_source] >>
  `functions_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    (irule check_contract_functions_well_typed_initial >> simp[]) >>
  `context_well_typed (initial_evaluation_context am.sources am.layouts tx src)` by
    metis_tac[call_tx_well_typed_initial_context] >>
  drule_all checked_function_body_typing_package >>
  strip_tac >>
  qexistsl [`env_body`, `env_after`] >> simp[] >>
  rw[env_consistent_def]
  >- (irule env_context_consistent_same_static_maps >>
      qexists `artifact_env art mods env_body.current_src` >>
      rpt (conj_tac >- simp[artifact_env_def, get_tenv_def, initial_evaluation_context_def]) >>
      irule check_contract_env_context_consistent_initial_src >>
      simp[])
  >- (`(st with scopes := [scope]) = st` by
        gvs[evaluation_state_component_equality] >>
      pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
      irule bind_arguments_env_scopes_consistent >>
      qexistsl [`args`, `type_env_all_modules mods`, `vals`] >>
      gvs[get_tenv_def, initial_evaluation_context_def] >> metis_tac[])
  >- (gvs[env_immutables_consistent_def] >>
      rw[] >>
      qpat_x_assum `immutables_ready _ _ _ _` mp_tac >>
      simp[immutables_ready_def] >>
      strip_tac >>
      first_x_assum drule_all >>
      simp[])
QED


Theorem checked_explicit_external_body_no_type_error_selected[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (res,st') ==>
  no_type_error_result res
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (qpat_x_assum `cx = _` SUBST1_TAC >>
     gvs[checked_contract_runtime_ready_def] >>
     drule_all checked_explicit_external_body_call_evaluation_safe >>
     simp[]) >>
  drule_all eval_stmts_no_type_error >>
  rw[vyperTypeExprSoundnessTheory.no_type_error_eval_def]
QED



Theorem checked_explicit_external_body_preserves_machine_components:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  bind_arguments (type_env_all_modules mods) args vals = SOME scope /\
  ALL_DISTINCT (MAP (string_to_num o FST) args) /\
  st.scopes = [scope] /\ st.immutables = am.immutables /\
  state_well_typed st /\ accounts_well_typed st.accounts /\
  eval_stmts cx body st = (res,st') ==>
  state_well_typed st' /\ accounts_well_typed st'.accounts
Proof
  strip_tac >>
  drule_all checked_explicit_external_body_setup >>
  strip_tac >>
  `call_evaluation_safe cx (int_calls_stmts body)` by
    (qpat_x_assum `cx = _` SUBST1_TAC >>
     gvs[checked_contract_runtime_ready_def] >>
     drule_all checked_explicit_external_body_call_evaluation_safe >>
     simp[]) >>
  irule eval_stmts_preserves_state_and_accounts_well_typed >>
  qexistsl [`cx`, `env_body`, `env_after`, `res`, `ret`, `body`, `st`] >>
  simp[]
QED


Theorem call_external_function_selected_explicit_raw_args_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\ call_tx_well_typed tx /\
  ALOOKUP mods src = SOME ts /\
  MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body) ts /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts tx.args body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def, evaluate_defaults_def] >>
  gvs[AllCaseEqs(), initial_evaluation_context_def] >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >> NO_TAC) >>
  strip_tac >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >> NO_TAC) >>
  irule checked_explicit_external_entry_no_type_error_selected >>
  qexistsl [`am`, `am'`, `args`, `art`, `body`, `dflts`, `mods`,
            `mut`, `nr`, `raw`, `ret`, `env`, `src`, `ts`, `tx`,
            `tx.args ++ dflt_vs`] >> simp[]
  >- (drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
      gvs[] >>
      qpat_x_assum `(\(res,st). (res,st)) _ = _` mp_tac >>
      simp[Once call_external_function_def, evaluate_defaults_def,
           initial_evaluation_context_def] >>
      gvs[AllCaseEqs(), initial_evaluation_context_def] >>
      strip_tac >> gvs[]) >>
  metis_tac[]
QED


Theorem call_external_function_selected_getter_raw_args_no_type_error_c53[local]:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  ALOOKUP mods src = SOME ts /\
  MEM decl ts /\
  is_public_getter_decl tx.function_name decl /\
  external_getter_tuple src decl = SOME (mut,nr,args,dflts,ret,body) /\
  cx = initial_evaluation_context am.sources am.layouts tx src /\
  call_external_function am cx nr mut ts mods args dflts tx.args body ret = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external_function _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once call_external_function_def, evaluate_defaults_def] >>
  gvs[AllCaseEqs(), initial_evaluation_context_def] >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >> NO_TAC) >>
  strip_tac >>
  TRY (gvs[vyperTypeExprSoundnessTheory.no_type_error_result_def] >> NO_TAC) >>
  irule call_external_function_exact_selected_getter_no_type_error_c53 >>
  qexistsl [`am`, `am'`, `args`, `art`, `body`,
            `initial_evaluation_context am.sources am.layouts tx src`,
            `decl`, `dflts`, `mods`, `mut`, `nr`, `ret`, `env`, `src`, `ts`, `tx`,
            `tx.args ++ dflt_vs`] >> simp[]
  >- (drule call_external_function_exact_args_rewrites_c53 >> strip_tac >>
      gvs[] >>
      qpat_x_assum `(\(res,st). (res,st)) _ = _` mp_tac >>
      simp[Once call_external_function_def, evaluate_defaults_def,
           initial_evaluation_context_def] >>
      gvs[AllCaseEqs(), initial_evaluation_context_def] >>
      strip_tac >> gvs[]) >>
  metis_tac[]
QED


(* ===== Checked external call no-TypeError ===== *)

Theorem checked_call_external_no_type_error:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  call_external am tx = (res,am') ==>
  no_type_error_result res
Proof
  rpt strip_tac >>
  qpat_x_assum `call_external am tx = (res,am')` mp_tac >>
  simp[Once call_external_def,
       vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  gvs[AllCaseEqs(),
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  strip_tac >>
  gvs[checked_contract_runtime_ready_def, get_self_code_def,
      vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  `(?raw.
      MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body') ts) \/
   (?decl.
      MEM decl ts /\
      is_public_getter_decl tx.function_name decl /\
      external_getter_tuple (find_function_module am tx.target tx.function_name) decl =
        SOME (mut,nr,args,dflts,ret,body'))` by
    (irule lookup_exported_function_checked_cases_current >> simp[] >> metis_tac[]) >>
  gvs[]
  >- (simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      irule call_external_function_selected_explicit_raw_args_no_type_error_c53 >>
      qexistsl [`am`, `am'`, `args`, `art`, `body'`,
                `initial_evaluation_context am.sources am.layouts tx
                   (find_function_module am tx.target tx.function_name)`,
                `dflts`, `all_mods`, `mut`, `nr`, `raw`, `ret`,
                `find_function_module am tx.target tx.function_name`, `ts`, `tx`] >>
      gvs[checked_contract_runtime_ready_def, get_module_code_def,
          initial_evaluation_context_def])
  >- (simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      irule call_external_function_selected_getter_raw_args_no_type_error_c53 >>
      qexistsl [`am`, `am'`, `args`, `art`, `body'`,
                `initial_evaluation_context am.sources am.layouts tx
                   (find_function_module am tx.target tx.function_name)`,
                `decl`, `dflts`, `all_mods`, `mut`, `nr`, `ret`,
                `find_function_module am tx.target tx.function_name`, `ts`, `tx`] >>
      gvs[checked_contract_runtime_ready_def, get_module_code_def,
          initial_evaluation_context_def])
  >- (simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
      irule call_external_function_selected_explicit_raw_args_no_type_error_c53 >>
      qexistsl [`am`, `am'`, `args`, `art`, `body'`,
                `initial_evaluation_context am.sources am.layouts tx
                   (find_function_module am tx.target tx.function_name)`,
                `dflts`, `all_mods`, `mut`, `nr`, `raw`, `ret`,
                `find_function_module am tx.target tx.function_name`, `ts`, `tx`] >>
      gvs[checked_contract_runtime_ready_def, get_module_code_def,
          initial_evaluation_context_def]) >>
  simp[GSYM vyperTypeExprSoundnessTheory.no_type_error_result_def] >>
  irule call_external_function_selected_getter_raw_args_no_type_error_c53 >>
  qexistsl [`am`, `am'`, `args`, `art`, `body'`,
            `initial_evaluation_context am.sources am.layouts tx
               (find_function_module am tx.target tx.function_name)`,
            `decl`, `dflts`, `all_mods`, `mut`, `nr`, `ret`,
            `find_function_module am tx.target tx.function_name`, `ts`, `tx`] >>
  gvs[checked_contract_runtime_ready_def, get_module_code_def,
      initial_evaluation_context_def]
QED






(* ===== Checked external call no escaping loop control ===== *)

Theorem checked_call_external_no_loop_control:
  check_contract F am.layouts tx.target mods = SOME art /\
  checked_contract_runtime_ready art mods am tx /\
  machine_well_typed am /\
  call_tx_well_typed tx /\
  call_external am tx = (INR exc,am') ==>
  exc <> BreakException /\ exc <> ContinueException
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `call_external am tx = (INR exc,am')` mp_tac >>
  simp[Once call_external_def] >>
  gvs[AllCaseEqs()] >>
  strip_tac >>
  gvs[checked_contract_runtime_ready_def, get_self_code_def] >>
  TRY (Cases_on `exc` >> gvs[] >> NO_TAC) >>
  `(?raw.
      MEM (FunctionDecl External mut nr raw tx.function_name args dflts ret body') ts) \/
   (?decl.
      MEM decl ts /\
      is_public_getter_decl tx.function_name decl /\
      external_getter_tuple (find_function_module am tx.target tx.function_name) decl =
        SOME (mut,nr,args,dflts,ret,body'))` by
    (irule lookup_exported_function_checked_cases_current >> simp[] >> metis_tac[]) >>
  gvs[]
  >- (gvs[get_module_code_def, initial_evaluation_context_def] >>
      metis_tac[call_external_function_no_loop_control_c53,
                checked_explicit_external_body_no_control_escape_selected])
  >- (gvs[get_module_code_def, initial_evaluation_context_def] >>
      metis_tac[call_external_function_no_loop_control_c53,
                checked_public_getter_body_no_control_escape_selected])
  >- (gvs[get_module_code_def, initial_evaluation_context_def] >>
      metis_tac[call_external_function_no_loop_control_c53,
                checked_explicit_external_body_no_control_escape_selected]) >>
  gvs[get_module_code_def, initial_evaluation_context_def] >>
  metis_tac[call_external_function_no_loop_control_c53,
            checked_public_getter_body_no_control_escape_selected]
QED
