Theory vyperEvalExprPreservesScopesDom
Ancestors
  vyperMisc vyperContext vyperState vyperCreate vyperInterpreter vyperLookup
  vyperScopePreservation vyperStatePreservation

(* ========================================================================
   Utility: eval_exprs preserves scopes dom from per-element IH
   (kept for downstream use)
   ======================================================================== *)

Theorem eval_exprs_preserves_scopes_dom_helper[local]:
  ∀es cx st res st'.
    (∀e. MEM e es ⇒ ∀cx st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  Induct >> simp[evaluate_def, return_def] >>
  rpt strip_tac >> gvs[bind_def, AllCaseEqs(), return_def] >>
  imp_res_tac materialise_scopes >> gvs[]
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
      first_x_assum (qspecl_then [`cx`, `s'³'`, `INL vs`, `s'⁴'`] mp_tac) >> simp[] >>
      disch_then irule >> rpt strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`cx'`, `e`, `res`] >> simp[])
  >- (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[]) >>
      first_x_assum (qspecl_then [`cx`, `s'³'`, `INR e`, `s'⁴'`] mp_tac) >> simp[] >>
      disch_then irule >> rpt strip_tac >> first_assum irule >> simp[] >>
      qexistsl_tac [`cx'`, `e'`, `res`] >> simp[])
  >- (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[])
  >- (first_assum (qspec_then `h` mp_tac) >> simp[] >> disch_then drule >> simp[])
QED

(* ========================================================================
   Specialized evaluate_ind principle for scopes domain preservation

   We use evaluate_ind (which provides IHs for ALL recursive calls,
   including default argument evaluation in IntCall) instead of
   structural induction on expr (which cannot provide IHs for runtime
   expressions not in the syntax tree).

   Predicates:
   - P0-P4, P6 (statements, iterator, targets, for) = T (trivially true)
   - P5 (eval_base_target) = domain preservation
   - P7 (eval_expr) = domain preservation
   - P8 (eval_exprs) = domain preservation
   ======================================================================== *)
local
  val p0 = ``\(cx:evaluation_context) (s:stmt). T``
  val p1 = ``\(cx:evaluation_context) (ss:stmt list). T``
  val p2 = ``\(cx:evaluation_context) (it:iterator). T``
  val p3 = ``\(cx:evaluation_context) (g:assignment_target). T``
  val p4 = ``\(cx:evaluation_context) (gs:assignment_target list). T``
  val p5 = ``\cx bt. !st res st'. eval_base_target cx bt st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val p6 = ``\(cx:evaluation_context) (tyv:type_value) (nm:num) (body:stmt list) (vs:value list). T``
  val p7 = ``\cx e. !st res st'. eval_expr cx e st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val p8 = ``\cx es. !st res st'. eval_exprs cx es st = (res, st') ==> MAP FDOM st.scopes = MAP FDOM st'.scopes``
  val spec_ind = SPECL [p0, p1, p2, p3, p4, p5, p6, p7, p8] evaluate_ind
  val spec_ind_beta = CONV_RULE (DEPTH_CONV BETA_CONV) spec_ind
in
  val scopes_dom_ind = save_thm("scopes_dom_ind", spec_ind_beta)
end

(* ========================================================================
   Helper lemmas for evaluate_ind cases (P5: eval_base_target)

   Statements match the evaluate_ind subgoal shapes exactly.
   ACCEPT_TAC works up to alpha-equivalence.
   ======================================================================== *)

(* Goal 1: NameTarget (no IH) *)
Theorem case_NameTarget_dom[local]:
  ∀cx nm st res st'.
    eval_base_target cx (NameTarget nm) st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def, raise_def] >>
  rpt strip_tac >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num nm) st.scopes)` >> gvs[return_def, raise_def]
QED

(* Goal 2: TopLevelNameTarget (no IH) *)
Theorem case_TopLevelNameTarget_dom[local]:
  ∀cx src_id_opt id st res st'.
    eval_base_target cx (TopLevelNameTarget (src_id_opt, id)) st = (res, st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  qpat_x_assum `_ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, lift_option_type_def, return_def, raise_def] >>
  Cases_on `get_module_code cx src_id_opt` >> simp[return_def, raise_def] >>
  Cases_on `is_immutable_decl (string_to_num id) x` >> simp[return_def]
QED

(* Goal 3: AttributeTarget (unguarded IH for eval_base_target on t) *)
Theorem case_AttributeTarget_dom[local]:
  ∀cx t id.
    (∀st res st'. eval_base_target cx t st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_base_target cx (AttributeTarget t id) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY]
QED

(* Goal 4: SubscriptTarget (guarded IH for e, unguarded IH for t) *)
Theorem case_SubscriptTarget_dom[local]:
  ∀cx t e.
    (∀sa loc sbs sb.
       eval_base_target cx t sa = (INL (loc,sbs),sb) ⇒
       ∀st res st'. eval_expr cx e st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_base_target cx t st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_base_target cx (SubscriptTarget t e) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[Once evaluate_def, bind_def, AllCaseEqs(), return_def, pairTheory.UNCURRY] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >>
  imp_res_tac lift_option_type_scopes >> gvs[] >>
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by (
    qpat_x_assum `∀st res st'. eval_base_target _ _ _ = _ ⇒ _` drule >> simp[]) >>
  PairCases_on `x` >>
  qpat_x_assum `∀sa loc sbs sb. _` drule >> disch_then drule >> simp[]
QED

(* ========================================================================
   Helper lemmas for evaluate_ind cases (P7: eval_expr)
   ======================================================================== *)

(* Goal 5: Name (no IH) *)
Theorem case_Name_dom[local]:
  ∀cx ty id st res st'.
    eval_expr cx (Name ty id) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  simp[evaluate_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def] >>
  rpt strip_tac >>
  Cases_on `lookup_scopes_val (string_to_num id) st.scopes` >> gvs[return_def, raise_def]
QED

(* Goal 6: TopLevelName (no IH) *)
Theorem case_TopLevelName_dom[local]:
  ∀cx ty src_id_opt id st res st'.
    eval_expr cx (TopLevelName ty (src_id_opt,id)) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def] >> imp_res_tac lookup_global_scopes >> gvs[]
QED

(* Goal 7: FlagMember (no IH) *)
Theorem case_FlagMember_dom[local]:
  ∀cx ty nsid mid st res st'.
    eval_expr cx (FlagMember ty nsid mid) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def] >> imp_res_tac lookup_flag_mem_scopes >> gvs[]
QED

(* Goal 8: IfExp (guarded IHs for e2,e3; unguarded for e1) *)
Theorem case_IfExp_dom[local]:
  ∀cx ty e1 e2 e3.
    (∀sa tv sb.
       eval_expr cx e1 sa = (INL tv,sb) ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀sa tv sb.
       eval_expr cx e1 sa = (INL tv,sb) ⇒
       ∀st res st'. eval_expr cx e3 st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (IfExp ty e1 e2 e3) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr cx (IfExp _ _ _ _) _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, switch_BoolV_def] >>
  strip_tac >> gvs[] >>
  `MAP FDOM st.scopes = MAP FDOM s''.scopes` by (last_x_assum drule >> simp[]) >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >>
      last_x_assum (qspecl_then [`st`, `Value (BoolV T)`, `s''`] mp_tac) >>
      simp[] >> disch_then (qspecl_then [`s''`, `res`, `st'`] mp_tac) >> simp[] >>
      strip_tac >> first_x_assum drule >> simp[])
  >> IF_CASES_TAC >> gvs[raise_def] >>
  strip_tac >>
  first_x_assum (qspecl_then [`st`, `Value (BoolV F)`, `s''`] mp_tac) >>
  simp[] >> disch_then (qspecl_then [`s''`, `res`, `st'`] mp_tac) >> simp[] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

(* Goal 9: Literal (no IH) *)
Theorem case_Literal_dom[local]:
  ∀cx ty l st res st'.
    eval_expr cx (Literal ty l) st = (res,st') ⇒
    MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, return_def]
QED

(* Goal 10: StructLit (unguarded IH for MAP SND kes) *)
Theorem case_StructLit_dom[local]:
  ∀cx ty src_id_opt id kes.
    (∀ks. ks = MAP FST kes ⇒
       ∀st res st'. eval_exprs cx (MAP SND kes) st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (StructLit ty (src_id_opt,id) kes) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> gvs[evaluate_def, bind_def, AllCaseEqs(), return_def]
QED

(* Goal 11: Subscript (guarded IH for e2, unguarded for e1) *)
Theorem case_Subscript_dom[local]:
  ∀cx ty e1 e2.
    (∀sa tv1 sb.
       eval_expr cx e1 sa = (INL tv1,sb) ⇒
       ∀st res st'. eval_expr cx e2 st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'. eval_expr cx e1 st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Subscript ty e1 e2) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr cx (Subscript _ _ _) _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def,
       ignore_bind_def] >>
  strip_tac >> gvs[] >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >>
  imp_res_tac lift_option_type_state >> gvs[] >>
  imp_res_tac check_array_bounds_state >> gvs[] >>
  first_x_assum $ drule_then assume_tac >>
  first_x_assum (qspecl_then [`st`, `tv1`, `s''`] mp_tac) >> simp[] >>
  disch_then $ drule_then assume_tac >> gvs[] >>
  rename1 `lift_sum _ _ = (INL subscript_res, _)` >>
  Cases_on `subscript_res` >> gvs[return_def, bind_def, AllCaseEqs()] >>
  PairCases_on `y` >> gvs[bind_def, AllCaseEqs(), lift_option_def, lift_option_type_def, return_def, raise_def] >>
  imp_res_tac read_storage_slot_scopes >> gvs[]
QED

(* Goal 12: Attribute (unguarded IH) *)
Theorem case_Attribute_dom[local]:
  ∀cx ty e id.
    (∀st res st'. eval_expr cx e st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Attribute ty e id) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, get_Value_def, lift_option_def] >>
  TRY (`MAP FDOM st.scopes = MAP FDOM s''.scopes` by (first_x_assum drule >> simp[])) >>
  imp_res_tac get_Value_scopes >> imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >> gvs[]
QED

(* Goal 13: Builtin (guarded P8 IH) *)
Theorem case_Builtin_dom[local]:
  ∀cx ty bt es.
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x,t) ∧
       bt ≠ Len ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀s'' x t.
       type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" s'' = (INL x,t) ∧
       bt = Len ⇒
       ∀st res st'. eval_expr cx (HD es) st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Builtin ty bt es) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
      check_def, type_check_def, assert_def, get_accounts_def, lift_sum_def] >>
  Cases_on `bt = Len` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def]
  >> TRY (imp_res_tac toplevel_array_length_state >> gvs[] >>
          res_tac >> gvs[] >> NO_TAC)
  >> gvs[get_accounts_def, return_def, sum_CASE_rator, CaseEq"sum", raise_def]
QED

(* Goal 14: Pop (unguarded IH for eval_base_target) *)
Theorem case_Pop_dom[local]:
  ∀cx ty bt.
    (∀st res st'. eval_base_target cx bt st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Pop ty bt) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac (CONJUNCT1 assign_target_preserves_scopes_dom) >> gvs[] >>
  imp_res_tac get_Value_scopes >> gvs[] >>
  imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes >> gvs[] >>
  imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >> imp_res_tac lift_option_type_scopes >> gvs[]
QED

(* Goal 15: TypeBuiltin (guarded P8 IH) *)
Theorem case_TypeBuiltin_dom[local]:
  ∀cx ty tb typ es.
    (∀s'' x t.
       type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (TypeBuiltin ty tb typ es) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def, ignore_bind_def,
      check_def, type_check_def, assert_def, lift_sum_def] >>
  TRY (Cases_on `evaluate_type_builtin cx tb typ vs` >> gvs[return_def, raise_def])
QED

(* Goal 16: Send (guarded P8 IH) *)
Theorem case_Send_dom[local]:
  ∀cx ty es v0.
    (∀s'' x t.
       type_check (LENGTH es = 2) "Send args" s'' = (INL x,t) ⇒
       ∀st res st'. eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call ty Send es v0) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def] >>
  strip_tac >> gvs[return_def, raise_def, GSYM lift_option_def, GSYM lift_option_type_def] >>
  imp_res_tac transfer_value_scopes >>
  imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes >> imp_res_tac lift_option_type_scopes >> gvs[] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[check_def, type_check_def, assert_def, return_def]
QED

(* ===== Chain interaction builtins (unguarded eval_exprs IH) ===== *)

(* RawCallTarget *)
Theorem case_RawCallTarget_dom[local]:
  ∀cx ty flags es v0.
    (∀st res st'. eval_exprs cx es st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call ty (RawCallTarget flags) es v0) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def,
       get_accounts_def, get_transient_storage_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  pairarg_tac >> gvs[update_accounts_def, update_transient_def, append_logs_def,
       bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs(), assert_def,
       COND_RATOR, CaseEq"bool"]
QED

(* RawLog *)
Theorem case_RawLog_dom[local]:
  ∀cx v0 es v1.
    (∀st res st'. eval_exprs cx es st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call v0 RawLog es v1) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def,
       push_log_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def]
QED

(* RawRevert *)
Theorem case_RawRevert_dom[local]:
  ∀cx v0 es v1.
    (∀st res st'. eval_exprs cx es st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call v0 RawRevert es v1) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >>
  gvs[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
      check_def, type_check_def, assert_def]
QED

(* SelfDestructTarget *)
Theorem case_SelfDestructTarget_dom[local]:
  ∀cx v0 es v1.
    (∀st res st'. eval_exprs cx es st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call v0 SelfDestructTarget es v1) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[evaluate_def, bind_def, ignore_bind_def, AllCaseEqs(), return_def, raise_def,
       check_def, type_check_def, assert_def, lift_option_def, lift_option_type_def,
       get_accounts_def, option_CASE_rator] >>
  strip_tac >> gvs[AllCaseEqs(), return_def, raise_def] >>
  imp_res_tac transfer_value_scopes >> gvs[]
QED

(* CreateTarget *)
Theorem case_CreateTarget_dom[local]:
  ∀cx ty kind has_salt rof es v0.
    (∀st res st'. eval_exprs cx es st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_expr cx (Call ty (CreateTarget kind has_salt rof) es v0) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_exprs cx es st` >> Cases_on `q` >> simp[] >>
  strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule eval_create_preserves_non_accounts >> strip_tac >> gvs[]
QED

(* Goal 17: ExtCall (exact evaluate_ind shape) *)
(* ========================================================================
   Helper lemmas for evaluate_ind cases (P8: eval_exprs)
   ======================================================================== *)

(* Goal 24: eval_exprs [] (no IH) *)
Theorem case_eval_exprs_nil_dom[local]:
  ∀cx st res st'.
    eval_exprs cx [] st = (res,st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  simp[evaluate_def, return_def]
QED

(* Goal 20: eval_exprs cons (exact evaluate_ind shape) *)
Theorem case_eval_exprs_cons_dom[local]:
  ∀cx e es.
    (∀s'' tv t s'³' v t'.
       eval_expr cx e s'' = (INL tv,t) ∧ materialise cx tv s'³' = (INL v,t') ⇒
       ∀st res st'.
         eval_exprs cx es st = (res,st') ⇒
         MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
    (∀st res st'.
       eval_expr cx e st = (res,st') ⇒
       MAP FDOM st.scopes = MAP FDOM st'.scopes) ⇒
    ∀st res st'.
      eval_exprs cx (e::es) st = (res,st') ⇒
      MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  rpt strip_tac >> qpat_x_assum `eval_exprs _ (_::_) _ = _` mp_tac >>
  simp[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
  strip_tac >> gvs[] >>
  imp_res_tac materialise_scopes >> gvs[] >>
  (* Cases where e fails: closed by unguarded IH *)
  TRY (qpat_x_assum `∀st res st'. eval_expr _ _ _ = _ ⇒ _` drule >> simp[] >> NO_TAC) >>
  (* Cases where e and materialise both succeed: chain IHs *)
  qpat_x_assum `∀st res st'. eval_expr _ _ _ = _ ⇒ _` $ drule_then assume_tac >>
  metis_tac[]
QED

(* ========================================================================
   Main mutual theorem using evaluate_ind

   Each subgoal is closed by ACCEPT_TAC of the corresponding helper.
   ======================================================================== *)

Theorem eval_mutual_preserves_scopes_dom[local]:
  (∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes) ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes)
Proof
  MP_TAC scopes_dom_ind >> impl_tac >- (
    rpt conj_tac >>
    TRY (simp[] >> NO_TAC) >-
    ACCEPT_TAC case_NameTarget_dom >-
    ACCEPT_TAC case_TopLevelNameTarget_dom >-
    ACCEPT_TAC case_AttributeTarget_dom >-
    ACCEPT_TAC case_SubscriptTarget_dom >-
    ACCEPT_TAC case_Name_dom >-
    ACCEPT_TAC case_TopLevelName_dom >-
    ACCEPT_TAC case_FlagMember_dom >-
    ACCEPT_TAC case_IfExp_dom >-
    ACCEPT_TAC case_Literal_dom >-
    ACCEPT_TAC case_StructLit_dom >-
    ACCEPT_TAC case_Subscript_dom >-
    ACCEPT_TAC case_Attribute_dom >-
    ACCEPT_TAC case_Builtin_dom >-
    ACCEPT_TAC case_Pop_dom >-
    ACCEPT_TAC case_TypeBuiltin_dom >-
    ACCEPT_TAC case_Send_dom >-
    suspend "ExtCall" >-
    suspend "IntCall" >-
    ACCEPT_TAC case_RawCallTarget_dom >-
    ACCEPT_TAC case_RawLog_dom >-
    ACCEPT_TAC case_RawRevert_dom >-
    ACCEPT_TAC case_SelfDestructTarget_dom >-
    ACCEPT_TAC case_CreateTarget_dom >-
    ACCEPT_TAC case_eval_exprs_nil_dom >-
    ACCEPT_TAC case_eval_exprs_cons_dom
  ) >>
  simp[]
QED

Resume eval_mutual_preserves_scopes_dom[ExtCall]:
  rpt gen_tac
  \\ strip_tac
  \\ rewrite_tac[Once evaluate_def]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ rpt gen_tac
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- rw[]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (pop_assum mp_tac \\ rw[check_def, type_check_def, assert_def])
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    first_x_assum drule
    \\ FIRST [drule lift_option_type_scopes, drule lift_option_scopes]
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ gvs[check_def, type_check_def, assert_def]
    \\ rw[] \\ gvs[] )
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    first_x_assum drule
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ FIRST [drule lift_option_type_scopes, drule lift_option_scopes]
    \\ gvs[check_def, type_check_def, assert_def, bind_def, COND_RATOR, CaseEq"bool",
           return_def, CaseEq"sum", CaseEq"prod"]
    \\ rw[]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[] )
  \\ pairarg_tac
  \\ asm_simp_tac std_ss []
  \\ BasicProvers.LET_ELIM_TAC
  \\ qpat_x_assum`_ = _`mp_tac
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    first_x_assum drule
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[check_def, type_check_def, assert_def, bind_def, COND_RATOR, CaseEq"bool",
           return_def, CaseEq"sum", CaseEq"prod"]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes \\ gvs[] )
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (pop_assum mp_tac \\ rw[get_accounts_def, return_def])
  \\ rewrite_tac[bind_def, ignore_bind_def, check_def, assert_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
    first_x_assum drule >>
    first_x_assum(qspec_then`ARB`kall_tac) \\ rw[] >>
    imp_res_tac lift_option_scopes >>
    imp_res_tac lift_option_type_scopes >>
    gvs[COND_RATOR, AllCaseEqs(),return_def,bind_def,check_def,
        type_check_def,assert_def,get_accounts_def] >>
    imp_res_tac lift_option_type_scopes >> gvs[] ) >>
  BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (pop_assum mp_tac \\ rw[get_transient_storage_def, return_def])
  \\ BasicProvers.LET_ELIM_TAC
  \\ qpat_x_assum`_ = _`mp_tac
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    first_x_assum drule
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[check_def, type_check_def, assert_def, bind_def, COND_RATOR, CaseEq"bool",
           return_def, CaseEq"sum", CaseEq"prod", get_accounts_def,
           get_transient_storage_def]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes \\ gvs[] )
  \\ BasicProvers.LET_ELIM_TAC
  \\ qpat_x_assum`_ = _`mp_tac
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    first_x_assum drule
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[check_def, type_check_def, assert_def, bind_def, COND_RATOR, CaseEq"bool",
           return_def, CaseEq"sum", CaseEq"prod", get_accounts_def,
           get_transient_storage_def]
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes \\ gvs[] )
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (pop_assum mp_tac \\ rw[update_accounts_def, return_def])
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (pop_assum mp_tac \\ rw[update_transient_def, return_def])
  \\ IF_CASES_TAC
  >- (
    strip_tac
    \\ last_x_assum $ funpow 2 drule_then drule
    \\ simp[]
    \\ rpt $ disch_then $ drule_at Any
    \\ gvs[]
    \\ rpt $ disch_then $ drule_at Any
    \\ gvs[ignore_bind_def]
    \\ disch_then $ drule_at Any
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac update_accounts_scopes
    \\ imp_res_tac update_transient_scopes
    \\ imp_res_tac append_logs_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ strip_tac
    \\ gvs[append_logs_def, return_def, check_def, type_check_def, assert_def]
    \\ first_x_assum drule
    \\ first_x_assum drule
    \\ gvs[get_accounts_def, get_transient_storage_def, return_def,
           check_def, assert_def,
           COND_RATOR, CaseEq"bool", bind_def, CaseEq"sum", CaseEq"prod"]
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[])
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    first_x_assum drule
    \\ first_x_assum(qspec_then`ARB`kall_tac)
    \\ rw[] \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac update_accounts_scopes
    \\ imp_res_tac update_transient_scopes
    \\ imp_res_tac append_logs_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes
    \\ gvs[get_accounts_def, get_transient_storage_def, return_def,
           COND_RATOR, CaseEq"bool", bind_def, CaseEq"sum", CaseEq"prod"]
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ gvs[assert_def] )
  \\ first_x_assum drule
  \\ first_x_assum(qspec_then`ARB`kall_tac)
  \\ rw[return_def] \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
  \\ imp_res_tac update_accounts_scopes
  \\ imp_res_tac update_transient_scopes
  \\ imp_res_tac append_logs_scopes
  \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
  \\ imp_res_tac lift_sum_scopes >> imp_res_tac lift_sum_runtime_scopes
  \\ gvs[get_accounts_def, get_transient_storage_def, return_def,
         COND_RATOR, CaseEq"bool", bind_def, CaseEq"sum", CaseEq"prod"]
  \\ imp_res_tac lift_sum_runtime_scopes
  \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
  \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
  \\ gvs[assert_def]
QED

(* Lock operations preserve scopes: needed for IntCall handler.
   Uses bind form (not ignore_bind) because earlier SIMP_TAC expands ignore_bind.
   Uses ≠ form because simp normalizes ¬(A ∨ B) to ¬A ∧ ¬B. *)
Theorem finally_intcall_handler_scopes[local]:
  ∀f nr mut cx prev s res s'.
    finally f
      (bind (set_scopes prev) (λx.
          if nr ∧ mut ≠ View ∧ mut ≠ Pure then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ())) s = (res, s') ⇒
    MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rw[finally_def, bind_def, ignore_bind_def,
     set_scopes_def, return_def, raise_def, AllCaseEqs()]
  \\ gvs[]
  \\ Cases_on `cx.nonreentrant_slot` \\ gvs[return_def]
  \\ imp_res_tac release_nonreentrant_lock_scopes \\ gvs[]
QED

Theorem finally_set_scopes_scopes[local]:
  ∀f prev s res s'.
    finally f (set_scopes prev) s = (res,s') ⇒
    MAP FDOM s'.scopes = MAP FDOM prev
Proof
  rw[finally_def, bind_def, ignore_bind_def,
     set_scopes_def, return_def, raise_def, AllCaseEqs()]
  \\ gvs[]
QED

Theorem lock_acquire_cond_scopes_dom[local]:
  ∀nr slot_opt addr is_view st res st'.
    (if nr then
       case slot_opt of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock addr slot is_view
     else return ()) st = (res,st') ⇒
    MAP FDOM st'.scopes = MAP FDOM st.scopes
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `nr` \\ gvs[return_def]
  \\ Cases_on `slot_opt` \\ gvs[raise_def]
  \\ imp_res_tac acquire_nonreentrant_lock_scopes \\ gvs[]
QED

Resume eval_mutual_preserves_scopes_dom[IntCall]:
  rpt gen_tac
  \\ strip_tac
  \\ rewrite_tac[Once evaluate_def]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ rpt gen_tac
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (FIRST [drule type_check_scopes, drule check_scopes] \\ rpt (pop_assum kall_tac) \\ rw[] \\ rw[])
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ rpt(qpat_x_assum`!x. _`kall_tac)
    \\ rw[] \\ gvs[] )
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    rpt(qpat_x_assum`!x. _`kall_tac)
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ rw[] \\ gvs[] )
  \\ BasicProvers.LET_ELIM_TAC
  \\ qpat_x_assum`_ = _`mp_tac
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    rpt(qpat_x_assum`!x. _`kall_tac)
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ rw[] \\ gvs[] )
  \\ pop_assum mp_tac
  \\ first_x_assum $ funpow 2 drule_then drule
  \\ simp[]
  \\ ntac 2 strip_tac
  \\ first_x_assum drule \\ strip_tac
  \\ BasicProvers.TOP_CASE_TAC
  \\ first_x_assum drule
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (
    rpt(qpat_x_assum`!x. _`kall_tac)
    \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
    \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
    \\ rw[] )
  \\ strip_tac
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ first_x_assum $ funpow 2 drule_then drule
  \\ simp[]
  \\ strip_tac
  \\ gvs[get_scopes_def, return_def]
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (strip_tac >> gvs[]
      >> drule finally_set_scopes_scopes >> simp[] >> strip_tac
      >> imp_res_tac check_scopes >> imp_res_tac type_check_scopes
      >> imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
      >> gvs[])
  \\ `MAP FDOM r'⁵'.scopes = MAP FDOM r'⁴'.scopes` by
       (drule finally_set_scopes_scopes >> simp[])
  (* Peel evaluate_type *)
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(qpat_x_assum`!x. _`kall_tac)
      \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
      \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
      \\ rw[] \\ gvs[])
  (* Peel evaluate_type *)
  \\ rewrite_tac[bind_def, ignore_bind_def, COND_RATOR]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (rpt(qpat_x_assum`!x. _`kall_tac)
      \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
      \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
      \\ rw[] \\ gvs[])
  (* Peel lock acquire; error branch preserves scope domains by primitive lock helper. *)
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ reverse (Cases_on `q` \\ gvs[AllCaseEqs()])
  >- (strip_tac \\ gvs[]
      \\ imp_res_tac lock_acquire_cond_scopes_dom
      \\ imp_res_tac acquire_nonreentrant_lock_scopes
      \\ imp_res_tac lift_option_type_scopes
      \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
      \\ gvs[])
  (* Expand push_function — always succeeds — and pop_function *)
  \\ simp[push_function_def, return_def, pop_function_def]
  (* Now goal has: case finally (...) (bind (set_scopes prev) ...) s of ... *)
  \\ rewrite_tac[bind_def, ignore_bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ drule finally_intcall_handler_scopes
  \\ reverse BasicProvers.TOP_CASE_TAC
  >- (imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
      \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
      \\ imp_res_tac acquire_nonreentrant_lock_scopes
      \\ rw[] \\ gvs[])
  (* Peel safe_cast + return *)
  \\ rewrite_tac[bind_def]
  \\ BasicProvers.TOP_CASE_TAC
  \\ imp_res_tac lift_option_scopes >> imp_res_tac lift_option_type_scopes
  \\ imp_res_tac check_scopes >> imp_res_tac type_check_scopes
  \\ imp_res_tac acquire_nonreentrant_lock_scopes
  \\ BasicProvers.TOP_CASE_TAC
  \\ rw[] \\ gvs[return_def]
QED

Finalise eval_mutual_preserves_scopes_dom

(* ========================================================================
   Main theorems (exported)
   ======================================================================== *)

Theorem eval_expr_preserves_scopes_dom:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_expr_preserves_var_in_scope:
  ∀cx st st' n e res.
    eval_expr cx e st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_expr_preserves_scopes_dom]
QED

Theorem eval_expr_preserves_scopes_len:
  ∀e cx st res st'.
    eval_expr cx e st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_expr_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_base_target_preserves_scopes_dom:
  ∀cx bt st res st'. eval_base_target cx bt st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_base_target_preserves_var_in_scope:
  ∀cx st st' n bt res.
    eval_base_target cx bt st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_base_target_preserves_scopes_dom]
QED

Theorem eval_base_target_preserves_scopes_len:
  ∀bt cx st res st'.
    eval_base_target cx bt st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_base_target_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED

Theorem eval_exprs_preserves_scopes_dom:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ MAP FDOM st.scopes = MAP FDOM st'.scopes
Proof
  metis_tac[eval_mutual_preserves_scopes_dom]
QED

Theorem eval_exprs_preserves_var_in_scope:
  ∀cx st st' n es res.
    eval_exprs cx es st = (res, st') ⇒
    (var_in_scope st n ⇔ var_in_scope st' n)
Proof
  metis_tac[var_in_scope_dom_iff, eval_exprs_preserves_scopes_dom]
QED

Theorem eval_exprs_preserves_scopes_len:
  ∀es cx st res st'.
    eval_exprs cx es st = (res, st') ⇒ LENGTH st.scopes = LENGTH st'.scopes
Proof
  rpt strip_tac >>
  drule eval_exprs_preserves_scopes_dom >> strip_tac >>
  `LENGTH (MAP FDOM st.scopes) = LENGTH (MAP FDOM st'.scopes)` by metis_tac[] >>
  gvs[listTheory.LENGTH_MAP]
QED
