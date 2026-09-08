Theory vyperInterpreter
Ancestors
  arithmetic alist combin option list finite_map pair
  rich_list cv cv_std vfmState vfmContext vfmCompute[ignore_grammar]
  vfmExecution[ignore_grammar] vyperAST vyperABI
  vyperMisc vyperValue vyperValueOperation vyperStorage vyperContext vyperState
  vyperEvent vyperCreate
Libs
  cv_transLib wordsLib monadsyntax

(* writing logs *)

Definition push_log_def:
  push_log log st = return () $ st with logs := st.logs ++ [log]
End

Definition append_logs_def:
  append_logs logs st = return () $ st with logs := st.logs ++ logs
End

val () = cv_auto_trans push_log_def;
val () = cv_auto_trans append_logs_def;

(* manipulating (internal call) function stack *)

Definition push_function_def:
  push_function src_fn sc cx st =
  return (cx with stk updated_by CONS src_fn)
    $ st with scopes := [sc]
End

val () = cv_auto_trans push_function_def;

Definition pop_function_def:
  pop_function prev = set_scopes prev
End

val () = cv_auto_trans pop_function_def;

(* helper for sending ether between accounts *)

Definition transfer_value_def:
  transfer_value fromAddr toAddr amount =
  if amount = 0 ∨ fromAddr = toAddr then return () else do
    acc <- get_accounts;
    sender <<- lookup_account fromAddr acc;
    check (amount <= sender.balance) "transfer_value amount";
    recipient <<- lookup_account toAddr acc;
    check (recipient.balance + amount < 2 ** 256) "transfer_value recipient overflow";
    update_accounts (
      update_account fromAddr (sender with balance updated_by (flip $- amount)) o
      update_account toAddr (recipient with balance updated_by ($+ amount)));
  od
End

val () = transfer_value_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, COND_RATOR, update_accounts_def, o_DEF, C_DEF]
  |> cv_auto_trans;

(* machinery for calls to functions in a Vyper contract, and for internal calls
* within a contract, including implicit functions associated with public
* variables *)

Definition getter_vtype_annotation_def:
  getter_vtype_annotation (Type ty) = ty ∧
  getter_vtype_annotation (HashMapT _ _) = NoneT
End

val () = cv_auto_trans getter_vtype_annotation_def;

Definition build_getter_def:
  build_getter e kt (Type vt) n =
    (let vn = num_to_dec_string n in
      if is_ArrayT vt then
        (let (args, ret, exp) =
           build_getter
             (Subscript vt e (Name kt vn))
             (BaseT (UintT 256)) (Type (ArrayT_type vt)) (SUC n) in
           ((vn, kt)::args, ret, exp))
      else ([(vn, kt)], vt, Subscript vt e (Name kt vn))) ∧
  build_getter e kt (HashMapT typ vtyp) n =
    (let vn = num_to_dec_string n in
     let (args, ret, exp) =
       build_getter
         (Subscript (getter_vtype_annotation (HashMapT typ vtyp)) e (Name kt vn))
         typ vtyp (SUC n) in
     ((vn, kt)::args, ret, exp))
Termination
  WF_REL_TAC ‘measure (value_type_size o FST o SND o SND)’
  \\ Cases \\ rw[type_size_def]
End

val () = cv_auto_trans_rec build_getter_def (
  WF_REL_TAC ‘measure (cv_size o FST o SND o SND)’
  \\ conj_tac \\ Cases \\ rw[]
  >- (
    qmatch_goalsub_rename_tac`cv_snd p`
    \\ Cases_on`p` \\ rw[] )
  \\ qmatch_asmsub_rename_tac`cv_is_ArrayT a`
  \\ Cases_on `a` \\ gvs[cv_is_ArrayT_def, cv_ArrayT_type_def]
  \\ rw[] \\ gvs[]
  \\ qmatch_goalsub_rename_tac`cv_fst p`
  \\ Cases_on `p` \\ gvs[]
);

Definition getter_def:
  getter ne kt vt =
  let (args, ret, exp) =
    build_getter ne kt vt 0
  in
    (View, F, args, [], ret, [Return $ SOME exp])
End

val () = cv_auto_trans getter_def;

Definition lookup_function_def:
  lookup_function src_id_opt name Deploy [] = SOME (Payable, F, [], [], NoneT, []) ∧
  lookup_function src_id_opt name vis [] = NONE ∧
  lookup_function src_id_opt name vis (FunctionDecl fv fm nr _ id args dflts ret body :: ts) =
  (if id = name ∧ vis = fv then SOME (fm, nr, args, dflts, ret, body)
   else lookup_function src_id_opt name vis ts) ∧
  lookup_function src_id_opt name External (VariableDecl Public mut id typ _ :: ts) =
  (if id = name then
    let ne = TopLevelName typ (src_id_opt, id) in
    if ¬is_ArrayT typ
    then SOME (View, F, [], [], typ, [Return (SOME ne)])
    else SOME $ getter ne (BaseT (UintT 256)) (Type (ArrayT_type typ))
   else lookup_function src_id_opt name External ts) ∧
  lookup_function src_id_opt name External (HashMapDecl Public _ id kt vt _ :: ts) =
  (if id = name then SOME $ getter (TopLevelName NoneT (src_id_opt, id)) kt vt
   else lookup_function src_id_opt name External ts) ∧
  lookup_function src_id_opt name vis (_ :: ts) =
    lookup_function src_id_opt name vis ts
End

val () = cv_auto_trans lookup_function_def;

(* Lookup function callable via IntCall: Internal always, Deploy only during deployment *)
Definition lookup_callable_function_def:
  lookup_callable_function in_deploy name ts =
    case lookup_function NONE name Internal ts of
    | SOME x => SOME x
    | NONE => if in_deploy then lookup_function NONE name Deploy ts else NONE
End

val () = cv_auto_trans lookup_callable_function_def;

Definition bind_arguments_def:
  bind_arguments tenv ([]: argument list) [] = SOME (FEMPTY: scope) ∧
  bind_arguments tenv ((id, typ)::params) (v::vs) =
    (case evaluate_type tenv typ of NONE => NONE | SOME tv =>
     case safe_cast tv v of NONE => NONE | SOME v =>
      OPTION_MAP (λm. m |+ (string_to_num id,
        <| assignable := T; type := tv; value := v |>))
        (bind_arguments tenv params vs)) ∧
  bind_arguments _ _ _ = NONE
End

val bind_arguments_pre_def = cv_auto_trans_pre "bind_arguments_pre" bind_arguments_def;

Theorem bind_arguments_pre[cv_pre]:
  ∀x y z. bind_arguments_pre x y z
Proof
  ho_match_mp_tac bind_arguments_ind \\ rw[]
  \\ rw[Once bind_arguments_pre_def]
QED

Definition handle_function_def:
  handle_function (ReturnException v) = return v ∧
  handle_function (Error e) = raise $ Error e ∧
  handle_function (AssertException str) = raise $ AssertException str ∧
  handle_function _ = raise $ Error (TypeError "handle_function")
End

val () = handle_function_def
  |> SRULE [FUN_EQ_THM]
  |> cv_auto_trans;

(* helpers for the termination argument for the main interpreter definition
* (evaulate_def below) *)

Theorem expr1_size_map:
  expr1_size ls = LENGTH ls + SUM (MAP expr2_size ls)
Proof
  Induct_on`ls` \\ rw[expr_size_def]
QED

Theorem expr2_size_map:
  expr2_size x = 1 + list_size char_size (FST x) + expr_size (SND x)
Proof
  Cases_on`x` \\ rw[expr_size_def]
QED

Theorem SUM_MAP_expr2_size:
  SUM (MAP expr2_size ls) =
  LENGTH ls +
  SUM (MAP (list_size char_size o FST) ls) +
  SUM (MAP (expr_size o SND) ls)
Proof
  Induct_on`ls` \\ rw[expr2_size_map]
QED

(* Cached helper for the callable-table part of bound_def termination. *)
Theorem callable_table_measure_ADELKEY_LE[local]:
  !key ts dflts ss.
    ALOOKUP ts key = SOME (dflts, ss) ==>
    SUM (MAP (\(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss)
             (ADELKEY key ts)) +
    (list_size expr_size dflts + list_size stmt_size ss) <=
    SUM (MAP (\(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts)
Proof
  rpt strip_tac >>
  drule ALOOKUP_MEM >>
  rw[ADELKEY_def] >>
  qmatch_goalsub_abbrev_tac `MAP f (FILTER P ts)` >>
  drule_then(qspecl_then[`f`,`P`]mp_tac) SUM_MAP_FILTER_MEM_LE >>
  simp[Abbr`P`, Abbr`f`]
QED

Definition bound_def:
  stmt_bound ts Pass = 0n ∧
  stmt_bound ts Continue = 0 ∧
  stmt_bound ts Break = 0 ∧
  stmt_bound ts (Return NONE) = 0 ∧
  stmt_bound ts (Return (SOME e)) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Raise RaiseBare) = 0 ∧
  stmt_bound ts (Raise RaiseUnreachable) = 0 ∧
  stmt_bound ts (Raise (RaiseReason e)) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Assert e1 AssertBare) =
    1 + expr_bound ts e1 ∧
  stmt_bound ts (Assert e1 AssertUnreachable) =
    1 + expr_bound ts e1 ∧
  stmt_bound ts (Assert e1 (AssertReason e2)) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  stmt_bound ts (Log _ es) =
    1 + exprs_bound ts es ∧
  stmt_bound ts (AnnAssign _ _ e) =
    1 + expr_bound ts e ∧
  stmt_bound ts (Append bt e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  stmt_bound ts (Assign g e) =
    1 + target_bound ts g
      + expr_bound ts e ∧
  stmt_bound ts (AugAssign _ bt _ e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  stmt_bound ts (If e ss1 ss2) =
    1 + expr_bound ts e +
     MAX (stmts_bound ts ss1)
         (stmts_bound ts ss2) ∧
  stmt_bound ts (For _ _ it n ss) =
    1 + iterator_bound ts it +
    1 + n + n * (stmts_bound ts ss) ∧
  stmt_bound ts (Expr e) =
    1 + expr_bound ts e ∧
  stmts_bound ts [] = 0 ∧
  stmts_bound ts (s::ss) =
    1 + stmt_bound ts s
      + stmts_bound ts ss ∧
  iterator_bound ts (Array e) =
    1 + expr_bound ts e ∧
  iterator_bound ts (Range e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  target_bound ts (BaseTarget bt) =
    1 + base_target_bound ts bt ∧
  target_bound ts (TupleTarget gs) =
    1 + targets_bound ts gs ∧
  targets_bound ts [] = 0 ∧
  targets_bound ts (g::gs) =
    1 + target_bound ts g
      + targets_bound ts gs ∧
  base_target_bound ts (NameTarget _) = 0 ∧
  base_target_bound ts (TopLevelNameTarget _) = 0 ∧
  base_target_bound ts (AttributeTarget bt _) =
    1 + base_target_bound ts bt ∧
  base_target_bound ts (SubscriptTarget bt e) =
    1 + base_target_bound ts bt
      + expr_bound ts e ∧
  expr_bound ts (Name _ _) = 0 ∧
  expr_bound ts (TopLevelName _ _) = 0 ∧
  expr_bound ts (FlagMember _ _ _) = 0 ∧
  expr_bound ts (IfExp _ e1 e2 e3) =
    1 + expr_bound ts e1
      + MAX (expr_bound ts e2)
            (expr_bound ts e3) ∧
  expr_bound ts (Subscript _ e1 e2) =
    1 + expr_bound ts e1
      + expr_bound ts e2 ∧
  expr_bound ts (Attribute _ e _) =
    1 + expr_bound ts e ∧
  expr_bound ts (Literal _ _) = 0 ∧
  expr_bound ts (StructLit _ _ kes) =
    1 + exprs_bound ts (MAP SND kes) ∧
  expr_bound ts (Builtin _ _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (Pop _ bt) =
    1 + base_target_bound ts bt ∧
  expr_bound ts (TypeBuiltin _ _ _ es) =
    1 + exprs_bound ts es ∧
  expr_bound ts (Call _ (IntCall (src_id_opt, fn)) es drv) =
    1 + exprs_bound ts es
      + (case drv of NONE => 0 | SOME e => expr_bound ts e)
      + (case ALOOKUP ts (src_id_opt, fn) of
         | SOME (dflts, ss) => exprs_bound (ADELKEY (src_id_opt, fn) ts) dflts
                             + stmts_bound (ADELKEY (src_id_opt, fn) ts) ss
         | NONE => 0) ∧
  expr_bound ts (Call _ t es drv) =
    1 + exprs_bound ts es
      + (case drv of NONE => 0 | SOME e => expr_bound ts e) ∧
  exprs_bound ts [] = 0 ∧
  exprs_bound ts (e::es) =
    1 + expr_bound ts e
      + exprs_bound ts es
Termination
  WF_REL_TAC ‘measure (λx. case x of
  | INR (INR (INR (INR (INR (INR (INR (ts, es))))))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      list_size expr_size es
  | INR (INR (INR (INR (INR (INR (INL (ts, e))))))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      expr_size e
  | INR (INR (INR (INR (INR (INL (ts, bt)))))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      base_assignment_target_size bt
  | INR (INR (INR (INR (INL (ts, gs))))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      list_size assignment_target_size gs
  | INR (INR (INR (INL (ts, g)))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      assignment_target_size g
  | INR (INR (INL (ts, it))) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      iterator_size it
  | INR (INL (ts, ss)) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      list_size stmt_size ss
  | INL (ts, s) =>
      SUM (MAP (λ(k, dflts, ss). list_size expr_size dflts + list_size stmt_size ss) ts) +
      stmt_size s)’
  \\ rw[expr1_size_map, expr2_size_map, SUM_MAP_expr2_size,
        MAP_MAP_o, list_size_pair_size_map]
  \\ TRY (gvs[] \\ drule callable_table_measure_ADELKEY_LE \\ simp[])
End

Theorem exprs_bound_DROP:
  ∀ts n es. exprs_bound ts (DROP n es) ≤ exprs_bound ts es
Proof
  Induct_on `es` \\ rw[bound_def, DROP_def]
  \\ Cases_on`n` \\ gvs[]
  \\ qmatch_goalsub_rename_tac`DROP n es`
  \\ first_x_assum(qspecl_then[`ts`,`n`]mp_tac)
  \\ simp[]
QED

(* Extract callable functions - for termination proof *)
(* Internal and Deploy are separate so we can order Internal before Deploy *)
Definition dest_Internal_Fn_def:
  dest_Internal_Fn (FunctionDecl Internal _ _ _ fn _ dflts _ ss) = [(fn, (dflts, ss))] ∧
  dest_Internal_Fn _ = []
End

Definition dest_Deploy_Fn_def:
  dest_Deploy_Fn (FunctionDecl Deploy _ _ _ fn _ dflts _ ss) = [(fn, (dflts, ss))] ∧
  dest_Deploy_Fn _ = []
End

(* For a single module, get its callable function definitions tagged with source_id *)
(* Keys are (source_id, fn). Internal entries come before Deploy entries. *)
(* This matches lookup_callable_function which tries Internal first. *)
Definition module_fns_def:
  module_fns src_id ts =
    MAP (λ(fn, ss). ((src_id, fn), ss))
        (FLAT (MAP dest_Internal_Fn ts) ++ FLAT (MAP dest_Deploy_Fn ts))
End

(* Get all callable function definitions from all modules, keyed by (source_id, fn) *)
Definition remcode_def:
  remcode cx =
  case ALOOKUP cx.sources cx.txn.target of
    NONE => []
  | SOME mods =>
      FILTER (λ((src_id, fn), ss). ¬MEM (src_id, fn) cx.stk)
        (FLAT (MAP (λ(src_id, ts). module_fns src_id ts) mods))
End

(* these helpers are also for termination, to enable HOL4's definition machinery
* to "see through" the state-exception monad when constructing the termination
* conditions *)

Theorem bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f' s = (INL x, t) ==> g x t = g' x t)
  ⇒
  bind f g = bind f' g'
Proof
  rw[bind_def, FUN_EQ_THM] \\ CASE_TAC \\ CASE_TAC \\ gs[]
  \\ first_x_assum irule \\ goal_assum drule
QED

Theorem ignore_bind_cong_implicit[defncong]:
  (f = f') ∧
  (∀s x t. f' s = (INL x, t) ⇒ g t = g' t)
  ⇒
  ignore_bind f g = ignore_bind f' g'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong_implicit
  \\ rw[]
  \\ first_x_assum irule
  \\ goal_assum drule
QED

Theorem try_cong[defncong]:
  (f s = f' s') ∧
  (∀e t. f' s = (INR e, t) ⇒ h e t = h' e t) ∧
  (s = s')
  ⇒
  try f h s = try f' h' s'
Proof
  rw[try_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem try_cong_implicit[defncong]:
  (f = f') ∧
  (∀s e t. f' s = (INR e, t) ⇒ h e t = h' e t)
  ⇒
  try f h = try f' h'
Proof
  rw[FUN_EQ_THM]
  \\ irule try_cong \\ rw[]
  \\ first_x_assum irule
  \\ metis_tac[]
QED

Theorem bind_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (INL x, t) ==> g x t = g' x t) ∧
  (s = s')
  ⇒
  bind f g s = bind f' g' s'
Proof
  rw[bind_def] \\ CASE_TAC \\ CASE_TAC \\ gs[]
QED

Theorem ignore_bind_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (INL x, t) ⇒ g t = g' t) ∧
  (s = s')
  ⇒
  ignore_bind f g s = ignore_bind f' g' s'
Proof
  rw[ignore_bind_def]
  \\ irule bind_cong
  \\ rw[]
QED

Theorem finally_cong[defncong]:
  (f s = f' s') ∧
  (∀x t. f' s = (x, t) ⇒ g t = g' t) ∧
  (s = s')
  ⇒
  finally f g s = finally f' g' s'
Proof
  rw[finally_def]
  \\ CASE_TAC \\ CASE_TAC
  \\ irule ignore_bind_cong \\ gs[]
QED

(* lookup_function with Internal finds body via ALOOKUP on dest_Internal_Fn *)
Theorem lookup_function_Internal_imp_ALOOKUP:
  ∀src_id_opt fn vis ts v nr w x y z.
  lookup_function src_id_opt fn vis ts = SOME (v,nr,w,x,y,z) ∧ vis = Internal ⇒
  (x, z) = ([], []) ∨ ALOOKUP (FLAT (MAP dest_Internal_Fn ts)) fn = SOME (x, z)
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Internal_Fn_def]
  \\ gvs[dest_Internal_Fn_def]
  \\ rename1 `FunctionDecl fv _ _ _ _ _ _ _ _`
  \\ Cases_on `fv` \\ gvs[dest_Internal_Fn_def]
QED

(* lookup_function with Deploy finds body via ALOOKUP on dest_Deploy_Fn *)
Theorem lookup_function_Deploy_imp_ALOOKUP:
  ∀src_id_opt fn vis ts v nr w x y z.
  lookup_function src_id_opt fn vis ts = SOME (v,nr,w,x,y,z) ∧ vis = Deploy ⇒
  (x, z) = ([], []) ∨ ALOOKUP (FLAT (MAP dest_Deploy_Fn ts)) fn = SOME (x, z)
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Deploy_Fn_def]
  \\ gvs[dest_Deploy_Fn_def]
  \\ rename1 `FunctionDecl fv _ _ _ _ _ _ _ _`
  \\ Cases_on `fv` \\ gvs[dest_Deploy_Fn_def]
QED

(* If Internal lookup fails, no Internal entry in the list *)
Theorem lookup_function_Internal_NONE_imp:
  ∀src_id_opt fn vis ts.
  lookup_function src_id_opt fn vis ts = NONE ∧ vis = Internal ⇒
  ALOOKUP (FLAT (MAP dest_Internal_Fn ts)) fn = NONE
Proof
  ho_match_mp_tac lookup_function_ind
  \\ rw[lookup_function_def, dest_Internal_Fn_def]
  \\ gvs[dest_Internal_Fn_def]
  \\ rename1 `FunctionDecl fv _ _ _ _ _ _ _ _`
  \\ Cases_on `fv` \\ gvs[dest_Internal_Fn_def]
QED

(* Key lemma: lookup_callable_function finds exactly what ALOOKUP on module_fns finds *)
(* This works because module_fns orders Internal entries before Deploy entries, *)
(* matching lookup_callable_function which tries Internal first. *)
Theorem lookup_callable_function_eq_ALOOKUP_module_fns:
  ∀in_deploy fn ts src_id v nr w x y z.
  lookup_callable_function in_deploy fn ts = SOME (v,nr,w,x,y,z) ∧ (x, z) ≠ ([], []) ⇒
  ALOOKUP (module_fns src_id ts) (src_id, fn) = SOME (x, z)
Proof
  rpt gen_tac
  \\ simp[lookup_callable_function_def, module_fns_def]
  \\ gvs[CaseEq"option"]
  \\ reverse strip_tac
  (* Case 1: Internal found *)
  >- (
    drule lookup_function_Internal_imp_ALOOKUP \\ rw[]
    \\ simp[ALOOKUP_APPEND]
    \\ qmatch_goalsub_abbrev_tac`option_CASE alo`
    \\ `alo = SOME (x, z)` suffices_by simp[]
    \\ qunabbrev_tac `alo`
    \\ pop_assum $ SUBST1_TAC o SYM
    \\ qmatch_goalsub_abbrev_tac`MAP fi`
    \\ `fi = $, src_id ## I` by simp[Abbr`fi`, FUN_EQ_THM, FORALL_PROD]
    \\ pop_assum SUBST_ALL_TAC
    \\ irule ALOOKUP_MAP_KEY_INJ
    \\ simp[]
  )
  (* Case 2: Internal NONE, Deploy found *)
  \\ drule lookup_function_Deploy_imp_ALOOKUP \\ rw[]
  \\ drule lookup_function_Internal_NONE_imp \\ rw[]
  \\ simp[ALOOKUP_APPEND]
  \\ qmatch_goalsub_abbrev_tac`option_CASE alo`
  \\ qmatch_goalsub_abbrev_tac`MAP fi`
  \\ `fi = $, src_id ## I` by simp[Abbr`fi`, FUN_EQ_THM, FORALL_PROD]
  \\ pop_assum SUBST_ALL_TAC
  \\ `alo = NONE`
  by (
    qpat_x_assum`_ = NONE` $ SUBST1_TAC o SYM
    \\ qunabbrev_tac`alo`
    \\ irule ALOOKUP_MAP_KEY_INJ
    \\ simp[] )
  \\ simp[]
  \\ qpat_x_assum`_ = SOME _` $ SUBST1_TAC o SYM
  \\ irule ALOOKUP_MAP_KEY_INJ
  \\ simp[]
QED

(* Helper: ALOOKUP in module_fns is NONE when src_id doesn't match *)
Theorem ALOOKUP_module_fns_diff_src:
  ∀ts sid1 sid2 fn.
    sid1 ≠ sid2 ⇒ ALOOKUP (module_fns sid1 ts) (sid2, fn) = NONE
Proof
  rw[module_fns_def, ALOOKUP_FAILS, MEM_MAP, MEM_APPEND, PULL_EXISTS, FORALL_PROD]
QED

(* Helper for ALOOKUP in FLAT of MAPs *)
Theorem ALOOKUP_FLAT_MAP_module_fns:
  ∀mods src_id ts fn body.
    ALOOKUP mods src_id = SOME ts ∧
    ALOOKUP (module_fns src_id ts) (src_id, fn) = SOME body ⇒
    ALOOKUP (FLAT (MAP (λ(sid, tl). module_fns sid tl) mods)) (src_id, fn) = SOME body
Proof
  Induct \\ rw[]
  \\ simp[ALOOKUP_APPEND]
  \\ PairCases_on`h`
  \\ gvs[ALOOKUP_module_fns_diff_src, AllCaseEqs()]
QED

(* a few more helper functions used in the main interpreter *)

Definition handle_loop_exception_def:
  handle_loop_exception e =
  if e = ContinueException then return F
  else if e = BreakException then return T
  else raise e
End

val () = handle_loop_exception_def
  |> SRULE [FUN_EQ_THM, COND_RATOR]
  |> cv_auto_trans;

Definition switch_BoolV_def:
  switch_BoolV v f g =
  if v = Value $ BoolV T then f
  else if v = Value $ BoolV F then g
  else raise $ Error (TypeError (if is_Value v then "not BoolV" else "not Value"))
End

Definition exactly_one_option_def:
  exactly_one_option NONE NONE = INR (TypeError "no option") ∧
  exactly_one_option (SOME _) (SOME _) = INR (TypeError "two options") ∧
  exactly_one_option (SOME x) _ = INL x ∧
  exactly_one_option _ (SOME y) = INL y
End

val () = cv_auto_trans exactly_one_option_def;

(* Check whether variable n is declared as Immutable (not Constant) in toplevels *)
Definition is_immutable_decl_def:
  is_immutable_decl n [] = F ∧
  is_immutable_decl n (VariableDecl _ Immutable vid _ _ :: ts) =
    (if string_to_num vid = n then T else is_immutable_decl n ts) ∧
  is_immutable_decl n (_ :: ts) = is_immutable_decl n ts
End

val () = cv_auto_trans is_immutable_decl_def;

Definition immutable_target_def:
  immutable_target (imms: num |-> (type_value # value)) src_id_opt id n =
  case FLOOKUP imms n of SOME _ => SOME $ ImmutableVar src_id_opt id
     | _ => NONE
End

val () = cv_auto_trans immutable_target_def;

Definition get_range_limits_def:
  get_range_limits (IntV n1) (IntV n2) =
  (if n1 ≤ n2
   then INL (n1, Num (n2 - n1))
   else INR (RuntimeError "no range")) ∧
  get_range_limits _ _ = INR (TypeError "range not IntV")
End

val () = cv_auto_trans get_range_limits_def;

(* ===== External Call Execution via Verifereum ===== *)

(* Build a transaction record for initial_context.
   Only the fields used by initial_msg_params matter:
   - from: becomes msg.sender (caller)
   - to: target address
   - value: becomes msg.value
   - data: becomes msg.data (calldata)
   - gasLimit: gas available for the call
   Other fields are unused placeholders. *)
Definition make_call_tx_def:
  make_call_tx caller callee value calldata gas_limit : transaction =
    <| from := caller
     ; to := SOME callee
     ; data := calldata
     ; nonce := 0
     ; value := value
     ; gasLimit := gas_limit
     ; gasPrice := 0
     ; accessList := []
     ; blobVersionedHashes := []
     ; maxFeePerBlobGas := NONE
     ; maxFeePerGas := NONE
     ; authorizationList := []
     |>
End

val () = cv_auto_trans make_call_tx_def;

(* Build transaction_parameters from Vyper call_txn.
   These are the transaction-level parameters that persist across calls.

   Maps call_txn fields to Verifereum transaction_parameters. *)
Definition vyper_to_tx_params_def:
  vyper_to_tx_params (txn: call_txn) : transaction_parameters =
    <| origin := txn.origin
     ; gasPrice := txn.gas_price
     ; baseFeePerGas := txn.base_fee
     ; baseFeePerBlobGas := txn.blob_base_fee
     ; blockNumber := txn.block_number
     ; blockTimeStamp := txn.time_stamp
     ; blockCoinBase := txn.coinbase
     ; blockGasLimit := txn.gas_limit
     ; prevRandao := n2w txn.prev_randao
     ; prevHashes := txn.block_hashes
     ; blobHashes := txn.blob_hashes
     ; chainId := txn.chain_id
     ; authRefund := 0
     |>
End

val () = cv_auto_trans vyper_to_tx_params_def;

(* Default gas limit for external calls - effectively infinite.
   TODO(semantic-limitation): this may need to be configurable or supplied by
   an oracle once external-call gas modelling is formalized. *)
Definition default_call_gas_limit_def:
  default_call_gas_limit : num = 2 ** 64
End

val () = cv_auto_trans default_call_gas_limit_def;

(* Build execution_state for an external call *)
Definition make_ext_call_state_def:
  make_ext_call_state caller callee code calldata value_opt
                      accounts tStorage txParams =
    let gas_limit = default_call_gas_limit in
    let value = (case value_opt of NONE => 0 | SOME v => v) in
    let is_static = IS_NONE value_opt in
    let tx = make_call_tx caller callee value calldata gas_limit in
    let ctxt = initial_context callee code is_static empty_return_destination tx in
    (* Transfer value from caller to callee, mirroring EVM CALL behavior.
       The EVM does this in proceed_call before entering the sub-context. *)
    let accounts = vfmExecution$transfer_value caller callee value accounts in
    let accesses = <| addresses := fINSERT caller (fINSERT callee fEMPTY)
                    ; storageKeys := fEMPTY |> in
    let rollback = <| accounts := accounts
                    ; tStorage := tStorage
                    ; accesses := accesses
                    ; toDelete := [] |> in
    <| contexts := [(ctxt, rollback)]
     ; txParams := txParams
     ; rollback := rollback
     ; msdomain := Collect empty_domain
     |>
End

val () = cv_auto_trans make_ext_call_state_def;

(* Extract results from verifereum execution.
   On success: return updated accounts/tStorage.
   On revert: return original accounts/tStorage (changes are discarded).
   On other exception: return NONE. *)
Definition extract_call_result_def:
  extract_call_result orig_accounts orig_tStorage
    (result: unit + vfmExecution$exception option, final_state) =
    case final_state.contexts of
    | [(ctxt, _)] =>
        (case result of
         | INR NONE =>  (* success - no exception *)
             SOME (T, ctxt.returnData,
                   final_state.rollback.accounts,
                   final_state.rollback.tStorage, ctxt.logs)
         | INR (SOME Reverted) =>  (* revert - discard callee effects *)
             SOME (F, ctxt.returnData, orig_accounts, orig_tStorage, [])
         | _ => NONE)  (* other exception or still running *)
    | _ => NONE  (* shouldn't happen for single-context call *)
End

val () = cv_auto_trans extract_call_result_def;

Definition ext_call_value_transfer_ok_def:
  ext_call_value_transfer_ok caller callee value_opt accounts =
    case value_opt of
    | NONE => T
    | SOME amount =>
        let sender = lookup_account caller accounts in
        let recipient = lookup_account callee accounts in
          amount <= sender.balance /\
          recipient.balance + amount < 2 ** 256
End

val () = cv_auto_trans ext_call_value_transfer_ok_def;

Definition account_runtime_well_typed_def:
  account_runtime_well_typed (a : account_state) <=>
    a.balance < 2 ** 256 /\ LENGTH a.code <= 24576
End

val () = cv_auto_trans account_runtime_well_typed_def;

Definition accounts_runtime_well_typed_def:
  accounts_runtime_well_typed (accounts : evm_accounts) <=>
    !addr. account_runtime_well_typed (lookup_account addr accounts)
End

Definition accounts_spt_runtime_well_typed_def:
  (accounts_spt_runtime_well_typed (LN : account_state spt) <=> T) /\
  (accounts_spt_runtime_well_typed (LS a) <=> account_runtime_well_typed a) /\
  (accounts_spt_runtime_well_typed (BN l r) <=>
    accounts_spt_runtime_well_typed l /\ accounts_spt_runtime_well_typed r) /\
  (accounts_spt_runtime_well_typed (BS l a r) <=>
    accounts_spt_runtime_well_typed l /\ account_runtime_well_typed a /\
    accounts_spt_runtime_well_typed r)
End

val () = cv_auto_trans accounts_spt_runtime_well_typed_def;

Theorem account_runtime_well_typed_empty_account_state[simp]:
  account_runtime_well_typed empty_account_state
Proof
  simp[account_runtime_well_typed_def, empty_account_state_def]
QED

Theorem accounts_spt_runtime_well_typed_lookup:
  !t k a.
    wf t /\ accounts_spt_runtime_well_typed t /\ lookup k t = SOME a ==>
    account_runtime_well_typed a
Proof
  Induct >> rw[accounts_spt_runtime_well_typed_def, sptreeTheory.lookup_def,
                sptreeTheory.wf_def]
  >> metis_tac[]
QED

Theorem accounts_spt_runtime_well_typed_insert:
  !k a t.
    accounts_spt_runtime_well_typed t /\ account_runtime_well_typed a ==>
    accounts_spt_runtime_well_typed (insert k a t)
Proof
  recInduct sptreeTheory.insert_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >> strip_tac >>
  gvs[accounts_spt_runtime_well_typed_def] >>
  Cases_on `k = 0` >-
    simp[Once sptreeTheory.insert_def, accounts_spt_runtime_well_typed_def] >>
  Cases_on `EVEN k` >-
    (PURE_ONCE_REWRITE_TAC [sptreeTheory.insert_def] >>
     gvs[accounts_spt_runtime_well_typed_def]) >>
  PURE_ONCE_REWRITE_TAC [sptreeTheory.insert_def] >>
  gvs[accounts_spt_runtime_well_typed_def]
QED

Theorem accounts_spt_runtime_well_typed_build_spt:
  !accounts.
    accounts_spt_runtime_well_typed
      (build_spt empty_account_state (dimword (:160)) accounts) <=>
    accounts_runtime_well_typed accounts
Proof
  rw[accounts_runtime_well_typed_def, EQ_IMP_THM]
  >- (
    Cases_on `accounts addr = empty_account_state` >- simp[lookup_account_def] >>
    `lookup (w2n addr) (build_spt empty_account_state (dimword (:160)) accounts) =
       SOME (accounts addr)`
      by (simp[lookup_build_spt] >> qspec_then `addr` mp_tac wordsTheory.w2n_lt >> simp[]) >>
    simp[lookup_account_def] >>
    irule accounts_spt_runtime_well_typed_lookup >>
    qexistsl [`w2n addr`, `build_spt empty_account_state (dimword (:160)) accounts`] >>
    simp[] ) >>
  qsuff_tac `!n. accounts_spt_runtime_well_typed
                   (build_spt empty_account_state n accounts)` >- simp[] >>
  Induct >- simp[build_spt_def, accounts_spt_runtime_well_typed_def] >>
  simp[build_spt_def] >> rw[] >>
  irule accounts_spt_runtime_well_typed_insert >> simp[] >>
  first_x_assum (qspec_then `n2w n` mp_tac) >> simp[lookup_account_def]
QED

val cv_accounts_spt_runtime_well_typed_thm = theorem "cv_accounts_spt_runtime_well_typed_thm";

Theorem accounts_runtime_well_typed_cv_rep[cv_rep]:
  cv_rep T
    (cv_accounts_spt_runtime_well_typed (from_evm_accounts accounts))
    b2c
    (accounts_runtime_well_typed accounts)
Proof
  simp[cv_repTheory.cv_rep_def, from_evm_accounts_def,
       GSYM cv_accounts_spt_runtime_well_typed_thm] >>
  AP_TERM_TAC >>
  simp[Once (GSYM accounts_spt_runtime_well_typed_build_spt)]
QED

Definition ext_call_success_accounts_ok_aux_def:
  ext_call_success_accounts_ok_aux
    (result : unit + vfmExecution$exception option) accounts =
    case result of
    | INR NONE => accounts_runtime_well_typed accounts
    | _ => T
End

val () = cv_auto_trans ext_call_success_accounts_ok_aux_def;

Definition ext_call_success_accounts_ok_def:
  ext_call_success_accounts_ok
    (outcome : (unit + vfmExecution$exception option) # vfmContext$execution_state) =
    ext_call_success_accounts_ok_aux (FST outcome) (SND outcome).rollback.accounts
End


(* Run external call via verifereum.

   Parameters:
   - caller: address of the calling contract (becomes msg.sender)
   - callee: address being called
   - calldata: encoded function call (from build_ext_calldata)
   - value: ETH to send (becomes msg.value)
   - is_static: true for staticcall (read-only)
   - accounts: current account states
   - tStorage: current transient storage
   - txParams: transaction parameters (preserves tx.origin, block info)

   Returns SOME (success, returnData, accounts', tStorage', emitted_logs)
   or NONE on error. Reverted calls return an empty emitted-log list. *)
Definition run_ext_call_def:
  run_ext_call caller callee calldata value_opt
               accounts tStorage txParams =
    if ext_call_value_transfer_ok caller callee value_opt accounts then
      let code = (lookup_account callee accounts).code in
      let s0 = make_ext_call_state caller callee code calldata value_opt
                                   accounts tStorage txParams in
      if fIN callee precompile_addresses then
        let outcome = vfmExecution$dispatch_precompiles callee s0 in
          if ext_call_success_accounts_ok outcome then
            extract_call_result accounts tStorage outcome
          else NONE
      else
        case vfmExecution$run_call s0 of
        | SOME outcome =>
            if ext_call_success_accounts_ok outcome then
              extract_call_result accounts tStorage outcome
            else NONE
        | NONE => NONE
    else NONE
End

val () = cv_auto_trans run_ext_call_def;

(* Dynamic array bounds check: reads stored length from storage *)
Definition check_array_bounds_def:
  check_array_bounds cx (ArrayRef is_transient base_slot _ (Dynamic _)) (IntV i) = do
    storage <- get_storage_backend cx is_transient;
    stored_len <<- w2n (lookup_storage base_slot storage);
    check (0 ≤ i ∧ Num i < stored_len) "subscript dynamic array oob"
  od ∧
  check_array_bounds _ _ _ = return ()
End

val () = check_array_bounds_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, check_def,
            toplevel_value_CASE_rator]
  |> cv_auto_trans;

(* ===== Reentrancy Lock Helpers ===== *)
(* Vyper's @nonreentrant uses transient storage (EIP-1153 on Cancun+).
   Lock values: 0 = unlocked (final), 1 = locked (temp).
   On entry: assert TLOAD(slot) ≠ 1, then TSTORE(slot, 1).
   On exit: TSTORE(slot, 0).
   For view functions: only check, don't acquire/release. *)

(* Check and acquire the reentrancy lock.
   Uses monadic transient storage accessors for cv_auto_trans compatibility. *)
Definition acquire_nonreentrant_lock_def:
  acquire_nonreentrant_lock (addr : address) (slot : num) (is_view : bool) = do
    tStore <- get_transient_storage;
    current <<- vfmState$lookup_storage (n2w slot)
                  (vfmExecution$lookup_transient_storage addr tStore);
    if current = 1w then raise (Error (RuntimeError "nonreentrant lock"))
    else if is_view then return ()
    else update_transient
      (vfmExecution$update_transient_storage addr
         (vfmState$update_storage (n2w slot) 1w
            (vfmExecution$lookup_transient_storage addr tStore)))
  od
End

val () = acquire_nonreentrant_lock_def
  |> SRULE [vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
            FUN_EQ_THM, LET_THM, COND_RATOR,
            get_transient_storage_def, update_transient_def,
            vyperStateTheory.return_def, vyperStateTheory.raise_def]
  |> cv_auto_trans;

(* Release the reentrancy lock *)
Definition release_nonreentrant_lock_def:
  release_nonreentrant_lock (addr : address) (slot : num) = do
    tStore <- get_transient_storage;
    update_transient
      (vfmExecution$update_transient_storage addr
         (vfmState$update_storage (n2w slot) 0w
            (vfmExecution$lookup_transient_storage addr tStore)))
  od
End

val () = release_nonreentrant_lock_def
  |> SRULE [vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
            FUN_EQ_THM, LET_THM,
            get_transient_storage_def, update_transient_def,
            vyperStateTheory.return_def]
  |> cv_auto_trans;

(* top-level definition of the Vyper interpreter *)

Definition evaluate_def:
  eval_stmt cx Pass = return () ∧
  eval_stmt cx Continue = raise ContinueException ∧
  eval_stmt cx Break = raise BreakException ∧
  eval_stmt cx (Return NONE) = raise $ ReturnException NoneV ∧
  eval_stmt cx (Return (SOME e)) = do
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    raise $ ReturnException v
  od ∧
  eval_stmt cx (Raise RaiseBare) =
    raise $ AssertException "" ∧
  eval_stmt cx (Raise RaiseUnreachable) =
    raise $ AssertException "UNREACHABLE" ∧
  eval_stmt cx (Raise (RaiseReason e)) = do
    tv <- eval_expr cx e;
    v <- get_Value tv;
    s <- lift_option_type (dest_StringV v) "not StringV";
    raise $ AssertException s
  od ∧
  eval_stmt cx (Assert e AssertBare) = do
    tv <- eval_expr cx e;
    switch_BoolV tv
      (return ())
      (raise $ AssertException "")
  od ∧
  eval_stmt cx (Assert e AssertUnreachable) = do
    tv <- eval_expr cx e;
    switch_BoolV tv
      (return ())
      (raise $ AssertException "UNREACHABLE")
  od ∧
  eval_stmt cx (Assert e (AssertReason se)) = do
    tv <- eval_expr cx e;
    switch_BoolV tv
      (return ())
      (do
         stv <- eval_expr cx se;
         sv <- get_Value stv;
         s <- lift_option_type (dest_StringV sv) "not StringV";
         raise $ AssertException s
       od)
  od ∧
  eval_stmt cx (Log id es) = do
    (* Checked programs guarantee that the declaration exists and that its
       evaluated arguments can be encoded using the declared types. *)
    vs <- eval_exprs cx es;
    event <- lift_option
      (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
      "Log encode event";
    push_log event
  od ∧
  eval_stmt cx (AnnAssign id typ e) = do
    tenv <<- get_tenv cx;
    tyv <- lift_option_type (evaluate_type tenv typ) "AnnAssign evaluate_type";
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    new_variable id tyv v
  od ∧
  eval_stmt cx (Append t e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    assign_target cx (BaseTargetV loc sbs) (AppendOp v);
    return ()
  od ∧
  eval_stmt cx (Assign g e) = do
    gv <- eval_target cx g;
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    assign_target cx gv (Replace v);
    return ()
  od ∧
  eval_stmt cx (AugAssign ty t bop e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    assign_target cx (BaseTargetV loc sbs) (Update ty bop v);
    return ()
  od ∧
  eval_stmt cx (If e ss1 ss2) = do
    tv <- eval_expr cx e;
    push_scope;
    finally (
      switch_BoolV tv
        (eval_stmts cx ss1)
        (eval_stmts cx ss2)
    ) pop_scope
  od ∧
  eval_stmt cx (For id typ it n body) = do
    tenv <<- get_tenv cx;
    tyv <- lift_option_type (evaluate_type tenv typ) "For evaluate_type";
    vs <- eval_iterator cx it;
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
    eval_for cx tyv (string_to_num id) body vs
  od ∧
  eval_stmt cx (Expr e) = do
    tv <- eval_expr cx e;
    type_check (¬is_HashMapRef tv) "Expr HashMapRef"
  od ∧
  eval_stmts cx [] = return () ∧
  eval_stmts cx (s::ss) = do
    eval_stmt cx s; eval_stmts cx ss
  od ∧
  eval_iterator cx (Array e) = do
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    arr_tv <- lift_option_type (evaluate_type (get_tenv cx) (expr_type e)) "For array type";
    vs <- lift_option_type (extract_elements arr_tv v) "For not ArrayV";
    return vs
  od ∧
  eval_iterator cx (Range e1 e2) = do
    tv1 <- eval_expr cx e1;
    v1 <- get_Value tv1;
    tv2 <- eval_expr cx e2;
    v2 <- get_Value tv2;
    rl <- lift_sum $ get_range_limits v1 v2;
    n1 <<- FST rl; n2 <<- SND rl;
    return $ GENLIST (λn. IntV (n1 + &n)) n2
  od ∧
  eval_target cx (BaseTarget t) = do
    (loc, sbs) <- eval_base_target cx t;
    return $ BaseTargetV loc sbs
  od ∧
  eval_target cx (TupleTarget gs) = do
    gvs <- eval_targets cx gs;
    return $ TupleTargetV gvs
  od ∧
  eval_targets cx [] = return [] ∧
  eval_targets cx (g::gs) = do
    gv <- eval_target cx g;
    gvs <- eval_targets cx gs;
    return $ gv::gvs
  od ∧
  eval_base_target cx (NameTarget id) = do
    sc <- get_scopes;
    n <<- string_to_num id;
    type_check (IS_SOME (lookup_scopes n sc)) "NameTarget not in scope";
    return $ (ScopedVar id, [])
  od ∧
  eval_base_target cx (TopLevelNameTarget (src_id_opt, id)) = do
    n <<- string_to_num id;
    ts <- lift_option_type
            (get_module_code cx src_id_opt)
            "TopLevelNameTarget get_module_code";
    if is_immutable_decl n ts then return $ (ImmutableVar src_id_opt id, [])
    else return $ (TopLevelVar src_id_opt id, [])
  od ∧
  eval_base_target cx (AttributeTarget t id) = do
    (loc, sbs) <- eval_base_target cx t;
    return $ (loc, AttrSubscript id :: sbs)
  od ∧
  eval_base_target cx (SubscriptTarget t e) = do
    (loc, sbs) <- eval_base_target cx t;
    tv <- eval_expr cx e;
    v <- get_Value tv;
    return $ (loc, ValueSubscript v :: sbs)
  od ∧
  eval_for cx tyv nm body [] = return () ∧
  eval_for cx tyv nm body (v::vs) = do
    push_scope_with_var nm tyv v;
    broke <- finally
      (try (do eval_stmts cx body; return F od) handle_loop_exception)
      pop_scope ;
    if broke then return () else eval_for cx tyv nm body vs
  od ∧
  eval_expr cx (Name _ id) = do
    env <- get_scopes;
    n <<- string_to_num id;
    v <- lift_option_type (lookup_scopes_val n env) "Name not in scope";
    return $ Value v
  od ∧
  eval_expr cx (TopLevelName _ (src_id_opt, id)) =
    lookup_global cx src_id_opt (string_to_num id) ∧
  eval_expr cx (FlagMember _ nsid mid) = lookup_flag_mem cx nsid mid ∧
  eval_expr cx (IfExp _ e1 e2 e3) = do
    tv <- eval_expr cx e1;
    switch_BoolV tv
      (eval_expr cx e2)
      (eval_expr cx e3)
  od ∧
  eval_expr cx (Literal _ l) = return $ Value $ evaluate_literal l ∧
  eval_expr cx (StructLit _ (src_id_opt, id) kes) = do
    (* TODO(semantic-limitation): struct literals currently trust
       frontend/type-system checks; validate fields against the src_id_opt
       struct definition when full type checking is formalized. *)
    ks <<- MAP FST kes;
    vs <- eval_exprs cx (MAP SND kes);
    return $ Value $ StructV $ ZIP (ks, vs)
  od ∧
  eval_expr cx (Subscript _ e1 e2) = do
    tv1 <- eval_expr cx e1;
    tv2 <- eval_expr cx e2;
    v2 <- get_Value tv2;
    tenv <<- get_tenv cx;
    arr_tv <- lift_option_type (evaluate_type tenv (expr_type e1)) "Subscript array type";
    check_array_bounds cx tv1 v2;
    res <- lift_sum $ evaluate_subscript tenv arr_tv tv1 v2;
    case res of INL v => return v | INR (is_transient, slot, tv) => do
      v <- read_storage_slot cx is_transient slot tv;
      return $ Value v
    od
  od ∧
  eval_expr cx (Attribute _ e id) = do
    tv <- eval_expr cx e;
    sv <- get_Value tv;
    v <- lift_sum $ evaluate_attribute sv id;
    return $ Value $ v
  od ∧
  eval_expr cx (Builtin ty bt es) = do
    type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args";
    v <- if bt = Len then do
      tv <- eval_expr cx (HD es);
      len <- toplevel_array_length cx tv;
      return $ IntV (&len)
    od else do
      vs <- eval_exprs cx es;
      acc <- get_accounts;
      lift_sum $ evaluate_builtin cx acc ty bt vs
    od;
    return $ Value v
  od ∧
  eval_expr cx (Pop _ bt) = do
    (loc, sbs) <- eval_base_target cx bt;
    popped <- assign_target cx (BaseTargetV loc sbs) PopOp;
    v <- lift_option_type popped "Pop returned NONE";
    return $ Value v
  od ∧
  eval_expr cx (TypeBuiltin _ tb typ es) = do
    type_check (type_builtin_args_length_ok tb (LENGTH es)) "TypeBuiltin args";
    vs <- eval_exprs cx es;
    v <- lift_sum $ evaluate_type_builtin cx tb typ vs;
    return $ Value v
  od ∧
  eval_expr cx (Call _ Send es _) = do
    type_check (LENGTH es = 2) "Send args";
    vs <- eval_exprs cx es;
    toAddr <- lift_option_type (dest_AddressV $ EL 0 vs) "Send not AddressV";
    amount <- lift_option_type (dest_NumV $ EL 1 vs) "Send not NumV";
    transfer_value cx.txn.target toAddr amount;
    return $ Value $ NoneV
  od ∧
  eval_expr cx (Call _ (ExtCall is_static (func_name, arg_types, ret_type)) es drv) = do
    vs <- eval_exprs cx es;
    type_check (vs ≠ []) "ExtCall no target";
    target_addr <- lift_option_type (dest_AddressV (HD vs)) "ExtCall target not address";
    (* Convention: staticcall (T) args = [target; arg1; ...]
                   extcall (F) args = [target; value; arg1; ...] *)
    (value_opt, arg_vals) <- if is_static then
      return (NONE, TL vs)
    else do
      type_check (TL vs ≠ []) "ExtCall no value";
      v <- lift_option_type (dest_NumV (HD (TL vs))) "ExtCall value not int";
      return (SOME v, TL (TL vs))
    od;
    tenv <<- get_tenv cx;
    calldata <- lift_option_type (build_ext_calldata tenv func_name arg_types arg_vals)
                                 "ExtCall build_calldata";
    accounts <- get_accounts;
    (* Vyper reverts if target has no code (EXTCODESIZE == 0) *)
    check (¬NULL (lookup_account target_addr accounts).code) "ExtCall target has no code";
    tStorage <- get_transient_storage;
    txParams <<- vyper_to_tx_params cx.txn;
    caller <<- cx.txn.target;
    result <- lift_option
      (run_ext_call caller target_addr calldata value_opt accounts tStorage txParams)
      "ExtCall run failed";
    (success, returnData, accounts', tStorage', emitted_logs) <<- result;
    check success "ExtCall reverted";
    update_accounts (K accounts');
    update_transient (K tStorage');
    append_logs emitted_logs;
    if returnData = [] ∧ IS_SOME drv then
      eval_expr cx (THE drv)
    else do
      ret_val <- lift_sum_runtime (evaluate_abi_decode_return tenv ret_type returnData);
      return $ Value ret_val
    od
  od ∧
  eval_expr cx (Call _ (IntCall (src_id_opt, fn)) es _) = do
    type_check (¬MEM (src_id_opt, fn) cx.stk) "recursion";
    ts <- lift_option_type (get_module_code cx src_id_opt) "IntCall get_module_code";
    tup <- lift_option_type (lookup_callable_function cx.in_deploy fn ts) "IntCall lookup_function";
    (* tup = (mut, nr, args, dflts, ret, body) *)
    mut <<- FST tup; stup <<- SND tup; nr <<- FST stup; stup2 <<- SND stup;
    args <<- FST stup2; sstup <<- SND stup2;
    dflts <<- FST sstup; sstup2 <<- SND sstup;
    ret <<- FST $ sstup2; body <<- SND $ sstup2;
    type_check (LENGTH es ≤ LENGTH args ∧
           LENGTH args - LENGTH es ≤ LENGTH dflts) "IntCall args length";
    vs <- eval_exprs cx es;
    needed_dflts <<- DROP (LENGTH dflts - (LENGTH args - LENGTH es)) dflts;
    cxd <<- cx with stk updated_by CONS (src_id_opt, fn);
    prev <- get_scopes;
    dflt_vs <- finally
      (do set_scopes [FEMPTY];
          eval_exprs cxd needed_dflts
       od)
      (set_scopes prev);
    (* Use combined type env (may reference types from other modules) *)
    all_tenv <<- get_tenv cx;
    env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs)) "IntCall bind_arguments";
    rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
    is_view <<- (mut = View ∨ mut = Pure);
    (* Acquire reentrancy lock BEFORE push_function so scopes are
       unmodified if lock acquire fails (preserves scopes_dom property).
       Lock operates only on transient storage, independent of scopes. *)
    (if nr then
       case cx.nonreentrant_slot of
       | NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return ());
    cxf <- push_function (src_id_opt, fn) env cx;
    rv <- finally
      (try (do eval_stmts cxf body; return NoneV od) handle_function)
      (do pop_function prev;
          (* Release reentrancy lock if nonreentrant and not view *)
          if nr ∧ ¬is_view then
            case cx.nonreentrant_slot of
            | NONE => return ()
            | SOME slot => release_nonreentrant_lock cx.txn.target slot
          else return ()
       od);
    crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
    return $ Value crv
  od ∧
  (* ===== Chain interaction builtins ===== *)
  (* raw_call(to, data, max_outsize=0, value=0, is_delegate_call=F, is_static_call=F, revert_on_failure=T)
     args = [to_addr; data_bytes; value] *)
  eval_expr cx (Call ty (RawCallTarget flags) es _) = do
    vs <- eval_exprs cx es;
    type_check (LENGTH vs = 3) "raw_call args";
    target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
    calldata <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
    amount <- lift_option_type (dest_NumV (EL 2 vs)) "raw_call value";
    value_opt <<- if flags.rcf_is_static then NONE else SOME amount;
    (* delegate_call not yet supported in semantics *)
    type_check (¬flags.rcf_is_delegate) "raw_call delegate unsupported";
    accounts <- get_accounts;
    tStorage <- get_transient_storage;
    txParams <<- vyper_to_tx_params cx.txn;
    caller <<- cx.txn.target;
    result <- lift_option
      (run_ext_call caller target_addr calldata value_opt accounts tStorage txParams)
      "raw_call run failed";
    (success, returnData, accounts', tStorage', emitted_logs) <<- result;
    update_accounts (K accounts');
    update_transient (K tStorage');
    append_logs emitted_logs;
    if flags.rcf_revert_on_failure then do
      check success "raw_call reverted";
      if flags.rcf_max_outsize = 0 then return $ Value NoneV
      else return $ Value $ BytesV (TAKE flags.rcf_max_outsize returnData)
    od else
      if flags.rcf_max_outsize = 0 then return $ Value $ BoolV success
      else return $ Value $ ArrayV $ TupleV [BoolV success;
             BytesV (TAKE flags.rcf_max_outsize returnData)]
  od ∧
  (* raw_log(topics_list, data)
     args = [topics_array; data_bytes] *)
  eval_expr cx (Call _ RawLog es _) = do
    vs <- eval_exprs cx es;
    type_check (LENGTH vs = 2) "raw_log args";
    topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
    data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
    topic_vals <<- (case topics of
       TupleV vs => vs | DynArrayV vs => vs | _ => []);
    type_check (LENGTH topic_vals ≤ 4) "raw_log too many topics";
    push_log (encode_raw_event_values cx.txn.target topic_vals data);
    return $ Value NoneV
  od ∧
  (* raw_revert(data) — terminus *)
  eval_expr cx (Call _ RawRevert es _) = do
    vs <- eval_exprs cx es;
    type_check (LENGTH vs = 1) "raw_revert args";
    raise $ Error $ RuntimeError "raw_revert"
  od ∧
  (* selfdestruct(to) — terminus *)
  eval_expr cx (Call _ SelfDestructTarget es _) = do
    vs <- eval_exprs cx es;
    type_check (LENGTH vs = 1) "selfdestruct args";
    target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "selfdestruct target";
    accounts <- get_accounts;
    self_acct <<- lookup_account cx.txn.target accounts;
    balance <<- self_acct.balance;
    (* Transfer all balance to target *)
    transfer_value cx.txn.target target_addr balance;
    (* Zero out sender balance (handled by transfer_value if target ≠ self) *)
    (* Note: post-Cancun, selfdestruct only sends balance, does not delete account
       unless in same transaction as creation. We model the simple case. *)
    return $ Value NoneV
  od ∧
  (* Creation operands use the kind-specific runtime layouts documented on
     CreateTarget.  eval_exprs preserves their evaluation order and the shared
     helper performs decoding, initcode/address derivation and account effects. *)
  eval_expr cx (Call ty (CreateTarget kind has_salt rof) es _) = do
    vs <- eval_exprs cx es;
    eval_create cx kind has_salt rof (MAP expr_type es) vs
  od ∧
  eval_exprs cx [] = return [] ∧
  eval_exprs cx (e::es) = do
    tv <- eval_expr cx e;
    v <- materialise cx tv;
    vs <- eval_exprs cx es;
    return $ v::vs
  od
Termination
  WF_REL_TAC ‘measure (λx. case x of
  | INR (INR (INR (INR (INR (INR (INR (INR (cx, es))))))))
    => exprs_bound (remcode cx) es
  | INR (INR (INR (INR (INR (INR (INR (INL (cx, e))))))))
    => expr_bound (remcode cx) e
  | INR (INR (INR (INR (INR (INR (INL (cx, tyv, nm, body, vs)))))))
    => 1 + LENGTH vs + (LENGTH vs) * (stmts_bound (remcode cx) body)
  | INR (INR (INR (INR (INR (INL (cx, t))))))
    => base_target_bound (remcode cx) t
  | INR (INR (INR (INR (INL (cx, gs)))))
    => targets_bound (remcode cx) gs
  | INR (INR (INR (INL (cx, g))))
    => target_bound (remcode cx) g
  | INR (INR (INL (cx, it)))
    => iterator_bound (remcode cx) it
  | INR (INL (cx, ss)) => stmts_bound (remcode cx) ss
  | INL (cx, s) => stmt_bound (remcode cx) s)’
  \\ rw[bound_def, MAX_DEF, MULT, IS_SOME_EXISTS] \\ gvs[]
  \\ rpt (FIRST [
    (* For loop: compatible_bound case *)
    (rename1`compatible_bound`
    \\ gvs[compatible_bound_def, check_def, type_check_def, assert_def]
    \\ qmatch_goalsub_abbrev_tac`(LENGTH vs) * x`
    \\ irule LESS_EQ_LESS_TRANS
    \\ qexists_tac`LENGTH vs + n * x + 1` \\ simp[]
    \\ PROVE_TAC[MULT_COMM, LESS_MONO_MULT]),
    (* Builtin: builtin_args_length_ok case *)
    (rename1`builtin_args_length_ok`
    \\ gvs[builtin_args_length_ok_def, check_def, type_check_def, assert_def,
           LENGTH_EQ_NUM_compute, bound_def]),
    (* TypeBuiltin: type_builtin_args_length_ok case *)
    (rename1`type_builtin_args_length_ok`
    \\ gvs[type_builtin_args_length_ok_def, check_def, type_check_def, assert_def,
           LENGTH_EQ_NUM_compute, bound_def]),
    (* IntCall cases *)
    (gvs[check_def, type_check_def, assert_def]
    \\ gvs[push_function_def, return_def]
    \\ gvs[lift_option_def, lift_option_type_def, CaseEq"option", CaseEq"prod", option_CASE_rator,
           raise_def, return_def]
    \\ gvs[remcode_def, get_module_code_def, ADELKEY_def]
    \\ TRY (qpat_x_assum`OUTR _ _ = _`kall_tac)
    \\ gvs[CaseEq"option"]
    \\ simp[bound_def]
    \\ qmatch_asmsub_rename_tac`lookup_callable_function _ fn ts = SOME (_, _, args, dflts, ret, bdy)`
    \\ Cases_on`(dflts, bdy) = ([], [])`
    >- gvs[bound_def]
    \\ `(dflts, bdy) <> ([], [])` by (strip_tac >> gvs[])
    \\ drule_all_then(qspec_then`src_id_opt`strip_assume_tac)
         lookup_callable_function_eq_ALOOKUP_module_fns
    \\ drule_at_then Any drule ALOOKUP_FLAT_MAP_module_fns
    \\ qmatch_goalsub_abbrev_tac`ALOOKUP (FILTER P ls) k`
    \\ `P = λ(k,v). ¬MEM k cx.stk` by simp[Abbr`P`,FUN_EQ_THM,FORALL_PROD]
    \\ TRY (simp[ALOOKUP_FILTER, FILTER_FILTER, Abbr`k`] \\ simp[LAMBDA_PROD]
      \\ qmatch_goalsub_abbrev_tac`exprs_bound fts (DROP n dflts)`
      \\ qspecl_then[`fts`,`n`,`dflts`]mp_tac exprs_bound_DROP
      \\ simp[] \\ NO_TAC)
    \\ pop_assum SUBST_ALL_TAC
    \\ simp[ALOOKUP_FILTER]
    \\ rw[FILTER_FILTER,UNCURRY,Abbr`k`]
    \\ simp[LAMBDA_PROD])
  ])
End

Theorem eval_exprs_length:
  ∀es cx st vs rt.
  eval_exprs cx es st = (INL vs, rt)
  ⇒ LENGTH vs = LENGTH es
Proof
  Induct \\ rw[evaluate_def, return_def, bind_def]
  \\ gvs[CaseEq"prod", CaseEq"sum"]
  \\ first_x_assum irule
  \\ goal_assum drule
QED

(* Semantics of initial state of a contract after deployment *)

Definition flag_value_def:
  flag_value m n acc [] = StructV $ REVERSE acc ∧
  flag_value m n acc (id::ids) =
  flag_value m (2n*n) ((id,FlagV n)::acc) ids
End

val () = cv_auto_trans flag_value_def;

(* Initialize immutables for a single module's toplevels *)
Definition initial_immutables_module_def:
  initial_immutables_module env src_id_opt [] acc = SOME acc ∧
  initial_immutables_module env src_id_opt (VariableDecl _ Immutable id typ _ :: ts) acc =
  (case evaluate_type env typ of
   | NONE => NONE
   | SOME tv =>
     let key = string_to_num id in
     let iv = default_value tv in
       initial_immutables_module env src_id_opt ts
         (update_immutable src_id_opt key tv iv acc)) ∧
  initial_immutables_module env src_id_opt (_ :: ts) acc =
    initial_immutables_module env src_id_opt ts acc
End

val () = cv_auto_trans initial_immutables_module_def;

(* Initialize immutables for all modules *)
Definition initial_immutables_def:
  initial_immutables env [] = SOME empty_immutables ∧
  initial_immutables env ((src_id_opt, ts) :: rest) =
    case initial_immutables env rest of
    | NONE => NONE
    | SOME acc => initial_immutables_module env src_id_opt ts acc
End

val () = cv_auto_trans initial_immutables_def;

(* Look up the nonreentrant key slot from the transient storage layout.
   In Python, this is the entry with key (NONE, "$.nonreentrant_key"). *)
Definition lookup_nonreentrant_slot_def:
  lookup_nonreentrant_slot layouts addr =
    case ALOOKUP layouts addr of
    | NONE => NONE
    | SOME (_, transient_layout) =>
        ALOOKUP transient_layout (NONE, "$.nonreentrant_key")
End

val () = cv_auto_trans lookup_nonreentrant_slot_def;

Definition initial_evaluation_context_def:
  initial_evaluation_context srcs layouts tx src_id_opt =
  <| sources := srcs
   ; layouts := layouts
   ; txn := tx
   ; stk := [(src_id_opt, tx.function_name)]
   ; in_deploy := F
   ; nonreentrant_slot := lookup_nonreentrant_slot layouts tx.target
   |>
End

val () = cv_auto_trans initial_evaluation_context_def;

Datatype:
  abstract_machine = <|
    sources: (address, (num option, toplevel list) alist) alist
  ; exports: (address, (string, num) alist) alist  (* address -> (func_name -> source_id) *)
  ; immutables: (address, module_immutables) alist
  ; accounts: evm_accounts
  ; layouts: (address, storage_layout # storage_layout) alist  (* (storage, transient) *)
  ; tStorage: transient_storage
  ; logs: log list
  |>
End

Definition initial_machine_state_def:
  initial_machine_state : abstract_machine = <|
    sources := []
  ; exports := []
  ; immutables := []
  ; accounts := empty_accounts
  ; layouts := []
  ; tStorage := empty_transient_storage
  ; logs := []
  |>
End

Definition initial_state_def:
  initial_state (am: abstract_machine) scs : evaluation_state =
  <| accounts := am.accounts
   ; immutables := am.immutables
   ; logs := am.logs
   ; scopes := scs
   ; tStorage := am.tStorage
   |>
End

val () = cv_auto_trans initial_state_def;

Definition abstract_machine_from_state_def:
  abstract_machine_from_state srcs exps layouts (st: evaluation_state) =
  <| sources := srcs
   ; exports := exps
   ; immutables := st.immutables
   ; accounts := st.accounts
   ; layouts := layouts
   ; tStorage := st.tStorage
   ; logs := st.logs
   |> : abstract_machine
End

val () = cv_auto_trans abstract_machine_from_state_def;

(* Top-level entry-points into the semantics: loading (deploying) a contract,
* and calling its external functions *)

(* Merge a constants fmap into the immutables for a given module *)
Definition merge_constants_def:
  merge_constants addr src_id_opt cenv (am: abstract_machine) =
    let imms = case ALOOKUP am.immutables addr of
                 SOME m => m | NONE => empty_immutables in
    let src_imms = get_source_immutables src_id_opt imms in
    let merged = FUNION cenv src_imms in
    let imms' = set_source_immutables src_id_opt merged imms in
    am with immutables updated_by
      (λal. (addr, imms') :: ADELKEY addr al)
End

val () = cv_auto_trans merge_constants_def;

(* Evaluate constant expressions in a module's toplevels.
   Previously-evaluated constants are merged into am.immutables so that
   top-level lookups find them (constants and immutables share the same
   runtime storage). *)
Definition constants_env_def:
  constants_env _ _ _ _ [] acc = SOME acc ∧
  constants_env cx am addr src_id_opt ((VariableDecl vis (Constant e) id typ _)::ts) acc =
    (case evaluate_type (get_tenv cx) typ of
     | NONE => NONE
     | SOME tv =>
       case FST $ eval_expr cx e
         (initial_state (merge_constants addr src_id_opt acc am) []) of
       | INL (Value v) => constants_env cx am addr src_id_opt ts $
                          acc |+ (string_to_num id, (tv, v))
       | _ => NONE) ∧
  constants_env cx am addr src_id_opt (t::ts) acc =
    constants_env cx am addr src_id_opt ts acc
End

(* Set current_module to a given src_id_opt while evaluating constant
   expressions. *)
Definition set_current_module_def:
  set_current_module cx src_id_opt = cx with stk := [(src_id_opt, "")]
End

val () = cv_auto_trans set_current_module_def;

(* Evaluate constants for all modules and merge into am.immutables. *)
Definition evaluate_all_constants_def:
  evaluate_all_constants cx am addr [] = SOME am ∧
  evaluate_all_constants cx am addr ((src_id_opt, ts) :: rest) =
    case constants_env (set_current_module cx src_id_opt)
                       am addr src_id_opt ts FEMPTY of
    | NONE => NONE
    | SOME cenv =>
        let am' = merge_constants addr src_id_opt cenv am in
        evaluate_all_constants cx am' addr rest
End

Definition send_call_value_def:
  send_call_value mut cx =
  let n = cx.txn.value in
  if n = 0 then return () else do
    check (mut = Payable) "not Payable";
    transfer_value cx.txn.sender cx.txn.target n
  od
End

val () = send_call_value_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, COND_RATOR]
  |> cv_auto_trans;

Definition evaluate_defaults_def:
  evaluate_defaults cx am [] = SOME [] ∧
  evaluate_defaults cx am (e::es) =
    (case FST $ eval_expr cx e (initial_state am []) of
     | INL (Value v) =>
         (case evaluate_defaults cx am es of
          | SOME vs => SOME (v :: vs)
          | NONE => NONE)
     | _ => NONE)
End

Definition call_external_function_def:
  call_external_function am cx nr mut ts all_mods args dflts vals body ret =
  let all_tenv = type_env_all_modules all_mods in
  let n_provided = LENGTH vals in
  let n_expected = LENGTH args in
  let n_missing = n_expected - n_provided in
  if n_provided > n_expected ∨ n_missing > LENGTH dflts then
    (INR $ Error (RuntimeError "call args length"), am)
  else
  let needed_dflts = DROP (LENGTH dflts - n_missing) dflts in
  case evaluate_defaults cx am needed_dflts of
  | NONE => (INR $ Error (RuntimeError "call evaluate_defaults"), am)
  | SOME dflt_vs =>
  case bind_arguments all_tenv args (vals ++ dflt_vs)
  of NONE => (INR $ Error (RuntimeError "call bind_arguments"), am)
   | SOME env =>
  (case (if cx.in_deploy then evaluate_all_constants cx am cx.txn.target all_mods
         else SOME am)
   of NONE => (INR $ Error (RuntimeError "call constants_env"), am)
    | SOME am_c =>
   let st = initial_state am_c [env] in
   let srcs = am_c.sources in
   let exps = am_c.exports in
   let layouts = am_c.layouts in
   let is_view = (mut = View ∨ mut = Pure) in
   let lock_action = if nr then
     case cx.nonreentrant_slot of
     | NONE => raise (Error (TypeError "nonreentrant slot missing"))
     | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
     else return () in
   let unlock_action = if nr ∧ ¬is_view then
     case cx.nonreentrant_slot of
     | NONE => return ()
     | SOME slot => release_nonreentrant_lock cx.txn.target slot
     else return () in
   let (res, st) =
     (case do lock_action; send_call_value mut cx; eval_stmts cx body od st
      of
       | (INL (), st) =>
           (case unlock_action st of
            | (INL (), st) => (INL NoneV, abstract_machine_from_state srcs exps layouts st)
            | (INR e, st) => (INR e, am))
       | (INR (ReturnException v), st) =>
           (case unlock_action st of
            | (INL (), st) =>
              (let am_ret = abstract_machine_from_state srcs exps layouts st in
               case evaluate_type all_tenv ret
               of NONE => (INR (Error (TypeError "eval ret")), am)
                | SOME tv =>
               case safe_cast tv v
               of NONE => (INR (Error (TypeError "ext cast ret")), am)
                | SOME v => (INL v, am_ret))
            | (INR e, st) => (INR e, am))
       | (INR e, st) => (INR e, am)) in
    (res, st (* transient storage cleared separately via ClearTransientStorage action *)))
End

(* Lookup function, checking exports first for external calls *)
Definition lookup_exported_function_def:
  lookup_exported_function cx am func_name =
    (* First check if this function is exported from another module *)
    case ALOOKUP am.exports cx.txn.target of
      NONE => (* No exports for this contract, use main module *)
        (case get_self_code cx of
           SOME ts => lookup_function NONE func_name External ts
         | NONE => NONE)
    | SOME export_map =>
        (case ALOOKUP export_map func_name of
           SOME src_id => (* Function is exported from module src_id *)
             (case get_module_code cx (SOME src_id) of
                SOME ts => lookup_function (SOME src_id) func_name External ts
              | NONE => NONE)
         | NONE => (* Not in exports, try main module *)
             (case get_self_code cx of
                SOME ts => lookup_function NONE func_name External ts
              | NONE => NONE))
End

(* Find which module a function is in (for exported functions) *)
Definition find_function_module_def:
  find_function_module am target func_name =
    case ALOOKUP am.exports target of
      NONE => NONE  (* Use main module *)
    | SOME export_map =>
        ALOOKUP export_map func_name  (* Returns SOME src_id if exported *)
End

Definition call_external_def:
  call_external am tx =
  (* Determine which module to use for type environment *)
  let src_id_opt = find_function_module am tx.target tx.function_name in
  let cx = initial_evaluation_context am.sources am.layouts tx src_id_opt in
  (* Get all modules for this contract (needed for combined type_env) *)
  case ALOOKUP am.sources tx.target of
    NONE => (INR $ Error (RuntimeError "call get sources"), am)
  | SOME all_mods =>
  case (case src_id_opt of
          NONE => get_self_code cx
        | SOME src_id => get_module_code cx (SOME src_id))
  of NONE => (INR $ Error (RuntimeError "call get_self_code"), am)
   | SOME ts =>
  case lookup_exported_function cx am tx.function_name
  of NONE => (INR $ Error (RuntimeError "call lookup_function"), am)
   | SOME (mut, nr, args, dflts, ret, body) =>
       call_external_function am cx nr mut ts all_mods args dflts tx.args body ret
End

(* Explicit transaction boundary. Ordinary function entry preserves accumulated
   logs so that nested and sequential calls can share one transaction trace;
   callers use this wrapper when starting a fresh top-level transaction. *)
Definition clear_machine_logs_def:
  clear_machine_logs (am: abstract_machine) = am with logs := []
End

Definition call_external_transaction_def:
  call_external_transaction am tx = call_external (clear_machine_logs am) tx
End

(* Vyper-level deployment abstraction.  The target address is supplied by the
   transaction rather than derived using EVM CREATE/CREATE2 rules, and successful
   deployment installs Vyper sources and exports rather than init/runtime
   bytecode.  Creator/created-account nonce updates and bytecode installation
   therefore belong to the future correspondence with Verifereum's EVM creation
   semantics.  Constructor value transfer, however, is performed by
   call_external_function and retained on success (or rolled back on failure). *)
Definition load_contract_def:
  load_contract am tx mods exps =
  let addr = tx.target in
  let ts = case ALOOKUP mods NONE of SOME ts => ts | NONE => [] in
  let tenv = type_env_all_modules mods in
  case initial_immutables tenv mods of
  | NONE => INR $ Error (TypeError "load_contract: evaluate_type failed")
  | SOME imms =>
  let am = am with <| immutables updated_by CONS (addr, imms);
                      exports updated_by CONS (addr, exps) |> in
  case lookup_function NONE tx.function_name Deploy ts of
     | NONE => INR $ Error (RuntimeError "no constructor")
     | SOME (mut, nr, args, dflts, ret, body) =>
       let cx = (initial_evaluation_context ((addr,mods)::am.sources) am.layouts tx NONE)
                with in_deploy := T in
       case call_external_function am cx nr mut ts mods args dflts tx.args body ret
         of (INR e, _) => INR e
          | (_, am) => INL (am with sources updated_by CONS (addr, mods))
End
