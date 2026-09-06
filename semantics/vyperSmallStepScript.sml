Theory vyperSmallStep
Ancestors
  arithmetic combin pair list While
  vyperMisc vyperValue vyperContext vyperState vyperCreate vyperInterpreter vyperABI
Libs
  cv_transLib wordsLib

(*
  plan for cps version:
  - define the same functions as in evaluate_def, but with an additional
    continuation argument. make the state argument explicit.
  - whenever there's a recursive call, make it a tail call and store anything
    required for the remainder on top of the given continuation
  - whenever there's a return (or raise), call an "apply" function (these are
    additional compared to evaluate_def) that applies the continuation to the
    result (there will be a kind of apply function for each kind of result)
  - applying a continuation to a result that it doesn't expect is an error: find
    the results it could expect by looking at where it was created
*)



Datatype:
  eval_continuation
  = ReturnK eval_continuation
  | AssertK assert_reason eval_continuation
  | RaiseK eval_continuation
  | LogK nsid eval_continuation
  | PopK eval_continuation
  | AppendK expr eval_continuation
  | AppendK1 base_target_value eval_continuation
  | AnnAssignK identifier type_value eval_continuation
  | AssignK expr eval_continuation
  | AssignK1 assignment_value eval_continuation
  | AugAssignK type binop expr eval_continuation
  | AugAssignK1 type base_target_value binop eval_continuation
  | IfK (stmt list) (stmt list) eval_continuation
  | IfK1 toplevel_value (stmt list) (stmt list) eval_continuation
  | IfK2 eval_continuation
  | ForK identifier type_value num (stmt list) eval_continuation
  | ForK1 type_value num (stmt list) (value list) eval_continuation
  | ExprK eval_continuation
  | StmtsK (stmt list) eval_continuation
  | ArrayK type eval_continuation
  | RangeK1 expr eval_continuation
  | RangeK2 value eval_continuation
  | BaseTargetK eval_continuation
  | TupleTargetK eval_continuation
  | TargetsK (assignment_target list) eval_continuation
  | TargetsK1 assignment_value eval_continuation
  | AttributeTargetK identifier eval_continuation
  | SubscriptTargetK expr eval_continuation
  | SubscriptTargetK1 base_target_value eval_continuation
  | IfExpK expr expr eval_continuation
  | StructLitK (identifier list) eval_continuation
  | SubscriptK type expr eval_continuation
  | SubscriptK1 type toplevel_value eval_continuation
  | AttributeK identifier eval_continuation
  | BuiltinK type builtin eval_continuation
  | LenK eval_continuation
  | TypeBuiltinK type_builtin type eval_continuation
  | CallSendK eval_continuation
  | ExtCallK bool identifier (type list) type (expr option) eval_continuation
  (* Chain interaction builtin continuations *)
  | RawCallK type raw_call_flags eval_continuation
  | RawLogK eval_continuation
  | RawRevertK eval_continuation
  | SelfDestructK eval_continuation
  | CreateK (type list) create_kind bool bool eval_continuation
  | IntCallK (num |-> type_args) (num option # identifier) ((identifier # type) list) (expr list) type (stmt list) bool function_mutability eval_continuation
  | IntCallK1 (num |-> type_args) (num option # identifier) ((identifier # type) list) (value list) (scope list) type (stmt list) bool function_mutability eval_continuation
  | IntCallK2 (scope list) type_value bool bool eval_continuation
  | ExprsK (expr list) eval_continuation
  | ExprsK1 value eval_continuation
  | DoneK
End

Datatype:
  apply_base_continuation
  = Apply
  | ApplyExc exception
  | ApplyTarget assignment_value
  | ApplyTargets (assignment_value list)
  | ApplyBaseTarget base_target_value
  | ApplyTv toplevel_value
  | ApplyVal value
  | ApplyVals (value list)
End

Datatype:
  apply_continuation
  = AK evaluation_context apply_base_continuation
       evaluation_state eval_continuation
End

Definition liftk_def:
  liftk cx a (INL x, st) = AK cx (a x) (st:evaluation_state) ∧
  liftk cx a (INR (ex:exception), st) = AK cx (ApplyExc ex) st
End

val liftk1 = oneline liftk_def;

Definition no_recursion_def:
  no_recursion (src_fn : num option # identifier) stk ⇔ ¬MEM src_fn stk
End

val () = cv_auto_trans no_recursion_def;

Definition eval_base_target_cps_def:
  eval_base_target_cps cx (NameTarget id) st k =
    (let r = do
        sc <- get_scopes;
        n <<- string_to_num id;
        type_check (IS_SOME (lookup_scopes n sc)) "NameTarget not in scope";
        return $ (ScopedVar id, []) od st in
     liftk cx ApplyBaseTarget r k) ∧
  eval_base_target_cps cx (TopLevelNameTarget (src_id_opt, id)) st k =
    (let r = do
        n <<- string_to_num id;
        ts <- lift_option_type
                (get_module_code cx src_id_opt)
                "TopLevelNameTarget get_module_code";
        if is_immutable_decl n ts then return $ (ImmutableVar src_id_opt id, [])
        else return $ (TopLevelVar src_id_opt id, []) od st in
     liftk cx ApplyBaseTarget r k) ∧
  eval_base_target_cps cx (AttributeTarget t id) st k =
    eval_base_target_cps cx t st (AttributeTargetK id k) ∧
  eval_base_target_cps cx (SubscriptTarget t e) st k =
    eval_base_target_cps cx t st (SubscriptTargetK e k)
End

val () = eval_base_target_cps_def
  |> SRULE [bind_def, ignore_bind_def,
            LET_RATOR, COND_RATOR, lift_option_def, lift_option_type_def, lift_option_type_def,
            prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, liftk1]
  |> cv_auto_trans;

Definition eval_expr_cps_def:
  eval_expr_cps cx1 (Name _ id) st k =
    liftk cx1 ApplyTv
      (do env <- get_scopes;
          n <<- string_to_num id;
          v <- lift_option_type (lookup_scopes_val n env) "Name not in scope";
          return $ Value v od st) k ∧
  eval_expr_cps cx2 (TopLevelName _ (src_id_opt, id)) st k =
    liftk cx2 ApplyTv (lookup_global cx2 src_id_opt (string_to_num id) st) k ∧
  eval_expr_cps cx2 (FlagMember _ nsid mid) st k =
    liftk cx2 ApplyTv (lookup_flag_mem cx2 nsid mid st) k ∧
  eval_expr_cps cx3 (IfExp _ e1 e2 e3) st k =
    eval_expr_cps cx3 e1 st (IfExpK e2 e3 k) ∧
  eval_expr_cps cx4 (Literal _ l) st k =
    AK cx4 (ApplyTv (Value $ evaluate_literal l)) st k ∧
  eval_expr_cps cx5 (StructLit _ (src_id_opt, id) kes) st k =
    eval_exprs_cps cx5 (MAP SND kes) st (StructLitK (MAP FST kes) k) ∧
  eval_expr_cps cx6 (Subscript _ e1 e2) st k =
    eval_expr_cps cx6 e1 st (SubscriptK (expr_type e1) e2 k) ∧
  eval_expr_cps cx7 (Attribute _ e id) st k =
    eval_expr_cps cx7 e st (AttributeK id k) ∧
  eval_expr_cps cx8 (Builtin ty bt es) st k =
    (case type_check (builtin_args_length_ok bt (LENGTH es)) "Builtin args" st of
       (INR ex, st) => AK cx8 (ApplyExc ex) st k
     | (INL (), st) => if bt = Len then eval_expr_cps cx8 (HD es) st (LenK k)
                       else eval_exprs_cps cx8 es st (BuiltinK ty bt k)) ∧
  eval_expr_cps cx8 (Pop _ bt) st k =
    eval_base_target_cps cx8 bt st (PopK k) ∧
  eval_expr_cps cx8 (TypeBuiltin _ tb typ es) st k =
    (case type_check (type_builtin_args_length_ok tb (LENGTH es))
            "TypeBuiltin args" st of
        (INR ex, st) => AK cx8 (ApplyExc ex) st k
      | (INL tv, st) => eval_exprs_cps cx8 es st (TypeBuiltinK tb typ k)) ∧
  eval_expr_cps cx9 (Call _ Send es _) st k =
    (case type_check (LENGTH es = 2) "Send args" st of
       (INR ex, st) => AK cx9 (ApplyExc ex) st k
     | (INL (), st) => eval_exprs_cps cx9 es st (CallSendK k)) ∧
  eval_expr_cps cx10 (Call _ (ExtCall is_static (func_name, arg_types, ret_type)) es drv) st k =
    eval_exprs_cps cx10 es st (ExtCallK is_static func_name arg_types ret_type drv k) ∧
  (* Chain interaction builtins *)
  eval_expr_cps cx10 (Call ty (RawCallTarget flags) es _) st k =
    eval_exprs_cps cx10 es st (RawCallK ty flags k) ∧
  eval_expr_cps cx10 (Call _ RawLog es _) st k =
    eval_exprs_cps cx10 es st (RawLogK k) ∧
  eval_expr_cps cx10 (Call _ RawRevert es _) st k =
    eval_exprs_cps cx10 es st (RawRevertK k) ∧
  eval_expr_cps cx10 (Call _ SelfDestructTarget es _) st k =
    eval_exprs_cps cx10 es st (SelfDestructK k) ∧
  eval_expr_cps cx10 (Call ty (CreateTarget kind has_salt rof) es _) st k =
    eval_exprs_cps cx10 es st (CreateK (MAP expr_type es) kind has_salt rof k) ∧
  eval_expr_cps cx10 (Call _ (IntCall (ns, fn)) es _) st k =
    (case do
      type_check (no_recursion (ns, fn) cx10.stk) "recursion";
      ts <- lift_option_type (get_module_code cx10 ns) "IntCall get_module_code";
      tup <- lift_option_type (lookup_callable_function cx10.in_deploy fn ts) "IntCall lookup_function";
      (* tup = (mut, nr, args, dflts, ret, body) *)
      mut <<- FST tup; stup <<- SND tup; nr <<- FST stup; stup2 <<- SND stup;
      args <<- FST stup2; sstup <<- SND stup2;
      dflts <<- FST sstup; sstup2 <<- SND sstup;
      ret <<- FST $ sstup2; body <<- SND $ sstup2;
      type_check (LENGTH es ≤ LENGTH args ∧
           LENGTH args - LENGTH es ≤ LENGTH dflts) "IntCall args length";
      (* Use combined type env (may reference types from other modules) *)
      all_tenv <<- get_tenv cx10;
      return (all_tenv, args, dflts, ret, body, nr, mut) od st
     of (INR ex, st) => AK cx10 (ApplyExc ex) st k
      | (INL (all_tenv, args, dflts, ret, body, nr, mut), st) =>
          eval_exprs_cps cx10 es st (IntCallK all_tenv (ns, fn) args dflts ret body nr mut k)) ∧
  eval_exprs_cps cx11 [] st k = AK cx11 (ApplyVals []) st k ∧
  eval_exprs_cps cx12 (e::es) st k =
    eval_expr_cps cx12 e st (ExprsK es k)
Termination
  WF_REL_TAC ‘measure (λx. case x of
    | INL (cx,e,st,k) => expr_size e
    | INR (cx,es,st,k) => list_size expr_size es)’
  \\ rw[expr1_size_map, SUM_MAP_expr2_size, list_size_SUM_MAP, MAP_MAP_o,
        list_size_pair_size_map, builtin_args_length_ok_def, check_def, type_check_def,
        assert_def, LENGTH_EQ_NUM_compute] \\ rw[]
End

val eval_expr_cps_pre_def = eval_expr_cps_def
   |> SRULE
        [liftk1, bind_def, ignore_bind_def,
         LET_RATOR, option_CASE_rator,
         sum_CASE_rator, prod_CASE_rator, lift_option_def]
   |> cv_auto_trans_pre "eval_expr_cps_pre eval_exprs_cps_pre";

Theorem eval_expr_cps_pre[cv_pre]:
  (∀a b c d. eval_expr_cps_pre a b c d) ∧
  (∀x y z w. eval_exprs_cps_pre x y z w)
Proof
  ho_match_mp_tac eval_expr_cps_ind \\ rw[]
  \\ rw[Once eval_expr_cps_pre_def]
  \\ gvs[CaseEq"prod", CaseEq"sum", CaseEq"option", raise_def, check_def, type_check_def,
         assert_def, builtin_args_length_ok_def, LENGTH_EQ_NUM_compute]
  \\ first_x_assum irule
  \\ gvs[bind_def, ignore_bind_def, lift_option_def, lift_option_type_def, assert_def]
QED

Definition eval_iterator_cps_def:
  eval_iterator_cps cx (Array e) st k =
    eval_expr_cps cx e st (ArrayK (expr_type e) k) ∧
  eval_iterator_cps cx (Range e1 e2) st k =
    eval_expr_cps cx e1 st (RangeK1 e2 k)
End

val () = cv_auto_trans eval_iterator_cps_def;

Definition eval_target_cps_def:
  eval_target_cps cx (BaseTarget t) st k =
    eval_base_target_cps cx t st (BaseTargetK k) ∧
  eval_target_cps cx (TupleTarget gs) st k =
    eval_targets_cps cx gs st (TupleTargetK k) ∧
  eval_targets_cps cx [] st k = AK cx (ApplyTargets []) st k ∧
  eval_targets_cps cx (g::gs) st k =
    eval_target_cps cx g st (TargetsK gs k)
End

val () = eval_target_cps_def |> cv_auto_trans;

Definition eval_stmt_cps_def:
  eval_stmt_cps cx Pass st k = AK cx Apply st k ∧
  eval_stmt_cps cx Continue st k = AK cx (ApplyExc ContinueException) st k ∧
  eval_stmt_cps cx Break st k = AK cx (ApplyExc BreakException) st k ∧
  eval_stmt_cps cx (Return NONE) st k = AK cx (ApplyExc (ReturnException NoneV)) st k ∧
  eval_stmt_cps cx (Return (SOME e)) st k = eval_expr_cps cx e st (ReturnK k) ∧
  eval_stmt_cps cx (Raise RaiseBare) st k =
    AK cx (ApplyExc (AssertException "")) st k ∧
  eval_stmt_cps cx (Raise RaiseUnreachable) st k =
    AK cx (ApplyExc (AssertException "UNREACHABLE")) st k ∧
  eval_stmt_cps cx (Raise (RaiseReason se)) st k =
    eval_expr_cps cx se st (RaiseK k) ∧
  eval_stmt_cps cx (Assert e reason) st k =
    eval_expr_cps cx e st (AssertK reason k) ∧
  eval_stmt_cps cx (Log id es) st k = eval_exprs_cps cx es st (LogK id k) ∧
  eval_stmt_cps cx (AnnAssign id typ e) st k =
    (case evaluate_type (get_tenv cx) typ of
       NONE => AK cx (ApplyExc (Error (TypeError "AnnAssign evaluate_type"))) st k
     | SOME tyv => eval_expr_cps cx e st (AnnAssignK id tyv k)) ∧
  eval_stmt_cps cx (Append t e) st k =
    eval_base_target_cps cx t st (AppendK e k) ∧
  eval_stmt_cps cx (Assign g e) st k =
    eval_target_cps cx g st (AssignK e k) ∧
  eval_stmt_cps cx (AugAssign ty t bop e) st k =
    eval_base_target_cps cx t st (AugAssignK ty bop e k) ∧
  eval_stmt_cps cx (If e ss1 ss2) st k =
    eval_expr_cps cx e st (IfK ss1 ss2 k) ∧
  eval_stmt_cps cx (For id typ it n body) st k =
    (case evaluate_type (get_tenv cx) typ of
       NONE => AK cx (ApplyExc (Error (TypeError "For evaluate_type"))) st k
     | SOME tyv => eval_iterator_cps cx it st (ForK id tyv n body k)) ∧
  eval_stmt_cps cx (Expr e) st k =
    eval_expr_cps cx e st (ExprK k)
End

val () = cv_auto_trans eval_stmt_cps_def;

Definition eval_stmts_cps_def:
  eval_stmts_cps cx [] st k = AK cx Apply st k ∧
  eval_stmts_cps cx (s::ss) st k =
    eval_stmt_cps cx s st (StmtsK ss k)
End

val () = cv_auto_trans eval_stmts_cps_def;

Definition eval_for_cps_def:
  eval_for_cps cx tyv nm body [] st k = AK cx Apply st k ∧
  eval_for_cps cx tyv nm body (v::vs) st k =
  (case push_scope_with_var nm tyv v st of
        (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => eval_stmts_cps cx body st (ForK1 tyv nm body vs k))
End

val () = cv_auto_trans eval_for_cps_def;

Definition apply_def:
  apply cx st (StmtsK ss k) =
    eval_stmts_cps cx ss st k ∧
  apply cx st (ForK1 tyv nm body vs k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => eval_for_cps cx tyv nm body vs st k) ∧
  apply cx st (IfK2 k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => AK cx Apply st k) ∧
  apply cx st (IfK1 (Value (BoolV b)) ss1 ss2 k) =
    eval_stmts_cps cx (if b then ss1 else ss2) st (IfK2 k) ∧
  apply cx st (IfK1 (Value _) ss1 ss2 k) =
    AK cx (ApplyExc $ Error (TypeError "not BoolV")) st (IfK2 k) ∧
  apply cx st (IfK1 _ ss1 ss2 k) =
    AK cx (ApplyExc $ Error (TypeError "not Value")) st (IfK2 k) ∧
  apply cx st (IntCallK2 prev rtv nr is_view k) =
    liftk (cx with stk updated_by TL) (ApplyTv o Value)
      (do pop_function prev;
          (* Release reentrancy lock if nonreentrant and not view *)
          (if nr ∧ ¬is_view then
             case cx.nonreentrant_slot of
             | NONE => return ()
             | SOME slot => release_nonreentrant_lock cx.txn.target slot
           else return ());
          crv <- lift_option_type (safe_cast rtv NoneV) "IntCall cast ret";
          return crv od st) k ∧
  apply cx st DoneK = AK cx Apply st DoneK ∧
  apply cx st _ = AK cx (ApplyExc $ Error (TypeError "apply k")) st DoneK
End

val () = apply_def
  |> SRULE [liftk1, ignore_bind_def, bind_def, prod_CASE_rator, sum_CASE_rator,
            COND_RATOR, option_CASE_rator]
  |> cv_auto_trans;

Definition apply_exc_def:
  apply_exc cx ex st (ReturnK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssertK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RaiseK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (LogK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AppendK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AppendK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AnnAssignK _ _ k) = AK cx (ApplyExc ex) st k ∧  (* id, tyv unused *)
  apply_exc cx ex st (AssignK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AssignK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AugAssignK1 _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK1 _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfK2 k) =
    (case pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL (), st) => AK cx (ApplyExc ex) st k) ∧
  apply_exc cx ex st (ForK _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ForK1 tyv nm body vs k) =
    (case finally (handle_loop_exception ex) pop_scope st
     of (INR ex, st) => AK cx (ApplyExc ex) st k
      | (INL broke, st) =>
          if broke then AK cx Apply st k
          else eval_for_cps cx tyv nm body vs st k) ∧
  apply_exc cx ex st (ExprK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (StmtsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ArrayK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RangeK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RangeK2 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BaseTargetK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TupleTargetK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TargetsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TargetsK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AttributeTargetK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptTargetK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptTargetK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IfExpK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (StructLitK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SubscriptK1 _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (AttributeK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (PopK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (BuiltinK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (LenK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (TypeBuiltinK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (CallSendK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExtCallK _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawCallK _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawLogK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (RawRevertK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (SelfDestructK k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (CreateK _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK _ _ _ _ _ _ _ _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (IntCallK1 _ _ _ _ prev _ _ _ _ k) =
    liftk (cx with stk updated_by TL) (K (ApplyExc ex)) (set_scopes prev st) k ∧
  apply_exc cx ex st (IntCallK2 prev rtv nr is_view k) =
    liftk (cx with stk updated_by TL) (ApplyTv o Value)
      (do rv <- finally (handle_function ex)
            (do pop_function prev;
                (* Release reentrancy lock if nonreentrant and not view *)
                if nr ∧ ¬is_view then
                  case cx.nonreentrant_slot of
                  | NONE => return ()
                  | SOME slot => release_nonreentrant_lock cx.txn.target slot
                else return ()
             od);
          crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
	  return crv od st)
      k ∧
  apply_exc cx ex st (ExprsK _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st (ExprsK1 _ k) = AK cx (ApplyExc ex) st k ∧
  apply_exc cx ex st DoneK = AK cx (ApplyExc ex) st DoneK
End

val () = apply_exc_def
  |> SRULE [finally_def, bind_def, ignore_bind_def,
            liftk1, prod_CASE_rator, sum_CASE_rator,
            COND_RATOR, option_CASE_rator]
  |> cv_auto_trans;

Definition apply_targets_def:
  apply_targets cx gvs st (TargetsK1 gv k) =
    AK cx (ApplyTargets (gv::gvs)) st k ∧
  apply_targets cx gvs st (TupleTargetK k) =
      AK cx (ApplyTarget (TupleTargetV gvs)) st k ∧
  apply_targets cx _ st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_targets k")) st DoneK
End

val () = cv_auto_trans apply_targets_def;

Definition apply_base_target_def:
  apply_base_target cx btv st (BaseTargetK k) =
    AK cx (ApplyTarget (BaseTargetV (FST btv) (SND btv))) st k ∧
  apply_base_target cx btv st (AttributeTargetK id k) =
    AK cx (ApplyBaseTarget (FST btv, AttrSubscript id :: SND btv)) st k ∧
  apply_base_target cx btv st (SubscriptTargetK e k) =
    eval_expr_cps cx e st (SubscriptTargetK1 btv k) ∧
  apply_base_target cx btv st (AugAssignK ty bop e k) =
    eval_expr_cps cx e st (AugAssignK1 ty btv bop k) ∧
  apply_base_target cx btv st (AppendK e k) =
    eval_expr_cps cx e st (AppendK1 btv k) ∧
  apply_base_target cx btv st (PopK k) =
    liftk cx ApplyTv (do
      sbs <<- SND btv;
      popped <- assign_target cx (BaseTargetV (FST btv) sbs) PopOp;
      v <- lift_option_type popped "Pop returned NONE";
      return $ Value v od st) k ∧
  apply_base_target cx btv st DoneK = AK cx (ApplyBaseTarget btv) st DoneK ∧
  apply_base_target cx _ st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_base_target k")) st DoneK
End

val () = apply_base_target_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator,
            LET_RATOR, bind_def, ignore_bind_def]
  |> cv_auto_trans;

Definition apply_target_def:
  apply_target cx gv st (AssignK e k) =
    eval_expr_cps cx e st (AssignK1 gv k) ∧
  apply_target cx gv st (TargetsK gs k) =
    eval_targets_cps cx gs st (TargetsK1 gv k) ∧
  apply_target cx gv st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_target k")) st DoneK
End

val () = cv_auto_trans apply_target_def;

Definition apply_tv_def:
  apply_tv cx tv st (SubscriptK arr_typ e k) =
    eval_expr_cps cx e st (SubscriptK1 arr_typ tv k) ∧
  apply_tv cx tv st (IfK ss1 ss2 k) =
    liftk cx (K Apply) (push_scope st) (IfK1 tv ss1 ss2 k) ∧
  apply_tv cx tv st (LenK k) =
    liftk cx ApplyTv (do
      len <- toplevel_array_length cx tv;
      return $ Value $ IntV (&len)
    od st) k ∧
  apply_tv cx tv st (ExprK k) =
    (case type_check (¬is_HashMapRef tv) "Expr HashMapRef" st of
       (INR ex, st) => apply_exc cx ex st k
     | (INL (), st) => apply cx st k) ∧
  apply_tv cx tv st (ReturnK k) =
    liftk cx ApplyVal (materialise cx tv st) (ReturnK k) ∧
  apply_tv cx tv st (AnnAssignK id tyv k) =
    liftk cx ApplyVal (materialise cx tv st) (AnnAssignK id tyv k) ∧
  apply_tv cx tv st (AppendK1 btv k) =
    liftk cx ApplyVal (materialise cx tv st) (AppendK1 btv k) ∧
  apply_tv cx tv st (AssignK1 gv k) =
    liftk cx ApplyVal (materialise cx tv st) (AssignK1 gv k) ∧
  apply_tv cx tv st (ArrayK arr_typ k) =
    liftk cx ApplyVal (materialise cx tv st) (ArrayK arr_typ k) ∧
  apply_tv cx tv st (ExprsK es k) =
    liftk cx ApplyVal (materialise cx tv st) (ExprsK es k) ∧
  apply_tv cx tv st DoneK = AK cx (ApplyTv tv) st DoneK ∧
  apply_tv cx tv st k =
    liftk cx ApplyVal (get_Value tv st) k
End

val () = apply_tv_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator]
  |> cv_auto_trans;

(* ===== apply_val helpers: extracted complex do-block clauses so each
        translates cheaply on its own (cv_trans speed) ===== *)
Definition apply_val_array_def:
  apply_val_array cx arr_typ v st k =
    (case evaluate_type (get_tenv cx) arr_typ of
     | SOME arr_tv =>
         liftk cx ApplyVals
           (lift_option_type (extract_elements arr_tv v) "For not ArrayV" st) k
     | NONE => AK cx (ApplyExc (Error (TypeError "For array type"))) st k)
End
val () = apply_val_array_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
            lift_option_type_def]
  |> cv_auto_trans;
Definition apply_val_range2_def:
  apply_val_range2 cx v1 v2 st k =
    (case do rl <- lift_sum $ get_range_limits v1 v2;
             n1 <<- FST rl; n2 <<- SND rl;
             return $ GENLIST (λn. IntV (n1 + &n)) n2
     od st
       of (INR ex, st) => apply_exc cx ex st k
        | (INL vs, st) => AK cx (ApplyVals vs) st k)
End
val () = apply_val_range2_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
            LET_RATOR, lift_sum_def, bind_def, ignore_bind_def]
  |> cv_auto_trans;
Definition apply_val_subscript_def:
  apply_val_subscript cx arr_typ tv1 v2 st k =
    liftk cx ApplyTv (do
      tenv <<- get_tenv cx;
      arr_tv <- lift_option_type (evaluate_type tenv arr_typ)
                  "Subscript array type";
      check_array_bounds cx tv1 v2;
      res <- lift_sum (evaluate_subscript tenv arr_tv tv1 v2);
       case res of INL v => return v | INR (is_transient, slot, tv) => do
         v <- read_storage_slot cx is_transient slot tv;
         return $ Value v
       od
    od st) k
End
val () = apply_val_subscript_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator, option_CASE_rator,
            LET_RATOR, lift_option_type_def, lift_sum_def, bind_def, ignore_bind_def]
  |> cv_auto_trans;
Definition apply_val_def:
  apply_val cx v st (ReturnK k) = apply_exc cx (ReturnException v) st k ∧
  apply_val cx v st (AssertK r k) =
    (case v of
       BoolV T => apply cx st k
     | BoolV F =>
         (case r of
            AssertBare => apply_exc cx (AssertException "") st k
          | AssertUnreachable => apply_exc cx (AssertException "UNREACHABLE") st k
          | AssertReason se => eval_expr_cps cx se st (RaiseK k))
     | _ => apply_exc cx (Error (TypeError "not BoolV")) st k) ∧
  apply_val cx v st (RaiseK k) =
    (case v of
       StringV str => apply_exc cx (AssertException str) st k
     | _ => apply_exc cx (Error (TypeError "not StringV")) st k) ∧
  apply_val cx v st (AnnAssignK id tyv k) =
    liftk cx (K Apply) (new_variable id tyv v st) k ∧
  apply_val cx v st (AssignK1 gv k) =
    liftk cx (K Apply) (assign_target cx gv (Replace v) st) k ∧
  apply_val cx v st (AugAssignK1 ty (loc, sbs) bop k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (Update ty bop v) st) k ∧
  apply_val cx v st (AppendK1 (loc, sbs) k) =
    liftk cx (K Apply) (assign_target cx (BaseTargetV loc sbs) (AppendOp v) st) k ∧
  apply_val cx v st (ArrayK arr_typ k) = apply_val_array cx arr_typ v st k ∧
  apply_val cx v st (RangeK1 e k) = eval_expr_cps cx e st (RangeK2 v k) ∧
  apply_val cx v2 st (RangeK2 v1 k) = apply_val_range2 cx v1 v2 st k ∧
  apply_val cx v st (SubscriptTargetK1 (loc, sbs) k) =
    AK cx (ApplyBaseTarget (loc, ValueSubscript v :: sbs)) st k ∧
  apply_val cx v st (IfExpK e2 e3 k) =
    (case v of
       BoolV T => eval_expr_cps cx e2 st k
     | BoolV F => eval_expr_cps cx e3 st k
     | _ => apply_exc cx (Error (TypeError "not BoolV")) st k) ∧
  apply_val cx v2 st (SubscriptK1 arr_typ tv1 k) =
    apply_val_subscript cx arr_typ tv1 v2 st k ∧
  apply_val cx v st (AttributeK id k) =
    liftk cx (ApplyTv o Value) (lift_sum (evaluate_attribute v id) st) k ∧
  apply_val cx v st (ExprsK es k) =
    eval_exprs_cps cx es st (ExprsK1 v k) ∧
  apply_val cx v st DoneK = AK cx (ApplyVal v) st DoneK ∧
  apply_val cx v st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_val k")) st DoneK
End

val () = apply_val_def
  |> SRULE [liftk1, prod_CASE_rator, sum_CASE_rator,
            option_CASE_rator, lift_option_def, lift_option_type_def, lift_sum_def, lift_sum_runtime_def,
            LET_RATOR, bind_def, ignore_bind_def]
  |> cv_auto_trans;

Definition apply_vals_def:
  apply_vals cx vs st (ExprsK1 v k) =
    apply_vals cx (v::vs) st k ∧
  apply_vals cx vs st (ForK id tyv n body k) =
    (case do check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long";
             return vs od st
     of (INR ex, st) => apply_exc cx ex st k
      | (INL vs, st) => eval_for_cps cx tyv (string_to_num id) body vs st k) ∧
  apply_vals cx vs st (StructLitK ks k) =
    apply_tv cx (Value $ StructV (ZIP (ks, vs))) st k ∧
  apply_vals cx vs st (BuiltinK ty bt k) =
    liftk cx ApplyTv (do
      acc <- get_accounts;
      v <- lift_sum $ evaluate_builtin cx acc ty bt vs;
      return $ Value v
    od st) k ∧
  apply_vals cx vs st (TypeBuiltinK tb typ k) =
    liftk cx ApplyTv (do
      v <- lift_sum $ evaluate_type_builtin cx tb typ vs;
      return $ Value v
    od st) k ∧
  apply_vals cx vs st (LogK id k) =
    liftk cx (K Apply) (do
      event <- lift_option
        (encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs)
        "Log encode event";
      push_log event
    od st) k ∧
  apply_vals cx vs st (CallSendK k) =
    liftk cx ApplyTv (do
      type_check (LENGTH vs = 2) "CallSendK nargs";
      toAddr <- lift_option_type (dest_AddressV $ EL 0 vs) "Send not AddressV";
      amount <- lift_option_type (dest_NumV $ EL 1 vs) "Send not NumV";
      transfer_value cx.txn.target toAddr amount;
      return $ Value NoneV
    od st) k ∧
  apply_vals cx vs st (ExtCallK is_static func_name arg_types ret_type drv k) =
    (case do
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
        return (INL (THE drv))
      else do
        ret_val <- lift_sum_runtime (evaluate_abi_decode_return tenv ret_type returnData);
        return (INR (Value ret_val))
      od
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL (INL e), st) => eval_expr_cps cx e st k
     | (INL (INR tv), st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (IntCallK all_tenv src_fn args dflts ret body nr mut k) =
    (case do
      prev <- get_scopes;
      set_scopes [FEMPTY];
      return prev
    od st of
     | (INR ex, st) => apply_exc cx ex st k
     | (INL prev, st) =>
        eval_exprs_cps (cx with stk updated_by CONS src_fn)
          (DROP (LENGTH dflts - (LENGTH args - LENGTH vs)) dflts) st
          (IntCallK1 all_tenv src_fn args vs prev ret body nr mut k)) ∧
  apply_vals cx dflt_vs st (IntCallK1 all_tenv src_fn args vs prev ret body nr mut k) =
    (case do
      set_scopes prev;
      env <- lift_option_type (bind_arguments all_tenv args (vs ++ dflt_vs)) "IntCall bind_arguments";
      rtv <- lift_option_type (evaluate_type all_tenv ret) "IntCall eval ret";
      is_view <<- (mut = View ∨ mut = Pure);
      (* Acquire lock BEFORE push_function so scopes are unmodified on failure *)
      (if nr then
         case cx.nonreentrant_slot of
         | NONE => raise (Error (TypeError "nonreentrant slot missing"))
         | SOME slot => acquire_nonreentrant_lock cx.txn.target slot is_view
       else return ());
      cxf <- push_function src_fn env (cx with stk updated_by TL);
      return (prev, cxf, body, rtv, is_view) od st
     of (INR ex, st) => apply_exc (cx with stk updated_by TL) ex st k
      | (INL (prev, cxf, body, rtv, is_view), st) =>
          eval_stmts_cps cxf body st (IntCallK2 prev rtv nr is_view k)) ∧
  (* ===== Chain interaction builtins ===== *)
  apply_vals cx vs st (RawCallK ty flags k) =
    (case do
      type_check (LENGTH vs = 3) "raw_call args";
      target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
      calldata <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
      amount <- lift_option_type (dest_NumV (EL 2 vs)) "raw_call value";
      value_opt <<- if flags.rcf_is_static then NONE else SOME amount;
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
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (RawLogK k) =
    (case do
      type_check (LENGTH vs = 2) "raw_log args";
      topics <- lift_option_type (dest_ArrayV (EL 0 vs)) "raw_log topics";
      data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_log data";
      topic_vals <<- (case topics of
         TupleV tvs => tvs | DynArrayV tvs => tvs | _ => []);
      type_check (LENGTH topic_vals ≤ 4) "raw_log too many topics";
      push_log (encode_raw_event_values cx.txn.target topic_vals data);
      return $ Value NoneV
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (RawRevertK k) =
    (case do
      type_check (LENGTH vs = 1) "raw_revert args";
      raise $ Error $ RuntimeError "raw_revert"
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (SelfDestructK k) =
    (case do
      type_check (LENGTH vs = 1) "selfdestruct args";
      target_addr <- lift_option_type (dest_AddressV (EL 0 vs)) "selfdestruct target";
      accounts <- get_accounts;
      self_acct <<- lookup_account cx.txn.target accounts;
      balance <<- self_acct.balance;
      transfer_value cx.txn.target target_addr balance;
      return $ Value NoneV
    od st
    of (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st (CreateK arg_tys kind has_salt rof k) =
    (case eval_create cx kind has_salt rof arg_tys vs st of
       (INR ex, st) => AK cx (ApplyExc ex) st k
     | (INL tv, st) => AK cx (ApplyTv tv) st k) ∧
  apply_vals cx vs st DoneK = AK cx (ApplyVals vs) st DoneK ∧
  apply_vals cx vs st _ =
    AK cx (ApplyExc $ Error (TypeError "apply_vals k")) st DoneK
End

Triviality LET4_UNCURRY:
  (let (x,y,z,w) = M in N x y z w) =
     let p = M; x = FST p; p = SND p; y = FST p; p = SND p;
         z = FST p; w = SND p in N x y z w
Proof
  rw[UNCURRY]
QED

Triviality LET5_UNCURRY:
  (let (x,y,z,w,v) = M in N x y z w v) =
     let p = M; x = FST p; p = SND p; y = FST p; p = SND p;
         z = FST p; p = SND p; w = FST p; v = SND p in N x y z w v
Proof
  rw[UNCURRY]
QED

val apply_vals_pre_def = apply_vals_def
  |> SRULE [liftk1, bind_def, ignore_bind_def, lift_option_def, lift_option_type_def, lift_option_type_def,
            lift_sum_def, lift_sum_runtime_def, prod_CASE_rator, LET_RATOR, LET4_UNCURRY, LET5_UNCURRY,
            UNCURRY, sum_CASE_rator, option_CASE_rator, COND_RATOR]
  |> cv_auto_trans_pre "apply_vals_pre";

Theorem apply_vals_pre[cv_pre]:
  ∀a b c d. apply_vals_pre a b c d
Proof
  ho_match_mp_tac apply_vals_ind \\ rw[]
  \\ rw[Once apply_vals_pre_def]
  \\ gvs[check_def, type_check_def, assert_def]
  \\ strip_tac \\ gvs[]
QED

Definition nextk_def[simp]:
  nextk (AK _ _ _ k) = k
End

val () = cv_auto_trans nextk_def;

Definition stepk_def:
  stepk (AK cx ak st k) =
  case ak of
     | Apply => apply cx st k
     | ApplyExc ex => apply_exc cx ex st k
     | ApplyTarget gv => apply_target cx gv st k
     | ApplyTargets gvs => apply_targets cx gvs st k
     | ApplyBaseTarget bv => apply_base_target cx bv st k
     | ApplyTv tv => apply_tv cx tv st k
     | ApplyVal v => apply_val cx v st k
     | ApplyVals vs => apply_vals cx vs st k
End

val () = cv_auto_trans stepk_def;

Definition cont_def:
  cont ak = OWHILE (λak. nextk ak ≠ DoneK) stepk ak
End


Triviality eval_expr_cps_owhile_result:
  ∀cx e st q r k.
  eval_expr cx e st = (q,r) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case eval_expr cx e st of
        (INL tv,st1) => AK cx (ApplyTv tv) st1
      | (INR ex,st1) => AK cx (ApplyExc ex) st1) k) ⇒
  OWHILE (λak. nextk ak ≠ DoneK) stepk (eval_expr_cps cx e st k) =
  OWHILE (λak. nextk ak ≠ DoneK) stepk
    ((case q of
        INL tv => AK cx (ApplyTv tv) r
      | INR ex => AK cx (ApplyExc ex) r) k)
Proof
  rw[]
QED




Triviality apply_exc_owhile_eq:
  ∀cx ex st k.
  OWHILE (λak. nextk ak ≠ DoneK) stepk (AK cx (ApplyExc ex) st k) =
  (if k ≠ DoneK then OWHILE (λak. nextk ak ≠ DoneK) stepk (apply_exc cx ex st k)
   else SOME (AK cx (ApplyExc ex) st DoneK))
Proof
  rw[Once OWHILE_THM, stepk_def]
QED

Triviality context_stk_pop_push[simp]:
  ∀cx src_fn. (cx with stk updated_by TL ∘ CONS src_fn) = cx
Proof
  rw[evaluation_context_component_equality, o_DEF, FUN_EQ_THM]
QED













Theorem eval_cps_eq:
 (∀cx s st k.
     cont (eval_stmt_cps cx s st k) =
     cont ((
       case eval_stmt cx s st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx ss st k.
     cont (eval_stmts_cps cx ss st k) =
     cont ((
       case eval_stmts cx ss st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx it st k.
     cont (eval_iterator_cps cx it st k) =
     cont ((
       case eval_iterator cx it st
         of (INL vs, st1) => (AK cx (ApplyVals vs) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx g st k.
     cont (eval_target_cps cx g st k) =
     cont ((
       case eval_target cx g st
         of (INL gv, st1) => (AK cx (ApplyTarget gv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx gs st k.
     cont (eval_targets_cps cx gs st k) =
     cont ((
       case eval_targets cx gs st
         of (INL gvs, st1) => (AK cx (ApplyTargets gvs) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx bt st k.
     cont (eval_base_target_cps cx bt st k) =
     cont ((
       case eval_base_target cx bt st
         of (INL bv, st1) => (AK cx (ApplyBaseTarget bv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx tyv nm body vs st k.
     cont (eval_for_cps cx tyv nm body vs st k) =
     cont ((
       case eval_for cx tyv nm body vs st
         of (INL (), st1) => (AK cx Apply st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx e st k.
     cont (eval_expr_cps cx e st k) =
     cont ((
       case eval_expr cx e st
         of (INL tv, st1) => (AK cx (ApplyTv tv) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k)) ∧
  (∀cx es st k.
     cont (eval_exprs_cps cx es st k) =
     cont ((
       case eval_exprs cx es st
         of (INL vs, st1) => (AK cx (ApplyVals vs) st1)
          | (INR ex, st1) => (AK cx (ApplyExc ex) st1)
     ) k))
(* CPS-big-step equivalence *)
Proof
  ho_match_mp_tac evaluate_ind
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, return_def] (* Pass *)
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Continue *)
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Break *)
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Return NONE *)
  \\ conj_tac >- ( (* Return (SOME e) *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[cont_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[cont_def]
    \\ rw[Once OWHILE_THM, stepk_def]
    \\ rw[apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[raise_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, stepk_def, SimpRHS] \\ gvs[]
    \\ rw[apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Raise RaiseBare *)
  \\ conj_tac >- rw[eval_stmt_cps_def, evaluate_def, raise_def] (* Raise RaiseUnreachable *)
  \\ conj_tac >- ( (* Raise (RaiseReason se) *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ reverse (Cases_on `x`) \\ simp[get_Value_def, raise_def, return_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ simp[Once OWHILE_THM, stepk_def]
    \\ Cases_on`v`
    \\ simp[dest_StringV_def, lift_option_def, lift_option_type_def, return_def,
            raise_def, apply_val_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM] )
  \\ conj_tac >- ( (* Assert e AssertBare *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ qmatch_goalsub_rename_tac`get_Value tv`
    \\ reverse $ Cases_on`tv` \\ rw[return_def, raise_def, get_Value_def]
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    \\ simp[switch_BoolV_def] \\ rw[return_def, raise_def]
    >- ( (* BoolV T *)
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_def] )
    >- ( (* BoolV F *)
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
    \\ Cases_on`v` \\ gvs[] (* else: not BoolV *)
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* Assert e AssertUnreachable *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ qmatch_goalsub_rename_tac`get_Value tv`
    \\ reverse $ Cases_on`tv` \\ rw[return_def, raise_def, get_Value_def]
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    \\ simp[switch_BoolV_def] \\ rw[return_def, raise_def]
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_def] )
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
    \\ Cases_on`v` \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* Assert e (AssertReason se) *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ qmatch_goalsub_rename_tac`get_Value tv`
    \\ reverse $ Cases_on`tv` \\ rw[return_def, raise_def, get_Value_def]
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    >- (rw[switch_BoolV_def, raise_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    \\ simp[switch_BoolV_def] \\ rw[return_def, raise_def]
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_def] )
    >- ( (* BoolV F: eval reason expr *)
      rw[Once OWHILE_THM, stepk_def, apply_val_def]
      \\ first_x_assum drule \\ rw[cont_def]
      \\ rw[bind_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
      \\ qmatch_goalsub_rename_tac`get_Value stv`
      \\ reverse $ Cases_on`stv` \\ rw[get_Value_def, return_def, raise_def]
      >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def]
      \\ rename1`Value sv`
      \\ Cases_on`sv`
      \\ simp[dest_StringV_def, lift_option_def, lift_option_type_def,
              return_def, raise_def, apply_val_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
      \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
    \\ Cases_on`v` \\ gvs[]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def] \\ gvs[]
    \\ rw[apply_exc_def] \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* Log id es *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, liftk1])
  \\ conj_tac >- ( (* AnnAssign id typ e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    \\ gvs[lift_option_type_def, raise_def, return_def, cont_def]
    \\ Cases_on `eval_expr cx e st` \\ Cases_on `q` \\ gvs[]
    >- (rename1 `eval_expr cx e st = (INL tv,st1)`
        \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
        \\ Cases_on `materialise cx tv st1` \\ Cases_on `q` \\ gvs[]
        >- rw[Once OWHILE_THM, stepk_def, liftk1, apply_val_def]
        \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
  \\ conj_tac >- ( (* Append t e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def, UNCURRY, ignore_bind_def]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ qmatch_goalsub_rename_tac`AppendK1 btv`
    \\ Cases_on`btv`
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def] )
  \\ conj_tac >- ( (* Assign g e — target→expr→materialise→assign *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ rw[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_target_def]
    \\ gvs[cont_def]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1,
          ignore_bind_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def])
  \\ conj_tac >- ( (* AugAssign t bop e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ qmatch_goalsub_rename_tac`AugAssignK1 _ p` \\ Cases_on`p`
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ gvs[oneline get_Value_def, toplevel_value_CASE_rator,
           CaseEq"toplevel_value", CaseEq"prod", raise_def, return_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1, bind_def,
          ignore_bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def])
  \\ conj_tac >- ( (* If e ss1 ss2 *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def, ignore_bind_def, UNCURRY]
    \\ CASE_TAC \\ gs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_def]
    \\ first_x_assum drule \\ rw[]
    \\ first_x_assum drule \\ rw[]
    \\ gvs[switch_BoolV_def]
    \\ IF_CASES_TAC \\ gvs[]
    >- (
      rw[apply_def, finally_def, bind_def, ignore_bind_def]
      \\ gvs[push_scope_def, return_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- (
        rw[Once OWHILE_THM, stepk_def, apply_exc_def]
        \\ CASE_TAC \\ CASE_TAC \\ rw[raise_def] )
      \\ rw[Once OWHILE_THM, stepk_def, apply_def]
      \\ CASE_TAC \\ CASE_TAC )
    \\ IF_CASES_TAC \\ gvs[]
    >- (
      rw[apply_def, finally_def, bind_def, ignore_bind_def]
      \\ gvs[push_scope_def, return_def]
      \\ CASE_TAC \\ reverse CASE_TAC
      >- (
        rw[Once OWHILE_THM, stepk_def, apply_exc_def]
        \\ CASE_TAC \\ CASE_TAC \\ rw[raise_def] )
      \\ rw[Once OWHILE_THM, stepk_def, apply_def]
      \\ CASE_TAC \\ CASE_TAC )
    \\ qmatch_goalsub_abbrev_tac`TypeError str`
    \\ gvs[push_scope_def, return_def]
    \\ reverse $ Cases_on`x`
    \\ rw[apply_def, finally_def, raise_def, ignore_bind_def, bind_def]
    \\ gvs[]
    >- (
      rw[pop_scope_def, return_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def]
      \\ rw[pop_scope_def, return_def] )
    \\ Cases_on `v` \\ rw[apply_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[pop_scope_def, return_def] )
  \\ conj_tac >- ( (* For id typ it n body *)
    rw[eval_stmt_cps_def, evaluate_def, ignore_bind_def, bind_def,
       lift_option_type_def, return_def, raise_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[return_def, raise_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ gvs[return_def]
    \\ first_x_assum $ drule_then drule
    \\ rw[] )
  \\ conj_tac >- ( (* Expr e *)
    rw[eval_stmt_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ rw[ignore_bind_def, bind_def, return_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_val_def]
    \\ gvs[] \\ rw[apply_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- rw[eval_stmts_cps_def, evaluate_def, return_def] (* eval_stmts [] *)
  \\ conj_tac >- ( (* eval_stmts (s::ss) *)
    rw[eval_stmts_cps_def, evaluate_def, return_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_def]
    \\ gvs[]
    \\ first_x_assum drule \\ rw[])
  \\ conj_tac >- ( (* eval_iterator (Array e) *)
    rw[eval_iterator_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_val_array_def,
          liftk1, lift_option_type_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def, raise_def]
    \\ gvs[raise_def] )
  \\ conj_tac >- ( (* eval_iterator (Range e1 e2) *)
    rw[eval_iterator_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_val_range2_def, liftk1]
    \\ gvs[]
    \\ first_x_assum $ drule_then drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_val_range2_def, liftk1]
    \\ rw[bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] )
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, SimpRHS]
      \\ gvs[apply_exc_def]
      \\ rw[Once OWHILE_THM, stepk_def, apply_exc_def] ))
  \\ conj_tac >- ( (* eval_target (BaseTarget t) *)
    rw[eval_target_cps_def, evaluate_def, bind_def, return_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- ( (* eval_target (TupleTarget gs) *)
    rw[eval_target_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_targets_def, return_def] )
  \\ conj_tac >- rw[eval_target_cps_def, evaluate_def, bind_def, return_def] (* eval_targets [] *)
  \\ conj_tac >- ( (* eval_targets (g::gs) *)
    rw[eval_target_cps_def, evaluate_def, bind_def, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_target_def]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_targets_def] )
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, liftk1] (* eval_base_target (NameTarget id) *)
  \\ conj_tac >- rw[eval_base_target_cps_def, evaluate_def, liftk1] (* eval_base_target (TopLevelNameTarget ...) *)
  \\ conj_tac >- ( (* eval_base_target (AttributeTarget t id) *)
    rw[eval_base_target_cps_def, evaluate_def, bind_def, UNCURRY, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def] )
  \\ conj_tac >- ( (* eval_base_target (SubscriptTarget t e) *)
    rw[eval_base_target_cps_def, evaluate_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_base_target_def]
    \\ qmatch_asmsub_rename_tac`INL p` \\ PairCases_on`p`
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ qmatch_asmsub_rename_tac`get_Value tv`
    \\ Cases_on`tv` \\ gvs[get_Value_def, raise_def, return_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def] )
  \\ conj_tac >- rw[eval_for_cps_def, evaluate_def, return_def] (* eval_for [] *)
  \\ conj_tac >- ( (* eval_for (v::vs) *)
    rw[eval_for_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC \\ gvs[]
    \\ first_assum drule \\ simp_tac std_ss [] \\ disch_then kall_tac
    \\ rw[finally_def, try_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- (
      rw[Once OWHILE_THM, stepk_def, apply_exc_def, finally_def]
      \\ CASE_TAC \\ CASE_TAC
      \\ rw[ignore_bind_def, bind_def, return_def, raise_def]
      \\ CASE_TAC \\ CASE_TAC
      \\ rw[return_def]
      \\ last_x_assum drule \\ rw[]
      \\ last_x_assum drule \\ rw[]
      \\ gvs[finally_def, bind_def, try_def, CaseEq"prod", CaseEq"sum",
             PULL_EXISTS, ignore_bind_def, return_def, raise_def]
      \\ fsrw_tac[DNF_ss][]
      \\ last_x_assum drule \\ rw[])
    \\ rw[return_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def]
    \\ last_x_assum drule \\ rw[]
    \\ gvs[finally_def, bind_def, try_def, CaseEq"prod", CaseEq"sum",
           PULL_EXISTS, ignore_bind_def, return_def, raise_def]
    \\ fsrw_tac[DNF_ss][]
    \\ last_x_assum drule \\ rw[]
    \\ last_x_assum drule \\ rw[])
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1] (* eval_expr (Name id) *)
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1] (* eval_expr (TopLevelName ...) *)
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, liftk1] (* eval_expr (FlagMember ...) *)
  \\ conj_tac >- ( (* eval_expr (IfExp e1 e2 e3) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ first_x_assum drule
    \\ first_x_assum drule
    \\ rw[]
    \\ simp[switch_BoolV_def]
    >> simp[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ IF_CASES_TAC \\ gvs[return_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ IF_CASES_TAC \\ gvs[return_def]
    >- rw[Once OWHILE_THM, stepk_def, apply_val_def]
    \\ simp[raise_def]
    \\ Cases_on`x` \\ gvs[return_def]
    >- (
      Cases_on`v`
      \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def]
      \\ rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_exc_def]
      \\ gvs[]
      \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def] )
    \\ gvs[raise_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_exc_def] )
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def] (* eval_expr (Literal l) *)
  \\ conj_tac >- ( (* eval_expr (StructLit ...) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def, return_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ rw[Once OWHILE_THM, stepk_def, apply_vals_def]
    \\ rw[Once OWHILE_THM, SimpRHS, stepk_def]
    \\ gvs[]
    \\ simp[apply_tv_def]
    \\ rw[Once OWHILE_THM, stepk_def] )
  \\ conj_tac >- ( (* eval_expr (Subscript e1 e2) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def]
    \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, apply_val_subscript_def, liftk1, bind_def]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def]
    \\ CASE_TAC \\ reverse CASE_TAC)
  \\ conj_tac >- ( (* eval_expr (Attribute e id) *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_val_def, liftk1]
    \\ CASE_TAC \\ reverse CASE_TAC
    \\ rw[return_def] )
  \\ conj_tac >- ( (* eval_expr (Builtin bt es) *)
    simp[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ rpt strip_tac
    \\ BasicProvers.TOP_CASE_TAC
    \\ gvs[cont_def]
    \\ BasicProvers.TOP_CASE_TAC
    \\ gvs[] \\ first_x_assum drule
    \\ first_x_assum drule
    \\ rw[bind_def]
    \\ (CASE_TAC \\ reverse CASE_TAC
        >- rw[Once OWHILE_THM, stepk_def, apply_exc_def])
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def,
          apply_tv_def, bind_def, liftk1]
    >> CASE_TAC \\ CASE_TAC \\ rw[return_def] )
  \\ conj_tac >- ( (* eval_expr (Pop bt) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def, UNCURRY]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_base_target_def, bind_def, liftk1] )
  \\ conj_tac >- ( (* eval_expr (TypeBuiltin ...) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def, liftk1] )
  \\ conj_tac >- ( (* eval_expr (Call Send es _) *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    \\ gvs[] \\ first_x_assum drule \\ rw[]
    \\ CASE_TAC \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    >> rw[Once OWHILE_THM, stepk_def, apply_vals_def,
          bind_def, ignore_bind_def, liftk1]
    \\ qmatch_goalsub_abbrev_tac`type_check b c d`
    \\ `type_check b c d = (INL (), d)`
    by (
      rw[check_def, type_check_def, assert_def, Abbr`b`]
      \\ drule eval_exprs_length
      \\ gvs[check_def, type_check_def, assert_def] )
    \\ rw[] )
  \\ conj_tac >- ( (* ExtCall *)
    rw[eval_expr_cps_def, evaluate_def, bind_def]
    >> CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
    >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
    \\ simp[Once OWHILE_THM, stepk_def, apply_vals_def, liftk1]
    \\ qmatch_goalsub_abbrev_tac`pair_CASE cc1`
    \\ qmatch_goalsub_abbrev_tac`lhs = _`
    \\ qmatch_goalsub_abbrev_tac`pair_CASE cc2`
    >> qmatch_asmsub_abbrev_tac`monad_bind (lift_option _ _) (λresult. gg result)`
    \\ qunabbrev_tac`lhs`
    >> qmatch_asmsub_abbrev_tac`ignore_bind tc1 _`
    >> Cases_on`tc1 r`
    >> reverse(Cases_on`q`)
    >- ( simp[Abbr`cc1`,Abbr`cc2`,ignore_bind_def,bind_def] )
    >> first_x_assum drule
    >> gvs[Abbr`tc1`]
    >> disch_then drule
    >> gvs[ignore_bind_def,bind_def]
    >> qmatch_asmsub_abbrev_tac`pair_CASE lot`
    >> Cases_on`lot` >> reverse(Cases_on`q`)
    >- ( simp[Abbr`cc1`,Abbr`cc2`,ignore_bind_def,bind_def] )
    >> gvs[]
    >> disch_then drule
    >> qmatch_asmsub_abbrev_tac`pair_CASE lot`
    >> Cases_on`lot` >> reverse(Cases_on`q`)
    >- ( simp[Abbr`cc1`,Abbr`cc2`,ignore_bind_def,bind_def] )
    >> gvs[]
    >> PairCases_on`x''`
    >> disch_then drule
    >> gvs[ignore_bind_def, bind_def]
    >> ntac 4 (
      qmatch_asmsub_abbrev_tac`pair_CASE lot`
      >> Cases_on`lot` >> reverse(Cases_on`q`)
      >- ( simp[Abbr`cc1`,Abbr`cc2`,ignore_bind_def,bind_def] )
      >> gvs[]
      >> disch_then drule )
    >> qmatch_asmsub_abbrev_tac`pair_CASE lot`
    >> Cases_on`lot` >> reverse(Cases_on`q`)
    >- ( simp[Abbr`cc1`,Abbr`cc2`,ignore_bind_def,bind_def] )
    >> gvs[]
    >> qmatch_asmsub_rename_tac`_ = (INL pp,_)`
    >> PairCases_on`pp`
    >> reverse(Cases_on`pp1=[]`)
    >- (
      disch_then kall_tac >>
      simp[Abbr`cc1`,Abbr`cc2`,Abbr`gg`,bind_def] >>
      ntac 5 CASE_TAC >> simp[] >>
      Cases_on`q` >> simp[] >>
      Cases_on`q'` >> simp[] >>
      Cases_on`q''` >> simp[] >>
      Cases_on`q'''` >> simp[] >>
      Cases_on`q''''` >> simp[return_def])
    >> gvs[bind_def,Abbr`gg`] >> disch_then drule
    >> ntac 4 (
      qmatch_asmsub_abbrev_tac`pair_CASE lot`
      >> Cases_on`lot` >> reverse(Cases_on`q`)
      >- ( simp[Abbr`cc1`,Abbr`cc2`,ignore_bind_def,bind_def] )
      >> gvs[]
      >> disch_then drule )
    >> simp[Abbr`cc1`,Abbr`cc2`]
    >> IF_CASES_TAC >> gvs[bind_def,return_def]
    >> CASE_TAC >> CASE_TAC >> simp[] )
  \\ conj_tac >- ( (* IntCall *)
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def,
       no_recursion_def]
    \\ BasicProvers.TOP_CASE_TAC
    \\ simp[cont_def]
    \\ reverse (Cases_on`q`)
    >- (qpat_x_assum `_ = (INR _,r)` mp_tac
        \\ simp[CaseEq"prod",CaseEq"sum",return_def]
        \\ strip_tac
        \\ simp[apply_exc_owhile_eq])
    \\ rename1`INL call_info`
    \\ PairCases_on`call_info`
    >> pop_assum mp_tac
    >> simp[CaseEq"prod",CaseEq"sum",return_def]
    >> strip_tac >> gvs[]
    >> first_x_assum drule_all
    >> simp[cont_def]
    >> disch_then kall_tac
    >> CASE_TAC
    \\ reverse CASE_TAC
    >- gvs[return_def, raise_def, apply_exc_owhile_eq,
           Once OWHILE_THM, stepk_def, apply_exc_def]
    >> simp[Once OWHILE_THM, stepk_def, apply_vals_def, bind_def]
    >> CASE_TAC
    >> reverse CASE_TAC
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> simp[ignore_bind_def, bind_def]
    >> CASE_TAC
    >> reverse CASE_TAC
    >- gvs[set_scopes_def,return_def]
    >> pop_assum mp_tac
    >> simp[return_def]
    >> strip_tac
    >> first_x_assum drule_all
    >> drule eval_exprs_length >> strip_tac
    >> simp[cont_def]
    >> disch_then kall_tac
    \\ CASE_TAC
    \\ reverse CASE_TAC
    >- gvs[return_def, raise_def, apply_exc_owhile_eq,
           Once OWHILE_THM, stepk_def, apply_exc_def, o_DEF,
           finally_def, bind_def, ignore_bind_def, liftk1,
           set_scopes_def, return_def]
    >> qmatch_goalsub_abbrev_tac`finally mm ss zz`
    >> Cases_on`finally mm ss zz`
    >> simp[]
    >> reverse $ Cases_on`q`
    >> simp[Abbr`ss`,Abbr`zz`]
    >- (
      pop_assum mp_tac >>
      simp[finally_def, ignore_bind_def, bind_def, return_def, raise_def] >>
      simp[CaseEq"prod",CaseEq"sum"] >>
      simp[set_scopes_def, return_def] >>
      simp[Abbr`mm`, bind_def])
    >> first_x_assum $ funpow 5 drule_then drule
    >> qunabbrev_tac`mm`
    >> disch_then drule
    >> strip_tac
    >> simp[Once OWHILE_THM,stepk_def,apply_vals_def,bind_def,ignore_bind_def]
    >> simp[Once set_scopes_def, return_def]
    >> qhdtm_x_assum`finally`mp_tac
    >> simp[finally_def,bind_def,ignore_bind_def]
    >> simp[Once set_scopes_def, return_def]
    >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `∃q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `∃q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `∃q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> qmatch_goalsub_abbrev_tac`pair_CASE (pair_CASE pp _)`
    >> `∃q r. pp = (q,r)` by (Cases_on`pp` >> gvs[])
    >> simp[Abbr`pp`]
    >> reverse $ Cases_on`q`
    >> simp[]
    >- (simp[Once OWHILE_THM,SimpRHS,stepk_def] >> rw[] >>
        simp[apply_exc_def] >> simp[Once OWHILE_THM,stepk_def] )
    >> first_x_assum drule >> simp[]
    >> disch_then drule
    >> gvs[]
    >> disch_then $ drule_then drule
    >> simp[cont_def]
    >> disch_then kall_tac
    >> simp[try_def, bind_def]
    >> CASE_TAC
    >> reverse CASE_TAC
    >> simp[]
    >- (
      simp[Once OWHILE_THM, stepk_def] >>
      simp[apply_exc_def, liftk1, finally_def, bind_def] >>
      qmatch_goalsub_rename_tac`handle_function ff ss` >>
      Cases_on`handle_function ff ss` >>
      simp[return_def, ignore_bind_def, bind_def] >>
      AP_TERM_TAC >>
      gvs[push_function_def, return_def] >>
      (* chains are pure computation; dead assumptions only slow simp down *)
      POP_ASSUM_LIST (K ALL_TAC) >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[return_def, raise_def] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] )
    >> simp[Once OWHILE_THM, stepk_def, apply_def, liftk1]
    >> simp[bind_def, return_def, ignore_bind_def]
    >> gvs[push_function_def, return_def]
    >> AP_TERM_TAC >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[return_def, raise_def] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[] >>
      CASE_TAC >> simp[])
  (* ===== Chain interaction builtins ===== *)
  (* All 5 new cases: CPS eval_exprs then continuation matches big-step body.
     Pattern: unfold both sides, use IH for eval_exprs, match continuation bodies. *)
  (* Chain interaction builtins: all use same tactic.
     CPS evals exprs then calls apply_vals which matches big-step body.
      Applied per-case (not via rpt) to stay within the per-tactic budget. *)
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- (
    rw[eval_expr_cps_def, evaluate_def, ignore_bind_def, bind_def]
    \\ gvs[prod_CASE_rator, sum_CASE_rator, cont_def]
    \\ CASE_TAC \\ gvs[] \\ CASE_TAC \\ gvs[]
    \\ rw[Once OWHILE_THM, nextk_def, stepk_def,
          apply_exc_def, apply_vals_def, ignore_bind_def, bind_def])
  \\ conj_tac >- rw[eval_expr_cps_def, evaluate_def, return_def] (* eval_exprs [] *)
  (* eval_exprs (e::es) *)
  \\ rw[eval_expr_cps_def, evaluate_def, bind_def]
  \\ CASE_TAC \\ gvs[cont_def] \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_tv_def, liftk1]
  \\ CASE_TAC \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_val_def]
  \\ first_x_assum (drule_then drule) \\ rw[]
  \\ CASE_TAC \\ reverse CASE_TAC
  >- rw[Once OWHILE_THM, stepk_def, apply_exc_def]
  \\ rw[return_def]
  >> rw[Once OWHILE_THM, stepk_def, apply_vals_def]
  >> rw[Once OWHILE_THM, SimpRHS, stepk_def, apply_vals_def]
  \\ gvs[apply_vals_def]
  \\ rw[Once OWHILE_THM, stepk_def]
QED

Definition fromk_def[simp]:
  fromk x =
    case x of
      (SOME (AK cx Apply st DoneK)) => (INL (), st)
    | (SOME (AK cx (ApplyExc ex) st DoneK)) => (INR ex, st)
    | _ => (INR $ Error (TypeError "fromk"), empty_state)
End

val () = cv_trans fromk_def;

Theorem cont_tr:
  cont ak = if nextk ak = DoneK then SOME ak else cont (stepk ak)
Proof
  simp[Once cont_def]
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC \\ gs[]
  \\ simp[Once cont_def]
QED

val cont_tr_pre_def = cv_trans_pre "cont_pre" cont_tr;

Theorem IS_SOME_cont:
  IS_SOME (cont ak) ⇔
  ∃n. nextk (FUNPOW stepk n ak) = DoneK
Proof
  rw[cont_def, OWHILE_def]
QED

Theorem cont_pre_IS_SOME_cont:
  cont_pre ak ⇔ IS_SOME (cont ak)
Proof
  EQ_TAC
  >- (
    qid_spec_tac`ak`
    \\ ho_match_mp_tac (theorem "cont_pre_ind")
    \\ rw[cont_def, OWHILE_def] \\ gs[]
    >- (
      first_x_assum(qspec_then`SUC n`mp_tac)
      \\ rw[FUNPOW] )
    \\ first_x_assum(qspec_then`0`mp_tac)
    \\ rw[] )
  \\ rw[IS_SOME_cont]
  \\ pop_assum mp_tac
  \\ qid_spec_tac`ak`
  \\ Induct_on`n` \\ rw[]
  >- rw[cont_tr_pre_def]
  \\ rw[Once cont_tr_pre_def]
  \\ first_x_assum irule
  \\ gs[FUNPOW]
QED

Theorem eval_stmts_eq_cont_cps:
  eval_stmts cx body st = fromk $ cont (eval_stmts_cps cx body st DoneK)
Proof
  Cases_on`eval_stmts cx body st`
  \\ qmatch_goalsub_rename_tac`res,st1`
  \\ qspecl_then[`cx`,`body`,`st`,`DoneK`]mp_tac(cj 2 eval_cps_eq)
  \\ simp[cont_def] \\ strip_tac
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC
  >- (Cases_on `res` \\ gvs[])
  \\ CASE_TAC \\ simp[]
QED

Definition fromtvk_def:
  fromtvk x =
    case x of
      (SOME (AK cx (ApplyTv tv) st DoneK)) => (INL tv, st)
    | (SOME (AK cx (ApplyExc ex) st DoneK)) => (INR ex, st)
    | _ => (INR $ Error (TypeError "fromtvk"), empty_state)
End

val () = cv_auto_trans fromtvk_def;

Theorem eval_expr_eq_cont_cps:
  eval_expr cx e st = fromtvk $ cont (eval_expr_cps cx e st DoneK)
Proof
  Cases_on`eval_expr cx e st`
  \\ qmatch_goalsub_rename_tac`res,st1`
  \\ qspecl_then[`cx`,`e`,`st`,`DoneK`]mp_tac(cj 8 eval_cps_eq)
  \\ simp[cont_def] \\ strip_tac
  \\ simp[Once OWHILE_THM]
  \\ IF_CASES_TAC
  \\ Cases_on `res` \\ gvs[]
  \\ simp[fromtvk_def]
QED

val constants_env_pre_def = constants_env_def
  |> SRULE [eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "constants_env_pre";

Theorem constants_env_pre[cv_pre]:
  ∀v0 v1 v2 v3 v acc. constants_env_pre v0 v1 v2 v3 v acc
Proof
  ho_match_mp_tac constants_env_ind
  \\ rw[]
  \\ rw[Once constants_env_pre_def]
  \\ gs[eval_expr_eq_cont_cps]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_abbrev_tac`eval_expr_cps ec ee es dk`
  \\ qspecl_then[`ec`,`ee`,`es`,`dk`]mp_tac $ cj 8 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC
  \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM, Abbr`dk`]
QED

val evaluate_defaults_pre_def = evaluate_defaults_def
  |> SRULE [eval_expr_eq_cont_cps]
  |> cv_auto_trans_pre "evaluate_defaults_pre";

Theorem evaluate_defaults_pre[cv_pre]:
  ∀cx am v. evaluate_defaults_pre cx am v
Proof
  ntac 2 gen_tac
  \\ Induct \\ rw[]
  \\ rw[Once evaluate_defaults_pre_def]
  \\ gs[eval_expr_eq_cont_cps]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_abbrev_tac`eval_expr_cps ec ee es dk`
  \\ qspecl_then[`ec`,`ee`,`es`,`dk`]mp_tac $ cj 8 eval_cps_eq
  \\ rw[cont_def]
  \\ CASE_TAC
  \\ CASE_TAC \\ gvs[]
  \\ rw[Once OWHILE_THM, Abbr`dk`]
QED

val call_external_function_pre_def = call_external_function_def
     |> SRULE [eval_stmts_eq_cont_cps,
               vyperStateTheory.bind_def, vyperStateTheory.ignore_bind_def,
               vyperStateTheory.return_def, vyperStateTheory.raise_def,
               LET_THM, COND_RATOR, option_CASE_rator,
               get_transient_storage_def, update_transient_def]
     |> cv_auto_trans_pre "call_external_function_pre";

Theorem call_external_function_pre[cv_pre]:
  call_external_function_pre am cx nr mut ts all_mods args dflts vals
    (bod:stmt list) ret
Proof
  rw[call_external_function_pre_def]
  \\ rw[cont_pre_IS_SOME_cont]
  \\ qmatch_goalsub_abbrev_tac`eval_stmts_cps cx ss st k`
  \\ qspecl_then[`cx`,`ss`,`st`,`k`]mp_tac $ cj 2 eval_cps_eq
  \\ rw[]
  \\ CASE_TAC
  \\ CASE_TAC
  \\ rw[Abbr`k`, cont_def]
  \\ rw[Once OWHILE_THM]
QED

val () = cv_auto_trans call_external_def;
val () = cv_auto_trans clear_machine_logs_def;
val () = cv_auto_trans call_external_transaction_def;

val () = cv_auto_trans load_contract_def;
