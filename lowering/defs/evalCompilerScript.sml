(*
 * Compiler Evaluation Fixtures
 *
 * STATUS: Regression/evaluation support, not core lowering definitions.
 * Defines small Vyper AST programs and evaluates the checked compiler with
 * EVAL_TAC. Successful cases produce SOME bytecode; known checked-guard
 * rejections are recorded explicitly as NONE. Kept build-checked under defs/.
 *)

Theory evalCompiler
Ancestors compileVyper concretizeMemLocDefs alist byte integer_word option
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Definition noop_program_def:
  noop_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) NoneT [Pass]]
End

Definition return_uint_program_def:
  return_uint_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]]
End

Definition return_arg_program_def:
  return_arg_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Name (BaseT (UintT 256)) "x"))]]
End

Definition local_uint_program_def:
  local_uint_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 1));
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition add_arg_program_def:
  add_arg_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "x";
              Literal (BaseT (UintT 256)) (IntL 1)]))]]
End

Definition two_external_program_def:
  two_external_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))];
     FunctionDecl External Nonpayable F F "bar"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 2)))]]
End

Definition storage_read_program_def:
  storage_read_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]]
End

Definition storage_write_program_def:
  storage_write_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
          (Literal (BaseT (UintT 256)) (IntL 5));
        Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]]
End

Definition deploy_storage_program_def:
  deploy_storage_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl Deploy Nonpayable F F "__init__"
       ([] : (string # type) list) ([] : expr list) NoneT
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
          (Literal (BaseT (UintT 256)) (IntL 5))];
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]]
End

Definition event_log_program_def:
  event_log_program =
    [EventDecl "Ping" [(("value", BaseT (UintT 256)), F)];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) NoneT
       [Log (NONE, "Ping") [Name (BaseT (UintT 256)) "x"]]]
End

Definition indexed_event_log_program_def:
  indexed_event_log_program =
    [EventDecl "Ping" [(("value", BaseT (UintT 256)), T)];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) NoneT
       [Log (NONE, "Ping") [Name (BaseT (UintT 256)) "x"]]]
End

Definition mixed_event_log_program_def:
  mixed_event_log_program =
    [EventDecl "Ping"
       [(("indexed_value", BaseT (UintT 256)), T);
        (("data_value", BaseT (UintT 256)), F)];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256)); ("y", BaseT (UintT 256))]
       ([] : expr list) NoneT
       [Log (NONE, "Ping")
          [Name (BaseT (UintT 256)) "x";
           Name (BaseT (UintT 256)) "y"]]]
End

Definition hashmap_read_program_def:
  hashmap_read_program =
    [HashMapDecl Private F "stored" (BaseT (UintT 256))
       (Type (BaseT (UintT 256))) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       [("k", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Subscript (BaseT (UintT 256))
             (TopLevelName NoneT (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))]]
End

Definition hashmap_write_program_def:
  hashmap_write_program =
    [HashMapDecl Private F "stored" (BaseT (UintT 256))
       (Type (BaseT (UintT 256))) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       [("k", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Assign (BaseTarget
          (SubscriptTarget (TopLevelNameTarget (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))
          (Literal (BaseT (UintT 256)) (IntL 5));
        Return (SOME
          (Subscript (BaseT (UintT 256))
             (TopLevelName NoneT (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))]]
End

Definition if_bool_program_def:
  if_bool_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT BoolT)] ([] : expr list) (BaseT (UintT 256))
       [If (Name (BaseT BoolT) "x")
          [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]
          [Return (SOME (Literal (BaseT (UintT 256)) (IntL 2)))]]]
End

Definition if_join_program_def:
  if_join_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT BoolT)] ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 1));
        If (Name (BaseT BoolT) "x")
          [Assign (BaseTarget (NameTarget "y"))
             (Literal (BaseT (UintT 256)) (IntL 2))]
          [Assign (BaseTarget (NameTarget "y"))
             (Literal (BaseT (UintT 256)) (IntL 3))];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_pass_program_def:
  for_pass_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 2)))
          0
          [Pass];
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]]
End

Definition for_accum_program_def:
  for_accum_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 2)))
          0
          [Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_continue_program_def:
  for_continue_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 3)))
          0
          [If (Builtin (BaseT BoolT) (Bop Eq)
                 [Name (BaseT (UintT 256)) "i";
                  Literal (BaseT (UintT 256)) (IntL 1)])
              [Continue]
              [];
           Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_break_program_def:
  for_break_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 3)))
          0
          [If (Builtin (BaseT BoolT) (Bop Eq)
                 [Name (BaseT (UintT 256)) "i";
                  Literal (BaseT (UintT 256)) (IntL 2)])
              [Break]
              [];
           Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition internal_call_program_def:
  internal_call_program =
    [FunctionDecl Internal Nonpayable F F "bar"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 7)))];
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
             ([] : expr list) NONE))]]
End

Definition internal_call_arg_program_def:
  internal_call_arg_program =
    [FunctionDecl Internal Nonpayable F F "bar"
       [("y", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "y";
              Literal (BaseT (UintT 256)) (IntL 1)]))];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
             [Name (BaseT (UintT 256)) "x"] NONE))]]
End

Theorem empty_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       ([] : toplevel list))
Proof
  EVAL_TAC
QED

Theorem noop_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       noop_program)
Proof
  EVAL_TAC
QED

Theorem return_uint_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       return_uint_program)
Proof
  EVAL_TAC
QED

Theorem return_arg_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       return_arg_program)
Proof
  EVAL_TAC
QED

Theorem local_uint_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       local_uint_program)
Proof
  EVAL_TAC
QED

Theorem add_arg_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       add_arg_program)
Proof
  EVAL_TAC
QED

Theorem two_external_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       two_external_program)
Proof
  EVAL_TAC
QED

Theorem storage_read_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       storage_read_program)
Proof
  EVAL_TAC
QED

Theorem storage_write_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       storage_write_program)
Proof
  EVAL_TAC
QED

Theorem deploy_storage_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       deploy_storage_program)
Proof
  EVAL_TAC
QED

Theorem event_log_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       event_log_program)
Proof
  EVAL_TAC
QED

Theorem indexed_event_log_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       indexed_event_log_program)
Proof
  EVAL_TAC
QED

Theorem mixed_event_log_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       mixed_event_log_program)
Proof
  EVAL_TAC
QED

Theorem hashmap_read_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       hashmap_read_program)
Proof
  EVAL_TAC
QED

Theorem hashmap_write_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       hashmap_write_program)
Proof
  EVAL_TAC
QED

Theorem if_bool_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       if_bool_program)
Proof
  EVAL_TAC
QED

Theorem if_join_compiles:
  IS_SOME
    (compile_vyper (K SOME) (o1_policy prague_capabilities)
       if_join_program)
Proof
  EVAL_TAC
QED

(* These loop programs evaluate to NONE at the checked O1 boundary.  make_ssa
 * introduces loop-header PHIs whose back-edge operands are defined in the loop
 * body.  The current def_dominates_uses guard treats every PHI operand as an
 * ordinary use in the header block, so it requires each back-edge definition
 * to dominate the header (and any same-block definition to precede the PHI).
 * A loop-body definition does not dominate its header, so the guard rejects
 * these otherwise expected SSA shapes.  Evaluation itself is complete; PHI
 * edge-use dominance is a separate semantic/correctness change. *)
Theorem for_pass_evaluates:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    for_pass_program = NONE
Proof
  EVAL_TAC
QED

Theorem for_accum_evaluates:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    for_accum_program = NONE
Proof
  EVAL_TAC
QED

Theorem for_continue_evaluates:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    for_continue_program = NONE
Proof
  EVAL_TAC
QED

Theorem for_break_evaluates:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    for_break_program = NONE
Proof
  EVAL_TAC
QED

(* These internal-call programs also evaluate to NONE, for a different checked
 * guard.  compile_internal_function currently emits the hidden return-PC input
 * as PARAM.  fn_user_param_insts therefore counts it as a user argument, and
 * invoke_input_arity_ok expects one more INVOKE argument than the call site
 * supplies.  The final fmp_lowered_context_wf check rejects that mismatch.
 * Distinguishing the hidden input as RETPC_PARAM changes lowering semantics and
 * is intentionally left for a separate change. *)
Theorem internal_call_evaluates:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    internal_call_program = NONE
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_evaluates:
  compile_vyper (K SOME) (o1_policy prague_capabilities)
    internal_call_arg_program = NONE
Proof
  EVAL_TAC
QED
