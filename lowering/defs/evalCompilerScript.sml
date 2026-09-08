(*
 * Compiler Evaluation Fixtures
 *
 * STATUS: Regression/evaluation support, not core lowering definitions.
 * Defines small Vyper AST programs and proves by EVAL_TAC that the executable
 * compiler produces SOME bytecode. Currently kept build-checked under defs/.
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
    (compile_vyper ([] : toplevel list)
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem noop_compiles:
  IS_SOME
    (compile_vyper noop_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem return_uint_compiles:
  IS_SOME
    (compile_vyper return_uint_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem return_arg_compiles:
  IS_SOME
    (compile_vyper return_arg_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem local_uint_compiles:
  IS_SOME
    (compile_vyper local_uint_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem add_arg_compiles:
  IS_SOME
    (compile_vyper add_arg_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem two_external_compiles:
  IS_SOME
    (compile_vyper two_external_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem storage_read_compiles:
  IS_SOME
    (compile_vyper storage_read_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem storage_write_compiles:
  IS_SOME
    (compile_vyper storage_write_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem deploy_storage_compiles:
  IS_SOME
    (compile_vyper deploy_storage_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem event_log_compiles:
  IS_SOME
    (compile_vyper event_log_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem indexed_event_log_compiles:
  IS_SOME
    (compile_vyper indexed_event_log_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem mixed_event_log_compiles:
  IS_SOME
    (compile_vyper mixed_event_log_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem hashmap_read_compiles:
  IS_SOME
    (compile_vyper hashmap_read_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem hashmap_write_compiles:
  IS_SOME
    (compile_vyper hashmap_write_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem if_bool_compiles:
  IS_SOME
    (compile_vyper if_bool_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem if_join_compiles:
  IS_SOME
    (compile_vyper if_join_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem for_pass_compiles:
  IS_SOME
    (compile_vyper for_pass_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem for_accum_compiles:
  IS_SOME
    (compile_vyper for_accum_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem for_continue_compiles:
  IS_SOME
    (compile_vyper for_continue_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem for_break_compiles:
  IS_SOME
    (compile_vyper for_break_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem internal_call_compiles:
  IS_SOME
    (compile_vyper internal_call_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_compiles:
  IS_SOME
    (compile_vyper internal_call_arg_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED
