open HolKernel boolLib bossLib Parse;
open wordsTheory integerTheory stringTheory listTheory optionTheory;

val _ = new_theory "vyperAst";

Type identifier = “:string”;

Datatype:
  constant
  = Str string
  | Hex string
  | Bytes (word8 list)
  | Int int
End;

Datatype:
  cmpop
  = Eq
  | NotEq
End;

Datatype:
  operator
  = Add
  | Sub
End;

Datatype:
  stmt
  = Pass
  | Continue
  | Break
  | For expr expr (stmt list)
  | If expr (stmt list) (stmt list)
  | Assert expr string
  | Raise stmt
  | Return (expr option)
  | Assign expr expr
  ;
  expr
  = NamedExpr expr expr
  | Name identifier
  | IfExp expr expr expr
  | Constant constant
  | Compare expr cmpop expr
  | BinOp expr operator expr
End;

Datatype:
  decorator
  = External
  | Internal
End;

Type argument = “:string”;

Datatype:
  toplevel
  = FunctionDef string (decorator list) (argument list) (stmt list)
End;

Definition test_if_control_flow_ast_def:
  test_if_control_flow_ast =
  FunctionDef "foo" [External] []
  [
    Assign (Name "a") (Constant (Int 1));
    If (Compare (Name "a") Eq (Constant (Int 1)))
    [
      Assign (Name "a") (Constant (Int 2))
    ]
    [
      Assign (Name "a") (Constant (Int 3))
    ];
    Return (SOME (BinOp (Name "a") Add (Constant (Int 42))))
  ]
End;

val _ = export_theory();
