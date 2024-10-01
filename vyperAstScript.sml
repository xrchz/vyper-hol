open HolKernel boolLib bossLib Parse wordsLib;
open wordsTheory integerTheory stringTheory listTheory optionTheory;

val _ = new_theory "vyperAst";

Type identifier = “:string”;

Datatype:
  type
  = Uint word5 (* the bit size divided by 8 *)
  | Int word5
  | Tuple (type list)
  | Void
  | Bool
End

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
  | Raise (string option)
  | Return (expr option)
  | Assign identifier (* TODO: could be a tuple *) expr
  | AnnAssign identifier type expr
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

Type argument = “:string # type”;

Datatype:
  toplevel
  = FunctionDef string (decorator list) (argument list) (stmt list) type
End;

Definition test_if_control_flow_ast_def:
  test_if_control_flow_ast =
  FunctionDef "foo" [External] []
  [
    AnnAssign "a" (Uint (n2w (256 DIV 8))) (Constant (Int 1));
    If (Compare (Name "a") Eq (Constant (Int 1)))
    [
      Assign "a" (Constant (Int 2))
    ]
    [
      Assign "a" (Constant (Int 3))
    ];
    Return (SOME (BinOp (Name "a") Add (Constant (Int 42))))
  ] (Uint (n2w (256 DIV 8)))
End;

val _ = export_theory();
