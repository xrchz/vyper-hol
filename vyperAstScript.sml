open HolKernel boolLib bossLib Parse;
open wordsTheory integerTheory stringTheory listTheory;

val _ = new_theory "vyperAst";

Datatype:
  constant
  = Str string
  | Hex string
  | Bytes (word8 list)
  | Int int
End

Datatype:
  stmt
  = Pass
  | Continue
  | Break
  | For expr expr (stmt list)
  | If (stmt list) (stmt list)
  | Assert expr string
  | Raise stmt
  ;
  expr
  = NamedExpr expr expr
  | IfExp expr expr expr
  | Constant constant
End


val _ = export_theory();
