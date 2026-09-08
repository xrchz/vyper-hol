Theory jsonAST
Ancestors
  string words
Libs
  cv_transLib

(* ===== Type Information ===== *)
(* Mirrors the "type" field in JSON *)

Datatype:
  json_type
  = JT_Named (int option) string              (* optional declaration source_id, name *)
  | JT_Integer num bool                       (* bits, is_signed *)
  | JT_BytesM num                             (* m for bytes1..bytes32 *)
  | JT_String num                             (* length *)
  | JT_Bytes num                              (* length *)
  | JT_StaticArray json_type num              (* value_type, length *)
  | JT_DynArray json_type num                 (* value_type, length *)
  | JT_Struct (int option) string             (* optional declaration source_id, name *)
  | JT_Flag (int option) string               (* optional declaration source_id, name *)
  | JT_Interface (int option) string          (* optional declaration source_id, name *)
  | JT_Tuple (json_type list)                 (* member_types *)
  | JT_HashMap json_type json_type            (* key_type, value_type *)
  | JT_None                                   (* null type *)
End

(* Syntactic type annotations are kept distinct from compiler-inferred type
   metadata. Names and qualified paths are resolved only by jsonToVyper. *)
Datatype:
  json_type_annotation
  = JTA_Named string
  | JTA_Integer num bool
  | JTA_BytesM num
  | JTA_String num
  | JTA_Bytes num
  | JTA_StaticArray json_type_annotation num
  | JTA_DynArray json_type_annotation num
  | JTA_Qualified (string list) string
  | JTA_Tuple (json_type_annotation list)
  | JTA_None
End

(* ===== Binary/Unary Operators ===== *)
(* Direct mirror of ast_type for operators *)

Datatype:
  json_binop
  = JBop_Add | JBop_Sub | JBop_Mult | JBop_Div | JBop_FloorDiv
  | JBop_Mod | JBop_Pow
  | JBop_And | JBop_Or | JBop_BitAnd | JBop_BitOr | JBop_BitXor
  | JBop_LShift | JBop_RShift
  | JBop_Eq | JBop_NotEq | JBop_Lt | JBop_LtE | JBop_Gt | JBop_GtE
  | JBop_In | JBop_NotIn
End

Datatype:
  json_unaryop = JUop_USub | JUop_Not | JUop_Invert
End

Datatype:
  json_boolop = JBoolop_And | JBoolop_Or
End

(* ===== Expressions ===== *)
(* Only keep type info where needed for translation *)

(* Raw declaration-source metadata: missing field versus an explicit compiler
   source ID. Interpretation belongs to jsonToVyper. *)
Datatype:
  json_source_ref
  = JMissingSource
  | JExplicitSource int
End

Datatype:
  json_expr
  (* Literals - need type for int bounds, string/bytes length *)
  = JE_Int int json_type                               (* value, type for bounds *)
  | JE_Decimal string                                  (* value as string *)
  | JE_Str num string                                  (* length, value *)
  | JE_GenericStr string                               (* generic string, no length *)
  | JE_Bytes num string                                (* length, hex value *)
  | JE_Hex string json_type                            (* hex value and compiler type *)
  | JE_Bool bool                                       (* True/False *)
  | JE_Ellipsis                                        (* interface stub body *)

  (* Variables and access *)
  | JE_Name string (string option) json_source_ref json_type         (* id, typeclass, declaration source, type *)
  | JE_Folded json_expr json_expr                       (* original expression, compiler-provided folded expression *)
  | JE_Attribute json_expr string (string option) (string option) (string option) json_source_ref json_type  (* value, attr, result_typeclass, base_type_name, base_typeclass, declaration source, type *)
  | JE_Subscript json_expr json_expr json_type         (* value, slice, type *)
  | JE_NamedExpr json_expr json_expr                   (* target, value - dependency binding in initializes: lib[dep := dep] *)

  (* Operators *)
  | JE_BinOp json_expr json_binop json_expr json_type  (* left, op, right, type *)
  | JE_Compare json_expr json_binop json_expr           (* left, op, right *)
  | JE_BoolOp json_boolop (json_expr list)             (* op, values *)
  | JE_UnaryOp json_unaryop json_expr json_type        (* op, operand, type *)
  | JE_IfExp json_expr json_expr json_expr json_type   (* test, body, orelse, type *)

  (* Compound - need type for array element type, tuple handling *)
  | JE_Tuple (json_expr list)                          (* elements *)
  | JE_List (json_expr list) json_type                 (* elements, type needed for elem type *)

  (* Calls - need type for builtins like concat/slice that embed return length *)
  (* Last field is source_id for module calls, extracted from func.type.type_decl_node *)
  | JE_Call json_expr (json_expr list) (json_keyword list) json_type json_source_ref

  (* External calls preserve target and ordinary arguments separately. *)
  | JE_ExtCall string json_source_ref (json_type list) json_type json_expr
      (json_expr list) (json_keyword list)
  | JE_StaticCall string json_source_ref (json_type list) json_type json_expr
      (json_expr list)
;
  json_keyword = JKeyword string json_expr             (* arg, value *)
End

(* ===== Statements ===== *)

Datatype:
  json_stmt
  = JS_Pass
  | JS_Break
  | JS_Continue
  | JS_Expr json_expr
  | JS_Return (json_expr option)
  | JS_Raise (json_expr option)
  | JS_Assert json_expr (json_expr option)             (* test, msg *)
  | JS_Log (json_source_ref # string) (json_expr list) (* declaration source, event name, args *)
  | JS_If json_expr (json_stmt list) (json_stmt list)  (* test, body, orelse *)
  | JS_For string json_type json_type_annotation json_iter (json_stmt list)
      (* var, inferred type, syntactic annotation, iter, body *)
  | JS_Assign json_target json_expr                    (* target, value *)
  | JS_AnnAssign string json_type json_type_annotation json_expr
      (* var name, inferred type, syntactic annotation, value *)
  | JS_AugAssign json_base_target json_binop json_expr (* target, op, value *)
  | JS_Append json_base_target json_expr               (* target, value *)
;
  (* Iterator - need type info for computing bounds *)
  json_iter
  = JIter_Range (json_expr list) (int option list) (num option)
                (* args, folded values per arg, explicit bound if given *)
  | JIter_Array json_expr json_type                    (* array expr, array type for bound *)
;
  (* Assignment targets *)
  json_base_target
  = JBT_Name string
  | JBT_TopLevelName (json_source_ref # string) (* declaration source and name *)
  | JBT_Subscript json_base_target json_expr
  | JBT_Attribute json_base_target string
;
  json_target
  = JTgt_Base json_base_target
  | JTgt_Tuple (json_target list)
End

(* ===== Top-level Declarations ===== *)

Datatype:
  json_arg = JArg string json_type json_type_annotation
    (* arg name, compiler-inferred type, syntactic annotation *)
End

Datatype:
  json_func_type = JFuncType (json_type list) json_type  (* argument_types, return_type *)
End

(* HashMap value types need special handling for nested hashmaps *)
Datatype:
  json_value_type
  = JVT_Type json_type
  | JVT_HashMap json_type json_value_type              (* key_type, value_type *)
End

Datatype:
  json_import_info
  = JImportInfo string int string string
    (* alias, source_id, qualified_module_name, resolved_path *)
End

(* ===== Interface Function Signature ===== *)
(* Represents a function signature within an interface definition *)

Datatype:
  json_interface_func
  = JInterfaceFunc string (json_arg list) json_type_annotation (string list)
    (* name, args, return_type, decorators (mutability) *)
End

Datatype:
  json_toplevel
  = JTL_FunctionDef string (string list) (json_arg list) (json_expr list) json_func_type json_type_annotation (json_stmt list)
      (* name, decorators, args, defaults, func_type, syntactic return annotation, body *)
  | JTL_VariableDecl string json_type json_type_annotation bool bool bool (json_expr option)
      (* name, inferred type, syntactic annotation, is_public, is_immutable, is_transient, value (for constants) *)
  | JTL_HashMapDecl string json_type json_value_type bool bool
      (* name, key_type, value_type, is_public, is_transient *)
  | JTL_EventDef string ((json_arg # bool) list)  (* bool = indexed *)
  | JTL_StructDef string (json_arg list)
  | JTL_FlagDef string (string list)                   (* name, member names *)
  | JTL_InterfaceDef string (json_interface_func list) (* name, function signatures *)
  (* Module-related declarations *)
  | JTL_Import (json_import_info list)                 (* import statement with import infos *)
  | JTL_ExportsDecl json_expr                          (* exports: annotation *)
  | JTL_InitializesDecl json_expr                      (* initializes: annotation *)
  | JTL_UsesDecl json_expr                             (* uses: annotation *)
  | JTL_ImplementsDecl json_expr                       (* implements: interface *)
End

(* ===== Module ===== *)

Datatype:
  json_module = JModule int bool (json_toplevel list)
    (* source_id, nonreentrancy_by_default, body *)
End

(* ===== Imported Module ===== *)
(* Represents an imported module from the imports array *)

Datatype:
  json_imported_module
  = JImportedModule int string string bool (json_toplevel list)
    (* source_id, path, resolved_path, nonreentrancy_by_default, body *)
End

(* ===== Annotated AST ===== *)
(* Full annotated AST with main module and imported modules *)

Datatype:
  json_annotated_ast
  = JAnnotatedAST json_module (json_imported_module list)  (* main ast, imports *)
End

(* ===== Storage Layout ===== *)
(* Maps variable names to their storage slot information *)

Datatype:
  storage_slot_info = <|
    slot : num;       (* starting slot number *)
    n_slots : num;    (* number of slots used *)
    type_str : string (* type as string, e.g. "uint256", "HashMap[int128, W]" *)
  |>
End

(* For immutables stored in code *)
Datatype:
  code_slot_info = <|
    offset : num;     (* byte offset in deployed code *)
    length : num;     (* length in bytes *)
    type_str : string (* type as string *)
  |>
End

(* Complete storage layout for a contract *)
(* Storage keys are (module_alias_opt, var_name):
   - (NONE, "counter") for main module variables
   - (SOME "lib1", "counter") for module lib1's variables *)
Datatype:
  json_storage_layout = <|
    storage : ((string option # string) # storage_slot_info) list;
    transient : ((string option # string) # storage_slot_info) list;
    code : (string # code_slot_info) list  (* immutables - no module nesting *)
  |>
End

(* Datatypes are automatically translated by cv_transLib when defined *)
