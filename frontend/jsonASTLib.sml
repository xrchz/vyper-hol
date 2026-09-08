(* jsonASTLib.sml - Parse JSON into jsonAST HOL terms
 *
 * This is a dead simple parser that mirrors JSON structure exactly.
 * NO semantic decisions (msg.sender recognition, loop bounds, etc.)
 * Those are handled in jsonToVyperScript.sml (Phase 3).
 *)

structure jsonASTLib :> jsonASTLib = struct

open HolKernel boolLib
open pairSyntax listSyntax stringSyntax optionSyntax numSyntax intSyntax
open jsonASTTheory JSONDecode

(* ===== HOL Term Helpers ===== *)

fun jastk s = prim_mk_const{Thy="jsonAST",Name=s}
fun jasty s = mk_thy_type{Thy="jsonAST",Tyop=s,Args=[]};

(* nsid: namespaced identifier (num option # string) *)
fun mk_nsid (src_id_opt, name) =
  mk_pair(src_id_opt, fromMLstring name);

(* ===== Types ===== *)

val json_type_ty = jasty "json_type"
val json_type_annotation_ty = jasty "json_type_annotation"
val json_expr_ty = jasty "json_expr"
val json_keyword_ty = jasty "json_keyword"
val json_stmt_ty = jasty "json_stmt"
val json_target_ty = jasty "json_target"
val json_arg_ty = jasty "json_arg"
val json_interface_func_ty = jasty "json_interface_func"
val json_import_info_ty = jasty "json_import_info"
val json_toplevel_ty = jasty "json_toplevel"

(* ===== Type Constructors ===== *)

val JT_Named_tm = jastk "JT_Named"
val JT_Integer_tm = jastk "JT_Integer"
val JT_BytesM_tm = jastk "JT_BytesM"
val JT_String_tm = jastk "JT_String"
val JT_Bytes_tm = jastk "JT_Bytes"
val JT_StaticArray_tm = jastk "JT_StaticArray"
val JT_DynArray_tm = jastk "JT_DynArray"
val JT_Struct_tm = jastk "JT_Struct"
val JT_Flag_tm = jastk "JT_Flag"
val JT_Interface_tm = jastk "JT_Interface"
val JT_Tuple_tm = jastk "JT_Tuple"
val JT_HashMap_tm = jastk "JT_HashMap"
val JT_None_tm = jastk "JT_None"

fun mk_JT_Named (sid_opt, s) = list_mk_comb(JT_Named_tm, [sid_opt, fromMLstring s])
fun mk_JT_Integer (bits, is_signed) =
  list_mk_comb(JT_Integer_tm, [bits, mk_bool is_signed])
fun mk_JT_BytesM m = mk_comb(JT_BytesM_tm, m)
fun mk_JT_String len = mk_comb(JT_String_tm, len)
fun mk_JT_Bytes len = mk_comb(JT_Bytes_tm, len)
fun mk_JT_StaticArray (vt, len) = list_mk_comb(JT_StaticArray_tm, [vt, len])
fun mk_JT_DynArray (vt, len) = list_mk_comb(JT_DynArray_tm, [vt, len])
fun mk_JT_Struct (sid_opt, s) = list_mk_comb(JT_Struct_tm, [sid_opt, fromMLstring s])
fun mk_JT_Flag (sid_opt, s) = list_mk_comb(JT_Flag_tm, [sid_opt, fromMLstring s])
fun mk_JT_Interface (sid_opt, s) =
  list_mk_comb(JT_Interface_tm, [sid_opt, fromMLstring s])
fun mk_JT_Tuple ts = mk_comb(JT_Tuple_tm, mk_list(ts, json_type_ty))
fun mk_JT_HashMap (kt, vt) = list_mk_comb(JT_HashMap_tm, [kt, vt])

(* ===== Type Annotation Constructors ===== *)

val JTA_Named_tm = jastk "JTA_Named"
val JTA_Integer_tm = jastk "JTA_Integer"
val JTA_BytesM_tm = jastk "JTA_BytesM"
val JTA_String_tm = jastk "JTA_String"
val JTA_Bytes_tm = jastk "JTA_Bytes"
val JTA_StaticArray_tm = jastk "JTA_StaticArray"
val JTA_DynArray_tm = jastk "JTA_DynArray"
val JTA_Qualified_tm = jastk "JTA_Qualified"
val JTA_Tuple_tm = jastk "JTA_Tuple"
val JTA_None_tm = jastk "JTA_None"

fun mk_JTA_Named s = mk_comb(JTA_Named_tm, fromMLstring s)
fun mk_JTA_Integer (bits, is_signed) =
  list_mk_comb(JTA_Integer_tm, [bits, mk_bool is_signed])
fun mk_JTA_BytesM m = mk_comb(JTA_BytesM_tm, m)
fun mk_JTA_String len = mk_comb(JTA_String_tm, len)
fun mk_JTA_Bytes len = mk_comb(JTA_Bytes_tm, len)
fun mk_JTA_StaticArray (vt, len) = list_mk_comb(JTA_StaticArray_tm, [vt, len])
fun mk_JTA_DynArray (vt, len) = list_mk_comb(JTA_DynArray_tm, [vt, len])
fun mk_JTA_Qualified (path, name) =
  list_mk_comb(JTA_Qualified_tm,
    [mk_list(List.map fromMLstring path, string_ty), fromMLstring name])
fun mk_JTA_Tuple ts =
  mk_comb(JTA_Tuple_tm, mk_list(ts, json_type_annotation_ty))

(* ===== Operator Constructors ===== *)

val JBop_Add_tm = jastk "JBop_Add"
val JBop_Sub_tm = jastk "JBop_Sub"
val JBop_Mult_tm = jastk "JBop_Mult"
val JBop_Div_tm = jastk "JBop_Div"
val JBop_FloorDiv_tm = jastk "JBop_FloorDiv"
val JBop_Mod_tm = jastk "JBop_Mod"
val JBop_Pow_tm = jastk "JBop_Pow"
val JBop_And_tm = jastk "JBop_And"
val JBop_Or_tm = jastk "JBop_Or"
val JBop_BitAnd_tm = jastk "JBop_BitAnd"
val JBop_BitOr_tm = jastk "JBop_BitOr"
val JBop_BitXor_tm = jastk "JBop_BitXor"
val JBop_LShift_tm = jastk "JBop_LShift"
val JBop_RShift_tm = jastk "JBop_RShift"
val JBop_Eq_tm = jastk "JBop_Eq"
val JBop_NotEq_tm = jastk "JBop_NotEq"
val JBop_Lt_tm = jastk "JBop_Lt"
val JBop_LtE_tm = jastk "JBop_LtE"
val JBop_Gt_tm = jastk "JBop_Gt"
val JBop_GtE_tm = jastk "JBop_GtE"
val JBop_In_tm = jastk "JBop_In"
val JBop_NotIn_tm = jastk "JBop_NotIn"

val JUop_USub_tm = jastk "JUop_USub"
val JUop_Not_tm = jastk "JUop_Not"
val JUop_Invert_tm = jastk "JUop_Invert"

val JBoolop_And_tm = jastk "JBoolop_And"
val JBoolop_Or_tm = jastk "JBoolop_Or"

(* ===== Expression Constructors ===== *)

val JE_Int_tm = jastk "JE_Int"
val JE_Decimal_tm = jastk "JE_Decimal"
val JE_Str_tm = jastk "JE_Str"
val JE_GenericStr_tm = jastk "JE_GenericStr"
val JE_Bytes_tm = jastk "JE_Bytes"
val JE_Hex_tm = jastk "JE_Hex"
val JE_Bool_tm = jastk "JE_Bool"
val JE_Ellipsis_tm = jastk "JE_Ellipsis"
val JE_Name_tm = jastk "JE_Name"
val JE_Folded_tm = jastk "JE_Folded"
val JE_Attribute_tm = jastk "JE_Attribute"
val JE_Subscript_tm = jastk "JE_Subscript"
val JE_NamedExpr_tm = jastk "JE_NamedExpr"
val JE_BinOp_tm = jastk "JE_BinOp"
val JE_Compare_tm = jastk "JE_Compare"
val JE_BoolOp_tm = jastk "JE_BoolOp"
val JE_UnaryOp_tm = jastk "JE_UnaryOp"
val JE_IfExp_tm = jastk "JE_IfExp"
val JE_Tuple_tm = jastk "JE_Tuple"
val JE_List_tm = jastk "JE_List"
val JE_Call_tm = jastk "JE_Call"
val JE_ExtCall_tm = jastk "JE_ExtCall"
val JE_StaticCall_tm = jastk "JE_StaticCall"

val JKeyword_tm = jastk "JKeyword"

fun mk_JE_Int (v, ty) = list_mk_comb(JE_Int_tm, [v, ty])
fun mk_JE_Decimal s = mk_comb(JE_Decimal_tm, fromMLstring s)
fun mk_JE_Str (len, v) = list_mk_comb(JE_Str_tm, [len, fromMLstring v])
fun mk_JE_GenericStr v = mk_comb(JE_GenericStr_tm, fromMLstring v)
fun mk_JE_Bytes (len, v) = list_mk_comb(JE_Bytes_tm, [len, fromMLstring v])
fun mk_JE_Hex (s, ty) = list_mk_comb(JE_Hex_tm, [fromMLstring s, ty])
fun mk_JE_Bool b = mk_comb(JE_Bool_tm, mk_bool b)
fun mk_JE_Name (s, tc_opt, src_id_opt, ty) =
  list_mk_comb(JE_Name_tm, [fromMLstring s,
                           lift_option (mk_option string_ty) fromMLstring tc_opt,
                           src_id_opt, ty])
fun mk_JE_Folded (original, folded) =
  list_mk_comb(JE_Folded_tm, [original, folded])
fun mk_JE_Attribute (e, attr, tc_opt, base_ty_name_opt, base_tc_opt, src_id_opt, ty) =
  list_mk_comb(JE_Attribute_tm, [e, fromMLstring attr,
                                 lift_option (mk_option string_ty) fromMLstring tc_opt,
                                 lift_option (mk_option string_ty) fromMLstring base_ty_name_opt,
                                 lift_option (mk_option string_ty) fromMLstring base_tc_opt,
                                 src_id_opt, ty])
fun mk_JE_Subscript (e1, e2, ty) = list_mk_comb(JE_Subscript_tm, [e1, e2, ty])
fun mk_JE_NamedExpr (e1, e2) = list_mk_comb(JE_NamedExpr_tm, [e1, e2])
fun mk_JE_BinOp (l, op_tm, r, ty) = list_mk_comb(JE_BinOp_tm, [l, op_tm, r, ty])
fun mk_JE_Compare (l, op_tm, r) =
  list_mk_comb(JE_Compare_tm, [l, op_tm, r])
fun mk_JE_BoolOp (op_tm, es) = list_mk_comb(JE_BoolOp_tm, [op_tm, mk_list(es, json_expr_ty)])
fun mk_JE_UnaryOp (op_tm, e, ty) = list_mk_comb(JE_UnaryOp_tm, [op_tm, e, ty])
fun mk_JE_IfExp (test, body, els, ty) = list_mk_comb(JE_IfExp_tm, [test, body, els, ty])
fun mk_JE_Tuple es = mk_comb(JE_Tuple_tm, mk_list(es, json_expr_ty))
fun mk_JE_List (es, ty) = list_mk_comb(JE_List_tm, [mk_list(es, json_expr_ty), ty])
fun mk_JE_Call (func, args, kwargs, ty, src_id_opt_tm) =
  list_mk_comb(JE_Call_tm, [func, mk_list(args, json_expr_ty),
                            mk_list(kwargs, json_keyword_ty), ty, src_id_opt_tm])
fun mk_JE_ExtCall (func_name, func_src, arg_types, ret_ty, target, args, keywords) =
  list_mk_comb(JE_ExtCall_tm, [fromMLstring func_name, func_src,
                               mk_list(arg_types, json_type_ty),
                               ret_ty, target, mk_list(args, json_expr_ty),
                               mk_list(keywords, json_keyword_ty)])
fun mk_JE_StaticCall (func_name, func_src, arg_types, ret_ty, target, args) =
  list_mk_comb(JE_StaticCall_tm, [fromMLstring func_name, func_src,
                                  mk_list(arg_types, json_type_ty),
                                  ret_ty, target, mk_list(args, json_expr_ty)])
fun mk_JKeyword (arg, v) = list_mk_comb(JKeyword_tm, [fromMLstring arg, v])

(* ===== Statement Constructors ===== *)

val JS_Pass_tm = jastk "JS_Pass"
val JS_Break_tm = jastk "JS_Break"
val JS_Continue_tm = jastk "JS_Continue"
val JS_Expr_tm = jastk "JS_Expr"
val JS_Return_tm = jastk "JS_Return"
val JS_Raise_tm = jastk "JS_Raise"
val JS_Assert_tm = jastk "JS_Assert"
val JS_Log_tm = jastk "JS_Log"
val JS_If_tm = jastk "JS_If"
val JS_For_tm = jastk "JS_For"
val JS_Assign_tm = jastk "JS_Assign"
val JS_AnnAssign_tm = jastk "JS_AnnAssign"
val JS_AugAssign_tm = jastk "JS_AugAssign"
val JS_Append_tm = jastk "JS_Append"

fun mk_JS_Expr e = mk_comb(JS_Expr_tm, e)
fun mk_JS_Return eopt = mk_comb(JS_Return_tm, lift_option (mk_option json_expr_ty) I eopt)
fun mk_JS_Raise eopt = mk_comb(JS_Raise_tm, lift_option (mk_option json_expr_ty) I eopt)
fun mk_JS_Assert (test, msgopt) =
  list_mk_comb(JS_Assert_tm, [test, lift_option (mk_option json_expr_ty) I msgopt])
fun mk_JS_Log (nsid, args) =
  list_mk_comb(JS_Log_tm, [nsid, mk_list(args, json_expr_ty)])
fun mk_JS_If (test, body, els) =
  list_mk_comb(JS_If_tm, [test, mk_list(body, json_stmt_ty), mk_list(els, json_stmt_ty)])
fun mk_JS_For (var, ty, ann, iter, body) =
  list_mk_comb(JS_For_tm,
    [fromMLstring var, ty, ann, iter, mk_list(body, json_stmt_ty)])
fun mk_JS_Assign (tgt, v) = list_mk_comb(JS_Assign_tm, [tgt, v])
fun mk_JS_AnnAssign (var, ty, ann, v) =
  list_mk_comb(JS_AnnAssign_tm, [fromMLstring var, ty, ann, v])
fun mk_JS_AugAssign (tgt, op_tm, v) = list_mk_comb(JS_AugAssign_tm, [tgt, op_tm, v])
fun mk_JS_Append (tgt, v) = list_mk_comb(JS_Append_tm, [tgt, v])

(* ===== Iterator Constructors ===== *)

val JIter_Range_tm = jastk "JIter_Range"
val JIter_Array_tm = jastk "JIter_Array"

fun mk_JIter_Range (args, fvs, boundopt) =
  list_mk_comb(JIter_Range_tm,
    [args, fvs,
     lift_option (mk_option num) I boundopt])
fun mk_JIter_Array (e, ty) = list_mk_comb(JIter_Array_tm, [e, ty])

(* ===== Target Constructors ===== *)

val JBT_Name_tm = jastk "JBT_Name"
val JBT_TopLevelName_tm = jastk "JBT_TopLevelName"
val JBT_Subscript_tm = jastk "JBT_Subscript"
val JBT_Attribute_tm = jastk "JBT_Attribute"
val JTgt_Base_tm = jastk "JTgt_Base"
val JTgt_Tuple_tm = jastk "JTgt_Tuple"

fun mk_JBT_Name s = mk_comb(JBT_Name_tm, fromMLstring s)
fun mk_JBT_TopLevelName nsid = mk_comb(JBT_TopLevelName_tm, nsid)
fun mk_JBT_Subscript (bt, e) = list_mk_comb(JBT_Subscript_tm, [bt, e])
fun mk_JBT_Attribute (bt, attr) = list_mk_comb(JBT_Attribute_tm, [bt, fromMLstring attr])
fun mk_JTgt_Base bt = mk_comb(JTgt_Base_tm, bt)
fun mk_JTgt_Tuple ts = mk_comb(JTgt_Tuple_tm, mk_list(ts, json_target_ty))

(* ===== Top-level Constructors ===== *)

val JArg_tm = jastk "JArg"
val JFuncType_tm = jastk "JFuncType"
val JVT_Type_tm = jastk "JVT_Type"
val JVT_HashMap_tm = jastk "JVT_HashMap"
val JTL_FunctionDef_tm = jastk "JTL_FunctionDef"
val JTL_VariableDecl_tm = jastk "JTL_VariableDecl"
val JTL_HashMapDecl_tm = jastk "JTL_HashMapDecl"
val JTL_EventDef_tm = jastk "JTL_EventDef"
val JTL_StructDef_tm = jastk "JTL_StructDef"
val JTL_FlagDef_tm = jastk "JTL_FlagDef"
val JInterfaceFunc_tm = jastk "JInterfaceFunc"
val JTL_InterfaceDef_tm = jastk "JTL_InterfaceDef"
val JTL_Import_tm = jastk "JTL_Import"
val JTL_ExportsDecl_tm = jastk "JTL_ExportsDecl"
val JTL_InitializesDecl_tm = jastk "JTL_InitializesDecl"
val JTL_UsesDecl_tm = jastk "JTL_UsesDecl"
val JTL_ImplementsDecl_tm = jastk "JTL_ImplementsDecl"
val JImportInfo_tm = jastk "JImportInfo"
val JModule_tm = jastk "JModule"
val JImportedModule_tm = jastk "JImportedModule"
val JAnnotatedAST_tm = jastk "JAnnotatedAST"

fun mk_JArg (name, ty, ann) =
  list_mk_comb(JArg_tm, [fromMLstring name, ty, ann])
fun mk_JFuncType (argtys, retty) =
  list_mk_comb(JFuncType_tm, [mk_list(argtys, json_type_ty), retty])
fun mk_JVT_Type ty = mk_comb(JVT_Type_tm, ty)
fun mk_JVT_HashMap (kt, vt) = list_mk_comb(JVT_HashMap_tm, [kt, vt])
fun mk_JTL_FunctionDef (name, decs, args, defaults, func_type, ret_ann, body) =
  list_mk_comb(JTL_FunctionDef_tm,
    [fromMLstring name,
     mk_list(List.map fromMLstring decs, string_ty),
     mk_list(args, json_arg_ty),
     mk_list(defaults, json_expr_ty),
     func_type,
     ret_ann,
     mk_list(body, json_stmt_ty)])
fun mk_JTL_VariableDecl (name, ty, ann_ty, is_public, is_immutable, is_transient, valopt) =
  list_mk_comb(JTL_VariableDecl_tm,
    [fromMLstring name, ty, ann_ty, mk_bool is_public, mk_bool is_immutable,
     mk_bool is_transient, lift_option (mk_option json_expr_ty) I valopt])
fun mk_JTL_HashMapDecl (name, kt, vt, is_public, is_transient) =
  list_mk_comb(JTL_HashMapDecl_tm,
    [fromMLstring name, kt, vt, mk_bool is_public, mk_bool is_transient])
val event_arg_ty = pairSyntax.mk_prod(json_arg_ty, Type.bool)
fun mk_JTL_EventDef (name, args) =
  list_mk_comb(JTL_EventDef_tm, [fromMLstring name, mk_list(args, event_arg_ty)])
fun mk_JTL_StructDef (name, args) =
  list_mk_comb(JTL_StructDef_tm, [fromMLstring name, mk_list(args, json_arg_ty)])
fun mk_JTL_FlagDef (name, members) =
  list_mk_comb(JTL_FlagDef_tm,
    [fromMLstring name, mk_list(List.map fromMLstring members, string_ty)])
fun mk_JInterfaceFunc (name, args, ret_ty, decorators) =
  list_mk_comb(JInterfaceFunc_tm,
    [fromMLstring name,
     mk_list(args, json_arg_ty),
     ret_ty,
     mk_list(List.map fromMLstring decorators, string_ty)])
fun mk_JTL_InterfaceDef (name, funcs) =
  list_mk_comb(JTL_InterfaceDef_tm,
    [fromMLstring name, mk_list(funcs, json_interface_func_ty)])
fun mk_JImportInfo (alias, src_id, qual_name, resolved_path) =
  list_mk_comb(JImportInfo_tm,
    [fromMLstring alias, src_id, fromMLstring qual_name,
     fromMLstring resolved_path])
fun mk_JTL_Import infos =
  mk_comb(JTL_Import_tm, mk_list(infos, json_import_info_ty))
fun mk_JTL_ExportsDecl ann = mk_comb(JTL_ExportsDecl_tm, ann)
fun mk_JTL_InitializesDecl ann = mk_comb(JTL_InitializesDecl_tm, ann)
fun mk_JTL_UsesDecl ann = mk_comb(JTL_UsesDecl_tm, ann)
fun mk_JTL_ImplementsDecl ann = mk_comb(JTL_ImplementsDecl_tm, ann)
fun mk_JModule (src_id, nr_default, tls) =
  list_mk_comb(JModule_tm,
    [src_id, mk_bool nr_default, mk_list(tls, json_toplevel_ty)])
fun mk_JImportedModule (src_id_tm, path, resolved_path, nr_default, body) =
  list_mk_comb(JImportedModule_tm,
    [src_id_tm, fromMLstring path, fromMLstring resolved_path,
     mk_bool nr_default, mk_list(body, json_toplevel_ty)])
fun mk_JAnnotatedAST (main_ast, imports) =
  list_mk_comb(JAnnotatedAST_tm,
    [main_ast,
     mk_list(imports, mk_type("json_imported_module", []))])

(* ===== Decoder Helpers ===== *)

(* Helper to check a field equals a specific string *)
fun check cd pred err d =
  andThen cd (fn x => if pred x then d else fail err)

fun check_field lab req =
  check (field lab string) (fn s => s = req) (lab ^ " not " ^ req)

fun check_ast_type req = check_field "ast_type" req

fun achoose err ls = orElse(choose ls, fail err)

(* Convert ML int to HOL num term *)
fun mk_num_from_int n = numSyntax.mk_numeral (Arbnum.fromInt n)
fun mk_num_from_largeint n = numSyntax.mk_numeral (Arbnum.fromLargeInt (IntInf.toLarge n))

val numtm : term decoder = JSONDecode.map mk_num_from_largeint intInf

(* Convert ML int to HOL int term *)
val inttm : term decoder =
  JSONDecode.map (intSyntax.term_of_int o Arbint.fromLargeInt) intInf

(* Preserve whether declaration-source metadata was absent or explicitly
   supplied. Source ID interpretation belongs to jsonToVyper. *)
val JMissingSource_tm = jastk "JMissingSource"
val JExplicitSource_tm = jastk "JExplicitSource"

val source_ref_tm : term decoder =
  JSONDecode.map (fn src_id => mk_comb (JExplicitSource_tm, src_id)) inttm
(* ===== Type Decoders ===== *)

(* Decode typeclass string to constructor *)
(* Main type decoder - handles all json_type cases *)
fun d_json_type () : term decoder = achoose "json_type" [
  (* Integer: has typeclass "integer", bits and is_signed fields *)
  check (field "typeclass" string) (fn s => s = "integer") "not integer" $
    JSONDecode.map (fn (bits, is_signed) => mk_JT_Integer(bits, is_signed)) $
    tuple2 (field "bits" numtm, field "is_signed" bool),

  (* bytes_m: has typeclass "bytes_m" and m field *)
  check (field "typeclass" string) (fn s => s = "bytes_m") "not bytes_m" $
    JSONDecode.map mk_JT_BytesM (field "m" numtm),

  (* String: name = "String" with length *)
  check (field "name" string) (fn s => s = "String") "not String" $
    JSONDecode.map mk_JT_String (field "length" numtm),

  (* Bytes: name = "Bytes" with length *)
  check (field "name" string) (fn s => s = "Bytes") "not Bytes" $
    JSONDecode.map mk_JT_Bytes (field "length" numtm),

  (* Static array: typeclass = "static_array" or "$SArray" *)
  check (field "typeclass" string) (fn s => s = "static_array" orelse s = "$SArray") "not static_array" $
    JSONDecode.map (fn (vt, len) => mk_JT_StaticArray(vt, len)) $
    tuple2 (field "value_type" (delay d_json_type), field "length" numtm),

  (* Dynamic array: typeclass = "dynamic_array" or name = "DynArray" *)
  check (field "typeclass" string) (fn s => s = "dynamic_array") "not dynamic_array" $
    JSONDecode.map (fn (vt, len) => mk_JT_DynArray(vt, len)) $
    tuple2 (field "value_type" (delay d_json_type), field "length" numtm),

  check (field "name" string) (fn s => s = "DynArray") "not DynArray" $
    JSONDecode.map (fn (vt, len) => mk_JT_DynArray(vt, len)) $
    tuple2 (field "value_type" (delay d_json_type), field "length" numtm),

  (* Struct: typeclass = "struct" *)
  check (field "typeclass" string) (fn s => s = "struct") "not struct" $
    JSONDecode.map mk_JT_Struct $
    tuple2 (orElse (JSONDecode.map mk_some (field "type_decl_node" $ field "source_id" inttm),
                    succeed (mk_none intSyntax.int_ty)),
            field "name" string),

  (* Flag: typeclass = "flag" *)
  check (field "typeclass" string) (fn s => s = "flag") "not flag" $
    JSONDecode.map mk_JT_Flag $
    tuple2 (orElse (JSONDecode.map mk_some (field "type_decl_node" $ field "source_id" inttm),
                    succeed (mk_none intSyntax.int_ty)),
            field "name" string),

  (* Tuple: typeclass = "tuple" *)
  check (field "typeclass" string) (fn s => s = "tuple") "not tuple" $
    JSONDecode.map mk_JT_Tuple (field "member_types" (array (delay d_json_type))),

  (* HashMap: typeclass = "hashmap" *)
  check (field "typeclass" string) (fn s => s = "hashmap") "not hashmap" $
    JSONDecode.map (fn (kt, vt) => mk_JT_HashMap(kt, vt)) $
    tuple2 (field "key_type" (delay d_json_type), field "value_type" (delay d_json_type)),

  (* Interface *)
  check (field "typeclass" string) (fn s => s = "interface") "not interface" $
    JSONDecode.map mk_JT_Interface $
    tuple2 (orElse (JSONDecode.map mk_some
                      (field "type_decl_node" $ field "source_id" inttm),
                    succeed (mk_none intSyntax.int_ty)),
            field "name" string),

  (* Named types (bool, address, decimal, etc) - preserve type declaration source if present *)
  JSONDecode.map mk_JT_Named $
    tuple2 (orElse (JSONDecode.map mk_some (field "type_decl_node" $ field "source_id" inttm),
                    succeed (mk_none intSyntax.int_ty)),
            field "name" string),

  (* Null type *)
  null JT_None_tm
]

val json_type = delay d_json_type

fun d_qualified_type_path () : (string list * string) decoder =
  check_ast_type "Attribute" $
    JSONDecode.map (fn ((path, name), attr) => (path @ [name], attr)) $
      tuple2 (field "value" $ achoose "qualified type base" [
                check_ast_type "Name" $
                  JSONDecode.map (fn id => ([], id)) (field "id" string),
                delay d_qualified_type_path
              ],
              field "attr" string)

(* Array-like annotation bounds may be literal Int nodes or constant
   expressions carrying a compiler-provided folded Int value. *)
val annotation_bound : term decoder = achoose "annotation bound" [
  check_ast_type "Int" $ field "value" numtm,
  field "folded_value" $ check_ast_type "Int" $ field "value" numtm
]

(* Type from AST node (for subscript/name patterns) *)
fun d_ast_type () : term decoder = achoose "ast_type" [
  (* Name node - check id for primitive types *)
  check_ast_type "Name" $
  achoose "Name type" [
    (* uintN *)
    check (field "id" string) (String.isPrefix "uint") "not uint" $
      JSONDecode.map (fn s =>
        let val bits = Option.valOf (Int.fromString (String.extract(s, 4, NONE)))
        in mk_JTA_Integer(mk_num_from_int bits, false) end) $
      field "id" string,
    (* intN *)
    check (field "id" string) (String.isPrefix "int") "not int" $
      JSONDecode.map (fn s =>
        let val bits = Option.valOf (Int.fromString (String.extract(s, 3, NONE)))
        in mk_JTA_Integer(mk_num_from_int bits, true) end) $
      field "id" string,
    (* bytesN (fixed) *)
    check (field "id" string) (String.isPrefix "bytes") "not bytes" $
      JSONDecode.map (fn s =>
        let val m = Option.valOf (Int.fromString (String.extract(s, 5, NONE)))
        in mk_JTA_BytesM(mk_num_from_int m) end) $
      field "id" string,
    (* Named types *)
    JSONDecode.map (fn s => mk_JTA_Named s) (field "id" string)
  ],

  (* Subscript node - for String[N], Bytes[N], DynArray[T, N], etc. *)
  check_ast_type "Subscript" $
  achoose "Subscript type" [
    (* String[N] *)
    check (field "value" (check_ast_type "Name" $ field "id" string))
          (fn s => s = "String") "not String" $
    JSONDecode.map mk_JTA_String $
      field "slice" annotation_bound,

    (* Bytes[N] *)
    check (field "value" (check_ast_type "Name" $ field "id" string))
          (fn s => s = "Bytes") "not Bytes" $
    JSONDecode.map mk_JTA_Bytes $
      field "slice" annotation_bound,

    (* DynArray[T, N] *)
    check (field "value" (check_ast_type "Name" $ field "id" string))
          (fn s => s = "DynArray") "not DynArray" $
    JSONDecode.map (fn (vt, len) => mk_JTA_DynArray(vt, len)) $
    field "slice" $ check_ast_type "Tuple" $ field "elements" $
      tuple2 (sub 0 (delay d_ast_type),
              sub 1 annotation_bound),

    (* Static array T[N] *)
    JSONDecode.map (fn (vt, len) => mk_JTA_StaticArray(vt, len)) $
    tuple2 (field "value" (delay d_ast_type),
            field "slice" annotation_bound)
  ],

  (* Tuple type *)
  check_ast_type "Tuple" $
    JSONDecode.map mk_JTA_Tuple $
    field "elements" (array (delay d_ast_type)),

  (* indexed(...) call - unwrap the inner type *)
  check_ast_type "Call" $
    check (field "func" (tuple2 (field "ast_type" string, field "id" string)))
          (fn p => p = ("Name", "indexed")) "not indexed" $
    field "args" $ sub 0 (delay d_ast_type),

  (* Attribute node - syntactic qualified type reference: library.SomeStruct, lib1.Roles *)
  JSONDecode.map (fn (path, name) => mk_JTA_Qualified(path, name)) $
    d_qualified_type_path (),

  (* null type *)
  null JTA_None_tm
]

val ast_type = delay d_ast_type

(* ===== Operator Decoders ===== *)

val json_binop : term decoder = achoose "binop" [
  check_ast_type "Add" $ succeed JBop_Add_tm,
  check_ast_type "Sub" $ succeed JBop_Sub_tm,
  check_ast_type "Mult" $ succeed JBop_Mult_tm,
  check_ast_type "Div" $ succeed JBop_Div_tm,
  check_ast_type "FloorDiv" $ succeed JBop_FloorDiv_tm,
  check_ast_type "Mod" $ succeed JBop_Mod_tm,
  check_ast_type "Pow" $ succeed JBop_Pow_tm,
  check_ast_type "And" $ succeed JBop_And_tm,
  check_ast_type "Or" $ succeed JBop_Or_tm,
  check_ast_type "BitAnd" $ succeed JBop_BitAnd_tm,
  check_ast_type "BitOr" $ succeed JBop_BitOr_tm,
  check_ast_type "BitXor" $ succeed JBop_BitXor_tm,
  check_ast_type "LShift" $ succeed JBop_LShift_tm,
  check_ast_type "RShift" $ succeed JBop_RShift_tm,
  check_ast_type "Eq" $ succeed JBop_Eq_tm,
  check_ast_type "NotEq" $ succeed JBop_NotEq_tm,
  check_ast_type "Lt" $ succeed JBop_Lt_tm,
  check_ast_type "LtE" $ succeed JBop_LtE_tm,
  check_ast_type "Gt" $ succeed JBop_Gt_tm,
  check_ast_type "GtE" $ succeed JBop_GtE_tm,
  check_ast_type "In" $ succeed JBop_In_tm,
  check_ast_type "NotIn" $ succeed JBop_NotIn_tm
]

val json_unaryop : term decoder = achoose "unaryop" [
  check_ast_type "USub" $ succeed JUop_USub_tm,
  check_ast_type "Not" $ succeed JUop_Not_tm,
  check_ast_type "Invert" $ succeed JUop_Invert_tm
]

val json_boolop : term decoder = achoose "boolop" [
  check_ast_type "And" $ succeed JBoolop_And_tm,
  check_ast_type "Or" $ succeed JBoolop_Or_tm
]

(* ===== Expression Decoder ===== *)

fun d_json_expr () : term decoder = achoose "expr" [
  (* Int literal - type may be absent for array indices/sizes *)
  check_ast_type "Int" $
    JSONDecode.map (fn (v, ty) => mk_JE_Int(v, ty)) $
    tuple2 (field "value" inttm,
            orElse(field "type" json_type, succeed JT_None_tm)),

  (* Decimal literal *)
  check_ast_type "Decimal" $
    JSONDecode.map mk_JE_Decimal (field "value" string),

  (* Generic string literal (e.g. method_id argument) - no length in type *)
  check_ast_type "Str" $
    check (field "type" $ field "generic" string) (fn s => s = "string") "not generic string" $
    JSONDecode.map mk_JE_GenericStr (field "value" string),

  (* String literal *)
  check_ast_type "Str" $
    JSONDecode.map (fn (len, v) => mk_JE_Str(len, v)) $
    tuple2 (field "type" (field "length" numtm), field "value" string),

  (* Bytes/HexBytes literal *)
  check (field "ast_type" string)
        (fn s => s = "Bytes" orelse s = "HexBytes") "not bytes" $
    JSONDecode.map (fn (len, v) => mk_JE_Bytes(len, v)) $
    tuple2 (field "type" (check (field "name" string) (fn s => s = "Bytes") "not Bytes type" $
                          field "length" numtm),
            field "value" string),

  (* Hex literal: preserve the compiler type, including address. *)
  check_ast_type "Hex" $
    JSONDecode.map mk_JE_Hex $
    tuple2 (field "value" string,
            orElse (field "type" json_type, succeed JT_None_tm)),

  (* Bool literal (NameConstant) *)
  check_ast_type "NameConstant" $
    JSONDecode.map mk_JE_Bool (field "value" bool),

  (* Ellipsis - appears in .vyi interface stub function bodies *)
  check_ast_type "Ellipsis" $ succeed JE_Ellipsis_tm,

  (* Name - preserve the original reference alongside any compiler-provided
     folded value. jsonToVyper decides which expression to lower. *)
  check_ast_type "Name" $
    JSONDecode.map
      (fn (original, folded_opt) =>
        case folded_opt of
          NONE => original
        | SOME folded => mk_JE_Folded (original, folded)) $
    tuple2 (
      JSONDecode.map
        (fn ((id, (tc, src_id_opt)), ty) =>
          mk_JE_Name(id, tc, src_id_opt, ty)) $
      tuple2 (tuple2 (field "id" string,
              tuple2 (try (orElse (field "type" $ field "typeclass" string,
                                  field "type" $ field "type_t" $ field "typeclass" string)),
                      orElse (field "type" $ field "type_decl_node" $ field "source_id" source_ref_tm,
                              orElse (field "type" $ field "type_t" $ field "type_decl_node" $ field "source_id" source_ref_tm,
                              succeed JMissingSource_tm)))),
              orElse(field "type" json_type, succeed JT_None_tm)),
      try (field "folded_value" $ achoose "folded Name value" [
        check_ast_type "NameConstant" $
          JSONDecode.map mk_JE_Bool (field "value" bool),
        check_ast_type "Int" $
          JSONDecode.map (fn (v, ty) => mk_JE_Int(v, ty)) $
          tuple2 (field "value" inttm,
                  orElse(field "type" json_type, succeed JT_None_tm))
      ])),

  (* Attribute - extract result typeclass, base_type_name, base_typeclass, source_id, and type *)
  (* source_id comes from variable_reads[0].decl_node.source_id OR type.type_decl_node.source_id *)
  (* base_type_name comes from value.type.name - used to distinguish address.code from struct.code *)
  (* base_typeclass comes from value.type.typeclass - used to distinguish interface.address from struct.address *)
  check_ast_type "Attribute" $
    JSONDecode.map (fn ((((((e, attr), tc_opt), base_ty_name_opt), base_tc_opt), src_id_opt), ty) => mk_JE_Attribute(e, attr, tc_opt, base_ty_name_opt, base_tc_opt, src_id_opt, ty)) $
    tuple2 (tuple2 (tuple2 (tuple2 (tuple2 (tuple2 (field "value" (delay d_json_expr), field "attr" string),
                    try (orElse (field "type" $ field "typeclass" string,
                                field "type" $ field "type_t" $ field "typeclass" string))),
            try (field "value" $ field "type" $ field "name" string)),
            try (field "value" $ field "type" $ field "typeclass" string)),
            orElse (field "variable_reads" $ sub 0 $
                              field "decl_node" $ field "source_id" source_ref_tm,
                    orElse (field "type" $ field "type_decl_node" $ field "source_id" source_ref_tm,
                            succeed JMissingSource_tm))),
            orElse(field "type" json_type, succeed JT_None_tm)),

  (* Subscript *)
  check_ast_type "Subscript" $
    JSONDecode.map (fn ((e1, e2), ty) => mk_JE_Subscript(e1, e2, ty)) $
    tuple2 (tuple2 (field "value" (delay d_json_expr), field "slice" (delay d_json_expr)),
            orElse(field "type" json_type, succeed JT_None_tm)),

  (* NamedExpr - dependency binding in initializes: lib[dep := dep] *)
  check_ast_type "NamedExpr" $
    JSONDecode.map (fn (e1, e2) => mk_JE_NamedExpr(e1, e2)) $
    tuple2 (field "target" (delay d_json_expr), field "value" (delay d_json_expr)),

  (* BinOp *)
  check_ast_type "BinOp" $
    JSONDecode.map (fn ((l, op_tm, r), ty) => mk_JE_BinOp(l, op_tm, r, ty)) $
    tuple2 (tuple3 (field "left" (delay d_json_expr),
            field "op" json_binop,
            field "right" (delay d_json_expr)),
            orElse(field "type" json_type, succeed JT_None_tm)),

  (* Compare *)
  check_ast_type "Compare" $
    JSONDecode.map (fn (l, op_tm, r) => mk_JE_Compare(l, op_tm, r)) $
    tuple3 (field "left" (delay d_json_expr),
            field "op" json_binop,
            field "right" (delay d_json_expr)),

  (* BoolOp *)
  check_ast_type "BoolOp" $
    JSONDecode.map (fn (op_tm, es) => mk_JE_BoolOp(op_tm, es)) $
    tuple2 (field "op" json_boolop,
            field "values" (array (delay d_json_expr))),

  (* UnaryOp *)
  check_ast_type "UnaryOp" $
    JSONDecode.map (fn ((op_tm, e), ty) => mk_JE_UnaryOp(op_tm, e, ty)) $
    tuple2 (tuple2 (field "op" json_unaryop,
            field "operand" (delay d_json_expr)),
            orElse(field "type" json_type, succeed JT_None_tm)),

  (* IfExp *)
  check_ast_type "IfExp" $
    JSONDecode.map (fn ((test, body, els), ty) => mk_JE_IfExp(test, body, els, ty)) $
    tuple2 (tuple3 (field "test" (delay d_json_expr),
            field "body" (delay d_json_expr),
            field "orelse" (delay d_json_expr)),
            orElse(field "type" json_type, succeed JT_None_tm)),

  (* Tuple *)
  check_ast_type "Tuple" $
    JSONDecode.map mk_JE_Tuple (field "elements" (array (delay d_json_expr))),

  (* List *)
  check_ast_type "List" $
    JSONDecode.map (fn (es, ty) => mk_JE_List(es, ty)) $
    tuple2 (field "elements" (array (delay d_json_expr)),
            field "type" json_type),

  (* Call - preserve any explicit declaration source ID from the function
     metadata; jsonToVyper interprets source IDs. *)
  check_ast_type "Call" $
    JSONDecode.map (fn ((func, args, kwargs), (ty, src_id_opt)) => mk_JE_Call(func, args, kwargs, ty, src_id_opt)) $
    tuple2 (tuple3 (field "func" (delay d_json_expr),
                    field "args" (array (delay d_json_expr)),
                    orElse(field "keywords" (array (delay d_json_keyword)), succeed [])),
            tuple2 ((* type field may be missing or null *)
                    orElse (field "type" json_type, succeed JT_None_tm),
                    orElse (field "func" $ field "type" $ field "type_decl_node" $ field "source_id" source_ref_tm,
                            succeed JMissingSource_tm))),

  (* ExtCall - preserve target separately from ordinary arguments. *)
  (* Signature extracted from func.type: argument_types, return_type *)
  check_ast_type "ExtCall" $
    JSONDecode.map (fn ((((func_name, func_src), arg_types), (ret_ty, (target, args))), keywords) =>
      mk_JE_ExtCall(func_name, func_src, arg_types, ret_ty, target, args, keywords)) $
    tuple2 (tuple2 (tuple2 (tuple2 (field "value" $ field "func" $ field "attr" string,
                                    orElse (field "value" $ field "func" $ field "type" $
                                      field "type_decl_node" $ field "source_id" source_ref_tm,
                                      succeed JMissingSource_tm)),
                            field "value" $ field "func" $ field "type" $
                              orElse (field "argument_types" (array json_type), succeed [])),
                    tuple2 (field "value" $ field "func" $ field "type" $
                              orElse (field "return_type" json_type, succeed JT_None_tm),
                            tuple2 (field "value" $ field "func" $ field "value" (delay d_json_expr),
                                    field "value" $ field "args" (array (delay d_json_expr))))),
            field "value" $ orElse (field "keywords" (array (delay d_json_keyword)), succeed [])),

  (* StaticCall - same structure as ExtCall. *)
  check_ast_type "StaticCall" $
    JSONDecode.map (fn (((func_name, func_src), arg_types), (ret_ty, (target, args))) =>
      mk_JE_StaticCall(func_name, func_src, arg_types, ret_ty, target, args)) $
    tuple2 (tuple2 (tuple2 (field "value" $ field "func" $ field "attr" string,
                            orElse (field "value" $ field "func" $ field "type" $
                              field "type_decl_node" $ field "source_id" source_ref_tm,
                              succeed JMissingSource_tm)),
                    field "value" $ field "func" $ field "type" $
                      orElse (field "argument_types" (array json_type), succeed [])),
            tuple2 (field "value" $ field "func" $ field "type" $
                      orElse (field "return_type" json_type, succeed JT_None_tm),
                    tuple2 (field "value" $ field "func" $ field "value" (delay d_json_expr),
                            field "value" $ field "args" (array (delay d_json_expr)))))
]
and d_json_keyword () : term decoder =
  JSONDecode.map (fn (arg, v) => mk_JKeyword(arg, v)) $
  tuple2 (field "arg" string, field "value" (delay d_json_expr))

val json_expr = delay d_json_expr
val json_keyword = delay d_json_keyword

(* ===== Target Decoders ===== *)

fun d_json_base_target () : term decoder = achoose "base_target" [
  (* self.x -> TopLevelName with source_id from variable_writes or variable_reads *)
  check_ast_type "Attribute" $
    check (field "value" (tuple2 (field "ast_type" string, field "id" string)))
          (fn p => p = ("Name", "self")) "not self" $
    JSONDecode.map (fn (attr, src_id_opt) => mk_JBT_TopLevelName (mk_nsid (src_id_opt, attr)))
      (tuple2 (field "attr" string,
               orElse (field "variable_writes" $ sub 0 $
                         field "decl_node" $ field "source_id" source_ref_tm,
                       orElse (field "variable_reads" $ sub 0 $
                                 field "decl_node" $ field "source_id" source_ref_tm,
                               succeed JMissingSource_tm)))),

  (* module.x (lib1.counter) -> TopLevelName with source_id from type.type_decl_node *)
  check_ast_type "Attribute" $
    check (field "value" $ field "type" $ field "typeclass" string)
          (fn tc => tc = "module") "not module" $
    JSONDecode.map (fn (attr, src_id_opt) => mk_JBT_TopLevelName (mk_nsid (src_id_opt, attr)))
      (tuple2 (field "attr" string,
               orElse (field "value" $ field "type" $
                         field "type_decl_node" $ field "source_id" source_ref_tm,
                       succeed JMissingSource_tm))),

  (* Name *)
  check_ast_type "Name" $
    JSONDecode.map mk_JBT_Name (field "id" string),

  (* Attribute (non-self, non-module) *)
  check_ast_type "Attribute" $
    JSONDecode.map (fn (bt, attr) => mk_JBT_Attribute(bt, attr)) $
    tuple2 (field "value" (delay d_json_base_target), field "attr" string),

  (* Subscript *)
  check_ast_type "Subscript" $
    JSONDecode.map (fn (bt, e) => mk_JBT_Subscript(bt, e)) $
    tuple2 (field "value" (delay d_json_base_target), field "slice" json_expr)
]

val json_base_target = delay d_json_base_target

fun d_json_target () : term decoder = achoose "target" [
  (* Tuple target *)
  check_ast_type "Tuple" $
    JSONDecode.map mk_JTgt_Tuple (field "elements" (array (delay d_json_target))),

  (* Base target *)
  JSONDecode.map mk_JTgt_Base json_base_target
]

val json_target = delay d_json_target

(* ===== Iterator Decoder ===== *)

(* Internal representation for iterator parsing *)
datatype iter_parse = RangeParse of term list * term list * term option | ArrayParse of term * term

val json_iter_internal : iter_parse decoder = achoose "iter" [
  (* range(...) call *)
  check_ast_type "Call" $
    check (field "func" (field "id" string)) (fn s => s = "range") "not range" $
    achoose "range variants" [
      (* range with explicit bound keyword *)
      check (field "keywords" $ sub 0 $ field "arg" string) (fn s => s = "bound") "not bounded" $
      JSONDecode.map (fn (args, bound) => RangeParse(args, [], SOME bound)) $
      tuple2 (field "args" (array json_expr),
              field "keywords" $ sub 0 $ field "value" $
                achoose "bound value" [
                  field "folded_value" $ field "value" numtm,
                  field "value" numtm
                ]),
      (* range without explicit bound - also extract folded_value integers for bound computation *)
      JSONDecode.map (fn (args, fvs) => RangeParse(args, fvs, NONE)) $
      tuple2 (field "args" (array json_expr),
              field "args" (array (
                orElse(
                  JSONDecode.map mk_some (field "folded_value" $ check_ast_type "Int" $ field "value" inttm),
                  succeed (mk_none intSyntax.int_ty)))))
    ],

  (* Array iteration *)
  JSONDecode.map (fn (e, ty) => ArrayParse(e, ty)) $
  tuple2 (json_expr, field "type" json_type)
]

fun iter_parse_to_term (RangeParse(args, fvs, boundopt)) =
      mk_JIter_Range(mk_list(args, json_expr_ty),
                      mk_list(fvs, mk_option intSyntax.int_ty),
                      boundopt)
  | iter_parse_to_term (ArrayParse(e, ty)) =
      mk_JIter_Array(e, ty)

(* ===== Statement Decoder ===== *)

fun d_json_stmt () : term decoder = achoose "stmt" [
  check_ast_type "Pass" $ succeed JS_Pass_tm,
  check_ast_type "Break" $ succeed JS_Break_tm,
  check_ast_type "Continue" $ succeed JS_Continue_tm,

  (* Expr (including append which shows up as Call inside Expr) *)
  check_ast_type "Expr" $
    field "value" $
    achoose "expr stmt" [
      (* append call *)
      check_ast_type "Call" $
        check (field "func" $ field "type" $ tuple2 (field "name" string, field "typeclass" string))
              (fn p => p = ("append", "member_function")) "not append" $
        JSONDecode.map (fn (tgt, e) => mk_JS_Append(tgt, e)) $
        tuple2 (field "func" $ field "value" json_base_target,
                field "args" $ sub 0 json_expr),
      (* other expression statement *)
      JSONDecode.map mk_JS_Expr json_expr
    ],

  (* Return *)
  check_ast_type "Return" $
    JSONDecode.map mk_JS_Return (field "value" (nullable json_expr)),

  (* Raise *)
  check_ast_type "Raise" $
    JSONDecode.map mk_JS_Raise (field "exc" (nullable json_expr)),

  (* Assert *)
  check_ast_type "Assert" $
    JSONDecode.map (fn (test, msg) => mk_JS_Assert(test, msg)) $
    tuple2 (field "test" json_expr, field "msg" (nullable json_expr)),

  (* Log - extract source_id from event type for module events *)
  check_ast_type "Log" $
    field "value" $
    check_ast_type "Call" $
    JSONDecode.map
      (fn ((name, src_id_opt), (keywords, args)) =>
        mk_JS_Log(mk_nsid(src_id_opt, name),
                  if List.null keywords then args else keywords)) $
    tuple2 (field "func" $ achoose "log func" [
              (* Same-module event: log MyEvent(...) *)
              check_ast_type "Name" $
              tuple2 (field "id" string,
                      orElse (field "type" $ field "type_decl_node" $ field "source_id" source_ref_tm,
                              succeed JMissingSource_tm)),
              (* Cross-module event: log lib1.MyEvent(...) *)
              check_ast_type "Attribute" $
              tuple2 (field "attr" string,
                      orElse (field "value" $ field "type" $
                                field "type_decl_node" $ field "source_id" source_ref_tm,
                              succeed JMissingSource_tm))],
            tuple2
              (field "keywords" (array (field "value" json_expr)),
               field "args" (array json_expr))),

  (* If *)
  check_ast_type "If" $
    JSONDecode.map (fn (test, body, els) => mk_JS_If(test, body, els)) $
    tuple3 (field "test" json_expr,
            field "body" (array (delay d_json_stmt)),
            field "orelse" (array (delay d_json_stmt))),

  (* For *)
  check_ast_type "For" $
    JSONDecode.map (fn ((var, (varty, ann)), iter_parsed, body) =>
      mk_JS_For(var, varty, ann, iter_parse_to_term iter_parsed, body)) $
    tuple3 (field "target" $ check_ast_type "AnnAssign" $
              tuple2 (field "target" $ check_ast_type "Name" $ field "id" string,
                      tuple2 (
                        orElse (field "target" $ field "type" json_type,
                                succeed JT_None_tm),
                        orElse (field "annotation" ast_type,
                                succeed JTA_None_tm))),
            field "iter" json_iter_internal,
            field "body" (array (delay d_json_stmt))),

  (* AugAssign *)
  check_ast_type "AugAssign" $
    JSONDecode.map (fn (tgt, op_tm, v) => mk_JS_AugAssign(tgt, op_tm, v)) $
    tuple3 (field "target" json_base_target,
            field "op" json_binop,
            field "value" json_expr),

  (* AnnAssign *)
  check_ast_type "AnnAssign" $
    JSONDecode.map (fn (var, ty, ann, v) =>
      mk_JS_AnnAssign(var, ty, ann, v)) $
    tuple4 (field "target" $ check_ast_type "Name" $ field "id" string,
            orElse (field "target" $ field "type" json_type,
                    succeed JT_None_tm),
            orElse (field "annotation" ast_type, succeed JTA_None_tm),
            field "value" json_expr),

  (* Assign *)
  check_ast_type "Assign" $
    JSONDecode.map (fn (tgt, v) => mk_JS_Assign(tgt, v)) $
    tuple2 (field "target" json_target, field "value" json_expr)
]

val json_stmt = delay d_json_stmt

(* ===== Value Type Decoder (for HashMaps) ===== *)

fun d_json_value_type () : term decoder = achoose "value_type" [
  (* Nested hashmap *)
  check (field "typeclass" string) (fn s => s = "hashmap") "not hashmap" $
    JSONDecode.map (fn (kt, vt) => mk_JVT_HashMap(kt, vt)) $
    tuple2 (field "key_type" json_type, field "value_type" (delay d_json_value_type)),

  (* Regular type *)
  JSONDecode.map mk_JVT_Type json_type
]

val json_value_type = delay d_json_value_type

(* ===== Top-level Decoder ===== *)

val json_arg : term decoder = achoose "json_arg" [
  (* New format: ast_type = "arg". *)
  check_ast_type "arg" $
    JSONDecode.map (fn (name, ty, ann) => mk_JArg(name, ty, ann)) $
    tuple3 (field "arg" string,
            orElse (field "type" json_type, succeed JT_None_tm),
            orElse (field "annotation" ast_type, succeed JTA_None_tm)),
  (* Old format: ast_type = "AnnAssign" with nested target. *)
  check_ast_type "AnnAssign" $
    JSONDecode.map (fn (name, ty, ann) => mk_JArg(name, ty, ann)) $
    tuple3 (field "target" $ check_ast_type "Name" $ field "id" string,
            orElse (field "target" $ field "type" json_type,
                    succeed JT_None_tm),
            orElse (field "annotation" ast_type, succeed JTA_None_tm))
]

val json_func_type : term decoder =
  JSONDecode.map (fn (argtys, retty) => mk_JFuncType(argtys, retty)) $
  tuple2 (field "argument_types" (array json_type),
          field "return_type" json_type)

(* Decorator name decoder: handles both Name nodes (e.g., @external)
   and Call nodes (e.g., @override(module_name)).
   Name: {"ast_type": "Name", "id": "external"}
   Call: {"ast_type": "Call", "func": {"id": "override"}, ...} *)
val decorator_name : string decoder =
  orElse (field "id" string,
          field "func" $ field "id" string)

(* Interface function signature parser
 * Parses FunctionDef nodes within InterfaceDef body.
 * Mutability comes from either decorator_list or body (as Expr > Name > id).
 *)
val json_interface_func : term decoder =
  check_ast_type "FunctionDef" $
  JSONDecode.map (fn (name, args, ret_ty, (decs, body_decs)) =>
    mk_JInterfaceFunc(name, args, ret_ty, decs @ body_decs)) $
  tuple4 (
    field "name" string,
    field "args" $ check_ast_type "arguments" $
      field "args" (array json_arg),
    (* returns can be null *)
    orElse(field "returns" ast_type, succeed JTA_None_tm),
    (* decorators from decorator_list and/or body *)
    tuple2 (
      orElse(field "decorator_list" (array decorator_name), succeed []),
      (* body may contain mutability as Expr > Name > id (e.g., "view", "payable") *)
      orElse(field "body" (array (
        check_ast_type "Expr" $
        field "value" $
        check_ast_type "Name" $
        field "id" string)), succeed [])
    )
  )

val json_toplevel : term decoder = achoose "toplevel" [
  (* FunctionDef *)
  check_ast_type "FunctionDef" $
    JSONDecode.map (fn ((n, d), (((a, df), f), ret_ann), b) =>
      mk_JTL_FunctionDef(n, d, a, df, f, ret_ann, b)) $
    tuple3 (
      tuple2 (field "name" string,
              field "decorator_list" (array decorator_name)),
      tuple2 (tuple2 (field "args" $ check_ast_type "arguments" $
                        tuple2 (field "args" (array json_arg),
                                orElse(field "defaults" (array json_expr), succeed [])),
                      field "func_type" json_func_type),
              orElse(field "returns" ast_type, succeed JTA_None_tm)),
      field "body" (array json_stmt)
    ),

  (* VariableDecl for HashMaps *)
  check_ast_type "VariableDecl" $
    check (field "target" $ field "type" $ field "typeclass" string)
          (fn s => s = "hashmap") "not hashmap" $
    JSONDecode.map (fn (n, k, (v, p), t) =>
      mk_JTL_HashMapDecl(n, k, v, p, t)) $
    tuple4 (
      field "target" $ check_ast_type "Name" $ field "id" string,
      field "target" $ field "type" $ field "key_type" json_type,
      tuple2 (
        field "target" $ field "type" $ field "value_type" json_value_type,
        field "is_public" bool
      ),
      field "is_transient" bool
    ),

  (* VariableDecl (non-hashmap) *)
  check_ast_type "VariableDecl" $
    JSONDecode.map (fn ((n, t), ann_ty, (p, i), (tr, v)) =>
      mk_JTL_VariableDecl(n, t, ann_ty, p, i, tr, v)) $
    tuple4 (
      tuple2 (
        field "target" $ check_ast_type "Name" $ field "id" string,
        field "target" $ field "type" json_type
      ),
      orElse(field "annotation" ast_type, succeed JTA_None_tm),
      tuple2 (field "is_public" bool, field "is_immutable" bool),
      tuple2 (
        field "is_transient" bool,
        andThen (field "is_constant" bool) (fn is_const =>
          if is_const
          then JSONDecode.map SOME (field "value" json_expr)
          else succeed NONE)
      )
    ),

  (* EventDef — detect indexed(type) annotations *)
  let
    (* An event arg is an AnnAssign where the annotation may be
       indexed(type), i.e. a Call node with func.id = "indexed".
       In that case, the actual type is the first arg of the Call. *)
    val json_event_arg : term decoder = achoose "json_event_arg" [
      (* New format: ast_type = "arg" *)
      check_ast_type "arg" $
        orElse(
          (* indexed: annotation is Call to "indexed" *)
          JSONDecode.map (fn (name, ty, ann) =>
            pairSyntax.mk_pair(mk_JArg(name, ty, ann), boolSyntax.T)) $
          tuple3 (field "arg" string,
                  orElse (field "type" json_type, succeed JT_None_tm),
                  field "annotation" $
                    check_ast_type "Call" $
                      andThen (field "func" $ check_ast_type "Name" $
                               field "id" string)
                        (fn f => if f = "indexed"
                                 then field "args" $ sub 0 ast_type
                                 else fail "not indexed")),
          (* non-indexed: bare annotation *)
          JSONDecode.map (fn (name, ty, ann) =>
            pairSyntax.mk_pair(mk_JArg(name, ty, ann), boolSyntax.F)) $
          tuple3 (field "arg" string,
                  orElse (field "type" json_type, succeed JT_None_tm),
                  field "annotation" ast_type)),
      (* Old format: ast_type = "AnnAssign" *)
      check_ast_type "AnnAssign" $
        orElse(
          (* indexed *)
          JSONDecode.map (fn (name, ty, ann) =>
            pairSyntax.mk_pair(mk_JArg(name, ty, ann), boolSyntax.T)) $
          tuple3 (field "target" $ check_ast_type "Name" $ field "id" string,
                  orElse (field "target" $ field "type" json_type,
                          succeed JT_None_tm),
                  field "annotation" $
                    check_ast_type "Call" $
                      andThen (field "func" $ check_ast_type "Name" $
                               field "id" string)
                        (fn f => if f = "indexed"
                                 then field "args" $ sub 0 ast_type
                                 else fail "not indexed")),
          (* non-indexed *)
          JSONDecode.map (fn (name, ty, ann) =>
            pairSyntax.mk_pair(mk_JArg(name, ty, ann), boolSyntax.F)) $
          tuple3 (field "target" $ check_ast_type "Name" $ field "id" string,
                  orElse (field "target" $ field "type" json_type,
                          succeed JT_None_tm),
                  field "annotation" ast_type))
    ]
  in
  check_ast_type "EventDef" $
    JSONDecode.map (fn (name, args) => mk_JTL_EventDef(name, args)) $
    tuple2 (field "name" string,
            field "body" $ orElse(
              array json_event_arg,
              sub 0 (check_ast_type "Pass" (succeed []))))
  end,

  (* StructDef *)
  check_ast_type "StructDef" $
    JSONDecode.map (fn (name, args) => mk_JTL_StructDef(name, args)) $
    tuple2 (field "name" string, field "body" (array json_arg)),

  (* FlagDef *)
  check_ast_type "FlagDef" $
    JSONDecode.map (fn (name, members) => mk_JTL_FlagDef(name, members)) $
    tuple2 (field "name" string,
            field "body" $ array $
              check_ast_type "Expr" $
              field "value" $
              check_ast_type "Name" $
              field "id" string),

  (* InterfaceDef - parse name and function signatures *)
  check_ast_type "InterfaceDef" $
    JSONDecode.map (fn (name, funcs) => mk_JTL_InterfaceDef(name, funcs)) $
    tuple2 (field "name" string,
            field "body" (array json_interface_func)),

  (* Import - module import statement *)
  check_ast_type "Import" $
    JSONDecode.map mk_JTL_Import $
    field "import_infos" $ array $
      JSONDecode.map mk_JImportInfo $
      tuple4 (field "alias" string,
              field "source_id" inttm,
              field "qualified_module_name" string,
              field "resolved_path" string),

  (* ImportFrom - from X import Y statement *)
  check_ast_type "ImportFrom" $
    JSONDecode.map mk_JTL_Import $
    field "import_infos" $ array $
      JSONDecode.map mk_JImportInfo $
      tuple4 (field "alias" string,
              field "source_id" inttm,
              field "qualified_module_name" string,
              field "resolved_path" string),

  (* ExportsDecl - exports declaration *)
  check_ast_type "ExportsDecl" $
    JSONDecode.map mk_JTL_ExportsDecl $
    field "annotation" json_expr,

  (* InitializesDecl - initializes declaration *)
  check_ast_type "InitializesDecl" $
    JSONDecode.map mk_JTL_InitializesDecl $
    field "annotation" json_expr,

  (* UsesDecl - uses declaration *)
  check_ast_type "UsesDecl" $
    JSONDecode.map mk_JTL_UsesDecl $
    field "annotation" json_expr,

  (* ImplementsDecl - implements declaration *)
  check_ast_type "ImplementsDecl" $
    JSONDecode.map mk_JTL_ImplementsDecl $
    field "children" $ sub 0 json_expr
]

(* ===== Module Decoder ===== *)

val nonreentrancy_by_default : bool decoder =
  orElse (field "settings" $ field "nonreentrancy_by_default" bool,
          succeed false)

val json_module : term decoder =
  JSONDecode.map (fn (src_id, nr, body) => mk_JModule(src_id, nr, body)) $
  tuple3 (orElse (field "source_id" inttm,
                  succeed (intSyntax.term_of_int (Arbint.fromInt ~1))),
          nonreentrancy_by_default,
          field "body" (array json_toplevel))

(* ===== Imported Module Decoder ===== *)
(* Decoder for imported modules from the imports array *)

val json_imported_module : term decoder =
  JSONDecode.map (fn ((src_id, path, resolved_path, nr), body) =>
    mk_JImportedModule(src_id, path, resolved_path, nr, body)) $
  tuple2 (tuple4 (field "source_id" inttm,
                  field "path" string,
                  field "resolved_path" string,
                  nonreentrancy_by_default),
          field "body" (array json_toplevel))

(* Parse raw Vyper `-f annotated_ast` output. *)
(* Returns JAnnotatedAST with main module and list of imported modules. *)
val annotated_ast : term decoder =
  JSONDecode.map mk_JAnnotatedAST $
  tuple2 (field "ast" json_module,
          orElse (field "imports" (array json_imported_module), succeed []))

(* Parse an object containing an annotated_ast field, as used by Vyper's
   exported deployment traces. *)
val wrapped_annotated_ast : term decoder =
  field "annotated_ast" annotated_ast

(* ===== Storage Layout ===== *)

val storage_slot_info_ty = jasty "storage_slot_info"
val code_slot_info_ty = jasty "code_slot_info"
val json_storage_layout_ty = jasty "json_storage_layout"

(* Record constructors - use TypeBase for record syntax *)
fun mk_storage_slot_info (slot, n_slots, type_str) =
  let
    val reccon = TypeBase.mk_record (storage_slot_info_ty,
      [("slot", slot), ("n_slots", n_slots), ("type_str", fromMLstring type_str)])
  in reccon end

fun mk_code_slot_info (offset, length, type_str) =
  let
    val reccon = TypeBase.mk_record (code_slot_info_ty,
      [("offset", offset), ("length", length), ("type_str", fromMLstring type_str)])
  in reccon end

(* Storage key is (string option # string) = (module_alias_opt, var_name) *)
fun mk_json_storage_layout (storage_list, transient_list, code_list) =
  let
    val string_option_ty = mk_option string_ty
    val storage_key_ty = mk_prod(string_option_ty, string_ty)
    val storage_pair_ty = mk_prod(storage_key_ty, storage_slot_info_ty)
    val code_pair_ty = mk_prod(string_ty, code_slot_info_ty)
    val storage_tm = mk_list(storage_list, storage_pair_ty)
    val transient_tm = mk_list(transient_list, storage_pair_ty)
    val code_tm = mk_list(code_list, code_pair_ty)
    val reccon = TypeBase.mk_record (json_storage_layout_ty,
      [("storage", storage_tm), ("transient", transient_tm), ("code", code_tm)])
  in reccon end

(* Decoder for a single storage slot entry *)
val storage_slot_info : term decoder =
  JSONDecode.map (fn (slot, n_slots, type_str) =>
                    mk_storage_slot_info (slot, n_slots, type_str))
  (tuple3 (field "slot" numtm,
           field "n_slots" numtm,
           field "type" string))

(* Decoder for a single code (immutable) slot entry *)
val code_slot_info : term decoder =
  JSONDecode.map (fn (offset, length, type_str) =>
                    mk_code_slot_info (offset, length, type_str))
  (tuple3 (field "offset" numtm,
           field "length" numtm,
           field "type" string))

(* Decode a JSON object as an association list, applying decoder to each value *)
fun decode_object_alist (decoder : term decoder) : (string * term) list decoder =
  andThen rawObject (fn pairs =>
    let
      fun decode_pair (name, value) = (name, decode decoder value)
    in
      succeed (List.map decode_pair pairs)
    end)

(* Decode storage layout, handling arbitrarily nested module structures.
   Flat: {"counter": {"slot": 0, ...}} -> [(NONE, "counter", info)]
   Nested: {"lib1": {"counter": {"slot": 0, ...}}} -> [(SOME "lib1", "counter", info)]
   Deep: {"lib2": {"lib1": {"counter": {...}}}} -> [(SOME "lib1", "counter", info)]
   
   The innermost module name is used as the alias - this corresponds to the
   source_id in the AST. The outer nesting reflects initialization hierarchy
   but the variable is "owned" by the innermost module.
   
   Returns (module_alias_opt, var_name, slot_info) triples. *)
fun decode_storage_layout_nested (slot_decoder : term decoder)
    : (string option * string * term) list decoder =
  andThen rawObject (fn pairs =>
    let
      (* Check if a value looks like a slot info (has "slot" field) or is nested (module) *)
      fun is_slot_info (JSON.OBJECT fields) =
            List.exists (fn (k,_) => k = "slot") fields
        | is_slot_info _ = false

      (* Recursively decode, tracking the innermost module name seen *)
      fun decode_entry innermost_module_opt (name, value) =
        if is_slot_info value
        then [(innermost_module_opt, name, decode slot_decoder value)]
        else (* Nested module - recurse, updating innermost module to current name *)
          case value of
            JSON.OBJECT nested_fields =>
              List.concat (List.map (decode_entry (SOME name)) nested_fields)
          | _ => []
    in
      succeed (List.concat (List.map (decode_entry NONE) pairs))
    end)

(* Helper to make storage key term: (module_alias_opt, var_name) *)
fun mk_storage_key (module_opt : string option, var_name : string) : term =
  let
    val alias_tm = case module_opt of
                     NONE => optionSyntax.mk_none string_ty
                   | SOME s => optionSyntax.mk_some (fromMLstring s)
  in
    pairSyntax.mk_pair(alias_tm, fromMLstring var_name)
  end

(* Parse the storage_layout object from a trace *)
(* Structure: { "storage_layout": {...}, "transient_storage_layout": {...}, "code_layout": {...} } *)
(* Note: inner storage_layout field is optional - some contracts have empty {} *)
(* Storage layout keys: (module_alias_opt, var_name) *)
val storage_layout : term decoder =
  JSONDecode.map (fn ((storage_triples, transient_triples), code_pairs) =>
                    mk_json_storage_layout (
                      List.map (fn (m,n,t) => pairSyntax.mk_pair(mk_storage_key(m,n), t)) storage_triples,
                      List.map (fn (m,n,t) => pairSyntax.mk_pair(mk_storage_key(m,n), t)) transient_triples,
                      List.map (fn (n,t) => pairSyntax.mk_pair(fromMLstring n, t)) code_pairs))
  (tuple2 (
     tuple2 (
       orElse (field "storage_layout" (decode_storage_layout_nested storage_slot_info), succeed []),
       orElse (field "transient_storage_layout" (decode_storage_layout_nested storage_slot_info), succeed [])),
     orElse (field "code_layout" (decode_object_alist code_slot_info), succeed [])))

end
