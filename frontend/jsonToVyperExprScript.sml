Theory jsonToVyperExpr
Ancestors
  integer alist jsonAST vyperAST jsonToVyperType
Libs
  intLib

Definition translate_binop_def:
  (translate_binop JBop_Add = Add) /\
  (translate_binop JBop_Sub = Sub) /\
  (translate_binop JBop_Mult = Mul) /\
  (translate_binop JBop_Div = Div) /\
  (translate_binop JBop_FloorDiv = Div) /\
  (translate_binop JBop_Mod = Mod) /\
  (translate_binop JBop_Pow = Exp) /\
  (translate_binop JBop_And = And) /\
  (translate_binop JBop_Or = Or) /\
  (translate_binop JBop_BitAnd = And) /\
  (translate_binop JBop_BitOr = Or) /\
  (translate_binop JBop_BitXor = XOr) /\
  (translate_binop JBop_LShift = ShL) /\
  (translate_binop JBop_RShift = ShR) /\
  (translate_binop JBop_Eq = Eq) /\
  (translate_binop JBop_NotEq = NotEq) /\
  (translate_binop JBop_Lt = Lt) /\
  (translate_binop JBop_LtE = LtE) /\
  (translate_binop JBop_Gt = Gt) /\
  (translate_binop JBop_GtE = GtE) /\
  (translate_binop JBop_In = In) /\
  (translate_binop JBop_NotIn = NotIn)
End


(* ===== Hex String to Word8 List Conversion ===== *)

Definition hex_digit_to_num_def:
  hex_digit_to_num c =
    if c = #"0" then 0n else
    if c = #"1" then 1 else
    if c = #"2" then 2 else
    if c = #"3" then 3 else
    if c = #"4" then 4 else
    if c = #"5" then 5 else
    if c = #"6" then 6 else
    if c = #"7" then 7 else
    if c = #"8" then 8 else
    if c = #"9" then 9 else
    if c = #"a" \/ c = #"A" then 10 else
    if c = #"b" \/ c = #"B" then 11 else
    if c = #"c" \/ c = #"C" then 12 else
    if c = #"d" \/ c = #"D" then 13 else
    if c = #"e" \/ c = #"E" then 14 else
    if c = #"f" \/ c = #"F" then 15 else 0
End


Definition hex_pair_to_word8_def:
  hex_pair_to_word8 hi lo = n2w (hex_digit_to_num hi * 16 + hex_digit_to_num lo) : word8
End


Definition hex_string_to_bytes_def:
  (hex_string_to_bytes [] = []) /\
  (hex_string_to_bytes [_] = []) /\
  (hex_string_to_bytes (hi::lo::rest) = hex_pair_to_word8 hi lo :: hex_string_to_bytes rest)
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End


Definition strip_0x_def:
  (strip_0x [] = []) /\
  (strip_0x [c] = [c]) /\
  (strip_0x (c1::c2::rest) =
     if c1 = #"0" /\ (c2 = #"x" \/ c2 = #"X")
     then rest
     else c1::c2::rest)
End


(* ===== Decimal String Parsing ===== *)

Definition is_digit_def:
  is_digit c =
    (c = #"0" \/ c = #"1" \/ c = #"2" \/ c = #"3" \/ c = #"4" \/
     c = #"5" \/ c = #"6" \/ c = #"7" \/ c = #"8" \/ c = #"9")
End


Definition digit_to_num_def:
  digit_to_num c =
    if c = #"0" then 0n else
    if c = #"1" then 1 else
    if c = #"2" then 2 else
    if c = #"3" then 3 else
    if c = #"4" then 4 else
    if c = #"5" then 5 else
    if c = #"6" then 6 else
    if c = #"7" then 7 else
    if c = #"8" then 8 else
    if c = #"9" then 9 else 0
End


Definition num_of_digits_acc_def:
  (num_of_digits_acc acc [] = acc) /\
  (num_of_digits_acc acc (c::cs) =
     num_of_digits_acc (acc * 10 + digit_to_num c) cs)
End


Definition num_of_digits_def:
  num_of_digits cs = num_of_digits_acc 0 cs
End


Definition strip_sign_def:
  (strip_sign [] = (F, [])) /\
  (strip_sign (c::cs) =
     if c = #"-" then (T, cs)
     else if c = #"+" then (F, cs)
     else (F, c::cs))
End


Definition drop_nondigit_def:
  (drop_nondigit [] = []) /\
  (drop_nondigit (c::cs) =
     if is_digit c then (c::cs) else drop_nondigit cs)
End


Definition split_at_e_def:
  (split_at_e [] = ([], [])) /\
  (split_at_e (c::cs) =
     if c = #"e" \/ c = #"E" then ([], cs)
     else let (l, r) = split_at_e cs in (c::l, r))
End


Definition split_at_dot_def:
  (split_at_dot [] = ([], [])) /\
  (split_at_dot (c::cs) =
     if c = #"." then ([], cs)
     else let (l, r) = split_at_dot cs in (c::l, r))
End


Definition pad_right_zeros_def:
  pad_right_zeros n xs =
    if LENGTH xs < n then xs ++ REPLICATE (n - LENGTH xs) #"0" else xs
End


Definition decimal_string_to_int_def:
  decimal_string_to_int s =
    let (base, exp) = split_at_e s in
    let (neg_exp, exp_rest) = strip_sign exp in
    let exp_digits = FILTER is_digit exp_rest in
    let exp_num = num_of_digits exp_digits in
    let exp_int = if neg_exp then &0 - &exp_num else &exp_num in
    let (bd, ad) = split_at_dot base in
    let ad = FILTER is_digit ad in
    let target = &10 + exp_int in
    let pad_len =
      if target <= & (LENGTH ad) then LENGTH ad else Num target in
    let ad' = pad_right_zeros pad_len ad in
    let ds = bd ++ ad' in
    let (neg, ds_rest) = strip_sign ds in
    let digits = FILTER is_digit ds_rest in
    let n = num_of_digits digits in
      if neg then &0 - &n else &n
End


(* ===== BoolOp Helpers ===== *)
(* These work on vyper expr lists (post-translation) *)

Definition boolop_and_def:
  (boolop_and [] = Literal (BaseT BoolT) (BoolL T)) /\
  (boolop_and [e] = e) /\
  (boolop_and (e::es) = IfExp (BaseT BoolT) e (boolop_and es) (Literal (BaseT BoolT) (BoolL F)))
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End


Definition boolop_or_def:
  (boolop_or [] = Literal (BaseT BoolT) (BoolL F)) /\
  (boolop_or [e] = e) /\
  (boolop_or (e::es) = IfExp (BaseT BoolT) e (Literal (BaseT BoolT) (BoolL T)) (boolop_or es))
Termination
  WF_REL_TAC `measure LENGTH` >> simp[]
End


(* ===== Builtin Call Helper (non-recursive, defined before translate_expr) ===== *)
(* This takes already-translated args and kwargs *)

Definition is_prefix_def:
  (is_prefix [] _ = T) /\
  (is_prefix _ [] = F) /\
  (is_prefix (p::ps) (s::ss) = ((p = s) /\ is_prefix ps ss))
End


Definition is_capitalized_def:
  (is_capitalized [] = F) /\
  (is_capitalized (c::cs) = (#"A" <= c /\ c <= #"Z"))
End


Definition is_cast_name_def:
  is_cast_name name =
    (is_capitalized name \/
     is_prefix "uint" name \/
     is_prefix "int" name \/
     is_prefix "bytes" name \/
     name = "decimal" \/
     name = "bool" \/
     name = "address")
End


Definition is_builtin_cast_name_def:
  is_builtin_cast_name name =
    (is_prefix "uint" name \/ is_prefix "Uint" name \/
     is_prefix "int" name \/ is_prefix "Int" name \/
     is_prefix "bytes" name \/ is_prefix "Bytes" name \/
     name = "decimal" \/ name = "Decimal" \/
     name = "bool" \/ name = "Bool" \/
     name = "address" \/ name = "Address")
End


Definition denomination_of_string_def:
  denomination_of_string s =
    if s = "wei" then SOME Wei else
    if s = "kwei" then SOME Kwei else
    if s = "babbage" then SOME Kwei else
    if s = "femtoether" then SOME Kwei else
    if s = "mwei" then SOME Mwei else
    if s = "lovelace" then SOME Mwei else
    if s = "picoether" then SOME Mwei else
    if s = "gwei" then SOME Gwei else
    if s = "shannon" then SOME Gwei else
    if s = "nanoether" then SOME Gwei else
    if s = "szabo" then SOME Szabo else
    if s = "microether" then SOME Szabo else
    if s = "finney" then SOME Finney else
    if s = "milliether" then SOME Finney else
    if s = "ether" then SOME Ether else
    if s = "kether" then SOME KEther else
    if s = "grand" then SOME KEther else
    if s = "mether" then SOME MEther else
    if s = "gether" then SOME GEther else
    if s = "tether" then SOME TEther else NONE
End


Definition denomination_of_expr_def:
  denomination_of_expr (Literal _ (StringL s)) = denomination_of_string s /\
  denomination_of_expr _ = NONE
End


(* ===== Keyword Argument Helpers ===== *)

(* Extract boolean kwarg: ALOOKUP on (name, expr) list, pattern match BoolL *)
Definition kwarg_bool_def:
  kwarg_bool key (kwargs : (identifier # expr) list) default =
    case ALOOKUP kwargs key of
      SOME (Literal _ (BoolL b)) => b
    | _ => default
End


(* Extract numeric kwarg: pattern match IntL *)
Definition kwarg_num_def:
  kwarg_num key (kwargs : (identifier # expr) list) (default : num) =
    case ALOOKUP kwargs key of
      SOME (Literal _ (IntL n)) => if n >= 0 then Num n else default
    | _ => default
End


(* Extract expression kwarg with default *)
Definition kwarg_expr_def:
  kwarg_expr key (kwargs : (identifier # expr) list) default =
    case ALOOKUP kwargs key of
      SOME e => e
    | NONE => default
End



(* Extract a compiler-validated four-byte method_id literal. *)
Definition kwarg_method_id_def:
  kwarg_method_id key (kwargs : (identifier # expr) list) =
    case ALOOKUP kwargs key of
      SOME (Literal _ (BytesL bs)) =>
        if LENGTH bs = 4 then SOME bs else NONE
    | _ => NONE
End


Definition make_builtin_call_def:
  make_builtin_call ty name args kwargs ret_ty =
    if name = "len" then Builtin ty Len args
    else if name = "concat" then
      (case ret_ty of JT_String n => Builtin ty (Concat n) args
                    | JT_Bytes n => Builtin ty (Concat n) args
                    | _ => Builtin ty (Concat 0) args)
    else if name = "slice" then
      (case ret_ty of JT_String n => Builtin ty (Slice n) args
                    | JT_Bytes n => Builtin ty (Slice n) args
                    | _ => Builtin ty (Slice 0) args)
    else if name = "keccak256" then Builtin ty Keccak256 args
    else if name = "sha256" then Builtin ty Sha256 args
    else if name = "floor" then Builtin ty Floor args
    else if name = "ceil" then Builtin ty Ceil args
    else if name = "blockhash" then Builtin ty BlockHash args
    else if name = "blobhash" then Builtin ty BlobHash args
    else if name = "ecrecover" then Builtin ty ECRecover args
    else if name = "ecadd" then Builtin ty ECAdd args
    else if name = "ecmul" then Builtin ty ECMul args
    else if name = "empty" then TypeBuiltin ty Empty ty []
    else if name = "max_value" then TypeBuiltin ty MaxValue ty []
    else if name = "min_value" then TypeBuiltin ty MinValue ty []
    else if name = "convert" then
      (case args of (arg::_) => TypeBuiltin ty Convert ty [arg]
                  | _ => TypeBuiltin ty Convert ty [])
    else if name = "unsafe_add" then Builtin ty (Bop UnsafeAdd) args
    else if name = "unsafe_sub" then Builtin ty (Bop UnsafeSub) args
    else if name = "unsafe_mul" then Builtin ty (Bop UnsafeMul) args
    else if name = "unsafe_div" then Builtin ty (Bop UnsafeDiv) args
    else if name = "uint256_addmod" then Builtin ty AddMod args
    else if name = "uint256_mulmod" then Builtin ty MulMod args
    else if name = "pow_mod256" then Builtin ty PowMod256 args
    else if name = "min" then Builtin ty (Bop Min) args
    else if name = "max" then Builtin ty (Bop Max) args
    else if name = "send" then Call ty Send args NONE
    (* ===== Chain interaction builtins ===== *)
    (* raw_call(to, data, max_outsize=0, gas=gas, value=0,
                is_delegate_call=F, is_static_call=F, revert_on_failure=T)
       Convention: args in Call = [to_addr; data_bytes; value] *)
    else if name = "raw_call" then
      let flags = <| rcf_max_outsize := kwarg_num "max_outsize" kwargs 0;
                     rcf_is_delegate := kwarg_bool "is_delegate_call" kwargs F;
                     rcf_is_static := kwarg_bool "is_static_call" kwargs F;
                     rcf_revert_on_failure := kwarg_bool "revert_on_failure" kwargs T |> in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      Call ty (RawCallTarget flags) (args ++ [value_e]) NONE
    else if name = "raw_log" then Call ty RawLog args NONE
    else if name = "raw_revert" then Call ty RawRevert args NONE
    else if name = "selfdestruct" then Call ty SelfDestructTarget args NONE
    else if name = "create_minimal_proxy_to" ∨ name = "create_forwarder_to" then
      let rof = kwarg_bool "revert_on_failure" kwargs T in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      let salt_opt = ALOOKUP kwargs "salt" in
      let salt_es = case salt_opt of NONE => [] | SOME salt_e => [salt_e] in
      Call ty (CreateTarget CreateMinimalProxy (IS_SOME salt_opt) rof)
        (TAKE 1 args ++ [value_e] ++ salt_es) NONE
    else if name = "create_copy_of" then
      let rof = kwarg_bool "revert_on_failure" kwargs T in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      let salt_opt = ALOOKUP kwargs "salt" in
      let salt_es = case salt_opt of NONE => [] | SOME salt_e => [salt_e] in
      Call ty (CreateTarget CreateCopyOf (IS_SOME salt_opt) rof)
        (TAKE 1 args ++ [value_e] ++ salt_es) NONE
    else if name = "create_from_blueprint" then
      let rof = kwarg_bool "revert_on_failure" kwargs T in
      let raw_args_flag = kwarg_bool "raw_args" kwargs F in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      let salt_opt = ALOOKUP kwargs "salt" in
      let salt_es = case salt_opt of NONE => [] | SOME salt_e => [salt_e] in
      let code_offset_e = kwarg_expr "code_offset" kwargs
        (Literal (BaseT (UintT 256)) (IntL 3)) in
      Call ty (CreateTarget (CreateFromBlueprint raw_args_flag) (IS_SOME salt_opt) rof)
        (TAKE 1 args ++ [value_e] ++ salt_es ++ [code_offset_e] ++ DROP 1 args) NONE
    else if name = "raw_create" then
      let rof = kwarg_bool "revert_on_failure" kwargs T in
      let value_e = kwarg_expr "value" kwargs (Literal (BaseT (UintT 256)) (IntL 0)) in
      let salt_opt = ALOOKUP kwargs "salt" in
      let salt_es = case salt_opt of NONE => [] | SOME salt_e => [salt_e] in
      Call ty (CreateTarget RawCreate (IS_SOME salt_opt) rof)
        (TAKE 1 args ++ [value_e] ++ DROP 1 args ++ salt_es) NONE
    else if name = "abs" then Builtin ty Abs args
    else if name = "as_wei_value" then
      (case args of
         (v::d::_) =>
           (case denomination_of_expr d of
              SOME dn => Builtin ty (AsWeiValue dn) [v]
            | NONE => Builtin ty (AsWeiValue Wei) [v])
       | (v::_) => Builtin ty (AsWeiValue Wei) [v]
       | _ => Builtin ty (AsWeiValue Wei) [])
    else if name = "uint2str" then
      (case ret_ty of JT_String n => Builtin ty (Uint2Str n) args
                    | _ => Builtin ty (Uint2Str 0) args)
    else if name = "abi_decode" ∨ name = "_abi_decode" then
      let unwrap = kwarg_bool "unwrap_tuple" kwargs T in
      (case args of (arg::_) => TypeBuiltin ty (AbiDecode unwrap) ty [arg]
                  | _ => TypeBuiltin ty (AbiDecode unwrap) ty [])
    else if name = "abi_encode" ∨ name = "_abi_encode" then
      let ensure = kwarg_bool "ensure_tuple" kwargs T in
      let method_id = kwarg_method_id "method_id" kwargs in
      let arg_types = TupleT (MAP expr_type args) in
      TypeBuiltin ty (AbiEncode ensure method_id) arg_types args
    else if name = "extract32" then
      TypeBuiltin ty Extract32 ty args
    else if name = "method_id" then
      Builtin ty MethodId args
    (* Struct constructor, cast, or regular call *)
    else (case ret_ty of
          | JT_Struct _ sname =>
              (case ty of
                 StructT nsid => StructLit ty nsid kwargs
               | _ => StructLit ty (NONE, sname) kwargs)
          | JT_Named _ _ =>
              if kwargs <> [] /\ ~is_builtin_cast_name name then
                (case ty of
                   StructT nsid => StructLit ty nsid kwargs
                 | _ => StructLit ty (NONE, name) kwargs)
              else
                if is_cast_name name then
                    if is_builtin_cast_name name then
                      (case ty of
                         BaseT _ =>
                           (case args of
                              (arg::_) => TypeBuiltin ty Convert ty [arg]
                            | _ => TypeBuiltin ty Convert ty [])
                       | _ =>
                           (case args of
                              (arg::_) => arg
                            | _ => Call ty (IntCall (NONE, name)) args NONE))
                    else
                      (case args of
                         (arg::_) => arg
                       | _ => Call ty (IntCall (NONE, name)) args NONE)
                else Call ty (IntCall (NONE, name)) args NONE
          | _ =>
              if is_cast_name name then
                  if is_builtin_cast_name name then
                    (case ty of
                       BaseT _ =>
                         (case args of
                            (arg::_) => TypeBuiltin ty Convert ty [arg]
                          | _ => TypeBuiltin ty Convert ty [])
                     | _ =>
                         (case args of
                            (arg::_) => arg
                          | _ => Call ty (IntCall (NONE, name)) args NONE))
                  else
                    (case args of
                       (arg::_) => arg
                     | _ => Call ty (IntCall (NONE, name)) args NONE)
              else Call ty (IntCall (NONE, name)) args NONE)
End


(* ===== Module Call Helpers ===== *)

(* Extract function name from a func expression *)
(* For JE_Attribute base fname, returns fname *)
Definition extract_func_name_def:
  (extract_func_name (JE_Attribute _ fname _ _ _ _ _) = fname) /\
  (extract_func_name (JE_Name name _ _ _) = name) /\
  (extract_func_name _ = "")
End


(* Check if a func expression has interface typeclass (for cross-module interface constructors) *)
Definition is_interface_constructor_def:
  (is_interface_constructor (JE_Attribute _ _ (SOME tc) _ _ _ _) = (tc = "interface")) /\
  (is_interface_constructor (JE_Name _ (SOME tc) _ _) = (tc = "interface")) /\
  (is_interface_constructor _ = F)
End


(* Extract the innermost module's source_id from a module chain *)
(* For lib1: returns SOME 0 (from JE_Name) *)
(* For lib1.lib2: returns SOME 1 (from the .lib2 Attribute) *)
Definition extract_innermost_module_src_def:
  (* Attribute with module/interface typeclass has source_id directly *)
  (extract_innermost_module_src (JE_Attribute _ _ (SOME tc) _ _ src_id_opt _) =
    if tc = "module" ∨ tc = "interface" then SOME src_id_opt else NONE) /\
  (* JE_Name with module/interface typeclass *)
  (extract_innermost_module_src (JE_Name _ (SOME tc) src_id_opt _) =
    if tc = "module" ∨ tc = "interface" then SOME src_id_opt else NONE) /\
  (* Other cases *)
  (extract_innermost_module_src _ = NONE)
End


(* Check if an expression is a module reference (not an interface-typed value).
   Used to detect nested module attribute access: mod3.mod2.mod1.X
   Interface-typed expressions like self.f should NOT match, because they are
   runtime values with attributes like .address and .balance. *)
Definition is_module_expr_def:
  (is_module_expr (JE_Attribute _ _ (SOME tc) _ _ _ _) = (tc = "module")) /\
  (is_module_expr (JE_Name _ (SOME tc) _ _) = (tc = "module")) /\
  (is_module_expr _ = F)
End


(* ===== Expression translation context and name helpers ===== *)

(* Expression translation carries the root source ID, current module
   namespace, current module import map, and names of constants/immutables. *)
Definition expr_main_src_id_def:
  expr_main_src_id ctx = FST ctx
End

Definition expr_current_nsid_def:
  expr_current_nsid ctx = FST (SND ctx)
End

Definition expr_import_map_def:
  expr_import_map ctx = FST (SND (SND ctx))
End

Definition expr_const_names_def:
  expr_const_names ctx = FST (SND (SND (SND ctx)))
End

Definition expr_local_types_def:
  expr_local_types ctx = FST (SND (SND (SND (SND ctx))))
End

Definition expr_toplevel_types_def:
  expr_toplevel_types ctx = SND (SND (SND (SND (SND ctx))))
End

Definition expr_with_local_types_def:
  expr_with_local_types ctx local_types =
    (expr_main_src_id ctx,
     (expr_current_nsid ctx,
      (expr_import_map ctx,
       (expr_const_names ctx, (local_types, expr_toplevel_types ctx)))))
End

Definition lookup_local_type_def:
  lookup_local_type ctx name fallback =
    case ALOOKUP (expr_local_types ctx) name of
    | SOME ty => ty
    | NONE => fallback
End

Definition lookup_toplevel_type_def:
  lookup_toplevel_type ctx nsid fallback =
    case ALOOKUP (expr_toplevel_types ctx) nsid of
    | SOME ty => ty
    | NONE => fallback
End

Definition expr_type_ctx_def:
  expr_type_ctx ctx =
    (expr_main_src_id ctx, expr_current_nsid ctx, expr_import_map ctx)
End

Definition resolve_source_ref_def:
  (resolve_source_ref ctx JMissingSource = expr_current_nsid ctx) /\
  (resolve_source_ref ctx (JExplicitSource src_id) =
    if src_id = -2 then expr_current_nsid ctx
    else source_id_to_nsid (expr_main_src_id ctx) src_id)
End

(* Module syntax carries the import alias that disambiguates Vyper's shared
   builtin source ID.  Prefer that canonical alias mapping to raw metadata. *)
Definition resolve_module_alias_def:
  resolve_module_alias ctx alias fallback =
    case ALOOKUP (expr_import_map ctx) alias of
    | SOME src_id => SOME src_id
    | NONE => resolve_source_ref ctx fallback
End

Definition resolve_func_module_ref_def:
  resolve_func_module_ref ctx
      (JE_Attribute (JE_Name alias (SOME "module") src _)
        _ _ _ _ _ _) fallback =
    resolve_module_alias ctx alias src ∧
  resolve_func_module_ref ctx _ fallback = resolve_source_ref ctx fallback
End

(* External signature metadata omits source IDs on nested nominal types.  Use
   the declaring function's module as the current type namespace. *)
Definition signature_type_ctx_def:
  signature_type_ctx ctx func_src =
    (expr_main_src_id ctx, resolve_source_ref ctx func_src, expr_import_map ctx)
End

(* Bare references to constants and immutables are translated as
   module-qualified top-level names; ordinary names remain local/scoped. *)
Definition make_name_def:
  make_name ctx ty id =
    if MEM id (expr_const_names ctx)
    then let nsid = (expr_current_nsid ctx, id) in
         TopLevelName (lookup_toplevel_type ctx nsid ty) nsid
    else Name (lookup_local_type ctx id ty) id
End

Definition make_name_target_def:
  make_name_target ctx id =
    if MEM id (expr_const_names ctx)
    then TopLevelNameTarget (expr_current_nsid ctx, id)
    else NameTarget id
End

Definition interface_constructor_result_def:
  interface_constructor_result ty [Literal _ (BytesL bs)] =
    Literal ty (BytesL bs) /\
  interface_constructor_result _ args = HD args
End

(* Cross-module flag result metadata may omit its declaration source. Recover
   that source from the module expression, then use it for both the result type
   and member lookup identity. *)
Definition extract_module_flag_def:
  (extract_module_flag ctx (JE_Attribute inner flag_name _ _ _ _ _) =
    case extract_innermost_module_src inner of
      SOME src => SOME (resolve_source_ref ctx src, flag_name)
    | NONE => NONE) /\
  (extract_module_flag ctx _ = NONE)
End

Definition make_flag_member_def:
  make_flag_member nsid attr = FlagMember (FlagT nsid) nsid attr
End

(* ===== Expression Translation ===== *)

(* Find a keyword by name in a keyword list, returns the json_expr if found *)
Definition find_keyword_def:
  find_keyword name [] = NONE ∧
  find_keyword name (JKeyword kw_name kw_val :: rest) =
    if kw_name = name then SOME kw_val
    else find_keyword name rest
End


(* Lemma: if find_keyword returns SOME v, then v is in the keyword list *)
Theorem find_keyword_MEM:
  ∀name kws v. find_keyword name kws = SOME v ⇒ ∃k. MEM (JKeyword k v) kws
Proof
  Induct_on `kws` >> rw[find_keyword_def] >>
  Cases_on `h` >> gvs[find_keyword_def] >>
  Cases_on `s = name` >> gvs[] >>
  metis_tac[]
QED

(* Size lemma for termination: keyword value is smaller than keyword list *)
Theorem find_keyword_size:
  ∀name kws v.
    find_keyword name kws = SOME v ⇒
    json_expr_size v < list_size json_keyword_size kws
Proof
  Induct_on `kws` >> rw[find_keyword_def] >>
  Cases_on `h` >> gvs[find_keyword_def, json_expr_size_def] >>
  Cases_on `s = name` >> gvs[json_expr_size_def] >>
  res_tac >> gvs[]
QED

Definition translate_expr_def:
  (translate_expr ctx (JE_Int v ty) =
    Literal (translate_type (expr_type_ctx ctx) ty) (IntL v)) /\

  (translate_expr ctx (JE_Decimal s) =
    Literal (BaseT DecimalT) (DecimalL (decimal_string_to_int s))) /\

  (translate_expr ctx (JE_Str len s) =
    Literal (BaseT (StringT len)) (StringL s)) /\

  (translate_expr ctx (JE_GenericStr s) =
    Literal (BaseT (StringT (STRLEN s))) (StringL s)) /\

  (translate_expr ctx (JE_Bytes len hex) =
    Literal (BaseT (BytesT (Dynamic len))) (BytesL (hex_string_to_bytes (FILTER isHexDigit (strip_0x hex))))) /\

  (translate_expr ctx (JE_Hex hex typ) =
    let bytes = hex_string_to_bytes (FILTER isHexDigit (strip_0x hex)) in
    let ty = case typ of
               JT_None => BaseT (BytesT (Fixed (LENGTH bytes)))
             | _ => translate_type (expr_type_ctx ctx) typ in
    Literal ty (BytesL bytes)) /\

  (translate_expr ctx (JE_Bool b) = Literal (BaseT BoolT) (BoolL b)) /\

  (translate_expr ctx JE_Ellipsis = Literal (BaseT BoolT) (BoolL T)) /\

  (translate_expr ctx (JE_Folded original folded) = translate_expr ctx folded) /\

  (translate_expr ctx (JE_Name id tc src_id_opt ret_ty) =
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    if id = "self" then Builtin (BaseT AddressT) (Env SelfAddr) [] else make_name ctx ty id) /\

  (* Special attributes: msg.*, block.*, tx.*, self.*, module.*, flag members *)
  (* attr_src_id_opt is from variable_reads on the outer Attribute (for self.x storage access) *)
  (* base_type_name is the type name of the base expression (e.g., "address" for addr.code) *)
  (* base_typeclass is the typeclass of the base expression (e.g., "interface" for interface.address) *)
  (translate_expr ctx (JE_Attribute (JE_Name obj tc src_id_opt base_ret_ty) attr result_tc base_type_name base_typeclass attr_src_id_opt ret_ty) =
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    let base_ty = translate_type (expr_type_ctx ctx) base_ret_ty in
    (* Same-module flag member: Action.BUY where tc = SOME "flag" *)
    if tc = SOME "flag" /\ result_tc = SOME "flag" then
      make_flag_member (expr_current_nsid ctx, obj) attr
    else if obj = "msg" /\ attr = "sender" then Builtin (BaseT AddressT) (Env Sender) []
    else if obj = "msg" /\ attr = "value" then Builtin (BaseT (UintT 256)) (Env ValueSent) []
    else if obj = "block" /\ attr = "timestamp" then Builtin (BaseT (UintT 256)) (Env TimeStamp) []
    else if obj = "block" /\ attr = "number" then Builtin (BaseT (UintT 256)) (Env BlockNumber) []
    else if obj = "block" /\ attr = "prevhash" then Builtin (BaseT (BytesT (Fixed 32))) (Env PrevHash) []
    else if obj = "block" /\ attr = "blobbasefee" then Builtin (BaseT (UintT 256)) (Env BlobBaseFee) []
    else if obj = "tx" /\ attr = "gasprice" then Builtin (BaseT (UintT 256)) (Env GasPrice) []
    else if obj = "chain" /\ attr = "id" then Builtin (BaseT (UintT 256)) (Env ChainId) []
    else if obj = "self" /\ attr = "balance" then
      Builtin (BaseT (UintT 256)) (Acc Balance) [Builtin (BaseT AddressT) (Env SelfAddr) []]
    else if obj = "self" /\ attr = "code" then
      Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [Builtin (BaseT AddressT) (Env SelfAddr) []]
    (* self.x: declaration types override incomplete compiler expression metadata. *)
    else if obj = "self" then
      let nsid = (resolve_source_ref ctx attr_src_id_opt, attr) in
      TopLevelName (lookup_toplevel_type ctx nsid ty) nsid
    (* Module variable access (lib1.x): use its canonical declaration type. *)
    else if tc = SOME "module" then
      let nsid = (resolve_module_alias ctx obj src_id_opt, attr) in
      TopLevelName (lookup_toplevel_type ctx nsid ty) nsid
    else if attr = "balance" /\ base_type_name = SOME "address" then Builtin (BaseT (UintT 256)) (Acc Balance) [make_name ctx base_ty obj]
    else if attr = "address" /\ base_type_name = SOME "address" then Builtin (BaseT AddressT) (Acc Address) [make_name ctx base_ty obj]
    else if attr = "address" /\ base_typeclass = SOME "interface" then make_name ctx base_ty obj (* interface.address = interface (identity) *)
    else if attr = "is_contract" /\ base_type_name = SOME "address" then Builtin (BaseT BoolT) (Acc IsContract) [make_name ctx base_ty obj]
    else if attr = "codesize" /\ base_type_name = SOME "address" then Builtin (BaseT (UintT 256)) (Acc Codesize) [make_name ctx base_ty obj]
    else if attr = "codehash" /\ base_type_name = SOME "address" then Builtin (BaseT (BytesT (Fixed 32))) (Acc Codehash) [make_name ctx base_ty obj]
    else if attr = "code" /\ base_type_name = SOME "address" then Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [make_name ctx base_ty obj]
    else Attribute ty (make_name ctx base_ty obj) attr) /\

  (* General attribute - handles nested and simple cases *)
  (* Check for cross-module flag access: lib1.Action.BUY *)
  (* base_type_name is the type name of the base expression (e.g., "address" for addr.code) *)
  (* base_typeclass is the typeclass of the base expression (e.g., "interface" for interface.address) *)
  (translate_expr ctx (JE_Attribute e attr result_tc base_type_name base_typeclass attr_src_id_opt ret_ty) =
    let ty = translate_type (expr_type_ctx ctx) ret_ty in
    if result_tc = SOME "flag" then
      case extract_module_flag ctx e of
        SOME nsid => make_flag_member nsid attr
      | NONE => Attribute ty (translate_expr ctx e) attr
    (* Nested module access: mod3.mod2.mod1.X — use variable_reads source_id *)
    else if is_module_expr e then
      let nsid = (resolve_source_ref ctx attr_src_id_opt, attr) in
      TopLevelName (lookup_toplevel_type ctx nsid ty) nsid
    else if attr = "balance" /\ base_type_name = SOME "address" then Builtin (BaseT (UintT 256)) (Acc Balance) [translate_expr ctx e]
    else if attr = "address" /\ base_type_name = SOME "address" then Builtin (BaseT AddressT) (Acc Address) [translate_expr ctx e]
    else if attr = "address" /\ base_typeclass = SOME "interface" then translate_expr ctx e (* interface.address = interface (identity) *)
    else if attr = "is_contract" /\ base_type_name = SOME "address" then Builtin (BaseT BoolT) (Acc IsContract) [translate_expr ctx e]
    else if attr = "codesize" /\ base_type_name = SOME "address" then Builtin (BaseT (UintT 256)) (Acc Codesize) [translate_expr ctx e]
    else if attr = "codehash" /\ base_type_name = SOME "address" then Builtin (BaseT (BytesT (Fixed 32))) (Acc Codehash) [translate_expr ctx e]
    else if attr = "code" /\ base_type_name = SOME "address" then Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code) [translate_expr ctx e]
    else Attribute ty (translate_expr ctx e) attr) /\

  (* Subscript *)
  (translate_expr ctx (JE_Subscript arr idx ret_ty) =
    Subscript (translate_type (expr_type_ctx ctx) ret_ty) (translate_expr ctx arr) (translate_expr ctx idx)) /\

  (* NamedExpr - only appears in initializes:/uses: annotations, not in executable code *)
  (translate_expr ctx (JE_NamedExpr target value) =
    Literal (BaseT BoolT) (BoolL T)) /\

  (* BinOp *)
  (translate_expr ctx (JE_BinOp l op r ret_ty) =
    Builtin (translate_type (expr_type_ctx ctx) ret_ty) (Bop (translate_binop op)) [translate_expr ctx l; translate_expr ctx r]) /\

  (translate_expr ctx (JE_Compare l op r) =
    Builtin (BaseT BoolT) (Bop (translate_binop op))
      [translate_expr ctx l; translate_expr ctx r]) /\

  (* BoolOp - convert to nested IfExp *)
  (translate_expr ctx (JE_BoolOp JBoolop_And es) =
    boolop_and (translate_expr_list ctx es)) /\
  (translate_expr ctx (JE_BoolOp JBoolop_Or es) =
    boolop_or (translate_expr_list ctx es)) /\

  (* UnaryOp *)
  (translate_expr ctx (JE_UnaryOp JUop_USub e ret_ty) =
    Builtin (translate_type (expr_type_ctx ctx) ret_ty) Neg [translate_expr ctx e]) /\
  (translate_expr ctx (JE_UnaryOp JUop_Not e ret_ty) =
    Builtin (BaseT BoolT) Not [translate_expr ctx e]) /\
  (translate_expr ctx (JE_UnaryOp JUop_Invert e ret_ty) =
    Builtin (translate_type (expr_type_ctx ctx) ret_ty) Not [translate_expr ctx e]) /\

  (* IfExp (ternary) *)
  (translate_expr ctx (JE_IfExp test body orelse ret_ty) =
    IfExp (translate_type (expr_type_ctx ctx) ret_ty) (translate_expr ctx test) (translate_expr ctx body) (translate_expr ctx orelse)) /\

  (* Tuple *)
  (translate_expr ctx (JE_Tuple es) =
    let es' = translate_expr_list ctx es in
    Builtin (TupleT (MAP expr_type es'))
      (MakeArray NONE (Fixed (LENGTH es'))) es') /\

  (* List - array literal *)
  (translate_expr ctx (JE_List es ty) =
    let ty' = translate_type (expr_type_ctx ctx) ty in
    case ty of
    | JT_StaticArray vt len =>
        Builtin ty' (MakeArray (SOME (translate_type (expr_type_ctx ctx) vt)) (Fixed len)) (translate_expr_list ctx es)
    | JT_DynArray vt len =>
        Builtin ty' (MakeArray (SOME (translate_type (expr_type_ctx ctx) vt)) (Dynamic len)) (translate_expr_list ctx es)
    | _ =>
        Builtin ty' (MakeArray NONE (Fixed (LENGTH es))) (translate_expr_list ctx es)) /\

  (* Call - single case with internal dispatch to avoid pattern completion issues *)
  (* JE_Call now includes source_id for module calls *)
  (translate_expr ctx (JE_Call func args kwargs ret_ty src_id_opt) =
    let args' = translate_expr_list ctx args in
    let kwargs' = translate_kwargs ctx kwargs in
    let rty = translate_type (signature_type_ctx ctx src_id_opt) ret_ty in
    case func of
    | JE_Name name (SOME "interface") _ _ =>
        interface_constructor_result rty args'
    | JE_Name name _ _ _ => make_builtin_call rty name args' kwargs' ret_ty
    (* lib.__at__(addr) / lib.__interface__(addr) - interface instantiation, just returns the address *)
    | JE_Attribute _ "__at__" _ _ _ _ _ =>
        interface_constructor_result rty args'
    | JE_Attribute _ "__interface__" _ _ _ _ _ =>
        interface_constructor_result rty args'
    | JE_Attribute base "pop" _ _ _ _ _ =>
        (case base of
         | JE_Name id _ _ _ => Pop rty (make_name_target ctx id)
         | JE_Attribute (JE_Name "self" _ _ _) attr _ _ _ _ _ => Pop rty (TopLevelNameTarget (NONE, attr))
         | JE_Attribute (JE_Name id (SOME "module") src_id_opt _) attr _ _ _ _ _ =>
             Pop rty (TopLevelNameTarget (resolve_source_ref ctx src_id_opt, attr))
         | JE_Attribute (JE_Name id _ _ _) attr _ _ _ _ _ =>
             Pop rty (AttributeTarget (make_name_target ctx id) attr)
         | JE_Subscript (JE_Name id _ _ _) idx _ =>
             Pop rty (SubscriptTarget (make_name_target ctx id) (translate_expr ctx idx))
         | _ => Call rty (IntCall (NONE, "pop")) args' NONE)
    (* self.func(args) - internal call *)
    | JE_Attribute (JE_Name "self" _ _ _) fname _ _ _ _ _ => Call rty (IntCall (resolve_source_ref ctx src_id_opt, fname)) args' NONE
    (* Module struct constructor, interface constructor, or module function call *)
    | _ => if is_interface_constructor func then
             interface_constructor_result rty args'
           else let nsid = resolve_func_module_ref ctx func src_id_opt;
               fname = extract_func_name func in
           (case ret_ty of
              JT_Struct src_id_opt sname =>
                if fname = sname then
                  (* Struct constructor: library.SomeStruct(x=2) *)
                  let mod_nsid = case src_id_opt of
                      SOME sid => source_id_to_nsid (expr_main_src_id ctx) sid
                    | NONE =>
                      case func of
                        JE_Attribute base _ _ _ _ _ _ =>
                          (case extract_innermost_module_src base of
                             SOME src => resolve_source_ref ctx src
                           | NONE => nsid)
                      | _ => nsid in
                  StructLit (StructT (mod_nsid, fname)) (mod_nsid, fname) kwargs'
                else
                  (* Function call that returns a struct: library.foo() *)
                  Call rty (IntCall (nsid, fname)) args' NONE
            | _ =>
              (* Module call: use source_id from type_decl_node *)
              Call rty (IntCall (nsid, fname)) args' NONE)) /\

  (* ExtCall - mutating external call (is_static = F) *)
  (translate_expr ctx
      (JE_ExtCall func_name func_src arg_types ret_ty target args keywords) =
    let value_expr = case find_keyword "value" keywords of
                     | SOME v => translate_expr ctx v
                     | NONE => Literal (BaseT (UintT 256)) (IntL 0) in
    let sig_ctx = signature_type_ctx ctx func_src in
    let ret_ty' = translate_type sig_ctx ret_ty in
    (* Vyper records the full declared parameter list in argument_types, even
       when trailing defaulted parameters are omitted.  ExtCall carries the
       effective ABI signature selected at this call site. *)
    Call ret_ty'
      (ExtCall F
        (func_name,
         TAKE (LENGTH args) (MAP (translate_type sig_ctx) arg_types),
         ret_ty'))
      (translate_expr ctx target :: value_expr :: translate_expr_list ctx args)
      (OPTION_MAP (translate_expr ctx)
        (find_keyword "default_return_value" keywords))) /\

  (* StaticCall - read-only external call (is_static = T) *)
  (translate_expr ctx
      (JE_StaticCall func_name func_src arg_types ret_ty target args) =
    let sig_ctx = signature_type_ctx ctx func_src in
    let ret_ty' = translate_type sig_ctx ret_ty in
    (* See ExtCall above: retain only the effective ABI argument types. *)
    Call ret_ty'
      (ExtCall T
        (func_name,
         TAKE (LENGTH args) (MAP (translate_type sig_ctx) arg_types),
         ret_ty'))
      (translate_expr ctx target :: translate_expr_list ctx args)
      NONE) /\

  (* Helper for translating expression lists *)
  (translate_expr_list ctx [] = []) /\
  (translate_expr_list ctx (e::es) = translate_expr ctx e :: translate_expr_list ctx es) /\

  (* Helper for translating keywords *)
  (translate_kwargs ctx [] = []) /\
  (translate_kwargs ctx (JKeyword k v :: rest) = (k, translate_expr ctx v) :: translate_kwargs ctx rest)
Termination
  WF_REL_TAC `measure (λx. case x of
    | INL (_, e) => json_expr_size e
    | INR (INL (_, es)) => list_size json_expr_size es
    | INR (INR (_, kws)) => list_size json_keyword_size kws)`
  >> rw[]
  >> imp_res_tac find_keyword_size
  >> gvs[]
End


(* ===== Assignment Target Translation ===== *)
(* Defined after translate_expr since it uses it for subscript indices *)

Definition translate_base_target_def:
  (translate_base_target ctx (JBT_Name id) = make_name_target ctx id) /\
  (* Top-level targets retain whether their declaration is current or imported. *)
  (translate_base_target ctx (JBT_TopLevelName (src, name)) =
    TopLevelNameTarget (resolve_source_ref ctx src, name)) /\
  (translate_base_target ctx (JBT_Subscript tgt idx) =
    SubscriptTarget (translate_base_target ctx tgt) (translate_expr ctx idx)) /\
  (translate_base_target ctx (JBT_Attribute tgt attr) =
    AttributeTarget (translate_base_target ctx tgt) attr)
Termination
  WF_REL_TAC `measure (json_base_target_size o SND)` >> simp[]
End


Definition translate_target_def:
  (translate_target ctx (JTgt_Base bt) = BaseTarget (translate_base_target ctx bt)) /\
  (translate_target ctx (JTgt_Tuple tgts) = TupleTarget (MAP (translate_target ctx) tgts))
Termination
  WF_REL_TAC `measure (json_target_size o SND)` >> simp[]
End


(* ===== Iterator Translation ===== *)

Definition json_expr_int_opt_def:
  (json_expr_int_opt (JE_Int v _) = SOME v) /\
  (json_expr_int_opt (JE_UnaryOp JUop_USub e _) =
     case json_expr_int_opt e of
       SOME n => SOME (0 - n)
     | NONE => NONE) /\
  (json_expr_int_opt (JE_BinOp l JBop_Add r _) =
     case (json_expr_int_opt l, json_expr_int_opt r) of
       (SOME n1, SOME n2) => SOME (n1 + n2)
     | _ => NONE) /\
  (json_expr_int_opt (JE_BinOp l JBop_Sub r _) =
     case (json_expr_int_opt l, json_expr_int_opt r) of
       (SOME n1, SOME n2) => SOME (n1 - n2)
     | _ => NONE) /\
  (json_expr_int_opt _ = NONE)
End


Definition range_bound_of_args_def:
  (range_bound_of_args [] = NONE) /\
  (range_bound_of_args [e] =
     case json_expr_int_opt e of
       SOME n => if 0 <= n then SOME (Num n) else SOME 0
     | NONE => NONE) /\
  (range_bound_of_args (s::e::_) =
     case (json_expr_int_opt s, json_expr_int_opt e) of
       (SOME s', SOME e') =>
         if s' <= e' then SOME (Num (e' - s')) else SOME 0
     | _ => NONE)
End


Definition folded_bound_of_args_def:
  (folded_bound_of_args [] = NONE) /\
  (folded_bound_of_args [fv] =
     case fv of
       SOME n => if 0 <= n then SOME (Num n) else SOME 0
     | NONE => NONE) /\
  (folded_bound_of_args (fs::fe::_) =
     case (fs, fe) of
       (SOME s, SOME e) =>
         if s <= e then SOME (Num (e - s)) else SOME 0
     | _ => NONE)
End


Definition get_iter_bound_def:
  (get_iter_bound (JIter_Range args _ (SOME n)) = n) /\
  (get_iter_bound (JIter_Range args fvs NONE) =
     case range_bound_of_args args of
       SOME n => n
     | NONE => case folded_bound_of_args fvs of SOME n => n | NONE => 0) /\
  (get_iter_bound (JIter_Array _ (JT_StaticArray _ len)) = len) /\
  (get_iter_bound (JIter_Array _ (JT_DynArray _ len)) = len) /\
  (get_iter_bound (JIter_Array _ _) = 0)
End


Definition translate_iter_def:
  (translate_iter ctx var_ty (JIter_Range [] _ _) =
    Range (Literal var_ty (IntL (integer$int_of_num 0)))
          (Literal var_ty (IntL (integer$int_of_num 0)))) /\
  (translate_iter ctx var_ty (JIter_Range [e] _ _) =
    Range (Literal var_ty (IntL (integer$int_of_num 0)))
          (translate_expr ctx e)) /\
  (translate_iter ctx var_ty (JIter_Range (s::e::_) _ _) =
    Range (translate_expr ctx s) (translate_expr ctx e)) /\
  (translate_iter ctx var_ty (JIter_Array e _) =
    Array (translate_expr ctx e))
End


(* ===== Statement Translation ===== *)

Definition translate_stmt_def:
  (translate_stmt ctx JS_Pass = Pass) /\
  (translate_stmt ctx JS_Break = Break) /\
  (translate_stmt ctx JS_Continue = Continue) /\
  (translate_stmt ctx (JS_Expr e) = Expr (translate_expr ctx e)) /\
  (translate_stmt ctx (JS_Return NONE) = Return NONE) /\
  (translate_stmt ctx (JS_Return (SOME e)) = Return (SOME (translate_expr ctx e))) /\
  (translate_stmt ctx (JS_Raise NONE) = Raise RaiseBare) /\
  (translate_stmt ctx (JS_Raise (SOME e)) = Raise (RaiseReason (translate_expr ctx e))) /\
  (translate_stmt ctx (JS_Assert test NONE) =
    Assert (translate_expr ctx test) AssertBare) /\
  (translate_stmt ctx (JS_Assert test (SOME msg)) =
    Assert (translate_expr ctx test) (AssertReason (translate_expr ctx msg))) /\
  (translate_stmt ctx (JS_Log (src, name) args) =
    Log (resolve_source_ref ctx src, name) (MAP (translate_expr ctx) args)) /\
  (translate_stmt ctx (JS_If test body orelse) =
    If (translate_expr ctx test)
       (MAP (translate_stmt ctx) body)
       (MAP (translate_stmt ctx) orelse)) /\
  (translate_stmt ctx (JS_For var ty ann iter body) =
    let fallback_ty = translate_decl_type (expr_type_ctx ctx) ty ann in
    let var_ty = lookup_local_type ctx var fallback_ty in
    For var var_ty (translate_iter ctx var_ty iter)
        (get_iter_bound iter) (MAP (translate_stmt ctx) body)) /\
  (translate_stmt ctx (JS_Assign tgt val) =
    Assign (translate_target ctx tgt) (translate_expr ctx val)) /\
  (translate_stmt ctx (JS_AnnAssign var ty ann val) =
    AnnAssign var
      (lookup_local_type ctx var
        (translate_decl_type (expr_type_ctx ctx) ty ann))
      (translate_expr ctx val)) /\
  (translate_stmt ctx (JS_AugAssign tgt op val) =
    AugAssign (expr_type (translate_expr ctx val))
      (translate_base_target ctx tgt) (translate_binop op) (translate_expr ctx val)) /\
  (translate_stmt ctx (JS_Append tgt val) =
    Append (translate_base_target ctx tgt) (translate_expr ctx val))
Termination
  WF_REL_TAC `measure (json_stmt_size o SND)` >>
  rw[] >> simp[json_stmt_size_def]
End


(* ===== Top-level Translation ===== *)

