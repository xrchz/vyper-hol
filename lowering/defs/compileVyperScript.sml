(*
 * Top-Level Vyper Compiler: toplevel list → byte list option
 *
 * Packages the full compilation pipeline:
 *   1. Extract metadata from toplevel list
 *   2. Build per-function compile_env
 *   3. Lower: Vyper AST → Venom IR (via compile_generate_runtime)
 *   4. Optimize: pipeline of Venom passes
 *   5. Codegen: Venom IR → EVM bytecode
 *
 * TOP-LEVEL:
 *   compile_vyper          -- toplevel list → byte list option
 *   compile_vyper_eval     -- bounded-dataflow evaluator variant
 *
 * The storage/transient layout (variable name → slot) comes from the
 * Python compiler's annotated AST, NOT recomputed here.
 * fn_eom is internal to the Venom pipeline and codegen.
 *)

Theory compileVyper
Ancestors
  exprLowering
  vyperCompiler
  venomPipeline
  codegen
  selectorDispatch
  jumptableUtils
  vyperContext
  vyperEvent
  compileEnv
  vyperAST
  byte


(* ===== Struct Fields Map ===== *)

(* Compute memory bytes for a type given a struct field map.
   Same as type_memory_bytes but takes sft directly (no cenv). *)
Definition type_mem_bytes_def:
  type_mem_bytes (sft : string -> (string # type # num) list)
    (BaseT (BytesT (Dynamic n))) = 32 + ((n + 31) DIV 32) * 32 ∧
  type_mem_bytes sft (BaseT (StringT n)) = 32 + ((n + 31) DIV 32) * 32 ∧
  type_mem_bytes sft (BaseT _) = 32 ∧
  type_mem_bytes sft (FlagT _) = 32 ∧
  type_mem_bytes sft (ArrayT elem_ty (Fixed n)) =
    n * type_mem_bytes sft elem_ty ∧
  type_mem_bytes sft (ArrayT elem_ty (Dynamic n)) =
    32 + n * type_mem_bytes sft elem_ty ∧
  type_mem_bytes sft (StructT nsid) =
    SUM (MAP (SND o SND) (sft (nsid_to_string nsid))) ∧
  type_mem_bytes sft (TupleT tys) =
    SUM (MAP (type_mem_bytes sft) tys) ∧
  type_mem_bytes sft NoneT = 0
Termination
  WF_REL_TAC `measure (type_size o SND)`
End

Definition build_struct_fields_one_def:
  build_struct_fields_one sft (args : (string # type) list) =
    MAP (λ(name, ty). (name, ty, type_mem_bytes sft ty)) args
End

Definition build_struct_fields_map_def:
  build_struct_fields_map [] (sft : (string, (string # type # num) list) fmap) = sft ∧
  build_struct_fields_map (top :: rest) sft =
    case top of
      StructDecl sname args =>
        build_struct_fields_map rest
          (sft |+ (sname, build_struct_fields_one (get_struct_fields sft) args))
    | _ => build_struct_fields_map rest sft
End

Definition make_struct_fields_map_def:
  make_struct_fields_map tops = build_struct_fields_map tops FEMPTY
End

(* ===== Simple AST Extractors ===== *)

Definition build_flag_member_id_one_def:
  build_flag_member_id_one [] (idx : num) = (K 0n) ∧
  build_flag_member_id_one (m :: ms) idx =
    let rest = build_flag_member_id_one ms (idx + 1) in
    (λname. if name = m then idx else rest name)
End

Definition build_flag_info_def:
  build_flag_info [] fmid fnm = (fmid, fnm) ∧
  build_flag_info (top :: rest) fmid fnm =
    case top of
      FlagDecl fname members =>
        build_flag_info rest
          (λfn. if fn = fname then build_flag_member_id_one members 0
                else fmid fn)
          (λfn. if fn = fname then LENGTH members else fnm fn)
    | _ => build_flag_info rest fmid fnm
End

Definition build_var_type_map_def:
  build_var_type_map ([] : toplevel list) = (K NONE : string -> type option) ∧
  build_var_type_map (top :: rest) =
    case top of
      VariableDecl _ _ vname ty _ =>
        (λn. if n = vname then SOME ty else build_var_type_map rest n)
    | _ => build_var_type_map rest
End

(* Sum of memory_bytes_required for all immutable variables.
   Mirrors Python: module_t.immutable_section_bytes. *)
Definition compute_immutables_len_def:
  compute_immutables_len sft ([] : toplevel list) = (0 : num) ∧
  compute_immutables_len sft (top :: rest) =
    (case top of
       VariableDecl _ Immutable _ ty _ =>
         type_mem_bytes sft ty + compute_immutables_len sft rest
     | _ => compute_immutables_len sft rest)
End

Definition build_is_hashmap_def:
  build_is_hashmap ([] : toplevel list) = (K F : string -> bool) ∧
  build_is_hashmap (top :: rest) =
    case top of
      HashMapDecl _ _ hname _ _ _ =>
        (λn. if n = hname then T else build_is_hashmap rest n)
    | _ => build_is_hashmap rest
End

(* ===== Event Info ===== *)

(* event_hash is shared with the source semantics in vyperEventTheory.
   is_bytestring_type is in compileEnvTheory. *)

Definition build_event_info_def:
  build_event_info tenv ([] : toplevel list) eim = eim ∧
  build_event_info tenv (top :: rest) eim =
    case top of
      EventDecl ename args_indexed =>
        let arg_types = MAP (SND o FST) args_indexed in
        let ehash = event_hash tenv ename arg_types in
        let indexed_flags = MAP SND args_indexed in
        build_event_info tenv rest
          (λn. if n = ename then SOME (ehash, arg_types, indexed_flags) else eim n)
    | _ => build_event_info tenv rest eim
End

Theorem build_event_info_lookup_event_metadata_in:
  ∀tops.
    event_decl_unique ename tops ⇒
    ∀eim.
      build_event_info tenv tops eim ename =
      case lookup_event_metadata_in tenv ename tops of
      | NONE => eim ename
      | SOME metadata => SOME metadata
Proof
  Induct_on `tops` >>
  simp[build_event_info_def, lookup_event_metadata_in_def] >>
  Cases_on `h` >>
  gvs[build_event_info_def, lookup_event_metadata_in_def,
      event_decl_unique_def] >>
  Cases_on `s = ename` >> gvs[] >>
  Cases_on `lookup_event_metadata_in tenv ename tops`
  >- simp[] >>
  drule lookup_event_metadata_in_some >>
  strip_tac >>
  strip_tac >>
  qpat_x_assum `∀args args'. _`
    (qspecl_then [`l`, `args`] mp_tac) >>
  simp[]
QED

Theorem build_event_info_empty_lookup_event_metadata_in:
  event_decl_unique ename tops ⇒
  build_event_info tenv tops (K NONE) ename =
  lookup_event_metadata_in tenv ename tops
Proof
  strip_tac >>
  drule build_event_info_lookup_event_metadata_in >>
  Cases_on `lookup_event_metadata_in tenv ename tops` >> simp[]
QED

Theorem build_event_info_empty_lookup_event_metadata:
  ALOOKUP sources target = SOME mods ⇒
  ALOOKUP mods NONE = SOME tops ⇒
  event_decl_unique ename tops ⇒
  build_event_info tenv tops (K NONE) ename =
  lookup_event_metadata tenv sources target (NONE, ename)
Proof
  simp[lookup_event_metadata_def,
       build_event_info_empty_lookup_event_metadata_in]
QED

(* ===== Nonreentrant Keys ===== *)

Definition assign_nkeys_def:
  assign_nkeys ([] : toplevel list) (next : num) = (K 0n : string -> num) ∧
  assign_nkeys (top :: rest) next =
    case top of
      FunctionDecl _ _ T _ fname _ _ _ _ =>
        let nkey_map = assign_nkeys rest (next + 1) in
        (λn. if n = fname then next else nkey_map n)
    | _ => assign_nkeys rest next
End

(* ===== Function Classification ===== *)

(* Classify functions into external, internal, fallback, and constructor.
   Deploy (__init__) goes into a separate ctor slot, NOT into internal fns.
   In Python, runtime and deploy are separate IRContexts:
   - Runtime: external fns + internal fns (is_ctor_context=False)
   - Deploy: __init__ + ctor-reachable internal fns (is_ctor_context=True)
   raw_return is threaded through the tuples for ce_raw_return. *)
Definition classify_function_def:
  classify_function (FunctionDecl vis mut nr rr fname fargs dflts ret body)
    (exts, ints, fb, ctor) =
    (case vis of
       External =>
         if fname = "__default__" then
           (exts, ints, SOME (mut, nr, rr, fname, fargs, dflts, ret, body),
            ctor)
         else
           ((mut, nr, rr, fname, fargs, dflts, ret, body) :: exts,
            ints, fb, ctor)
     | Internal =>
         (exts,
          (mut, nr, rr, fname, fargs, dflts, ret, body) :: ints,
          fb, ctor)
     | Deploy =>
         (exts, ints, fb,
          SOME (mut, nr, rr, fname, fargs, dflts, ret, body))) ∧
  classify_function _ acc = acc
End

Definition classify_functions_def:
  classify_functions tops = FOLDR classify_function ([], [], NONE, NONE) tops
End

(* ===== Memory Allocation ===== *)

Definition allocate_args_def:
  allocate_args sft [] (offset : num) vars = (vars, offset) ∧
  allocate_args sft ((name, ty) :: rest) offset vars =
    let sz = type_mem_bytes sft ty in
    allocate_args sft rest (offset + sz)
      (vars |+ (name, MemLoc offset sz))
End

Definition allocate_internal_special_vars_def:
  allocate_internal_special_vars has_return_buf offset vars =
    let (vars1, off1) =
      if has_return_buf then
        (vars |+ ("__return_buf__", MemLoc offset 32), offset + 32)
      else (vars, offset) in
    (vars1 |+ ("__return_pc__", MemLoc off1 32), off1 + 32)
End

Definition add_module_var_locations_def:
  add_module_var_locations ([] : toplevel list) vars = vars ∧
  add_module_var_locations (top :: rest) vars =
    let vars' =
      case top of
        VariableDecl _ Storage name _ (SOME slot) =>
          vars |+ (name, StorageLoc (n2w slot))
      | VariableDecl _ Transient name _ (SOME slot) =>
          vars |+ (name, TransientLoc (n2w slot))
      | HashMapDecl _ transient name _ _ (SOME slot) =>
          vars |+ (name,
            if transient then TransientLoc (n2w slot)
            else StorageLoc (n2w slot))
      | _ => vars in
    add_module_var_locations rest vars'
End

(* ===== Local Variable Collection ===== *)

Definition collect_locals_def:
  collect_locals ([] : stmt list) = ([] : (string # type) list) ∧
  collect_locals (AnnAssign id ty _ :: rest) =
    (id, ty) :: collect_locals rest ∧
  collect_locals (If _ then_stmts else_stmts :: rest) =
    collect_locals then_stmts ++
    collect_locals else_stmts ++
    collect_locals rest ∧
  collect_locals (For id ty _ _ for_body :: rest) =
    (id, ty) :: collect_locals for_body ++ collect_locals rest ∧
  collect_locals (_ :: rest) = collect_locals rest
End

(* ===== Dynamic Array Capacity ===== *)

Definition dynarray_capacity_of_type_def:
  dynarray_capacity_of_type (ArrayT _ (Dynamic n)) = SOME n ∧
  dynarray_capacity_of_type _ = NONE
End

Definition build_dynarray_capacity_def:
  build_dynarray_capacity ([] : (string # type) list) = (K 0n : string -> num) ∧
  build_dynarray_capacity ((vname, ty) :: rest) =
    let rest_map = build_dynarray_capacity rest in
    case dynarray_capacity_of_type ty of
      SOME n => (λs. if s = vname then n else rest_map s)
    | NONE => rest_map
End

Definition collect_module_vars_def:
  collect_module_vars ([] : toplevel list) = ([] : (string # type) list) ∧
  collect_module_vars (top :: rest) =
    (case top of
       VariableDecl _ _ vname ty _ => [(vname, ty)]
     | _ => []) ++ collect_module_vars rest
End

(* ===== Method ID Map ===== *)

Definition build_method_id_map_def:
  build_method_id_map tenv ([] : toplevel list) = (K 0n : string -> num) ∧
  build_method_id_map tenv (top :: rest) =
    let rest_map = build_method_id_map tenv rest in
    case top of
      FunctionDecl External _ _ _ fname fargs _ _ _ =>
        let abi_types = vyper_to_abi_types tenv (MAP SND fargs) in
        let sel_bytes = function_selector fname abi_types in
        let sel_num = w2n (calldata_method_id sel_bytes) in
        (λs. if s = fname then sel_num else rest_map s)
    | _ => rest_map
End

(* ===== Internal Function Info ===== *)

Definition build_func_info_def:
  build_func_info sft ([] : toplevel list) =
    (K (0n, 0n, [] : bool list) : string -> num # num # bool list) ∧
  build_func_info sft (top :: rest) =
    let rest_map = build_func_info sft rest in
    case top of
      FunctionDecl vis _ _ _ fname fargs _ ret _ =>
        if vis = External then rest_map
        else
          let fn_lbl = fname in
          let arg_types = MAP SND fargs in
          let ret_mem = type_mem_bytes sft ret in
          let info = compute_func_info (λn. MAP (FST o SND) (sft n))
                       ret ret_mem arg_types in
          (λs. if s = fn_lbl then info else rest_map s)
    | _ => rest_map
End

(* ===== Positional Args for ABI Decoding ===== *)

Definition build_positional_arg_def:
  build_positional_arg cenv ((name, ty) : string # type) =
    let is_prim = is_word_type ty in
    let is_dyn = is_abi_dynamic cenv.ce_struct_fields ty in
    let abi_sz = abi_embedded_static_size cenv.ce_struct_fields ty in
    let dec = type_to_abi_dec_info cenv.ce_struct_fields cenv ty in
    (name, is_prim, is_dyn, abi_sz, dec)
End

Definition build_positional_args_def:
  build_positional_args cenv args =
    MAP (build_positional_arg cenv) args
End

(* ===== Min Calldata Size ===== *)

Definition min_calldata_size_def:
  min_calldata_size cenv (args : (string # type) list) (n_defaults : num) =
    let required = TAKE (LENGTH args - n_defaults) args in
    let sizes = MAP (λ(_,ty). abi_embedded_static_size cenv.ce_struct_fields ty)
                    required in
    4 + SUM sizes
End
Theorem build_positional_args_single_uint256:
  !cenv name.
    build_positional_args cenv [(name, BaseT (UintT 256))] =
      [(name, T, F, 32, DecPrimWord NoClamp)]
Proof
  simp[build_positional_args_def, build_positional_arg_def,
       is_word_type_def, is_abi_dynamic_def,
       abi_embedded_static_size_def, abi_static_size_def,
       type_to_abi_dec_info_def, type_to_abi_clamp_def]
QED

Theorem min_calldata_size_single_uint256:
  !cenv name.
    min_calldata_size cenv [(name, BaseT (UintT 256))] 0 = 36
Proof
  simp[min_calldata_size_def, abi_embedded_static_size_def,
       is_abi_dynamic_def, abi_static_size_def]
QED


(* ===== Storage Layout from AST ===== *)

(* Extract storage/transient layout from the annotated AST.
   Slots are set on VariableDecl/HashMapDecl during JSON translation. *)
Definition extract_layout_def:
  extract_layout ([] : toplevel list) = (FEMPTY : (string, bytes32) fmap) ∧
  extract_layout (VariableDecl _ (Storage) name _ (SOME slot) :: rest) =
    extract_layout rest |+ (name, n2w slot) ∧
  extract_layout (VariableDecl _ (Transient) name _ (SOME slot) :: rest) =
    extract_layout rest |+ (name, n2w slot) ∧
  extract_layout (HashMapDecl _ _ name _ _ (SOME slot) :: rest) =
    extract_layout rest |+ (name, n2w slot) ∧
  extract_layout (_ :: rest) = extract_layout rest
End

(* ===== Compile Env Construction ===== *)

(* Build a compile_env for a function.
   Storage slots come from the annotated AST (set during JSON translation). *)
Definition build_compile_env_def:
  build_compile_env tops
    vis (mut : function_mutability) func_name
    (args : (string # type) list) (ret_type : type)
    (body : stmt list) (use_transient_locks : bool) =
    let sft = make_struct_fields_map tops in
    let sft_fn = get_struct_fields sft in
    let sft_types = (λname. MAP (FST o SND) (sft_fn name)) in
    let (flag_member_id, flag_n_members) = build_flag_info tops (K (K 0)) (K 0) in
    let storage_layout = extract_layout tops in
    let var_type_map = build_var_type_map tops in
    let is_hashmap = build_is_hashmap tops in
    let tenv = type_env tops in
    let event_info =
          build_event_info tenv tops
            ((K NONE) : string -> (num # type list # bool list) option) in
    let is_external = (vis = External) in
    let rc = returns_stack_count sft_types ret_type in
    let has_return_buf = (rc = 0 ∧ ret_type ≠ NoneT) in
    let module_vars = add_module_var_locations tops FEMPTY in
    let (arg_vars, args_end) = allocate_args sft_fn args 0 module_vars in
    let locals = collect_locals body in
    let (local_vars, locals_end) = allocate_args sft_fn locals args_end arg_vars in
    let (all_vars, total_mem) =
      if is_external then (local_vars, locals_end)
      else allocate_internal_special_vars has_return_buf locals_end local_vars in
    let ret_buf = if has_return_buf then SOME (total_mem : num) else NONE in
    let all_decls = collect_module_vars tops ++ args ++ locals in
    let dynarray_cap = build_dynarray_capacity all_decls in
    let method_id_map = build_method_id_map tenv tops in
    let func_info = build_func_info sft_fn tops in
    let local_var_type = (λn.
          case ALOOKUP (REVERSE (args ++ locals)) n of
            SOME ty => SOME ty
          | NONE => var_type_map n) in
    <| ce_target := prague_capabilities;
       ce_vars := all_vars;
       ce_storage_layout := storage_layout;
       (* TODO: NONE = main module. For multi-module (imports), should
          be SOME src_id. Currently single-module only. *)
       ce_module := NONE;
       ce_struct_fields := sft;
       ce_dynarray_capacity := dynarray_cap;
       ce_method_id := method_id_map;
       ce_flag_member_id := flag_member_id;
       ce_flag_n_members := flag_n_members;
       ce_var_type := local_var_type;
       ce_is_hashmap := is_hashmap;
       ce_event_info := event_info;
       ce_type_env := tenv;
       ce_returns_count := rc;
       ce_return_buf := ret_buf;
       ce_is_external := is_external;
       ce_ret_enc_info := AbiPrimWord;
       ce_ret_dec_info := DecPrimWord NoClamp;
       ce_max_return_size := 0;
       (* Default: overridden by package_internal_fn for ctor context *)
       ce_is_ctor := (vis = Deploy);
       ce_func_info := func_info;
       ce_nonreentrant := (F, 0n, use_transient_locks, mut = View);
       (* Default: overridden by package_*_fn from FunctionDecl raw_return field *)
       ce_raw_return := F
    |> : compile_env
End

Theorem build_compile_env_ce_target[simp]:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_target = prague_capabilities
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_ce_struct_fields:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_struct_fields = make_struct_fields_map tops
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_ce_func_info:
  !tops vis mut func_name args ret_type (body : stmt list) use_trans.
    (build_compile_env tops vis mut func_name args ret_type body use_trans).
      ce_func_info =
    build_func_info (get_struct_fields (make_struct_fields_map tops)) tops
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem build_compile_env_external_single_uint_arg_lookup:
  !tops mut func_name arg_name ret_type (body : stmt list) use_trans.
    add_module_var_locations tops FEMPTY = FEMPTY /\
    collect_locals body = [] ==>
    FLOOKUP
      (build_compile_env tops External mut func_name
         [(arg_name, BaseT (UintT 256))] ret_type body use_trans).ce_vars
      arg_name = SOME (MemLoc 0 32)
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[allocate_args_def, type_mem_bytes_def])
  >> EVAL_TAC
QED

Theorem build_compile_env_external_single_uint_arg_no_return_pc:
  !tops mut func_name arg_name ret_type (body : stmt list) use_trans.
    add_module_var_locations tops FEMPTY = FEMPTY /\
    collect_locals body = [] /\
    arg_name <> "__return_pc__" ==>
    FLOOKUP
      (build_compile_env tops External mut func_name
         [(arg_name, BaseT (UintT 256))] ret_type body use_trans).ce_vars
      "__return_pc__" = NONE
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[allocate_args_def, type_mem_bytes_def])
  >> EVAL_TAC
  >> gvs[]
QED


Definition update_cenv_ret_abi_def:
  update_cenv_ret_abi cenv ret_type =
    let enc_info = type_to_abi_enc_info cenv.ce_struct_fields cenv ret_type in
    let dec_info = type_to_abi_dec_info cenv.ce_struct_fields cenv ret_type in
    let max_ret = abi_size_bound cenv.ce_struct_fields ret_type in
    cenv with <| ce_ret_enc_info := enc_info;
                 ce_ret_dec_info := dec_info;
                 ce_max_return_size := max_ret |>
End

Definition update_cenv_nonreentrant_def:
  update_cenv_nonreentrant cenv is_nr nkey use_trans is_view =
    cenv with ce_nonreentrant := (is_nr, nkey, use_trans, is_view)
End

Theorem update_cenv_ret_abi_ce_target[simp]:
  (update_cenv_ret_abi cenv ret_type).ce_target = cenv.ce_target
Proof
  simp[update_cenv_ret_abi_def]
QED

Theorem update_cenv_nonreentrant_ce_target[simp]:
  (update_cenv_nonreentrant cenv nr nkey use_trans is_view).ce_target =
  cenv.ce_target
Proof
  simp[update_cenv_nonreentrant_def]
QED
Theorem compile_env_ce_raw_return_fupd[simp]:
  (cenv with ce_raw_return := rr).ce_target = cenv.ce_target
Proof
  Cases_on `cenv` >> simp[]
QED

Theorem compile_env_ce_is_ctor_fupd[simp]:
  (cenv with ce_is_ctor := is_ctor).ce_target = cenv.ce_target
Proof
  Cases_on `cenv` >> simp[]
QED


Theorem compile_env_target_update_id:
  cenv.ce_target = target ==>
  (cenv with ce_target := target) = cenv
Proof
  Cases_on `cenv` >> simp[compile_env_component_equality]
QED

(* ===== Selector Construction ===== *)

Definition selector_has_trailing_zeroes_def:
  selector_has_trailing_zeroes (sel_num : num) = (sel_num MOD 256 = 0)
End

Definition compute_selector_def:
  compute_selector tenv func_name (arg_types : type list) =
    let abi_types = vyper_to_abi_types tenv arg_types in
    let sel_bytes = function_selector func_name abi_types in
    let sel_num = w2n (calldata_method_id sel_bytes) in
    let entry_lbl = "fn_" ++ func_name in
    (sel_num, entry_lbl, selector_has_trailing_zeroes sel_num)
End

Definition build_selectors_def:
  build_selectors tenv [] = [] ∧
  build_selectors tenv
    ((_, _, _, fname, fargs, _, _, _) :: rest) =
    compute_selector tenv fname (MAP SND fargs) ::
    build_selectors tenv rest
End

(* ===== Function Packaging ===== *)

Definition package_external_fn_def:
  package_external_fn tops use_trans nkey_map
    (mut, nr, rr, fname, fargs, dflts, ret, body) =
    let entry_lbl = "fn_" ++ fname in
    let cenv_base = build_compile_env tops
                      External mut fname fargs ret body use_trans in
    let cenv0 = cenv_base with ce_raw_return := rr in
    let cenv = if ret ≠ NoneT then update_cenv_ret_abi cenv0 ret
               else cenv0 in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let pos_args = build_positional_args cenv_final fargs in
    let min_cds = min_calldata_size cenv_final fargs (LENGTH dflts) in
    let is_payable = (mut = Payable) in
    let is_view = (mut = View) in
    (entry_lbl, cenv_final, pos_args, min_cds,
     is_payable, nr, nkey, use_trans, is_view,
     body, SOME ret)
End

(* Package an internal function for compilation.
   is_ctor_context: T in deploy context (internal fns called from __init__),
                    F in runtime context.
   Mirrors Python: _generate_internal_function(is_ctor_context=...) *)
Definition package_internal_fn_def:
  package_internal_fn tops use_trans nkey_map is_ctor_context immutables_len
    (mut, nr, rr, fname, fargs, _, ret, body) =
    let fn_lbl = fname in
    let sft = make_struct_fields_map tops in
    let sft_fn = get_struct_fields sft in
    let sft_types = (λname. MAP (FST o SND) (sft_fn name)) in
    let vis = if is_ctor_context then Deploy else Internal in
    let cenv = (build_compile_env tops
                  vis mut fname fargs ret body use_trans)
                 with <| ce_is_ctor := is_ctor_context;
                         ce_raw_return := rr |> in
    let rc = returns_stack_count sft_types ret in
    let has_ret_buf = (rc = 0 ∧ ret ≠ NoneT) in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let is_view = (mut = View) in
    let pvs = compute_pass_via_stack (MAP SND fargs) rc in
    let params = ZIP (MAP FST fargs, pvs) in
    (fn_lbl, cenv_final, params, has_ret_buf,
     nr, nkey, use_trans, is_view,
     is_ctor_context, (if is_ctor_context then immutables_len else 0n),
     body, SOME ret)
End

Theorem package_internal_fn_call_label:
  !tops use_trans nkey_map is_ctor_context immutables_len
   mut nr rr fname fargs dflts ret body.
    FST (package_internal_fn tops use_trans nkey_map is_ctor_context
           immutables_len
           (mut, nr, rr, fname, fargs, dflts, ret, body)) =
    nsid_to_string (NONE, fname)
Proof
  simp[package_internal_fn_def, nsid_to_string_def]
QED

Definition source_internal_fn_descriptor_def:
  source_internal_fn_descriptor tops
    (mut, nr, rr, fname, fargs, dflts, ret, body) =
    let sft_types =
      (\name. MAP (FST o SND)
                    (get_struct_fields (make_struct_fields_map tops) name)) in
    let rc = returns_stack_count sft_types ret in
    (fname, rc = 0 /\ ret <> NoneT, rc)
End

Theorem build_compile_env_returns_count:
  !tops vis mut fname fargs ret body use_trans.
    (build_compile_env tops vis mut fname fargs ret body use_trans).
      ce_returns_count =
    returns_stack_count
      (\name. MAP (FST o SND)
                    (get_struct_fields (make_struct_fields_map tops) name)) ret
Proof
  rpt strip_tac
  >> simp[build_compile_env_def]
  >> rpt (pairarg_tac >> gvs[])
QED

Theorem package_internal_fn_descriptor:
  !tops use_trans nkey_map is_ctor_context immutables_len
   mut nr rr fname fargs dflts ret body.
    internal_fn_descriptors
      [package_internal_fn tops use_trans nkey_map is_ctor_context
         immutables_len
         (mut, nr, rr, fname, fargs, dflts, ret, body)] =
    [source_internal_fn_descriptor tops
       (mut, nr, rr, fname, fargs, dflts, ret, body)]
Proof
  simp[internal_fn_descriptors_def, package_internal_fn_def,
       source_internal_fn_descriptor_def, update_cenv_nonreentrant_def,
       build_compile_env_returns_count]
QED

Theorem internal_fn_descriptors_MAP_package_internal_fn:
  !fs tops use_trans nkey_map is_ctor_context immutables_len.
    internal_fn_descriptors
      (MAP (package_internal_fn tops use_trans nkey_map is_ctor_context
              immutables_len) fs) =
    MAP (source_internal_fn_descriptor tops) fs
Proof
  Induct
  >- simp[internal_fn_descriptors_def]
  >> Cases_on `h`
  >> PairCases_on `r`
  >> simp[internal_fn_descriptors_def, package_internal_fn_def,
          source_internal_fn_descriptor_def, update_cenv_nonreentrant_def,
          build_compile_env_returns_count]
QED

Definition package_fallback_fn_def:
  package_fallback_fn tops use_trans nkey_map NONE = NONE ∧
  package_fallback_fn tops use_trans nkey_map
    (SOME (mut, nr, rr, fname, fargs, _, ret, body)) =
    let cenv = (build_compile_env tops
                  External mut fname fargs ret body use_trans)
                 with ce_raw_return := rr in
    let nkey = nkey_map fname in
    let is_payable = (mut = Payable) in
    let is_view = (mut = View) in
    SOME (cenv, is_payable, nr, nkey, use_trans, is_view,
          body, if ret = NoneT then NONE else SOME ret)
End

(* ===== Constructor Packaging ===== *)

(* Package the constructor for deploy-phase compilation.
   ctor_fn: the Deploy function from classify_functions.
   Returns: (cenv, args, is_payable, is_nr, nkey, use_trans, body, ret). *)
Definition package_constructor_def:
  package_constructor tops use_trans nkey_map
    (mut, nr, rr, fname, fargs, _, ret, body) =
    let cenv = (build_compile_env tops
                  Deploy mut fname fargs ret body use_trans)
                 with <| ce_is_ctor := T; ce_raw_return := rr |> in
    let nkey = nkey_map fname in
    let cenv_final = update_cenv_nonreentrant cenv nr nkey use_trans
                       (mut = View) in
    let pos_args = build_positional_args cenv_final fargs in
    (cenv_final, pos_args, (mut = Payable), nr, nkey, use_trans, body, ret)
End

(* ===== Full Compilation ===== *)

(* compile_vyper: the top-level compiler function.

   Two-phase compilation matching Python's module.py:
   Phase 1 (runtime): selector dispatch + external fns + internal fns (is_ctor=F)
   Phase 2 (deploy):  __init__ + ctor-reachable internal fns (is_ctor=T)

   Returns: SOME (deploy_bytecode, runtime_bytecode) or NONE on codegen failure.

   Takes:
   - tops: Vyper AST (toplevel list, with storage slots annotated)
   - pipeline: Venom optimization passes
   - dispatch_strategy: Linear, Sparse, or Dense

   Derived from AST (not external inputs):
   - immutables_len: sum of memory_bytes_required for Immutable vars
   - deploy data section: [runtime_bytecode] (built internally)

   Storage/transient slots come from the annotated AST.
   fn_eom is internal to the Venom pipeline (codegen defaults to 0).
   raw_return is per-function (from @raw_return decorator). *)
(* Build entry_info map from packaged external functions.
   Each packaged fn has (entry_lbl, cenv, pos_args, min_cds,
   is_payable, nr, nkey, use_trans, is_view, body, ret).
   entry_info: method_id -> (label, min_cds, is_nonpayable). *)
Definition build_dense_entry_info_def:
  build_dense_entry_info [] [] = (K ("", 0n, F) : num -> string # num # bool) /\
  build_dense_entry_info ((sel_num, _, _) :: srest)
    ((entry_lbl, _, _, min_cds, is_payable, _, _, _, _, _, _) :: erest) =
    (let rest_map = build_dense_entry_info srest erest in
     (\n. if n = sel_num then (entry_lbl, min_cds, ~is_payable)
          else rest_map n)) /\
  build_dense_entry_info _ _ = K ("", 0n, F)
End
(* Install the one resolved target into packaged function environments without
   changing source-visible ABI metadata or any other package field. *)
Definition set_external_package_target_def:
  set_external_package_target target
    (entry_lbl, cenv, pos_args, min_cds, is_payable, nr, nkey, use_trans,
     is_view, body, ret) =
    (entry_lbl, cenv with ce_target := target, pos_args, min_cds, is_payable,
     nr, nkey, use_trans, is_view, body, ret)
End

Definition set_internal_package_target_def:
  set_internal_package_target target
    (fn_lbl, cenv, params, has_ret_buf, nr, nkey, use_trans, is_view,
     is_ctor, immutables_len, body, ret) =
    (fn_lbl, cenv with ce_target := target, params, has_ret_buf, nr, nkey,
     use_trans, is_view, is_ctor, immutables_len, body, ret)
End

Definition set_fallback_package_target_def:
  set_fallback_package_target target NONE = NONE /\
  set_fallback_package_target target
    (SOME (cenv, is_payable, nr, nkey, use_trans, is_view, body, ret)) =
    SOME (cenv with ce_target := target, is_payable, nr, nkey, use_trans,
          is_view, body, ret)
End

Definition set_constructor_package_target_def:
  set_constructor_package_target target
    (cenv, pos_args, is_payable, nr, nkey, use_trans, body, ret) =
    (cenv with ce_target := target, pos_args, is_payable, nr, nkey,
     use_trans, body, ret)
End

Theorem internal_fn_descriptors_set_internal_package_target:
  internal_fn_descriptors
    (MAP (set_internal_package_target target) internal_fns) =
  internal_fn_descriptors internal_fns
Proof
  Induct_on `internal_fns`
  >- simp[internal_fn_descriptors_def]
  >> Cases_on `h` >> PairCases_on `r`
  >> simp[set_internal_package_target_def, internal_fn_descriptors_def]
QED

Theorem set_internal_package_target_capability:
  set_internal_package_target target
    (fn_lbl, cenv, params, has_ret_buf, nr, nkey, use_trans, is_view,
     is_ctor, immutables_len, body, ret) =
    (fn_lbl, cenv', params, has_ret_buf, nr, nkey, use_trans, is_view,
     is_ctor, immutables_len, body, ret) ==>
  cenv'.ce_target = target /\
  cenv'.ce_returns_count = cenv.ce_returns_count
Proof
  simp[set_internal_package_target_def] >> strip_tac >> gvs[]
QED

Theorem set_external_package_target_prague[simp]:
  set_external_package_target prague_capabilities
    (package_external_fn tops use_trans nkey_map source) =
  package_external_fn tops use_trans nkey_map source
Proof
  Cases_on `source` >> PairCases_on `r` >>
  simp[set_external_package_target_def, package_external_fn_def] >>
  irule compile_env_target_update_id >> IF_CASES_TAC >> simp[]
QED

Theorem set_internal_package_target_prague[simp]:
  set_internal_package_target prague_capabilities
    (package_internal_fn tops use_trans nkey_map is_ctor immutables_len source) =
  package_internal_fn tops use_trans nkey_map is_ctor immutables_len source
Proof
  Cases_on `source` >> PairCases_on `r` >>
  simp[set_internal_package_target_def, package_internal_fn_def] >>
  irule compile_env_target_update_id >> simp[]
QED

Theorem set_fallback_package_target_prague[simp]:
  set_fallback_package_target prague_capabilities
    (package_fallback_fn tops use_trans nkey_map source) =
  package_fallback_fn tops use_trans nkey_map source
Proof
  Cases_on `source`
  >- simp[set_fallback_package_target_def, package_fallback_fn_def]
  >> Cases_on `x` >> PairCases_on `r` >>
  simp[set_fallback_package_target_def, package_fallback_fn_def] >>
  irule compile_env_target_update_id >> simp[]
QED

Theorem set_constructor_package_target_prague[simp]:
  set_constructor_package_target prague_capabilities
    (package_constructor tops use_trans nkey_map source) =
  package_constructor tops use_trans nkey_map source
Proof
  Cases_on `source` >> PairCases_on `r` >>
  simp[set_constructor_package_target_def, package_constructor_def] >>
  irule compile_env_target_update_id >> simp[]
QED

Theorem set_external_package_target_all[simp]:
  set_external_package_target (K T)
    (package_external_fn tops use_trans nkey_map source) =
  package_external_fn tops use_trans nkey_map source
Proof
  rw[GSYM venomPolicyTypesTheory.prague_capabilities_def]
QED

Theorem set_internal_package_target_all[simp]:
  set_internal_package_target (K T)
    (package_internal_fn tops use_trans nkey_map is_ctor immutables_len source) =
  package_internal_fn tops use_trans nkey_map is_ctor immutables_len source
Proof
  rw[GSYM venomPolicyTypesTheory.prague_capabilities_def]
QED

Theorem set_fallback_package_target_all[simp]:
  set_fallback_package_target (K T)
    (package_fallback_fn tops use_trans nkey_map source) =
  package_fallback_fn tops use_trans nkey_map source
Proof
  rw[GSYM venomPolicyTypesTheory.prague_capabilities_def]
QED

Theorem set_constructor_package_target_all[simp]:
  set_constructor_package_target (K T)
    (package_constructor tops use_trans nkey_map source) =
  package_constructor tops use_trans nkey_map source
Proof
  rw[GSYM venomPolicyTypesTheory.prague_capabilities_def]
QED


(* ===== Policy-driven complete-unit lowering ===== *)

(* Package runtime metadata from source, but keep the raw lowering result atomic.
   The checked raw boundary accepts only Linear O1 policies, so no independent
   dispatch or jumptable choice is exposed here. *)
Definition lower_vyper_runtime_unit_def:
  lower_vyper_runtime_unit (tops : toplevel list)
                           (rpolicy : resolved_compiler_policy) =
    let tenv = type_env tops in
    let nkey_map = assign_nkeys tops 0 in
    let use_trans = F in
    let (ext_fns, int_fns, fb_fn, ctor_fn) = classify_functions tops in
    let selectors = build_selectors tenv ext_fns in
    let external_fns =
          MAP (set_external_package_target rpolicy.rpol_target o
               package_external_fn tops use_trans nkey_map) ext_fns in
    let runtime_int_fns =
          MAP (set_internal_package_target rpolicy.rpol_target o
               package_internal_fn tops use_trans nkey_map F 0) int_fns in
    let fallback_fn =
          set_fallback_package_target rpolicy.rpol_target
            (package_fallback_fn tops use_trans nkey_map fb_fn) in
    let entry_info = build_dense_entry_info selectors external_fns in
    run_lowering selectors external_fns runtime_int_fns fallback_fn
      rpolicy 0 0 ([] : dense_bucket list) entry_info "__entry"
End

(* Deploy lowering receives the actual runtime bytes.  Their size and data
   section are both owned by run_deploy_lowering. *)
Definition lower_vyper_deploy_unit_def:
  lower_vyper_deploy_unit (tops : toplevel list)
                          (rpolicy : resolved_compiler_policy)
                          (runtime_bytecode : byte list) =
    let sft = make_struct_fields_map tops in
    let sft_fn = get_struct_fields sft in
    let immutables_len = compute_immutables_len sft_fn tops in
    let nkey_map = assign_nkeys tops 0 in
    let use_trans = F in
    let (ext_fns, int_fns, fb_fn, ctor_fn) = classify_functions tops in
    let has_constructor = IS_SOME ctor_fn in
    let deploy_int_fns =
          if has_constructor then
            MAP (set_internal_package_target rpolicy.rpol_target o
                 package_internal_fn tops use_trans nkey_map T immutables_len)
                int_fns
          else [] in
    let (ctor_cenv, ctor_args, ctor_payable, ctor_nr, ctor_nkey,
         ctor_trans, ctor_body, ctor_ret) =
      set_constructor_package_target rpolicy.rpol_target
        (case ctor_fn of
           SOME cf => package_constructor tops use_trans nkey_map cf
         | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                    F, F, 0n, F, ([] : stmt list), NoneT)) in
    run_deploy_lowering has_constructor rpolicy runtime_bytecode
      immutables_len ctor_args 0 deploy_int_fns ctor_cenv ctor_body
      ctor_payable ctor_nr ctor_nkey ctor_trans "__deploy"
End


(* Run one complete compilation unit through a resolved-policy pipeline and
   reject any output whose final-assembly policy disagrees with that policy. *)
Definition checked_unit_pipeline_def:
  checked_unit_pipeline
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (rpolicy : resolved_compiler_policy)
    (unit : compilation_unit) =
    case pipeline rpolicy unit of
      NONE => NONE
    | SOME out =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen finalizer rpolicy out.po_unit
End

(* Bounded planning is deliberately exposed only as a testing boundary. *)
Definition finalize_codegen_fuel_for_testing_def:
  finalize_codegen_fuel_for_testing fuel
    (finalizer : assembly_finalizer)
    (rpolicy : resolved_compiler_policy)
    (unit : compilation_unit) =
    case codegen_assembly_fuel fuel rpolicy unit of
      NONE => NONE
    | SOME asm =>
        case finalizer rpolicy asm of
          NONE => NONE
        | SOME finalized_asm =>
            if assembly_target_safe rpolicy.rpol_target finalized_asm
            then SOME (assemble finalized_asm)
            else NONE
End

Definition checked_unit_pipeline_fuel_for_testing_def:
  checked_unit_pipeline_fuel_for_testing fuel
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (rpolicy : resolved_compiler_policy)
    (unit : compilation_unit) =
    case pipeline rpolicy unit of
      NONE => NONE
    | SOME out =>
        if out.po_final_assembly <> rpolicy.rpol_final_assembly then NONE
        else finalize_codegen_fuel_for_testing fuel finalizer rpolicy out.po_unit
End

(* Closed executable probes for the checked complete-unit boundary. *)
Theorem lower_vyper_runtime_unit_empty_prague:
  IS_SOME
    (lower_vyper_runtime_unit ([] : toplevel list)
      <| rpol_target := prague_capabilities;
         rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>)
Proof
  EVAL_TAC >> simp[finite_mapTheory.FEVERY_FEMPTY,
                    venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
QED

Theorem lower_vyper_deploy_unit_empty_installs_runtime:
  case lower_vyper_deploy_unit ([] : toplevel list)
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |>
         ([170w; 187w] : byte list) of
    NONE => F
  | SOME u =>
      MEM <| ds_label := "runtime_begin";
             ds_items := [DataBytes ([170w; 187w] : byte list)] |>
          u.cu_data_segment
Proof
  EVAL_TAC >> simp[finite_mapTheory.FEVERY_FEMPTY,
                    venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
QED

Theorem lower_vyper_runtime_unit_rejects_missing_mcopy:
  lower_vyper_runtime_unit ([] : toplevel list)
    <| rpol_target := (\c. c <> CapMcopy);
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |> = NONE
Proof
  EVAL_TAC
QED

Theorem lower_vyper_runtime_unit_rejects_malformed_dispatch:
  lower_vyper_runtime_unit ([] : toplevel list)
    <| rpol_target := prague_capabilities;
       rpol_frontend_dispatch := Sparse;
       rpol_final_assembly := FAP_Optimize |> = NONE
Proof
  EVAL_TAC
QED
Definition compile_vyper_with_def:
  compile_vyper_with
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (policy : compiler_policy)
    (tops : toplevel list) =
    case resolve_o1_policy policy of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME runtime_unit =>
            case checked_unit_pipeline pipeline finalizer rpolicy runtime_unit of
              NONE => NONE
            | SOME runtime_bytecode =>
                case lower_vyper_deploy_unit tops rpolicy runtime_bytecode of
                  NONE => NONE
                | SOME deploy_unit =>
                    case checked_unit_pipeline pipeline finalizer rpolicy deploy_unit of
                      NONE => NONE
                    | SOME deploy_bytecode =>
                        SOME (deploy_bytecode, runtime_bytecode)
End

(* The bounded wrapper mirrors the normative unit sequencing exactly, but is
   named explicitly as a testing-only interface. *)
Definition compile_vyper_fuel_for_testing_def:
  compile_vyper_fuel_for_testing fuel
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    (finalizer : assembly_finalizer)
    (policy : compiler_policy)
    (tops : toplevel list) =
    case resolve_o1_policy policy of
      NONE => NONE
    | SOME rpolicy =>
        case lower_vyper_runtime_unit tops rpolicy of
          NONE => NONE
        | SOME runtime_unit =>
            case checked_unit_pipeline_fuel_for_testing fuel pipeline finalizer
                    rpolicy runtime_unit of
              NONE => NONE
            | SOME runtime_bytecode =>
                case lower_vyper_deploy_unit tops rpolicy runtime_bytecode of
                  NONE => NONE
                | SOME deploy_unit =>
                    case checked_unit_pipeline_fuel_for_testing fuel pipeline finalizer
                            rpolicy deploy_unit of
                      NONE => NONE
                    | SOME deploy_bytecode =>
                        SOME (deploy_bytecode, runtime_bytecode)
End

(* The shortest generic compiler fixes the exact O1 pipeline but leaves target
   policy and final assembly implementation explicit. *)
Definition compile_vyper_def:
  compile_vyper (finalizer : assembly_finalizer)
                (policy : compiler_policy)
                (tops : toplevel list) =
    compile_vyper_with
      (\rpolicy unit.
         run_venom_pipeline (K T) (K T) (K T)
           rpolicy o1_pipeline_spec unit)
      finalizer policy tops
End

(* Prague is only the exact O1 target specialization. *)
Definition compile_vyper_o1_def:
  compile_vyper_o1 (finalizer : assembly_finalizer)
                   (tops : toplevel list) =
    compile_vyper finalizer (o1_policy prague_capabilities) tops
End
