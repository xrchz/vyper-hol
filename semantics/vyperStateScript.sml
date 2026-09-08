Theory vyperState
Ancestors
  arithmetic alist combin option list finite_map pair rich_list
  cv cv_std vfmTypes vfmState vfmContext vfmExecution[ignore_grammar]
  vyperAST vyperMisc vyperValue vyperValueOperation
  vyperStorage vyperContext
Libs
  cv_transLib wordsLib monadsyntax

(* `subscript`s are the possible kinds of keys into HashMaps *)

Datatype:
  subscript
  = ValueSubscript value
  | AttrSubscript identifier
End

(* since HashMaps and storage arrays can only appear at the top level, they are
* not mutually recursive with other `value`s, and we have `toplevel_value`: *)
(* HashMapRef stores a base slot, key type, and value_type for lazy storage access.
   When subscripted:
   - If value_type is HashMapT kt vt, returns HashMapRef with new slot and kt
   - If value_type is Type t, reads from storage at the computed slot
   ArrayRef stores a base slot, element type_value, and bound for lazy storage
   access. When subscripted, computes the element slot offset instead of
   materializing the entire array. *)

Datatype:
  toplevel_value = Value value
                 | HashMapRef bool bytes32 type value_type
                 | ArrayRef bool bytes32 type_value bound
End

Theorem toplevel_value_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperState",Tyop="toplevel_value"}));

Definition is_Value_def[simp]:
  (is_Value (Value _) ⇔ T) ∧
  (is_Value _ ⇔ F)
End

val () = cv_auto_trans is_Value_def;

Definition is_HashMapRef_def[simp]:
  (is_HashMapRef (HashMapRef _ _ _ _) ⇔ T) ∧
  (is_HashMapRef _ ⇔ F)
End

val () = cv_auto_trans is_HashMapRef_def;

(* exception type for interpreter control flow *)
Datatype:
  exception
  = Error error
  | AssertException string
  | BreakException
  | ContinueException
  | ReturnException value
End

(* Machinery for managing variables (local, top-level, mutable, immutable), and
* other stateful data during execution (e.g., EVM account states, logs)*)

(*
We don't use identifiers directly because cv compute prefers num keys
*)

Datatype:
  scope_entry = <|
    assignable: bool
  ; type: type_value
  ; value: value
  |>
End

Type scope = “:num |-> scope_entry”;

(* find a variable in a list of nested scopes *)
Definition lookup_scopes_def:
  lookup_scopes id [] = NONE ∧
  lookup_scopes id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes id rest
  | SOME entry => SOME entry
End

(* lookup only the value (discarding the type) *)
Definition lookup_scopes_val_def:
  lookup_scopes_val id [] = NONE ∧
  lookup_scopes_val id ((env: scope)::rest) =
  case FLOOKUP env id of NONE =>
    lookup_scopes_val id rest
  | SOME entry => SOME entry.value
End

val () = cv_auto_trans lookup_scopes_val_def;

(* find the location of a variable in a list of nested scopes (as well as its
* entry): this is used when assigning to that variable *)
Definition find_containing_scope_def:
  find_containing_scope id ([]:scope list) = NONE ∧
  find_containing_scope id (env::rest) =
  case FLOOKUP env id of NONE =>
    OPTION_MAP (λ(p,q). (env::p, q)) (find_containing_scope id rest)
  | SOME entry => SOME ([], env, entry, rest)
End

val () = cv_auto_trans find_containing_scope_def;

(* Transaction-level, externally observable EVM event. *)
Type log = “:event”;

(* Module-aware immutables: keyed by source_id *)
(* NONE = main contract, SOME n = module with source_id n *)
Type module_immutables = “:(num option, num |-> (type_value # value)) alist”

Definition empty_immutables_def:
  empty_immutables : module_immutables = []
End

val () = cv_auto_trans empty_immutables_def;

Datatype:
  evaluation_state = <|
    immutables: (address, module_immutables) alist
  ; logs: log list
  ; scopes: scope list
  ; accounts: evm_accounts
  ; tStorage: transient_storage
  |>
End

Definition empty_state_def:
  empty_state : evaluation_state = <|
    accounts := empty_accounts;
    immutables := [];
    logs := [];
    scopes := [];
    tStorage := empty_transient_storage
  |>
End

val () = cv_trans empty_state_def;

(* state-exception monad used for the main interpreter *)

Type evaluation_result = “:(α + exception) # evaluation_state”

Definition return_def:
  return x s = (INL x, s) : α evaluation_result
End

val () = cv_auto_trans return_def;

Definition raise_def:
  raise e s = (INR e, s) : α evaluation_result
End

val () = cv_auto_trans raise_def;

Definition bind_def:
  bind f g (s: evaluation_state) : α evaluation_result =
  case f s of (INL x, s) => g x s | (INR e, s) => (INR e, s)
End

Definition ignore_bind_def:
  ignore_bind f g = bind f (λx. g)
End

Definition assert_def:
  assert b e s = ((if b then INL () else INR e), s) : unit evaluation_result
End

val () = cv_auto_trans assert_def;

Definition check_def:
  check b str = assert b (Error (RuntimeError str))
End

val () = cv_auto_trans check_def;

Definition type_check_def:
  type_check b str = assert b (Error (TypeError str))
End

val () = cv_auto_trans type_check_def;

val () = declare_monad ("vyper_evaluation",
  { bind = “bind”, unit = “return”,
    ignorebind = SOME “ignore_bind”, choice = NONE,
    fail = SOME “raise”, guard = SOME “assert”
  });
val () = enable_monad "vyper_evaluation";
val () = enable_monadsyntax();

Theorem bind_apply:
  !f g s. (do v <- f; g v od) s =
    case f s of (INL v,s') => g v s' | (INR e,s') => (INR e,s')
Proof
  rpt gen_tac >> simp[bind_def, pairTheory.UNCURRY]
QED

Theorem ignore_bind_apply:
  !f g s. (do f; g od) s =
    case f s of (INL x,s') => g s' | (INR e,s') => (INR e,s')
Proof
  EVAL_TAC >> simp[bind_def]
QED

Definition try_def:
  try f h s : α evaluation_result =
  case f s of (INR e, s) => h e s | x => x
End

Definition finally_def:
  finally f g s : α evaluation_result =
  case f s of (INL x, s) => ignore_bind g (return x) s
     | (INR e, s) => ignore_bind g (raise e) s
End

Definition lift_option_def:
  lift_option x str =
    case x of SOME v => return v | NONE => raise $ Error (RuntimeError str)
End

val () = lift_option_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Definition lift_sum_def:
  lift_sum x =
    case x of INL v => return v | INR e => raise $ Error e
End

val () = lift_sum_def
  |> SRULE [FUN_EQ_THM, sum_CASE_rator]
  |> cv_auto_trans;

Definition lift_sum_runtime_def:
  lift_sum_runtime x =
    case x of INL v => return v | INR str => raise $ Error (RuntimeError str)
End

val () = lift_sum_runtime_def
  |> SRULE [FUN_EQ_THM, sum_CASE_rator]
  |> cv_auto_trans;

Definition lift_option_type_def:
  lift_option_type x str =
    case x of SOME v => return v | NONE => raise $ Error (TypeError str)
End

val () = lift_option_type_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

Theorem lift_option_type_SOME[simp]:
  lift_option_type (SOME v) msg st = (INL v, st)
Proof
  simp[lift_option_type_def, return_def]
QED

Theorem lift_option_type_NONE[simp]:
  lift_option_type NONE msg st = (INR (Error (TypeError msg)), st)
Proof
  simp[lift_option_type_def, raise_def]
QED

(* reading from the state *)

Definition get_address_immutables_def:
  get_address_immutables cx st =
    lift_option_type (ALOOKUP st.immutables cx.txn.target) "get_address_immutables" st
End

val () = get_address_immutables_def
  |> SRULE [lift_option_type_def, option_CASE_rator]
  |> cv_auto_trans;

(* Helper: get immutables for a source_id, or empty if not present *)
Definition get_source_immutables_def:
  get_source_immutables src_id_opt (imms: module_immutables) =
    case ALOOKUP imms src_id_opt of
      NONE => FEMPTY
    | SOME imm => imm
End

val () = cv_auto_trans get_source_immutables_def;

(* Helper: set immutables for a source_id *)
Definition set_source_immutables_def:
  set_source_immutables src_id_opt imm (imms: module_immutables) =
    (src_id_opt, imm) :: ADELKEY src_id_opt imms
End

val () = cv_auto_trans set_source_immutables_def;

(* Find a storage variable or hashmap declaration in toplevels *)
Datatype:
  var_decl_info
  = StorageVarDecl bool type            (* is_transient, type *)
  | HashMapVarDecl bool type value_type (* is_transient, key type, value type *)
End

Theorem var_decl_info_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperState",Tyop="var_decl_info"}));

(* Look up variable slot from storage_layout *)
Definition lookup_var_slot_from_layout_def:
  lookup_var_slot_from_layout cx is_transient src_id_opt var_name =
    case ALOOKUP cx.layouts cx.txn.target of
    | NONE => NONE
    | SOME (storage_lay, transient_lay) =>
        ALOOKUP (if is_transient then transient_lay else storage_lay) (src_id_opt, var_name)
End

val () = cv_auto_trans lookup_var_slot_from_layout_def;

(* Find var decl by num key (comparing string_to_num of each id) *)
Definition find_var_decl_by_num_def:
  find_var_decl_by_num n [] = NONE ∧
  find_var_decl_by_num n (VariableDecl _ mut vid typ _ :: ts) =
    (if (mut = Storage ∨ mut = Transient) ∧ string_to_num vid = n
     then SOME (StorageVarDecl (mut = Transient) typ, vid)
     else find_var_decl_by_num n ts) ∧
  find_var_decl_by_num n (HashMapDecl _ is_transient vid kt vt _ :: ts) =
    (if string_to_num vid = n then SOME (HashMapVarDecl is_transient kt vt, vid)
     else find_var_decl_by_num n ts) ∧
  find_var_decl_by_num n (_ :: ts) = find_var_decl_by_num n ts
End

val () = cv_auto_trans find_var_decl_by_num_def;

Definition get_accounts_def:
  get_accounts st = return st.accounts st
End

val () = cv_auto_trans get_accounts_def;

Definition update_accounts_def:
  update_accounts f st = return () (st with accounts updated_by f)
End

Definition get_transient_storage_def:
  get_transient_storage st = return st.tStorage st
End

val () = cv_auto_trans get_transient_storage_def;

Definition update_transient_def:
  update_transient f st = return () (st with tStorage updated_by f)
End

Definition get_storage_backend_def:
  get_storage_backend cx T = do
    tStore <- get_transient_storage;
    return $ vfmExecution$lookup_transient_storage cx.txn.target tStore
  od ∧
  get_storage_backend cx F = do
    accts <- get_accounts;
    return $ (lookup_account cx.txn.target accts).storage
  od
End

val () = get_storage_backend_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition set_storage_backend_def:
  set_storage_backend cx T storage' =
    update_transient (vfmExecution$update_transient_storage cx.txn.target storage') ∧
  set_storage_backend cx F storage' = do
    accts <- get_accounts;
    acc <<- lookup_account cx.txn.target accts;
    update_accounts (update_account cx.txn.target (acc with storage := storage'))
  od
End

val () = set_storage_backend_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, update_transient_def, update_accounts_def]
  |> cv_auto_trans;

(* Read a value from storage at a slot *)
Definition read_storage_slot_def:
  read_storage_slot cx is_transient (slot : bytes32) tv = do
    storage <- get_storage_backend cx is_transient;
    lift_option (decode_value storage (w2n slot) tv)
      "read_storage_slot decode"
  od
End

val () = read_storage_slot_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

(* Write a value to storage at a slot *)
Definition write_storage_slot_def:
  write_storage_slot cx is_transient slot tv v = do
    storage <- get_storage_backend cx is_transient;
    writes <- lift_option_type (encode_value tv v) "write_storage_slot encode";
    storage' <<- apply_writes slot writes storage;
    set_storage_backend cx is_transient storage'
  od
End

val () = write_storage_slot_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, set_storage_backend_def,
            update_transient_def, update_accounts_def]
  |> cv_auto_trans;

(* Module-aware immutables lookup *)
Definition get_immutables_def:
  get_immutables cx src_id_opt = do
    imms <- get_address_immutables cx;
    return (get_source_immutables src_id_opt imms)
  od
End

val () = get_immutables_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

(* Module-aware global lookup: look up variable n in module src_id_opt *)
Definition lookup_global_def:
  lookup_global cx src_id_opt n = do
    ts <- lift_option_type (get_module_code cx src_id_opt) "lookup_global get_module_code";
    tenv <<- get_tenv cx;
    case find_var_decl_by_num n ts of
    | NONE => do
        (* Not a storage/hashmap var - check immutables *)
        imms <- get_immutables cx src_id_opt;
        case FLOOKUP imms n of
        | SOME tvv => return (Value (SND tvv))
        | NONE => raise $ Error (TypeError "lookup_global: var not found")
      od
    | SOME (StorageVarDecl is_transient typ, id) => do
        var_slot <- lift_option_type (lookup_var_slot_from_layout cx is_transient src_id_opt id) "lookup_global var_slot";
        tv <- lift_option_type (evaluate_type tenv typ) "lookup_global evaluate_type";
        case tv of
        | ArrayTV elem_tv bd => return (ArrayRef is_transient (n2w var_slot) elem_tv bd)
        | _ => do
            v <- read_storage_slot cx is_transient (n2w var_slot) tv;
            return (Value v)
          od
      od
    | SOME (HashMapVarDecl is_transient kt vt, id) => do
        var_slot <- lift_option_type (lookup_var_slot_from_layout cx is_transient src_id_opt id) "lookup_global hashmap var_slot";
        return (HashMapRef is_transient (n2w var_slot) kt vt)
      od
  od
End

val () = lookup_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator,
            prod_CASE_rator, var_decl_info_CASE_rator,
            type_value_CASE_rator, UNCURRY, LET_THM]
  |> cv_auto_trans;

Definition update_immutable_def:
  update_immutable src_id key tv v (imms: module_immutables) =
    let imm = get_source_immutables src_id imms in
    set_source_immutables src_id (imm |+ (key, (tv, v))) imms
End

val () = cv_auto_trans update_immutable_def;

(* Convert subscript back to a value for hashmap key encoding *)
Definition subscript_to_value_def:
  subscript_to_value (ValueSubscript v) = SOME v ∧
  subscript_to_value (AttrSubscript _) = NONE  (* Attributes are not valid hashmap keys *)
End

val () = cv_auto_trans subscript_to_value_def;

(* Compute final slot from base slot, key types, and list of subscripts *)
Definition compute_hashmap_slot_def:
  compute_hashmap_slot slot [] [] = SOME slot ∧
  compute_hashmap_slot slot (kt::kts) (k::ks) =
    (case subscript_to_value k of
     | NONE => NONE
     | SOME v =>
       let slot = hashmap_slot slot $ encode_hashmap_key kt v in
         compute_hashmap_slot slot kts ks) ∧
  compute_hashmap_slot _ _ _ = NONE
End

val compute_hashmap_slot_pre_def = cv_auto_trans_pre
  "compute_hashmap_slot_pre" compute_hashmap_slot_def;

Theorem compute_hashmap_slot_pre[cv_pre]:
  ∀x y z. compute_hashmap_slot_pre x y z
Proof
  ho_match_mp_tac compute_hashmap_slot_ind
  \\ rw[] \\ rw[Once compute_hashmap_slot_pre_def]
QED

(* Get the final value type after traversing hashmap keys.
   Returns (final_type, key_types, remaining_subs) for nested access within the value. *)
Definition split_hashmap_subscripts_def:
  split_hashmap_subscripts (Type t) subs = SOME (t, [], subs) ∧
  split_hashmap_subscripts (HashMapT kt vt) [] = NONE ∧  (* Not enough subscripts *)
  split_hashmap_subscripts (HashMapT kt vt) (_::ks) =
    (case split_hashmap_subscripts vt ks of
     | SOME (t, kts, remaining) => SOME (t, kt::kts, remaining)
     | NONE => NONE)
End

val () = cv_auto_trans split_hashmap_subscripts_def;

Definition get_scopes_def:
  get_scopes st = return st.scopes st
End

val () = cv_auto_trans get_scopes_def;

Definition lookup_flag_def:
  lookup_flag fid [] = NONE ∧
  lookup_flag fid (FlagDecl id ls :: ts) =
    (if fid = id then SOME ls else lookup_flag fid ts) ∧
  lookup_flag fid (t :: ts) = lookup_flag fid ts
End

val () = cv_auto_trans lookup_flag_def;

Definition lookup_flag_mem_def:
  lookup_flag_mem cx (src_id_opt, fid) mid =
  case get_module_code cx src_id_opt
    of NONE => raise $ Error (TypeError "lookup_flag_mem code")
     | SOME ts =>
  case lookup_flag fid ts
    of NONE => raise $ Error (TypeError "lookup_flag")
     | SOME ls =>
  case INDEX_OF mid ls
    of NONE => raise $ Error (TypeError "lookup_flag_mem index")
     | SOME i => return $ Value $ FlagV (2 ** i)
End

val () = lookup_flag_mem_def
  |> SRULE [FUN_EQ_THM, option_CASE_rator]
  |> cv_auto_trans;

(* writing to the state *)

Definition set_address_immutables_def:
  set_address_immutables cx imms st =
  let addr = cx.txn.target in
    return () $ st with immutables updated_by
      (λal. (addr, imms) :: (ADELKEY addr al))
End

val () = cv_auto_trans set_address_immutables_def;

(* Module-aware global set: write a value to EVM storage *)
Definition set_global_def:
  set_global cx src_id_opt n v = do
    ts <- lift_option_type (get_module_code cx src_id_opt) "set_global get_module_code";
    tenv <<- get_tenv cx;
    case find_var_decl_by_num n ts of
    | NONE => raise $ Error (TypeError "set_global: var not found")
    | SOME (StorageVarDecl is_transient typ, id) => do
        var_slot <- lift_option_type (lookup_var_slot_from_layout cx is_transient src_id_opt id) "set_global var_slot";
        tv <- lift_option_type (evaluate_type tenv typ) "set_global evaluate_type";
        write_storage_slot cx is_transient (n2w var_slot) tv v
      od
    | SOME (HashMapVarDecl _ kt vt, id) =>
        raise $ Error (TypeError "set_global: cannot set hashmap directly")
  od
End

val () = set_global_def
  |> SRULE [bind_def, FUN_EQ_THM, option_CASE_rator,
            prod_CASE_rator, var_decl_info_CASE_rator, UNCURRY, LET_THM]
  |> cv_auto_trans;

Definition set_immutable_def:
  set_immutable cx src_id_opt n tv v = do
    imms <- get_address_immutables cx;
    let imm = get_source_immutables src_id_opt imms in
    set_address_immutables cx $ set_source_immutables src_id_opt (imm |+ (n, (tv, v))) imms
  od
End

val () = set_immutable_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition set_scopes_def:
  set_scopes env st = return () $ st with scopes := env
End

val () = cv_auto_trans set_scopes_def;

Definition push_scope_def:
  push_scope st = return () $ st with scopes updated_by CONS FEMPTY
End

val () = cv_auto_trans push_scope_def;

Definition push_scope_with_var_def:
  push_scope_with_var nm tv v st =
    return () $ st with scopes updated_by
      CONS (FEMPTY |+ (nm, <| assignable := F; type := tv; value := v |>))
End

val () = cv_auto_trans push_scope_with_var_def;

Definition pop_scope_def:
  pop_scope st =
    case st.scopes
    of [] => raise (Error (TypeError "pop_scope")) st
       | _::tl => return () (st with scopes := tl)
End

val () = cv_auto_trans pop_scope_def;

(* writing variables *)

Definition new_variable_def:
  new_variable id tv v = do
    n <<- string_to_num id;
    env <- get_scopes;
    type_check (IS_NONE (lookup_scopes n env)) "new_variable bound";
    case env of [] => raise $ Error (TypeError "new_variable null")
    | e::es => set_scopes ((e |+ (n, <| assignable := T; type := tv; value := v |>))::es)
  od
End

val () = new_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def,
            LET_RATOR, list_CASE_rator]
  |> cv_auto_trans;

Definition set_variable_def:
  set_variable id v = do
    n <<- string_to_num id;
    sc <- get_scopes;
    (pre, env, entry, rest) <-
      lift_option_type (find_containing_scope n sc) "set_variable not found";
    type_check entry.assignable "set_variable not assignable";
    set_scopes (pre ++ (env |+ (n, entry with value := v))::rest)
  od
End

val () = set_variable_def
  |> SRULE [FUN_EQ_THM, bind_def, lift_option_def,
            ignore_bind_def, LET_RATOR, UNCURRY, option_CASE_rator]
  |> cv_auto_trans;

(* assignment to existing locations *)

Definition get_Value_def[simp]:
  get_Value (Value v) = return v ∧
  get_Value _ = raise $ Error (TypeError "not Value")
End

val () = get_Value_def
  |> SIMP_RULE std_ss [FUN_EQ_THM]
  |> cv_auto_trans;

Definition materialise_def:
  materialise cx (ArrayRef is_transient base_slot elem_tv bd) = do
    v <- read_storage_slot cx is_transient base_slot (ArrayTV elem_tv bd);
    return v
  od ∧
  materialise cx (Value v) = return v ∧
  materialise _ _ = raise $ Error (TypeError "materialise")
End

val () = materialise_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, toplevel_value_CASE_rator]
  |> cv_auto_trans;

Definition toplevel_array_length_def:
  toplevel_array_length cx (ArrayRef is_transient base_slot _ (Fixed n)) =
    return $ (&n : num) ∧
  toplevel_array_length cx (ArrayRef is_transient base_slot _ (Dynamic _)) = do
    storage <- get_storage_backend cx is_transient;
    return $ &(w2n (lookup_storage base_slot storage))
  od ∧
  toplevel_array_length cx (Value (ArrayV (DynArrayV vs))) =
    return $ &(LENGTH vs) ∧
  toplevel_array_length cx (Value (ArrayV (SArrayV sparse))) =
    return $ &(LENGTH sparse) ∧
  toplevel_array_length cx (Value (ArrayV (TupleV vs))) =
    return $ &(LENGTH vs) ∧
  toplevel_array_length cx (Value (BytesV ls)) =
    return $ &(LENGTH ls) ∧
  toplevel_array_length cx (Value (StringV ls)) =
    return $ &(LENGTH ls) ∧
  toplevel_array_length _ _ = raise $ Error (TypeError "toplevel_array_length")
End

val () = toplevel_array_length_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, toplevel_value_CASE_rator]
  |> cv_auto_trans;

Theorem toplevel_array_length_sarrayv[local]:
  toplevel_array_length cx (Value (ArrayV (SArrayV sparse))) st =
    (INL (&LENGTH sparse), st)
Proof
  simp[toplevel_array_length_def, return_def]
QED

Definition evaluate_subscript_def:
  evaluate_subscript tenv tv (Value (ArrayV av)) (IntV i) =
  (case array_index tv av i
   of SOME v => INL $ INL $ Value v
    | _ => INR (RuntimeError "subscript array_index")) ∧
  evaluate_subscript tenv _ (HashMapRef is_transient slot kt vt) kv =
  (let new_slot = hashmap_slot slot $ encode_hashmap_key kt kv in
   case vt
   of HashMapT kt' vt' => INL $ INL $ HashMapRef is_transient new_slot kt' vt'
    | Type t =>
        (case evaluate_type tenv t of
         | SOME tv => INL $ INR (is_transient, new_slot, tv)
         | NONE => INR (TypeError "evaluate_subscript evaluate_type"))) ∧
  evaluate_subscript tenv _ (ArrayRef is_transient base_slot elem_tv bd) (IntV i) =
  (if 0 ≤ i ∧ Num i < bound_length bd then
    let elem_offset = (case bd of Fixed _ => 0 | Dynamic _ => 1) in
    let slot = base_slot + n2w (elem_offset + Num i * type_slot_size elem_tv) in
    case elem_tv of
    | ArrayTV inner_tv inner_bd =>
        INL $ INL $ ArrayRef is_transient slot inner_tv inner_bd
    | _ => INL $ INR (is_transient, slot, elem_tv)
   else INR (RuntimeError "subscript array out of bounds")) ∧
  evaluate_subscript _ _ _ _ = INR (TypeError "evaluate_subscript")
End

val () = cv_auto_trans evaluate_subscript_def;

Definition evaluate_subscripts_def:
  evaluate_subscripts tv a [] = INL a ∧
  evaluate_subscripts tv a ((ValueSubscript (IntV i))::is) =
  (case a of ArrayV av =>
   (let elem_tv = (case tv of ArrayTV t _ => t | _ => NoneTV) in
    case array_index tv av i of SOME v =>
    (case evaluate_subscripts elem_tv v is of INL vj => INL vj
     | INR err => INR err)
    | _ => INR (RuntimeError "evaluate_subscripts array_index"))
   | _ => INR (TypeError "evaluate_subscripts type")) ∧
  evaluate_subscripts tv (StructV al) ((AttrSubscript id)::is) =
  (let field_tv = (case tv of StructTV args =>
      (case ALOOKUP args id of SOME t => t | NONE => NoneTV) | _ => NoneTV) in
   case ALOOKUP al id of SOME v =>
    (case evaluate_subscripts field_tv v is of INL v' => INL v'
     | INR err => INR err)
   | _ => INR (TypeError "evaluate_subscripts AttrSubscript")) ∧
  evaluate_subscripts _ _ _ = INR (TypeError "evaluate_subscripts")
End

val evaluate_subscripts_pre_def =
  cv_auto_trans_pre "evaluate_subscripts_pre" evaluate_subscripts_def;

Theorem evaluate_subscripts_pre[cv_pre]:
  !a b c. evaluate_subscripts_pre a b c
Proof
  ho_match_mp_tac evaluate_subscripts_ind
  \\ rw[Once evaluate_subscripts_pre_def]
  \\ rw[Once evaluate_subscripts_pre_def]
  \\ gvs[] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED

(* mutating inside arrays, structs, hashmaps *)

Datatype:
  assign_operation
  = Replace value
  | Update type binop value
  | AppendOp value
  | PopOp
End

Theorem assign_operation_CASE_rator =
  DatatypeSimps.mk_case_rator_thm_tyinfo
    (Option.valOf (TypeBase.read {Thy="vyperState",Tyop="assign_operation"}));

Definition assign_subscripts_def:
  (* TODO(semantic-limitation): replacement currently trusts callers/type
     checks to provide a value castable to the target type. *)
  assign_subscripts tv a [] (Replace v) = INL v ∧
  assign_subscripts tv a [] (Update ty bop v) =
    (let u = case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0 in
       evaluate_binop u tv bop a v) ∧
  assign_subscripts tv a [] (AppendOp v) = append_element tv a v ∧
  assign_subscripts tv a [] PopOp = pop_element a ∧
  assign_subscripts tv a ((ValueSubscript (IntV i))::is) ao =
  (case a of ArrayV av =>
   (let elem_tv = (case tv of ArrayTV t _ => t | _ => NoneTV) in
    case array_index tv av i of SOME v =>
    (case assign_subscripts elem_tv v is ao of INL vj =>
       array_set_index tv av i vj
     | INR err => INR err)
    | _ => INR (RuntimeError "assign_subscripts array_index"))
   | _ => INR (TypeError "assign_subscripts type")) ∧
  assign_subscripts tv (StructV al) ((AttrSubscript id)::is) ao =
  (let field_tv = (case tv of StructTV args =>
      (case ALOOKUP args id of SOME t => t | NONE => NoneTV) | _ => NoneTV) in
   case ALOOKUP al id of SOME v =>
    (case assign_subscripts field_tv v is ao of INL v' =>
      INL $ StructV $ AFUPDKEY id (K v') al
     | INR err => INR err)
   | _ => INR (TypeError "assign_subscripts AttrSubscript")) ∧
  assign_subscripts _ _ _ _ = INR (TypeError "assign_subscripts")
End

val assign_subscripts_pre_def =
  cv_auto_trans_pre "assign_subscripts_pre" assign_subscripts_def;

Theorem assign_subscripts_pre[cv_pre]:
  !a b c d. assign_subscripts_pre a b c d
Proof
  ho_match_mp_tac assign_subscripts_ind
  \\ rw[Once assign_subscripts_pre_def]
  \\ rw[Once assign_subscripts_pre_def]
  \\ gvs[] \\ rw[]
  \\ qmatch_asmsub_rename_tac`0i ≤ w`
  \\ Cases_on`w` \\ gs[]
QED

Datatype:
  location
  = ScopedVar identifier
  | ImmutableVar (num option) identifier  (* source_id, var_name *)
  | TopLevelVar (num option) identifier   (* source_id, var_name *)
End

Datatype:
  assignment_value
  = BaseTargetV location (subscript list)
  | TupleTargetV (assignment_value list)
End

Type base_target_value = “:location # subscript list”;

(* Walk through nested array subscripts computing the final element slot *)
Definition resolve_array_element_def:
  resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) ((ValueSubscript (IntV idx))::rest) = do
    elem_offset <- (case bd of
     | Fixed n => do
         check (0 ≤ idx ∧ Num idx < n) "array fixed oob";
         return 0
       od
     | Dynamic n => do
         check (0 ≤ idx ∧ Num idx < n) "array dynamic capacity oob";
         storage <- get_storage_backend cx is_transient;
         stored_len <<- w2n (lookup_storage base_slot storage);
         check (Num idx < stored_len) "array dynamic length oob";
         return 1
       od);
    elem_slot <<- base_slot + n2w (elem_offset + Num idx * type_slot_size elem_tv);
    resolve_array_element cx is_transient elem_slot elem_tv rest
  od ∧
  resolve_array_element _ _ _ (ArrayTV _ _) (_::_) =
    raise (Error (TypeError "resolve_array_element: array needs int subscript")) ∧
  resolve_array_element _ _ base_slot tv rest = return (base_slot, tv, rest)
End

val resolve_array_element_pre_def = resolve_array_element_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM, check_def,
            ignore_bind_def, bound_CASE_rator]
  |> cv_auto_trans_pre "resolve_array_element_pre";

Theorem resolve_array_element_pre[cv_pre]:
  ∀a b c d e f. resolve_array_element_pre a b c d e f
Proof
  ho_match_mp_tac resolve_array_element_ind \\ rw[]
  \\ rw[Once resolve_array_element_pre_def]
QED

Definition assign_result_def:
  assign_result tv PopOp old_val subs = do
    arr <- lift_sum $ evaluate_subscripts tv old_val subs;
    p <- lift_sum $ popped_value arr;
    return $ SOME p
  od ∧
  assign_result _ _ _ _ = return NONE
End

val () = assign_result_def
  |> SRULE [bind_def, FUN_EQ_THM, LET_THM]
  |> cv_auto_trans;

Definition assign_target_def:
  assign_target cx (BaseTargetV (ScopedVar id) is) ao = do
    ni <<- string_to_num id;
    sc <- get_scopes;
    (pre, env, entry, rest) <- lift_option (find_containing_scope ni sc) "assign_target lookup";
    type_check entry.assignable "assign_target not assignable";
    a' <- lift_sum $ assign_subscripts entry.type entry.value (REVERSE is) ao;
    set_scopes $ pre ++ env |+ (ni, entry with value := a') :: rest;
    assign_result entry.type ao entry.value (REVERSE is)
  od ∧
  assign_target cx (BaseTargetV (TopLevelVar src_id_opt id) is) ao = do
    ni <<- string_to_num id;
    tv <- lookup_global cx src_id_opt ni;
    ts <- lift_option_type (get_module_code cx src_id_opt) "assign_target get_module_code";
    tenv <<- get_tenv cx;
    case tv of
    | Value v => do
        var_tv <- lift_option_type
          (OPTION_BIND (find_var_decl_by_num ni ts)
             (λp. case FST p of StorageVarDecl _ typ => evaluate_type tenv typ | _ => NONE))
          "assign_target TopLevelVar type";
        v' <- lift_sum $ assign_subscripts var_tv v (REVERSE is) ao;
        set_global cx src_id_opt ni v';
        assign_result var_tv ao v (REVERSE is)
      od
    | HashMapRef is_transient base_slot kt vt => do
        (first_sub, rest_subs) <- lift_option_type
          (case REVERSE is of x::xs => SOME (x, xs) | [] => NONE)
          "assign_target hashmap needs subscript";
        (final_type, key_types, remaining_subs) <- lift_option_type
          (split_hashmap_subscripts vt rest_subs)
          "assign_target split_hashmap_subscripts";
        hashmap_subs <<- first_sub :: TAKE (LENGTH rest_subs - LENGTH remaining_subs) rest_subs;
        all_key_types <<- kt :: key_types;
        final_slot <- lift_option_type
          (compute_hashmap_slot base_slot all_key_types hashmap_subs)
          "assign_target compute_hashmap_slot";
        final_tv <- lift_option_type (evaluate_type tenv final_type) "assign_target evaluate_type";
        current_val <- read_storage_slot cx is_transient final_slot final_tv;
        new_val <- lift_sum $ assign_subscripts final_tv current_val remaining_subs ao;
        write_storage_slot cx is_transient final_slot final_tv new_val;
        assign_result final_tv ao current_val remaining_subs
      od
    | ArrayRef is_transient base_slot elem_tv bd => do
        (elem_slot, final_tv, remaining_subs) <-
          resolve_array_element cx is_transient base_slot (ArrayTV elem_tv bd) (REVERSE is);
        case (ao, final_tv) of
        | (PopOp, ArrayTV pop_elem_tv (Dynamic _)) => do
            storage <- get_storage_backend cx is_transient;
            stored_len <<- w2n (lookup_storage elem_slot storage);
            check (stored_len > 0) "pop empty storage array";
            last_idx <<- stored_len - 1;
            last_slot <<- elem_slot + n2w (1 + last_idx * type_slot_size pop_elem_tv);
            popped <- read_storage_slot cx is_transient last_slot pop_elem_tv;
            write_storage_slot cx is_transient last_slot pop_elem_tv (default_value pop_elem_tv);
            write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
              (IntV &last_idx);
            return $ SOME popped
          od
        | (AppendOp v, ArrayTV app_elem_tv (Dynamic n)) => do
            storage <- get_storage_backend cx is_transient;
            stored_len <<- w2n (lookup_storage elem_slot storage);
            check (stored_len < n) "append full storage array";
            new_slot <<- elem_slot + n2w (1 + stored_len * type_slot_size app_elem_tv);
            write_storage_slot cx is_transient new_slot app_elem_tv v;
            write_storage_slot cx is_transient elem_slot (BaseTV (UintT 256))
              (IntV &(stored_len + 1));
            return NONE
          od
        | _ => do
            current_val <- read_storage_slot cx is_transient elem_slot final_tv;
            new_val <- lift_sum $ assign_subscripts final_tv current_val remaining_subs ao;
            write_storage_slot cx is_transient elem_slot final_tv new_val;
            assign_result final_tv ao current_val remaining_subs
          od
      od
  od ∧
  assign_target cx (BaseTargetV (ImmutableVar src_id_opt id) is) ao = do
    ni <<- string_to_num id;
    imms <- get_immutables cx src_id_opt;
    tva <- lift_option_type (FLOOKUP imms ni) "assign_target ImmutableVar";
    a' <- lift_sum $ assign_subscripts (FST tva) (SND tva) (REVERSE is) ao;
    set_immutable cx src_id_opt ni (FST tva) a';
    assign_result (FST tva) ao (SND tva) (REVERSE is)
  od ∧
  assign_target cx (TupleTargetV gvs) (Replace (ArrayV (TupleV vs))) = do
    type_check (LENGTH gvs = LENGTH vs) "TupleTargetV length";
    assign_targets cx gvs vs;
    return NONE
  od ∧
  assign_target _ _ _ = raise (Error (TypeError "assign_target")) ∧
  assign_targets cx [] [] = return () ∧
  assign_targets cx (gv::gvs) (v::vs) = do
    assign_target cx gv (Replace v);
    assign_targets cx gvs vs
  od ∧
  assign_targets _ _ _ = raise (Error (TypeError "assign_targets"))
End

val assign_target_pre_def = assign_target_def
  |> SRULE [FUN_EQ_THM, bind_def, LET_RATOR, ignore_bind_def,
            UNCURRY, prod_CASE_rator, option_CASE_rator,
            toplevel_value_CASE_rator, lift_option_def,
            type_value_CASE_rator, bound_CASE_rator,
            assign_operation_CASE_rator]
  |> cv_auto_trans_pre "assign_target_pre assign_targets_pre";

Theorem assign_target_pre[cv_pre]:
  (∀w x y z. assign_target_pre w x y z) ∧
  (∀w x y z. assign_targets_pre w x y z)
Proof
  ho_match_mp_tac assign_target_ind \\ rw[]
  \\ rw[Once assign_target_pre_def]
QED
