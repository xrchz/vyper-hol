Theory vyperTestRunner
Ancestors
  contractABI vyperABI vyperSmallStep jsonAST jsonToVyper
Libs
  cv_transLib wordsLib

(* TODO(cleanup): move this ABI test-runner representation to contractABITheory
   or another shared ABI support theory. *)

Datatype:
  abi_function = <|
    name: string
  ; inputs: (string # abi_type) list
  ; outputs: (string # abi_type) list
  ; mutability: function_mutability (* TODO(cleanup): not dependent on Vyper. *)
  |>
End

Datatype:
  abi_entry
  = Function abi_function
  | Event string (* TODO(test-semantics): determine whether event argument metadata is needed. *)
End

Datatype:
  deployment_trace = <|
    sourceAst: (num option, toplevel list) alist
  ; sourceExports: (string # num) list
  ; importMap: (string # num) list  (* alias -> source_id, for storage layout key transform *)
  ; contractAbi: abi_entry list
  ; deployedAddress: address
  ; deployer: address
  ; deploymentSuccess: bool
  ; value: num
  ; timeStamp: num
  ; blockNumber: num
  ; blockHashes: bytes32 list
  ; blobHashes: bytes32 list
  ; blobBaseFee: num
  ; gasPrice: num
  ; chainId: num
  ; callData: byte list
  ; runtimeBytecode: byte list
  ; storageLayout: json_storage_layout
  ; isBlueprint: bool
  |>
End

val () = cv_auto_trans extract_storage_layout_def;

Definition compute_selector_names_def:
  compute_selector_names [] = [] ∧
  compute_selector_names (Function x::ls) = (
  let name = x.name in
  let argTypes = MAP SND x.inputs in
  let retTypes = MAP SND x.outputs in
  let sel = function_selector name argTypes in
    (sel, name, argTypes, retTypes)::compute_selector_names ls ) ∧
  compute_selector_names (e::ls) = compute_selector_names ls
End

val () = cv_auto_trans compute_selector_names_def;

Definition find_deploy_function_name_def:
  find_deploy_function_name [] = "__init__" ∧
  find_deploy_function_name ((FunctionDecl Deploy _ _ _ name _ _ _ _)::_) = name ∧
  find_deploy_function_name (_::ts) = find_deploy_function_name ts
End

val () = cv_auto_trans find_deploy_function_name_def;

Definition find_args_by_name_def:
  find_args_by_name n [] = [] ∧
  find_args_by_name n (Function x::ls) =
  (if n = x.name then MAP SND x.inputs else
     find_args_by_name n ls) ∧
  find_args_by_name n (_::ls) =
  find_args_by_name n ls
End

val () = cv_auto_trans find_args_by_name_def;

Datatype:
  call_trace = <|
    sender: address
  ; target: address
  ; callData: byte list
  ; value: num
  ; timeStamp: num
  ; blockNumber: num
  ; blockHashes: bytes32 list
  ; blobHashes: bytes32 list
  ; blobBaseFee: num
  ; gasLimit: num
  ; gasPrice: num
  ; chainId: num
  ; static: bool
  ; expectedOutput: byte list option
  |>
End

Datatype:
  trace
  = Deployment deployment_trace
  | Call call_trace
  | SetBalance address num
  | ClearTransientStorage
End

Definition compute_vyper_args_def:
  compute_vyper_args all_mods ts vis name argTys cd = let
    abiTupTy = Tuple argTys;
    vyTysRet = case lookup_function NONE name vis ts
                of SOME (_,_,args,_,ret,_) => (MAP SND args, ret)
                  | NONE => ([], NoneT);
    vyTys = TAKE (LENGTH argTys) (FST vyTysRet);
    (* Use combined type env from all modules so cross-module types work *)
    tenv = type_env_all_modules all_mods;
    (* Pad calldata with zeros to model EVM semantics: CALLDATALOAD past
       the end of calldata returns zero. We pad to vyper_abi_size_bound,
       which is the maximum encoding size for this type. *)
    bound = vyper_abi_size_bound tenv (TupleT vyTys);
    padded = PAD_RIGHT 0w bound cd;
    argsOpt = if
      static_length abiTupTy ≤ LENGTH cd ∧
      valid_enc abiTupTy padded
    then let
      abiArgsTup = dec abiTupTy padded;
      vyArgsTup = abi_to_vyper tenv (TupleT vyTys) abiArgsTup;
      vyArgsTv = evaluate_type tenv (TupleT vyTys);
      vyArgs = (case OPTION_BIND vyArgsTv
                  (λtv. OPTION_BIND vyArgsTup (extract_elements tv))
                  of NONE => [] | SOME ls => ls)
      in SOME vyArgs else NONE;
  in
    (argsOpt, tenv, SND vyTysRet)
End

val () = cv_auto_trans compute_vyper_args_def;

Definition run_deployment_def:
  run_deployment am dt = let
    sns = compute_selector_names dt.contractAbi;
    all_mods = annotate_sources_slots dt.storageLayout dt.sourceAst;
    ts = case ALOOKUP all_mods NONE of SOME ts => ts | NONE => [];
    name = find_deploy_function_name ts;
    argTys = find_args_by_name name dt.contractAbi;
    ar = compute_vyper_args all_mods ts Deploy name argTys dt.callData;
    res = case FST ar of NONE => INR (Error $ RuntimeError "run_deployment args")
          | SOME args => let
    tx = <| sender := dt.deployer
          ; target := dt.deployedAddress
          ; function_name := name
          ; args := args
          ; value := dt.value
          ; time_stamp := dt.timeStamp
          ; block_number := dt.blockNumber
          ; block_hashes := dt.blockHashes
          ; blob_hashes := dt.blobHashes
          ; blob_base_fee := dt.blobBaseFee
          ; gas_price := dt.gasPrice
          ; chain_id := dt.chainId
          ; is_creation := T
          ; coinbase := 0w
          ; gas_limit := 0
          ; base_fee := 0
          ; prev_randao := 0
          ; origin := dt.deployer |>;
    in load_contract am tx all_mods dt.sourceExports
  in (sns, res)
End

val () = cv_auto_trans run_deployment_def;

Definition run_call_def:
  run_call sns am ct = let
    sel = TAKE 4 ct.callData;
    fna = case ALOOKUP sns sel of SOME fna => fna
             | NONE => ("__default__", [], []);
    name = FST fna; argTys = FST (SND fna);
    all_mods = case ALOOKUP am.sources ct.target of
                 SOME mods => mods
               | _ => [];
    (* Check exports to find which module the function lives in *)
    src_id_opt = case ALOOKUP am.exports ct.target of
                   NONE => NONE
                 | SOME export_map => ALOOKUP export_map name;
    ts = case ALOOKUP all_mods src_id_opt of
           SOME ts => ts
         | NONE => case ALOOKUP all_mods NONE of SOME ts => ts | _ => [];
    ar = compute_vyper_args all_mods ts External name argTys (DROP 4 ct.callData);
    retTys = SND (SND fna);
    tenv = FST (SND ar);
    retTypes = SND (SND ar);
  in
    case FST ar of NONE => ((INR (Error $ RuntimeError "run_call args"), am),
                            (retTys, (retTypes, FEMPTY)))
  | SOME args => let
    tx = <| sender := ct.sender
          ; target := ct.target
          ; function_name := name
          ; args := args
          ; value := ct.value
          ; time_stamp := ct.timeStamp
          ; block_number := ct.blockNumber
          ; block_hashes := ct.blockHashes
          ; blob_hashes := ct.blobHashes
          ; blob_base_fee := ct.blobBaseFee
          ; gas_price := ct.gasPrice
          ; chain_id := ct.chainId
          ; is_creation := F
          ; coinbase := 0w
          ; gas_limit := ct.gasLimit
          ; base_fee := 0
          ; prev_randao := 0
          ; origin := ct.sender |>;
    (* TODO(test-semantics): set static-call context based on ct.static. *)
    (* TODO(test-semantics): thread additional environment data from the trace. *)
  in (call_external am tx, (retTys, (retTypes, tenv)))
End

val () = cv_auto_trans run_call_def;

Definition is_transfer_def:
  is_transfer ct ⇔
  NULL ct.callData ∧ ¬ct.static ∧
  ct.expectedOutput = SOME []
End

val () = cv_auto_trans is_transfer_def;

Definition do_transfer_def:
  do_transfer ct am = let
    acc = am.accounts;
    saddr = ct.sender;
    taddr = ct.target;
    sender = lookup_account saddr acc;
    target = lookup_account taddr acc;
    value = ct.value;
    sbal = sender.balance;
    (* TODO(test-semantics): charge gas for value transfers. *)
  in
    if value ≤ sbal then
      INL $
      am with accounts updated_by
        (update_account saddr
          (sender with <| balance updated_by (flip $- value);
                          nonce updated_by SUC |>) o
          (update_account taddr
            (target with balance updated_by ($+ value))))
    else INR (Error $ RuntimeError "do_transfer")
End

val () = do_transfer_def
  |> SRULE [combinTheory.o_DEF, combinTheory.C_DEF]
  |> cv_auto_trans;

Definition run_trace_def:
  run_trace snss am tr =
  case tr
  of Deployment dt =>
    if dt.isBlueprint then
      (* Blueprint deployment: just store bytecode, no constructor *)
      let am' = am with accounts updated_by
            (update_account dt.deployedAddress
              ((lookup_account dt.deployedAddress am.accounts)
                with code := dt.runtimeBytecode)) in
      ((dt.deployedAddress,[])::snss, INL am')
    else let
      (s_layout, t_layout) = extract_storage_layout dt.importMap dt.storageLayout;
      am_with_layout = am with layouts updated_by CONS (dt.deployedAddress, (s_layout, t_layout));
      result = run_deployment am_with_layout dt;
      sns = FST result; res = SND result;
      res = if dt.deploymentSuccess then
              (* Set the bytecode in accounts after successful deployment *)
              case res of
                INL am' => INL (am' with
                  accounts updated_by
                    (update_account dt.deployedAddress
                      ((lookup_account dt.deployedAddress am'.accounts)
                        with code := dt.runtimeBytecode)))
              | err => err
            else if ISR res then INL am
            else INR (Error $ RuntimeError "deployment success");
      snss = (dt.deployedAddress,sns)::snss;
    in
      (snss, res)
   | ClearTransientStorage => (snss,
       INL (am with tStorage := empty_transient_storage))
   | SetBalance addr bal => (snss,
       INL (am with accounts updated_by
            (update_account addr
             ((lookup_account addr am.accounts) with balance := bal)))
     )
   | Call ct => (snss,
     case ALOOKUP snss ct.target
     of NONE => if is_transfer ct then do_transfer ct am
                else if IS_NONE ct.expectedOutput then INL am
                else INR (Error $ TypeError "sns not found")
      | SOME sns => let
        cr = run_call sns am ct;
        call_res = FST cr;
        am = SND call_res in
       case FST call_res
       of (* TODO(test-semantics): decide whether AssertException should satisfy expected failure traces. *)
       | INR ex => if IS_NONE ct.expectedOutput then INL am
                   else INR ex
       | INL v =>
       case ct.expectedOutput
         of NONE => INR (Error $ RuntimeError "error expected")
          | SOME out => let
              ar = SND (SND cr);
              rawVyRetTy = FST ar; tenv = SND ar;
            in
              case evaluate_abi_decode_return tenv rawVyRetTy out of
              | INR _ => INR (Error $ RuntimeError "output mismatch")
              | INL decoded =>
                  if decoded = v
                  then INL am
                  else INR (Error $ RuntimeError "output mismatch"))
End

val () = cv_auto_trans run_trace_def;

Definition run_test_loop_def:
  run_test_loop snss am [] = INL () ∧
  run_test_loop snss am (tr::trs) =
  case run_trace snss am tr of
       (snss, INL am) => run_test_loop snss am trs
     | (_, INR ex) => INR ex
End

val () = cv_auto_trans run_test_loop_def;

Definition run_test_def:
  run_test trs = run_test_loop []
    initial_machine_state trs
End

val () = cv_auto_trans run_test_def;
