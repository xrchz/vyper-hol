(* Executable probes and consumer-facing properties of call layouts. *)

Theory callLayoutProps
Ancestors
  callLayoutDefs

Definition layout_test_fn_def:
  layout_test_fn entry_insts other_blocks =
    mk_raw_function "f"
      (<| bb_label := "entry"; bb_instructions := entry_insts |> ::
       other_blocks)
End

Definition layout_test_block_def:
  layout_test_block name insts =
    <| bb_label := name; bb_instructions := insts |>
End

Theorem canonical_param_prefix_valid_eval:
  canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 PARAM [Lit 0w] ["u0"];
       mk_inst 1 PARAM [Lit 1w] ["u1"];
       mk_inst 2 FMP_PARAM [Lit 2w] ["fmp"];
       mk_inst 3 RETPC_PARAM [Lit 3w] ["retpc"];
       mk_inst 4 ADD [] ["sum"]]
      [layout_test_block "exit" [mk_inst 5 RET [] []]]) /\
  canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 PARAM [Lit 0w] ["u0"]]
      []) /\
  canonical_param_prefix (layout_test_fn [] [])
Proof
  EVAL_TAC
QED

Theorem canonical_param_prefix_malformed_eval:
  ~canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 FMP_PARAM [Lit 0w] ["fmp"];
       mk_inst 1 PARAM [Lit 1w] ["u0"]] []) /\
  ~canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 PARAM [Lit 1w] ["u0"]] []) /\
  ~canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 FMP_PARAM [Lit 0w] ["fmp0"];
       mk_inst 1 FMP_PARAM [Lit 1w] ["fmp1"]] []) /\
  ~canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 PARAM [Lit 0w] ["u0"];
       mk_inst 1 ADD [] ["x"];
       mk_inst 2 RETPC_PARAM [Lit 2w] ["retpc"]] []) /\
  ~canonical_param_prefix
    (layout_test_fn []
      [layout_test_block "later"
        [mk_inst 0 PARAM [Lit 0w] ["u0"]]]) /\
  ~canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 RETPC_PARAM [Lit 0w] ["retpc0"];
       mk_inst 1 RETPC_PARAM [Lit 1w] ["retpc1"]] []) /\
  ~canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 PARAM [Lit 0w] []] []) /\
  ~canonical_param_prefix
    (layout_test_fn
      [mk_inst 0 FMP_PARAM [Lit 0w] ["fmp"; "extra"]] [])
Proof
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

Theorem entry_param_queries_eval:
  let fn = layout_test_fn
      [mk_inst 0 PARAM [Lit 0w] ["u0"];
       mk_inst 1 PARAM [Lit 1w] ["u1"];
       mk_inst 2 FMP_PARAM [Lit 2w] ["fmp"];
       mk_inst 3 RETPC_PARAM [Lit 3w] ["retpc"]] [] in
    MAP (\inst. inst.inst_opcode) (fn_user_param_insts fn) = [PARAM; PARAM] /\
    OPTION_MAP (\inst. inst.inst_opcode) (fn_hidden_fmp_param fn) =
      SOME FMP_PARAM /\
    OPTION_MAP (\inst. inst.inst_opcode) (fn_retpc_param fn) =
      SOME RETPC_PARAM
Proof
  EVAL_TAC
QED


Definition layout_test_fn_with_abi_def:
  layout_test_fn_with_abi entry_insts other_blocks has_mem_ret user_returns =
    layout_test_fn entry_insts other_blocks with
      fn_call_abi := <|
        ica_has_memory_return_buffer := has_mem_ret;
        ica_user_return_count := user_returns
      |>
End

Theorem raw_return_user_arity_eval:
  raw_return_user_arity (mk_inst 10 RET [Var "rpc"] []) = SOME 0 /\
  raw_return_user_arity
    (mk_inst 11 RET [Var "u0"; Var "u1"; Var "rpc"] []) = SOME 2 /\
  raw_return_user_arity
    (mk_inst 12 RETFMP [Var "u0"; Var "rpc"] []) = SOME 1 /\
  raw_return_user_arity
    (mk_inst 13 DRET
      [Lit 1w; Var "ordinary"; Var "src"; Lit 32w; Var "rpc"] []) =
      SOME 2 /\
  raw_return_user_arity (mk_inst 14 RET [] []) = NONE /\
  raw_return_user_arity (mk_inst 15 RETFMP [] []) = NONE /\
  raw_return_user_arity (mk_inst 16 DRET [Lit 1w] []) = NONE /\
  raw_return_user_arity (mk_inst 17 ADD [] []) = NONE
Proof
  EVAL_TAC
QED

Theorem fn_unique_return_arity_eval:
  fn_unique_return_arity
    (layout_test_fn
      [mk_inst 0 RET [Var "u"; Var "rpc"] [];
       mk_inst 1 RETFMP [Var "u"; Var "rpc"] []] []) = SOME 1 /\
  fn_unique_return_arity
    (layout_test_fn
      [mk_inst 0 RET [Var "u"; Var "rpc"] [];
       mk_inst 1 RETFMP [Var "u0"; Var "u1"; Var "rpc"] []] []) = NONE /\
  fn_unique_return_arity
    (layout_test_fn [mk_inst 0 RET [] []] []) = NONE /\
  fn_unique_return_arity (layout_test_fn [mk_inst 0 ADD [] []] []) = NONE
Proof
  EVAL_TAC
QED

Theorem fn_return_abi_matches_eval:
  fn_return_abi_matches
    (layout_test_fn_with_abi
      [mk_inst 0 PARAM [Lit 0w] ["retbuf"];
       mk_inst 1 RET [Var "u"; Var "rpc"] []]
      [] (SOME T) (SOME 1)) /\
  ~fn_return_abi_matches
    (layout_test_fn_with_abi
      [mk_inst 0 RET [Var "u"; Var "rpc"] []]
      [] (SOME T) (SOME 1)) /\
  ~fn_return_abi_matches
    (layout_test_fn_with_abi
      [mk_inst 0 PARAM [Lit 0w] ["retbuf"];
       mk_inst 1 RET [Var "u"; Var "rpc"] []]
      [] (SOME T) (SOME 2)) /\
  fn_memory_return_buffer_param
    (layout_test_fn_with_abi
      [mk_inst 0 PARAM [Lit 0w] ["retbuf"];
       mk_inst 1 RET [Var "rpc"] []]
      [] (SOME T) (SOME 0)) =
    SOME (mk_inst 0 PARAM [Lit 0w] ["retbuf"])
Proof
  EVAL_TAC >> decide_tac
QED

Definition layout_test_sig_def:
  layout_test_sig has_fmp publishes = <|
    fms_has_fmp_param := has_fmp;
    fms_publishes := publishes
  |>
End

Theorem invoke_arity_positive_eval:
  let callee = layout_test_fn_with_abi
      [mk_inst 0 PARAM [Lit 0w] ["u0"];
       mk_inst 1 PARAM [Lit 1w] ["u1"];
       mk_inst 2 RET [Var "r0"; Var "r1"; Var "rpc"] []]
      [] NONE (SOME 2) in
    invoke_input_arity_ok callee (layout_test_sig F F)
      (mk_inst 10 INVOKE [Label "callee"; Var "a0"; Var "a1"]
        ["o0"; "o1"]) /\
    invoke_input_arity_ok callee (layout_test_sig T F)
      (mk_inst 11 INVOKE
        [Label "callee"; Var "a0"; Var "a1"; Var "hidden_fmp"]
        ["o0"; "o1"]) /\
    invoke_output_arity_ok callee (layout_test_sig F F)
      (mk_inst 12 INVOKE [Label "callee"; Var "a0"; Var "a1"]
        ["o0"; "o1"]) /\
    invoke_output_arity_ok callee (layout_test_sig F T)
      (mk_inst 13 INVOKE [Label "callee"; Var "a0"; Var "a1"]
        ["o0"; "o1"; "published_fmp"])
Proof
  EVAL_TAC
QED

Theorem invoke_arity_fallback_and_malformed_eval:
  let inferred = layout_test_fn
      [mk_inst 0 PARAM [Lit 0w] ["u0"];
       mk_inst 1 RET [Var "r0"; Var "rpc"] []] [] in
    invoke_output_arity_ok inferred (layout_test_sig F F)
      (mk_inst 20 INVOKE [Label "callee"; Var "a0"] ["o0"]) /\
    ~invoke_input_arity_ok inferred (layout_test_sig F F)
      (mk_inst 21 INVOKE [Label "callee"] ["o0"]) /\
    ~invoke_input_arity_ok inferred (layout_test_sig T F)
      (mk_inst 22 INVOKE [Label "callee"; Var "a0"] ["o0"]) /\
    ~invoke_output_arity_ok inferred (layout_test_sig F T)
      (mk_inst 23 INVOKE [Label "callee"; Var "a0"] ["o0"]) /\
    ~invoke_output_arity_ok inferred (layout_test_sig F F)
      (mk_inst 24 ADD [Label "callee"; Var "a0"] ["o0"]) /\
    ~invoke_input_arity_ok inferred (layout_test_sig F F)
      (mk_inst 25 INVOKE [Var "not_a_label"; Var "a0"] ["o0"])
Proof
  EVAL_TAC
QED
val _ = export_theory();
