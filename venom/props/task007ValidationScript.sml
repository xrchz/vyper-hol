(*
 * TASK_007 executable regression checks.
 *
 * These checked examples pin the intended raw-FMP, explicit BUMP, and hidden
 * parameter semantics, including malformed instruction behaviour.
 *)

Theory task007Validation
Ancestors
  venomExecSemantics venomLayout words

Theorem task007_dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem task007_ceil32_validation:
  ceil32 0 = 0 /\
  ceil32 1 = 32 /\
  ceil32 32 = 32 /\
  ceil32 33 = 64 /\
  ceil32 (dimword (:256) - 32) = dimword (:256) - 32 /\
  33 <= ceil32 33 /\
  ceil32 33 MOD 32 = 0 /\
  ceil32 (dimword (:256) - 32) < dimword (:256)
Proof
  EVAL_TAC >> simp[dimword_def]
QED

Theorem task007_valid_fmp_steps:
  let s_get = init_venom_state "entry" with vs_fmp := (64w:bytes32) in
  let s_set = init_venom_state "entry" in
  let s_alloc = init_venom_state "entry" with vs_fmp := (96w:bytes32) in
  let s_initial = init_venom_state "entry" with vs_initial_fmp := (224w:bytes32) in
  let s_param = init_venom_state "entry" with vs_params := [(11w:bytes32); 22w] in
    step_inst_base (mk_inst 0 GETFMP [] ["out"]) s_get =
      OK (update_var "out" 64w s_get) /\
    step_inst_base (mk_inst 1 SETFMP [Lit 128w] []) s_set =
      OK (s_set with vs_fmp := 128w) /\
    step_inst_base (mk_inst 2 DALLOCA [Lit 33w] ["ptr"]) s_alloc =
      OK (update_var "ptr" 96w (s_alloc with vs_fmp := 160w)) /\
    step_inst_base (mk_inst 3 INITIAL_FMP [] ["out"]) s_initial =
      OK (update_var "out" 224w s_initial) /\
    step_inst_base (mk_inst 4 FMP_PARAM [Lit 1w] ["out"]) s_param =
      OK (update_var "out" 22w s_param)
Proof
  EVAL_TAC >> simp[dimword_def] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem task007_bump_wraps_and_is_fmp_independent:
  let base : bytes32 = n2w (dimword (:256) - 16) in
  let s = init_venom_state "entry" with <|
      vs_fmp := (777w:bytes32);
      vs_call_entry_fmp := 888w;
      vs_initial_fmp := 999w;
      vs_return_pc_token := 111w
    |> in
    step_inst_base
      (mk_inst 5 BUMP [Lit base; Lit 33w] ["ptr"; "next"]) s =
    OK (update_var "next" 48w (update_var "ptr" base s))
Proof
  EVAL_TAC
QED

Theorem task007_retpc_ignores_params:
  let s_empty = init_venom_state "entry" with <|
      vs_params := [];
      vs_return_pc_token := (444w:bytes32)
    |> in
  let s_other = init_venom_state "entry" with <|
      vs_params := [(1w:bytes32); 2w; 3w];
      vs_return_pc_token := (444w:bytes32)
    |> in
    step_inst_base (mk_inst 6 RETPC_PARAM [Lit 0w] ["ret"]) s_empty =
      OK (update_var "ret" 444w s_empty) /\
    step_inst_base (mk_inst 7 RETPC_PARAM [Lit 99w] ["ret"]) s_other =
      OK (update_var "ret" 444w s_other)
Proof
  EVAL_TAC
QED

Theorem task007_malformed_shape_steps:
  let s = init_venom_state "entry" in
    step_inst_base (mk_inst 10 GETFMP [Lit 0w] ["out"]) s =
      Error "getfmp requires no operands and one output" /\
    step_inst_base (mk_inst 11 GETFMP [] []) s =
      Error "getfmp requires no operands and one output" /\
    step_inst_base (mk_inst 12 SETFMP [] []) s =
      Error "setfmp requires one operand and no outputs" /\
    step_inst_base (mk_inst 13 SETFMP [Lit 0w] ["out"]) s =
      Error "setfmp requires one operand and no outputs" /\
    step_inst_base (mk_inst 14 DALLOCA [] ["out"]) s =
      Error "dalloca requires one operand and one output" /\
    step_inst_base (mk_inst 15 DALLOCA [Lit 0w] []) s =
      Error "dalloca requires one operand and one output" /\
    step_inst_base (mk_inst 16 INITIAL_FMP [Lit 0w] ["out"]) s =
      Error "initial_fmp requires no operands and one output" /\
    step_inst_base (mk_inst 17 INITIAL_FMP [] []) s =
      Error "initial_fmp requires no operands and one output" /\
    step_inst_base (mk_inst 18 BUMP [Lit 0w] ["a"; "b"]) s =
      Error "bump requires two operands and two outputs" /\
    step_inst_base (mk_inst 19 BUMP [Lit 0w; Lit 0w] ["a"]) s =
      Error "bump requires two operands and two outputs" /\
    step_inst_base (mk_inst 20 FMP_PARAM [] ["out"]) s =
      Error "fmp_param requires literal index and one output" /\
    step_inst_base (mk_inst 21 FMP_PARAM [Lit 0w] []) s =
      Error "fmp_param requires literal index and one output" /\
    step_inst_base (mk_inst 22 RETPC_PARAM [] ["out"]) s =
      Error "retpc_param requires literal index and one output" /\
    step_inst_base (mk_inst 23 RETPC_PARAM [Lit 0w] []) s =
      Error "retpc_param requires literal index and one output"
Proof
  EVAL_TAC
QED

Theorem task007_undefined_and_range_errors:
  let s = init_venom_state "entry" in
    step_inst_base (mk_inst 30 SETFMP [Var "missing"] []) s =
      Error "setfmp: undefined operand" /\
    step_inst_base (mk_inst 31 DALLOCA [Var "missing"] ["out"]) s =
      Error "dalloca: undefined operand" /\
    step_inst_base
      (mk_inst 32 BUMP [Var "missing"; Lit 0w] ["a"; "b"]) s =
      Error "bump: undefined operand" /\
    step_inst_base (mk_inst 33 FMP_PARAM [Lit 0w] ["out"]) s =
      Error "fmp_param: index out of range" /\
    step_inst_base (mk_inst 34 FMP_PARAM [Var "missing"] ["out"]) s =
      Error "fmp_param requires literal index and one output" /\
    step_inst_base (mk_inst 35 RETPC_PARAM [Var "missing"] ["out"]) s =
      Error "retpc_param requires literal index and one output"
Proof
  EVAL_TAC
QED

val _ = export_theory();
