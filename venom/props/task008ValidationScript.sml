(*
 * TASK_008 executable regression checks.
 *
 * These examples pin internal-return payloads, checked dynamic-return packing,
 * and the caller/callee frame boundary for FMP adoption.
 *)

Theory task008Validation
Ancestors
  venomExecSemantics words

Theorem task008_dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem task008_ret_and_retfmp:
  let s = init_venom_state "entry" with vs_fmp := (160w:bytes32) in
    step_inst_base (mk_inst 0 RET [Lit 11w; Lit 22w; Lit 999w] []) s =
      IntRet <| iret_values := [11w; 22w]; iret_adopt_fmp := NONE |> s /\
    step_inst_base (mk_inst 1 RETFMP [Lit 11w; Lit 22w; Lit 999w] []) s =
      IntRet <| iret_values := [11w; 22w];
                iret_adopt_fmp := SOME 160w |> s
Proof
  EVAL_TAC
QED

Theorem task008_multi_dynamic_dret:
  let s = init_venom_state "entry" with <|
      vs_memory := GENLIST (\i. n2w i) 64;
      vs_fmp := (777w:bytes32);
      vs_call_entry_fmp := 100w;
      vs_return_pc_token := 555w
    |> in
  let inst = mk_inst 2 DRET
      [Lit 2w; Lit 11w; Lit 1w; Lit 3w; Lit 10w; Lit 32w; Lit 999w] [] in
    parse_dret_shape inst = SOME (1,2) /\
    case step_inst_base inst s of
      IntRet ir s' =>
        ir.iret_values = [(11w:bytes32); 100w; 132w] /\
        ir.iret_adopt_fmp = SOME 164w /\
        s'.vs_fmp = (164w:bytes32) /\
        s'.vs_call_entry_fmp = (100w:bytes32) /\
        s'.vs_return_pc_token = (555w:bytes32) /\
        TAKE 3 (DROP 100 s'.vs_memory) =
          [(1w:byte); 2w; 3w] /\
        TAKE 32 (DROP 132 s'.vs_memory) =
          GENLIST (\i. n2w (10 + i)) 32
    | _ => F
Proof
  EVAL_TAC >> simp[dimword_def] >> wordsLib.WORD_DECIDE_TAC
QED

Theorem task008_nested_return_frame_boundary:
  let caller = init_venom_state "outer" with <|
      vs_fmp := (64w:bytes32);
      vs_call_entry_fmp := 32w;
      vs_return_pc_token := 11w
    |> in
  let ordinary_bb = <|
      bb_label := "ordinary";
      bb_instructions := [mk_inst 10 RET [Lit 222w] []]
    |> in
  let publishing_bb = <|
      bb_label := "publishing";
      bb_instructions :=
        [mk_inst 11 SETFMP [Lit 160w] [];
         mk_inst 12 RETFMP [Lit 222w] []]
    |> in
  let ordinary_fn = mk_raw_function "ordinary_fn" [ordinary_bb] in
  let publishing_fn = mk_raw_function "publishing_fn" [publishing_bb] in
  let ordinary_ctx = mk_venom_context [ordinary_fn] NONE in
  let publishing_ctx = mk_venom_context [publishing_fn] NONE in
  let ordinary_invoke =
      mk_inst 20 INVOKE [Label "ordinary_fn"; Lit 222w] [] in
  let publishing_invoke =
      mk_inst 21 INVOKE [Label "publishing_fn"; Lit 333w] [] in
    (case setup_callee ordinary_fn [(222w:bytes32)] caller of
       SOME callee =>
         callee.vs_call_entry_fmp = (64w:bytes32) /\
         callee.vs_return_pc_token = (222w:bytes32)
     | NONE => F) /\
    (case setup_callee publishing_fn [(333w:bytes32)] caller of
       SOME callee =>
         callee.vs_call_entry_fmp = (64w:bytes32) /\
         callee.vs_return_pc_token = (333w:bytes32)
     | NONE => F) /\
    (case step_inst 2 ordinary_ctx ordinary_invoke caller of
       OK s =>
         s.vs_fmp = (64w:bytes32) /\
         s.vs_call_entry_fmp = (32w:bytes32) /\
         s.vs_return_pc_token = (11w:bytes32)
     | _ => F) /\
    (case step_inst 2 publishing_ctx publishing_invoke caller of
       OK s =>
         s.vs_fmp = (160w:bytes32) /\
         s.vs_call_entry_fmp = (32w:bytes32) /\
         s.vs_return_pc_token = (11w:bytes32)
     | _ => F)
Proof
  EVAL_TAC
QED

Theorem task008_malformed_and_undefined_dret:
  let s = init_venom_state "entry" in
    step_inst_base (mk_inst 30 DRET [Lit 0w; Lit 999w] []) s =
      Error "dret: malformed operand envelope" /\
    step_inst_base
      (mk_inst 31 DRET
        [Lit 1w; Lit 7w; Var "missing"; Lit 3w; Lit 999w] []) s =
      Error "dret: undefined operand" /\
    step_inst_base
      (mk_inst 32 DRET
        [Lit 1w; Lit 7w; Lit 1w; Lit 3w; Lit 999w] ["bad"]) s =
      Error "dret requires no outputs"
Proof
  EVAL_TAC
QED

val _ = export_theory();
