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

val _ = export_theory();
