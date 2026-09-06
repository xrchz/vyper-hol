(* Focused executable validation for TASK 045 plan generation/execution. *)

Theory task045Validation
Ancestors
  planExec
Libs
  BasicProvers

Definition task045_param_inst_def:
  task045_param_inst id opc idx out = mk_inst id opc [Lit (n2w idx)] [out]
End

Definition task045_valid_fn_def:
  task045_valid_fn =
    mk_raw_function "task045_valid"
      [<| bb_label := "entry";
          bb_instructions :=
            [task045_param_inst 0 PARAM 0 "u0";
             task045_param_inst 1 FMP_PARAM 1 "fmp";
             task045_param_inst 2 RETPC_PARAM 2 "retpc"] |>]
End

Definition task045_param_live_def:
  task045_param_live =
    <| ds_inst := FEMPTY |+ (("entry", 3), ["u0"; "fmp"; "retpc"]);
       ds_boundary := FEMPTY |>
End

Definition task045_param_state_def:
  task045_param_state spill_base =
    (init_plan_state spill_base) with
      ps_stack := [Var "u0"; Var "fmp"; Var "retpc"]
End

Definition task045_initial_fmp_inst_def:
  task045_initial_fmp_inst = mk_inst 0 INITIAL_FMP [] ["fmp"]
End

Theorem task045_initial_fmp_plan_trace:
  generate_emit_ops task045_initial_fmp_inst 0 (init_plan_state 0) =
    ([SOInitialFmp], init_plan_state 0)
Proof
  EVAL_TAC
QED

Theorem task045_initial_fmp_trace:
  exec_stack_op 320 SOInitialFmp = [AsmPush [1w; 64w]] /\
  execute_plan 320 [SOInitialFmp] = [AsmPush [1w; 64w]] /\
  ~MEM (AsmOp "MSIZE") (execute_plan 320 [SOInitialFmp])
Proof
  EVAL_TAC
QED

Definition task045_bump_inst_def:
  task045_bump_inst =
    mk_inst 3 BUMP [Var "base"; Var "size"] ["ptr"; "next"]
End

Definition task045_bump_state_def:
  task045_bump_state =
    (init_plan_state 0) with ps_stack := [Var "base"; Var "size"]
End

Theorem task045_bump_emit_trace:
  generate_emit_ops task045_bump_inst 0 task045_bump_state =
    ([SOPush (Lit 31w); SOEmit "ADD";
      SOPush (Lit 5w); SOEmit "SHR";
      SOPush (Lit 5w); SOEmit "SHL";
      SODup 2; SOEmit "ADD"], task045_bump_state) /\
  execute_plan 0
    [SOPush (Lit 31w); SOEmit "ADD";
     SOPush (Lit 5w); SOEmit "SHR";
     SOPush (Lit 5w); SOEmit "SHL";
     SODup 2; SOEmit "ADD"] =
    [AsmPush [31w]; AsmOp "ADD";
     AsmPush [5w]; AsmOp "SHR";
     AsmPush [5w]; AsmOp "SHL";
     AsmOp "DUP2"; AsmOp "ADD"]
Proof
  EVAL_TAC
QED

Theorem task045_bump_plan_trace:
  generate_regular_inst_plan task045_param_live dfg_empty
    (cfg_analyze task045_valid_fn) task045_valid_fn task045_bump_inst
    ["ptr"; "next"] F F "entry" task045_bump_state =
  ([SOPush (Lit 31w); SOEmit "ADD";
    SOPush (Lit 5w); SOEmit "SHR";
    SOPush (Lit 5w); SOEmit "SHL";
    SODup 2; SOEmit "ADD"],
   task045_bump_state with ps_stack := [Var "ptr"; Var "next"])
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem task045_canonical_params_trace:
  canonical_param_prefix task045_valid_fn /\
  get_params (HD task045_valid_fn.fn_blocks).bb_instructions =
    [task045_param_inst 0 PARAM 0 "u0";
     task045_param_inst 1 FMP_PARAM 1 "fmp";
     task045_param_inst 2 RETPC_PARAM 2 "retpc"] /\
  prepare_params_plan task045_param_live task045_valid_fn
    (init_plan_state 64) = ([], task045_param_state 64) /\
  execute_plan 320 [] = []
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Definition task045_fn_def:
  task045_fn name insts =
    mk_raw_function name [<|bb_label := "entry"; bb_instructions := insts|>]
End

Definition task045_bad_order_def:
  task045_bad_order = task045_fn "bad_order"
    [task045_param_inst 0 FMP_PARAM 0 "fmp";
     task045_param_inst 1 PARAM 1 "u0"]
End

Definition task045_bad_index_def:
  task045_bad_index = task045_fn "bad_index"
    [task045_param_inst 0 PARAM 1 "u0"]
End

Definition task045_bad_duplicate_def:
  task045_bad_duplicate = task045_fn "bad_duplicate"
    [task045_param_inst 0 FMP_PARAM 0 "fmp0";
     task045_param_inst 1 FMP_PARAM 1 "fmp1"]
End

Definition task045_bad_nonprefix_def:
  task045_bad_nonprefix = task045_fn "bad_nonprefix"
    [task045_param_inst 0 PARAM 0 "u0";
     mk_inst 1 ADD [] ["x"];
     task045_param_inst 2 RETPC_PARAM 2 "retpc"]
End

Theorem task045_malformed_prefix_rejected:
  let bad = [task045_bad_order; task045_bad_index;
             task045_bad_duplicate; task045_bad_nonprefix] in
    EVERY (\fn. ~canonical_param_prefix fn) bad /\
    EVERY (\fn. ~codegen_ready_fn fn) bad /\
    EVERY (\fn. generate_fn_plan fn 0 0 = NONE) bad /\
    EVERY (\fn. generate_fn_plan_fuel 20 fn 0 0 = NONE) bad
Proof
  EVAL_TAC >> wordsLib.WORD_DECIDE_TAC
QED

Theorem task045_raw_fmp_and_memtop_rejected:
  let rejected = [DALLOCA; DRET; GETFMP; SETFMP; RETFMP; MEMTOP] in
    MAP is_pre_codegen_opcode rejected = REPLICATE 6 T /\
    MAP (\opc. codegen_ready_inst (mk_inst 0 opc [] [])) rejected =
      REPLICATE 6 F /\
    MAP (\opc. generate_inst_plan task045_param_live dfg_empty
          (cfg_analyze task045_valid_fn) task045_valid_fn
          (mk_inst 0 opc [] []) [] F F "entry" (init_plan_state 0)) rejected =
      REPLICATE 6 NONE
Proof
  EVAL_TAC
QED
