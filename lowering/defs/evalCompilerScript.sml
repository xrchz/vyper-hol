(*
 * Compiler Evaluation Fixtures
 *
 * STATUS: Regression/evaluation support, not core lowering definitions.
 * Defines small Vyper AST programs and proves by EVAL_TAC that the executable
 * compiler produces SOME bytecode. Currently kept build-checked under defs/.
 *)

Theory evalCompiler
Ancestors compileVyper concretizeMemLocDefs alist byte integer_word option
Libs finite_mapLib computeLib wordsLib cv_transLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

val () = Globals.max_print_depth := 20

Definition noop_program_def:
  noop_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) NoneT [Pass]]
End

Definition return_uint_program_def:
  return_uint_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]]
End

Definition return_arg_program_def:
  return_arg_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Name (BaseT (UintT 256)) "x"))]]
End

Definition local_uint_program_def:
  local_uint_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 1));
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition add_arg_program_def:
  add_arg_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "x";
              Literal (BaseT (UintT 256)) (IntL 1)]))]]
End

Definition two_external_program_def:
  two_external_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))];
     FunctionDecl External Nonpayable F F "bar"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 2)))]]
End

Definition storage_read_program_def:
  storage_read_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]]
End

Definition storage_write_program_def:
  storage_write_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
          (Literal (BaseT (UintT 256)) (IntL 5));
        Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]]
End

Definition deploy_storage_program_def:
  deploy_storage_program =
    [VariableDecl Private Storage "stored" (BaseT (UintT 256)) (SOME 0);
     FunctionDecl Deploy Nonpayable F F "__init__"
       ([] : (string # type) list) ([] : expr list) NoneT
       [Assign (BaseTarget (TopLevelNameTarget (NONE, "stored")))
          (Literal (BaseT (UintT 256)) (IntL 5))];
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (TopLevelName (BaseT (UintT 256)) (NONE, "stored")))]]
End

Definition event_log_program_def:
  event_log_program =
    [EventDecl "Ping" [(("value", BaseT (UintT 256)), F)];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) NoneT
       [Log (NONE, "Ping") [Name (BaseT (UintT 256)) "x"]]]
End

Definition indexed_event_log_program_def:
  indexed_event_log_program =
    [EventDecl "Ping" [(("value", BaseT (UintT 256)), T)];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) NoneT
       [Log (NONE, "Ping") [Name (BaseT (UintT 256)) "x"]]]
End

Definition mixed_event_log_program_def:
  mixed_event_log_program =
    [EventDecl "Ping"
       [(("indexed_value", BaseT (UintT 256)), T);
        (("data_value", BaseT (UintT 256)), F)];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256)); ("y", BaseT (UintT 256))]
       ([] : expr list) NoneT
       [Log (NONE, "Ping")
          [Name (BaseT (UintT 256)) "x";
           Name (BaseT (UintT 256)) "y"]]]
End

Definition hashmap_read_program_def:
  hashmap_read_program =
    [HashMapDecl Private F "stored" (BaseT (UintT 256))
       (Type (BaseT (UintT 256))) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       [("k", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Subscript (BaseT (UintT 256))
             (TopLevelName NoneT (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))]]
End

Definition hashmap_write_program_def:
  hashmap_write_program =
    [HashMapDecl Private F "stored" (BaseT (UintT 256))
       (Type (BaseT (UintT 256))) (SOME 0);
     FunctionDecl External Nonpayable F F "foo"
       [("k", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Assign (BaseTarget
          (SubscriptTarget (TopLevelNameTarget (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))
          (Literal (BaseT (UintT 256)) (IntL 5));
        Return (SOME
          (Subscript (BaseT (UintT 256))
             (TopLevelName NoneT (NONE, "stored"))
             (Name (BaseT (UintT 256)) "k")))]]
End

Definition if_bool_program_def:
  if_bool_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT BoolT)] ([] : expr list) (BaseT (UintT 256))
       [If (Name (BaseT BoolT) "x")
          [Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]
          [Return (SOME (Literal (BaseT (UintT 256)) (IntL 2)))]]]
End

Definition if_join_program_def:
  if_join_program =
    [FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT BoolT)] ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 1));
        If (Name (BaseT BoolT) "x")
          [Assign (BaseTarget (NameTarget "y"))
             (Literal (BaseT (UintT 256)) (IntL 2))]
          [Assign (BaseTarget (NameTarget "y"))
             (Literal (BaseT (UintT 256)) (IntL 3))];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_pass_program_def:
  for_pass_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 2)))
          0
          [Pass];
        Return (SOME (Literal (BaseT (UintT 256)) (IntL 1)))]]
End

Definition for_accum_program_def:
  for_accum_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 2)))
          0
          [Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_continue_program_def:
  for_continue_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 3)))
          0
          [If (Builtin (BaseT BoolT) (Bop Eq)
                 [Name (BaseT (UintT 256)) "i";
                  Literal (BaseT (UintT 256)) (IntL 1)])
              [Continue]
              [];
           Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition for_break_program_def:
  for_break_program =
    [FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [AnnAssign "y" (BaseT (UintT 256))
          (Literal (BaseT (UintT 256)) (IntL 0));
        For "i" (BaseT (UintT 256))
          (Range (Literal (BaseT (UintT 256)) (IntL 0))
                 (Literal (BaseT (UintT 256)) (IntL 3)))
          0
          [If (Builtin (BaseT BoolT) (Bop Eq)
                 [Name (BaseT (UintT 256)) "i";
                  Literal (BaseT (UintT 256)) (IntL 2)])
              [Break]
              [];
           Assign (BaseTarget (NameTarget "y"))
             (Builtin (BaseT (UintT 256)) (Bop Add)
                [Name (BaseT (UintT 256)) "y";
                 Name (BaseT (UintT 256)) "i"])];
        Return (SOME (Name (BaseT (UintT 256)) "y"))]]
End

Definition internal_call_program_def:
  internal_call_program =
    [FunctionDecl Internal Nonpayable F F "bar"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Literal (BaseT (UintT 256)) (IntL 7)))];
     FunctionDecl External Nonpayable F F "foo"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
             ([] : expr list) NONE))]]
End

Definition internal_call_arg_program_def:
  internal_call_arg_program =
    [FunctionDecl Internal Nonpayable F F "bar"
       [("y", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "y";
              Literal (BaseT (UintT 256)) (IntL 1)]))];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Call (BaseT (UintT 256)) (IntCall (NONE, "bar"))
             [Name (BaseT (UintT 256)) "x"] NONE))]]
End


Definition nested_internal_call_program_def:
  nested_internal_call_program =
    [FunctionDecl Internal Nonpayable F F "leaf"
       [("z", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Name (BaseT (UintT 256)) "z"))];
     FunctionDecl Internal Nonpayable F F "mid"
       [("y", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Call (BaseT (UintT 256)) (IntCall (NONE, "leaf"))
             [Name (BaseT (UintT 256)) "y"] NONE))];
     FunctionDecl External Nonpayable F F "foo"
       [("x", BaseT (UintT 256))] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Call (BaseT (UintT 256)) (IntCall (NONE, "mid"))
             [Name (BaseT (UintT 256)) "x"] NONE))]]
End

Theorem nested_internal_call_source_descriptors:
  let (_, internal_fns, _, _) =
    classify_functions nested_internal_call_program in
  MAP (source_internal_fn_descriptor nested_internal_call_program)
    internal_fns = [("leaf", F, 1); ("mid", F, 1)]
Proof
  EVAL_TAC
QED

Definition nested_external_source_def:
  nested_external_source =
    (Nonpayable, F, F, "foo", [("x", BaseT (UintT 256))],
     ([] : expr list), BaseT (UintT 256),
     [Return (SOME
        (Call (BaseT (UintT 256)) (IntCall (NONE, "mid"))
           [Name (BaseT (UintT 256)) "x"] NONE))])
End

Definition nested_leaf_source_def:
  nested_leaf_source =
    (Nonpayable, F, F, "leaf", [("z", BaseT (UintT 256))],
     ([] : expr list), BaseT (UintT 256),
     [Return (SOME (Name (BaseT (UintT 256)) "z"))])
End

Definition nested_mid_source_def:
  nested_mid_source =
    (Nonpayable, F, F, "mid", [("y", BaseT (UintT 256))],
     ([] : expr list), BaseT (UintT 256),
     [Return (SOME
        (Call (BaseT (UintT 256)) (IntCall (NONE, "leaf"))
           [Name (BaseT (UintT 256)) "y"] NONE))])
End

Theorem nested_internal_call_classify:
  classify_functions nested_internal_call_program =
    ([nested_external_source],
     [nested_leaf_source; nested_mid_source], NONE, NONE)
Proof
  EVAL_TAC
QED

Theorem nested_foo_function_selector:
  function_selector "foo" [Uint 256] =
    ([47w; 190w; 189w; 56w] : byte list)
Proof
  CONV_TAC cv_eval
QED

Theorem nested_internal_call_selectors:
  build_selectors (type_env nested_internal_call_program)
    [nested_external_source] = [(801029432, "fn_foo", F)]
Proof
  simp[build_selectors_def, compute_selector_def,
       nested_external_source_def, nested_internal_call_program_def,
       vyperContextTheory.type_env_def,
       vyperContextTheory.type_env_for_module_def,
       nested_foo_function_selector,
       selectorDispatchTheory.calldata_method_id_def,
       selector_has_trailing_zeroes_def]
QED

Definition nested_external_cenv_def:
  nested_external_cenv =
    update_cenv_nonreentrant
      (update_cenv_ret_abi
        ((build_compile_env nested_internal_call_program External Nonpayable
            "foo" [("x", BaseT (UintT 256))] (BaseT (UintT 256))
            [Return (SOME
              (Call (BaseT (UintT 256)) (IntCall (NONE, "mid"))
                [Name (BaseT (UintT 256)) "x"] NONE))] F)
          with ce_raw_return := F)
        (BaseT (UintT 256))) F 0 F F
End

Definition nested_external_package_def:
  nested_external_package =
    ("fn_foo", nested_external_cenv,
     build_positional_args nested_external_cenv
       [("x", BaseT (UintT 256))],
     min_calldata_size nested_external_cenv
       [("x", BaseT (UintT 256))] 0,
     F, F, 0n, F, F,
     [Return (SOME
       (Call (BaseT (UintT 256)) (IntCall (NONE, "mid"))
         [Name (BaseT (UintT 256)) "x"] NONE))],
     SOME (BaseT (UintT 256)))
End

Theorem nested_internal_call_external_package:
  MAP (package_external_fn nested_internal_call_program F
         (assign_nkeys nested_internal_call_program 0))
      [nested_external_source] = [nested_external_package]
Proof
  simp[nested_external_source_def, nested_external_package_def,
       nested_external_cenv_def, package_external_fn_def,
       nested_internal_call_program_def, assign_nkeys_def]
QED

Definition nested_fallback_label_def:
  nested_fallback_label = fresh_label_output "fallback" 0
End

Definition nested_dispatch_stage_def:
  nested_dispatch_stage =
    do fallback_lbl <- fresh_label "fallback";
       compile_selector_dispatch_linear [(801029432, "fn_foo")] fallback_lbl;
       return fallback_lbl
    od
End

Definition nested_after_dispatch_state_def:
  nested_after_dispatch_state : compile_state =
    <| cs_next_var := 6;
       cs_next_label := 4;
       cs_next_id := 10;
       cs_current_bb := fresh_label_output "next" 3;
       cs_current_insts :=
         [mk_inst 9 JMP [Label nested_fallback_label] []];
       cs_blocks :=
         [<| bb_label := fresh_label_output "match" 2;
             bb_instructions :=
               [mk_inst 8 JMP [Label "fn_foo"] []] |>;
          <| bb_label := fresh_label_output "dispatch" 1;
             bb_instructions :=
               [mk_inst 4 CALLDATALOAD [Lit 0w] ["%3"];
                mk_inst 5 SHR [Lit 224w; Var "%3"] ["%4"];
                mk_inst 6 EQ [Var "%4"; Lit (n2w 801029432)] ["%5"];
                mk_inst 7 JNZ
                  [Var "%5"; Label (fresh_label_output "match" 2);
                   Label (fresh_label_output "next" 3)] []] |>;
          <| bb_label := "__entry";
             bb_instructions :=
               [mk_inst 0 CALLDATASIZE [] ["%0"];
                mk_inst 1 LT [Var "%0"; Lit 4w] ["%1"];
                mk_inst 2 ISZERO [Var "%1"] ["%2"];
                mk_inst 3 JNZ
                  [Var "%2"; Label (fresh_label_output "dispatch" 1);
                   Label nested_fallback_label] []] |>];
       cs_data_sections := [] |>
End

Theorem nested_dispatch_stage_eq:
  nested_dispatch_stage (initial_compile_state "__entry") =
    (nested_fallback_label, nested_after_dispatch_state)
Proof
  EVAL_TAC
QED

Theorem nested_external_entry_inputs:
  min_calldata_size nested_external_cenv [("x", BaseT (UintT 256))] 0 = 36 /\
  build_positional_args nested_external_cenv [("x", BaseT (UintT 256))] =
    [("x", T, F, 32, DecPrimWord NoClamp)] /\
  FLOOKUP nested_external_cenv.ce_vars "x" = SOME (MemLoc 0 32)
Proof
  simp[build_positional_args_single_uint256,
       min_calldata_size_single_uint256]
  >> simp[nested_external_cenv_def, update_cenv_nonreentrant_def,
          update_cenv_ret_abi_def]
  >> irule build_compile_env_external_single_uint_arg_lookup
  >> simp[nested_internal_call_program_def, add_module_var_locations_def,
          collect_locals_def]
QED


Definition nested_foo_entry_stage_def:
  nested_foo_entry_stage =
    do new_block "fn_foo";
       compile_entry_checks
         (min_calldata_size nested_external_cenv
            [("x", BaseT (UintT 256))] 0) F;
       compile_register_positional_args nested_external_cenv
         (build_positional_args nested_external_cenv
            [("x", BaseT (UintT 256))]) 4
    od
End

Definition nested_after_foo_entry_state_def:
  nested_after_foo_entry_state : compile_state =
    <| cs_next_var := 13;
       cs_next_label := 4;
       cs_next_id := 20;
       cs_current_bb := "fn_foo";
       cs_current_insts :=
         [mk_inst 10 CALLVALUE [] ["%6"];
          mk_inst 11 ISZERO [Var "%6"] ["%7"];
          mk_inst 12 ASSERT [Var "%7"] [];
          mk_inst 13 CALLDATASIZE [] ["%8"];
          mk_inst 14 LT [Var "%8"; Lit 36w] ["%9"];
          mk_inst 15 ISZERO [Var "%9"] ["%10"];
          mk_inst 16 ASSERT [Var "%10"] [];
          mk_inst 17 CALLDATASIZE [] ["%11"];
          mk_inst 18 CALLDATALOAD [Lit 4w] ["%12"];
          mk_inst 19 MSTORE [Lit 0w; Var "%12"] []];
       cs_blocks :=
         [<| bb_label := fresh_label_output "next" 3;
             bb_instructions :=
               [mk_inst 9 JMP [Label nested_fallback_label] []] |>;
          <| bb_label := fresh_label_output "match" 2;
             bb_instructions :=
               [mk_inst 8 JMP [Label "fn_foo"] []] |>;
          <| bb_label := fresh_label_output "dispatch" 1;
             bb_instructions :=
               [mk_inst 4 CALLDATALOAD [Lit 0w] ["%3"];
                mk_inst 5 SHR [Lit 224w; Var "%3"] ["%4"];
                mk_inst 6 EQ [Var "%4"; Lit (n2w 801029432)] ["%5"];
                mk_inst 7 JNZ
                  [Var "%5"; Label (fresh_label_output "match" 2);
                   Label (fresh_label_output "next" 3)] []] |>;
          <| bb_label := "__entry";
             bb_instructions :=
               [mk_inst 0 CALLDATASIZE [] ["%0"];
                mk_inst 1 LT [Var "%0"; Lit 4w] ["%1"];
                mk_inst 2 ISZERO [Var "%1"] ["%2"];
                mk_inst 3 JNZ
                  [Var "%2"; Label (fresh_label_output "dispatch" 1);
                   Label nested_fallback_label] []] |>];
       cs_data_sections := [] |>
End

Theorem nested_foo_entry_stage_eq:
  nested_foo_entry_stage nested_after_dispatch_state =
    ((), nested_after_foo_entry_state)
Proof
  simp[nested_foo_entry_stage_def, nested_external_entry_inputs,
       moduleLoweringTheory.compile_entry_checks_def,
       moduleLoweringTheory.compile_register_positional_args_def,
       moduleLoweringTheory.compile_decode_args_def,
       abiEncoderTheory.compile_abi_clamp_basetype_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       compileEnvTheory.new_block_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       nested_after_dispatch_state_def, nested_after_foo_entry_state_def]
QED
Definition nested_leaf_cenv_def:
  nested_leaf_cenv =
    update_cenv_nonreentrant
      ((build_compile_env nested_internal_call_program Internal Nonpayable
          "leaf" [("z", BaseT (UintT 256))] (BaseT (UintT 256))
          [Return (SOME (Name (BaseT (UintT 256)) "z"))] F)
        with <| ce_is_ctor := F; ce_raw_return := F |>)
      F 0 F F
End

Definition nested_leaf_package_def:
  nested_leaf_package =
    ("leaf", nested_leaf_cenv, [("z", T)], F,
     F, 0n, F, F, F, 0n,
     [Return (SOME (Name (BaseT (UintT 256)) "z"))],
     SOME (BaseT (UintT 256)))
End

Definition nested_mid_cenv_def:
  nested_mid_cenv =
    update_cenv_nonreentrant
      ((build_compile_env nested_internal_call_program Internal Nonpayable
          "mid" [("y", BaseT (UintT 256))] (BaseT (UintT 256))
          [Return (SOME
            (Call (BaseT (UintT 256)) (IntCall (NONE, "leaf"))
              [Name (BaseT (UintT 256)) "y"] NONE))] F)
        with <| ce_is_ctor := F; ce_raw_return := F |>)
      F 0 F F
End

Definition nested_mid_package_def:
  nested_mid_package =
    ("mid", nested_mid_cenv, [("y", T)], F,
     F, 0n, F, F, F, 0n,
     [Return (SOME
       (Call (BaseT (UintT 256)) (IntCall (NONE, "leaf"))
         [Name (BaseT (UintT 256)) "y"] NONE))],
     SOME (BaseT (UintT 256)))
End

Theorem nested_internal_call_internal_packages:
  MAP (package_internal_fn nested_internal_call_program F
         (assign_nkeys nested_internal_call_program 0) F)
      [nested_leaf_source; nested_mid_source] =
    [nested_leaf_package; nested_mid_package]
Proof
  simp[nested_leaf_source_def, nested_mid_source_def,
       nested_leaf_package_def, nested_mid_package_def,
       nested_leaf_cenv_def, nested_mid_cenv_def,
       package_internal_fn_def, nested_internal_call_program_def,
       assign_nkeys_def, make_struct_fields_map_def,
       compileEnvTheory.returns_stack_count_def,
       compileEnvTheory.compute_pass_via_stack_def,
       compileEnvTheory.is_word_type_def,
       compileEnvTheory.MAX_STACK_ARGS_def]
QED

Theorem nested_internal_call_packaged_descriptors:
  !use_trans nkey_map is_ctor_context.
    let (_, internal_fns, _, _) =
      classify_functions nested_internal_call_program in
    internal_fn_descriptors
      (MAP (package_internal_fn nested_internal_call_program
              use_trans nkey_map is_ctor_context) internal_fns) =
    [("leaf", F, 1); ("mid", F, 1)]
Proof
  rpt strip_tac
  >> rewrite_tac[internal_fn_descriptors_MAP_package_internal_fn]
  >> MATCH_ACCEPT_TAC nested_internal_call_source_descriptors
QED



Theorem empty_compiles:
  IS_SOME
    (compile_vyper ([] : toplevel list)
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem noop_compiles:
  IS_SOME
    (compile_vyper noop_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem return_uint_compiles:
  IS_SOME
    (compile_vyper return_uint_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem return_arg_compiles:
  IS_SOME
    (compile_vyper return_arg_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem local_uint_compiles:
  IS_SOME
    (compile_vyper local_uint_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem add_arg_compiles:
  IS_SOME
    (compile_vyper add_arg_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem two_external_compiles:
  IS_SOME
    (compile_vyper two_external_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem storage_read_compiles:
  IS_SOME
    (compile_vyper storage_read_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem storage_write_compiles:
  IS_SOME
    (compile_vyper storage_write_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem deploy_storage_compiles:
  IS_SOME
    (compile_vyper deploy_storage_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem event_log_compiles:
  IS_SOME
    (compile_vyper event_log_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem indexed_event_log_compiles:
  IS_SOME
    (compile_vyper indexed_event_log_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem mixed_event_log_compiles:
  IS_SOME
    (compile_vyper mixed_event_log_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem hashmap_read_compiles:
  IS_SOME
    (compile_vyper hashmap_read_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem hashmap_write_compiles:
  IS_SOME
    (compile_vyper hashmap_write_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem if_bool_compiles:
  IS_SOME
    (compile_vyper if_bool_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem if_join_compiles:
  IS_SOME
    (compile_vyper if_join_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem for_pass_compiles:
  IS_SOME
    (compile_vyper for_pass_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem for_accum_compiles:
  IS_SOME
    (compile_vyper for_accum_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem for_continue_compiles:
  IS_SOME
    (compile_vyper for_continue_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem for_break_compiles:
  IS_SOME
    (compile_vyper for_break_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem internal_call_compiles:
  IS_SOME
    (compile_vyper internal_call_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_compiles:
  IS_SOME
    (compile_vyper internal_call_arg_program
       concretize_context_eval Linear)
Proof
  EVAL_TAC
QED



Theorem nested_internal_call_packaging:
  case lower_vyper_runtime_unit nested_internal_call_program
         <| rpol_target := prague_capabilities;
            rpol_frontend_dispatch := Linear;
            rpol_final_assembly := FAP_Optimize |> of
    NONE => F
  | SOME unit =>
      let ctx = unit.cu_context in
      ctx_fn_names ctx = ["__entry"; "leaf"; "mid"] /\
      ALL_DISTINCT (ctx_fn_names ctx) /\
      wf_invoke_targets ctx /\
      OPTION_MAP (\fn. fn.fn_name)
        (lookup_function "leaf" ctx.ctx_functions) = SOME "leaf" /\
      OPTION_MAP (\fn. fn.fn_name)
        (lookup_function "mid" ctx.ctx_functions) = SOME "mid" /\
      MAP (\fn. (fn.fn_name, fn.fn_call_abi, fn.fn_noinline,
                 fn.fn_eom, fn.fn_fmp_signature)) ctx.ctx_functions =
        [("__entry", default_internal_call_abi, F, NONE, NONE);
         ("leaf",
          <| ica_has_memory_return_buffer := SOME F;
             ica_user_return_count := SOME 1 |>, F, NONE, NONE);
         ("mid",
          <| ica_has_memory_return_buffer := SOME F;
             ica_user_return_count := SOME 1 |>, F, NONE, NONE)] /\
      EVERY (\fn. fn.fn_eom = NONE /\ fn.fn_fmp_signature = NONE)
        ctx.ctx_functions
Proof
  rewrite_tac[GSYM wf_invoke_targets_check_eq] >> EVAL_TAC
QED
