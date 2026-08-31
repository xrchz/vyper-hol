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

Theorem nested_external_cenv_body_facts:
  FLOOKUP nested_external_cenv.ce_vars "x" = SOME (MemLoc 0 32) /\
  FLOOKUP nested_external_cenv.ce_vars "__return_pc__" = NONE /\
  nested_external_cenv.ce_func_info "mid" = (1,0,[T]) /\
  (nested_external_cenv.ce_raw_return <=> F) /\
  nested_external_cenv.ce_ret_enc_info = AbiPrimWord /\
  nested_external_cenv.ce_max_return_size = 32 /\
  nested_external_cenv.ce_nonreentrant = (F,0,F,F) /\
  expr_type
    (Call (BaseT (UintT 256)) (IntCall (NONE,"mid"))
      [Name (BaseT (UintT 256)) "x"] NONE) = BaseT (UintT 256) /\
  is_word_type (BaseT (UintT 256))
Proof
  conj_tac
  >- metis_tac[nested_external_entry_inputs]
  >> conj_tac
  >- (simp[nested_external_cenv_def, update_cenv_nonreentrant_def,
           update_cenv_ret_abi_def]
      >> irule build_compile_env_external_single_uint_arg_no_return_pc
      >> simp[nested_internal_call_program_def, add_module_var_locations_def,
              collect_locals_def])
  >> conj_tac
  >- simp[nested_external_cenv_def, update_cenv_nonreentrant_def,
          update_cenv_ret_abi_def, build_compile_env_ce_func_info,
          nested_internal_call_program_def, build_func_info_def,
          make_struct_fields_map_def, compileEnvTheory.get_struct_fields_def,
          compileEnvTheory.compute_func_info_def,
          compileEnvTheory.returns_stack_count_def,
          compileEnvTheory.compute_pass_via_stack_def,
          compileEnvTheory.is_word_type_def,
          compileEnvTheory.MAX_STACK_ARGS_def]
  >> simp[nested_external_cenv_def, update_cenv_nonreentrant_def,
          update_cenv_ret_abi_def, build_compile_env_ce_struct_fields,
          exprLoweringTheory.type_to_abi_enc_info_def,
          compileEnvTheory.abi_size_bound_def,
          compileEnvTheory.abi_static_size_def,
          vyperASTTheory.expr_type_def,
          compileEnvTheory.is_word_type_def]
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

Definition nested_foo_name_stage_def:
  nested_foo_name_stage =
    lower_value compile_expr nested_external_cenv (BaseT (UintT 256))
      (Name (BaseT (UintT 256)) "x")
End

Definition nested_foo_x_operand_def:
  nested_foo_x_operand = Var "%13"
End

Definition nested_after_foo_name_state_def:
  nested_after_foo_name_state =
    nested_after_foo_entry_state with
      <| cs_next_var := 14;
         cs_next_id := 21;
         cs_current_insts :=
           nested_after_foo_entry_state.cs_current_insts ++
             [mk_inst 20 MLOAD [Lit 0w] ["%13"]] |>
End

Theorem nested_foo_name_stage_eq:
  nested_foo_name_stage nested_after_foo_entry_state =
    (nested_foo_x_operand, nested_after_foo_name_state)
Proof
  simp[nested_foo_name_stage_def, exprLoweringTheory.lower_value_def,
       Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_name_vv_def,
       nested_external_cenv_body_facts,
       exprLoweringTheory.unwrap_value_def,
       vyperASTTheory.expr_type_def,
       compileEnvTheory.is_word_type_def, contextTheory.mk_ptr_def,
       contextTheory.compile_ptr_load_def, emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def, nested_foo_x_operand_def,
       nested_after_foo_entry_state_def, nested_after_foo_name_state_def]
QED

Theorem nested_foo_singleton_args_stage_eq:
  compile_multi_exprs
    (\cenv ty e st. compile_expr cenv ty e st)
    nested_external_cenv
    [Name (BaseT (UintT 256)) "x"]
    nested_after_foo_entry_state =
  ([nested_foo_x_operand], nested_after_foo_name_state)
Proof
  simp[SF ETA_ss, exprLoweringTheory.compile_multi_exprs_def,
       vyperASTTheory.expr_type_def,
       GSYM nested_foo_name_stage_def, nested_foo_name_stage_eq,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def]
QED

Definition nested_foo_mid_call_stage_def:
  nested_foo_mid_call_stage =
    lower_value compile_expr nested_external_cenv (BaseT (UintT 256))
      (Call (BaseT (UintT 256)) (IntCall (NONE, "mid"))
        [Name (BaseT (UintT 256)) "x"] NONE)
End

Definition nested_foo_mid_call_operand_def:
  nested_foo_mid_call_operand = Var "%16"
End


Definition nested_after_foo_alloc_state_def:
  nested_after_foo_alloc_state =
    nested_after_foo_name_state with
      <| cs_next_var := 15;
         cs_next_id := 22;
         cs_current_insts :=
           nested_after_foo_name_state.cs_current_insts ++
             [mk_inst 21 ALLOCA [Lit 32w] ["%14"]] |>
End

Theorem fresh_vars_one:
  !cs. fresh_vars 1 cs =
    (["%" ++ toString cs.cs_next_var],
     cs with cs_next_var := cs.cs_next_var + 1)
Proof
  gen_tac
  >> rewrite_tac[arithmeticTheory.ONE,
                 CONJUNCT2 emitHelperTheory.fresh_vars_def,
                 CONJUNCT1 emitHelperTheory.fresh_vars_def]
  >> simp[compileEnvTheory.fresh_var_def,
          compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def]
QED

Theorem nested_after_foo_alloc_state_next_var:
  nested_after_foo_alloc_state.cs_next_var = 15
Proof
  simp[nested_after_foo_alloc_state_def]
QED

Theorem nested_foo_fresh_vars_one_eq:
  fresh_vars 1 nested_after_foo_alloc_state =
    (["%15"], nested_after_foo_alloc_state with cs_next_var := 16)
Proof
  simp[fresh_vars_one, nested_after_foo_alloc_state_next_var]
QED

Definition nested_after_foo_invoke_state_def:
  nested_after_foo_invoke_state =
    (nested_after_foo_alloc_state with cs_next_var := 16) with
      <| cs_next_id := 23;
         cs_current_insts :=
           nested_after_foo_alloc_state.cs_current_insts ++
             [mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"]] |>
End

Theorem nested_foo_emit_mid_one_eq:
  emit_multi_op INVOKE [Label "mid"; nested_foo_x_operand] 1
    nested_after_foo_alloc_state =
  ([Var "%15"], nested_after_foo_invoke_state)
Proof
  simp[emitHelperTheory.emit_multi_op_def,
       nested_foo_fresh_vars_one_eq,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       nested_after_foo_invoke_state_def]
  >> simp[nested_after_foo_alloc_state_def]
QED
Definition nested_after_foo_mid_call_state_def:
  nested_after_foo_mid_call_state =
    nested_after_foo_name_state with
      <| cs_next_var := 17;
         cs_next_id := 25;
         cs_current_insts :=
           nested_after_foo_name_state.cs_current_insts ++
             [mk_inst 21 ALLOCA [Lit 32w] ["%14"];
              mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"];
              mk_inst 23 MSTORE [Var "%14"; Var "%15"] [];
              mk_inst 24 MLOAD [Var "%14"] ["%16"]] |>
End

Theorem nested_foo_mid_call_stage_eq:
  nested_foo_mid_call_stage nested_after_foo_entry_state =
    (nested_foo_mid_call_operand, nested_after_foo_mid_call_state)
Proof
  `nested_after_foo_name_state.cs_next_var = 14 /\
   nested_after_foo_name_state.cs_next_id = 21` by
    simp[nested_after_foo_name_state_def]
  >> simp[nested_foo_mid_call_stage_def, exprLoweringTheory.lower_value_def,
       Once exprLoweringTheory.compile_expr_def,
       Once exprLoweringTheory.compile_call_def,
       compileEnvTheory.nsid_to_string_def,
       vyperASTTheory.expr_type_def,
       nested_external_cenv_body_facts,
       nested_foo_singleton_args_stage_eq,
       exprLoweringTheory.compile_stage_intcall_args_def,
       contextTheory.compile_alloc_buffer_def,
       emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       GSYM nested_after_foo_alloc_state_def]
  >> rewrite_tac[nested_foo_emit_mid_one_eq]
  >> simp[exprLoweringTheory.store_multi_results_def,
          contextTheory.base_ptr_def, exprLoweringTheory.unwrap_value_def,
          contextTheory.compile_ptr_load_def,
          compileEnvTheory.is_word_type_def,
          emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
          compileEnvTheory.emit_def,
          nested_foo_mid_call_operand_def,
          nested_after_foo_mid_call_state_def,
          nested_after_foo_invoke_state_def,
          nested_after_foo_alloc_state_def]
  >> `nested_after_foo_name_state.cs_current_insts ++
        [mk_inst 21 ALLOCA [Lit 32w] ["%14"]] ++
        [mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"]] ++
        [mk_inst 23 MSTORE [Var "%14"; Var "%15"] []] ++
        [mk_inst 24 MLOAD [Var "%14"] ["%16"]] =
      nested_after_foo_name_state.cs_current_insts ++
        [mk_inst 21 ALLOCA [Lit 32w] ["%14"];
         mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"];
         mk_inst 23 MSTORE [Var "%14"; Var "%15"] [];
         mk_inst 24 MLOAD [Var "%14"] ["%16"]]` by
       (rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[])
  >> simp[]
QED

Definition nested_foo_external_return_stage_def:
  nested_foo_external_return_stage =
    compile_external_return (SOME nested_foo_mid_call_operand) T F
      AbiPrimWord 32 F 0 F F
End

Definition nested_after_foo_body_state_def:
  nested_after_foo_body_state =
    nested_after_foo_mid_call_state with
      <| cs_next_var := 18;
         cs_next_id := 28;
         cs_current_insts :=
           nested_after_foo_mid_call_state.cs_current_insts ++
             [mk_inst 25 ALLOCA [Lit 32w] ["%17"];
              mk_inst 26 MSTORE [Var "%17"; nested_foo_mid_call_operand] [];
              mk_inst 27 RETURN [Var "%17"; Lit 32w] []] |>
End

Theorem nested_foo_external_return_stage_eq:
  nested_foo_external_return_stage nested_after_foo_mid_call_state =
    ((), nested_after_foo_body_state)
Proof
  simp[nested_foo_external_return_stage_def,
       stmtLoweringTheory.compile_external_return_def,
       contextTheory.compile_alloc_buffer_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       nested_foo_mid_call_operand_def,
       nested_after_foo_body_state_def,
       nested_after_foo_mid_call_state_def]
  >> `(nested_after_foo_name_state.cs_current_insts ++
         [mk_inst 21 ALLOCA [Lit 32w] ["%14"];
          mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"];
          mk_inst 23 MSTORE [Var "%14"; Var "%15"] [];
          mk_inst 24 MLOAD [Var "%14"] ["%16"]]) ++
        [mk_inst 25 ALLOCA [Lit 32w] ["%17"]] ++
        [mk_inst 26 MSTORE [Var "%17"; Var "%16"] []] ++
        [mk_inst 27 RETURN [Var "%17"; Lit 32w] []] =
      (nested_after_foo_name_state.cs_current_insts ++
         [mk_inst 21 ALLOCA [Lit 32w] ["%14"];
          mk_inst 22 INVOKE [Label "mid"; nested_foo_x_operand] ["%15"];
          mk_inst 23 MSTORE [Var "%14"; Var "%15"] [];
          mk_inst 24 MLOAD [Var "%14"] ["%16"]]) ++
        [mk_inst 25 ALLOCA [Lit 32w] ["%17"];
         mk_inst 26 MSTORE [Var "%17"; Var "%16"] [];
         mk_inst 27 RETURN [Var "%17"; Lit 32w] []]` by
       (rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[])
  >> simp[]
QED


Theorem nested_LAST_APPEND_NONEMPTY_SUFFIX:
  !prefix suffix. suffix <> [] ==>
    LAST (prefix ++ suffix) = LAST suffix
Proof
  rpt strip_tac
  >> Cases_on `suffix`
  >> gvs[listTheory.LAST_APPEND_CONS]
QED
Theorem nested_after_foo_body_state_terminated:
  block_is_terminated nested_after_foo_body_state
Proof
  `nested_after_foo_body_state.cs_current_insts <> []` by
    simp[nested_after_foo_body_state_def,
         nested_after_foo_mid_call_state_def]
  >> `LAST nested_after_foo_body_state.cs_current_insts =
        mk_inst 27 RETURN [Var "%17"; Lit 32w] []` by
       simp[nested_after_foo_body_state_def,
            nested_after_foo_mid_call_state_def,
            nested_LAST_APPEND_NONEMPTY_SUFFIX]
  >> Cases_on `nested_after_foo_body_state.cs_current_insts`
  >- gvs[]
  >> FIRST
       [qpat_assum `nested_after_foo_body_state.cs_current_insts = _`
          (fn th => rewrite_tac[th]),
        qpat_assum `_ = nested_after_foo_body_state.cs_current_insts`
          (fn th => rewrite_tac[GSYM th])]
  >> simp[compileEnvTheory.block_is_terminated_def,
          venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def]
QED

Definition nested_foo_guarded_body_stage_def:
  nested_foo_guarded_body_stage =
    compile_guarded_body nested_external_cenv F 0 F F
      [Return (SOME
        (Call (BaseT (UintT 256)) (IntCall (NONE, "mid"))
          [Name (BaseT (UintT 256)) "x"] NONE))]
      (SOME (BaseT (UintT 256)))
End

Theorem nested_foo_guarded_body_stage_eq:
  nested_foo_guarded_body_stage nested_after_foo_entry_state =
    ((), nested_after_foo_body_state)
Proof
  `~block_is_terminated nested_after_foo_entry_state` by
    simp[compileEnvTheory.block_is_terminated_def,
         nested_after_foo_entry_state_def,
         venomInstTheory.mk_inst_def,
         venomInstTheory.is_terminator_def]
  >> simp[nested_foo_guarded_body_stage_def,
       moduleLoweringTheory.compile_guarded_body_def,
       stmtLoweringTheory.compile_stmt_def,
       compileEnvTheory.comp_get_def,
       compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       nested_external_cenv_body_facts,
       vyperASTTheory.expr_type_def,
       compileEnvTheory.is_word_type_def,
       GSYM nested_foo_mid_call_stage_def,
       nested_foo_mid_call_stage_eq,
       GSYM nested_foo_external_return_stage_def,
       nested_foo_external_return_stage_eq,
       nested_after_foo_body_state_terminated]
QED

Theorem comp_ignore_bind_assoc[local]:
  !m n p.
    comp_ignore_bind (comp_ignore_bind m n) p =
    comp_ignore_bind m (comp_ignore_bind n p)
Proof
  simp[compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_bind_assoc]
QED

Theorem nested_external_fn_bodies_eq:
  compile_external_fn_bodies [nested_external_package]
    nested_after_dispatch_state = ((), nested_after_foo_body_state)
Proof
  `compile_external_fn_bodies [nested_external_package] =
    (do nested_foo_entry_stage;
        nested_foo_guarded_body_stage;
        return ()
     od)` by
    simp[moduleLoweringTheory.compile_external_fn_bodies_def,
         nested_external_package_def,
         moduleLoweringTheory.compile_external_function_body_def,
         nested_foo_entry_stage_def,
         nested_foo_guarded_body_stage_def,
         comp_ignore_bind_assoc]
  >> pop_assum (fn th => rewrite_tac[th])
  >> simp[nested_foo_entry_stage_eq,
          nested_foo_guarded_body_stage_eq,
          compileEnvTheory.comp_return_def,
          compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def]
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

Theorem nested_leaf_cenv_entry_facts:
  FLOOKUP nested_leaf_cenv.ce_vars "z" = SOME (MemLoc 0 32) /\
  FLOOKUP nested_leaf_cenv.ce_vars "__return_pc__" = SOME (MemLoc 32 32) /\
  FLOOKUP nested_leaf_cenv.ce_vars "__return_buf__" = NONE /\
  nested_leaf_cenv.ce_returns_count = 1
Proof
  simp[nested_leaf_cenv_def, update_cenv_nonreentrant_def,
       build_compile_env_def, nested_internal_call_program_def,
       add_module_var_locations_def, collect_locals_def,
       allocate_args_def, allocate_internal_special_vars_def,
       make_struct_fields_map_def, compileEnvTheory.get_struct_fields_def,
       compileEnvTheory.returns_stack_count_def,
       compileEnvTheory.is_word_type_def,
       type_mem_bytes_def]
  >> pairarg_tac
  >> pop_assum (fn th => rewrite_tac[th])
  >> simp[finite_mapTheory.FLOOKUP_UPDATE,
          finite_mapTheory.FLOOKUP_EMPTY]
QED


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



Definition nested_fallback_stage_def:
  nested_fallback_stage =
    do new_block nested_fallback_label;
       emit_inst REVERT [Lit 0w; Lit 0w] []
    od
End

Definition nested_after_fallback_state_def:
  nested_after_fallback_state =
    nested_after_foo_body_state with
      <| cs_next_id := 29;
         cs_current_bb := nested_fallback_label;
         cs_current_insts := [mk_inst 28 REVERT [Lit 0w; Lit 0w] []];
         cs_blocks :=
           <| bb_label := nested_after_foo_body_state.cs_current_bb;
              bb_instructions := nested_after_foo_body_state.cs_current_insts |> ::
           nested_after_foo_body_state.cs_blocks |>
End

Theorem nested_fallback_stage_eq:
  nested_fallback_stage nested_after_foo_body_state =
    ((), nested_after_fallback_state)
Proof
  simp[nested_fallback_stage_def, nested_after_fallback_state_def,
       compileEnvTheory.new_block_def, emitHelperTheory.emit_inst_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.comp_return_def, nested_after_foo_body_state_def]
QED

Definition nested_leaf_entry_stage_def:
  nested_leaf_entry_stage =
    do new_block "leaf";
       params_result <- compile_internal_params nested_leaf_cenv [("z", T)] 0;
       cenv2 <- return (FST params_result);
       next_idx <- return (SND params_result);
       return_pc <- emit_op PARAM [Lit (n2w next_idx)];
       (case FLOOKUP cenv2.ce_vars "__return_pc__" of
          SOME (MemLoc rpc_off _) =>
            emit_void MSTORE [Lit (n2w rpc_off); return_pc]
        | _ => return ());
       return (cenv2, return_pc)
    od
End

Definition nested_leaf_z_operand_def:
  nested_leaf_z_operand = Var "%18"
End

Definition nested_leaf_return_pc_operand_def:
  nested_leaf_return_pc_operand = Var "%19"
End

Definition nested_after_leaf_entry_state_def:
  nested_after_leaf_entry_state =
    nested_after_fallback_state with
      <| cs_next_var := 20;
         cs_next_id := 33;
         cs_current_bb := "leaf";
         cs_current_insts :=
           [mk_inst 29 PARAM [Lit 0w] ["%18"];
            mk_inst 30 MSTORE [Lit 0w; nested_leaf_z_operand] [];
            mk_inst 31 PARAM [Lit 1w] ["%19"];
            mk_inst 32 MSTORE [Lit 32w; nested_leaf_return_pc_operand] []];
         cs_blocks :=
           <| bb_label := nested_after_fallback_state.cs_current_bb;
              bb_instructions := nested_after_fallback_state.cs_current_insts |> ::
           nested_after_fallback_state.cs_blocks |>
End

Theorem nested_leaf_entry_stage_eq:
  nested_leaf_entry_stage nested_after_fallback_state =
    ((nested_leaf_cenv, nested_leaf_return_pc_operand),
     nested_after_leaf_entry_state)
Proof
  simp[nested_leaf_entry_stage_def,
       moduleLoweringTheory.compile_internal_params_def,
       nested_leaf_cenv_entry_facts,
       compileEnvTheory.new_block_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       nested_leaf_z_operand_def, nested_leaf_return_pc_operand_def,
       nested_after_leaf_entry_state_def,
       nested_after_fallback_state_def,
       nested_after_foo_body_state_def]
QED

Definition nested_leaf_return_body_stage_def:
  nested_leaf_return_body_stage =
    compile_stmts nested_leaf_cenv NoLoop (BaseT (UintT 256))
      [Return (SOME (Name (BaseT (UintT 256)) "z"))]
End

Definition nested_leaf_value_operand_def:
  nested_leaf_value_operand = Var "%20"
End

Definition nested_leaf_loaded_return_pc_operand_def:
  nested_leaf_loaded_return_pc_operand = Var "%21"
End

Definition nested_after_leaf_body_state_def:
  nested_after_leaf_body_state =
    nested_after_leaf_entry_state with
      <| cs_next_var := 22;
         cs_next_id := 36;
         cs_current_insts :=
           nested_after_leaf_entry_state.cs_current_insts ++
             [mk_inst 33 MLOAD [Lit 0w] ["%20"];
              mk_inst 34 MLOAD [Lit 32w] ["%21"];
              mk_inst 35 RET
                [nested_leaf_value_operand;
                 nested_leaf_loaded_return_pc_operand] []] |>
End

Theorem nested_after_leaf_entry_state_facts:
  nested_after_leaf_entry_state.cs_next_var = 20 /\
  nested_after_leaf_entry_state.cs_next_id = 33 /\
  nested_after_leaf_entry_state.cs_current_insts =
    [mk_inst 29 PARAM [Lit 0w] ["%18"];
     mk_inst 30 MSTORE [Lit 0w; nested_leaf_z_operand] [];
     mk_inst 31 PARAM [Lit 1w] ["%19"];
     mk_inst 32 MSTORE [Lit 32w; nested_leaf_return_pc_operand] []] /\
  ~block_is_terminated nested_after_leaf_entry_state
Proof
  simp[nested_after_leaf_entry_state_def,
       compileEnvTheory.block_is_terminated_def,
       venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def]
QED

Theorem nested_leaf_return_body_stage_eq:
  nested_leaf_return_body_stage nested_after_leaf_entry_state =
    ((), nested_after_leaf_body_state)
Proof
  simp[nested_leaf_return_body_stage_def,
       nested_after_leaf_entry_state_facts,
       stmtLoweringTheory.compile_stmt_def,
       exprLoweringTheory.lower_value_def,
       Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_name_vv_def,
       exprLoweringTheory.unwrap_value_def,
       nested_leaf_cenv_entry_facts,
       stmtLoweringTheory.compile_internal_return_def,
       vyperASTTheory.expr_type_def,
       compileEnvTheory.is_word_type_def,
       contextTheory.mk_ptr_def, contextTheory.compile_ptr_load_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
       compileEnvTheory.comp_get_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       nested_leaf_value_operand_def,
       nested_leaf_loaded_return_pc_operand_def,
       nested_after_leaf_body_state_def]
  >> rewrite_tac[GSYM listTheory.APPEND_ASSOC]
  >> simp[]
QED

Theorem nested_after_leaf_body_state_terminated:
  block_is_terminated nested_after_leaf_body_state
Proof
  `nested_after_leaf_body_state.cs_current_insts <> []` by
    simp[nested_after_leaf_body_state_def]
  >> `LAST nested_after_leaf_body_state.cs_current_insts =
        mk_inst 35 RET
          [nested_leaf_value_operand;
           nested_leaf_loaded_return_pc_operand] []` by
       simp[nested_after_leaf_body_state_def,
            nested_LAST_APPEND_NONEMPTY_SUFFIX]
  >> Cases_on `nested_after_leaf_body_state.cs_current_insts`
  >- gvs[]
  >> FIRST
       [qpat_assum `nested_after_leaf_body_state.cs_current_insts = _`
          (fn th => rewrite_tac[th]),
        qpat_assum `_ = nested_after_leaf_body_state.cs_current_insts`
          (fn th => rewrite_tac[GSYM th])]
  >> simp[compileEnvTheory.block_is_terminated_def,
          venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def]
QED


Theorem nested_leaf_entry_continuation_eq:
  !k.
    (do new_block "leaf";
        return ();
        return_buf_var <- return (NONE : operand option);
        param_idx_start <- return 0;
        params_result <-
          compile_internal_params nested_leaf_cenv [("z", T)] param_idx_start;
        cenv2 <- return (FST params_result);
        next_idx <- return (SND params_result);
        return_pc <- emit_op PARAM [Lit (n2w next_idx)];
        (case FLOOKUP cenv2.ce_vars "__return_pc__" of
           SOME (MemLoc rpc_off _) =>
             emit_void MSTORE [Lit (n2w rpc_off); return_pc]
         | _ => return ());
        return ();
        k cenv2 return_pc
     od) nested_after_fallback_state =
    k nested_leaf_cenv nested_leaf_return_pc_operand
      nested_after_leaf_entry_state
Proof
  gen_tac
  >> simp[moduleLoweringTheory.compile_internal_params_def,
       nested_leaf_cenv_entry_facts,
       compileEnvTheory.new_block_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       nested_leaf_z_operand_def,
       nested_leaf_return_pc_operand_def,
       nested_after_leaf_entry_state_def,
       nested_after_fallback_state_def,
       nested_after_foo_body_state_def]
QED

Theorem nested_leaf_applied_entry_continuation_eq:
  !k.
    (\(_0, cs').
       (\(params_result, cs').
          (\(return_pc, cs').
             (\(_0, cs').
                k (FST params_result) return_pc cs')
               ((case FLOOKUP (FST params_result).ce_vars "__return_pc__" of
                   NONE => comp_return ()
                 | SOME (MemLoc rpc_off _) =>
                     emit_void MSTORE [Lit (n2w rpc_off); return_pc]
                 | SOME (StorageLoc _) => comp_return ()
                 | SOME (TransientLoc _) => comp_return ()
                 | SOME (ImmutableLoc _) => comp_return ()
                 | SOME (PtrVar _ _) => comp_return ()) cs'))
            (emit_op PARAM [Lit (n2w (SND params_result))] cs'))
         (compile_internal_params nested_leaf_cenv [("z", T)] 0 cs'))
      (new_block "leaf" nested_after_fallback_state) =
    k nested_leaf_cenv nested_leaf_return_pc_operand
      nested_after_leaf_entry_state
Proof
  gen_tac
  >> simp[moduleLoweringTheory.compile_internal_params_def,
       nested_leaf_cenv_entry_facts,
       compileEnvTheory.new_block_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       nested_leaf_z_operand_def,
       nested_leaf_return_pc_operand_def,
       nested_after_leaf_entry_state_def,
       nested_after_fallback_state_def,
       nested_after_foo_body_state_def]
QED

Definition nested_leaf_stage_def:
  nested_leaf_stage =
    do new_block "leaf";
       compile_internal_function nested_leaf_cenv [("z", T)]
         F F 0 F F F 0
         [Return (SOME (Name (BaseT (UintT 256)) "z"))]
         (SOME (BaseT (UintT 256)))
    od
End

Theorem nested_leaf_stage_eq:
  nested_leaf_stage nested_after_fallback_state =
    ((), nested_after_leaf_body_state)
Proof
  pure_rewrite_tac[nested_leaf_stage_def,
                   moduleLoweringTheory.compile_internal_function_def]
  >> simp[nested_leaf_applied_entry_continuation_eq,
          compileEnvTheory.comp_get_def,
          compileEnvTheory.comp_return_def,
          compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def]
  >> rewrite_tac[GSYM nested_leaf_return_body_stage_def,
                 nested_leaf_return_body_stage_eq]
  >> simp[nested_after_leaf_body_state_terminated,
          compileEnvTheory.comp_get_def,
          compileEnvTheory.comp_return_def,
          compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def]
QED

Theorem nested_mid_cenv_entry_facts:
  FLOOKUP nested_mid_cenv.ce_vars "y" = SOME (MemLoc 0 32) /\
  FLOOKUP nested_mid_cenv.ce_vars "__return_pc__" = SOME (MemLoc 32 32) /\
  FLOOKUP nested_mid_cenv.ce_vars "__return_buf__" = NONE /\
  nested_mid_cenv.ce_returns_count = 1 /\
  nested_mid_cenv.ce_func_info "leaf" = (1, 0, [T])
Proof
  simp[nested_mid_cenv_def, update_cenv_nonreentrant_def,
       build_compile_env_def, build_compile_env_ce_func_info,
       nested_internal_call_program_def,
       add_module_var_locations_def, collect_locals_def,
       allocate_args_def, allocate_internal_special_vars_def,
       build_func_info_def, make_struct_fields_map_def,
       compileEnvTheory.get_struct_fields_def,
       compileEnvTheory.compute_func_info_def,
       compileEnvTheory.returns_stack_count_def,
       compileEnvTheory.compute_pass_via_stack_def,
       compileEnvTheory.is_word_type_def,
       compileEnvTheory.MAX_STACK_ARGS_def,
       type_mem_bytes_def]
  >> pairarg_tac
  >> pop_assum (fn th => rewrite_tac[th])
  >> simp[finite_mapTheory.FLOOKUP_UPDATE,
          finite_mapTheory.FLOOKUP_EMPTY]
QED

Definition nested_mid_y_operand_def:
  nested_mid_y_operand = Var "%22"
End

Definition nested_mid_return_pc_operand_def:
  nested_mid_return_pc_operand = Var "%23"
End

Definition nested_after_mid_entry_state_def:
  nested_after_mid_entry_state =
    nested_after_leaf_body_state with
      <| cs_next_var := 24;
         cs_next_id := 40;
         cs_current_bb := "mid";
         cs_current_insts :=
           [mk_inst 36 PARAM [Lit 0w] ["%22"];
            mk_inst 37 MSTORE [Lit 0w; nested_mid_y_operand] [];
            mk_inst 38 PARAM [Lit 1w] ["%23"];
            mk_inst 39 MSTORE [Lit 32w; nested_mid_return_pc_operand] []];
         cs_blocks :=
           <| bb_label := nested_after_leaf_body_state.cs_current_bb;
              bb_instructions := nested_after_leaf_body_state.cs_current_insts |> ::
           nested_after_leaf_body_state.cs_blocks |>
End

Definition nested_mid_entry_stage_def:
  nested_mid_entry_stage =
    do new_block "mid";
       params_result <-
         compile_internal_params nested_mid_cenv [("y", T)] 0;
       cenv2 <- return (FST params_result);
       next_idx <- return (SND params_result);
       return_pc <- emit_op PARAM [Lit (n2w next_idx)];
       (case FLOOKUP cenv2.ce_vars "__return_pc__" of
          SOME (MemLoc rpc_off _) =>
            emit_void MSTORE [Lit (n2w rpc_off); return_pc]
        | _ => return ());
       return (cenv2, return_pc)
    od
End

Theorem nested_mid_entry_stage_eq:
  nested_mid_entry_stage nested_after_leaf_body_state =
    ((nested_mid_cenv, nested_mid_return_pc_operand),
     nested_after_mid_entry_state)
Proof
  simp[nested_mid_entry_stage_def,
       moduleLoweringTheory.compile_internal_params_def,
       nested_mid_cenv_entry_facts,
       compileEnvTheory.new_block_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       nested_mid_y_operand_def, nested_mid_return_pc_operand_def,
       nested_after_mid_entry_state_def,
       nested_after_leaf_body_state_def]
QED

Definition nested_mid_name_stage_def:
  nested_mid_name_stage =
    lower_value compile_expr nested_mid_cenv (BaseT (UintT 256))
      (Name (BaseT (UintT 256)) "y")
End

Definition nested_mid_y_value_operand_def:
  nested_mid_y_value_operand = Var "%24"
End

Definition nested_after_mid_name_state_def:
  nested_after_mid_name_state =
    nested_after_mid_entry_state with
      <| cs_next_var := 25;
         cs_next_id := 41;
         cs_current_insts :=
           nested_after_mid_entry_state.cs_current_insts ++
             [mk_inst 40 MLOAD [Lit 0w] ["%24"]] |>
End

Theorem nested_mid_name_stage_eq:
  nested_mid_name_stage nested_after_mid_entry_state =
    (nested_mid_y_value_operand, nested_after_mid_name_state)
Proof
  simp[nested_mid_name_stage_def, exprLoweringTheory.lower_value_def,
       Once exprLoweringTheory.compile_expr_def,
       exprLoweringTheory.compile_name_vv_def,
       nested_mid_cenv_entry_facts,
       exprLoweringTheory.unwrap_value_def,
       vyperASTTheory.expr_type_def,
       compileEnvTheory.is_word_type_def, contextTheory.mk_ptr_def,
       contextTheory.compile_ptr_load_def, emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def, nested_mid_y_value_operand_def,
       nested_after_mid_entry_state_def, nested_after_mid_name_state_def]
QED

Theorem nested_mid_singleton_args_stage_eq:
  compile_multi_exprs
    (\cenv ty e st. compile_expr cenv ty e st)
    nested_mid_cenv
    [Name (BaseT (UintT 256)) "y"]
    nested_after_mid_entry_state =
  ([nested_mid_y_value_operand], nested_after_mid_name_state)
Proof
  simp[SF ETA_ss, exprLoweringTheory.compile_multi_exprs_def,
       vyperASTTheory.expr_type_def,
       GSYM nested_mid_name_stage_def, nested_mid_name_stage_eq,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def]
QED

Definition nested_mid_leaf_call_stage_def:
  nested_mid_leaf_call_stage =
    lower_value compile_expr nested_mid_cenv (BaseT (UintT 256))
      (Call (BaseT (UintT 256)) (IntCall (NONE, "leaf"))
        [Name (BaseT (UintT 256)) "y"] NONE)
End

Definition nested_mid_leaf_call_operand_def:
  nested_mid_leaf_call_operand = Var "%27"
End

Definition nested_after_mid_alloc_state_def:
  nested_after_mid_alloc_state =
    nested_after_mid_name_state with
      <| cs_next_var := 26;
         cs_next_id := 42;
         cs_current_insts :=
           nested_after_mid_name_state.cs_current_insts ++
             [mk_inst 41 ALLOCA [Lit 32w] ["%25"]] |>
End

Theorem nested_after_mid_alloc_state_next_var:
  nested_after_mid_alloc_state.cs_next_var = 26
Proof
  simp[nested_after_mid_alloc_state_def]
QED

Theorem nested_mid_fresh_vars_one_eq:
  fresh_vars 1 nested_after_mid_alloc_state =
    (["%26"], nested_after_mid_alloc_state with cs_next_var := 27)
Proof
  simp[fresh_vars_one, nested_after_mid_alloc_state_next_var]
QED

Definition nested_after_mid_invoke_state_def:
  nested_after_mid_invoke_state =
    (nested_after_mid_alloc_state with cs_next_var := 27) with
      <| cs_next_id := 43;
         cs_current_insts :=
           nested_after_mid_alloc_state.cs_current_insts ++
             [mk_inst 42 INVOKE
                [Label "leaf"; nested_mid_y_value_operand] ["%26"]] |>
End

Theorem nested_mid_emit_leaf_one_eq:
  emit_multi_op INVOKE [Label "leaf"; nested_mid_y_value_operand] 1
    nested_after_mid_alloc_state =
  ([Var "%26"], nested_after_mid_invoke_state)
Proof
  simp[emitHelperTheory.emit_multi_op_def,
       nested_mid_fresh_vars_one_eq,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.comp_bind_def, compileEnvTheory.comp_return_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       nested_after_mid_invoke_state_def]
  >> simp[nested_after_mid_alloc_state_def]
QED

Definition nested_after_mid_leaf_call_state_def:
  nested_after_mid_leaf_call_state =
    nested_after_mid_name_state with
      <| cs_next_var := 28;
         cs_next_id := 45;
         cs_current_insts :=
           nested_after_mid_name_state.cs_current_insts ++
             [mk_inst 41 ALLOCA [Lit 32w] ["%25"];
              mk_inst 42 INVOKE
                [Label "leaf"; nested_mid_y_value_operand] ["%26"];
              mk_inst 43 MSTORE [Var "%25"; Var "%26"] [];
              mk_inst 44 MLOAD [Var "%25"] ["%27"]] |>
End

Theorem nested_mid_leaf_call_stage_eq:
  nested_mid_leaf_call_stage nested_after_mid_entry_state =
    (nested_mid_leaf_call_operand, nested_after_mid_leaf_call_state)
Proof
  `nested_after_mid_name_state.cs_next_var = 25 /\
   nested_after_mid_name_state.cs_next_id = 41` by
    simp[nested_after_mid_name_state_def]
  >> simp[nested_mid_leaf_call_stage_def,
       exprLoweringTheory.lower_value_def,
       Once exprLoweringTheory.compile_expr_def,
       Once exprLoweringTheory.compile_call_def,
       compileEnvTheory.nsid_to_string_def,
       vyperASTTheory.expr_type_def,
       nested_mid_cenv_entry_facts,
       nested_mid_singleton_args_stage_eq,
       exprLoweringTheory.compile_stage_intcall_args_def,
       contextTheory.compile_alloc_buffer_def,
       emitHelperTheory.emit_op_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       GSYM nested_after_mid_alloc_state_def]
  >> rewrite_tac[nested_mid_emit_leaf_one_eq]
  >> simp[exprLoweringTheory.store_multi_results_def,
          contextTheory.base_ptr_def, exprLoweringTheory.unwrap_value_def,
          contextTheory.compile_ptr_load_def,
          compileEnvTheory.is_word_type_def,
          emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
          compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def,
          compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
          compileEnvTheory.emit_def,
          nested_mid_leaf_call_operand_def,
          nested_after_mid_leaf_call_state_def,
          nested_after_mid_invoke_state_def,
          nested_after_mid_alloc_state_def]
  >> `nested_after_mid_name_state.cs_current_insts ++
        [mk_inst 41 ALLOCA [Lit 32w] ["%25"]] ++
        [mk_inst 42 INVOKE
           [Label "leaf"; nested_mid_y_value_operand] ["%26"]] ++
        [mk_inst 43 MSTORE [Var "%25"; Var "%26"] []] ++
        [mk_inst 44 MLOAD [Var "%25"] ["%27"]] =
      nested_after_mid_name_state.cs_current_insts ++
        [mk_inst 41 ALLOCA [Lit 32w] ["%25"];
         mk_inst 42 INVOKE
           [Label "leaf"; nested_mid_y_value_operand] ["%26"];
         mk_inst 43 MSTORE [Var "%25"; Var "%26"] [];
         mk_inst 44 MLOAD [Var "%25"] ["%27"]]` by
       (rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[])
  >> simp[]
QED

Definition nested_mid_return_stage_def:
  nested_mid_return_stage =
    do rpc <- emit_op MLOAD [Lit 32w];
       compile_internal_return nested_mid_cenv
         (SOME nested_mid_leaf_call_operand) rpc
         nested_mid_cenv.ce_returns_count
         (BaseT (UintT 256)) (BaseT (UintT 256)) [] NONE
    od
End

Definition nested_mid_loaded_return_pc_operand_def:
  nested_mid_loaded_return_pc_operand = Var "%28"
End

Definition nested_after_mid_body_state_def:
  nested_after_mid_body_state =
    nested_after_mid_leaf_call_state with
      <| cs_next_var := 29;
         cs_next_id := 47;
         cs_current_insts :=
           nested_after_mid_leaf_call_state.cs_current_insts ++
             [mk_inst 45 MLOAD [Lit 32w] ["%28"]] ++
             [mk_inst 46 RET
                [nested_mid_leaf_call_operand;
                 nested_mid_loaded_return_pc_operand] []] |>
End

Theorem nested_mid_return_stage_eq:
  nested_mid_return_stage nested_after_mid_leaf_call_state =
    ((), nested_after_mid_body_state)
Proof
  simp[nested_mid_return_stage_def,
       nested_mid_cenv_entry_facts,
       stmtLoweringTheory.compile_internal_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       nested_mid_leaf_call_operand_def,
       nested_mid_loaded_return_pc_operand_def,
       nested_after_mid_body_state_def,
       nested_after_mid_leaf_call_state_def]
  >> simp[listTheory.APPEND_ASSOC]
QED


Theorem nested_mid_applied_return_stage_eq:
  (\(_0, cs'). ((), cs'))
    ((\(rpc, cs').
        compile_internal_return nested_mid_cenv
          (SOME nested_mid_leaf_call_operand) rpc 1
          (BaseT (UintT 256)) (BaseT (UintT 256)) [] NONE cs')
      (emit_op MLOAD [Lit 32w] nested_after_mid_leaf_call_state)) =
    ((), nested_after_mid_body_state)
Proof
  simp[nested_mid_cenv_entry_facts,
       stmtLoweringTheory.compile_internal_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_inst_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       nested_mid_leaf_call_operand_def,
       nested_mid_loaded_return_pc_operand_def,
       nested_after_mid_body_state_def,
       nested_after_mid_leaf_call_state_def,
       listTheory.APPEND_ASSOC]
QED
Theorem nested_after_mid_body_state_terminated:
  block_is_terminated nested_after_mid_body_state
Proof
  `nested_after_mid_body_state.cs_current_insts <> []` by
    simp[nested_after_mid_body_state_def]
  >> `LAST nested_after_mid_body_state.cs_current_insts =
        mk_inst 46 RET
          [nested_mid_leaf_call_operand;
           nested_mid_loaded_return_pc_operand] []` by
       simp[nested_after_mid_body_state_def,
            nested_LAST_APPEND_NONEMPTY_SUFFIX]
  >> Cases_on `nested_after_mid_body_state.cs_current_insts`
  >- gvs[]
  >> FIRST
       [qpat_assum `nested_after_mid_body_state.cs_current_insts = _`
          (fn th => rewrite_tac[th]),
        qpat_assum `_ = nested_after_mid_body_state.cs_current_insts`
          (fn th => rewrite_tac[GSYM th])]
  >> simp[compileEnvTheory.block_is_terminated_def,
          venomInstTheory.mk_inst_def,
          venomInstTheory.is_terminator_def]
QED

Theorem nested_mid_applied_entry_continuation_eq:
  !k.
    (\(_0, cs').
       (\(params_result, cs').
          (\(return_pc, cs').
             (\(_0, cs').
                k (FST params_result) return_pc cs')
               ((case FLOOKUP (FST params_result).ce_vars "__return_pc__" of
                   NONE => comp_return ()
                 | SOME (MemLoc rpc_off _) =>
                     emit_void MSTORE [Lit (n2w rpc_off); return_pc]
                 | SOME (StorageLoc _) => comp_return ()
                 | SOME (TransientLoc _) => comp_return ()
                 | SOME (ImmutableLoc _) => comp_return ()
                 | SOME (PtrVar _ _) => comp_return ()) cs'))
            (emit_op PARAM [Lit (n2w (SND params_result))] cs'))
         (compile_internal_params nested_mid_cenv [("y", T)] 0 cs'))
      (new_block "mid" nested_after_leaf_body_state) =
    k nested_mid_cenv nested_mid_return_pc_operand
      nested_after_mid_entry_state
Proof
  gen_tac
  >> simp[moduleLoweringTheory.compile_internal_params_def,
       nested_mid_cenv_entry_facts,
       compileEnvTheory.new_block_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       emitHelperTheory.emit_inst_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def,
       nested_mid_y_operand_def, nested_mid_return_pc_operand_def,
       nested_after_mid_entry_state_def,
       nested_after_leaf_body_state_def]
QED


Theorem nested_after_mid_entry_state_not_terminated:
  ~block_is_terminated nested_after_mid_entry_state
Proof
  simp[nested_after_mid_entry_state_def,
       compileEnvTheory.block_is_terminated_def,
       venomInstTheory.mk_inst_def,
       venomInstTheory.is_terminator_def]
QED
Definition nested_mid_body_stage_def:
  nested_mid_body_stage =
    compile_stmts nested_mid_cenv NoLoop (BaseT (UintT 256))
      [Return (SOME
        (Call (BaseT (UintT 256)) (IntCall (NONE, "leaf"))
          [Name (BaseT (UintT 256)) "y"] NONE))]
End

Theorem nested_mid_body_stage_eq:
  nested_mid_body_stage nested_after_mid_entry_state =
    ((), nested_after_mid_body_state)
Proof
  simp[nested_mid_body_stage_def,
       nested_after_mid_entry_state_not_terminated,
       nested_mid_cenv_entry_facts,
       stmtLoweringTheory.compile_stmt_def,
       vyperASTTheory.expr_type_def,
       compileEnvTheory.is_word_type_def,
       GSYM nested_mid_leaf_call_stage_def,
       nested_mid_leaf_call_stage_eq,
       compileEnvTheory.comp_get_def,
       compileEnvTheory.comp_return_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def]
  >> MATCH_ACCEPT_TAC nested_mid_applied_return_stage_eq
QED

Definition nested_mid_stage_def:
  nested_mid_stage =
    do new_block "mid";
       compile_internal_function nested_mid_cenv [("y", T)]
         F F 0 F F F 0
         [Return (SOME
           (Call (BaseT (UintT 256)) (IntCall (NONE, "leaf"))
             [Name (BaseT (UintT 256)) "y"] NONE))]
         (SOME (BaseT (UintT 256)))
    od
End

Theorem nested_mid_stage_eq:
  nested_mid_stage nested_after_leaf_body_state =
    ((), nested_after_mid_body_state)
Proof
  pure_rewrite_tac[nested_mid_stage_def,
                   moduleLoweringTheory.compile_internal_function_def]
  >> simp[nested_mid_applied_entry_continuation_eq,
          compileEnvTheory.comp_get_def,
          compileEnvTheory.comp_return_def,
          compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def]
  >> rewrite_tac[GSYM nested_mid_body_stage_def,
                 nested_mid_body_stage_eq]
  >> simp[nested_after_mid_body_state_terminated,
          compileEnvTheory.comp_get_def,
          compileEnvTheory.comp_return_def,
          compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def]
QED

Theorem nested_internal_fn_bodies_eq:
  compile_internal_fn_bodies [nested_leaf_package; nested_mid_package]
    nested_after_fallback_state =
  ((), nested_after_mid_body_state)
Proof
  `compile_internal_fn_bodies [nested_leaf_package; nested_mid_package] =
    (do nested_leaf_stage;
        nested_mid_stage;
        return ()
     od)` by
    simp[moduleLoweringTheory.compile_internal_fn_bodies_def,
         nested_leaf_package_def, nested_mid_package_def,
         nested_leaf_stage_def, nested_mid_stage_def,
         comp_ignore_bind_assoc]
  >> pop_assum (fn th => rewrite_tac[th])
  >> simp[nested_leaf_stage_eq, nested_mid_stage_eq,
          compileEnvTheory.comp_return_def,
          compileEnvTheory.comp_bind_def,
          compileEnvTheory.comp_ignore_bind_def]
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
  rewrite_tac[GSYM vyperCompilerTheory.wf_invoke_targets_check_eq] >> EVAL_TAC
QED
