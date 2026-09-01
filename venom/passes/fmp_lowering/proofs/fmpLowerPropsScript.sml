(*
 * Executable acceptance probes for checked FMP lowering.
 *)

Theory fmpLowerProps
Ancestors
  fmpLowerDefs

Definition fmp_test_supply_def:
  fmp_test_supply = <|
    irs_next_inst := 100;
    irs_next_var := 0;
    irs_next_label := 0;
    irs_used_inst_ids := [];
    irs_used_vars := [];
    irs_used_labels := []
  |>
End

Definition fmp_test_ctx_def:
  fmp_test_ctx = mk_venom_context [] NONE
End

Theorem fmp_lower_dalloca_eval:
  ?s.
    fmp_lower_inst FEMPTY fmp_test_ctx "runner" fmp_test_supply
      (mk_inst 7 DALLOCA [Var "size"] ["ptr"]) =
      SOME
        ([mk_inst 100 ADD [Var "size"; Lit 31w] ["formal_var_0"];
          mk_inst 101 AND
            [Var "formal_var_0";
             Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
            ["formal_var_1"];
          mk_inst 102 BUMP
            [Var "runner"; Var "formal_var_1"] ["ptr";"runner"]],s) /\
    s.irs_next_inst = 103 /\ s.irs_next_var = 2
Proof
  EVAL_TAC >> simp[]
QED

Theorem fmp_lower_getfmp_eval:
  fmp_lower_inst FEMPTY fmp_test_ctx "runner" fmp_test_supply
    (mk_inst 8 GETFMP [] ["out"]) =
  SOME ([mk_inst 8 ASSIGN [Var "runner"] ["out"]],fmp_test_supply)
Proof
  EVAL_TAC
QED

Theorem fmp_lower_setfmp_eval:
  fmp_lower_inst FEMPTY fmp_test_ctx "runner" fmp_test_supply
    (mk_inst 9 SETFMP [Var "adopted"] []) =
  SOME ([mk_inst 9 ASSIGN [Var "adopted"] ["runner"]],fmp_test_supply)
Proof
  EVAL_TAC
QED

Theorem fmp_lower_retfmp_eval:
  fmp_lower_inst FEMPTY fmp_test_ctx "runner" fmp_test_supply
    (mk_inst 10 RETFMP [Var "value"; Var "pc"] []) =
  SOME
    ([mk_inst 10 RET [Var "value"; Var "runner"; Var "pc"] []],
     fmp_test_supply)
Proof
  EVAL_TAC
QED

Theorem fmp_lower_dret_rejected_eval:
  fmp_lower_inst FEMPTY fmp_test_ctx "runner" fmp_test_supply
    (mk_inst 11 DRET [Lit 0w; Var "pc"] []) = NONE
Proof
  EVAL_TAC
QED

Definition fmp_entry_probe_fn_def:
  fmp_entry_probe_fn =
    mk_raw_function "entry"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 1 PARAM [Lit 0w] ["arg"];
             mk_inst 2 RETPC_PARAM [Lit 1w] ["pc"];
             mk_inst 3 RETFMP [Var "pc"] []] |>]
End

Definition fmp_need_info_def:
  fmp_need_info = <| fi_needs_fmp := T; fi_publishes_fmp := T |>
End

Theorem fmp_entry_initial_root_eval:
  fmp_make_root_layout
    (mk_venom_context [fmp_entry_probe_fn] (SOME "entry"))
    fmp_entry_probe_fn fmp_need_info "runner" fmp_test_supply =
  SOME (FmpRootLayout 1
    (SOME (mk_inst 100 INITIAL_FMP [] ["runner"]))
    (SOME (mk_inst 2 RETPC_PARAM [Lit 1w] ["pc"]))
    (fmp_test_supply with <|
       irs_next_inst := 101;
       irs_used_inst_ids := [100] |>))
Proof
  EVAL_TAC
QED

Theorem fmp_callee_hidden_root_layout_eval:
  fmp_make_root_layout
    (mk_venom_context [fmp_entry_probe_fn] NONE)
    fmp_entry_probe_fn fmp_need_info "runner" fmp_test_supply =
  SOME (FmpRootLayout 1
    (SOME (mk_inst 100 FMP_PARAM [Lit 1w] ["runner"]))
    (SOME (mk_inst 2 RETPC_PARAM [Lit 2w] ["pc"]))
    (fmp_test_supply with <|
       irs_next_inst := 101;
       irs_used_inst_ids := [100] |>)) /\
  fmp_install_root
    (mk_venom_context [fmp_entry_probe_fn] NONE)
    fmp_entry_probe_fn
    (FmpRootLayout 1
      (SOME (mk_inst 100 FMP_PARAM [Lit 1w] ["runner"]))
      (SOME (mk_inst 2 RETPC_PARAM [Lit 2w] ["pc"]))
      fmp_test_supply)
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 1 PARAM [Lit 0w] ["arg"];
           mk_inst 2 RETPC_PARAM [Lit 1w] ["pc"];
           mk_inst 3 RET [Var "runner"; Var "pc"] []] |>] =
  SOME
    ([<| bb_label := "entry";
         bb_instructions :=
           [mk_inst 1 PARAM [Lit 0w] ["arg"];
            mk_inst 100 FMP_PARAM [Lit 1w] ["runner"];
            mk_inst 2 RETPC_PARAM [Lit 2w] ["pc"];
            mk_inst 3 RET [Var "runner"; Var "pc"] []] |>],
     fmp_test_supply)
Proof
  EVAL_TAC
QED

Theorem fmp_reclaim_restore_eval:
  fmp_emit_restores "runner" fmp_test_supply ["newer";"older"] =
    ([mk_inst 100 ASSIGN [Var "newer"] ["runner"];
      mk_inst 101 ASSIGN [Var "older"] ["runner"]],
     fmp_test_supply with <|
       irs_next_inst := 102;
       irs_used_inst_ids := [101;100] |>)
Proof
  EVAL_TAC
QED

Theorem fmp_seal_bits_and_metadata_eval:
  let sealed = fmp_seal
    (mk_venom_context [fmp_entry_probe_fn] NONE)
    fmp_entry_probe_fn fmp_need_info fmp_entry_probe_fn.fn_blocks in
    sealed.fn_fmp_signature = SOME <|
      fms_has_fmp_param := T; fms_publishes := T |> /\
    sealed.fn_name = fmp_entry_probe_fn.fn_name /\
    sealed.fn_call_abi = fmp_entry_probe_fn.fn_call_abi /\
    sealed.fn_noinline = fmp_entry_probe_fn.fn_noinline /\
    sealed.fn_forced_alloc_positions =
      fmp_entry_probe_fn.fn_forced_alloc_positions /\
    sealed.fn_eom = fmp_entry_probe_fn.fn_eom
Proof
  EVAL_TAC
QED

val _ = export_theory();
