(*
 * Executable acceptance probes for checked FMP lowering.
 *)

Theory fmpLowerProps
Ancestors
  fmpLowerDefs fmpAnalysisProps fmpWfProps

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

Theorem fmp_publishing_invoke_and_runner_eval:
  fmp_lower_insts
    (FEMPTY |+ ("callee",fmp_probe_info_tt))
    fmp_probe_sealed_ctx "runner" fmp_test_supply
    [mk_inst 2 INVOKE [Label "callee"; Lit 7w] ["user_out"];
     mk_inst 3 GETFMP [] ["seen"]] =
  SOME
    ([mk_inst 2 INVOKE
        [Label "callee"; Lit 7w; Var "runner"]
        ["user_out"; "runner"];
      mk_inst 3 ASSIGN [Var "runner"] ["seen"]],
     fmp_test_supply)
Proof
  EVAL_TAC
QED

Theorem fmp_valid_sealed_identity_eval:
  fmp_lower_function fmp_probe_sealed_ctx fmp_test_supply
    fmp_positive_callee =
  SOME (fmp_positive_callee,fmp_test_supply)
Proof
  strip_assume_tac fmp_sealed_and_caller_propagation_eval
  >> asm_rewrite_tac[fmp_lower_function_def]
  >> simp[fmp_lower_function_with_info_def, fmp_positive_callee_def,
          fmp_probe_sealed_callee_matches,
          fmp_positive_callee_basics_wf]
QED

Definition fmp_changed_ctx_def:
  fmp_changed_ctx = fmp_probe_bad_sealed_ctx
End

Theorem fmp_public_context_freshness_eval:
  fmp_lower_function fmp_changed_ctx fmp_test_supply
    fmp_positive_callee = NONE
Proof
  simp[fmp_lower_function_def, fmp_changed_ctx_def,
       fmp_sealed_mutation_rejected_eval]
QED

Definition fmp_sealed_raw_fn_def:
  fmp_sealed_raw_fn =
    fmp_positive_callee with fn_blocks :=
      [<| bb_label := "entry";
          bb_instructions := [mk_inst 30 GETFMP [] ["raw"]] |>]
End

Theorem fmp_sealed_raw_rejected_eval:
  fmp_lower_function_with_info FEMPTY fmp_test_ctx fmp_test_supply
    fmp_sealed_raw_fn = NONE
Proof
  EVAL_TAC
QED


Theorem fmp_lower_inst_no_raw:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  Cases_on `inst.inst_opcode` >>
  simp[fmp_lower_inst_def, fmp_lower_inst_shape_def,
       venomInstTheory.is_raw_fmp_opcode_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[AllCaseEqs(), venomInstTheory.mk_inst_def,
      venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_lower_insts_no_raw:
  fmp_lower_insts infos ctx runner s insts = SOME (out,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`s`] >> Induct_on `insts`
  >- simp[fmp_lower_insts_def]
  >> simp[fmp_lower_insts_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[listTheory.EVERY_APPEND] >>
  metis_tac[fmp_lower_inst_no_raw]
QED

Theorem fmp_emit_restores_no_raw:
  fmp_emit_restores runner s bases = (out,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  map_every qid_spec_tac [`s'`,`out`,`s`] >> Induct_on `bases`
  >- simp[fmp_emit_restores_def]
  >> simp[fmp_emit_restores_def, AllCaseEqs(),
          venomInstTheory.mk_inst_def,
          venomInstTheory.is_raw_fmp_opcode_def] >>
  rpt strip_tac >>
  gvs[venomInstTheory.is_raw_fmp_opcode_def] >>
  metis_tac[]
QED

Theorem fmp_lower_blocks_no_raw:
  fmp_lower_blocks infos ctx runner s restores bbs =
    SOME (FmpBlocksResult out leftover s') ==>
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) out
Proof
  map_every qid_spec_tac [`s'`,`leftover`,`out`,`restores`,`s`] >>
  Induct_on `bbs`
  >- simp[fmp_lower_blocks_def]
  >> rpt gen_tac >>
  Cases_on `fmp_select_point_restores
    <| fp_block := h.bb_label; fp_index := LENGTH h.bb_instructions |>
    restores` >>
  simp[fmp_lower_blocks_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[listTheory.EVERY_APPEND] >>
  metis_tac[fmp_lower_insts_no_raw, fmp_emit_restores_no_raw]
QED

Theorem fmp_install_root_no_raw:
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) blocks /\
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST root) /\
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST retpc) /\
  fmp_install_root ctx fn (FmpRootLayout n root retpc s) blocks =
    SOME (out,s') ==>
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) out
Proof
  Cases_on `blocks` >>
  simp[fmp_install_root_def, listTheory.EVERY_APPEND] >>
  rpt strip_tac >>
  gvs[listTheory.EVERY_APPEND] >>
  Cases_on `fn_is_context_entry ctx fn` >>
  simp[listTheory.EVERY_APPEND] >>
  metis_tac[rich_listTheory.EVERY_TAKE, rich_listTheory.EVERY_DROP]
QED

Theorem fmp_seal_signature:
  (fmp_seal ctx fn info blocks).fn_fmp_signature =
    SOME <| fms_has_fmp_param := (info.fi_needs_fmp /\
                                   ~fn_is_context_entry ctx fn);
            fms_publishes := info.fi_publishes_fmp |>
Proof
  simp[fmp_seal_def]
QED

Theorem fmp_seal_preserves_nonfmp_metadata:
  fn_identity_metadata_eq (fmp_seal ctx fn info blocks) fn /\
  fn_static_input_eq (fmp_seal ctx fn info blocks) fn /\
  fn_static_layout_eq (fmp_seal ctx fn info blocks) fn
Proof
  simp[fmp_seal_def,
       venomInstTheory.fn_identity_metadata_eq_def,
       venomInstTheory.fn_static_input_eq_def,
       venomInstTheory.fn_static_layout_eq_def]
QED

val _ = export_theory();
