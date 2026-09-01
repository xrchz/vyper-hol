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

Theorem fmp_malformed_raw_rejected_eval:
  fmp_lower_inst FEMPTY fmp_test_ctx "runner" fmp_test_supply
    (mk_inst 12 GETFMP [Lit 0w] ["out"]) = NONE
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

Theorem fmp_generated_supply_threading_eval:
  (case fresh_ir_var fmp_test_supply of
     (runner,s1) =>
       case fmp_make_root_layout
         (mk_venom_context [fmp_entry_probe_fn] (SOME "entry"))
         fmp_entry_probe_fn fmp_need_info runner s1 of
         NONE => NONE
       | SOME (FmpRootLayout n root retpc s2) =>
           case fmp_lower_inst FEMPTY fmp_test_ctx runner s2
             (mk_inst 7 DALLOCA [Var "size"] ["ptr"]) of
             NONE => NONE
           | SOME (insts,s3) =>
               SOME (runner,root,insts,s3.irs_next_inst,s3.irs_next_var,
                     s3.irs_used_inst_ids,s3.irs_used_vars)) =
  SOME
    ("formal_var_0",
     SOME (mk_inst 100 INITIAL_FMP [] ["formal_var_0"]),
     [mk_inst 101 ADD [Var "size"; Lit 31w] ["formal_var_1"];
      mk_inst 102 AND
        [Var "formal_var_1";
         Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
        ["formal_var_2"];
      mk_inst 103 BUMP
        [Var "formal_var_0"; Var "formal_var_2"] ["ptr";"formal_var_0"]],
     104,3,[103;102;101;100],
     ["formal_var_2";"formal_var_1";"formal_var_0"])
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
  >> `lookup_function fmp_positive_callee.fn_name
        fmp_probe_sealed_ctx.ctx_functions = SOME fmp_positive_callee` by
       EVAL_TAC
  >> `fmp_info_valid fmp_probe_sealed_ctx infos` by
       metis_tac[analyze_fmp_context_valid]
  >> simp[fmp_lower_function_with_info_def, fmp_positive_callee_def,
          fmp_probe_sealed_callee_matches,
          fmp_positive_callee_basics_wf]
QED
Theorem fmp_stale_info_sealed_rejected_eval:
  fmp_lower_function_with_info FEMPTY fmp_probe_sealed_ctx fmp_test_supply
    fmp_positive_callee = NONE
Proof
  `MEM fmp_positive_callee fmp_probe_sealed_ctx.ctx_functions` by EVAL_TAC
  >> `~fmp_info_valid fmp_probe_sealed_ctx FEMPTY` by
       (simp[fmpAnalysisDefsTheory.fmp_info_valid_def] >> metis_tac[])
  >> Cases_on `fmp_positive_callee.fn_fmp_signature`
  >> simp[fmp_lower_function_with_info_def]
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
  fmp_lower_function
    (mk_venom_context [fmp_sealed_raw_fn] NONE)
    fmp_test_supply fmp_sealed_raw_fn = NONE
Proof
  EVAL_TAC
QED


Definition fmp_e2e_entry_fn_def:
  fmp_e2e_entry_fn =
    mk_raw_function "e2e_entry"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 0 DALLOCA [Lit 32w] ["p"];
             mk_inst 1 MLOAD [Var "p"] ["x"];
             mk_inst 2 STOP [] []] |>;
       <| bb_label := "ret";
          bb_instructions := [mk_inst 3 RETFMP [Lit 99w] []] |>]
End

Definition fmp_e2e_entry_ctx_def:
  fmp_e2e_entry_ctx =
    mk_venom_context [fmp_e2e_entry_fn] (SOME "e2e_entry")
End

Theorem fmp_e2e_entry_analysis_eval:
  analyze_fmp_context fmp_e2e_entry_ctx =
    SOME (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
Proof
  EVAL_TAC
QED

Theorem fmp_e2e_entry_info_valid:
  fmp_info_valid fmp_e2e_entry_ctx
    (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
Proof
  irule analyze_fmp_context_valid
  >> ACCEPT_TAC fmp_e2e_entry_analysis_eval
QED

Theorem fmp_e2e_lt3_cases[local]:
  !(k:num). k < 3 <=> k = 0 \/ k = 1 \/ k = 2
Proof
  Induct >> simp[]
QED

Theorem fmp_e2e_entry_wf:
  wf_function fmp_e2e_entry_fn /\ fn_inst_wf fmp_e2e_entry_fn
Proof
  EVAL_TAC >> rw[]
  >> gvs[fmp_e2e_lt3_cases, listTheory.REV_DEF,
         venomInstTheory.is_terminator_def, venomStateTheory.get_label_def,
         venomWfTheory.inst_wf_def]
QED

Definition fmp_e2e_entry_states_def:
  fmp_e2e_entry_states = THE (fmp_reclaim_states fmp_e2e_entry_fn)
End

Theorem fmp_e2e_entry_captures:
  FLAT (MAP fmp_getfmp_outputs (fn_insts fmp_e2e_entry_fn)) = []
Proof
  EVAL_TAC
QED

Theorem fmp_e2e_entry_states_eq:
  fmp_reclaim_states fmp_e2e_entry_fn = SOME fmp_e2e_entry_states
Proof
  EVAL_TAC
QED

Theorem fmp_e2e_entry_state_at_exit:
  df_at NONE fmp_e2e_entry_states "entry" 3 =
    SOME <| frs_stack := ["p"]; frs_captures := [];
            frs_can_reclaim := T |>
Proof
  EVAL_TAC
  >> simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_e2e_entry_target_ok:
  fmp_restore_target_ok
    (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
    fmp_e2e_entry_ctx fmp_e2e_entry_fn
    (liveness_analyze fmp_e2e_entry_fn) [] ("entry",3) "p"
Proof
  simp[fmpReclaimDefsTheory.fmp_restore_target_ok_def, fmp_e2e_entry_info_valid]
  >> EVAL_TAC
  >> simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_e2e_entry_plan_ok:
  fmp_reclaim_plan_ok
    (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
    fmp_e2e_entry_ctx fmp_e2e_entry_fn
    (FEMPTY |+ (("entry",3),"p"))
Proof
  simp[fmpReclaimDefsTheory.fmp_reclaim_plan_ok_def, fmpReclaimDefsTheory.fmp_reclaim_entry_ok_def,
       finite_mapTheory.FLOOKUP_UPDATE, fmp_e2e_entry_captures,
       fmp_e2e_entry_target_ok]
QED

Theorem fmp_e2e_entry_block_candidate:
  fmp_block_restore
    (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
    fmp_e2e_entry_ctx fmp_e2e_entry_fn
    (liveness_analyze fmp_e2e_entry_fn) (cfg_analyze fmp_e2e_entry_fn)
    fmp_e2e_entry_states
    <| bb_label := "entry";
       bb_instructions :=
         [mk_inst 0 DALLOCA [Lit 32w] ["p"];
          mk_inst 1 MLOAD [Var "p"] ["x"];
          mk_inst 2 STOP [] []] |> = SOME (("entry",3),"p")
Proof
  simp[fmpReclaimDefsTheory.fmp_block_restore_def, fmp_e2e_entry_state_at_exit,
       fmpReclaimDefsTheory.fmp_stack_reclaimable_def, fmp_e2e_entry_target_ok,
       fmpReclaimDefsTheory.fmp_oldest_def]
  >> EVAL_TAC
QED

Theorem fmp_e2e_ret_block_candidate:
  fmp_block_restore
    (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
    fmp_e2e_entry_ctx fmp_e2e_entry_fn
    (liveness_analyze fmp_e2e_entry_fn) (cfg_analyze fmp_e2e_entry_fn)
    fmp_e2e_entry_states
    <| bb_label := "ret";
       bb_instructions := [mk_inst 3 RETFMP [Lit 99w] []] |> = NONE
Proof
  simp[fmpReclaimDefsTheory.fmp_block_restore_def]
  >> EVAL_TAC
  >> simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_e2e_entry_blocks:
  fmp_e2e_entry_fn.fn_blocks =
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 MLOAD [Var "p"] ["x"];
           mk_inst 2 STOP [] []] |>;
     <| bb_label := "ret";
        bb_instructions := [mk_inst 3 RETFMP [Lit 99w] []] |>]
Proof
  EVAL_TAC
QED

Theorem fmp_e2e_entry_candidate:
  fmp_candidate_plan
    (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
    fmp_e2e_entry_ctx fmp_e2e_entry_fn fmp_e2e_entry_states =
    FEMPTY |+ (("entry",3),"p")
Proof
  simp[fmpReclaimDefsTheory.fmp_candidate_plan_def, fmp_e2e_entry_blocks,
       fmpReclaimDefsTheory.fmp_collect_candidates_def,
       fmp_e2e_entry_block_candidate, fmp_e2e_ret_block_candidate,
       fmpReclaimDefsTheory.fmp_plan_of_list_def]
  >> EVAL_TAC
QED

Theorem fmp_e2e_entry_reclaim_eval:
  analyze_fmp_reclaims
    (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
    fmp_e2e_entry_ctx fmp_e2e_entry_fn =
    SOME (FEMPTY |+ (("entry",3),"p"))
Proof
  irule fmpReclaimPropsTheory.analyze_fmp_reclaims_ready
  >> simp[fmp_e2e_entry_info_valid, fmp_e2e_entry_wf,
          fmp_e2e_entry_states_eq, fmp_e2e_entry_candidate,
          fmp_e2e_entry_plan_ok]
  >> EVAL_TAC
QED

Theorem fmp_e2e_entry_lower_input:
  fmp_lower_input
    (FEMPTY |+ ("e2e_entry",fmp_probe_info_tt))
    fmp_e2e_entry_ctx fmp_e2e_entry_fn
Proof
  EVAL_TAC
QED

Theorem fmp_e2e_entry_reclaim_input:
  fmp_reclaim_input fmp_e2e_entry_fn
    (FEMPTY |+ (("entry",3),"p"))
Proof
  simp[fmp_reclaim_input_def, finite_mapTheory.FLOOKUP_UPDATE]
  >> rpt strip_tac >> gvs[]
  >> EVAL_TAC
  >> qexists `<| bb_label := "entry";
                  bb_instructions :=
                    [mk_inst 0 DALLOCA [Lit 32w] ["p"];
                     mk_inst 1 MLOAD [Var "p"] ["x"];
                     mk_inst 2 STOP [] []] |>`
  >> EVAL_TAC
QED

Theorem fmp_e2e_entry_plan_alist:
  fmap_to_alist
    ((FEMPTY : (fmp_point,string) fmap) |+ (("entry",3),"p")) =
    [("entry",3),"p"]
Proof
  simp[alistTheory.fmap_to_alist_def]
QED

Theorem fmp_e2e_entry_select_restores:
  fmp_select_point_restores ("entry",3)
    (MAP (\k. (k,if k = ("entry",3) then "p" else FEMPTY ' k))
      (SET_TO_LIST {("entry",3)})) = (["p"],[])
Proof
  once_rewrite_tac[GSYM fmp_e2e_entry_plan_alist]
  >> simp[fmp_e2e_entry_plan_alist, fmp_select_point_restores_def]
QED

Theorem fmp_e2e_entry_lower_blocks_plan:
  !infos ctx runner s blocks.
    fmp_lower_blocks infos ctx runner s
      (fmap_to_alist (FEMPTY |+ (("entry",3),"p"))) blocks =
    fmp_lower_blocks infos ctx runner s [("entry",3),"p"] blocks
Proof
  rpt strip_tac
  >> cong_tac (SOME 1)
  >> MATCH_ACCEPT_TAC fmp_e2e_entry_plan_alist
QED

Theorem fmp_e2e_entry_reclaim_and_raw_ops_eval:
  ?sealed s.
    fmp_lower_function fmp_e2e_entry_ctx fmp_test_supply
      fmp_e2e_entry_fn = SOME (sealed,s) /\
    sealed.fn_blocks =
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 100 INITIAL_FMP [] ["formal_var_0"];
             mk_inst 101 ADD [Lit 32w; Lit 31w] ["formal_var_1"];
             mk_inst 102 AND
               [Var "formal_var_1";
                Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
               ["formal_var_2"];
             mk_inst 103 BUMP
               [Var "formal_var_0"; Var "formal_var_2"]
               ["p";"formal_var_0"];
             mk_inst 1 MLOAD [Var "p"] ["x"];
             mk_inst 2 STOP [] [];
             mk_inst 104 ASSIGN [Var "p"] ["formal_var_0"]] |>;
       <| bb_label := "ret";
          bb_instructions :=
            [mk_inst 3 RET [Var "formal_var_0"; Lit 99w] []] |>] /\
    sealed.fn_fmp_signature =
      SOME <| fms_has_fmp_param := F; fms_publishes := T |> /\
    s.irs_next_inst = 105 /\ s.irs_next_var = 3
Proof
  rewrite_tac[fmp_lower_function_def, fmp_e2e_entry_analysis_eval]
  >> simp[fmp_lower_function_with_info_def, fmp_e2e_entry_info_valid,
          fmp_e2e_entry_lower_input, fmp_e2e_entry_reclaim_eval,
          fmp_e2e_entry_reclaim_input, fmp_e2e_entry_plan_alist]
  >> rewrite_tac[fmp_e2e_entry_lower_blocks_plan]
  >> EVAL_TAC
  >> simp[]
QED

Definition fmp_e2e_callee_fn_def:
  fmp_e2e_callee_fn =
    mk_raw_function "e2e_callee"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 0 PARAM [Lit 0w] ["arg"];
             mk_inst 1 RETPC_PARAM [Lit 1w] ["pc"];
             mk_inst 2 RETFMP [Var "arg"; Var "pc"] []] |>]
End

Definition fmp_e2e_callee_ctx_def:
  fmp_e2e_callee_ctx = mk_venom_context [fmp_e2e_callee_fn] NONE
End

Theorem fmp_e2e_callee_analysis_eval:
  analyze_fmp_context fmp_e2e_callee_ctx =
    SOME (FEMPTY |+ ("e2e_callee",fmp_probe_info_tt))
Proof
  EVAL_TAC
QED

Theorem fmp_e2e_callee_info_valid:
  fmp_info_valid fmp_e2e_callee_ctx
    (FEMPTY |+ ("e2e_callee",fmp_probe_info_tt))
Proof
  irule analyze_fmp_context_valid
  >> ACCEPT_TAC fmp_e2e_callee_analysis_eval
QED

Theorem fmp_e2e_callee_lower_input:
  fmp_lower_input
    (FEMPTY |+ ("e2e_callee",fmp_probe_info_tt))
    fmp_e2e_callee_ctx fmp_e2e_callee_fn
Proof
  EVAL_TAC
QED

Theorem fmp_e2e_callee_wf:
  wf_function fmp_e2e_callee_fn /\ fn_inst_wf fmp_e2e_callee_fn
Proof
  EVAL_TAC >> rw[]
  >> gvs[fmp_e2e_lt3_cases, listTheory.REV_DEF,
         venomInstTheory.is_terminator_def, venomStateTheory.get_label_def,
         venomWfTheory.inst_wf_def]
QED

Definition fmp_e2e_callee_states_def:
  fmp_e2e_callee_states = THE (fmp_reclaim_states fmp_e2e_callee_fn)
End

Theorem fmp_e2e_callee_states_eq:
  fmp_reclaim_states fmp_e2e_callee_fn = SOME fmp_e2e_callee_states
Proof
  EVAL_TAC
QED

Theorem fmp_e2e_callee_candidate_empty:
  fmp_candidate_plan
    (FEMPTY |+ ("e2e_callee",fmp_probe_info_tt))
    fmp_e2e_callee_ctx fmp_e2e_callee_fn fmp_e2e_callee_states = FEMPTY
Proof
  EVAL_TAC
  >> simp[finite_mapTheory.FLOOKUP_FUNION,
          finite_mapTheory.FLOOKUP_UPDATE,
          fmpReclaimDefsTheory.fmp_plan_of_list_def]
QED

Theorem fmp_e2e_callee_reclaim_eval:
  analyze_fmp_reclaims
    (FEMPTY |+ ("e2e_callee",fmp_probe_info_tt))
    fmp_e2e_callee_ctx fmp_e2e_callee_fn = SOME FEMPTY
Proof
  irule fmpReclaimPropsTheory.analyze_fmp_reclaims_ready
  >> simp[fmp_e2e_callee_info_valid, fmp_e2e_callee_wf,
          fmp_e2e_callee_states_eq, fmp_e2e_callee_candidate_empty,
          fmpReclaimDefsTheory.fmp_reclaim_plan_ok_def]
  >> EVAL_TAC
QED

Theorem fmp_e2e_callee_hidden_layout_eval:
  ?sealed s.
    fmp_lower_function fmp_e2e_callee_ctx fmp_test_supply
      fmp_e2e_callee_fn = SOME (sealed,s) /\
    sealed.fn_blocks =
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 0 PARAM [Lit 0w] ["arg"];
             mk_inst 100 FMP_PARAM [Lit 1w] ["formal_var_0"];
             mk_inst 1 RETPC_PARAM [Lit 2w] ["pc"];
             mk_inst 2 RET
               [Var "arg"; Var "formal_var_0"; Var "pc"] []] |>] /\
    sealed.fn_fmp_signature =
      SOME <| fms_has_fmp_param := T; fms_publishes := T |> /\
    s.irs_next_inst = 101 /\ s.irs_next_var = 1
Proof
  rewrite_tac[fmp_lower_function_def, fmp_e2e_callee_analysis_eval]
  >> simp[fmp_lower_function_with_info_def, fmp_e2e_callee_info_valid,
          fmp_e2e_callee_lower_input, fmp_e2e_callee_reclaim_eval]
  >> EVAL_TAC
  >> simp[]
QED

Theorem fmp_malformed_invoke_arities_rejected_eval:
  fmp_lower_inst (FEMPTY |+ ("callee",fmp_probe_info_tt))
    fmp_probe_sealed_ctx "runner" fmp_test_supply
    (mk_inst 40 INVOKE [Label "callee"] ["user_out"]) = NONE /\
  fmp_lower_inst (FEMPTY |+ ("callee",fmp_probe_info_tt))
    fmp_probe_sealed_ctx "runner" fmp_test_supply
    (mk_inst 41 INVOKE [Label "callee"; Lit 7w] []) = NONE
Proof
  EVAL_TAC
QED


Theorem fmp_lower_inst_no_raw:
  fmp_lower_inst infos ctx runner s inst = SOME (out,s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) out
Proof
  Cases_on `inst.inst_opcode` >>
  gvs[fmp_lower_inst_def, fmp_lower_inst_shape_def,
      venomInstTheory.mk_inst_def, AllCaseEqs()] >>
  rpt strip_tac >>
  gvs[venomInstTheory.is_raw_fmp_opcode_def]
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
    (h.bb_label,LENGTH h.bb_instructions) restores` >>
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


Theorem fmp_lower_function_preserves_nonfmp_metadata:
  fmp_lower_function ctx supply fn = SOME (fn',supply') ==>
  fn_identity_metadata_eq fn' fn /\
  fn_static_input_eq fn' fn /\
  fn_static_layout_eq fn' fn
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[fmp_seal_preserves_nonfmp_metadata,
       venomInstTheory.fn_identity_metadata_eq_def,
       venomInstTheory.fn_static_input_eq_def,
       venomInstTheory.fn_static_layout_eq_def]
QED

Theorem fmp_lower_function_seals_signature_exact:
  analyze_fmp_context ctx = SOME infos /\
  fmp_lower_input infos ctx fn /\
  FLOOKUP infos fn.fn_name = SOME info /\
  fn.fn_fmp_signature = NONE /\
  fmp_lower_function ctx supply fn = SOME (fn',supply') ==>
  fn'.fn_fmp_signature =
    SOME <| fms_has_fmp_param := (info.fi_needs_fmp /\
                                   ~fn_is_context_entry ctx fn);
            fms_publishes := info.fi_publishes_fmp |>
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[fmp_seal_signature]
QED

Theorem fmp_lower_function_seals_signature:
  analyze_fmp_context ctx = SOME infos /\
  fmp_lower_input infos ctx fn /\
  fn.fn_fmp_signature = NONE /\
  fmp_lower_function ctx supply fn = SOME (fn',supply') ==>
  ?sig. fn'.fn_fmp_signature = SOME sig
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[fmp_seal_signature]
QED

Theorem fmp_lookup_function_self:
  ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\ MEM fn fns ==>
  lookup_function fn.fn_name fns = SOME fn
Proof
  Induct_on `fns`
  >- simp[venomInstTheory.lookup_function_def]
  >> rpt gen_tac
  >> simp[venomInstTheory.lookup_function_def, listTheory.FIND_thm]
  >> rpt strip_tac
  >> gvs[]
  >> `h.fn_name <> fn.fn_name` by
       metis_tac[listTheory.MEM_MAP]
  >> gvs[venomInstTheory.lookup_function_def]
QED

Theorem fmp_lower_function_idempotent:
  analyze_fmp_context ctx = SOME infos /\
  MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = SOME sig /\
  fmp_signature_matches_fn ctx fn /\
  no_raw_fmp_ops fn ==>
  fmp_lower_function ctx supply fn = SOME (fn,supply)
Proof
  rpt strip_tac >>
  `fmp_info_valid ctx infos` by
    metis_tac[analyze_fmp_context_valid] >>
  `lookup_function fn.fn_name ctx.ctx_functions = SOME fn` by
    (irule fmp_lookup_function_self >>
     gvs[fmpAnalysisDefsTheory.fmp_info_valid_def,
         venomWfTheory.ctx_distinct_fn_names_def,
         venomInstTheory.ctx_fn_names_def]) >>
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def]
QED

Theorem fmp_scan_insts_no_bits_no_raw:
  fmp_scan_insts insts = info /\
  ~info.fi_needs_fmp /\ ~info.fi_publishes_fmp ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) insts
Proof
  map_every qid_spec_tac [`info`] >> Induct_on `insts` >>
  simp[fmpAnalysisDefsTheory.fmp_scan_insts_def,
       fmpAnalysisDefsTheory.fmp_info_bottom_def,
       fmpAnalysisDefsTheory.fmp_info_join_def,
       fmpAnalysisDefsTheory.fmp_opcode_needs_fmp_def,
       fmpAnalysisDefsTheory.fmp_opcode_publishes_fmp_def,
       venomInstTheory.is_raw_fmp_opcode_def] >>
  rpt strip_tac >> Cases_on `h.inst_opcode` >>
  gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_direct_info_no_bits_no_raw:
  ~(fmp_direct_info fn).fi_needs_fmp /\
  ~(fmp_direct_info fn).fi_publishes_fmp ==>
  no_raw_fmp_ops fn
Proof
  simp[fmpAnalysisDefsTheory.fmp_direct_info_def,
       venomInstTheory.no_raw_fmp_ops_def,
       venomInstTheory.fn_insts_def] >> strip_tac >>
  `EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
         (fn_insts_blocks fn.fn_blocks)` by
    (irule fmp_scan_insts_no_bits_no_raw >> simp[]) >>
  gvs[listTheory.EVERY_MEM]
QED

Theorem fmp_fn_insts_blocks_mem:
  MEM inst (fn_insts_blocks blocks) ==>
  ?bb. MEM bb blocks /\ MEM inst bb.bb_instructions
Proof
  Induct_on `blocks` >>
  simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]
QED

Theorem fmp_blocks_every_no_raw:
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) blocks ==>
  no_raw_fmp_ops (fn with fn_blocks := blocks)
Proof
  simp[venomInstTheory.no_raw_fmp_ops_def,
       venomInstTheory.fn_insts_def, listTheory.EVERY_MEM] >>
  metis_tac[fmp_fn_insts_blocks_mem]
QED

Theorem fmp_option_every_no_raw:
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST opt) <=>
  !i. opt = SOME i ==> ~is_raw_fmp_opcode i.inst_opcode
Proof
  Cases_on `opt` >> EVAL_TAC >> simp[]
QED

Theorem split_fmp_entry_from_retpc_opcode:
  split_fmp_entry_from k users insts =
    SOME (FmpEntryLayout users' (SOME retpc) tailinsts) ==>
  retpc.inst_opcode = RETPC_PARAM
Proof
  map_every qid_spec_tac [`tailinsts`,`retpc`,`users'`,`users`,`k`] >>
  Induct_on `insts`
  >- simp[split_fmp_entry_from_def]
  >> simp[split_fmp_entry_from_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED


Theorem split_fmp_entry_retpc_opcode:
  split_fmp_entry fn =
    SOME (FmpEntryLayout users (SOME retpc) tailinsts) ==>
  retpc.inst_opcode = RETPC_PARAM
Proof
  simp[split_fmp_entry_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[split_fmp_entry_from_retpc_opcode]
QED
Theorem split_fmp_entry_retpc_no_raw:
  split_fmp_entry fn = SOME (FmpEntryLayout users retpc tailinsts) ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST retpc)
Proof
  simp[split_fmp_entry_def, AllCaseEqs(), fmp_option_every_no_raw] >>
  rpt strip_tac >>
  metis_tac[split_fmp_entry_from_retpc_opcode,
            venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_make_root_layout_no_raw_insertions:
  fmp_make_root_layout ctx fn info runner s =
    SOME (FmpRootLayout n root retpc s') ==>
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST root) /\
  EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode) (OPTION_TO_LIST retpc)
Proof
  simp[fmp_make_root_layout_def, AllCaseEqs(), fmp_option_every_no_raw] >>
  rpt strip_tac >>
  gvs[venomInstTheory.mk_inst_def, set_param_index_def,
      venomInstTheory.is_raw_fmp_opcode_def] >>
  metis_tac[split_fmp_entry_retpc_opcode,
            venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_seal_no_raw:
  EVERY (\bb. EVERY (\i. ~is_raw_fmp_opcode i.inst_opcode)
                     bb.bb_instructions) blocks ==>
  no_raw_fmp_ops (fmp_seal ctx fn info blocks)
Proof
  strip_tac >> drule fmp_blocks_every_no_raw >>
  simp[fmp_seal_def]
QED

Theorem fmp_no_need_input_no_raw:
  analyze_fmp_context ctx = SOME infos /\
  fmp_lower_input infos ctx fn /\
  FLOOKUP infos fn.fn_name = SOME info /\
  ~info.fi_needs_fmp /\ ~info.fi_publishes_fmp ==>
  no_raw_fmp_ops fn
Proof
  simp[fmp_lower_input_def] >> rpt strip_tac >>
  `MEM fn ctx.ctx_functions` by
    metis_tac[venomInstTheory.lookup_function_MEM] >>
  drule_all analyze_fmp_context_unsealed_direct_fields >> strip_tac >>
  irule fmp_direct_info_no_bits_no_raw >> metis_tac[]
QED

Theorem fmp_lower_function_removes_raw_ops:
  analyze_fmp_context ctx = SOME infos /\
  fmp_lower_input infos ctx fn /\
  fmp_lower_function ctx supply fn = SOME (fn',supply') ==>
  no_raw_fmp_ops fn'
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (drule_all fmp_no_need_input_no_raw >>
      simp[fmp_seal_def, venomInstTheory.no_raw_fmp_ops_def,
           venomInstTheory.fn_insts_def])
  >> Cases_on `root_layout` >> gvs[] >>
  drule fmp_lower_blocks_no_raw >> strip_tac >>
  drule fmp_make_root_layout_no_raw_insertions >> strip_tac >>
  drule_all fmp_install_root_no_raw >> strip_tac >>
  drule fmp_seal_no_raw >> simp[]
QED

Theorem fmp_lowered_context_wf_sealed_raw_free:
  fmp_lowered_context_wf ctx /\ MEM fn ctx.ctx_functions ==>
  (?sig. fn.fn_fmp_signature = SOME sig) /\ no_raw_fmp_ops fn
Proof
  strip_tac >>
  drule_all fmp_lowered_context_wf_function >> strip_tac >>
  conj_tac
  >- (Cases_on `fn.fn_fmp_signature` >>
      gvs[fmpWfDefsTheory.fmp_signature_matches_fn_def])
  >> simp[]
QED

Theorem fmp_lowered_context_wf_signature_matches:
  fmp_lowered_context_wf ctx /\ MEM fn ctx.ctx_functions ==>
  fmp_signature_matches_fn ctx fn
Proof
  metis_tac[fmp_lowered_context_wf_function]
QED

Theorem fmp_invalid_seal_rejected:
  analyze_fmp_context ctx = SOME infos /\
  fn.fn_fmp_signature = SOME sig /\
  (~fmp_signature_matches_fn ctx fn \/ ~no_raw_fmp_ops fn) ==>
  fmp_lower_function ctx supply fn = NONE
Proof
  simp[fmp_lower_function_def, fmp_lower_function_with_info_def]
QED
val _ = export_theory();
