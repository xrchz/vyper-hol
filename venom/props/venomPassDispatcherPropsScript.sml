Theory venomPassDispatcherProps
Ancestors
  venomPassDispatcher
  makeSsaCurrentProps cfgNormSupplyProofs singleUseExpansionSupplyProofs
  simplifyCfgLabelProps lowerDloadSupplyProofs
  concretizeMemLocTransitionProofs fmpLowerProps fmpLowerInvokeProps
  dretDesugarProofs dretDesugarProps dftStructural

Theorem fn_identity_metadata_eq_call_abi[local]:
  fn_identity_metadata_eq after before ==>
  after.fn_call_abi = before.fn_call_abi
Proof
  simp[venomInstTheory.fn_identity_metadata_eq_def]
QED

Theorem fmp_lower_function_success_has_signature[local]:
  fmp_lower_function ctx s fn = SOME (fn',s') ==>
  IS_SOME fn'.fn_fmp_signature
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       fmpLowerDefsTheory.fmp_lower_function_with_info_def,
       fmpLowerDefsTheory.fmp_checked_seal_def,
       fmpLowerDefsTheory.fmp_seal_def, AllCaseEqs()] >>
  strip_tac >> gvs[]
QED
Theorem dft_fn_metadata[local]:
  fn_identity_metadata_eq (dft_fn fn) fn /\
  fn_static_input_eq (dft_fn fn) fn /\
  fn_static_layout_eq (dft_fn fn) fn /\
  fn_fmp_convention_eq (dft_fn fn) fn
Proof
  simp[dftDefsTheory.dft_fn_def] >>
  pairarg_tac >>
  simp[venomInstTheory.fn_identity_metadata_eq_def,
       venomInstTheory.fn_static_input_eq_def,
       venomInstTheory.fn_static_layout_eq_def,
       venomInstTheory.fn_fmp_convention_eq_def]
QED
Theorem sue_blocks_invoke_labels_eq_scan[local]:
  !bbs.
    FLAT (MAP (\bb. MAP FST (get_invoke_targets bb.bb_instructions)) bbs) =
    MAP FST (get_invoke_targets (fn_insts_blocks bbs))
Proof
  Induct_on `bbs` >>
  simp[venomInstTheory.fn_insts_blocks_def, sue_get_invoke_targets_append,
       fcgDefsTheory.get_invoke_targets_def]
QED

Theorem sue_fn_invoke_labels_eq_scan[local]:
  sue_fn_invoke_labels fn = MAP FST (fcg_scan_function fn)
Proof
  simp[sue_fn_invoke_labels_def, fcgDefsTheory.fcg_scan_function_def,
       venomInstTheory.fn_insts_def, sue_blocks_invoke_labels_eq_scan]
QED


Definition dispatcher_probe_supply_def:
  dispatcher_probe_supply =
    <| irs_next_inst := 10; irs_next_var := 10; irs_next_label := 10;
       irs_used_inst_ids := []; irs_used_vars := []; irs_used_labels := [] |>
End

Definition dispatcher_empty_fn_def:
  dispatcher_empty_fn = mk_raw_function "dispatcher_probe" []
End

Definition dispatcher_empty_unit_def:
  dispatcher_empty_unit =
    <| cu_context := mk_venom_context [dispatcher_empty_fn] NONE;
       cu_data_segment := [] |>
End

Definition dispatcher_probe_policy_def:
  dispatcher_probe_policy =
    <| rpol_target := prague_capabilities;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
End

Theorem dispatcher_total_empty_tags_eval:
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_CFGNormalization) dispatcher_empty_unit
    dispatcher_probe_supply dispatcher_empty_fn =
      SOME <| fpo_function := dispatcher_empty_fn; fpo_label_map := [];
              fpo_supply := dispatcher_probe_supply |> /\
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_DFT) dispatcher_empty_unit
    dispatcher_probe_supply dispatcher_empty_fn =
      SOME <| fpo_function := dispatcher_empty_fn; fpo_label_map := [];
              fpo_supply := dispatcher_probe_supply |> /\
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_LowerDload) dispatcher_empty_unit
    dispatcher_probe_supply dispatcher_empty_fn =
      SOME <| fpo_function := dispatcher_empty_fn; fpo_label_map := [];
              fpo_supply := dispatcher_probe_supply |> /\
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_MakeSSA) dispatcher_empty_unit
    dispatcher_probe_supply dispatcher_empty_fn =
      SOME <| fpo_function := dispatcher_empty_fn; fpo_label_map := [];
              fpo_supply := dispatcher_probe_supply |> /\
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_SimplifyCFG) dispatcher_empty_unit
    dispatcher_probe_supply dispatcher_empty_fn =
      SOME <| fpo_function := dispatcher_empty_fn; fpo_label_map := [];
              fpo_supply := dispatcher_probe_supply |> /\
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_SingleUseExpansion) dispatcher_empty_unit
    dispatcher_probe_supply dispatcher_empty_fn =
      SOME <| fpo_function := dispatcher_empty_fn; fpo_label_map := [];
              fpo_supply := dispatcher_probe_supply |>
Proof
  EVAL_TAC
QED


Definition dispatcher_concretize_fn_def:
  dispatcher_concretize_fn = mk_raw_function "global" []
End

Definition dispatcher_concretize_unit_def:
  dispatcher_concretize_unit =
    <| cu_context :=
         ((mk_venom_context [dispatcher_concretize_fn] NONE) with
            ctx_global_reserved := [(8,4)]);
       cu_data_segment := [] |>
End

Definition dispatcher_concretize_stale_fn_def:
  dispatcher_concretize_stale_fn =
    (dispatcher_concretize_fn with fn_eom := SOME 12) with
      fn_forced_alloc_positions := FEMPTY |+ (7,32)
End

Theorem dispatcher_concretize_success_and_failure_eval:
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_ConcretizeMemLoc) dispatcher_concretize_unit
    dispatcher_probe_supply dispatcher_concretize_fn =
      SOME <| fpo_function := dispatcher_concretize_fn with fn_eom := SOME 12;
              fpo_label_map := []; fpo_supply := dispatcher_probe_supply |> /\
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_ConcretizeMemLoc) dispatcher_concretize_unit
    dispatcher_probe_supply dispatcher_concretize_stale_fn = NONE
Proof
  conj_tac
  >- simp[execute_configured_fn_pass_def, dispatcher_concretize_unit_def,
          dispatcher_concretize_fn_def, dispatcher_probe_supply_def,
          concretizeMemLocDefsTheory.concretize_function_eval_global_only] >>
  EVAL_TAC >> simp[finite_mapTheory.FUPDATE_EQ]
QED

Theorem dispatcher_simplify_cfg_label_map_eval:
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_SimplifyCFG) dispatcher_empty_unit
    dispatcher_probe_supply simplify_cfg_chain_fixture =
  SOME <| fpo_function := simplify_cfg_chain_result;
          fpo_label_map := [("mid","old");("new","old")];
          fpo_supply := dispatcher_probe_supply |>
Proof
  simp[simplify_cfg_chain_collapse_eval]
QED

Definition dispatcher_dret_disabled_policy_def:
  dispatcher_dret_disabled_policy =
    dispatcher_probe_policy with rpol_target := (\c. F)
End

Theorem dispatcher_dret_target_behavior_eval:
  (case execute_configured_fn_pass dispatcher_probe_policy
          (CFP_Simple VP_DretDesugar) dispatcher_empty_unit
          dret_test_supply dret_multi_fn of
     NONE => F
   | SOME out =>
       no_dret out.fpo_function /\
       dret_opcode_count MCOPY out.fpo_function = 2 /\
       out.fpo_label_map = [] /\ out.fpo_supply.irs_next_inst = 114) /\
  execute_configured_fn_pass dispatcher_dret_disabled_policy
    (CFP_Simple VP_DretDesugar) dispatcher_empty_unit
    dret_test_supply dret_multi_fn = NONE
Proof
  conj_tac
  >- (mp_tac dret_multiple_expansion_eval >> strip_tac >>
      Cases_on `dret_desugar_function prague_capabilities
                  dret_test_supply dret_multi_fn`
      >- gvs[] >>
      PairCases_on `x` >>
      qpat_x_assum `dret_desugar_function _ _ _ = SOME _`
        (fn th => fs[th, execute_configured_fn_pass_def,
                     dispatcher_probe_policy_def])) >>
  simp[execute_configured_fn_pass_def, dispatcher_probe_policy_def,
       dispatcher_dret_disabled_policy_def,
       dret_missing_mcopy_rejected_eval]
QED

Definition dispatcher_fmp_current_unit_def:
  dispatcher_fmp_current_unit =
    <| cu_context := fmp_probe_sealed_ctx; cu_data_segment := [] |>
End

Definition dispatcher_fmp_stale_unit_def:
  dispatcher_fmp_stale_unit =
    <| cu_context := fmp_probe_bad_sealed_ctx; cu_data_segment := [] |>
End

Theorem dispatcher_fmp_current_unit_eval:
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_FmpLowering) dispatcher_fmp_current_unit
    fmp_test_supply fmp_positive_callee =
      SOME <| fpo_function := fmp_positive_callee; fpo_label_map := [];
              fpo_supply := fmp_test_supply |> /\
  execute_configured_fn_pass dispatcher_probe_policy
    (CFP_Simple VP_FmpLowering) dispatcher_fmp_stale_unit
    fmp_test_supply fmp_positive_callee = NONE
Proof
  conj_tac
  >- simp[dispatcher_fmp_current_unit_def, fmp_valid_sealed_identity_eval] >>
  simp[dispatcher_fmp_stale_unit_def] >>
  rewrite_tac[GSYM fmp_changed_ctx_def, fmp_public_context_freshness_eval] >>
  simp[]
QED


Theorem execute_configured_fn_pass_effects:
  execute_configured_fn_pass rpolicy pass unit s fn = SOME out ==>
  fn_pass_effects_hold (fn_pass_tag pass) fn out
Proof
  Cases_on `pass` >> rename1 `CFP_Simple tag` >> Cases_on `tag` >>
  gvs[execute_configured_fn_pass_def, venomPassScheduleTheory.fn_pass_tag_def,
      fn_pass_effects_hold_def, fn_metadata_effect_holds_def,
      fn_static_layout_effect_holds_def, fn_abi_effect_holds_def,
      fn_pass_metadata_effect_def, fn_pass_static_layout_effect_def,
      fn_pass_abi_effect_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac concretize_function_eval_metadata_transition >>
  imp_res_tac concretize_function_eval_sets_eom >>
  imp_res_tac dft_fn_metadata >>
  imp_res_tac cfg_norm_function_supply_metadata >>
  imp_res_tac dret_desugar_function_metadata >>
  imp_res_tac fmp_lower_function_preserves_nonfmp_metadata >>
  imp_res_tac fmp_lower_function_success_has_signature >>
  imp_res_tac lower_dload_function_supply_metadata >>
  imp_res_tac make_ssa_current_fn_metadata >>
  imp_res_tac simplify_cfg_fn_with_labels_metadata >>
  imp_res_tac sue_expand_function_supply_structural >>
  gvs[dft_fn_metadata, fn_identity_metadata_eq_call_abi,
      venomInstTheory.fn_identity_metadata_eq_def,
      venomInstTheory.fn_static_input_eq_def,
      venomInstTheory.fn_static_layout_eq_def,
      venomInstTheory.fn_fmp_convention_eq_def] >>
  Cases_on `lower_dload_invalidates_layout fn` >> gvs[]
QED

Definition runner_refines_current_dispatch_def:
  runner_refines_current_dispatch runner <=>
    !rpolicy pass unit supply fn.
      runner rpolicy pass unit supply fn =
      execute_configured_fn_pass rpolicy pass unit supply fn
End

Theorem execute_configured_fn_pass_self_refines:
  runner_refines_current_dispatch execute_configured_fn_pass
Proof
  simp[runner_refines_current_dispatch_def]
QED

Theorem execute_configured_fn_pass_introduces_no_invoke_edges:
  execute_configured_fn_pass rpolicy pass unit s fn = SOME out ==>
  introduces_no_invoke_edges fn out.fpo_function
Proof
  Cases_on `pass` >> rename1 `CFP_Simple tag` >> Cases_on `tag` >>
  gvs[execute_configured_fn_pass_def, introduces_no_invoke_edges_def,
      AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  imp_res_tac concretize_function_eval_invoke_targets >>
  imp_res_tac cfg_norm_function_supply_invoke_labels_subset >>
  imp_res_tac dft_fn_invoke_subset >>
  imp_res_tac dret_desugar_function_invoke_targets >>
  imp_res_tac fmp_lower_function_invoke_targets_subset >>
  imp_res_tac lower_dload_function_supply_invoke_targets >>
  imp_res_tac make_ssa_current_fn_invoke_targets_subset >>
  imp_res_tac simplify_cfg_fn_with_labels_invoke_subset >>
  imp_res_tac sue_expand_function_supply_structural >>
  gvs[dft_fn_invoke_subset,
      simplify_cfg_fn_with_labels_invoke_subset,
      simplify_cfg_invoke_subset_def,
      simplify_cfg_fn_invoke_labels_def,
      sue_fn_invoke_labels_eq_scan,
      listTheory.EVERY_MEM]
  >- (`simplify_cfg_invoke_subset
         (FST (simplify_cfg_fn_with_labels fn)) fn` by
        simp[simplify_cfg_fn_with_labels_invoke_subset] >>
      gvs[simplify_cfg_invoke_subset_def,
          simplify_cfg_fn_invoke_labels_def])
QED

Theorem execute_configured_fn_pass_o1_suffix_no_raw_fmp_ops:
  MEM tag [VP_MakeSSA; VP_SimplifyCFG; VP_SingleUseExpansion;
           VP_DFT; VP_CFGNormalization] /\
  no_raw_fmp_ops fn /\
  execute_configured_fn_pass rpolicy (CFP_Simple tag) unit s fn = SOME out ==>
  no_raw_fmp_ops out.fpo_function
Proof
  Cases_on `tag` >>
  gvs[execute_configured_fn_pass_def,AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  `no_raw_fmp_ops (FST (make_ssa_current_fn s fn))` by
    metis_tac[make_ssa_current_fn_no_raw_fmp_ops] >>
  `no_raw_fmp_ops (FST (simplify_cfg_fn_with_labels fn))` by
    metis_tac[simplify_cfg_fn_with_labels_no_raw_fmp_ops] >>
  `no_raw_fmp_ops (FST (sue_expand_function_supply s fn))` by
    metis_tac[sue_expand_function_supply_no_raw_fmp_ops] >>
  `no_raw_fmp_ops (dft_fn fn)` by
    metis_tac[dft_fn_no_raw_fmp_ops] >>
  `no_raw_fmp_ops (FST (cfg_norm_function_supply s fn))` by
    metis_tac[cfg_norm_function_supply_no_raw_fmp_ops] >>
  gvs[]
QED

val _ = export_theory ();
