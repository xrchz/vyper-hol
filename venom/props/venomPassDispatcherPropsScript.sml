Theory venomPassDispatcherProps
Ancestors
  venomPassDispatcher
  makeSsaCurrentProps cfgNormSupplyProofs singleUseExpansionSupplyProofs
  simplifyCfgLabelProps lowerDloadSupplyProofs
  concretizeMemLocTransitionProofs fmpLowerProps fmpLowerInvokeProps
  dretDesugarProofs dftStructural

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
