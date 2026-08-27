# Compiler proof baseline

Captured 2026-08-27 from the repository state before the O1 implementation.
This is the comparison baseline for active proof cheats and build diagnostics.

## Capture

- Source revision: `6801aec340fb803ceec9666e072900749d7b83c1` (`vyper-o1-pipeline`)
- Build: active-cheat source theories were temporarily invalidated with comment-only rebuild markers, then rebuilt with normal goalfrag output; resource-limited parallel runs were resumed or completed as individual logical targets, after which every marker was restored.
- Result: all source-triggered targets passed, and the restored root passed (`holbuild finished in 1.180s`; cache-restored theories correctly emit no fresh warning records).
- Fresh source-triggered theory compilation recorded **131** `Saved CHEAT` warning records in successful `build.log` files; the normalized file/theorem inventory is [`compiler-proof-baseline-warnings.txt`](compiler-proof-baseline-warnings.txt).
- Static active `cheat` tokens: **144** in **117** file/theorem sites across **42** files.

The static scan covered tracked `*.sml` files, ignored nested comments, and keyed
entries by source file and nearest enclosing theorem/definition name. Occurrence
counts are recorded so later line movement does not change site identity. Comments
and generated `.holbuild` files are excluded. Build warnings are recorded
separately: ordinary HOL warnings are not counted as `CHEAT` warnings. A warning can
be propagated through an `ACCEPT_TAC` or dependent theorem, so the warning inventory
is intentionally not required to be a one-to-one copy of the static token table.

## Active cheat sites

| File | Theorem/definition | Occurrences |
|---|---|---:|
| `lowering/abiEncoderPropsScript.sml` | `compile_abi_decode_static_correct` | 1 |
| `lowering/abiEncoderPropsScript.sml` | `compile_abi_encode_to_buf_correct` | 8 |
| `lowering/abiEncoderPropsScript.sml` | `compile_abi_zero_pad_correct` | 1 |
| `lowering/builtinPropsScript.sml` | `compile_raw_call_correct` | 1 |
| `lowering/builtinPropsScript.sml` | `compile_send_correct` | 1 |
| `lowering/builtinPropsScript.sml` | `compile_raw_create_correct` | 1 |
| `lowering/builtinPropsScript.sml` | `lower_abi_encode_correct` | 1 |
| `lowering/builtinPropsScript.sml` | `lower_abi_decode_correct` | 1 |
| `lowering/builtinTypeConvertPropsScript.sml` | `compile_type_convert_correct` | 1 |
| `lowering/e2eCorrectnessScript.sml` | `compile_vyper_evm_correspondence` | 1 |
| `lowering/e2eCorrectnessScript.sml` | `evm_correspondence_to_call_result` | 1 |
| `lowering/e2eCorrectnessScript.sml` | `evm_revert_state_unchanged` | 1 |
| `lowering/e2eCorrectnessScript.sml` | `o2_pipeline_ctx_pass_correct` | 1 |
| `lowering/emitHelperPropsScript.sml` | `fresh_label_output_inj` | 1 |
| `lowering/emitHelperPropsScript.sml` | `compile_state_ok_initial` | 1 |
| `lowering/emitHelperPropsScript.sml` | `compile_state_ok_emit_op` | 1 |
| `lowering/emitHelperPropsScript.sml` | `compile_state_ok_emit_void` | 1 |
| `lowering/emitHelperPropsScript.sml` | `compile_state_ok_emit_inst` | 1 |
| `lowering/emitHelperPropsScript.sml` | `fresh_label_produces_external` | 1 |
| `lowering/emitHelperPropsScript.sml` | `compile_state_ok_fresh_var` | 1 |
| `lowering/emitHelperPropsScript.sml` | `compile_state_ok_fresh_id` | 1 |
| `lowering/emitHelperPropsScript.sml` | `compile_state_ok_new_block` | 1 |
| `lowering/emitHelperPropsScript.sml` | `label_external_mono` | 1 |
| `lowering/exprLoweringPropsScript.sml` | `compile_expr_correct` | 1 |
| `lowering/exprLoweringPropsScript.sml` | `compile_name_correct` | 1 |
| `lowering/exprLoweringPropsScript.sml` | `compile_binop_correct` | 1 |
| `lowering/exprLoweringPropsScript.sml` | `compile_neg_correct` | 1 |
| `lowering/exprLoweringPropsScript.sml` | `compile_expr_ci_mono` | 1 |
| `lowering/moduleLoweringPropsScript.sml` | `compile_selector_dispatch_linear_correct` | 1 |
| `lowering/moduleLoweringPropsScript.sml` | `compile_selector_dispatch_sparse_correct` | 1 |
| `lowering/moduleLoweringPropsScript.sml` | `compile_entry_point_kwargs_correct` | 1 |
| `lowering/moduleLoweringPropsScript.sml` | `compile_generate_runtime_correct` | 1 |
| `lowering/proofs/loweringMemSafetyProofsScript.sml` | `lowering_memory_safe` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_stmt_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_stmts_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_expr_stmt_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_annassign_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_assign_name_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_assert_correct_true` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_assert_bare_correct_false` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_assert_reason_correct_false` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_return_none_external_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_return_none_internal_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_return_some_external_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_return_some_internal_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_if_correct` | 1 |
| `lowering/stmtLoweringPropsScript.sml` | `compile_for_range_correct` | 1 |
| `lowering/vyperLoweringCorrectScript.sml` | `vyper_to_venom_correct` | 1 |
| `venom/codegen/asmToBytecodePropsScript.sml` | `asm_bytecode_sim` | 1 |
| `venom/codegen/codegenCorrectnessScript.sml` | `codegen_fn_correct` | 1 |
| `venom/codegen/codegenCorrectnessScript.sml` | `codegen_correct` | 1 |
| `venom/codegen/proofs/genBlockSimScript.sml` | `gen_inst_halt_sim` | 1 |
| `venom/codegen/proofs/genBlockSimScript.sml` | `gen_inst_abort_sim` | 2 |
| `venom/codegen/proofs/genBlockSimScript.sml` | `do_dup_poke_venom_asm_rel` | 15 |
| `venom/codegen/venomToAsmPropsScript.sml` | `gen_inst_simulation` | 1 |
| `venom/codegen/venomToAsmPropsScript.sml` | `gen_block_simulation` | 1 |
| `venom/codegen/venomToAsmPropsScript.sml` | `gen_fn_simulation` | 1 |
| `venom/passes/algebraic_opt/algebraicOptCorrectnessScript.sml` | `ao_preserves_ssa_form` | 1 |
| `venom/passes/algebraic_opt/algebraicOptCorrectnessScript.sml` | `ao_preserves_wf_function` | 1 |
| `venom/passes/algebraic_opt/proofs/algebraicOptProofsScript.sml` | `ao_transform_function_correct_proof` | 1 |
| `venom/passes/assert_combiner/assertCombinerCorrectnessScript.sml` | `ac_preserves_ssa_form` | 1 |
| `venom/passes/assert_combiner/assertCombinerCorrectnessScript.sml` | `ac_preserves_wf_function` | 1 |
| `venom/passes/branch_opt/branchOptCorrectnessScript.sml` | `branch_opt_preserves_ssa_form` | 1 |
| `venom/passes/branch_opt/branchOptCorrectnessScript.sml` | `branch_opt_preserves_wf_function` | 1 |
| `venom/passes/cfg_normalization/cfgNormCorrectnessScript.sml` | `cfg_norm_pass_correct` | 1 |
| `venom/passes/cfg_normalization/cfgNormCorrectnessScript.sml` | `cfg_norm_establishes_normalized_cfg` | 1 |
| `venom/passes/cfg_normalization/cfgNormCorrectnessScript.sml` | `cfg_norm_preserves_ssa_form` | 1 |
| `venom/passes/cfg_normalization/cfgNormCorrectnessScript.sml` | `cfg_norm_preserves_wf_function` | 1 |
| `venom/passes/cse/cseCorrectnessScript.sml` | `cse_preserves_ssa_form` | 1 |
| `venom/passes/cse/cseCorrectnessScript.sml` | `cse_preserves_wf_function` | 1 |
| `venom/passes/cse/proofs/cseProofsScript.sml` | `cse_function_correct_proof` | 1 |
| `venom/passes/dead_store_elim/proofs/deadStoreElimProofsScript.sml` | `dse_function_space_correct` | 1 |
| `venom/passes/dead_store_elim/proofs/deadStoreElimProofsScript.sml` | `dse_function_correct` | 1 |
| `venom/passes/function_inliner/defs/functionInlinerDefsScript.sml` | `call_walk_dfs_def` | 1 |
| `venom/passes/function_inliner/functionInlinerCorrectnessScript.sml` | `function_inliner_preserves_wf_function` | 1 |
| `venom/passes/function_inliner/proofs/functionInlinerProofScript.sml` | `function_inliner_correct` | 1 |
| `venom/passes/internal_return_copy_fwd/proofs/internalReturnCopyFwdProofsScript.sml` | `ircf_pass_correct` | 1 |
| `venom/passes/load_elim/loadElimCorrectnessScript.sml` | `load_elim_preserves_ssa_form` | 1 |
| `venom/passes/load_elim/loadElimCorrectnessScript.sml` | `load_elim_preserves_wf_function` | 1 |
| `venom/passes/load_elim/proofs/loadElimProofsScript.sml` | `load_elim_one_correct_proof` | 1 |
| `venom/passes/load_elim/proofs/loadElimProofsScript.sml` | `load_elim_function_correct_proof` | 1 |
| `venom/passes/lower_dload/lowerDloadCorrectnessScript.sml` | `lower_dload_preserves_ssa_form` | 1 |
| `venom/passes/lower_dload/lowerDloadCorrectnessScript.sml` | `lower_dload_preserves_wf_function` | 1 |
| `venom/passes/mem2var/mem2varCorrectnessScript.sml` | `m2v_preserves_ssa_form` | 1 |
| `venom/passes/mem2var/mem2varCorrectnessScript.sml` | `m2v_preserves_wf_function` | 1 |
| `venom/passes/memmerging/proofs/mmWfProofsScript.sml` | `mm_preserves_ssa_form` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `bp_analyze_ptr_fdom` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `bp_analyze_vv_inv` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `bp_analyze_fixpoint` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `bp_fixpoint_drestrict_or_match` | 2 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `bp_assign_drestrict_ptrs_eq` | 2 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `cf_alloca_ok_opt_joined` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `cf_keys_ok_boundary` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `stage2_correct` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `lse_step_equiv` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `load_new_entry_sound` | 1 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `lse_inv_preserved` | 2 |
| `venom/passes/memory_copy_elision/proofs/memoryCopyElisionProofsScript.sml` | `staticcall_lf_sound_helper` | 3 |
| `venom/passes/readonly_invoke_copy_fwd/proofs/readonlyInvokeCopyFwdProofsScript.sml` | `ricf_pass_correct` | 1 |
| `venom/passes/remove_unused/proofs/removeUnusedStructProofsScript.sml` | `rusp_preserves_alloca_pointer_confined` | 1 |
| `venom/passes/revert_to_assert/rtaCorrectnessScript.sml` | `rta_preserves_ssa_form` | 1 |
| `venom/passes/revert_to_assert/rtaCorrectnessScript.sml` | `rta_preserves_wf_function` | 1 |
| `venom/passes/shared/proofs/copyFwdEquivScript.sml` | `copy_fwd_read_equiv` | 1 |
| `venom/passes/shared/proofs/copyFwdEquivScript.sml` | `copy_fwd_write_equiv` | 1 |
| `venom/passes/shared/proofs/copyFwdEquivScript.sml` | `copy_fwd_terminator_equiv` | 1 |
| `venom/passes/shared/proofs/copyFwdEquivScript.sml` | `copy_fwd_rel_preserved_identical_inst` | 1 |
| `venom/passes/simplify_cfg/defs/simplifyCfgDefsScript.sml` | `collapse_dfs_def` | 1 |
| `venom/passes/simplify_cfg/proofs/simplifyCfgProofScript.sml` | `simplify_cfg_fn_correct` | 1 |
| `venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml` | `simplify_cfg_establishes_all_reachable` | 1 |
| `venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml` | `simplify_cfg_preserves_ssa_form` | 1 |
| `venom/passes/simplify_cfg/simplifyCfgCorrectnessScript.sml` | `simplify_cfg_preserves_wf_function` | 1 |
| `venom/passes/single_use_expansion/singleUseExpansionCorrectnessScript.sml` | `sue_preserves_ssa_form` | 1 |
| `venom/passes/single_use_expansion/singleUseExpansionCorrectnessScript.sml` | `sue_preserves_wf_function` | 1 |
| `venom/passes/tail_merge/tailMergeCorrectnessScript.sml` | `tail_merge_pass_correct` | 1 |
| `venom/passes/tail_merge/tailMergeCorrectnessScript.sml` | `tail_merge_preserves_ssa_form` | 1 |
| `venom/passes/tail_merge/tailMergeCorrectnessScript.sml` | `tail_merge_preserves_wf_function` | 1 |
| `venom/proofs/execEquivProofsScript.sml` | `run_function_result_equiv_closed` | 1 |
