(* Executable boundary probes and structural properties for fresh FMP analysis. *)

Theory fmpAnalysisProps
Ancestors
  fmpAnalysisDefs
  fmpWfProps
  fmpWfDefs
  callLayoutDefs
  venomInst
Definition fmp_probe_info_ff_def:
  fmp_probe_info_ff = <| fi_needs_fmp := F; fi_publishes_fmp := F |>
End

Definition fmp_probe_info_tf_def:
  fmp_probe_info_tf = <| fi_needs_fmp := T; fi_publishes_fmp := F |>
End

Definition fmp_probe_info_ft_def:
  fmp_probe_info_ft = <| fi_needs_fmp := F; fi_publishes_fmp := T |>
End

Definition fmp_probe_info_tt_def:
  fmp_probe_info_tt = <| fi_needs_fmp := T; fi_publishes_fmp := T |>
End

Definition fmp_probe_block_def:
  fmp_probe_block insts = <| bb_label := "entry"; bb_instructions := insts |>
End

Definition fmp_probe_raw_fn_def:
  fmp_probe_raw_fn name insts = mk_raw_function name [fmp_probe_block insts]
End

Definition fmp_probe_invoke_def:
  fmp_probe_invoke id target = mk_inst id INVOKE [Label target] []
End

Definition fmp_probe_get_fn_def:
  fmp_probe_get_fn = fmp_probe_raw_fn "raw" [mk_inst 1 GETFMP [] ["fmp"]]
End

Definition fmp_probe_set_fn_def:
  fmp_probe_set_fn = fmp_probe_raw_fn "raw" [mk_inst 2 SETFMP [Lit 32w] []]
End

Theorem fmp_direct_raw_seed_eval:
  fmp_direct_info fmp_probe_get_fn = fmp_probe_info_tf /\
  fmp_direct_info fmp_probe_set_fn = fmp_probe_info_ft /\
  FLOOKUP (THE (analyze_fmp_context
    (mk_venom_context [fmp_probe_get_fn] NONE))) "raw" =
      SOME fmp_probe_info_tf
Proof
  EVAL_TAC
QED

(* Current syntax is rescanned: changing GETFMP to SETFMP changes both bits. *)
Theorem fmp_raw_mutation_freshness_eval:
  analyze_fmp_context (mk_venom_context [fmp_probe_get_fn] NONE) <>
  analyze_fmp_context (mk_venom_context [fmp_probe_set_fn] NONE)
Proof
  EVAL_TAC
  >> strip_tac
  >> pop_assum (mp_tac o Q.AP_TERM `\m. FLOOKUP m "raw"`)
  >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Definition fmp_probe_caller_def:
  fmp_probe_caller =
    fmp_probe_raw_fn "caller" [fmp_probe_invoke 10 "callee"]
End

Definition fmp_probe_sealed_ctx_def:
  fmp_probe_sealed_ctx =
    mk_venom_context [fmp_probe_caller; fmp_positive_callee] (SOME "caller")
End

Theorem fmp_probe_callee_cfmp_fuel:
  !fuel. fmp_value_rooted_fuel fmp_probe_sealed_ctx fmp_positive_callee_sig
    fmp_positive_callee (SUC fuel) "cfmp"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_param
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> qexists `mk_inst 21 FMP_PARAM [Lit 1w] ["cfmp"]` >> EVAL_TAC
QED

Theorem fmp_probe_callee_adopted_fuel:
  !fuel. fmp_value_rooted_fuel fmp_probe_sealed_ctx fmp_positive_callee_sig
    fmp_positive_callee (SUC (SUC fuel)) "cadopt"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_arith
  >> qexists `mk_inst 23 ADD [Var "cfmp"; Lit 1w] ["cadopt"]`
  >> simp[fmp_probe_callee_cfmp_fuel] >> EVAL_TAC
QED

Theorem fmp_probe_callee_adopted_rooted:
  fmp_value_rooted fmp_probe_sealed_ctx fmp_positive_callee_sig
    fmp_positive_callee "cadopt"
Proof
  rewrite_tac[fmp_value_rooted_def, cj 2 fmp_positive_defined_values_lengths]
  >> qspec_then `3` mp_tac fmp_probe_callee_adopted_fuel >> simp[]
QED

Theorem fmp_probe_callee_return_inst_wf:
  fmp_runner_inst_wf fmp_probe_sealed_ctx fmp_positive_callee_sig
    fmp_positive_callee
    (mk_inst 24 RET [Var "cu"; Var "cadopt"; Var "crpc"] [])
Proof
  simp[fmp_runner_inst_wf_def, fmp_bump_consumer_wf_def,
       fmp_invoke_consumer_wf_def, fmp_return_consumer_wf_def,
       venomInstTheory.mk_inst_def]
  >> strip_tac
  >> qexistsl [`1`, `"cadopt"`]
  >> simp[fmp_probe_callee_adopted_rooted]
  >> EVAL_TAC
QED

Theorem fmp_probe_sealed_callee_matches:
  fmp_signature_matches_fn fmp_probe_sealed_ctx fmp_positive_callee
Proof
  simp[fmp_signature_matches_fn_def, cj 2 fmp_positive_signature_fields,
       fmp_positive_callee_syntax_wf]
  >> rewrite_tac[fmp_runner_rooted_wf_def, fmp_positive_callee_insts]
  >> simp[fmp_probe_callee_return_inst_wf, fmp_runner_inst_wf_def,
          fmp_bump_consumer_wf_def, fmp_invoke_consumer_wf_def,
          fmp_return_consumer_wf_def, venomInstTheory.mk_inst_def]
QED

Theorem fmp_probe_sealed_ctx_functions:
  fmp_probe_sealed_ctx.ctx_functions =
    [fmp_probe_caller; fmp_positive_callee]
Proof
  EVAL_TAC
QED

Theorem fmp_probe_sealed_lookup:
  lookup_function "callee" fmp_probe_sealed_ctx.ctx_functions =
    SOME fmp_positive_callee
Proof
  EVAL_TAC
QED

Theorem fmp_probe_sealed_seed_eval:
  seed_fmp_context fmp_probe_sealed_ctx =
    SOME (FEMPTY |+ ("caller", fmp_probe_info_ff) |+
                  ("callee", fmp_probe_info_tt))
Proof
  simp[seed_fmp_context_def, fmp_probe_sealed_ctx_functions,
       fmp_seed_functions_def, fmp_seed_function_def,
       fmp_probe_caller_def, fmp_probe_raw_fn_def, fmp_probe_block_def,
       fmp_probe_invoke_def, fmp_function_targets_def,
       fmp_collect_invokes_def, fmp_invoke_target_def,
       fmp_resolve_targets_def, fmp_probe_sealed_lookup,
       fmp_probe_sealed_callee_matches]
  >> EVAL_TAC
QED

Theorem fmp_sealed_and_caller_propagation_eval:
  ?infos.
    analyze_fmp_context fmp_probe_sealed_ctx = SOME infos /\
    FLOOKUP infos "callee" = SOME fmp_probe_info_tt /\
    FLOOKUP infos "caller" = SOME fmp_probe_info_tt
Proof
  rewrite_tac[analyze_fmp_context_def, fmp_probe_sealed_seed_eval]
  >> EVAL_TAC
  >> qexists `FEMPTY |+ ("caller", fmp_probe_info_tt) |+
                       ("callee", fmp_probe_info_tt)`
  >> simp[finite_mapTheory.FLOOKUP_UPDATE, fmp_probe_info_tt_def]
QED

Definition fmp_probe_bad_sealed_ctx_def:
  fmp_probe_bad_sealed_ctx =
    mk_venom_context [fmp_probe_caller; fmp_hidden_mismatch_fn]
      (SOME "caller")
End

(* Mutating the current sealed layout/signature is observed and rejected. *)
Theorem fmp_sealed_mutation_rejected_eval:
  analyze_fmp_context fmp_probe_bad_sealed_ctx = NONE
Proof
  EVAL_TAC
QED

Definition fmp_probe_dangling_fn_def:
  fmp_probe_dangling_fn =
    fmp_probe_raw_fn "dangling" [fmp_probe_invoke 20 "missing"]
End

Definition fmp_probe_malformed_fn_def:
  fmp_probe_malformed_fn =
    fmp_probe_raw_fn "malformed" [mk_inst 21 INVOKE [Var "not_a_label"] []]
End

Theorem fmp_bad_invokes_rejected_eval:
  analyze_fmp_context
    (mk_venom_context [fmp_probe_dangling_fn] NONE) = NONE /\
  analyze_fmp_context
    (mk_venom_context [fmp_probe_malformed_fn] NONE) = NONE
Proof
  EVAL_TAC
QED

Definition fmp_probe_duplicate_ctx_def:
  fmp_probe_duplicate_ctx =
    mk_venom_context
      [fmp_probe_raw_fn "dup" []; fmp_probe_raw_fn "dup" []] NONE
End

Theorem fmp_duplicate_names_rejected_eval:
  analyze_fmp_context fmp_probe_duplicate_ctx = NONE
Proof
  EVAL_TAC
QED

(* Three functions are deliberately ordered caller-to-callee: an in-place
 * left fold could not propagate the leaf seed to top in one round. *)
Definition fmp_probe_leaf_def:
  fmp_probe_leaf =
    fmp_probe_raw_fn "leaf" [mk_inst 30 DALLOCA [Lit 32w] ["p"]]
End

Definition fmp_probe_mid_def:
  fmp_probe_mid = fmp_probe_raw_fn "mid" [fmp_probe_invoke 31 "leaf"]
End

Definition fmp_probe_top_def:
  fmp_probe_top = fmp_probe_raw_fn "top" [fmp_probe_invoke 32 "mid"]
End

Definition fmp_probe_chain_ctx_def:
  fmp_probe_chain_ctx =
    mk_venom_context [fmp_probe_top; fmp_probe_mid; fmp_probe_leaf] NONE
End

Theorem fmp_multihop_synchronous_eval:
  FLOOKUP (THE (analyze_fmp_context fmp_probe_chain_ctx)) "top" =
    SOME fmp_probe_info_tt
Proof
  EVAL_TAC
QED

Definition fmp_probe_cycle_a_def:
  fmp_probe_cycle_a seeded =
    fmp_probe_raw_fn "a"
      (fmp_probe_invoke 40 "b" ::
       if seeded then [mk_inst 41 GETFMP [] ["f"]] else [])
End

Definition fmp_probe_cycle_b_def:
  fmp_probe_cycle_b =
    fmp_probe_raw_fn "b" [fmp_probe_invoke 42 "a"]
End

Definition fmp_probe_cycle_ctx_def:
  fmp_probe_cycle_ctx seeded =
    mk_venom_context [fmp_probe_cycle_b; fmp_probe_cycle_a seeded] NONE
End

Theorem fmp_seeded_cycle_total_and_propagates_eval:
  ?infos.
    analyze_fmp_context (fmp_probe_cycle_ctx T) = SOME infos /\
    FLOOKUP infos "a" = SOME fmp_probe_info_tf /\
    FLOOKUP infos "b" = SOME fmp_probe_info_tf
Proof
  EVAL_TAC
  >> qexists `FEMPTY |+ ("b", fmp_probe_info_tf) |+
                       ("a", fmp_probe_info_tf)`
  >> simp[finite_mapTheory.FLOOKUP_UPDATE, fmp_probe_info_tf_def]
QED

Theorem fmp_seedless_cycle_total_and_bottom_eval:
  ?infos.
    analyze_fmp_context (fmp_probe_cycle_ctx F) = SOME infos /\
    FLOOKUP infos "a" = SOME fmp_probe_info_ff /\
    FLOOKUP infos "b" = SOME fmp_probe_info_ff
Proof
  EVAL_TAC
  >> qexists `FEMPTY |+ ("b", fmp_probe_info_ff) |+
                       ("a", fmp_probe_info_ff)`
  >> simp[finite_mapTheory.FLOOKUP_UPDATE, fmp_probe_info_ff_def]
QED

val _ = export_theory();
