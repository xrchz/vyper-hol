(* Executable boundary probes and structural properties for fresh FMP analysis. *)

Theory fmpAnalysisProps
Ancestors
  fmpAnalysisDefs
  fmpWfProps
  fmpWfDefs
  callLayoutDefs
  venomWf
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


(* ------------------------------------------------------------------------- *)
(* Generic seed and synchronous-step boundaries. *)

Theorem fmp_info_join_fields[simp]:
  (fmp_info_join x y).fi_needs_fmp =
    (x.fi_needs_fmp \/ y.fi_needs_fmp) /\
  (fmp_info_join x y).fi_publishes_fmp =
    (x.fi_publishes_fmp \/ y.fi_publishes_fmp)
Proof
  Cases_on `x` >> Cases_on `y` >> simp[fmp_info_join_def]
QED

Theorem fmp_join_target_info_fields_mono:
  !targets acc out.
    fmp_join_target_info infos targets acc = SOME out ==>
    (acc.fi_needs_fmp ==> out.fi_needs_fmp) /\
    (acc.fi_publishes_fmp ==> out.fi_publishes_fmp)
Proof
  Induct >> simp[fmp_join_target_info_def]
  >> rpt gen_tac
  >> Cases_on `FLOOKUP infos h` >> simp[]
  >> strip_tac
  >> first_x_assum
       (qspecl_then [`fmp_info_join acc x`, `out`] mp_tac)
  >> simp[]
QED

Theorem fmp_seed_function_own_lookup:
  fmp_seed_function ctx fn acc = SOME acc' ==>
  ?info. FLOOKUP acc' fn.fn_name = SOME info
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> Cases_on `fn.fn_fmp_signature` >> gvs[]
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_seed_function_preserves_lookup:
  fmp_seed_function ctx fn acc = SOME acc' /\
  FLOOKUP acc name = SOME info ==>
  FLOOKUP acc' name = SOME info
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> Cases_on `fn.fn_fmp_signature` >> gvs[]
  >> Cases_on `fn.fn_name = name` >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_seed_functions_preserves_lookup:
  !fns acc out name info.
    fmp_seed_functions ctx fns acc = SOME out /\
    FLOOKUP acc name = SOME info ==>
    FLOOKUP out name = SOME info
Proof
  Induct >> rw[fmp_seed_functions_def]
  >> Cases_on `fmp_seed_function ctx h acc` >> gvs[]
  >> first_x_assum irule
  >> metis_tac[fmp_seed_function_preserves_lookup]
QED

Theorem fmp_seed_functions_coverage:
  !fns acc out fn.
    fmp_seed_functions ctx fns acc = SOME out /\ MEM fn fns ==>
    ?info. FLOOKUP out fn.fn_name = SOME info
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> metis_tac[fmp_seed_function_own_lookup,
               fmp_seed_functions_preserves_lookup]
QED

Theorem seed_fmp_context_coverage:
  seed_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions ==>
  ?info. FLOOKUP infos fn.fn_name = SOME info
Proof
  simp[seed_fmp_context_def]
  >> metis_tac[fmp_seed_functions_coverage]
QED
Theorem fmp_seed_function_targets:
  fmp_seed_function ctx fn acc = SOME acc' ==>
  ?targets. fmp_function_targets ctx fn = SOME targets
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
QED

Theorem fmp_seed_functions_targets:
  !fns acc out fn.
    fmp_seed_functions ctx fns acc = SOME out /\ MEM fn fns ==>
    ?targets. fmp_function_targets ctx fn = SOME targets
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> metis_tac[fmp_seed_function_targets]
QED

Theorem seed_fmp_context_targets:
  seed_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions ==>
  ?targets. fmp_function_targets ctx fn = SOME targets
Proof
  simp[seed_fmp_context_def]
  >> metis_tac[fmp_seed_functions_targets]
QED

Theorem fmp_seed_function_sealed_lookup:
  fmp_seed_function ctx fn acc = SOME acc' /\
  fn.fn_fmp_signature = SOME sig ==>
  fmp_signature_matches_fn ctx fn /\
  FLOOKUP acc' fn.fn_name = SOME (fmp_info_of_signature sig)
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_seed_functions_sealed_lookup:
  !fns acc out fn sig.
    fmp_seed_functions ctx fns acc = SOME out /\ MEM fn fns /\
    fn.fn_fmp_signature = SOME sig ==>
    fmp_signature_matches_fn ctx fn /\
    FLOOKUP out fn.fn_name = SOME (fmp_info_of_signature sig)
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> metis_tac[fmp_seed_function_sealed_lookup,
               fmp_seed_functions_preserves_lookup]
QED
Theorem seed_fmp_context_sealed_lookup:
  seed_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = SOME sig ==>
  fmp_signature_matches_fn ctx fn /\
  FLOOKUP infos fn.fn_name = SOME (fmp_info_of_signature sig)
Proof
  simp[seed_fmp_context_def]
  >> metis_tac[fmp_seed_functions_sealed_lookup]
QED


Theorem fmp_seed_functions_existing_name_not_mem:
  !fns acc out name info.
    fmp_seed_functions ctx fns acc = SOME out /\
    FLOOKUP acc name = SOME info ==>
    !fn. MEM fn fns ==> fn.fn_name <> name
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> strip_tac
  >> gen_tac >> strip_tac
  >> Cases_on `fn = h`
  >- (strip_tac >> gvs[fmp_seed_function_def])
  >> gvs[]
  >> `FLOOKUP x name = SOME info` by
       metis_tac[fmp_seed_function_preserves_lookup]
  >> first_x_assum (qspecl_then [`x`, `out`, `name`, `info`] mp_tac)
  >> simp[]
QED
Theorem fmp_seed_functions_distinct:
  !fns acc out.
    fmp_seed_functions ctx fns acc = SOME out ==>
    ALL_DISTINCT (MAP (\fn. fn.fn_name) fns)
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> strip_tac
  >> conj_tac
  >- (drule fmp_seed_function_own_lookup
      >> strip_tac
      >> qspecl_then [`fns`, `x`, `out`, `h.fn_name`, `info`] mp_tac
           fmp_seed_functions_existing_name_not_mem
      >> simp[listTheory.MEM_MAP]
      >> metis_tac[])
  >> first_x_assum (qspecl_then [`x`, `out`] mp_tac) >> simp[]
QED

Theorem seed_fmp_context_distinct:
  seed_fmp_context ctx = SOME infos ==> ctx_distinct_fn_names ctx
Proof
  simp[seed_fmp_context_def, ctx_distinct_fn_names_def, ctx_fn_names_def]
  >> metis_tac[fmp_seed_functions_distinct]
QED

Theorem fmp_step_functions_preserves_other_lookup:
  !fns fresh out name info.
    EVERY (\fn. fn.fn_name <> name) fns /\
    FLOOKUP fresh name = SOME info /\
    fmp_step_functions ctx old fns fresh = SOME out ==>
    FLOOKUP out name = SOME info
Proof
  Induct >> simp[fmp_step_functions_def]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_step_function ctx old h` >> gvs[]
  >> first_x_assum
       (qspecl_then [`fresh |+ (h.fn_name,x)`, `out`, `name`, `info`] mp_tac)
  >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_step_functions_lookup:
  !fns fresh out fn.
    ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\ MEM fn fns /\
    fmp_step_functions ctx old fns fresh = SOME out ==>
    ?info.
      fmp_step_function ctx old fn = SOME info /\
      FLOOKUP out fn.fn_name = SOME info
Proof
  Induct >> simp[fmp_step_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_step_function ctx old h` >> simp[]
  >> strip_tac
  >- (qexists `x` >> simp[]
      >> qspecl_then
           [`fns`, `fresh |+ (h.fn_name,x)`, `out`, `h.fn_name`, `x`]
           mp_tac fmp_step_functions_preserves_other_lookup
      >> simp[finite_mapTheory.FLOOKUP_UPDATE, listTheory.EVERY_MEM]
      >> disch_then irule
      >> simp[listTheory.EVERY_MEM]
      >> metis_tac[listTheory.MEM_MAP])
  >> first_x_assum
       (qspecl_then [`fresh |+ (h.fn_name,x)`, `out`, `fn`] mp_tac)
  >> simp[]
QED

Theorem fmp_context_step_lookup:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fmp_context_step ctx old = SOME out ==>
  ?info.
    fmp_step_function ctx old fn = SOME info /\
    FLOOKUP out fn.fn_name = SOME info
Proof
  simp[fmp_context_step_def, ctx_distinct_fn_names_def, ctx_fn_names_def]
  >> metis_tac[fmp_step_functions_lookup]
QED

Theorem fmp_context_step_coverage:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fmp_context_step ctx old = SOME out ==>
  ?info. FLOOKUP out fn.fn_name = SOME info
Proof
  metis_tac[fmp_context_step_lookup]
QED

Theorem fmp_context_step_sealed_lookup:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = SOME sig /\
  fmp_context_step ctx old = SOME out ==>
  FLOOKUP out fn.fn_name = FLOOKUP old fn.fn_name
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_lookup
  >> strip_tac
  >> Cases_on `FLOOKUP old fn.fn_name`
  >> gvs[fmp_step_function_def]
QED

Theorem fmp_context_step_unsealed_lookup:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out ==>
  ?old_info targets info.
    FLOOKUP old fn.fn_name = SOME old_info /\
    fmp_function_targets ctx fn = SOME targets /\
    fmp_join_target_info old targets
      (fmp_info_join old_info (fmp_direct_info fn)) = SOME info /\
    FLOOKUP out fn.fn_name = SOME info
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_lookup
  >> simp[fmp_step_function_def]
  >> Cases_on `FLOOKUP old fn.fn_name` >> simp[]
  >> Cases_on `fmp_function_targets ctx fn` >> simp[]
  >> metis_tac[]
QED
Theorem fmp_context_step_unsealed_old_fields_mono:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out /\
  FLOOKUP old fn.fn_name = SOME old_info /\
  FLOOKUP out fn.fn_name = SOME info ==>
  (old_info.fi_needs_fmp ==> info.fi_needs_fmp) /\
  (old_info.fi_publishes_fmp ==> info.fi_publishes_fmp)
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_unsealed_lookup
  >> strip_tac
  >> gvs[]
  >> drule fmp_join_target_info_fields_mono
  >> simp[]
QED

Theorem fmp_context_step_unsealed_direct_fields:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out /\
  FLOOKUP out fn.fn_name = SOME info ==>
  ((fmp_direct_info fn).fi_needs_fmp ==> info.fi_needs_fmp) /\
  ((fmp_direct_info fn).fi_publishes_fmp ==> info.fi_publishes_fmp)
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_unsealed_lookup
  >> strip_tac
  >> gvs[]
  >> drule fmp_join_target_info_fields_mono
  >> simp[]
QED


(* ------------------------------------------------------------------------- *)
(* Bounded-round invariants and the public analysis contract. *)

Theorem fmp_option_step_none_funpow[simp]:
  !n. FUNPOW (fmp_option_step ctx) n NONE = NONE
Proof
  Induct >> simp[arithmeticTheory.FUNPOW, fmp_option_step_def]
QED

Theorem analyze_fmp_context_seeded:
  analyze_fmp_context ctx = SOME infos ==>
  ?seed. seed_fmp_context ctx = SOME seed
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
QED

Theorem analyze_fmp_context_distinct:
  analyze_fmp_context ctx = SOME infos ==>
  ctx_distinct_fn_names ctx
Proof
  metis_tac[analyze_fmp_context_seeded, seed_fmp_context_distinct]
QED

Theorem fmp_option_rounds_coverage:
  !n old out.
    ctx_distinct_fn_names ctx /\
    (!fn. MEM fn ctx.ctx_functions ==>
      ?info. FLOOKUP old fn.fn_name = SOME info) /\
    FUNPOW (fmp_option_step ctx) n (SOME old) = SOME out ==>
    !fn. MEM fn ctx.ctx_functions ==>
      ?info. FLOOKUP out fn.fn_name = SOME info
Proof
  Induct
  >- simp[arithmeticTheory.FUNPOW]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_context_step ctx old`
  >> gvs[arithmeticTheory.FUNPOW, fmp_option_step_def]
  >> first_x_assum (qspecl_then [`x`, `out`] mp_tac)
  >> metis_tac[fmp_context_step_coverage]
QED

Theorem fmp_option_rounds_sealed_lookup:
  !n old out.
    ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
    fn.fn_fmp_signature = SOME sig /\
    FUNPOW (fmp_option_step ctx) n (SOME old) = SOME out ==>
    FLOOKUP out fn.fn_name = FLOOKUP old fn.fn_name
Proof
  Induct
  >- simp[arithmeticTheory.FUNPOW]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_context_step ctx old`
  >> gvs[arithmeticTheory.FUNPOW, fmp_option_step_def]
  >> first_x_assum (qspecl_then [`x`, `out`] mp_tac)
  >> metis_tac[fmp_context_step_sealed_lookup]
QED

Theorem analyze_fmp_context_coverage:
  analyze_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions ==>
  ?info. FLOOKUP infos fn.fn_name = SOME info
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
  >> metis_tac[seed_fmp_context_distinct, seed_fmp_context_coverage,
               fmp_option_rounds_coverage]
QED

Theorem analyze_fmp_context_sealed_lookup:
  analyze_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = SOME sig ==>
  fmp_signature_matches_fn ctx fn /\
  FLOOKUP infos fn.fn_name = SOME (fmp_info_of_signature sig)
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
  >> metis_tac[seed_fmp_context_distinct, seed_fmp_context_sealed_lookup,
               fmp_option_rounds_sealed_lookup]
QED

Theorem fmp_option_rounds_unsealed_old_fields_mono:
  !n old out old_info info.
    ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
    fn.fn_fmp_signature = NONE /\
    FLOOKUP old fn.fn_name = SOME old_info /\
    FUNPOW (fmp_option_step ctx) n (SOME old) = SOME out /\
    FLOOKUP out fn.fn_name = SOME info ==>
    (old_info.fi_needs_fmp ==> info.fi_needs_fmp) /\
    (old_info.fi_publishes_fmp ==> info.fi_publishes_fmp)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[arithmeticTheory.FUNPOW])
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_context_step ctx old`
  >> gvs[arithmeticTheory.FUNPOW, fmp_option_step_def]
  >> metis_tac[fmp_context_step_coverage,
               fmp_context_step_unsealed_old_fields_mono]
QED

Theorem fmp_seed_function_unsealed_lookup:
  fmp_seed_function ctx fn acc = SOME acc' /\
  fn.fn_fmp_signature = NONE ==>
  FLOOKUP acc' fn.fn_name = SOME (fmp_direct_info fn)
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_seed_functions_unsealed_lookup:
  !fns acc out fn.
    fmp_seed_functions ctx fns acc = SOME out /\ MEM fn fns /\
    fn.fn_fmp_signature = NONE ==>
    FLOOKUP out fn.fn_name = SOME (fmp_direct_info fn)
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> metis_tac[fmp_seed_function_unsealed_lookup,
               fmp_seed_functions_preserves_lookup]
QED

Theorem seed_fmp_context_unsealed_lookup:
  seed_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE ==>
  FLOOKUP infos fn.fn_name = SOME (fmp_direct_info fn)
Proof
  simp[seed_fmp_context_def]
  >> metis_tac[fmp_seed_functions_unsealed_lookup]
QED

Theorem analyze_fmp_context_unsealed_direct_fields:
  analyze_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  FLOOKUP infos fn.fn_name = SOME info ==>
  ((fmp_direct_info fn).fi_needs_fmp ==> info.fi_needs_fmp) /\
  ((fmp_direct_info fn).fi_publishes_fmp ==> info.fi_publishes_fmp)
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
  >> metis_tac[seed_fmp_context_distinct,
               seed_fmp_context_unsealed_lookup,
               fmp_option_rounds_unsealed_old_fields_mono]
QED

Theorem fmp_join_target_info_needs_iff:
  !targets acc out.
    fmp_join_target_info infos targets acc = SOME out ==>
    (out.fi_needs_fmp <=>
       acc.fi_needs_fmp \/
       ?name info. MEM name targets /\
         FLOOKUP infos name = SOME info /\ info.fi_needs_fmp)
Proof
  Induct >> simp[fmp_join_target_info_def]
  >> rpt gen_tac
  >> Cases_on `FLOOKUP infos h` >> simp[]
  >> strip_tac
  >> first_x_assum
       (qspecl_then [`fmp_info_join acc x`, `out`] mp_tac)
  >> simp[]
  >> disch_then (fn th => rewrite_tac[th])
  >> eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_join_target_info_publishes_iff:
  !targets acc out.
    fmp_join_target_info infos targets acc = SOME out ==>
    (out.fi_publishes_fmp <=>
       acc.fi_publishes_fmp \/
       ?name info. MEM name targets /\
         FLOOKUP infos name = SOME info /\ info.fi_publishes_fmp)
Proof
  Induct >> simp[fmp_join_target_info_def]
  >> rpt gen_tac
  >> Cases_on `FLOOKUP infos h` >> simp[]
  >> strip_tac
  >> first_x_assum
       (qspecl_then [`fmp_info_join acc x`, `out`] mp_tac)
  >> simp[]
  >> disch_then (fn th => rewrite_tac[th])
  >> eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Definition fmp_unsealed_calls_def:
  fmp_unsealed_calls ctx caller callee <=>
    MEM caller ctx.ctx_functions /\
    caller.fn_fmp_signature = NONE /\
    MEM callee ctx.ctx_functions /\
    ?targets. fmp_function_targets ctx caller = SOME targets /\
              MEM callee.fn_name targets
End

Definition fmp_needs_source_def:
  fmp_needs_source fn <=>
    case fn.fn_fmp_signature of
      SOME sig => (fmp_info_of_signature sig).fi_needs_fmp
    | NONE => (fmp_direct_info fn).fi_needs_fmp
End

Definition fmp_publishes_source_def:
  fmp_publishes_source fn <=>
    case fn.fn_fmp_signature of
      SOME sig => (fmp_info_of_signature sig).fi_publishes_fmp
    | NONE => (fmp_direct_info fn).fi_publishes_fmp
End

Theorem fmp_resolve_targets_lookup:
  !targets name.
    fmp_resolve_targets ctx targets /\ MEM name targets ==>
    ?fn. lookup_function name ctx.ctx_functions = SOME fn
Proof
  Induct >> simp[fmp_resolve_targets_def]
  >> rpt gen_tac >> strip_tac
  >> gvs[]
  >> Cases_on `lookup_function h ctx.ctx_functions` >> gvs[]
  >> metis_tac[]
QED

Theorem fmp_function_targets_lookup:
  fmp_function_targets ctx caller = SOME targets /\ MEM name targets ==>
  ?callee. lookup_function name ctx.ctx_functions = SOME callee
Proof
  rw[fmp_function_targets_def]
  >> Cases_on `fmp_collect_invokes (fn_insts caller)` >> gvs[]
  >> metis_tac[fmp_resolve_targets_lookup]
QED

Theorem seed_fmp_context_needs_source:
  seed_fmp_context ctx = SOME seed /\ MEM fn ctx.ctx_functions /\
  FLOOKUP seed fn.fn_name = SOME info ==>
  (info.fi_needs_fmp <=> fmp_needs_source fn)
Proof
  Cases_on `fn.fn_fmp_signature`
  >- (simp[fmp_needs_source_def] >> strip_tac
      >> drule_all seed_fmp_context_unsealed_lookup >> gvs[])
  >> simp[fmp_needs_source_def] >> strip_tac
  >> drule_all seed_fmp_context_sealed_lookup >> gvs[]
QED

Theorem seed_fmp_context_publishes_source:
  seed_fmp_context ctx = SOME seed /\ MEM fn ctx.ctx_functions /\
  FLOOKUP seed fn.fn_name = SOME info ==>
  (info.fi_publishes_fmp <=> fmp_publishes_source fn)
Proof
  Cases_on `fn.fn_fmp_signature`
  >- (simp[fmp_publishes_source_def] >> strip_tac
      >> drule_all seed_fmp_context_unsealed_lookup >> gvs[])
  >> simp[fmp_publishes_source_def] >> strip_tac
  >> drule_all seed_fmp_context_sealed_lookup >> gvs[]
QED

Theorem lookup_function_name:
  !name fns fn.
    lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct_on `fns` >> rw[lookup_function_def, listTheory.FIND_thm]
  >> gvs[lookup_function_def]
QED

Theorem fmp_target_name_callee:
  fmp_function_targets ctx caller = SOME targets /\ MEM name targets ==>
  ?callee. MEM callee ctx.ctx_functions /\ callee.fn_name = name
Proof
  strip_tac
  >> drule_all fmp_function_targets_lookup
  >> strip_tac
  >> qexists `callee`
  >> metis_tac[lookup_function_MEM, lookup_function_name]
QED

Theorem fmp_target_needs_exists:
  MEM caller ctx.ctx_functions /\ caller.fn_fmp_signature = NONE /\
  fmp_function_targets ctx caller = SOME targets ==>
  ((?name info. MEM name targets /\ FLOOKUP old name = SOME info /\
                 info.fi_needs_fmp) <=>
   ?callee info. fmp_unsealed_calls ctx caller callee /\
     FLOOKUP old callee.fn_name = SOME info /\ info.fi_needs_fmp)
Proof
  strip_tac >> eq_tac
  >- (strip_tac
      >> drule_all fmp_target_name_callee >> strip_tac
      >> qexistsl [`callee`, `info`]
      >> simp[fmp_unsealed_calls_def] >> metis_tac[])
  >> strip_tac >> gvs[fmp_unsealed_calls_def]
  >> qexistsl [`callee.fn_name`, `info`] >> metis_tac[]
QED

Theorem fmp_target_publishes_exists:
  MEM caller ctx.ctx_functions /\ caller.fn_fmp_signature = NONE /\
  fmp_function_targets ctx caller = SOME targets ==>
  ((?name info. MEM name targets /\ FLOOKUP old name = SOME info /\
                 info.fi_publishes_fmp) <=>
   ?callee info. fmp_unsealed_calls ctx caller callee /\
     FLOOKUP old callee.fn_name = SOME info /\ info.fi_publishes_fmp)
Proof
  strip_tac >> eq_tac
  >- (strip_tac
      >> drule_all fmp_target_name_callee >> strip_tac
      >> qexistsl [`callee`, `info`]
      >> simp[fmp_unsealed_calls_def] >> metis_tac[])
  >> strip_tac >> gvs[fmp_unsealed_calls_def]
  >> qexistsl [`callee.fn_name`, `info`] >> metis_tac[]
QED

Theorem fmp_context_step_unsealed_needs_iff:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out /\
  FLOOKUP old fn.fn_name = SOME old_info /\
  FLOOKUP out fn.fn_name = SOME info ==>
  (info.fi_needs_fmp <=>
    old_info.fi_needs_fmp \/ (fmp_direct_info fn).fi_needs_fmp \/
    ?callee callee_info. fmp_unsealed_calls ctx fn callee /\
      FLOOKUP old callee.fn_name = SOME callee_info /\
      callee_info.fi_needs_fmp)
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_unsealed_lookup
  >> strip_tac >> gvs[]
  >> drule fmp_join_target_info_needs_iff >> simp[]
  >> disch_then (fn th => once_rewrite_tac[th])
  >> drule_all fmp_target_needs_exists
  >> strip_tac
  >> first_x_assum (qspec_then `old` mp_tac)
  >> strip_tac >> metis_tac[]
QED

Theorem fmp_context_step_unsealed_publishes_iff:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out /\
  FLOOKUP old fn.fn_name = SOME old_info /\
  FLOOKUP out fn.fn_name = SOME info ==>
  (info.fi_publishes_fmp <=>
    old_info.fi_publishes_fmp \/ (fmp_direct_info fn).fi_publishes_fmp \/
    ?callee callee_info. fmp_unsealed_calls ctx fn callee /\
      FLOOKUP old callee.fn_name = SOME callee_info /\
      callee_info.fi_publishes_fmp)
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_unsealed_lookup
  >> strip_tac >> gvs[]
  >> drule fmp_join_target_info_publishes_iff >> simp[]
  >> disch_then (fn th => once_rewrite_tac[th])
  >> drule_all fmp_target_publishes_exists
  >> strip_tac
  >> first_x_assum (qspec_then `old` mp_tac)
  >> strip_tac >> metis_tac[]
QED

Definition fmp_reaches_in_def:
  (fmp_reaches_in ctx 0 caller source <=> caller = source) /\
  (fmp_reaches_in ctx (SUC n) caller source <=>
     caller = source \/
     ?callee. fmp_unsealed_calls ctx caller callee /\
              fmp_reaches_in ctx n callee source)
End

Theorem fmp_reaches_in_mono:
  !n caller source.
    fmp_reaches_in ctx n caller source ==>
    fmp_reaches_in ctx (SUC n) caller source
Proof
  Induct
  >- simp[fmp_reaches_in_def]
  >> rpt gen_tac
  >> pure_rewrite_tac[fmp_reaches_in_def]
  >> strip_tac
  >- simp[]
  >> disj2_tac
  >> qexists `callee`
  >> simp[]
  >> first_x_assum (qspecl_then [`callee`, `source`] mp_tac)
  >> simp[fmp_reaches_in_def]
QED

Theorem fmp_reaches_in_carrier:
  !n caller source.
    MEM caller ctx.ctx_functions /\ fmp_reaches_in ctx n caller source ==>
    MEM source ctx.ctx_functions
Proof
  Induct >> simp[fmp_reaches_in_def, fmp_unsealed_calls_def]
  >> metis_tac[]
QED

val _ = export_theory();
