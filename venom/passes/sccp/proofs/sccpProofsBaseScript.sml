(*
 * SCCP — Counterexample for the original theorem statement.
 *
 * The frozen theorem statement:
 *   !fuel ctx fn fn' s.
 *     ssa_form fn /\ sccp_function fn = SOME fn' ==>
 *     lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
 *       (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' s)
 *
 * is FALSE. This file contains a machine-checked counterexample.
 *
 * Counterexample:
 *   fn  = ir_function "test_fn"
 *           [basic_block "entry" [ASSERT(Lit 1w), STOP]]
 *   fn' = sccp_function fn
 *       = SOME (fn with block "entry" = [STOP])
 *         (ASSERT(Lit 1w) becomes NOP under SCCP, clear_nops removes it)
 *   s   = init_venom_state "entry" with
 *           <|vs_inst_idx := 1; vs_current_bb := "entry"|>
 *   fuel = 1, ctx = ARB
 *
 * With vs_inst_idx = 1:
 *   - fn has 2 instructions, index 1 = STOP => Halt
 *   - fn' has 1 instruction, index 1 out of bounds => Error
 *   - lift_result _ _ (Halt _) (Error _) = F
 *
 * Tightest fix: add s.vs_inst_idx = 0, fn_entry_label fn = SOME s.vs_current_bb,
 * wf_function fn, fn_inst_wf fn, and the error disjunction (?e. ... = Error e) \/.
 *)

Theory sccpProofsBase
Ancestors
  sccpDefs sccpSound sccpConvergence
  analysisSimDefs analysisSimProps analysisSimProofsBase
  passSimulationDefs passSimulationProps
  venomWf venomExecSemantics venomInst venomInstProps venomExecProps venomState
  dfAnalyzeDefs dfAnalyzeProps
  cfgAnalysisProps cfgDefs
  passSharedDefs passSharedProps
  stateEquiv stateEquivProps
  execEquivParamBase execEquivParamProps
  finite_map worklistDefs worklistProps
  list
Libs
  pairLib BasicProvers

(* ===== Counterexample infrastructure ===== *)

(* The counterexample function *)
Definition cx_fn_def:
  cx_fn = mk_raw_function "test_fn"
    [basic_block "entry"
       [instruction 0 ASSERT [Lit 1w] [];
        instruction 1 STOP [] []]]
End

(* DFS walks on the single-block CFG — needed because EVAL can't
   handle the mutually recursive dfs_*_walk definitions *)
Triviality cx_dfs_post[local]:
  dfs_post_walk (FEMPTY |+ ("entry", []:(string list))) [] "entry" =
    (["entry"], ["entry"])
Proof
  ONCE_REWRITE_TAC [dfs_post_walk_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  simp[set_insert_def, fmap_lookup_list_def] >>
  CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) >>
  simp[FLOOKUP_UPDATE] >>
  ONCE_REWRITE_TAC [dfs_post_walk_def] >> simp[]
QED

Triviality cx_dfs_pre[local]:
  dfs_pre_walk (FEMPTY |+ ("entry", []:(string list))) [] "entry" =
    (["entry"], ["entry"])
Proof
  ONCE_REWRITE_TAC [dfs_pre_walk_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  simp[set_insert_def, fmap_lookup_list_def] >>
  CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) >>
  simp[FLOOKUP_UPDATE] >>
  ONCE_REWRITE_TAC [dfs_pre_walk_def] >> simp[]
QED

(* cfg_analyze for the counterexample function *)
Triviality cx_cfg[local]:
  cfg_analyze cx_fn =
    <| cfg_succs := FEMPTY |+ ("entry", []:string list) |+ ("entry", []);
       cfg_preds := FEMPTY |+ ("entry", []:string list);
       cfg_reachable := FEMPTY |+ ("entry", T);
       cfg_dfs_post := ["entry"];
       cfg_dfs_pre := ["entry"] |>
Proof
  simp[cfg_analyze_def, cx_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) >>
  (* build_succs, build_preds reduce by EVAL *)
  CONV_TAC (RATOR_CONV (RAND_CONV EVAL)) >>
  simp[] >>
  (* dfs walks need manual unfolding *)
  REWRITE_TAC [cx_dfs_post, cx_dfs_pre] >> simp[] >>
  EVAL_TAC >> simp[] >>
  REWRITE_TAC [cx_dfs_post, cx_dfs_pre] >> simp[]
QED

(* Helper: wl_step on the concrete initial state *)
Triviality cx_wl_step[local]:
  wl_step
    (\lbl old new.
       df_boundary <|sl_vals := FEMPTY; sl_targets := {} |> new lbl <>
       df_boundary <|sl_vals := FEMPTY; sl_targets := {} |> old lbl)
    (df_process_block Forward <|sl_vals := FEMPTY; sl_targets := {} |>
      sccp_join sccp_transfer_inst sccp_edge_transfer
      (mk_raw_function "test_fn"
        [basic_block "entry"
          [instruction 0 ASSERT [Lit 1w] []; instruction 1 STOP [] []]])
      (SOME ("entry", <|sl_vals := FEMPTY; sl_targets := {} |>))
      <| cfg_succs := FEMPTY |+ ("entry", []:string list);
         cfg_preds := FEMPTY |+ ("entry", []:string list);
         cfg_reachable := FEMPTY |+ ("entry", T);
         cfg_dfs_post := ["entry"]; cfg_dfs_pre := ["entry"] |>
      [basic_block "entry"
        [instruction 0 ASSERT [Lit 1w] []; instruction 1 STOP [] []]])
    (cfg_succs_of
      <| cfg_succs := FEMPTY |+ ("entry", []:string list);
         cfg_preds := FEMPTY |+ ("entry", []:string list);
         cfg_reachable := FEMPTY |+ ("entry", T);
         cfg_dfs_post := ["entry"]; cfg_dfs_pre := ["entry"] |>)
    (["entry"],
     <|ds_inst := FEMPTY;
       ds_boundary :=
         FEMPTY |+ ("entry", <|sl_vals := FEMPTY; sl_targets := {} |>) |>) =
  ([],
   <|ds_inst := FEMPTY;
     ds_boundary :=
       FEMPTY |+ ("entry", <|sl_vals := FEMPTY; sl_targets := {} |>) |>)
Proof
  EVAL_TAC >> simp[FUN_FMAP_EMPTY, FUNION_FEMPTY_2]
QED

(* The key computation: sccp_function on the counterexample *)
Triviality cx_sccp_function[local]:
  sccp_function cx_fn = SOME
    (cx_fn with fn_blocks :=
      [basic_block "entry"
        [instruction 0 ASSERT [Lit 1w] []; instruction 1 STOP [] []]
       with bb_instructions :=
        [instruction 1 STOP [] [] with inst_operands := []]])
Proof
  simp[sccp_function_def, LET_THM] >>
  simp[sccp_df_analyze_def, cx_fn_def, df_analyze_def, cx_cfg,
       init_df_state_def, sccp_bottom_def,
       fn_entry_label_def, entry_block_def] >>
  CONV_TAC (DEPTH_CONV (PairRules.PBETA_CONV)) >>
  simp[] >>
  (* Unfold wl_iterate to WHILE, then unfold WHILE once *)
  simp[wl_iterate_def] >>
  ONCE_REWRITE_TAC [DB.fetch "While" "WHILE"] >> simp[] >>
  (* Rewrite the wl_step body with our pre-computed result *)
  REWRITE_TAC [cx_wl_step] >>
  (* Worklist is empty, unfold WHILE again to terminate *)
  ONCE_REWRITE_TAC [DB.fetch "While" "WHILE"] >> simp[] >>
  (* sccp_has_static_assertion_failure check *)
  (conj_tac >- (
    EVAL_TAC >> simp[] >>
    rpt strip_tac >> Cases_on `idx` >> fs[] >> Cases_on `n` >> fs[])) >>
  (* analysis_function_transform + clear_nops *)
  EVAL_TAC >> simp[]
QED

(* SSA form for the counterexample *)
Triviality cx_ssa[local]:
  ssa_form cx_fn
Proof
  simp[ssa_form_def, cx_fn_def] >> EVAL_TAC >> simp[] >>
  rpt strip_tac >> gvs[]
QED

(* ===== THE COUNTEREXAMPLE ===== *)

(* The frozen theorem statement WAS false due to missing vs_inst_idx=0
   precondition. After run_block/run_function refactoring, run_blocks now
   internally resets vs_inst_idx := 0 via exec_block wrapper, so the
   counterexample (which used vs_inst_idx := 1) no longer applies.
   The original statement may now be provable without the precondition. *)
(*
Theorem sccp_function_correct_proof_false:
  ~!fuel ctx fn fn' s.
    ssa_form fn /\ sccp_function fn = SOME fn' ==>
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' s)
Proof
  simp[] >>
  qexists_tac `SUC 0` >>
  qexists_tac `ARB` >>
  qexists_tac `cx_fn` >>
  simp[cx_sccp_function, cx_ssa] >>
  qexists_tac `(init_venom_state "entry") with
    <|vs_inst_idx := 1; vs_current_bb := "entry"; vs_halted := F|>` >>
  simp[lift_result_def] >>
  EVAL_TAC
QED
*)

(* ================================================================
   SCCP Correctness Proof
   ================================================================

   Architecture:
   - const_sound(lat, s): every CL_Const in lat matches s
   - Under wf_ssa, use fuel induction carrying const_sound
   - Cross-block via cond_const_sound (conditional on x in FDOM)
   - Per-block simulation from sccp_inst_simulates
   ================================================================ *)

(* ===== const_sound helpers ===== *)

Triviality const_meet_CL_Const:
  !x y c. const_meet x y = CL_Const c ==>
    (x = CL_Const c \/ y = CL_Const c)
Proof
  Cases >> Cases >> simp[const_meet_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality const_sound_FLOOKUP:
  !st s v c. const_sound st s /\ FLOOKUP st v = SOME (CL_Const c) ==>
    FLOOKUP s.vs_vars v = SOME c
Proof
  rw[const_sound_def]
QED

Triviality const_sound_sccp_join[local]:
  !a b s.
    const_sound a.sl_vals s /\ const_sound b.sl_vals s ==>
    const_sound (sccp_join a b).sl_vals s
Proof
  rpt strip_tac >>
  rw[const_sound_def, sccp_join_def, LET_THM] >>
  `FINITE (FDOM a.sl_vals UNION FDOM b.sl_vals)` by simp[] >>
  `v IN FDOM a.sl_vals UNION FDOM b.sl_vals` by
    (spose_not_then strip_assume_tac >> fs[FUN_FMAP_DEF, flookup_thm]) >>
  gvs[FUN_FMAP_DEF, flookup_thm, const_lookup_def] >>
  Cases_on `FLOOKUP a.sl_vals v` >> Cases_on `FLOOKUP b.sl_vals v` >>
  gvs[const_meet_def] >>
  imp_res_tac const_meet_CL_Const >> gvs[] >>
  imp_res_tac const_sound_FLOOKUP >> gvs[flookup_thm]
QED

(* const_sound of FOLDL sccp_join when all elements are sound *)
Triviality const_sound_foldl_sccp_join[local]:
  !vals acc s.
    const_sound acc.sl_vals s /\
    EVERY (\v. const_sound v.sl_vals s) vals ==>
    const_sound (FOLDL sccp_join acc vals).sl_vals s
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  irule const_sound_sccp_join >> simp[]
QED

(* ===== Fixpoint helpers ===== *)

(* Forward-specialized fixpoint/transfer theorems *)
val intra_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzePropsTheory.df_at_intra_transfer));

val boundary_fixpoint_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzePropsTheory.df_boundary_fixpoint));

val inter_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzePropsTheory.df_at_inter_transfer));

val _ = delsimps ["is_fixpoint_def"];

val sccp_unfold = SIMP_RULE (srw_ss()) [LET_THM] sccp_df_analyze_def;
val sccp_refold = GSYM sccp_unfold;

(* Partially specialize framework theorems for SCCP lattice *)
val sccp_intra = ISPECL [``sccp_bottom``, ``sccp_join``, ``sccp_transfer_inst``,
  ``sccp_edge_transfer``] intra_fwd;
val sccp_bdry = ISPECL [``sccp_bottom``, ``sccp_join``, ``sccp_transfer_inst``,
  ``sccp_edge_transfer``] boundary_fixpoint_fwd;

val fixpoint_restricted_fwd = SIMP_RULE (srw_ss()) []
  (Q.SPEC `Forward` (SIMP_RULE (srw_ss()) [LET_THM]
    dfAnalyzeProofsTheory.df_analyze_fixpoint_process_restricted));

(* SCCP is_fixpoint *)
Triviality sccp_is_fixpoint[local]:
  !fn. wf_function fn ==>
    is_fixpoint
      (df_process_block Forward sccp_bottom sccp_join sccp_transfer_inst
         sccp_edge_transfer fn
         (OPTION_MAP (\lbl. (lbl, sccp_bottom)) (fn_entry_label fn))
         (cfg_analyze fn) fn.fn_blocks)
      (cfg_analyze fn).cfg_dfs_pre
      (sccp_df_analyze fn)
Proof
  gen_tac >> strip_tac >>
  simp[sccp_df_analyze_def] >>
  irule fixpoint_restricted_fwd >>
  conj_tac
  >- (
    qexistsl_tac [
      `sccp_measure_inv fn`,
      `sccp_measure_bound fn`,
      `sccp_measure fn`,
      `\lbl. MEM lbl (cfg_analyze fn).cfg_dfs_pre`] >>
    rpt conj_tac
    >- ((* bounded *)
        rpt strip_tac >>
        `sccp_state_inv fn x` by fs[sccpConvergenceTheory.sccp_measure_inv_def] >>
        metis_tac[sccpConvergenceTheory.sccp_measure_bounded])
    >- metis_tac[sccpConvergenceTheory.sccp_measure_inv_preserved]
    >- metis_tac[sccpConvergenceTheory.sccp_measure_monotone, MEM_APPEND]
    >- metis_tac[analysisSimProofsTheory.cfg_dfs_pre_succs_closed]
    >- simp[listTheory.EVERY_MEM]
    >- (mp_tac (Q.SPEC `fn` sccpConvergenceTheory.sccp_measure_inv_initial) >>
        Cases_on `fn_entry_label fn` >> simp[]))
  >>
  (* wl_deps_complete *)
  match_mp_tac (SIMP_RULE std_ss [LET_THM]
    dfAnalyzeProofsTheory.df_process_deps_complete_proof |>
    SPEC ``Forward : direction`` |>
    SIMP_RULE std_ss [dfAnalyzeDefsTheory.direction_case_def]) >>
  rw[sccpConvergenceTheory.sccp_join_absorption] >>
  metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]
QED

(* At the dataflow fixpoint, each intra-block transfer step equals
   sccp_transfer_inst applied to the instruction and prior lattice state.
   Requires wf_function and label in cfg_dfs_pre. *)
Theorem sccp_intra_fwd:
  !fn lbl bb idx.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    SUC idx <= LENGTH bb.bb_instructions ==>
    df_at sccp_bottom (sccp_df_analyze fn) lbl (SUC idx) =
      sccp_transfer_inst fn (EL idx bb.bb_instructions)
        (df_at sccp_bottom (sccp_df_analyze fn) lbl idx)
Proof
  rpt strip_tac >>
  simp[SIMP_RULE (srw_ss()) [LET_THM] sccp_df_analyze_def] >>
  irule sccp_intra >>
  simp[GSYM (SIMP_RULE (srw_ss()) [LET_THM] sccp_df_analyze_def),
       sccp_is_fixpoint]
QED

(* Inter-block transfer at fixpoint for SCCP *)
Triviality sccp_inter_fwd[local]:
  !fn lbl bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    df_at sccp_bottom (sccp_df_analyze fn) lbl 0 =
      sccp_joined fn (sccp_df_analyze fn) lbl
Proof
  rpt strip_tac >>
  simp[sccp_unfold] >>
  mp_tac (ISPECL [``sccp_bottom``, ``sccp_join``, ``sccp_transfer_inst``,
    ``sccp_edge_transfer``] inter_fwd) >>
  disch_then (qspecl_then [`fn`, `OPTION_MAP (\lbl. (lbl,sccp_bottom))
    (fn_entry_label fn)`, `fn`, `lbl`, `bb`] mp_tac) >>
  simp[sccp_refold, sccp_is_fixpoint] >>
  disch_then (fn th => REWRITE_TAC [th]) >>
  simp[sccp_joined_def, LET_THM, df_joined_val_def, direction_case_def] >>
  Cases_on `fn_entry_label fn` >> simp[sccp_edge_transfer_def]
QED

(* Boundary fixpoint at fixpoint for SCCP *)
Triviality sccp_boundary_fixpoint[local]:
  !fn lbl bb.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    df_boundary sccp_bottom (sccp_df_analyze fn) lbl =
      sccp_join (df_boundary sccp_bottom (sccp_df_analyze fn) lbl)
                (df_at sccp_bottom (sccp_df_analyze fn) lbl
                   (LENGTH bb.bb_instructions))
Proof
  rpt strip_tac >>
  simp[sccp_unfold] >>
  irule sccp_bdry >>
  simp[sccp_refold, sccp_is_fixpoint]
QED

(* Well-formed functions contain only well-formed basic blocks *)
Theorem wf_function_bb_well_formed:
  wf_function fn /\ MEM bb fn.fn_blocks ==> bb_well_formed bb
Proof
  fs[wf_function_def]
QED

(* ===== Exit soundness from nophi at entry ===== *)

(* ALL_DISTINCT on sublist of fn_insts_blocks *)
Triviality ssa_block_outputs_distinct_aux[local]:
  !bbs bb.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) ==>
    MEM bb bbs ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  Induct >> simp[fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[]
  >- fs[ALL_DISTINCT_APPEND]
  >> (first_x_assum irule >> gvs[] >> fs[ALL_DISTINCT_APPEND])
QED

Triviality ssa_block_outputs_distinct[local]:
  !fn bb.
    ssa_form fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  rpt strip_tac >> irule ssa_block_outputs_distinct_aux >>
  fs[ssa_form_def, fn_insts_def] >> metis_tac[]
QED

(* ALL_DISTINCT FLAT MAP: elements at different indices are disjoint *)
Triviality all_distinct_flat_map_disjoint[local]:
  !l (f:'a -> 'b list) k j y.
    ALL_DISTINCT (FLAT (MAP f l)) /\
    k < LENGTH l /\ j < LENGTH l /\ k <> j /\
    MEM y (f (EL k l)) ==>
    ~MEM y (f (EL j l))
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  fs[FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  Cases_on `k` >> Cases_on `j` >> gvs[]
  >- (fs[MEM_FLAT, MEM_MAP] >> metis_tac[MEM_EL])
  >- (fs[MEM_FLAT, MEM_MAP] >> metis_tac[MEM_EL])
  >> (first_x_assum irule >> simp[] >> metis_tac[])
QED

(* SSA: outputs of different instructions in the same block are disjoint *)
Triviality ssa_no_output_overlap[local]:
  !fn bb k j y.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    k < LENGTH bb.bb_instructions /\ j < LENGTH bb.bb_instructions /\
    k <> j /\
    MEM y (EL k bb.bb_instructions).inst_outputs ==>
    ~MEM y (EL j bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  drule_all ssa_block_outputs_distinct >>
  strip_tac >>
  metis_tac[all_distinct_flat_map_disjoint]
QED

(* In SSA form, different instructions in the same block produce disjoint
   output variables *)
Theorem ssa_no_output_overlap_inst:
  !fn bb k idx y.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    k < LENGTH bb.bb_instructions /\ idx < LENGTH bb.bb_instructions /\
    k <> idx /\
    MEM y (EL k bb.bb_instructions).inst_outputs ==>
    ~MEM y (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  metis_tac[ssa_no_output_overlap]
QED

(* Terminator step_inst_base is independent of vs_inst_idx *)
Triviality term_step_base_idx_0[local]:
  !inst s v.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK v ==>
    step_inst_base inst (s with vs_inst_idx := 0) = OK v
Proof
  rpt strip_tac >>
  `v.vs_inst_idx = 0` by
    metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0] >>
  qabbrev_tac `f = \st:venom_state. st with vs_inst_idx := 0` >>
  `exec_result_map f (step_inst_base inst (s with vs_inst_idx := 0)) =
   exec_result_map f (step_inst_base inst s)` by
    (unabbrev_all_tac >>
     metis_tac[instIdxIndepTheory.terminator_step_inst_base_idx_norm0]) >>
  `exec_result_map f (step_inst_base inst s) = OK v` by
    (simp[Abbr `f`, instIdxIndepTheory.exec_result_map_def] >>
     `v with vs_inst_idx := 0 = v` by
       simp[venom_state_component_equality] >> fs[]) >>
  fs[] >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := 0)` >>
  fs[Abbr `f`, instIdxIndepTheory.exec_result_map_def] >>
  `v'.vs_inst_idx = 0` by
    metis_tac[instIdxIndepTheory.terminator_OK_inst_idx_0] >>
  fs[venom_state_component_equality]
QED

(* ===== Conditional const_sound ===== *)

(* cond_const_sound: const_sound restricted to variables in FDOM.
   This is the right cross-block invariant for SCCP because the analysis
   may have CL_Const for variables not yet defined on the actual execution
   path (due to optimistic join). *)
Definition cond_const_sound_def:
  cond_const_sound st s <=>
    !x c. FLOOKUP st x = SOME (CL_Const c) /\ x IN FDOM s.vs_vars ==>
           FLOOKUP s.vs_vars x = SOME c
End

(* PHI output predicate: x is a PHI output variable in block lbl *)
Definition is_phi_output_of_block_def:
  is_phi_output_of_block bbs lbl x <=>
    ?bb inst. lookup_block lbl bbs = SOME bb /\
              MEM inst bb.bb_instructions /\
              inst.inst_opcode = PHI /\
              MEM x inst.inst_outputs
End

(* cond_const_sound is trivially true when FDOM is empty *)
Triviality cond_const_sound_empty[local]:
  !st s. FDOM s.vs_vars = {} ==> cond_const_sound st s
Proof
  rw[cond_const_sound_def] >> fs[]
QED

(* const_sound implies cond_const_sound *)
Triviality const_sound_imp_cond[local]:
  !st s. const_sound st s ==> cond_const_sound st s
Proof
  rw[const_sound_def, cond_const_sound_def]
QED

(* cond_const_sound implies const_sound when all CL_Const vars are in FDOM *)
Triviality cond_to_const_sound[local]:
  !st s. cond_const_sound st s /\
         (!x c. FLOOKUP st x = SOME (CL_Const c) ==> x IN FDOM s.vs_vars) ==>
         const_sound st s
Proof
  rw[const_sound_def, cond_const_sound_def]
QED

(* cond_const_sound preserved by state_equiv {} *)
Triviality cond_const_sound_state_equiv[local]:
  !st s1 s2. state_equiv {} s1 s2 /\ cond_const_sound st s1 ==>
    cond_const_sound st s2
Proof
  rw[cond_const_sound_def] >> rpt strip_tac >>
  `FLOOKUP s1.vs_vars x = FLOOKUP s2.vs_vars x` by
    fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
  `x IN FDOM s1.vs_vars` by (
    spose_not_then assume_tac >>
    `FLOOKUP s1.vs_vars x = NONE` by fs[FLOOKUP_DEF] >>
    `FLOOKUP s2.vs_vars x = NONE` by fs[] >>
    fs[FLOOKUP_DEF]) >>
  metis_tac[]
QED

(* ===== Per-block simulation from cond_const_sound ===== *)

(* Bridge strategy: restrict lattice to FDOM, giving const_sound,
   then show sccp_inst agrees on the restriction for operand vars. *)

(* DRESTRICT preserves const_lookup for vars in the restriction domain *)
Triviality const_lookup_drestrict[local]:
  !st fdom x. x IN fdom ==>
    const_lookup (DRESTRICT st fdom) x = const_lookup st x
Proof
  rw[const_lookup_def, FLOOKUP_DRESTRICT]
QED

(* const_subst_op agrees on DRESTRICT for vars in fdom *)
Triviality const_subst_op_drestrict[local]:
  !st fdom op. (!x. op = Var x ==> x IN fdom) ==>
    const_subst_op (DRESTRICT st fdom) op = const_subst_op st op
Proof
  Cases_on `op` >>
  simp[const_subst_op_def, const_lookup_drestrict]
QED

(* const_eval_operand agrees on DRESTRICT for vars in fdom *)
Triviality const_eval_operand_drestrict[local]:
  !st fdom op. (!x. op = Var x ==> x IN fdom) ==>
    const_eval_operand (DRESTRICT st fdom) op = const_eval_operand st op
Proof
  Cases_on `op` >>
  simp[const_eval_operand_def, const_lookup_drestrict]
QED

(* cond_const_sound + DRESTRICT = const_sound *)
Triviality cond_const_sound_drestrict[local]:
  !st s. cond_const_sound st s ==>
    const_sound (DRESTRICT st (FDOM s.vs_vars)) s
Proof
  rw[const_sound_def, cond_const_sound_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum irule >> simp[flookup_thm]
QED

(* const_eval_ops agrees on DRESTRICT for Var ops in fdom *)
Triviality const_eval_ops_drestrict[local]:
  !st fdom ops. EVERY (\op. !x. op = Var x ==> x IN fdom) ops ==>
    const_eval_ops (DRESTRICT st fdom) ops = const_eval_ops st ops
Proof
  Induct_on `ops` >> simp[const_eval_ops_def] >>
  rpt strip_tac >> fs[const_eval_operand_drestrict] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* const_try_fold agrees on DRESTRICT *)
Triviality const_try_fold_drestrict[local]:
  !opcode st fdom ops. EVERY (\op. !x. op = Var x ==> x IN fdom) ops ==>
    const_try_fold opcode (DRESTRICT st fdom) ops =
    const_try_fold opcode st ops
Proof
  rpt strip_tac >> simp[const_try_fold_def] >>
  `const_eval_ops (DRESTRICT st fdom) ops = const_eval_ops st ops`
    suffices_by simp[] >>
  irule const_eval_ops_drestrict >> simp[]
QED

(* sccp_inst depends on lattice only through MAP (const_subst_op st) *)
Triviality sccp_inst_subst_eq[local]:
  !st1 st2 inst.
    MAP (const_subst_op st1) inst.inst_operands =
    MAP (const_subst_op st2) inst.inst_operands ==>
    sccp_inst st1 inst = sccp_inst st2 inst
Proof
  rpt strip_tac >> simp[sccp_inst_def, LET_THM]
QED

(* Lattice agreement on operand vars implies sccp_inst agreement *)
Triviality sccp_inst_operand_agree[local]:
  !st1 st2 inst.
    (!x. MEM (Var x) inst.inst_operands ==>
         const_lookup st1 x = const_lookup st2 x) ==>
    sccp_inst st1 inst = sccp_inst st2 inst
Proof
  rpt strip_tac >>
  match_mp_tac sccp_inst_subst_eq >>
  match_mp_tac listTheory.MAP_CONG >> simp[] >>
  rpt strip_tac >> Cases_on `x` >> simp[const_subst_op_def]
QED

(* sccp_inst preserves step_inst when cond_const_sound holds and all Var
   operands are defined in the state. Bridges cond_const_sound to
   const_sound via DRESTRICT. *)
Theorem sccp_inst_step_correct_cond:
  !st fuel ctx inst s.
    cond_const_sound st s /\ inst_wf inst /\
    (!x. MEM (Var x) inst.inst_operands ==> x IN FDOM s.vs_vars) ==>
    step_inst fuel ctx (sccp_inst st inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `const_sound (DRESTRICT st (FDOM s.vs_vars)) s` by
    metis_tac[cond_const_sound_drestrict] >>
  `step_inst fuel ctx (sccp_inst (DRESTRICT st (FDOM s.vs_vars)) inst) s =
   step_inst fuel ctx inst s` by
    metis_tac[sccp_inst_step_correct] >>
  `sccp_inst (DRESTRICT st (FDOM s.vs_vars)) inst = sccp_inst st inst` by (
    match_mp_tac sccp_inst_operand_agree >>
    rpt strip_tac >> simp[const_lookup_def, FLOOKUP_DRESTRICT] >>
    res_tac) >>
  gvs[]
QED

(* ===== inst_transform_structural for SCCP ===== *)

(* sccp_inst preserves terminators, INVOKE, and non-terminator structure.
   Reproved here because sccp_inst_structural is LOCAL in sccpSoundTheory. *)
Triviality sccp_inst_structural[local]:
  inst_transform_structural (\lat inst. [sccp_inst lat.sl_vals inst])
Proof
  simp[inst_transform_structural_def] >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >> simp[sccp_inst_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  BasicProvers.every_case_tac >> simp[] >>
  gvs[is_terminator_def, mk_nop_inst_def]
QED

Triviality sccp_inst_is_terminator[local]:
  !st inst. is_terminator (sccp_inst st inst).inst_opcode =
            is_terminator inst.inst_opcode
Proof
  rpt gen_tac >> simp[sccp_inst_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  BasicProvers.every_case_tac >> simp[] >>
  gvs[is_terminator_def, mk_nop_inst_def]
QED

(* ===== Helpers for cond_const_sound step_inst preservation ===== *)

(* eval_operands SOME implies all operands evaluate *)
Triviality eval_operands_mem[local]:
  !ops s vs. eval_operands ops s = SOME vs ==>
    !op. MEM op ops ==> eval_operand op s <> NONE
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  rpt strip_tac >> gvs[] >> res_tac
QED

(* cond_const_sound + defined operand => const_subst_op preserves eval *)
Triviality cond_subst_op_correct[local]:
  !st s op. cond_const_sound st s /\ eval_operand op s <> NONE ==>
    eval_operand (const_subst_op st op) s = eval_operand op s
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, const_subst_op_def, const_lookup_def, lookup_var_def] >>
  strip_tac >>
  BasicProvers.every_case_tac >> simp[eval_operand_def] >>
  fs[cond_const_sound_def, lookup_var_def, flookup_thm]
QED

(* exec_*_eval: each exec helper returns OK only when operands evaluate *)
val staged_top_case_fs_tac =
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> fs[];

Triviality exec_pure1_eval[local]:
  exec_pure1 f inst s = OK s' /\ MEM op inst.inst_operands ==>
  eval_operand op s <> NONE
Proof
  simp[exec_pure1_def] >> staged_top_case_fs_tac >> rw[] >> fs[]
QED

Triviality exec_pure2_eval[local]:
  exec_pure2 f inst s = OK s' /\ MEM op inst.inst_operands ==>
  eval_operand op s <> NONE
Proof
  simp[exec_pure2_def] >> staged_top_case_fs_tac >> rw[] >> fs[]
QED

Triviality exec_pure3_eval[local]:
  exec_pure3 f inst s = OK s' /\ MEM op inst.inst_operands ==>
  eval_operand op s <> NONE
Proof
  simp[exec_pure3_def] >> staged_top_case_fs_tac >> rw[] >> fs[]
QED

Triviality exec_read1_eval[local]:
  exec_read1 f inst s = OK s' /\ MEM op inst.inst_operands ==>
  eval_operand op s <> NONE
Proof
  simp[exec_read1_def] >> staged_top_case_fs_tac >> rw[] >> fs[]
QED

Triviality exec_write2_eval[local]:
  exec_write2 f inst s = OK s' /\ MEM op inst.inst_operands ==>
  eval_operand op s <> NONE
Proof
  simp[exec_write2_def] >> staged_top_case_fs_tac >> rw[] >> fs[]
QED


(* For NOP, exec_read0, STOP, SINK, INVALID: step_inst_base ignores operands *)
Triviality exec_read0_ops_irrel[local]:
  !f inst ops s.
    exec_read0 f (inst with inst_operands := ops) s = exec_read0 f inst s
Proof
  rw[exec_read0_def]
QED

val ops_irrel_tac =
  simp[Once step_inst_base_def, exec_read0_ops_irrel] >>
  simp[Once step_inst_base_def, exec_read0_ops_irrel];

Triviality step_inst_base_ops_irrel[local]:
  !inst s ops.
    MEM inst.inst_opcode [NOP; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MEMTOP] ==>
    step_inst_base (inst with inst_operands := ops) s =
    step_inst_base inst s
Proof
  Cases_on `inst` >>
  rpt strip_tac >> gvs[MEM]
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
  >- ops_irrel_tac
QED

(* Helper: eval_operands SOME implies all Var operands in FDOM *)
Triviality eval_operands_var_fdom[local]:
  !ops s vals x. eval_operands ops s = SOME vals /\ MEM (Var x) ops ==>
    x IN FDOM s.vs_vars
Proof
  Induct >> simp[eval_operands_def] >> rpt strip_tac >>
  BasicProvers.every_case_tac >> fs[] >> rw[] >>
  fs[eval_operand_def, lookup_var_def, flookup_thm]
QED

(* step_inst_base_nonerr_var_fdom: imported from venomExecPropsTheory *)

(* INVOKE case: if step_inst returns non-Error, all Var operands are in FDOM *)
Triviality invoke_nonerr_var_fdom[local]:
  !fuel ctx inst s x.
    inst.inst_opcode = INVOKE /\
    (!e. step_inst fuel ctx inst s <> Error e) /\
    MEM (Var x) inst.inst_operands ==>
    x IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  (* Extract: step_inst returns some non-Error result *)
  Cases_on `step_inst fuel ctx inst s` >> gvs[] >>
  (* Now have step_inst ... = OK/Halt/Abort/IntRet *)
  gvs[Once step_inst_def, decode_invoke_def, AllCaseEqs()] >>
  imp_res_tac eval_operands_mem >>
  fs[eval_operand_def, lookup_var_def, flookup_thm]
QED

(* Combined: step_inst non-Error => Var operands in FDOM.
   For non-NOP/PHI/exec_read0 opcodes, if step_inst doesn't error,
   all Var operands must have been evaluated successfully. *)
Triviality step_inst_nonerr_var_fdom[local]:
  !fuel ctx inst s x.
    (!e. step_inst fuel ctx inst s <> Error e) /\
    ~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MEMTOP] /\
    inst_wf inst /\ MEM (Var x) inst.inst_operands ==>
    x IN FDOM s.vs_vars
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- metis_tac[invoke_nonerr_var_fdom] >>
  irule step_inst_base_nonerr_var_fdom >>
  fs[MEM] >> metis_tac[step_inst_non_invoke]
QED

(* ===== analysis_inst_simulates for cond_const_sound ===== *)

(* For non-special opcodes (not PHI/JNZ/ASSERT/ASSERT_UNREACHABLE),
   sccp_inst only substitutes operands *)
Triviality sccp_inst_non_special[local]:
  !lat inst. inst.inst_opcode <> PHI /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> ASSERT /\ inst.inst_opcode <> ASSERT_UNREACHABLE ==>
    sccp_inst lat inst = inst with inst_operands :=
      MAP (const_subst_op lat) inst.inst_operands
Proof
  simp[sccp_inst_def, LET_THM]
QED

(* sccp_inst preserves step_inst OK under cond_const_sound.
   Three cases:
   1. PHI: sccp_inst is identity
   2. NOP/exec_read0: operands irrelevant (step_inst_base_read0_nop_ops_irrel)
   3. Other non-special: all Var operands in FDOM (step_inst_base_ok_var_fdom),
      so cond_const_sound acts like const_sound (sccp_inst_step_correct_cond) *)
(* For NOP/exec_read0 opcodes, sccp_inst gives same step_inst result
   (equality, not just OK-preservation) because operands are irrelevant *)
Triviality sccp_inst_nop_eq[local]:
  !lat fuel ctx inst s.
    MEM inst.inst_opcode [NOP; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE;
      GAS; GASLIMIT; ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER;
      PREVRANDAO; CHAINID; SELFBALANCE; BASEFEE; BLOBBASEFEE;
      CALLDATASIZE; RETURNDATASIZE; CODESIZE; MEMTOP] ==>
    step_inst fuel ctx (sccp_inst lat inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  `sccp_inst lat inst = inst with inst_operands :=
     MAP (const_subst_op lat) inst.inst_operands` by (
    irule sccp_inst_non_special >> fs[]) >>
  `inst.inst_opcode <> INVOKE` by fs[] >>
  simp[step_inst_non_invoke] >>
  imp_res_tac step_inst_base_ops_irrel >>
  gvs[step_inst_non_invoke]
QED

(* sccp_inst preserves step_inst for non-Error results under
   cond_const_sound and inst_wf *)
Theorem sccp_inst_cond_eq:
  !lat fuel ctx inst s.
    cond_const_sound lat s /\ inst_wf inst /\
    (!e. step_inst fuel ctx inst s <> Error e) ==>
    step_inst fuel ctx (sccp_inst lat inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  (* Cases 1+2: PHI (identity) or NOP/exec_read0/STOP/SINK/INVALID (ops irrelevant) *)
  Cases_on `MEM inst.inst_opcode [PHI; NOP; STOP; SINK; INVALID;
    CALLER; ADDRESS; CALLVALUE;
    GAS; GASLIMIT; ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER;
    PREVRANDAO; CHAINID; SELFBALANCE; BASEFEE; BLOBBASEFEE;
    CALLDATASIZE; RETURNDATASIZE; CODESIZE; MEMTOP]`
  >- (
    fs[] >> gvs[]
    >- simp[sccp_inst_def]
    >> metis_tac[sccp_inst_nop_eq, MEM])
  >>
  (* Case 3: all Var operands in FDOM, so cond = const *)
  `!x. MEM (Var x) inst.inst_operands ==> x IN FDOM s.vs_vars` by (
    rpt strip_tac >>
    match_mp_tac step_inst_nonerr_var_fdom >>
    fs[MEM] >> metis_tac[]) >>
  metis_tac[sccp_inst_step_correct_cond]
QED

Triviality sccp_inst_simulates_cond[local]:
  analysis_inst_simulates (state_equiv {}) (execution_equiv {})
    (\lat. cond_const_sound lat.sl_vals)
    (\lat inst. [sccp_inst lat.sl_vals inst])
Proof
  simp[analysis_inst_simulates_def, sccp_inst_structural] >>
  rpt strip_tac >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  (* Error case discharged by simp[]; remaining: OK, Halt, Abort, IntRet *)
  simp[lift_result_def, run_insts_def] >>
  `!e. step_inst fuel ctx inst s <> Error e` by simp[] >>
  drule_all sccp_inst_cond_eq >> strip_tac >>
  simp[state_equiv_refl, execution_equiv_refl, lift_result_def]
QED

(* ===== Transfer soundness for cond_const_sound ===== *)

(* Helper: if lookup_var is preserved and x in new FDOM, then x in old FDOM *)
Triviality lookup_var_preserves_fdom[local]:
  !x s s'.
    lookup_var x s' = lookup_var x s /\
    x IN FDOM s'.vs_vars ==>
    x IN FDOM s.vs_vars
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `FLOOKUP s.vs_vars x = NONE` by metis_tac[flookup_thm] >>
  `FLOOKUP s'.vs_vars x = NONE` by fs[lookup_var_def] >>
  `x NOTIN FDOM s'.vs_vars` by metis_tac[flookup_thm] >>
  fs[]
QED

(* Helper: cond_const_sound preserved through single-output update *)
Triviality cond_const_sound_single_output[local]:
  !st fuel ctx inst s s' out cv.
    cond_const_sound st s /\
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_outputs = [out] /\
    (!c. cv = CL_Const c ==> FLOOKUP s'.vs_vars out = SOME c) ==>
    cond_const_sound (st |+ (out, cv)) s'
Proof
  rpt strip_tac >> rw[cond_const_sound_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `x = out` >> gvs[] >>
  `lookup_var x s' = lookup_var x s` by (
    irule step_preserves_non_output_vars >>
    qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[MEM]) >>
  `x IN FDOM s.vs_vars` by (
    spose_not_then assume_tac >>
    `FLOOKUP s.vs_vars x = NONE` by metis_tac[flookup_thm] >>
    `FLOOKUP s'.vs_vars x = NONE` by fs[lookup_var_def] >>
    `x NOTIN FDOM s'.vs_vars` by metis_tac[flookup_thm] >>
    fs[]) >>
  fs[cond_const_sound_def, lookup_var_def]
QED

(* Helper: terminators preserve cond_const_sound *)
Triviality cond_const_sound_after_terminator[local]:
  !lat fuel ctx inst s s'.
    cond_const_sound lat.sl_vals s /\
    is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    cond_const_sound lat.sl_vals s'
Proof
  rpt strip_tac >> fs[cond_const_sound_def] >> rpt strip_tac >>
  `lookup_var x s' = lookup_var x s`
    by metis_tac[step_terminator_preserves_vars] >>
  `x IN FDOM s.vs_vars` by metis_tac[lookup_var_preserves_fdom] >>
  first_x_assum (drule_all_then strip_assume_tac) >>
  fs[lookup_var_def]
QED

(* Helper: no-output non-terminator preserves cond_const_sound *)
Triviality cond_const_sound_no_outputs[local]:
  !st fuel ctx inst s s'.
    cond_const_sound st s /\
    inst.inst_outputs = [] /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    cond_const_sound st s'
Proof
  rpt strip_tac >> fs[cond_const_sound_def] >> rpt strip_tac >>
  `lookup_var x s' = lookup_var x s` by (
    irule step_preserves_non_output_vars >> metis_tac[MEM]) >>
  `x IN FDOM s.vs_vars` by metis_tac[lookup_var_preserves_fdom] >>
  metis_tac[lookup_var_def]
QED

(* FOLDL of |+ CL_Bottom: members get SOME CL_Bottom,
   non-members preserve FLOOKUP *)
Theorem foldl_fupdate_bottom:
  !outs l x.
    (MEM x outs ==>
      FLOOKUP (FOLDL (\m v. m |+ (v, CL_Bottom)) l outs) x = SOME CL_Bottom) /\
    (~MEM x outs ==>
      FLOOKUP (FOLDL (\m v. m |+ (v, CL_Bottom)) l outs) x = FLOOKUP l x)
Proof
  Induct >> simp[FOLDL, FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac >> Cases_on `x = h` >> gvs[]
  >- (Cases_on `MEM h outs` >> gvs[FLOOKUP_UPDATE])
QED

(* Helper: FOLDL CL_Bottom preserves cond_const_sound after step *)
Triviality cond_const_sound_after_step_bottom[local]:
  !st fuel ctx inst s s'.
    cond_const_sound st s /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    cond_const_sound
      (FOLDL (\l v. l |+ (v, CL_Bottom)) st inst.inst_outputs) s'
Proof
  rpt strip_tac >>
  fs[cond_const_sound_def] >> rpt strip_tac >>
  Cases_on `MEM x inst.inst_outputs`
  >- (imp_res_tac (cj 1 foldl_fupdate_bottom) >> gvs[])
  >>
  imp_res_tac (cj 2 foldl_fupdate_bottom) >> gvs[] >>
  `lookup_var x s' = lookup_var x s` by (
    irule step_preserves_non_output_vars >> metis_tac[MEM]) >>
  `x IN FDOM s.vs_vars` by metis_tac[lookup_var_preserves_fdom] >>
  metis_tac[lookup_var_def]
QED

(* Helper: const_eval_operand soundness for cond_const_sound *)
Triviality cond_const_eval_operand_sound[local]:
  !st s op c.
    cond_const_sound st s /\ const_eval_operand st op = CL_Const c /\
    eval_operand op s <> NONE ==>
    eval_operand op s = SOME c
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[const_eval_operand_def, const_lookup_def, eval_operand_def,
      lookup_var_def] >>
  Cases_on `FLOOKUP st s'` >> gvs[] >>
  fs[cond_const_sound_def] >>
  first_x_assum irule >>
  Cases_on `FLOOKUP s.vs_vars s'` >> gvs[flookup_thm]
QED

(* Bridge: cond_const_sound + step OK + foldable ⇒ FLOOKUP result *)
Triviality cond_const_try_fold_sound[local]:
  !st s fuel ctx inst out c s'.
    cond_const_sound st s /\
    const_try_fold inst.inst_opcode st inst.inst_operands = CL_Const c /\
    is_sccp_foldable inst.inst_opcode /\
    inst_wf inst /\
    inst.inst_outputs = [out] /\
    step_inst fuel ctx inst s = OK s' ==>
    FLOOKUP s'.vs_vars out = SOME c
Proof
  rpt strip_tac >>
  `!x. MEM (Var x) inst.inst_operands ==> x IN FDOM s.vs_vars` by (
    rpt strip_tac >> irule step_inst_nonerr_var_fdom >>
    qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[] >>
    simp[MEM] >> Cases_on `inst.inst_opcode` >>
    gvs[is_sccp_foldable_def]) >>
  `const_sound (DRESTRICT st (FDOM s.vs_vars)) s` by
    metis_tac[cond_const_sound_drestrict] >>
  `const_try_fold inst.inst_opcode (DRESTRICT st (FDOM s.vs_vars))
     inst.inst_operands = CL_Const c` by (
    `EVERY (\op. !x. op = Var x ==> x IN FDOM s.vs_vars) inst.inst_operands`
      by (simp[EVERY_MEM] >> rpt strip_tac >> gvs[]) >>
    metis_tac[const_try_fold_drestrict]) >>
  irule const_try_fold_sound >> metis_tac[]
QED

(* ASSIGN step result: evaluates operand and stores in output *)
Triviality step_assign_result[local]:
  !fuel ctx inst src_op dst s s'.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [src_op] /\
    inst.inst_outputs = [dst] /\
    step_inst fuel ctx inst s = OK s' ==>
    ?val. eval_operand src_op s = SOME val /\
          s' = update_var dst val s
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by (
    `inst.inst_opcode <> INVOKE` by simp[] >>
    metis_tac[step_inst_non_invoke]) >>
  pop_assum mp_tac >>
  simp_tac std_ss [Once step_inst_base_def] >>
  Cases_on `eval_operand src_op s` >> simp[]
QED

(* sccp_transfer_inst preserves cond_const_sound through each step *)
Theorem sccp_transfer_sound_cond:
  !fn. transfer_sound_wf (\lat. cond_const_sound lat.sl_vals)
         sccp_transfer_inst fn
Proof
  rw[transfer_sound_wf_def] >> rpt strip_tac >>
  simp[sccp_transfer_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  REWRITE_TAC [FOLDL] >>
  (* Terminator goals *)
  TRY (irule cond_const_sound_after_terminator >> metis_tac[] >> NO_TAC) >>
  (* No-output goals *)
  TRY (irule cond_const_sound_no_outputs >> metis_tac[] >> NO_TAC) >>
  (* FOLDL-bottom goals *)
  TRY (irule cond_const_sound_after_step_bottom >>
       simp[is_terminator_def] >> metis_tac[] >> NO_TAC) >>
  (* Multi-output partially-evaluated FOLDL *)
  TRY (`cond_const_sound (FOLDL (\l v. l |+ (v, CL_Bottom))
          lat.sl_vals inst.inst_outputs) s'`
         by (irule cond_const_sound_after_step_bottom >>
             simp[is_terminator_def] >> metis_tac[]) >>
       gvs[] >> NO_TAC) >>
  (* Single-output CL_Bottom goals *)
  TRY (irule cond_const_sound_single_output >> simp[] >>
       rpt strip_tac >> gvs[] >> NO_TAC) >>
  (* ASSIGN and foldable: need FLOOKUP s'.vs_vars out = SOME c *)
  irule cond_const_sound_single_output >> simp[] >>
  rpt strip_tac >>
  (* ASSIGN FLOOKUP: eval_operand gives the constant value *)
  TRY (imp_res_tac step_assign_result >>
       `eval_operand h s <> NONE` by gvs[] >>
       imp_res_tac cond_const_eval_operand_sound >>
       gvs[update_var_def, FLOOKUP_UPDATE] >> NO_TAC) >>
  (* Existential witness goals *)
  TRY (qexistsl_tac [`run_ctx`, `fuel`, `inst`, `s`] >> simp[] >> NO_TAC) >>
  (* Foldable FLOOKUP: bridge via cond_const_try_fold_sound *)
  irule cond_const_try_fold_sound >> metis_tac[]
QED

(* ===== Cross-block helpers ===== *)

(* FDOM of sccp_join is union *)
Triviality sccp_join_fdom[local]:
  FDOM (sccp_join a b).sl_vals = FDOM a.sl_vals UNION FDOM b.sl_vals
Proof
  simp[sccp_join_def, FUN_FMAP_DEF]
QED

(* FLOOKUP in sccp_join *)
Triviality sccp_join_flookup[local]:
  FLOOKUP (sccp_join a b).sl_vals x =
    if x IN FDOM a.sl_vals UNION FDOM b.sl_vals then
      SOME (const_meet (const_lookup a.sl_vals x) (const_lookup b.sl_vals x))
    else NONE
Proof
  simp[sccp_join_def] >>
  simp[FLOOKUP_FUN_FMAP]
QED

(* const_lookup version: always equals const_meet, no FDOM condition *)
Triviality sccp_join_const_lookup[local]:
  const_lookup (sccp_join a b).sl_vals x =
    const_meet (const_lookup a.sl_vals x) (const_lookup b.sl_vals x)
Proof
  simp[const_lookup_def, sccp_join_flookup] >>
  Cases_on `x IN FDOM a.sl_vals UNION FDOM b.sl_vals` >> simp[] >>
  gvs[pred_setTheory.IN_UNION, const_lookup_def, const_meet_def] >>
  Cases_on `FLOOKUP a.sl_vals x` >> Cases_on `FLOOKUP b.sl_vals x` >>
  gvs[flookup_thm, const_meet_def]
QED

(* const_meet never returns CL_Top unless both inputs are CL_Top *)
Triviality const_meet_not_top[local]:
  a <> CL_Top \/ b <> CL_Top ==> const_meet a b <> CL_Top
Proof
  Cases_on `a` >> Cases_on `b` >> simp[const_meet_def] >> rw[]
QED

(* const_meet(a, CL_Const c) = CL_Const c iff a IN {CL_Top, CL_Const c} *)
Triviality const_meet_const_right[local]:
  const_meet a b = CL_Const c /\ b <> CL_Top ==> b = CL_Const c
Proof
  Cases_on `a` >> Cases_on `b` >> simp[const_meet_def] >> rw[]
QED

(* Join soundness: if b is sound for v, and every variable in FDOM v.vs_vars
   has a non-CL_Top value in b, then the join is sound for v. *)
(* Bridge: FLOOKUP form of no-top implies const_lookup form *)
Triviality flookup_no_top_const_lookup[local]:
  x IN FDOM fm /\ FLOOKUP fm x <> SOME CL_Top ==>
  const_lookup fm x <> CL_Top
Proof
  simp[const_lookup_def] >>
  Cases_on `FLOOKUP fm x` >> gvs[] >> metis_tac[flookup_thm]
QED

Triviality cond_const_sound_join_right[local]:
  cond_const_sound b.sl_vals v /\
  (!x. x IN FDOM v.vs_vars ==>
     x IN FDOM b.sl_vals /\ FLOOKUP b.sl_vals x <> SOME CL_Top)
  ==>
  cond_const_sound (sccp_join a b).sl_vals v
Proof
  rw[cond_const_sound_def, sccp_join_flookup] >>
  rpt strip_tac >> gvs[] >>
  `x IN FDOM b.sl_vals /\ FLOOKUP b.sl_vals x <> SOME CL_Top` by metis_tac[] >>
  `const_lookup b.sl_vals x <> CL_Top` by metis_tac[flookup_no_top_const_lookup] >>
  drule_all const_meet_const_right >> strip_tac >>
  `FLOOKUP b.sl_vals x = SOME (CL_Const c)` by
    (Cases_on `FLOOKUP b.sl_vals x` >>
     gvs[const_lookup_def]) >>
  metis_tac[]
QED

(* Join preserves non-CL_Top: if b has non-CL_Top for x, so does join(a,b) *)
Triviality sccp_join_preserves_no_top[local]:
  x IN FDOM b.sl_vals /\ FLOOKUP b.sl_vals x <> SOME CL_Top ==>
  FLOOKUP (sccp_join a b).sl_vals x <> SOME CL_Top
Proof
  rpt strip_tac >>
  gvs[sccp_join_flookup] >>
  Cases_on `FLOOKUP b.sl_vals x` >>
  gvs[flookup_thm, const_lookup_def] >>
  metis_tac[const_meet_not_top]
QED

(* Left-side version *)
Triviality sccp_join_preserves_no_top_left[local]:
  x IN FDOM a.sl_vals /\ FLOOKUP a.sl_vals x <> SOME CL_Top ==>
  FLOOKUP (sccp_join a b).sl_vals x <> SOME CL_Top
Proof
  rpt strip_tac >>
  gvs[sccp_join_flookup] >>
  Cases_on `FLOOKUP a.sl_vals x` >>
  gvs[flookup_thm, const_lookup_def] >>
  metis_tac[const_meet_not_top]
QED

(* Join preserves FDOM membership *)
Triviality sccp_join_fdom_right[local]:
  x IN FDOM b.sl_vals ==> x IN FDOM (sccp_join a b).sl_vals
Proof
  simp[sccp_join_fdom]
QED

Triviality sccp_join_fdom_left[local]:
  x IN FDOM a.sl_vals ==> x IN FDOM (sccp_join a b).sl_vals
Proof
  simp[sccp_join_fdom]
QED

(* ===== FDOM tracking through FOLDL |+ CL_Bottom ===== *)

Triviality foldl_fupdate_fdom[local]:
  !outs lat y. MEM y outs \/ y IN FDOM lat ==>
    y IN FDOM (FOLDL (\l v. l |+ (v, CL_Bottom)) lat outs)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[]
QED

Triviality foldl_bottom_not_top[local]:
  !outs lat x.
    (MEM x outs \/
     (x IN FDOM lat /\ FLOOKUP lat x <> SOME CL_Top)) ==>
    FLOOKUP (FOLDL (\l v. l |+ (v, CL_Bottom)) lat outs) x <> SOME CL_Top
Proof
  Induct >> simp[] >> rpt strip_tac >>
  (first_x_assum (qspecl_then [`lat |+ (h, CL_Bottom)`, `x`] mp_tac) >>
   impl_tac >- (Cases_on `x = h` >>
     gvs[FLOOKUP_UPDATE, FDOM_FUPDATE]) >>
   gvs[])
QED

(* ===== FDOM/non-CL_Top tracking through sccp_transfer_inst ===== *)

(* sccp_transfer_inst is FDOM-monotone: the output FDOM is a superset
   of the input *)
Theorem sccp_transfer_fdom_mono:
  !fn inst lat x. x IN FDOM lat.sl_vals ==>
    x IN FDOM (sccp_transfer_inst fn inst lat).sl_vals
Proof
  rpt strip_tac >> simp[sccp_transfer_inst_def] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
  rpt (IF_CASES_TAC >> gvs[]) >>
  TRY (simp[FDOM_FUPDATE] >> NO_TAC) >>
  irule foldl_fupdate_fdom >> simp[FDOM_FUPDATE]
QED

(* Transfer adds outputs to FDOM *)
Triviality sccp_transfer_outputs_in_fdom[local]:
  !fn inst lat y. MEM y inst.inst_outputs /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI ==>
    y IN FDOM (sccp_transfer_inst fn inst lat).sl_vals
Proof
  rpt strip_tac >> gvs[sccp_transfer_inst_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `inst.inst_opcode = ASSIGN` >> gvs[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[FDOM_FUPDATE] >>
  irule foldl_fupdate_fdom >> simp[]
QED

(* FOLDL |+ Bottom preserves FLOOKUP for non-members *)
Triviality foldl_fupdate_bottom_non_mem[local]:
  !outs lat x. ~MEM x outs ==>
    FLOOKUP (FOLDL (\l v. l |+ (v, CL_Bottom)) lat outs) x = FLOOKUP lat x
Proof
  Induct >> simp[FLOOKUP_UPDATE]
QED

(* sccp_transfer_inst preserves FLOOKUP for non-output variables *)
Theorem sccp_transfer_non_output_flookup:
  !fn inst lat x. ~MEM x inst.inst_outputs ==>
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x =
    FLOOKUP lat.sl_vals x
Proof
  rpt strip_tac >> simp[sccp_transfer_inst_def] >>
  IF_CASES_TAC >> gvs[]
  >- (irule foldl_fupdate_bottom_non_mem >> simp[])
  >> IF_CASES_TAC >> gvs[]
  >- (TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[] >>
      TRY BasicProvers.TOP_CASE_TAC >> gvs[])
  >> Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `inst.inst_opcode = ASSIGN` >> gvs[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[FLOOKUP_UPDATE] >>
  simp[foldl_fupdate_bottom_non_mem, FLOOKUP_UPDATE]
QED

(* Transfer writes non-CL_Top for output variables when operands are non-CL_Top.
   Restricted to non-terminator, non-PHI (terminators don't modify sl_vals,
   PHI writes CL_Bottom). For PHI, included via the foldl_bottom_not_top path. *)
(* Helper: const_eval_operand is not CL_Top when Var operands are in FDOM
   with non-CL_Top values *)
Triviality const_eval_operand_not_top[local]:
  !st op. (!v. op = Var v ==> v IN FDOM st /\ FLOOKUP st v <> SOME CL_Top) ==>
          const_eval_operand st op <> CL_Top
Proof
  rpt gen_tac \\ Cases_on `op`
  \\ simp[const_eval_operand_def, const_lookup_def]
  \\ strip_tac \\ Cases_on `FLOOKUP st s` \\ gvs[flookup_thm]
QED

(* Helper: const_eval_ops never returns EvalTop when all Var operands are
   in FDOM with non-CL_Top values *)
Triviality const_eval_ops_not_top[local]:
  !st ops. (!v. MEM (Var v) ops ==> v IN FDOM st /\ FLOOKUP st v <> SOME CL_Top) ==>
           const_eval_ops st ops <> EvalTop
Proof
  Induct_on `ops`
  \\ simp[const_eval_ops_def]
  \\ rpt gen_tac \\ strip_tac
  \\ `const_eval_operand st h <> CL_Top` by
       (irule const_eval_operand_not_top \\ rpt strip_tac \\ gvs[])
  \\ Cases_on `const_eval_operand st h` \\ gvs[]
  \\ `const_eval_ops st ops <> EvalTop` by
       (first_x_assum irule \\ rpt strip_tac \\ gvs[])
  \\ Cases_on `const_eval_ops st ops` \\ gvs[]
QED

(* Helper: const_try_fold never returns CL_Top when all Var operands are
   in FDOM with non-CL_Top values *)
Triviality const_try_fold_not_top[local]:
  !op st ops. (!v. MEM (Var v) ops ==> v IN FDOM st /\ FLOOKUP st v <> SOME CL_Top) ==>
              const_try_fold op st ops <> CL_Top
Proof
  simp[const_try_fold_def]
  \\ rpt gen_tac \\ strip_tac
  \\ `const_eval_ops st ops <> EvalTop` by
       (irule const_eval_ops_not_top \\ simp[])
  \\ Cases_on `const_eval_ops st ops` \\ gvs[]
  \\ BasicProvers.EVERY_CASE_TAC
QED

(* Single output case: the core of sccp_transfer_output_not_top *)
Triviality sccp_transfer_single_output_not_top[local]:
  !fn inst lat out.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> PHI /\
    inst.inst_outputs = [out] /\
    (!v. MEM (Var v) inst.inst_operands ==>
         v IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals v <> SOME CL_Top) ==>
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals out <> SOME CL_Top
Proof
  rpt gen_tac \\ strip_tac
  \\ simp[sccp_transfer_inst_def, FLOOKUP_UPDATE]
  \\ Cases_on `inst.inst_opcode = ASSIGN`
  \\ simp[]
  \\ BasicProvers.EVERY_CASE_TAC
  \\ simp[FLOOKUP_UPDATE]
  \\ TRY (irule const_eval_operand_not_top
          \\ rpt strip_tac \\ gvs[] \\ NO_TAC)
  \\ irule const_try_fold_not_top \\ simp[]
QED

Triviality sccp_transfer_output_not_top[local]:
  !fn inst lat x.
    ~is_terminator inst.inst_opcode /\
    MEM x inst.inst_outputs /\
    (!v. MEM (Var v) inst.inst_operands ==>
         v IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals v <> SOME CL_Top) ==>
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x <> SOME CL_Top
Proof
  rpt gen_tac \\ strip_tac
  \\ Cases_on `inst.inst_opcode = PHI`
  >- simp[sccp_transfer_inst_def, foldl_bottom_not_top]
  \\ Cases_on `inst.inst_outputs` \\ gvs[]
  \\ Cases_on `t`
  \\ gvs[]
  >- metis_tac[sccp_transfer_single_output_not_top]
  \\ simp[sccp_transfer_inst_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp[]
  \\ irule foldl_bottom_not_top \\ simp[FLOOKUP_UPDATE]
QED

Triviality sccp_terminator_opcode_cases[local]:
  !op.
    is_terminator op ==>
    op = JMP \/ op = JNZ \/ op = DJMP \/ op = RET \/
    op = RETURN \/ op = REVERT \/ op = STOP \/ op = SINK \/
    op = SELFDESTRUCT \/ op = INVALID \/ op = DRET \/ op = RETFMP
Proof
  Cases \\ gvs[is_terminator_def]
QED

(* Terminators don't modify sl_vals *)
Triviality sccp_transfer_terminator_sl_vals[local]:
  !fn inst lat.
    is_terminator inst.inst_opcode ==>
    (sccp_transfer_inst fn inst lat).sl_vals = lat.sl_vals
Proof
  rpt strip_tac
  \\ drule sccp_terminator_opcode_cases \\ strip_tac
  \\ gvs[sccp_transfer_inst_def]
  \\ BasicProvers.EVERY_CASE_TAC \\ simp[]
QED

(* extract_labels ops = SOME labels means all ops are Labels, so
   FOLDR collecting Label destinations gives set labels *)
Triviality extract_labels_el_in_foldr[local]:
  !ops labels k.
    extract_labels ops = SOME labels /\ k < LENGTH labels ==>
    EL k labels IN
    FOLDR (\op acc. case op of Label dst => dst INSERT acc | _ => acc) {} ops
Proof
  Induct >> simp[extract_labels_def] >>
  Cases >> simp[extract_labels_def] >>
  rpt strip_tac >>
  Cases_on `extract_labels ops` >> gvs[] >>
  Cases_on `k` >> gvs[]
QED

(* Terminator transfer puts the actual successor in sl_targets.
   For JNZ with known constant, cond_const_sound ensures the taken branch matches. *)
val term_succ_base_tac =
  fs[sccp_transfer_inst_def, step_inst_base_def, AllCaseEqs()] >>
  gvs[jump_to_def, is_terminator_def];

val term_succ_jnz_tac =
  fs[sccp_transfer_inst_def, step_inst_base_def, AllCaseEqs()] >>
  gvs[jump_to_def, is_terminator_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  TRY (metis_tac[cond_const_eval_operand_sound,
                 optionTheory.SOME_11, optionTheory.NOT_NONE_SOME]);

val term_succ_djmp_tac =
  fs[sccp_transfer_inst_def, step_inst_base_def, AllCaseEqs()] >>
  gvs[jump_to_def, is_terminator_def] >>
  DISJ1_TAC >> irule extract_labels_el_in_foldr >> metis_tac[];

Triviality sccp_transfer_term_succ_in_targets[local]:
  !inst fn lat s s'.
    inst_wf inst /\ is_terminator inst.inst_opcode /\
    cond_const_sound lat.sl_vals s /\
    step_inst_base inst s = OK s' ==>
    s'.vs_current_bb IN (sccp_transfer_inst fn inst lat).sl_targets
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def]
  >- term_succ_base_tac
  >- term_succ_jnz_tac
  >- term_succ_djmp_tac
  >- term_succ_base_tac
  >- term_succ_base_tac
  >- term_succ_base_tac
  >- term_succ_base_tac
  >- term_succ_base_tac
  >- (term_succ_base_tac >> pairarg_tac >> gvs[])
  >- term_succ_base_tac
  >- term_succ_base_tac
  >- term_succ_base_tac
QED

(* Combined: transfer preserves non-CL_Top for all variables in its output FDOM *)
Triviality sccp_transfer_no_top[local]:
  !fn inst lat x.
    x IN FDOM (sccp_transfer_inst fn inst lat).sl_vals /\
    (x IN FDOM lat.sl_vals ==> FLOOKUP lat.sl_vals x <> SOME CL_Top) /\
    (!v. MEM (Var v) inst.inst_operands ==>
         v IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals v <> SOME CL_Top)
    ==>
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x <> SOME CL_Top
Proof
  rpt strip_tac
  \\ Cases_on `is_terminator inst.inst_opcode`
  >- (imp_res_tac sccp_transfer_terminator_sl_vals \\ gvs[]
      \\ metis_tac[flookup_thm])
  \\ Cases_on `MEM x inst.inst_outputs`
  >- metis_tac[sccp_transfer_output_not_top]
  \\ `FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x =
      FLOOKUP lat.sl_vals x` by
       (irule sccp_transfer_non_output_flookup \\ simp[])
  \\ gvs[] \\ metis_tac[flookup_thm, sccp_transfer_fdom_mono]
QED

(* ===== FDOM tracking through exec_block ===== *)

(* ===== Intra-block FDOM+non-CL_Top invariant preservation ===== *)

(* Per-step: if FDOM s.vs_vars is covered by lat with non-CL_Top,
   and step_inst succeeds, then FDOM s'.vs_vars is covered by
   (sccp_transfer_inst fn inst lat) with non-CL_Top.
   This is transfer_sound for the coverage predicate. *)
(* For non-PHI, non-terminator, non-ASSIGN, non-foldable opcodes,
   outputs get CL_Bottom in the transfer *)
Triviality foldl_fupdate_bottom_mem[local]:
  !outs l x. MEM x outs ==>
    FLOOKUP (FOLDL (\m v. m |+ (v, CL_Bottom)) l outs) x = SOME CL_Bottom
Proof
  Induct >> simp[FLOOKUP_UPDATE] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  (* x = h case: either MEM h outs (IH) or not (FLOOKUP_UPDATE) *)
  Cases_on `MEM h outs`
  >- metis_tac[]
  >> imp_res_tac (cj 2 foldl_fupdate_bottom) >> gvs[FLOOKUP_UPDATE]
QED

(* Key insight: FOLDL CL_Bottom preserves existing CL_Bottom entries *)
Triviality foldl_fupdate_bottom_preserves[local]:
  !outs l x. FLOOKUP l x = SOME CL_Bottom ==>
    FLOOKUP (FOLDL (\m v. m |+ (v, CL_Bottom)) l outs) x = SOME CL_Bottom
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> simp[FLOOKUP_UPDATE]
QED

Triviality sccp_transfer_nonfoldable_bottom[local]:
  !fn inst lat x.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> PHI /\ inst.inst_opcode <> ASSIGN /\
    ~is_sccp_foldable inst.inst_opcode /\
    MEM x inst.inst_outputs ==>
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x = SOME CL_Bottom
Proof
  rpt strip_tac >>
  simp[sccp_transfer_inst_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  TRY (simp[FLOOKUP_UPDATE] >> NO_TAC) >>
  TRY (irule foldl_fupdate_bottom_mem >> simp[] >> NO_TAC) >>
  irule foldl_fupdate_bottom_preserves >> simp[FLOOKUP_UPDATE]
QED

(* If lookup_var is preserved from s to s' and x ∈ FDOM s', then
   x ∈ FDOM s *)
Theorem lookup_var_fdom_back:
  lookup_var x s' = lookup_var x s /\ x IN FDOM s'.vs_vars ==>
  x IN FDOM s.vs_vars
Proof
  gvs[lookup_var_def] >>
  Cases_on `FLOOKUP s'.vs_vars x` >> Cases_on `FLOOKUP s.vs_vars x` >>
  gvs[flookup_thm]
QED

(* Case 1: Terminator — sl_vals unchanged, vars unchanged *)
Triviality sccp_fdom_terminator[local]:
  !fn inst lat s s'' fuel run_ctx x.
    is_terminator inst.inst_opcode /\
    step_inst fuel run_ctx inst s = OK s'' /\
    x IN FDOM s''.vs_vars /\
    (!x. x IN FDOM s.vs_vars ==>
       x IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals x <> SOME CL_Top) ==>
    x IN FDOM (sccp_transfer_inst fn inst lat).sl_vals /\
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x <> SOME CL_Top
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac sccp_transfer_terminator_sl_vals >>
  imp_res_tac step_terminator_preserves_vars >>
  `x IN FDOM s.vs_vars` by metis_tac[lookup_var_fdom_back] >>
  gvs[]
QED

(* Bridge: step_inst OK + invariant + foldable/ASSIGN => operand coverage.
   Combines step_inst_nonerr_var_fdom with the FDOM/¬Top invariant.
   Only needed for foldable/ASSIGN opcodes (nonfoldable get CL_Bottom anyway). *)
Triviality sccp_operand_coverage[local]:
  !fn inst lat s s'' fuel run_ctx.
    (is_sccp_foldable inst.inst_opcode \/ inst.inst_opcode = ASSIGN) /\
    inst_wf inst /\
    step_inst fuel run_ctx inst s = OK s'' /\
    (!x. x IN FDOM s.vs_vars ==>
       x IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals x <> SOME CL_Top) ==>
    (!v. MEM (Var v) inst.inst_operands ==>
       v IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals v <> SOME CL_Top)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac
  \\ first_x_assum irule
  \\ irule step_inst_nonerr_var_fdom
  \\ qexistsl_tac [`run_ctx`, `fuel`, `inst`] >> gvs[MEM]
  \\ Cases_on `inst.inst_opcode` >> gvs[is_sccp_foldable_def]
QED

(* Case 2a: PHI output — FOLDL gives CL_Bottom *)
Triviality sccp_fdom_output_phi[local]:
  !fn inst lat x.
    inst.inst_opcode = PHI /\
    MEM x inst.inst_outputs ==>
    x IN FDOM (sccp_transfer_inst fn inst lat).sl_vals /\
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x <> SOME CL_Top
Proof
  rpt gen_tac >> strip_tac
  \\ simp[sccp_transfer_inst_def]
  \\ imp_res_tac foldl_fupdate_bottom_mem
  \\ conj_tac
  >- metis_tac[flookup_thm]
  \\ gvs[]
QED

(* Case 2b: Non-PHI, foldable/ASSIGN output *)
Triviality sccp_fdom_output_foldable[local]:
  !fn inst lat s s'' fuel run_ctx x.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> PHI /\
    (is_sccp_foldable inst.inst_opcode \/ inst.inst_opcode = ASSIGN) /\
    MEM x inst.inst_outputs /\
    inst_wf inst /\
    step_inst fuel run_ctx inst s = OK s'' /\
    (!x. x IN FDOM s.vs_vars ==>
       x IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals x <> SOME CL_Top) ==>
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x <> SOME CL_Top
Proof
  rpt gen_tac >> disch_tac
  \\ irule sccp_transfer_output_not_top >> gvs[]
  \\ metis_tac[sccp_operand_coverage]
QED

(* Case 2c: Non-PHI, nonfoldable output *)
Triviality sccp_fdom_output_nonfoldable[local]:
  !fn inst lat x.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> PHI /\
    ~is_sccp_foldable inst.inst_opcode /\ inst.inst_opcode <> ASSIGN /\
    MEM x inst.inst_outputs ==>
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x <> SOME CL_Top
Proof
  rpt gen_tac >> strip_tac
  \\ imp_res_tac sccp_transfer_nonfoldable_bottom >> gvs[]
QED

(* Case 2: Non-terminator, x is an output — combine subcases *)
Triviality sccp_fdom_output[local]:
  !fn inst lat s s'' fuel run_ctx x.
    ~is_terminator inst.inst_opcode /\
    MEM x inst.inst_outputs /\
    inst_wf inst /\
    step_inst fuel run_ctx inst s = OK s'' /\
    (!x. x IN FDOM s.vs_vars ==>
       x IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals x <> SOME CL_Top) ==>
    x IN FDOM (sccp_transfer_inst fn inst lat).sl_vals /\
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x <> SOME CL_Top
Proof
  rpt gen_tac >> strip_tac
  \\ Cases_on `inst.inst_opcode = PHI`
  >- metis_tac[sccp_fdom_output_phi]
  \\ conj_tac
  >- metis_tac[sccp_transfer_outputs_in_fdom]
  \\ Cases_on `is_sccp_foldable inst.inst_opcode \/ inst.inst_opcode = ASSIGN`
  >- metis_tac[sccp_fdom_output_foldable]
  \\ metis_tac[sccp_fdom_output_nonfoldable]
QED

(* Case 3: Non-terminator, x is not an output.
   Key insight: sccp_transfer_non_output_flookup preserves FLOOKUP for non-outputs,
   so FDOM and ¬Top transfer directly from the invariant. *)
Triviality sccp_fdom_non_output[local]:
  !fn inst lat s s'' fuel run_ctx x.
    ~is_terminator inst.inst_opcode /\
    ~MEM x inst.inst_outputs /\
    step_inst fuel run_ctx inst s = OK s'' /\
    x IN FDOM s''.vs_vars /\
    (!x. x IN FDOM s.vs_vars ==>
       x IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals x <> SOME CL_Top) ==>
    x IN FDOM (sccp_transfer_inst fn inst lat).sl_vals /\
    FLOOKUP (sccp_transfer_inst fn inst lat).sl_vals x <> SOME CL_Top
Proof
  rpt gen_tac >> strip_tac
  \\ `lookup_var x s'' = lookup_var x s` by
    metis_tac[step_preserves_non_output_vars]
  \\ `x IN FDOM s.vs_vars` by metis_tac[lookup_var_fdom_back]
  \\ imp_res_tac sccp_transfer_non_output_flookup
  \\ res_tac >> gvs[] >> metis_tac[flookup_thm]
QED

(* sccp_transfer_inst preserves the FDOM/non-CL_Top coverage invariant
   through each step *)
Theorem sccp_transfer_sound_fdom:
  !fn. transfer_sound_wf
    (\lat s. !x. x IN FDOM s.vs_vars ==>
       x IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals x <> SOME CL_Top)
    sccp_transfer_inst fn
Proof
  simp[transfer_sound_wf_def] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[sccp_fdom_terminator]
  >> Cases_on `MEM x inst.inst_outputs`
  >- metis_tac[sccp_fdom_output]
  >> metis_tac[sccp_fdom_non_output]
QED

(* state_equiv {} implies all lookup_var agree *)
Triviality state_equiv_empty_lookup_var[local]:
  state_equiv {} s1 s2 ==> (lookup_var x s1 = lookup_var x s2)
Proof
  simp[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

Triviality state_equiv_empty_vs_vars[local]:
  state_equiv {} s1 s2 ==> (s1.vs_vars = s2.vs_vars)
Proof
  rpt strip_tac >>
  `FLOOKUP s1.vs_vars = FLOOKUP s2.vs_vars` suffices_by
    simp[FLOOKUP_EXT] >>
  simp[FUN_EQ_THM] >> gen_tac >>
  imp_res_tac state_equiv_empty_lookup_var >>
  gvs[lookup_var_def]
QED

(* Universally quantified version of sccp_intra_fwd — avoids fn parse issues *)
Triviality sccp_intra_fwd_all[local]:
  !fn bb.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre ==>
    !idx. SUC idx <= LENGTH bb.bb_instructions ==>
      df_at sccp_bottom (sccp_df_analyze fn) bb.bb_label (SUC idx) =
      sccp_transfer_inst fn (EL idx bb.bb_instructions)
        (df_at sccp_bottom (sccp_df_analyze fn) bb.bb_label idx)
Proof
  rpt strip_tac >> irule sccp_intra_fwd >>
  fs[wf_function_def, fn_labels_def] >>
  metis_tac[MEM_lookup_block]
QED

(* Specialize transfer_sound_exit_wf for FDOM/coverage predicate *)
(* FDOM coverage preserved through entire block using transfer_sound_exit_wf_len *)
Triviality sccp_exit_covered[local]:
  !fn bb s v fuel ctx.
    fn_inst_wf fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    (!x. x IN FDOM s.vs_vars ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze fn) bb.bb_label 0).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze fn) bb.bb_label 0).sl_vals x
         <> SOME CL_Top) /\
    exec_block fuel ctx bb s = OK v ==>
    (!x. x IN FDOM v.vs_vars ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze fn) bb.bb_label
                    (LENGTH bb.bb_instructions)).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze fn) bb.bb_label
                  (LENGTH bb.bb_instructions)).sl_vals x <> SOME CL_Top)
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac wf_function_bb_well_formed >>
  drule (REWRITE_RULE [GSYM AND_IMP_INTRO] sccp_intra_fwd_all) >>
  disch_then (qspecl_then [`bb`] mp_tac) >> simp[] >> strip_tac >>
  mp_tac (transfer_sound_exit_wf_len
    |> Q.SPECL [`state_equiv {}`, `execution_equiv {}`]
    |> ISPECL [``\lat s. !x. x IN FDOM s.vs_vars ==>
                  x IN FDOM lat.sl_vals /\ FLOOKUP lat.sl_vals x <> SOME CL_Top``,
               ``sccp_transfer_inst``]
    |> Q.SPEC [QUOTE "fn"]
    |> Q.SPECL [`bb`, `sccp_bottom`]
    |> Q.SPEC [QUOTE "sccp_df_analyze fn"]
    |> BETA_RULE
    |> REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
  simp[state_equiv_execution_equiv_valid_state_rel] >>
  (impl_tac >- metis_tac[sccp_transfer_sound_fdom]) >>
  (impl_tac >- (fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[])) >>
  simp[] >>
  (impl_tac >- metis_tac[state_equiv_empty_vs_vars]) >>
  simp[] >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`, `v`] mp_tac) >> simp[]
QED

(* ===== Cross-block helpers ===== *)

(* sccp_eval_phis_for_edge preserves FLOOKUP for non-PHI-output vars *)
Triviality sccp_eval_phi_for_edge_output[local]:
  !src_lbl src_vals inst out v.
    sccp_eval_phi_for_edge src_lbl src_vals inst = SOME (out, v) ==>
    MEM out inst.inst_outputs
Proof
  rpt gen_tac >> simp[sccp_eval_phi_for_edge_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `FIND (\(lbl, _0). lbl = src_lbl) (sccp_phi_pairs inst.inst_operands)` >>
  simp[] >> PairCases_on `x` >> simp[]
QED

Triviality sccp_eval_phis_cons[local]:
  !h t src_lbl src_vals lat.
    sccp_eval_phis_for_edge src_lbl src_vals (h::t) lat =
    sccp_eval_phis_for_edge src_lbl src_vals t
      (if h.inst_opcode = PHI then
         case sccp_eval_phi_for_edge src_lbl src_vals h of
           NONE => lat
         | SOME (out, v) => lat with sl_vals := lat.sl_vals |+ (out, v)
       else lat)
Proof
  simp[sccp_eval_phis_for_edge_def]
QED

Triviality sccp_eval_phis_preserves_non_phi[local]:
  !instrs src_lbl src_vals lat x.
    (!inst. MEM inst instrs /\ inst.inst_opcode = PHI ==>
       ~MEM x inst.inst_outputs) ==>
    FLOOKUP (sccp_eval_phis_for_edge src_lbl src_vals instrs lat).sl_vals x =
    FLOOKUP lat.sl_vals x
Proof
  Induct THEN1 simp[sccp_eval_phis_for_edge_def]
  \\
  rpt gen_tac >> strip_tac
  \\
  (* simp uses IH to reduce sccp_eval_phis_for_edge (h::instrs) to
     one-step update. After this, goal is about single-step effect. *)
  simp[Once sccp_eval_phis_cons]
  \\
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `sccp_eval_phi_for_edge src_lbl src_vals h` >> simp[] >>
  PairCases_on `x'` >> simp[FLOOKUP_UPDATE] >>
  imp_res_tac sccp_eval_phi_for_edge_output >>
  `~MEM x h.inst_outputs` by (first_x_assum (qspec_then `h` mp_tac) >> simp[]) >>
  `x'0 <> x` by (CCONTR_TAC >> gvs[]) >>
  simp[]
QED

(* sccp_eval_phis_for_edge preserves FDOM *)
Triviality sccp_eval_phis_fdom[local]:
  !instrs src_lbl src_vals lat x.
    x IN FDOM lat.sl_vals ==>
    x IN FDOM (sccp_eval_phis_for_edge src_lbl src_vals instrs lat).sl_vals
Proof
  Induct THEN1 simp[sccp_eval_phis_for_edge_def]
  \\
  rpt gen_tac >> strip_tac
  \\
  simp[Once sccp_eval_phis_cons]
  \\
  (* simp will apply IH. Goal reduces to: x IN FDOM (one-step update).sl_vals *)
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `sccp_eval_phi_for_edge src_lbl src_vals h` >> simp[] >>
  PairCases_on `x'` >> simp[FDOM_FUPDATE]
QED

(* const_meet a b = CL_Const c /\ a <> CL_Top ==> a = CL_Const c *)
Triviality const_meet_const_left[local]:
  !a b c. const_meet a b = CL_Const c /\ a <> CL_Top ==> a = CL_Const c
Proof
  Cases >> Cases >> simp[const_meet_def] >> rw[]
QED

(* cond_const_sound preserved through join when LEFT side is sound *)
Triviality cond_const_sound_join_left[local]:
  !a b v.
    cond_const_sound a.sl_vals v /\
    (!x. x IN FDOM v.vs_vars ==>
       x IN FDOM a.sl_vals /\ FLOOKUP a.sl_vals x <> SOME CL_Top) ==>
    cond_const_sound (sccp_join a b).sl_vals v
Proof
  rpt strip_tac >> simp[cond_const_sound_def] >>
  rpt gen_tac >> strip_tac >>
  `x IN FDOM a.sl_vals /\ FLOOKUP a.sl_vals x <> SOME CL_Top` by metis_tac[] >>
  (* Use sccp_join_flookup as rewrite *)
  gvs[sccp_join_flookup, pred_setTheory.IN_UNION] >>
  `const_lookup a.sl_vals x <> CL_Top` by
    (simp[const_lookup_def] >>
     Cases_on `FLOOKUP a.sl_vals x` >> gvs[] >> metis_tac[flookup_thm]) >>
  `const_lookup a.sl_vals x = CL_Const c` by metis_tac[const_meet_const_left] >>
  gvs[const_lookup_def] >>
  Cases_on `FLOOKUP a.sl_vals x` >> gvs[] >>
  fs[cond_const_sound_def]
QED

(* Accumulator soundness preserved through FOLDL sccp_join *)
Triviality cond_const_sound_foldl_acc[local]:
  !rest acc v.
    cond_const_sound acc.sl_vals v /\
    (!x. x IN FDOM v.vs_vars ==>
       x IN FDOM acc.sl_vals /\ FLOOKUP acc.sl_vals x <> SOME CL_Top) ==>
    cond_const_sound (FOLDL sccp_join acc rest).sl_vals v /\
    (!x. x IN FDOM v.vs_vars ==>
       x IN FDOM (FOLDL sccp_join acc rest).sl_vals /\
       FLOOKUP (FOLDL sccp_join acc rest).sl_vals x <> SOME CL_Top)
Proof
  Induct THEN1 simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[] >>
  first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> res_tac >>
      metis_tac[sccp_join_fdom_left, sccp_join_preserves_no_top_left])
  >- (irule cond_const_sound_join_left >> simp[])
QED

(* cond_const_sound + FDOM/~Top preserved through FOLDL sccp_join *)
Triviality cond_const_sound_foldl_join[local]:
  !vals acc e v.
    MEM e vals /\
    cond_const_sound e.sl_vals v /\
    (!x. x IN FDOM v.vs_vars ==>
       x IN FDOM e.sl_vals /\ FLOOKUP e.sl_vals x <> SOME CL_Top) ==>
    cond_const_sound (FOLDL sccp_join acc vals).sl_vals v /\
    (!x. x IN FDOM v.vs_vars ==>
       x IN FDOM (FOLDL sccp_join acc vals).sl_vals /\
       FLOOKUP (FOLDL sccp_join acc vals).sl_vals x <> SOME CL_Top)
Proof
  Induct >> simp[] >>
  rpt gen_tac >> disch_tac >> simp[] >>
  Cases_on `e = h` >> gvs[]
  >- ((* e = h *)
    irule cond_const_sound_foldl_acc >>
    conj_tac
    >- (rpt gen_tac >> disch_tac >> res_tac >>
        metis_tac[sccp_join_fdom_right, sccp_join_preserves_no_top])
    >> (irule cond_const_sound_join_right >> gvs[]))
  >> ((* MEM e vals *)
    first_x_assum (qspecl_then [`sccp_join acc h`, `e`, `v`] mp_tac) >> gvs[])
QED

(* const_meet cannot produce CL_Top unless both inputs are CL_Top *)
Triviality const_meet_top_both[local]:
  const_meet a b = CL_Top ==> a = CL_Top /\ b = CL_Top
Proof
  Cases_on `a` >> Cases_on `b` >> simp[const_meet_def] >> rw[]
QED

(* If FOLDL result is CL_Const c, the accumulator had CL_Top or CL_Const c *)
Triviality foldl_join_acc_const_or_top[local]:
  !rest acc x c.
    const_lookup (FOLDL sccp_join acc rest).sl_vals x = CL_Const c ==>
    const_lookup acc.sl_vals x = CL_Top \/
    const_lookup acc.sl_vals x = CL_Const c
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`sccp_join acc h`, `x`, `c`] mp_tac) >>
  strip_tac >> gvs[sccp_join_const_lookup]
  >- (imp_res_tac const_meet_top_both >> simp[])
  >> (imp_res_tac const_meet_const_left >>
      Cases_on `const_lookup acc.sl_vals x = CL_Top` >> gvs[])
QED

(* If FOLDL sccp_join result has CL_Const c at x, and member e has non-Top
   at x, then e must have CL_Const c at x. Purely lattice-theoretic.
   Stated in const_lookup to avoid FLOOKUP/FDOM impedance. *)
Triviality foldl_join_member_const[local]:
  !vals acc e x c.
    MEM e vals /\
    const_lookup e.sl_vals x <> CL_Top /\
    const_lookup (FOLDL sccp_join acc vals).sl_vals x = CL_Const c ==>
    const_lookup e.sl_vals x = CL_Const c
Proof
  Induct >> simp[] >>
  rpt gen_tac >> strip_tac >> gvs[]
  >- ((* e = h *)
    drule foldl_join_acc_const_or_top >> simp[sccp_join_const_lookup] >> strip_tac
    >- (imp_res_tac const_meet_top_both >> gvs[])
    >> (drule_all const_meet_const_right >> simp[]))
  >> ((* MEM e vals *)
    first_x_assum irule >> gvs[] >>
    qexists_tac `sccp_join acc h` >> gvs[])
QED

(* FDOM/~Top coverage from any single member of the FOLDL join.
   Does NOT require cond_const_sound of the member. *)
(* Helper: FOLDL sccp_join preserves FDOM from accumulator *)
Triviality foldl_join_preserves_fdom[local]:
  !vals acc x. x IN FDOM acc.sl_vals ==>
    x IN FDOM (FOLDL sccp_join acc vals).sl_vals
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >> irule sccp_join_fdom_left >> simp[]
QED

(* Helper: FOLDL sccp_join preserves not-Top from accumulator *)
Triviality foldl_join_preserves_no_top[local]:
  !vals acc x. x IN FDOM acc.sl_vals /\
    FLOOKUP acc.sl_vals x <> SOME CL_Top ==>
    FLOOKUP (FOLDL sccp_join acc vals).sl_vals x <> SOME CL_Top
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  metis_tac[sccp_join_fdom_left, sccp_join_preserves_no_top_left]
QED

(* FDOM/¬Top for a single x lifts through FOLDL join from any member *)
Triviality foldl_join_coverage_var[local]:
  !vals acc e x.
    MEM e vals /\
    x IN FDOM e.sl_vals /\ FLOOKUP e.sl_vals x <> SOME CL_Top ==>
    x IN FDOM (FOLDL sccp_join acc vals).sl_vals /\
    FLOOKUP (FOLDL sccp_join acc vals).sl_vals x <> SOME CL_Top
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >|
  [(* e = h case *)
   conj_tac
   >- (irule foldl_join_preserves_fdom >>
       irule sccp_join_fdom_right >> gvs[])
   >> (irule foldl_join_preserves_no_top >>
       metis_tac[sccp_join_fdom_right, sccp_join_preserves_no_top]),
   (* MEM e vals case *)
   first_x_assum (qspecl_then [`sccp_join acc h`, `e`, `x`] mp_tac) >>
   simp[]]
QED

(* ===== Exit helpers: nophi at entry → full invariant at exit ===== *)

(* nophi_sound plus CL_Bottom on PHI outputs implies cond_const_sound *)
Theorem nophi_phi_bottom_imp_cond:
  !fn bb instrs lbl lat s.
    lookup_block lbl fn.fn_blocks = SOME bb /\
    instrs = bb.bb_instructions /\
    (!x c. FLOOKUP lat x = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block fn.fn_blocks lbl x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!k y. k < LENGTH instrs /\
           (EL k instrs).inst_opcode = PHI /\
           MEM y (EL k instrs).inst_outputs ==>
           FLOOKUP lat y = SOME CL_Bottom) ==>
    cond_const_sound lat s
Proof
  rpt strip_tac >> rw[cond_const_sound_def] >> rpt strip_tac >>
  Cases_on `is_phi_output_of_block fn.fn_blocks lbl x`
  >- (fs[is_phi_output_of_block_def] >> gvs[] >>
      imp_res_tac MEM_EL >> rename1 `n' < LENGTH bb.bb_instructions` >>
      first_x_assum (qspecl_then [`n'`, `x`] mp_tac) >> simp[] >> gvs[])
  >> metis_tac[]
QED

(* nophi_coverage plus CL_Bottom on PHI outputs implies full
   FDOM/non-CL_Top coverage *)
Theorem nophi_phi_bottom_imp_coverage:
  !fn bb instrs lbl lat s.
    lookup_block lbl fn.fn_blocks = SOME bb /\
    instrs = bb.bb_instructions /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block fn.fn_blocks lbl x ==>
         x IN FDOM lat /\ FLOOKUP lat x <> SOME CL_Top) /\
    (!k y. k < LENGTH instrs /\
           (EL k instrs).inst_opcode = PHI /\
           MEM y (EL k instrs).inst_outputs ==>
           FLOOKUP lat y = SOME CL_Bottom) ==>
    (!x. x IN FDOM s.vs_vars ==>
         x IN FDOM lat /\ FLOOKUP lat x <> SOME CL_Top)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  Cases_on `is_phi_output_of_block fn.fn_blocks lbl x`
  >- (fs[is_phi_output_of_block_def] >> gvs[] >>
      imp_res_tac MEM_EL >> rename1 `n' < LENGTH bb.bb_instructions` >>
      first_x_assum (qspecl_then [`n'`, `x`] mp_tac) >> simp[] >>
      gvs[flookup_thm])
  >> (first_x_assum (qspec_then `x` mp_tac) >> simp[])
QED

(* Starting from nophi_sound/nophi_coverage at any instruction position in
   a block, cond_const_sound, FDOM/non-CL_Top coverage, and
   successor-in-sl_targets all hold at block exit *)
Theorem sccp_nophi_exit_props_from:
  !f bb fuel ctx s v.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre /\
    s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
    (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
              bb.bb_label s.vs_inst_idx).sl_vals x = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!k y. k < s.vs_inst_idx /\ k < LENGTH bb.bb_instructions /\
           (EL k bb.bb_instructions).inst_opcode = PHI /\
           MEM y (EL k bb.bb_instructions).inst_outputs ==>
           FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
              bb.bb_label s.vs_inst_idx).sl_vals y = SOME CL_Bottom) /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f)
                    bb.bb_label s.vs_inst_idx).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
                  bb.bb_label s.vs_inst_idx).sl_vals x <> SOME CL_Top) /\
    exec_block fuel ctx bb s = OK v ==>
    cond_const_sound
      (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
         (LENGTH bb.bb_instructions)).sl_vals v /\
    (!x. x IN FDOM v.vs_vars ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
                    (LENGTH bb.bb_instructions)).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
                  (LENGTH bb.bb_instructions)).sl_vals x <> SOME CL_Top) /\
    v.vs_current_bb IN
      (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
         (LENGTH bb.bb_instructions)).sl_targets
Proof
  rpt gen_tac >> strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]) >>
  qabbrev_tac `result = sccp_df_analyze f` >>
  qabbrev_tac `lbl = bb.bb_label` >>
  qabbrev_tac `instrs = bb.bb_instructions` >>
  (* Intra-forward property *)
  `!idx. SUC idx <= LENGTH instrs ==>
     df_at sccp_bottom result lbl (SUC idx) =
     sccp_transfer_inst f (EL idx instrs)
       (df_at sccp_bottom result lbl idx)` by
    (rpt strip_tac >> unabbrev_all_tac >>
     irule sccp_intra_fwd >> metis_tac[]) >>
  (* Terminator index setup *)
  `SUC (PRE (LENGTH instrs)) = LENGTH instrs` by
    (Cases_on `instrs` >> fs[]) >>
  qabbrev_tac `ti = PRE (LENGTH instrs)` >>
  `ti < LENGTH instrs` by (Cases_on `instrs` >> fs[Abbr `ti`]) >>
  `is_terminator (EL ti instrs).inst_opcode` by
    (fs[bb_well_formed_def, Abbr `ti`, Abbr `instrs`] >>
     Cases_on `bb.bb_instructions` >> fs[LAST_EL]) >>
  `!j. j < ti ==> ~is_terminator (EL j instrs).inst_opcode` by
    (fs[bb_well_formed_def, Abbr `ti`, Abbr `instrs`] >>
     rpt strip_tac >> CCONTR_TAC >> fs[] >> res_tac >> fs[]) >>
  `ssa_form f` by fs[wf_ssa_def] >>
  (* === Complete induction with TRIPLE invariant:
     1) nophi_sound at position idx
     2) phi_bottom at position idx
     3) nophi_coverage at position idx
     Conclude: cond_const_sound + full coverage at exit *)
  `!n fuel' ctx' s'.
     n = ti + 1 - s'.vs_inst_idx /\
     s'.vs_inst_idx <= ti /\
     (!x c. FLOOKUP (df_at sccp_bottom result lbl s'.vs_inst_idx).sl_vals x
               = SOME (CL_Const c) /\
            x IN FDOM (s' with vs_inst_idx := 0).vs_vars /\
            ~is_phi_output_of_block f.fn_blocks lbl x ==>
            FLOOKUP (s' with vs_inst_idx := 0).vs_vars x = SOME c) /\
     (!k y. k < s'.vs_inst_idx /\ k < LENGTH instrs /\
            (EL k instrs).inst_opcode = PHI /\
            MEM y (EL k instrs).inst_outputs ==>
            FLOOKUP (df_at sccp_bottom result lbl s'.vs_inst_idx).sl_vals y
              = SOME CL_Bottom) /\
     (!x. x IN FDOM (s' with vs_inst_idx := 0).vs_vars /\
          ~is_phi_output_of_block f.fn_blocks lbl x ==>
        x IN FDOM (df_at sccp_bottom result lbl s'.vs_inst_idx).sl_vals /\
        FLOOKUP (df_at sccp_bottom result lbl s'.vs_inst_idx).sl_vals x
          <> SOME CL_Top) /\
     exec_block fuel' ctx' bb s' = OK v ==>
     cond_const_sound (df_at sccp_bottom result lbl (SUC ti)).sl_vals v /\
     (!x. x IN FDOM v.vs_vars ==>
        x IN FDOM (df_at sccp_bottom result lbl (SUC ti)).sl_vals /\
        FLOOKUP (df_at sccp_bottom result lbl (SUC ti)).sl_vals x
          <> SOME CL_Top) /\
     v.vs_current_bb IN (df_at sccp_bottom result lbl (SUC ti)).sl_targets`
    suffices_by (
      strip_tac >>
      qpat_x_assum `SUC ti = LENGTH instrs`
        (fn th => PURE_REWRITE_TAC [SYM th]) >>
      qpat_x_assum `!n fuel0 ctx0 s0. n = ti + 1 - s0.vs_inst_idx /\ _ ==> _`
        (mp_tac o Q.SPECL [`ti + 1 - s.vs_inst_idx`, `fuel`, `ctx`, `s`]) >>
      disch_then match_mp_tac >>
      gvs[Abbr `ti`, Abbr `instrs`, Abbr `lbl`, Abbr `result`] >>
      metis_tac[]) >>
  completeInduct_on `n` >> gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `idx = s'.vs_inst_idx` >>
  `idx < LENGTH instrs` by decide_tac >>
  qabbrev_tac `inst = EL idx instrs` >>
  `inst_wf inst` by metis_tac[EVERY_EL, markerTheory.Abbrev_def] >>
  (* Unfold exec_block one step *)
  `exec_block fuel' ctx' bb s' =
   case step_inst fuel' ctx' inst s' of
     OK s'' =>
       if is_terminator inst.inst_opcode then
         if s''.vs_halted then Halt s'' else OK s''
       else exec_block fuel' ctx' bb (s'' with vs_inst_idx := SUC idx)
   | Halt s'' => Halt s''
   | Abort a s'' => Abort a s''
   | IntRet rv ss => IntRet rv ss
   | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `idx`]) >>
  pop_assum (fn th => FULL_SIMP_TAC std_ss [th]) >>
  Cases_on `step_inst fuel' ctx' inst s'` >> fs[]
  >- (
    rename1 `OK s''` >>
    Cases_on `idx = ti`
    >- (
      (* ===== TERMINATOR CASE ===== *)
      `is_terminator inst.inst_opcode` by fs[Abbr `inst`] >>
      `~(inst.inst_opcode = PHI)` by
        (strip_tac >> gvs[is_terminator_def]) >>
      `inst.inst_opcode <> INVOKE` by
        (strip_tac >> gvs[is_terminator_def]) >>
      Cases_on `s''.vs_halted` >- fs[] >>
      fs[] >>
      `step_inst_base inst s' = OK v` by
        metis_tac[step_inst_non_invoke] >>
      `step_inst_base inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[term_step_base_idx_0] >>
      `step_inst fuel' ctx' inst (s' with vs_inst_idx := 0) = OK v` by
        metis_tac[step_inst_non_invoke] >>
      (* All PHIs are before the terminator *)
      `!k. k < LENGTH instrs /\ (EL k instrs).inst_opcode = PHI ==> k < idx` by
        (rpt strip_tac >> CCONTR_TAC >> fs[] >>
         Cases_on `k = idx` >- gvs[Abbr `inst`] >>
         `idx < k` by decide_tac >>
         fs[bb_well_formed_def, Abbr `instrs`]) >>
      (* Derive cond_const_sound at position idx *)
      `cond_const_sound (df_at sccp_bottom result lbl idx).sl_vals
                        (s' with vs_inst_idx := 0)` by (
        match_mp_tac (nophi_phi_bottom_imp_cond
          |> Q.SPECL [`f`, `bb`, `instrs`, `lbl`]) >>
        simp[Abbr `lbl`] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
      (* Terminator preserves cond_const_sound *)
      `cond_const_sound (df_at sccp_bottom result lbl idx).sl_vals v` by
        metis_tac[cond_const_sound_after_terminator] >>
      (* Terminator transfer preserves sl_vals *)
      `(sccp_transfer_inst f inst
          (df_at sccp_bottom result lbl idx)).sl_vals =
       (df_at sccp_bottom result lbl idx).sl_vals` by
        metis_tac[sccp_transfer_terminator_sl_vals] >>
      `(df_at sccp_bottom result lbl (SUC ti)).sl_vals =
       (df_at sccp_bottom result lbl ti).sl_vals` by
        metis_tac[DECIDE ``SUC idx <= SUC idx``] >>
      (* Derive unconditional coverage from nophi_coverage + phi_bottom *)
      `!x. x IN FDOM (s' with vs_inst_idx := 0).vs_vars ==>
         x IN FDOM (df_at sccp_bottom result lbl idx).sl_vals /\
         FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x
           <> SOME CL_Top` by (
        match_mp_tac (nophi_phi_bottom_imp_coverage
          |> Q.SPECL [`f`, `bb`, `instrs`, `lbl`]) >>
        simp[Abbr `lbl`] >> rpt conj_tac >> rpt strip_tac >>
        metis_tac[]) >>
      (* Part 1: cond_const_sound at exit — use metis_tac NOT gvs/simp *)
      conj_tac >- metis_tac[cond_const_sound_def] >>
      (* Part 2: FDOM/¬Top coverage at exit via sccp_fdom_terminator *)
      conj_tac >- (rpt gen_tac >> disch_tac >>
        irule sccp_fdom_terminator >> metis_tac[]) >>
      (* Part 3: v.vs_current_bb IN exit.sl_targets *)
      suspend "term_targets")
    >- (
      (* ===== NON-TERMINATOR CASE ===== *)
      `idx < ti` by decide_tac >>
      `~is_terminator inst.inst_opcode` by
        (qpat_x_assum `!j. j < ti ==> _` (qspec_then `idx` mp_tac) >>
         simp[Abbr `inst`]) >>
      `exec_block fuel' ctx' bb (s'' with vs_inst_idx := SUC idx) = OK v` by
        (qpat_x_assum `(if _ then _ else _) = _` mp_tac >> simp[]) >>
      `step_inst fuel' ctx' inst (s' with vs_inst_idx := 0) =
       OK (s'' with vs_inst_idx := 0)` by (
        Cases_on `inst.inst_opcode = INVOKE`
        >- (mp_tac (Q.SPECL [`fuel'`, `ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only) >>
            simp[])
        >- (mp_tac (Q.SPECL [`fuel'`, `ctx'`, `inst`, `s'`, `0`]
              analysisSimProofsBaseTheory.step_inst_idx_indep) >>
            simp[instIdxIndepTheory.exec_result_map_def])) >>
      (* Apply IH *)
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `ti + 1 - SUC idx` mp_tac) >>
      (impl_tac >- decide_tac) >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `s'' with vs_inst_idx := SUC idx`] mp_tac) >>
      simp[] >>
      (* After simp: IH conclusion becomes P ==> conclusion where P is the
         triple invariant at SUC idx, with sccp_transfer_inst form *)
      impl_tac
      >- suspend "nophi_step"
      >> simp[]))
  >> fs[AllCaseEqs()]
QED

Resume sccp_nophi_exit_props_from[nophi_step]:
  Cases_on `inst.inst_opcode = PHI`
  >- (
    (* === PHI case: split into 3 suspended conjuncts === *)
    rpt conj_tac
    >- suspend "phi_c1"
    >- suspend "phi_c2"
    >- suspend "phi_c3")
  >- suspend "nonphi"
QED

(* --- PHI case, Conjunct 1: nophi_sound --- *)
Resume sccp_nophi_exit_props_from[phi_c1]:
  rpt strip_tac >>
  `~MEM x inst.inst_outputs` by (
    spose_not_then assume_tac >>
    fs[is_phi_output_of_block_def, Abbr `lbl`] >>
    metis_tac[MEM_EL, markerTheory.Abbrev_def]) >>
  `FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x =
   SOME (CL_Const c)` by
    metis_tac[sccp_transfer_non_output_flookup] >>
  `lookup_var x s'' = lookup_var x s'` by
    (irule step_preserves_non_output_vars >> metis_tac[]) >>
  `x IN FDOM s'.vs_vars` by
    metis_tac[lookup_var_fdom_back] >>
  `FLOOKUP s'.vs_vars x = SOME c` by metis_tac[] >>
  fs[lookup_var_def]
QED

(* --- PHI case, Conjunct 2: phi_bottom --- *)
Resume sccp_nophi_exit_props_from[phi_c2]:
  rpt strip_tac >>
  Cases_on `k = idx`
  >- (simp[sccp_transfer_inst_def, Abbr `inst`] >>
      metis_tac[cj 1 foldl_fupdate_bottom])
  >- (`k < idx` by decide_tac >>
      `FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals y
         = SOME CL_Bottom` by metis_tac[] >>
      `~MEM y inst.inst_outputs` by
        metis_tac[ssa_no_output_overlap_inst,
          markerTheory.Abbrev_def, wf_ssa_def] >>
      metis_tac[sccp_transfer_non_output_flookup])
QED

(* --- PHI case, Conjunct 3: nophi_coverage --- *)
Resume sccp_nophi_exit_props_from[phi_c3]:
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (
    (* FDOM membership *)
    `~MEM x inst.inst_outputs` by (
      spose_not_then assume_tac >>
      fs[is_phi_output_of_block_def, Abbr `lbl`] >>
      metis_tac[MEM_EL, markerTheory.Abbrev_def]) >>
    `lookup_var x s'' = lookup_var x s'` by
      (irule step_preserves_non_output_vars >> metis_tac[]) >>
    `x IN FDOM s'.vs_vars` by
      metis_tac[lookup_var_fdom_back] >>
    `x IN FDOM (df_at sccp_bottom result lbl idx).sl_vals` by
      metis_tac[] >>
    metis_tac[sccp_transfer_fdom_mono])
  >- (
    (* ¬ CL_Top *)
    `~MEM x inst.inst_outputs` by (
      spose_not_then assume_tac >>
      fs[is_phi_output_of_block_def, Abbr `lbl`] >>
      metis_tac[MEM_EL, markerTheory.Abbrev_def]) >>
    `lookup_var x s'' = lookup_var x s'` by
      (irule step_preserves_non_output_vars >> metis_tac[]) >>
    `x IN FDOM s'.vs_vars` by
      metis_tac[lookup_var_fdom_back] >>
    `FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x <> SOME CL_Top` by
      metis_tac[] >>
    `FLOOKUP (sccp_transfer_inst f inst
        (df_at sccp_bottom result lbl idx)).sl_vals x =
     FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x` by
      metis_tac[sccp_transfer_non_output_flookup] >>
    metis_tac[])
QED

(* --- Non-PHI case --- *)
Resume sccp_nophi_exit_props_from[nonphi]:
  (* All PHIs are before idx *)
  `!k. k < LENGTH instrs /\ (EL k instrs).inst_opcode = PHI ==>
   k < idx` by (
    rpt strip_tac >> spose_not_then assume_tac >>
    `idx <= k` by decide_tac >>
    `inst.inst_opcode = PHI` suffices_by metis_tac[] >>
    Cases_on `k = idx`
    >- metis_tac[markerTheory.Abbrev_def]
    >- (`idx < k` by decide_tac >>
        `inst = EL idx instrs` by metis_tac[markerTheory.Abbrev_def] >>
        `instrs = bb.bb_instructions` by metis_tac[markerTheory.Abbrev_def] >>
        metis_tac[bb_well_formed_def])) >>
  (* Derive cond_const_sound at idx *)
  `cond_const_sound (df_at sccp_bottom result lbl idx).sl_vals
                    (s' with vs_inst_idx := 0)` by (
    match_mp_tac (nophi_phi_bottom_imp_cond
      |> Q.SPECL [`f`, `bb`, `instrs`, `lbl`]) >>
    simp[Abbr `lbl`] >> rpt conj_tac >> rpt strip_tac >>
    metis_tac[]) >>
  (* Use suspend/Resume to split nonphi into 3 independently provable pieces *)
  rpt conj_tac
  (* Conjunct 1: nophi_sound *)
  >- suspend "np_c1"
  (* Conjunct 2: phi_bottom *)
  >- suspend "np_c2"
  (* Conjunct 3: nophi_coverage *)
  >- suspend "np_c3"
QED

(* --- np_c1: nophi_sound conjunct (non-PHI case) --- *)
Resume sccp_nophi_exit_props_from[np_c1]:
  (* Goal: nophi_sound at SUC idx after non-PHI instruction *)
  (* Have cond_const_sound at idx via nophi + phi_bottom bridge *)
  `cond_const_sound (df_at sccp_bottom result lbl idx).sl_vals
                    (s' with vs_inst_idx := 0)` by (
    match_mp_tac (nophi_phi_bottom_imp_cond
      |> Q.SPECL [`f`, `bb`, `instrs`, `lbl`]) >>
    simp[Abbr `lbl`] >> rpt conj_tac >> rpt strip_tac >>
    metis_tac[]) >>
  (* Transfer preserves cond_const_sound *)
  `cond_const_sound (sccp_transfer_inst f inst
      (df_at sccp_bottom result lbl idx)).sl_vals
                    (s'' with vs_inst_idx := 0)` by (
    irule (BETA_RULE (REWRITE_RULE [transfer_sound_wf_def]
              (Q.SPEC `f` sccp_transfer_sound_cond))) >>
    metis_tac[]) >>
  (* nophi_sound follows from cond_const_sound (weaker) *)
  rpt gen_tac >> strip_tac >>
  gvs[cond_const_sound_def]
QED

(* --- np_c2: phi_bottom conjunct (non-PHI case) --- *)
Resume sccp_nophi_exit_props_from[np_c2]:
  rpt strip_tac >>
  `k < idx` by metis_tac[] >>
  `FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals y
     = SOME CL_Bottom` by metis_tac[] >>
  `~MEM y inst.inst_outputs` by
    metis_tac[ssa_no_output_overlap_inst,
      markerTheory.Abbrev_def, wf_ssa_def] >>
  metis_tac[sccp_transfer_non_output_flookup]
QED

(* --- np_c3: nophi_coverage conjunct (non-PHI case) --- *)
Resume sccp_nophi_exit_props_from[np_c3]:
  rpt gen_tac >> disch_tac >>
  (* Unconditional coverage at idx: bridge nophi + phi_bottom *)
  `!x'. x' IN FDOM s'.vs_vars ==>
      x' IN FDOM (df_at sccp_bottom result lbl idx).sl_vals /\
      FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x'
        <> SOME CL_Top` by
    suspend "np_c3_bridge" >>
  (* Apply transfer_sound_fdom *)
  mp_tac (BETA_RULE (REWRITE_RULE [transfer_sound_wf_def]
            (Q.SPEC `f` sccp_transfer_sound_fdom))) >>
  disch_then (qspecl_then [`fuel'`, `ctx'`,
    `df_at sccp_bottom result lbl idx`, `inst`,
    `s' with vs_inst_idx := 0`,
    `s'' with vs_inst_idx := 0`] mp_tac) >>
  simp[]
QED

(* --- np_c3_bridge: unconditional coverage at idx --- *)
Resume sccp_nophi_exit_props_from[np_c3_bridge]:
  (* Use nophi_phi_bottom_imp_coverage to bridge *)
  match_mp_tac (nophi_phi_bottom_imp_coverage
    |> Q.SPECL [`f`, `bb`, `instrs`, `lbl`]) >>
  simp[Abbr `lbl`] >>
  rpt gen_tac >> strip_tac >>
  `k < idx` by metis_tac[] >>
  qpat_assum `!k y. k < idx /\ _ ==> _`
    (qspecl_then [`k`, `y`] mp_tac) >>
  simp[]
QED

Resume sccp_nophi_exit_props_from[term_targets]:
  metis_tac[sccp_transfer_term_succ_in_targets]
QED

Finalise sccp_nophi_exit_props_from

(* Projections for callers that need only one half *)
Triviality sccp_nophi_exit_cond_sound[local]:
  !f bb fuel ctx s v.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals x
         <> SOME CL_Top) /\
    exec_block fuel ctx bb s = OK v ==>
    cond_const_sound
      (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
         (LENGTH bb.bb_instructions)).sl_vals v
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`f`, `bb`, `fuel`, `ctx`, `s`, `v`]
            sccp_nophi_exit_props_from) >>
  impl_tac >- gvs[] >>
  strip_tac >>
  gvs[]
QED

Triviality sccp_nophi_exit_covered[local]:
  !f bb s v fuel ctx.
    fn_inst_wf f /\ wf_function f /\ wf_ssa f /\
    MEM bb f.fn_blocks /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals x
         <> SOME CL_Top) /\
    exec_block fuel ctx bb s = OK v ==>
    (!x. x IN FDOM v.vs_vars ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
                    (LENGTH bb.bb_instructions)).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
                  (LENGTH bb.bb_instructions)).sl_vals x <> SOME CL_Top)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`f`, `bb`, `fuel`, `ctx`, `s`, `v`]
            sccp_nophi_exit_props_from) >>
  impl_tac >- gvs[] >>
  strip_tac >>
  gvs[]
QED

Triviality sccp_nophi_exit_succ_in_targets[local]:
  !f bb fuel ctx s v.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre /\
    s.vs_inst_idx = 0 /\
    (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals x
         <> SOME CL_Top) /\
    exec_block fuel ctx bb s = OK v ==>
    v.vs_current_bb IN
      (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
         (LENGTH bb.bb_instructions)).sl_targets
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`f`, `bb`, `fuel`, `ctx`, `s`, `v`]
            sccp_nophi_exit_props_from) >>
  impl_tac >- gvs[] >>
  strip_tac >>
  gvs[]
QED

(* Helper: lookup_block from fn_labels membership *)
Triviality fn_labels_lookup_block[local]:
  !f lbl. wf_function f /\ MEM lbl (fn_labels f) ==>
    ?bb. lookup_block lbl f.fn_blocks = SOME bb
Proof
  rpt strip_tac >>
  fs[fn_labels_def, listTheory.MEM_MAP] >>
  qexists_tac `bb` >>
  irule venomExecPropsTheory.MEM_lookup_block >>
  fs[wf_function_def, fn_labels_def]
QED

(* Helper: exit.sl_targets ⊆ boundary.sl_targets at fixpoint *)
Triviality sccp_boundary_contains_exit_targets[local]:
  !f lbl bb x.
    wf_function f /\ MEM lbl (cfg_analyze f).cfg_dfs_pre /\
    lookup_block lbl f.fn_blocks = SOME bb /\
    x IN (df_at sccp_bottom (sccp_df_analyze f) lbl
            (LENGTH bb.bb_instructions)).sl_targets ==>
    x IN (df_boundary sccp_bottom (sccp_df_analyze f) lbl).sl_targets
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`f`, `lbl`, `bb`] sccp_boundary_fixpoint) >>
  simp[] >> disch_tac >>
  pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
  simp[sccp_join_def]
QED

(* Helper: for non-PHI x, edge transfer preserves FLOOKUP from boundary *)
Triviality sccp_edge_non_phi_flookup[local]:
  !f src dst boundary_lat x.
    ~is_phi_output_of_block f.fn_blocks dst x /\
    dst IN boundary_lat.sl_targets ==>
    FLOOKUP (sccp_edge_transfer f src dst boundary_lat).sl_vals x =
    FLOOKUP boundary_lat.sl_vals x
Proof
  rpt strip_tac >>
  simp[sccp_edge_transfer_def] >>
  Cases_on `lookup_block dst f.fn_blocks` >> simp[]
  >- simp[sccp_eval_phis_for_edge_def] >>
  mp_tac (Q.SPECL [`x'.bb_instructions`, `src`, `boundary_lat.sl_vals`,
    `boundary_lat with sl_targets := {}`, `x`]
    sccp_eval_phis_preserves_non_phi) >>
  simp[] >> metis_tac[is_phi_output_of_block_def,
    venomExecPropsTheory.lookup_block_MEM]
QED

(* Helper: const_lookup through sccp_join sccp_bottom *)
Triviality const_lookup_join_bottom_left[local]:
  !lat x. const_lookup (sccp_join sccp_bottom lat).sl_vals x =
          const_lookup lat.sl_vals x
Proof
  rpt gen_tac >>
  `const_lookup (sccp_join sccp_bottom lat).sl_vals x =
   const_meet (const_lookup sccp_bottom.sl_vals x) (const_lookup lat.sl_vals x)` by
    metis_tac[sccp_join_const_lookup] >>
  simp[sccp_bottom_def, const_lookup_def, const_meet_def]
QED

(* Helper: sccp_joined member_const — connects joined to edge via FOLDL *)
Triviality sccp_joined_member_const[local]:
  !f lbl src e x c.
    wf_function f /\
    MEM lbl (cfg_analyze f).cfg_dfs_pre /\
    (?bb'. lookup_block lbl f.fn_blocks = SOME bb') /\
    MEM src (cfg_preds_of (cfg_analyze f) lbl) /\
    e = sccp_edge_transfer f src lbl
          (df_boundary sccp_bottom (sccp_df_analyze f) src) /\
    const_lookup e.sl_vals x <> CL_Top /\
    const_lookup (sccp_joined f (sccp_df_analyze f) lbl).sl_vals x =
      CL_Const c ==>
    const_lookup e.sl_vals x = CL_Const c
Proof
  rpt strip_tac >>
  qabbrev_tac `edge_vals = MAP (\nbr. sccp_edge_transfer f nbr lbl
    (df_boundary sccp_bottom (sccp_df_analyze f) nbr))
    (cfg_preds_of (cfg_analyze f) lbl)` >>
  `MEM e edge_vals` by (
    simp[Abbr `edge_vals`, listTheory.MEM_MAP] >>
    qexists_tac `src` >> simp[]) >>
  `edge_vals <> []` by (Cases_on `edge_vals` >> fs[]) >>
  (* Key: const_lookup joined = const_lookup (FOLDL join bottom edge_vals) *)
  `const_lookup (FOLDL sccp_join sccp_bottom edge_vals).sl_vals x =
   CL_Const c` by (
    qpat_x_assum `const_lookup (sccp_joined _ _ _).sl_vals _ = _` mp_tac >>
    simp[sccpConvergenceTheory.sccp_joined_def, LET_THM] >>
    Cases_on `edge_vals` >> fs[] >>
    Cases_on `fn_entry_label f` >> simp[] >>
    Cases_on `lbl = x'` >> simp[] >>
    metis_tac[const_lookup_join_bottom_left]) >>
  irule foldl_join_member_const >> metis_tac[]
QED

(* Helper: FDOM/¬Top through sccp_join sccp_bottom *)
Triviality fdom_no_top_join_bottom_left[local]:
  !lat x.
    x IN FDOM lat.sl_vals /\
    FLOOKUP lat.sl_vals x <> SOME CL_Top ==>
    x IN FDOM (sccp_join sccp_bottom lat).sl_vals /\
    FLOOKUP (sccp_join sccp_bottom lat).sl_vals x <> SOME CL_Top
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[sccp_join_fdom_right]
  >>
  `const_lookup (sccp_join sccp_bottom lat).sl_vals x =
   const_lookup lat.sl_vals x` by metis_tac[const_lookup_join_bottom_left] >>
  fs[const_lookup_def] >>
  Cases_on `FLOOKUP (sccp_join sccp_bottom lat).sl_vals x` >>
  fs[] >> Cases_on `FLOOKUP lat.sl_vals x` >> fs[flookup_thm]
QED

(* Helper: FDOM/¬Top coverage lifts from a single edge entry to sccp_joined.
   Per-variable version: given x ∈ FDOM e ∧ ¬Top in edge, same in joined. *)
Triviality sccp_joined_coverage_var[local]:
  !f lbl src e x.
    MEM src (cfg_preds_of (cfg_analyze f) lbl) /\
    e = sccp_edge_transfer f src lbl
          (df_boundary sccp_bottom (sccp_df_analyze f) src) /\
    x IN FDOM e.sl_vals /\ FLOOKUP e.sl_vals x <> SOME CL_Top ==>
    x IN FDOM (sccp_joined f (sccp_df_analyze f) lbl).sl_vals /\
    FLOOKUP (sccp_joined f (sccp_df_analyze f) lbl).sl_vals x <>
      SOME CL_Top
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `edge_vals = MAP (\nbr. sccp_edge_transfer f nbr lbl
    (df_boundary sccp_bottom (sccp_df_analyze f) nbr))
    (cfg_preds_of (cfg_analyze f) lbl)` >>
  `MEM e edge_vals` by (
    simp[Abbr `edge_vals`, listTheory.MEM_MAP] >>
    qexists_tac `src` >> simp[]) >>
  (* Get FOLDL coverage for this x via foldl_join_coverage_var *)
  `x IN FDOM (FOLDL sccp_join sccp_bottom edge_vals).sl_vals /\
   FLOOKUP (FOLDL sccp_join sccp_bottom edge_vals).sl_vals x <>
     SOME CL_Top` by metis_tac[foldl_join_coverage_var] >>
  (* Connect FOLDL to sccp_joined *)
  `edge_vals <> []` by (Cases_on `edge_vals` >> fs[]) >>
  (* Reduce sccp_joined to FOLDL or sccp_join sccp_bottom (FOLDL ...) *)
  spose_not_then strip_assume_tac >>
  `~(x IN FDOM (sccp_joined f (sccp_df_analyze f) lbl).sl_vals) \/
   FLOOKUP (sccp_joined f (sccp_df_analyze f) lbl).sl_vals x = SOME CL_Top` by
    metis_tac[] >|
  [(* Case 1: x not in FDOM joined *)
   qpat_x_assum `x NOTIN FDOM _` mp_tac >>
   simp[sccpConvergenceTheory.sccp_joined_def, LET_THM] >>
   Cases_on `edge_vals` >> fs[] >>
   Cases_on `fn_entry_label f` >> simp[] >>
   Cases_on `lbl = x'` >> simp[] >>
   metis_tac[fdom_no_top_join_bottom_left, flookup_thm],
   (* Case 2: FLOOKUP joined = SOME CL_Top *)
   qpat_x_assum `FLOOKUP (sccp_joined _ _ _).sl_vals _ = SOME CL_Top` mp_tac >>
   simp[sccpConvergenceTheory.sccp_joined_def, LET_THM] >>
   Cases_on `edge_vals` >> fs[] >>
   Cases_on `fn_entry_label f` >> simp[] >>
   Cases_on `lbl = x'` >> simp[] >>
   metis_tac[fdom_no_top_join_bottom_left]]
QED

(* ===== Cross-block invariant: nophi sound + coverage preserved ===== *)
(* Cross-block transfer: nophi_sound and nophi_coverage preserved from
   block entry to successor entry *)
Triviality sccp_cross_block_inv:
  !f bb fuel ctx s v.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre /\
    s.vs_inst_idx <= PRE (LENGTH bb.bb_instructions) /\
    (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
              bb.bb_label s.vs_inst_idx).sl_vals x = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!k y. k < s.vs_inst_idx /\ k < LENGTH bb.bb_instructions /\
           (EL k bb.bb_instructions).inst_opcode = PHI /\
           MEM y (EL k bb.bb_instructions).inst_outputs ==>
           FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
              bb.bb_label s.vs_inst_idx).sl_vals y = SOME CL_Bottom) /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f)
                    bb.bb_label s.vs_inst_idx).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
                  bb.bb_label s.vs_inst_idx).sl_vals x <> SOME CL_Top) /\
    s.vs_current_bb = bb.bb_label /\
    exec_block fuel ctx bb s = OK v ==>
    (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) v.vs_current_bb 0).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM v.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks v.vs_current_bb x ==>
           FLOOKUP v.vs_vars x = SOME c) /\
    (!x. x IN FDOM v.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks v.vs_current_bb x ==>
       x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) v.vs_current_bb 0).sl_vals /\
       FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) v.vs_current_bb 0).sl_vals x
         <> SOME CL_Top) /\
    MEM v.vs_current_bb (cfg_analyze f).cfg_dfs_pre
Proof
  rpt gen_tac >> strip_tac >>
  (* === Shared setup: derive all structural + join facts === *)
  (* Exit properties *)
  `cond_const_sound
     (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
        (LENGTH bb.bb_instructions)).sl_vals v /\
   (!x. x IN FDOM v.vs_vars ==>
     x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
        (LENGTH bb.bb_instructions)).sl_vals /\
     FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
        (LENGTH bb.bb_instructions)).sl_vals x <> SOME CL_Top) /\
   v.vs_current_bb IN
     (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
        (LENGTH bb.bb_instructions)).sl_targets` by (
    mp_tac (Q.SPECL [`f`, `bb`, `fuel`, `ctx`, `s`, `v`]
      sccp_nophi_exit_props_from) >>
    impl_tac >- metis_tac[] >>
    simp[]) >>
  (* dfs_pre membership *)
  `MEM v.vs_current_bb (cfg_analyze f).cfg_dfs_pre` by suspend "xb_dfs_pre" >>
  simp[] >>
  (* Structural facts *)
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `bb.bb_instructions <> []` by (fs[bb_well_formed_def]) >>
  `ALL_DISTINCT (fn_labels f)` by fs[wf_function_def] >>
  `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
    metis_tac[venomExecPropsTheory.MEM_lookup_block, fn_labels_def] >>
  `?bb'. lookup_block v.vs_current_bb f.fn_blocks = SOME bb'` by (
    `MEM v.vs_current_bb (fn_labels f)` by
      metis_tac[dfAnalyzePropsTheory.cfg_dfs_pre_subset_fn_labels,
                listTheory.MEM_FLAT, listTheory.MEM] >>
    metis_tac[fn_labels_lookup_block]) >>
  (* bb.bb_label is predecessor of v.vs_current_bb *)
  `EVERY inst_wf bb.bb_instructions` by (
    simp[listTheory.EVERY_MEM] >> metis_tac[fn_inst_wf_def]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> fs[bb_well_formed_def] >>
    `i = PRE (LENGTH bb.bb_instructions)` by (first_x_assum irule >> simp[]) >>
    fs[]) >>
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
  `MEM bb.bb_label (cfg_preds_of (cfg_analyze f) v.vs_current_bb)` by (
    `MEM v.vs_current_bb (bb_succs bb)` by
      metis_tac[venomExecPropsTheory.exec_block_current_bb_in_succs] >>
    metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs,
              cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]) >>
  (* sl_targets chain *)
  `v.vs_current_bb IN
     (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
        (LENGTH bb.bb_instructions)).sl_targets` by
    metis_tac[] >>
  `v.vs_current_bb IN
     (df_boundary sccp_bottom (sccp_df_analyze f) bb.bb_label).sl_targets` by (
    mp_tac (Q.SPECL [`f`, `bb.bb_label`, `bb`] sccp_boundary_fixpoint) >>
    simp[] >> disch_tac >>
    `(sccp_join (df_boundary sccp_bottom (sccp_df_analyze f) bb.bb_label)
        (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
           (LENGTH bb.bb_instructions))).sl_targets =
     (df_boundary sccp_bottom (sccp_df_analyze f) bb.bb_label).sl_targets` by
      metis_tac[] >>
    fs[sccp_join_def] >> metis_tac[pred_setTheory.UNION_DEF,
      pred_setTheory.IN_UNION]) >>
  (* Abbreviations for lattice values *)
  qabbrev_tac `boundary_bb =
    df_boundary sccp_bottom (sccp_df_analyze f) bb.bb_label` >>
  qabbrev_tac `exit_bb =
    df_at sccp_bottom (sccp_df_analyze f) bb.bb_label
      (LENGTH bb.bb_instructions)` >>
  qabbrev_tac `edge =
    sccp_edge_transfer f bb.bb_label v.vs_current_bb boundary_bb` >>
  qabbrev_tac `joined =
    sccp_joined f (sccp_df_analyze f) v.vs_current_bb` >>
  (* df_at 0 at successor = joined *)
  `df_at sccp_bottom (sccp_df_analyze f) v.vs_current_bb 0 = joined` by (
    simp[Abbr `joined`] >>
    irule sccp_inter_fwd >> metis_tac[]) >>
  (* boundary fixpoint equation *)
  `boundary_bb = sccp_join boundary_bb exit_bb` by
    metis_tac[sccp_boundary_fixpoint, markerTheory.Abbrev_def] >>
  (* const_lookup boundary_bb for non-PHI x: <> CL_Top *)
  `!x. x IN FDOM v.vs_vars /\
       ~is_phi_output_of_block f.fn_blocks v.vs_current_bb x ==>
       const_lookup boundary_bb.sl_vals x <> CL_Top` by (
    rpt strip_tac >>
    `x IN FDOM exit_bb.sl_vals /\
     FLOOKUP exit_bb.sl_vals x <> SOME CL_Top` by metis_tac[] >>
    `const_lookup exit_bb.sl_vals x <> CL_Top` by
      metis_tac[flookup_no_top_const_lookup] >>
    `const_lookup boundary_bb.sl_vals x =
     const_meet (const_lookup boundary_bb.sl_vals x)
                (const_lookup exit_bb.sl_vals x)` by (
      `const_lookup (sccp_join boundary_bb exit_bb).sl_vals x =
       const_meet (const_lookup boundary_bb.sl_vals x)
                  (const_lookup exit_bb.sl_vals x)` by
        metis_tac[sccp_join_const_lookup] >>
      metis_tac[]) >>
    metis_tac[const_meet_not_top]) >>
  (* FLOOKUP edge = FLOOKUP boundary for non-PHI x *)
  `!x. ~is_phi_output_of_block f.fn_blocks v.vs_current_bb x ==>
       FLOOKUP edge.sl_vals x = FLOOKUP boundary_bb.sl_vals x` by
    metis_tac[sccp_edge_non_phi_flookup, markerTheory.Abbrev_def] >>
  (* Edge coverage for non-PHI: FDOM + ¬Top *)
  `!x. x IN FDOM v.vs_vars /\
       ~is_phi_output_of_block f.fn_blocks v.vs_current_bb x ==>
       x IN FDOM edge.sl_vals /\
       FLOOKUP edge.sl_vals x <> SOME CL_Top` by (
    rpt strip_tac >> (
    `FLOOKUP edge.sl_vals x = FLOOKUP boundary_bb.sl_vals x` by metis_tac[] >>
    `const_lookup boundary_bb.sl_vals x <> CL_Top` by metis_tac[] >>
    fs[const_lookup_def] >>
    Cases_on `FLOOKUP boundary_bb.sl_vals x` >> fs[flookup_thm])) >>
  (* === Now split into xb_sound and xb_covered === *)
  rpt conj_tac
  >- suspend "xb_sound"
  >- suspend "xb_covered"
QED

(* --- xb_dfs_pre: successor is in cfg_dfs_pre --- *)
Resume sccp_cross_block_inv[xb_dfs_pre]:
  fs[wf_function_def] >>
  `bb_well_formed bb` by metis_tac[] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >>
    `bb_well_formed bb` by metis_tac[] >>
    fs[bb_well_formed_def] >>
    `i = PRE (LENGTH bb.bb_instructions)` by
      (first_x_assum irule >> simp[]) >>
    fs[]) >>
  `s.vs_inst_idx <= LENGTH bb.bb_instructions` by decide_tac >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[venomExecPropsTheory.exec_block_current_bb_in_succs] >>
  `MEM v.vs_current_bb (cfg_succs_of (cfg_analyze f) bb.bb_label)` by
    metis_tac[cfgAnalysisPropsTheory.bb_succs_in_cfg_succs] >>
  imp_res_tac cfg_dfs_pre_succs_closed >> fs[EVERY_MEM]
QED

(* --- xb_sound: nophi_sound at successor --- *)
Resume sccp_cross_block_inv[xb_sound]:
  rpt gen_tac >> strip_tac >>
  (* Rewrite df_at 0 at successor to joined in goal *)
  `FLOOKUP joined.sl_vals x = SOME (CL_Const c)` by metis_tac[] >>
  (* const_lookup edge.sl_vals x <> CL_Top *)
  `const_lookup edge.sl_vals x <> CL_Top` by (
    `x IN FDOM edge.sl_vals /\ FLOOKUP edge.sl_vals x <> SOME CL_Top` by
      metis_tac[] >>
    metis_tac[flookup_no_top_const_lookup]) >>
  `const_lookup joined.sl_vals x = CL_Const c` by
    (simp[const_lookup_def]) >>
  (* sccp_joined_member_const: const_lookup edge x = CL_Const c *)
  `const_lookup edge.sl_vals x = CL_Const c` by
    metis_tac[sccp_joined_member_const, markerTheory.Abbrev_def] >>
  (* Chain: edge -> boundary -> exit -> cond_const_sound *)
  `const_lookup boundary_bb.sl_vals x = CL_Const c` by (
    `FLOOKUP edge.sl_vals x = FLOOKUP boundary_bb.sl_vals x` by metis_tac[] >>
    fs[const_lookup_def] >>
    Cases_on `FLOOKUP boundary_bb.sl_vals x` >> fs[] >>
    Cases_on `FLOOKUP edge.sl_vals x` >> fs[]) >>
  `const_lookup exit_bb.sl_vals x = CL_Const c` by (
    `const_lookup (sccp_join boundary_bb exit_bb).sl_vals x =
     const_meet (const_lookup boundary_bb.sl_vals x)
                (const_lookup exit_bb.sl_vals x)` by
      metis_tac[sccp_join_const_lookup] >>
    `x IN FDOM exit_bb.sl_vals /\ FLOOKUP exit_bb.sl_vals x <> SOME CL_Top` by
      metis_tac[] >>
    `const_lookup exit_bb.sl_vals x <> CL_Top` by
      metis_tac[flookup_no_top_const_lookup] >>
    metis_tac[const_meet_const_right]) >>
  `FLOOKUP exit_bb.sl_vals x = SOME (CL_Const c)` by (
    fs[const_lookup_def] >>
    Cases_on `FLOOKUP exit_bb.sl_vals x` >> fs[]) >>
  fs[cond_const_sound_def]
QED

(* --- xb_covered: nophi_coverage at successor --- *)
Resume sccp_cross_block_inv[xb_covered]:
  rpt gen_tac >> strip_tac >>
  (* Get edge coverage for this specific x *)
  `x IN FDOM edge.sl_vals /\ FLOOKUP edge.sl_vals x <> SOME CL_Top` by
    metis_tac[] >>
  (* Lift to joined via sccp_joined_coverage_var *)
  `x IN FDOM (sccp_joined f (sccp_df_analyze f) v.vs_current_bb).sl_vals /\
   FLOOKUP (sccp_joined f (sccp_df_analyze f) v.vs_current_bb).sl_vals x <>
     SOME CL_Top` by
    metis_tac[sccp_joined_coverage_var, markerTheory.Abbrev_def] >>
  (* Rewrite from sccp_joined to df_at 0 via abbreviations *)
  metis_tac[markerTheory.Abbrev_def]
QED

Finalise sccp_cross_block_inv

(* ===== Per-block simulation ===== *)

(* SCCP per-block simulation under cond_const_sound: execution is
   equivalent or both produce Error *)
Theorem sccp_per_block_sim:
  !fn bb.
    wf_function fn /\ fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      cond_const_sound
        (df_at sccp_bottom (sccp_df_analyze fn) bb.bb_label 0).sl_vals s ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
          (analysis_block_transform sccp_bottom (sccp_df_analyze fn)
            (\lat inst. [sccp_inst lat.sl_vals inst]) bb) s)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def])
  \\
  irule (analysisSimProofsBaseTheory.analysis_block_sim_wf
    |> INST_TYPE [alpha |-> ``:sccp_lattice``, beta |-> ``:ir_function``]
    |> Q.SPECL [`state_equiv {}`, `execution_equiv {}`]
    |> REWRITE_RULE [GSYM AND_IMP_INTRO]
    |> Q.SPECL [`\lat. cond_const_sound lat.sl_vals`,
                `\lat inst. [sccp_inst lat.sl_vals inst]`]
    |> BETA_RULE) >>
  simp[state_equiv_execution_equiv_valid_state_rel,
       sccp_inst_simulates_cond]
  \\
  rpt conj_tac
  >- (rpt strip_tac >> imp_res_tac state_equiv_empty_lookup_var >> gvs[])
  >- (qexistsl_tac [[QUOTE "fn"], `sccp_transfer_inst`] >> rpt conj_tac
      >- (rpt strip_tac >>
          irule (BETA_RULE (REWRITE_RULE [transfer_sound_wf_def]
                    (Q.SPEC [QUOTE "fn"] sccp_transfer_sound_cond))) >>
          metis_tac[])
      >> (rpt strip_tac >> irule sccp_intra_fwd >> metis_tac[]))
  >- metis_tac[cond_const_sound_state_equiv]
  >- metis_tac[execution_equiv_trans]
  >> metis_tac[state_equiv_trans]
QED


(* The function entry label is in cfg_dfs_pre *)
Theorem entry_label_in_dfs_pre:
  !fn lbl. fn_entry_label fn = SOME lbl ==>
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  rpt strip_tac >> fs[fn_entry_label_def] >>
  Cases_on `entry_block fn` >> gvs[] >>
  imp_res_tac cfg_analyze_preorder_entry_first >>
  Cases_on `(cfg_analyze fn).cfg_dfs_pre` >> gvs[]
QED

(* ===== Function-level lift_result ===== *)

(* FLAT (MAPi with singleton wrapper) = MAPi *)
Theorem flat_mapi_singleton:
  !(g:num -> 'a -> 'b) l.
    FLAT (MAPi (\i x. [g i x]) l) = MAPi g l
Proof
  Induct_on `l` >> simp[indexedListsTheory.MAPi_def] >>
  rpt strip_tac >> first_x_assum (qspec_then `g o SUC` mp_tac) >>
  simp[combinTheory.o_DEF]
QED

(* SCCP block transformation preserves instruction count *)
Theorem sccp_bt_length:
  !(bb:basic_block) bottom result
   (f:sccp_lattice -> instruction -> instruction list).
   (!lat inst. f lat inst = [sccp_inst lat.sl_vals inst]) ==>
   LENGTH (analysis_block_transform bottom result f bb).bb_instructions =
   LENGTH bb.bb_instructions
Proof
  rpt strip_tac >> simp[analysis_block_transform_def] >>
  ASM_REWRITE_TAC[] >> simp[flat_mapi_singleton, indexedListsTheory.LENGTH_MAPi]
QED

(* SCCP block transformation: EL idx of transformed instructions equals
   sccp_inst of the original instruction with its lattice state *)
Theorem sccp_bt_el:
  !(bb:basic_block) bottom result
   (f:sccp_lattice -> instruction -> instruction list) idx.
   (!lat inst. f lat inst = [sccp_inst lat.sl_vals inst]) /\
   idx < LENGTH bb.bb_instructions ==>
   EL idx (analysis_block_transform bottom result f bb).bb_instructions =
     sccp_inst (df_at bottom result bb.bb_label idx).sl_vals
               (EL idx bb.bb_instructions)
Proof
  rpt strip_tac >> simp[analysis_block_transform_def] >>
  ASM_REWRITE_TAC[] >> simp[flat_mapi_singleton, indexedListsTheory.EL_MAPi]
QED

(* sccp_inst is the identity on PHI instructions *)
Theorem sccp_inst_phi_identity:
  !st inst. inst.inst_opcode = PHI ==> sccp_inst st inst = inst
Proof
  simp[sccp_inst_def]
QED

(* PHI outputs get CL_Bottom in sccp_transfer_inst *)
Triviality sccp_transfer_phi_bottom:
  !f inst lat y.
    inst.inst_opcode = PHI /\ MEM y inst.inst_outputs ==>
    FLOOKUP (sccp_transfer_inst f inst lat).sl_vals y = SOME CL_Bottom
Proof
  rpt strip_tac >> simp[sccp_transfer_inst_def] >>
  metis_tac[cj 1 foldl_fupdate_bottom]
QED

(* PHI invariant preservation: since PHI is identity-transformed,
   non-output vars are unchanged by step_inst *)
Triviality phi_inv_pres_tac:
  !f bb instrs lbl result idx inst s s' fuel ctx.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\ ssa_form f /\
    MEM bb f.fn_blocks /\
    lookup_block lbl f.fn_blocks = SOME bb /\
    lbl = bb.bb_label /\ instrs = bb.bb_instructions /\
    inst_wf inst /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\
    idx < LENGTH instrs /\ inst = EL idx instrs /\
    result = sccp_df_analyze f /\
    step_inst fuel ctx inst (s with vs_inst_idx := idx) = OK s' /\
    SUC idx <= LENGTH instrs /\
    df_at sccp_bottom result lbl (SUC idx) =
      sccp_transfer_inst f (EL idx instrs)
        (df_at sccp_bottom result lbl idx) /\
    (!x c. FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks lbl x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks lbl x ==>
       x IN FDOM (df_at sccp_bottom result lbl idx).sl_vals /\
       FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x
         <> SOME CL_Top) /\
    (!k. k < idx ==>
      !y. MEM y (EL k instrs).inst_outputs ==>
          (EL k instrs).inst_opcode = PHI ==>
          FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals y
            = SOME CL_Bottom)
    ==>
    (!x c. FLOOKUP (df_at sccp_bottom result lbl (SUC idx)).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s'.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks lbl x ==>
           FLOOKUP s'.vs_vars x = SOME c) /\
    (!x. x IN FDOM s'.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks lbl x ==>
       x IN FDOM (df_at sccp_bottom result lbl (SUC idx)).sl_vals /\
       FLOOKUP (df_at sccp_bottom result lbl (SUC idx)).sl_vals x
         <> SOME CL_Top) /\
    (!k. k < SUC idx ==>
      !y. MEM y (EL k instrs).inst_outputs ==>
          (EL k instrs).inst_opcode = PHI ==>
          FLOOKUP (df_at sccp_bottom result lbl (SUC idx)).sl_vals y
            = SOME CL_Bottom)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `~is_terminator (EL idx (bb.bb_instructions)).inst_opcode` by
    simp[is_terminator_def] >>
  rpt conj_tac
  (* C1: nophi_sound *)
  >- (rpt strip_tac >>
      `~MEM x (EL idx (bb.bb_instructions)).inst_outputs` by
        metis_tac[is_phi_output_of_block_def] >>
      `FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx).sl_vals x =
       SOME (CL_Const c)` by
        metis_tac[sccp_transfer_non_output_flookup] >>
      `lookup_var x s' = lookup_var x (s with vs_inst_idx := idx)` by
        (irule step_preserves_non_output_vars >> metis_tac[]) >>
      `x IN FDOM (s with vs_inst_idx := idx).vs_vars` by
        metis_tac[lookup_var_fdom_back] >>
      fs[lookup_var_def])
  (* C2: nophi_coverage *)
  >- (rpt gen_tac >> strip_tac >>
      `~MEM x (EL idx (bb.bb_instructions)).inst_outputs` by
        metis_tac[is_phi_output_of_block_def] >>
      `lookup_var x s' = lookup_var x (s with vs_inst_idx := idx)` by
        (irule step_preserves_non_output_vars >> metis_tac[]) >>
      `x IN FDOM (s with vs_inst_idx := idx).vs_vars` by
        metis_tac[lookup_var_fdom_back] >>
      `x IN FDOM s.vs_vars` by fs[] >>
      conj_tac
      >- (`x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx).sl_vals` by
            metis_tac[] >>
          metis_tac[sccp_transfer_fdom_mono])
      >- (`FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx).sl_vals x <>
           SOME CL_Top` by metis_tac[] >>
          metis_tac[sccp_transfer_non_output_flookup]))
  (* C3: phi_bottom *)
  >> (rpt strip_tac >>
      Cases_on `k = idx`
      >- metis_tac[sccp_transfer_phi_bottom]
      >- (`k < idx` by decide_tac >>
          `FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx).sl_vals y
             = SOME CL_Bottom` by metis_tac[] >>
          `idx < LENGTH bb.bb_instructions` by decide_tac >>
          `k < LENGTH bb.bb_instructions` by decide_tac >>
          `~MEM y (EL idx (bb.bb_instructions)).inst_outputs` by
            metis_tac[ssa_no_output_overlap_inst, wf_ssa_def] >>
          metis_tac[sccp_transfer_non_output_flookup]))
QED

(* Non-PHI invariant preservation: uses transfer_sound_cond/fdom *)
Triviality nonphi_inv_pres_tac:
  !f bb instrs lbl result idx inst s s' fuel ctx.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\ ssa_form f /\
    MEM bb f.fn_blocks /\
    lookup_block lbl f.fn_blocks = SOME bb /\
    lbl = bb.bb_label /\ instrs = bb.bb_instructions /\
    inst_wf inst /\ MEM inst bb.bb_instructions /\
    ~(inst.inst_opcode = PHI) /\ ~is_terminator inst.inst_opcode /\
    bb_well_formed bb /\
    idx < LENGTH instrs /\ inst = EL idx instrs /\
    result = sccp_df_analyze f /\
    step_inst fuel ctx inst (s with vs_inst_idx := idx) = OK s' /\
    SUC idx <= LENGTH instrs /\
    df_at sccp_bottom result lbl (SUC idx) =
      sccp_transfer_inst f (EL idx instrs)
        (df_at sccp_bottom result lbl idx) /\
    cond_const_sound (df_at sccp_bottom result lbl idx).sl_vals
      (s with vs_inst_idx := idx) /\
    (!k. k < LENGTH instrs /\ (EL k instrs).inst_opcode = PHI ==>
     k < idx) /\
    (!x c. FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks lbl x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!x. x IN FDOM s.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks lbl x ==>
       x IN FDOM (df_at sccp_bottom result lbl idx).sl_vals /\
       FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x
         <> SOME CL_Top) /\
    (!k. k < idx ==>
      !y. MEM y (EL k instrs).inst_outputs ==>
          (EL k instrs).inst_opcode = PHI ==>
          FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals y
            = SOME CL_Bottom)
    ==>
    (!x c. FLOOKUP (df_at sccp_bottom result lbl (SUC idx)).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s'.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks lbl x ==>
           FLOOKUP s'.vs_vars x = SOME c) /\
    (!x. x IN FDOM s'.vs_vars /\
         ~is_phi_output_of_block f.fn_blocks lbl x ==>
       x IN FDOM (df_at sccp_bottom result lbl (SUC idx)).sl_vals /\
       FLOOKUP (df_at sccp_bottom result lbl (SUC idx)).sl_vals x
         <> SOME CL_Top) /\
    (!k. k < SUC idx ==>
      !y. MEM y (EL k instrs).inst_outputs ==>
          (EL k instrs).inst_opcode = PHI ==>
          FLOOKUP (df_at sccp_bottom result lbl (SUC idx)).sl_vals y
            = SOME CL_Bottom)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  (* Derive unconditional coverage for transfer_sound_fdom *)
  `!x'. x' IN FDOM (s with vs_inst_idx := idx).vs_vars ==>
      x' IN FDOM (df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx).sl_vals /\
      FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx).sl_vals x'
        <> SOME CL_Top` by (
    match_mp_tac (nophi_phi_bottom_imp_coverage
      |> Q.SPECL [`f`, `bb`, `bb.bb_instructions`, `bb.bb_label`]) >>
    simp[] >> rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
  rpt conj_tac
  (* C1: nophi_sound *)
  >- (`cond_const_sound (sccp_transfer_inst f (EL idx (bb.bb_instructions))
          (df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx)).sl_vals s'` by (
        irule (BETA_RULE (REWRITE_RULE [transfer_sound_wf_def]
                  (Q.SPEC `f` sccp_transfer_sound_cond))) >>
        metis_tac[]) >>
      rpt gen_tac >> strip_tac >>
      gvs[cond_const_sound_def])
  (* C2: nophi_coverage *)
  >- (rpt gen_tac >> disch_tac >>
      mp_tac (BETA_RULE (REWRITE_RULE [transfer_sound_wf_def]
                (Q.SPEC `f` sccp_transfer_sound_fdom))) >>
      disch_then (qspecl_then [`fuel`, `ctx`,
        `df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx`,
        `EL idx (bb.bb_instructions)`,
        `s with vs_inst_idx := idx`, `s'`] mp_tac) >>
      simp[])
  (* C3: phi_bottom *)
  >> (rpt strip_tac >>
      `k < LENGTH bb.bb_instructions` by decide_tac >>
      `k < idx` by metis_tac[] >>
      `FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) (bb.bb_label) idx).sl_vals y
         = SOME CL_Bottom` by metis_tac[] >>
      `idx < LENGTH bb.bb_instructions` by decide_tac >>
      `~MEM y (EL idx (bb.bb_instructions)).inst_outputs` by
        metis_tac[ssa_no_output_overlap_inst, wf_ssa_def] >>
      metis_tac[sccp_transfer_non_output_flookup])
QED

(* Helper: at a non-PHI instruction, all PHIs are before us and cond_const_sound holds *)
Triviality nophi_at_idx:
  !f bb idx s result lbl instrs.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\ bb_well_formed bb /\
    instrs = bb.bb_instructions /\ lbl = bb.bb_label /\
    result = sccp_df_analyze f /\
    lookup_block lbl f.fn_blocks = SOME bb /\
    idx < LENGTH instrs /\ ~((EL idx instrs).inst_opcode = PHI) /\
    (!x c. FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals x
              = SOME (CL_Const c) /\
           x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks lbl x ==>
           FLOOKUP s.vs_vars x = SOME c) /\
    (!k. k < idx ==>
      !y. MEM y (EL k instrs).inst_outputs ==>
          (EL k instrs).inst_opcode = PHI ==>
          FLOOKUP (df_at sccp_bottom result lbl idx).sl_vals y
            = SOME CL_Bottom) ==>
    (!k. k < LENGTH instrs /\ (EL k instrs).inst_opcode = PHI ==> k < idx) /\
    cond_const_sound (df_at sccp_bottom result lbl idx).sl_vals
      (s with vs_inst_idx := idx)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `!k. k < LENGTH bb.bb_instructions /\
       (EL k bb.bb_instructions).inst_opcode = PHI ==> k < idx` by (
    rpt strip_tac >> spose_not_then assume_tac >>
    `idx <= k` by decide_tac >>
    Cases_on `k = idx` >- metis_tac[] >>
    `idx < k` by decide_tac >> metis_tac[bb_well_formed_def]) >>
  conj_tac >- metis_tac[] >>
  match_mp_tac (nophi_phi_bottom_imp_cond
    |> Q.SPECL [`f`, `bb`, `bb.bb_instructions`, `bb.bb_label`]) >>
  simp[] >> rpt strip_tac >>
  `k < idx` by metis_tac[] >> metis_tac[]
QED

(* Core block induction with nophi invariant: backward induction from
   terminator shows per-block equivalence or Error disjunction *)
Theorem sccp_block_induction_core:
  !f bb.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre ==>
    !n idx fuel ctx s.
      n = LENGTH bb.bb_instructions - idx /\
      s.vs_inst_idx = idx /\ idx <= LENGTH bb.bb_instructions /\
      (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
                bb.bb_label idx).sl_vals x
                = SOME (CL_Const c) /\
             x IN FDOM s.vs_vars /\
             ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
             FLOOKUP s.vs_vars x = SOME c) /\
      (!x. x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
         x IN FDOM (df_at sccp_bottom (sccp_df_analyze f)
                bb.bb_label idx).sl_vals /\
         FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
                bb.bb_label idx).sl_vals x
           <> SOME CL_Top) /\
      (!k. k < idx ==>
        !y. MEM y (EL k bb.bb_instructions).inst_outputs ==>
            (EL k bb.bb_instructions).inst_opcode = PHI ==>
            FLOOKUP (df_at sccp_bottom (sccp_df_analyze f)
                bb.bb_label idx).sl_vals y
              = SOME CL_Bottom)
      ==>
      (?e. exec_block fuel ctx bb (s with vs_inst_idx := idx) = Error e) \/
      lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
        (exec_block fuel ctx bb (s with vs_inst_idx := idx))
        (exec_block fuel ctx
          (analysis_block_transform sccp_bottom (sccp_df_analyze f)
            (\lat inst. [sccp_inst lat.sl_vals inst]) bb)
          (s with vs_inst_idx := idx))
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[EVERY_MEM, fn_inst_wf_def] >> metis_tac[]) >>
  `bb_well_formed bb` by metis_tac[wf_function_bb_well_formed] >>
  `ssa_form f` by fs[wf_ssa_def] >>
  `lookup_block bb.bb_label f.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> fs[wf_function_def, fn_labels_def]) >>
  qabbrev_tac `result = sccp_df_analyze f` >>
  qabbrev_tac `lbl = bb.bb_label` >>
  qabbrev_tac `instrs = bb.bb_instructions` >>
  qabbrev_tac `bt = analysis_block_transform sccp_bottom result
    (\lat inst. [sccp_inst lat.sl_vals inst]) bb` >>
  `LENGTH bt.bb_instructions = LENGTH instrs` by
    (simp[Abbr `bt`, Abbr `instrs`] >> irule sccp_bt_length >> simp[]) >>
  `!idx. idx < LENGTH instrs ==>
     EL idx bt.bb_instructions =
       sccp_inst (df_at sccp_bottom result lbl idx).sl_vals (EL idx instrs)` by
    (rpt strip_tac >> simp[Abbr `bt`, Abbr `instrs`, Abbr `lbl`] >>
     irule sccp_bt_el >> simp[]) >>
  (* Intra-forward equation *)
  `!idx. SUC idx <= LENGTH instrs ==>
     df_at sccp_bottom result lbl (SUC idx) =
     sccp_transfer_inst f (EL idx instrs)
       (df_at sccp_bottom result lbl idx)` by
    (rpt strip_tac >> unabbrev_all_tac >>
     irule sccp_intra_fwd >> metis_tac[]) >>
  Induct >> rpt strip_tac
  >- (
    (* Base: n=0 => idx = LENGTH instrs => past end *)
    `idx = LENGTH instrs` by simp[] >>
    ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
    simp[get_instruction_def])
  >- suspend "step"
QED

Resume sccp_block_induction_core[step]:
  (* Step case *)
  `idx < LENGTH instrs` by simp[] >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.exec_block_def] >>
  simp[get_instruction_def] >>
  `idx < LENGTH bt.bb_instructions` by simp[] >>
  simp[] >>
  qabbrev_tac `inst = EL idx instrs` >>
  `EL idx bt.bb_instructions =
     sccp_inst (df_at sccp_bottom result lbl idx).sl_vals inst` by
    (simp[Abbr `inst`] >> qpat_assum `!idx. idx < LENGTH instrs ==> _`
      (fn th => irule th) >> simp[]) >>
  simp[] >>
  `inst_wf inst` by (fs[EVERY_EL, Abbr `inst`]) >>
  `MEM inst bb.bb_instructions` by
    (simp[markerTheory.Abbrev_def] >> metis_tac[MEM_EL]) >>
  (* Key step: establish sccp_inst equivalence for non-error *)
  `(!e. step_inst fuel ctx inst (s with vs_inst_idx := idx) <> Error e) ==>
   step_inst fuel ctx
     (sccp_inst (df_at sccp_bottom result lbl idx).sl_vals inst)
     (s with vs_inst_idx := idx) =
   step_inst fuel ctx inst (s with vs_inst_idx := idx)` by (
    strip_tac >>
    Cases_on `inst.inst_opcode = PHI`
    >- (`sccp_inst (df_at sccp_bottom result lbl idx).sl_vals inst = inst` by
          metis_tac[sccp_inst_phi_identity] >> simp[])
    >>
    mp_tac (Q.SPECL [`f`, `bb`, `idx`, `s`, `result`, `lbl`, `instrs`]
      nophi_at_idx) >>
    simp[markerTheory.Abbrev_def] >>
    strip_tac >>
    metis_tac[sccp_inst_cond_eq]) >>
  (* Case-split on step_inst result *)
  Cases_on `step_inst fuel ctx inst (s with vs_inst_idx := idx)`
  >- suspend "ok_case"
  >- simp[lift_result_def, execution_equiv_refl]
  >- simp[lift_result_def, execution_equiv_refl]
  >- simp[lift_result_def, execution_equiv_refl]
  >- simp[]
QED


Resume sccp_block_induction_core[ok_case]:
    (* Consume ALL abbreviations so assumptions and goal use concrete names.
       This avoids the simp[] asymmetry where simp substitutes in the goal
       but not in assumptions. *)
    simp[Abbr `inst`, Abbr `lbl`, Abbr `instrs`, Abbr `result`] >>
    simp[sccp_inst_is_terminator] >>
    Cases_on `is_terminator (EL idx (bb.bb_instructions)).inst_opcode` >> simp[]
    >- (IF_CASES_TAC >>
        simp[lift_result_def, state_equiv_refl, execution_equiv_refl])
    >>
    Cases_on `(EL idx (bb.bb_instructions)).inst_opcode = PHI`
    >- suspend "phi_step"
    >- suspend "nonphi_step"
QED

Resume sccp_block_induction_core[phi_step]:
    (* PHI case: use phi_inv_pres_tac then apply IH *)
    mp_tac (Q.SPECL [`f`, `bb`, `bb.bb_instructions`, `bb.bb_label`,
      `sccp_df_analyze f`, `idx`, `EL idx (bb.bb_instructions)`,
      `s`, `v`, `fuel`, `ctx`] phi_inv_pres_tac) >>
    simp[] >>
    (* phi_inv_pres_tac leaves phi_bottom premise undischarged: resolve it *)
    (impl_tac >- first_assum ACCEPT_TAC) >>
    strip_tac >>
    (* Apply IH directly *)
    first_x_assum (qspecl_then
      [`SUC idx`, `fuel`, `ctx`, `v with vs_inst_idx := SUC idx`] mp_tac) >>
    simp[] >>
    disch_then irule >>
    first_assum ACCEPT_TAC
QED

Resume sccp_block_induction_core[nonphi_step]:
    (* Non-PHI case: establish nophi_at_idx, then nonphi_inv_pres_tac, then IH *)
    mp_tac (Q.SPECL [`f`, `bb`, `idx`, `s`, `sccp_df_analyze f`,
      `bb.bb_label`, `bb.bb_instructions`] nophi_at_idx) >>
    (impl_tac >- (simp[] >> metis_tac[])) >>
    strip_tac >>
    mp_tac (Q.SPECL [`f`, `bb`, `bb.bb_instructions`, `bb.bb_label`,
      `sccp_df_analyze f`, `idx`, `EL idx (bb.bb_instructions)`,
      `s`, `v`, `fuel`, `ctx`] nonphi_inv_pres_tac) >>
    simp[] >>
    (* nonphi_inv_pres_tac leaves phi_bottom premise undischarged: resolve it *)
    (impl_tac >- first_assum ACCEPT_TAC) >>
    strip_tac >>
    (* Apply IH directly *)
    first_x_assum (qspecl_then
      [`SUC idx`, `fuel`, `ctx`, `v with vs_inst_idx := SUC idx`] mp_tac) >>
    simp[] >>
    disch_then irule >>
    first_assum ACCEPT_TAC
QED

Finalise sccp_block_induction_core;

(* SCCP per-block simulation from nophi invariant at entry:
   execution is equivalent or both produce Error *)
Theorem sccp_per_block_sim_nophi:
  !f bb.
    wf_function f /\ wf_ssa f /\ fn_inst_wf f /\
    MEM bb f.fn_blocks /\
    MEM bb.bb_label (cfg_analyze f).cfg_dfs_pre ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      (!x c. FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals x
                = SOME (CL_Const c) /\
             x IN FDOM s.vs_vars /\
             ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
             FLOOKUP s.vs_vars x = SOME c) /\
      (!x. x IN FDOM s.vs_vars /\
           ~is_phi_output_of_block f.fn_blocks bb.bb_label x ==>
         x IN FDOM (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals /\
         FLOOKUP (df_at sccp_bottom (sccp_df_analyze f) bb.bb_label 0).sl_vals x
           <> SOME CL_Top) ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
          (analysis_block_transform sccp_bottom (sccp_df_analyze f)
            (\lat inst. [sccp_inst lat.sl_vals inst]) bb) s)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`f`, `bb`] sccp_block_induction_core) >>
  (impl_tac >- simp[]) >>
  disch_then (qspecl_then
    [`LENGTH bb.bb_instructions`, `0`, `fuel`, `ctx`, `s`] mp_tac) >>
  `s with vs_inst_idx := 0 = s` by
    simp[venom_state_component_equality] >>
  simp[]
QED


