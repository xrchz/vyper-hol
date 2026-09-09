(*
 * CFG Analysis Correctness Proofs
 *)

Theory cfgCorrectnessProof
Ancestors
  cfgDefs cfgHelpers venomWf venomInst venomState finite_map list relation pair

(* ==========================================================================
   Concrete evaluation simpset for counterexamples
   ========================================================================== *)

val dfs_ss = srw_ss() ++ rewrites [dfs_post_walk_def, dfs_pre_walk_def,
  set_insert_def, fmap_lookup_list_def,
  FLOOKUP_UPDATE, FLOOKUP_EMPTY, LET_THM];

val cfg_eval_defs = [cfg_analyze_def, build_succs_def, init_succs_def,
  build_preds_def, init_preds_def, build_reachable_def,
  entry_block_def, bb_succs_def, get_successors_def, is_terminator_def,
  get_label_def, cfg_preds_of_def, cfg_succs_of_def, cfg_reachable_of_def,
  cfg_path_def, fn_labels_def, INDEX_OF_def, INDEX_FIND_def, nub_def,
  mk_raw_function_def];

val cfg_eval_tac = simp_tac dfs_ss cfg_eval_defs;

(* ==========================================================================
   Concrete counterexample functions
   ========================================================================== *)

(* CE1: single block "a" → "b", where "b" is not a block label.
   Used for: preds_domain, reachable_sets, semantic_reachability *)
Definition ce_fn1_def:
  ce_fn1 = mk_raw_function "f" [
    <| bb_label := "a";
       bb_instructions := [<| inst_id := 0; inst_opcode := JMP;
         inst_operands := [Label "b"]; inst_outputs := [] |>] |>]
End

(* CE2: duplicate label "a" — first block "a"→"b", second "a"→STOP.
   Used for: preserves_bb_succs *)
Definition ce_fn2_def:
  ce_fn2 = mk_raw_function "f" [
    <| bb_label := "a";
       bb_instructions := [<| inst_id := 0; inst_opcode := JMP;
         inst_operands := [Label "b"]; inst_outputs := [] |>] |>;
    <| bb_label := "b";
       bb_instructions := [<| inst_id := 1; inst_opcode := STOP;
         inst_operands := []; inst_outputs := [] |>] |>;
    <| bb_label := "a";
       bb_instructions := [<| inst_id := 2; inst_opcode := STOP;
         inst_operands := []; inst_outputs := [] |>] |>]
End

(* CE3: cross-edge graph for preorder_order.
   entry→{s,a}, s→{b}, b→{}, a→{b}
   Pre output: [entry,s,b,a]. INDEX_OF "a" = 3, INDEX_OF "b" = 2.
   a→b is non-back (succs["b"]=[], so no path b→a). Want 3 < 2? FALSE. *)
Definition ce_fn3_def:
  ce_fn3 = mk_raw_function "f" [
    <| bb_label := "entry";
       bb_instructions := [<| inst_id := 0; inst_opcode := JMP;
         inst_operands := [Label "a"; Label "s"]; inst_outputs := [] |>] |>;
    <| bb_label := "s";
       bb_instructions := [<| inst_id := 1; inst_opcode := JMP;
         inst_operands := [Label "b"]; inst_outputs := [] |>] |>;
    <| bb_label := "b";
       bb_instructions := [<| inst_id := 2; inst_opcode := STOP;
         inst_operands := []; inst_outputs := [] |>] |>;
    <| bb_label := "a";
       bb_instructions := [<| inst_id := 3; inst_opcode := JMP;
         inst_operands := [Label "b"]; inst_outputs := [] |>] |>]
End

(* ==========================================================================
   1) Label-domain and shape invariants
   ========================================================================== *)

Theorem cfg_analyze_reachable_in_labels_proof:
  !fn lbl.
    cfg_reachable_of (cfg_analyze fn) lbl ==>
    MEM lbl (fn_labels fn)
Proof
  rpt strip_tac >>
  gvs[cfg_reachable_of_def, cfg_analyze_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `lbl ∈ FDOM (build_reachable (MAP (λbb. bb.bb_label) fn.fn_blocks) vis_post)` by
    (Cases_on `FLOOKUP (build_reachable (MAP (λbb. bb.bb_label) fn.fn_blocks) vis_post) lbl` >>
     gvs[FLOOKUP_DEF]) >>
  gvs[fdom_build_reachable, fn_labels_def] >>
  metis_tac[MEM_MAP]
QED

Theorem cfg_analyze_succ_labels_proof:
  !fn lbl succ.
    wf_function fn /\
    MEM succ (cfg_succs_of (cfg_analyze fn) lbl) ==>
    MEM succ (fn_labels fn)
Proof
  rpt strip_tac >>
  gvs[cfg_analyze_succs, wf_function_def, fn_succs_closed_def] >>
  Cases_on `MEM lbl (fn_labels fn)` >> gvs[fn_labels_def] >| [
    gvs[MEM_MAP] >>
    `fmap_lookup_list (build_succs fn.fn_blocks) bb.bb_label = bb_succs bb` by
      metis_tac[cfg_succs_of_build_succs] >>
    gvs[] >> simp[MEM_MAP] >> metis_tac[],
    `fmap_lookup_list (build_succs fn.fn_blocks) lbl = []` by
      (irule fmap_lookup_list_not_in_fdom >> gvs[fdom_build_succs]) >>
    gvs[]
  ]
QED

Theorem cfg_analyze_pred_labels_proof:
  !fn lbl pred.
    wf_function fn /\
    MEM pred (cfg_preds_of (cfg_analyze fn) lbl) ==>
    MEM pred (fn_labels fn)
Proof
  rpt strip_tac >>
  fs[cfg_analyze_preds, wf_function_def, fn_labels_def] >>
  `∃bb. MEM bb fn.fn_blocks ∧ bb.bb_label = pred ∧
        MEM lbl (fmap_lookup_list (build_succs fn.fn_blocks) bb.bb_label)` by
    metis_tac[mem_build_preds] >>
  simp[MEM_MAP] >> metis_tac[]
QED

(* Without wf_function, preds can reference labels outside fn_labels. *)
Triviality ce_preds_domain_false:
  cfg_preds_of (cfg_analyze ce_fn1) "b" <> [] /\ ~MEM "b" (fn_labels ce_fn1)
Proof
  cfg_eval_tac >> simp[ce_fn1_def] >> cfg_eval_tac
QED

Theorem cfg_analyze_preds_domain_proof:
  !fn lbl.
    wf_function fn /\
    cfg_preds_of (cfg_analyze fn) lbl <> [] ==>
    MEM lbl (fn_labels fn)
Proof
  rpt strip_tac >>
  fs[cfg_analyze_preds] >>
  Cases_on `fmap_lookup_list (build_preds fn.fn_blocks (build_succs fn.fn_blocks)) lbl` >> gvs[] >>
  `MEM h (fmap_lookup_list (build_preds fn.fn_blocks (build_succs fn.fn_blocks)) lbl)` by simp[] >>
  fs[mem_build_preds] >>
  gvs[wf_function_def, fn_labels_def] >>
  `fmap_lookup_list (build_succs fn.fn_blocks) bb.bb_label = bb_succs bb` by
    metis_tac[cfg_succs_of_build_succs] >>
  gvs[fn_succs_closed_def, fn_labels_def] >> metis_tac[]
QED

(* ==========================================================================
   2) Structural correctness
   ========================================================================== *)

(* Without wf_function (ALL_DISTINCT labels), duplicate labels cause
   build_succs to keep only the last block's successors. *)
Triviality ce_preserves_bb_succs_false:
  let bb = <| bb_label := "a";
     bb_instructions := [<| inst_id := 0; inst_opcode := JMP;
       inst_operands := [Label "b"]; inst_outputs := [] |>] |> in
  MEM bb ce_fn2.fn_blocks /\
  cfg_succs_of (cfg_analyze ce_fn2) bb.bb_label <> bb_succs bb
Proof
  simp[ce_fn2_def] >> cfg_eval_tac
QED

Theorem cfg_analyze_preserves_bb_succs_proof:
  !fn bb.
    wf_function fn /\
    MEM bb fn.fn_blocks ==>
    cfg_succs_of (cfg_analyze fn) bb.bb_label = bb_succs bb
Proof
  rpt strip_tac >>
  simp[cfg_analyze_succs] >>
  irule cfg_succs_of_build_succs >>
  gvs[wf_function_def, fn_labels_def]
QED

Theorem cfg_analyze_edge_symmetry_proof:
  !fn lbl succ.
    MEM lbl (fn_labels fn) /\
    MEM succ (fn_labels fn) ==>
      (MEM succ (cfg_succs_of (cfg_analyze fn) lbl) <=>
       MEM lbl (cfg_preds_of (cfg_analyze fn) succ))
Proof
  rpt strip_tac >>
  simp[cfg_analyze_succs, cfg_analyze_preds, mem_build_preds] >>
  eq_tac >> strip_tac
  THENL [
    gvs[fn_labels_def, MEM_MAP] >> qexists_tac `bb` >> simp[],
    gvs[]
  ]
QED

(* ==========================================================================
   3) Traversal properties
   ========================================================================== *)

Theorem cfg_analyze_dfs_post_distinct_proof:
  !fn. ALL_DISTINCT (cfg_dfs_post (cfg_analyze fn))
Proof
  gen_tac >>
  qspec_then `fn` mp_tac cfg_analyze_dfs_post >>
  Cases_on `entry_block fn` >> simp[] >>
  disch_then (fn th => REWRITE_TAC [th]) >>
  simp[dfs_post_walk_distinct]
QED

Theorem cfg_analyze_dfs_pre_distinct_proof:
  !fn. ALL_DISTINCT (cfg_dfs_pre (cfg_analyze fn))
Proof
  gen_tac >>
  qspec_then `fn` mp_tac cfg_analyze_dfs_pre >>
  Cases_on `entry_block fn` >> simp[] >>
  disch_then (fn th => REWRITE_TAC [th]) >>
  simp[dfs_pre_walk_distinct]
QED

(* Without wf_function, DFS can visit labels outside fn_labels (via
   jumps to non-existent blocks), breaking the set equality. *)
Triviality ce_reachable_sets_false:
  MEM "b" (cfg_dfs_post (cfg_analyze ce_fn1)) /\
  ~cfg_reachable_of (cfg_analyze ce_fn1) "b"
Proof
  simp[ce_fn1_def] >> cfg_eval_tac
QED

(* Local helper: characterize cfg_reachable_of under wf_function.
   Rewrites cfg_reachable_of in terms of fn_labels and DFS visited set. *)
Theorem cfg_reachable_of_char[local]:
  !fn eb lbl.
    wf_function fn /\ entry_block fn = SOME eb ==>
    (cfg_reachable_of (cfg_analyze fn) lbl <=>
     MEM lbl (fn_labels fn) /\
     MEM lbl (FST (dfs_post_walk (build_succs fn.fn_blocks) [] eb.bb_label)))
Proof
  rpt strip_tac >>
  qspec_then `fn` mp_tac cfg_analyze_reachable >>
  asm_simp_tac (srw_ss()) [] >> strip_tac >>
  simp[cfg_reachable_of_def] >>
  Cases_on `MEM lbl (fn_labels fn)` >> simp[]
  >- (`ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
        gvs[wf_function_def, fn_labels_def] >>
      `MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks)` by gvs[fn_labels_def] >>
      drule_all flookup_build_reachable >> simp[])
  >- (`~MEM lbl (MAP (\bb. bb.bb_label) fn.fn_blocks)` by gvs[fn_labels_def] >>
      `lbl NOTIN FDOM (build_reachable (MAP (\bb. bb.bb_label) fn.fn_blocks)
         (FST (dfs_post_walk (build_succs fn.fn_blocks) [] eb.bb_label)))` by
        gvs[fdom_build_reachable] >>
      gvs[FLOOKUP_DEF])
QED

(* String-specialized DFS soundness and visited_eq to avoid polymorphic metis *)
val post_sound_s = INST_TYPE [alpha |-> ``:string``] dfs_post_walk_sound_thm;
val post_vis_eq_s = CONJUNCT1 (INST_TYPE [alpha |-> ``:string``] dfs_post_walk_visited_eq);

Theorem cfg_analyze_reachable_sets_proof:
  !fn.
    wf_function fn ==>
    set (cfg_dfs_post (cfg_analyze fn)) = set (cfg_dfs_pre (cfg_analyze fn)) /\
    set (cfg_dfs_post (cfg_analyze fn)) =
      {lbl | cfg_reachable_of (cfg_analyze fn) lbl}
Proof
  rpt strip_tac >> fs[wf_function_def] >>
  `fn.fn_blocks <> []` by gvs[fn_has_entry_def] >>
  `?eb. entry_block fn = SOME eb` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  `MEM eb fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  `wf_function fn` by gvs[wf_function_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by gvs[fn_labels_def] >>
  `!bb succ. MEM bb fn.fn_blocks /\ MEM succ (bb_succs bb) ==>
     MEM succ (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    gvs[fn_succs_closed_def, fn_labels_def] >>
  `MEM eb.bb_label (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  qspec_then `fn` mp_tac cfg_analyze_dfs_post >>
  qspec_then `fn` mp_tac cfg_analyze_dfs_pre >>
  asm_simp_tac (srw_ss()) [] >> rpt strip_tac
  >- simp[dfs_walks_same_output_set]
  >- (
    simp[pred_setTheory.EXTENSION, IN_DEF] >> gen_tac >> EQ_TAC >> strip_tac
    >- (
      (* ⇒: MEM x dfs_post → cfg_reachable_of x *)
      `MEM x (SND (dfs_post_walk (build_succs fn.fn_blocks) [] eb.bb_label))` by
        fs[IN_DEF] >>
      drule post_sound_s >> strip_tac >>
      drule_all rtc_build_succs_closed >> strip_tac >>
      `MEM x (fn_labels fn)` by simp[fn_labels_def] >>
      `MEM x (FST (dfs_post_walk (build_succs fn.fn_blocks) [] eb.bb_label))` by (
        mp_tac (Q.SPECL [`build_succs fn.fn_blocks`, `[]`, `eb.bb_label`]
           post_vis_eq_s) >> simp[pred_setTheory.EXTENSION, IN_DEF]) >>
      metis_tac[cfg_reachable_of_char])
    >- (
      (* ⇐: cfg_reachable_of x → MEM x dfs_post *)
      `MEM x (fn_labels fn) /\
       MEM x (FST (dfs_post_walk (build_succs fn.fn_blocks) [] eb.bb_label))` by
        metis_tac[cfg_reachable_of_char] >>
      simp[IN_DEF] >>
      mp_tac (Q.SPECL [`build_succs fn.fn_blocks`, `[]`, `eb.bb_label`]
         post_vis_eq_s) >>
      simp[pred_setTheory.EXTENSION, IN_DEF] >>
      strip_tac >> fs[IN_DEF])
  )
QED

Theorem cfg_analyze_preorder_entry_first_proof:
  !fn bb.
    entry_block fn = SOME bb ==>
    cfg_dfs_pre (cfg_analyze fn) <> [] /\
    HD (cfg_dfs_pre (cfg_analyze fn)) = bb.bb_label
Proof
  rpt strip_tac >> (
    qspec_then `fn` mp_tac cfg_analyze_dfs_pre >>
    asm_simp_tac (srw_ss()) [] >> strip_tac >>
    metis_tac[dfs_pre_walk_entry_hd, MEM]
  )
QED

Theorem cfg_analyze_postorder_entry_last_proof:
  !fn bb.
    entry_block fn = SOME bb ==>
    cfg_dfs_post (cfg_analyze fn) <> [] /\
    LAST (cfg_dfs_post (cfg_analyze fn)) = bb.bb_label
Proof
  rpt strip_tac >> (
    qspec_then `fn` mp_tac cfg_analyze_dfs_post >>
    asm_simp_tac (srw_ss()) [] >> strip_tac >>
    metis_tac[dfs_post_walk_entry_last, MEM]
  )
QED

(* ==========================================================================
   4) Semantic reachability
   ========================================================================== *)

(* Without wf_function, cfg_path can reach labels that cfg_reachable_of
   rejects (because build_reachable only covers fn_labels). *)
Triviality ce_semantic_reachability_false:
  entry_block ce_fn1 = SOME (HD ce_fn1.fn_blocks) /\
  ~(cfg_reachable_of (cfg_analyze ce_fn1) "b" <=>
    cfg_path (cfg_analyze ce_fn1) (HD ce_fn1.fn_blocks).bb_label "b")
Proof
  simp[ce_fn1_def] >> cfg_eval_tac >>
  simp[relationTheory.RTC_RULES]
QED

Theorem cfg_analyze_semantic_reachability_proof:
  !fn bb lbl.
    wf_function fn /\
    entry_block fn = SOME bb ==>
    (cfg_reachable_of (cfg_analyze fn) lbl <=>
     cfg_path (cfg_analyze fn) bb.bb_label lbl)
Proof
  rpt strip_tac >>
  `MEM bb fn.fn_blocks` by
    (Cases_on `fn.fn_blocks` >>
     gvs[wf_function_def, fn_has_entry_def, entry_block_def]) >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_labels_def] >>
  `!bb succ. MEM bb fn.fn_blocks /\ MEM succ (bb_succs bb) ==>
     MEM succ (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    gvs[wf_function_def, fn_succs_closed_def, fn_labels_def] >>
  `MEM bb.bb_label (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (simp[listTheory.MEM_MAP] >> metis_tac[]) >>
  (* Rewrite both sides to DFS / RTC characterizations *)
  `cfg_reachable_of (cfg_analyze fn) lbl <=>
   MEM lbl (fn_labels fn) /\
   MEM lbl (FST (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label))` by
    metis_tac[cfg_reachable_of_char] >>
  `cfg_path (cfg_analyze fn) bb.bb_label lbl <=>
   (λa b. MEM b (fmap_lookup_list (build_succs fn.fn_blocks) a))^* bb.bb_label lbl` by
    simp[cfg_path_def, cfg_analyze_succs] >>
  simp[] >> EQ_TAC >> strip_tac
  >- (
    (* → : vis_post -> dfs_post -> RTC (soundness) *)
    `MEM lbl (SND (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label))` by (
      `set (FST (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label)) =
       set [] UNION set (SND (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label))` by
        metis_tac[post_vis_eq_s] >> fs[]) >>
    metis_tac[post_sound_s])
  >- (
    (* ← : RTC -> completeness + rtc_build_succs_closed *)
    `MEM lbl (SND (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label))` by
      metis_tac[dfs_post_walk_complete] >>
    conj_tac
    >- (simp[fn_labels_def] >> drule_all rtc_build_succs_closed >> simp[])
    >- (`set (FST (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label)) =
         set [] UNION set (SND (dfs_post_walk (build_succs fn.fn_blocks) [] bb.bb_label))` by
          metis_tac[post_vis_eq_s] >> fs[]))
QED

(* ==========================================================================
   5) Traversal ordering
   ========================================================================== *)

Theorem cfg_analyze_postorder_order_proof:
  !fn a b i j.
    cfg_reachable_of (cfg_analyze fn) a /\
    MEM b (cfg_succs_of (cfg_analyze fn) a) /\
    ~cfg_path (cfg_analyze fn) b a /\
    INDEX_OF b (cfg_dfs_post (cfg_analyze fn)) = SOME i /\
    INDEX_OF a (cfg_dfs_post (cfg_analyze fn)) = SOME j ==>
    i < j
Proof
  rpt strip_tac >>
  Cases_on `entry_block fn`
  THENL [
    `(cfg_analyze fn).cfg_dfs_post = []` by
      (qspec_then `fn` mp_tac cfg_analyze_dfs_post >> simp[]) >>
    fs[INDEX_OF_def, INDEX_FIND_def],
    `(cfg_analyze fn).cfg_dfs_post =
     SND (dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label)` by
      (qspec_then `fn` mp_tac cfg_analyze_dfs_post >> simp[]) >>
    `cfg_succs_of (cfg_analyze fn) =
     fmap_lookup_list (build_succs fn.fn_blocks)` by
      simp[cfg_analyze_succs] >>
    `cfg_path (cfg_analyze fn) =
     RTC (\a b. MEM b (fmap_lookup_list (build_succs fn.fn_blocks) a))` by
      simp[cfg_path_def] >>
    gvs[] >>
    `MEM a (SND (dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label))` by
      (`~(INDEX_OF a (SND (dfs_post_walk (build_succs fn.fn_blocks) []
            x.bb_label)) = NONE)` by simp[] >>
       fs[INDEX_OF_eq_NONE]) >>
    metis_tac[CONJUNCT1 dfs_post_walk_general_order]
  ]
QED

(* Preorder does not have the analogous ordering property: cross edges
   can cause a successor to appear before its predecessor in preorder. *)
Theorem ce_preorder_order_false:
  cfg_reachable_of (cfg_analyze ce_fn3) "a" /\
  MEM "b" (cfg_succs_of (cfg_analyze ce_fn3) "a") /\
  ~cfg_path (cfg_analyze ce_fn3) "b" "a" /\
  INDEX_OF "a" (cfg_dfs_pre (cfg_analyze ce_fn3)) = SOME 3 /\
  INDEX_OF "b" (cfg_dfs_pre (cfg_analyze ce_fn3)) = SOME 2 /\
  ~(3 < 2)
Proof
  simp[ce_fn3_def] >> rpt conj_tac
  >- cfg_eval_tac
  >- cfg_eval_tac
  >- (cfg_eval_tac >>
      (* Since succs "b" = [], RTC only permits the reflexive case. *)
      rpt strip_tac >>
      qpat_x_assum `(λa b. _)^* "b" "a"` mp_tac >>
      simp[Once relationTheory.RTC_CASES1])
  >- cfg_eval_tac
  >- cfg_eval_tac
QED

(* ==========================================================================
   Unconditional edge symmetry
   ========================================================================== *)

(* Helper: cfg_succs = build_succs *)
Theorem cfg_succs_build[local]:
  !fn. (cfg_analyze fn).cfg_succs = build_succs fn.fn_blocks
Proof
  rw[cfgDefsTheory.cfg_analyze_def] >> simp_tac std_ss [LET_THM] >>
  Cases_on `entry_block fn` >> simp[] >>
  Cases_on `dfs_post_walk (build_succs fn.fn_blocks) [] x.bb_label` >> simp[] >>
  Cases_on `dfs_pre_walk (build_succs fn.fn_blocks) [] x.bb_label` >> simp[]
QED

(* Unconditional edge symmetry: removes MEM-in-fn_labels precondition.
   If label is NOT in fn_labels, succs is [] and preds side is vacuously false. *)
Theorem cfg_edge_symmetry_uncond_proof:
  !fn a b. MEM b (cfg_succs_of (cfg_analyze fn) a) <=>
           MEM a (cfg_preds_of (cfg_analyze fn) b)
Proof
  rpt gen_tac >>
  simp[cfg_analyze_succs, cfg_analyze_preds, mem_build_preds] >>
  eq_tac >> rpt strip_tac
  >- (
    `?blk. MEM blk fn.fn_blocks /\ blk.bb_label = a` by (
      spose_not_then strip_assume_tac >>
      `~MEM a (MAP (\bb. bb.bb_label) fn.fn_blocks)` by (
        simp[MEM_MAP] >> metis_tac[]) >>
      `fmap_lookup_list (build_succs fn.fn_blocks) a = []` by
        metis_tac[cfg_succs_of_not_in_labels] >>
      fs[]) >>
    qexists_tac `blk` >> fs[])
  >- metis_tac[]
QED
