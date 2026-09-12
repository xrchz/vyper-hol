(*
 * CFG Analysis
 *
 * Computes control-flow graph info for Venom IR functions.
 *)

Theory cfgDefs
Ancestors
  list finite_map relation pred_set
  venomInst
Libs
  Defn TotalDefn pairLib pairTheory relationTheory pred_setTheory
  finite_mapTheory

(* ==========================================================================
   Small helpers
   ========================================================================== *)

(* Cons x onto xs if x is not already a member (list-backed set insert). *)
Definition set_insert_def:
  set_insert x xs = if MEM x xs then xs else x::xs
End

(* Look up a key in a finite map, returning [] if absent. *)
Definition fmap_lookup_list_def:
  fmap_lookup_list m k =
    case FLOOKUP m k of
      NONE => []
    | SOME v => v
End

(* ==========================================================================
   Result type and query API
   ========================================================================== *)

Datatype:
  cfg_analysis = <|
    cfg_succs : (string, string list) fmap;
    cfg_preds : (string, string list) fmap;
    cfg_reachable : (string, bool) fmap;
    cfg_dfs_post : string list;
    cfg_dfs_pre : string list
  |>
End

(* Successor labels of lbl in the CFG ([] if lbl is absent). *)
Definition cfg_succs_of_def:
  cfg_succs_of cfg lbl = fmap_lookup_list cfg.cfg_succs lbl
End

(* Predecessor labels of lbl in the CFG ([] if lbl is absent). *)
Definition cfg_preds_of_def:
  cfg_preds_of cfg lbl = fmap_lookup_list cfg.cfg_preds lbl
End

(* Block-level CFG path: consecutive labels are connected by CFG edges. *)
Definition is_cfg_path_def:
  is_cfg_path cfg [] = T ∧
  is_cfg_path cfg [l] = T ∧
  is_cfg_path cfg (l1 :: l2 :: rest) =
    (MEM l2 (cfg_succs_of cfg l1) ∧ is_cfg_path cfg (l2 :: rest))
End

(* Whether lbl was reached during DFS from the entry block. *)
Definition cfg_reachable_of_def:
  cfg_reachable_of cfg lbl =
    case FLOOKUP cfg.cfg_reachable lbl of
      NONE => F
    | SOME b => b
End

(* No critical edges: every block either has at most one predecessor,
 * or all its predecessors have at most one successor.
 * Not currently used but may be a precondition for SSA/phi-elimination. *)
Definition cfg_is_normalized_def:
  cfg_is_normalized cfg fn <=>
    !bb. MEM bb fn.fn_blocks ==>
      (LENGTH (cfg_preds_of cfg bb.bb_label) <= 1) \/
      (!pred.
         MEM pred (cfg_preds_of cfg bb.bb_label) ==>
         LENGTH (cfg_succs_of cfg pred) <= 1)
End

Theorem cfg_is_normalized_compute[compute]:
  cfg_is_normalized cfg fn <=>
    EVERY
      (λbb.
        LENGTH (cfg_preds_of cfg bb.bb_label) <= 1 \/
        EVERY (λpred. LENGTH (cfg_succs_of cfg pred) <= 1)
          (cfg_preds_of cfg bb.bb_label))
      fn.fn_blocks
Proof
  simp[cfg_is_normalized_def, listTheory.EVERY_MEM]
QED

(* ==========================================================================
   Successor / predecessor map construction
   ========================================================================== *)

(* Initialize a label -> [] map for all block labels. *)
Definition init_succs_def:
  init_succs bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, [])) FEMPTY bbs
End

(* Initialize a label -> [] map for all block labels. *)
Definition init_preds_def:
  init_preds bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, [])) FEMPTY bbs
End

(* Map each block label to its bb_succs. *)
Definition build_succs_def:
  build_succs bbs =
    FOLDL (λm bb. m |+ (bb.bb_label, bb_succs bb)) (init_succs bbs) bbs
End

(* For each block, add it as a predecessor of each of its successors. *)
Definition build_preds_def:
  build_preds bbs succs =
    FOLDL
      (λm bb.
         let succs_lbl = fmap_lookup_list succs bb.bb_label in
         FOLDR
           (λsucc m2.
              let old = fmap_lookup_list m2 succ in
              m2 |+ (succ, set_insert bb.bb_label old))
           m succs_lbl)
      (init_preds bbs) bbs
End

(* ==========================================================================
   DFS termination machinery
   ========================================================================== *)

val sum_ty = ``:('a |-> 'a list) # 'a list # 'a +
                ('a |-> 'a list) # 'a list # 'a list``;

val dfs_R = ``inv_image ($< LEX $< LEX ($< : num -> num -> bool))
  (\x. case (x : ^(ty_antiq sum_ty)) of
    INL (succs, visited, lbl) =>
        (CARD (FDOM succs DIFF set visited),
         if lbl IN FDOM succs then 0n else 1n, 0n)
    | INR (succs, visited, lst) =>
        (CARD (FDOM succs DIFF set visited), LENGTH lst, 1n))``;

val dfs_P = ``\(x : ^(ty_antiq sum_ty)) (result : 'a list # 'a list).
  set (case x of INL (s,v,l) => v | INR (s,v,l) => v) SUBSET set (FST result)``;

val dfs_wf_thm = prove(``WF ^dfs_R``,
  MATCH_MP_TAC WF_inv_image >>
  MATCH_MP_TAC WF_LEX >> simp[] >>
  MATCH_MP_TAC WF_LEX >> simp[]);

(* Shared INDUCTIVE_INVARIANT tactic for both DFS functions.
   Generic: avoids naming UNION' function variable via qmatch_goalsub_abbrev_tac.
   INL case: pairarg_tac exposes pair, IH via first_x_assum, SUBSET_TRANS.
   INR case: existential pair witnesses, IH applied twice, SUBSET_TRANS. *)
val dfs_inv_tac =
  simp[INDUCTIVE_INVARIANT_DEF, inv_image_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `x` >> simp[]
  (* INL case *)
  >- (
    PairCases_on `x'` >> simp[] >> rw[] >>
    pairarg_tac >> gvs[] >>
    first_x_assum (qspec_then
      `INR(x'0, set_insert x'2 x'1, fmap_lookup_list x'0 x'2)`
      (fn th => mp_tac (SIMP_RULE (srw_ss()) [] th))) >>
    impl_tac
    >- (
      Cases_on `x'2 IN FDOM x'0` >> simp[LEX_DEF]
      >- (
        `FDOM x'0 INTER set x'1 PSUBSET
         FDOM x'0 INTER set (set_insert x'2 x'1)` by (
          simp[PSUBSET_DEF, SUBSET_DEF, set_insert_def, EXTENSION] >>
          qexists_tac `x'2` >> simp[]
        ) >>
        `FINITE (FDOM x'0 INTER set (set_insert x'2 x'1))` by simp[] >>
        `CARD (FDOM x'0 INTER set x'1) <
         CARD (FDOM x'0 INTER set (set_insert x'2 x'1))` by
          metis_tac[CARD_PSUBSET] >>
        `CARD (FDOM x'0 INTER set (set_insert x'2 x'1)) <=
         CARD (FDOM x'0)` by (irule CARD_SUBSET >> simp[SUBSET_DEF]) >>
        simp[]
      )
      >- (
        DISJ2_TAC >>
        `FDOM x'0 INTER set (set_insert x'2 x'1) =
         FDOM x'0 INTER set x'1` by
          (simp[EXTENSION, set_insert_def] >> metis_tac[]) >>
        simp[fmap_lookup_list_def, FLOOKUP_DEF]
      )
    )
    >- (
      strip_tac >>
      `set x'1 SUBSET set (set_insert x'2 x'1)` by
        simp[set_insert_def, SUBSET_DEF] >>
      `set (set_insert x'2 x'1) SUBSET set vis2` by gvs[] >>
      metis_tac[SUBSET_TRANS]
    )
  )
  (* INR case *)
  >- (
    PairCases_on `y` >> simp[] >>
    Cases_on `y2` >> simp[] >>
    qmatch_goalsub_abbrev_tac `ff (INL _)` >>
    `?q1 q2. ff (INL (y0,y1,h)) = (q1,q2)` by
      metis_tac[pairTheory.PAIR] >>
    `?r1 r2. ff (INR (y0,q1,t)) = (r1,r2)` by
      metis_tac[pairTheory.PAIR] >>
    simp[] >>
    qunabbrev_tac `ff` >>
    first_assum (qspec_then `INL(y0, y1, h)`
      (fn th => mp_tac (SIMP_RULE (srw_ss()) [] th))) >>
    impl_tac
    >- (simp[LEX_DEF] >>
        Cases_on `h IN FDOM y0` >> simp[] >>
        Cases_on `t` >> simp[])
    >- (
      strip_tac >>
      `set y1 SUBSET set q1` by gvs[] >>
      first_assum (qspec_then `INR(y0, q1, t)`
        (fn th => mp_tac (SIMP_RULE (srw_ss()) [] th))) >>
      impl_tac
      >- (
        simp[LEX_DEF] >>
        `CARD (FDOM y0 INTER set y1) <= CARD (FDOM y0 INTER set q1)` by (
          irule CARD_SUBSET >> simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF]
        ) >>
        simp[]
      )
      >- (
        strip_tac >>
        `set q1 SUBSET set r1` by gvs[] >>
        metis_tac[SUBSET_TRANS]
      )
    )
  );

(* Obligation tactic *)
fun dfs_obl_tac mono_aux =
  EXISTS_TAC dfs_R >>
  conj_tac >- (ACCEPT_TAC dfs_wf_thm) >>
  conj_tac >- (
    rpt strip_tac >>
    simp[inv_image_def, LEX_DEF, set_insert_def] >>
    Cases_on `lbl IN FDOM succs` >> simp[]
    >- (
      `FDOM succs INTER set visited PSUBSET
       FDOM succs INTER (lbl INSERT set visited)` by (
        simp[PSUBSET_DEF, SUBSET_DEF, EXTENSION] >>
        qexists_tac `lbl` >> simp[]
      ) >>
      `FINITE (FDOM succs INTER (lbl INSERT set visited))` by simp[] >>
      `CARD (FDOM succs INTER set visited) <
       CARD (FDOM succs INTER (lbl INSERT set visited))` by
        metis_tac[CARD_PSUBSET] >>
      `CARD (FDOM succs INTER (lbl INSERT set visited)) <=
       CARD (FDOM succs)` by (irule CARD_SUBSET >> simp[SUBSET_DEF]) >>
      simp[]
    )
    >- (
      `FDOM succs INTER (lbl INSERT set visited) =
       FDOM succs INTER set visited` by
        (simp[EXTENSION] >> metis_tac[]) >>
      simp[fmap_lookup_list_def, FLOOKUP_DEF]
    )
  ) >>
  conj_tac >- (
    rpt strip_tac >>
    simp[inv_image_def, LEX_DEF] >>
    `set visited SUBSET set v'` by metis_tac[mono_aux] >>
    `CARD (FDOM succs INTER set visited) <=
     CARD (FDOM succs INTER set v')` by (
      irule CARD_SUBSET >> simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF]
    ) >>
    simp[]
  ) >>
  rpt strip_tac >>
  simp[inv_image_def, LEX_DEF] >>
  Cases_on `s IN FDOM succs` >> simp[] >>
  Cases_on `ss` >> simp[];

(* Helper: extract clean monotonicity lemma from INDUCTIVE_INVARIANT *)
fun mk_mono_aux inv_thm aux_def =
  let
    val mono = MATCH_MP INDUCTIVE_INVARIANT_WFREC (CONJ dfs_wf_thm inv_thm)
    val mono' = REWRITE_RULE [GSYM aux_def] mono
    val mono_simp = SIMP_RULE (srw_ss()) [] mono'
    val aux_tm = aux_def |> SPEC_ALL |> concl |> lhs |> rator
  in
    prove(
      ``!succs visited s v' ords'.
        (v', ords') = ^aux_tm ^dfs_R (INL (succs, visited, s)) ==>
        set visited SUBSET set v'``,
      rpt strip_tac >>
      mp_tac (Q.SPEC `INL(succs,visited,s)` mono_simp) >>
      pop_assum (fn th =>
        REWRITE_TAC [GSYM (SIMP_RULE (srw_ss()) [CARD_DIFF_EQN] th)]) >>
      simp[]
    )
  end;

(* TODO: investigate if Definition/Termination syntax can be used here.
   Currently Hol_defn/Defn.tprove is needed to access UNION_AUX_def
   for the INDUCTIVE_INVARIANT monotonicity proof. *)

(* ===== dfs_post_walk ===== *)

val dfs_post_defn = Hol_defn "dfs_post_walk" `
  (dfs_post_walk succs visited lbl =
    if MEM lbl visited then (visited, [])
    else
      let visited' = set_insert lbl visited in
      let succs_lbl = fmap_lookup_list succs lbl in
      let (vis2, orders) = dfs_post_walk_list succs visited' succs_lbl in
      (vis2, orders ++ [lbl])) /\
  (dfs_post_walk_list succs visited [] = (visited, [])) /\
  (dfs_post_walk_list succs visited (s::ss) =
    let (v', ords') = dfs_post_walk succs visited s in
    let (v'', ords'') = dfs_post_walk_list succs v' ss in
    (v'', ords' ++ ords''))`;

val dfs_post_aux_def = DB.fetch "-" "dfs_post_walk_UNION_AUX_def";
val dfs_post_M = dfs_post_aux_def |> SPEC_ALL |> concl |> rhs |> rand;
val dfs_post_inv = prove(
  ``INDUCTIVE_INVARIANT ^dfs_R ^dfs_P ^dfs_post_M``, dfs_inv_tac);
val dfs_post_mono_aux = mk_mono_aux dfs_post_inv dfs_post_aux_def;
val (dfs_post_walk_def, dfs_post_walk_ind) =
  Defn.tprove(dfs_post_defn, dfs_obl_tac dfs_post_mono_aux);

Theorem dfs_post_walk_def[compute] = dfs_post_walk_def
Theorem dfs_post_walk_ind = dfs_post_walk_ind

(* ===== dfs_pre_walk ===== *)

val dfs_pre_defn = Hol_defn "dfs_pre_walk" `
  (dfs_pre_walk succs visited lbl =
    if MEM lbl visited then (visited, [])
    else
      let visited' = set_insert lbl visited in
      let succs_lbl = fmap_lookup_list succs lbl in
      let (vis2, orders) = dfs_pre_walk_list succs visited' succs_lbl in
      (vis2, lbl :: orders)) /\
  (dfs_pre_walk_list succs visited [] = (visited, [])) /\
  (dfs_pre_walk_list succs visited (s::ss) =
    let (v', ords') = dfs_pre_walk succs visited s in
    let (v'', ords'') = dfs_pre_walk_list succs v' ss in
    (v'', ords' ++ ords''))`;

val dfs_pre_aux_def = DB.fetch "-" "dfs_pre_walk_UNION_AUX_def";
val dfs_pre_M = dfs_pre_aux_def |> SPEC_ALL |> concl |> rhs |> rand;
val dfs_pre_inv = prove(
  ``INDUCTIVE_INVARIANT ^dfs_R ^dfs_P ^dfs_pre_M``, dfs_inv_tac);
val dfs_pre_mono_aux = mk_mono_aux dfs_pre_inv dfs_pre_aux_def;
val (dfs_pre_walk_def, dfs_pre_walk_ind) =
  Defn.tprove(dfs_pre_defn, dfs_obl_tac dfs_pre_mono_aux);

Theorem dfs_pre_walk_def[compute] = dfs_pre_walk_def
Theorem dfs_pre_walk_ind = dfs_pre_walk_ind

(* ==========================================================================
   Remaining definitions
   ========================================================================== *)

(* Map each label to whether it appears in the visited set. *)
Definition build_reachable_def:
  build_reachable labels visited =
    FOLDL (λm k. m |+ (k, MEM k visited)) FEMPTY labels
End

(* Run the full CFG analysis on a function: build successor/predecessor maps,
 * run DFS from the entry block to compute pre/postorder and reachability. *)
Definition cfg_analyze_def:
  cfg_analyze fn =
    let bbs = fn.fn_blocks in
    let succs = build_succs bbs in
    let preds = build_preds bbs succs in
    let labels = MAP (λbb. bb.bb_label) bbs in
    let entry =
      case entry_block fn of
        NONE => NONE
      | SOME bb => SOME bb.bb_label in
    let (vis_post, post) =
      case entry of
        NONE => ([], [])
      | SOME lbl => dfs_post_walk succs [] lbl in
    let (_, pre) =
      case entry of
        NONE => ([], [])
      | SOME lbl => dfs_pre_walk succs [] lbl in
    let reach = build_reachable labels vis_post in
    <| cfg_succs := succs;
       cfg_preds := preds;
       cfg_reachable := reach;
       cfg_dfs_post := post;
       cfg_dfs_pre := pre |>
End

(* cfg_path: reachability via successor edges (defined as RTC). *)
Definition cfg_path_def:
  cfg_path cfg = RTC (λa b. MEM b (cfg_succs_of cfg a))
End
