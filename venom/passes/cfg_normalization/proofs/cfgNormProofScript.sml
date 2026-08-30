(*
 * CFG Normalization Pass -- Invariant Preservation and Correctness
 *
 * Depends on cfgNormBase for simulation lemmas and insert_split_correct.
 *)

Theory cfgNormProof
Ancestors
  cfgNormBase cfgNormDefs cfgNormSim cfgTransformProofs cfgTransformProps stateEquiv stateEquivProps
  venomExecSemantics execEquivProofs venomWf venomExecProps venomInstProps
  venomExecProofs prevBbIndep
Libs
  cfgNormBaseTheory cfgNormDefsTheory cfgNormSimTheory cfgTransformTheory
  cfgTransformProofsTheory cfgTransformPropsTheory stateEquivTheory stateEquivPropsTheory
  venomExecSemanticsTheory venomInstPropsTheory
  venomInstTheory venomStateTheory venomWfTheory venomExecPropsTheory
  venomExecProofsTheory prevBbIndepTheory finite_mapTheory

(* ================================================================
   Section 5: find_and_split correctness -- one round preserves semantics
   ================================================================ *)

(*
 * find_and_split_correct: scanning the block list and performing
 * one split preserves function semantics.
 *
 * Strategy: Induction on bbs.
 *   Base: bbs=[] returns (func, F, _), contradicts changed=T.
 *   Step: bbs=bb::rest. Three cases:
 *     1) LENGTH preds <= 1 or FIND returns NONE: recurse, IH applies.
 *     2) FIND returns SOME pred_bb: apply insert_split_correct.
 *        - MEM pred_bb func.fn_blocks from FIND_MEM + block_preds
 *        - MEM bb func.fn_blocks from EVERY assumption
 *        - pred_bb.bb_label <> bb.bb_label from no_self_loops
 *        - split_labels_fresh gives ~MEM split_lbl (fn_labels func)
 *        - State conditions from fn_entry_label + prev_bb = NONE
 *)
Theorem entry_in_fn_labels:
  !func entry. wf_function_no_ids func /\ fn_entry_label func = SOME entry ==>
    MEM entry (fn_labels func)
Proof
  rw[wf_function_no_ids_def, fn_has_entry_def, fn_labels_def] >>
  Cases_on `func.fn_blocks` >> fs[fn_entry_label_def, entry_block_def]
QED

(* Helper: if a in L and b not in L, then a <> b *)
Theorem MEM_not_MEM_neq:
  !a b L. MEM a L /\ ~MEM b L ==> a <> b /\ b <> a
Proof
  rpt strip_tac >> fs[]
QED

(* ================================================================
   Section 6: Invariant for iteration
   ================================================================ *)

(* Bundle all conditions needed by find_and_split_correct into one
   predicate, parameterized by the ORIGINAL function func0. *)
Definition cfg_norm_inv_def:
  cfg_norm_inv func0 func <=>
    wf_function_no_ids func /\
    fn_inst_wf func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    ALL_DISTINCT (fn_labels func) /\
    (* Every label is original or a split label from original pairs *)
    (!lbl. MEM lbl (fn_labels func) ==>
       MEM lbl (fn_labels func0) \/
       ?p t. MEM p (fn_labels func0) /\ MEM t (fn_labels func0) /\
             lbl = split_block_name p t) /\
    (* split_block_name is injective on original labels *)
    (!p1 t1 p2 t2.
       MEM p1 (fn_labels func0) /\ MEM t1 (fn_labels func0) /\
       MEM p2 (fn_labels func0) /\ MEM t2 (fn_labels func0) /\
       split_block_name p1 t1 = split_block_name p2 t2 ==>
       p1 = p2 /\ t1 = t2) /\
    (* Original function has no split block collisions *)
    split_labels_fresh split_block_name func0 /\
    (* For any edge in func, the split name is fresh *)
    (!bb lbl. MEM bb func.fn_blocks /\ MEM lbl (bb_succs bb) ==>
       ~MEM (split_block_name bb.bb_label lbl) (fn_labels func)) /\
    (* Variable freshness: fwd vars for ORIGINAL label pairs ==> split in fn_labels *)
    (!pred_lbl tgt_lbl var.
       MEM pred_lbl (fn_labels func0) /\ MEM tgt_lbl (fn_labels func0) /\
       MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
                   (fn_all_vars func) ==>
       MEM (split_block_name pred_lbl tgt_lbl) (fn_labels func)) /\
    (* No self-loop critical edges *)
    (!bb. MEM bb func.fn_blocks ==>
       !lbl. MEM lbl (bb_succs bb) ==> lbl <> bb.bb_label) /\
    (* Entry label preserved *)
    fn_entry_label func = fn_entry_label func0 /\
    (* Non-original blocks have at most 1 successor *)
    (!bb. MEM bb func.fn_blocks /\ ~MEM bb.bb_label (fn_labels func0) ==>
      num_succs bb <= 1) /\
    (* Non-original labels have at most 1 predecessor block *)
    (!lbl bb1 bb2. MEM bb1 func.fn_blocks /\ MEM bb2 func.fn_blocks /\
      MEM lbl (bb_succs bb1) /\ MEM lbl (bb_succs bb2) /\
      ~MEM lbl (fn_labels func0) ==>
      bb1.bb_label = bb2.bb_label) /\
    (* Per-block inst_id distinctness (weaker than fn_inst_ids_distinct) *)
    (!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    (* No original label starts with "split_" -- prevents _split_ separator
       ambiguity at right boundary. Trivially satisfied by Venom pipeline.
       Without this, split_block_name is not injective:
       split_block_name "" "split_" = split_block_name "_split" "" *)
    (!L. MEM L (fn_labels func0) ==> TAKE 6 L <> "split_") /\
    (* No original label contains "_fwd" (4-char) as a substring -- prevents
       _fwd_ separator ambiguity in forwarding variable names. Stronger than
       no "_fwd_" (5-char) to ensure fwd_cancel_right works. Trivially
       satisfied by Venom pipeline (no block label contains "_fwd"). *)
    (!L. MEM L (fn_labels func0) ==> !a b. L <> STRCAT a (STRCAT "_fwd" b)) /\
    (* No original label ends with "_split" (6-char) -- prevents _split_
       separator border ambiguity in compound split_fwd strings. Without this,
       A++"_split_"++B++"_fwd_"++v = C++"_split_"++D++"_fwd_"++w does not
       imply A=C. CE: A="", B="split", C="_split", D="fwd".
       Trivially satisfied by Venom pipeline (labels are "bb0", "global", etc). *)
    (!L. MEM L (fn_labels func0) ==> !x. L <> STRCAT x "_split")
End

(* Extract edge freshness from cfg_norm_inv *)
Theorem cfg_norm_inv_edge_fresh:
  !func0 func bb lbl.
    cfg_norm_inv func0 func /\
    MEM bb func.fn_blocks /\ MEM lbl (bb_succs bb) ==>
    ~MEM (split_block_name bb.bb_label lbl) (fn_labels func)
Proof
  rw[cfg_norm_inv_def]
QED


(* ================================================================
   Section 7: String nesting helpers for edge freshness
   ================================================================ *)

(* Original labels cannot have the form a ++ "_split_" ++ b *)
Theorem original_no_split_substr:
  !func0 L a b.
    split_labels_fresh split_block_name func0 /\
    MEM L (fn_labels func0) ==>
    L <> STRCAT a (STRCAT "_split_" b)
Proof
  rw[split_labels_fresh_def, split_block_name_def] >>
  metis_tac[]
QED

(* Helper: no "_split_" substring means no "_split_" substring in tail *)
Theorem no_split_substr_tail:
  !h s. (!a b. STRING h s <> STRCAT a (STRCAT "_split_" b)) ==>
        (!a b. s <> STRCAT a (STRCAT "_split_" b))
Proof
  rpt strip_tac >> fs[] >>
  first_x_assum (qspecl_then [`STRING h a`, `b`] mp_tac) >>
  simp[stringTheory.STRCAT_EQNS]
QED

(* --- Rightmost "_split_" cancellation ---
   Key insight: if target has no "_split_" substring AND doesn't start with
   "split_", then the rightmost "_split_" in A++"_split_"++target is exactly
   the explicit separator. This makes split_block_name right-cancellative.

   The old prefix_impossible/strcat_split_cancel/split_block_name_cancel
   are FALSE without the "doesn't start with split_" condition.
   Counterexample: split_block_name "" "split_" = split_block_name "_split" ""
*)

(* Helper: when "_split_" ++ target = B ++ "_split_" ++ target' and
   target has no "_split_" substring and TAKE 6 target <> "split_",
   then B="" and target=target'.
   Proof strategy: STRLEN case analysis on B (see FOCUS/LEARNINGS L393) *)
Theorem split_peel_contra[local]:
  !B target target'.
    (!x y. target <> STRCAT x (STRCAT "_split_" y)) /\
    TAKE 6 target <> "split_" /\
    STRCAT "_split_" target = STRCAT B (STRCAT "_split_" target') ==>
    B = "" /\ target = target'
Proof
  rpt gen_tac >> strip_tac >>
  `STRLEN (STRCAT "_split_" target) =
   STRLEN (STRCAT B (STRCAT "_split_" target'))` by metis_tac[] >>
  full_simp_tac std_ss
    [stringTheory.STRLEN_CAT, EVAL ``STRLEN "_split_"``] >>
  Cases_on `STRLEN B = 0`
  >- (fs[stringTheory.STRLEN_EQ_0, stringTheory.STRCAT_11]) >>
  Cases_on `STRLEN B >= 7`
  >- (
    `STRLEN B <= STRLEN (STRCAT "_split_" target)` by
      simp[stringTheory.STRLEN_CAT] >>
    `TAKE (STRLEN B) (STRCAT B (STRCAT "_split_" target')) = B` by
      simp[listTheory.TAKE_APPEND1] >>
    `TAKE (STRLEN B) (STRCAT "_split_" target) = B` by metis_tac[] >>
    `7 <= STRLEN B` by fs[] >>
    `TAKE 7 (TAKE (STRLEN B) (STRCAT "_split_" target)) =
     TAKE 7 (STRCAT "_split_" target)` by
      simp[rich_listTheory.TAKE_TAKE] >>
    `TAKE 7 (STRCAT "_split_" target) = "_split_"` by
      (EVAL_TAC >> simp[]) >>
    `TAKE 7 B = "_split_"` by metis_tac[] >>
    `B = STRCAT (TAKE 7 B) (DROP 7 B)` by
      metis_tac[listTheory.TAKE_DROP] >>
    `B = STRCAT "_split_" (DROP 7 B)` by metis_tac[] >>
    `STRCAT "_split_" target =
     STRCAT (STRCAT "_split_" (DROP 7 B)) (STRCAT "_split_" target')` by
      metis_tac[] >>
    full_simp_tac std_ss
      [GSYM stringTheory.STRCAT_ASSOC, stringTheory.STRCAT_11] >>
    metis_tac[]
  ) >>
  `STRLEN B <= 6` by fs[] >>
  `STRLEN B <= STRLEN (STRCAT "_split_" target)` by
    simp[stringTheory.STRLEN_CAT] >>
  `TAKE (STRLEN B) (STRCAT B (STRCAT "_split_" target')) = B` by
    simp[listTheory.TAKE_APPEND1] >>
  `B = TAKE (STRLEN B) (STRCAT "_split_" target)` by metis_tac[] >>
  `STRLEN B = 1 \/ STRLEN B = 2 \/ STRLEN B = 3 \/
   STRLEN B = 4 \/ STRLEN B = 5 \/ STRLEN B = 6` by simp[] >>
  fs[]
QED

(* Main cancellation: right-cancel through "_split_" separator.
   If both targets have no "_split_" substring and don't start with "split_",
   then A ++ "_split_" ++ target = B ++ "_split_" ++ target' implies
   A = B and target = target'.
   Uses split_peel_contra for the asymmetric cases. *)
Theorem split_cancel_right:
  !A B target target'.
    (!x y. target <> STRCAT x (STRCAT "_split_" y)) /\
    (!x y. target' <> STRCAT x (STRCAT "_split_" y)) /\
    TAKE 6 target <> "split_" /\
    TAKE 6 target' <> "split_" /\
    STRCAT A (STRCAT "_split_" target) =
      STRCAT B (STRCAT "_split_" target') ==>
    A = B /\ target = target'
Proof
  Induct_on `A` >> rpt gen_tac >> strip_tac
  (* Base: A = "" *)
  >- (
    qpat_x_assum `STRCAT _ _ = _`
      (mp_tac o REWRITE_RULE [CONJUNCT1 stringTheory.STRCAT_def]) >>
    strip_tac >>
    mp_tac (Q.SPECL [`B`, `target`, `target'`] split_peel_contra) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]
  )
  (* Step: A = STRING h A *)
  >> Cases_on `B`
  >- (
    qpat_x_assum `STRCAT _ _ = STRCAT _ _`
      (mp_tac o REWRITE_RULE[CONJUNCT1 stringTheory.STRCAT_def] o GSYM) >>
    strip_tac >>
    mp_tac (Q.SPECL [`STRING h A`, `target'`, `target`] split_peel_contra) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >> fs[]
  )
  (* B = STRING h' t: STRING injectivity gives h=h', then IH *)
  >> qpat_x_assum `STRCAT _ _ = STRCAT _ _` mp_tac
  >> ONCE_REWRITE_TAC[stringTheory.STRCAT_EQNS]
  >> PURE_REWRITE_TAC[listTheory.CONS_11] >> strip_tac
  >> last_x_assum (qspecl_then [`t`, `target`, `target'`] mp_tac)
  >> impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)
  >> strip_tac >> rw[]
QED

(* Pure string fact: a string with two "_split_" occurrences cannot equal
   one with a single "_split_" where both prefix and suffix are clean.
   Proof: STRLEN case analysis on |A| vs |p|. *)
Theorem double_split_contra[local]:
  !A p t x y.
    (!a b. A <> STRCAT a (STRCAT "_split_" b)) /\
    (!a b. p <> STRCAT a (STRCAT "_split_" b)) /\
    (!a b. t <> STRCAT a (STRCAT "_split_" b)) /\
    TAKE 6 t <> "split_" ==>
    STRCAT A (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y))) <>
    STRCAT p (STRCAT "_split_" t)
Proof
  rpt strip_tac >>
  (* After rpt strip_tac: hyps + equation as assumptions, goal = F *)
  (* Derive STRLEN equality *)
  `STRLEN A + 7 + STRLEN x + 7 + STRLEN y = STRLEN p + 7 + STRLEN t` by (
    qpat_x_assum `STRCAT A _ = STRCAT p _` (mp_tac o AP_TERM ``STRLEN``) >>
    simp[stringTheory.STRLEN_CAT, EVAL ``STRLEN "_split_"``]) >>
  Cases_on `STRLEN A = STRLEN p`
  >- (
    (* |A| = |p|: APPEND_LENGTH_EQ gives A = p, rest equal *)
    `STRLEN (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y))) =
     STRLEN (STRCAT "_split_" t)` by simp[stringTheory.STRLEN_CAT] >>
    `A = p` by metis_tac[listTheory.APPEND_LENGTH_EQ] >>
    (* Cancel prefix *)
    qpat_x_assum `STRCAT A _ = STRCAT p _` mp_tac >>
    qpat_x_assum `A = p` SUBST_ALL_TAC >>
    simp[stringTheory.STRCAT_11] >> strip_tac >>
    (* t = x ++ "_split_" ++ y contradicts t clean *)
    metis_tac[])
  >> Cases_on `STRLEN A < STRLEN p`
  >- (
    (* |A| < |p|: DROP |A| from both sides *)
    `DROP (STRLEN A) (STRCAT A (STRCAT "_split_"
       (STRCAT x (STRCAT "_split_" y)))) =
     STRCAT "_split_" (STRCAT x (STRCAT "_split_" y))` by
      simp[listTheory.DROP_APPEND1] >>
    `STRLEN A <= STRLEN p` by simp[] >>
    `DROP (STRLEN A) (STRCAT p (STRCAT "_split_" t)) =
     STRCAT (DROP (STRLEN A) p) (STRCAT "_split_" t)` by
      simp[listTheory.DROP_APPEND1] >>
    `STRCAT "_split_" (STRCAT x (STRCAT "_split_" y)) =
     STRCAT (DROP (STRLEN A) p) (STRCAT "_split_" t)` by metis_tac[] >>
    qabbrev_tac `d = STRLEN p - STRLEN A` >>
    `STRLEN (DROP (STRLEN A) p) = d /\ d > 0 /\
     d <= STRLEN (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y)))` by
      simp[Abbr `d`, stringTheory.STRLEN_CAT] >>
    Cases_on `d >= 7`
    >- (
      (* d >= 7: TAKE 7 of (DROP |A| p) = "_split_" => p has "_split_" substr *)
      `TAKE d (STRCAT (DROP (STRLEN A) p) (STRCAT "_split_" t)) =
       DROP (STRLEN A) p` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE d (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y))) =
       DROP (STRLEN A) p` by metis_tac[] >>
      `TAKE 7 (TAKE d (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y)))) =
       TAKE 7 (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y)))` by
        simp[rich_listTheory.TAKE_TAKE] >>
      `TAKE 7 (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y))) =
       "_split_"` by (EVAL_TAC >> simp[]) >>
      `TAKE 7 (DROP (STRLEN A) p) = "_split_"` by metis_tac[] >>
      `DROP (STRLEN A) p =
       STRCAT (TAKE 7 (DROP (STRLEN A) p)) (DROP 7 (DROP (STRLEN A) p))` by
        metis_tac[listTheory.TAKE_DROP] >>
      `p = STRCAT (TAKE (STRLEN A) p) (DROP (STRLEN A) p)` by
        metis_tac[listTheory.TAKE_DROP] >>
      metis_tac[])
    >- (
      (* 1 <= d <= 6 *)
      `d <= 6` by fs[] >>
      qunabbrev_tac `d` >>
      `TAKE (STRLEN p - STRLEN A) (STRCAT (DROP (STRLEN A) p) (STRCAT "_split_" t)) =
       DROP (STRLEN A) p` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE (STRLEN p - STRLEN A) (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y))) =
       DROP (STRLEN A) p` by metis_tac[] >>
      `TAKE (STRLEN p - STRLEN A) (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y))) =
       TAKE (STRLEN p - STRLEN A) "_split_"` by
        (irule listTheory.TAKE_APPEND1 >> simp[EVAL ``STRLEN "_split_"``]) >>
      `DROP (STRLEN A) p = TAKE (STRLEN p - STRLEN A) "_split_"` by metis_tac[] >>
      Cases_on `STRLEN p - STRLEN A = 6`
      >- (
        (* d=6: derive x++"_split_"++y = "split_"++t, prepend "_",
           apply split_peel_contra to get "_"++x="" contradiction *)
        `DROP 7 (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y))) =
         STRCAT x (STRCAT "_split_" y)` by
          simp[listTheory.DROP_APPEND1, EVAL ``STRLEN "_split_"``] >>
        `DROP 7 (STRCAT (TAKE 6 "_split_") (STRCAT "_split_" t)) =
         STRCAT "split_" t` by (EVAL_TAC >> simp[]) >>
        `STRCAT x (STRCAT "_split_" y) = STRCAT "split_" t` by metis_tac[] >>
        (* Prepend "_": "_split_"++t = ("_"++x)++"_split_"++y *)
        `STRCAT "_split_" t =
         STRCAT (STRCAT "_" x) (STRCAT "_split_" y)` by
          metis_tac[stringTheory.STRCAT_ASSOC, stringTheory.STRCAT_11,
                    EVAL ``STRCAT "_" "split_"``] >>
        mp_tac (Q.SPECL [`STRCAT "_" x`, `t`, `y`] split_peel_contra) >>
        impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
        strip_tac >> fs[])
      >- (
        (* d = 1..5: char mismatch via EVAL *)
        `STRLEN p - STRLEN A = 1 \/ STRLEN p - STRLEN A = 2 \/
         STRLEN p - STRLEN A = 3 \/ STRLEN p - STRLEN A = 4 \/
         STRLEN p - STRLEN A = 5` by simp[] >>
        fs[])))
  >- (
    (* |A| > |p|: DROP |p| from both sides *)
    `STRLEN p < STRLEN A` by simp[] >>
    `STRLEN p <= STRLEN A` by simp[] >>
    `DROP (STRLEN p) (STRCAT p (STRCAT "_split_" t)) =
     STRCAT "_split_" t` by simp[listTheory.DROP_APPEND1] >>
    `DROP (STRLEN p) (STRCAT A (STRCAT "_split_"
       (STRCAT x (STRCAT "_split_" y)))) =
     STRCAT (DROP (STRLEN p) A) (STRCAT "_split_"
       (STRCAT x (STRCAT "_split_" y)))` by
      simp[listTheory.DROP_APPEND1] >>
    `STRCAT "_split_" t =
     STRCAT (DROP (STRLEN p) A) (STRCAT "_split_"
       (STRCAT x (STRCAT "_split_" y)))` by metis_tac[] >>
    qabbrev_tac `d = STRLEN A - STRLEN p` >>
    `STRLEN (DROP (STRLEN p) A) = d /\ d > 0 /\
     d <= STRLEN (STRCAT "_split_" t)` by
      simp[Abbr `d`, stringTheory.STRLEN_CAT] >>
    Cases_on `d >= 7`
    >- (
      (* d >= 7: A has "_split_" substring *)
      `TAKE d (STRCAT (DROP (STRLEN p) A) (STRCAT "_split_"
         (STRCAT x (STRCAT "_split_" y)))) =
       DROP (STRLEN p) A` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE d (STRCAT "_split_" t) = DROP (STRLEN p) A` by metis_tac[] >>
      `TAKE 7 (TAKE d (STRCAT "_split_" t)) =
       TAKE 7 (STRCAT "_split_" t)` by simp[rich_listTheory.TAKE_TAKE] >>
      `TAKE 7 (STRCAT "_split_" t) = "_split_"` by (EVAL_TAC >> simp[]) >>
      `TAKE 7 (DROP (STRLEN p) A) = "_split_"` by metis_tac[] >>
      `DROP (STRLEN p) A =
       STRCAT (TAKE 7 (DROP (STRLEN p) A)) (DROP 7 (DROP (STRLEN p) A))` by
        metis_tac[listTheory.TAKE_DROP] >>
      `A = STRCAT (TAKE (STRLEN p) A) (DROP (STRLEN p) A)` by
        metis_tac[listTheory.TAKE_DROP] >>
      metis_tac[])
    >- (
      (* 1 <= d <= 6 *)
      `d <= 6` by fs[] >>
      qunabbrev_tac `d` >>
      `TAKE (STRLEN A - STRLEN p) (STRCAT (DROP (STRLEN p) A) (STRCAT "_split_"
         (STRCAT x (STRCAT "_split_" y)))) =
       DROP (STRLEN p) A` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE (STRLEN A - STRLEN p) (STRCAT "_split_" t) = DROP (STRLEN p) A` by metis_tac[] >>
      `TAKE (STRLEN A - STRLEN p) (STRCAT "_split_" t) = TAKE (STRLEN A - STRLEN p) "_split_"` by
        (irule listTheory.TAKE_APPEND1 >> simp[EVAL ``STRLEN "_split_"``]) >>
      `DROP (STRLEN p) A = TAKE (STRLEN A - STRLEN p) "_split_"` by metis_tac[] >>
      Cases_on `STRLEN A - STRLEN p = 6`
      >- (
        (* d=6: t = "split_"++ rest, contradicts TAKE 6 t <> "split_" *)
        `DROP 7 (STRCAT "_split_" t) = t` by
          simp[listTheory.DROP_APPEND1, EVAL ``STRLEN "_split_"``] >>
        `DROP 7 (STRCAT (TAKE 6 "_split_") (STRCAT "_split_"
           (STRCAT x (STRCAT "_split_" y)))) =
         STRCAT "split_" (STRCAT x (STRCAT "_split_" y))` by
          (EVAL_TAC >> simp[]) >>
        `t = STRCAT "split_" (STRCAT x (STRCAT "_split_" y))` by
          metis_tac[] >>
        qpat_x_assum `t = _` SUBST_ALL_TAC >>
        fs[rich_listTheory.TAKE_APPEND1, EVAL ``STRLEN "split_"``])
      >- (
        (* d = 1..5: char mismatch via EVAL *)
        `STRLEN A - STRLEN p = 1 \/ STRLEN A - STRLEN p = 2 \/
         STRLEN A - STRLEN p = 3 \/ STRLEN A - STRLEN p = 4 \/
         STRLEN A - STRLEN p = 5` by simp[] >>
        fs[])))
QED


(* "_fwd_" cancellation: if no 4-char "_fwd" substring in either prefix,
   then the separator is unambiguous *)
Theorem fwd_cancel_right:
  !A B var var'.
    (!a b. A <> STRCAT a (STRCAT "_fwd" b)) /\
    (!a b. B <> STRCAT a (STRCAT "_fwd" b)) /\
    STRCAT A (STRCAT "_fwd_" var) = STRCAT B (STRCAT "_fwd_" var') ==>
    A = B /\ var = var'
Proof
  rpt gen_tac >> strip_tac >>
  `STRLEN A + 5 + STRLEN var = STRLEN B + 5 + STRLEN var'` by (
    qpat_x_assum `STRCAT A _ = STRCAT B _` (mp_tac o AP_TERM ``STRLEN``) >>
    simp[stringTheory.STRLEN_CAT, EVAL ``STRLEN "_fwd_"``]) >>
  Cases_on `STRLEN A = STRLEN B`
  >- (
    `STRLEN (STRCAT "_fwd_" var) = STRLEN (STRCAT "_fwd_" var')` by
      simp[stringTheory.STRLEN_CAT] >>
    `A = B` by metis_tac[listTheory.APPEND_LENGTH_EQ] >>
    qpat_x_assum `STRCAT A _ = STRCAT B _` mp_tac >>
    qpat_x_assum `A = B` SUBST_ALL_TAC >>
    simp[stringTheory.STRCAT_11])
  >> Cases_on `STRLEN A < STRLEN B`
  >- (
    (* |A| < |B|: B = A ++ Z, then "_fwd_"++var = Z++"_fwd_"++var' *)
    `DROP (STRLEN A) (STRCAT A (STRCAT "_fwd_" var)) =
     STRCAT "_fwd_" var` by simp[listTheory.DROP_APPEND1] >>
    `STRLEN A <= STRLEN B` by simp[] >>
    `DROP (STRLEN A) (STRCAT B (STRCAT "_fwd_" var')) =
     STRCAT (DROP (STRLEN A) B) (STRCAT "_fwd_" var')` by
      simp[listTheory.DROP_APPEND1] >>
    `STRCAT "_fwd_" var =
     STRCAT (DROP (STRLEN A) B) (STRCAT "_fwd_" var')` by metis_tac[] >>
    qabbrev_tac `d = STRLEN B - STRLEN A` >>
    `STRLEN (DROP (STRLEN A) B) = d /\ d > 0` by
      simp[Abbr `d`] >>
    Cases_on `d >= 4`
    >- (
      (* d >= 4: TAKE 4 of (DROP |A| B) = "_fwd" => B has "_fwd" substring *)
      `TAKE d (STRCAT (DROP (STRLEN A) B) (STRCAT "_fwd_" var')) =
       DROP (STRLEN A) B` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE d (STRCAT "_fwd_" var) = DROP (STRLEN A) B` by metis_tac[] >>
      `4 <= d` by simp[] >>
      `TAKE 4 (TAKE d (STRCAT "_fwd_" var)) =
       TAKE 4 (STRCAT "_fwd_" var)` by
        simp[rich_listTheory.TAKE_TAKE] >>
      `TAKE 4 (STRCAT "_fwd_" var) = "_fwd"` by (EVAL_TAC >> simp[]) >>
      `TAKE 4 (DROP (STRLEN A) B) = "_fwd"` by metis_tac[] >>
      `DROP (STRLEN A) B =
       STRCAT (TAKE 4 (DROP (STRLEN A) B)) (DROP 4 (DROP (STRLEN A) B))` by
        metis_tac[listTheory.TAKE_DROP] >>
      `B = STRCAT (TAKE (STRLEN A) B) (DROP (STRLEN A) B)` by
        metis_tac[listTheory.TAKE_DROP] >>
      metis_tac[])
    >- (
      (* d = 1..3: char mismatch *)
      `d <= 3` by fs[] >>
      qunabbrev_tac `d` >>
      `TAKE (STRLEN B - STRLEN A) (STRCAT (DROP (STRLEN A) B)
         (STRCAT "_fwd_" var')) = DROP (STRLEN A) B` by
        simp[listTheory.TAKE_APPEND1] >>
      `TAKE (STRLEN B - STRLEN A) (STRCAT "_fwd_" var) =
       DROP (STRLEN A) B` by metis_tac[] >>
      `TAKE (STRLEN B - STRLEN A) (STRCAT "_fwd_" var) =
       TAKE (STRLEN B - STRLEN A) "_fwd_"` by
        (irule listTheory.TAKE_APPEND1 >>
         simp[EVAL ``STRLEN "_fwd_"``]) >>
      `DROP (STRLEN A) B =
       TAKE (STRLEN B - STRLEN A) "_fwd_"` by metis_tac[] >>
      `STRLEN B - STRLEN A = 1 \/ STRLEN B - STRLEN A = 2 \/
       STRLEN B - STRLEN A = 3` by simp[] >>
      fs[]))
  >- (
    (* |A| > |B|: symmetric *)
    `STRLEN B < STRLEN A` by simp[] >>
    `STRLEN B <= STRLEN A` by simp[] >>
    `DROP (STRLEN B) (STRCAT B (STRCAT "_fwd_" var')) =
     STRCAT "_fwd_" var'` by simp[listTheory.DROP_APPEND1] >>
    `DROP (STRLEN B) (STRCAT A (STRCAT "_fwd_" var)) =
     STRCAT (DROP (STRLEN B) A) (STRCAT "_fwd_" var)` by
      simp[listTheory.DROP_APPEND1] >>
    `STRCAT "_fwd_" var' =
     STRCAT (DROP (STRLEN B) A) (STRCAT "_fwd_" var)` by metis_tac[] >>
    qabbrev_tac `d = STRLEN A - STRLEN B` >>
    `STRLEN (DROP (STRLEN B) A) = d /\ d > 0` by
      simp[Abbr `d`] >>
    Cases_on `d >= 4`
    >- (
      `TAKE d (STRCAT (DROP (STRLEN B) A) (STRCAT "_fwd_" var)) =
       DROP (STRLEN B) A` by simp[listTheory.TAKE_APPEND1] >>
      `TAKE d (STRCAT "_fwd_" var') = DROP (STRLEN B) A` by metis_tac[] >>
      `4 <= d` by simp[] >>
      `TAKE 4 (TAKE d (STRCAT "_fwd_" var')) =
       TAKE 4 (STRCAT "_fwd_" var')` by
        simp[rich_listTheory.TAKE_TAKE] >>
      `TAKE 4 (STRCAT "_fwd_" var') = "_fwd"` by (EVAL_TAC >> simp[]) >>
      `TAKE 4 (DROP (STRLEN B) A) = "_fwd"` by metis_tac[] >>
      `DROP (STRLEN B) A =
       STRCAT (TAKE 4 (DROP (STRLEN B) A)) (DROP 4 (DROP (STRLEN B) A))` by
        metis_tac[listTheory.TAKE_DROP] >>
      `A = STRCAT (TAKE (STRLEN B) A) (DROP (STRLEN B) A)` by
        metis_tac[listTheory.TAKE_DROP] >>
      metis_tac[])
    >- (
      `d <= 3` by fs[] >>
      qunabbrev_tac `d` >>
      `TAKE (STRLEN A - STRLEN B) (STRCAT (DROP (STRLEN B) A)
         (STRCAT "_fwd_" var)) = DROP (STRLEN B) A` by
        simp[listTheory.TAKE_APPEND1] >>
      `TAKE (STRLEN A - STRLEN B) (STRCAT "_fwd_" var') =
       DROP (STRLEN B) A` by metis_tac[] >>
      `TAKE (STRLEN A - STRLEN B) (STRCAT "_fwd_" var') =
       TAKE (STRLEN A - STRLEN B) "_fwd_"` by
        (irule listTheory.TAKE_APPEND1 >>
         simp[EVAL ``STRLEN "_fwd_"``]) >>
      `DROP (STRLEN B) A =
       TAKE (STRLEN A - STRLEN B) "_fwd_"` by metis_tac[] >>
      `STRLEN A - STRLEN B = 1 \/ STRLEN A - STRLEN B = 2 \/
       STRLEN A - STRLEN B = 3` by simp[] >>
      fs[]))
QED

(* ================================================================
   Section 8: Generic lifting and invariant preservation
   ================================================================ *)

(* Generic lifting: if P is preserved by insert_split, then
   find_and_split preserves P *)
Theorem find_and_split_preserves:
  !P bbs func id_base func' id_base'.
    P func /\
    EVERY (\bb. MEM bb func.fn_blocks) bbs /\
    (!pred_bb target_bb id.
       P func /\
       MEM pred_bb func.fn_blocks /\
       MEM target_bb func.fn_blocks /\
       MEM target_bb.bb_label (bb_succs pred_bb) /\
       num_succs pred_bb > 1 /\
       LENGTH (block_preds func target_bb.bb_label) > 1 ==>
       P (insert_split func pred_bb target_bb id)) /\
    find_and_split func id_base bbs = (func', T, id_base') ==>
    P func'
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac >>
  fs[find_and_split_def, LET_THM] >>
  BasicProvers.every_case_tac >> fs[] >>
  TRY (first_x_assum irule >> simp[] >> metis_tac[] >> NO_TAC) >>
  rename1 `FIND _ _ = SOME pred_bb` >>
  `num_succs pred_bb > 1` by
    (imp_res_tac venomExecProofsTheory.FIND_P >> fs[]) >>
  `MEM pred_bb (block_preds func h.bb_label)` by
    (imp_res_tac venomExecProofsTheory.FIND_MEM >> fs[]) >>
  `MEM pred_bb func.fn_blocks /\ MEM h.bb_label (bb_succs pred_bb)` by
    fs[block_preds_def, listTheory.MEM_FILTER] >>
  `LENGTH (block_preds func h.bb_label) > 1` by
    (fs[] >> DECIDE_TAC) >>
  qpat_x_assum `insert_split _ _ _ _ = _` (SUBST1_TAC o GSYM) >>
  first_x_assum (qspecl_then [`pred_bb`, `h`, `id_base`] match_mp_tac) >>
  simp[]
QED

(* ================================================================
   Section 8a: Toolkit for insert_split invariant preservation
   ================================================================ *)

(* MEM in replace_block *)
Theorem MEM_replace_block[local]:
  !bb lbl bb' bbs.
    MEM bb (replace_block lbl bb' bbs) <=>
    (bb = bb' /\ MEM lbl (MAP (\b. b.bb_label) bbs)) \/
    (MEM bb bbs /\ bb.bb_label <> lbl)
Proof
  rw[cfgTransformTheory.replace_block_def, listTheory.MEM_MAP] >>
  eq_tac >> strip_tac >> fs[] >> rw[] >> fs[] >>
  TRY (DISJ1_TAC >> qexists_tac `bb''` >> fs[] >> NO_TAC) >>
  TRY (qexists_tac `bb` >> fs[] >> NO_TAC) >>
  qexists_tac `b` >> fs[]
QED

(* MEM in insert_split output blocks *)
Theorem MEM_insert_split:
  !bb func pred_bb target_bb id_base.
    let (split_bb, var_repls) = build_split_block pred_bb target_bb id_base in
    let split_lbl = split_bb.bb_label in
    let pred_bb' = subst_label_terminator target_bb.bb_label split_lbl pred_bb in
    let target_bb' = update_phis_for_split pred_bb.bb_label split_lbl var_repls target_bb in
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks ==>
    (MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks <=>
     bb = split_bb \/
     (bb = pred_bb' /\ MEM pred_bb func.fn_blocks) \/
     (bb = target_bb' /\ MEM target_bb func.fn_blocks) \/
     (MEM bb func.fn_blocks /\
      bb.bb_label <> pred_bb.bb_label /\
      bb.bb_label <> target_bb.bb_label))
Proof
  rw[cfgNormDefsTheory.insert_split_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  simp[listTheory.MEM_APPEND, MEM_replace_block,
       cfgNormSimTheory.subst_label_terminator_bb_label,
       cfgNormSimTheory.update_phis_for_split_bb_label] >>
  simp[fn_labels_def] >>
  strip_tac >>
  `MEM pred_bb.bb_label (MAP (\b. b.bb_label) func.fn_blocks)` by
    (rw[listTheory.MEM_MAP] >> qexists_tac `pred_bb` >> fs[]) >>
  `MAP (\b. b.bb_label)
      (replace_block pred_bb.bb_label
        (subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb)
        func.fn_blocks) =
   MAP (\b. b.bb_label) func.fn_blocks` by
    (irule cfgTransformPropsTheory.fn_labels_replace_block >>
     rw[cfgNormSimTheory.subst_label_terminator_bb_label]) >>
  `MEM target_bb.bb_label (MAP (\b. b.bb_label) func.fn_blocks)` by
    (rw[listTheory.MEM_MAP] >> qexists_tac `target_bb` >> fs[]) >>
  fs[] >>
  eq_tac >> rw[] >>
  fs[cfgNormSimTheory.subst_label_terminator_bb_label]
QED

(* Substituting a label preserves whether an operand carries a label. *)
Theorem get_label_subst_label_op_is_some[local]:
  !old_lbl new_lbl op.
    IS_SOME (get_label op) ==>
    IS_SOME (get_label (subst_label_op old_lbl new_lbl op))
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[cfgTransformTheory.subst_label_op_def,
      venomStateTheory.get_label_def] >>
  Cases_on `s = old_lbl` >>
  gvs[venomStateTheory.get_label_def]
QED

(* Core lemma: subst_label_op preserves get_label structure *)
Theorem get_labels_subst_label_ops[local]:
  !ops old_lbl new_lbl.
    MAP THE (FILTER IS_SOME (MAP get_label (MAP (subst_label_op old_lbl new_lbl) ops))) =
    MAP (\l. if l = old_lbl then new_lbl else l)
        (MAP THE (FILTER IS_SOME (MAP get_label ops)))
Proof
  Induct >> rw[] >>
  Cases_on `h` >>
  rw[cfgTransformTheory.subst_label_op_def,
     venomStateTheory.get_label_def] >>
  fs[venomStateTheory.get_label_def,
     cfgTransformTheory.subst_label_op_def,
     COND_RAND, COND_RATOR]
QED

(* get_successors of subst_label_inst *)
Theorem get_successors_subst_label_inst[local]:
  !old_lbl new_lbl inst.
    is_terminator inst.inst_opcode ==>
    get_successors (subst_label_inst old_lbl new_lbl inst) =
    MAP (\l. if l = old_lbl then new_lbl else l) (get_successors inst)
Proof
  rw[cfgTransformTheory.subst_label_inst_def, get_successors_def,
     venomInstTheory.is_terminator_def, get_labels_subst_label_ops]
QED

(* bb_succs when instructions are non-empty *)
Theorem bb_succs_nonempty[local]:
  !bb. bb.bb_instructions <> [] ==>
    bb_succs bb = nub (REVERSE (get_successors (LAST bb.bb_instructions)))
Proof
  rw[bb_succs_def] >> Cases_on `bb.bb_instructions` >> fs[]
QED

(* LAST of subst_label_terminator instructions *)
Theorem LAST_subst_label_terminator[local]:
  !old_lbl new_lbl bb.
    bb.bb_instructions <> [] ==>
    LAST (subst_label_terminator old_lbl new_lbl bb).bb_instructions =
    let i = LAST bb.bb_instructions in
    if is_terminator i.inst_opcode then subst_label_inst old_lbl new_lbl i else i
Proof
  rw[cfgTransformTheory.subst_label_terminator_def, listTheory.LAST_MAP, LET_THM]
QED

(* bb_succs of subst_label_terminator *)
Theorem bb_succs_subst_label_terminator[local]:
  !old_lbl new_lbl bb.
    bb.bb_instructions <> [] ==>
    bb_succs (subst_label_terminator old_lbl new_lbl bb) =
    if is_terminator (LAST bb.bb_instructions).inst_opcode then
      nub (REVERSE (MAP (\l. if l = old_lbl then new_lbl else l)
                        (get_successors (LAST bb.bb_instructions))))
    else bb_succs bb
Proof
  rw[] >>
  `(subst_label_terminator old_lbl new_lbl bb).bb_instructions <> []` by
    fs[cfgTransformTheory.subst_label_terminator_def] >>
  rw[bb_succs_nonempty, LAST_subst_label_terminator, LET_THM,
     get_successors_subst_label_inst]
QED

(* Corollary: non-new labels in subst_label_terminator succs were original succs *)
Theorem MEM_bb_succs_subst_back[local]:
  !old_lbl new_lbl bb lbl.
    bb_well_formed bb /\
    MEM lbl (bb_succs (subst_label_terminator old_lbl new_lbl bb)) /\
    lbl <> new_lbl ==>
    MEM lbl (bb_succs bb)
Proof
  rpt strip_tac >>
  sg `bb.bb_instructions <> []`
  >- fs[venomWfTheory.bb_well_formed_def] >>
  fs[bb_succs_subst_label_terminator] >>
  Cases_on `is_terminator (LAST bb.bb_instructions).inst_opcode` >>
  fs[listTheory.MEM_nub, listTheory.MEM_REVERSE, listTheory.MEM_MAP] >>
  BasicProvers.every_case_tac >> fs[] >>
  imp_res_tac bb_succs_nonempty >>
  fs[listTheory.MEM_nub, listTheory.MEM_REVERSE]
QED

(* old label is NOT in bb_succs after subst_label_terminator *)
Theorem old_not_in_subst_succs[local]:
  !old_lbl new_lbl bb.
    bb_well_formed bb /\ old_lbl <> new_lbl ==>
    ~MEM old_lbl (bb_succs (subst_label_terminator old_lbl new_lbl bb))
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by
    fs[venomWfTheory.bb_well_formed_def] >>
  fs[bb_succs_subst_label_terminator] >>
  Cases_on `is_terminator (LAST bb.bb_instructions).inst_opcode` >>
  gvs[listTheory.MEM_nub, listTheory.MEM_REVERSE, listTheory.MEM_MAP,
      bb_succs_def, get_successors_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* bb_succs of split_bb: just [target_bb.bb_label] *)
Theorem bb_succs_split_bb[local]:
  !pred_bb target_bb id_base split_bb var_repls.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) ==>
    bb_succs split_bb = [target_bb.bb_label]
Proof
  rw[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  simp[bb_succs_nonempty, rich_listTheory.LAST_APPEND_NOT_NIL,
       get_successors_def, venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.nub_def]
QED

(* num_succs of split_bb = 1 *)
Theorem num_succs_split_bb[local]:
  !pred_bb target_bb id_base split_bb var_repls.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) ==>
    num_succs split_bb = 1
Proof
  rw[cfgTransformTheory.num_succs_def] >>
  imp_res_tac bb_succs_split_bb >> simp[]
QED

(* split_bb is well-formed *)
Theorem bb_well_formed_split_bb[local]:
  !pred_bb target_bb id_base split_bb var_repls.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) ==>
    bb_well_formed split_bb
Proof
  rw[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  simp[bb_well_formed_def, rich_listTheory.LAST_APPEND,
       venomInstTheory.is_terminator_def] >>
  rpt conj_tac >-
  (rw[] >>
   imp_res_tac cfgNormSimTheory.build_forwarding_assigns_insts >>
   Cases_on `i < LENGTH fwd_insts` >-
   (fs[rich_listTheory.EL_APPEND1] >>
    `(EL i fwd_insts).inst_opcode = ASSIGN` by simp[] >>
    fs[venomInstTheory.is_terminator_def]) >>
   fs[rich_listTheory.EL_APPEND2] >>
   `i - LENGTH fwd_insts = 0` by DECIDE_TAC >>
   fs[venomInstTheory.is_terminator_def]) >>
  rw[] >>
  imp_res_tac cfgNormSimTheory.build_forwarding_assigns_insts >>
  Cases_on `j < LENGTH fwd_insts` >-
  (`(EL j fwd_insts).inst_opcode = ASSIGN` by simp[] >>
   fs[rich_listTheory.EL_APPEND1]) >>
  `j = LENGTH fwd_insts` by DECIDE_TAC >>
  fs[rich_listTheory.EL_APPEND2]
QED

(* bb_well_formed preserved by subst_label_terminator *)
Theorem bb_well_formed_map_opcode_preserving[local]:
  !f bb. (!inst. (f inst).inst_opcode = inst.inst_opcode) ==>
    bb_well_formed bb ==>
    bb_well_formed (bb with bb_instructions := MAP f bb.bb_instructions)
Proof
  rw[bb_well_formed_def] >>
  `!n. n < LENGTH bb.bb_instructions ==>
    (MAP f bb.bb_instructions)❲n❳.inst_opcode =
    bb.bb_instructions❲n❳.inst_opcode` by
    simp[listTheory.EL_MAP] >>
  res_tac >> fs[]
QED

Theorem bb_well_formed_subst_label_terminator[local]:
  !old_lbl new_lbl bb.
    bb_well_formed bb ==>
    bb_well_formed (subst_label_terminator old_lbl new_lbl bb)
Proof
  rw[cfgTransformTheory.subst_label_terminator_def] >>
  irule bb_well_formed_map_opcode_preserving >> rw[] >>
  Cases_on `is_terminator inst.inst_opcode` >>
  simp[cfgTransformTheory.subst_label_inst_def]
QED

(* bb_well_formed preserved by update_phis_for_split *)
Theorem bb_well_formed_update_phis[local]:
  !old_lbl new_lbl var_repls bb.
    bb_well_formed bb ==>
    bb_well_formed (update_phis_for_split old_lbl new_lbl var_repls bb)
Proof
  rw[cfgNormDefsTheory.update_phis_for_split_def] >>
  irule bb_well_formed_map_opcode_preserving >> rw[]
QED

(* Label substitution does not change DRET's literal/count envelope. *)
Theorem parse_dret_shape_subst_label_inst[local]:
  !old_lbl new_lbl inst.
    parse_dret_shape (subst_label_inst old_lbl new_lbl inst) =
    parse_dret_shape inst
Proof
  rw[cfgTransformTheory.subst_label_inst_def,
     dretShapeDefsTheory.parse_dret_shape_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `h` >>
  gvs[cfgTransformTheory.subst_label_op_def] >>
  Cases_on `s = old_lbl` >> gvs[]
QED

(* inst_wf preserved by subst_label_inst for terminators *)
Theorem inst_wf_subst_label_inst[local]:
  !old_lbl new_lbl inst.
    inst_wf inst /\ is_terminator inst.inst_opcode ==>
    inst_wf (subst_label_inst old_lbl new_lbl inst)
Proof
  rw[cfgTransformTheory.subst_label_inst_def, inst_wf_def] >>
  Cases_on `inst.inst_opcode` >>
  fs[venomInstTheory.is_terminator_def, listTheory.LENGTH_MAP,
     listTheory.MAP_MAP_o, cfgTransformTheory.subst_label_op_def] >>
  rw[] >> fs[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rw[] >> res_tac >>
  FIRST
    [(rename1 `IS_SOME (get_label (subst_label_op old_lbl new_lbl x))` >>
      qspecl_then [`old_lbl`, `new_lbl`, `x`] mp_tac
        get_label_subst_label_op_is_some >> simp[]),
     (qspecl_then [`old_lbl`, `new_lbl`, `inst`] mp_tac
        parse_dret_shape_subst_label_inst >>
      simp[cfgTransformTheory.subst_label_inst_def])]
QED

(* inst_wf of instructions in subst_label_terminator *)
Theorem inst_wf_subst_label_terminator[local]:
  !old_lbl new_lbl bb inst.
    EVERY inst_wf bb.bb_instructions /\
    MEM inst (subst_label_terminator old_lbl new_lbl bb).bb_instructions ==>
    inst_wf inst
Proof
  rw[cfgTransformTheory.subst_label_terminator_def, listTheory.MEM_MAP] >>
  Cases_on `is_terminator inst'.inst_opcode` >> fs[] >-
  (irule inst_wf_subst_label_inst >> fs[listTheory.EVERY_MEM]) >>
  fs[listTheory.EVERY_MEM]
QED

Theorem phi_well_formed_update_phi_ops[local]:
  !ops old_lbl new_lbl var_repls.
    phi_well_formed ops ==>
    phi_well_formed (update_phi_ops old_lbl new_lbl var_repls ops)
Proof
  Induct_on `ops` using venomWfTheory.phi_well_formed_ind >>
  simp[venomWfTheory.phi_well_formed_def,
       cfgNormDefsTheory.update_phi_ops_def] >>
  rw[] >> fs[venomWfTheory.phi_well_formed_def] >>
  BasicProvers.every_case_tac >>
  fs[venomWfTheory.phi_well_formed_def]
QED

(* inst_wf of instructions in update_phis_for_split *)
Theorem inst_wf_update_phis[local]:
  !old_lbl new_lbl var_repls bb inst.
    EVERY inst_wf bb.bb_instructions /\
    MEM inst (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions ==>
    inst_wf inst
Proof
  rw[cfgNormDefsTheory.update_phis_for_split_def, listTheory.MEM_MAP] >>
  Cases_on `inst'.inst_opcode = PHI` >> fs[listTheory.EVERY_MEM] >>
  `inst_wf inst'` by res_tac >>
  imp_res_tac inst_wf_phi_well_formed >>
  simp[inst_wf_def] >>
  irule phi_well_formed_update_phi_ops >> fs[]
QED

(* inst_wf of instructions in split_bb *)
Theorem inst_wf_split_bb[local]:
  !pred_bb target_bb id_base split_bb var_repls inst.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    MEM inst split_bb.bb_instructions ==>
    inst_wf inst
Proof
  rw[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  fs[listTheory.MEM_APPEND] >-
  (imp_res_tac cfgNormSimTheory.build_forwarding_assigns_insts >>
   fs[listTheory.MEM_EL] >>
   `(EL n fwd_insts).inst_opcode = ASSIGN /\
    (EL n fwd_insts).inst_operands = [Var (EL n (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb target_bb.bb_instructions)))] /\
    (EL n fwd_insts).inst_outputs = [STRCAT (STRCAT (split_block_name pred_bb.bb_label target_bb.bb_label) "_fwd_") (EL n (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb target_bb.bb_instructions)))]` by simp[] >>
   rw[inst_wf_def]) >>
  fs[] >> rw[inst_wf_def] >>
  simp[venomInstTheory.is_terminator_def]
QED

(* ================================================================
   Section 8b: insert_split_preserves_inv infrastructure
   ================================================================ *)

(* inst_id preservation *)
Theorem inst_ids_subst_label_terminator[local]:
  !old_lbl new_lbl bb.
    MAP (\i. i.inst_id) (subst_label_terminator old_lbl new_lbl bb).bb_instructions =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rw[cfgTransformTheory.subst_label_terminator_def, listTheory.MAP_MAP_o,
     combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> rw[] >>
  rw[cfgTransformProofsTheory.subst_label_inst_fields]
QED

Theorem inst_ids_update_phis[local]:
  !old_lbl new_lbl var_repls bb.
    MAP (\i. i.inst_id) (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions =
    MAP (\i. i.inst_id) bb.bb_instructions
Proof
  rw[cfgNormDefsTheory.update_phis_for_split_def, listTheory.MAP_MAP_o,
     combinTheory.o_DEF] >>
  irule listTheory.MAP_CONG >> rw[]
QED

(* General: if new bb has same LAST instruction and non-empty, bb_succs is same *)
Theorem bb_succs_same_last[local]:
  !bb bb'.
    bb.bb_instructions <> [] /\
    bb'.bb_instructions <> [] /\
    LAST bb'.bb_instructions = LAST bb.bb_instructions ==>
    bb_succs bb' = bb_succs bb
Proof
  rpt strip_tac >>
  imp_res_tac bb_succs_nonempty >> simp[]
QED

(* LAST instruction preserved by update_phis_for_split *)
Theorem LAST_update_phis_for_split[local]:
  !old_lbl new_lbl var_repls bb.
    bb_well_formed bb ==>
    LAST (update_phis_for_split old_lbl new_lbl var_repls bb).bb_instructions =
    LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by fs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     fs[venomInstTheory.is_terminator_def]) >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[]) >>
  `bb.bb_instructions❲PRE (LENGTH bb.bb_instructions)❳.inst_opcode <> PHI` by
    simp[GSYM listTheory.LAST_EL] >>
  simp[cfgNormDefsTheory.update_phis_for_split_def, listTheory.LAST_EL,
       cfgNormSimTheory.update_phis_for_split_length,
       cfgNormSimTheory.update_phis_for_split_non_phi]
QED

(* bb_succs preservation for update_phis *)
Theorem bb_succs_update_phis[local]:
  !old_lbl new_lbl var_repls bb.
    bb_well_formed bb ==>
    bb_succs (update_phis_for_split old_lbl new_lbl var_repls bb) = bb_succs bb
Proof
  rpt strip_tac >>
  irule bb_succs_same_last >>
  fs[bb_well_formed_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> PHI` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     fs[venomInstTheory.is_terminator_def]) >>
  simp[cfgNormDefsTheory.update_phis_for_split_def,
       LAST_update_phis_for_split]
QED

(* cfg_norm_inv conjunct extractors -- uniform proof: rw + res_tac + simp *)
val inv_tac = rw[cfg_norm_inv_def] >> res_tac >> simp[];

Theorem cfg_norm_inv_wf:
  !func0 func. cfg_norm_inv func0 func ==> wf_function_no_ids func
Proof
  inv_tac
QED

Theorem cfg_norm_inv_inst_wf:
  !func0 func. cfg_norm_inv func0 func ==> fn_inst_wf func
Proof
  inv_tac
QED

Theorem cfg_norm_inv_phi_preds:
  !func0 func. cfg_norm_inv func0 func ==> fn_phi_preds_closed func
Proof
  inv_tac
QED

Theorem cfg_norm_inv_phi_noninterf:
  !func0 func. cfg_norm_inv func0 func ==> fn_phis_non_interfering func
Proof
  inv_tac
QED

Theorem cfg_norm_inv_phi_distinct:
  !func0 func. cfg_norm_inv func0 func ==> fn_phi_labels_distinct func
Proof
  inv_tac
QED

Theorem cfg_norm_inv_labels_distinct:
  !func0 func. cfg_norm_inv func0 func ==> ALL_DISTINCT (fn_labels func)
Proof
  inv_tac
QED

Theorem cfg_norm_inv_label_origin:
  !func0 func lbl. cfg_norm_inv func0 func /\ MEM lbl (fn_labels func) ==>
    MEM lbl (fn_labels func0) \/
    ?p t. MEM p (fn_labels func0) /\ MEM t (fn_labels func0) /\
          lbl = split_block_name p t
Proof
  inv_tac
QED

Theorem cfg_norm_inv_inj:
  !func0 func p1 t1 p2 t2.
    cfg_norm_inv func0 func /\
    MEM p1 (fn_labels func0) /\ MEM t1 (fn_labels func0) /\
    MEM p2 (fn_labels func0) /\ MEM t2 (fn_labels func0) /\
    split_block_name p1 t1 = split_block_name p2 t2 ==>
    p1 = p2 /\ t1 = t2
Proof
  rpt strip_tac >>
  qpat_x_assum `cfg_norm_inv func0 func` mp_tac >>
  PURE_REWRITE_TAC[cfg_norm_inv_def] >> strip_tac >>
  qpat_x_assum `!p1 t1 p2 t2. _`
    (qspecl_then [`p1`, `t1`, `p2`, `t2`] mp_tac) >>
  simp[]
QED

Theorem cfg_norm_inv_split_fresh:
  !func0 func. cfg_norm_inv func0 func ==> split_labels_fresh split_block_name func0
Proof
  inv_tac
QED

(* edge_fresh already exists as cfg_norm_inv_edge_fresh *)

Theorem cfg_norm_inv_var_fresh:
  !func0 func pred_lbl tgt_lbl var.
    cfg_norm_inv func0 func /\
    MEM pred_lbl (fn_labels func0) /\ MEM tgt_lbl (fn_labels func0) /\
    MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
                (fn_all_vars func) ==>
    MEM (split_block_name pred_lbl tgt_lbl) (fn_labels func)
Proof
  inv_tac
QED

Theorem cfg_norm_inv_no_self_loop:
  !func0 func bb lbl. cfg_norm_inv func0 func /\
    MEM bb func.fn_blocks /\ MEM lbl (bb_succs bb) ==>
    lbl <> bb.bb_label
Proof
  rw[cfg_norm_inv_def] >> rpt strip_tac >>
  res_tac >> fs[]
QED

Theorem cfg_norm_inv_entry:
  !func0 func. cfg_norm_inv func0 func ==> fn_entry_label func = fn_entry_label func0
Proof
  inv_tac
QED

Theorem cfg_norm_inv_nonoriginal_1succ[local]:
  !func0 func bb. cfg_norm_inv func0 func /\
    MEM bb func.fn_blocks /\ ~MEM bb.bb_label (fn_labels func0) ==>
    num_succs bb <= 1
Proof
  rw[cfg_norm_inv_def] >> res_tac >> res_tac
QED

Theorem cfg_norm_inv_nonoriginal_1pred[local]:
  !func0 func lbl bb1 bb2.
    cfg_norm_inv func0 func /\
    MEM bb1 func.fn_blocks /\ MEM bb2 func.fn_blocks /\
    MEM lbl (bb_succs bb1) /\ MEM lbl (bb_succs bb2) /\
    ~MEM lbl (fn_labels func0) ==>
    bb1.bb_label = bb2.bb_label
Proof
  rw[cfg_norm_inv_def] >> res_tac >> res_tac
QED

Theorem cfg_norm_inv_block_ids:
  !func0 func bb. cfg_norm_inv func0 func /\ MEM bb func.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rw[cfg_norm_inv_def] >> res_tac >> simp[]
QED

Theorem cfg_norm_inv_sep_clean:
  !func0 func L. cfg_norm_inv func0 func /\ MEM L (fn_labels func0) ==>
    TAKE 6 L <> "split_"
Proof
  rw[cfg_norm_inv_def]
QED

Theorem cfg_norm_inv_fwd_clean:
  !func0 func L. cfg_norm_inv func0 func /\ MEM L (fn_labels func0) ==>
    !a b. L <> STRCAT a (STRCAT "_fwd" b)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `cfg_norm_inv func0 func` mp_tac >>
  PURE_REWRITE_TAC[cfg_norm_inv_def] >>
  strip_tac >>
  qpat_x_assum `!L. MEM L (fn_labels func0) ==> !a b. _`
    (qspec_then `L` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac
QED

Theorem cfg_norm_inv_no_split_suffix:
  !func0 func L. cfg_norm_inv func0 func /\ MEM L (fn_labels func0) ==>
    !x. L <> STRCAT x "_split"
Proof
  rw[cfg_norm_inv_def]
QED

Theorem cfg_norm_inv_double_split_preconds[local]:
  !func0 func A p t.
    cfg_norm_inv func0 func /\
    MEM A (fn_labels func0) /\ MEM p (fn_labels func0) /\
    MEM t (fn_labels func0) ==>
    (!a b. A <> STRCAT a (STRCAT "_split_" b)) /\
    (!a b. p <> STRCAT a (STRCAT "_split_" b)) /\
    (!a b. t <> STRCAT a (STRCAT "_split_" b)) /\
    TAKE 6 t <> "split_"
Proof
  rw[]
  >- (`split_labels_fresh split_block_name func0` by fs[cfg_norm_inv_def] >>
      mp_tac (Q.SPECL [`func0`, `A`, `a`, `b`] original_no_split_substr) >>
      simp[stringTheory.STRCAT_ASSOC])
  >- (`split_labels_fresh split_block_name func0` by fs[cfg_norm_inv_def] >>
      mp_tac (Q.SPECL [`func0`, `p`, `a`, `b`] original_no_split_substr) >>
      simp[stringTheory.STRCAT_ASSOC])
  >- (`split_labels_fresh split_block_name func0` by fs[cfg_norm_inv_def] >>
      mp_tac (Q.SPECL [`func0`, `t`, `a`, `b`] original_no_split_substr) >>
      simp[stringTheory.STRCAT_ASSOC])
  >- (drule_all cfg_norm_inv_sep_clean >> simp[])
QED

(* Inner nesting of split_block_name can never equal single split_block_name
   when all component labels are original. *)
Theorem double_split_inner_contra[local]:
  !func0 func A q r p t.
    cfg_norm_inv func0 func /\
    MEM A (fn_labels func0) /\ MEM q (fn_labels func0) /\
    MEM r (fn_labels func0) /\ MEM p (fn_labels func0) /\
    MEM t (fn_labels func0) /\
    split_block_name A (split_block_name q r) = split_block_name p t ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `split_block_name _ _ = split_block_name _ _` mp_tac >>
  PURE_REWRITE_TAC[cfgNormDefsTheory.split_block_name_def] >>
  mp_tac (Q.SPECL [`A`, `p`, `t`, `q`, `r`] double_split_contra) >>
  impl_tac >- metis_tac[cfg_norm_inv_double_split_preconds] >>
  simp[]
QED

(* Generalized injectivity: first arg must be original, second can be any
   label in fn_labels func. Combines cfg_norm_inv_inj + double_split_contra.
   Useful when lbl comes from fn_succs_closed (may be non-original). *)
Theorem cfg_norm_inv_inj_gen[local]:
  !func0 func A lbl p t.
    cfg_norm_inv func0 func /\
    MEM A (fn_labels func0) /\
    MEM lbl (fn_labels func) /\
    MEM p (fn_labels func0) /\ MEM t (fn_labels func0) /\
    split_block_name A lbl = split_block_name p t ==>
    A = p /\ lbl = t
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`func0`, `func`, `lbl`] cfg_norm_inv_label_origin) >>
  (impl_tac >- simp[]) >> strip_tac
  >- (
    (* lbl original: direct injectivity *)
    mp_tac (Q.SPECL [`func0`, `func`, `A`, `lbl`, `p`, `t`]
      cfg_norm_inv_inj) >> simp[]
  ) >>
  (* lbl = split_block_name q r: contradiction *)
  qpat_x_assum `lbl = split_block_name _ _` SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`func0`, `func`, `A`, `p'`, `t'`, `p`, `t`]
    double_split_inner_contra) >> simp[]
QED

(* Introduction rule: construct cfg_norm_inv from 18 conjuncts *)
Theorem cfg_norm_inv_intro:
  !func0 func.
    wf_function_no_ids func /\
    fn_inst_wf func /\
    fn_phi_preds_closed func /\
    fn_phis_non_interfering func /\
    fn_phi_labels_distinct func /\
    ALL_DISTINCT (fn_labels func) /\
    (!lbl. MEM lbl (fn_labels func) ==>
       MEM lbl (fn_labels func0) \/
       ?p t. MEM p (fn_labels func0) /\ MEM t (fn_labels func0) /\
             lbl = split_block_name p t) /\
    (!p1 t1 p2 t2.
       MEM p1 (fn_labels func0) /\ MEM t1 (fn_labels func0) /\
       MEM p2 (fn_labels func0) /\ MEM t2 (fn_labels func0) /\
       split_block_name p1 t1 = split_block_name p2 t2 ==>
       p1 = p2 /\ t1 = t2) /\
    split_labels_fresh split_block_name func0 /\
    (!bb lbl. MEM bb func.fn_blocks /\ MEM lbl (bb_succs bb) ==>
       ~MEM (split_block_name bb.bb_label lbl) (fn_labels func)) /\
    (!pred_lbl tgt_lbl var.
       MEM pred_lbl (fn_labels func0) /\ MEM tgt_lbl (fn_labels func0) /\
       MEM (STRCAT (STRCAT (split_block_name pred_lbl tgt_lbl) "_fwd_") var)
                   (fn_all_vars func) ==>
       MEM (split_block_name pred_lbl tgt_lbl) (fn_labels func)) /\
    (!bb. MEM bb func.fn_blocks ==>
       !lbl. MEM lbl (bb_succs bb) ==> lbl <> bb.bb_label) /\
    fn_entry_label func = fn_entry_label func0 /\
    (!bb. MEM bb func.fn_blocks /\ ~MEM bb.bb_label (fn_labels func0) ==>
      num_succs bb <= 1) /\
    (!lbl bb1 bb2. MEM bb1 func.fn_blocks /\ MEM bb2 func.fn_blocks /\
      MEM lbl (bb_succs bb1) /\ MEM lbl (bb_succs bb2) /\
      ~MEM lbl (fn_labels func0) ==>
      bb1.bb_label = bb2.bb_label) /\
    (!bb. MEM bb func.fn_blocks ==>
      ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    (!L. MEM L (fn_labels func0) ==> TAKE 6 L <> "split_") /\
    (!L. MEM L (fn_labels func0) ==> !a b. L <> STRCAT a (STRCAT "_fwd" b)) /\
    (!L. MEM L (fn_labels func0) ==> !x. L <> STRCAT x "_split") ==>
    cfg_norm_inv func0 func
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[cfg_norm_inv_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* ================================================================
   Section 8b: insert_split_preserves_inv
   ================================================================ *)

(* --- PHI helpers for update_phi_ops --- *)

(* After update_phi_ops, resolve_phi with old_label returns NONE *)
Theorem resolve_phi_update_phi_ops_old:
  !old_label new_label var_repls ops.
    old_label <> new_label ==>
    resolve_phi old_label (update_phi_ops old_label new_label var_repls ops) = NONE
Proof
  recInduct cfgNormDefsTheory.update_phi_ops_ind >>
  rw[update_phi_ops_def, resolve_phi_def, LET_THM]
QED

(* MAP FST of phi_pairs after update_phi_ops substitutes old -> new *)
Theorem phi_pairs_fst_update_phi_ops[local]:
  !old_label new_label var_repls ops.
    MAP FST (phi_pairs (update_phi_ops old_label new_label var_repls ops)) =
    MAP (\l. if l = old_label then new_label else l)
        (MAP FST (phi_pairs ops))
Proof
  recInduct cfgNormDefsTheory.update_phi_ops_ind >>
  rw[update_phi_ops_def, venomInstTheory.phi_pairs_def, LET_THM] >>
  TRY (Cases_on `val_op` >>
       simp[venomInstTheory.phi_pairs_def] >>
       BasicProvers.every_case_tac >>
       simp[venomInstTheory.phi_pairs_def] >> NO_TAC) >>
  Cases_on `y` >> simp[venomInstTheory.phi_pairs_def]
QED

(* --- Helper: if all FILTER elements have the same f-value,
   and f-values are ALL_DISTINCT, then FILTER has length <= 1 --- *)
Theorem filter_all_same_label_le1[local]:
  !P (l:'a list) (f:'a -> 'b).
    ALL_DISTINCT (MAP f l) /\
    (!a b. MEM a l /\ MEM b l /\ P a /\ P b ==> f a = f b) ==>
    LENGTH (FILTER P l) <= 1
Proof
  ntac 2 gen_tac >> Induct_on `l` >>
  rw[listTheory.FILTER]
  >- ((* P h: show FILTER P l = [] *)
      `FILTER P l = []` suffices_by (strip_tac >> simp[]) >>
      rw[listTheory.FILTER_EQ_NIL, listTheory.EVERY_MEM] >>
      CCONTR_TAC >> fs[] >>
      `f x = f h` by metis_tac[] >>
      metis_tac[listTheory.MEM_MAP])
  >- ((* ~P h: IH applies directly *)
      first_x_assum irule >> simp[] >> metis_tac[])
QED

(* pred is original: non-original blocks have num_succs <= 1 *)
Theorem pred_original:
  !func0 func pred_bb.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    num_succs pred_bb > 1 ==>
    MEM pred_bb.bb_label (fn_labels func0)
Proof
  rpt strip_tac >> CCONTR_TAC >>
  imp_res_tac cfg_norm_inv_nonoriginal_1succ >> fs[]
QED

(* block_preds bounded when all same-label preds and labels distinct *)
Theorem block_preds_le1[local]:
  !l lbl.
    ALL_DISTINCT (MAP (\b. b.bb_label) l) /\
    (!bb1 bb2. MEM bb1 l /\ MEM bb2 l /\
               MEM lbl (bb_succs bb1) /\ MEM lbl (bb_succs bb2) ==>
               bb1.bb_label = bb2.bb_label) ==>
    LENGTH (FILTER (\b. MEM lbl (bb_succs b)) l) <= 1
Proof
  rpt strip_tac >>
  mp_tac (ISPECL [``\b:basic_block. MEM lbl (bb_succs b)``,
                  ``l:basic_block list``,
                  ``\b:basic_block. b.bb_label``] filter_all_same_label_le1) >>
  simp[]
QED

(* target is original: non-original labels have unique predecessor *)
Theorem target_original:
  !func0 func target_bb.
    cfg_norm_inv func0 func /\
    MEM target_bb func.fn_blocks /\
    LENGTH (block_preds func target_bb.bb_label) > 1 ==>
    MEM target_bb.bb_label (fn_labels func0)
Proof
  rpt strip_tac >> CCONTR_TAC >>
  `LENGTH (block_preds func target_bb.bb_label) <= 1` suffices_by fs[] >>
  rewrite_tac[block_preds_def] >>
  irule block_preds_le1 >> conj_tac
  >- (rpt strip_tac >>
      irule cfg_norm_inv_nonoriginal_1pred >>
      qexistsl_tac [`func`, `func0`, `target_bb.bb_label`] >> simp[])
  >- (imp_res_tac cfg_norm_inv_labels_distinct >> fs[fn_labels_def])
QED

(* Composing two replace_blocks preserves HD label *)
Theorem hd_label_two_replace_blocks[local]:
  !l1 b1 l2 b2 bbs.
    bbs <> [] /\ b1.bb_label = l1 /\ b2.bb_label = l2 ==>
    (HD (replace_block l2 b2 (replace_block l1 b1 bbs))).bb_label =
    (HD bbs).bb_label
Proof
  Cases_on `bbs` >>
  rw[cfgTransformTheory.replace_block_def] >>
  BasicProvers.every_case_tac >> fs[]
QED

(* insert_split preserves fn_entry_label *)
Theorem fn_entry_label_insert_split:
  !func pred_bb target_bb id_base.
    func.fn_blocks <> [] ==>
    fn_entry_label (insert_split func pred_bb target_bb id_base) =
    fn_entry_label func
Proof
  rw[cfgNormDefsTheory.insert_split_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  simp[venomInstTheory.fn_entry_label_def,
       venomInstTheory.entry_block_def] >>
  `replace_block target_bb.bb_label
     (update_phis_for_split pred_bb.bb_label split_bb.bb_label var_repls
        target_bb)
     (replace_block pred_bb.bb_label
        (subst_label_terminator target_bb.bb_label split_bb.bb_label pred_bb)
        func.fn_blocks) <> []` by
    simp[cfgTransformTheory.replace_block_def] >>
  simp[rich_listTheory.HD_APPEND_NOT_NIL] >>
  fs[listTheory.NULL_EQ] >>
  irule hd_label_two_replace_blocks >>
  simp[cfgNormSimTheory.subst_label_terminator_bb_label,
       cfgNormSimTheory.update_phis_for_split_bb_label]
QED

Theorem mem_block_mem_fn_labels:
  !bb func. MEM bb func.fn_blocks ==>
    MEM bb.bb_label (fn_labels func)
Proof
  rw[fn_labels_def, listTheory.MEM_MAP] >> metis_tac[]
QED

(* C14: non-original blocks have <=1 successor after insert_split *)
Theorem insert_split_nonoriginal_1succ[local]:
  !func func0 pred_bb target_bb id_base bb.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    MEM pred_bb.bb_label (fn_labels func0) /\
    MEM target_bb.bb_label (fn_labels func0) /\
    (!bb. MEM bb func.fn_blocks /\ ~MEM bb.bb_label (fn_labels func0) ==>
          num_succs bb <= 1) /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks /\
    ~MEM bb.bb_label (fn_labels func0) ==>
    num_succs bb <= 1
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac
  (* Case 1: bb = split_bb *)
  >- (imp_res_tac num_succs_split_bb >> simp[])
  (* Case 2: bb = pred' (subst_label_terminator) — contradiction *)
  >- (fs[cfgNormSimTheory.subst_label_terminator_bb_label])
  (* Case 3: bb = target' (update_phis) — contradiction *)
  >- (fs[cfgNormSimTheory.update_phis_for_split_bb_label])
  (* Case 4: original block *)
  >> first_x_assum irule >> simp[]
QED

(* General per-block lifting lemma for insert_split.
   Factors out the MEM_insert_split 4-way case split once and for all. *)
Theorem insert_split_block_lift[local]:
  !func pred_bb target_bb id_base P.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    (!bb. MEM bb func.fn_blocks /\ bb.bb_label <> pred_bb.bb_label /\
          bb.bb_label <> target_bb.bb_label ==> P bb) /\
    P (subst_label_terminator target_bb.bb_label
         (split_block_name pred_bb.bb_label target_bb.bb_label) pred_bb) /\
    P (update_phis_for_split pred_bb.bb_label
         (split_block_name pred_bb.bb_label target_bb.bb_label)
         (SND (build_split_block pred_bb target_bb id_base)) target_bb) /\
    (let (split_bb, var_repls) = build_split_block pred_bb target_bb id_base
     in P split_bb) ==>
    !bb. MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks ==>
      P bb
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac
  >- fs[]  (* split_bb case *)
  >- fs[cfgNormSimTheory.subst_label_terminator_bb_label]  (* pred case *)
  >- fs[cfgNormSimTheory.update_phis_for_split_bb_label]  (* target case *)
  >> first_x_assum irule >> simp[]  (* original case *)
QED

(* C7: label origin preserved by insert_split *)
Theorem insert_split_label_origin:
  !func func0 pred_bb target_bb id_base lbl.
    (!lbl. MEM lbl (fn_labels func) ==>
      MEM lbl (fn_labels func0) \/
      ?p t. MEM p (fn_labels func0) /\ MEM t (fn_labels func0) /\
            lbl = split_block_name p t) /\
    MEM pred_bb.bb_label (fn_labels func0) /\
    MEM target_bb.bb_label (fn_labels func0) /\
    MEM lbl (fn_labels (insert_split func pred_bb target_bb id_base)) ==>
    MEM lbl (fn_labels func0) \/
    ?p t. MEM p (fn_labels func0) /\ MEM t (fn_labels func0) /\
          lbl = split_block_name p t
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
    cfgNormSimTheory.fn_labels_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac >> fs[listTheory.MEM_APPEND, listTheory.MEM] >>
  DISJ2_TAC >> qexistsl_tac [`pred_bb.bb_label`, `target_bb.bb_label`] >> simp[]
QED

(* Helper: build_forwarding_assigns produces consecutive inst_ids *)
Theorem build_fwd_assigns_inst_ids[local]:
  !split_label id_base vars repls insts.
    build_forwarding_assigns split_label id_base vars = (repls, insts) ==>
    MAP (\i. i.inst_id) insts = GENLIST (\k. id_base + k) (LENGTH vars)
Proof
  Induct_on `vars` >>
  rw[cfgNormDefsTheory.build_forwarding_assigns_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  first_x_assum (drule_then strip_assume_tac) >>
  simp[listTheory.GENLIST_CONS, combinTheory.o_DEF] >>
  AP_THM_TAC >> AP_TERM_TAC >> simp[FUN_EQ_THM]
QED

(* C16: per-block inst_ids preserved by insert_split *)
Theorem insert_split_block_ids[local]:
  !func pred_bb target_bb id_base bb.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    (!bb. MEM bb func.fn_blocks ==>
       ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)) /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac
  (* split_bb: consecutive ids are distinct *)
  >- (fs[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
      pairarg_tac >> fs[] >> rw[] >>
      imp_res_tac build_fwd_assigns_inst_ids >>
      simp[listTheory.MAP_APPEND, listTheory.MAP,
           listTheory.ALL_DISTINCT_APPEND, listTheory.MEM,
           listTheory.MEM_GENLIST, listTheory.ALL_DISTINCT_GENLIST])
  (* pred: inst_ids preserved by subst_label_terminator *)
  >- (fs[cfgNormSimTheory.subst_label_terminator_bb_label,
         inst_ids_subst_label_terminator])
  (* target: inst_ids preserved by update_phis *)
  >- (fs[cfgNormSimTheory.update_phis_for_split_bb_label,
         inst_ids_update_phis])
  (* original: from IH *)
  >> res_tac
QED

(* C2: fn_inst_wf preserved by insert_split *)
Theorem insert_split_fn_inst_wf:
  !func pred_bb target_bb id_base.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    fn_inst_wf func /\
    wf_function_no_ids func ==>
    fn_inst_wf (insert_split func pred_bb target_bb id_base)
Proof
  rpt strip_tac >>
  `EVERY inst_wf pred_bb.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     fs[fn_inst_wf_def] >> res_tac >> res_tac) >>
  `EVERY inst_wf target_bb.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
     fs[fn_inst_wf_def] >> res_tac >> res_tac) >>
  simp[fn_inst_wf_def] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac
  >- (fs[] >> imp_res_tac inst_wf_split_bb)
  >- (fs[cfgNormSimTheory.subst_label_terminator_bb_label] >>
      imp_res_tac inst_wf_subst_label_terminator)
  >- (fs[cfgNormSimTheory.update_phis_for_split_bb_label] >>
      `bb_well_formed target_bb` by fs[wf_function_no_ids_def] >>
      imp_res_tac inst_wf_update_phis)
  >> fs[fn_inst_wf_def] >> res_tac >> res_tac
QED

(* C12: no self-loops preserved by insert_split *)
Theorem no_self_loop_subst_label_terminator[local]:
  !old_lbl new_lbl bb.
    bb_well_formed bb /\
    ~MEM bb.bb_label (bb_succs bb) /\
    bb.bb_label <> new_lbl ==>
    ~MEM (subst_label_terminator old_lbl new_lbl bb).bb_label
         (bb_succs (subst_label_terminator old_lbl new_lbl bb))
Proof
  rpt strip_tac >>
  fs[cfgNormSimTheory.subst_label_terminator_bb_label] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  imp_res_tac bb_succs_nonempty >>
  fs[bb_succs_subst_label_terminator] >>
  BasicProvers.every_case_tac >> fs[] >>
  fs[listTheory.MEM_nub, listTheory.MEM_REVERSE, listTheory.MEM_MAP] >>
  Cases_on `l = old_lbl` >> fs[]
QED

Theorem insert_split_no_self_loop[local]:
  !func pred_bb target_bb id_base bb.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    wf_function_no_ids func /\
    (!bb. MEM bb func.fn_blocks ==>
       !lbl. MEM lbl (bb_succs bb) ==> lbl <> bb.bb_label) /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks ==>
    !lbl. MEM lbl (bb_succs bb) ==> lbl <> bb.bb_label
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac >> fs[]
  (* split_bb: label = split_lbl, succ = [target], freshness gives neq *)
  >- (imp_res_tac bb_succs_split_bb >>
      fs[listTheory.MEM] >>
      imp_res_tac mem_block_mem_fn_labels >>
      imp_res_tac MEM_not_MEM_neq >> fs[])
  (* pred: use no_self_loop_subst_label_terminator *)
  >- (mp_tac (Q.SPECL [`target_bb.bb_label`,
                        `split_block_name pred_bb.bb_label target_bb.bb_label`,
                        `pred_bb`] no_self_loop_subst_label_terminator) >>
      simp[] >>
      imp_res_tac mem_block_mem_fn_labels >>
      imp_res_tac MEM_not_MEM_neq >>
      fs[wf_function_no_ids_def] >> res_tac)
  (* target: succs unchanged by update_phis *)
  >- (fs[cfgNormSimTheory.update_phis_for_split_bb_label] >>
      `bb_well_formed target_bb` by fs[wf_function_no_ids_def] >>
      imp_res_tac bb_succs_update_phis >> fs[] >> res_tac)
QED

(* phi_pairs label implies resolve_phi succeeds *)
Theorem phi_pairs_resolve_phi_some[local]:
  !ops l v.
    phi_well_formed ops /\ MEM (l, v) (phi_pairs ops) ==>
    resolve_phi l ops <> NONE
Proof
  recInduct venomWfTheory.phi_well_formed_ind >>
  rw[venomWfTheory.phi_well_formed_def, venomInstTheory.phi_pairs_def,
     venomExecSemanticsTheory.resolve_phi_def] >> fs[]
  >- (res_tac >> fs[]) >>
  Cases_on `v3` >>
  fs[venomInstTheory.phi_pairs_def, venomExecSemanticsTheory.resolve_phi_def] >>
  res_tac
QED

(* General: injective conditional substitution preserves ALL_DISTINCT *)
Theorem ALL_DISTINCT_MAP_subst[local]:
  !old new ls.
    ALL_DISTINCT ls /\ ~MEM new ls ==>
    ALL_DISTINCT (MAP (\l. if l = old then new else l) ls)
Proof
  Induct_on `ls` >> rw[] >> fs[listTheory.MEM_MAP] >>
  rpt strip_tac >> BasicProvers.every_case_tac >> fs[]
QED

(* split_bb contains no PHI instructions *)
Theorem split_bb_no_phi:
  !pred_bb target_bb id_base split_bb var_repls inst.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    MEM inst split_bb.bb_instructions ==>
    inst.inst_opcode <> PHI
Proof
  rpt strip_tac >>
  fs[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> fs[] >> rw[] >>
  fs[listTheory.MEM_APPEND, listTheory.MEM]
  >- (imp_res_tac cfgNormSimTheory.build_forwarding_assigns_insts >>
      `?n. n < LENGTH fwd_insts /\ inst = EL n fwd_insts` by
        metis_tac[listTheory.MEM_EL] >>
      `n < LENGTH (nub (phi_vars_needing_forward pred_bb.bb_label
          pred_bb target_bb.bb_instructions))` by fs[] >>
      res_tac >> fs[])
  >- (rw[] >> fs[GSYM venomInstTheory.opcode2num_11,
                   venomInstTheory.opcode2num_thm])
QED

(* fn_labels monotonicity: old labels survive insert_split *)
Theorem fn_labels_mono_insert_split[local]:
  !func pred_bb target_bb id_base x.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    MEM x (fn_labels func) ==>
    MEM x (fn_labels (insert_split func pred_bb target_bb id_base))
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
    cfgNormSimTheory.fn_labels_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[listTheory.MEM_APPEND]
QED

(* C1: insert_split preserves wf_function_no_ids *)
Theorem insert_split_wf_no_ids:
  !func pred_bb target_bb id_base.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    wf_function_no_ids func /\
    fn_succs_closed func ==>
    wf_function_no_ids (insert_split func pred_bb target_bb id_base)
Proof
  rpt strip_tac >>
  fs[wf_function_no_ids_def] >>
  rpt conj_tac
  (* ALL_DISTINCT fn_labels *)
  >- (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
        cfgNormSimTheory.fn_labels_insert_split) >>
      simp[LET_THM] >> pairarg_tac >> fs[] >>
      imp_res_tac cfgNormSimTheory.build_split_block_label >>
      rw[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM] >> rw[])
  (* fn_has_entry *)
  >- (`func.fn_blocks <> []` by fs[venomWfTheory.fn_has_entry_def] >>
      imp_res_tac fn_entry_label_insert_split >>
      `(insert_split func pred_bb target_bb id_base).fn_blocks <> []` by (
        simp[insert_split_def, LET_THM] >> pairarg_tac >> simp[]) >>
      fs[venomWfTheory.fn_has_entry_def] >>
      Cases_on `(insert_split func pred_bb target_bb id_base).fn_blocks` >>
      fs[])
  (* bb_well_formed *)
  >- (rpt strip_tac >>
      mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
        MEM_insert_split) >>
      simp[LET_THM] >> pairarg_tac >> fs[] >>
      imp_res_tac cfgNormSimTheory.build_split_block_label >>
      strip_tac >> fs[]
      >- (imp_res_tac bb_well_formed_split_bb >> fs[])
      >- (irule bb_well_formed_subst_label_terminator >> res_tac)
      >- (`bb_well_formed target_bb` by res_tac >>
          imp_res_tac bb_well_formed_update_phis >> fs[])
      )
  (* fn_succs_closed: for each block case, show succ ∈ fn_labels func' *)
  >- (rw[venomWfTheory.fn_succs_closed_def] >>
      mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
        MEM_insert_split) >>
      simp[LET_THM] >> pairarg_tac >> fs[] >>
      imp_res_tac cfgNormSimTheory.build_split_block_label >>
      strip_tac >> fs[]
      (* split_bb: succ = [target.bb_label] in fn_labels func' *)
      >- (imp_res_tac bb_succs_split_bb >> fs[listTheory.MEM] >>
          imp_res_tac mem_block_mem_fn_labels >>
          irule fn_labels_mono_insert_split >> simp[])
      (* pred: succs via subst_label_terminator *)
      >- (`pred_bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
          fs[bb_succs_subst_label_terminator] >>
          BasicProvers.every_case_tac >> fs[]
          >- (fs[listTheory.MEM_nub, listTheory.MEM_REVERSE, listTheory.MEM_MAP] >>
              Cases_on `l = target_bb.bb_label` >> fs[]
              >- (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
                    cfgNormSimTheory.fn_labels_insert_split) >>
                  simp[LET_THM] >> pairarg_tac >> fs[] >>
                  rw[listTheory.MEM_APPEND, listTheory.MEM])
              >- (`MEM l (bb_succs pred_bb)` by (
                    imp_res_tac bb_succs_nonempty >>
                    fs[listTheory.MEM_nub, listTheory.MEM_REVERSE]) >>
                  `MEM l (fn_labels func)` by
                    (fs[venomWfTheory.fn_succs_closed_def] >> res_tac) >>
                  irule fn_labels_mono_insert_split >> simp[]))
          >- (`MEM succ (fn_labels func)` by
                (fs[venomWfTheory.fn_succs_closed_def] >> res_tac) >>
              irule fn_labels_mono_insert_split >> simp[]))
      (* target: succs unchanged *)
      >- (`bb_well_formed target_bb` by res_tac >>
          imp_res_tac bb_succs_update_phis >> fs[] >>
          `MEM succ (fn_labels func)` by
            (fs[venomWfTheory.fn_succs_closed_def] >> res_tac) >>
          irule fn_labels_mono_insert_split >> simp[])
      (* original: succs unchanged *)
      >- (`MEM succ (fn_labels func)` by
            (fs[venomWfTheory.fn_succs_closed_def] >> res_tac) >>
          irule fn_labels_mono_insert_split >> simp[])
  )
QED

(* PHI in subst_label_terminator output => same PHI in original *)
Theorem pred_phi_mem_original:
  !old new bb inst.
    MEM inst (subst_label_terminator old new bb).bb_instructions /\
    inst.inst_opcode = PHI ==>
    MEM inst bb.bb_instructions
Proof
  rpt strip_tac >>
  fs[cfgTransformTheory.subst_label_terminator_def, listTheory.MEM_MAP] >>
  Cases_on `is_terminator inst'.inst_opcode` >> fs[] >>
  `(subst_label_inst old new inst').inst_opcode = inst'.inst_opcode` by
    simp[cfgTransformTheory.subst_label_inst_def] >>
  `inst'.inst_opcode = PHI` by metis_tac[] >>
  fs[venomInstTheory.is_terminator_def]
QED

(* PHI in update_phis_for_split output => related PHI in original *)
Theorem target_phi_operands:
  !old new repls bb inst.
    MEM inst (update_phis_for_split old new repls bb).bb_instructions /\
    inst.inst_opcode = PHI ==>
    ?inst0. MEM inst0 bb.bb_instructions /\ inst0.inst_opcode = PHI /\
            inst.inst_operands = update_phi_ops old new repls inst0.inst_operands /\
            inst.inst_outputs = inst0.inst_outputs /\
            inst.inst_id = inst0.inst_id
Proof
  rpt strip_tac >>
  fs[cfgNormDefsTheory.update_phis_for_split_def, listTheory.MEM_MAP] >>
  Cases_on `inst'.inst_opcode = PHI` >> fs[]
  (* PHI case: inst = inst' with operands updated *)
  >- (qexists_tac `inst'` >> simp[])
  (* non-PHI case: inst = inst' but inst.opcode = PHI, inst'.opcode <> PHI — contradiction *)
  >- (qpat_x_assum `inst = _` SUBST_ALL_TAC >> fs[])
QED

(* Stronger version: PHI in update_phis_for_split output with wf context *)
(* Gives original inst0, inst_wf, phi_well_formed, ALL_DISTINCT phi_pairs *)
Theorem target_phi_wf[local]:
  !func bb old new repls inst.
    MEM bb func.fn_blocks /\
    fn_inst_wf func /\
    fn_phi_labels_distinct func /\
    MEM inst (update_phis_for_split old new repls bb).bb_instructions /\
    inst.inst_opcode = PHI ==>
    ?inst0. MEM inst0 bb.bb_instructions /\ inst0.inst_opcode = PHI /\
            inst.inst_operands = update_phi_ops old new repls inst0.inst_operands /\
            inst.inst_outputs = inst0.inst_outputs /\
            inst.inst_id = inst0.inst_id /\
            inst_wf inst0 /\
            phi_well_formed inst0.inst_operands /\
            ALL_DISTINCT (MAP FST (phi_pairs inst0.inst_operands))
Proof
  rpt strip_tac >>
  (* Use def-expansion directly instead of imp_res_tac to avoid double witnesses *)
  fs[cfgNormDefsTheory.update_phis_for_split_def, listTheory.MEM_MAP] >>
  Cases_on `inst'.inst_opcode = PHI` >> fs[]
  >- (
    qexists_tac `inst'` >> simp[] >>
    `inst_wf inst'` by (
      fs[venomWfTheory.fn_inst_wf_def] >> res_tac >> res_tac) >>
    `phi_well_formed inst'.inst_operands` by (
      imp_res_tac inst_wf_phi_well_formed >> fs[]) >>
    `ALL_DISTINCT (MAP FST (phi_pairs inst'.inst_operands))` by (
      fs[cfgNormBaseTheory.fn_phi_labels_distinct_def] >> res_tac) >>
    simp[])
  >- (qpat_x_assum `inst = _` SUBST_ALL_TAC >> fs[])
QED

(* Key lemma: phi pair labels are in fn_labels (derived from preds_closed) *)
Theorem phi_pair_labels_in_fn_labels[local]:
  !func bb inst0 l.
    MEM bb func.fn_blocks /\
    MEM inst0 bb.bb_instructions /\
    inst0.inst_opcode = PHI /\
    fn_phi_preds_closed func /\
    phi_well_formed inst0.inst_operands /\
    MEM l (MAP FST (phi_pairs inst0.inst_operands)) ==>
    MEM l (fn_labels func)
Proof
  rpt strip_tac >>
  fs[listTheory.MEM_MAP] >>
  Cases_on `y` >>
  `resolve_phi l inst0.inst_operands <> NONE` by (
    irule phi_pairs_resolve_phi_some >> simp[] >>
    qexists_tac `r` >> simp[]) >>
  fs[cfgNormBaseTheory.fn_phi_preds_closed_def] >>
  rw[] >> res_tac
QED

(* update_phi_ops preserves ALL_DISTINCT of phi pair labels *)
Theorem update_phi_ops_preserves_distinct[local]:
  !old new repls inst0 func bb.
    MEM bb func.fn_blocks /\
    MEM inst0 bb.bb_instructions /\
    inst0.inst_opcode = PHI /\
    fn_phi_preds_closed func /\
    phi_well_formed inst0.inst_operands /\
    ALL_DISTINCT (MAP FST (phi_pairs inst0.inst_operands)) /\
    ~MEM new (fn_labels func) ==>
    ALL_DISTINCT (MAP FST (phi_pairs
      (update_phi_ops old new repls inst0.inst_operands)))
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[phi_pairs_fst_update_phi_ops] >>
  irule ALL_DISTINCT_MAP_subst >> simp[] >>
  CCONTR_TAC >> fs[] >>
  imp_res_tac phi_pair_labels_in_fn_labels
QED

(* Helper: target block phi_labels_distinct after update_phis_for_split *)
Theorem phi_labels_distinct_target[local]:
  !func old new repls bb inst.
    MEM bb func.fn_blocks /\
    fn_inst_wf func /\
    fn_phi_labels_distinct func /\
    fn_phi_preds_closed func /\
    ~MEM new (fn_labels func) /\
    MEM inst (update_phis_for_split old new repls bb).bb_instructions /\
    inst.inst_opcode = PHI ==>
    ALL_DISTINCT (MAP FST (phi_pairs inst.inst_operands))
Proof
  rpt strip_tac >>
  (* get original inst0 via def-expansion *)
  fs[cfgNormDefsTheory.update_phis_for_split_def, listTheory.MEM_MAP] >>
  reverse (Cases_on `inst'.inst_opcode = PHI`) >> fs[]
  >- (qpat_x_assum `inst = _` SUBST_ALL_TAC >> fs[]) >>
  (* PHI case: inst = inst' with operands := update_phi_ops ... inst'.operands *)
  (* derive inst_wf, phi_well_formed, ALL_DISTINCT for original inst' *)
  `inst_wf inst'` by (
    fs[venomWfTheory.fn_inst_wf_def] >> res_tac >> res_tac) >>
  `phi_well_formed inst'.inst_operands` by (
    imp_res_tac inst_wf_phi_well_formed >> fs[]) >>
  `ALL_DISTINCT (MAP FST (phi_pairs inst'.inst_operands))` by (
    fs[cfgNormBaseTheory.fn_phi_labels_distinct_def] >> res_tac) >>
  (* apply update_phi_ops_preserves_distinct *)
  irule update_phi_ops_preserves_distinct >>
  rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bb`, `func`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* C5: insert_split preserves fn_phi_labels_distinct *)
Theorem insert_split_phi_labels_distinct:
  !func pred_bb target_bb id_base.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    fn_phi_labels_distinct func /\
    fn_phi_preds_closed func /\
    fn_inst_wf func ==>
    fn_phi_labels_distinct (insert_split func pred_bb target_bb id_base)
Proof
  rpt strip_tac >>
  rw[cfgNormBaseTheory.fn_phi_labels_distinct_def] >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac >> fs[cfgNormSimTheory.subst_label_terminator_bb_label,
                  cfgNormSimTheory.update_phis_for_split_bb_label]
  (* split_bb: no PHI instructions *)
  >- (imp_res_tac split_bb_no_phi >> fs[])
  (* pred: subst_label_terminator preserves PHIs — use def-expansion *)
  >- (fs[cfgNormBaseTheory.fn_phi_labels_distinct_def] >>
      imp_res_tac pred_phi_mem_original >> res_tac)
  (* target: use phi_labels_distinct_target *)
  >- (mp_tac (Q.SPECL [`func`,
        `pred_bb.bb_label`,
        `split_block_name pred_bb.bb_label target_bb.bb_label`,
        `var_repls`, `target_bb`, `inst`]
        phi_labels_distinct_target) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[])
  (* original: unchanged *)
  >- (fs[cfgNormBaseTheory.fn_phi_labels_distinct_def] >> res_tac)
QED

(* --- Helper: split_lbl only reachable from pred' --- *)
(* If MEM split_lbl (bb_succs bb) for bb in func', then bb = pred' *)
Theorem split_lbl_only_from_pred[local]:
  !func pred_bb target_bb id_base bb.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    wf_function_no_ids func /\
    fn_succs_closed func /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks /\
    MEM (split_block_name pred_bb.bb_label target_bb.bb_label) (bb_succs bb) ==>
    bb.bb_label = pred_bb.bb_label
Proof
  rpt strip_tac >>
  qabbrev_tac `split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label` >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac >> fs[]
  (* split_bb: succs = [target_bb.bb_label], split_lbl <> target_bb.bb_label *)
  >- (imp_res_tac bb_succs_split_bb >> gvs[listTheory.MEM] >>
      imp_res_tac mem_block_mem_fn_labels >> metis_tac[])
  (* pred': has split_lbl as succ -- label matches *)
  >- simp[cfgNormSimTheory.subst_label_terminator_bb_label]
  (* target': succs unchanged from target_bb, split_lbl not in fn_labels func *)
  >- (`bb_well_formed target_bb` by (fs[wf_function_no_ids_def] >> res_tac) >>
      imp_res_tac bb_succs_update_phis >>
      `MEM split_lbl (bb_succs target_bb)` by metis_tac[] >>
      `MEM split_lbl (fn_labels func)` by
        (fs[venomWfTheory.fn_succs_closed_def] >> res_tac) >>
      metis_tac[])
  (* original: succs unchanged, split_lbl not in fn_labels func *)
  >- (`MEM split_lbl (fn_labels func)` by
        (fs[venomWfTheory.fn_succs_closed_def] >> res_tac) >>
      metis_tac[])
QED

(* For non-split_lbl successors, trace back to original block *)
Theorem succ_traceback[local]:
  !func0 func pred_bb target_bb id_base bb lbl.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    MEM pred_bb.bb_label (fn_labels func0) /\
    MEM target_bb.bb_label (fn_labels func0) /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    wf_function_no_ids func /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks /\
    MEM lbl (bb_succs bb) /\
    lbl <> split_block_name pred_bb.bb_label target_bb.bb_label /\
    ~MEM lbl (fn_labels func0) ==>
    ?bb_orig. MEM bb_orig func.fn_blocks /\
              bb_orig.bb_label = bb.bb_label /\
              MEM lbl (bb_succs bb_orig)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> fs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac >> fs[]
  (* split_bb: succs = [target_bb.bb_label] which is original -- contradiction *)
  >- (imp_res_tac bb_succs_split_bb >> gvs[listTheory.MEM])
  (* pred': non-split_lbl successor traces back to original *)
  >- (qexists_tac `pred_bb` >>
      conj_tac >- simp[] >>
      conj_tac >- simp[cfgNormSimTheory.subst_label_terminator_bb_label] >>
      fs[wf_function_no_ids_def] >> res_tac >>
      metis_tac[MEM_bb_succs_subst_back])
  (* target': succs unchanged *)
  >- (qexists_tac `target_bb` >>
      sg `bb_well_formed target_bb`
      >- (fs[wf_function_no_ids_def] >> res_tac) >>
      imp_res_tac bb_succs_update_phis >>
      fs[cfgNormSimTheory.update_phis_for_split_bb_label])
  (* original *)
  >- (qexists_tac `bb` >> simp[])
QED

(* --- C15: non-original labels have unique predecessor --- *)
Theorem insert_split_unique_pred_inv:
  !func0 func pred_bb target_bb id_base lbl bb1 bb2.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    MEM target_bb.bb_label (bb_succs pred_bb) /\
    MEM pred_bb.bb_label (fn_labels func0) /\
    MEM target_bb.bb_label (fn_labels func0) /\
    MEM bb1 (insert_split func pred_bb target_bb id_base).fn_blocks /\
    MEM bb2 (insert_split func pred_bb target_bb id_base).fn_blocks /\
    MEM lbl (bb_succs bb1) /\
    MEM lbl (bb_succs bb2) /\
    ~MEM lbl (fn_labels func0) ==>
    bb1.bb_label = bb2.bb_label
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels func)` by imp_res_tac cfg_norm_inv_labels_distinct >>
  `wf_function_no_ids func` by imp_res_tac cfg_norm_inv_wf >>
  `fn_succs_closed func` by fs[wf_function_no_ids_def] >>
  `~MEM (split_block_name pred_bb.bb_label target_bb.bb_label) (fn_labels func)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`,
      `target_bb.bb_label`] cfg_norm_inv_edge_fresh) >> simp[]) >>
  (* Case: is lbl = split_block_name? *)
  Cases_on `lbl = split_block_name pred_bb.bb_label target_bb.bb_label`
  >- (
    (* lbl = split_lbl: only pred' has split_lbl as successor *)
    `bb1.bb_label = pred_bb.bb_label` by (
      mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `bb1`]
        split_lbl_only_from_pred) >> fs[]) >>
    `bb2.bb_label = pred_bb.bb_label` by (
      mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `bb2`]
        split_lbl_only_from_pred) >> fs[]) >>
    simp[]
  )
  >- (
    (* lbl <> split_lbl: old non-original label *)
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`, `bb1`, `lbl`] succ_traceback) >>
    simp[] >> strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `target_bb`,
      `id_base`, `bb2`, `lbl`] succ_traceback) >>
    simp[] >> strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `lbl`, `bb_orig`, `bb_orig'`]
      cfg_norm_inv_nonoriginal_1pred) >> simp[]
  )
QED


Theorem insert_split_nonoriginal_1succ_inv:
  !func0 func pred_bb target_bb id_base bb.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    MEM pred_bb.bb_label (fn_labels func0) /\
    MEM target_bb.bb_label (fn_labels func0) /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks /\
    ~MEM bb.bb_label (fn_labels func0) ==>
    num_succs bb <= 1
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels func)` by (imp_res_tac cfg_norm_inv_labels_distinct) >>
  mp_tac (Q.SPECL [`func`, `func0`, `pred_bb`, `target_bb`, `id_base`, `bb`]
    insert_split_nonoriginal_1succ) >>
  impl_tac >- (
    simp[] >> rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `bb'`] cfg_norm_inv_nonoriginal_1succ) >>
    simp[]
  ) >> simp[]
QED

Theorem insert_split_no_self_loop_inv:
  !func0 func pred_bb target_bb id_base bb.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks ==>
    !lbl. MEM lbl (bb_succs bb) ==> lbl <> bb.bb_label
Proof
  rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `bb`]
    insert_split_no_self_loop) >>
  imp_res_tac cfg_norm_inv_wf >> simp[] >>
  rpt gen_tac >> strip_tac >> CCONTR_TAC >> fs[] >>
  mp_tac (Q.SPECL [`func0`, `func`, `bb'`, `bb'.bb_label`]
    cfg_norm_inv_no_self_loop) >> simp[]
QED

Theorem insert_split_block_ids_inv:
  !func0 func pred_bb target_bb id_base bb.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `bb`]
    insert_split_block_ids) >>
  impl_tac >- (
    simp[] >> rpt strip_tac >>
    mp_tac (Q.SPECL [`func0`, `func`, `bb'`] cfg_norm_inv_block_ids) >>
    simp[]
  ) >> simp[]
QED

(* C3 helper: phi_preds_closed for target' block *)
Theorem phi_preds_closed_target[local]:
  !func pred_bb target_bb id_base split_bb var_repls inst l.
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    fn_phi_preds_closed func /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) /\
    MEM inst (update_phis_for_split pred_bb.bb_label split_bb.bb_label
                var_repls target_bb).bb_instructions /\
    inst.inst_opcode = PHI /\
    resolve_phi l inst.inst_operands <> NONE ==>
    MEM l (fn_labels (insert_split func pred_bb target_bb id_base))
Proof
  rpt strip_tac >>
  drule target_phi_operands >> disch_then drule >> strip_tac >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  (* 3-way case analysis: l = pred_bb.bb_label | l = split_bb.bb_label | other *)
  Cases_on `l = pred_bb.bb_label`
  >- (
    (* Case 1: l = pred_bb.bb_label -- contradiction via resolve_phi = NONE *)
    qpat_x_assum `resolve_phi l _ <> _` mp_tac >>
    qpat_x_assum `l = _` SUBST_ALL_TAC >>
    qpat_x_assum `inst.inst_operands = _` SUBST_ALL_TAC >>
    simp[resolve_phi_update_phi_ops_old, cfgNormDefsTheory.split_block_name_def])
  >>
  Cases_on `l = split_bb.bb_label`
  >- (
    (* Case 2: l = split_bb.bb_label -- new label, in fn_labels func' *)
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
      cfgNormSimTheory.fn_labels_insert_split) >>
    simp[LET_THM] >> strip_tac >>
    fs[listTheory.MEM_APPEND, listTheory.MEM])
  >>
  (* Case 3: l is some other label -- unchanged by update_phi_ops *)
  qpat_x_assum `resolve_phi l _ <> _` mp_tac >>
  qpat_x_assum `inst.inst_operands = _` SUBST_ALL_TAC >>
  simp[cfgNormSimTheory.resolve_phi_update_phi_ops_other] >>
  strip_tac >>
  SUBGOAL_THEN ``MEM l (fn_labels func)`` ASSUME_TAC
  >- (
    qpat_x_assum `fn_phi_preds_closed _`
      (mp_tac o REWRITE_RULE [cfgNormBaseTheory.fn_phi_preds_closed_def]) >>
    disch_then (qspecl_then [`target_bb`, `inst0`, `l`] mp_tac) >>
    simp[])
  >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `l`]
    fn_labels_mono_insert_split) >> simp[]
QED

(* C3: insert_split preserves fn_phi_preds_closed *)
Theorem insert_split_phi_preds_closed:
  !func pred_bb target_bb id_base.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    MEM target_bb.bb_label (bb_succs pred_bb) /\
    pred_bb.bb_label <> target_bb.bb_label /\
    ALL_DISTINCT (fn_labels func) /\
    fn_phi_preds_closed func /\
    ~MEM (split_block_name pred_bb.bb_label target_bb.bb_label)
         (fn_labels func) ==>
    fn_phi_preds_closed (insert_split func pred_bb target_bb id_base)
Proof
  rpt strip_tac >>
  simp[cfgNormBaseTheory.fn_phi_preds_closed_def] >>
  rpt strip_tac >>
  (* Get split_bb and split_lbl *)
  `?split_bb var_repls. build_split_block pred_bb target_bb id_base =
     (split_bb, var_repls)` by metis_tac[pairTheory.PAIR] >>
  qabbrev_tac `split_lbl = split_bb.bb_label` >>
  (* 4-way case analysis on bb *)
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> strip_tac
  >- (fs[] >> imp_res_tac split_bb_no_phi >> fs[])
  >- (
    fs[] >> imp_res_tac pred_phi_mem_original >>
    `MEM l (fn_labels func)` by (
      fs[cfgNormBaseTheory.fn_phi_preds_closed_def] >> res_tac) >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `l`]
      fn_labels_mono_insert_split) >> simp[])
  >- (
    fs[] >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
      `split_bb`, `var_repls`, `inst`, `l`] phi_preds_closed_target) >>
    simp[])
  >- (
    `MEM l (fn_labels func)` by (
      fs[cfgNormBaseTheory.fn_phi_preds_closed_def] >> res_tac) >>
    mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`, `l`]
      fn_labels_mono_insert_split) >> simp[])
QED

(* Wrapper: double-split labels cannot be in fn_labels under cfg_norm_inv.
   Uses double_split_contra for the core string argument. *)
(* A is original, B has "_split_" => split_block_name A B not in fn_labels *)
Theorem double_split_not_in_labels[local]:
  !func0 func A B.
    cfg_norm_inv func0 func /\
    MEM A (fn_labels func0) /\
    (?x y. B = STRCAT x (STRCAT "_split_" y)) ==>
    ~MEM (split_block_name A B) (fn_labels func)
Proof
  rw[split_block_name_def] >> strip_tac >>
  qpat_x_assum `cfg_norm_inv _ _`
    (fn th => ASSUME_TAC th >> mp_tac (REWRITE_RULE[cfg_norm_inv_def] th)) >>
  strip_tac >>
  qpat_x_assum `!lbl. MEM lbl (fn_labels func) ==> _`
    (qspec_then `STRCAT A (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y)))` mp_tac) >>
  (impl_tac >- (
    qpat_x_assum `MEM (STRCAT (STRCAT A _) _) _` mp_tac >>
    PURE_REWRITE_TAC[GSYM stringTheory.STRCAT_ASSOC] >>
    simp[])) >>
  strip_tac
  >- (mp_tac (Q.SPECL [`func0`,
        `STRCAT A (STRCAT "_split_" (STRCAT x (STRCAT "_split_" y)))`,
        `A`, `STRCAT x (STRCAT "_split_" y)`]
        original_no_split_substr) >>
      simp[])
  >> qpat_x_assum `_ = split_block_name p t`
       (mp_tac o REWRITE_RULE[split_block_name_def]) >>
  PURE_REWRITE_TAC[GSYM stringTheory.STRCAT_ASSOC] >> strip_tac >>
  mp_tac (Q.SPECL [`A`, `p`, `t`, `x`, `y`] double_split_contra) >>
  impl_tac >- (
    mp_tac (Q.SPECL [`func0`, `func`, `A`, `p`, `t`]
      cfg_norm_inv_double_split_preconds) >>
    disch_then match_mp_tac >> ASM_REWRITE_TAC[]) >>
  metis_tac[]
QED

(* Specialization: A has "_split_" (is a split label), B is original *)
Theorem double_split_not_in_labels_A[local]:
  !func0 func A1 A2 B.
    cfg_norm_inv func0 func /\
    MEM A1 (fn_labels func0) /\
    MEM A2 (fn_labels func0) ==>
    ~MEM (split_block_name (split_block_name A1 A2) B) (fn_labels func)
Proof
  rw[split_block_name_def] >> strip_tac >>
  qpat_x_assum `cfg_norm_inv _ _`
    (fn th => ASSUME_TAC th >> mp_tac (REWRITE_RULE[cfg_norm_inv_def] th)) >>
  strip_tac >>
  (* The MEM assumption is left-associated STRCAT, C7 expects right-associated.
     Use PURE_REWRITE_TAC to normalize. *)
  qpat_x_assum `!lbl. MEM lbl (fn_labels func) ==> _`
    (qspec_then `STRCAT A1 (STRCAT "_split_" (STRCAT A2 (STRCAT "_split_" B)))` mp_tac) >>
  (impl_tac >- (
    qpat_x_assum `MEM (STRCAT _ B) (fn_labels func)` mp_tac >>
    PURE_REWRITE_TAC[GSYM stringTheory.STRCAT_ASSOC] >>
    simp[])) >>
  strip_tac
  >- (mp_tac (Q.SPECL [`func0`,
        `STRCAT A1 (STRCAT "_split_" (STRCAT A2 (STRCAT "_split_" B)))`,
        `A1`, `STRCAT A2 (STRCAT "_split_" B)`]
        original_no_split_substr) >>
      simp[])
  >> qpat_x_assum `_ = split_block_name p t`
       (mp_tac o REWRITE_RULE[split_block_name_def]) >>
  PURE_REWRITE_TAC[GSYM stringTheory.STRCAT_ASSOC] >> strip_tac >>
  mp_tac (Q.SPECL [`A1`, `p`, `t`, `A2`, `B`] double_split_contra) >>
  impl_tac >- (
    mp_tac (Q.SPECL [`func0`, `func`, `A1`, `p`, `t`]
      cfg_norm_inv_double_split_preconds) >>
    disch_then match_mp_tac >> ASM_REWRITE_TAC[]) >>
  metis_tac[]
QED

(* Double-split: also not equal to any single split label *)
Theorem double_split_neq_single[local]:
  !func0 func A1 A2 B.
    cfg_norm_inv func0 func /\
    MEM A1 (fn_labels func0) /\
    MEM A2 (fn_labels func0) ==>
    !p t. MEM p (fn_labels func0) /\ MEM t (fn_labels func0) ==>
    split_block_name (split_block_name A1 A2) B <>
    split_block_name p t
Proof
  rw[split_block_name_def] >>
  PURE_REWRITE_TAC[GSYM stringTheory.STRCAT_ASSOC] >>
  mp_tac (Q.SPECL [`A1`, `p`, `t`, `A2`, `B`] double_split_contra) >>
  impl_tac >- (
    mp_tac (Q.SPECL [`func0`, `func`, `A1`, `p`, `t`]
      cfg_norm_inv_double_split_preconds) >>
    disch_then match_mp_tac >> ASM_REWRITE_TAC[]) >>
  metis_tac[]
QED

(* C10: edge freshness after insert_split *)
Theorem insert_split_edge_fresh_inv:
  !func0 func pred_bb target_bb id_base.
    cfg_norm_inv func0 func /\
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    MEM target_bb.bb_label (bb_succs pred_bb) /\
    num_succs pred_bb > 1 /\
    LENGTH (block_preds func target_bb.bb_label) > 1 ==>
    !bb lbl.
      MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks /\
      MEM lbl (bb_succs bb) ==>
      ~MEM (split_block_name bb.bb_label lbl)
           (fn_labels (insert_split func pred_bb target_bb id_base))
Proof
  rpt strip_tac >>
  (* Derive shared facts *)
  `MEM pred_bb.bb_label (fn_labels func0)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`] pred_original) >> simp[]) >>
  `MEM target_bb.bb_label (fn_labels func0)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `target_bb`] target_original) >> simp[]) >>
  `pred_bb.bb_label <> target_bb.bb_label` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`,
      `target_bb.bb_label`] cfg_norm_inv_no_self_loop) >> simp[]) >>
  `~MEM (split_block_name pred_bb.bb_label target_bb.bb_label) (fn_labels func)` by (
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`,
      `target_bb.bb_label`] cfg_norm_inv_edge_fresh) >> simp[]) >>
  `ALL_DISTINCT (fn_labels func)` by (
    mp_tac (Q.SPECL [`func0`, `func`] cfg_norm_inv_labels_distinct) >> simp[]) >>
  `wf_function_no_ids func` by (
    mp_tac (Q.SPECL [`func0`, `func`] cfg_norm_inv_wf) >> simp[]) >>
  (* fn_labels func' = fn_labels func ++ [split_lbl] *)
  mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`]
    cfgNormSimTheory.fn_labels_insert_split) >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  imp_res_tac cfgNormSimTheory.build_split_block_label >>
  strip_tac >>
  (* Goal is F. MEM (split_block_name bb lbl) in fn_labels func'.
     Rewrite fn_labels to see which part it falls into. *)
  qpat_x_assum `MEM (split_block_name _ _) (fn_labels _)` mp_tac >>
  simp[listTheory.MEM_APPEND, listTheory.MEM] >>
  (* Decompose MEM bb into 4 cases BEFORE stripping the disjunction *)
  qpat_x_assum `MEM bb (insert_split _ _ _ _).fn_blocks` mp_tac >>
  mp_tac (Q.SPECL [`bb`, `func`, `pred_bb`, `target_bb`, `id_base`]
    MEM_insert_split) >>
  simp[LET_THM] >> strip_tac >>
  (* Now goal:
     (bb = split_bb \/ bb = pred' \/ bb = target' \/ (MEM bb func ... /\ ...)) ==>
     (MEM (split_block_name bb lbl) (fn_labels func) \/
      split_block_name bb lbl = split_lbl) ==> F *)
  strip_tac >> gvs[]
  (* Case 1: bb = split_bb *)
  >- (
    mp_tac (Q.SPECL [`pred_bb`, `target_bb`, `id_base`]
      bb_succs_split_bb) >> simp[] >> strip_tac >> gvs[] >>
    conj_tac
    >- (mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`,
          `target_bb.bb_label`, `target_bb.bb_label`]
          double_split_not_in_labels_A) >> simp[])
    >> mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`,
         `target_bb.bb_label`, `target_bb.bb_label`]
         double_split_neq_single) >>
       (impl_tac >- simp[]) >>
       DISCH_THEN (qspecl_then [`pred_bb.bb_label`, `target_bb.bb_label`] mp_tac) >>
       simp[])
  (* Case 2: bb = pred' = subst_label_terminator *)
  >- (
    gvs[cfgNormSimTheory.subst_label_terminator_bb_label] >>
    `bb_well_formed pred_bb` by (
      qpat_x_assum `wf_function_no_ids func` mp_tac >>
      simp[cfgNormBaseTheory.wf_function_no_ids_def,
           venomWfTheory.wf_function_def,
           listTheory.EVERY_MEM] >> metis_tac[]) >>
    Cases_on `lbl = split_block_name pred_bb.bb_label target_bb.bb_label`
    >- (
      (* lbl = split_lbl: double split in second argument *)
      gvs[] >> conj_tac
      >- (mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`,
            `split_block_name pred_bb.bb_label target_bb.bb_label`]
            double_split_not_in_labels) >>
          (impl_tac >- (
            simp[] >>
            qexistsl_tac [`pred_bb.bb_label`, `target_bb.bb_label`] >>
            simp[cfgNormDefsTheory.split_block_name_def])) >>
          simp[])
      >> SPOSE_NOT_THEN ASSUME_TAC >>
      mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`,
        `pred_bb.bb_label`, `target_bb.bb_label`,
        `pred_bb.bb_label`, `target_bb.bb_label`]
        double_split_inner_contra) >> simp[])
    >> (* lbl <> split_lbl *)
    `MEM lbl (bb_succs pred_bb)` by (
      mp_tac (Q.SPECL [`target_bb.bb_label`,
        `split_block_name pred_bb.bb_label target_bb.bb_label`,
        `pred_bb`, `lbl`] MEM_bb_succs_subst_back) >> simp[]) >>
    `MEM lbl (fn_labels func)` by (
      qpat_x_assum `wf_function_no_ids func` mp_tac >>
      simp[cfgNormBaseTheory.wf_function_no_ids_def,
           venomWfTheory.fn_succs_closed_def] >> metis_tac[]) >>
    conj_tac
    >- (mp_tac (Q.SPECL [`func0`, `func`, `pred_bb`, `lbl`]
          cfg_norm_inv_edge_fresh) >> simp[])
    >> SPOSE_NOT_THEN ASSUME_TAC >>
    mp_tac (Q.SPECL [`func0`, `func`, `pred_bb.bb_label`, `lbl`,
      `pred_bb.bb_label`, `target_bb.bb_label`] cfg_norm_inv_inj_gen) >>
    simp[] >> strip_tac >> gvs[] >>
    mp_tac (Q.SPECL [`target_bb.bb_label`,
      `split_block_name pred_bb.bb_label target_bb.bb_label`,
      `pred_bb`] old_not_in_subst_succs) >> simp[])
  (* Case 3: bb = target' = update_phis_for_split *)
  >- (
    gvs[cfgNormSimTheory.update_phis_for_split_bb_label] >>
    `bb_well_formed target_bb` by (
      qpat_x_assum `wf_function_no_ids func` mp_tac >>
      simp[cfgNormBaseTheory.wf_function_no_ids_def,
           venomWfTheory.wf_function_def,
           listTheory.EVERY_MEM] >> metis_tac[]) >>
    `MEM lbl (bb_succs target_bb)` by (
      imp_res_tac bb_succs_update_phis >> gvs[]) >>
    `MEM lbl (fn_labels func)` by (
      qpat_x_assum `wf_function_no_ids func` mp_tac >>
      simp[cfgNormBaseTheory.wf_function_no_ids_def,
           venomWfTheory.fn_succs_closed_def] >> metis_tac[]) >>
    conj_tac
    >- (mp_tac (Q.SPECL [`func0`, `func`, `target_bb`, `lbl`]
          cfg_norm_inv_edge_fresh) >> simp[])
    >> SPOSE_NOT_THEN ASSUME_TAC >>
    mp_tac (Q.SPECL [`func0`, `func`, `target_bb.bb_label`, `lbl`,
      `pred_bb.bb_label`, `target_bb.bb_label`] cfg_norm_inv_inj_gen) >>
    simp[])
  (* Case 4: original bb, bb.bb_label <> pred, <> target *)
  >> (
    `MEM lbl (fn_labels func)` by (
      qpat_x_assum `wf_function_no_ids func` mp_tac >>
      simp[cfgNormBaseTheory.wf_function_no_ids_def,
           venomWfTheory.fn_succs_closed_def] >> metis_tac[]) >>
    conj_tac
    >- (mp_tac (Q.SPECL [`func0`, `func`, `bb`, `lbl`]
          cfg_norm_inv_edge_fresh) >> simp[])
    >> `MEM bb.bb_label (fn_labels func)` by (
         simp[venomInstTheory.fn_labels_def, listTheory.MEM_MAP] >>
         metis_tac[]) >>
    mp_tac (Q.SPECL [`func0`, `func`, `bb.bb_label`]
      cfg_norm_inv_label_origin) >> simp[] >>
    strip_tac
    >- (SPOSE_NOT_THEN ASSUME_TAC >>
        mp_tac (Q.SPECL [`func0`, `func`, `bb.bb_label`, `lbl`,
          `pred_bb.bb_label`, `target_bb.bb_label`] cfg_norm_inv_inj_gen) >>
        simp[])
    >> gvs[] >>
    mp_tac (Q.SPECL [`func0`, `func`, `p`, `t`, `lbl`]
      double_split_neq_single) >>
    (impl_tac >- simp[]) >>
    DISCH_THEN (qspecl_then [`pred_bb.bb_label`,
      `target_bb.bb_label`] mp_tac) >> simp[])
QED

(* Re-prove locally: inst output is in fn_all_vars *)
Theorem inst_output_in_fn_all_vars:
  !func bb inst out.
    MEM bb func.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM out inst.inst_outputs ==>
    MEM out (fn_all_vars func)
Proof
  rpt strip_tac >>
  simp[cfgTransformTheory.fn_all_vars_def, listTheory.MEM_FLAT, listTheory.MEM_MAP,
       listTheory.MEM_APPEND, PULL_EXISTS] >>
  qexistsl_tac [`bb`, `inst`] >> simp[] >>
  DISJ1_TAC >> simp[]
QED

(* If Var v appears in update_phi_ops output, either it was in original ops
   or it came from an ALOOKUP substitution *)
Theorem update_phi_ops_var_source[local]:
  !old new vr ops v.
    MEM (Var v) (update_phi_ops old new vr ops) ==>
    MEM (Var v) ops \/ ?w. ALOOKUP vr w = SOME v
Proof
  recInduct cfgNormDefsTheory.update_phi_ops_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[cfgNormDefsTheory.update_phi_ops_def, listTheory.MEM] >>
  disch_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `l = old_label` >> gvs[listTheory.MEM] >>
  TRY (Cases_on `val_op` >> gvs[listTheory.MEM] >>
       Cases_on `ALOOKUP var_repls s` >> gvs[listTheory.MEM]) >>
  res_tac >> metis_tac[]
QED

(* --- var_source case helpers: one per MEM_insert_split case --- *)

(* Case 1: split_bb - vars come from build_split_block.
   Outputs are fwd vars (DISJ2), operands are phi vars in fn_all_vars (DISJ1). *)
Theorem var_source_split_bb[local]:
  !func pred_bb target_bb id_base split_bb var_repls inst v.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    MEM inst split_bb.bb_instructions /\
    (MEM v inst.inst_outputs \/ MEM (Var v) inst.inst_operands) ==>
    MEM v (fn_all_vars func) \/
    ?w. v = STRCAT (STRCAT (split_block_name pred_bb.bb_label
              target_bb.bb_label) "_fwd_") w
Proof
  rpt gen_tac >> strip_tac >>
  gvs[cfgNormDefsTheory.build_split_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  qpat_x_assum `MEM inst _` mp_tac >>
  simp[listTheory.MEM_APPEND, listTheory.MEM] >> strip_tac >> gvs[] >>
  (* JMP instruction: outputs=[], operands=[Label ...] -> no vars *)
  TRY (gvs[] >> Cases_on `v' = v` >> gvs[] >> NO_TAC) >>
  (* Forwarding assign: use build_forwarding_assigns_insts *)
  imp_res_tac cfgNormSimTheory.build_forwarding_assigns_insts >>
  qpat_x_assum `MEM inst _` mp_tac >>
  simp[listTheory.MEM_EL] >> strip_tac >> gvs[] >>
  qpat_x_assum `!k. k < _ ==> _` (qspec_then `n` mp_tac) >>
  simp[] >> strip_tac >> gvs[] >>
  (* After gvs: outputs case gives v = fwd var (DISJ2),
     operands case gives v = phi var (DISJ1) *)
  TRY (DISJ2_TAC >>
    qexists_tac `EL n (nub (phi_vars_needing_forward
      pred_bb.bb_label pred_bb target_bb.bb_instructions))` >> simp[] >> NO_TAC) >>
  DISJ1_TAC >> simp[GSYM listTheory.MEM_EL] >>
  mp_tac (Q.SPECL [`func`, `target_bb`, `pred_bb.bb_label`, `pred_bb`,
    `EL n (nub (phi_vars_needing_forward pred_bb.bb_label pred_bb
      target_bb.bb_instructions))`]
    cfgNormBaseTheory.phi_fwd_var_in_fn_all_vars) >>
  strip_tac >> pop_assum match_mp_tac >> conj_tac
  >- first_assum ACCEPT_TAC >>
  metis_tac[listTheory.MEM_nub, listTheory.MEM_EL]
QED

(* Case 2: pred' - subst_label_terminator only renames labels, vars from func.
   Key facts: subst_label_inst preserves outputs (subst_label_inst_fields),
   and subst_label_op (Var v) = Var v (subst_label_op_Var). *)
Theorem var_source_pred[local]:
  !func pred_bb target_bb split_lbl inst v.
    MEM pred_bb func.fn_blocks /\
    MEM inst (subst_label_terminator target_bb.bb_label split_lbl pred_bb).bb_instructions /\
    (MEM v inst.inst_outputs \/ MEM (Var v) inst.inst_operands) ==>
    MEM v (fn_all_vars func)
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM inst _` mp_tac >>
  simp[cfgTransformTheory.subst_label_terminator_def, listTheory.MEM_MAP] >>
  disch_tac >> pop_assum (qx_choose_then `inst0` strip_assume_tac) >>
  Cases_on `is_terminator inst0.inst_opcode` >> gvs[] >>
  (* Non-terminator goals: inst was substituted to inst0 by gvs *)
  TRY (qpat_x_assum `MEM _ _.inst_outputs` mp_tac >>
       qpat_x_assum `MEM _ _.bb_instructions` mp_tac >>
       qpat_x_assum `MEM _ func.fn_blocks` mp_tac >>
       metis_tac[inst_output_in_fn_all_vars,
                 cfgNormBaseTheory.inst_operand_var_in_fn_all_vars] >> NO_TAC) >>
  TRY (qpat_x_assum `MEM (Var _) _.inst_operands` mp_tac >>
       qpat_x_assum `MEM _ _.bb_instructions` mp_tac >>
       qpat_x_assum `MEM _ func.fn_blocks` mp_tac >>
       metis_tac[inst_output_in_fn_all_vars,
                 cfgNormBaseTheory.inst_operand_var_in_fn_all_vars] >> NO_TAC) >>
  (* Terminator outputs: use subst_label_inst_fields *)
  TRY (gvs[cfgTransformProofsTheory.subst_label_inst_fields] >>
       metis_tac[inst_output_in_fn_all_vars] >> NO_TAC) >>
  (* Terminator operands: trace through subst_label_op *)
  gvs[cfgTransformTheory.subst_label_inst_def, listTheory.MEM_MAP] >>
  Cases_on `y` >>
  gvs[cfgTransformProofsTheory.subst_label_op_Var,
      cfgTransformProofsTheory.subst_label_op_Lit,
      cfgTransformProofsTheory.subst_label_op_Label] >>
  TRY (BasicProvers.every_case_tac >> gvs[] >> NO_TAC) >>
  mp_tac (Q.SPECL [`func`, `pred_bb`, `inst0`, `s`]
    cfgNormBaseTheory.inst_operand_var_in_fn_all_vars) >> simp[]
QED

(* Case 3: target' - update_phis_for_split may introduce fwd vars *)
Theorem var_source_target[local]:
  !func pred_bb target_bb id_base split_bb var_repls split_lbl inst v.
    MEM target_bb func.fn_blocks /\
    build_split_block pred_bb target_bb id_base = (split_bb, var_repls) /\
    split_lbl = split_block_name pred_bb.bb_label target_bb.bb_label /\
    MEM inst (update_phis_for_split pred_bb.bb_label split_lbl
              var_repls target_bb).bb_instructions /\
    (MEM v inst.inst_outputs \/ MEM (Var v) inst.inst_operands) ==>
    MEM v (fn_all_vars func) \/
    ?w. v = STRCAT (STRCAT (split_block_name pred_bb.bb_label
              target_bb.bb_label) "_fwd_") w
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM inst (update_phis_for_split _ _ _ _).bb_instructions` mp_tac >>
  simp[cfgNormDefsTheory.update_phis_for_split_def, listTheory.MEM_MAP] >>
  disch_tac >> pop_assum (qx_choose_then `inst0` strip_assume_tac) >>
  Cases_on `inst0.inst_opcode = PHI` >> gvs[] >>
  (* Goals 1,2: PHI outputs/operands. Goals 3,4: non-PHI outputs/operands *)
  (* Handle non-PHI + PHI-outputs: all use DISJ1_TAC + existing var lemmas *)
  TRY (DISJ1_TAC >>
    qpat_x_assum `MEM _ _.bb_instructions` mp_tac >>
    qpat_x_assum `MEM _ func.fn_blocks` mp_tac >>
    TRY (qpat_x_assum `MEM _ _.inst_outputs` mp_tac) >>
    TRY (qpat_x_assum `MEM (Var _) _.inst_operands` mp_tac) >>
    metis_tac[inst_output_in_fn_all_vars,
              cfgNormBaseTheory.inst_operand_var_in_fn_all_vars] >> NO_TAC) >>
  (* Remaining: PHI operands - use update_phi_ops_var_source *)
  mp_tac (Q.SPECL [`pred_bb.bb_label`,
    `split_block_name pred_bb.bb_label target_bb.bb_label`,
    `var_repls`, `inst0.inst_operands`, `v`] update_phi_ops_var_source) >>
  simp[] >> strip_tac >>
  TRY (DISJ1_TAC >>
    mp_tac (Q.SPECL [`func`, `target_bb`, `inst0`, `v`]
      cfgNormBaseTheory.inst_operand_var_in_fn_all_vars) >> simp[] >> NO_TAC) >>
  DISJ2_TAC >>
  imp_res_tac cfgNormBaseTheory.build_split_block_repls >>
  res_tac >> qexists_tac `w` >> simp[]
QED

(* Case 4: original block - unchanged, vars from func *)
Theorem var_source_original[local]:
  !func bb inst v.
    MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    (MEM v inst.inst_outputs \/ MEM (Var v) inst.inst_operands) ==>
    MEM v (fn_all_vars func)
Proof
  rpt strip_tac >>
  TRY (irule cfgNormBaseTheory.inst_operand_var_in_fn_all_vars >>
      qexistsl_tac [`bb`, `inst`] >> simp[] >> NO_TAC) >>
  irule inst_output_in_fn_all_vars >>
  qexistsl_tac [`bb`, `inst`] >> simp[]
QED

(* Key helper: every variable in insert_split func' is either from func
   or is a forwarding variable with the split label prefix.
   Combines the 4 case helpers above. *)
Theorem insert_split_var_source[local]:
  !func pred_bb target_bb id_base bb inst v.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    ALL_DISTINCT (fn_labels func) /\
    pred_bb.bb_label <> target_bb.bb_label /\
    MEM bb (insert_split func pred_bb target_bb id_base).fn_blocks /\
    MEM inst bb.bb_instructions /\
    (MEM v inst.inst_outputs \/ MEM (Var v) inst.inst_operands) ==>
    MEM v (fn_all_vars func) \/
    ?w. v = STRCAT (STRCAT (split_block_name pred_bb.bb_label
              target_bb.bb_label) "_fwd_") w
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM bb _` mp_tac >>
  simp[cfgNormDefsTheory.insert_split_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  simp[listTheory.MEM_APPEND, MEM_replace_block] >>
  strip_tac >> gvs[] >>
  (* Reconstruct the disjunction that rpt strip_tac split *)
  SUBGOAL_THEN ``MEM v inst.inst_outputs \/ MEM (Var v) inst.inst_operands``
    ASSUME_TAC
  >- (TRY (DISJ1_TAC >> simp[] >> NO_TAC) >> DISJ2_TAC >> simp[]) >>
  (* Case 1: split_bb (both gvs directions) *)
  TRY (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
       `split_bb`, `var_repls`, `inst`, `v`] var_source_split_bb) >>
       simp[] >> NO_TAC) >>
  TRY (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
       `bb`, `var_repls`, `inst`, `v`] var_source_split_bb) >>
       simp[] >> NO_TAC) >>
  (* Case 2: pred' *)
  TRY (DISJ1_TAC >> mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`,
       `split_bb.bb_label`, `inst`, `v`] var_source_pred) >> simp[] >> NO_TAC) >>
  (* Case 3: target' *)
  TRY (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
       `split_bb`, `var_repls`, `split_bb.bb_label`,
       `inst`, `v`] var_source_target) >>
       (impl_tac >- (
         imp_res_tac cfgNormSimTheory.build_split_block_label >> simp[])) >>
       simp[] >> NO_TAC) >>
  (* Case 4: original *)
  DISJ1_TAC >> irule var_source_original >>
  qexistsl_tac [`bb`, `inst`] >> gvs[]
QED

(* Lifts insert_split_var_source from per-instruction to per-function level.
   Any variable in fn_all_vars of insert_split result is either:
   (1) in fn_all_vars of the original func, or
   (2) has the form split_lbl ++ "_fwd_" ++ w *)
Theorem insert_split_all_var_source:
  !func pred_bb target_bb id_base v.
    MEM pred_bb func.fn_blocks /\
    MEM target_bb func.fn_blocks /\
    ALL_DISTINCT (fn_labels func) /\
    pred_bb.bb_label <> target_bb.bb_label /\
    MEM v (fn_all_vars (insert_split func pred_bb target_bb id_base)) ==>
    MEM v (fn_all_vars func) \/
    ?w. v = STRCAT (STRCAT (split_block_name pred_bb.bb_label
              target_bb.bb_label) "_fwd_") w
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  CONV_TAC (LAND_CONV (SIMP_CONV (srw_ss())
    [cfgTransformTheory.fn_all_vars_def, listTheory.MEM_FLAT,
     listTheory.MEM_MAP, listTheory.MEM_APPEND, PULL_EXISTS])) >>
  simp[PULL_EXISTS] >> rpt gen_tac >> strip_tac
  (* outputs branch *)
  >- (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
        `bb`, `inst`, `v`] insert_split_var_source) >>
      simp[])
  (* operands branch: need MEM (Var v) inst.inst_operands *)
  >> (mp_tac (Q.SPECL [`func`, `pred_bb`, `target_bb`, `id_base`,
        `bb`, `inst`, `v`] insert_split_var_source) >>
      simp[] >> disch_then irule >> DISJ2_TAC >>
      qpat_x_assum `MEM op _` mp_tac >>
      qpat_x_assum `MEM v _` mp_tac >>
      Cases_on `op` >> simp[listTheory.MEM])
QED
