(*
 * Dominator Analysis — Proofs
 *
 * Proves correctness properties of the dominator analysis.
 * Uses df_analyze fixpoint/invariant/transfer infrastructure from dfAnalyzeProps.
 *)

Theory dominatorProofs
Ancestors
  dominatorDefs cfgAnalysisProps dfAnalyzeProps dfHelperProps
Libs
  listTheory finite_mapTheory pred_setTheory pairTheory

(* ========================================================================
   Finite map / FOLDL helpers (used by multiple theorems)
   ======================================================================== *)

Triviality fupdate_eq_self_flookup:
  !m k v. m |+ (k, v) = m ==> FLOOKUP m k = SOME v
Proof
  rpt strip_tac >>
  `FLOOKUP (m |+ (k, v)) k = SOME v` by simp[FLOOKUP_UPDATE] >>
  metis_tac[]
QED

Theorem foldl_fupdate_fdom[local]:
  !ls f m0.
    FDOM (FOLDL (\m lbl. m |+ (lbl, f lbl)) m0 ls) = FDOM m0 UNION set ls
Proof
  Induct >> rw[FOLDL, FDOM_FUPDATE] >>
  rw[EXTENSION] >> metis_tac[]
QED

Triviality foldl_fupdate_not_mem:
  !ls f m0 k.
    ~MEM k ls ==>
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, f lbl)) m0 ls) k = FLOOKUP m0 k
Proof
  Induct >> rw[FOLDL, FLOOKUP_UPDATE]
QED

Theorem foldl_fupdate_flookup[local]:
  !ls f m0 k.
    ALL_DISTINCT ls /\ MEM k ls ==>
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, f lbl)) m0 ls) k = SOME (f k)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  fs[foldl_fupdate_not_mem, FLOOKUP_UPDATE]
QED

Triviality foldl_fupdate_const[local]:
  !ls v m0 k.
    ALL_DISTINCT ls /\ MEM k ls ==>
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, v)) m0 ls) k = SOME v
Proof
  rpt strip_tac >>
  qspecl_then [`ls`, `K v`, `m0`, `k`] mp_tac foldl_fupdate_flookup >>
  simp[combinTheory.K_DEF]
QED

Theorem foldl_cond_insert_none[local]:
  !ls f m0 k.
    FLOOKUP m0 k = NONE /\
    (!lbl. MEM lbl ls /\ lbl = k ==> f lbl = NONE) ==>
    FLOOKUP (FOLDL (\m lbl.
      case f lbl of NONE => m | SOME v => m |+ (lbl, v)) m0 ls) k = NONE
Proof
  Induct >> rw[FOLDL] >>
  first_x_assum irule >>
  Cases_on `f h` >> rw[FLOOKUP_UPDATE] >>
  CCONTR_TAC >> fs[]
QED

Triviality wf_unique_block:
  !bbs bb bb'.
    ALL_DISTINCT (MAP (\b. b.bb_label) bbs) /\
    MEM bb bbs /\ MEM bb' bbs /\ (bb.bb_label = bb'.bb_label) ==> (bb = bb')
Proof
  Induct >> rw[] >> fs[listTheory.MEM_MAP] >> metis_tac[]
QED

Triviality valid_key_in_fold:
  !fn lbl i bb.
    wf_function fn /\ MEM bb fn.fn_blocks /\ bb.bb_label = lbl /\
    (lbl, i) IN df_valid_inst_keys fn.fn_blocks ==>
    i < LENGTH bb.bb_instructions + 1
Proof
  rw[dfAnalyzeProofsTheory.df_valid_inst_keys_def,
     pred_setTheory.IN_BIGUNION, listTheory.MEM_MAP,
     pred_setTheory.IN_IMAGE, pred_setTheory.IN_COUNT] >>
  `bb'.bb_label = bb.bb_label` by fs[] >>
  sg `bb' = bb`
  >- (irule wf_unique_block >> rw[] >>
      qexists_tac `fn.fn_blocks` >>
      fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def]) >>
  fs[pred_setTheory.IN_IMAGE, pred_setTheory.IN_COUNT]
QED

(* ========================================================================
   Category A: FOLDL/domain properties
   ======================================================================== *)

Theorem dom_analyze_domain_proof:
  !fn cfg lbl.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    MEM lbl (fn_labels fn) ==>
    lbl IN FDOM (dom_analyze cfg fn).da_dominators
Proof
  rw[dom_analyze_def, dom_sets_of_def] >>
  simp_tac std_ss [LET_THM] >>
  fs[foldl_fupdate_fdom, FDOM_FEMPTY]
QED

Theorem idom_entry_none_proof:
  !fn cfg bb.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    entry_block fn = SOME bb ==>
    idom_of (dom_analyze cfg fn) bb.bb_label = NONE
Proof
  rw[idom_of_def, dom_analyze_def] >>
  simp_tac std_ss [LET_THM] >>
  `fn_entry_label fn = SOME bb.bb_label` by
    rw[venomInstTheory.fn_entry_label_def] >>
  rw[compute_idom_def] >>
  irule foldl_cond_insert_none >>
  rw[FLOOKUP_DEF, FDOM_FEMPTY, compute_idom_for_def]
QED

(* ========================================================================
   Convergence toolkit for dominator analysis

   Three-component measure: boundary complement + inst complement + CARD.
   dom_transfer_inst is identity, so all inst values at block lbl equal
   the joined input for that block. This drastically simplifies proofs.
   ======================================================================== *)

(* --- Joined value computation --- *)
Definition dom_joined_def:
  dom_joined fn st lbl =
    df_joined_val Forward (fn_labels fn) list_intersect
      dom_edge_transfer ()
      (OPTION_MAP (\l. (l,[l])) (fn_entry_label fn))
      (cfg_analyze fn) st lbl
End

(* --- State invariant --- *)
Definition dom_state_inv_def:
  dom_state_inv fn (st : string list df_state) <=>
    (* C1: boundary values are ALL_DISTINCT sublists of fn_labels *)
    (!lbl v. FLOOKUP st.ds_boundary lbl = SOME v ==>
       ALL_DISTINCT v /\ set v SUBSET set (fn_labels fn)) /\
    (* C2: inst keys bounded *)
    FDOM st.ds_inst SUBSET df_valid_inst_keys fn.fn_blocks /\
    (* C3: inst values bounded *)
    (!k v. FLOOKUP st.ds_inst k = SOME v ==>
       ALL_DISTINCT v /\ set v SUBSET set (fn_labels fn)) /\
    (* C4: current joined ⊆ stored value at (lbl,0) *)
    (!lbl v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 ==>
       set (dom_joined fn st lbl) SUBSET set v0) /\
    (* C5: stored v0 is a FILTER of fn_labels *)
    (!lbl v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 ==>
       ?P. v0 = FILTER P (fn_labels fn)) /\
    (* C6: (lbl,j) ∈ FDOM ⟹ (lbl,0) ∈ FDOM *)
    (!lbl j. (lbl, j) IN FDOM st.ds_inst ==>
       (lbl, 0n) IN FDOM st.ds_inst) /\
    (* C7: all inst values for a block are same (identity transfer) *)
    (!lbl i v. FLOOKUP st.ds_inst (lbl, i) = SOME v ==>
       FLOOKUP st.ds_inst (lbl, 0n) = SOME v) /\
    (* C8: processed blocks have boundaries *)
    (!lbl. (lbl, 0n) IN FDOM st.ds_inst ==>
       lbl IN FDOM st.ds_boundary) /\
    (* C9: each label is in its own boundary *)
    (!lbl. MEM lbl (fn_labels fn) ==>
       MEM lbl (df_boundary (fn_labels fn) st lbl))
End

(* Boundary-only subset of dom_state_inv — sufficient at fixpoint level *)
Definition dom_state_inv_bdy_def:
  dom_state_inv_bdy fn (st : string list df_state) <=>
    (* C1: boundary values are ALL_DISTINCT sublists of fn_labels *)
    (!lbl v. FLOOKUP st.ds_boundary lbl = SOME v ==>
       ALL_DISTINCT v /\ set v SUBSET set (fn_labels fn)) /\
    (* C9: each label is in its own boundary *)
    (!lbl. MEM lbl (fn_labels fn) ==>
       MEM lbl (df_boundary (fn_labels fn) st lbl))
End

Triviality dom_state_inv_imp_bdy[local]:
  !fn st. dom_state_inv fn st ==> dom_state_inv_bdy fn st
Proof
  rw[dom_state_inv_def, dom_state_inv_bdy_def]
QED

(* Entry label is always a member of fn_labels *)
Triviality fn_entry_mem_fn_labels:
  !fn e. wf_function fn /\ fn_entry_label fn = SOME e ==>
         MEM e (fn_labels fn)
Proof
  rpt strip_tac >>
  fs[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
  Cases_on `fn.fn_blocks` >> fs[NULL_EQ] >>
  rw[venomInstTheory.fn_labels_def, MEM_MAP]
QED

(* --- Extra invariant: entry + fixpoint-equation direction --- *)
Definition dom_extra_inv_def:
  dom_extra_inv fn (st : string list df_state) <=>
    (* E0: all labels have boundary entries *)
    (!lbl. MEM lbl (fn_labels fn) ==> lbl IN FDOM st.ds_boundary) /\
    (* E1: entry boundary ⊆ {entry} *)
    (!e v. fn_entry_label fn = SOME e /\
           FLOOKUP st.ds_boundary e = SOME v ==>
           set v SUBSET {e}) /\
    (* E2: entry ∈ every boundary *)
    (!e lbl v. fn_entry_label fn = SOME e /\
               FLOOKUP st.ds_boundary lbl = SOME v ==>
               MEM e v) /\
    (* E3: joined ⊆ boundary for non-entry blocks *)
    (!lbl v. fn_entry_label fn <> SOME lbl /\
             FLOOKUP st.ds_boundary lbl = SOME v ==>
             set (dom_joined fn st lbl) SUBSET set v)
End

(* Combined invariant *)
Definition dom_full_inv_def:
  dom_full_inv fn st <=> dom_state_inv fn st /\ dom_extra_inv fn st
End

(* --- Inst complement: how far each inst value is from "top" --- *)
Definition dom_inst_complement_def:
  dom_inst_complement fn (st : string list df_state) =
    SIGMA (\k. LENGTH (fn_labels fn) -
               LENGTH (THE (FLOOKUP st.ds_inst k))) (FDOM st.ds_inst)
End

(* --- Three-component measure --- *)
Definition dom_measure_def:
  dom_measure fn st =
    SUM (MAP (\lbl. LENGTH (fn_labels fn) -
                    LENGTH (df_boundary (fn_labels fn) st lbl))
         (fn_labels fn)) +
    dom_inst_complement fn st +
    CARD (FDOM st.ds_inst)
End

Definition dom_measure_bound_def:
  dom_measure_bound fn =
    LENGTH (fn_labels fn) * LENGTH (fn_labels fn) +
    LENGTH (fn_labels fn) * df_total_inst_slots fn.fn_blocks +
    df_total_inst_slots fn.fn_blocks
End

(* ========================================================================
   Basic helpers
   ======================================================================== *)

Theorem three_sum_strict[local]:
  !a b c a' b' (c':num).
    a <= a' /\ b <= b' /\ c <= c' /\
    (a < a' \/ b < b' \/ c < c') ==>
    a + b + c < a' + b' + c'
Proof
  rpt strip_tac >> fs[]
QED

Theorem all_distinct_psubset_length[local]:
  !xs ys.
    ALL_DISTINCT xs /\ ALL_DISTINCT ys /\
    set xs SUBSET set ys /\ set xs <> set ys ==>
    LENGTH xs < LENGTH ys
Proof
  rw[] >>
  `FINITE (set ys)` by rw[FINITE_LIST_TO_SET] >>
  `CARD (set xs) = LENGTH xs` by metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `CARD (set ys) = LENGTH ys` by metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `set xs PSUBSET set ys` by (rw[PSUBSET_DEF] >> metis_tac[]) >>
  `CARD (set xs) < CARD (set ys)` by metis_tac[CARD_PSUBSET] >>
  DECIDE_TAC
QED

(* Identity transfer: fold output = accumulator, all values = init_val *)
Theorem identity_fold_block_values[local]:
  !lbl instrs init_val fv im.
    df_fold_block Forward (dom_transfer_inst ()) lbl instrs init_val
      = (fv, im) ==>
    fv = init_val /\
    !k v. FLOOKUP im k = SOME v ==> v = init_val
Proof
  rw[dfAnalyzeDefsTheory.df_fold_block_def] >>
  qspecl_then [`instrs`, `dom_transfer_inst ()`, `lbl`, `0`,
    `init_val`, `FEMPTY`, `fv`, `im`, `\x. x = init_val`]
    mp_tac dfAnalyzeProofsTheory.df_fold_forward_invariant >>
  simp[dominatorDefsTheory.dom_transfer_inst_def] >>
  metis_tac[]
QED

(* Helpers for list_intersect [x] ys — trivially ALL_DISTINCT, subset *)
Triviality list_intersect_single_ad[local]:
  ALL_DISTINCT (list_intersect [x] ys)
Proof
  simp[dfHelperDefsTheory.list_intersect_def] >>
  IF_CASES_TAC >> simp[]
QED

Triviality list_intersect_single_subset[local]:
  set (list_intersect [x] ys) SUBSET set ys
Proof
  simp[dfHelperDefsTheory.list_intersect_def, SUBSET_DEF, MEM_FILTER] >>
  IF_CASES_TAC >> simp[]
QED


(* Joined value is ALL_DISTINCT sublist of fn_labels *)
Theorem dom_joined_invariant[local]:
  !fn lbl st.
    wf_function fn /\ dom_state_inv fn st ==>
    ALL_DISTINCT (dom_joined fn st lbl) /\
    set (dom_joined fn st lbl) SUBSET set (fn_labels fn)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  simp[dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >>
  gvs[list_intersect_single_ad, SUBSET_REFL, list_intersect_single_subset]
  >> FIRST [
       (* ALL_DISTINCT (FOLDL ...) *)
       match_mp_tac dfHelperPropsTheory.foldl_intersect_all_distinct >>
       simp[dfHelperDefsTheory.list_intersect_def, FILTER_ALL_DISTINCT],
       (* set (list_intersect [x] (FOLDL ...)) SUBSET set fn_labels *)
       irule SUBSET_TRANS >>
       irule_at Any list_intersect_single_subset >>
       irule SUBSET_TRANS >>
       irule_at Any dfHelperPropsTheory.foldl_list_intersect_subset >>
       simp[dfHelperDefsTheory.list_intersect_def,
            LIST_TO_SET_FILTER, INTER_SUBSET],
       (* set (FOLDL ...) SUBSET set fn_labels *)
       irule SUBSET_TRANS >>
       irule_at Any dfHelperPropsTheory.foldl_list_intersect_subset >>
       simp[dfHelperDefsTheory.list_intersect_def,
            LIST_TO_SET_FILTER, INTER_SUBSET]
     ]
QED

(* Joined value is a FILTER of fn_labels *)
Theorem dom_joined_is_filter[local]:
  !fn st lbl.
    wf_function fn ==>
    ?P. dom_joined fn st lbl = FILTER P (fn_labels fn)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  (* Expand to base + entry_val structure *)
  PURE_REWRITE_TAC [dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def,
                    LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  Cases_on `fn_entry_label fn` >> simp[]
  >- ((* NONE: no entry join *)
      Cases_on `MAP (\nbr. dom_edge_transfer () nbr lbl
                  (df_boundary (fn_labels fn) st nbr))
                  (cfg_preds_of (cfg_analyze fn) lbl)` >> simp[]
      >- (qexists_tac `\x. T` >> rw[listTheory.FILTER_T])
      >> simp[dfHelperDefsTheory.list_intersect_def] >>
         qspecl_then [`t`, `FILTER (\x. MEM x h) (fn_labels fn)`]
           strip_assume_tac dfHelperPropsTheory.foldl_intersect_is_filter >>
         qexists_tac `\x. P x /\ MEM x h` >>
         simp[rich_listTheory.FILTER_FILTER])
  >> (* SOME x: have entry join when lbl = x *)
     Cases_on `lbl = x` >> simp[]
     >- ((* lbl = entry *)
         simp[dfHelperDefsTheory.list_intersect_def] >>
         Cases_on `MAP (\nbr. dom_edge_transfer () nbr x
                     (df_boundary (fn_labels fn) st nbr))
                     (cfg_preds_of (cfg_analyze fn) x)` >> simp[]
         >- ((* edge_vals = []: FILTER (\y. MEM y fn_labels) [x] *)
             Cases_on `MEM x (fn_labels fn)` >> simp[]
             >- (qexists_tac `$= x` >> metis_tac[ALL_DISTINCT_FILTER])
             >> qexists_tac `\y. F` >> simp[])
         >> (* edge_vals = h::t: FILTER (\y. MEM y (FOLDL ...)) [x] *)
            simp[dfHelperDefsTheory.list_intersect_def] >>
            Cases_on `MEM x (FOLDL list_intersect
                       (FILTER (\x. MEM x h) (fn_labels fn)) t)` >> simp[]
            >- (`MEM x (fn_labels fn)` by (
                  `set (FOLDL list_intersect
                     (FILTER (\x. MEM x h) (fn_labels fn)) t)
                   SUBSET set (FILTER (\x. MEM x h) (fn_labels fn))` by
                    simp[dfHelperPropsTheory.foldl_list_intersect_subset] >>
                  fs[pred_setTheory.SUBSET_DEF, listTheory.MEM_FILTER]) >>
                qexists_tac `$= x` >> metis_tac[ALL_DISTINCT_FILTER])
            >> qexists_tac `\y. F` >> simp[])
     >> (* lbl ≠ entry: same as NONE *)
        Cases_on `MAP (\nbr. dom_edge_transfer () nbr lbl
                    (df_boundary (fn_labels fn) st nbr))
                    (cfg_preds_of (cfg_analyze fn) lbl)` >> simp[]
        >- (qexists_tac `\x. T` >> rw[listTheory.FILTER_T])
        >> simp[dfHelperDefsTheory.list_intersect_def] >>
           qspecl_then [`t`, `FILTER (\x. MEM x h) (fn_labels fn)`]
             strip_assume_tac dfHelperPropsTheory.foldl_intersect_is_filter >>
           qexists_tac `\x. P x /\ MEM x h` >>
           simp[rich_listTheory.FILTER_FILTER]
QED

(* dom_joined only depends on ds_boundary *)
Theorem dom_joined_boundary_only[local]:
  !fn st1 st2 lbl.
    st1.ds_boundary = st2.ds_boundary ==>
    dom_joined fn st1 lbl = dom_joined fn st2 lbl
Proof
  rw[dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM, dfAnalyzeDefsTheory.df_boundary_def]
QED

Triviality edge_transfer_mono:
  !nbr b (new_bnd:string list) fn st lbl.
    set new_bnd SUBSET set (df_boundary (fn_labels fn) st b) ==>
    set (dom_edge_transfer () nbr lbl
          (df_boundary (fn_labels fn)
             (st with ds_boundary := st.ds_boundary |+ (b, new_bnd)) nbr))
    SUBSET
    set (dom_edge_transfer () nbr lbl
          (df_boundary (fn_labels fn) st nbr))
Proof
  rw[dominatorDefsTheory.dom_edge_transfer_def,
     cfgDefsTheory.set_insert_def,
     dfAnalyzeDefsTheory.df_boundary_def, FLOOKUP_UPDATE] >>
  metis_tac[SUBSET_DEF, IN_INSERT]
QED

(* Joined value monotonicity: shrinking a boundary shrinks joined *)
Theorem dom_joined_boundary_mono[local]:
  !fn st lbl b new_bnd.
    set new_bnd SUBSET set (df_boundary (fn_labels fn) st b) ==>
    set (dom_joined fn
           (st with ds_boundary := st.ds_boundary |+ (b, new_bnd)) lbl)
    SUBSET set (dom_joined fn st lbl)
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC [dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def,
    LET_THM, dfAnalyzeDefsTheory.direction_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl`
  >- ((* preds = []: base = fn_labels, entry wrapper identical on both sides *)
      simp[SUBSET_REFL])
  >> ((* preds = h::t: base = FOLDL *)
      simp[] >>
      (* entry_val wrapper preserves SUBSET when base does *)
      BasicProvers.EVERY_CASE_TAC >> gvs[SUBSET_REFL] >>
      simp[dfHelperPropsTheory.list_intersect_set, SUBSET_DEF, IN_INTER] >>
      rpt strip_tac >> gvs[] >>
      `set (FOLDL list_intersect (fn_labels fn)
         (MAP (\nbr. dom_edge_transfer () nbr lbl
           (df_boundary (fn_labels fn)
             (st with ds_boundary := st.ds_boundary |+ (b,new_bnd)) nbr))
           (h::t)))
       SUBSET
       set (FOLDL list_intersect (fn_labels fn)
         (MAP (\nbr. dom_edge_transfer () nbr lbl
           (df_boundary (fn_labels fn) st nbr)) (h::t)))` by
        (irule dfHelperPropsTheory.foldl_list_intersect_mono >>
         rw[listTheory.EL_MAP] >> metis_tac[edge_transfer_mono]) >>
      fs[SUBSET_DEF])
QED

(* MEM is preserved by FOLDL list_intersect when element is in all lists *)
Triviality foldl_list_intersect_mem_all:
  !xs a v.
    MEM v a /\ EVERY (\x. MEM v x) xs ==>
    MEM v (FOLDL list_intersect a xs)
Proof
  Induct >> rw[FOLDL] >>
  first_x_assum irule >> rw[dfHelperPropsTheory.list_intersect_mem]
QED

(* dom_edge_transfer always adds lbl to the boundary *)
Triviality dom_edge_transfer_mem_lbl:
  !ctx nbr lbl bdy. MEM lbl (dom_edge_transfer ctx nbr lbl bdy)
Proof
  rw[dominatorDefsTheory.dom_edge_transfer_def,
     cfgHelpersTheory.mem_set_insert]
QED

(* dom_joined always contains the label itself *)
Triviality dom_joined_contains_self:
  !fn st lbl.
    MEM lbl (fn_labels fn) ==>
    MEM lbl (dom_joined fn st lbl)
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC [dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def,
                    LET_THM, dfAnalyzeDefsTheory.direction_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  (* Establish EVERY before case-splitting MAP *)
  qabbrev_tac `evs = MAP (\nbr. dom_edge_transfer () nbr lbl
    (df_boundary (fn_labels fn) st nbr))
    (cfg_preds_of (cfg_analyze fn) lbl)` >>
  `EVERY (\e. MEM lbl e) evs` by
    (simp[Abbr `evs`, listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
     rpt strip_tac >> simp[dom_edge_transfer_mem_lbl]) >>
  Cases_on `evs`
  >- (BasicProvers.EVERY_CASE_TAC >>
      gvs[dfHelperPropsTheory.list_intersect_mem])
  >> `MEM lbl (FOLDL list_intersect (fn_labels fn) (h::t))` by
       (irule foldl_list_intersect_mem_all >> fs[listTheory.EVERY_DEF]) >>
     BasicProvers.EVERY_CASE_TAC >>
     gvs[dfHelperPropsTheory.list_intersect_mem]
QED

(* Entry label is in every df_boundary when dom_extra_inv holds *)
Triviality entry_mem_df_boundary:
  !fn st e nbr.
    wf_function fn /\ dom_extra_inv fn st /\
    fn_entry_label fn = SOME e ==>
    MEM e (df_boundary (fn_labels fn) st nbr)
Proof
  rw[dfAnalyzeDefsTheory.df_boundary_def] >>
  Cases_on `FLOOKUP st.ds_boundary nbr` >> fs[]
  >- (imp_res_tac fn_entry_mem_fn_labels >> fs[])
  >> fs[dom_extra_inv_def] >> res_tac
QED

(* Entry label is in dom_joined for every label *)
Triviality dom_joined_contains_entry:
  !fn st e lbl.
    wf_function fn /\ dom_extra_inv fn st /\
    fn_entry_label fn = SOME e ==>
    MEM e (dom_joined fn st lbl)
Proof
  rw[] >>
  Cases_on `lbl = e`
  >- (imp_res_tac fn_entry_mem_fn_labels >>
      metis_tac[dom_joined_contains_self])
  >> (* lbl ≠ e: entry is in every edge_transfer output *)
  `!nbr. MEM e (dom_edge_transfer () nbr lbl
                  (df_boundary (fn_labels fn) st nbr))` by
    (gen_tac >>
     simp[dominatorDefsTheory.dom_edge_transfer_def,
          cfgDefsTheory.set_insert_def] >>
     IF_CASES_TAC >> simp[] >>
     imp_res_tac entry_mem_df_boundary >> fs[]) >>
  simp[dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM] >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> simp[]
  >- (imp_res_tac fn_entry_mem_fn_labels >> fs[])
  >> irule foldl_list_intersect_mem_all >>
  simp[dfHelperPropsTheory.list_intersect_mem,
       listTheory.EVERY_MEM, listTheory.MEM_MAP] >>
  imp_res_tac fn_entry_mem_fn_labels >> rw[] >> fs[]
QED

(* Bridge: df_process_block for dominators = fold from dom_joined *)
Triviality dom_process_eq[local]:
  !fn lbl st.
    df_process_block Forward (fn_labels fn) list_intersect dom_transfer_inst
      dom_edge_transfer ()
      (OPTION_MAP (\l. (l,[l])) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st =
    let instrs = case lookup_block lbl fn.fn_blocks of
                   NONE => [] | SOME bb => bb.bb_instructions in
    let (fv, inst_map) = df_fold_block Forward
                           (dom_transfer_inst ()) lbl
                           instrs (dom_joined fn st lbl) in
    let new_bnd = list_intersect (df_boundary (fn_labels fn) st lbl) fv in
      if new_bnd = df_boundary (fn_labels fn) st lbl then st
      else st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd)
Proof
  rw[dfAnalyzeDefsTheory.df_process_block_def] >>
  simp_tac std_ss [LET_THM, dfAnalyzeDefsTheory.direction_case_def] >>
  rw[dom_edge_transfer_def] >>
  simp[dom_joined_def, LET_THM]
QED

(* --- Initial state satisfies invariant --- *)
Theorem dom_init_state_inv[local]:
  !fn.
    wf_function fn ==>
    let entry_val = OPTION_MAP (\lbl. (lbl, [lbl])) (fn_entry_label fn) in
    let st0 = init_df_state (fn_labels fn)
                (MAP (\bb. bb.bb_label) fn.fn_blocks) in
    case entry_val of
      NONE => dom_state_inv fn st0
    | SOME (lbl, v) =>
        dom_state_inv fn (st0 with ds_boundary := st0.ds_boundary |+ (lbl, v))
Proof
  rw[] >> simp_tac std_ss [LET_THM] >>
  `fn_entry_label fn = SOME (HD fn.fn_blocks).bb_label` by (
    fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
    rw[venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def] >>
    fs[NULL_EQ]) >>
  simp[] >>
  rw[dom_state_inv_def, dfAnalyzeDefsTheory.init_df_state_def] >>
  Cases_on `lbl = (HD fn.fn_blocks).bb_label` >>
  fs[FLOOKUP_UPDATE]
  >- rw[]
  >- (drule dfAnalyzeProofsTheory.foldl_init_flookup >> rw[] >>
      fs[venomWfTheory.wf_function_def])
  >- (rw[] >>
      `MEM (HD fn.fn_blocks) fn.fn_blocks` by
        (Cases_on `fn.fn_blocks` >>
         fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def]) >>
      fs[venomInstTheory.fn_labels_def, MEM_MAP] >> metis_tac[])
  >- (drule dfAnalyzeProofsTheory.foldl_init_flookup >> rw[SUBSET_REFL])
  (* C9: MEM lbl (df_boundary ...) *)
  >- (simp[dfAnalyzeDefsTheory.df_boundary_def, FLOOKUP_UPDATE])
  >- (srw_tac [][dfAnalyzeDefsTheory.df_boundary_def, FLOOKUP_UPDATE] >>
      qspecl_then [`MAP (\bb. bb.bb_label) fn.fn_blocks`,
                   `K (fn_labels fn)`, `FEMPTY`, `lbl`]
        mp_tac foldl_fupdate_flookup >>
      simp[combinTheory.K_DEF, venomInstTheory.fn_labels_def] >>
      fs[venomWfTheory.wf_function_def, venomInstTheory.fn_labels_def])
QED

(* --- Invariant preserved by process --- *)
Theorem dom_inv_preserved[local]:
  !fn lbl st.
    wf_function fn /\
    MEM lbl (fn_labels fn) /\
    dom_state_inv fn st ==>
    let cfg = cfg_analyze fn in
    let all_labels = fn_labels fn in
    let entry_val = OPTION_MAP (\l. (l, [l])) (fn_entry_label fn) in
    let process = df_process_block Forward all_labels list_intersect
                    dom_transfer_inst dom_edge_transfer () entry_val cfg
                    fn.fn_blocks in
    dom_state_inv fn (process lbl st)
Proof
  rpt strip_tac >>
  qpat_assum `dom_state_inv fn st`
    (fn th => assume_tac th >>
     strip_assume_tac (SIMP_RULE std_ss [dom_state_inv_def] th)) >>
  simp_tac std_ss [LET_THM] >>
  rewrite_tac[dom_process_eq] >>
  simp_tac std_ss [LET_THM] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  drule identity_fold_block_values >> strip_tac >>
  simp[dom_state_inv_def, FLOOKUP_UPDATE] >>
  rpt conj_tac (* 7 subgoals: C1 bdy, C2-C6 trivial, C7 bdy *)
  >- suspend "C1"
  >- suspend "C2"
  >- suspend "C3"
  >- suspend "C4"
  >- suspend "C5"
  >- suspend "C6"
  >> suspend "C7"
QED

Resume dom_inv_preserved[C1]:
  rpt gen_tac >> IF_CASES_TAC >> gvs[]
  >- (strip_tac >> pop_assum (SUBST_ALL_TAC o SYM) >>
      conj_tac
      >- (irule dfHelperPropsTheory.list_intersect_all_distinct >>
          irule dfAnalyzeProofsTheory.df_boundary_all_distinct >>
          fs[venomWfTheory.wf_function_def] >>
          first_assum ACCEPT_TAC)
      >> simp[dfHelperPropsTheory.list_intersect_set] >>
         drule_all dom_joined_invariant >> strip_tac >>
         irule SUBSET_TRANS >>
         qexists `set (dom_joined fn st lbl)` >>
         simp[INTER_SUBSET])
  >> strip_tac >> res_tac >> simp[]
QED

Resume dom_inv_preserved[C2]:
  first_assum ACCEPT_TAC
QED

Resume dom_inv_preserved[C3]:
  rpt gen_tac >> strip_tac >>
  irule SUBSET_TRANS >>
  qexists `set (dom_joined fn st lbl')` >> conj_tac
  >- (irule dom_joined_boundary_mono >>
      simp[dfHelperPropsTheory.list_intersect_set, INTER_SUBSET])
  >> res_tac
QED

Resume dom_inv_preserved[C4]:
  first_assum ACCEPT_TAC
QED

Resume dom_inv_preserved[C5]:
  first_assum ACCEPT_TAC
QED

Resume dom_inv_preserved[C6]:
  first_assum ACCEPT_TAC
QED

Resume dom_inv_preserved[C7]:
  rpt gen_tac >> strip_tac >>
  simp[dfAnalyzeDefsTheory.df_boundary_def, FLOOKUP_UPDATE] >>
  IF_CASES_TAC
  >- (simp[dfHelperPropsTheory.list_intersect_mem] >>
      conj_tac
      >- (first_x_assum (qspec_then `lbl` mp_tac) >>
          simp[dfAnalyzeDefsTheory.df_boundary_def])
      >> gvs[] >> irule (GEN_ALL dom_joined_contains_self) >> simp[])
  >> first_x_assum (qspec_then `lbl'` mp_tac) >> simp[] >>
     simp[dfAnalyzeDefsTheory.df_boundary_def, FLOOKUP_UPDATE]
QED

Finalise dom_inv_preserved

(* --- Measure bounded under invariant --- *)
Theorem dom_measure_bounded[local]:
  !fn st.
    wf_function fn /\ dom_state_inv fn st ==>
    dom_measure fn st <= dom_measure_bound fn
Proof
  rpt strip_tac >>
  simp_tac std_ss [dom_measure_def, dom_measure_bound_def] >>
  (* Boundary complement sum ≤ |labels| * |labels| *)
  `SUM (MAP (\lbl. LENGTH (fn_labels fn) -
                   LENGTH (df_boundary (fn_labels fn) st lbl))
            (fn_labels fn)) <=
   LENGTH (fn_labels fn) * LENGTH (fn_labels fn)` by (
    irule dfHelperPropsTheory.sum_map_bounded >>
    rw[EVERY_MEM] >> rpt strip_tac >>
    `LENGTH (df_boundary (fn_labels fn) st x) <= LENGTH (fn_labels fn)` by (
      irule dfAnalyzeProofsTheory.df_boundary_length_le >>
      fs[venomWfTheory.wf_function_def, dom_state_inv_def]) >>
    DECIDE_TAC) >>
  (* Inst complement ≤ |labels| * total_slots *)
  `dom_inst_complement fn st <=
   LENGTH (fn_labels fn) * df_total_inst_slots fn.fn_blocks` by (
    rw[dom_inst_complement_def] >>
    `!k. k IN FDOM st.ds_inst ==>
       LENGTH (fn_labels fn) - LENGTH (THE (FLOOKUP st.ds_inst k)) <=
       LENGTH (fn_labels fn)` by rw[] >>
    `SIGMA (\k. LENGTH (fn_labels fn) - LENGTH (THE (FLOOKUP st.ds_inst k)))
       (FDOM st.ds_inst) <=
     SIGMA (\k. LENGTH (fn_labels fn)) (FDOM st.ds_inst)` by
      (irule pred_setTheory.SUM_IMAGE_MONO_LESS_EQ >> rw[]) >>
    `CARD (FDOM st.ds_inst) <= df_total_inst_slots fn.fn_blocks` by (
      `CARD (FDOM st.ds_inst) <= CARD (df_valid_inst_keys fn.fn_blocks)` by (
        irule pred_setTheory.CARD_SUBSET >>
        rw[dfAnalyzeProofsTheory.df_valid_inst_keys_finite] >>
        fs[dom_state_inv_def]) >>
      metis_tac[dfAnalyzeProofsTheory.df_valid_inst_keys_card,
                arithmeticTheory.LESS_EQ_TRANS]) >>
    `(\k:string#num. LENGTH (fn_labels fn)) =
     K (LENGTH (fn_labels fn))` by
      rw[FUN_EQ_THM, combinTheory.K_DEF] >>
    fs[pred_setTheory.SUM_IMAGE_CONSTANT] >>
    irule arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `LENGTH (fn_labels fn) * CARD (FDOM st.ds_inst)` >>
    simp[]) >>
  (* CARD ≤ total_slots *)
  `CARD (FDOM st.ds_inst) <= df_total_inst_slots fn.fn_blocks` by (
    irule arithmeticTheory.LESS_EQ_TRANS >>
    qexists_tac `CARD (df_valid_inst_keys fn.fn_blocks)` >> conj_tac
    >- (irule pred_setTheory.CARD_SUBSET >>
        rw[dfAnalyzeProofsTheory.df_valid_inst_keys_finite] >>
        fs[dom_state_inv_def])
    >- rw[dfAnalyzeProofsTheory.df_valid_inst_keys_card]) >>
  DECIDE_TAC
QED

(* --- Convergence helpers for measure_increases --- *)

Triviality sum_complement_mono[local]:
  !f g (n:num) ls.
    (!x. MEM x ls ==> g x <= f x /\ f x <= n) ==>
    SUM (MAP (\x. n - f x) ls) <= SUM (MAP (\x. n - g x) ls)
Proof
  Induct_on `ls` >> simp[] >> rpt strip_tac >>
  `g h <= f h /\ f h <= n` by metis_tac[] >>
  `!x. MEM x ls ==> g x <= f x /\ f x <= n` by metis_tac[] >>
  res_tac >> DECIDE_TAC
QED

Triviality sum_complement_strict[local]:
  !f g (n:num) ls x.
    MEM x ls /\ g x < f x /\ f x <= n /\
    (!y. MEM y ls ==> g y <= f y /\ f y <= n) ==>
    SUM (MAP (\y. n - f y) ls) < SUM (MAP (\y. n - g y) ls)
Proof
  Induct_on `ls` >> rw[] >> fs[] >> (
    `g h <= f h /\ f h <= n` by metis_tac[] >>
    `!y. MEM y ls ==> g y <= f y /\ f y <= n` by metis_tac[]
  )
  >- (`SUM (MAP (\y. n - f y) ls) <= SUM (MAP (\y. n - g y) ls)` by
        (irule sum_complement_mono >> metis_tac[]) >>
      DECIDE_TAC)
  >> `SUM (MAP (\y. n - f y) ls) < SUM (MAP (\y. n - g y) ls)` by
       (first_x_assum (qspecl_then [`f`, `g`, `n`, `x`] mp_tac) >> simp[] >>
        metis_tac[]) >>
     DECIDE_TAC
QED

Triviality dom_inst_complement_mono_base[local]:
  !fn st inst_map.
    (!k v_old v_new. FLOOKUP st.ds_inst k = SOME v_old /\
       FLOOKUP inst_map k = SOME v_new ==>
       ALL_DISTINCT v_new /\ ALL_DISTINCT v_old /\
       set v_new SUBSET set v_old) ==>
    dom_inst_complement fn st <=
    dom_inst_complement fn (st with ds_inst := FUNION inst_map st.ds_inst)
Proof
  rw[dom_inst_complement_def, finite_mapTheory.FDOM_FUNION] >>
  irule arithmeticTheory.LESS_EQ_TRANS >>
  qexists_tac `SIGMA (\k. LENGTH (fn_labels fn) -
    LENGTH (THE (FLOOKUP (FUNION inst_map st.ds_inst) k)))
    (FDOM st.ds_inst)` >>
  conj_tac
  >- (irule pred_setTheory.SUM_IMAGE_MONO_LESS_EQ >> rw[] >>
      simp[finite_mapTheory.FLOOKUP_FUNION] >>
      Cases_on `FLOOKUP inst_map x` >> simp[] >>
      `?v_old. FLOOKUP st.ds_inst x = SOME v_old` by
        metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
      simp[] >> res_tac >>
      `LENGTH x' <= LENGTH v_old` by
        metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET, pred_setTheory.CARD_SUBSET,
                  listTheory.FINITE_LIST_TO_SET, arithmeticTheory.LESS_EQ_TRANS] >>
      DECIDE_TAC)
  >- (irule pred_setTheory.SUM_IMAGE_SUBSET_LE >>
      simp[pred_setTheory.SUBSET_UNION])
QED

(* Generalized: works with any st' that has st'.ds_inst = FUNION inst_map st.ds_inst *)
Triviality dom_inst_complement_mono[local]:
  !fn st st' inst_map.
    st'.ds_inst = FUNION inst_map st.ds_inst /\
    (!k v_old v_new. FLOOKUP st.ds_inst k = SOME v_old /\
       FLOOKUP inst_map k = SOME v_new ==>
       ALL_DISTINCT v_new /\ ALL_DISTINCT v_old /\
       set v_new SUBSET set v_old) ==>
    dom_inst_complement fn st <= dom_inst_complement fn st'
Proof
  rpt strip_tac >>
  `dom_inst_complement fn st' =
   dom_inst_complement fn (st with ds_inst := FUNION inst_map st.ds_inst)` by
    simp[dom_inst_complement_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule dom_inst_complement_mono_base >> metis_tac[]
QED

Triviality dom_inst_complement_strict_base[local]:
  !fn st inst_map k0 v0 v_new.
    FLOOKUP st.ds_inst k0 = SOME v0 /\
    FLOOKUP inst_map k0 = SOME v_new /\
    LENGTH v_new < LENGTH v0 /\
    LENGTH v0 <= LENGTH (fn_labels fn) /\
    (!k v_old v_new'. FLOOKUP st.ds_inst k = SOME v_old /\
       FLOOKUP inst_map k = SOME v_new' ==>
       LENGTH v_new' <= LENGTH v_old) ==>
    dom_inst_complement fn st <
    dom_inst_complement fn (st with ds_inst := FUNION inst_map st.ds_inst)
Proof
  rpt strip_tac >>
  simp[dom_inst_complement_def, finite_mapTheory.FDOM_FUNION] >>
  irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
  qexists_tac `SIGMA (\k. LENGTH (fn_labels fn) -
    LENGTH (THE (FLOOKUP (FUNION inst_map st.ds_inst) k)))
    (FDOM st.ds_inst)` >>
  conj_tac
  >- (irule pred_setTheory.SUM_IMAGE_MONO_LESS >>
      rpt conj_tac
      >- (rw[] >>
          simp[finite_mapTheory.FLOOKUP_FUNION] >>
          Cases_on `FLOOKUP inst_map x` >> simp[] >>
          `?vx. FLOOKUP st.ds_inst x = SOME vx` by
            metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_NONE_SOME] >>
          simp[] >> res_tac >> DECIDE_TAC)
      >- (qexists_tac `k0` >> simp[] >>
          `k0 IN FDOM st.ds_inst` by
            metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
          simp[finite_mapTheory.FLOOKUP_FUNION] >> DECIDE_TAC)
      >- simp[])
  >- (irule pred_setTheory.SUM_IMAGE_SUBSET_LE >>
      simp[pred_setTheory.SUBSET_UNION])
QED

(* Generalized: works with any st' that has st'.ds_inst = FUNION inst_map st.ds_inst *)
Triviality dom_inst_complement_strict[local]:
  !fn st st' inst_map k0 v0 v_new.
    st'.ds_inst = FUNION inst_map st.ds_inst /\
    FLOOKUP st.ds_inst k0 = SOME v0 /\
    FLOOKUP inst_map k0 = SOME v_new /\
    LENGTH v_new < LENGTH v0 /\
    LENGTH v0 <= LENGTH (fn_labels fn) /\
    (!k v_old v_new'. FLOOKUP st.ds_inst k = SOME v_old /\
       FLOOKUP inst_map k = SOME v_new' ==>
       LENGTH v_new' <= LENGTH v_old) ==>
    dom_inst_complement fn st < dom_inst_complement fn st'
Proof
  rpt strip_tac >>
  `dom_inst_complement fn st' =
   dom_inst_complement fn (st with ds_inst := FUNION inst_map st.ds_inst)` by
    simp[dom_inst_complement_def] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule dom_inst_complement_strict_base >> metis_tac[]
QED

Triviality dom_boundary_len_mono[local]:
  !fn st lbl new_bv inst_map fv x.
    Abbrev (new_bv = list_intersect
              (df_boundary (fn_labels fn) st lbl) fv) ==>
    LENGTH (df_boundary (fn_labels fn)
              <|ds_inst := FUNION inst_map st.ds_inst;
                ds_boundary := st.ds_boundary |+ (lbl, new_bv)|> x) <=
    LENGTH (df_boundary (fn_labels fn) st x)
Proof
  rpt strip_tac >>
  simp[dfAnalyzeDefsTheory.df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `x = lbl` >> simp[] >>
  fs[markerTheory.Abbrev_def, dfAnalyzeDefsTheory.df_boundary_def] >>
  metis_tac[dfHelperPropsTheory.list_intersect_length_le]
QED

(* When all inst_map values equal joined, and all overlapping st keys
   also have value joined, and FDOM inst_map ⊆ FDOM st.ds_inst,
   then FUNION inst_map st.ds_inst = st.ds_inst *)
Triviality dom_funion_id[local]:
  !(inst_map:(string # num) |-> 'b) (st:'b df_state).
    FDOM inst_map SUBSET FDOM st.ds_inst /\
    (!k. k IN FDOM inst_map ==>
       FLOOKUP inst_map k = FLOOKUP st.ds_inst k) ==>
    FUNION inst_map st.ds_inst = st.ds_inst
Proof
  rw[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
     finite_mapTheory.FLOOKUP_FUNION] >>
  Cases_on `FLOOKUP inst_map x` >> simp[] >>
  `x IN FDOM inst_map` by fs[finite_mapTheory.FLOOKUP_DEF] >>
  res_tac >> fs[]
QED

(* When the fold produces values all equal to v0, and dom_state_inv holds,
   then FUNION inst_map st.ds_inst = st.ds_inst.
   Takes dom_state_inv directly to avoid fs[] corruption of v0. *)
Triviality dom_identity_funion[local]:
  !fn st inst_map lbl v0.
    dom_state_inv fn st /\
    FDOM inst_map SUBSET FDOM st.ds_inst /\
    FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 /\
    (!k v. FLOOKUP inst_map k = SOME v ==> v = v0) /\
    (!k. k IN FDOM inst_map ==> FST k = lbl) ==>
    FUNION inst_map st.ds_inst = st.ds_inst
Proof
  rpt strip_tac >>
  irule dom_funion_id >> reverse conj_tac >- fs[] >>
  rpt strip_tac >>
  `?w. FLOOKUP inst_map k = SOME w` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  `w = v0` by res_tac >>
  `k IN FDOM st.ds_inst` by metis_tac[pred_setTheory.SUBSET_DEF] >>
  `?sv. FLOOKUP st.ds_inst k = SOME sv` by
    metis_tac[finite_mapTheory.FLOOKUP_DEF, optionTheory.NOT_SOME_NONE] >>
  `FST k = lbl` by res_tac >>
  Cases_on `k` >> fs[] >>
  qpat_x_assum `dom_state_inv fn st` mp_tac >>
  simp[dom_state_inv_def] >> rpt strip_tac >>
  res_tac >> fs[]
QED

(* Helper: when inst and boundary updates are identity, process = st.
   Takes the fold equation with the raw case expression as input,
   matching what pairarg_tac produces in dom_measure_increases. *)
Triviality dom_process_identity[local]:
  !fn lbl st bb inst_map final_val.
    MEM lbl (fn_labels fn) /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_label = lbl /\
    df_fold_block Forward (dom_transfer_inst ()) lbl bb.bb_instructions
      (dom_joined fn st lbl) = (final_val, inst_map) /\
    FUNION inst_map st.ds_inst = st.ds_inst /\
    list_intersect (df_boundary (fn_labels fn) st lbl) final_val =
      df_boundary (fn_labels fn) st lbl /\
    lbl IN FDOM st.ds_boundary /\
    st.ds_boundary |+ (lbl, df_boundary (fn_labels fn) st lbl) =
      st.ds_boundary ==>
    df_process_block Forward (fn_labels fn) list_intersect
      dom_transfer_inst dom_edge_transfer ()
      (OPTION_MAP (\l. (l,[l])) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st = st
Proof
  rpt strip_tac >>
  simp_tac std_ss [dfAnalyzeDefsTheory.df_process_block_def,
                   LET_THM, dfAnalyzeDefsTheory.direction_case_def] >>
  `(case lookup_block lbl fn.fn_blocks of
      NONE => [] | SOME bb => bb.bb_instructions) =
   bb.bb_instructions` by (ASM_REWRITE_TAC [] >> simp[]) >>
  pop_assum (fn th => PURE_REWRITE_TAC [th]) >>
  fs[GSYM dom_joined_def] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[dfAnalyzeDefsTheory.df_state_component_equality]
QED

(* B2 contradiction: if joined=v0 (old value at slot 0), boundary unchanged,
   FDOM unchanged, then process = st. Used in measure_increases to rule out
   the "all unchanged" case. *)
Triviality dom_b2_process_eq_st:
  !fn lbl st bb inst_map joined v0.
    wf_function fn /\
    MEM lbl (fn_labels fn) /\
    dom_state_inv fn st /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_label = lbl /\
    df_fold_block Forward (dom_transfer_inst ()) lbl bb.bb_instructions
      (dom_joined fn st lbl) = (joined, inst_map) /\
    (!k v. FLOOKUP inst_map k = SOME v ==> v = joined) /\
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    FDOM inst_map SUBSET FDOM st.ds_inst /\
    (lbl, 0n) IN FDOM inst_map /\
    FLOOKUP st.ds_inst (lbl, 0n) = SOME v0 /\
    joined = v0 /\
    list_intersect (df_boundary (fn_labels fn) st lbl) joined =
      df_boundary (fn_labels fn) st lbl ==>
    df_process_block Forward (fn_labels fn) list_intersect
      dom_transfer_inst dom_edge_transfer ()
      (OPTION_MAP (\l. (l,[l])) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st = st
Proof
  rpt strip_tac >>
  `(lbl,0n) IN FDOM st.ds_inst` by fs[pred_setTheory.SUBSET_DEF] >>
  `!k v'. FLOOKUP inst_map k = SOME v' ==> v' = v0` by metis_tac[] >>
  `FUNION inst_map st.ds_inst = st.ds_inst` by
    (match_mp_tac dom_identity_funion >> metis_tac[]) >>
  `lbl IN FDOM st.ds_boundary` by
    (fs[dom_state_inv_def] >> metis_tac[]) >>
  `st.ds_boundary |+ (lbl, df_boundary (fn_labels fn) st lbl) =
     st.ds_boundary` by
    (irule finite_mapTheory.FUPDATE_ELIM >>
     simp[dfAnalyzeDefsTheory.df_boundary_def,
          finite_mapTheory.FLOOKUP_DEF,
          finite_mapTheory.FAPPLY_FUPDATE_THM]) >>
  match_mp_tac dom_process_identity >>
  qexistsl_tac [`bb`, `inst_map`, `joined`] >>
  simp[]
QED

(* Case A helper: boundary changed → boundary sum strictly increases *)
Triviality dom_measure_case_a[local]:
  !fn lbl st new_bv inst_map joined.
    wf_function fn /\
    MEM lbl (fn_labels fn) /\
    dom_state_inv fn st /\
    new_bv = list_intersect (df_boundary (fn_labels fn) st lbl) joined /\
    new_bv <> df_boundary (fn_labels fn) st lbl ==>
    SUM (MAP (\l. LENGTH (fn_labels fn) -
                  LENGTH (df_boundary (fn_labels fn) st l)) (fn_labels fn)) <
    SUM (MAP (\l. LENGTH (fn_labels fn) -
                  LENGTH (df_boundary (fn_labels fn)
                    <|ds_inst := inst_map ⊌ st.ds_inst;
                      ds_boundary := st.ds_boundary |+ (lbl,new_bv)|> l))
             (fn_labels fn))
Proof
  rpt strip_tac >>
  `Abbrev (new_bv = list_intersect (df_boundary (fn_labels fn) st lbl) joined)` by
    fs[markerTheory.Abbrev_def] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  `!l v. FLOOKUP st.ds_boundary l = SOME v ==>
     ALL_DISTINCT v /\ set v SUBSET set (fn_labels fn)` by
    fs[dom_state_inv_def] >>
  `ALL_DISTINCT (df_boundary (fn_labels fn) st lbl)` by
    metis_tac[dfAnalyzeProofsTheory.df_boundary_all_distinct] >>
  `LENGTH new_bv < LENGTH (df_boundary (fn_labels fn) st lbl)` by
    metis_tac[dfHelperPropsTheory.list_intersect_strict_length] >>
  qspecl_then [
    `\x. LENGTH (df_boundary (fn_labels fn) st x)`,
    `\x. LENGTH (df_boundary (fn_labels fn)
       <|ds_inst := inst_map ⊌ st.ds_inst;
         ds_boundary := st.ds_boundary |+ (lbl,new_bv)|> x)`,
    `LENGTH (fn_labels fn)`, `fn_labels fn`, `lbl`
  ] mp_tac sum_complement_strict >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  impl_tac >| [
    rpt conj_tac >| [
      first_assum ACCEPT_TAC,
      srw_tac [][dfAnalyzeDefsTheory.df_boundary_def,
                 finite_mapTheory.FLOOKUP_UPDATE] >>
      fs[dfAnalyzeDefsTheory.df_boundary_def],
      metis_tac[dfAnalyzeProofsTheory.df_boundary_length_le],
      rpt strip_tac >| [
        irule dom_boundary_len_mono >>
        qexists_tac `joined` >> first_assum ACCEPT_TAC,
        metis_tac[dfAnalyzeProofsTheory.df_boundary_length_le]
      ]
    ],
    simp[]
  ]
QED

(* Case B helper: boundary unchanged → inst complement strict or CARD strict *)
Triviality dom_measure_case_b[local]:
  !fn lbl st bb inst_map joined.
    wf_function fn /\
    MEM lbl (fn_labels fn) /\
    dom_state_inv fn st /\
    joined = dom_joined fn st lbl /\
    lookup_block lbl fn.fn_blocks = SOME bb /\
    bb.bb_label = lbl /\
    MEM bb fn.fn_blocks /\
    df_fold_block Forward (dom_transfer_inst ()) lbl bb.bb_instructions
      (dom_joined fn st lbl) = (joined, inst_map) /\
    (!k v. FLOOKUP inst_map k = SOME v ==> v = joined) /\
    (!k. k IN FDOM inst_map ==> FST k = lbl) /\
    (lbl, 0n) IN FDOM inst_map /\
    FDOM inst_map SUBSET df_valid_inst_keys fn.fn_blocks /\
    (!k v_old. FLOOKUP st.ds_inst k = SOME v_old /\ k IN FDOM inst_map ==>
       set joined SUBSET set v_old) /\
    list_intersect (df_boundary (fn_labels fn) st lbl) joined =
      df_boundary (fn_labels fn) st lbl /\
    df_process_block Forward (fn_labels fn) list_intersect
      dom_transfer_inst dom_edge_transfer ()
      (OPTION_MAP (\l. (l,[l])) (fn_entry_label fn))
      (cfg_analyze fn) fn.fn_blocks lbl st <> st ==>
    dom_inst_complement fn st <
    dom_inst_complement fn
      <|ds_inst := inst_map ⊌ st.ds_inst;
        ds_boundary := st.ds_boundary |+
          (lbl, df_boundary (fn_labels fn) st lbl)|> \/
    CARD (FDOM st.ds_inst) <
    CARD (FDOM <|ds_inst := inst_map ⊌ st.ds_inst;
                 ds_boundary := st.ds_boundary |+
                   (lbl, df_boundary (fn_labels fn) st lbl)|>.ds_inst)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  `ALL_DISTINCT joined /\ set joined SUBSET set (fn_labels fn)` by
    metis_tac[dom_joined_invariant] >>
  qpat_assum `dom_state_inv fn st`
    (fn th => assume_tac th >>
     strip_assume_tac (SIMP_RULE std_ss [dom_state_inv_def] th)) >>
  Cases_on `FDOM inst_map SUBSET FDOM st.ds_inst`
  >- ((* B2: all inst keys exist *)
      `(lbl, 0n) IN FDOM st.ds_inst` by
        fs[pred_setTheory.SUBSET_DEF] >>
      `?v0. FLOOKUP st.ds_inst (lbl, 0n) = SOME v0` by
        fs[finite_mapTheory.FLOOKUP_DEF] >>
      `set joined SUBSET set v0` by
        (qpat_assum `!k v_old. FLOOKUP st.ds_inst k = SOME v_old /\
           k IN FDOM inst_map ==> _`
          (qspecl_then [`(lbl,0n)`, `v0`] mp_tac) >>
         simp[]) >>
      `ALL_DISTINCT v0 /\ set v0 SUBSET set (fn_labels fn)` by
        (qpat_assum `!k v. FLOOKUP st.ds_inst k = SOME v ==>
           ALL_DISTINCT v /\ _`
          (drule_then assume_tac) >> fs[]) >>
      `?P. v0 = FILTER P (fn_labels fn)` by
        (qpat_assum `!lbl' v0'. FLOOKUP st.ds_inst (lbl',0) = SOME v0' ==>
           ?P. _`
          (drule_then assume_tac) >> metis_tac[]) >>
      `?Q. joined = FILTER Q (fn_labels fn)` by
        metis_tac[dom_joined_is_filter] >>
      Cases_on `set (joined:string list) = set v0`
      >- ((* set equal: derive joined = v0, then process = st — contradiction *)
          `FILTER Q (fn_labels fn) = FILTER P (fn_labels fn)` by
            (irule dfHelperPropsTheory.filter_set_eq_filter_eq >> rfs[]) >>
          `joined = v0` by metis_tac[] >>
          `df_process_block Forward (fn_labels fn) list_intersect
             dom_transfer_inst dom_edge_transfer ()
             (OPTION_MAP (\l. (l,[l])) (fn_entry_label fn))
             (cfg_analyze fn) fn.fn_blocks lbl st = st` by
            (match_mp_tac dom_b2_process_eq_st >>
             qexistsl_tac [`bb`, `inst_map`, `joined`, `v0`] >>
             rpt conj_tac >> first_assum ACCEPT_TAC) >>
          metis_tac[])
      >- ((* set not equal: proper subset, derive strict inst complement *)
          DISJ1_TAC >>
          `LENGTH joined < LENGTH v0` by
            metis_tac[all_distinct_psubset_length] >>
          irule dom_inst_complement_strict >>
          simp[dfAnalyzeDefsTheory.df_state_accessors] >>
          qexistsl_tac [`inst_map`, `(lbl, 0n)`, `v0`, `joined`] >> simp[] >>
          rpt conj_tac
          >- (`CARD (set v0) <= CARD (set (fn_labels fn))` by
                (irule pred_setTheory.CARD_SUBSET >> fs[]) >>
              metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET])
          >- (rpt strip_tac >>
              `v_new' = joined` by res_tac >>
              `k IN FDOM inst_map` by fs[finite_mapTheory.FLOOKUP_DEF] >>
              `set joined SUBSET set v_old` by
                (qpat_assum `!k v_old. FLOOKUP st.ds_inst k = SOME v_old /\
                   k IN FDOM inst_map ==> _`
                  (qspecl_then [`k`, `v_old`] mp_tac) >> simp[]) >>
              `ALL_DISTINCT v_old` by
                (qpat_assum `!k v. FLOOKUP st.ds_inst k = SOME v ==>
                   ALL_DISTINCT v /\ _`
                  (drule_then assume_tac) >> fs[]) >>
              `CARD (set joined) <= CARD (set v_old)` by
                (irule pred_setTheory.CARD_SUBSET >> fs[]) >>
              metis_tac[ALL_DISTINCT_CARD_LIST_TO_SET])
          >- (`(lbl,0n) IN FDOM inst_map` by fs[] >>
              `?w. FLOOKUP inst_map (lbl, 0n) = SOME w` by
                fs[finite_mapTheory.FLOOKUP_DEF] >>
              `w = joined` by res_tac >> fs[])))
  >- ((* B1: some inst key is new — CARD strict *)
      DISJ2_TAC >>
      simp[dfAnalyzeDefsTheory.df_state_accessors,
           finite_mapTheory.FDOM_FUNION] >>
      irule pred_setTheory.CARD_PSUBSET >>
      simp[pred_setTheory.PSUBSET_DEF, pred_setTheory.SUBSET_UNION] >>
      fs[pred_setTheory.SUBSET_DEF] >>
      metis_tac[pred_setTheory.IN_UNION])
QED

(* --- Measure strictly increases when state changes --- *)
Theorem dom_measure_increases[local]:
  !fn lbl st.
    wf_function fn /\
    MEM lbl (fn_labels fn) /\
    dom_state_inv fn st ==>
    let cfg = cfg_analyze fn in
    let all_labels = fn_labels fn in
    let entry_val = OPTION_MAP (\l. (l, [l])) (fn_entry_label fn) in
    let process = df_process_block Forward all_labels list_intersect
                    dom_transfer_inst dom_edge_transfer () entry_val cfg
                    fn.fn_blocks in
    process lbl st <> st ==>
    dom_measure fn st < dom_measure fn (process lbl st)
Proof
  simp_tac std_ss [LET_THM] >> rpt strip_tac >>
  rewrite_tac[dom_process_eq] >> simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC
  >- ((* Unchanged: process = st, contradicts process ≠ st *)
      gvs[] >>
      qpat_x_assum `_ <> _` mp_tac >> simp[dom_process_eq] >>
      simp_tac std_ss [LET_THM] >> pairarg_tac >> simp[] >>
      drule identity_fold_block_values >> strip_tac >>
      gvs[GSYM dom_joined_def]) >>
  (* Changed: boundary updated *)
  drule identity_fold_block_values >> strip_tac >>
  gvs[GSYM dom_joined_def] >>
  qpat_assum `dom_state_inv fn st`
    (fn th => assume_tac th >>
     strip_assume_tac (SIMP_RULE std_ss [dom_state_inv_def] th)) >>
  (* Simplify measure: ds_inst unchanged *)
  simp[dom_measure_def, dom_inst_complement_def] >>
  (* Remaining measure argument *)
  suspend "measure_main"
QED

Resume dom_measure_increases[measure_main]:
  `ALL_DISTINCT (df_boundary (fn_labels fn) st lbl)` by
    (irule dfAnalyzeProofsTheory.df_boundary_all_distinct >>
     conj_tac >- first_assum ACCEPT_TAC >>
     gvs[venomWfTheory.wf_function_def]) >>
  `LENGTH (list_intersect (df_boundary (fn_labels fn) st lbl)
                           (dom_joined fn st lbl)) <
   LENGTH (df_boundary (fn_labels fn) st lbl)` by
    (match_mp_tac dfHelperPropsTheory.list_intersect_strict_length >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [
    `\x. LENGTH (df_boundary (fn_labels fn) st x)`,
    `\x. LENGTH (df_boundary (fn_labels fn)
       (st with ds_boundary := st.ds_boundary |+
         (lbl, list_intersect (df_boundary (fn_labels fn) st lbl)
                               (dom_joined fn st lbl))) x)`,
    `LENGTH (fn_labels fn)`, `fn_labels fn`, `lbl`
  ] mp_tac sum_complement_strict >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  impl_tac >| [
    rpt conj_tac >| [
      first_assum ACCEPT_TAC,
      simp[dfAnalyzeDefsTheory.df_boundary_def, FLOOKUP_UPDATE] >>
      rewrite_tac[GSYM dfAnalyzeDefsTheory.df_boundary_def] >>
      first_assum ACCEPT_TAC,
      metis_tac[dfAnalyzeProofsTheory.df_boundary_length_le,
                venomWfTheory.wf_function_def],
      rpt strip_tac >| [
        simp[dfAnalyzeDefsTheory.df_boundary_def, FLOOKUP_UPDATE] >>
        Cases_on `y = lbl` >> simp[] >>
        rewrite_tac[GSYM dfAnalyzeDefsTheory.df_boundary_def] >>
        metis_tac[dfHelperPropsTheory.list_intersect_length_le],
        metis_tac[dfAnalyzeProofsTheory.df_boundary_length_le,
                  venomWfTheory.wf_function_def]
      ]
    ],
    simp[]
  ]
QED

Finalise dom_measure_increases;

(* dom_joined is always ⊆ fn_labels, for ANY state *)
Triviality dom_joined_subset_fn_labels:
  !fn st lbl.
    wf_function fn ==>
    set (dom_joined fn st lbl) SUBSET set (fn_labels fn)
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC [dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def,
                    LET_THM, dfAnalyzeDefsTheory.direction_case_def] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl`
  >- ((* [] preds: base = fn_labels, entry wrapper ⊆ fn_labels *)
      BasicProvers.EVERY_CASE_TAC >> gvs[SUBSET_REFL] >>
      simp[dfHelperPropsTheory.list_intersect_set,
           pred_setTheory.SUBSET_DEF, pred_setTheory.IN_INTER])
  >> (* h::t preds: FOLDL ⊆ fn_labels, then entry wrapper preserves *)
  simp[] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  metis_tac[SUBSET_TRANS,
            dfHelperPropsTheory.foldl_list_intersect_subset,
            list_intersect_single_subset,
            pred_setTheory.INTER_SUBSET,
            dfHelperPropsTheory.list_intersect_set]
QED

(* --- dom_extra_inv: initial state --- *)
Theorem dom_extra_init[local]:
  !fn.
    wf_function fn ==>
    let st0 = init_df_state (fn_labels fn)
                (MAP (\bb. bb.bb_label) fn.fn_blocks) in
    let st0' = case OPTION_MAP (\l. (l,[l])) (fn_entry_label fn) of
                 NONE => st0
               | SOME (lbl,v) =>
                   st0 with ds_boundary := st0.ds_boundary |+ (lbl,v) in
    dom_extra_inv fn st0'
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM, dom_extra_inv_def] >>
  (* Helper: at init, all boundaries = fn_labels fn *)
  `!lbl v. FLOOKUP (init_df_state (fn_labels fn)
     (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary lbl = SOME v ==>
     v = fn_labels fn` by
    (rw[dfAnalyzeDefsTheory.init_df_state_def] >>
     imp_res_tac dfAnalyzeProofsTheory.foldl_init_flookup >> fs[]) >>
  (* Helper: at init, all fn_labels have boundary entries *)
  `!lbl. MEM lbl (fn_labels fn) ==>
   lbl IN FDOM (init_df_state (fn_labels fn)
     (MAP (\bb. bb.bb_label) fn.fn_blocks)).ds_boundary` by
    (rw[dfAnalyzeDefsTheory.init_df_state_def,
        venomInstTheory.fn_labels_def] >>
     rw[foldl_fupdate_fdom]) >>
  Cases_on `fn_entry_label fn` >> simp[]
  >- ((* No entry — E0 from helper, E1,E2 vacuous, E3: joined ⊆ fn_labels *)
      rpt conj_tac >> TRY (rpt gen_tac >> strip_tac >> res_tac >> rw[] >>
      metis_tac[dom_joined_subset_fn_labels]))
  >> (* SOME x — E0 already solved by simp[], 3 remaining: E1, E2, E3 *)
  `MEM x (fn_labels fn)` by metis_tac[fn_entry_mem_fn_labels] >>
  rpt conj_tac
  >- ((* E1: entry boundary = [x], so set [x] ⊆ {x} *)
      rw[FLOOKUP_UPDATE] >> rw[pred_setTheory.SUBSET_DEF])
  >- ((* E2: entry ∈ every boundary *)
      rpt gen_tac >> strip_tac >>
      Cases_on `x = lbl` >> gvs[FLOOKUP_UPDATE, MEM] >>
      res_tac >> fs[])
  >> (* E3: joined ⊆ boundary for non-entry blocks *)
  rpt gen_tac >> strip_tac >>
  fs[FLOOKUP_UPDATE] >>
  res_tac >> fs[] >>
  metis_tac[dom_joined_subset_fn_labels]
QED

(* dom_joined only depends on ds_boundary, not ds_inst *)
Triviality dom_joined_inst_irrelevant:
  !fn st inst lbl.
    dom_joined fn (st with ds_inst := inst) lbl = dom_joined fn st lbl
Proof
  rw[dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM, dfAnalyzeDefsTheory.df_boundary_def]
QED

(* dom_extra_inv only depends on ds_boundary, not ds_inst *)
Triviality dom_extra_inv_inst_irrelevant:
  !fn st inst.
    dom_extra_inv fn (st with ds_inst := inst) = dom_extra_inv fn st
Proof
  rw[dom_extra_inv_def, dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM,
     dfAnalyzeDefsTheory.df_boundary_def]
QED

(* dom_joined monotonicity for bare record form (no st with) *)
Triviality dom_joined_boundary_mono_bare:
  !fn st lbl new_bnd l.
    set new_bnd SUBSET set (df_boundary (fn_labels fn) st lbl) ==>
    set (dom_joined fn
      <|ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|> l) SUBSET
    set (dom_joined fn st l)
Proof
  rpt strip_tac >>
  `dom_joined fn <|ds_boundary := st.ds_boundary |+ (lbl, new_bnd)|> l =
   dom_joined fn (st with ds_boundary := st.ds_boundary |+ (lbl, new_bnd)) l`
    by (irule dom_joined_boundary_only >> simp[]) >>
  rw[] >> irule dom_joined_boundary_mono >> simp[]
QED

(* Same ds_boundary implies same dom_extra_inv *)
Triviality dom_extra_inv_boundary_eq:
  !fn st1 st2. st1.ds_boundary = st2.ds_boundary ==>
    (dom_extra_inv fn st1 <=> dom_extra_inv fn st2)
Proof
  rw[dom_extra_inv_def] >>
  `dom_joined fn st1 = dom_joined fn st2` by
    (rw[FUN_EQ_THM] >> irule dom_joined_boundary_only >> simp[]) >>
  fs[]
QED

(* KEY HELPER: updating one boundary entry preserves dom_extra_inv *)
Triviality dom_extra_inv_boundary_update:
  !fn st lbl new_bdy.
    dom_extra_inv fn st /\ MEM lbl (fn_labels fn) /\
    set new_bdy SUBSET set (df_boundary (fn_labels fn) st lbl) /\
    (!e. fn_entry_label fn = SOME e ==> MEM e new_bdy) /\
    (fn_entry_label fn = SOME lbl ==> set new_bdy SUBSET {lbl}) /\
    (fn_entry_label fn <> SOME lbl ==>
     set (dom_joined fn st lbl) SUBSET set new_bdy)
    ==>
    dom_extra_inv fn (st with ds_boundary := st.ds_boundary |+ (lbl, new_bdy))
Proof
  rw[dom_extra_inv_def] >> rpt strip_tac
  (* E0 solved by rw. Remaining: E1, E2, E3 *)
  >- ((* E1 *) Cases_on `lbl = e` >> gvs[FLOOKUP_UPDATE] >> res_tac >> fs[])
  >- ((* E2 *) Cases_on `lbl = lbl'` >> gvs[FLOOKUP_UPDATE] >> res_tac >> fs[])
  >> (* E3 *) Cases_on `lbl = lbl'` >> gvs[FLOOKUP_UPDATE]
  >- (irule SUBSET_TRANS >>
      qexists_tac `set (dom_joined fn st lbl)` >>
      reverse conj_tac >- fs[] >>
      mp_tac (Q.SPECL [`fn`, `st`, `lbl`, `lbl`, `new_bdy`]
               dom_joined_boundary_mono) >> simp[])
  >> irule SUBSET_TRANS >>
  qexists_tac `set (dom_joined fn st lbl')` >>
  conj_tac
  >- (mp_tac (Q.SPECL [`fn`, `st`, `lbl'`, `lbl`, `new_bdy`]
                dom_joined_boundary_mono) >> simp[])
  >> res_tac
QED

(* --- dom_extra_inv: preserved by process --- *)
Theorem dom_extra_preserved[local]:
  !fn lbl st.
    wf_function fn /\
    MEM lbl (fn_labels fn) /\
    dom_state_inv fn st /\
    dom_extra_inv fn st ==>
    let cfg = cfg_analyze fn in
    let all_labels = fn_labels fn in
    let entry_val = OPTION_MAP (\l. (l, [l])) (fn_entry_label fn) in
    let process = df_process_block Forward all_labels list_intersect
                    dom_transfer_inst dom_edge_transfer () entry_val cfg
                    fn.fn_blocks in
    dom_extra_inv fn (process lbl st)
Proof
  rpt strip_tac >>
  simp_tac std_ss [LET_THM] >>
  rewrite_tac[dom_process_eq] >> simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC
  >- ((* Unchanged: process = st *)
      gvs[]) >>
  (* Changed: boundary updated *)
  drule identity_fold_block_values >> strip_tac >>
  gvs[GSYM dom_joined_def] >>
  (* Apply the boundary update helper *)
  irule dom_extra_inv_boundary_update >> simp[] >>
  rpt conj_tac
  >- ((* 1. MEM e (list_intersect bdy joined) *)
      rpt strip_tac >>
      simp[dfHelperPropsTheory.list_intersect_mem] >>
      metis_tac[entry_mem_df_boundary, dom_joined_contains_entry])
  >- ((* 2. non-entry: joined ⊆ list_intersect(bdy, joined) *)
      rpt strip_tac >>
      simp[dfHelperPropsTheory.list_intersect_set,
           pred_setTheory.SUBSET_INTER] >>
      `lbl IN FDOM st.ds_boundary` by fs[dom_extra_inv_def] >>
      `?v. FLOOKUP st.ds_boundary lbl = SOME v` by
        fs[finite_mapTheory.FLOOKUP_DEF] >>
      simp[dfAnalyzeDefsTheory.df_boundary_def] >>
      fs[dom_extra_inv_def] >> res_tac)
  >- ((* 3. entry: list_intersect(bdy, joined) ⊆ {lbl} *)
      rpt strip_tac >>
      irule SUBSET_TRANS >>
      qexists_tac `set (df_boundary (fn_labels fn) st lbl)` >>
      simp[dfHelperPropsTheory.list_intersect_set, INTER_SUBSET] >>
      `lbl IN FDOM st.ds_boundary` by fs[dom_extra_inv_def] >>
      `?v. FLOOKUP st.ds_boundary lbl = SOME v` by
        fs[finite_mapTheory.FLOOKUP_DEF] >>
      simp[dfAnalyzeDefsTheory.df_boundary_def] >>
      fs[dom_extra_inv_def] >> res_tac >> fs[])
  >> (* 4. list_intersect(bdy, joined) ⊆ bdy — trivial *)
  simp[dfHelperPropsTheory.list_intersect_set, INTER_SUBSET]
QED

(* Pre-strip LETs from key local theorems — avoids repeated SIMP_RULE *)
val strip_let = SIMP_RULE std_ss [LET_THM];
val dom_inv_preserved' = strip_let dom_inv_preserved;
val dom_extra_preserved' = strip_let dom_extra_preserved;
val dom_measure_increases' = strip_let dom_measure_increases;
val dom_measure_bounded' = strip_let dom_measure_bounded;
val dom_init_state_inv' = strip_let dom_init_state_inv;
val dom_extra_init' = strip_let dom_extra_init;
val df_analyze_invariant_forward' =
  strip_let dfAnalyzeProofsTheory.df_analyze_invariant_forward;
val df_analyze_fixpoint_forward' =
  strip_let dfAnalyzeProofsTheory.df_analyze_fixpoint_forward;
val df_process_deps_complete_fwd' =
  strip_let dfAnalyzeProofsTheory.df_process_deps_complete_proof
  |> Q.SPEC `Forward`
  |> SIMP_RULE std_ss [dfAnalyzeDefsTheory.direction_case_def];

(* FOLDL that only touches ds_inst preserves ds_boundary *)
Triviality foldl_inst_only_boundary[local]:
  !lbls (f : 'a df_state -> string -> 'a df_state) acc.
    (!st lbl. (f st lbl).ds_boundary = st.ds_boundary) ==>
    (FOLDL f acc lbls).ds_boundary = acc.ds_boundary
Proof
  Induct >> simp[]
QED

(* df_populate_inst preserves ds_boundary *)
Triviality populate_inst_ds_boundary[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st.
    (df_populate_inst dir bottom join transfer edge_transfer ctx
       entry_val cfg bbs lbls st).ds_boundary = st.ds_boundary
Proof
  rpt gen_tac >>
  simp[dfAnalyzeDefsTheory.df_populate_inst_def] >>
  irule foldl_inst_only_boundary >>
  simp[LET_THM] >>
  rpt gen_tac >> pairarg_tac >> simp[]
QED

(* If Q only depends on ds_boundary and Q holds before populate_inst,
   then Q holds after. *)
Triviality populate_inst_boundary_inv[local]:
  !dir bottom join transfer edge_transfer ctx entry_val cfg bbs lbls st Q.
    (!s1 s2. s1.ds_boundary = s2.ds_boundary ==> (Q s1 <=> Q s2)) ==>
    Q st ==>
    Q (df_populate_inst dir bottom join transfer edge_transfer ctx
         entry_val cfg bbs lbls st)
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`st`,
    `df_populate_inst dir bottom join transfer edge_transfer ctx
       entry_val cfg bbs lbls st`] mp_tac) >>
  simp[populate_inst_ds_boundary]
QED

(* dom_extra_inv only depends on ds_boundary *)
Triviality dom_extra_inv_boundary_only[local]:
  !fn s1 s2. s1.ds_boundary = s2.ds_boundary ==>
    (dom_extra_inv fn s1 <=> dom_extra_inv fn s2)
Proof
  rw[dom_extra_inv_def, dom_joined_def,
     dfAnalyzeDefsTheory.df_joined_val_def, LET_THM,
     dfAnalyzeDefsTheory.direction_case_def,
     dfAnalyzeDefsTheory.df_boundary_def]
QED

(* dom_state_inv_bdy only depends on ds_boundary *)
Triviality dom_state_inv_bdy_boundary_only[local]:
  !fn s1 s2. s1.ds_boundary = s2.ds_boundary ==>
    (dom_state_inv_bdy fn s1 <=> dom_state_inv_bdy fn s2)
Proof
  rw[dom_state_inv_bdy_def, dfAnalyzeDefsTheory.df_boundary_def]
QED

(* --- Worklist result has dom_full_inv --- *)
Triviality dom_full_inv_worklist[local]:
  !fn.
    wf_function fn ==>
    let cfg = cfg_analyze fn in
    let bbs = fn.fn_blocks in
    let lbls = MAP (\bb. bb.bb_label) bbs in
    let st0 = init_df_state (fn_labels fn) lbls in
    let st0' =
      (case OPTION_MAP (\lbl. (lbl, [lbl])) (fn_entry_label fn) of
         NONE => st0
       | SOME (lbl, v) =>
           st0 with ds_boundary := st0.ds_boundary |+ (lbl, v)) in
    let process =
      df_process_block Forward (fn_labels fn) list_intersect
        dom_transfer_inst dom_edge_transfer ()
        (OPTION_MAP (\lbl. (lbl,[lbl])) (fn_entry_label fn))
        cfg bbs in
    let changed =
      (\lbl old new.
         df_boundary (fn_labels fn) new lbl <>
         df_boundary (fn_labels fn) old lbl) in
    let deps = cfg_succs_of cfg in
    let wl0 = cfg.cfg_dfs_pre in
    dom_full_inv fn (SND (wl_iterate changed process deps wl0 st0'))
Proof
  rpt strip_tac >>
  simp_tac std_ss [LET_THM] >>
  mp_tac (INST_TYPE [alpha |-> ``:string list``, beta |-> ``:unit``]
    df_analyze_invariant_forward'
    |> Q.SPECL [`fn_labels fn`, `list_intersect`, `dom_transfer_inst`,
                `dom_edge_transfer`, `()`,
                `OPTION_MAP (\lbl. (lbl, [lbl])) (fn_entry_label fn)`,
                `fn`, `dom_measure fn`, `dom_measure_bound fn`,
                `dom_full_inv fn`]) >>
  impl_tac
  >- (fs[] >> rpt conj_tac
      >- (rpt strip_tac >>
          `dom_state_inv fn st` by fs[dom_full_inv_def] >>
          metis_tac[dom_measure_increases'])
      >- (rpt strip_tac >> fs[dom_full_inv_def] >>
          metis_tac[dom_inv_preserved', dom_extra_preserved'])
      >- (mp_tac (Q.SPEC `fn` dom_init_state_inv') >>
          mp_tac (Q.SPEC `fn` dom_extra_init') >>
          simp[dom_full_inv_def] >>
          Cases_on `fn_entry_label fn` >> simp[])
      >- (rpt strip_tac >>
          `dom_state_inv fn x` by fs[dom_full_inv_def] >>
          metis_tac[dom_measure_bounded'])) >>
  simp_tac std_ss [LET_THM]
QED

val dom_full_inv_worklist' = SIMP_RULE std_ss [LET_THM] dom_full_inv_worklist;

(* --- dom_full_inv (boundary parts) at fixpoint --- *)
Theorem dom_full_inv_fixpoint[local]:
  !fn.
    wf_function fn ==>
    dom_state_inv_bdy fn (dom_fixpoint fn) /\
    dom_extra_inv fn (dom_fixpoint fn)
Proof
  gen_tac >> strip_tac >>
  mp_tac (Q.SPEC `fn` dom_full_inv_worklist') >> simp[] >> strip_tac >>
  fs[dom_full_inv_def] >>
  qpat_x_assum `dom_state_inv _ _`
    (strip_assume_tac o MATCH_MP dom_state_inv_imp_bdy) >>
  simp_tac std_ss [LET_THM, dominatorDefsTheory.dom_fixpoint_def,
                   dfAnalyzeDefsTheory.df_analyze_def,
                   dfAnalyzeDefsTheory.direction_case_def] >>
  (* df_populate_inst preserves ds_boundary, so boundary-only invs transfer *)
  qmatch_goalsub_abbrev_tac `df_populate_inst _ _ _ _ _ _ _ _ _ _ wl_res` >>
  `(df_populate_inst Forward (fn_labels fn) list_intersect dom_transfer_inst
       dom_edge_transfer ()
       (OPTION_MAP (\lbl. (lbl,[lbl])) (fn_entry_label fn))
       (cfg_analyze fn) fn.fn_blocks
       (MAP (\bb. bb.bb_label) fn.fn_blocks)
       wl_res).ds_boundary = wl_res.ds_boundary`
    by simp[populate_inst_ds_boundary] >>
  metis_tac[dom_state_inv_bdy_boundary_only, dom_extra_inv_boundary_only]
QED

(* --- Fixpoint: combine convergence witnesses --- *)
Theorem dom_fixpoint_is_fixpoint[local]:
  !fn.
    wf_function fn ==>
    let cfg = cfg_analyze fn in
    let all_labels = fn_labels fn in
    let entry_val = OPTION_MAP (\lbl. (lbl, [lbl])) (fn_entry_label fn) in
    let process = df_process_block Forward all_labels list_intersect
                    dom_transfer_inst dom_edge_transfer () entry_val cfg
                    fn.fn_blocks in
    let all_lbls = cfg.cfg_dfs_pre in
    is_fixpoint process all_lbls (dom_fixpoint fn)
Proof
  rpt strip_tac >>
  simp_tac std_ss [LET_THM, dominatorDefsTheory.dom_fixpoint_def] >>
  irule df_analyze_fixpoint_forward' >>
  conj_tac >- fs[] >>
  conj_tac
  >- (qexistsl_tac [`dom_state_inv fn`,
                     `dom_measure_bound fn`,
                     `dom_measure fn`] >>
      rpt conj_tac
      >- metis_tac[dom_measure_bounded]
      >- metis_tac[dom_inv_preserved]
      >- metis_tac[dom_measure_increases]
      >- metis_tac[dom_init_state_inv])
  >> match_mp_tac df_process_deps_complete_fwd' >>
  rw[dfHelperPropsTheory.list_intersect_absorption] >>
  metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]
QED

val dom_fixpoint_is_fixpoint' = strip_let dom_fixpoint_is_fixpoint;

Theorem dom_fixpoint_inv[local]:
  !fn.
    wf_function fn ==>
    dom_state_inv_bdy fn (dom_fixpoint fn)
Proof
  metis_tac[dom_full_inv_fixpoint]
QED

(* ========================================================================
   Bridge lemmas: connect public API to internal fixpoint state
   ======================================================================== *)

(* cfg_dfs_pre membership implies fn_labels membership *)
Triviality cfg_dfs_pre_mem_fn_labels:
  !fn lbl. wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
           MEM lbl (fn_labels fn)
Proof
  rpt strip_tac >>
  irule cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels >>
  `set (cfg_analyze fn).cfg_dfs_pre =
   {lbl | cfg_reachable_of (cfg_analyze fn) lbl}` by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_reachable_sets] >>
  fs[pred_setTheory.EXTENSION, pred_setTheory.GSPECIFICATION]
QED

(* dom_sets_of extracts boundary values for each label *)
Theorem dom_sets_lookup[local]:
  !fn lbl.
    wf_function fn /\ MEM lbl (fn_labels fn) ==>
    FLOOKUP (dom_sets_of fn (dom_fixpoint fn)) lbl =
    SOME (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl)
Proof
  rpt strip_tac >>
  simp[dominatorDefsTheory.dom_sets_of_def, LET_THM] >>
  irule foldl_fupdate_flookup >>
  fs[venomWfTheory.wf_function_def]
QED

(* Bridge: fmap_lookup_list on da_dominators = df_boundary at fixpoint *)
Triviality dom_lookup_boundary:
  !fn cfg lbl.
    wf_function fn /\ cfg = cfg_analyze fn /\ MEM lbl (fn_labels fn) ==>
    fmap_lookup_list (dom_analyze cfg fn).da_dominators lbl =
    df_boundary (fn_labels fn) (dom_fixpoint fn) lbl
Proof
  rpt strip_tac >>
  simp[dominatorDefsTheory.dom_analyze_def, LET_THM,
       cfgDefsTheory.fmap_lookup_list_def] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  simp[dominatorDefsTheory.dom_sets_of_def, LET_THM] >>
  `FLOOKUP (FOLDL (\m lbl. m |+ (lbl, df_boundary (fn_labels fn)
      (dom_fixpoint fn) lbl)) FEMPTY (fn_labels fn)) lbl =
   SOME (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl)` by
    (irule foldl_fupdate_flookup >> fs[]) >>
  simp[]
QED

(* At the fixpoint, boundary(lbl) ⊆ joined(lbl) *)
Theorem dom_fixpoint_boundary_subset[local]:
  !fn lbl.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    set (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl) SUBSET
    set (dom_joined fn (dom_fixpoint fn) lbl)
Proof
  rpt strip_tac >>
  `MEM lbl (fn_labels fn)` by metis_tac[cfg_dfs_pre_mem_fn_labels] >>
  (* Get fixpoint equation: process lbl st = st *)
  `is_fixpoint
     (df_process_block Forward (fn_labels fn) list_intersect
        dom_transfer_inst dom_edge_transfer ()
        (OPTION_MAP (\lbl. (lbl,[lbl])) (fn_entry_label fn))
        (cfg_analyze fn) fn.fn_blocks)
     (cfg_analyze fn).cfg_dfs_pre (dom_fixpoint fn)` by
    metis_tac[dom_fixpoint_is_fixpoint'] >>
  fs[worklistDefsTheory.is_fixpoint_def] >>
  first_x_assum (qspec_then `lbl` mp_tac) >> simp[] >>
  (* Use bridge lemma instead of raw df_process_block_def *)
  rewrite_tac[dom_process_eq] >> simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  drule identity_fold_block_values >> strip_tac >> gvs[] >>
  (* At fixpoint: IF branch must be true (otherwise contradiction) *)
  IF_CASES_TAC >> gvs[]
  >- ((* list_intersect bdy joined = bdy => set bdy ⊆ set joined *)
      `set (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl) =
       set (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl) INTER
       set (dom_joined fn (dom_fixpoint fn) lbl)` by
        metis_tac[dfHelperPropsTheory.list_intersect_set] >>
      fs[pred_setTheory.INTER_SUBSET_EQN])
  >> (* False branch: update = identity => contradiction *)
  strip_tac >>
  gvs[dfAnalyzeDefsTheory.df_state_component_equality] >>
  imp_res_tac fupdate_eq_self_flookup >>
  fs[dfAnalyzeDefsTheory.df_boundary_def] >>
  Cases_on `FLOOKUP (dom_fixpoint fn).ds_boundary lbl` >> gvs[]
QED

(* ========================================================================
   Master bridge: connects da_dominators to df_boundary + dom_state_inv
   ======================================================================== *)

(* For any label in fn_labels: da_dominators lookup = df_boundary,
   and boundary invariants hold at the fixpoint. *)
Triviality dom_bridge:
  !fn lbl.
    wf_function fn /\ MEM lbl (fn_labels fn) ==>
    fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl =
      df_boundary (fn_labels fn) (dom_fixpoint fn) lbl /\
    dom_state_inv_bdy fn (dom_fixpoint fn) /\
    dom_extra_inv fn (dom_fixpoint fn)
Proof
  metis_tac[dom_lookup_boundary, dom_fixpoint_inv,
            dom_full_inv_fixpoint]
QED

(* Shorthand: dom set of lbl = boundary at fixpoint *)
Triviality dom_set_eq:
  !fn lbl.
    wf_function fn /\ MEM lbl (fn_labels fn) ==>
    set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl) =
    set (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl)
Proof
  metis_tac[dom_bridge]
QED

(* At fixpoint, FLOOKUP is SOME for all fn_labels *)
Triviality dom_fixpoint_flookup_some:
  !fn lbl.
    wf_function fn /\ MEM lbl (fn_labels fn) ==>
    ?v. FLOOKUP (dom_fixpoint fn).ds_boundary lbl = SOME v
Proof
  rpt strip_tac >>
  `dom_extra_inv fn (dom_fixpoint fn)` by
    metis_tac[dom_full_inv_fixpoint] >>
  fs[dom_extra_inv_def, finite_mapTheory.FLOOKUP_DEF]
QED

(* At fixpoint, df_boundary for entry = {entry} *)
Triviality dom_fixpoint_entry_boundary:
  !fn e.
    wf_function fn /\ fn_entry_label fn = SOME e ==>
    set (df_boundary (fn_labels fn) (dom_fixpoint fn) e) = {e}
Proof
  rpt strip_tac >>
  `dom_extra_inv fn (dom_fixpoint fn)` by
    metis_tac[dom_full_inv_fixpoint] >>
  `MEM e (fn_labels fn)` by metis_tac[fn_entry_mem_fn_labels] >>
  `?v. FLOOKUP (dom_fixpoint fn).ds_boundary e = SOME v` by
    metis_tac[dom_fixpoint_flookup_some] >>
  simp[dfAnalyzeDefsTheory.df_boundary_def] >>
  `set v SUBSET {e}` by (fs[dom_extra_inv_def] >> res_tac) >>
  `MEM e v` by (fs[dom_extra_inv_def] >> res_tac) >>
  fs[pred_setTheory.EXTENSION, pred_setTheory.SUBSET_DEF] >>
  metis_tac[]
QED

(* At fixpoint, entry is in every label's boundary *)
Triviality dom_fixpoint_entry_in_boundary:
  !fn e lbl.
    wf_function fn /\ fn_entry_label fn = SOME e /\
    MEM lbl (fn_labels fn) ==>
    MEM e (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl)
Proof
  rpt strip_tac >>
  `dom_extra_inv fn (dom_fixpoint fn)` by
    metis_tac[dom_full_inv_fixpoint] >>
  `?v. FLOOKUP (dom_fixpoint fn).ds_boundary lbl = SOME v` by
    metis_tac[dom_fixpoint_flookup_some] >>
  simp[dfAnalyzeDefsTheory.df_boundary_def] >>
  fs[dom_extra_inv_def] >> res_tac
QED

(* FOLDL list_intersect membership iff *)
Triviality foldl_list_intersect_mem_iff:
  !xs a v.
    MEM v (FOLDL list_intersect a xs) <=>
    MEM v a /\ EVERY (\x. MEM v x) xs
Proof
  Induct >> simp[dfHelperPropsTheory.list_intersect_mem] >>
  metis_tac[]
QED

(* FOLDL list_intersect set characterization *)
Triviality foldl_list_intersect_set:
  !xs a.
    set (FOLDL list_intersect a xs) =
    set a INTER BIGINTER (IMAGE set (set xs))
Proof
  simp[pred_setTheory.EXTENSION, foldl_list_intersect_mem_iff,
       listTheory.EVERY_MEM, pred_setTheory.IN_BIGINTER_IMAGE,
       listTheory.MEM_MAP]
QED

(* dom_joined set characterization for non-empty preds, non-entry *)
Triviality dom_joined_set:
  !fn st lbl.
    wf_function fn /\
    fn_entry_label fn <> SOME lbl /\
    cfg_preds_of (cfg_analyze fn) lbl <> [] ==>
    set (dom_joined fn st lbl) =
      set (fn_labels fn) INTER
      BIGINTER (IMAGE (\p. lbl INSERT set (df_boundary (fn_labels fn) st p))
                       (set (cfg_preds_of (cfg_analyze fn) lbl)))
Proof
  rpt strip_tac >>
  simp[dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM] >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> fs[] >>
  (* Eliminate entry_val case: fn_entry_label ≠ SOME lbl *)
  Cases_on `fn_entry_label fn` >> simp[] >>
  Cases_on `lbl = x` >> gvs[] >>
  simp[foldl_list_intersect_set, listTheory.LIST_TO_SET_MAP,
       pred_setTheory.IMAGE_IMAGE] >>
  simp[pred_setTheory.EXTENSION, pred_setTheory.IN_BIGINTER_IMAGE,
       pred_setTheory.IN_INTER,
       dominatorDefsTheory.dom_edge_transfer_def,
       cfgHelpersTheory.set_set_insert,
       dfHelperPropsTheory.list_intersect_mem,
       cfgHelpersTheory.mem_set_insert] >>
  simp[CONJ_ASSOC]
QED

(* At fixpoint for non-entry reachable: boundary = joined *)
Triviality dom_fixpoint_bdy_eq_joined:
  !fn lbl.
    wf_function fn /\
    MEM lbl (cfg_analyze fn).cfg_dfs_pre /\
    fn_entry_label fn <> SOME lbl ==>
    set (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl) =
    set (dom_joined fn (dom_fixpoint fn) lbl)
Proof
  rpt strip_tac >>
  `MEM lbl (fn_labels fn)` by metis_tac[cfg_dfs_pre_mem_fn_labels] >>
  irule pred_setTheory.SUBSET_ANTISYM >> conj_tac
  >- metis_tac[dom_fixpoint_boundary_subset]
  >> (* joined ⊆ bdy: from dom_extra_inv E3 *)
  `dom_extra_inv fn (dom_fixpoint fn)` by
    metis_tac[dom_full_inv_fixpoint] >>
  `?v. FLOOKUP (dom_fixpoint fn).ds_boundary lbl = SOME v` by
    metis_tac[dom_fixpoint_flookup_some] >>
  simp[dfAnalyzeDefsTheory.df_boundary_def] >>
  fs[dom_extra_inv_def]
QED

(* Reachable ⇒ MEM in fn_labels *)
Triviality reachable_mem_fn_labels:
  !fn lbl.
    wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl ==>
    MEM lbl (fn_labels fn)
Proof
  metis_tac[cfg_dfs_pre_mem_fn_labels,
            cfgCorrectnessProofTheory.cfg_analyze_reachable_sets_proof,
            pred_setTheory.EXTENSION, pred_setTheory.IN_GSPEC_IFF,
            listTheory.MEM, pred_setTheory.SPECIFICATION]
QED

(* Reachable ⇒ MEM in cfg_dfs_pre *)
Triviality reachable_mem_dfs_pre:
  !fn lbl.
    wf_function fn /\ cfg_reachable_of (cfg_analyze fn) lbl ==>
    MEM lbl (cfg_analyze fn).cfg_dfs_pre
Proof
  metis_tac[cfgCorrectnessProofTheory.cfg_analyze_reachable_sets_proof,
            pred_setTheory.EXTENSION, pred_setTheory.IN_GSPEC_IFF,
            listTheory.MEM, pred_setTheory.SPECIFICATION]
QED

(* For reachable labels: boundary ⊆ joined at fixpoint *)
Triviality dom_boundary_sub_joined:
  !fn lbl.
    wf_function fn /\ MEM lbl (cfg_analyze fn).cfg_dfs_pre ==>
    set (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl) SUBSET
    set (dom_joined fn (dom_fixpoint fn) lbl)
Proof
  metis_tac[dom_fixpoint_boundary_subset]
QED

(* df_boundary at fixpoint is always a subset of fn_labels *)
Triviality dom_fixpoint_bdy_sub_fn_labels:
  !fn lbl.
    wf_function fn /\ MEM lbl (fn_labels fn) ==>
    set (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl) SUBSET
    set (fn_labels fn)
Proof
  rpt strip_tac >>
  `dom_state_inv_bdy fn (dom_fixpoint fn)` by
    metis_tac[dom_full_inv_fixpoint] >>
  fs[dom_state_inv_bdy_def] >> res_tac >>
  fs[dfAnalyzeDefsTheory.df_boundary_def] >>
  Cases_on `FLOOKUP (dom_fixpoint fn).ds_boundary lbl` >> fs[] >>
  res_tac
QED

(* ========================================================================
   Category B: Fixpoint-derived properties
   ======================================================================== *)

Theorem dom_labels_bounded_proof:
  !fn cfg lbl d.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    MEM lbl (fn_labels fn) ==>
    let dom = dom_analyze cfg fn in
    MEM d (fmap_lookup_list dom.da_dominators lbl) ==>
    MEM d (fn_labels fn)
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  drule_all dom_bridge >> strip_tac >>
  fs[dom_state_inv_bdy_def, dfAnalyzeDefsTheory.df_boundary_def] >>
  Cases_on `FLOOKUP (dom_fixpoint fn).ds_boundary lbl` >> fs[] >>
  fs[pred_setTheory.SUBSET_DEF] >> metis_tac[]
QED

Theorem dom_self_proof:
  !fn cfg lbl.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    MEM lbl (fn_labels fn) ==>
    dominates (dom_analyze cfg fn) lbl lbl
Proof
  rpt strip_tac >> simp[dominatorDefsTheory.dominates_def] >>
  drule_all dom_bridge >> strip_tac >> simp[] >>
  fs[dom_state_inv_bdy_def]
QED

Theorem dom_entry_self_proof:
  !fn cfg bb.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    entry_block fn = SOME bb ==>
    set (fmap_lookup_list (dom_analyze cfg fn).da_dominators bb.bb_label) =
      {bb.bb_label}
Proof
  rpt strip_tac >> rw[] >>
  `fn_entry_label fn = SOME bb.bb_label` by
    simp[venomInstTheory.fn_entry_label_def] >>
  `MEM bb.bb_label (fn_labels fn)` by metis_tac[fn_entry_mem_fn_labels] >>
  drule_all dom_set_eq >> strip_tac >> simp[] >>
  metis_tac[dom_fixpoint_entry_boundary]
QED

Theorem dom_fixpoint_equation_proof:
  !fn cfg bb lbl.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of cfg lbl /\
    lbl <> bb.bb_label /\
    cfg_preds_of cfg lbl <> [] ==>
    let dom = dom_analyze cfg fn in
    set (fmap_lookup_list dom.da_dominators lbl) =
      {lbl} UNION
      BIGINTER (IMAGE (\p. set (fmap_lookup_list dom.da_dominators p))
                      (set (cfg_preds_of cfg lbl)))
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >> rw[] >>
  `fn_entry_label fn = SOME bb.bb_label` by
    simp[venomInstTheory.fn_entry_label_def] >>
  `fn_entry_label fn <> SOME lbl` by (strip_tac >> fs[]) >>
  `MEM lbl (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by metis_tac[reachable_mem_dfs_pre] >>
  `!p. MEM p (cfg_preds_of (cfg_analyze fn) lbl) ==>
       MEM p (fn_labels fn)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_pred_labels] >>
  (* LHS chain: da_dominators → df_boundary → dom_joined → set expression *)
  drule_all dom_set_eq >> strip_tac >> simp[] >>
  drule dom_fixpoint_bdy_eq_joined >> disch_then drule >>
  disch_then (fn th => simp[th]) >>
  drule dom_joined_set >>
  disch_then (qspecl_then [`dom_fixpoint fn`, `lbl`] mp_tac) >>
  simp[] >> disch_then (fn th => simp[th]) >>
  (* RHS: replace da_dominators with df_boundary for each pred *)
  `BIGINTER (IMAGE (\p. set (fmap_lookup_list
       (dom_analyze (cfg_analyze fn) fn).da_dominators p))
       (set (cfg_preds_of (cfg_analyze fn) lbl))) =
   BIGINTER (IMAGE (\p. set (df_boundary (fn_labels fn)
       (dom_fixpoint fn) p))
       (set (cfg_preds_of (cfg_analyze fn) lbl)))` by
    (AP_TERM_TAC >> simp[pred_setTheory.EXTENSION, pred_setTheory.IMAGE_DEF,
       pred_setTheory.GSPECIFICATION] >>
     rpt strip_tac >> eq_tac >> rpt strip_tac >> qexists_tac `p` >> simp[] >>
     res_tac >> drule_all dom_set_eq >> simp[]) >>
  pop_assum (fn th => rewrite_tac [th]) >>
  (* ⋂{lbl INSERT bdy(p)} = {lbl} ∪ ⋂{bdy(p)} *)
  `BIGINTER (IMAGE (\p. lbl INSERT
       set (df_boundary (fn_labels fn) (dom_fixpoint fn) p))
       (set (cfg_preds_of (cfg_analyze fn) lbl))) =
   {lbl} UNION BIGINTER (IMAGE (\p.
       set (df_boundary (fn_labels fn) (dom_fixpoint fn) p))
       (set (cfg_preds_of (cfg_analyze fn) lbl)))` by
    (simp[pred_setTheory.EXTENSION, pred_setTheory.IN_BIGINTER_IMAGE,
          pred_setTheory.IN_INSERT, pred_setTheory.IN_UNION] >>
     metis_tac[]) >>
  pop_assum (fn th => rewrite_tac [th]) >>
  (* fn_labels ∩ X = X because X ⊆ fn_labels *)
  ONCE_REWRITE_TAC [pred_setTheory.INTER_COMM] >>
  simp[GSYM pred_setTheory.SUBSET_INTER_ABSORPTION] >>
  irule pred_setTheory.SUBSET_TRANS >>
  Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> fs[] >>
  qexists_tac `set (df_boundary (fn_labels fn) (dom_fixpoint fn) h)` >>
  conj_tac >- simp[pred_setTheory.INTER_SUBSET] >>
  mp_tac (Q.SPECL [`fn`, `h`] dom_fixpoint_bdy_sub_fn_labels) >> simp[]
QED

Theorem dom_entry_dominates_all_proof:
  !fn cfg bb lbl.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of cfg lbl ==>
    dominates (dom_analyze cfg fn) bb.bb_label lbl
Proof
  rpt strip_tac >> rw[dominatorDefsTheory.dominates_def] >>
  `fn_entry_label fn = SOME bb.bb_label` by
    simp[venomInstTheory.fn_entry_label_def] >>
  `MEM lbl (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  drule_all dom_bridge >> strip_tac >> simp[] >>
  metis_tac[dom_fixpoint_entry_in_boundary]
QED

(* Characterize df_boundary after dom-processing a label.
   Reusable helper for dom_gfp and other process-level reasoning. *)
Triviality dom_process_boundary:
  !fn lbl st c.
    let process = df_process_block Forward (fn_labels fn) list_intersect
          dom_transfer_inst dom_edge_transfer ()
          (OPTION_MAP (\lbl. (lbl, [lbl])) (fn_entry_label fn))
          (cfg_analyze fn) fn.fn_blocks in
    df_boundary (fn_labels fn) (process lbl st) c =
      if c = lbl then
        list_intersect (df_boundary (fn_labels fn) st lbl)
                       (dom_joined fn st lbl)
      else df_boundary (fn_labels fn) st c
Proof
  rpt strip_tac >> simp_tac std_ss [LET_THM] >>
  rewrite_tac[dom_process_eq] >> simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  drule identity_fold_block_values >> strip_tac >> gvs[] >>
  IF_CASES_TAC >> gvs[]
  >- (Cases_on `c = lbl` >> simp[] >>
      rewrite_tac[GSYM dfAnalyzeDefsTheory.df_boundary_def] >> simp[])
  >> simp[dfAnalyzeDefsTheory.df_boundary_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `c = lbl` >> simp[]
QED

val dom_process_boundary' =
  SIMP_RULE std_ss [LET_THM] dom_process_boundary;

(* Greatest fixpoint property: any post-fixpoint of the dominator equation
   bounded by fn_labels is contained in the computed fixpoint.
   This is the key lemma enabling the backward direction of the
   path characterization. *)
(* Greatest fixpoint property: any post-fixpoint of the dominator equation
   bounded by fn_labels is contained in the computed fixpoint.

   Proof approach: df_analyze_invariant_forward with
   Q = dom_full_inv ∧ (∀c. X(c) ⊆ boundary(c)).
   Process preservation: dom_process_boundary' + list_intersect_set + dom_joined_set.
*)
Triviality dom_gfp:
  !fn X.
    wf_function fn /\
    (!c. set (X c) SUBSET set (fn_labels fn)) /\
    (!e. fn_entry_label fn = SOME e ==> set (X e) SUBSET {e}) /\
    (!c. MEM c (fn_labels fn) /\
         cfg_preds_of (cfg_analyze fn) c <> [] /\
         fn_entry_label fn <> SOME c ==>
         set (X c) SUBSET
           {c} UNION
           BIGINTER (IMAGE (\p. set (X p))
                           (set (cfg_preds_of (cfg_analyze fn) c)))) ==>
    !c. MEM c (fn_labels fn) ==>
    set (X c) SUBSET set (df_boundary (fn_labels fn) (dom_fixpoint fn) c)
Proof
  rpt strip_tac >>
  simp_tac std_ss [LET_THM, dominatorDefsTheory.dom_fixpoint_def] >>
  mp_tac (INST_TYPE [alpha |-> ``:string list``, beta |-> ``:unit``]
    df_analyze_invariant_forward'
    |> Q.SPECL [`fn_labels fn`, `list_intersect`, `dom_transfer_inst`,
                `dom_edge_transfer`, `()`,
                `OPTION_MAP (\lbl. (lbl, [lbl])) (fn_entry_label fn)`,
                `fn`, `dom_measure fn`, `dom_measure_bound fn`,
                `\st. dom_full_inv fn st /\
                  !c'. MEM c' (fn_labels fn) ==>
                  set (X c') SUBSET
                    set (df_boundary (fn_labels fn) st c')`]) >>
  impl_tac
  >- (simp_tac std_ss [LET_THM] >> simp[Excl "dom_full_inv_def"] >>
      rpt conj_tac
      (* 1. Measure *)
      >- (rpt strip_tac >>
          `dom_state_inv fn st` by
            (qpat_x_assum `dom_full_inv _ _` mp_tac >>
             simp[dom_full_inv_def]) >>
          metis_tac[dom_measure_increases'])
      (* 2. Process preserves Q *)
      >- (rpt strip_tac
          >- (fs[dom_full_inv_def] >>
              metis_tac[dom_inv_preserved', dom_extra_preserved'])
          >> simp[dom_process_boundary'] >>
          reverse (Cases_on `c' = lbl`)
          >- simp[]
          >> suspend "process_bdy")
      (* 3a. dom_full_inv init *)
      >- (mp_tac (Q.SPEC `fn` dom_init_state_inv') >>
          mp_tac (Q.SPEC `fn` dom_extra_init') >>
          simp[dom_full_inv_def] >>
          Cases_on `fn_entry_label fn` >> simp[])
      (* 3b. X ⊆ boundary init *)
      >- (Cases_on `fn_entry_label fn` >> simp[]
          >- (rpt strip_tac >>
              simp[dfAnalyzeDefsTheory.df_boundary_def,
                   dfAnalyzeDefsTheory.init_df_state_def] >>
              Cases_on `FLOOKUP (FOLDL (\m lbl. m |+ (lbl,fn_labels fn))
                         FEMPTY (MAP (\bb. bb.bb_label) fn.fn_blocks)) c'`
              >- simp[]
              >> drule dfAnalyzeProofsTheory.foldl_fempty_val >> simp[])
          >> rpt strip_tac >>
          simp[dfAnalyzeDefsTheory.df_boundary_def,
               dfAnalyzeDefsTheory.init_df_state_def,
               finite_mapTheory.FLOOKUP_UPDATE] >>
          Cases_on `c' = x` >> simp[] >>
          Cases_on `FLOOKUP (FOLDL (\m lbl. m |+ (lbl,fn_labels fn))
                        FEMPTY (MAP (\bb. bb.bb_label) fn.fn_blocks)) c'`
          >- simp[]
          >> drule dfAnalyzeProofsTheory.foldl_fempty_val >> simp[])
      (* 4. Measure bounded *)
      >> rpt strip_tac >>
      `dom_state_inv fn x` by
        (qpat_x_assum `dom_full_inv _ _` mp_tac >>
         simp[dom_full_inv_def]) >>
      metis_tac[dom_measure_bounded']) >>
  (* Bridge from SND(wl_iterate ...) to df_analyze via populate_inst *)
  (* df_analyze_invariant_forward gives Q(SND(wl_iterate...)).
     We only need the boundary part at the df_analyze level. *)
  disch_then (strip_assume_tac o SIMP_RULE std_ss []) >>
  simp_tac std_ss [LET_THM, dominatorDefsTheory.dom_fixpoint_def,
                   dfAnalyzeDefsTheory.df_analyze_def,
                   dfAnalyzeDefsTheory.direction_case_def] >>
  qmatch_goalsub_abbrev_tac `df_populate_inst _ _ _ _ _ _ _ _ _ _ wl_res` >>
  `(df_populate_inst Forward (fn_labels fn) list_intersect dom_transfer_inst
       dom_edge_transfer ()
       (OPTION_MAP (\lbl. (lbl,[lbl])) (fn_entry_label fn))
       (cfg_analyze fn) fn.fn_blocks
       (MAP (\bb. bb.bb_label) fn.fn_blocks)
       wl_res).ds_boundary = wl_res.ds_boundary`
    by simp[populate_inst_ds_boundary] >>
  `!c'. df_boundary (fn_labels fn)
          (df_populate_inst Forward (fn_labels fn) list_intersect
             dom_transfer_inst dom_edge_transfer ()
             (OPTION_MAP (\lbl. (lbl,[lbl])) (fn_entry_label fn))
             (cfg_analyze fn) fn.fn_blocks
             (MAP (\bb. bb.bb_label) fn.fn_blocks) wl_res) c' =
        df_boundary (fn_labels fn) wl_res c'` by
    simp[dfAnalyzeDefsTheory.df_boundary_def] >>
  rpt strip_tac >> res_tac >> fs[]
QED

Resume dom_gfp[process_bdy]:
  gvs[] >>
  simp[dfHelperPropsTheory.list_intersect_set, pred_setTheory.SUBSET_INTER] >>
  (* Remaining: set (X c') ⊆ set (dom_joined fn st c') *)
  Cases_on `fn_entry_label fn = SOME c'`
  >- (irule SUBSET_TRANS >> qexists `{c'}` >> conj_tac
      >- metis_tac[]
      >> simp[pred_setTheory.SUBSET_DEF] >>
      metis_tac[dom_joined_contains_self])
  >> Cases_on `cfg_preds_of (cfg_analyze fn) c' = []`
  >- (simp[dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM] >>
      Cases_on `fn_entry_label fn` >> simp[] >>
      Cases_on `c' = x` >> gvs[])
  >> drule_all dom_joined_set >> strip_tac >>
  simp[] >>
  irule SUBSET_TRANS >>
  qexists `{c'} UNION
    BIGINTER (IMAGE (\p. set (X p))
      (set (cfg_preds_of (cfg_analyze fn) c')))` >>
  conj_tac
  >- metis_tac[]
  >> (rw[pred_setTheory.SUBSET_DEF, pred_setTheory.IN_BIGINTER_IMAGE,
         pred_setTheory.IN_INSERT, pred_setTheory.IN_UNION] >>
      `MEM p (fn_labels fn)` by
        metis_tac[cfgAnalysisPropsTheory.cfg_analyze_pred_labels] >>
      `set (X p) SUBSET set (df_boundary (fn_labels fn) st p)` by res_tac >>
      fs[pred_setTheory.SUBSET_DEF])
QED

Finalise dom_gfp

(* LET-stripped versions of key exported theorems *)
val dom_labels_bounded' = strip_let dom_labels_bounded_proof;
val dom_fixpoint_equation' = strip_let dom_fixpoint_equation_proof;

(* Entry block existence from wf_function *)
Triviality wf_entry_block_exists[local]:
  wf_function fn ==> ?bb. entry_block fn = SOME bb
Proof
  simp[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def,
       venomInstTheory.entry_block_def] >>
  Cases_on `fn.fn_blocks` >> simp[]
QED

(* ========================================================================
   LRC path toolkit — reusable helpers for path-based dominator proofs
   ======================================================================== *)

(* LRC path decomposition: APPEND splits into two sub-paths *)
Triviality lrc_append[local]:
  !xs ys R (a:'a) c.
    LRC R (xs ++ ys) a c ==>
    ?b. LRC R xs a b /\ LRC R ys b c
Proof
  Induct_on `xs` >> simp[listTheory.LRC_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* LRC path construction: join two sub-paths *)
Triviality lrc_build[local]:
  !xs ys R (a:'a) b c. LRC R xs a b /\ LRC R ys b c ==> LRC R (xs ++ ys) a c
Proof
  Induct_on `xs` >> simp[listTheory.LRC_def] >>
  rpt strip_tac >> metis_tac[]
QED

(* Split LRC path at a member: gives prefix and suffix sub-paths *)
Triviality lrc_split_at[local]:
  !R (ls:'a list) a c x.
    LRC R ls a c /\ MEM x ls ==>
    ?l1 l2. ls = l1 ++ x :: l2 /\
            LRC R l1 a x /\ LRC R (x::l2) x c
Proof
  Induct_on `ls` >> simp[listTheory.LRC_def] >>
  rpt strip_tac >> gvs[]
  >- (qexistsl_tac [`[]`, `ls`] >> simp[listTheory.LRC_def] >> metis_tac[])
  >> first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`h::l1`, `l2`] >>
  simp[listTheory.LRC_def] >>
  fs[listTheory.LRC_def] >> metis_tac[]
QED

(* LRC path implies RTC *)
Triviality lrc_to_rtc[local]:
  !R (ls:'a list) x y. LRC R ls x y ==> R^* x y
Proof
  Induct_on `ls` >> simp[listTheory.LRC_def] >> rpt strip_tac >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >> metis_tac[]
QED

(* LRC path from entry implies reachable *)
Triviality lrc_to_reachable[local]:
  !fn bb ls lbl.
    wf_function fn /\
    entry_block fn = SOME bb /\
    LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) ls bb.bb_label lbl ==>
    cfg_reachable_of (cfg_analyze fn) lbl
Proof
  rpt strip_tac >>
  mp_tac cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability >>
  disch_then drule >> disch_then drule >>
  disch_then (qspec_then `lbl` mp_tac) >> simp[cfgDefsTheory.cfg_path_def] >>
  metis_tac[lrc_to_rtc]
QED

(* Reachable labels have an LRC path from entry *)
Triviality reachable_has_lrc_path[local]:
  !fn bb lbl.
    wf_function fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) lbl ==>
    ?ls. LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) ls bb.bb_label lbl
Proof
  rpt strip_tac >>
  drule_all cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability >> strip_tac >>
  fs[cfgDefsTheory.cfg_path_def, arithmeticTheory.RTC_eq_NRC,
     listTheory.NRC_LRC] >> metis_tac[]
QED

(* dom membership implies on every path from entry.
   d ∈ dom(c) ⟹ d = c ∨ MEM d ls for any LRC path ls from entry to c.
   Proof: SNOC induction. Base: dom(entry) = {entry}. Step: decompose
   SNOC x ls into LRC ls entry x and R x c. x is pred of c, so
   d ∈ dom(c)\{c} ⊆ ⋂dom(p) ⊆ dom(x). IH on shorter path ls. *)
Theorem dom_on_every_path:
  !fn bb ls c.
    wf_function fn /\
    entry_block fn = SOME bb /\
    LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) ls bb.bb_label c ==>
    !d. MEM d (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators c) ==>
    d = c \/ MEM d ls
Proof
  gen_tac >> gen_tac >>
  HO_MATCH_MP_TAC rich_listTheory.SNOC_INDUCT >>
  rpt strip_tac
  >- ((* Base: ls = [], so c = entry, dom = {entry} *)
      fs[listTheory.LRC_def] >>
      `set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators
              bb.bb_label) = {bb.bb_label}` by
        metis_tac[dom_entry_self_proof] >>
      gvs[pred_setTheory.EXTENSION])
  >> (* Step: ls = SNOC x ls'. Decompose into LRC ls' entry x, R x c *)
  `?mid. LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) ls bb.bb_label mid /\
         LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) [x] mid c` by
    metis_tac[lrc_append, listTheory.SNOC_APPEND] >>
  fs[listTheory.LRC_def] >> gvs[] >>
  rename [`LRC _ ls bb.bb_label mid`, `MEM c (cfg_succs_of _ mid)`] >>
  `MEM mid (cfg_preds_of (cfg_analyze fn) c)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  Cases_on `d = c` >- simp[listTheory.MEM_SNOC] >>
  simp[listTheory.MEM_SNOC] >>
  (* c is reachable: we already have LRC to SNOC mid ls *)
  `cfg_reachable_of (cfg_analyze fn) c` by
    metis_tac[lrc_to_reachable] >>
  (* c ≠ entry *)
  `c <> bb.bb_label` by
    (strip_tac >> gvs[] >>
     `set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators
             bb.bb_label) = {bb.bb_label}` by
       metis_tac[dom_entry_self_proof] >>
     fs[pred_setTheory.EXTENSION]) >>
  `cfg_preds_of (cfg_analyze fn) c <> []` by
    (Cases_on `cfg_preds_of (cfg_analyze fn) c` >> fs[]) >>
  (* Fixpoint equation: dom(c) = {c} ∪ ⋂dom(p) *)
  `set (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators c) =
   {c} UNION BIGINTER (IMAGE (\p. set (fmap_lookup_list
     (dom_analyze (cfg_analyze fn) fn).da_dominators p))
     (set (cfg_preds_of (cfg_analyze fn) c)))` by
    (mp_tac dom_fixpoint_equation' >>
     disch_then drule >> simp[] >> disch_then drule >>
     disch_then (qspec_then `c` mp_tac) >> simp[]) >>
  (* d ∈ ⋂dom(p) since d ≠ c *)
  `d IN BIGINTER (IMAGE (\p. set (fmap_lookup_list
     (dom_analyze (cfg_analyze fn) fn).da_dominators p))
     (set (cfg_preds_of (cfg_analyze fn) c)))` by
    (fs[pred_setTheory.EXTENSION] >> metis_tac[]) >>
  (* d ∈ dom(mid) in particular *)
  `MEM d (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators mid)` by
    (fs[pred_setTheory.IN_BIGINTER_IMAGE] >>
     first_x_assum (qspec_then `mid` mp_tac) >> simp[]) >>
  metis_tac[]
QED

(* Converse: d on every LRC path from entry to c ⟹ d ∈ dom(c).
   Proof: instantiate dom_gfp with X(n) = [d] if d on every path to n, else [].
   Entry: d on every path to entry ⟹ d = entry (by trivial path []).
   Post-fixpoint: d on every path to c, d ≠ c ⟹ d on every path to pred p
   (extend path to p by one step p→c to get path to c, apply hypothesis). *)
Theorem on_every_path_dom:
  !fn bb d c.
    wf_function fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) c /\
    MEM d (fn_labels fn) /\
    (!ls. LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))
              ls bb.bb_label c ==> d = c \/ MEM d ls) ==>
    MEM d (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators c)
Proof
  rpt strip_tac >>
  `MEM c (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `fn_entry_label fn = SOME bb.bb_label` by
    simp[venomInstTheory.fn_entry_label_def] >>
  (* Helper: d on every path to c', d ≠ c', p pred of c' ⟹ d on every path to p *)
  `!c' p. MEM p (cfg_preds_of (cfg_analyze fn) c') /\
          (!ls. LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))
                    ls bb.bb_label c' ==> d = c' \/ MEM d ls) /\
          d <> c' ==>
          (!ls. LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))
                    ls bb.bb_label p ==> d = p \/ MEM d ls)` by
    (rpt strip_tac >>
     `MEM c' (cfg_succs_of (cfg_analyze fn) p)` by
       metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
     first_x_assum (qspec_then `ls ++ [p]` mp_tac) >>
     impl_tac
     >- (irule lrc_build >> qexists_tac `p` >>
         simp[listTheory.LRC_def] >> metis_tac[])
     >> simp[listTheory.MEM_APPEND] >> metis_tac[]) >>
  mp_tac dom_gfp >>
  disch_then (qspecl_then [`fn`,
    `\n. if (!ls. LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))
                     ls bb.bb_label n ==> d = n \/ MEM d ls)
         then [d] else []`] mp_tac) >>
  simp[] >> impl_tac
  >- (rpt conj_tac
      (* 1. X(c) ⊆ fn_labels *)
      >- (rpt strip_tac >> IF_CASES_TAC >> simp[])
      (* 2. X(entry) ⊆ {entry}: trivial path [] gives d = entry *)
      >- (rpt strip_tac >> gvs[] >> IF_CASES_TAC >> simp[] >>
          first_x_assum (qspec_then `[]` mp_tac) >>
          simp[listTheory.LRC_def])
      (* 3. Post-fixpoint *)
      >> rpt strip_tac >> IF_CASES_TAC >> simp[] >>
      simp[pred_setTheory.SUBSET_DEF] >> rpt strip_tac >>
      Cases_on `d = c'` >- simp[] >>
      simp[pred_setTheory.IN_BIGINTER_IMAGE] >> rpt strip_tac >>
      `!ls. LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))
                ls bb.bb_label p ==> d = p \/ MEM d ls` by
        metis_tac[] >>
      simp[])
  >> disch_then (qspec_then `c` mp_tac) >> simp[] >>
  drule_all dom_bridge >> strip_tac >> simp[]
QED

(* Transitivity: a ∈ dom(b) ∧ b ∈ dom(c) ⟹ a ∈ dom(c).
   Any path to c goes through b (dom_on_every_path), split at b gives
   prefix to b, a is on that prefix (dom_on_every_path), so a is on
   every path to c, hence a ∈ dom(c) (on_every_path_dom). *)
Theorem dominates_trans_proof:
  !fn cfg a b c.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    cfg_reachable_of cfg c ==>
    let dom = dom_analyze cfg fn in
    dominates dom a b /\ dominates dom b c ==>
    dominates dom a c
Proof
  rpt strip_tac >> gvs[LET_THM] >>
  simp[dominatorDefsTheory.dominates_def] >> strip_tac >>
  drule wf_entry_block_exists >> strip_tac >>
  `MEM a (fn_labels fn)` by
    metis_tac[dom_labels_bounded', reachable_mem_fn_labels] >>
  irule on_every_path_dom >> simp[] >> rpt strip_tac >>
  (* b on path ls to c *)
  `b = c \/ MEM b ls` by metis_tac[dom_on_every_path]
  >- metis_tac[dom_on_every_path]
  (* split at b: prefix l1 to b, suffix from b *)
  >> drule_all lrc_split_at >> strip_tac >>
  (* a on prefix to b *)
  metis_tac[dom_on_every_path, listTheory.MEM_APPEND]
QED

Theorem dominates_antisym_proof:
  !fn cfg a b.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    cfg_reachable_of cfg a /\
    cfg_reachable_of cfg b ==>
    let dom = dom_analyze cfg fn in
    dominates dom a b /\ dominates dom b a ==>
    a = b
Proof
  rpt strip_tac >> gvs[LET_THM] >>
  simp[dominatorDefsTheory.dominates_def] >> strip_tac >>
  drule wf_entry_block_exists >> strip_tac >>
  CCONTR_TAC >>
  `?ls. LRC (\a' b'. MEM b' (cfg_succs_of (cfg_analyze fn) a'))
            ls bb.bb_label b` by metis_tac[reachable_has_lrc_path] >>
  (* Infinite descent on path length *)
  `!n ls. LENGTH ls = n /\
          LRC (\a' b'. MEM b' (cfg_succs_of (cfg_analyze fn) a'))
              ls bb.bb_label b ==> F` suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >>
  (* a on path ls' to b *)
  `MEM a ls'` by
    (`a = b \/ MEM a ls'` by metis_tac[dom_on_every_path] >> fs[]) >>
  (* split at a: prefix l1 to a *)
  drule_all lrc_split_at >> strip_tac >>
  (* b on prefix l1 to a *)
  `MEM b l1` by
    (`b = a \/ MEM b l1` by metis_tac[dom_on_every_path] >> fs[]) >>
  (* split prefix at b: l1a to b *)
  drule_all lrc_split_at >> strip_tac >>
  (* l1a is strictly shorter than ls' *)
  first_x_assum (qspec_then `LENGTH l1'` mp_tac) >>
  impl_tac >- (gvs[] >> simp[listTheory.LENGTH_APPEND]) >>
  disch_then (qspec_then `l1'` mp_tac) >> simp[]
QED

(* ========================================================================
   Category D: Idom computation — FOLDL map-building helpers
   ======================================================================== *)

(* General FOLDL map lookup: unconditional insertion *)
Triviality foldl_fupdate_lookup[local]:
  !labels (f:'a -> 'b) m k.
    ALL_DISTINCT labels ==>
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, f lbl)) m labels) k =
    if MEM k labels then SOME (f k) else FLOOKUP m k
Proof
  Induct_on `labels` >> simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `k = h` >> gvs[]
QED

(* General FOLDL map lookup: conditional insertion *)
Triviality foldl_fupdate_opt_lookup[local]:
  !labels (f:'a -> 'b option) m k.
    ALL_DISTINCT labels ==>
    FLOOKUP (FOLDL (\m lbl. case f lbl of NONE => m
                             | SOME v => m |+ (lbl, v)) m labels) k =
    if (?v. MEM k labels /\ f k = SOME v) then f k else FLOOKUP m k
Proof
  Induct_on `labels` >> simp[] >>
  rpt strip_tac >> Cases_on `f h` >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `k = h` >> gvs[]
QED

(* FEMPTY corollaries — clean rewrites for FOLDL-built maps *)
Triviality foldl_fupdate_fempty[local]:
  !labels (f:'a -> 'b) k.
    ALL_DISTINCT labels /\ MEM k labels ==>
    FLOOKUP (FOLDL (\m lbl. m |+ (lbl, f lbl)) FEMPTY labels) k =
    SOME (f k)
Proof
  rpt strip_tac >> drule foldl_fupdate_lookup >>
  disch_then (qspecl_then [`f`, `FEMPTY`, `k`] mp_tac) >> simp[]
QED

Triviality foldl_fupdate_opt_fempty[local]:
  !labels (f:'a -> 'b option) k.
    ALL_DISTINCT labels /\ MEM k labels ==>
    FLOOKUP (FOLDL (\m lbl. case f lbl of NONE => m
                             | SOME v => m |+ (lbl, v)) FEMPTY labels) k =
    f k
Proof
  rpt strip_tac >> drule foldl_fupdate_opt_lookup >>
  disch_then (qspecl_then [`f`, `FEMPTY`, `k`] mp_tac) >>
  simp[] >> Cases_on `f k` >> simp[]
QED

(* dom_sets_of lookup *)
Triviality dom_sets_lookup_eq[local]:
  wf_function fn /\ MEM lbl (fn_labels fn) ==>
  fmap_lookup_list (dom_sets_of fn (dom_fixpoint fn)) lbl =
  df_boundary (fn_labels fn) (dom_fixpoint fn) lbl
Proof
  rpt strip_tac >>
  simp[dominatorDefsTheory.dom_sets_of_def, LET_THM,
       cfgDefsTheory.fmap_lookup_list_def] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  mp_tac (INST_TYPE [alpha |-> ``:string``, beta |-> ``:string list``]
    foldl_fupdate_lookup
    |> Q.SPECL [`fn_labels fn`,
       `\x. df_boundary (fn_labels fn) (dom_fixpoint fn) x`,
       `FEMPTY`, `lbl`]) >>
  simp[]
QED

(* compute_idom lookup — bidirectional *)
Triviality compute_idom_lookup[local]:
  ALL_DISTINCT labels /\ MEM lbl labels ==>
  FLOOKUP (compute_idom order entry_opt dom_sets labels) lbl =
  compute_idom_for order entry_opt dom_sets lbl
Proof
  rpt strip_tac >>
  simp[dominatorDefsTheory.compute_idom_def] >>
  drule_all foldl_fupdate_opt_fempty >> simp[]
QED

(* QSORT preserves length and membership *)
Triviality qsort_length[local]:
  !R (xs:'a list). LENGTH (QSORT R xs) = LENGTH xs
Proof
  metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_LENGTH]
QED

Triviality qsort_mem[local]:
  !R (xs:'a list) x. MEM x (QSORT R xs) <=> MEM x xs
Proof
  metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ]
QED

(* Bridge: idom_of connects to compute_idom_for *)
Triviality idom_bridge[local]:
  wf_function fn /\ MEM lbl (fn_labels fn) ==>
  idom_of (dom_analyze (cfg_analyze fn) fn) lbl =
  compute_idom_for (cfg_analyze fn).cfg_dfs_post
    (fn_entry_label fn) (dom_sets_of fn (dom_fixpoint fn)) lbl
Proof
  rpt strip_tac >>
  simp[dominatorDefsTheory.idom_of_def,
       dominatorDefsTheory.dom_analyze_def, LET_THM] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  metis_tac[compute_idom_lookup]
QED

(* Bridge: dominated_of connects to compute_dominated *)
Triviality dominated_bridge[local]:
  wf_function fn /\ MEM n (fn_labels fn) ==>
  dominated_of (dom_analyze (cfg_analyze fn) fn) n =
  fmap_lookup_list
    (compute_dominated
      (compute_idom (cfg_analyze fn).cfg_dfs_post
        (fn_entry_label fn)
        (dom_sets_of fn (dom_fixpoint fn))
        (fn_labels fn))
      (fn_labels fn)) n
Proof
  simp[dominatorDefsTheory.dominated_of_def,
       dominatorDefsTheory.dom_analyze_def, LET_THM]
QED

(* Bridge: frontier_of connects to compute_df *)
Triviality frontier_bridge[local]:
  wf_function fn /\ MEM n (fn_labels fn) ==>
  frontier_of (dom_analyze (cfg_analyze fn) fn) n =
  fmap_lookup_list
    (compute_df (cfg_analyze fn)
      (compute_idom (cfg_analyze fn).cfg_dfs_post
        (fn_entry_label fn)
        (dom_sets_of fn (dom_fixpoint fn))
        (fn_labels fn))
      (cfg_analyze fn).cfg_dfs_post
      (LENGTH (fn_labels fn))) n
Proof
  simp[dominatorDefsTheory.frontier_of_def,
       dominatorDefsTheory.dom_analyze_def, LET_THM]
QED

Theorem idom_exists_proof:
  !fn cfg bb lbl.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of cfg lbl /\
    lbl <> bb.bb_label ==>
    ?d. idom_of (dom_analyze cfg fn) lbl = SOME d
Proof
  rpt strip_tac >> gvs[] >>
  `MEM lbl (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `fn_entry_label fn = SOME bb.bb_label` by
    simp[venomInstTheory.fn_entry_label_def] >>
  drule_all idom_bridge >> strip_tac >> simp[] >>
  simp[dominatorDefsTheory.compute_idom_for_def, LET_THM] >>
  `fmap_lookup_list (dom_sets_of fn (dom_fixpoint fn)) lbl =
   df_boundary (fn_labels fn) (dom_fixpoint fn) lbl` by
    metis_tac[dom_sets_lookup_eq] >>
  simp[] >>
  qabbrev_tac `doms = df_boundary (fn_labels fn) (dom_fixpoint fn) lbl` >>
  (* doms has >= 2 elements: lbl and bb.bb_label *)
  `MEM lbl doms /\ MEM bb.bb_label doms` by (
    unabbrev_all_tac >> conj_tac >| [
      drule_all dom_bridge >> strip_tac >> fs[dom_state_inv_bdy_def],
      metis_tac[dom_fixpoint_entry_in_boundary]]) >>
  (* sorted list has >= 2 elements since lbl and bb.bb_label are both in doms *)
  `2 <= LENGTH doms` by (
    `lbl <> bb.bb_label` by simp[] >>
    `?i. LENGTH doms = i` by metis_tac[] >>
    Cases_on `doms` >> fs[] >>
    Cases_on `t` >> fs[] >>
    fs[MEM] >> metis_tac[]) >>
  `2 <= LENGTH (QSORT (\a b. post_order_index (cfg_analyze fn).cfg_dfs_post a
    < post_order_index (cfg_analyze fn).cfg_dfs_post b) doms)` by
    metis_tac[qsort_length] >>
  Cases_on `QSORT (\a b. post_order_index (cfg_analyze fn).cfg_dfs_post a
    < post_order_index (cfg_analyze fn).cfg_dfs_post b) doms` >> fs[] >>
  Cases_on `t` >> fs[]
QED

(* dom_reachable: a dominator of a reachable node is itself reachable.
   d ∈ dom(c), reachable c ⟹ reachable d.
   Proof: get LRC path to c, dom_on_every_path puts d on it, split path at d. *)
Triviality dom_reachable[local]:
  !fn bb c d.
    wf_function fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) c /\
    MEM d (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators c) ==>
    cfg_reachable_of (cfg_analyze fn) d
Proof
  rpt strip_tac >>
  `?ls. LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x))
            ls bb.bb_label c` by metis_tac[reachable_has_lrc_path] >>
  `d = c \/ MEM d ls` by metis_tac[dom_on_every_path] >- gvs[] >>
  drule_all lrc_split_at >> strip_tac >> metis_tac[lrc_to_reachable]
QED

(* dom_chain: dominators of a node are totally ordered.
   If a and b both dominate c (and a ≠ b), then a dom b or b dom a.
   Proof by contradiction + strong induction on suffix length.
   Assume ¬(a dom b) ∧ ¬(b dom a). Then:
   - ∃ path Q to b avoiding a (contrapositive of on_every_path_dom)
   - ∃ path R to a avoiding b
   - Any path to c has b on it; split to get suffix S from b to c
   - Q ++ S is path to c; a must be on it; a ∉ Q; so a ∈ S
   - Split S at a to get suffix T from a to c
   - R ++ T is path to c; b must be on it; b ∉ R; so b ∈ T
   - Split T at b to get suffix U from b to c with LENGTH U < LENGTH S
   - Repeat (strong induction), eventually suffix has length 0 → contradiction *)
Theorem dom_chain:
  !fn bb a b c.
    wf_function fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) c /\
    MEM a (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators c) /\
    MEM b (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators c) ==>
    MEM a (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators b) \/
    MEM b (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators a)
Proof
  rpt strip_tac >>
  Cases_on `a = b` >- (
    disj1_tac >> gvs[] >>
    `MEM c (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
    `MEM a (fn_labels fn)` by metis_tac[dom_labels_bounded'] >>
    `dominates (dom_analyze (cfg_analyze fn) fn) a a` by
      metis_tac[dom_self_proof] >>
    fs[dominatorDefsTheory.dominates_def]) >>
  (* Sufficient to show by contradiction *)
  SPOSE_NOT_THEN strip_assume_tac >>
  (* Get entry block info *)
  `fn_entry_label fn = SOME bb.bb_label` by
    simp[venomInstTheory.fn_entry_label_def] >>
  `MEM c (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `MEM a (fn_labels fn)` by metis_tac[dom_labels_bounded'] >>
  `MEM b (fn_labels fn)` by metis_tac[dom_labels_bounded'] >>
  `cfg_reachable_of (cfg_analyze fn) a` by metis_tac[dom_reachable] >>
  `cfg_reachable_of (cfg_analyze fn) b` by metis_tac[dom_reachable] >>
  (* ¬(a dom b) → ∃ path to b avoiding a *)
  `?ls_q. LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x))
              ls_q bb.bb_label b /\ ~MEM a ls_q` by
    (SPOSE_NOT_THEN strip_assume_tac >>
     `MEM a (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators b)` by
       (irule on_every_path_dom >> simp[] >> rpt strip_tac >>
        `?ls. LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x))
                  ls bb.bb_label b` by metis_tac[reachable_has_lrc_path] >>
        first_x_assum (qspec_then `ls` mp_tac) >> simp[] >>
        metis_tac[]) >>
     metis_tac[]) >>
  (* ¬(b dom a) → ∃ path to a avoiding b *)
  `?ls_r. LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x))
              ls_r bb.bb_label a /\ ~MEM b ls_r` by
    (SPOSE_NOT_THEN strip_assume_tac >>
     `MEM b (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators a)` by
       (irule on_every_path_dom >> simp[] >> rpt strip_tac >>
        `?ls. LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x))
                  ls bb.bb_label a` by metis_tac[reachable_has_lrc_path] >>
        first_x_assum (qspec_then `ls` mp_tac) >> simp[] >>
        metis_tac[]) >>
     metis_tac[]) >>
  (* Get a path to c and split at b to get a suffix from b to c *)
  `?ls_p. LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x))
              ls_p bb.bb_label c` by metis_tac[reachable_has_lrc_path] >>
  `b <> c` by metis_tac[] >>
  `MEM b ls_p` by (
    qspecl_then [`fn`, `bb`, `ls_p`, `c`] mp_tac dom_on_every_path >>
    simp[] >> disch_then (qspec_then `b` mp_tac) >> simp[]) >>
  drule_all lrc_split_at >> strip_tac >>
  (* ls_p = l1 ++ b::l2 with LRC ... l1 bb.bb_label b and LRC ... (b::l2) b c *)
  rename [`ls_p = l1 ++ b::suffix`, `LRC _ (b::suffix) b c`] >>
  (* Now: induction on LENGTH suffix *)
  (* Key lemma: if we have a suffix from b to c of length n,
     we can find a shorter suffix → eventually length 0 → contradiction *)
  `!n. !sfx. LENGTH sfx = n ==>
    LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x)) (b::sfx) b c ==>
    F` suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >>
  (* Q ++ (b::sfx) is a path to c *)
  `LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x))
       (ls_q ++ b::sfx) bb.bb_label c` by
    metis_tac[lrc_build] >>
  (* a must be on this path *)
  `a = c \/ MEM a (ls_q ++ b::sfx)` by metis_tac[dom_on_every_path] >>
  `a <> c` by
    (strip_tac >> gvs[] >>
     metis_tac[dom_bridge, dom_state_inv_bdy_def]) >>
  `MEM a (ls_q ++ b::sfx)` by metis_tac[] >>
  `~MEM a ls_q` by metis_tac[] >>
  `MEM a (b::sfx)` by metis_tac[listTheory.MEM_APPEND] >>
  `a <> b` by metis_tac[] >>
  `MEM a sfx` by metis_tac[listTheory.MEM] >>
  (* Split b::sfx at a: get path from b to a, and suffix from a to c *)
  `?la lb. (b::sfx) = la ++ a::lb /\
    LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x)) la b a /\
    LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x)) (a::lb) a c` by
    metis_tac[lrc_split_at] >>
  (* R ++ (a::lb) is a path to c *)
  `LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x))
       (ls_r ++ a::lb) bb.bb_label c` by
    metis_tac[lrc_build] >>
  (* b must be on this path *)
  `b = c \/ MEM b (ls_r ++ a::lb)` by metis_tac[dom_on_every_path] >>
  `~MEM b ls_r` by metis_tac[] >>
  `MEM b (a::lb)` by metis_tac[listTheory.MEM_APPEND] >>
  `MEM b lb` by metis_tac[listTheory.MEM] >>
  (* Split a::lb at b: get suffix from b to c *)
  `?lc ld. (a::lb) = lc ++ b::ld /\
    LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x)) lc a b /\
    LRC (\x y. MEM y (cfg_succs_of (cfg_analyze fn) x)) (b::ld) b c` by
    metis_tac[lrc_split_at] >>
  (* LENGTH ld < LENGTH sfx *)
  (* b::sfx = la ++ a::lb, a::lb = lc ++ b::ld *)
  (* sfx = TL la ++ a::lb (if la = b::la', then sfx = la' ++ a::lb) *)
  (* lb = TL lc ++ b::ld (if lc = a::lc', then lb = lc' ++ b::ld) *)
  (* So LENGTH sfx = LENGTH la - 1 + 1 + LENGTH lb
                   = LENGTH la + LENGTH lb
     LENGTH lb = LENGTH lc - 1 + 1 + LENGTH ld
              = LENGTH lc + LENGTH ld
     LENGTH sfx = LENGTH la + LENGTH lc + LENGTH ld
     LENGTH ld ≤ LENGTH sfx, strictly if la or lc nonempty *)
  `LENGTH ld < LENGTH sfx` by (
    `la <> []` by (Cases_on `la` >> fs[]) >>
    `LENGTH (b::sfx) = LENGTH la + LENGTH (a::lb)` by
      metis_tac[listTheory.LENGTH_APPEND] >>
    `LENGTH (a::lb) = LENGTH lc + LENGTH (b::ld)` by
      metis_tac[listTheory.LENGTH_APPEND] >>
    Cases_on `la` >> fs[]) >>
  (* Apply IH with shorter suffix *)
  first_x_assum (qspec_then `LENGTH ld` mp_tac) >> simp[] >>
  metis_tac[]
QED

(* reachable_mem_dfs_post: reachable nodes are in dfs_post output *)
Triviality reachable_mem_dfs_post[local]:
  !fn bb lbl.
    wf_function fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) lbl ==>
    MEM lbl (cfg_analyze fn).cfg_dfs_post
Proof
  rpt strip_tac >>
  `MEM lbl (cfg_analyze fn).cfg_dfs_pre` by metis_tac[reachable_mem_dfs_pre] >>
  `set ((cfg_analyze fn).cfg_dfs_post) = set ((cfg_analyze fn).cfg_dfs_pre)` by (
    simp[cfgHelpersTheory.cfg_analyze_dfs_post,
         cfgHelpersTheory.cfg_analyze_dfs_pre] >>
    Cases_on `entry_block fn` >> fs[] >>
    metis_tac[cfgHelpersTheory.dfs_walks_same_output_set]) >>
  fs[pred_setTheory.EXTENSION]
QED

(* dom_post_order: dominators have higher DFS post-order index.
   If d strictly dominates lbl, then INDEX_OF lbl post < INDEX_OF d post.
   Proof: by contradiction. If INDEX_OF d <= INDEX_OF lbl, since d ≠ lbl
   we get INDEX_OF d < INDEX_OF lbl. Two cases:
   - d = entry: LAST of post = entry, so INDEX_OF entry = max. Contradiction.
   - d ≠ entry: dfs_post_walk_avoiding_path gives LRC path avoiding d.
     But dom_on_every_path says d is on every path. Contradiction. *)
Triviality dom_post_order[local]:
  !fn bb d lbl.
    wf_function fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) lbl /\
    MEM d (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl) /\
    d <> lbl ==>
    ?i j. INDEX_OF lbl (cfg_analyze fn).cfg_dfs_post = SOME i /\
          INDEX_OF d (cfg_analyze fn).cfg_dfs_post = SOME j /\
          i < j
Proof
  rpt strip_tac >>
  qabbrev_tac `succs = build_succs fn.fn_blocks` >>
  qabbrev_tac `post = (cfg_analyze fn).cfg_dfs_post` >>
  (* Establish post = SND(dfs_post_walk succs [] bb.bb_label) *)
  `post = SND (dfs_post_walk succs [] bb.bb_label)` by (
    unabbrev_all_tac >>
    simp[cfgHelpersTheory.cfg_analyze_dfs_post] >>
    Cases_on `entry_block fn` >> fs[]) >>
  (* ALL_DISTINCT post *)
  `ALL_DISTINCT post` by
    metis_tac[cfgHelpersTheory.dfs_post_walk_distinct_disj] >>
  (* Membership via dom_reachable + reachable_mem_dfs_post *)
  `cfg_reachable_of (cfg_analyze fn) d` by metis_tac[dom_reachable] >>
  `MEM lbl post /\ MEM d post` by
    metis_tac[reachable_mem_dfs_post, markerTheory.Abbrev_def] >>
  (* Contradiction argument *)
  SPOSE_NOT_THEN ASSUME_TAC >>
  `?i. INDEX_OF lbl post = SOME i` by
    (Cases_on `INDEX_OF lbl post` >> fs[INDEX_OF_eq_NONE]) >>
  `?j. INDEX_OF d post = SOME j` by
    (Cases_on `INDEX_OF d post` >> fs[INDEX_OF_eq_NONE]) >>
  `~(i < j)` by metis_tac[] >>
  `i <> j` by (
    CCONTR_TAC >> gvs[] >> fs[listTheory.INDEX_OF_eq_SOME]) >>
  `j < i` by simp[] >>
  Cases_on `d = bb.bb_label`
  >- ((* d = entry: entry is LAST of post, so j = max index *)
      `post <> [] /\ LAST post = d` by (
        gvs[] >>
        mp_tac (INST_TYPE [alpha |-> ``:string``]
                  cfgHelpersTheory.dfs_post_walk_entry_last
                |> Q.SPECL [`succs`, `[]`, `bb.bb_label`]) >> simp[]) >>
      mp_tac (INST_TYPE [alpha |-> ``:string``]
                cfgHelpersTheory.index_of_last_max
              |> Q.SPECL [`post`, `d`, `lbl`, `i`, `j`]) >> simp[])
  >- ((* d ≠ entry: avoiding path exists *)
      mp_tac (CONJUNCT1 cfgHelpersTheory.dfs_post_walk_avoiding_path) >>
      disch_then (qspecl_then [`succs`, `[]`, `bb.bb_label`,
                               `lbl`, `d`, `j`, `i`] mp_tac) >>
      impl_tac >- (fs[] >> metis_tac[]) >>
      strip_tac >>
      (* Convert fmap_lookup_list succs path to cfg_succs_of path *)
      `cfg_succs_of (cfg_analyze fn) = fmap_lookup_list succs` by
        (unabbrev_all_tac >> simp[cfgHelpersTheory.cfg_analyze_succs]) >>
      `LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) ls bb.bb_label lbl` by
        (qpat_x_assum `LRC _ ls _ _` mp_tac >> rw[]) >>
      mp_tac dom_on_every_path >>
      disch_then (qspecl_then [`fn`, `bb`, `ls`, `lbl`] mp_tac) >>
      simp[] >> metis_tac[])
QED

(* PART preserves ALL_DISTINCT *)
Triviality part_all_distinct[local]:
  !P L l1 l2 a1 a2.
    (a1,a2) = PART P L l1 l2 /\ ALL_DISTINCT (L ++ l1 ++ l2) ==>
    ALL_DISTINCT (a1 ++ a2)
Proof
  Induct_on `L` >> simp[sortingTheory.PART_DEF] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `P h` >> gvs[] >>
  first_x_assum irule
  >- (qexistsl_tac [`P`, `h::l1`, `l2`] >> simp[] >>
      fs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM] >> metis_tac[])
  >> qexistsl_tac [`P`, `l1`, `h::l2`] >> simp[] >>
     fs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM] >> metis_tac[]
QED

(* ALL_DISTINCT (MAP f) transfers from superset to subset *)
Triviality all_distinct_map_sub[local]:
  !f l1 t. ALL_DISTINCT (MAP f t) /\ ALL_DISTINCT l1 /\
           (!x. MEM x l1 ==> MEM x t) ==>
           ALL_DISTINCT (MAP f l1)
Proof
  rpt strip_tac >> irule listTheory.ALL_DISTINCT_MAP_INJ >> simp[] >>
  rpt strip_tac >> SPOSE_NOT_THEN ASSUME_TAC >>
  `MEM x t /\ MEM y t` by metis_tac[] >>
  `?i. i < LENGTH t /\ EL i t = x` by metis_tac[listTheory.MEM_EL] >>
  `?j. j < LENGTH t /\ EL j t = y` by metis_tac[listTheory.MEM_EL] >>
  `EL i (MAP f t) = f x` by simp[listTheory.EL_MAP] >>
  `EL j (MAP f t) = f y` by simp[listTheory.EL_MAP] >>
  `i < LENGTH (MAP f t) /\ j < LENGTH (MAP f t)` by simp[] >>
  `i = j` by metis_tac[listTheory.ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

(* f h ≠ f x when h::t has ALL_DISTINCT (MAP f) and x ∈ t *)
Triviality ad_map_head_neq[local]:
  !f h t x. ALL_DISTINCT (MAP f (h::t)) /\ MEM x t ==> f h <> f x
Proof
  simp[listTheory.MAP, listTheory.ALL_DISTINCT] >>
  rpt strip_tac >> gvs[] >> metis_tac[listTheory.MEM_MAP_f]
QED

(* QSORT with strict < on distinct-image elements produces a SORTED list.
   Key: on distinct elements, ¬(y < h) ∧ y ≠ h ⟹ h < y (trichotomy). *)
Triviality qsort_strict_sorted[local]:
  !(f:'a -> num) L. ALL_DISTINCT (MAP f L) ==>
        SORTED (\a b. f a < f b) (QSORT (\a b. f a < f b) L)
Proof
  gen_tac >>
  `!ord L. ord = (\a b. f a < f b) ==> ALL_DISTINCT (MAP f L) ==>
   SORTED ord (QSORT ord L)` suffices_by simp[] >>
  ho_match_mp_tac sortingTheory.QSORT_IND >> rpt strip_tac >> gvs[]
  >- simp[sortingTheory.QSORT_DEF]
  >> simp[sortingTheory.QSORT_DEF] >> pairarg_tac >> simp[]
  (* Partition membership and properties *)
  >> `(l1,l2) = PART (\a. f a < f h) t [] []` by fs[sortingTheory.PARTITION_DEF]
  >> `!x. MEM x (l1 ++ l2) <=> MEM x t` by
       (imp_res_tac sortingTheory.PART_MEM >> fs[])
  >> `!x. MEM x l1 ==> f x < f h` by
       (imp_res_tac sortingTheory.PARTs_HAVE_PROP >> fs[])
  >> `!x. MEM x l2 ==> ~(f x < f h)` by
       (imp_res_tac sortingTheory.PARTs_HAVE_PROP >> fs[])
  (* ALL_DISTINCT for partition halves *)
  >> `ALL_DISTINCT (l1 ++ l2)` by (
       `ALL_DISTINCT t` by metis_tac[listTheory.ALL_DISTINCT_MAP] >>
       `ALL_DISTINCT (t ++ [] ++ [])` by simp[] >>
       metis_tac[part_all_distinct])
  >> `ALL_DISTINCT l1 /\ ALL_DISTINCT l2` by
       fs[listTheory.ALL_DISTINCT_APPEND]
  >> `ALL_DISTINCT (MAP f l1)` by
       metis_tac[all_distinct_map_sub, listTheory.MEM_APPEND]
  >> `ALL_DISTINCT (MAP f l2)` by
       metis_tac[all_distinct_map_sub, listTheory.MEM_APPEND]
  (* IH: both halves sorted *)
  >> `SORTED (\a b. f a < f b) (QSORT (\a b. f a < f b) l1)` by
       (first_x_assum (qspecl_then [`l1`, `l2`] mp_tac) >> simp[sortingTheory.PARTITION_DEF])
  >> `SORTED (\a b. f a < f b) (QSORT (\a b. f a < f b) l2)` by
       (last_x_assum (qspecl_then [`l1`, `l2`] mp_tac) >> simp[sortingTheory.PARTITION_DEF])
  (* Combine using SORTED_APPEND_GEN *)
  >> simp[sortingTheory.SORTED_APPEND_GEN, sortingTheory.SORTED_DEF]
  >> conj_tac
  >- (Cases_on `QSORT (\a b. f a < f b) l1` >> simp[] >>
      `MEM (LAST (h'::t')) (h'::t')` by simp[rich_listTheory.MEM_LAST] >>
      `MEM (LAST (h'::t')) l1` by
        metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ] >>
      res_tac)
  >> Cases_on `QSORT (\a b. f a < f b) l2` >> simp[] >>
     `MEM h' l2` by
       metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ, listTheory.MEM] >>
     `~(f h' < f h)` by metis_tac[] >>
     `MEM h' t` by metis_tac[listTheory.MEM_APPEND] >>
     `f h' <> f h` by metis_tac[listTheory.MEM_MAP_f] >>
     simp[]
QED

(* post_order_index is injective on members of an ALL_DISTINCT list *)
Triviality post_order_inj[local]:
  !post x y. ALL_DISTINCT post /\ MEM x post /\ MEM y post /\
             post_order_index post x = post_order_index post y ==>
             x = y
Proof
  rpt strip_tac >>
  `?i. INDEX_OF x post = SOME i` by
    (Cases_on `INDEX_OF x post` >> fs[listTheory.INDEX_OF_eq_NONE]) >>
  `?j. INDEX_OF y post = SOME j` by
    (Cases_on `INDEX_OF y post` >> fs[listTheory.INDEX_OF_eq_NONE]) >>
  fs[dominatorDefsTheory.post_order_index_def] >>
  `i < LENGTH post /\ EL i post = x` by fs[listTheory.INDEX_OF_eq_SOME] >>
  `j < LENGTH post /\ EL j post = y` by fs[listTheory.INDEX_OF_eq_SOME] >>
  `i = j` by simp[] >>
  metis_tac[]
QED

(* SORTED R (QSORT R doms) /\ transitive R /\ MEM lbl doms /\
   (!x. MEM x doms /\ x <> lbl ==> R lbl x) ==>
   HD (QSORT R doms) = lbl, given LENGTH >= 1 *)
Triviality sorted_hd_is_min[local]:
  !R (l:'a list) m.
    transitive R /\ SORTED R l /\ MEM m l /\
    (!x. MEM x l /\ x <> m ==> R m x) /\
    irreflexive R ==>
    HD l = m
Proof
  rpt strip_tac >>
  Cases_on `l` >> fs[] >>
  Cases_on `h = m` >> simp[] >>
  `R m h` by metis_tac[] >>
  `R h m` by metis_tac[sortingTheory.SORTED_EQ, listTheory.MEM] >>
  fs[relationTheory.irreflexive_def, relationTheory.transitive_def] >>
  metis_tac[]
QED

(* dom_post_order gives INDEX_OF; this corollary gives post_order_index directly *)
Triviality dom_post_order_poi[local]:
  !fn bb d lbl.
    wf_function fn /\ entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) lbl /\
    dominates (dom_analyze (cfg_analyze fn) fn) d lbl /\
    d <> lbl ==>
    post_order_index (cfg_analyze fn).cfg_dfs_post lbl <
    post_order_index (cfg_analyze fn).cfg_dfs_post d
Proof
  rpt strip_tac >>
  fs[dominatorDefsTheory.dominates_def] >>
  drule_all (strip_let dom_post_order) >>
  strip_tac >>
  simp[dominatorDefsTheory.post_order_index_def]
QED

(* transitive R /\ SORTED R (a::b::rest) /\ MEM x rest ==> R b x *)
Triviality sorted_second_rest[local]:
  !R (a:'a) b rest x.
    transitive R /\ SORTED R (a :: b :: rest) /\ MEM x rest ==>
    R b x
Proof
  rpt strip_tac >>
  `SORTED R (b :: rest)` by fs[sortingTheory.SORTED_DEF] >>
  metis_tac[sortingTheory.SORTED_EQ, listTheory.MEM]
QED

Theorem idom_is_immediate_proof:
  !fn cfg lbl d.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    cfg_reachable_of cfg lbl ==>
    let dom = dom_analyze cfg fn in
    idom_of dom lbl = SOME d ==>
    strict_dominates dom d lbl /\
    !d'. strict_dominates dom d' lbl /\ d' <> d ==>
         dominates dom d' d
Proof
  rpt strip_tac >> gvs[LET_THM] >> strip_tac >>
  `MEM lbl (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  drule wf_entry_block_exists >> strip_tac >>
  (* Bridges *)
  `!x. MEM x (fmap_lookup_list
       (dom_analyze (cfg_analyze fn) fn).da_dominators lbl) <=>
       MEM x (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl)` by
    (drule_all dom_bridge >> simp[]) >>
  `!x. MEM x (fmap_lookup_list
       (dom_sets_of fn (dom_fixpoint fn)) lbl) <=>
       MEM x (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl)` by
    (drule_all dom_sets_lookup_eq >> simp[]) >>
  `fn_entry_label fn <> SOME lbl` by (
    SPOSE_NOT_THEN ASSUME_TAC >>
    `idom_of (dom_analyze (cfg_analyze fn) fn) lbl =
     compute_idom_for (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
       (dom_sets_of fn (dom_fixpoint fn)) lbl` by metis_tac[idom_bridge] >>
    fs[dominatorDefsTheory.compute_idom_for_def, LET_THM]) >>
  (* Abbreviate the dominator list *)
  qabbrev_tac `doms = fmap_lookup_list (dom_sets_of fn (dom_fixpoint fn)) lbl` >>
  `ALL_DISTINCT doms` by (
    `dom_state_inv_bdy fn (dom_fixpoint fn)` by
      metis_tac[dom_fixpoint_inv] >>
    `?v. FLOOKUP (dom_fixpoint fn).ds_boundary lbl = SOME v` by
      metis_tac[dom_fixpoint_flookup_some] >>
    `ALL_DISTINCT v` by (fs[dom_state_inv_bdy_def] >> res_tac) >>
    qunabbrev_tac `doms` >>
    drule_all dom_sets_lookup_eq >>
    simp[dfAnalyzeDefsTheory.df_boundary_def]) >>
  `ALL_DISTINCT (cfg_analyze fn).cfg_dfs_post` by (
    simp[cfgHelpersTheory.cfg_analyze_dfs_post] >>
    Cases_on `entry_block fn` >> fs[] >>
    metis_tac[cfgHelpersTheory.dfs_post_walk_distinct_disj]) >>
  `!x. MEM x doms ==> MEM x (cfg_analyze fn).cfg_dfs_post` by (
    rpt strip_tac >>
    `MEM x (fmap_lookup_list
       (dom_analyze (cfg_analyze fn) fn).da_dominators lbl)` by metis_tac[] >>
    `cfg_reachable_of (cfg_analyze fn) x` by metis_tac[dom_reachable] >>
    mp_tac (Q.SPECL [`fn`, `bb`, `x`] reachable_mem_dfs_post) >> simp[]) >>
  `ALL_DISTINCT (MAP (post_order_index (cfg_analyze fn).cfg_dfs_post) doms)` by (
    irule listTheory.ALL_DISTINCT_MAP_INJ >> simp[] >>
    rpt strip_tac >> irule post_order_inj >> metis_tac[]) >>
  qabbrev_tac `cmp = \a b. post_order_index (cfg_analyze fn).cfg_dfs_post a <
                            (post_order_index (cfg_analyze fn).cfg_dfs_post b : num)` >>
  (* SORTED step — avoid Q.SPEC backtick nesting *)
  sg `SORTED cmp (QSORT cmp doms)` >-
    (qunabbrev_tac `cmp` >> irule qsort_strict_sorted >> simp[]) >>
  (* MEM preservation *)
  sg `!x. MEM x (QSORT cmp doms) <=> MEM x doms` >-
    metis_tac[sortingTheory.QSORT_PERM, sortingTheory.PERM_MEM_EQ] >>
  (* idom_bridge *)
  sg `idom_of (dom_analyze (cfg_analyze fn) fn) lbl =
   compute_idom_for (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
     (dom_sets_of fn (dom_fixpoint fn)) lbl` >-
    metis_tac[idom_bridge] >>
  fs[dominatorDefsTheory.compute_idom_for_def, LET_THM] >>
  Cases_on `QSORT cmp doms` >> fs[] >>
  Cases_on `t` >> fs[] >> gvs[] >>
  (* All elements dominate lbl *)
  sg `!x. x = h \/ x = d \/ MEM x t' ==>
       dominates (dom_analyze (cfg_analyze fn) fn) x lbl` >-
    (rpt strip_tac >> simp[dominatorDefsTheory.dominates_def] >>
     `MEM x (df_boundary (fn_labels fn) (dom_fixpoint fn) lbl)` by
       metis_tac[] >> metis_tac[]) >>
  (* h = lbl: lbl has minimum poi among dominators *)
  sg `h = lbl` >- (
    SPOSE_NOT_THEN ASSUME_TAC >>
    `dominates (dom_analyze (cfg_analyze fn) fn) lbl lbl` by
      metis_tac[dom_self_proof] >>
    `dominates (dom_analyze (cfg_analyze fn) fn) h lbl` by metis_tac[] >>
    `post_order_index (cfg_analyze fn).cfg_dfs_post lbl <
     post_order_index (cfg_analyze fn).cfg_dfs_post h` by
      metis_tac[dom_post_order_poi] >>
    `lbl = h \/ lbl = d \/ MEM lbl t'` by
      (fs[dominatorDefsTheory.dominates_def] >> metis_tac[]) >>
    gvs[] >>
    qunabbrev_tac `cmp` >>
    fs[sortingTheory.SORTED_EQ, relationTheory.transitive_def] >>
    res_tac >> fs[]) >>
  pop_assum SUBST_ALL_TAC >>
  (* d <> lbl *)
  sg `d <> lbl` >-
    (strip_tac >> gvs[] >> qunabbrev_tac `cmp` >> fs[sortingTheory.SORTED_DEF]) >>
  (* Part 1: strict_dominates d lbl *)
  conj_tac >- (simp[dominatorDefsTheory.strict_dominates_def] >> metis_tac[]) >>
  (* Part 2: any other strict dominator d' dominates d *)
  rpt strip_tac >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d' lbl` by
    fs[dominatorDefsTheory.strict_dominates_def] >>
  `d' <> lbl` by fs[dominatorDefsTheory.strict_dominates_def] >>
  `MEM d' (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl)` by
    fs[dominatorDefsTheory.dominates_def] >>
  `MEM d (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl)` by
    (fs[] >> metis_tac[]) >>
  `MEM d' (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators d) \/
   MEM d (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators d')` by (
    irule (strip_let dom_chain) >> metis_tac[]) >>
  gvs[] >- simp[dominatorDefsTheory.dominates_def] >>
  (* Contradiction case: d dominates d' *)
  `cfg_reachable_of (cfg_analyze fn) d'` by metis_tac[dom_reachable] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) d d'` by
    simp[dominatorDefsTheory.dominates_def] >>
  `d <> d'` by
    (strip_tac >> gvs[] >> fs[dominatorDefsTheory.strict_dominates_def]) >>
  `post_order_index (cfg_analyze fn).cfg_dfs_post d' <
   post_order_index (cfg_analyze fn).cfg_dfs_post d` by
    metis_tac[dom_post_order_poi] >>
  `d' = lbl \/ d' = d \/ MEM d' t'` by metis_tac[] >> gvs[] >>
  qunabbrev_tac `cmp` >>
  fs[sortingTheory.SORTED_EQ, relationTheory.transitive_def] >>
  res_tac >> fs[]
QED

(* ========================================================================
   Category E: Dom-tree children and frontier
   ======================================================================== *)

(* compute_dominated: MEM c (lookup n) <=> FLOOKUP idom c = SOME n /\ MEM c labels.
   Generalized over accumulator m, then specialized to FEMPTY. *)
Triviality compute_dominated_mem_gen[local]:
  !labels (idom:'a |-> 'b) (m:'b |-> 'a list) n c.
    MEM c (fmap_lookup_list (FOLDL (\m lbl.
      case FLOOKUP idom lbl of NONE => m
      | SOME parent => m |+ (parent,
          set_insert lbl (fmap_lookup_list m parent))) m labels) n) <=>
    MEM c (fmap_lookup_list m n) \/
    (MEM c labels /\ FLOOKUP idom c = SOME n)
Proof
  Induct_on `labels` >> simp[] >> rpt gen_tac >>
  Cases_on `FLOOKUP idom h` >>
  simp[cfgDefsTheory.fmap_lookup_list_def,
       finite_mapTheory.FLOOKUP_UPDATE,
       cfgDefsTheory.set_insert_def] >>
  Cases_on `c = h` >> gvs[] >>
  TRY (rename1 `FLOOKUP idom h = SOME parent`) >>
  TRY (Cases_on `parent = n`) >> gvs[] >>
  simp[cfgDefsTheory.fmap_lookup_list_def, MEM] >>
  TRY IF_CASES_TAC >> simp[MEM]
QED

Triviality compute_dominated_mem[local]:
  !labels idom n c.
    MEM c (fmap_lookup_list (compute_dominated idom labels) n) <=>
    MEM c labels /\ FLOOKUP idom c = SOME n
Proof
  rpt gen_tac >>
  simp[dominatorDefsTheory.compute_dominated_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  ONCE_REWRITE_TAC [compute_dominated_mem_gen] >>
  simp[cfgDefsTheory.fmap_lookup_list_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem dominated_iff_idom_proof:
  !fn cfg n c.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    MEM n (fn_labels fn) /\
    MEM c (fn_labels fn) ==>
    let dom = dom_analyze cfg fn in
    (MEM c (dominated_of dom n) <=> idom_of dom c = SOME n)
Proof
  rpt strip_tac >> gvs[] >> simp[LET_THM] >>
  `dominated_of (dom_analyze (cfg_analyze fn) fn) n =
   fmap_lookup_list
     (compute_dominated
       (compute_idom (cfg_analyze fn).cfg_dfs_post
         (fn_entry_label fn)
         (dom_sets_of fn (dom_fixpoint fn))
         (fn_labels fn))
       (fn_labels fn)) n` by (
    irule dominated_bridge >> simp[]) >>
  simp[compute_dominated_mem] >>
  simp[dominatorDefsTheory.idom_of_def,
       dominatorDefsTheory.dom_analyze_def, LET_THM]
QED

(* Full characterization of fmap_lookup_list after set_insert update.
   Subsumes the old fmap_update_set_insert_mem (monotonicity). *)
Triviality fmap_update_set_insert_iff[local]:
  !df k v n x.
    MEM x (fmap_lookup_list (df |+ (k, set_insert v (fmap_lookup_list df k))) n)
    <=> MEM x (fmap_lookup_list df n) \/ (n = k /\ x = v)
Proof
  rpt gen_tac >>
  simp[cfgDefsTheory.fmap_lookup_list_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `n = k` >> simp[cfgDefsTheory.set_insert_def] >>
  Cases_on `FLOOKUP df k` >> simp[MEM] >>
  Cases_on `MEM v x'` >> simp[MEM] >> metis_tac[]
QED

(* walk_to_idom monotonicity: walk only adds entries *)
Triviality walk_to_idom_mono[local]:
  !fuel idom target runner df n x.
    MEM x (fmap_lookup_list df n) ==>
    MEM x (fmap_lookup_list (walk_to_idom idom target runner df fuel) n)
Proof
  Induct_on `fuel` >>
  simp[dominatorDefsTheory.walk_to_idom_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP idom target` >> simp[] >>
  Cases_on `runner = x'` >> simp[] >>
  simp[LET_THM] >>
  Cases_on `FLOOKUP idom runner` >> simp[] >-
    simp[fmap_update_set_insert_iff] >>
  first_x_assum irule >>
  simp[fmap_update_set_insert_iff]
QED

(* idom_step: the relation followed by walk_to_idom *)
Definition idom_step_def:
  idom_step idom a b <=> (FLOOKUP idom a = SOME b)
End

(* walk_to_idom adds target to n's frontier iff n is on the idom path from
   runner, before reaching idom(target), within fuel steps *)
Triviality walk_to_idom_adds[local]:
  !fuel idom target runner df n.
    FLOOKUP idom target = SOME target_idom ==>
    (MEM target (fmap_lookup_list (walk_to_idom idom target runner df fuel) n) <=>
     MEM target (fmap_lookup_list df n) \/
     (n <> target_idom /\
      ?k. k < fuel /\
          NRC (idom_step idom) k runner n /\
          !j m. j < k /\ NRC (idom_step idom) j runner m ==> m <> target_idom))
Proof
  Induct_on `fuel` >| [
    simp[dominatorDefsTheory.walk_to_idom_def],
    rpt strip_tac >>
    simp[dominatorDefsTheory.walk_to_idom_def] >>
    Cases_on `runner = target_idom` >> simp[] >| [
      (* runner = target_idom: walk returns df, RHS disjunct is false *)
      EQ_TAC >> simp[] >> rpt strip_tac >>
      Cases_on `k` >> fs[arithmeticTheory.NRC] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[arithmeticTheory.NRC],
      (* runner <> target_idom *)
      Cases_on `FLOOKUP idom runner` >> simp[] >| [
        (* NONE: walk stops at df |+ (runner, ...) *)
        simp[fmap_update_set_insert_iff] >>
        EQ_TAC >> rpt strip_tac >> simp[] >| [
          disj2_tac >> fs[] >> qexists_tac `0` >> simp[arithmeticTheory.NRC],
          Cases_on `k` >> fs[arithmeticTheory.NRC, idom_step_def] >> fs[]
        ],
        (* SOME x: IH applied, fmap_update_set_insert_iff applied *)
        simp[fmap_update_set_insert_iff] >>
        EQ_TAC >> rpt strip_tac >> simp[] >| [
          (* n = runner => k=0 in RHS *)
          disj2_tac >> fs[] >> qexists_tac `0` >> simp[arithmeticTheory.NRC],
          (* NRC k x n from IH => NRC (SUC k) runner n *)
          disj2_tac >> simp[] >>
          qexists_tac `SUC k` >> simp[arithmeticTheory.NRC] >>
          conj_tac >- (qexists_tac `x` >> simp[idom_step_def]) >>
          rpt strip_tac >>
          Cases_on `j` >> fs[arithmeticTheory.NRC, idom_step_def] >> res_tac,
          (* NRC k runner n => (MEM \/ n=runner) \/ NRC k' x n *)
          Cases_on `k` >> fs[arithmeticTheory.NRC] >>
          fs[idom_step_def] >> gvs[] >>
          disj2_tac >> qexists_tac `n'` >> simp[] >>
          rpt strip_tac >>
          first_x_assum (qspec_then `SUC j` mp_tac) >>
          simp[arithmeticTheory.NRC, idom_step_def] >> metis_tac[]
        ]
      ]
    ]
  ]
QED

(* When target has no idom, walk_to_idom is identity *)
Triviality walk_to_idom_no_idom[local]:
  !fuel idom target runner df.
    FLOOKUP idom target = NONE ==>
    walk_to_idom idom target runner df fuel = df
Proof
  Cases_on `fuel` >>
  simp[dominatorDefsTheory.walk_to_idom_def]
QED

(* Inner FOLDL over preds: characterize what walk_to_idom adds across preds *)
Triviality walk_foldl_preds[local]:
  !preds idom target df fuel n.
    FLOOKUP idom target = SOME target_idom ==>
    (MEM target (fmap_lookup_list
       (FOLDL (\df' pred. walk_to_idom idom target pred df' fuel) df preds) n) <=>
     MEM target (fmap_lookup_list df n) \/
     (n <> target_idom /\
      ?p k. MEM p preds /\ k < fuel /\
            NRC (idom_step idom) k p n /\
            !j m. j < k /\ NRC (idom_step idom) j p m ==> m <> target_idom))
Proof
  Induct_on `preds` >> simp[] >> rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `idom`, `target`, `h`, `df`, `n`]
    walk_to_idom_adds) >>
  simp[] >> strip_tac >> metis_tac[]
QED

(* walk_to_idom with different target doesn't affect queries for y *)
Triviality walk_to_idom_other[local]:
  !fuel idom target runner df n y.
    target <> y ==>
    (MEM y (fmap_lookup_list (walk_to_idom idom target runner df fuel) n) <=>
     MEM y (fmap_lookup_list df n))
Proof
  Induct_on `fuel` >>
  simp[dominatorDefsTheory.walk_to_idom_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP idom target` >> simp[] >>
  Cases_on `runner = x` >> simp[] >>
  simp[LET_THM] >>
  Cases_on `FLOOKUP idom runner` >> simp[] >>
  simp[fmap_update_set_insert_iff]
QED

(* Extend walk_to_idom_other to inner FOLDL over preds *)
Triviality walk_foldl_preds_other[local]:
  !preds idom target df fuel n y.
    target <> y ==>
    (MEM y (fmap_lookup_list
       (FOLDL (\df' pred. walk_to_idom idom target pred df' fuel) df preds) n) <=>
     MEM y (fmap_lookup_list df n))
Proof
  Induct_on `preds` >> simp[] >> rpt strip_tac >>
  simp[walk_to_idom_other]
QED

(* Generalized FOLDL characterization with arbitrary initial df *)
Triviality compute_df_foldl_mem[local]:
  !order cfg idom fuel n y df0.
    (MEM y (fmap_lookup_list (FOLDL (\df lbl.
       if LENGTH (cfg_preds_of cfg lbl) <= 1 then df
       else FOLDL (\df' pred. walk_to_idom idom lbl pred df' fuel) df
              (cfg_preds_of cfg lbl)) df0 order) n) <=>
     MEM y (fmap_lookup_list df0 n) \/
     (MEM y order /\
      LENGTH (cfg_preds_of cfg y) > 1 /\
      (case FLOOKUP idom y of
         NONE => F
       | SOME target_idom =>
           n <> target_idom /\
           ?p k. MEM p (cfg_preds_of cfg y) /\ k < fuel /\
                 NRC (idom_step idom) k p n /\
                 !j m. j < k /\ NRC (idom_step idom) j p m ==> m <> target_idom)))
Proof
  Induct_on `order`
  >- simp[cfgHelpersTheory.fmap_lookup_list_fempty]
  >> simp[FOLDL] >> rpt strip_tac >> Cases_on `y = h`
  >- (gvs[] >> Cases_on `LENGTH (cfg_preds_of cfg h) <= 1` >> simp[] >>
      Cases_on `FLOOKUP idom h` >> simp[]
      >- (`!preds df0. FLOOKUP idom h = NONE ==>
            FOLDL (\df' pred. walk_to_idom idom h pred df' fuel) df0 preds = df0` by
            (Induct >> simp[walk_to_idom_no_idom]) >> simp[])
      >> mp_tac (walk_foldl_preds
           |> INST_TYPE [alpha |-> ``:string``]
           |> INST [``target_idom:string`` |-> ``x:string``]) >>
         simp[] >> metis_tac[])
  >> Cases_on `LENGTH (cfg_preds_of cfg h) <= 1` >>
     simp[walk_foldl_preds_other]
QED

(* Outer FOLDL: characterize MEM in compute_df result *)
Triviality compute_df_mem[local]:
  !order cfg idom fuel n y.
    (MEM y (fmap_lookup_list (compute_df cfg idom order fuel) n) <=>
     MEM y order /\
     LENGTH (cfg_preds_of cfg y) > 1 /\
     (case FLOOKUP idom y of
        NONE => F
      | SOME target_idom =>
          n <> target_idom /\
          ?p k. MEM p (cfg_preds_of cfg y) /\ k < fuel /\
                NRC (idom_step idom) k p n /\
                !j m. j < k /\ NRC (idom_step idom) j p m ==> m <> target_idom))
Proof
  simp[dominatorDefsTheory.compute_df_def, compute_df_foldl_mem,
       cfgHelpersTheory.fmap_lookup_list_fempty]
QED

(* Bridge: FLOOKUP compute_idom = idom_of dom_analyze *)
Triviality idom_flookup_eq[local]:
  wf_function fn /\ MEM lbl (fn_labels fn) ==>
  (FLOOKUP (compute_idom (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
     (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn)) lbl =
   idom_of (dom_analyze (cfg_analyze fn) fn) lbl)
Proof
  strip_tac >>
  `FLOOKUP (compute_idom (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
     (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn)) lbl =
   compute_idom_for (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
     (dom_sets_of fn (dom_fixpoint fn)) lbl` by
    (irule compute_idom_lookup >> fs[venomWfTheory.wf_function_def]) >>
  `idom_of (dom_analyze (cfg_analyze fn) fn) lbl =
   compute_idom_for (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
     (dom_sets_of fn (dom_fixpoint fn)) lbl` by
    (irule idom_bridge >> simp[]) >>
  simp[]
QED

(* Dominator of a reachable node is reachable *)
Theorem dominates_reachable:
  !fn d p. wf_function fn /\
    cfg_reachable_of (cfg_analyze fn) p /\
    dominates (dom_analyze (cfg_analyze fn) fn) d p ==>
    cfg_reachable_of (cfg_analyze fn) d
Proof
  rpt strip_tac >>
  `?bb. entry_block fn = SOME bb` by
    (irule wf_entry_block_exists >> simp[]) >>
  irule dom_reachable >> simp[] >> qexists_tac `p` >>
  fs[dominatorDefsTheory.dominates_def]
QED

(* idom_step implies domination: NRC idom_step k p n ==> dominates n p *)
Triviality nrc_idom_dominates[local]:
  !fn cfg k p n.
    wf_function fn /\ cfg = cfg_analyze fn /\
    cfg_reachable_of cfg p ==>
    let dom = dom_analyze cfg fn in
    let idom = compute_idom cfg.cfg_dfs_post (fn_entry_label fn)
                 (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn) in
    NRC (idom_step idom) k p n ==>
    dominates dom n p
Proof
  Induct_on `k`
  >- (rpt strip_tac >> fs[arithmeticTheory.NRC, LET_THM] >>
      strip_tac >> gvs[] >>
      irule dom_self_proof >> metis_tac[reachable_mem_fn_labels])
  >> rpt strip_tac >> gvs[LET_THM] >>
  fs[arithmeticTheory.NRC] >> strip_tac >>
  rename1 `idom_step _ p z` >>
  `MEM p (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `idom_of (dom_analyze (cfg_analyze fn) fn) p = SOME z` by
    (mp_tac (idom_flookup_eq |> INST [``lbl:string`` |-> ``p:string``]) >>
     simp[] >> fs[idom_step_def]) >>
  mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `p`, `z`]
            idom_is_immediate_proof) >>
  simp[LET_THM] >> strip_tac >>
  `cfg_reachable_of (cfg_analyze fn) z` by
    (irule dominates_reachable >>
     fs[dominatorDefsTheory.strict_dominates_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `dominates (dom_analyze (cfg_analyze fn) fn) n z` by metis_tac[] >>
  `dominates (dom_analyze (cfg_analyze fn) fn) z p` by
    fs[dominatorDefsTheory.strict_dominates_def] >>
  mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `n`, `z`, `p`]
            dominates_trans_proof) >>
  simp[LET_THM]
QED

(* Strict domination implies strictly fewer dominators *)
Theorem strict_dom_doms_lt:
  !fn d p.
    wf_function fn /\
    cfg_reachable_of (cfg_analyze fn) d /\
    cfg_reachable_of (cfg_analyze fn) p /\
    strict_dominates (dom_analyze (cfg_analyze fn) fn) d p ==>
    LENGTH (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators d) <
    LENGTH (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators p)
Proof
  rw[dominatorDefsTheory.strict_dominates_def] >>
  `MEM d (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `MEM p (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  irule dfHelperPropsTheory.all_distinct_psubset_length >>
  `dom_state_inv_bdy fn (dom_fixpoint fn)` by metis_tac[dom_bridge] >>
  (* ALL_DISTINCT *)
  rpt conj_tac
  >- (mp_tac (Q.SPECL [`fn`, `d`] dom_bridge) >> simp[] >>
      strip_tac >> simp[dfAnalyzeDefsTheory.df_boundary_def] >>
      `?v. FLOOKUP (dom_fixpoint fn).ds_boundary d = SOME v` by
        metis_tac[dom_fixpoint_flookup_some] >>
      simp[] >> fs[dom_state_inv_bdy_def] >> metis_tac[])
  >- (mp_tac (Q.SPECL [`fn`, `p`] dom_bridge) >> simp[] >>
      strip_tac >> simp[dfAnalyzeDefsTheory.df_boundary_def] >>
      `?v. FLOOKUP (dom_fixpoint fn).ds_boundary p = SOME v` by
        metis_tac[dom_fixpoint_flookup_some] >>
      simp[] >> fs[dom_state_inv_bdy_def] >> metis_tac[])
  (* Goal 1: set doms(d) ≠ set doms(p) *)
  >- (
    simp[pred_setTheory.EXTENSION] >> qexists_tac `p` >>
    (* Goal: MEM p doms(d) ⇎ MEM p doms(p) *)
    `dominates (dom_analyze (cfg_analyze fn) fn) p p` by
      (irule dom_self_proof >> metis_tac[]) >>
    `~dominates (dom_analyze (cfg_analyze fn) fn) p d` by
      (strip_tac >>
       mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `p`, `d`]
                 dominates_antisym_proof) >>
       simp[LET_THM]) >>
    fs[dominatorDefsTheory.dominates_def])
  (* Goal 2: set doms(d) ⊆ set doms(p) *)
  >- (
    rw[pred_setTheory.SUBSET_DEF, dominatorDefsTheory.dominates_def] >>
    mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `x`, `d`, `p`]
              dominates_trans_proof) >>
    simp[LET_THM, dominatorDefsTheory.dominates_def])
QED

(* Dominator list length bounded by fn_labels length *)
Triviality doms_length_le_labels[local]:
  !fn p.
    wf_function fn /\ MEM p (fn_labels fn) ==>
    LENGTH (fmap_lookup_list
      (dom_analyze (cfg_analyze fn) fn).da_dominators p) <=
    LENGTH (fn_labels fn)
Proof
  rpt strip_tac >>
  `dom_state_inv_bdy fn (dom_fixpoint fn)` by metis_tac[dom_bridge] >>
  `fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators p =
   df_boundary (fn_labels fn) (dom_fixpoint fn) p` by metis_tac[dom_bridge] >>
  `?v. FLOOKUP (dom_fixpoint fn).ds_boundary p = SOME v` by
    metis_tac[dom_fixpoint_flookup_some] >>
  `ALL_DISTINCT (df_boundary (fn_labels fn) (dom_fixpoint fn) p)` by
    (fs[dfAnalyzeDefsTheory.df_boundary_def, dom_state_inv_bdy_def] >>
     metis_tac[]) >>
  `set (df_boundary (fn_labels fn) (dom_fixpoint fn) p) SUBSET
   set (fn_labels fn)` by
    (fs[dfAnalyzeDefsTheory.df_boundary_def, dom_state_inv_bdy_def] >>
     metis_tac[]) >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  simp[] >>
  `LENGTH (df_boundary (fn_labels fn) (dom_fixpoint fn) p) =
   CARD (set (df_boundary (fn_labels fn) (dom_fixpoint fn) p))` by
    metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET] >>
  `LENGTH (fn_labels fn) =
   CARD (set (fn_labels fn))` by
    metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET] >>
  simp[] >>
  irule pred_setTheory.CARD_SUBSET >>
  simp[listTheory.FINITE_LIST_TO_SET]
QED

(* strict_dominates <=> dominates the idom *)
Triviality strict_dom_iff_dom_idom[local]:
  !fn cfg bb n y.
    wf_function fn /\ cfg = cfg_analyze fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of cfg n /\
    cfg_reachable_of cfg y /\
    y <> bb.bb_label ==>
    let dom = dom_analyze cfg fn in
    (strict_dominates dom n y <=>
     dominates dom n (THE (idom_of dom y)))
Proof
  rpt strip_tac >> gvs[LET_THM] >>
  (* Establish idom exists *)
  `?d. idom_of (dom_analyze (cfg_analyze fn) fn) y = SOME d` by
    (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `bb`, `y`] idom_exists_proof) >>
     simp[]) >>
  simp[] >>
  (* Get idom_is_immediate *)
  mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `y`, `d`] idom_is_immediate_proof) >>
  simp[LET_THM] >> strip_tac >>
  simp[dominatorDefsTheory.strict_dominates_def] >>
  EQ_TAC >> strip_tac
  >- ((* Forward: dominates n y /\ n <> y ==> dominates n d *)
      Cases_on `n = d` >- metis_tac[dom_self_proof, reachable_mem_fn_labels] >>
      first_x_assum irule >> simp[dominatorDefsTheory.strict_dominates_def])
  >- ((* Backward: dominates n d ==> dominates n y /\ n <> y *)
      `dominates (dom_analyze (cfg_analyze fn) fn) d y` by
        fs[dominatorDefsTheory.strict_dominates_def] >>
      conj_tac
      >- ((* dominates n y by transitivity via d *)
          mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `n`, `d`, `y`]
                    dominates_trans_proof) >>
          simp[LET_THM])
      >- ((* n <> y: if n=y, then y dom d and d dom y => d=y, contradicting d<>y *)
          strip_tac >> gvs[] >>
          `cfg_reachable_of (cfg_analyze fn) d` by
            (irule dom_reachable >> simp[] >> qexists_tac `n` >>
             fs[dominatorDefsTheory.strict_dominates_def,
                dominatorDefsTheory.dominates_def]) >>
          `dominates (dom_analyze (cfg_analyze fn) fn) d n` by
            fs[dominatorDefsTheory.strict_dominates_def] >>
          `d = n` by
            (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `d`, `n`]
                       dominates_antisym_proof) >>
             simp[LET_THM]) >>
          fs[dominatorDefsTheory.strict_dominates_def]))
QED

(* If d dominates y, d <> y, and p is a CFG predecessor of y, then d dominates p. *)
Theorem dom_dominates_pred:
  !fn cfg bb d y p.
    wf_function fn /\ cfg = cfg_analyze fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of cfg p /\
    cfg_reachable_of cfg y /\
    MEM p (cfg_preds_of cfg y) /\
    dominates (dom_analyze cfg fn) d y /\
    d <> y ==>
    dominates (dom_analyze cfg fn) d p
Proof
  rpt strip_tac >> gvs[] >>
  simp[dominatorDefsTheory.dominates_def] >>
  irule on_every_path_dom >> simp[] >>
  reverse conj_tac
  >- (`cfg_reachable_of (cfg_analyze fn) d` by
        (irule dom_reachable >> simp[] >> qexists_tac `y` >>
         fs[dominatorDefsTheory.dominates_def]) >>
      metis_tac[reachable_mem_fn_labels]) >>
  rpt strip_tac >>
  `MEM y (cfg_succs_of (cfg_analyze fn) p)` by
    (mp_tac (Q.SPEC `fn` cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond) >>
     simp[]) >>
  `LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a))
       (ls ++ [p]) bb.bb_label y` by
    (irule lrc_build >> qexists_tac `p` >> simp[LRC_def]) >>
  mp_tac dom_on_every_path >>
  disch_then (qspecl_then [`fn`, `bb`, `ls ++ [p]`, `y`] mp_tac) >>
  simp[dominatorDefsTheory.dominates_def] >> strip_tac >>
  `d = y \/ MEM d ls \/ d = p` by
    (first_x_assum irule >> fs[dominatorDefsTheory.dominates_def]) >>
  gvs[]
QED


(* dominates implies reachable via NRC idom_step, with all intermediates dominated.
   Tight bound: k < LENGTH doms(p). *)
Triviality dominates_nrc_idom_tight[local]:
  !fn n p.
    wf_function fn /\
    cfg_reachable_of (cfg_analyze fn) p /\
    dominates (dom_analyze (cfg_analyze fn) fn) n p ==>
    ?k. k < LENGTH (fmap_lookup_list
           (dom_analyze (cfg_analyze fn) fn).da_dominators p) /\
        NRC (idom_step (compute_idom (cfg_analyze fn).cfg_dfs_post
               (fn_entry_label fn)
               (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn))) k p n /\
        !j m. j < k /\
          NRC (idom_step (compute_idom (cfg_analyze fn).cfg_dfs_post
                 (fn_entry_label fn)
                 (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn))) j p m ==>
          dominates (dom_analyze (cfg_analyze fn) fn) n m
Proof
  gen_tac >>
  (* Strong induction on LENGTH of dominator list of p *)
  completeInduct_on
    `LENGTH (fmap_lookup_list
       (dom_analyze (cfg_analyze fn) fn).da_dominators p)` >>
  rpt strip_tac >>
  Cases_on `n = p`
  >- (
    (* Base: n = p, take k = 0 *)
    qexists_tac `0` >> simp[arithmeticTheory.NRC] >>
    (* 0 < LENGTH doms(p): p ∈ doms(p) by self-domination *)
    `MEM p (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
    `dominates (dom_analyze (cfg_analyze fn) fn) p p` by
      (irule dom_self_proof >> metis_tac[]) >>
    fs[dominatorDefsTheory.dominates_def] >>
    Cases_on `fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators p` >>
    fs[listTheory.MEM])
  >- (
    (* Step: n ≠ p *)
    `?bb. entry_block fn = SOME bb` by
      (irule wf_entry_block_exists >> simp[]) >>
    `cfg_reachable_of (cfg_analyze fn) n` by
      metis_tac[dominates_reachable] >>
    (* p ≠ entry *)
    `p <> bb.bb_label` by
      (strip_tac >> gvs[] >>
       mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `bb`, `n`]
                 dom_entry_dominates_all_proof) >> simp[] >>
       strip_tac >>
       mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `n`, `bb.bb_label`]
                 dominates_antisym_proof) >>
       simp[LET_THM]) >>
    `MEM p (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
    (* idom(p) exists *)
    `?z. idom_of (dom_analyze (cfg_analyze fn) fn) p = SOME z` by
      (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `bb`, `p`]
                 idom_exists_proof) >> simp[]) >>
    (* idom_step p z *)
    `FLOOKUP (compute_idom (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
       (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn)) p = SOME z` by
      (mp_tac (idom_flookup_eq |> INST [``lbl:string`` |-> ``p:string``]) >>
       simp[]) >>
    (* strict_dom z p from idom_is_immediate *)
    `strict_dominates (dom_analyze (cfg_analyze fn) fn) z p` by
      (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `p`, `z`]
                 idom_is_immediate_proof) >>
       simp[LET_THM]) >>
    (* z is reachable *)
    `cfg_reachable_of (cfg_analyze fn) z` by
      (irule dominates_reachable >>
       fs[dominatorDefsTheory.strict_dominates_def] >>
       goal_assum (drule_at Any) >> simp[]) >>
    (* n dominates z: n strictly dom p, so n dom idom(p) = z *)
    `strict_dominates (dom_analyze (cfg_analyze fn) fn) n p` by
      fs[dominatorDefsTheory.strict_dominates_def] >>
    `dominates (dom_analyze (cfg_analyze fn) fn) n z` by
      (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `bb`, `n`, `p`]
                 strict_dom_iff_dom_idom) >>
       simp[LET_THM]) >>
    (* Measure decreases *)
    `LENGTH (fmap_lookup_list
       (dom_analyze (cfg_analyze fn) fn).da_dominators z) <
     LENGTH (fmap_lookup_list
       (dom_analyze (cfg_analyze fn) fn).da_dominators p)` by
      (irule strict_dom_doms_lt >> simp[]) >>
    (* Apply IH *)
    first_x_assum (qspec_then
      `LENGTH (fmap_lookup_list
         (dom_analyze (cfg_analyze fn) fn).da_dominators z)` mp_tac) >>
    simp[] >> disch_then (qspecl_then [`fn`, `z`] mp_tac) >>
    simp[] >> disch_then (qspec_then `n` mp_tac) >>
    simp[] >> strip_tac >>
    (* k = SUC k' *)
    rename1 `NRC _ k' z n` >>
    qexists_tac `SUC k'` >> rpt conj_tac
    >- simp[] (* SUC k' < LENGTH doms(p): k' < LENGTH doms(z) < LENGTH doms(p) *)
    >- (
      (* NRC (SUC k') p n *)
      simp[arithmeticTheory.NRC] >>
      qexists_tac `z` >> simp[idom_step_def])
    >- (
      (* All intermediates dominated: j=0 closed by gvs[NRC], SUC case below *)
      rpt strip_tac >>
      Cases_on `j` >> gvs[arithmeticTheory.NRC] >>
      fs[idom_step_def] >> gvs[] >>
      first_x_assum irule >> metis_tac[]))
QED

(* Wrap with fn_labels bound and LET *)
Triviality dominates_nrc_idom[local]:
  !fn cfg n p.
    wf_function fn /\ cfg = cfg_analyze fn /\
    cfg_reachable_of cfg p ==>
    let dom = dom_analyze cfg fn in
    let idom = compute_idom cfg.cfg_dfs_post (fn_entry_label fn)
                 (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn) in
    dominates dom n p ==>
    ?k. k < LENGTH (fn_labels fn) /\
        NRC (idom_step idom) k p n /\
        !j m. j < k /\ NRC (idom_step idom) j p m ==>
          dominates dom n m
Proof
  rpt strip_tac >> gvs[LET_THM] >>
  strip_tac >>
  drule_all dominates_nrc_idom_tight >> strip_tac >>
  `MEM p (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `LENGTH (fmap_lookup_list
     (dom_analyze (cfg_analyze fn) fn).da_dominators p) <=
   LENGTH (fn_labels fn)` by metis_tac[doms_length_le_labels] >>
  qexists_tac `k` >> rpt conj_tac >> simp[] >> first_assum ACCEPT_TAC
QED
(* Deterministic NRC: same start + same steps = same end *)
Triviality nrc_deterministic[local]:
  !R j a x y.
    (!a b c. R a b /\ R a c ==> b = c) /\
    NRC R j a x /\ NRC R j a y ==> x = y
Proof
  Induct_on `j` >> rpt strip_tac >> fs[arithmeticTheory.NRC] >>
  metis_tac[]
QED

(* In a deterministic relation, if NRC k a x and NRC j a y with j <= k,
   then NRC (k - j) y x. The path from a is unique, so y is on the way to x. *)
Triviality nrc_deterministic_prefix[local]:
  !R j k a x y.
    (!a b c. R a b /\ R a c ==> b = c) /\
    NRC R k a x /\ NRC R j a y /\ j <= k ==>
    NRC R (k - j) y x
Proof
  Induct_on `j`
  >- (rpt strip_tac >> fs[arithmeticTheory.NRC])
  >- (rpt strip_tac >>
      `?z. R a z /\ NRC R j z y` by
        metis_tac[arithmeticTheory.NRC] >>
      `k = SUC (k - 1)` by simp[] >>
      `?z'. R a z' /\ NRC R (k - 1) z' x` by
        metis_tac[arithmeticTheory.NRC] >>
      `z = z'` by metis_tac[] >>
      `k - SUC j = (k - 1) - j` by simp[] >>
      ntac 2 (pop_assum SUBST_ALL_TAC) >>
      first_x_assum match_mp_tac >>
      qexists_tac `z'` >> rpt conj_tac >> fs[])
QED

(* idom_step is deterministic *)
Triviality idom_step_deterministic[local]:
  !idom a b c. idom_step idom a b /\ idom_step idom a c ==> b = c
Proof
  simp[idom_step_def] >> metis_tac[optionTheory.SOME_11]
QED

(* df_fold_forward with identity transfer is identity on acc *)
Triviality df_fold_forward_id[local]:
  !lbl' instrs idx acc im.
    FST (df_fold_forward (dom_transfer_inst ()) lbl' instrs idx acc im) = acc
Proof
  Induct_on `instrs` >>
  simp[dfAnalyzeDefsTheory.df_fold_forward_def, LET_THM,
       dominatorDefsTheory.dom_transfer_inst_def]
QED

(* FOLDL list_intersect xs over copies of xs is identity *)
Triviality foldl_list_intersect_self[local]:
  !ls xs. FOLDL list_intersect xs (MAP (\v. xs) ls) = xs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `list_intersect xs xs = xs` by
    simp[dfHelperDefsTheory.list_intersect_def,
         listTheory.FILTER_EQ_ID, listTheory.EVERY_MEM] >>
  simp[]
QED

(* Entry label is always reachable *)
Triviality entry_is_reachable[local]:
  !fn elbl. wf_function fn /\ fn_entry_label fn = SOME elbl ==>
            cfg_reachable_of (cfg_analyze fn) elbl
Proof
  rpt strip_tac >>
  `?bb. entry_block fn = SOME bb` by metis_tac[wf_entry_block_exists] >>
  `bb.bb_label = elbl` by fs[venomInstTheory.fn_entry_label_def] >>
  mp_tac (INST_TYPE [alpha |-> ``:string``]
            cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability
          |> Q.SPECL [`fn`, `bb`, `elbl`]) >> simp[] >>
  simp[cfgDefsTheory.cfg_path_def]
QED

(* Predecessors of unreachable nodes are unreachable *)
Triviality preds_of_unreachable[local]:
  !fn q nbr. wf_function fn /\
             ~cfg_reachable_of (cfg_analyze fn) q /\
             MEM nbr (cfg_preds_of (cfg_analyze fn) q) ==>
             ~cfg_reachable_of (cfg_analyze fn) nbr
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `?bb. entry_block fn = SOME bb` by metis_tac[wf_entry_block_exists] >>
  `cfg_reachable_of (cfg_analyze fn) q` suffices_by metis_tac[] >>
  `MEM q (cfg_succs_of (cfg_analyze fn) nbr)` by
    metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond] >>
  `cfg_path (cfg_analyze fn) bb.bb_label nbr` by
    metis_tac[cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability] >>
  mp_tac (INST_TYPE [alpha |-> ``:string``]
            cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability
          |> Q.SPECL [`fn`, `bb`, `q`]) >> simp[] >>
  fs[cfgDefsTheory.cfg_path_def] >>
  simp[Once relationTheory.RTC_CASES2] >>
  disj2_tac >> qexists_tac `nbr` >> simp[]
QED

(* Unreachable boundary preservation through df_process_block *)
Triviality unreachable_bdy_preserved[local]:
  !fn lbl st q.
    wf_function fn /\ MEM lbl (fn_labels fn) /\ dom_full_inv fn st /\
    (!q. ~cfg_reachable_of (cfg_analyze fn) q /\ MEM q (fn_labels fn) ==>
         FLOOKUP st.ds_boundary q = SOME (fn_labels fn)) /\
    ~cfg_reachable_of (cfg_analyze fn) q /\ MEM q (fn_labels fn) ==>
    FLOOKUP (df_process_block Forward (fn_labels fn) list_intersect
       dom_transfer_inst dom_edge_transfer ()
       (OPTION_MAP (\lbl. (lbl,[lbl])) (fn_entry_label fn))
       (cfg_analyze fn) fn.fn_blocks lbl st).ds_boundary q =
    SOME (fn_labels fn)
Proof
  rpt strip_tac >>
  `FLOOKUP st.ds_boundary q = SOME (fn_labels fn)` by metis_tac[] >>
  rewrite_tac[dom_process_eq] >> simp_tac std_ss [LET_THM] >>
  pairarg_tac >> simp[] >>
  drule identity_fold_block_values >> strip_tac >> gvs[] >>
  (* Goal: FLOOKUP (if ... then st else st |+ (lbl,...)).ds_boundary q = ... *)
  Cases_on `lbl = q` >> gvs[]
  >- ((* lbl = q: show boundary unchanged (IF true) by proving joined = fn_labels *)
      `FLOOKUP st.ds_boundary lbl = SOME (fn_labels fn)` by metis_tac[] >>
      `df_boundary (fn_labels fn) st lbl = fn_labels fn` by
        simp[dfAnalyzeDefsTheory.df_boundary_def] >>
      (* Show all predecessor boundaries = fn_labels *)
      `!nbr. MEM nbr (cfg_preds_of (cfg_analyze fn) lbl) ==>
             FLOOKUP st.ds_boundary nbr = SOME (fn_labels fn)` by (
        rpt strip_tac >>
        `MEM nbr (fn_labels fn)` by
          metis_tac[INST_TYPE [alpha |-> ``:string``]
                      cfgAnalysisPropsTheory.cfg_analyze_pred_labels] >>
        first_x_assum irule >> simp[] >>
        metis_tac[preds_of_unreachable]) >>
      (* Show dom_joined fn st lbl = fn_labels fn *)
      `dom_joined fn st lbl = fn_labels fn` by (
        simp_tac std_ss
          [dom_joined_def, dfAnalyzeDefsTheory.df_joined_val_def, LET_THM] >>
        `MAP (\nbr. dom_edge_transfer () nbr lbl
                      (df_boundary (fn_labels fn) st nbr))
             (cfg_preds_of (cfg_analyze fn) lbl) =
         MAP (\nbr. fn_labels fn) (cfg_preds_of (cfg_analyze fn) lbl)` by (
          irule listTheory.MAP_CONG >> simp[] >> rpt strip_tac >>
          `FLOOKUP st.ds_boundary x = SOME (fn_labels fn)` by metis_tac[] >>
          simp[dominatorDefsTheory.dom_edge_transfer_def,
               dfAnalyzeDefsTheory.df_boundary_def,
               cfgDefsTheory.set_insert_def]) >>
        simp[foldl_list_intersect_self] >>
        Cases_on `cfg_preds_of (cfg_analyze fn) lbl` >> simp[] >>
        Cases_on `fn_entry_label fn` >> simp[] >>
        rename1 `fn_entry_label fn = SOME elbl` >>
        `lbl <> elbl` by metis_tac[entry_is_reachable] >>
        simp[]) >>
      (* Now IF condition is true: list_intersect (fn_labels fn) (fn_labels fn) = fn_labels fn *)
      `list_intersect (fn_labels fn) (fn_labels fn) = fn_labels fn` by
        simp[dfHelperDefsTheory.list_intersect_def,
             listTheory.FILTER_EQ_ID, listTheory.EVERY_MEM] >>
      simp[])
  >- ((* lbl <> q: boundary for q unchanged in both IF branches *)
      IF_CASES_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE])
QED

(* Unreachable nodes are dominated by all labels *)
Triviality unreachable_doms_all[local]:
  !fn p n.
    wf_function fn /\ MEM p (fn_labels fn) /\ MEM n (fn_labels fn) /\
    ~cfg_reachable_of (cfg_analyze fn) p ==>
    dominates (dom_analyze (cfg_analyze fn) fn) n p
Proof
  rpt strip_tac >>
  simp[dominatorDefsTheory.dominates_def, dominatorDefsTheory.dom_analyze_def,
       LET_THM, dominatorDefsTheory.dom_sets_of_def] >>
  `ALL_DISTINCT (fn_labels fn)` by fs[venomWfTheory.wf_function_def] >>
  simp[cfgDefsTheory.fmap_lookup_list_def, foldl_fupdate_lookup] >>
  `FLOOKUP (dom_fixpoint fn).ds_boundary p = SOME (fn_labels fn)` suffices_by
    simp[dfAnalyzeDefsTheory.df_boundary_def] >>
  simp_tac std_ss [dominatorDefsTheory.dom_fixpoint_def] >>
  mp_tac (INST_TYPE [alpha |-> ``:string list``, beta |-> ``:unit``]
    df_analyze_invariant_forward'
    |> Q.SPECL [`fn_labels fn`, `list_intersect`, `dom_transfer_inst`,
                `dom_edge_transfer`, `()`,
                `OPTION_MAP (\lbl. (lbl, [lbl])) (fn_entry_label fn)`,
                `fn`, `dom_measure fn`, `dom_measure_bound fn`,
                `\st. dom_full_inv fn st /\
                      !q. ~cfg_reachable_of (cfg_analyze fn) q /\
                          MEM q (fn_labels fn) ==>
                          FLOOKUP st.ds_boundary q = SOME (fn_labels fn)`]) >>
  simp_tac std_ss [LET_THM] >>
  impl_tac >- (
    conj_tac >- simp[] >>
    conj_tac >- (
      rpt strip_tac >>
      `dom_state_inv fn st` by (fs[dom_full_inv_def] >> metis_tac[]) >>
      metis_tac[dom_measure_increases']) >>
    conj_tac >- (
      rpt gen_tac >> strip_tac >> conj_tac
      >- (fs[dom_full_inv_def] >>
          metis_tac[dom_inv_preserved', dom_extra_preserved'])
      >> metis_tac[unreachable_bdy_preserved]) >>
    conj_tac >- (
      Cases_on `fn_entry_label fn` >> simp[]
      >- ((* NONE *)
          conj_tac
          >- (mp_tac (Q.SPEC `fn` dom_init_state_inv') >>
              mp_tac (Q.SPEC `fn` dom_extra_init') >>
              simp[dom_full_inv_def])
          >> rpt strip_tac >>
          simp[dfAnalyzeDefsTheory.init_df_state_def,
               finite_mapTheory.FLOOKUP_UPDATE] >>
          irule foldl_fupdate_const >> fs[venomInstTheory.fn_labels_def])
      >> (* SOME *)
      rename1 `fn_entry_label fn = SOME elbl` >>
      conj_tac
      >- (mp_tac (Q.SPEC `fn` dom_init_state_inv') >>
          mp_tac (Q.SPEC `fn` dom_extra_init') >>
          simp[dom_full_inv_def])
      >> rpt strip_tac >>
      `q <> elbl` by metis_tac[entry_is_reachable] >>
      simp[dfAnalyzeDefsTheory.init_df_state_def,
           finite_mapTheory.FLOOKUP_UPDATE] >>
      irule foldl_fupdate_const >> fs[venomInstTheory.fn_labels_def]) >>
    rpt strip_tac >>
    `dom_state_inv fn x` by fs[dom_full_inv_def] >>
    metis_tac[dom_measure_bounded']) >>
  (* Bridge: df_analyze_invariant_forward' concludes about SND(wl_iterate ...),
     but goal is about df_analyze (= df_populate_inst ... (SND(wl_iterate ...))).
     df_populate_inst preserves ds_boundary. *)
  disch_then (strip_assume_tac o SIMP_RULE std_ss []) >>
  simp_tac std_ss [LET_THM, dominatorDefsTheory.dom_fixpoint_def,
                   dfAnalyzeDefsTheory.df_analyze_def,
                   dfAnalyzeDefsTheory.direction_case_def] >>
  qmatch_goalsub_abbrev_tac `df_populate_inst _ _ _ _ _ _ _ _ _ _ wl_res` >>
  `(df_populate_inst Forward (fn_labels fn) list_intersect dom_transfer_inst
       dom_edge_transfer ()
       (OPTION_MAP (\lbl. (lbl,[lbl])) (fn_entry_label fn))
       (cfg_analyze fn) fn.fn_blocks
       (MAP (\bb. bb.bb_label) fn.fn_blocks)
       wl_res).ds_boundary = wl_res.ds_boundary`
    by simp[populate_inst_ds_boundary] >>
  metis_tac[]
QED

(* dom_frontier_correct_proof — design note:
   The existential requires cfg_reachable_of cfg p, matching the standard
   Cytron et al. (1991) definition which only considers reachable predecessors.
   Without this, the theorem is FALSE: unreachable predecessors have
   vacuous dominator sets (= fn_labels), causing idom walks that bypass
   the true idom and producing spurious frontier entries.
   Backward direction is unaffected since dom n p ∧ reachable n implies
   reachable p.
*)

(* SML vals for NRC lemma specialization, avoids nested backtick issues *)
val the_idom = ``compute_idom (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
   (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn)``;
val nrc_det_spec = nrc_deterministic
  |> INST_TYPE [alpha |-> ``:string``]
  |> Q.SPEC `idom_step ^the_idom`;
val nrc_prefix_spec = nrc_deterministic_prefix
  |> INST_TYPE [alpha |-> ``:string``]
  |> Q.SPEC `idom_step ^the_idom`;
val dominates_nrc_idom_rw = REWRITE_RULE [LET_THM] dominates_nrc_idom;

Theorem dom_frontier_correct_proof:
  !fn cfg n y.
    wf_function fn /\
    cfg = cfg_analyze fn /\
    cfg_reachable_of cfg n /\
    cfg_reachable_of cfg y /\
    LENGTH (cfg_preds_of cfg y) > 1 /\
    fn_entry_label fn <> SOME y /\
    (!p. MEM p (cfg_preds_of cfg y) ==> cfg_reachable_of cfg p) ==>
    let dom = dom_analyze cfg fn in
    (MEM y (frontier_of dom n) <=>
     ?p. MEM p (cfg_preds_of cfg y) /\
         dominates dom n p /\
         ~strict_dominates dom n y)
Proof
  rpt strip_tac >> gvs[LET_THM] >>
  `MEM n (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `MEM y (fn_labels fn)` by metis_tac[reachable_mem_fn_labels] >>
  `?bb. entry_block fn = SOME bb` by
    (irule wf_entry_block_exists >> simp[]) >>
  `y <> bb.bb_label` by
    (strip_tac >> fs[venomInstTheory.fn_entry_label_def]) >>
  `?target_idom. idom_of (dom_analyze (cfg_analyze fn) fn) y = SOME target_idom` by
    (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `bb`, `y`]
               idom_exists_proof) >> simp[]) >>
  `FLOOKUP (compute_idom (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
     (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn)) y = SOME target_idom` by
    (mp_tac (idom_flookup_eq |> INST [``lbl:string`` |-> ``y:string``]) >>
     simp[]) >>
  `MEM y (cfg_analyze fn).cfg_dfs_post` by
    metis_tac[reachable_mem_dfs_post] >>
  `frontier_of (dom_analyze (cfg_analyze fn) fn) n =
   fmap_lookup_list
     (compute_df (cfg_analyze fn)
       (compute_idom (cfg_analyze fn).cfg_dfs_post (fn_entry_label fn)
         (dom_sets_of fn (dom_fixpoint fn)) (fn_labels fn))
       (cfg_analyze fn).cfg_dfs_post (LENGTH (fn_labels fn))) n` by
    (mp_tac frontier_bridge >> simp[]) >>
  (* Substitute frontier_of, then expand compute_df_mem.
     CRITICAL: Do NOT establish fn_entry_label fn = SOME bb.bb_label before
     this point, simp would substitute inside NRC terms, creating a mismatch
     with helper theorems that produce fn_entry_label fn. *)
  fs[] >> simp[compute_df_mem] >>
  (* Establish strict_dom <=> dom target_idom, using fn_entry_label_def locally *)
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) n y <=>
   dominates (dom_analyze (cfg_analyze fn) fn) n target_idom` by
    (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `bb`, `n`, `y`]
               strict_dom_iff_dom_idom) >>
     simp[LET_THM, venomInstTheory.fn_entry_label_def]) >>
  `strict_dominates (dom_analyze (cfg_analyze fn) fn) target_idom y` by
    (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `y`, `target_idom`]
               idom_is_immediate_proof) >>
     simp[LET_THM, venomInstTheory.fn_entry_label_def]) >>
  `dominates (dom_analyze (cfg_analyze fn) fn) target_idom y` by
    fs[dominatorDefsTheory.strict_dominates_def] >>
  `target_idom <> y` by
    fs[dominatorDefsTheory.strict_dominates_def] >>
  `cfg_reachable_of (cfg_analyze fn) target_idom` by
    (irule dominates_reachable >>
     fs[dominatorDefsTheory.strict_dominates_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `MEM target_idom (fn_labels fn)` by
    (mp_tac (Q.SPECL [`fn`, `target_idom`] reachable_mem_fn_labels) >>
     simp[]) >>
  eq_tac
  >- (
    (* Forward: NRC path avoiding target_idom => dom n p /\ ~strict_dom n y *)
    rpt strip_tac >>
    `cfg_reachable_of (cfg_analyze fn) p` by metis_tac[] >>
    qexists_tac `p` >> simp[] >>
    conj_tac
    >- (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `k`, `p`, `n`]
                  nrc_idom_dominates) >> simp[LET_THM])
    >- (
      (* Show ~strict_dom n y, i.e. ~dom n target_idom *)
      CCONTR_TAC >> fs[] >>
      `dominates (dom_analyze (cfg_analyze fn) fn) target_idom p` by
        (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `bb`, `target_idom`, `y`, `p`]
                   dom_dominates_pred) >> simp[]) >>
      (* Get NRC path from p to target_idom via MATCH_MP pattern *)
      mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `target_idom`, `p`]
                dominates_nrc_idom_rw) >>
      impl_tac >- simp[] >>
      CONV_TAC (DEPTH_CONV BETA_CONV) >>
      disch_then (fn th => assume_tac (MATCH_MP th
        (ASSUME ``dominates (dom_analyze (cfg_analyze fn) fn) target_idom p``))) >>
      fs[] >> rename1 `NRC _ k1 p target_idom` >>
      (* k1 >= k contradicts avoidance condition *)
      `k <= k1` by (
        CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS_EQUAL] >>
        `~NRC (idom_step (compute_idom (cfg_analyze fn).cfg_dfs_post
           (fn_entry_label fn) (dom_sets_of fn (dom_fixpoint fn))
           (fn_labels fn))) k1 p target_idom` by metis_tac[] >>
        metis_tac[]) >>
      Cases_on `k1 = k`
      >- (gvs[] >>
          mp_tac (Q.SPECL [`k:num`, `p:string`, `n:string`,
                            `target_idom:string`] nrc_det_spec) >>
          metis_tac[idom_step_deterministic])
      >- (
        `k < k1` by simp[] >>
        mp_tac (Q.SPECL [`k:num`, `k1:num`, `p:string`,
                          `target_idom:string`, `n:string`] nrc_prefix_spec) >>
        impl_tac >- metis_tac[idom_step_deterministic] >>
        strip_tac >>
        `dominates (dom_analyze (cfg_analyze fn) fn) target_idom n` by
          (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `k1 - k`, `n`,
                             `target_idom`] nrc_idom_dominates) >>
           simp[LET_THM]) >>
        `n = target_idom` by
          (mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `n`, `target_idom`]
                    dominates_antisym_proof) >>
           simp[LET_THM] >> metis_tac[dominates_reachable]) >>
        metis_tac[])))
  >- (
    (* Backward: dom n p /\ ~strict_dom n y => NRC conditions *)
    strip_tac >>
    `~dominates (dom_analyze (cfg_analyze fn) fn) n target_idom` by
      (fs[] >> strip_tac >> fs[]) >>
    `cfg_reachable_of (cfg_analyze fn) p` by metis_tac[] >>
    `MEM p (fn_labels fn)` by
      (mp_tac (Q.SPECL [`fn`, `p`] reachable_mem_fn_labels) >> simp[]) >>
    (* Get NRC path from p to n via MATCH_MP pattern *)
    mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `n`, `p`]
              dominates_nrc_idom_rw) >>
    impl_tac >- simp[] >>
    CONV_TAC (DEPTH_CONV BETA_CONV) >>
    disch_then (fn th => assume_tac (MATCH_MP th
      (ASSUME ``dominates (dom_analyze (cfg_analyze fn) fn) n p``))) >>
    fs[] >> rename1 `NRC _ k0 p n` >>
    conj_tac
    >- (strip_tac >> gvs[] >>
      mp_tac (Q.SPECL [`fn`, `cfg_analyze fn`, `target_idom`]
                dom_self_proof) >> simp[])
    >- (qexistsl_tac [`p`, `k0`] >> simp[] >>
      rpt gen_tac >> CCONTR_TAC >> fs[] >> metis_tac[]))
QED



(* Helper: split LRC at SNOC to get predecessor *)
Triviality lrc_snoc_pred[local]:
  !R ls0 x (a:'a) c.
    LRC R (SNOC x ls0) a c ==>
    ?pred. LRC R ls0 a pred /\ R pred c
Proof
  rpt strip_tac >>
  sg `?b. LRC R ls0 a b /\ LRC R [x] b c`
  >- metis_tac[lrc_append, rich_listTheory.SNOC_APPEND] >>
  fs[listTheory.LRC_def] >> qexists_tac `b` >> simp[]
QED

(* Every reachable non-entry block has a reachable predecessor NOT dominated by it.
   Proof: complete induction on LRC path length from entry to lbl.
   In each step, take the predecessor pred of lbl on the path.
   If ~dominates lbl pred, done. Otherwise, lbl is on the path to pred,
   giving a strictly shorter path, and the IH applies. *)
Theorem exists_pred_not_dominated:
  !fn bb lbl.
    wf_function fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) lbl /\
    lbl <> bb.bb_label ==>
    ?p. MEM p (cfg_preds_of (cfg_analyze fn) lbl) /\
        cfg_reachable_of (cfg_analyze fn) p /\
        ~dominates (dom_analyze (cfg_analyze fn) fn) lbl p
Proof
  rpt strip_tac >>
  qabbrev_tac `R = \a b. MEM b (cfg_succs_of (cfg_analyze fn) a)` >>
  sg `!n ls. LENGTH ls = n ==>
       LRC R ls bb.bb_label lbl ==>
       ?p. MEM p (cfg_preds_of (cfg_analyze fn) lbl) /\
           cfg_reachable_of (cfg_analyze fn) p /\
           ~dominates (dom_analyze (cfg_analyze fn) fn) lbl p`
  >- (
    completeInduct_on `n` >> rpt strip_tac >>
    sg `ls <> []` >- (Cases_on `ls` >> fs[listTheory.LRC_def]) >>
    sg `?ls0 x. ls = SNOC x ls0` >- metis_tac[rich_listTheory.SNOC_CASES] >>
    gvs[] >>
    drule lrc_snoc_pred >> strip_tac >>
    (* pred is a CFG predecessor of lbl *)
    sg `MEM pred (cfg_preds_of (cfg_analyze fn) lbl)`
    >- (fs[Abbr `R`] >> metis_tac[cfgAnalysisPropsTheory.cfg_edge_symmetry_uncond]) >>
    (* pred is reachable *)
    sg `cfg_reachable_of (cfg_analyze fn) pred`
    >- (irule lrc_to_reachable >> simp[] >> qexists_tac `ls0` >> simp[Abbr `R`]) >>
    (* Case: does lbl dominate pred? *)
    Cases_on `dominates (dom_analyze (cfg_analyze fn) fn) lbl pred` >| [
      (* YES: lbl dominates pred, so lbl is on the path to pred *)
      sg `lbl = pred \/ MEM lbl ls0`
      >- (qspecl_then [`fn`, `bb`, `ls0`, `pred`] mp_tac dom_on_every_path >>
          (impl_tac >- simp[Abbr `R`]) >>
          disch_then (qspec_then `lbl` mp_tac) >>
          fs[dominatorDefsTheory.dominates_def]) >>
      gvs[] >| [
        (* lbl = pred: path ls0 is strictly shorter *)
        first_x_assum (qspec_then `LENGTH ls0` mp_tac) >>
        simp[rich_listTheory.LENGTH_SNOC] >>
        disch_then (qspec_then `ls0` mp_tac) >> simp[],
        (* MEM lbl ls0: split path at lbl, prefix is strictly shorter *)
        drule_all lrc_split_at >> strip_tac >> gvs[] >>
        first_x_assum (qspec_then `LENGTH l1` mp_tac) >>
        simp[rich_listTheory.LENGTH_SNOC, listTheory.LENGTH_APPEND] >>
        disch_then (qspec_then `l1` mp_tac) >> simp[]
      ],
      (* NO: pred is the witness *)
      qexists_tac `pred` >> simp[]
    ]) >>
  sg `?ls. LRC R ls bb.bb_label lbl`
  >- (simp[Abbr `R`] >> irule reachable_has_lrc_path >> simp[]) >>
  first_x_assum (qspecl_then [`LENGTH ls`, `ls`] mp_tac) >> simp[]
QED

(* dom_pre_order: dominators have lower DFS pre-order index.
   If d strictly dominates lbl, then INDEX_OF d pre < INDEX_OF lbl pre.
   Proof: by contradiction. If INDEX_OF d >= INDEX_OF lbl, since d ≠ lbl
   we get INDEX_OF d > INDEX_OF lbl.
   - d = entry: d = HD(pre), INDEX_OF d = 0, INDEX_OF lbl < 0 impossible.
   - d ≠ entry: dfs_pre_walk_avoiding_path gives LRC path avoiding d.
     But dom_on_every_path says d is on every path. Contradiction. *)
Theorem dom_pre_order:
  !fn bb d lbl.
    wf_function fn /\
    entry_block fn = SOME bb /\
    cfg_reachable_of (cfg_analyze fn) lbl /\
    MEM d (fmap_lookup_list (dom_analyze (cfg_analyze fn) fn).da_dominators lbl) /\
    d <> lbl ==>
    ?i j. INDEX_OF d (cfg_analyze fn).cfg_dfs_pre = SOME i /\
          INDEX_OF lbl (cfg_analyze fn).cfg_dfs_pre = SOME j /\
          i < j
Proof
  rpt strip_tac >>
  qabbrev_tac `succs = build_succs fn.fn_blocks` >>
  qabbrev_tac `pre = (cfg_analyze fn).cfg_dfs_pre` >>
  (* Establish pre = SND(dfs_pre_walk succs [] bb.bb_label) *)
  `pre = SND (dfs_pre_walk succs [] bb.bb_label)` by (
    unabbrev_all_tac >>
    simp[cfgHelpersTheory.cfg_analyze_dfs_pre] >>
    Cases_on `entry_block fn` >> fs[]) >>
  (* ALL_DISTINCT pre *)
  `ALL_DISTINCT pre` by
    metis_tac[cfgHelpersTheory.dfs_pre_walk_distinct_disj] >>
  (* Membership via dom_reachable + reachable_mem_dfs_pre *)
  `cfg_reachable_of (cfg_analyze fn) d` by metis_tac[dom_reachable] >>
  `MEM lbl pre /\ MEM d pre` by
    metis_tac[reachable_mem_dfs_pre, markerTheory.Abbrev_def] >>
  (* Contradiction argument *)
  SPOSE_NOT_THEN ASSUME_TAC >>
  `?i. INDEX_OF d pre = SOME i` by
    (Cases_on `INDEX_OF d pre` >> fs[INDEX_OF_eq_NONE]) >>
  `?j. INDEX_OF lbl pre = SOME j` by
    (Cases_on `INDEX_OF lbl pre` >> fs[INDEX_OF_eq_NONE]) >>
  `~(i < j)` by metis_tac[] >>
  `i <> j` by (
    CCONTR_TAC >> gvs[] >> fs[listTheory.INDEX_OF_eq_SOME]) >>
  `j < i` by simp[] >>
  Cases_on `d = bb.bb_label`
  >- ((* d = entry: entry is HD of pre, so i = 0, j < 0 impossible *)
      `pre <> [] /\ HD pre = d` by (
        gvs[] >>
        mp_tac (INST_TYPE [alpha |-> ``:string``]
                  cfgHelpersTheory.dfs_pre_walk_entry_hd
                |> Q.SPECL [`succs`, `[]`, `bb.bb_label`]) >> simp[]) >>
      mp_tac (INST_TYPE [alpha |-> ``:string``]
                cfgHelpersTheory.index_of_hd_min
              |> Q.SPECL [`pre`, `d`, `lbl`, `j`, `i`]) >> simp[])
  >- ((* d ≠ entry: avoiding path exists *)
      mp_tac (CONJUNCT1 cfgHelpersTheory.dfs_pre_walk_avoiding_path) >>
      disch_then (qspecl_then [`succs`, `[]`, `bb.bb_label`,
                               `lbl`, `d`, `i`, `j`] mp_tac) >>
      impl_tac >- (fs[] >> metis_tac[]) >>
      strip_tac >>
      (* Convert fmap_lookup_list succs path to cfg_succs_of path *)
      `cfg_succs_of (cfg_analyze fn) = fmap_lookup_list succs` by
        (unabbrev_all_tac >> simp[cfgHelpersTheory.cfg_analyze_succs]) >>
      `LRC (\a b. MEM b (cfg_succs_of (cfg_analyze fn) a)) ls bb.bb_label lbl` by
        (qpat_x_assum `LRC _ ls _ _` mp_tac >> rw[]) >>
      mp_tac dom_on_every_path >>
      disch_then (qspecl_then [`fn`, `bb`, `ls`, `lbl`] mp_tac) >>
      simp[] >> metis_tac[])
QED

(* Dominator chain: dominators of a node are totally ordered *)
Theorem dominates_chain_proof:
  ∀fn cfg a b c.
    wf_function fn ∧
    cfg = cfg_analyze fn ∧
    cfg_reachable_of cfg c ⇒
    let dom = dom_analyze cfg fn in
    dominates dom a c ∧ dominates dom b c ⇒
    dominates dom a b ∨ dominates dom b a
Proof
  rpt gen_tac >> simp_tac std_ss [LET_THM] >> strip_tac >>
  `∃bb. entry_block fn = SOME bb` by (
    fs[venomWfTheory.wf_function_def, venomWfTheory.fn_has_entry_def] >>
    simp[venomInstTheory.entry_block_def] >>
    Cases_on `fn.fn_blocks` >> gvs[]) >>
  fs[dominatorDefsTheory.dominates_def] >>
  metis_tac[dom_chain]
QED
