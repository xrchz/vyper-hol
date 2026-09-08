(*
 * Tail Merge Pass — Main Proofs
 *
 * run_block_sim: Generalized block simulation via canonical instructions
 * halting_sig_equiv: Blocks with same signature produce equivalent results
 * tail_merge_fn_correct: The tail merge pass preserves function semantics
 *)

Theory tailMergeProof
Ancestors
  tailMergeSim tailMergeHelpers tailMergeStep tailMergeDefs stateEquiv
  cfgTransform venomState venomExecSemantics venomInst
  venomWf cfgTransformProofs execEquivProofs stateEquivProofs
  venomInstProps venomExecProps execEquivParamProps

(* ================================================================
   Section 1: lookup_block in transformed function
   ================================================================ *)

Theorem lookup_block_MAP_subst[local]:
  !m bbs lbl bb.
    lookup_block lbl bbs = SOME bb ==>
    lookup_block lbl (MAP (subst_block_labels_block m) bbs) =
      SOME (subst_block_labels_block m bb)
Proof
  Induct_on `bbs` >> rw[lookup_block_def, listTheory.FIND_thm] >>
  gvs[GSYM lookup_block_def]
QED

Theorem lookup_block_FILTER_not_mem[local]:
  !bbs lbl removed bb.
    lookup_block lbl bbs = SOME bb /\ ~MEM lbl removed ==>
    lookup_block lbl (FILTER (\bb. ~MEM bb.bb_label removed) bbs) = SOME bb
Proof
  Induct >> rw[lookup_block_def, listTheory.FIND_thm] >>
  gvs[GSYM lookup_block_def]
QED

Theorem lookup_block_tail_merge[local]:
  !m bbs lbl bb removed.
    lookup_block lbl bbs = SOME bb /\ ~MEM lbl removed ==>
    lookup_block lbl
      (FILTER (\bb'. ~MEM bb'.bb_label removed)
              (MAP (subst_block_labels_block m) bbs)) =
    SOME (subst_block_labels_block m bb)
Proof
  rw[] >> irule lookup_block_FILTER_not_mem >> simp[] >>
  irule lookup_block_MAP_subst >> simp[]
QED

(* ================================================================
   Section 2: Properties of block_sigs and compute_merge_map
   ================================================================ *)

Theorem block_sigs_excludes_entry[local]:
  !func entry bbs lbl sig.
    MEM (lbl, sig) (block_sigs func entry bbs) ==> lbl <> entry
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >> rw[] >> gvs[]
QED

Theorem block_sigs_MEM_blocks[local]:
  !func entry bbs lbl sig.
    MEM (lbl, sig) (block_sigs func entry bbs) ==>
    ?bb. MEM bb bbs /\ bb.bb_label = lbl /\ sig = block_signature bb
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >> rw[] >> gvs[] >> metis_tac[]
QED

Theorem block_sigs_FST_subset[local]:
  !func entry bbs lbl.
    MEM lbl (MAP FST (block_sigs func entry bbs)) ==>
    ?bb. MEM bb bbs /\ bb.bb_label = lbl
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >> rw[] >> gvs[] >>
  metis_tac[]
QED

Theorem block_sigs_all_distinct_FST[local]:
  !func entry bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    ALL_DISTINCT (MAP FST (block_sigs func entry bbs))
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >> rw[] >> gvs[] >>
  CCONTR_TAC >> gvs[] >>
  drule block_sigs_FST_subset >> strip_tac >>
  gvs[listTheory.MEM_MAP]
QED

Theorem compute_merge_map_source[local]:
  !sigs groups lbl keeper.
    MEM (lbl, keeper) (compute_merge_map sigs groups) ==>
    ?sig. MEM (lbl, SOME sig) sigs
Proof
  Induct >> simp[compute_merge_map_def] >> rw[] >>
  Cases_on `h` >> gvs[compute_merge_map_def] >>
  Cases_on `r` >> gvs[compute_merge_map_def] >-
    metis_tac[] >>
  Cases_on `ALOOKUP groups x` >> gvs[] >> metis_tac[]
QED

Theorem compute_merge_map_keeper_gen[local]:
  !sigs groups lbl keeper.
    MEM (lbl, keeper) (compute_merge_map sigs groups) ==>
    ?sig. MEM (lbl, SOME sig) sigs /\
          (MEM (keeper, SOME sig) sigs \/ ALOOKUP groups sig = SOME keeper)
Proof
  Induct_on `sigs` >- simp[compute_merge_map_def] >>
  rpt gen_tac >> Cases_on `h` >> Cases_on `r` >| [
    simp[compute_merge_map_def] >>
    strip_tac >> first_x_assum drule >> strip_tac >>
    qexists_tac `sig` >> simp[],
    simp[compute_merge_map_def] >>
    Cases_on `ALOOKUP groups x` >> simp[] >| [
      strip_tac >> first_x_assum drule >> strip_tac >>
      fs[alistTheory.ALOOKUP_def] >>
      Cases_on `sig = x` >> fs[] >-
        (qexists_tac `x` >> simp[]) >>
      qexists_tac `sig` >> fs[],
      strip_tac >> fs[] >-
        (qexists_tac `x` >> simp[]) >>
      first_x_assum drule >> strip_tac >>
      qexists_tac `sig` >> fs[]
    ]
  ]
QED

Theorem compute_merge_map_keeper_same_sig[local]:
  !sigs lbl keeper.
    MEM (lbl, keeper) (compute_merge_map sigs []) ==>
    ?sig. MEM (lbl, SOME sig) sigs /\ MEM (keeper, SOME sig) sigs
Proof
  rpt strip_tac >> drule compute_merge_map_keeper_gen >>
  strip_tac >> qexists_tac `sig` >> fs[alistTheory.ALOOKUP_def]
QED

Theorem compute_merge_map_not_entry[local]:
  !func entry bbs lbl keeper.
    MEM (lbl, keeper) (compute_merge_map (block_sigs func entry bbs) []) ==>
    lbl <> entry /\ keeper <> entry
Proof
  rpt strip_tac >>
  drule compute_merge_map_keeper_same_sig >> strip_tac >| [
    drule compute_merge_map_source >> strip_tac >>
    drule_at Any block_sigs_excludes_entry >> simp[],
    imp_res_tac block_sigs_excludes_entry >> gvs[]
  ]
QED

Theorem compute_merge_map_halting[local]:
  !func entry bbs lbl keeper.
    MEM (lbl, keeper) (compute_merge_map (block_sigs func entry bbs) []) ==>
    ?bb_lbl bb_kpr sig.
      MEM bb_lbl bbs /\ bb_lbl.bb_label = lbl /\
      MEM bb_kpr bbs /\ bb_kpr.bb_label = keeper /\
      block_signature bb_lbl = SOME sig /\
      block_signature bb_kpr = SOME sig /\
      bb_is_halting bb_lbl /\ bb_self_contained bb_lbl /\
      bb_is_halting bb_kpr /\ bb_self_contained bb_kpr
Proof
  rpt strip_tac >>
  drule compute_merge_map_keeper_same_sig >> strip_tac >>
  `?bb1. MEM bb1 bbs /\ bb1.bb_label = lbl /\
         SOME sig = block_signature bb1` by metis_tac[block_sigs_MEM_blocks] >>
  `?bb2. MEM bb2 bbs /\ bb2.bb_label = keeper /\
         SOME sig = block_signature bb2` by metis_tac[block_sigs_MEM_blocks] >>
  qexistsl_tac [`bb1`, `bb2`, `sig`] >>
  gvs[block_signature_def]
QED

(* Sources of compute_merge_map come from sigs *)
Theorem compute_merge_map_FST_subset[local]:
  !sigs groups x.
    MEM x (MAP FST (compute_merge_map sigs groups)) ==>
    MEM x (MAP FST sigs)
Proof
  Induct >- simp[compute_merge_map_def] >>
  rpt gen_tac >> Cases_on `h` >> Cases_on `r` >| [
    simp[compute_merge_map_def] >> metis_tac[],
    simp[compute_merge_map_def] >>
    Cases_on `ALOOKUP groups x'` >> simp[] >| [
      strip_tac >> metis_tac[],
      strip_tac >> gvs[] >> metis_tac[]
    ]
  ]
QED

(* Keepers of compute_merge_map come from groups values *)
Theorem compute_merge_map_SND_subset[local]:
  !sigs groups x.
    MEM x (MAP SND (compute_merge_map sigs groups)) ==>
    MEM x (MAP SND groups) \/ MEM x (MAP FST sigs)
Proof
  Induct >- simp[compute_merge_map_def] >>
  rpt gen_tac >> Cases_on `h` >> Cases_on `r` >| [
    (* (lbl, NONE) *)
    simp[compute_merge_map_def] >>
    strip_tac >> res_tac >> simp[],
    (* (lbl, SOME sig) *)
    simp[compute_merge_map_def] >>
    Cases_on `ALOOKUP groups x'` >> simp[] >| [
      (* ALOOKUP = NONE: lbl added to groups *)
      strip_tac >>
      first_x_assum (qspecl_then [`(x', q)::groups`, `x`] mp_tac) >>
      simp[] >> strip_tac >> gvs[] >> metis_tac[],
      (* ALOOKUP = SOME keeper *)
      strip_tac >> gvs[] >| [
        (* x is the keeper from ALOOKUP *)
        rename1 `ALOOKUP groups _ = SOME keeper` >>
        drule alistTheory.ALOOKUP_MEM >> strip_tac >>
        `MEM keeper (MAP SND groups)` by
          metis_tac[listTheory.MEM_MAP, pairTheory.SND] >>
        simp[],
        (* x from recursive call *)
        res_tac >> simp[]
      ]
    ]
  ]
QED

(* Sources (MAP FST) and keepers (MAP SND) of compute_merge_map are disjoint.
   Direct induction: a label is either stored in groups (keeper) or emitted (source),
   never both, because ALL_DISTINCT prevents re-processing. *)
Theorem compute_merge_map_disjoint_gen[local]:
  !sigs groups.
    ALL_DISTINCT (MAP FST sigs) /\
    DISJOINT (set (MAP FST sigs)) (set (MAP SND groups)) ==>
    DISJOINT (set (MAP FST (compute_merge_map sigs groups)))
             (set (MAP SND (compute_merge_map sigs groups)))
Proof
  Induct >- simp[compute_merge_map_def, pred_setTheory.DISJOINT_EMPTY] >>
  rpt gen_tac >> Cases_on `h` >> Cases_on `r` >- (
    (* (lbl, NONE): skip *)
    simp[compute_merge_map_def] >> strip_tac >>
    first_x_assum (qspec_then `groups` mp_tac) >> simp[] >>
    disch_then irule >>
    gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
    metis_tac[]
  ) >>
  (* (lbl, SOME sig) — NONE case solved by simp, only SOME remains *)
  rename1 `(q, SOME sig)` >>
  REWRITE_TAC[compute_merge_map_def] >>
  Cases_on `ALOOKUP groups sig` >> simp[] >>
  (* ALOOKUP = SOME keeper: (q, keeper) emitted *)
  strip_tac >>
  rename1 `ALOOKUP groups sig = SOME keeper` >>
  `MEM keeper (MAP SND groups)` by (
    drule alistTheory.ALOOKUP_MEM >> strip_tac >>
    metis_tac[listTheory.MEM_MAP, pairTheory.SND]) >>
  (* keeper not in FST(rec): keeper is from groups, not sigs *)
  `~MEM keeper (MAP FST (compute_merge_map sigs groups))` by (
    CCONTR_TAC >> gvs[] >>
    drule compute_merge_map_FST_subset >> strip_tac >>
    gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
    metis_tac[]) >>
  (* q <> keeper: q not in groups, keeper is *)
  `q <> keeper` by (
    gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
    metis_tac[]) >>
  (* q not in SND(rec): q not in sigs tail or groups *)
  `~MEM q (MAP SND (compute_merge_map sigs groups))` by (
    CCONTR_TAC >> gvs[] >>
    drule compute_merge_map_SND_subset >> strip_tac >> gvs[]) >>
  simp[]
QED

Theorem compute_merge_map_disjoint[local]:
  !sigs.
    ALL_DISTINCT (MAP FST sigs) ==>
    DISJOINT (set (MAP FST (compute_merge_map sigs [])))
             (set (MAP SND (compute_merge_map sigs [])))
Proof
  rpt strip_tac >> irule compute_merge_map_disjoint_gen >>
  simp[pred_setTheory.DISJOINT_EMPTY]
QED

Theorem compute_merge_map_SND_not_FST[local]:
  !sigs lbl keeper.
    ALL_DISTINCT (MAP FST sigs) /\
    MEM (lbl, keeper) (compute_merge_map sigs []) ==>
    ~MEM keeper (MAP FST (compute_merge_map sigs []))
Proof
  rpt strip_tac >>
  drule compute_merge_map_disjoint >> strip_tac >>
  `MEM keeper (MAP SND (compute_merge_map sigs []))` by
    metis_tac[listTheory.MEM_MAP, pairTheory.SND] >>
  gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
      pred_setTheory.IN_INSERT, listTheory.MEM] >>
  metis_tac[]
QED

(* ALL_DISTINCT of FLAT means distinct sublists are disjoint *)
Theorem all_distinct_flat_disjoint[local]:
  !ls (i:num) j x.
    ALL_DISTINCT (FLAT ls) /\ i < LENGTH ls /\ j < LENGTH ls /\ i <> j /\
    MEM x (EL i ls) /\ MEM x (EL j ls) ==> F
Proof
  rpt strip_tac >>
  wlog_tac `i < j` [`i`, `j`] >- (`j < i` by simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (FLAT (TAKE (SUC i) ls) ++ FLAT (DROP (SUC i) ls))`
    by metis_tac[listTheory.FLAT_APPEND, listTheory.TAKE_DROP] >>
  fs[listTheory.ALL_DISTINCT_APPEND] >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >>
  `SUC i <= LENGTH ls` by simp[] >>
  conj_tac >- (
    (* MEM x (FLAT (TAKE (SUC i) ls)): EL i ls is in TAKE (SUC i) ls *)
    simp[listTheory.MEM_FLAT] >>
    qexists_tac `EL i ls` >> simp[] >>
    `i < LENGTH (TAKE (SUC i) ls)` by simp[listTheory.LENGTH_TAKE] >>
    `EL i (TAKE (SUC i) ls) = EL i ls` by simp[listTheory.EL_TAKE] >>
    metis_tac[listTheory.EL_MEM]) >>
  (* MEM x (FLAT (DROP (SUC i) ls)): EL j ls is in DROP (SUC i) ls *)
  simp[listTheory.MEM_FLAT] >>
  qexists_tac `EL j ls` >> simp[] >>
  `j - SUC i < LENGTH (DROP (SUC i) ls)` by simp[listTheory.LENGTH_DROP] >>
  `(j - SUC i) + SUC i = j` by simp[] >>
  `EL (j - SUC i) (DROP (SUC i) ls) = EL j ls`
    by metis_tac[listTheory.EL_DROP] >>
  metis_tac[listTheory.EL_MEM]
QED

(* Self-contained block: operand Var at instruction i was output of
   earlier instruction, so it's in the var_map *)
Theorem self_contained_operand_in_map[local]:
  !bb vm i v.
    bb_self_contained bb /\
    i < LENGTH bb.bb_instructions /\
    MEM (Var v) (EL i bb.bb_instructions).inst_operands /\
    (!j w. j < i /\ j < LENGTH bb.bb_instructions /\
           MEM w (EL j bb.bb_instructions).inst_outputs ==>
           ?idx. ALOOKUP vm w = SOME idx) ==>
    ?idx. ALOOKUP vm v = SOME idx
Proof
  rw[bb_self_contained_def] >>
  qpat_x_assum `!i v. _ /\ MEM (Var _) _ ==> _`
    (qspecl_then [`i`, `v`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  first_x_assum (qspecl_then [`j`, `v`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >> simp[]
QED

(* ALL_DISTINCT outputs + self-contained: operand var not in same
   instruction outputs *)
Theorem self_contained_operand_not_output[local]:
  !bb i v.
    bb_self_contained bb /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    i < LENGTH bb.bb_instructions /\
    MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
    ~MEM v (EL i bb.bb_instructions).inst_outputs
Proof
  rw[bb_self_contained_def] >>
  qpat_x_assum `!i v. _ /\ MEM (Var _) _ ==> _`
    (qspecl_then [`i`, `v`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  strip_tac >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  qsuff_tac `F` >- simp[] >>
  qabbrev_tac `outs = MAP (\inst. inst.inst_outputs) bb.bb_instructions` >>
  `i < LENGTH outs /\ j < LENGTH outs` by simp[Abbr `outs`] >>
  `MEM v (EL j outs) /\ MEM v (EL i outs)`
    by simp[Abbr `outs`, listTheory.EL_MAP] >>
  `j <> i` by simp[] >>
  `ALL_DISTINCT (FLAT outs)` by simp[Abbr `outs`] >>
  metis_tac[all_distinct_flat_disjoint]
QED

(* ================================================================
   Section 3: Generalized simulation for exec_block
   ================================================================ *)

(* Lifting result_equiv through exec_block's terminator wrapping *)
Theorem result_equiv_term_wrap[local]:
  !r1 r2.
    result_equiv UNIV r1 r2 ==>
    result_equiv UNIV
      (case r1 of OK s'' => if s''.vs_halted then Halt s'' else OK s''
                | Halt s' => Halt s' | Abort a s' => Abort a s'
                | IntRet v s' => IntRet v s' | Error e => Error e)
      (case r2 of OK s'' => if s''.vs_halted then Halt s'' else OK s''
                | Halt s' => Halt s' | Abort a s' => Abort a s'
                | IntRet v s' => IntRet v s' | Error e => Error e)
Proof
  Cases >> Cases >> simp[result_equiv_def] >> rw[] >>
  gvs[state_equiv_def, execution_equiv_def, result_equiv_def]
QED

Theorem wf_terminator_is_last[local]:
  !bb idx. bb_well_formed bb /\
    is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    idx < LENGTH bb.bb_instructions ==>
    idx = PRE (LENGTH bb.bb_instructions)
Proof
  rw[bb_well_formed_def]
QED

Theorem wf_halting_last[local]:
  !bb idx. bb_well_formed bb /\ bb_is_halting bb /\
    is_terminator (EL idx bb.bb_instructions).inst_opcode /\
    idx < LENGTH bb.bb_instructions ==>
    is_halting_opcode (EL idx bb.bb_instructions).inst_opcode
Proof
  rw[bb_well_formed_def, bb_is_halting_def] >>
  `idx = PRE (LENGTH bb.bb_instructions)` by simp[] >>
  gvs[listTheory.LAST_EL]
QED

(* Operand properties for instruction at index idx in self-contained block:
   all Var operands are in the var_map, and not in same inst's outputs *)
Theorem canon_inst_operand_props[local]:
  !bb vm inst vm' ci idx.
    canon_inst vm inst = (vm', ci) /\
    bb_self_contained bb /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    idx < LENGTH bb.bb_instructions /\
    EL idx bb.bb_instructions = inst /\
    (!j v. j < idx /\ j < LENGTH bb.bb_instructions /\
           MEM v (EL j bb.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm v = SOME i) ==>
    (!v. MEM (Var v) inst.inst_operands ==> ?i. ALOOKUP vm v = SOME i) /\
    (!v. MEM (Var v) inst.inst_operands ==> ~MEM v inst.inst_outputs)
Proof
  rpt strip_tac >> gvs[]
  >- (drule_all self_contained_operand_in_map >> simp[])
  >- (drule_all self_contained_operand_not_output >> simp[])
QED


(* Structural properties that follow from same canonical form *)
Theorem canon_inst_structure[local]:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) ==>
    inst1.inst_opcode = inst2.inst_opcode /\
    inst1.inst_id = inst2.inst_id /\
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i l. i < LENGTH inst1.inst_operands /\
           EL i inst1.inst_operands = Label l ==>
           EL i inst2.inst_operands = Label l) /\
    (!i l. i < LENGTH inst2.inst_operands /\
           EL i inst2.inst_operands = Label l ==>
           EL i inst1.inst_operands = Label l) /\
    (!i w. i < LENGTH inst1.inst_operands /\
           EL i inst1.inst_operands = Lit w ==>
           EL i inst2.inst_operands = Lit w) /\
    (!i w. i < LENGTH inst2.inst_operands /\
           EL i inst2.inst_operands = Lit w ==>
           EL i inst1.inst_operands = Lit w)
Proof
  rpt strip_tac >>
  PairCases_on `ci` >>
  gvs[canon_inst_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >> gvs[] >>
  metis_tac[canon_operands_label_lit, canon_outputs_length]
QED

(* Build sim_pre from canonical instruction structure *)
Theorem canon_inst_sim_pre[local]:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci s1 s2.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) /\
    sim_inv vm1 vm2 s1 s2 /\
    (!v. MEM (Var v) inst1.inst_operands ==> ?i. ALOOKUP vm1 v = SOME i) /\
    (!v. MEM (Var v) inst2.inst_operands ==> ?i. ALOOKUP vm2 v = SOME i) /\
    (!v. MEM (Var v) inst1.inst_operands ==> ~MEM v inst1.inst_outputs) /\
    (!v. MEM (Var v) inst2.inst_operands ==> ~MEM v inst2.inst_outputs) ==>
    sim_pre inst1 inst2 s1 s2
Proof
  rpt strip_tac >>
  (* Get structural properties via targeted MATCH_MP *)
  (let val cs = REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL canon_inst_structure)
   in
     qpat_x_assum `canon_inst vm1 _ = _`
       (fn th1 => qpat_x_assum `canon_inst vm2 _ = _`
         (fn th2 => assume_tac (MATCH_MP (MATCH_MP cs th1) th2) >>
                    assume_tac th1 >> assume_tac th2))
   end) >>
  fs[] >>
  (* Get MAP eval_operand equality via targeted MATCH_MP *)
  (let val cem = REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL canon_inst_eval_match)
   in
     qpat_x_assum `canon_inst vm1 _ = _`
       (fn th1 => qpat_x_assum `canon_inst vm2 _ = _`
         (fn th2 => qpat_x_assum `sim_inv _ _ _ _`
           (fn th3 =>
              mp_tac (MATCH_MP (MATCH_MP (MATCH_MP cem th1) th2) th3) >>
              assume_tac th1 >> assume_tac th2 >> assume_tac th3)))
   end) >>
  rpt (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (* Assemble sim_pre: all pieces are in assumptions *)
  fs[sim_pre_def, sim_inv_def,
     listTheory.LIST_EQ_REWRITE, listTheory.EL_MAP]
QED

(* Extending a var map with (v, LENGTH vm) preserves wf *)
Theorem var_map_wf_cons[local]:
  !vm v. var_map_wf vm ==> var_map_wf ((v, LENGTH vm)::vm)
Proof
  rw[var_map_wf_def, alistTheory.ALOOKUP_def] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> simp[]
QED

(* Single-map: canon_outputs preserves var_map_wf *)
Theorem canon_outputs_wf[local]:
  !vs vm vm' idxs.
    canon_outputs vm vs = (vm', idxs) /\ var_map_wf vm ==> var_map_wf vm'
Proof
  Induct >- simp[canon_outputs_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[canon_outputs_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum irule >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[var_map_wf_cons]
QED

(* Single-map: canon_operands preserves var_map_wf *)
Theorem canon_operands_wf[local]:
  !ops vm vm' cops.
    canon_operands vm ops = (vm', cops) /\ var_map_wf vm ==> var_map_wf vm'
Proof
  Induct >- simp[canon_operands_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[canon_operands_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum irule >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  Cases_on `h` >> gvs[canon_operand_def, LET_THM] >>
  BasicProvers.every_case_tac >> gvs[] >>
  simp[var_map_wf_cons]
QED

(* Single-map: canon_inst preserves var_map_wf *)
Theorem canon_inst_wf[local]:
  !vm inst vm' ci.
    canon_inst vm inst = (vm', ci) /\ var_map_wf vm ==> var_map_wf vm'
Proof
  rw[canon_inst_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  irule canon_operands_wf >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  irule canon_outputs_wf >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  simp[]
QED

(* Helper: same cop from same-length wf maps ==> same length after *)
Theorem canon_operand_eq_length[local]:
  !op1 op2 vm1 vm2 vm1' vm2' cop.
    canon_operand vm1 op1 = (vm1', cop) /\
    canon_operand vm2 op2 = (vm2', cop) /\
    var_map_wf vm1 /\ var_map_wf vm2 /\
    LENGTH vm1 = LENGTH vm2 ==>
    LENGTH vm1' = LENGTH vm2' /\ var_map_wf vm1' /\ var_map_wf vm2'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op1` >> Cases_on `op2`
  >> gvs[canon_operand_def, LET_THM]
  >> rpt (BasicProvers.FULL_CASE_TAC >> gvs[])
  >> simp[var_map_wf_cons]
  >> gvs[var_map_wf_def]
  >> rpt strip_tac >> BasicProvers.every_case_tac >> gvs[]
  >> res_tac >> simp[]
QED

(* LENGTH equality: canon_operands with same cops preserves LENGTH equality *)
Theorem canon_operands_map_eq_length[local]:
  !ops1 ops2 vm1 vm2 vm1' vm2' cops.
    canon_operands vm1 ops1 = (vm1', cops) /\
    canon_operands vm2 ops2 = (vm2', cops) /\
    var_map_wf vm1 /\ var_map_wf vm2 /\
    LENGTH vm1 = LENGTH vm2 ==>
    LENGTH vm1' = LENGTH vm2'
Proof
  Induct_on `ops1`
  >- (rw[canon_operands_def] >>
      imp_res_tac canon_operands_length >> gvs[] >>
      imp_res_tac canon_operands_nil >> gvs[])
  >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `canon_operands vm1 (_::_) = _` mp_tac >>
  simp[Once canon_operands_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  `ops2 <> []`
    by (imp_res_tac canon_operands_length >>
        Cases_on `ops2` >> gvs[]) >>
  Cases_on `ops2` >> gvs[] >>
  qpat_x_assum `canon_operands vm2 (_::_) = _` mp_tac >>
  simp[Once canon_operands_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  (let val thm = REWRITE_RULE [GSYM AND_IMP_INTRO]
                   (SPEC_ALL canon_operand_eq_length)
   in
     qpat_x_assum `canon_operand vm1 _ = _`
       (fn th1 => qpat_x_assum `canon_operand vm2 _ = _`
         (fn th2 =>
            mp_tac (MATCH_MP (MATCH_MP thm th1) th2) >>
            assume_tac th1 >> assume_tac th2))
   end) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!ops2 vm1 vm2 vm1' vm2' cops. _`
    (fn ih =>
       qpat_x_assum `canon_operands _ ops1 = _`
         (fn th1 => qpat_x_assum `canon_operands _ t = _`
           (fn th2 =>
              mp_tac (MATCH_MP
                (MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                  (SPEC_ALL ih)) th1) th2) >>
              assume_tac th1 >> assume_tac th2))) >>
  simp[]
QED

(* LENGTH equality: canon_inst with same ci preserves LENGTH equality *)
Theorem canon_inst_map_eq_length[local]:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) /\
    var_map_wf vm1 /\ var_map_wf vm2 /\
    LENGTH vm1 = LENGTH vm2 ==>
    LENGTH vm1' = LENGTH vm2'
Proof
  rw[canon_inst_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >>
  (let val thm = REWRITE_RULE [GSYM AND_IMP_INTRO]
                   (SPEC_ALL canon_operands_map_eq_length)
   in
     qpat_x_assum `canon_operands _ inst1.inst_operands = _`
       (fn th1 => qpat_x_assum `canon_operands _ inst2.inst_operands = _`
         (fn th2 =>
            mp_tac (MATCH_MP (MATCH_MP thm th1) th2) >>
            assume_tac th1 >> assume_tac th2))
   end) >>
  rpt (impl_tac >- (
    imp_res_tac canon_outputs_map_length >>
    imp_res_tac canon_outputs_length >> gvs[] >>
    metis_tac[canon_outputs_wf])) >>
  simp[]
QED

(* Existing ALOOKUP entries are preserved through canon_operands.
   Unlike canon_outputs, this is unconditional because canon_operand
   only adds entries when ALOOKUP returns NONE (no shadowing). *)
Theorem canon_operands_alookup_mono[local]:
  !ops vm vm' cops v idx.
    canon_operands vm ops = (vm', cops) /\
    ALOOKUP vm v = SOME idx ==>
    ALOOKUP vm' v = SOME idx
Proof
  Induct >- simp[canon_operands_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[canon_operands_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  first_x_assum irule >>
  goal_assum (first_assum o mp_then Any mp_tac) >>
  Cases_on `h` >> gvs[canon_operand_def, LET_THM] >>
  BasicProvers.every_case_tac >> gvs[alistTheory.ALOOKUP_def] >>
  Cases_on `s = v` >> gvs[]
QED

(* Complete ALOOKUP characterization for canon_outputs.
   Subsumes: idx_forward, idx_reverse, mem_idx_ge, domain, alookup_orig *)
Theorem canon_outputs_alookup_complete[local]:
  !vs vm vm' idxs.
    canon_outputs vm vs = (vm', idxs) /\
    var_map_wf vm /\ ALL_DISTINCT vs /\
    (!w. MEM w vs ==> ALOOKUP vm w = NONE) ==>
    !v idx. ALOOKUP vm' v = SOME idx <=>
      (?k. k < LENGTH vs /\ v = EL k vs /\ idx = LENGTH vm + k) \/
      (~MEM v vs /\ ALOOKUP vm v = SOME idx)
Proof
  Induct
  >- gvs[canon_outputs_def]
  >> rpt gen_tac >> strip_tac
  >> gvs[canon_outputs_def, LET_THM]
  >> pairarg_tac >> gvs[]
  >> first_x_assum (qspec_then `(h, LENGTH vm)::vm` mp_tac)
  >> disch_then drule
  >> (impl_tac THEN1 (
      (conj_tac THEN1 (irule var_map_wf_cons >> ASM_REWRITE_TAC[])) >>
      gen_tac >> strip_tac >>
      ONCE_REWRITE_TAC[alistTheory.ALOOKUP_def] >>
      IF_CASES_TAC >> gvs[] >>
      first_x_assum (qspec_then `w` mp_tac) >> simp[]))
  >> strip_tac >> rpt gen_tac
  >> pop_assum (fn ih => REWRITE_TAC[ih])
  >> simp[alistTheory.ALOOKUP_def, arithmeticTheory.ADD_CLAUSES]
  >> eq_tac >> rpt strip_tac >> gvs[arithmeticTheory.ADD_CLAUSES]
  >> TRY (disj1_tac >> qexists_tac `SUC k` >> simp[] >> NO_TAC)
  >> TRY (Cases_on `k` >> gvs[arithmeticTheory.ADD_CLAUSES]
          >> TRY (disj2_tac >> simp[] >> NO_TAC)
          >> disj1_tac >> qexists_tac `n` >> simp[] >> NO_TAC)
  >> Cases_on `h = v` >> gvs[]
QED

(* Domain characterization: every entry in var map after canon_outputs/operands/inst
   came from outputs, operand Vars, or was already in the input map *)
Theorem canon_outputs_domain[local]:
  !vs vm vm' idxs v i.
    canon_outputs vm vs = (vm', idxs) /\
    ALOOKUP vm' v = SOME i ==>
    MEM v vs \/ (?j. ALOOKUP vm v = SOME j)
Proof
  Induct >> rw[canon_outputs_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >> rw[] >>
  res_tac >> gvs[] >>
  Cases_on `v = h` >> gvs[]
QED

Theorem canon_operands_domain[local]:
  !ops vm vm' cops v i.
    canon_operands vm ops = (vm', cops) /\
    ALOOKUP vm' v = SOME i ==>
    MEM (Var v) ops \/ (?j. ALOOKUP vm v = SOME j)
Proof
  Induct >> rw[canon_operands_def, LET_THM] >>
  rpt (pairarg_tac >> fs[]) >> rw[] >>
  res_tac >> gvs[] >>
  Cases_on `h` >> gvs[canon_operand_def, LET_THM] >>
  BasicProvers.every_case_tac >> gvs[] >> metis_tac[]
QED

Theorem canon_inst_domain[local]:
  !vm inst vm' ci v i.
    canon_inst vm inst = (vm', ci) /\
    ALOOKUP vm' v = SOME i ==>
    MEM v inst.inst_outputs \/ MEM (Var v) inst.inst_operands \/
    (?j. ALOOKUP vm v = SOME j)
Proof
  rw[canon_inst_def, LET_THM] >>
  pairarg_tac >> fs[] >>
  pairarg_tac >> fs[] >> rw[] >>
  `MEM (Var v) inst.inst_operands \/ ?j. ALOOKUP var_map' v = SOME j`
    by metis_tac[canon_operands_domain] >>
  gvs[] >>
  metis_tac[canon_outputs_domain]
QED

(* When all Var operands are already in the map, canon_operands
   doesn't change the map — it only computes canonical operand forms *)
Theorem canon_operands_map_unchanged[local]:
  !ops vm vm' cops.
    canon_operands vm ops = (vm', cops) /\
    (!v. MEM (Var v) ops ==> ?idx. ALOOKUP vm v = SOME idx) ==>
    vm' = vm
Proof
  Induct >- simp[canon_operands_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[canon_operands_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  `var_map' = vm` by (
    Cases_on `h` >> gvs[canon_operand_def, LET_THM]
    >- (
      `?idx. ALOOKUP vm s = SOME idx` by (
        qpat_x_assum `!v. _ ==> ?idx. _` (qspec_then `s` mp_tac) >>
        simp[]) >>
      gvs[])
    >> BasicProvers.every_case_tac >> gvs[]) >>
  gvs[]
QED

(* Complete ALOOKUP characterization for canon_inst.
   Subsumes: canon_inst_domain, canon_inst_output_idx, canon_inst_alookup_mono *)
Theorem canon_inst_alookup_complete[local]:
  !vm inst vm' ci.
    canon_inst vm inst = (vm', ci) /\
    var_map_wf vm /\
    ALL_DISTINCT inst.inst_outputs /\
    (!w. MEM w inst.inst_outputs ==> ALOOKUP vm w = NONE) /\
    (!v. MEM (Var v) inst.inst_operands ==> ?idx. ALOOKUP vm v = SOME idx) ==>
    !v idx. ALOOKUP vm' v = SOME idx <=>
      (?k. k < LENGTH inst.inst_outputs /\ v = EL k inst.inst_outputs /\
           idx = LENGTH vm + k) \/
      (~MEM v inst.inst_outputs /\ ALOOKUP vm v = SOME idx)
Proof
  rw[canon_inst_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> rw[] >>
  (* All operand vars are in var_map' (post-outputs map) *)
  `!v'. MEM (Var v') inst.inst_operands ==>
        ?idx. ALOOKUP var_map' v' = SOME idx` by (
    rpt strip_tac >>
    `?idx. ALOOKUP vm v' = SOME idx` by metis_tac[] >>
    `~MEM v' inst.inst_outputs` by (
      CCONTR_TAC >> gvs[] >>
      `ALOOKUP vm v' = NONE` by metis_tac[] >> gvs[]) >>
    metis_tac[canon_outputs_alookup_orig]) >>
  (* canon_operands doesn't change the map *)
  `var_map'' = var_map'`
    by metis_tac[canon_operands_map_unchanged] >>
  gvs[] >>
  drule_all canon_outputs_alookup_complete >>
  simp[arithmeticTheory.ADD_COMM]
QED

(* Extract ee from step_sim when both results are OK *)
Theorem step_sim_ok_ee[local]:
  !inst1 inst2 s1 s2 s1' s2'.
    step_sim inst1 inst2 s1 s2 /\
    step_inst_base inst1 s1 = OK s1' /\
    step_inst_base inst2 s2 = OK s2' ==>
    execution_equiv UNIV s1' s2'
Proof
  rpt strip_tac >>
  gvs[step_sim_def]
QED

Theorem var_map_wf_idx_bound[local]:
  !vm v idx. var_map_wf vm /\ ALOOKUP vm v = SOME idx ==> idx < LENGTH vm
Proof
  rpt strip_tac >> fs[var_map_wf_def] >> res_tac
QED

(* var_corr preserved through a step with output opcode *)
Theorem var_corr_after_step_output[local]:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci s1 s2 s1' s2'.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) /\
    var_corr vm1 vm2 s1 s2 /\
    var_map_wf vm1 /\ var_map_wf vm2 /\ LENGTH vm1 = LENGTH vm2 /\
    step_inst_base inst1 s1 = OK s1' /\
    step_inst_base inst2 s2 = OK s2' /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    inst1.inst_opcode <> PHI /\ inst1.inst_opcode <> PARAM /\
    inst1.inst_opcode <> RET /\
    is_output_opcode inst1.inst_opcode /\
    inst1.inst_id = inst2.inst_id /\
    sim_pre inst1 inst2 s1 s2 /\
    ALL_DISTINCT inst1.inst_outputs /\ ALL_DISTINCT inst2.inst_outputs /\
    (!v. (?idx. ALOOKUP vm1 v = SOME idx) ==> ~MEM v inst1.inst_outputs) /\
    (!v. (?idx. ALOOKUP vm2 v = SOME idx) ==> ~MEM v inst2.inst_outputs) /\
    (!v. MEM (Var v) inst1.inst_operands ==> ?idx. ALOOKUP vm1 v = SOME idx) /\
    (!v. MEM (Var v) inst2.inst_operands ==> ?idx. ALOOKUP vm2 v = SOME idx) /\
    (!v. ~MEM v inst1.inst_outputs ==> lookup_var v s1' = lookup_var v s1) /\
    (!v. ~MEM v inst2.inst_outputs ==> lookup_var v s2' = lookup_var v s2) /\
    (!v idx. ALOOKUP vm1' v = SOME idx <=>
      (?k. k < LENGTH inst1.inst_outputs /\ v = EL k inst1.inst_outputs /\
           idx = LENGTH vm1 + k) \/
      (~MEM v inst1.inst_outputs /\ ALOOKUP vm1 v = SOME idx)) /\
    (!v idx. ALOOKUP vm2' v = SOME idx <=>
      (?k. k < LENGTH inst2.inst_outputs /\ v = EL k inst2.inst_outputs /\
           idx = LENGTH vm2 + k) \/
      (~MEM v inst2.inst_outputs /\ ALOOKUP vm2 v = SOME idx))
    ==>
    var_corr vm1' vm2' s1' s2'
Proof
  rpt strip_tac >>
  PURE_REWRITE_TAC[var_corr_def] >> rpt strip_tac >>
  (* Resolve vm1' ALOOKUP via biconditional *)
  qpat_assum `!v idx. ALOOKUP vm1' v = SOME idx <=> _`
    (qspecl_then [`v1`, `idx`] mp_tac) >>
  qpat_assum `ALOOKUP vm1' v1 = SOME idx` (fn th => REWRITE_TAC[th]) >>
  strip_tac
  (* Branch A: v1 is an output variable *)
  >- (
    (* Resolve vm2' ALOOKUP *)
    qpat_assum `!v idx. ALOOKUP vm2' v = SOME idx <=> _`
      (qspecl_then [`v2`, `idx`] mp_tac) >>
    qpat_assum `ALOOKUP vm2' v2 = SOME idx` (fn th => REWRITE_TAC[th]) >>
    strip_tac
    (* Case 1: Both outputs *)
    >- (
      `k = k'` by decide_tac >>
      rpt BasicProvers.VAR_EQ_TAC >>
      mp_tac step_inst_base_output_match >>
      disch_then (qspecl_then [`inst1`, `inst2`, `s1`, `s2`, `s1'`, `s2'`]
        mp_tac) >>
      ASM_REWRITE_TAC[] >>
      disch_then (qspec_then `k` mp_tac) >>
      (impl_tac >- ASM_REWRITE_TAC[]) >>
      disch_then ACCEPT_TAC
    )
    (* Case 2: v1 output, v2 non-output — index contradiction *)
    >> (imp_res_tac var_map_wf_idx_bound >>
        (`F` suffices_by DECIDE_TAC) >> decide_tac)
  )
  (* Branch B: v1 is a non-output variable *)
  >> (
    (* Resolve vm2' ALOOKUP *)
    qpat_assum `!v idx. ALOOKUP vm2' v = SOME idx <=> _`
      (qspecl_then [`v2`, `idx`] mp_tac) >>
    qpat_assum `ALOOKUP vm2' v2 = SOME idx` (fn th => REWRITE_TAC[th]) >>
    strip_tac
    (* Case 3: v1 non-output, v2 output — index contradiction *)
    >- (imp_res_tac var_map_wf_idx_bound >>
        (`F` suffices_by DECIDE_TAC) >> decide_tac)
    (* Case 4: Both non-outputs — use var_corr + step_preserves *)
    >> (
      `lookup_var v1 s1 = lookup_var v2 s2` by (
        qpat_assum `var_corr _ _ s1 s2`
          (mp_tac o REWRITE_RULE [var_corr_def]) >>
        disch_then (qspecl_then [`v1`, `v2`, `idx`] mp_tac) >>
        ASM_REWRITE_TAC[]) >>
      res_tac >> fs[]
    )
  )
QED

(* sim_inv preserved for is_output_opcode case.
   Uses var_corr_after_step_output for the hard var_corr subgoal. *)
Theorem sim_inv_after_step_output[local]:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci s1 s2 s1' s2'.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) /\
    sim_inv vm1 vm2 s1 s2 /\
    sim_pre inst1 inst2 s1 s2 /\
    step_inst_base inst1 s1 = OK s1' /\
    step_inst_base inst2 s2 = OK s2' /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    inst1.inst_opcode <> PHI /\
    inst1.inst_opcode <> PARAM /\
    inst1.inst_opcode <> RET /\
    inst1.inst_id = inst2.inst_id /\
    is_output_opcode inst1.inst_opcode /\
    ALL_DISTINCT inst1.inst_outputs /\
    ALL_DISTINCT inst2.inst_outputs /\
    (!v. (?idx. ALOOKUP vm1 v = SOME idx) ==>
         ~MEM v inst1.inst_outputs) /\
    (!v. (?idx. ALOOKUP vm2 v = SOME idx) ==>
         ~MEM v inst2.inst_outputs) /\
    (!v. MEM (Var v) inst1.inst_operands ==>
         ?idx. ALOOKUP vm1 v = SOME idx) /\
    (!v. MEM (Var v) inst2.inst_operands ==>
         ?idx. ALOOKUP vm2 v = SOME idx) ==>
    sim_inv vm1' vm2' s1' s2'
Proof
  rpt strip_tac
  (* derive structural/wf facts *)
  \\ `inst1.inst_opcode = inst2.inst_opcode /\
      inst1.inst_id = inst2.inst_id /\
      LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
      LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs`
       by metis_tac[canon_inst_structure]
  \\ `inst2.inst_opcode <> INVOKE` by metis_tac[]
  \\ `~is_terminator inst2.inst_opcode` by metis_tac[]
  \\ `var_map_wf vm1 /\ var_map_wf vm2 /\ LENGTH vm1 = LENGTH vm2 /\
      var_corr vm1 vm2 s1 s2 /\ execution_equiv UNIV s1 s2`
       by fs[sim_inv_def]
  (* derive ALOOKUP NONE for outputs *)
  \\ `!w. MEM w inst1.inst_outputs ==> ALOOKUP vm1 w = NONE` by (
       rpt strip_tac >> CCONTR_TAC >>
       `?i. ALOOKUP vm1 w = SOME i` by (Cases_on `ALOOKUP vm1 w` >> gvs[]) >>
       metis_tac[])
  \\ `!w. MEM w inst2.inst_outputs ==> ALOOKUP vm2 w = NONE` by (
       rpt strip_tac >> CCONTR_TAC >>
       `?i. ALOOKUP vm2 w = SOME i` by (Cases_on `ALOOKUP vm2 w` >> gvs[]) >>
       metis_tac[])
  (* ALOOKUP characterizations *)
  \\ `!v idx. ALOOKUP vm1' v = SOME idx <=>
       (?k. k < LENGTH inst1.inst_outputs /\ v = EL k inst1.inst_outputs /\
            idx = LENGTH vm1 + k) \/
       (~MEM v inst1.inst_outputs /\ ALOOKUP vm1 v = SOME idx)` by (
       qpat_assum `canon_inst vm1 _ = _`
         (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
           canon_inst_alookup_complete)) >>
       ASM_REWRITE_TAC[] >>
       CONV_TAC (DEPTH_CONV (REWR_CONV arithmeticTheory.ADD_COMM)) >>
       REWRITE_TAC[])
  \\ `!v idx. ALOOKUP vm2' v = SOME idx <=>
       (?k. k < LENGTH inst2.inst_outputs /\ v = EL k inst2.inst_outputs /\
            idx = LENGTH vm2 + k) \/
       (~MEM v inst2.inst_outputs /\ ALOOKUP vm2 v = SOME idx)` by (
       qpat_assum `canon_inst vm2 _ = _`
         (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
           canon_inst_alookup_complete)) >>
       ASM_REWRITE_TAC[] >>
       CONV_TAC (DEPTH_CONV (REWR_CONV arithmeticTheory.ADD_COMM)) >>
       REWRITE_TAC[])
  (* step_inst from step_inst_base *)
  \\ `step_inst ARB ARB inst1 s1 = OK s1'` by (
       qpat_assum `inst1.inst_opcode <> INVOKE`
         (fn th => REWRITE_TAC[MATCH_MP step_inst_non_invoke th]) >>
       ASM_REWRITE_TAC[])
  \\ `step_inst ARB ARB inst2 s2 = OK s2'` by (
       qpat_assum `inst2.inst_opcode <> INVOKE`
         (fn th => REWRITE_TAC[MATCH_MP step_inst_non_invoke th]) >>
       ASM_REWRITE_TAC[])
  (* step_preserves_non_output_vars *)
  \\ `!v. ~MEM v inst1.inst_outputs ==> lookup_var v s1' = lookup_var v s1`
       by (gen_tac >> strip_tac >>
           irule step_preserves_non_output_vars >>
           qexistsl_tac [`ARB`, `ARB`, `inst1`] >> ASM_REWRITE_TAC[])
  \\ `!v. ~MEM v inst2.inst_outputs ==> lookup_var v s2' = lookup_var v s2`
       by (gen_tac >> strip_tac >>
           irule step_preserves_non_output_vars >>
           qexistsl_tac [`ARB`, `ARB`, `inst2`] >> ASM_REWRITE_TAC[])
  (* step_sim + ee *)
  \\ `step_sim inst1 inst2 s1 s2` by (
       irule step_inst_base_sim >> rpt conj_tac >> ASM_REWRITE_TAC[])
  \\ `execution_equiv UNIV s1' s2'` by metis_tac[step_sim_ok_ee]
  (* var_corr via helper *)
  \\ `var_corr vm1' vm2' s1' s2'` by (
       irule var_corr_after_step_output >>
       qexistsl_tac [`ci`, `inst1`, `inst2`, `s1`, `s2`, `vm1`, `vm2`] >>
       ASM_REWRITE_TAC[] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)
  (* wf + LENGTH *)
  \\ `var_map_wf vm1'` by metis_tac[canon_inst_wf]
  \\ `var_map_wf vm2'` by metis_tac[canon_inst_wf]
  \\ `LENGTH vm1' = LENGTH vm2'` by
       metis_tac[canon_inst_map_eq_length]
  (* Assemble sim_inv *)
  \\ ASM_REWRITE_TAC[sim_inv_def]
QED

(* sim_inv preserved for inst_outputs = [] case (no output vars) *)
Theorem sim_inv_after_step_no_output[local]:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci s1 s2 s1' s2'.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) /\
    sim_inv vm1 vm2 s1 s2 /\
    sim_pre inst1 inst2 s1 s2 /\
    step_inst_base inst1 s1 = OK s1' /\
    step_inst_base inst2 s2 = OK s2' /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    inst1.inst_opcode <> PHI /\
    inst1.inst_opcode <> PARAM /\
    inst1.inst_opcode <> RET /\
    inst1.inst_id = inst2.inst_id /\
    inst1.inst_outputs = [] /\
    (!v. MEM (Var v) inst1.inst_operands ==>
         ?idx. ALOOKUP vm1 v = SOME idx) /\
    (!v. MEM (Var v) inst2.inst_operands ==>
         ?idx. ALOOKUP vm2 v = SOME idx) ==>
    sim_inv vm1' vm2' s1' s2'
Proof
  rpt strip_tac
  \\ `inst1.inst_opcode = inst2.inst_opcode /\
      inst1.inst_id = inst2.inst_id /\
      LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
      LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs`
       by metis_tac[canon_inst_structure]
  \\ `inst2.inst_outputs = []` by
       metis_tac[listTheory.LENGTH_NIL, listTheory.LENGTH]
  \\ `inst2.inst_opcode <> INVOKE` by metis_tac[]
  \\ `var_map_wf vm1 /\ var_map_wf vm2 /\ LENGTH vm1 = LENGTH vm2 /\
      var_corr vm1 vm2 s1 s2 /\ execution_equiv UNIV s1 s2`
       by fs[sim_inv_def]
  \\ `vm1' = vm1` by (
       qpat_x_assum `canon_inst vm1 _ = _` mp_tac >>
       simp[canon_inst_def, LET_THM, canon_outputs_def] >>
       pairarg_tac >> simp[] >> strip_tac >>
       metis_tac[canon_operands_map_unchanged])
  \\ `vm2' = vm2` by (
       qpat_x_assum `canon_inst vm2 _ = _` mp_tac >>
       simp[canon_inst_def, LET_THM, canon_outputs_def] >>
       pairarg_tac >> simp[] >> strip_tac >>
       metis_tac[canon_operands_map_unchanged])
  \\ `step_inst ARB ARB inst1 s1 = OK s1'` by (
       qpat_assum `inst1.inst_opcode <> INVOKE`
         (fn th => REWRITE_TAC[MATCH_MP step_inst_non_invoke th]) >>
       ASM_REWRITE_TAC[])
  \\ `step_inst ARB ARB inst2 s2 = OK s2'` by (
       qpat_assum `inst2.inst_opcode <> INVOKE`
         (fn th => REWRITE_TAC[MATCH_MP step_inst_non_invoke th]) >>
       ASM_REWRITE_TAC[])
  \\ `!v. lookup_var v s1' = lookup_var v s1` by (
       gen_tac >> irule step_preserves_non_output_vars >>
       qexistsl_tac [`ARB`, `ARB`, `inst1`] >> ASM_REWRITE_TAC[listTheory.MEM])
  \\ `~is_terminator inst2.inst_opcode` by metis_tac[]
  \\ `!v. lookup_var v s2' = lookup_var v s2` by (
       gen_tac >> irule step_preserves_non_output_vars >>
       qexistsl_tac [`ARB`, `ARB`, `inst2`] >> ASM_REWRITE_TAC[listTheory.MEM])
  \\ `var_corr vm1' vm2' s1' s2'` by (
       ASM_REWRITE_TAC[] >>
       PURE_REWRITE_TAC[var_corr_def] >> rpt strip_tac >>
       ASM_REWRITE_TAC[] >>
       qpat_assum `var_corr _ _ _ _`
         (mp_tac o REWRITE_RULE [var_corr_def]) >>
       disch_then (qspecl_then [`v1`, `v2`, `idx`] mp_tac) >>
       ASM_REWRITE_TAC[])
  \\ `step_sim inst1 inst2 s1 s2` by (
       irule step_inst_base_sim >> rpt conj_tac >> ASM_REWRITE_TAC[])
  \\ `execution_equiv UNIV s1' s2'` by metis_tac[step_sim_ok_ee]
  \\ ASM_REWRITE_TAC[sim_inv_def]
QED

(* sim_inv is preserved through a non-terminator step — wrapper *)
Theorem sim_inv_after_step[local]:
  !vm1 vm2 inst1 inst2 vm1' vm2' ci s1 s2 s1' s2'.
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) /\
    sim_inv vm1 vm2 s1 s2 /\
    sim_pre inst1 inst2 s1 s2 /\
    step_inst_base inst1 s1 = OK s1' /\
    step_inst_base inst2 s2 = OK s2' /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    inst1.inst_opcode <> PHI /\
    inst1.inst_opcode <> PARAM /\
    inst1.inst_opcode <> RET /\
    inst1.inst_id = inst2.inst_id /\
    (is_output_opcode inst1.inst_opcode \/ inst1.inst_outputs = []) /\
    ALL_DISTINCT inst1.inst_outputs /\
    ALL_DISTINCT inst2.inst_outputs /\
    (!v. (?idx. ALOOKUP vm1 v = SOME idx) ==>
         ~MEM v inst1.inst_outputs) /\
    (!v. (?idx. ALOOKUP vm2 v = SOME idx) ==>
         ~MEM v inst2.inst_outputs) /\
    (!v. MEM (Var v) inst1.inst_operands ==>
         ?idx. ALOOKUP vm1 v = SOME idx) /\
    (!v. MEM (Var v) inst2.inst_operands ==>
         ?idx. ALOOKUP vm2 v = SOME idx) ==>
    sim_inv vm1' vm2' s1' s2'
Proof
  rpt strip_tac >>
  Cases_on `is_output_opcode inst1.inst_opcode`
  >- (irule sim_inv_after_step_output >>
      qexistsl_tac [`ci`, `inst1`, `inst2`, `s1`, `s2`, `vm1`, `vm2`] >>
      ASM_REWRITE_TAC[])
  >> (irule sim_inv_after_step_no_output >>
      qexistsl_tac [`ci`, `inst1`, `inst2`, `s1`, `s2`, `vm1`, `vm2`] >>
      ASM_REWRITE_TAC[] >> gvs[])
QED

(* Terminator case: halting instructions produce equivalent results
   when operands evaluate to the same values *)
Theorem halting_step_equiv[local]:
  !inst1 inst2 vm1 vm2 vm1' vm2' ci s1 s2 bb1 bb2 idx.
    is_halting_opcode inst1.inst_opcode /\
    canon_inst vm1 inst1 = (vm1', ci) /\
    canon_inst vm2 inst2 = (vm2', ci) /\
    sim_inv vm1 vm2 s1 s2 /\
    bb_self_contained bb1 /\ bb_self_contained bb2 /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions)) /\
    idx < LENGTH bb1.bb_instructions /\
    idx < LENGTH bb2.bb_instructions /\
    EL idx bb1.bb_instructions = inst1 /\
    EL idx bb2.bb_instructions = inst2 /\
    (!j v. j < idx /\ j < LENGTH bb1.bb_instructions /\
           MEM v (EL j bb1.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm1 v = SOME i) /\
    (!j v. j < idx /\ j < LENGTH bb2.bb_instructions /\
           MEM v (EL j bb2.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm2 v = SOME i) ==>
    result_equiv UNIV (step_inst_base inst1 s1) (step_inst_base inst2 s2)
Proof
  rpt strip_tac >>
  `inst1.inst_opcode = inst2.inst_opcode`
    by metis_tac[canon_inst_same_opcode] >>
  (* Derive operand properties for inst1 and inst2 *)
  `(!v. MEM (Var v) inst1.inst_operands ==> ?i. ALOOKUP vm1 v = SOME i) /\
   (!v. MEM (Var v) inst1.inst_operands ==> ~MEM v inst1.inst_outputs)`
    by (irule canon_inst_operand_props >> rpt conj_tac
        >- (qexistsl_tac [`bb1`, `idx`] >> ASM_REWRITE_TAC[])
        >> qexistsl_tac [`ci`, `vm1'`] >> ASM_REWRITE_TAC[]) >>
  `(!v. MEM (Var v) inst2.inst_operands ==> ?i. ALOOKUP vm2 v = SOME i) /\
   (!v. MEM (Var v) inst2.inst_operands ==> ~MEM v inst2.inst_outputs)`
    by (irule canon_inst_operand_props >> rpt conj_tac
        >- (qexistsl_tac [`bb2`, `idx`] >> ASM_REWRITE_TAC[])
        >> qexistsl_tac [`ci`, `vm2'`] >> ASM_REWRITE_TAC[]) >>
  irule halting_term_sim >> rpt conj_tac
  >- ASM_REWRITE_TAC[]
  >- (irule canon_inst_eval_match >> rpt conj_tac
      >- ASM_REWRITE_TAC[]
      >- ASM_REWRITE_TAC[]
      >> qexistsl_tac [`ci`, `vm1`, `vm1'`, `vm2`, `vm2'`] >>
         ASM_REWRITE_TAC[])
  >- ASM_REWRITE_TAC[]
  >- fs[sim_inv_def]
QED


(* Lift step_sim to result_equiv for case-split continuations.
   Handles Error/Error, Abort/Abort automatically; delegates OK/OK to caller. *)
(* Derives step_sim from block-level context *)
Theorem block_ctx_step_sim[local]:
  !idx bb1 bb2 vm1 vm2 ci vm1' vm2' s1 s2.
    sim_inv vm1 vm2 s1 s2 /\
    idx < LENGTH bb1.bb_instructions /\
    idx < LENGTH bb2.bb_instructions /\
    canon_inst vm1 (EL idx bb1.bb_instructions) = (vm1', ci) /\
    canon_inst vm2 (EL idx bb2.bb_instructions) = (vm2', ci) /\
    bb_self_contained bb1 /\ bb_self_contained bb2 /\
    ~is_terminator (EL idx bb1.bb_instructions).inst_opcode /\
    (EL idx bb1.bb_instructions).inst_opcode <> INVOKE /\
    (EL idx bb2.bb_instructions).inst_opcode <> INVOKE /\
    (EL idx bb1.bb_instructions).inst_opcode <> PARAM /\
    (EL idx bb2.bb_instructions).inst_opcode <> PARAM /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions)) /\
    (!j v. j < idx /\ j < LENGTH bb1.bb_instructions /\
           MEM v (EL j bb1.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm1 v = SOME i) /\
    (!j v. j < idx /\ j < LENGTH bb2.bb_instructions /\
           MEM v (EL j bb2.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm2 v = SOME i) /\
    (!v. (?i. ALOOKUP vm1 v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb1.bb_instructions /\
             MEM v (EL j bb1.bb_instructions).inst_outputs) /\
    (!v. (?i. ALOOKUP vm2 v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb2.bb_instructions /\
             MEM v (EL j bb2.bb_instructions).inst_outputs) ==>
    step_sim (EL idx bb1.bb_instructions) (EL idx bb2.bb_instructions) s1 s2
Proof
  rpt strip_tac
  (* Derive PHI/RET exclusion *)
  \\ `(EL idx bb1.bb_instructions).inst_opcode <> PHI /\
       (EL idx bb2.bb_instructions).inst_opcode <> PHI`
       by (qpat_x_assum `bb_self_contained bb1`
             (fn th => assume_tac (REWRITE_RULE [bb_self_contained_def] th)) >>
           qpat_x_assum `bb_self_contained bb2`
             (fn th => assume_tac (REWRITE_RULE [bb_self_contained_def] th)) >>
           fs[listTheory.EVERY_EL])
  \\ `(EL idx bb1.bb_instructions).inst_opcode <> RET`
       by (strip_tac >> fs[is_terminator_def])
  (* Derive operand props *)
  \\ `(!v. MEM (Var v) (EL idx bb1.bb_instructions).inst_operands ==>
            ?i. ALOOKUP vm1 v = SOME i) /\
       (!v. MEM (Var v) (EL idx bb1.bb_instructions).inst_operands ==>
            ~MEM v (EL idx bb1.bb_instructions).inst_outputs)`
       by (irule canon_inst_operand_props >> rpt conj_tac
           >- (qexistsl_tac [`bb1`, `idx`] >> ASM_REWRITE_TAC[])
           >> qexistsl_tac [`ci`, `vm1'`] >> ASM_REWRITE_TAC[])
  \\ `(!v. MEM (Var v) (EL idx bb2.bb_instructions).inst_operands ==>
            ?i. ALOOKUP vm2 v = SOME i) /\
       (!v. MEM (Var v) (EL idx bb2.bb_instructions).inst_operands ==>
            ~MEM v (EL idx bb2.bb_instructions).inst_outputs)`
       by (irule canon_inst_operand_props >> rpt conj_tac
           >- (qexistsl_tac [`bb2`, `idx`] >> ASM_REWRITE_TAC[])
           >> qexistsl_tac [`ci`, `vm2'`] >> ASM_REWRITE_TAC[])
  (* sim_pre then step_sim *)
  \\ `sim_pre (EL idx bb1.bb_instructions) (EL idx bb2.bb_instructions) s1 s2`
       by ((let val thm = REWRITE_RULE [GSYM AND_IMP_INTRO]
                            (SPEC_ALL canon_inst_sim_pre)
            in qpat_assum `canon_inst vm1 _ = _`
                 (fn th1 => qpat_assum `canon_inst vm2 _ = _`
                   (fn th2 => mp_tac (MATCH_MP (MATCH_MP thm th1) th2) >>
                               assume_tac th1 >> assume_tac th2))
            end) >>
            rpt (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac)
  \\ `(EL idx bb1.bb_instructions).inst_id =
      (EL idx bb2.bb_instructions).inst_id`
       by (imp_res_tac canon_inst_same_id)
  \\ irule step_inst_base_sim
  \\ rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Element of ALL_DISTINCT FLAT list is ALL_DISTINCT — generic *)
Theorem all_distinct_flat_el_gen[local]:
  !(ls:'a list list) n.
    ALL_DISTINCT (FLAT ls) /\ n < LENGTH ls ==>
    ALL_DISTINCT (EL n ls)
Proof
  Induct >> rw[listTheory.FLAT, listTheory.ALL_DISTINCT_APPEND] >>
  Cases_on `n` >> gvs[]
QED

(* Specialization to bb instruction outputs — avoids lambda in quotations *)
Theorem all_distinct_el_outputs[local]:
  !bb idx.
    ALL_DISTINCT (FLAT (MAP (\x. x.inst_outputs) bb.bb_instructions)) ==>
    idx < LENGTH bb.bb_instructions ==>
    ALL_DISTINCT (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `(EL idx bb.bb_instructions).inst_outputs =
   EL idx (MAP (\x. x.inst_outputs) bb.bb_instructions)`
    by simp[listTheory.EL_MAP] >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  irule all_distinct_flat_el_gen >> simp[]
QED

(* Outputs at different instruction indices are disjoint — specialized for bb *)
Theorem outputs_disjoint[local]:
  !bb i j x.
    ALL_DISTINCT (FLAT (MAP (\x. x.inst_outputs) bb.bb_instructions)) /\
    i < LENGTH bb.bb_instructions /\
    j < LENGTH bb.bb_instructions /\ i <> j /\
    MEM x (EL i bb.bb_instructions).inst_outputs /\
    MEM x (EL j bb.bb_instructions).inst_outputs ==> F
Proof
  rpt strip_tac >>
  `MEM x (EL i (MAP (\x. x.inst_outputs) bb.bb_instructions)) /\
   MEM x (EL j (MAP (\x. x.inst_outputs) bb.bb_instructions))`
    by simp[listTheory.EL_MAP] >>
  metis_tac[all_distinct_flat_disjoint, listTheory.LENGTH_MAP]
QED

(* From block-level ALL_DISTINCT and domain inverse, derive:
   1. ALL_DISTINCT (EL idx bb).inst_outputs
   2. ALOOKUP vm v = SOME _ ==> ~MEM v (EL idx bb).inst_outputs
   3. MEM w (EL idx bb).inst_outputs ==> ALOOKUP vm w = NONE *)
Theorem block_ctx_outputs_fresh[local]:
  !bb vm idx w.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    idx < LENGTH bb.bb_instructions /\
    (!v. (?i. ALOOKUP vm v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb.bb_instructions /\
             MEM v (EL j bb.bb_instructions).inst_outputs) /\
    MEM w (EL idx bb.bb_instructions).inst_outputs ==>
    ALOOKUP vm w = NONE
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  Cases_on `ALOOKUP vm w` >> gvs[] >>
  first_x_assum (qspec_then `w` mp_tac) >>
  (impl_tac >- (qexists_tac `x` >> ASM_REWRITE_TAC[])) >>
  strip_tac >>
  irule outputs_disjoint >>
  qexistsl_tac [`bb`, `j`, `idx`, `w`] >>
  ASM_REWRITE_TAC[] >> decide_tac
QED

(* Single-block domain invariant update through canon_inst *)

(* Forward direction: j < SUC idx ==> ALOOKUP vm' v exists *)
Theorem canon_inst_domain_forward[local]:
  !bb vm vm' ci idx j v.
    canon_inst vm (EL idx bb.bb_instructions) = (vm', ci) /\
    var_map_wf vm /\
    bb_self_contained bb /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    idx < LENGTH bb.bb_instructions /\
    (!j v. j < idx /\ j < LENGTH bb.bb_instructions /\
           MEM v (EL j bb.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm v = SOME i) /\
    (!v. (?i. ALOOKUP vm v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb.bb_instructions /\
             MEM v (EL j bb.bb_instructions).inst_outputs) /\
    j < SUC idx /\ j < LENGTH bb.bb_instructions /\
    MEM v (EL j bb.bb_instructions).inst_outputs ==>
    ?i. ALOOKUP vm' v = SOME i
Proof
  rpt strip_tac
  \\ imp_res_tac all_distinct_el_outputs
  \\ (`!w. MEM w (EL idx bb.bb_instructions).inst_outputs ==>
           ALOOKUP vm w = NONE`
        by (rpt strip_tac >> irule block_ctx_outputs_fresh >>
            qexistsl_tac [`bb`, `idx`] >> ASM_REWRITE_TAC[]))
  \\ (`(!v'. MEM (Var v') (EL idx bb.bb_instructions).inst_operands ==>
             ?i. ALOOKUP vm v' = SOME i) /\
       (!v'. MEM (Var v') (EL idx bb.bb_instructions).inst_operands ==>
             ~MEM v' (EL idx bb.bb_instructions).inst_outputs)`
        by (irule canon_inst_operand_props >> rpt conj_tac
            >- (qexistsl_tac [`bb`, `idx`] >> ASM_REWRITE_TAC[])
            >> qexistsl_tac [`ci`, `vm'`] >> ASM_REWRITE_TAC[]))
  \\ (`!v' idx'. ALOOKUP vm' v' = SOME idx' <=>
         (?k. k < LENGTH (EL idx bb.bb_instructions).inst_outputs /\
              v' = EL k (EL idx bb.bb_instructions).inst_outputs /\
              idx' = LENGTH vm + k) \/
         (~MEM v' (EL idx bb.bb_instructions).inst_outputs /\
          ALOOKUP vm v' = SOME idx')`
        by (irule canon_inst_alookup_complete >> simp[]))
  \\ Cases_on `j = idx`
  >- (gvs[listTheory.MEM_EL] >>
      qexists_tac `LENGTH vm + n` >>
      qpat_assum `!v' idx'. ALOOKUP vm' v' = SOME idx' <=> _`
        (fn bicond => REWRITE_TAC[bicond]) >>
      disj1_tac >> qexists_tac `n` >> simp[])
  >- ((`j < idx` by simp[]) >>
      (`?i'. ALOOKUP vm v = SOME i'` by metis_tac[]) >>
      (`~MEM v (EL idx bb.bb_instructions).inst_outputs`
         by metis_tac[all_distinct_flat_disjoint,
                      listTheory.EL_MAP, listTheory.LENGTH_MAP]) >>
      qexists_tac `i'` >>
      qpat_assum `!v' idx'. ALOOKUP vm' v' = SOME idx' <=> _`
        (fn bicond => REWRITE_TAC[bicond]) >>
      disj2_tac >> ASM_REWRITE_TAC[])
QED

(* Inverse direction: ALOOKUP vm' v exists ==> j < SUC idx *)
Theorem canon_inst_domain_inverse[local]:
  !bb vm vm' ci idx v.
    canon_inst vm (EL idx bb.bb_instructions) = (vm', ci) /\
    var_map_wf vm /\
    bb_self_contained bb /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    idx < LENGTH bb.bb_instructions /\
    (!j v. j < idx /\ j < LENGTH bb.bb_instructions /\
           MEM v (EL j bb.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm v = SOME i) /\
    (!v. (?i. ALOOKUP vm v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb.bb_instructions /\
             MEM v (EL j bb.bb_instructions).inst_outputs) /\
    (?i. ALOOKUP vm' v = SOME i) ==>
    ?j. j < SUC idx /\ j < LENGTH bb.bb_instructions /\
        MEM v (EL j bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac
  \\ imp_res_tac all_distinct_el_outputs
  \\ (`!w. MEM w (EL idx bb.bb_instructions).inst_outputs ==>
           ALOOKUP vm w = NONE`
        by (rpt strip_tac >> irule block_ctx_outputs_fresh >>
            qexistsl_tac [`bb`, `idx`] >> ASM_REWRITE_TAC[]))
  \\ (`(!v'. MEM (Var v') (EL idx bb.bb_instructions).inst_operands ==>
             ?i'. ALOOKUP vm v' = SOME i') /\
       (!v'. MEM (Var v') (EL idx bb.bb_instructions).inst_operands ==>
             ~MEM v' (EL idx bb.bb_instructions).inst_outputs)`
        by (irule canon_inst_operand_props >> rpt conj_tac
            >- (qexistsl_tac [`bb`, `idx`] >> ASM_REWRITE_TAC[])
            >> qexistsl_tac [`ci`, `vm'`] >> ASM_REWRITE_TAC[]))
  \\ (`!v' idx'. ALOOKUP vm' v' = SOME idx' <=>
         (?k. k < LENGTH (EL idx bb.bb_instructions).inst_outputs /\
              v' = EL k (EL idx bb.bb_instructions).inst_outputs /\
              idx' = LENGTH vm + k) \/
         (~MEM v' (EL idx bb.bb_instructions).inst_outputs /\
          ALOOKUP vm v' = SOME idx')`
        by (irule canon_inst_alookup_complete >> simp[]))
  \\ (`(?k. k < LENGTH (EL idx bb.bb_instructions).inst_outputs /\
            v = EL k (EL idx bb.bb_instructions).inst_outputs /\
            i = LENGTH vm + k) \/
       (~MEM v (EL idx bb.bb_instructions).inst_outputs /\
        ALOOKUP vm v = SOME i)` by metis_tac[])
  >- (qexists_tac `idx` >> simp[] >> metis_tac[listTheory.EL_MEM])
  >- ((`?j. j < idx /\ j < LENGTH bb.bb_instructions /\
            MEM v (EL j bb.bb_instructions).inst_outputs` by metis_tac[]) >>
      qexists_tac `j` >> simp[])
QED

(* Composition: domain update at SUC idx *)
Theorem canon_inst_domain_update[local]:
  !bb vm vm' ci idx.
    canon_inst vm (EL idx bb.bb_instructions) = (vm', ci) /\
    var_map_wf vm /\
    bb_self_contained bb /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    idx < LENGTH bb.bb_instructions /\
    (!j v. j < idx /\ j < LENGTH bb.bb_instructions /\
           MEM v (EL j bb.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm v = SOME i) /\
    (!v. (?i. ALOOKUP vm v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb.bb_instructions /\
             MEM v (EL j bb.bb_instructions).inst_outputs) ==>
    (!j v. j < SUC idx /\ j < LENGTH bb.bb_instructions /\
           MEM v (EL j bb.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm' v = SOME i) /\
    (!v. (?i. ALOOKUP vm' v = SOME i) ==>
         ?j. j < SUC idx /\ j < LENGTH bb.bb_instructions /\
             MEM v (EL j bb.bb_instructions).inst_outputs)
Proof
  rpt gen_tac >> strip_tac >> conj_tac >> rpt strip_tac
  >- (mp_tac (Q.SPECL [`bb`, `vm`, `vm'`, `ci`, `idx`, `j`, `v`]
                       canon_inst_domain_forward) >>
      ASM_REWRITE_TAC[])
  >- (mp_tac (Q.SPECL [`bb`, `vm`, `vm'`, `ci`, `idx`, `v`]
                       canon_inst_domain_inverse) >>
      ASM_REWRITE_TAC[] >> disch_then match_mp_tac >>
      qexists_tac `i` >> ASM_REWRITE_TAC[])
QED

(* After a non-terminator step with OK results, update sim_inv
   and domain invariants for the inductive step at SUC idx. *)
Theorem non_term_step_invariant[local]:
  !idx bb1 bb2 vm1 vm2 ci vm1' vm2' s1 s2 s1' s2'.
    sim_inv vm1 vm2 s1 s2 /\
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    idx < LENGTH bb1.bb_instructions /\
    canon_inst vm1 (EL idx bb1.bb_instructions) = (vm1', ci) /\
    canon_inst vm2 (EL idx bb2.bb_instructions) = (vm2', ci) /\
    bb_self_contained bb1 /\ bb_self_contained bb2 /\
    ~is_terminator (EL idx bb1.bb_instructions).inst_opcode /\
    (EL idx bb1.bb_instructions).inst_opcode <> INVOKE /\
    (EL idx bb2.bb_instructions).inst_opcode <> INVOKE /\
    (EL idx bb1.bb_instructions).inst_opcode <> PARAM /\
    (EL idx bb2.bb_instructions).inst_opcode <> PARAM /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions)) /\
    (is_output_opcode (EL idx bb1.bb_instructions).inst_opcode \/
     (EL idx bb1.bb_instructions).inst_outputs = []) /\
    step_inst_base (EL idx bb1.bb_instructions) s1 = OK s1' /\
    step_inst_base (EL idx bb2.bb_instructions) s2 = OK s2' /\
    (!j v. j < idx /\ j < LENGTH bb1.bb_instructions /\
           MEM v (EL j bb1.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm1 v = SOME i) /\
    (!j v. j < idx /\ j < LENGTH bb2.bb_instructions /\
           MEM v (EL j bb2.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm2 v = SOME i) /\
    (!v. (?i. ALOOKUP vm1 v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb1.bb_instructions /\
             MEM v (EL j bb1.bb_instructions).inst_outputs) /\
    (!v. (?i. ALOOKUP vm2 v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb2.bb_instructions /\
             MEM v (EL j bb2.bb_instructions).inst_outputs) ==>
    sim_inv vm1' vm2' s1' s2' /\
    (!j v. j < SUC idx /\ j < LENGTH bb1.bb_instructions /\
           MEM v (EL j bb1.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm1' v = SOME i) /\
    (!j v. j < SUC idx /\ j < LENGTH bb2.bb_instructions /\
           MEM v (EL j bb2.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm2' v = SOME i) /\
    (!v. (?i. ALOOKUP vm1' v = SOME i) ==>
         ?j. j < SUC idx /\ j < LENGTH bb1.bb_instructions /\
             MEM v (EL j bb1.bb_instructions).inst_outputs) /\
    (!v. (?i. ALOOKUP vm2' v = SOME i) ==>
         ?j. j < SUC idx /\ j < LENGTH bb2.bb_instructions /\
             MEM v (EL j bb2.bb_instructions).inst_outputs)
Proof
  rpt gen_tac >> strip_tac >> (
  (* Derive opcode/id equality *)
  (let val thm = REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL canon_inst_same_fields)
   in qpat_assum `canon_inst vm1 _ = _`
        (fn th1 => qpat_assum `canon_inst vm2 _ = _`
          (fn th2 =>
            let val fields = MATCH_MP (MATCH_MP thm th1) th2
            in assume_tac (CONJUNCT1 fields) >>
               assume_tac (CONJUNCT2 fields) >>
               assume_tac th1 >> assume_tac th2
            end))
   end) >>
  (* Derive operand props *)
  (`(!v. MEM (Var v) (EL idx bb1.bb_instructions).inst_operands ==>
         ?i. ALOOKUP vm1 v = SOME i) /\
    (!v. MEM (Var v) (EL idx bb1.bb_instructions).inst_operands ==>
         ~MEM v (EL idx bb1.bb_instructions).inst_outputs)`
     by (irule canon_inst_operand_props >> rpt conj_tac
         >- (qexistsl_tac [`bb1`, `idx`] >> ASM_REWRITE_TAC[])
         >> qexistsl_tac [`ci`, `vm1'`] >> ASM_REWRITE_TAC[])) >>
  (`(!v. MEM (Var v) (EL idx bb2.bb_instructions).inst_operands ==>
         ?i. ALOOKUP vm2 v = SOME i) /\
    (!v. MEM (Var v) (EL idx bb2.bb_instructions).inst_operands ==>
         ~MEM v (EL idx bb2.bb_instructions).inst_outputs)`
     by (irule canon_inst_operand_props >> rpt conj_tac
         >- (qexistsl_tac [`bb2`, `idx`] >> ASM_REWRITE_TAC[] >> fs[])
         >> qexistsl_tac [`ci`, `vm2'`] >> ASM_REWRITE_TAC[])) >>
  (* Derive sim_pre *)
  (`sim_pre (EL idx bb1.bb_instructions) (EL idx bb2.bb_instructions) s1 s2`
     by (mp_tac (Q.SPECL [`vm1`, `vm2`, `(EL idx bb1.bb_instructions)`,
                           `(EL idx bb2.bb_instructions)`, `vm1'`, `vm2'`, `ci`,
                           `s1`, `s2`] canon_inst_sim_pre) >>
         ASM_REWRITE_TAC[] >> simp[])) >>
  (* Derive exclusions *)
  (`(EL idx bb1.bb_instructions).inst_opcode <> PHI`
     by (fs[bb_self_contained_def, listTheory.EVERY_EL]
         >> strip_tac >> fs[])) >>
  (`(EL idx bb1.bb_instructions).inst_opcode <> RET`
     by (strip_tac >> fs[is_terminator_def])) >>
  (`ALL_DISTINCT (EL idx bb1.bb_instructions).inst_outputs`
     by metis_tac[all_distinct_el_outputs]) >>
  (`ALL_DISTINCT (EL idx bb2.bb_instructions).inst_outputs`
     by (metis_tac[all_distinct_el_outputs,
                   DECIDE ``idx < (n:num) /\ n = m ==> idx < m``])) >>
  (`!v. (?i. ALOOKUP vm1 v = SOME i) ==>
        ~MEM v (EL idx bb1.bb_instructions).inst_outputs`
     by (rpt strip_tac >> CCONTR_TAC >> fs[] >>
         `ALOOKUP vm1 v = NONE`
           by (irule block_ctx_outputs_fresh >>
               qexistsl_tac [`bb1`, `idx`] >>
               ASM_REWRITE_TAC[]) >>
         fs[])) >>
  (`!v. (?i. ALOOKUP vm2 v = SOME i) ==>
        ~MEM v (EL idx bb2.bb_instructions).inst_outputs`
     by (rpt strip_tac >> CCONTR_TAC >> fs[] >>
         `ALOOKUP vm2 v = NONE`
           by (irule block_ctx_outputs_fresh >>
               qexistsl_tac [`bb2`, `idx`] >>
               ASM_REWRITE_TAC[] >> fs[]) >>
         fs[])) >>
  (* --- sim_inv preservation --- *)
  (`sim_inv vm1' vm2' s1' s2'`
     by (mp_tac (Q.SPECL [`vm1`, `vm2`,
                           `EL idx bb1.bb_instructions`,
                           `EL idx bb2.bb_instructions`,
                           `vm1'`, `vm2'`, `ci`,
                           `s1`, `s2`, `s1'`, `s2'`]
                          sim_inv_after_step) >>
         ASM_REWRITE_TAC[] >> simp[])) >>
  (* --- Domain updates for bb1 and bb2 --- *)
  (`(!j v. j < SUC idx /\ j < LENGTH bb1.bb_instructions /\
           MEM v (EL j bb1.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm1' v = SOME i) /\
    (!v. (?i. ALOOKUP vm1' v = SOME i) ==>
         ?j. j < SUC idx /\ j < LENGTH bb1.bb_instructions /\
             MEM v (EL j bb1.bb_instructions).inst_outputs)`
     by (mp_tac (Q.SPECL [`bb1`, `vm1`, `vm1'`, `ci`, `idx`]
                          canon_inst_domain_update) >>
         ASM_REWRITE_TAC[] >>
         impl_tac >- fs[sim_inv_def] >> simp[])) >>
  (`(!j v. j < SUC idx /\ j < LENGTH bb2.bb_instructions /\
           MEM v (EL j bb2.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm2' v = SOME i) /\
    (!v. (?i. ALOOKUP vm2' v = SOME i) ==>
         ?j. j < SUC idx /\ j < LENGTH bb2.bb_instructions /\
             MEM v (EL j bb2.bb_instructions).inst_outputs)`
     by (mp_tac (Q.SPECL [`bb2`, `vm2`, `vm2'`, `ci`, `idx`]
                          canon_inst_domain_update) >>
         ASM_REWRITE_TAC[] >>
         impl_tac >- (fs[sim_inv_def] >> fs[]) >> simp[])) >>
  metis_tac[])
QED

Theorem step_sim_lift_result[local]:
  !inst1 inst2 s1 s2 f1 f2.
    step_sim inst1 inst2 s1 s2 /\
    (!s1' s2'. step_inst_base inst1 s1 = OK s1' /\
               step_inst_base inst2 s2 = OK s2' /\
               execution_equiv UNIV s1' s2' ==>
               result_equiv UNIV (f1 s1') (f2 s2')) ==>
    result_equiv UNIV
      (case step_inst_base inst1 s1 of
         OK s'' => f1 s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet vals s' => IntRet vals s'
       | Error e => Error e)
      (case step_inst_base inst2 s2 of
         OK s'' => f2 s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet vals s' => IntRet vals s'
       | Error e => Error e)
Proof
  rpt strip_tac >>
  Cases_on `step_inst_base inst1 s1` >>
  Cases_on `step_inst_base inst2 s2` >>
  gvs[step_sim_def, result_equiv_def]
QED

(* ML tactic: instantiates step_sim_lift_result with concrete OK-branch
   functions extracted from the goal, then applies MATCH_MP_TAC *)
val step_sim_lift_tac :tactic = fn (asms, gl) =>
  let val args = snd (strip_comb gl)
      val r1 = el 2 args val r2 = el 3 args
      val ca1 = snd (strip_comb r1) val ca2 = snd (strip_comb r2)
      val sr1 = hd ca1 val sr2 = hd ca2
      val sa1 = snd (strip_comb sr1) val sa2 = snd (strip_comb sr2)
      val sslr_inst = INST [
        ``inst1:instruction`` |-> el 1 sa1, ``inst2:instruction`` |-> el 1 sa2,
        ``s1:venom_state`` |-> el 2 sa1, ``s2:venom_state`` |-> el 2 sa2,
        ``f1:venom_state -> exec_result`` |-> el 2 ca1,
        ``f2:venom_state -> exec_result`` |-> el 2 ca2
      ] (SPEC_ALL step_sim_lift_result)
  in MATCH_MP_TAC (BETA_RULE sslr_inst) (asms, gl) end

Theorem sim_inv_inst_idx[local]:
  !vm1 vm2 s1 s2 k1 k2.
    sim_inv vm1 vm2 s1 s2 ==>
    sim_inv vm1 vm2 (s1 with vs_inst_idx := k1)
                    (s2 with vs_inst_idx := k2)
Proof
  rpt strip_tac
  \\ fs[sim_inv_def, var_corr_def, execution_equiv_def,
        venomStateTheory.lookup_var_def]
QED

Theorem run_block_sim[local]:
  !n idx bb1 bb2 vm1 vm2 s1 s2 fuel ctx.
    n = LENGTH bb1.bb_instructions - idx /\
    sim_inv vm1 vm2 s1 s2 /\
    s1.vs_inst_idx = idx /\ s2.vs_inst_idx = idx /\
    LENGTH bb1.bb_instructions = LENGTH bb2.bb_instructions /\
    canon_insts vm1 (DROP idx bb1.bb_instructions) =
      canon_insts vm2 (DROP idx bb2.bb_instructions) /\
    bb_self_contained bb1 /\ bb_self_contained bb2 /\
    bb_is_halting bb1 /\ bb_is_halting bb2 /\
    bb_well_formed bb1 /\ bb_well_formed bb2 /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb1.bb_instructions /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb2.bb_instructions /\
    EVERY (\i. i.inst_opcode <> PARAM) bb1.bb_instructions /\
    EVERY (\i. i.inst_opcode <> PARAM) bb2.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions)) /\
    EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
          bb1.bb_instructions /\
    EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
          bb2.bb_instructions /\
    (!j v. j < idx /\ j < LENGTH bb1.bb_instructions /\
           MEM v (EL j bb1.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm1 v = SOME i) /\
    (!j v. j < idx /\ j < LENGTH bb2.bb_instructions /\
           MEM v (EL j bb2.bb_instructions).inst_outputs ==>
           ?i. ALOOKUP vm2 v = SOME i) /\
    (!v. (?i. ALOOKUP vm1 v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb1.bb_instructions /\
             MEM v (EL j bb1.bb_instructions).inst_outputs) /\
    (!v. (?i. ALOOKUP vm2 v = SOME i) ==>
         ?j. j < idx /\ j < LENGTH bb2.bb_instructions /\
             MEM v (EL j bb2.bb_instructions).inst_outputs) ==>
    result_equiv UNIV (exec_block fuel ctx bb1 s1) (exec_block fuel ctx bb2 s2)
Proof
  ho_match_mp_tac arithmeticTheory.COMPLETE_INDUCTION
  \\ rpt strip_tac
  (* Unfold exec_block once on each side *)
  \\ CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])))
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def]))
  \\ ASM_REWRITE_TAC[get_instruction_def]
  (* Base case: idx >= LENGTH *)
  \\ reverse (Cases_on `idx < LENGTH bb1.bb_instructions`)
  >- (fs[] >> simp[result_equiv_UNIV_refl])
  \\ (`idx < LENGTH bb2.bb_instructions` by fs[])
  \\ ASM_REWRITE_TAC[]
  (* Decompose DROP into head :: tail *)
  \\ (`DROP idx bb1.bb_instructions =
       EL idx bb1.bb_instructions :: DROP (SUC idx) bb1.bb_instructions`
      by simp[rich_listTheory.DROP_CONS_EL])
  \\ (`DROP idx bb2.bb_instructions =
       EL idx bb2.bb_instructions :: DROP (SUC idx) bb2.bb_instructions`
      by simp[rich_listTheory.DROP_CONS_EL])
  \\ fs[]
  \\ drule canon_insts_cons \\ strip_tac
  (* Setup: derive opcode equality, step_inst rewrite, is_terminator rewrite *)
  \\ (let val csf = REWRITE_RULE [GSYM AND_IMP_INTRO] (SPEC_ALL canon_inst_same_fields)
         val sni = SPEC_ALL step_inst_non_invoke
         val every_el = SIMP_RULE bool_ss [listTheory.EVERY_EL]
      in fn (asms, gl) =>
        let (* Find the two canon_inst assumptions *)
            val cis = List.filter (can (match_term
               ``canon_inst vm (EL n bb.bb_instructions) = x``)) asms
            val ci1 = hd cis val ci2 = hd (tl cis)
            (* Derive opcode/id equality *)
            val result = MATCH_MP (MATCH_MP csf (ASSUME ci1)) (ASSUME ci2)
            val opc_eq = CONJUNCT1 result
            val id_eq = CONJUNCT2 result
            (* Derive INVOKE exclusions from EVERY + idx < LENGTH *)
            val ev_invs = List.filter (can (match_term
               ``EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions``)) asms
            val idx_lts = List.filter (can (match_term
               ``n < LENGTH bb.bb_instructions``)) asms
            val neqs = List.concat (List.map (fn ev =>
               List.mapPartial (fn lt =>
                 SOME (BETA_RULE (MATCH_MP (SPEC_ALL (every_el (ASSUME ev)))
                                           (ASSUME lt)))
                 handle _ => NONE) idx_lts) ev_invs)
            val rws = map (fn th => MATCH_MP sni th) neqs
            val is_term_eq = AP_TERM ``is_terminator`` opc_eq
        in (assume_tac opc_eq >> assume_tac id_eq >>
            REWRITE_TAC rws >>
            assume_tac is_term_eq >>
            (* Also add the GSYM so ASM_REWRITE_TAC can go both directions *)
            assume_tac (GSYM is_term_eq))
           (asms, gl)
        end
      end)
  (* Case split on terminator *)
  \\ Cases_on `is_terminator (EL idx bb1.bb_instructions).inst_opcode`
  (* ---- Terminator case ---- *)
  >- (ASM_REWRITE_TAC[]
      \\ irule result_equiv_term_wrap
      \\ irule halting_step_equiv
      \\ conj_tac
      >- (mp_tac (Q.SPECL [`bb1`, `idx`] wf_halting_last)
          \\ ASM_REWRITE_TAC[])
      \\ qexistsl_tac [`bb1`, `bb2`, `ci`, `idx`, `vm1`, `vm1'`, `vm2`, `vm2'`]
      \\ ASM_REWRITE_TAC[])
  (* ---- Non-terminator case ---- *)
  \\ ASM_REWRITE_TAC[]
  \\ (`step_sim (EL idx bb1.bb_instructions)
                (EL idx bb2.bb_instructions) s1 s2`
      by (mp_tac (Q.SPECL [`idx`, `bb1`, `bb2`, `vm1`, `vm2`, `ci`,
                            `vm1'`, `vm2'`, `s1`, `s2`]
                           block_ctx_step_sim)
          \\ ASM_REWRITE_TAC[]
          \\ DISCH_TAC \\ first_x_assum irule
          \\ fs[listTheory.EVERY_EL]))
  \\ step_sim_lift_tac
  \\ conj_tac >- ASM_REWRITE_TAC[]
  \\ rpt strip_tac
  (* Establish invariants at SUC idx *)
  \\ (mp_tac (Q.SPECL [`idx`, `bb1`, `bb2`, `vm1`, `vm2`, `ci`,
                        `vm1'`, `vm2'`, `s1`, `s2`, `s1'`, `s2'`]
                       non_term_step_invariant)
      \\ ASM_REWRITE_TAC[]
      \\ (impl_tac >- fs[listTheory.EVERY_EL])
      \\ strip_tac)
  (* Apply IH *)
  \\ (`sim_inv vm1' vm2' (s1' with vs_inst_idx := SUC idx)
       (s2' with vs_inst_idx := SUC idx)` by
      (irule sim_inv_inst_idx \\ ASM_REWRITE_TAC[]))
  \\ (`LENGTH bb1.bb_instructions - SUC idx <
       LENGTH bb2.bb_instructions - idx` by simp[])
  \\ (first_x_assum (fn ih =>
        first_x_assum (fn lt =>
          mp_tac (MATCH_MP ih lt))))
  \\ disch_then (qspecl_then [`bb1`, `bb2`, `vm1'`, `vm2'`,
       `s1' with vs_inst_idx := SUC idx`,
       `s2' with vs_inst_idx := SUC idx`,
       `fuel`, `ctx`] mp_tac)
  \\ simp[]
  \\ (impl_tac >- ASM_REWRITE_TAC[])
  \\ DISCH_TAC \\ ASM_REWRITE_TAC[]
QED

(* ================================================================
   Section 4: Halting signature equivalence (corollary)
   ================================================================ *)

(* Strengthened: allows different states related by execution_equiv UNIV *)
Theorem halting_sig_equiv[local]:
  !bb1 bb2 s1 s2 fuel ctx.
    block_signature bb1 = block_signature bb2 /\
    block_signature bb1 <> NONE /\
    bb_well_formed bb1 /\ bb_well_formed bb2 /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb1.bb_instructions /\
    EVERY (\i. i.inst_opcode <> INVOKE) bb2.bb_instructions /\
    EVERY (\i. i.inst_opcode <> PARAM) bb1.bb_instructions /\
    EVERY (\i. i.inst_opcode <> PARAM) bb2.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb1.bb_instructions)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb2.bb_instructions)) /\
    EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
          bb1.bb_instructions /\
    EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
          bb2.bb_instructions /\
    execution_equiv UNIV s1 s2 /\
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 ==>
    result_equiv UNIV
      (exec_block fuel ctx bb1 s1)
      (exec_block fuel ctx bb2 s2)
Proof
  rpt strip_tac >>
  gvs[block_signature_def, AllCaseEqs()] >>
  irule run_block_sim >> simp[] >>
  conj_tac >- metis_tac[canon_insts_same_length] >>
  qexists_tac `[]` >> qexists_tac `[]` >>
  simp[sim_inv_def, var_corr_def, var_map_wf_def]
QED

(* ================================================================
   Section 5: Main theorem
   ================================================================ *)

(* Key block-level lemma: running a block and its label-rewritten
   version from the same state *)

(* Helper: non-block-label-opcode instructions are unchanged *)
Theorem subst_block_labels_inst_id[local]:
  !m inst.
    ~is_block_label_opcode inst.inst_opcode ==>
    subst_block_labels_inst m inst = inst
Proof
  rw[subst_block_labels_inst_def]
QED

(* Helper: non-terminator, non-PHI instructions are unchanged *)
Theorem subst_non_term_non_phi[local]:
  !m inst.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> PHI ==>
    subst_block_labels_inst m inst = inst
Proof
  rw[subst_block_labels_inst_def, is_block_label_opcode_def]
QED

(* ================================================================
   Section: resolve_phi under label substitution
   ================================================================ *)

(* resolve_phi + eval_operand is unchanged by label substitution when
   prev_bb is not in the domain or range of the map.

   resolve_phi may return a DIFFERENT operand (Label substituted), but
   eval_operand on it gives the same result when the map's labels
   (both domain and range) are disjoint from vs_labels. This is
   the "labels_safe" precondition -- block labels in the merge map
   are never in vs_labels (which stores function/offset label values).
   This makes eval_operand invariant under subst_label_map_op. *)

(* eval_operand on a substituted operand equals eval_operand on original
   when the map's labels are disjoint from vs_labels *)
Theorem eval_operand_subst_label_map[local]:
  !m op (st:venom_state).
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    eval_operand (subst_label_map_op m op) st = eval_operand op st
Proof
  rpt strip_tac >>
  Cases_on `op` >> simp[subst_label_map_op_def, eval_operand_def] >>
  rename1 `ALOOKUP m lbl` >>
  Cases_on `ALOOKUP m lbl` >> simp[eval_operand_def] >>
  rename1 `ALOOKUP m lbl = SOME new_lbl` >>
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  `MEM lbl (MAP FST m)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `(lbl, new_lbl)` >> simp[]) >>
  `MEM new_lbl (MAP SND m)` by
    (simp[listTheory.MEM_MAP] >> qexists_tac `(lbl, new_lbl)` >> simp[]) >>
  res_tac >> simp[]
QED

Theorem eval_operands_subst_label_map[local]:
  !ops m (st:venom_state).
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    eval_operands (MAP (subst_label_map_op m) ops) st = eval_operands ops st
Proof
  Induct >> simp[eval_operands_def] >>
  rpt strip_tac >>
  `eval_operand (subst_label_map_op m h) st = eval_operand h st` by (
    irule eval_operand_subst_label_map >> simp[]) >>
  simp[] >> CASE_TAC >> simp[] >>
  qpat_x_assum `!m st. _ ==> eval_operands _ _ = _` irule >> simp[]
QED

(* resolve_phi commutes with subst_label_map_op when prev_bb is not
   in domain or range of m *)
Theorem resolve_phi_subst_comm[local]:
  !prev_bb ops m.
    ~MEM prev_bb (MAP FST m) /\ ~MEM prev_bb (MAP SND m) ==>
    resolve_phi prev_bb (MAP (subst_label_map_op m) ops) =
    OPTION_MAP (subst_label_map_op m) (resolve_phi prev_bb ops)
Proof
  ho_match_mp_tac (fetch "venomExecSemantics" "resolve_phi_ind") >>
  rw[resolve_phi_def, subst_label_map_op_def] >>
  Cases_on `ALOOKUP m lbl` >>
  gvs[resolve_phi_def] >>
  TRY (Cases_on `lbl = prev_bb` >> gvs[] >> NO_TAC) >>
  rename1 `ALOOKUP m lbl = SOME new_lbl` >>
  simp[resolve_phi_def] >>
  (`new_lbl <> prev_bb` by
    (CCONTR_TAC >> gvs[] >>
     imp_res_tac alistTheory.ALOOKUP_MEM >>
     gvs[listTheory.MEM_MAP] >> metis_tac[pairTheory.SND])) >>
  (`lbl <> prev_bb` by
    (CCONTR_TAC >> gvs[] >>
     imp_res_tac alistTheory.ALOOKUP_MEM >>
     gvs[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST])) >>
  simp[] >>
  (* Remaining: contradiction -- ALOOKUP found lbl but ~MEM lbl (MAP FST m) *)
  imp_res_tac alistTheory.ALOOKUP_MEM >>
  gvs[listTheory.MEM_MAP]
QED

(* step_inst_base on a PHI instruction is unchanged by label substitution
   when prev_bb is not in domain or range, and map labels are safe *)
Theorem step_inst_base_phi_subst[local]:
  !m inst (st:venom_state).
    inst.inst_opcode = PHI /\
    (case st.vs_prev_bb of NONE => T
     | SOME prev => ~MEM prev (MAP FST m) /\ ~MEM prev (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    step_inst_base (subst_block_labels_inst m inst) st =
    step_inst_base inst st
Proof
  rw[subst_block_labels_inst_def, is_block_label_opcode_def,
     subst_label_map_inst_def] >>
  simp[Once step_inst_base_def] >>
  simp[Once step_inst_base_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `st.vs_prev_bb` >> simp[] >>
  gvs[resolve_phi_subst_comm] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  (* resolve_phi returned SOME; now eval_operand on subst vs original *)
  `eval_operand (subst_label_map_op m x') st = eval_operand x' st` by (
    irule eval_operand_subst_label_map >> simp[]) >>
  simp[]
QED

(* For non-terminator instructions (including PHI with constraints),
   step_inst_base on subst version equals step_inst_base on original *)
Theorem step_inst_base_subst_non_term[local]:
  !m inst (st:venom_state).
    ~is_terminator inst.inst_opcode /\
    (inst.inst_opcode = PHI ==>
       case st.vs_prev_bb of NONE => T
       | SOME prev => ~MEM prev (MAP FST m) /\ ~MEM prev (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    step_inst_base (subst_block_labels_inst m inst) st =
    step_inst_base inst st
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = PHI` >-
  (gvs[] >> irule step_inst_base_phi_subst >> simp[]) >>
  (`subst_block_labels_inst m inst = inst`
     by (irule subst_non_term_non_phi >> simp[])) >>
  simp[]
QED

(* ================================================================
   Section: exec_block under label substitution (non-terminator prefix)
   ================================================================ *)

(* exec_block on subst block vs original: same for non-jump, mapped for jump *)

Theorem subst_block_labels_block_length[local]:
  !m bb. LENGTH (subst_block_labels_block m bb).bb_instructions =
         LENGTH bb.bb_instructions
Proof
  rw[subst_block_labels_block_def]
QED

Theorem get_instruction_subst[local]:
  !m bb idx.
    get_instruction (subst_block_labels_block m bb) idx =
    if idx < LENGTH bb.bb_instructions then
      SOME (subst_block_labels_inst m (EL idx bb.bb_instructions))
    else NONE
Proof
  rw[get_instruction_def, subst_block_labels_block_def] >>
  simp[listTheory.EL_MAP]
QED

Theorem subst_block_labels_inst_opcode[local]:
  !m inst. (subst_block_labels_inst m inst).inst_opcode = inst.inst_opcode
Proof
  rw[subst_block_labels_inst_def, subst_label_map_inst_def]
QED

(* Block-level result relationship under label substitution *)

(* Helper: subst_label_map_op is identity on non-Label operands *)
Theorem subst_label_map_op_non_label[local]:
  !m op. (!l. op <> Label l) ==> subst_label_map_op m op = op
Proof
  Cases_on `op` >> simp[subst_label_map_op_def]
QED

(* Helper: MAP subst_label_map_op over non-Label ops is identity *)
Theorem map_subst_label_map_op_no_labels[local]:
  !m ops. EVERY (\op. !l. op <> Label l) ops ==>
          MAP (subst_label_map_op m) ops = ops
Proof
  Induct_on `ops` >> simp[] >>
  rpt strip_tac >> Cases_on `h` >> gvs[subst_label_map_op_def]
QED

(* Helper: if all operands are non-Label, subst_label_map_inst is identity *)
Theorem subst_label_map_inst_no_labels[local]:
  !m inst.
    EVERY (\op. !l. op <> Label l) inst.inst_operands ==>
    subst_label_map_inst m inst = inst
Proof
  rw[subst_label_map_inst_def, venomInstTheory.instruction_component_equality] >>
  simp[map_subst_label_map_op_no_labels]
QED

(* For halting terminators, subst_block_labels_inst is identity because
   halting opcodes have no Label operands in well-formed programs.
   We state this as: step_inst_base on subst = step_inst_base on original
   for halting terminators that have no Label operands. *)
Theorem step_inst_base_subst_no_label_ops[local]:
  !m inst s.
    EVERY (\op. !l. op <> Label l) inst.inst_operands ==>
    step_inst_base (subst_block_labels_inst m inst) s =
    step_inst_base inst s
Proof
  rpt strip_tac >>
  Cases_on `is_block_label_opcode inst.inst_opcode` >-
  (gvs[subst_block_labels_inst_def, subst_label_map_inst_no_labels]) >>
  gvs[subst_block_labels_inst_def]
QED

(* ================================================================
   Section: step_inst under label substitution for non-terminators

   Non-terminator instructions are unchanged by subst (for non-PHI)
   or produce the same step_inst result (for PHI with prev_bb constraint).
   INVOKE instructions are also unchanged (not is_block_label_opcode).
   ================================================================ *)

(* step_inst on non-terminator subst'd instruction = step_inst on original *)
Theorem step_inst_subst_non_term[local]:
  !fuel ctx m inst (st:venom_state).
    ~is_terminator inst.inst_opcode /\
    (inst.inst_opcode = PHI ==>
       case st.vs_prev_bb of NONE => T
       | SOME prev => ~MEM prev (MAP FST m) /\ ~MEM prev (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    step_inst fuel ctx (subst_block_labels_inst m inst) st =
    step_inst fuel ctx inst st
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >-
  ((* INVOKE: subst doesn't change it *)
   `subst_block_labels_inst m inst = inst`
     by (rw[subst_block_labels_inst_def, is_block_label_opcode_def] >>
         gvs[is_terminator_def]) >>
   simp[]) >>
  (* Non-INVOKE: step_inst = step_inst_base *)
  simp[step_inst_non_invoke] >>
  `(subst_block_labels_inst m inst).inst_opcode = inst.inst_opcode`
    by simp[subst_block_labels_inst_opcode] >>
  simp[step_inst_non_invoke] >>
  irule step_inst_base_subst_non_term >> simp[]
QED

(* ================================================================
   Section: Terminator instruction under label substitution
   ================================================================ *)

(* extract_labels commutes with MAP subst_label_map_op *)
Theorem extract_labels_map_subst[local]:
  !ops m.
    extract_labels (MAP (subst_label_map_op m) ops) =
    OPTION_MAP (MAP (\l. case ALOOKUP m l of NONE => l | SOME k => k))
              (extract_labels ops)
Proof
  Induct >> simp[extract_labels_def] >>
  rpt gen_tac >> Cases_on `h` >>
  simp[subst_label_map_op_def, extract_labels_def] >>
  Cases_on `ALOOKUP m s` >> simp[extract_labels_def] >>
  Cases_on `extract_labels (MAP (subst_label_map_op m) ops)` >> simp[] >>
  Cases_on `extract_labels ops` >> gvs[]
QED

Theorem parse_dret_shape_subst_label_map[local]:
  !m inst.
    parse_dret_shape
      (inst with inst_operands := MAP (subst_label_map_op m) inst.inst_operands) =
    parse_dret_shape inst
Proof
  rpt gen_tac >>
  Cases_on `inst.inst_operands` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def] >>
  Cases_on `h` >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def, subst_label_map_op_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[]
QED

(* Non-jumping terminator: step_inst_base unchanged when map labels are
   disjoint from vs_labels. Uses eval_operands_subst_label_map. *)
val non_jump_term_tac =
  rpt strip_tac >>
  simp[subst_block_labels_inst_def, is_block_label_opcode_def,
       is_terminator_def, subst_label_map_inst_def,
       parse_dret_shape_subst_label_map] >>
  simp[Once step_inst_base_def] >>
  simp[Once step_inst_base_def] >>
  `eval_operands (MAP (subst_label_map_op m) inst.inst_operands) st =
   eval_operands inst.inst_operands st` by (
    irule eval_operands_subst_label_map >> fs[]) >>
  simp[parse_dret_shape_subst_label_map] >>
  Cases_on `inst.inst_operands` >> simp[parse_dret_shape_subst_label_map] >>
  TRY (Cases_on `t` >> simp[]) >>
  TRY (Cases_on `t'` >> simp[]) >>
  TRY (
    `eval_operand (subst_label_map_op m h) st = eval_operand h st` by (
      irule eval_operand_subst_label_map >> fs[]) >>
    simp[]) >>
  TRY (
    `eval_operand (subst_label_map_op m h') st = eval_operand h' st` by (
      irule eval_operand_subst_label_map >> fs[]) >>
    simp[]);

Theorem step_inst_base_subst_non_jump_term[local]:
  !m inst (st:venom_state).
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    step_inst_base (subst_block_labels_inst m inst) st =
    step_inst_base inst st
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
  >- non_jump_term_tac (* RET *)
  >- non_jump_term_tac (* RETURN *)
  >- non_jump_term_tac (* REVERT *)
  >- non_jump_term_tac (* STOP *)
  >- non_jump_term_tac (* SINK *)
  >- non_jump_term_tac (* DRET *)
  >- non_jump_term_tac (* RETFMP *)
  >- non_jump_term_tac (* SELFDESTRUCT *)
  >- non_jump_term_tac (* INVALID *)
QED

(* Helper: jump_to preserves execution_equiv UNIV *)
Theorem jump_to_ee_UNIV[local]:
  !lbl1 lbl2 s.
    execution_equiv UNIV (jump_to lbl1 s) (jump_to lbl2 s)
Proof
  rw[jump_to_def, execution_equiv_def]
QED

(* Helper: jump_to sets fields predictably *)
Theorem jump_to_fields[local]:
  !lbl s.
    (jump_to lbl s).vs_current_bb = lbl /\
    (jump_to lbl s).vs_prev_bb = SOME s.vs_current_bb /\
    (jump_to lbl s).vs_inst_idx = 0 /\
    (jump_to lbl s).vs_halted = s.vs_halted /\
    (jump_to lbl s).vs_vars = s.vs_vars
Proof
  rw[jump_to_def]
QED

(* Tactic to pick existential witness from second conjunct:
   ∃lbl. ... ∧ jump_to X s = jump_to lbl s → witness is X
   Also handles record-update form from DJMP *)
val pick_jump_witness_tac :tactic = fn (asl, g) =>
  let val (v, body) = dest_exists g
      val (_, eq2) = dest_conj body
      val (lhs, rhs) = dest_eq eq2
      fun find_witness l r =
        if is_var r andalso r ~~ v then l
        else if is_comb l andalso is_comb r then
          let val (fl, al) = dest_comb l
              val (fr, ar) = dest_comb r
          in (find_witness al ar handle HOL_ERR _ => find_witness fl fr)
          end
        else raise mk_HOL_ERR "" "" ""
  in EXISTS_TAC (find_witness lhs rhs) (asl, g) end;

(* Per-opcode lemmas for jumping terminators.
   With labels_safe, eval_operand is invariant under subst_label_map_op,
   so we can rewrite all operand evals uniformly. *)
Theorem step_inst_base_subst_jmp[local]:
  !m inst (st:venom_state).
    inst.inst_opcode = JMP /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    case step_inst_base inst st of
      Error e => step_inst_base (subst_block_labels_inst m inst) st = Error e
    | OK s1 => ?lbl.
        step_inst_base (subst_block_labels_inst m inst) st =
          OK (jump_to (case ALOOKUP m lbl of NONE => lbl | SOME k => k) st) /\
        s1 = jump_to lbl st
    | Halt s1 => F     (* JMP never produces Halt *)
    | Abort a s1 => F  (* JMP never produces Abort *)
    | IntRet v s1 => F  (* JMP never produces IntRet *)
Proof
  rpt gen_tac >> strip_tac >>
  `subst_block_labels_inst m inst =
   inst with inst_operands := MAP (subst_label_map_op m) inst.inst_operands`
    by simp[subst_block_labels_inst_def, is_block_label_opcode_def,
            is_terminator_def, subst_label_map_inst_def] >>
  pop_assum SUBST1_TAC >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  PURE_REWRITE_TAC[instruction_accfupds] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  Cases_on `inst.inst_operands` >> simp[subst_label_map_op_def] >>
  Cases_on `t` >> simp[subst_label_map_op_def] >>
  Cases_on `h` >> simp[subst_label_map_op_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  pick_jump_witness_tac >> simp[]
QED

Theorem step_inst_base_subst_jnz[local]:
  !m inst (st:venom_state).
    inst.inst_opcode = JNZ /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    case step_inst_base inst st of
      Error e => step_inst_base (subst_block_labels_inst m inst) st = Error e
    | OK s1 => ?lbl.
        step_inst_base (subst_block_labels_inst m inst) st =
          OK (jump_to (case ALOOKUP m lbl of NONE => lbl | SOME k => k) st) /\
        s1 = jump_to lbl st
    | Halt s1 => F     (* JNZ never produces Halt *)
    | Abort a s1 => F  (* JNZ never produces Abort *)
    | IntRet v s1 => F  (* JNZ never produces IntRet *)
Proof
  rpt gen_tac >> strip_tac >>
  `subst_block_labels_inst m inst =
   inst with inst_operands := MAP (subst_label_map_op m) inst.inst_operands`
    by simp[subst_block_labels_inst_def, is_block_label_opcode_def,
            is_terminator_def, subst_label_map_inst_def] >>
  pop_assum SUBST1_TAC >>
  `!op. eval_operand (subst_label_map_op m op) st = eval_operand op st` by (
    rpt strip_tac >> irule eval_operand_subst_label_map >> simp[]) >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  PURE_REWRITE_TAC[instruction_accfupds] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  Cases_on `inst.inst_operands` >> simp[subst_label_map_op_def] >>
  Cases_on `t` >> simp[subst_label_map_op_def] >>
  Cases_on `h'` >> simp[subst_label_map_op_def] >>
  Cases_on `t'` >> simp[subst_label_map_op_def] >>
  TRY (BasicProvers.every_case_tac >> simp[] >> NO_TAC) >>
  Cases_on `h'` >> simp[subst_label_map_op_def] >>
  Cases_on `t` >> simp[subst_label_map_op_def] >>
  TRY (BasicProvers.every_case_tac >> simp[] >> NO_TAC) >>
  BasicProvers.every_case_tac >> gvs[] >>
  pick_jump_witness_tac >> simp[]
QED

Theorem step_inst_base_subst_djmp[local]:
  !m inst (st:venom_state).
    inst.inst_opcode = DJMP /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    case step_inst_base inst st of
      Error e => step_inst_base (subst_block_labels_inst m inst) st = Error e
    | OK s1 => ?lbl.
        step_inst_base (subst_block_labels_inst m inst) st =
          OK (jump_to (case ALOOKUP m lbl of NONE => lbl | SOME k => k) st) /\
        s1 = jump_to lbl st
    | Halt s1 => F     (* DJMP never produces Halt *)
    | Abort a s1 => F  (* DJMP never produces Abort *)
    | IntRet v s1 => F  (* DJMP never produces IntRet *)
Proof
  rpt gen_tac >> strip_tac >>
  `subst_block_labels_inst m inst =
   inst with inst_operands := MAP (subst_label_map_op m) inst.inst_operands`
    by simp[subst_block_labels_inst_def, is_block_label_opcode_def,
            is_terminator_def, subst_label_map_inst_def] >>
  pop_assum SUBST1_TAC >>
  `!op. eval_operand (subst_label_map_op m op) st = eval_operand op st` by (
    rpt strip_tac >> irule eval_operand_subst_label_map >> simp[]) >>
  simp[step_inst_base_def, subst_label_map_op_def,
       extract_labels_map_subst, is_terminator_def] >>
  Cases_on `inst.inst_operands` >> simp[subst_label_map_op_def] >>
  BasicProvers.every_case_tac >>
  gvs[extract_labels_map_subst, listTheory.EL_MAP,
      jump_to_def, optionTheory.OPTION_MAP_DEF] >>
  pick_jump_witness_tac >> simp[]
QED

(* Unified: for any jumping terminator, step_inst_base gives same Error or
   both give OK (jump_to ...) with possibly different labels *)
Theorem step_inst_base_subst_jump[local]:
  !m inst (st:venom_state).
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP st.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP st.vs_labels l = NONE) ==>
    case step_inst_base inst st of
      Error e => step_inst_base (subst_block_labels_inst m inst) st = Error e
    | OK s1 => ?lbl.
        step_inst_base (subst_block_labels_inst m inst) st =
          OK (jump_to (case ALOOKUP m lbl of NONE => lbl | SOME k => k) st) /\
        s1 = jump_to lbl st
    | Halt s1 => F
    | Abort a s1 => F
    | IntRet v s1 => F
Proof
  rpt strip_tac >> gvs[] >>
  metis_tac[step_inst_base_subst_jmp, step_inst_base_subst_jnz,
            step_inst_base_subst_djmp]
QED

(* ================================================================
   Section: exec_block under label substitution

   Key theorem: exec_block on subst block from same state produces:
   - Identical result for non-OK cases (Error/Halt/Abort/IntRet)
   - For OK case: same state except vs_current_bb mapped through m

   Proved by complete induction on instructions remaining
   ================================================================ *)

(* Abbreviation for the block-level subst relationship *)
Definition block_subst_rel_def:
  block_subst_rel m r1 r2 <=>
    case r1 of
      Error e => r2 = Error e
    | Abort a s' => r2 = Abort a s'
    | IntRet vs s' => r2 = IntRet vs s'
    | Halt s' =>
        ?s''. r2 = Halt s'' /\ execution_equiv UNIV s'' s'
    | OK s' =>
        ?s''. r2 = OK s'' /\ execution_equiv UNIV s'' s' /\
              s''.vs_vars = s'.vs_vars /\
              s''.vs_inst_idx = s'.vs_inst_idx /\
              s''.vs_prev_bb = s'.vs_prev_bb /\
              (ALOOKUP m s'.vs_current_bb = NONE ==>
               s''.vs_current_bb = s'.vs_current_bb) /\
              (!k. ALOOKUP m s'.vs_current_bb = SOME k ==>
                   s''.vs_current_bb = k)
End

(* block_subst_rel is reflexive when ALOOKUP m always returns NONE *)
Theorem block_subst_rel_refl[local]:
  !m r. (!k. ALOOKUP m k = NONE) ==> block_subst_rel m r r
Proof
  rw[block_subst_rel_def] >>
  Cases_on `r` >> simp[execution_equiv_def]
QED

val term_ok_jump_tac =
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, eval_operands_def, eval_operand_def,
       AllCaseEqs()] >>
  rpt CASE_TAC >> gvs[] >> TRY pairarg_tac >> gvs[];

Theorem step_inst_base_ok_terminator_jump[local]:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
    inst.inst_opcode = DJMP
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
  >- term_ok_jump_tac
  >- term_ok_jump_tac
  >- term_ok_jump_tac
  >- term_ok_jump_tac
  >- term_ok_jump_tac
  >- (term_ok_jump_tac >> rpt strip_tac >>
      Cases_on `pack_dret_dynamic s.vs_call_entry_fmp pairs s` >>
      Cases_on `r` >> gvs[])
  >- term_ok_jump_tac
  >- term_ok_jump_tac
  >- term_ok_jump_tac
QED

(* Non-jump terminators never return OK *)
Theorem step_inst_base_non_jump_term_not_ok[local]:
  !inst s.
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
    inst.inst_opcode <> DJMP ==>
    (!v. step_inst_base inst s <> OK v)
Proof
  rpt strip_tac >> CCONTR_TAC >>
  drule_all step_inst_base_ok_terminator_jump >>
  strip_tac >> gvs[]
QED

(* Non-jumping terminator case *)
Theorem run_block_subst_term_non_jump[local]:
  !fuel ctx bb s m.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
    ~((EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JMP) /\
    ~((EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ) /\
    ~((EL s.vs_inst_idx bb.bb_instructions).inst_opcode = DJMP) /\
    bb_well_formed bb /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) ==>
    block_subst_rel m
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (subst_block_labels_block m bb) s)
Proof
  rpt strip_tac >>
  `get_instruction bb s.vs_inst_idx =
   SOME (EL s.vs_inst_idx bb.bb_instructions)`
    by simp[get_instruction_def] >>
  `get_instruction (subst_block_labels_block m bb) s.vs_inst_idx =
   SOME (subst_block_labels_inst m (EL s.vs_inst_idx bb.bb_instructions))`
    by simp[get_instruction_subst, subst_block_labels_block_length] >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE`
    by (Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
        gvs[is_terminator_def]) >>
  `(subst_block_labels_inst m (EL s.vs_inst_idx bb.bb_instructions)).inst_opcode
   = (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
    by simp[subst_block_labels_inst_opcode] >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  `step_inst_base (subst_block_labels_inst m
     (EL s.vs_inst_idx bb.bb_instructions)) s =
   step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s`
    by (irule step_inst_base_subst_non_jump_term >> simp[]) >>
  ASM_REWRITE_TAC[] >>
  `!v. step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s <> OK v`
    by (irule step_inst_base_non_jump_term_not_ok >> simp[]) >>
  Cases_on `step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[block_subst_rel_def, execution_equiv_def] >>
  metis_tac[]
QED

(* Jumping terminator case *)
Theorem run_block_subst_term_jump[local]:
  !fuel ctx bb s m.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
    ((EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JMP \/
     (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ \/
     (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = DJMP) /\
    bb_well_formed bb /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) ==>
    block_subst_rel m
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (subst_block_labels_block m bb) s)
Proof
  rpt strip_tac >>
  `get_instruction bb s.vs_inst_idx =
   SOME (EL s.vs_inst_idx bb.bb_instructions)`
    by simp[get_instruction_def] >>
  `get_instruction (subst_block_labels_block m bb) s.vs_inst_idx =
   SOME (subst_block_labels_inst m (EL s.vs_inst_idx bb.bb_instructions))`
    by simp[get_instruction_subst, subst_block_labels_block_length] >>
  `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> INVOKE`
    by (Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >>
        gvs[is_terminator_def]) >>
  `(subst_block_labels_inst m (EL s.vs_inst_idx bb.bb_instructions)).inst_opcode
   = (EL s.vs_inst_idx bb.bb_instructions).inst_opcode`
    by simp[subst_block_labels_inst_opcode] >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  simp[Once exec_block_def, step_inst_non_invoke] >>
  mp_tac (Q.SPECL [`m`, `EL s.vs_inst_idx bb.bb_instructions`, `s`]
    step_inst_base_subst_jump) >>
  ASM_REWRITE_TAC[] >>
  Cases_on `step_inst_base (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[] >>
  TRY (simp[block_subst_rel_def] >> NO_TAC) >>
  strip_tac >> gvs[] >>
  Cases_on `s.vs_halted` >> (
    simp[block_subst_rel_def, jump_to_fields] >>
    Cases_on `ALOOKUP m lbl` >>
    simp[jump_to_fields, execution_equiv_def, jump_to_ee_UNIV]
  )
QED

(* Terminator case: standalone, no IH needed *)
Theorem run_block_subst_term[local]:
  !fuel ctx bb s m.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
    bb_well_formed bb /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) ==>
    block_subst_rel m
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (subst_block_labels_block m bb) s)
Proof
  rpt strip_tac >>
  Cases_on `(EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JMP \/
            (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ \/
            (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = DJMP`
  >- (irule run_block_subst_term_jump >> simp[])
  >> (irule run_block_subst_term_non_jump >> gvs[])
QED

(* Reusable: unfold exec_block for a non-terminator instruction *)
Theorem run_block_non_term_unfold[local]:
  !fuel ctx bb s inst.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    ~is_terminator inst.inst_opcode ==>
    exec_block fuel ctx bb s =
      case step_inst fuel ctx inst s of
        OK s' => exec_block fuel ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx)
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | IntRet v s' => IntRet v s'
      | Error e => Error e
Proof
  rpt strip_tac >>
  CONV_TAC (RATOR_CONV (RAND_CONV
    (PURE_ONCE_REWRITE_CONV [exec_block_def]))) >>
  ASM_REWRITE_TAC[] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[]
QED

(* Non-terminator single step: if IH gives block_subst_rel for continuation,
   then block_subst_rel holds for the current step too *)
Theorem run_block_subst_non_term[local]:
  !fuel ctx bb s m.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
    bb_well_formed bb /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!s1. step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s = OK s1 ==>
          block_subst_rel m
            (exec_block fuel ctx bb (s1 with vs_inst_idx := SUC s.vs_inst_idx))
            (exec_block fuel ctx (subst_block_labels_block m bb)
               (s1 with vs_inst_idx := SUC s.vs_inst_idx)))
    ==>
    block_subst_rel m
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (subst_block_labels_block m bb) s)
Proof
  rpt strip_tac >>
  `get_instruction bb s.vs_inst_idx =
   SOME (EL s.vs_inst_idx bb.bb_instructions)`
    by simp[get_instruction_def] >>
  `get_instruction (subst_block_labels_block m bb) s.vs_inst_idx =
   SOME (subst_block_labels_inst m (EL s.vs_inst_idx bb.bb_instructions))`
    by simp[get_instruction_subst, subst_block_labels_block_length] >>
  `step_inst fuel ctx (subst_block_labels_inst m
     (EL s.vs_inst_idx bb.bb_instructions)) s =
   step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` by (
    irule step_inst_subst_non_term >> ASM_REWRITE_TAC[] >>
    Cases_on `s.vs_prev_bb` >> fs[]) >>
  `~is_terminator (subst_block_labels_inst m
     (EL s.vs_inst_idx bb.bb_instructions)).inst_opcode` by
    simp[subst_block_labels_inst_opcode] >>
  `exec_block fuel ctx bb s =
     case step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s of
       OK s' => exec_block fuel ctx bb (s' with vs_inst_idx := SUC s.vs_inst_idx)
     | Halt s' => Halt s'
     | Abort a s' => Abort a s'
     | IntRet v s' => IntRet v s'
     | Error e => Error e` by (
    irule run_block_non_term_unfold >> ASM_REWRITE_TAC[]) >>
  `exec_block fuel ctx (subst_block_labels_block m bb) s =
     case step_inst fuel ctx
       (subst_block_labels_inst m (EL s.vs_inst_idx bb.bb_instructions)) s of
       OK s' => exec_block fuel ctx (subst_block_labels_block m bb)
                  (s' with vs_inst_idx := SUC s.vs_inst_idx)
     | Halt s' => Halt s'
     | Abort a s' => Abort a s'
     | IntRet v s' => IntRet v s'
     | Error e => Error e` by (
    irule run_block_non_term_unfold >>
    ASM_REWRITE_TAC[]) >>
  ASM_REWRITE_TAC[] >>
  Cases_on `step_inst fuel ctx
              (EL s.vs_inst_idx bb.bb_instructions) s`
  >- ((* OK: apply IH hypothesis *)
    gvs[block_subst_rel_def])
  >> (* Non-OK: both sides identical *)
  gvs[block_subst_rel_def, execution_equiv_refl]
QED

(* Base case: inst_idx >= LENGTH *)
Theorem run_block_subst_base[local]:
  !fuel ctx bb s m.
    s.vs_inst_idx >= LENGTH bb.bb_instructions ==>
    block_subst_rel m
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (subst_block_labels_block m bb) s)
Proof
  rpt strip_tac >>
  `s.vs_inst_idx >= LENGTH (subst_block_labels_block m bb).bb_instructions` by
    simp[subst_block_labels_block_length] >>
  `get_instruction bb s.vs_inst_idx = NONE` by simp[get_instruction_def] >>
  `get_instruction (subst_block_labels_block m bb) s.vs_inst_idx = NONE` by
    simp[get_instruction_def, subst_block_labels_block_length] >>
  simp[Once exec_block_def, block_subst_rel_def] >>
  simp[Once exec_block_def]
QED

(* Helper: apply IH in the non-terminator recursive case *)
Theorem run_block_subst_non_term_IH[local]:
  !fuel ctx bb s m s1.
    step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s = OK s1 /\
    ~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    bb_well_formed bb /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!fuel' ctx' bb' s' m'.
       LENGTH bb'.bb_instructions - s'.vs_inst_idx <
         LENGTH bb.bb_instructions - s.vs_inst_idx /\
       bb_well_formed bb' /\
       s'.vs_inst_idx <= LENGTH bb'.bb_instructions /\
       (case s'.vs_prev_bb of
          NONE => T
        | SOME p => ~MEM p (MAP FST m') /\ ~MEM p (MAP SND m')) /\
       (!l. MEM l (MAP FST m') ==> FLOOKUP s'.vs_labels l = NONE) /\
       (!l. MEM l (MAP SND m') ==> FLOOKUP s'.vs_labels l = NONE) ==>
       block_subst_rel m'
         (exec_block fuel' ctx' bb' s')
         (exec_block fuel' ctx' (subst_block_labels_block m' bb') s')) ==>
    block_subst_rel m
      (exec_block fuel ctx bb (s1 with vs_inst_idx := SUC s.vs_inst_idx))
      (exec_block fuel ctx (subst_block_labels_block m bb)
         (s1 with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  rpt strip_tac >>
  `s1.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[step_preserves_control_flow] >>
  `s1.vs_labels = s.vs_labels` by
    metis_tac[step_preserves_labels] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`,
    `s1 with vs_inst_idx := SUC s.vs_inst_idx`, `m`] mp_tac) >>
  (impl_tac >- (simp[] >> Cases_on `s.vs_prev_bb` >> gvs[])) >>
  simp[]
QED

(* Main induction: compose term + non_term + base.
   Tactic-free body: just dispatches to sub-lemmas *)

Theorem run_block_subst_equiv[local]:
  !n fuel ctx bb s m.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    bb_well_formed bb /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) ==>
    block_subst_rel m
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (subst_block_labels_block m bb) s)
Proof
  completeInduct_on `n` >> rw[] >>
  Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >- (
    Cases_on `is_terminator
      (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >- (
      irule run_block_subst_term >> simp[] >>
      Cases_on `s.vs_prev_bb` >> gvs[]
    ) >>
    irule run_block_subst_non_term >> simp[] >>
    rpt strip_tac >>
    irule run_block_subst_non_term_IH >> simp[] >>
    rpt strip_tac >>
    first_x_assum (qspecl_then [`fuel'`, `ctx'`, `bb'`, `s'`, `m'`]
      mp_tac) >>
    (impl_tac >- simp[])
  ) >>
  irule run_block_subst_base >> simp[]
QED

(* ================================================================
   Section 5: Helpers for tail_merge_fn_correct_gen
   ================================================================ *)

(* exec_block OK from inst_idx=0 on a well-formed block implies no PHIs.
   Reason: step_inst on PHI returns Error, so exec_block would return Error.
   Uses phi_before_non_phi (PHIs form a prefix in well-formed blocks). *)
Theorem exec_block_OK_imp_no_phis[local]:
  !fuel ctx bb s v.
    bb_well_formed bb /\
    exec_block fuel ctx bb s = OK v /\
    s.vs_inst_idx = 0 ==>
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  fs[listTheory.NOT_EVERY_EXISTS_FIRST] >>
  `0 < LENGTH bb.bb_instructions` by decide_tac >>
  Cases_on `(EL 0 bb.bb_instructions).inst_opcode = PHI` THENL [
    (* YES case: EL 0 is PHI. exec_block encounters it and step_inst returns Error.
       So exec_block returns Error, contradiction with exec_block = OK v *)
    `(EL 0 bb.bb_instructions).inst_opcode <> INVOKE` by simp[] >>
    `get_instruction bb 0 = SOME (EL 0 bb.bb_instructions)` by simp[get_instruction_def] >>
    `step_inst fuel ctx (EL 0 bb.bb_instructions) s = Error "phi outside prefix"`
      by metis_tac[venomExecProofsTheory.step_inst_phi_error] >>
    (* Unfold exec_block = OK v in the assumption to get step_inst, then contradiction *)
    qpat_x_assum `exec_block _ _ _ _ = OK _` (assume_tac o ONCE_REWRITE_RULE[exec_block_def]) >>
    gvs[get_instruction_def],
    (* NO case: EL 0 is not PHI. But EL i is PHI (from NOT_EVERY_EXISTS_FIRST).
       phi_before_non_phi(i,0) gives i < 0, which is impossible. *)
    mp_tac (Q.SPECL [`bb`, `i`, `0`] venomExecProofsTheory.phi_before_non_phi) >>
    simp[] >> decide_tac]
QED

(* Bridge: run_block_entry = OK v when exec_block = OK v and no_phis *)
Theorem run_block_entry_eq_exec_block_OK[local]:
  !fuel ctx bb s v.
    bb_well_formed bb /\
    exec_block fuel ctx bb s = OK v /\
    s.vs_inst_idx = 0 ==>
    run_block_entry fuel ctx bb s = OK v
Proof
  rpt strip_tac >>
  imp_res_tac exec_block_OK_imp_no_phis >>
  imp_res_tac venomExecProofsTheory.run_block_no_phis_eq_exec_block >>
  fs[venom_state_component_equality]
QED

(* FIND SOME implies MEM *)
Theorem FIND_SOME_MEM[local]:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[listTheory.FIND_thm] >> rw[] >> metis_tac[]
QED

(* lookup_block SOME implies MEM *)
Theorem lookup_block_MEM[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  rw[lookup_block_def] >> metis_tac[FIND_SOME_MEM]
QED

Theorem FIND_SOME_P[local]:
  !P l x. FIND P l = SOME x ==> P x
Proof
  Induct_on `l` >> simp[listTheory.FIND_thm] >> rw[] >> gvs[]
QED

Theorem lookup_block_label[local]:
  !lbl bbs bb. lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  rw[lookup_block_def] >> imp_res_tac FIND_SOME_P >> gvs[]
QED

Theorem ALL_DISTINCT_MAP_MEM_INJ[local]:
  !f l x y.
    ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ (f x = f y) ==>
    x = y
Proof
  strip_tac >> Induct_on `l` >> simp[] >> rw[] >> gvs[] >>
  fs[listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem lookup_block_MEM_unique[local]:
  !func lbl bb bb2.
    lookup_block lbl func.fn_blocks = SOME bb /\
    MEM bb2 func.fn_blocks /\ bb2.bb_label = lbl /\
    wf_function func ==>
    bb = bb2
Proof
  rw[] >>
  imp_res_tac lookup_block_label >>
  imp_res_tac lookup_block_MEM >>
  `bb.bb_label = bb2.bb_label` by gvs[] >>
  gvs[wf_function_def, fn_labels_def] >>
  metis_tac[ALL_DISTINCT_MAP_MEM_INJ]
QED

(* wf_function + lookup_block => bb_well_formed *)
Theorem wf_lookup_bb_well_formed[local]:
  !func lbl bb.
    wf_function func /\ lookup_block lbl func.fn_blocks = SOME bb ==>
    bb_well_formed bb
Proof
  rw[wf_function_def] >> metis_tac[lookup_block_MEM]
QED

(* execution_equiv UNIV is symmetric *)
Theorem execution_equiv_UNIV_sym[local]:
  !s1 s2. execution_equiv UNIV s1 s2 ==> execution_equiv UNIV s2 s1
Proof
  simp[execution_equiv_def]
QED

(* result_equiv UNIV is symmetric *)
Theorem result_equiv_UNIV_sym[local]:
  !r1 r2. result_equiv UNIV r1 r2 ==> result_equiv UNIV r2 r1
Proof
  Cases >> Cases >> simp[result_equiv_def, execution_equiv_def] >>
  simp[state_equiv_def, execution_equiv_def]
QED

(* Halting terminator: step_inst never returns OK *)
Theorem halting_term_step_not_ok[local]:
  !fuel ctx inst s.
    is_halting_opcode inst.inst_opcode /\
    is_terminator inst.inst_opcode ==>
    !v. step_inst fuel ctx inst s <> OK v
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (
    Cases_on `inst.inst_opcode` >> gvs[is_halting_opcode_def]) >>
  `step_inst fuel ctx inst s = step_inst_base inst s` by
    metis_tac[step_inst_non_invoke] >>
  `inst.inst_opcode <> JMP /\ inst.inst_opcode <> JNZ /\
   inst.inst_opcode <> DJMP` by (
    Cases_on `inst.inst_opcode` >> gvs[is_halting_opcode_def]) >>
  metis_tac[step_inst_base_non_jump_term_not_ok]
QED

(* At a terminator in a halting well-formed block, the instruction is halting *)
Theorem wf_halting_term_is_halting[local]:
  !bb idx inst.
    bb_is_halting bb /\ bb_well_formed bb /\
    idx < LENGTH bb.bb_instructions /\
    get_instruction bb idx = SOME inst /\
    is_terminator inst.inst_opcode ==>
    is_halting_opcode inst.inst_opcode
Proof
  rw[] >>
  `idx = PRE (LENGTH bb.bb_instructions)` by (
    gvs[bb_well_formed_def] >> res_tac >>
    gvs[get_instruction_def, AllCaseEqs(), listTheory.EL_MAP]) >>
  `inst = LAST bb.bb_instructions` by (
    gvs[get_instruction_def, AllCaseEqs(), listTheory.EL_MAP] >>
    metis_tac[listTheory.LAST_EL, bb_is_halting_def]) >>
  gvs[bb_is_halting_def]
QED

(* Helper: base case — past end of block *)
Theorem halting_block_not_OK_base[local]:
  !fuel ctx bb s.
    bb_is_halting bb /\ bb_well_formed bb /\
    LENGTH bb.bb_instructions <= s.vs_inst_idx ==>
    (!s'. exec_block fuel ctx bb s <> OK s')
Proof
  rw[] >> simp[Once exec_block_def, get_instruction_def]
QED

(* Helper: terminator case — halting opcode never OK *)
Theorem halting_block_not_OK_term[local]:
  !fuel ctx bb s inst.
    bb_is_halting bb /\ bb_well_formed bb /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode ==>
    (!s'. exec_block fuel ctx bb s <> OK s')
Proof
  rw[] >>
  mp_tac (Q.SPECL [`bb`, `s.vs_inst_idx`, `inst`]
    wf_halting_term_is_halting) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`]
    halting_term_step_not_ok) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  simp[Once exec_block_def] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[]
QED

(* get_instruction exists when idx < LENGTH *)
Theorem get_instruction_exists[local]:
  !bb idx. idx < LENGTH bb.bb_instructions ==>
    ?inst. get_instruction bb idx = SOME inst
Proof
  simp[get_instruction_def, AllCaseEqs()]
QED

(* Halting blocks never return OK: base case (measure = 0) *)
Theorem halting_block_not_OK_zero[local]:
  !fuel ctx bb s s'.
    0 = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    bb_is_halting bb /\ bb_well_formed bb /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    exec_block fuel ctx bb s = OK s' ==> F
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`] halting_block_not_OK_base) >>
  ASM_REWRITE_TAC[] >>
  (impl_tac >- DECIDE_TAC) >>
  metis_tac[]
QED

(* idx < LENGTH from SUC v = LENGTH - idx and idx <= LENGTH *)
Theorem suc_diff_implies_lt[local]:
  !v n m. SUC v = n - m /\ m <= n ==> m < n
Proof
  DECIDE_TAC
QED

(* Halting blocks never return OK from exec_block — step case *)
Theorem halting_block_not_OK_suc[local]:
  !v fuel ctx bb s s'.
    SUC v = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    bb_is_halting bb /\ bb_well_formed bb /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    exec_block fuel ctx bb s = OK s' /\
    (!bb1 s1 fuel1 ctx1 s1'.
       v = LENGTH bb1.bb_instructions - s1.vs_inst_idx /\
       bb_is_halting bb1 /\ bb_well_formed bb1 /\
       s1.vs_inst_idx <= LENGTH bb1.bb_instructions /\
       exec_block fuel1 ctx1 bb1 s1 = OK s1' ==> F)
    ==> F
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`v`, `LENGTH bb.bb_instructions`,
    `s.vs_inst_idx`] suc_diff_implies_lt) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  mp_tac (Q.SPECL [`bb`, `s.vs_inst_idx`] get_instruction_exists) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode` >- (
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`, `inst`]
      halting_block_not_OK_term) >>
    ASM_REWRITE_TAC[] >> metis_tac[]
  ) >>
  Cases_on `step_inst fuel ctx inst s` >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def]
QED

(* Halting blocks never return OK from exec_block *)
Theorem halting_block_not_OK[local]:
  !fuel ctx bb s s'.
    bb_is_halting bb /\ bb_well_formed bb /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    exec_block fuel ctx bb s = OK s' ==> F
Proof
  Induct_on `LENGTH bb.bb_instructions - s.vs_inst_idx`
  >- metis_tac[halting_block_not_OK_zero]
  >> metis_tac[halting_block_not_OK_suc]
QED

(* After exec_block OK, prev_bb = SOME (entry current_bb).
   Non-terminators preserve current_bb and prev_bb.
   Jump terminators call jump_to which sets prev_bb := SOME current_bb *)
(* exec_block OK sets prev_bb to current_bb *)
Theorem run_block_OK_prev_bb[local]:
  !n fuel ctx bb s s'.
    n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
    exec_block fuel ctx bb s = OK s' ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  Induct >> rpt strip_tac >- (
    (* n = 0: no instructions left => get_instruction = NONE => Error *)
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    simp[Once exec_block_def] >>
    `get_instruction bb s.vs_inst_idx = NONE` by (
      simp[get_instruction_def] >>
      Cases_on `s.vs_inst_idx < LENGTH bb.bb_instructions` >>
      gvs[]) >>
    simp[]
  ) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  Cases_on `step_inst fuel ctx x s` >> simp[] >>
  rw[] >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[] >- (
    `x.inst_opcode <> INVOKE` by (Cases_on `x.inst_opcode` >> gvs[is_terminator_def]) >>
    `step_inst_base x s = OK s'` by metis_tac[step_inst_non_invoke] >>
    drule_all venomExecPropsTheory.step_inst_base_term_prev_bb >> simp[]
  ) >>
  (* non-terminator: recurse *)
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`,
    `v with vs_inst_idx := SUC s.vs_inst_idx`, `s'`] mp_tac) >>
  imp_res_tac step_preserves_control_flow >> gvs[]
QED

(* Connecting tail_merge_fn blocks to FILTER/MAP.
   When merge_map <> [] and entry exists *)
Theorem lookup_block_tail_merge_fn[local]:
  !func lbl bb m entry.
    fn_entry_label func = SOME entry /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    m <> [] /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    ~MEM lbl (MAP FST m) ==>
    lookup_block lbl (tail_merge_fn func).fn_blocks =
      SOME (subst_block_labels_block m bb)
Proof
  rw[tail_merge_fn_def, subst_block_labels_fn_def] >>
  gvs[] >>
  irule lookup_block_tail_merge >> simp[]
QED

(* When merge_map = [], tail_merge_fn is identity *)
Theorem tail_merge_fn_nil_merge_map[local]:
  !func entry.
    fn_entry_label func = SOME entry /\
    compute_merge_map (block_sigs func entry func.fn_blocks) [] = [] ==>
    tail_merge_fn func = func
Proof
  rw[tail_merge_fn_def]
QED

(* When fn_entry_label = NONE, tail_merge_fn is identity *)
Theorem tail_merge_fn_no_entry[local]:
  !func.
    fn_entry_label func = NONE ==>
    tail_merge_fn func = func
Proof
  rw[tail_merge_fn_def]
QED

(* Helper: merge map labels correspond to actual blocks, so
   lookup_block matches the block from compute_merge_map_halting *)
Theorem merge_map_lookup_halting[local]:
  !func entry m lbl bb.
    wf_function func /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    (?keeper. MEM (lbl, keeper) m \/ MEM (keeper, lbl) m) ==>
    bb_is_halting bb
Proof
  rw[] >> (
    drule compute_merge_map_halting >> strip_tac >>
    `bb.bb_label = lbl` by metis_tac[lookup_block_label] >> (
      `bb = bb_lbl` by metis_tac[lookup_block_MEM_unique] ORELSE
      `bb = bb_kpr` by metis_tac[lookup_block_MEM_unique]
    ) >> gvs[]
  )
QED

(* Source labels are halting *)
Theorem merge_source_halting[local]:
  !func entry m lbl bb.
    wf_function func /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    MEM lbl (MAP FST m) /\
    lookup_block lbl func.fn_blocks = SOME bb ==>
    bb_is_halting bb
Proof
  rw[] >> gvs[listTheory.MEM_MAP] >>
  Cases_on `y` >> gvs[] >>
  metis_tac[merge_map_lookup_halting]
QED

(* Keeper labels are halting *)
Theorem merge_keeper_halting[local]:
  !func entry m lbl bb.
    wf_function func /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    MEM lbl (MAP SND m) /\
    lookup_block lbl func.fn_blocks = SOME bb ==>
    bb_is_halting bb
Proof
  rw[] >> gvs[listTheory.MEM_MAP] >>
  Cases_on `y` >> gvs[] >>
  metis_tac[merge_map_lookup_halting]
QED

(* subst_block_labels_block preserves bb_is_halting *)
Theorem bb_is_halting_subst[local]:
  !m bb. bb_is_halting bb ==> bb_is_halting (subst_block_labels_block m bb)
Proof
  rw[bb_is_halting_def, subst_block_labels_block_def]
QED

(* subst_block_labels_block preserves bb_well_formed *)
Theorem bb_well_formed_subst[local]:
  !m bb. bb_well_formed bb ==> bb_well_formed (subst_block_labels_block m bb)
Proof
  rw[bb_well_formed_def, subst_block_labels_block_def] >>
  gvs[listTheory.EL_MAP, subst_block_labels_inst_opcode] >>
  metis_tac[]
QED

(* Composing result_equiv with block_subst_rel for non-OK results *)
Theorem result_equiv_block_subst_rel_non_ok[local]:
  !m r1 r2 r3.
    result_equiv UNIV r1 r2 /\ block_subst_rel m r2 r3 /\
    (!s. r2 <> OK s) ==>
    result_equiv UNIV r1 r3
Proof
  rpt strip_tac >>
  Cases_on `r2` >> gvs[block_subst_rel_def] >>
  (* Only Halt remains: compose ee via sym+trans *)
  Cases_on `r1` >> gvs[result_equiv_def] >>
  irule stateEquivPropsTheory.execution_equiv_trans >>
  qexists_tac `v` >> simp[] >>
  irule execution_equiv_UNIV_sym >> simp[]
QED

(* Label substitution preserves no_phis (doesn't change opcodes) *)
Theorem no_phis_subst_block_labels[local]:
  !m bb. no_phis bb ==> no_phis (subst_block_labels_block m bb)
Proof
  simp[no_phis_def, subst_block_labels_block_def, listTheory.EVERY_MAP] >>
  metis_tac[subst_block_labels_inst_opcode]
QED

Theorem phi_prefix_length_subst_block_labels[local]:
  !m insts.
    phi_prefix_length (MAP (subst_block_labels_inst m) insts) =
    phi_prefix_length insts
Proof
  Induct_on `insts` >> simp[phi_prefix_length_def, subst_block_labels_inst_opcode]
QED

Theorem eval_one_phi_subst_block_labels[local]:
  !m inst (s:venom_state).
    inst.inst_opcode = PHI /\
    (case s.vs_prev_bb of NONE => T
     | SOME prev => ~MEM prev (MAP FST m) /\ ~MEM prev (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) ==>
    eval_one_phi s (subst_block_labels_inst m inst) = eval_one_phi s inst
Proof
  rw[subst_block_labels_inst_def, is_block_label_opcode_def,
     subst_label_map_inst_def, eval_one_phi_def] >>
  simp[venomInstTheory.is_terminator_def] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `s.vs_prev_bb` >> simp[] >>
  gvs[resolve_phi_subst_comm] >>
  Cases_on `resolve_phi x inst.inst_operands` >> simp[] >>
  `eval_operand (subst_label_map_op m x') s = eval_operand x' s` by (
    irule eval_operand_subst_label_map >> simp[]) >>
  simp[]
QED

Theorem eval_phis_subst_block_labels[local]:
  !m (s:venom_state) insts.
    (case s.vs_prev_bb of NONE => T
     | SOME prev => ~MEM prev (MAP FST m) /\ ~MEM prev (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) ==>
    eval_phis s (MAP (subst_block_labels_inst m) insts) = eval_phis s insts
Proof
  Induct_on `insts` >> simp[eval_phis_def] >>
  rpt strip_tac >>
  `(subst_block_labels_inst m h).inst_opcode = h.inst_opcode` by
    simp[subst_block_labels_inst_opcode] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def] >>
  `eval_one_phi s (subst_block_labels_inst m h) = eval_one_phi s h` by (
    irule eval_one_phi_subst_block_labels >> simp[]) >>
  simp[] >>
  Cases_on `eval_one_phi s h` >> simp[] >>
  Cases_on `x` >> simp[]
QED

(* Helper: run_blocks on a halting no-phis block reduces to exec_block.
   With no_phis, run_block = exec_block (s with vs_inst_idx := 0).
   Since s.vs_inst_idx = 0, this is exec_block s.
   For a halting block, exec_block never returns OK,
   so the run_blocks wrapper passes through the result unchanged. *)
Theorem run_function_halting_step[local]:
  !fuel ctx fn bb s.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    bb_is_halting bb /\ bb_well_formed bb /\ no_phis bb /\ ~s.vs_halted /\
    s.vs_inst_idx = 0 ==>
    run_blocks (SUC fuel) ctx fn s = exec_block fuel ctx bb s
Proof
  rpt strip_tac >>
  fs[no_phis_def] >>
  drule venomExecProofsTheory.run_block_no_phis_eq_exec_block >>
  strip_tac >>
  `s with vs_inst_idx := 0 = s` by
    simp[venomStateTheory.venom_state_component_equality] >>
  simp[Once run_blocks_unfold] >>
  gvs[] >>
  Cases_on `exec_block fuel ctx bb s` >> gvs[] >>
  metis_tac[halting_block_not_OK, DECIDE ``0 ≤ n:num``]
QED

(* Helper: MEM bb bbs with bb.bb_label = lbl => lookup_block finds something *)
Theorem MEM_lookup_block_exists[local]:
  !lbl bbs bb.
    MEM bb bbs /\ bb.bb_label = lbl ==>
    ?bb'. lookup_block lbl bbs = SOME bb'
Proof
  rpt strip_tac >> gvs[] >>
  simp[lookup_block_def] >>
  Cases_on `FIND (\b. b.bb_label = bb.bb_label) bbs` >- (
    gvs[listTheory.FIND_thm] >>
    Induct_on `bbs` >> simp[listTheory.FIND_thm] >>
    rw[] >> gvs[] >> metis_tac[]
  ) >>
  metis_tac[]
QED

(* Helper: source block from merge map has lookup, is halting, wf, has sig *)
Theorem merge_source_lookup[local]:
  !func entry m src.
    wf_function func /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    MEM src (MAP FST m) ==>
    ?bb. lookup_block src func.fn_blocks = SOME bb /\
         bb_is_halting bb /\ bb_well_formed bb /\
         block_signature bb <> NONE
Proof
  rw[] >> gvs[listTheory.MEM_MAP] >>
  Cases_on `y` >> gvs[] >>
  drule compute_merge_map_source >> strip_tac >>
  drule block_sigs_MEM_blocks >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`bb.bb_label`, `func.fn_blocks`, `bb`]
    MEM_lookup_block_exists) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  `bb' = bb` by metis_tac[lookup_block_MEM_unique] >> gvs[] >>
  rpt conj_tac >- (
    irule merge_source_halting >>
    qexistsl_tac [`entry`, `func`] >> simp[] >>
    simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST]
  ) >- (
    irule wf_lookup_bb_well_formed >> metis_tac[]
  ) >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

(* Helper: keeper block from merge map has lookup, is halting, wf, has sig *)
Theorem merge_keeper_lookup[local]:
  !func entry m keeper.
    wf_function func /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    MEM keeper (MAP SND m) ==>
    ?bb. lookup_block keeper func.fn_blocks = SOME bb /\
         bb_is_halting bb /\ bb_well_formed bb /\
         block_signature bb <> NONE
Proof
  rw[] >> gvs[listTheory.MEM_MAP] >>
  Cases_on `y` >> gvs[] >>
  drule compute_merge_map_keeper_same_sig >> strip_tac >>
  drule_at (Pos last) block_sigs_MEM_blocks >> strip_tac >> gvs[] >>
  mp_tac (Q.SPECL [`bb.bb_label`, `func.fn_blocks`, `bb`]
    MEM_lookup_block_exists) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  `bb' = bb` by metis_tac[lookup_block_MEM_unique] >> gvs[] >>
  rpt conj_tac >- (
    irule merge_keeper_halting >>
    qexistsl_tac [`entry`, `func`] >> simp[] >>
    simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.SND]
  ) >- (
    irule wf_lookup_bb_well_formed >> metis_tac[]
  ) >>
  metis_tac[optionTheory.NOT_SOME_NONE]
QED

(* lookup_block NONE is preserved by MAP subst_block_labels_block *)
Theorem lookup_block_NONE_MAP_subst[local]:
  !lbl m bbs.
    lookup_block lbl bbs = NONE ==>
    lookup_block lbl (MAP (subst_block_labels_block m) bbs) = NONE
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, listTheory.FIND_thm] >>
  rw[subst_block_labels_block_def] >>
  gvs[lookup_block_def]
QED

(* lookup_block NONE is preserved by FILTER *)
Theorem lookup_block_NONE_FILTER[local]:
  !lbl P bbs.
    lookup_block lbl bbs = NONE ==>
    lookup_block lbl (FILTER P bbs) = NONE
Proof
  Induct_on `bbs` >>
  simp[lookup_block_def, listTheory.FIND_thm, listTheory.FILTER] >>
  rw[] >> simp[listTheory.FIND_thm] >> gvs[lookup_block_def]
QED

(* lookup_block NONE propagates through tail_merge_fn *)
Theorem lookup_block_NONE_tail_merge_fn[local]:
  !lbl func.
    lookup_block lbl func.fn_blocks = NONE ==>
    lookup_block lbl (tail_merge_fn func).fn_blocks = NONE
Proof
  rw[tail_merge_fn_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  simp[subst_block_labels_fn_def] >>
  irule lookup_block_NONE_FILTER >>
  irule lookup_block_NONE_MAP_subst >> simp[]
QED

(* Keeper blocks are halting, so exec_block on them can never return OK *)
Theorem keeper_block_not_OK[local]:
  !func entry m lbl bb fuel ctx s s'.
    wf_function func /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    MEM lbl (MAP SND m) /\
    lookup_block lbl func.fn_blocks = SOME bb /\
    bb_well_formed bb /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    exec_block fuel ctx bb s = OK s' ==> F
Proof
  rpt strip_tac >>
  `bb_is_halting bb` by metis_tac[merge_keeper_halting] >>
  metis_tac[halting_block_not_OK]
QED

(* Helper: merge map pairs have same block signature *)
Theorem merge_pair_same_sig[local]:
  !func entry m lbl keeper src_bb kpr_bb.
    wf_function func /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    MEM (lbl, keeper) m /\
    lookup_block lbl func.fn_blocks = SOME src_bb /\
    lookup_block keeper func.fn_blocks = SOME kpr_bb ==>
    block_signature src_bb = block_signature kpr_bb
Proof
  rpt strip_tac >> gvs[] >>
  drule compute_merge_map_halting >> strip_tac >>
  `src_bb = bb_lbl` by metis_tac[lookup_block_MEM_unique] >>
  `kpr_bb = bb_kpr` by metis_tac[lookup_block_MEM_unique] >>
  gvs[]
QED

(* Helper: block_subst_rel for a keeper block after OK return from non-source block.
   Bundles run_block_subst_equiv + prev_bb reasoning + keeper_block_not_OK. *)
Theorem block_subst_rel_after_ok[local]:
  !fuel fuel' ctx m bb s s' kpr_bb s''.
    ~MEM s.vs_current_bb (MAP FST m) /\
    ~MEM s.vs_current_bb (MAP SND m) /\
    bb_well_formed bb /\ s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    exec_block fuel ctx bb s = OK s' /\
    bb_well_formed kpr_bb /\
    s''.vs_inst_idx = 0 /\
    s''.vs_prev_bb = s'.vs_prev_bb /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s''.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s''.vs_labels l = NONE) ==>
    block_subst_rel m (exec_block fuel' ctx kpr_bb s'')
      (exec_block fuel' ctx (subst_block_labels_block m kpr_bb) s'')
Proof
  rpt strip_tac >>
  `s'.vs_prev_bb = SOME s.vs_current_bb` by (
    mp_tac (Q.SPECL [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
                       `fuel`, `ctx`, `bb`, `s`, `s'`]
              run_block_OK_prev_bb) >>
    ASM_REWRITE_TAC[]) >>
  `s''.vs_prev_bb = SOME s.vs_current_bb` by ASM_REWRITE_TAC[] >>
  irule run_block_subst_equiv >>
  ASM_REWRITE_TAC[optionTheory.option_case_def] >>
  simp[]
QED

(* OK-continuation case *)
(* SOME-keeper case *)
Theorem tail_merge_some_case[local]:
  !fuel func ctx s entry m bb s' s'' keeper.
    wf_function func /\
    fn_entry_label func = SOME entry /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    m <> [] /\
    (!bb. MEM bb func.fn_blocks /\ block_signature bb <> NONE ==>
      EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
      EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
      EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
            bb.bb_instructions) /\
    ~MEM s.vs_current_bb (MAP FST m) /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    bb_well_formed bb /\
    exec_block fuel ctx bb s = OK s' /\
    exec_block fuel ctx (subst_block_labels_block m bb) s = OK s'' /\
    execution_equiv UNIV s'' s' /\
    s''.vs_vars = s'.vs_vars /\
    s''.vs_inst_idx = s'.vs_inst_idx /\
    s''.vs_prev_bb = s'.vs_prev_bb /\
    ~s'.vs_halted /\ ~s''.vs_halted /\
    ALOOKUP m s'.vs_current_bb = SOME keeper /\
    s''.vs_current_bb = keeper ==>
    result_equiv UNIV
      (run_blocks fuel ctx func s')
      (run_blocks fuel ctx (tail_merge_fn func) s'')
Proof
  rpt strip_tac >>
  `MEM (s'.vs_current_bb, keeper) m` by (
    drule alistTheory.ALOOKUP_MEM >> simp[]) >>
  `MEM s'.vs_current_bb (MAP FST m)` by
    metis_tac[listTheory.MEM_MAP, pairTheory.FST] >>
  `MEM keeper (MAP SND m)` by
    metis_tac[listTheory.MEM_MAP, pairTheory.SND] >>
  `?src_bb. lookup_block s'.vs_current_bb func.fn_blocks = SOME src_bb /\
            bb_is_halting src_bb /\ bb_well_formed src_bb /\
            block_signature src_bb <> NONE` by (
    mp_tac (Q.SPECL [`func`, `entry`, `m`, `s'.vs_current_bb`]
      merge_source_lookup) >> ASM_REWRITE_TAC[]) >>
  `?kpr_bb. lookup_block keeper func.fn_blocks = SOME kpr_bb /\
            bb_is_halting kpr_bb /\ bb_well_formed kpr_bb /\
            block_signature kpr_bb <> NONE` by (
    mp_tac (Q.SPECL [`func`, `entry`, `m`, `keeper`]
      merge_keeper_lookup) >> ASM_REWRITE_TAC[]) >>
  `MEM src_bb func.fn_blocks` by
    metis_tac[lookup_block_MEM] >>
  `MEM kpr_bb func.fn_blocks` by
    metis_tac[lookup_block_MEM] >>
  `block_signature src_bb = block_signature kpr_bb` by (
    mp_tac (Q.SPECL [`func`, `entry`, `m`, `s'.vs_current_bb`, `keeper`,
      `src_bb`, `kpr_bb`] merge_pair_same_sig) >>
    ASM_REWRITE_TAC[]
  ) >>
  `s'.vs_inst_idx = 0` by (
    drule venomExecPropsTheory.exec_block_OK_inst_idx_0 >> simp[]) >>
  Cases_on `fuel` THENL [simp[run_blocks_def, result_equiv_def], ALL_TAC] >>
  `no_phis src_bb` by (
    simp[no_phis_def] >>
    `bb_self_contained src_bb` by (
      CCONTR_TAC >> fs[block_signature_def] >>
      Cases_on `bb_is_halting src_bb` >> fs[]) >>
    fs[bb_self_contained_def]) >>
  `run_blocks (SUC n) ctx func s' = exec_block n ctx src_bb s'` by (
    irule run_function_halting_step >> simp[]
  ) >>
  `ALL_DISTINCT (MAP FST (block_sigs func entry func.fn_blocks))` by (
    irule block_sigs_all_distinct_FST >>
    gvs[wf_function_def, fn_labels_def]
  ) >>
  `DISJOINT (set (MAP FST m)) (set (MAP SND m))` by (
    ASM_REWRITE_TAC[] >>
    irule compute_merge_map_disjoint >> ASM_REWRITE_TAC[]
  ) >>
  `~MEM keeper (MAP FST m)` by (
    CCONTR_TAC >>
    gvs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
    metis_tac[]
  ) >>
  `lookup_block keeper (tail_merge_fn func).fn_blocks =
     SOME (subst_block_labels_block m kpr_bb)` by (
    irule lookup_block_tail_merge_fn >> simp[] >>
    drule compute_merge_map_not_entry >> simp[]
  ) >>
  `s''.vs_inst_idx = 0` by simp[] >>
  `bb_is_halting (subst_block_labels_block m kpr_bb)` by (
    irule bb_is_halting_subst >> ASM_REWRITE_TAC[]) >>
  `bb_well_formed (subst_block_labels_block m kpr_bb)` by (
    irule bb_well_formed_subst >> ASM_REWRITE_TAC[]) >>
  `s''.vs_inst_idx <= LENGTH (subst_block_labels_block m kpr_bb).bb_instructions` by
    simp[subst_block_labels_block_length] >>
  `no_phis kpr_bb` by (
    simp[no_phis_def] >>
    `bb_self_contained kpr_bb` by (
      CCONTR_TAC >> fs[block_signature_def] >>
      Cases_on `bb_is_halting kpr_bb` >> fs[]) >>
    fs[bb_self_contained_def]) >>
  `no_phis (subst_block_labels_block m kpr_bb)` by (
    irule no_phis_subst_block_labels >> ASM_REWRITE_TAC[]) >>
  `run_blocks (SUC n) ctx (tail_merge_fn func) s'' =
   exec_block n ctx (subst_block_labels_block m kpr_bb) s''` by (
    irule run_function_halting_step >> ASM_REWRITE_TAC[]
  ) >>
  qpat_x_assum `run_blocks _ _ (tail_merge_fn _) _ = _`
    (fn th => REWRITE_TAC[th]) >>
  qpat_x_assum `run_blocks _ _ func _ = _`
    (fn th => REWRITE_TAC[th]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE) src_bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> PARAM) src_bb.bb_instructions /\
   ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) src_bb.bb_instructions)) /\
   EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
         src_bb.bb_instructions` by (
    first_assum (qspec_then `src_bb` mp_tac) >> simp[]
  ) >>
  `EVERY (\i. i.inst_opcode <> INVOKE) kpr_bb.bb_instructions /\
   EVERY (\i. i.inst_opcode <> PARAM) kpr_bb.bb_instructions /\
   ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) kpr_bb.bb_instructions)) /\
   EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
         kpr_bb.bb_instructions` by (
    first_assum (qspec_then `kpr_bb` mp_tac) >> simp[]
  ) >>
  `result_equiv UNIV (exec_block n ctx src_bb s')
                     (exec_block n ctx kpr_bb s'')` by (
    irule halting_sig_equiv >> simp[] >>
    irule execution_equiv_UNIV_sym >> simp[]
  ) >>
  `~MEM s.vs_current_bb (MAP SND m)` by (
    rpt strip_tac >>
    mp_tac (Q.SPECL [`func`, `entry`, `m`,
      `s.vs_current_bb`, `bb`, `SUC n`, `ctx`, `s`, `s'`]
      keeper_block_not_OK) >>
    ASM_REWRITE_TAC[] >> simp[]) >>
  `s''.vs_labels = s.vs_labels` by (
    qpat_x_assum `exec_block _ _ (subst_block_labels_block _ _) _ = OK _`
      (mp_tac o MATCH_MP venomExecPropsTheory.exec_block_preserves_labels) >>
    simp[]) >>
  qpat_x_assum `m = _` (K ALL_TAC) >>
  mp_tac (Q.SPECL [`SUC n`, `n`, `ctx`, `m`, `bb`, `s`, `s'`,
                    `kpr_bb`, `s''`] block_subst_rel_after_ok) >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  irule result_equiv_block_subst_rel_non_ok >>
  qexists_tac `m` >>
  qexists_tac `exec_block n ctx kpr_bb s''` >>
  ASM_REWRITE_TAC[] >>
  rpt strip_tac >>
  `s''.vs_inst_idx <= LENGTH kpr_bb.bb_instructions` by simp[] >>
  metis_tac[halting_block_not_OK]
QED

(* execution_equiv UNIV + 4 field equalities => full state equality *)
Theorem execution_equiv_full_eq[local]:
  !s1 s2.
    execution_equiv UNIV s1 s2 /\
    s1.vs_vars = s2.vs_vars /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb ==>
    s1 = s2
Proof
  rpt strip_tac >>
  gvs[execution_equiv_def, venom_state_component_equality]
QED

(* Main OK case dispatcher: halted, NONE, SOME *)
Theorem tail_merge_none_case[local]:
  !fuel func ctx s entry m bb s'.
    (!func' ctx' s0.
      wf_function func' /\ fn_entry_label func' <> NONE /\
      (!bb. MEM bb func'.fn_blocks /\ block_signature bb <> NONE ==>
        EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
        EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions /\
        ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
        EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
              bb.bb_instructions) /\
      (let m' = compute_merge_map
                  (block_sigs func' (THE (fn_entry_label func'))
                              func'.fn_blocks) [] in
       ~MEM s0.vs_current_bb (MAP FST m') /\
       s0.vs_inst_idx = 0 /\
       (case s0.vs_prev_bb of
          NONE => T
        | SOME p => ~MEM p (MAP FST m') /\ ~MEM p (MAP SND m')) /\
       (!l. MEM l (MAP FST m') ==> FLOOKUP s0.vs_labels l = NONE) /\
       (!l. MEM l (MAP SND m') ==> FLOOKUP s0.vs_labels l = NONE)) ==>
      result_equiv UNIV
        (run_blocks fuel ctx' func' s0)
        (run_blocks fuel ctx' (tail_merge_fn func') s0)) /\
    wf_function func /\
    fn_entry_label func = SOME entry /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    m <> [] /\
    (!bb. MEM bb func.fn_blocks /\ block_signature bb <> NONE ==>
      EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
      EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
      EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
            bb.bb_instructions) /\
    ~MEM s.vs_current_bb (MAP FST m) /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    bb_well_formed bb /\
    exec_block fuel ctx bb s = OK s' /\
    ALOOKUP m s'.vs_current_bb = NONE /\
    ~s'.vs_halted ==>
    result_equiv UNIV
      (run_blocks fuel ctx func s')
      (run_blocks fuel ctx (tail_merge_fn func) s')
Proof
  rpt strip_tac >>
  `s'.vs_labels = s.vs_labels` by
    metis_tac[venomExecPropsTheory.exec_block_preserves_labels] >>
  `s'.vs_inst_idx = 0` by
    metis_tac[venomExecPropsTheory.exec_block_OK_inst_idx_0] >>
  `s'.vs_prev_bb = SOME s.vs_current_bb` by (
    mp_tac (Q.SPECL [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
                     `fuel`, `ctx`, `bb`, `s`, `s'`]
            run_block_OK_prev_bb) >> ASM_REWRITE_TAC[]) >>
  `~MEM s.vs_current_bb (MAP SND m)` by (
    CCONTR_TAC >> fs[] >>
    mp_tac (Q.SPECL [`func`, `entry`, `m`,
      `s.vs_current_bb`, `bb`, `fuel`, `ctx`, `s`, `s'`]
      keeper_block_not_OK) >> ASM_REWRITE_TAC[] >>
    simp[]) >>
  qpat_x_assum `m = _` SUBST_ALL_TAC >>
  first_x_assum (qspecl_then [`func`, `ctx`, `s'`] mp_tac) >>
  simp[] >>
  disch_then match_mp_tac >>
  gvs[alistTheory.ALOOKUP_NONE]
QED

Theorem tail_merge_ok_case[local]:
  !fuel func ctx s entry m bb s' s''.
    (* IH *)
    (!func' ctx' s0.
      wf_function func' /\ fn_entry_label func' <> NONE /\
      (!bb. MEM bb func'.fn_blocks /\ block_signature bb <> NONE ==>
        EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
        EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions /\
        ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
        EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
              bb.bb_instructions) /\
      (let m' = compute_merge_map
                  (block_sigs func' (THE (fn_entry_label func'))
                              func'.fn_blocks) [] in
       ~MEM s0.vs_current_bb (MAP FST m') /\
       s0.vs_inst_idx = 0 /\
       (case s0.vs_prev_bb of
          NONE => T
        | SOME p => ~MEM p (MAP FST m') /\ ~MEM p (MAP SND m')) /\
       (!l. MEM l (MAP FST m') ==> FLOOKUP s0.vs_labels l = NONE) /\
       (!l. MEM l (MAP SND m') ==> FLOOKUP s0.vs_labels l = NONE)) ==>
      result_equiv UNIV
        (run_blocks fuel ctx' func' s0)
        (run_blocks fuel ctx' (tail_merge_fn func') s0)) /\
    wf_function func /\
    fn_entry_label func = SOME entry /\
    m = compute_merge_map (block_sigs func entry func.fn_blocks) [] /\
    m <> [] /\
    (!bb. MEM bb func.fn_blocks /\ block_signature bb <> NONE ==>
      EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
      EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
      EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
            bb.bb_instructions) /\
    ~MEM s.vs_current_bb (MAP FST m) /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    (case s.vs_prev_bb of
       NONE => T
     | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
    (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
    (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE) /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    bb_well_formed bb /\
    exec_block fuel ctx bb s = OK s' /\
    exec_block fuel ctx (subst_block_labels_block m bb) s = OK s'' /\
    execution_equiv UNIV s'' s' /\
    s''.vs_vars = s'.vs_vars /\
    s''.vs_inst_idx = s'.vs_inst_idx /\
    s''.vs_prev_bb = s'.vs_prev_bb /\
    (ALOOKUP m s'.vs_current_bb = NONE ==>
     s''.vs_current_bb = s'.vs_current_bb) /\
    (!k. ALOOKUP m s'.vs_current_bb = SOME k ==>
         s''.vs_current_bb = k) ==>
    result_equiv UNIV
      (if s'.vs_halted then Halt s' else run_blocks fuel ctx func s')
      (if s''.vs_halted then Halt s''
       else run_blocks fuel ctx (tail_merge_fn func) s'')
Proof
  rpt strip_tac >>
  Cases_on `s'.vs_halted` >- (
    `s''.vs_halted` by gvs[execution_equiv_def] >>
    simp[result_equiv_def] >>
    irule execution_equiv_UNIV_sym >> simp[]
  ) >>
  `~s''.vs_halted` by gvs[execution_equiv_def] >>
  simp[] >>
  Cases_on `ALOOKUP m s'.vs_current_bb` >> simp[]
  >- (
    `s''.vs_current_bb = s'.vs_current_bb` by simp[] >>
    `s'' = s'` by (
      match_mp_tac execution_equiv_full_eq >> ASM_REWRITE_TAC[]) >>
    qpat_x_assum `s'' = s'` SUBST_ALL_TAC >>
    mp_tac (Q.SPECL [`fuel`, `func`, `ctx`, `s`, `entry`, `m`,
      `bb`, `s'`] tail_merge_none_case) >>
    ASM_REWRITE_TAC[]
  ) >>
  (* SOME: delegate to tail_merge_some_case *)
  rename1 `SOME keeper` >>
  `s''.vs_current_bb = keeper` by gvs[] >>
  mp_tac (Q.SPECL [`fuel`, `func`, `ctx`, `s`, `entry`, `m`,
    `bb`, `s'`, `s''`, `keeper`] tail_merge_some_case) >>
  ASM_REWRITE_TAC[]
QED

(* Generalized fuel induction lemma *)
Theorem tail_merge_fn_correct_gen[local]:
  !fuel func ctx s.
    wf_function func /\
    fn_entry_label func <> NONE /\
    (* Simulation prerequisites for mergeable blocks *)
    (!bb. MEM bb func.fn_blocks /\ block_signature bb <> NONE ==>
      EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
      EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
      EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
            bb.bb_instructions) /\
    (let m = compute_merge_map
               (block_sigs func (THE (fn_entry_label func))
                           func.fn_blocks) [] in
     ~MEM s.vs_current_bb (MAP FST m) /\
     s.vs_inst_idx = 0 /\
     (case s.vs_prev_bb of
        NONE => T
      | SOME p => ~MEM p (MAP FST m) /\ ~MEM p (MAP SND m)) /\
     (!l. MEM l (MAP FST m) ==> FLOOKUP s.vs_labels l = NONE) /\
     (!l. MEM l (MAP SND m) ==> FLOOKUP s.vs_labels l = NONE)) ==>
    result_equiv UNIV
      (run_blocks fuel ctx func s)
      (run_blocks fuel ctx (tail_merge_fn func) s)
Proof
  Induct_on `fuel` THENL [simp[run_blocks_def, result_equiv_def], ALL_TAC] >>
  rpt strip_tac
  >> gvs[]
  >> Cases_on `fn_entry_label func` >> gvs[]
  >> rename1 `fn_entry_label func = SOME entry`
  >> qabbrev_tac `m = compute_merge_map
       (block_sigs func entry func.fn_blocks) []`
  >> Cases_on `m = []` THENL [
       `tail_merge_fn func = func` by (
         irule tail_merge_fn_nil_merge_map >> metis_tac[]) >>
       simp[result_equiv_def] >>
       Cases_on `run_blocks (SUC fuel) ctx func s` >>
       simp[result_equiv_def, execution_equiv_def, state_equiv_def],
       ALL_TAC] >>
  simp[Once run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb func.fn_blocks` THENL [
       simp[result_equiv_def] >>
       simp[Once run_blocks_unfold] >>
       `lookup_block s.vs_current_bb (tail_merge_fn func).fn_blocks = NONE` by (
         irule lookup_block_NONE_tail_merge_fn >> simp[]) >>
       simp[result_equiv_def],
       ALL_TAC] >>
  rename1 `SOME bb`
  >> `lookup_block s.vs_current_bb (tail_merge_fn func).fn_blocks =
        SOME (subst_block_labels_block m bb)` by (
       irule lookup_block_tail_merge_fn >> metis_tac[])
  >> CONV_TAC (RAND_CONV (PURE_ONCE_REWRITE_CONV [run_blocks_unfold]))
  >> simp[]
  >> `bb_well_formed bb` by (metis_tac[wf_lookup_bb_well_formed])
  >> `eval_phis s (subst_block_labels_block m bb).bb_instructions =
        eval_phis s bb.bb_instructions` by (
       simp[subst_block_labels_block_def] >>
       irule eval_phis_subst_block_labels >>
       Cases_on `s.vs_prev_bb` >> gvs[])
  >> `phi_prefix_length (subst_block_labels_block m bb).bb_instructions =
        phi_prefix_length bb.bb_instructions` by
       simp[subst_block_labels_block_def, phi_prefix_length_subst_block_labels]
  >> PURE_REWRITE_TAC[run_block_def]
  >> gvs[]
  >> DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >> gvs[block_subst_rel_def, result_equiv_def]
  >> rename1 `eval_phis s bb.bb_instructions = OK s_phi`
  >> qabbrev_tac `s0 = s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`
  >> `s_phi = s with vs_vars := s_phi.vs_vars` by (
       irule venomExecProofsTheory.eval_phis_only_updates_vs_vars >>
       qexists_tac `bb.bb_instructions` >> simp[])
  >> `s_phi.vs_prev_bb = s.vs_prev_bb /\
      s_phi.vs_labels = s.vs_labels /\
      s_phi.vs_current_bb = s.vs_current_bb` by
       gvs[venom_state_component_equality]
  >> `block_subst_rel m (exec_block fuel ctx bb s0)
        (exec_block fuel ctx (subst_block_labels_block m bb) s0)` by (
       match_mp_tac (Q.SPECL [`LENGTH bb.bb_instructions - s0.vs_inst_idx`,
                               `fuel`, `ctx`, `bb`, `s0`, `m`]
                     run_block_subst_equiv) >>
       ASM_REWRITE_TAC[] >>
       gvs[Abbr`s0`, venomExecProofsTheory.phi_prefix_length_le])
  >> Cases_on `exec_block fuel ctx bb s0`
  >> gvs[block_subst_rel_def]
  >> TRY (simp[result_equiv_def] >> NO_TAC)
  >> TRY (simp[result_equiv_def] >> irule execution_equiv_UNIV_sym >> simp[] >> NO_TAC)
  >> (* OK case *)
     mp_tac (Q.SPECL [`fuel`, `func`, `ctx`, `s0`, `entry`,
       `m`, `bb`, `v`, `s''`] tail_merge_ok_case) >>
     ASM_REWRITE_TAC[] >>
     disch_then match_mp_tac >>
     simp[Abbr`s0`, venomExecProofsTheory.phi_prefix_length_le]
QED

Theorem block_sigs_FST_subset_fn_labels[local]:
  !func entry bbs l.
    MEM l (MAP FST (block_sigs func entry bbs)) ==>
    MEM l (MAP (\bb. bb.bb_label) bbs)
Proof
  Induct_on `bbs` >> simp[block_sigs_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.bb_label = entry` >> gvs[] >>
  Cases_on `reachable func h.bb_label` >> gvs[block_sigs_def] >>
  gvs[] >> metis_tac[]
QED

(* tail_merge_fn preserves fn_entry_label *)
Theorem tail_merge_fn_preserves_entry[local]:
  !func lbl.
    fn_entry_label func = SOME lbl ==>
    fn_entry_label (tail_merge_fn func) = SOME lbl
Proof
  rpt strip_tac >>
  simp[tail_merge_fn_def, LET_THM] >>
  Cases_on `compute_merge_map
    (block_sigs func lbl func.fn_blocks) []` THENL [simp[], ALL_TAC] >>
  simp[fn_entry_label_def, entry_block_def,
       subst_block_labels_fn_def, subst_block_labels_block_def, LET_THM] >>
  fs[fn_entry_label_def, entry_block_def] >>
  Cases_on `func.fn_blocks` THENL [gvs[], ALL_TAC] >>
  gvs[] >>
  Cases_on `h` >>
  (* Entry not in merge map — use EVERY *)
  `q <> h'.bb_label /\ ~MEM h'.bb_label (MAP FST t)` suffices_by (
    strip_tac >> simp[subst_block_labels_block_def]) >>
  (* q <> h'.bb_label *)
  conj_tac THENL [
    `MEM (q,r) (compute_merge_map (block_sigs func h'.bb_label (h'::t')) [])` suffices_by (
      strip_tac >> imp_res_tac compute_merge_map_not_entry >> gvs[]) >>
    simp[], ALL_TAC] >>
  (* ~MEM h'.bb_label (MAP FST t) *)
  simp[listTheory.MEM_MAP] >> rpt strip_tac >> Cases_on `y` >> gvs[] >>
  `MEM (h'.bb_label,r') (compute_merge_map (block_sigs func h'.bb_label (h'::t')) [])` suffices_by (
    strip_tac >> imp_res_tac compute_merge_map_not_entry >> gvs[]) >>
  simp[]
QED

Theorem tail_merge_fn_correct:
  !func s fuel ctx.
    wf_function func /\
    fn_entry_label func = SOME s.vs_current_bb /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    (* Simulation prerequisites for mergeable blocks *)
    (!bb. MEM bb func.fn_blocks /\ block_signature bb <> NONE ==>
      EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
      EVERY (\i. i.inst_opcode <> PARAM) bb.bb_instructions /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
      EVERY (\i. is_output_opcode i.inst_opcode \/ i.inst_outputs = [])
            bb.bb_instructions) /\
    (* Labels are not used as runtime values *)
    (!l. MEM l (fn_labels func) ==> FLOOKUP s.vs_labels l = NONE) ==>
    let func' = tail_merge_fn func in
    result_equiv UNIV
      (run_function fuel ctx func s)
      (run_function fuel ctx func' s)
Proof
  rpt strip_tac >>
  simp[LET_THM] >>
  (* Step 1: Unfold run_function on both sides *)
  simp[Once run_function_def] >>
  simp[Once run_function_def] >>
  (* Step 2: fn_entry_label of tail_merge_fn *)
  imp_res_tac tail_merge_fn_preserves_entry >>
  gvs[] >>
  (* Step 3: Connect to tail_merge_fn_correct_gen *)
  irule tail_merge_fn_correct_gen >>
  simp[] >>
  rpt conj_tac >>
  TRY (
    simp[listTheory.MEM_MAP] >>
    rpt strip_tac >> rename1 `MEM y _` >>
    Cases_on `y` >> gvs[] >>
    imp_res_tac compute_merge_map_not_entry >> gvs[] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    first_x_assum match_mp_tac >>
    simp[fn_labels_def] >>
    drule compute_merge_map_FST_subset >>
    simp[] >>
    metis_tac[block_sigs_FST_subset_fn_labels] >> NO_TAC) >>
  TRY (
    rpt strip_tac >>
    first_x_assum match_mp_tac >>
    simp[fn_labels_def] >>
    drule compute_merge_map_SND_subset >>
    simp[] >>
    metis_tac[block_sigs_FST_subset_fn_labels] >> NO_TAC)
QED
