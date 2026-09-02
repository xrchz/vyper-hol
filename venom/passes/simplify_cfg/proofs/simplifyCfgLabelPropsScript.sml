Theory simplifyCfgLabelProps
Ancestors
  simplifyCfgDefs cfgTransformProps unitLabelMap fcgBridge cfgWf
Libs
  listTheory

(* Unary result predicates avoid the paired-abstraction packaging of the
   generated mutual induction theorem.  Clients may destruct the result in
   their predicate, after the induction cases have been generated. *)
Definition collapse_dfs_result_def:
  collapse_dfs_result P func label_map visited lbl <=>
    P (collapse_dfs func label_map visited lbl)
End

Definition collapse_dfs_succs_result_def:
  collapse_dfs_succs_result P func label_map visited succs <=>
    P (collapse_dfs_succs func label_map visited succs)
End

Theorem collapse_ind_T[local]:
  (!func label_map visited lbl.
     collapse_dfs_result (\result. T) func label_map visited lbl) /\
  (!func label_map visited succs.
     collapse_dfs_succs_result (\result. T) func label_map visited succs)
Proof
  ho_match_mp_tac collapse_dfs_ind >>
  simp[collapse_dfs_result_def, collapse_dfs_succs_result_def]
QED

Theorem fn_labels_update_succ_phi_labels[local]:
  !old new bbs succs.
    MAP (\bb. bb.bb_label) (update_succ_phi_labels old new bbs succs) =
    MAP (\bb. bb.bb_label) bbs
Proof
  rpt gen_tac >> qid_spec_tac `bbs` >> Induct_on `succs` >>
  fs[update_succ_phi_labels_def] >>
  rpt gen_tac >> Cases_on `lookup_block h bbs` >> simp[] >>
  irule fn_labels_replace_block >> simp[] >>
  metis_tac[venomExecPropsTheory.lookup_block_label]
QED

Theorem chain_merge_event_labels:
  !func bb next_lbl next_bb label_map.
    lookup_block bb.bb_label func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    next_bb.bb_label = next_lbl /\
    can_merge_blocks func bb next_bb /\
    ALL_DISTINCT (fn_labels func) ==>
    let merged = merge_blocks bb next_bb in
    let bbs' = replace_block bb.bb_label merged
                 (remove_block next_lbl func.fn_blocks) in
    let bbs'' = update_succ_phi_labels next_lbl bb.bb_label bbs'
                  (bb_succs merged) in
    let func' = func with fn_blocks := bbs'' in
      MEM next_lbl (fn_labels func) /\
      MEM bb.bb_label (fn_labels func') /\
      ~MEM next_lbl (fn_labels func') /\
      next_lbl <> bb.bb_label /\
      ALL_DISTINCT (fn_labels func')
Proof
  rpt strip_tac >>
  drule can_merge_blocks_distinct >> strip_tac >>
  simp[venomInstTheory.fn_labels_def, fn_labels_update_succ_phi_labels, merge_blocks_def,
       fn_labels_replace_block, fn_labels_remove_block] >>
  gvs[venomExecPropsTheory.MEM_lookup_block, venomInstTheory.fn_labels_def, MEM_FILTER] >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  simp[MEM_MAP, FILTER_ALL_DISTINCT] >> metis_tac[]
QED

Theorem can_bypass_jump_target_distinct[local]:
  !func a b target.
    ALL_DISTINCT (fn_labels func) /\
    lookup_block a.bb_label func.fn_blocks = SOME a /\
    lookup_block b.bb_label func.fn_blocks = SOME b /\
    can_bypass_jump func a b /\
    bb_succs b = [target] ==>
    b.bb_label <> target
Proof
  rpt strip_tac >>
  fs[can_bypass_jump_def, cfgTransformTheory.num_preds_def,
     cfgTransformTheory.num_succs_def] >>
  `a <> b` by (strip_tac >> gvs[]) >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  qabbrev_tac `preds = FILTER (\bb. MEM b.bb_label (bb_succs bb)) func.fn_blocks` >>
  `MEM a preds` by simp[Abbr `preds`, MEM_FILTER] >>
  `MEM b preds` by simp[Abbr `preds`, MEM_FILTER] >>
  fs[cfgTransformTheory.block_preds_def] >>
  Cases_on `preds` >> gvs[] >> Cases_on `t` >> gvs[]
QED

Theorem do_merge_jump_event_labels:
  !func a b label_map func' label_map'.
    ALL_DISTINCT (fn_labels func) /\
    lookup_block a.bb_label func.fn_blocks = SOME a /\
    lookup_block b.bb_label func.fn_blocks = SOME b /\
    can_bypass_jump func a b /\
    do_merge_jump func a b label_map = SOME (func', label_map') ==>
    ?target.
      label_map' = (b.bb_label,target)::label_map /\
      MEM b.bb_label (fn_labels func) /\
      MEM target (fn_labels func') /\
      ~MEM b.bb_label (fn_labels func') /\
      b.bb_label <> target /\
      ALL_DISTINCT (fn_labels func')
Proof
  rpt strip_tac >>
  fs[do_merge_jump_def] >>
  Cases_on `bb_succs b` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1 `bb_succs b = [target]` >>
  Cases_on `lookup_block target func.fn_blocks` >> gvs[] >>
  `b.bb_label <> target` by
    metis_tac[can_bypass_jump_target_distinct] >>
  `x.bb_label = target` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  simp[venomInstTheory.fn_labels_def, fn_labels_replace_block, fn_labels_remove_block,
       MEM_FILTER] >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  simp[MEM_MAP, FILTER_ALL_DISTINCT] >>
  conj_tac >- (qexists `b` >> simp[]) >>
  conj_tac >- (qexists `x` >> simp[]) >>
  irule FILTER_ALL_DISTINCT >> gvs[venomInstTheory.fn_labels_def]
QED

(* A chronological event trace records the exact label-list evolution: each
   source is removed while its distinct target is still present. *)
Definition label_event_trace_def:
  (label_event_trace labels [] final_labels = (final_labels = labels)) /\
  (label_event_trace labels ((source,target)::rest) final_labels =
    (MEM source labels /\ MEM target labels /\ source <> target /\
     label_event_trace (FILTER (\l. l <> source) labels) rest final_labels))
End

Definition fn_result_events_def:
  fn_result_events initial_labels incoming func' label_map' <=>
    ?events.
      label_map' = REVERSE events ++ incoming /\
      label_event_trace initial_labels events (fn_labels func')
End

Definition collapse_result_events_def:
  collapse_result_events initial_labels incoming result <=>
    ?func' label_map' visited'.
      result = (func',label_map',visited') /\
      fn_result_events initial_labels incoming func' label_map'
End

Theorem label_event_trace_append:
  !initial first second final.
    label_event_trace initial (first ++ second) final <=>
    ?middle.
      label_event_trace initial first middle /\
      label_event_trace middle second final
Proof
  Induct_on `first` >> simp[label_event_trace_def] >>
  Cases_on `h` >> simp[label_event_trace_def] >> metis_tac[]
QED

Theorem chain_merge_event_trace[local]:
  !func bb next_lbl next_bb.
    lookup_block bb.bb_label func.fn_blocks = SOME bb /\
    lookup_block next_lbl func.fn_blocks = SOME next_bb /\
    next_bb.bb_label = next_lbl /\
    can_merge_blocks func bb next_bb /\
    ALL_DISTINCT (fn_labels func) ==>
    let merged = merge_blocks bb next_bb in
    let bbs' = replace_block bb.bb_label merged
                 (remove_block next_lbl func.fn_blocks) in
    let bbs'' = update_succ_phi_labels next_lbl bb.bb_label bbs'
                  (bb_succs merged) in
    let func' = func with fn_blocks := bbs'' in
      label_event_trace (fn_labels func) [(next_lbl,bb.bb_label)]
        (fn_labels func')
Proof
  rpt strip_tac >>
  drule can_merge_blocks_distinct >> strip_tac >>
  simp[label_event_trace_def, venomInstTheory.fn_labels_def,
       fn_labels_update_succ_phi_labels, merge_blocks_def,
       fn_labels_replace_block, fn_labels_remove_block, MEM_FILTER] >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem do_merge_jump_event_trace[local]:
  !func a b label_map func' label_map'.
    ALL_DISTINCT (fn_labels func) /\
    lookup_block a.bb_label func.fn_blocks = SOME a /\
    lookup_block b.bb_label func.fn_blocks = SOME b /\
    can_bypass_jump func a b /\
    do_merge_jump func a b label_map = SOME (func',label_map') ==>
    ?target.
      label_map' = (b.bb_label,target)::label_map /\
      label_event_trace (fn_labels func) [(b.bb_label,target)]
        (fn_labels func')
Proof
  rpt strip_tac >>
  fs[do_merge_jump_def] >>
  Cases_on `bb_succs b` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1 `bb_succs b = [target]` >>
  Cases_on `lookup_block target func.fn_blocks` >> gvs[] >>
  `b.bb_label <> target` by
    metis_tac[can_bypass_jump_target_distinct] >>
  `x.bb_label = target` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  simp[label_event_trace_def, venomInstTheory.fn_labels_def,
       fn_labels_replace_block, fn_labels_remove_block, MEM_FILTER] >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem fn_result_events_refl[local]:
  fn_result_events (fn_labels func) incoming func incoming
Proof
  simp[fn_result_events_def, label_event_trace_def]
QED

Theorem fn_result_events_compose[local]:
  fn_result_events initial incoming middle middle_map /\
  fn_result_events (fn_labels middle) middle_map final final_map ==>
  fn_result_events initial incoming final final_map
Proof
  simp[fn_result_events_def] >>
  rpt strip_tac >>
  qexists `events ++ events'` >>
  simp[REVERSE_APPEND, APPEND_ASSOC] >>
  metis_tac[label_event_trace_append]
QED

Theorem do_merge_jump_fn_result_events[local]:
  !func a b incoming func' outgoing.
    do_merge_jump func a b incoming = SOME (func',outgoing) ==>
    ALL_DISTINCT (fn_labels func) ==>
    lookup_block a.bb_label func.fn_blocks = SOME a ==>
    lookup_block b.bb_label func.fn_blocks = SOME b ==>
    can_bypass_jump func a b ==>
    fn_result_events (fn_labels func) incoming func' outgoing
Proof
  rpt strip_tac >>
  `?target.
      outgoing = (b.bb_label,target)::incoming /\
      label_event_trace (fn_labels func) [(b.bb_label,target)]
        (fn_labels func')` by
    metis_tac[do_merge_jump_event_trace] >>
  gvs[fn_result_events_def] >>
  qexists `[(b.bb_label,target)]` >> simp[]
QED

Theorem try_bypass_events[local]:
  !succs func incoming bb func' outgoing success.
    ALL_DISTINCT (fn_labels func) /\
    lookup_block bb.bb_label func.fn_blocks = SOME bb /\
    try_bypass func incoming bb succs = (func',outgoing,success) ==>
    fn_result_events (fn_labels func) incoming func' outgoing
Proof
  Induct_on `succs`
  >- simp[try_bypass_def, fn_result_events_refl] >>
  rpt strip_tac >>
  gvs[Once try_bypass_def, AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[]) >>
  `next_bb.bb_label = h` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  drule do_merge_jump_fn_result_events >>
  simp[]
QED

Theorem try_bypass_events_at[local]:
  try_bypass func incoming bb succs = (func',outgoing,success) ==>
  ALL_DISTINCT (fn_labels func) ==>
  lookup_block bb.bb_label func.fn_blocks = SOME bb ==>
  fn_result_events (fn_labels func) incoming func' outgoing
Proof
  metis_tac[try_bypass_events]
QED

Theorem label_event_trace_all_distinct[local]:
  !initial events final.
    ALL_DISTINCT initial /\ label_event_trace initial events final ==>
    ALL_DISTINCT final
Proof
  Induct_on `events` >> simp[label_event_trace_def] >>
  Cases_on `h` >> simp[label_event_trace_def] >>
  metis_tac[FILTER_ALL_DISTINCT]
QED

Theorem fn_result_events_all_distinct[local]:
  ALL_DISTINCT initial /\ fn_result_events initial incoming func' outgoing ==>
  ALL_DISTINCT (fn_labels func')
Proof
  simp[fn_result_events_def] >>
  metis_tac[label_event_trace_all_distinct]
QED

Theorem collapse_result_events_compose[local]:
  fn_result_events initial incoming middle middle_map /\
  collapse_result_events (fn_labels middle) middle_map result ==>
  collapse_result_events initial incoming result
Proof
  Cases_on `result` >> PairCases_on `r` >>
  simp[collapse_result_events_def] >>
  metis_tac[fn_result_events_compose]
QED
Theorem collapse_dfs_result_events_compose[local]:
  fn_result_events initial incoming middle middle_map ==>
  collapse_dfs_result
    (collapse_result_events (fn_labels middle) middle_map)
    middle middle_map visited lbl ==>
  collapse_result_events initial incoming
    (collapse_dfs middle middle_map visited lbl)
Proof
  simp[collapse_dfs_result_def] >>
  metis_tac[collapse_result_events_compose]
QED

Theorem collapse_dfs_succs_result_events_compose[local]:
  fn_result_events initial incoming middle middle_map ==>
  collapse_dfs_succs_result
    (collapse_result_events (fn_labels middle) middle_map)
    middle middle_map visited succs ==>
  collapse_result_events initial incoming
    (collapse_dfs_succs middle middle_map visited succs)
Proof
  simp[collapse_dfs_succs_result_def] >>
  metis_tac[collapse_result_events_compose]
QED


Theorem chain_merge_fn_result_events[local]:
  lookup_block lbl func.fn_blocks = SOME bb ==>
  bb.bb_label = lbl ==>
  lookup_block next_lbl func.fn_blocks = SOME next_bb ==>
  next_bb.bb_label = next_lbl ==>
  can_merge_blocks func bb next_bb ==>
  ALL_DISTINCT (fn_labels func) ==>
  let merged = merge_blocks bb next_bb in
  let bbs' = replace_block lbl merged
               (remove_block next_lbl func.fn_blocks) in
  let bbs'' = update_succ_phi_labels next_lbl lbl bbs'
                (bb_succs merged) in
  let func' = func with fn_blocks := bbs'' in
    fn_result_events (fn_labels func) incoming func'
      ((next_lbl,lbl)::incoming)
Proof
  rpt strip_tac >> gvs[] >>
  drule can_merge_blocks_distinct >> strip_tac >>
  simp[fn_result_events_def] >>
  qexists `[(next_bb.bb_label,bb.bb_label)]` >>
  simp[label_event_trace_def, venomInstTheory.fn_labels_def,
       fn_labels_update_succ_phi_labels, merge_blocks_def,
       fn_labels_replace_block, fn_labels_remove_block, MEM_FILTER] >>
  imp_res_tac venomExecPropsTheory.lookup_block_MEM >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem collapse_result_events_pair[local]:
  collapse_result_events initial incoming (func',outgoing,visited') <=>
  fn_result_events initial incoming func' outgoing
Proof
  simp[collapse_result_events_def]
QED

Theorem collapse_events_joint[local]:
  (!func incoming visited lbl.
     ALL_DISTINCT (fn_labels func) ==>
     collapse_dfs_result
       (collapse_result_events (fn_labels func) incoming)
       func incoming visited lbl) /\
  (!func incoming visited succs.
     ALL_DISTINCT (fn_labels func) ==>
     collapse_dfs_succs_result
       (collapse_result_events (fn_labels func) incoming)
       func incoming visited succs)
Proof
  ho_match_mp_tac collapse_dfs_ind >>
  rpt conj_tac
  >- suspend "dfs"
  >- suspend "nil"
  >> suspend "succs"
QED

Resume collapse_events_joint[dfs]:
  rpt strip_tac >>
  simp[NoAsms, collapse_dfs_result_def, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl func.fn_blocks`
  >- simp[collapse_result_events_pair, fn_result_events_refl] >>
  rename1 `lookup_block lbl func.fn_blocks = SOME bb` >>
  Cases_on `bb_succs bb`
  >- (Cases_on `MEM lbl visited`
      >- simp[try_bypass_def, collapse_result_events_pair,
              fn_result_events_refl]
      >> gvs[try_bypass_def, collapse_dfs_succs_result_def]) >>
  Cases_on `t`
  >- (Cases_on `lookup_block h func.fn_blocks`
      >- (Cases_on `MEM lbl visited` >>
          simp[collapse_result_events_pair, fn_result_events_refl])
      >> rename1 `lookup_block h func.fn_blocks = SOME next_bb`
      >> Cases_on `can_merge_blocks func bb next_bb`
      >- (gvs[] >>
          `bb.bb_label = lbl` by
            metis_tac[venomExecPropsTheory.lookup_block_label] >>
          `next_bb.bb_label = h` by
            metis_tac[venomExecPropsTheory.lookup_block_label] >>
          qmatch_goalsub_abbrev_tac
            `collapse_dfs merged_func merged_incoming visited lbl` >>
          irule collapse_result_events_compose >>
          qexistsl [`merged_func`,`merged_incoming`] >>
          reverse conj_asm2_tac
          >- (simp[Abbr `merged_func`, Abbr `merged_incoming`] >>
              drule_all chain_merge_fn_result_events >> simp[]) >>
          imp_res_tac fn_result_events_all_distinct >>
          first_x_assum drule >>
          simp[collapse_dfs_result_def])
      >> Cases_on `MEM lbl visited`
      >- simp[collapse_result_events_pair, fn_result_events_refl]
      >> gvs[collapse_dfs_result_def])
  >> Cases_on `try_bypass func incoming bb (h::h'::t')`
  >> PairCases_on `r`
  >> Cases_on `r1`
  >- (gvs[] >>
      `bb.bb_label = lbl` by
        metis_tac[venomExecPropsTheory.lookup_block_label] >>
      `lookup_block bb.bb_label func.fn_blocks = SOME bb` by gvs[] >>
      `fn_result_events (fn_labels func) incoming q r0` by
        (drule_all try_bypass_events_at >> simp[]) >>
      `ALL_DISTINCT (fn_labels q)` by
        metis_tac[fn_result_events_all_distinct] >>
      metis_tac[collapse_dfs_result_events_compose])
  >> gvs[] >>
  `bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `lookup_block bb.bb_label func.fn_blocks = SOME bb` by gvs[] >>
  `fn_result_events (fn_labels func) incoming q r0` by
    (drule_all try_bypass_events_at >> simp[]) >>
  `ALL_DISTINCT (fn_labels q)` by
    metis_tac[fn_result_events_all_distinct] >>
  Cases_on `MEM lbl visited`
  >- simp[collapse_result_events_pair] >>
  metis_tac[collapse_dfs_succs_result_events_compose]
QED

Resume collapse_events_joint[nil]:
  simp[collapse_dfs_succs_result_def, collapse_dfs_def,
       collapse_result_events_pair, fn_result_events_refl]
QED

Resume collapse_events_joint[succs]:
  rpt strip_tac >>
  simp[collapse_dfs_succs_result_def, Once collapse_dfs_def] >>
  Cases_on `collapse_dfs func incoming visited lbl` >>
  PairCases_on `r` >> gvs[collapse_dfs_result_def] >>
  `fn_result_events (fn_labels func) incoming q r0` by
    gvs[collapse_result_events_pair] >>
  `ALL_DISTINCT (fn_labels q)` by
    metis_tac[fn_result_events_all_distinct] >>
  metis_tac[collapse_dfs_succs_result_events_compose]
QED

Finalise collapse_events_joint

Theorem simplify_cfg_round_with_labels_event_trace[local]:
  ALL_DISTINCT
    (fn_labels (fix_all_phis (remove_unreachable_blocks func))) ==>
  case fn_entry_label func of
    NONE => SND (simplify_cfg_round_with_labels func) = []
  | SOME entry =>
      ?collapsed visited.
        collapse_dfs (fix_all_phis (remove_unreachable_blocks func)) [] [] entry =
          (collapsed,
           REVERSE (SND (simplify_cfg_round_with_labels func)),
           visited) /\
        label_event_trace
          (fn_labels (fix_all_phis (remove_unreachable_blocks func)))
          (SND (simplify_cfg_round_with_labels func))
          (fn_labels collapsed)
Proof
  strip_tac >> Cases_on `fn_entry_label func`
  >- simp[simplify_cfg_round_with_labels_def] >>
  rename1 `fn_entry_label func = SOME entry` >>
  Cases_on
    `collapse_dfs (fix_all_phis (remove_unreachable_blocks func)) [] [] entry` >>
  PairCases_on `r` >>
  simp[simplify_cfg_round_with_labels_def] >>
  `collapse_result_events
     (fn_labels (fix_all_phis (remove_unreachable_blocks func))) []
     (q,r0,r1)` by
    (metis_tac[collapse_dfs_result_def,
               CONJUNCT1 collapse_events_joint]) >>
  gvs[collapse_result_events_pair, fn_result_events_def]
QED

Definition chronological_label_map_def:
  chronological_label_map [] = T /\
  chronological_label_map ((source,target)::rest) =
    (source <> target /\
     ~MEM source (MAP FST rest) /\
     ~MEM source (MAP SND rest) /\
     chronological_label_map rest)
End

Theorem label_event_trace_endpoints:
  !initial events final.
    label_event_trace initial events final ==>
    EVERY (\entry.
      MEM (FST entry) initial /\ MEM (SND entry) initial) events
Proof
  Induct_on `events` >> simp[label_event_trace_def] >>
  Cases_on `h` >> simp[label_event_trace_def] >>
  rpt strip_tac >>
  first_x_assum drule >>
  simp[listTheory.EVERY_MEM, MEM_FILTER] >>
  metis_tac[]
QED

Theorem label_event_trace_chronological:
  !initial events final.
    label_event_trace initial events final ==>
    chronological_label_map events
Proof
  Induct_on `events` >> simp[label_event_trace_def,
                              chronological_label_map_def] >>
  Cases_on `h` >> simp[label_event_trace_def,
                       chronological_label_map_def] >>
  rpt strip_tac >>
  `EVERY (\entry.
      MEM (FST entry) (FILTER (\l. l <> q) initial) /\
      MEM (SND entry) (FILTER (\l. l <> q) initial)) events` by
    metis_tac[label_event_trace_endpoints] >>
  gvs[listTheory.EVERY_MEM, MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem chronological_label_map_all_distinct_sources:
  !events.
    chronological_label_map events ==>
    ALL_DISTINCT (MAP FST events)
Proof
  Induct_on `events` >> simp[chronological_label_map_def] >>
  Cases_on `h` >> simp[chronological_label_map_def]
QED

Definition label_map_transition_def:
  label_map_transition initial label_map final <=>
    chronological_label_map label_map /\
    EVERY (\entry.
      MEM (FST entry) initial /\ MEM (SND entry) initial) label_map /\
    EVERY (\entry. ~MEM (FST entry) final) label_map /\
    EVERY (\label. MEM label initial) final /\
    ALL_DISTINCT final
End

Theorem label_map_transition_refl:
  ALL_DISTINCT labels ==>
  label_map_transition labels [] labels
Proof
  simp[label_map_transition_def, chronological_label_map_def,
       listTheory.EVERY_MEM]
QED

Theorem chronological_label_map_append[local]:
  !first middle second.
    chronological_label_map first /\
    EVERY (\entry. ~MEM (FST entry) middle) first /\
    EVERY (\entry.
      MEM (FST entry) middle /\ MEM (SND entry) middle) second /\
    chronological_label_map second ==>
    chronological_label_map (first ++ second)
Proof
  Induct_on `first`
  >- simp[] >>
  Cases_on `h` >>
  simp[chronological_label_map_def] >>
  rpt strip_tac >>
  gvs[listTheory.EVERY_MEM, MEM_MAP] >>
  metis_tac[]
QED

Theorem label_map_transition_append:
  !initial first middle second final.
    label_map_transition initial first middle /\
    label_map_transition middle second final ==>
    label_map_transition initial (first ++ second) final
Proof
  rpt strip_tac >>
  fs[label_map_transition_def] >>
  simp[label_map_transition_def, listTheory.EVERY_APPEND] >>
  rpt conj_tac
  >- metis_tac[chronological_label_map_append]
  >- (gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >- (gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >- (gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >> gvs[]
QED

Theorem bb_label_fix_phis_in_block[local]:
  (fix_phis_in_block actual_preds bb).bb_label = bb.bb_label
Proof
  simp[fix_phis_in_block_def] >>
  pairarg_tac >> simp[]
QED

Theorem fn_labels_fix_all_phis[local]:
  fn_labels (fix_all_phis func) = fn_labels func
Proof
  simp[fix_all_phis_def, venomInstTheory.fn_labels_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF,
       bb_label_fix_phis_in_block]
QED

Theorem bb_label_subst_block_labels_block[local]:
  (subst_block_labels_block label_map bb).bb_label = bb.bb_label
Proof
  simp[cfgTransformTheory.subst_block_labels_block_def]
QED

Theorem fn_labels_subst_block_labels_fn[local]:
  fn_labels (subst_block_labels_fn label_map func) = fn_labels func
Proof
  simp[cfgTransformTheory.subst_block_labels_fn_def,
       venomInstTheory.fn_labels_def, listTheory.MAP_MAP_o,
       combinTheory.o_DEF, bb_label_subst_block_labels_block]
QED

Theorem fn_labels_remove_unreachable_subset[local]:
  EVERY (\label. MEM label (fn_labels func))
    (fn_labels (remove_unreachable_blocks func))
Proof
  Cases_on `fn_entry_label func` >>
  simp[remove_unreachable_blocks_def, venomInstTheory.fn_labels_def,
       listTheory.EVERY_MEM, MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem fn_labels_filter_blocks[local]:
  MAP (\bb. bb.bb_label) (FILTER (\bb. pred bb.bb_label) blocks) =
  FILTER pred (MAP (\bb. bb.bb_label) blocks)
Proof
  Induct_on `blocks` >> simp[] >>
  gen_tac >> Cases_on `pred h.bb_label` >> simp[]
QED

Theorem fn_labels_remove_unreachable_all_distinct[local]:
  ALL_DISTINCT (fn_labels func) ==>
  ALL_DISTINCT (fn_labels (remove_unreachable_blocks func))
Proof
  Cases_on `fn_entry_label func` >>
  simp[remove_unreachable_blocks_def, venomInstTheory.fn_labels_def,
       fn_labels_filter_blocks, FILTER_ALL_DISTINCT]
QED
Theorem label_event_trace_final_subset[local]:
  !initial events final.
    label_event_trace initial events final ==>
    EVERY (\label. MEM label initial) final
Proof
  Induct_on `events`
  >- simp[label_event_trace_def, listTheory.EVERY_MEM] >>
  Cases_on `h` >>
  simp[label_event_trace_def] >>
  rpt strip_tac >>
  first_x_assum drule >>
  gvs[listTheory.EVERY_MEM, MEM_FILTER] >>
  metis_tac[]
QED

Theorem label_event_trace_sources_absent[local]:
  !initial events final.
    label_event_trace initial events final ==>
    EVERY (\entry. ~MEM (FST entry) final) events
Proof
  Induct_on `events`
  >- simp[label_event_trace_def] >>
  Cases_on `h` >>
  simp[label_event_trace_def] >>
  rpt strip_tac >>
  `EVERY (\label. MEM label (FILTER (\l. l <> q) initial)) final` by
    metis_tac[label_event_trace_final_subset] >>
  first_x_assum drule >>
  gvs[listTheory.EVERY_MEM, MEM_FILTER] >>
  metis_tac[]
QED

Theorem label_event_trace_transition[local]:
  ALL_DISTINCT initial /\ label_event_trace initial events final ==>
  label_map_transition initial events final
Proof
  rpt strip_tac >>
  simp[label_map_transition_def] >>
  metis_tac[label_event_trace_chronological,
            label_event_trace_endpoints,
            label_event_trace_sources_absent,
            label_event_trace_final_subset,
            label_event_trace_all_distinct]
QED

Theorem label_map_transition_widen_restrict[local]:
  label_map_transition inner label_map middle /\
  EVERY (\label. MEM label outer) inner /\
  EVERY (\label. MEM label middle) final /\
  ALL_DISTINCT final ==>
  label_map_transition outer label_map final
Proof
  rpt strip_tac >>
  fs[label_map_transition_def] >>
  simp[label_map_transition_def] >>
  rpt conj_tac
  >- (gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >- (gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >- (gvs[listTheory.EVERY_MEM] >> metis_tac[])
  >> gvs[]
QED

Theorem collapse_postprocess_transition[local]:
  ALL_DISTINCT initial /\
  EVERY (\label. MEM label outer) initial /\
  label_event_trace initial events (fn_labels collapsed) ==>
  label_map_transition outer events
    (fn_labels (fix_all_phis (remove_unreachable_blocks
      (if raw_map = [] then collapsed
       else subst_block_labels_fn raw_map collapsed))))
Proof
  rpt strip_tac >>
  `label_map_transition initial events (fn_labels collapsed)` by
    metis_tac[label_event_trace_transition] >>
  `fn_labels (if raw_map = [] then collapsed
              else subst_block_labels_fn raw_map collapsed) =
   fn_labels collapsed` by
    (Cases_on `raw_map = []` >> simp[fn_labels_subst_block_labels_fn]) >>
  `ALL_DISTINCT (fn_labels collapsed)` by
    metis_tac[label_event_trace_all_distinct] >>
  `ALL_DISTINCT (fn_labels (remove_unreachable_blocks
      (if raw_map = [] then collapsed
       else subst_block_labels_fn raw_map collapsed)))` by
    metis_tac[fn_labels_remove_unreachable_all_distinct] >>
  simp[fn_labels_fix_all_phis] >>
  irule label_map_transition_widen_restrict >>
  conj_tac >- gvs[] >>
  qexists `initial` >>
  qexists `fn_labels collapsed` >>
  qpat_assum
    `fn_labels (if raw_map = [] then collapsed
                else subst_block_labels_fn raw_map collapsed) =
     fn_labels collapsed`
    (fn th => rewrite_tac[GSYM th]) >>
  simp[fn_labels_remove_unreachable_subset]
QED


Theorem simplify_cfg_round_with_labels_transition:
  ALL_DISTINCT (fn_labels func) ==>
  label_map_transition (fn_labels func)
    (SND (simplify_cfg_round_with_labels func))
    (fn_labels (FST (simplify_cfg_round_with_labels func)))
Proof
  strip_tac >> Cases_on `fn_entry_label func`
  >- simp[simplify_cfg_round_with_labels_def, label_map_transition_refl] >>
  rename1 `fn_entry_label func = SOME entry` >>
  `ALL_DISTINCT
     (fn_labels (fix_all_phis (remove_unreachable_blocks func)))` by
    metis_tac[fn_labels_fix_all_phis,
              fn_labels_remove_unreachable_all_distinct] >>
  `EVERY (\label. MEM label (fn_labels func))
     (fn_labels (fix_all_phis (remove_unreachable_blocks func)))` by
    simp[fn_labels_fix_all_phis, fn_labels_remove_unreachable_subset] >>
  Cases_on
    `collapse_dfs (fix_all_phis (remove_unreachable_blocks func)) [] [] entry` >>
  PairCases_on `r` >>
  drule simplify_cfg_round_with_labels_event_trace >>
  simp[] >>
  strip_tac >>
  `simplify_cfg_round_with_labels func =
   (fix_all_phis (remove_unreachable_blocks
      (if r0 = [] then q else subst_block_labels_fn r0 q)),
    REVERSE r0)` by
    (pure_once_rewrite_tac[simplify_cfg_round_with_labels_def] >>
     qpat_assum `fn_entry_label func = SOME entry`
       (fn th => rewrite_tac[th]) >>
     qpat_assum
       `collapse_dfs (fix_all_phis (remove_unreachable_blocks func)) [] [] entry =
        (q,r0,r1)`
       (fn th => rewrite_tac[th]) >>
     simp[]) >>
  `label_event_trace
     (fn_labels (fix_all_phis (remove_unreachable_blocks func)))
     (REVERSE r0) (fn_labels q)` by
    (qpat_x_assum
       `label_event_trace _ (SND (simplify_cfg_round_with_labels func)) _`
       mp_tac >>
     qpat_assum `simplify_cfg_round_with_labels func = _`
       (fn th => rewrite_tac[th]) >>
     simp[]) >>
  qpat_assum `simplify_cfg_round_with_labels func = _`
    (fn th => rewrite_tac[th]) >>
  irule collapse_postprocess_transition >>
  qexists `fn_labels (fix_all_phis (remove_unreachable_blocks func))` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem simplify_cfg_iter_with_labels_transition:
  !n func. ALL_DISTINCT (fn_labels func) ==>
    label_map_transition (fn_labels func)
      (SND (simplify_cfg_iter_with_labels n func))
      (fn_labels (FST (simplify_cfg_iter_with_labels n func)))
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def, label_map_transition_refl] >>
  rpt strip_tac >>
  Cases_on `simplify_cfg_round_with_labels func` >>
  rename1 `simplify_cfg_round_with_labels func = (func',round_map)` >>
  `label_map_transition (fn_labels func)
     (SND (simplify_cfg_round_with_labels func))
     (fn_labels (FST (simplify_cfg_round_with_labels func)))` by
    metis_tac[simplify_cfg_round_with_labels_transition] >>
  `label_map_transition (fn_labels func) round_map (fn_labels func')` by
    (qpat_x_assum `label_map_transition _ (SND _) _` mp_tac >>
     qpat_assum `simplify_cfg_round_with_labels func = (func',round_map)`
       (fn th => rewrite_tac[th]) >>
     simp[]) >>
  `ALL_DISTINCT (fn_labels func')` by
    gvs[label_map_transition_def] >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >>
  qpat_assum `simplify_cfg_round_with_labels func = (func',round_map)`
    (fn th => rewrite_tac[th]) >>
  simp[] >>
  IF_CASES_TAC
  >- (simp[] >>
      `fn_labels func' = fn_labels func` by
        gvs[venomInstTheory.fn_labels_def] >>
      gvs[]) >>
  Cases_on `simplify_cfg_iter_with_labels n func'` >>
  rename1 `simplify_cfg_iter_with_labels n func' = (result,later_map)` >>
  `label_map_transition (fn_labels func')
     (SND (simplify_cfg_iter_with_labels n func'))
     (fn_labels (FST (simplify_cfg_iter_with_labels n func')))` by
    metis_tac[] >>
  `label_map_transition (fn_labels func') later_map (fn_labels result)` by
    (qpat_x_assum `label_map_transition _ (SND _) _` mp_tac >>
     qpat_assum `simplify_cfg_iter_with_labels n func' = (result,later_map)`
       (fn th => rewrite_tac[th]) >>
     simp[]) >>
  simp[] >>
  irule label_map_transition_append >>
  qexists `fn_labels func'` >>
  simp[]
QED

Theorem simplify_cfg_fn_with_labels_transition:
  ALL_DISTINCT (fn_labels func) ==>
  label_map_transition (fn_labels func)
    (SND (simplify_cfg_fn_with_labels func))
    (fn_labels (FST (simplify_cfg_fn_with_labels func)))
Proof
  simp[simplify_cfg_fn_with_labels_def,
       simplify_cfg_iter_with_labels_transition]
QED

Theorem resolve_label_fuel_cons_irrelevant[local]:
  !fuel rest source target visited label.
    label <> source /\ ~MEM source (MAP SND rest) ==>
    resolve_label_fuel ((source,target)::rest) visited fuel label =
    resolve_label_fuel rest visited fuel label
Proof
  Induct_on `fuel`
  >- simp[resolve_label_fuel_def, alistTheory.ALOOKUP_def] >>
  rpt strip_tac >>
  simp[resolve_label_fuel_def, alistTheory.ALOOKUP_def] >>
  Cases_on `MEM label visited` >> simp[] >>
  Cases_on `ALOOKUP rest label` >> simp[] >>
  first_x_assum irule >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  qpat_x_assum `~MEM source (MAP SND rest)` mp_tac >>
  simp[MEM_MAP] >> strip_tac >>
  first_x_assum (qspec_then `(label,x)` mp_tac) >> simp[]
QED

Definition visited_avoids_label_map_def:
  visited_avoids_label_map visited label label_map <=>
    ~MEM label visited /\
    EVERY (\seen.
      ~MEM seen (MAP FST label_map) /\
      ~MEM seen (MAP SND label_map)) visited
End

Theorem resolve_label_fuel_chronological[local]:
  !label_map fuel visited label.
    chronological_label_map label_map /\
    LENGTH label_map < fuel /\
    visited_avoids_label_map visited label label_map ==>
    ?terminal.
      resolve_label_fuel label_map visited fuel label = SOME terminal
Proof
  Induct_on `label_map`
  >- (Cases_on `fuel` >>
      simp[resolve_label_fuel_def, visited_avoids_label_map_def]) >>
  Cases_on `h` >> rpt strip_tac >>
  Cases_on `fuel` >> gvs[] >>
  fs[chronological_label_map_def, visited_avoids_label_map_def] >>
  Cases_on `label = q`
  >- (gvs[] >>
      simp[resolve_label_fuel_def, alistTheory.ALOOKUP_def] >>
      simp[resolve_label_fuel_cons_irrelevant] >>
      first_x_assum irule >>
      simp[visited_avoids_label_map_def] >>
      gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[resolve_label_fuel_cons_irrelevant] >>
  first_x_assum irule >>
  simp[visited_avoids_label_map_def] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem resolve_label_entries_chronological[local]:
  chronological_label_map label_map /\ LENGTH label_map < fuel ==>
  !entries.
    ?resolved.
      resolve_label_entries label_map fuel entries = SOME resolved
Proof
  strip_tac >> Induct
  >- simp[resolve_label_entries_def] >>
  Cases_on `h` >>
  `?terminal.
      resolve_label_fuel label_map [] fuel q = SOME terminal` by
    (irule resolve_label_fuel_chronological >>
     simp[visited_avoids_label_map_def]) >>
  gvs[resolve_label_entries_def]
QED

Theorem chronological_label_map_resolves:
  chronological_label_map label_map ==>
  ?resolved. resolve_label_map label_map = SOME resolved
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST label_map)` by
    metis_tac[chronological_label_map_all_distinct_sources] >>
  `?resolved.
      resolve_label_entries label_map (SUC (LENGTH label_map)) label_map =
        SOME resolved` by
    (irule resolve_label_entries_chronological >> simp[]) >>
  gvs[resolve_label_map_def]
QED

Theorem resolve_label_fuel_endpoint[local]:
  !fuel label visited terminal.
    EVERY (\entry.
      MEM (FST entry) namespace /\ MEM (SND entry) namespace) label_map /\
    MEM label namespace /\
    resolve_label_fuel label_map visited fuel label = SOME terminal ==>
    MEM terminal namespace
Proof
  Induct_on `fuel`
  >- (rpt strip_tac >>
      gvs[resolve_label_fuel_def, AllCaseEqs()]) >>
  rpt strip_tac >>
  gvs[resolve_label_fuel_def, AllCaseEqs()] >>
  drule alistTheory.ALOOKUP_MEM >> strip_tac >>
  gvs[listTheory.EVERY_MEM] >>
  first_x_assum drule >> simp[] >>
  metis_tac[]
QED

Theorem resolve_label_entries_chronological_endpoints[local]:
  chronological_label_map label_map /\
  LENGTH label_map < fuel /\
  EVERY (\entry.
    MEM (FST entry) namespace /\ MEM (SND entry) namespace) label_map /\
  EVERY (\entry. MEM (FST entry) namespace) entries ==>
  ?resolved.
    resolve_label_entries label_map fuel entries = SOME resolved /\
    EVERY (\entry. MEM (SND entry) namespace) resolved
Proof
  Induct_on `entries`
  >- simp[resolve_label_entries_def] >>
  Cases_on `h` >> rpt strip_tac >>
  gvs[] >>
  `?terminal.
      resolve_label_fuel label_map [] fuel q = SOME terminal` by
    (irule resolve_label_fuel_chronological >>
     simp[visited_avoids_label_map_def]) >>
  `MEM terminal namespace` by
    metis_tac[resolve_label_fuel_endpoint] >>
  qexists `(q,terminal)::resolved` >>
  simp[resolve_label_entries_def]
QED

Theorem chronological_label_map_resolves_endpoints:
  chronological_label_map label_map /\
  EVERY (\entry.
    MEM (FST entry) namespace /\ MEM (SND entry) namespace) label_map ==>
  ?resolved.
    resolve_label_map label_map = SOME resolved /\
    EVERY (\entry. MEM (SND entry) namespace) resolved
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP FST label_map)` by
    metis_tac[chronological_label_map_all_distinct_sources] >>
  `?resolved.
      resolve_label_entries label_map (SUC (LENGTH label_map)) label_map =
        SOME resolved /\
      EVERY (\entry. MEM (SND entry) namespace) resolved` by
    (irule resolve_label_entries_chronological_endpoints >>
     simp[] >> gvs[listTheory.EVERY_MEM]) >>
  qexists `resolved` >>
  simp[resolve_label_map_def]
QED


Theorem simplify_cfg_fn_with_labels_resolves:
  ALL_DISTINCT (fn_labels func) /\
  EVERY (\label. MEM label (unit_label_namespace unit)) (fn_labels func) ==>
  ?resolved.
    resolve_label_map (SND (simplify_cfg_fn_with_labels func)) = SOME resolved /\
    resolved_label_endpoints_valid unit resolved
Proof
  rpt strip_tac >>
  `label_map_transition (fn_labels func)
     (SND (simplify_cfg_fn_with_labels func))
     (fn_labels (FST (simplify_cfg_fn_with_labels func)))` by
    metis_tac[simplify_cfg_fn_with_labels_transition] >>
  fs[label_map_transition_def] >>
  `EVERY (\entry.
     MEM (FST entry) (unit_label_namespace unit) /\
     MEM (SND entry) (unit_label_namespace unit))
     (SND (simplify_cfg_fn_with_labels func))` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `?resolved.
     resolve_label_map (SND (simplify_cfg_fn_with_labels func)) = SOME resolved /\
     EVERY (\entry. MEM (SND entry) (unit_label_namespace unit)) resolved` by
    metis_tac[chronological_label_map_resolves_endpoints] >>
  qexists `resolved` >>
  simp[resolved_label_endpoints_valid_def]
QED

Theorem simplify_cfg_fn_with_labels_apply_unit_label_map:
  ALL_DISTINCT (fn_labels func) /\
  EVERY (\label. MEM label (unit_label_namespace unit)) (fn_labels func) ==>
  ?unit'. apply_unit_label_map
    (SND (simplify_cfg_fn_with_labels func)) unit = SOME unit'
Proof
  rpt strip_tac >>
  `?resolved.
     resolve_label_map (SND (simplify_cfg_fn_with_labels func)) = SOME resolved /\
     resolved_label_endpoints_valid unit resolved` by
    metis_tac[simplify_cfg_fn_with_labels_resolves] >>
  qexists `apply_resolved_unit_label_map resolved unit` >>
  simp[apply_unit_label_map_def]
QED


(* Extensional function-call edge view used by SimplifyCFG consumers. *)
Definition simplify_cfg_fn_invoke_labels_def:
  simplify_cfg_fn_invoke_labels func = MAP FST (fcg_scan_function func)
End

Definition simplify_cfg_block_invoke_labels_def:
  simplify_cfg_block_invoke_labels bb =
    MAP FST (get_invoke_targets bb.bb_instructions)
End

Theorem simplify_cfg_invoke_labels_append[local]:
  !first second.
    MAP FST (get_invoke_targets (first ++ second)) =
    MAP FST (get_invoke_targets first) ++
    MAP FST (get_invoke_targets second)
Proof
  Induct_on `first` >>
  simp[fcgDefsTheory.get_invoke_targets_def] >>
  rpt gen_tac >> rpt CASE_TAC >> gvs[]
QED

Theorem fn_insts_blocks_mem[local]:
  !blocks inst.
    MEM inst (fn_insts_blocks blocks) <=>
    ?bb. MEM bb blocks /\ MEM inst bb.bb_instructions
Proof
  Induct_on `blocks` >>
  simp[venomInstTheory.fn_insts_blocks_def] >> metis_tac[]
QED

Theorem simplify_cfg_fn_invoke_labels_mem:
  MEM callee (simplify_cfg_fn_invoke_labels func) <=>
  ?bb inst operands.
    MEM bb func.fn_blocks /\
    MEM inst bb.bb_instructions /\
    inst.inst_opcode = INVOKE /\
    inst.inst_operands = Label callee :: operands
Proof
  simp[simplify_cfg_fn_invoke_labels_def, fcgDefsTheory.fcg_scan_function_def,
       venomInstTheory.fn_insts_def, fcgBridgeTheory.mem_get_invoke_targets,
       fn_insts_blocks_mem] >>
  metis_tac[]
QED
Theorem fn_blocks_update_metadata[local]:
  fn_identity_metadata_eq (func with fn_blocks := blocks) func /\
  fn_static_input_eq (func with fn_blocks := blocks) func /\
  fn_static_layout_eq (func with fn_blocks := blocks) func /\
  fn_fmp_convention_eq (func with fn_blocks := blocks) func
Proof
  simp[venomInstTheory.fn_identity_metadata_eq_def,
       venomInstTheory.fn_static_input_eq_def,
       venomInstTheory.fn_static_layout_eq_def,
       venomInstTheory.fn_fmp_convention_eq_def]
QED


Theorem fix_phi_inst_invoke_shape[local]:
  (fix_phi_inst preds inst).inst_opcode = INVOKE /\
  (fix_phi_inst preds inst).inst_operands = Label callee :: operands <=>
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: operands
Proof
  simp[fix_phi_inst_def] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (gvs[] >> Cases_on `filter_phi_ops preds inst.inst_operands` >> gvs[] >>
      Cases_on `t` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  gvs[]
QED

Theorem subst_block_labels_inst_invoke_shape[local]:
  (subst_block_labels_inst label_map inst).inst_opcode = INVOKE /\
  (subst_block_labels_inst label_map inst).inst_operands =
    Label callee :: operands <=>
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: operands
Proof
  Cases_on `inst.inst_opcode` >>
  simp[cfgTransformTheory.subst_block_labels_inst_def,
       cfgTransformTheory.subst_label_map_inst_def,
       venomInstTheory.is_block_label_opcode_def,
       venomInstTheory.is_terminator_def]
QED

Theorem invoke_labels_map_fix_phi[local]:
  MEM callee
    (MAP FST (get_invoke_targets (MAP (fix_phi_inst preds) insts))) <=>
  MEM callee (MAP FST (get_invoke_targets insts))
Proof
  simp[fcgBridgeTheory.mem_get_invoke_targets, MEM_MAP] >>
  metis_tac[fix_phi_inst_invoke_shape]
QED

Theorem invoke_labels_map_subst_block_labels[local]:
  MEM callee
    (MAP FST (get_invoke_targets
      (MAP (subst_block_labels_inst label_map) insts))) <=>
  MEM callee (MAP FST (get_invoke_targets insts))
Proof
  simp[fcgBridgeTheory.mem_get_invoke_targets, MEM_MAP] >>
  metis_tac[subst_block_labels_inst_invoke_shape]
QED


Theorem partition_mem_pair[local]:
  !xs yes no.
    PARTITION pred xs = (yes,no) ==>
    (MEM item yes \/ MEM item no <=> MEM item xs)
Proof
  rpt strip_tac >>
  qpat_x_assum `PARTITION pred xs = (yes,no)` (assume_tac o GSYM) >>
  fs[sortingTheory.PARTITION_DEF] >>
  drule sortingTheory.PART_MEM >>
  simp[]
QED

Theorem fix_phis_in_block_invoke_labels[local]:
  MEM callee
    (simplify_cfg_block_invoke_labels (fix_phis_in_block preds bb)) <=>
  MEM callee (simplify_cfg_block_invoke_labels bb)
Proof
  simp[simplify_cfg_block_invoke_labels_def, fix_phis_in_block_def,
       fcgBridgeTheory.mem_get_invoke_targets] >>
  pairarg_tac >>
  `!item. MEM item phis \/ MEM item non_phis <=>
          MEM item (MAP (fix_phi_inst preds) bb.bb_instructions)` by
    (gen_tac >> drule partition_mem_pair >> simp[]) >>
  qpat_assum `PARTITION _ _ = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `PARTITION _ _ = _` kall_tac >>
  gvs[MEM_APPEND, MEM_MAP] >>
  metis_tac[fix_phi_inst_invoke_shape]
QED

Theorem subst_block_labels_block_invoke_labels[local]:
  MEM callee
    (simplify_cfg_block_invoke_labels
      (subst_block_labels_block label_map bb)) <=>
  MEM callee (simplify_cfg_block_invoke_labels bb)
Proof
  simp[simplify_cfg_block_invoke_labels_def,
       cfgTransformTheory.subst_block_labels_block_def,
       fcgBridgeTheory.mem_get_invoke_targets, MEM_MAP] >>
  metis_tac[subst_block_labels_inst_invoke_shape]
QED

Theorem fix_all_phis_invoke_labels:
  MEM callee (simplify_cfg_fn_invoke_labels (fix_all_phis func)) <=>
  MEM callee (simplify_cfg_fn_invoke_labels func)
Proof
  simp[simplify_cfg_fn_invoke_labels_mem, fix_all_phis_def, MEM_MAP] >>
  metis_tac[fix_phis_in_block_invoke_labels,
            simplify_cfg_block_invoke_labels_def,
            fcgBridgeTheory.mem_get_invoke_targets]
QED

Theorem subst_block_labels_fn_invoke_labels:
  MEM callee
    (simplify_cfg_fn_invoke_labels (subst_block_labels_fn label_map func)) <=>
  MEM callee (simplify_cfg_fn_invoke_labels func)
Proof
  simp[simplify_cfg_fn_invoke_labels_mem,
       cfgTransformTheory.subst_block_labels_fn_def, MEM_MAP] >>
  metis_tac[subst_block_labels_block_invoke_labels,
            simplify_cfg_block_invoke_labels_def,
            fcgBridgeTheory.mem_get_invoke_targets]
QED


Theorem fn_remove_block_invoke_labels[local]:
  MEM callee
    (simplify_cfg_fn_invoke_labels
      (func with fn_blocks := remove_block lbl func.fn_blocks)) <=>
  ?bb. MEM bb func.fn_blocks /\ bb.bb_label <> lbl /\
       MEM callee (simplify_cfg_block_invoke_labels bb)
Proof
  simp[simplify_cfg_fn_invoke_labels_mem,
       simplify_cfg_block_invoke_labels_def,
       fcgBridgeTheory.mem_get_invoke_targets,
       cfgTransformTheory.remove_block_def, MEM_FILTER] >>
  metis_tac[]
QED

Theorem fn_replace_block_invoke_labels[local]:
  MEM callee
    (simplify_cfg_fn_invoke_labels
      (func with fn_blocks := replace_block lbl replacement func.fn_blocks)) <=>
  ?bb. MEM bb func.fn_blocks /\
       MEM callee
         (simplify_cfg_block_invoke_labels
           (if bb.bb_label = lbl then replacement else bb))
Proof
  simp[simplify_cfg_fn_invoke_labels_mem,
       simplify_cfg_block_invoke_labels_def,
       fcgBridgeTheory.mem_get_invoke_targets,
       cfgTransformTheory.replace_block_def, MEM_MAP] >>
  metis_tac[]
QED

Theorem remove_unreachable_blocks_invoke_labels_subset:
  MEM callee
    (simplify_cfg_fn_invoke_labels (remove_unreachable_blocks func)) ==>
  MEM callee (simplify_cfg_fn_invoke_labels func)
Proof
  Cases_on `fn_entry_label func` >>
  simp[remove_unreachable_blocks_def,
       simplify_cfg_fn_invoke_labels_mem, MEM_FILTER] >>
  metis_tac[]
QED

Theorem remove_unreachable_blocks_invoke_labels_mem:
  fn_entry_label func = SOME entry ==>
  (MEM callee
     (simplify_cfg_fn_invoke_labels (remove_unreachable_blocks func)) <=>
   ?bb. MEM bb func.fn_blocks /\ reachable func bb.bb_label /\
        MEM callee (simplify_cfg_block_invoke_labels bb))
Proof
  rpt strip_tac >>
  simp[remove_unreachable_blocks_def,
       simplify_cfg_fn_invoke_labels_mem,
       simplify_cfg_block_invoke_labels_def,
       fcgBridgeTheory.mem_get_invoke_targets, MEM_FILTER] >>
  metis_tac[]
QED

Theorem fn_cfg_edge_iff_fn_succ[local]:
  ALL_DISTINCT (fn_labels func) ==>
  (fn_cfg_edge func src dst <=> fn_succ func src dst)
Proof
  strip_tac >>
  simp[venomWfTheory.fn_cfg_edge_def, cfgTransformTheory.fn_succ_def] >>
  eq_tac >> rpt strip_tac
  >- (qexists `bb` >> simp[] >>
      irule venomExecPropsTheory.MEM_lookup_block >>
      simp[GSYM venomInstTheory.fn_labels_def]) >>
  qexists `bb` >>
  metis_tac[venomExecPropsTheory.lookup_block_MEM,
            venomExecPropsTheory.lookup_block_label]
QED

Theorem fn_reachable_iff_reachable[local]:
  ALL_DISTINCT (fn_labels func) ==>
  (fn_reachable func lbl <=> reachable func lbl)
Proof
  rpt strip_tac >>
  gvs[venomWfTheory.fn_reachable_def, cfgTransformTheory.reachable_def] >>
  eq_tac >> strip_tac >> qexists `entry` >> simp[]
  >- (irule relationTheory.RTC_MONOTONE >>
      metis_tac[fn_cfg_edge_iff_fn_succ]) >>
  irule relationTheory.RTC_MONOTONE >>
  metis_tac[fn_cfg_edge_iff_fn_succ]
QED

Theorem remove_unreachable_blocks_invoke_labels_exact[local]:
  ALL_DISTINCT (fn_labels func) /\ all_reachable func ==>
  (MEM callee
     (simplify_cfg_fn_invoke_labels (remove_unreachable_blocks func)) <=>
   MEM callee (simplify_cfg_fn_invoke_labels func))
Proof
  rpt strip_tac >>
  Cases_on `fn_entry_label func`
  >- simp[remove_unreachable_blocks_def] >>
  simp[remove_unreachable_blocks_invoke_labels_mem] >>
  eq_tac >> rpt strip_tac
  >- (fs[simplify_cfg_block_invoke_labels_def,
          fcgBridgeTheory.mem_get_invoke_targets] >>
      simp[simplify_cfg_fn_invoke_labels_mem] >>
      qexistsl [`bb`,`inst`,`rest`] >> simp[]) >>
  qpat_x_assum
    `MEM callee (simplify_cfg_fn_invoke_labels func)` mp_tac >>
  simp[simplify_cfg_fn_invoke_labels_mem] >> strip_tac >>
  qexists `bb` >>
  simp[simplify_cfg_block_invoke_labels_def,
       fcgBridgeTheory.mem_get_invoke_targets] >>
  fs[cfgWfTheory.all_reachable_def] >>
  `fn_reachable func bb.bb_label` by metis_tac[] >>
  metis_tac[fn_reachable_iff_reachable]
QED


Theorem mem_front_last[local]:
  !xs item. xs <> [] ==>
    (MEM item xs <=> MEM item (FRONT xs) \/ item = LAST xs)
Proof
  Induct_on `xs`
  >- simp[] >>
  Cases_on `xs` >> simp[] >> metis_tac[]
QED

Theorem invoke_labels_front[local]:
  insts <> [] /\ (LAST insts).inst_opcode <> INVOKE ==>
  (MEM callee (MAP FST (get_invoke_targets (FRONT insts))) <=>
   MEM callee (MAP FST (get_invoke_targets insts)))
Proof
  rpt strip_tac >>
  simp[fcgBridgeTheory.mem_get_invoke_targets] >>
  eq_tac >> rpt strip_tac
  >- (qexistsl [`inst`,`rest`] >> simp[] >>
      metis_tac[mem_front_last]) >>
  drule mem_front_last >> strip_tac >>
  qexistsl [`inst`,`rest`] >> gvs[]
QED

Theorem can_merge_blocks_front_no_invoke[local]:
  can_merge_blocks func a b ==>
  a.bb_instructions <> [] /\
  (LAST a.bb_instructions).inst_opcode <> INVOKE
Proof
  simp[can_merge_blocks_def] >> rpt strip_tac >>
  Cases_on `a.bb_instructions`
  >- gvs[venomInstTheory.bb_succs_def] >>
  gvs[venomInstTheory.bb_succs_def,
      venomInstTheory.get_successors_def,
      venomInstTheory.is_terminator_def]
QED

Theorem merge_blocks_invoke_labels[local]:
  can_merge_blocks func a b ==>
  (MEM callee (simplify_cfg_block_invoke_labels (merge_blocks a b)) <=>
   MEM callee (simplify_cfg_block_invoke_labels a) \/
   MEM callee (simplify_cfg_block_invoke_labels b))
Proof
  strip_tac >>
  drule can_merge_blocks_front_no_invoke >> strip_tac >>
  simp[merge_blocks_def, simplify_cfg_block_invoke_labels_def,
       simplify_cfg_invoke_labels_append] >>
  metis_tac[invoke_labels_front]
QED


Theorem can_bypass_jump_no_invoke[local]:
  can_bypass_jump func a b ==>
  !inst. MEM inst b.bb_instructions ==> inst.inst_opcode <> INVOKE
Proof
  simp[can_bypass_jump_def] >> rpt strip_tac >>
  Cases_on `b.bb_instructions` >> gvs[] >>
  gvs[cfgTransformTheory.num_succs_def,
      venomInstTheory.bb_succs_def,
      venomInstTheory.get_successors_def,
      venomInstTheory.is_terminator_def]
QED

Theorem update_phi_bypass_invoke_shape[local]:
  (update_phi_bypass a_label b_label inst).inst_opcode = INVOKE /\
  (update_phi_bypass a_label b_label inst).inst_operands =
    Label callee :: operands <=>
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: operands
Proof
  Cases_on `inst.inst_opcode` >>
  Cases_on `MEM (Label a_label) inst.inst_operands` >>
  simp[update_phi_bypass_def]
QED

Theorem bypass_source_inst_invoke_shape[local]:
  ((if ~is_terminator inst.inst_opcode then inst
     else subst_label_inst old_lbl new_lbl inst).inst_opcode = INVOKE /\
   (if ~is_terminator inst.inst_opcode then inst
    else subst_label_inst old_lbl new_lbl inst).inst_operands =
      Label callee :: operands) <=>
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: operands
Proof
  Cases_on `inst.inst_opcode` >>
  simp[venomInstTheory.is_terminator_def,
       cfgTransformTheory.subst_label_inst_def]
QED

Theorem update_phi_bypass_invoke_labels[local]:
  MEM callee
    (MAP FST (get_invoke_targets
      (MAP (update_phi_bypass a_label b_label) insts))) <=>
  MEM callee (MAP FST (get_invoke_targets insts))
Proof
  simp[fcgBridgeTheory.mem_get_invoke_targets, MEM_MAP] >>
  metis_tac[update_phi_bypass_invoke_shape]
QED

Theorem bypass_source_invoke_labels[local]:
  MEM callee
    (MAP FST (get_invoke_targets
      (MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                    else subst_label_inst old_lbl new_lbl inst) insts))) <=>
  MEM callee (MAP FST (get_invoke_targets insts))
Proof
  simp[fcgBridgeTheory.mem_get_invoke_targets, MEM_MAP] >>
  metis_tac[bypass_source_inst_invoke_shape]
QED


Theorem map_replace_label_absent[local]:
  !bbs lbl replacement.
    ~MEM lbl (MAP (\bb. bb.bb_label) bbs) ==>
    MAP (\bb. if bb.bb_label = lbl then replacement else bb) bbs = bbs
Proof
  Induct_on `bbs` >> simp[]
QED

Theorem fn_replace_block_invoke_labels_preserve[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  lookup_block lbl bbs = SOME old /\
  (MEM callee (simplify_cfg_block_invoke_labels replacement) <=>
   MEM callee (simplify_cfg_block_invoke_labels old)) ==>
  (MEM callee
     (simplify_cfg_fn_invoke_labels
       (func with fn_blocks := replace_block lbl replacement bbs)) <=>
   MEM callee
     (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs)))
Proof
  qid_spec_tac `bbs` >> Induct_on `bbs`
  >- simp[venomInstTheory.lookup_block_def, FIND_thm] >>
  rpt strip_tac >>
  fs[venomInstTheory.lookup_block_def, FIND_thm] >>
  Cases_on `h.bb_label = lbl`
  >- (`MAP (\bb. if bb.bb_label = h.bb_label then replacement else bb) bbs =
       bbs` by metis_tac[map_replace_label_absent] >>
      gvs[cfgTransformTheory.replace_block_def,
          simplify_cfg_fn_invoke_labels_mem,
          simplify_cfg_block_invoke_labels_def,
          fcgBridgeTheory.mem_get_invoke_targets] >>
      metis_tac[]) >>
  gvs[cfgTransformTheory.replace_block_def,
      simplify_cfg_fn_invoke_labels_mem] >>
  metis_tac[]
QED


Theorem succ_phi_update_invoke_shape[local]:
  ((if inst.inst_opcode <> PHI then inst
     else subst_label_inst old_lbl new_lbl inst).inst_opcode = INVOKE /\
   (if inst.inst_opcode <> PHI then inst
    else subst_label_inst old_lbl new_lbl inst).inst_operands =
      Label callee :: operands) <=>
  inst.inst_opcode = INVOKE /\
  inst.inst_operands = Label callee :: operands
Proof
  Cases_on `inst.inst_opcode` >>
  simp[cfgTransformTheory.subst_label_inst_def]
QED

Theorem succ_phi_update_invoke_labels[local]:
  MEM callee
    (MAP FST (get_invoke_targets
      (MAP (\inst. if inst.inst_opcode <> PHI then inst
                    else subst_label_inst old_lbl new_lbl inst) insts))) <=>
  MEM callee (MAP FST (get_invoke_targets insts))
Proof
  simp[fcgBridgeTheory.mem_get_invoke_targets, MEM_MAP] >>
  metis_tac[succ_phi_update_invoke_shape]
QED

Theorem update_succ_phi_labels_invoke_labels[local]:
  !succs bbs.
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    (MEM callee
       (simplify_cfg_fn_invoke_labels
         (func with fn_blocks :=
           update_succ_phi_labels old_lbl new_lbl bbs succs)) <=>
     MEM callee
       (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs)))
Proof
  Induct_on `succs`
  >- simp[update_succ_phi_labels_def] >>
  rpt gen_tac >> strip_tac >>
  simp[update_succ_phi_labels_def] >>
  Cases_on `lookup_block h bbs` >> simp[]
  >- (first_x_assum drule >> simp[update_succ_phi_labels_def]) >>
  rename1 `lookup_block h bbs = SOME target` >>
  `target.bb_label = h` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `MEM callee
      (simplify_cfg_block_invoke_labels
        (target with bb_instructions :=
          MAP (\inst. if inst.inst_opcode <> PHI then inst
                       else subst_label_inst old_lbl new_lbl inst)
              target.bb_instructions)) <=>
   MEM callee (simplify_cfg_block_invoke_labels target)` by
    simp[simplify_cfg_block_invoke_labels_def,
         succ_phi_update_invoke_labels] >>
  `ALL_DISTINCT
      (MAP (\bb. bb.bb_label)
        (replace_block h
          (target with bb_instructions :=
            MAP (\inst. if inst.inst_opcode <> PHI then inst
                         else subst_label_inst old_lbl new_lbl inst)
                target.bb_instructions) bbs))` by
    simp[fn_labels_replace_block] >>
  first_x_assum drule >> strip_tac >>
  gvs[update_succ_phi_labels_def] >>
  metis_tac[fn_replace_block_invoke_labels_preserve]
QED


Theorem fn_remove_block_invoke_labels_preserve[local]:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) /\
  lookup_block lbl bbs = SOME removed /\
  ~MEM callee (simplify_cfg_block_invoke_labels removed) ==>
  (MEM callee
     (simplify_cfg_fn_invoke_labels
       (func with fn_blocks := remove_block lbl bbs)) <=>
   MEM callee
     (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs)))
Proof
  rpt strip_tac >>
  gvs[simplify_cfg_fn_invoke_labels_mem,
      simplify_cfg_block_invoke_labels_def,
      fcgBridgeTheory.mem_get_invoke_targets,
      cfgTransformTheory.remove_block_def, MEM_FILTER] >>
  eq_tac >> rpt strip_tac
  >- metis_tac[] >>
  Cases_on `bb.bb_label = lbl`
  >- (`lookup_block lbl bbs = SOME bb` by
        (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
      gvs[]) >>
  metis_tac[]
QED


Theorem do_merge_jump_metadata[local]:
  do_merge_jump func a b label_map = SOME (func',label_map') ==>
  fn_identity_metadata_eq func' func /\
  fn_static_input_eq func' func /\
  fn_static_layout_eq func' func /\
  fn_fmp_convention_eq func' func
Proof
  simp[do_merge_jump_def] >>
  rpt CASE_TAC >> gvs[] >> rpt strip_tac >>
  gvs[venomInstTheory.fn_identity_metadata_eq_def,
      venomInstTheory.fn_static_input_eq_def,
      venomInstTheory.fn_static_layout_eq_def,
      venomInstTheory.fn_fmp_convention_eq_def]
QED

Theorem fix_all_phis_metadata[local]:
  fn_identity_metadata_eq (fix_all_phis func) func /\
  fn_static_input_eq (fix_all_phis func) func /\
  fn_static_layout_eq (fix_all_phis func) func /\
  fn_fmp_convention_eq (fix_all_phis func) func
Proof
  simp[fix_all_phis_def, fn_blocks_update_metadata]
QED

Theorem subst_block_labels_fn_metadata[local]:
  fn_identity_metadata_eq (subst_block_labels_fn label_map func) func /\
  fn_static_input_eq (subst_block_labels_fn label_map func) func /\
  fn_static_layout_eq (subst_block_labels_fn label_map func) func /\
  fn_fmp_convention_eq (subst_block_labels_fn label_map func) func
Proof
  simp[cfgTransformTheory.subst_block_labels_fn_def,
       fn_blocks_update_metadata]
QED

Theorem remove_unreachable_blocks_metadata[local]:
  fn_identity_metadata_eq (remove_unreachable_blocks func) func /\
  fn_static_input_eq (remove_unreachable_blocks func) func /\
  fn_static_layout_eq (remove_unreachable_blocks func) func /\
  fn_fmp_convention_eq (remove_unreachable_blocks func) func
Proof
  Cases_on `fn_entry_label func` >>
  simp[remove_unreachable_blocks_def, fn_blocks_update_metadata,
       venomInstTheory.fn_identity_metadata_eq_def,
       venomInstTheory.fn_static_input_eq_def,
       venomInstTheory.fn_static_layout_eq_def,
       venomInstTheory.fn_fmp_convention_eq_def]
QED


Theorem do_merge_jump_invoke_labels[local]:
  ALL_DISTINCT (fn_labels func) /\
  lookup_block a.bb_label func.fn_blocks = SOME a /\
  lookup_block b.bb_label func.fn_blocks = SOME b /\
  can_bypass_jump func a b /\
  do_merge_jump func a b label_map = SOME (func',label_map') ==>
  (MEM callee (simplify_cfg_fn_invoke_labels func') <=>
   MEM callee (simplify_cfg_fn_invoke_labels func))
Proof
  rpt strip_tac >>
  fs[do_merge_jump_def] >>
  Cases_on `bb_succs b` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1 `bb_succs b = [target_lbl]` >>
  Cases_on `lookup_block target_lbl func.fn_blocks` >> gvs[] >>
  rename1 `lookup_block target_lbl func.fn_blocks = SOME target` >>
  `target.bb_label = target_lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `b.bb_label <> target_lbl` by
    metis_tac[can_bypass_jump_target_distinct] >>
  `a.bb_label <> b.bb_label` by
    (strip_tac >>
     `a = b` by gvs[] >>
     gvs[can_bypass_jump_def]) >>
  `~MEM callee (simplify_cfg_block_invoke_labels b)` by
    (simp[simplify_cfg_block_invoke_labels_def,
          fcgBridgeTheory.mem_get_invoke_targets] >>
     metis_tac[can_bypass_jump_no_invoke]) >>
  qabbrev_tac `bbs0 = remove_block b.bb_label func.fn_blocks` >>
  qabbrev_tac `target' = target with bb_instructions :=
    MAP (update_phi_bypass a.bb_label b.bb_label) target.bb_instructions` >>
  qabbrev_tac `bbs1 = replace_block target_lbl target' bbs0` >>
  qabbrev_tac `a' = a with bb_instructions :=
    MAP (\inst. if ~is_terminator inst.inst_opcode then inst
                  else subst_label_inst b.bb_label target_lbl inst)
        a.bb_instructions` >>
  `MEM callee (simplify_cfg_block_invoke_labels target') <=>
   MEM callee (simplify_cfg_block_invoke_labels target)` by
    simp[Abbr `target'`, simplify_cfg_block_invoke_labels_def,
         update_phi_bypass_invoke_labels] >>
  `MEM callee (simplify_cfg_block_invoke_labels a') <=>
   MEM callee (simplify_cfg_block_invoke_labels a)` by
    simp[Abbr `a'`, simplify_cfg_block_invoke_labels_def,
         bypass_source_invoke_labels] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs0)` by
    simp[Abbr `bbs0`, cfgTransformPropsTheory.ALL_DISTINCT_remove_block,
         GSYM venomInstTheory.fn_labels_def] >>
  `lookup_block target_lbl bbs0 = SOME target` by
    simp[Abbr `bbs0`, cfgTransformPropsTheory.lookup_block_remove_neq] >>
  `lookup_block a.bb_label bbs0 = SOME a` by
    simp[Abbr `bbs0`, cfgTransformPropsTheory.lookup_block_remove_neq] >>
  `target'.bb_label = target_lbl` by simp[Abbr `target'`] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
    simp[Abbr `bbs1`, fn_labels_replace_block] >>
  `lookup_block a.bb_label bbs1 =
   (if a.bb_label = target_lbl then SOME target' else SOME a)` by
    (Cases_on `a.bb_label = target_lbl`
     >- simp[Abbr `bbs1`, cfgTransformPropsTheory.lookup_block_replace_eq] >>
     simp[Abbr `bbs1`, cfgTransformPropsTheory.lookup_block_replace_neq]) >>
  `MEM callee
      (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs0)) <=>
   MEM callee
      (simplify_cfg_fn_invoke_labels
        (func with fn_blocks := func.fn_blocks))` by
    (simp[Abbr `bbs0`] >>
     irule fn_remove_block_invoke_labels_preserve >>
     simp[GSYM venomInstTheory.fn_labels_def]) >>
  `MEM callee
      (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs1)) <=>
   MEM callee
      (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs0))` by
    metis_tac[fn_replace_block_invoke_labels_preserve] >>
  Cases_on `a.bb_label = target_lbl`
  >- (`a = target` by gvs[] >>
      `MEM callee (simplify_cfg_block_invoke_labels a') <=>
       MEM callee (simplify_cfg_block_invoke_labels target')` by
        metis_tac[] >>
      `MEM callee
          (simplify_cfg_fn_invoke_labels
            (func with fn_blocks := replace_block a.bb_label a' bbs1)) <=>
       MEM callee
          (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs1))` by
        (irule fn_replace_block_invoke_labels_preserve >> simp[]) >>
      gvs[simplify_cfg_fn_invoke_labels_def,
          fcgDefsTheory.fcg_scan_function_def,
          venomInstTheory.fn_insts_def]) >>
  `MEM callee
      (simplify_cfg_fn_invoke_labels
        (func with fn_blocks := replace_block a.bb_label a' bbs1)) <=>
   MEM callee
      (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs1))` by
    (irule fn_replace_block_invoke_labels_preserve >> simp[]) >>
  gvs[Abbr `bbs1`, simplify_cfg_fn_invoke_labels_def,
      fcgDefsTheory.fcg_scan_function_def,
      venomInstTheory.fn_insts_def]
QED


Theorem try_bypass_invoke_labels[local]:
  !succs func incoming bb func' outgoing success.
    ALL_DISTINCT (fn_labels func) /\
    lookup_block bb.bb_label func.fn_blocks = SOME bb /\
    try_bypass func incoming bb succs = (func',outgoing,success) ==>
    (MEM callee (simplify_cfg_fn_invoke_labels func') <=>
     MEM callee (simplify_cfg_fn_invoke_labels func))
Proof
  Induct_on `succs`
  >- simp[try_bypass_def] >>
  rpt strip_tac >>
  gvs[Once try_bypass_def, AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[]) >>
  `next_bb.bb_label = h` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  metis_tac[do_merge_jump_invoke_labels]
QED


Theorem try_bypass_metadata[local]:
  !succs func incoming bb func' outgoing success.
    try_bypass func incoming bb succs = (func',outgoing,success) ==>
    fn_identity_metadata_eq func' func /\
    fn_static_input_eq func' func /\
    fn_static_layout_eq func' func /\
    fn_fmp_convention_eq func' func
Proof
  Induct_on `succs`
  >- simp[try_bypass_def,
          venomInstTheory.fn_identity_metadata_eq_def,
          venomInstTheory.fn_static_input_eq_def,
          venomInstTheory.fn_static_layout_eq_def,
          venomInstTheory.fn_fmp_convention_eq_def] >>
  rpt strip_tac >>
  gvs[Once try_bypass_def, AllCaseEqs()] >>
  TRY (first_x_assum drule_all >> simp[]) >>
  metis_tac[do_merge_jump_metadata]
QED


Definition simplify_cfg_invoke_subset_def:
  simplify_cfg_invoke_subset result original <=>
    !callee. MEM callee (simplify_cfg_fn_invoke_labels result) ==>
             MEM callee (simplify_cfg_fn_invoke_labels original)
End

Theorem simplify_cfg_invoke_subset_refl[local]:
  simplify_cfg_invoke_subset func func
Proof
  simp[simplify_cfg_invoke_subset_def]
QED

Theorem simplify_cfg_invoke_subset_trans[local]:
  simplify_cfg_invoke_subset final middle /\
  simplify_cfg_invoke_subset middle initial ==>
  simplify_cfg_invoke_subset final initial
Proof
  simp[simplify_cfg_invoke_subset_def] >> metis_tac[]
QED

Theorem chain_merge_invoke_subset[local]:
  ALL_DISTINCT (fn_labels func) /\
  lookup_block bb.bb_label func.fn_blocks = SOME bb /\
  lookup_block next_bb.bb_label func.fn_blocks = SOME next_bb /\
  can_merge_blocks func bb next_bb ==>
  let merged = merge_blocks bb next_bb in
  let bbs0 = remove_block next_bb.bb_label func.fn_blocks in
  let bbs1 = replace_block bb.bb_label merged bbs0 in
  let bbs2 = update_succ_phi_labels next_bb.bb_label bb.bb_label bbs1 (bb_succs merged) in
  simplify_cfg_invoke_subset (func with fn_blocks := bbs2) func
Proof
  rpt strip_tac >> gvs[] >>
  drule can_merge_blocks_distinct >> strip_tac >>
  qabbrev_tac `merged = merge_blocks bb next_bb` >>
  qabbrev_tac `bbs0 = remove_block next_bb.bb_label func.fn_blocks` >>
  qabbrev_tac `bbs1 = replace_block bb.bb_label merged bbs0` >>
  `merged.bb_label = bb.bb_label` by simp[Abbr `merged`, merge_blocks_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs0)` by
    simp[Abbr `bbs0`, cfgTransformPropsTheory.ALL_DISTINCT_remove_block,
         GSYM venomInstTheory.fn_labels_def] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs1)` by
    simp[Abbr `bbs1`, fn_labels_replace_block] >>
  simp[simplify_cfg_invoke_subset_def] >> rpt strip_tac >>
  `MEM callee
      (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs1))` by
    metis_tac[update_succ_phi_labels_invoke_labels] >>
  qpat_x_assum
    `MEM callee (simplify_cfg_fn_invoke_labels (func with fn_blocks := bbs1))`
    mp_tac >>
  simp[Abbr `bbs1`, fn_replace_block_invoke_labels,
       Abbr `bbs0`, cfgTransformTheory.remove_block_def, MEM_FILTER] >>
  strip_tac >>
  gvs[simplify_cfg_fn_invoke_labels_mem,
      cfgTransformTheory.replace_block_def, MEM_MAP] >>
  rename [`MEM old (FILTER _ func.fn_blocks)`,
          `MEM callinst
             (if old.bb_label = bb.bb_label then merged else old).bb_instructions`,
          `callinst.inst_operands = Label callee :: callops`] >>
  Cases_on `old.bb_label = bb.bb_label`
  >- (`MEM callee (simplify_cfg_block_invoke_labels merged)` by
        (simp[simplify_cfg_block_invoke_labels_def,
              fcgBridgeTheory.mem_get_invoke_targets] >>
         metis_tac[]) >>
      `MEM callee (simplify_cfg_block_invoke_labels bb) \/
       MEM callee (simplify_cfg_block_invoke_labels next_bb)` by
        metis_tac[merge_blocks_invoke_labels] >>
      gvs[simplify_cfg_fn_invoke_labels_mem,
          simplify_cfg_block_invoke_labels_def,
          fcgBridgeTheory.mem_get_invoke_targets] >>
      metis_tac[venomExecPropsTheory.lookup_block_MEM]) >>
  gvs[simplify_cfg_fn_invoke_labels_mem,
      simplify_cfg_block_invoke_labels_def,
      fcgBridgeTheory.mem_get_invoke_targets] >>
  qexistsl [`old`,`callinst`,`callops`] >>
  gvs[MEM_FILTER]
QED

Theorem collapse_dfs_result_invoke_subset_compose[local]:
  simplify_cfg_invoke_subset middle initial ==>
  collapse_dfs_result
    (\result. simplify_cfg_invoke_subset (FST result) middle)
    middle label_map visited lbl ==>
  simplify_cfg_invoke_subset
    (FST (collapse_dfs middle label_map visited lbl)) initial
Proof
  simp[collapse_dfs_result_def] >>
  metis_tac[simplify_cfg_invoke_subset_trans]
QED

Theorem collapse_dfs_succs_result_invoke_subset_compose[local]:
  simplify_cfg_invoke_subset middle initial ==>
  collapse_dfs_succs_result
    (\result. simplify_cfg_invoke_subset (FST result) middle)
    middle label_map visited succs ==>
  simplify_cfg_invoke_subset
    (FST (collapse_dfs_succs middle label_map visited succs)) initial
Proof
  simp[collapse_dfs_succs_result_def] >>
  metis_tac[simplify_cfg_invoke_subset_trans]
QED


Theorem collapse_invoke_subset_joint[local]:
  (!func label_map visited lbl.
     ALL_DISTINCT (fn_labels func) ==>
     collapse_dfs_result
       (\result. simplify_cfg_invoke_subset (FST result) func)
       func label_map visited lbl) /\
  (!func label_map visited succs.
     ALL_DISTINCT (fn_labels func) ==>
     collapse_dfs_succs_result
       (\result. simplify_cfg_invoke_subset (FST result) func)
       func label_map visited succs)
Proof
  ho_match_mp_tac collapse_dfs_ind >>
  rpt conj_tac
  >- suspend "dfs"
  >- suspend "nil"
  >> suspend "succs"
QED

Resume collapse_invoke_subset_joint[dfs]:
  rpt strip_tac >>
  simp[NoAsms, collapse_dfs_result_def, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl func.fn_blocks`
  >- simp[simplify_cfg_invoke_subset_refl] >>
  rename1 `lookup_block lbl func.fn_blocks = SOME bb` >>
  Cases_on `bb_succs bb`
  >- (Cases_on `MEM lbl visited`
      >- simp[try_bypass_def, simplify_cfg_invoke_subset_refl]
      >> gvs[try_bypass_def, collapse_dfs_succs_result_def]) >>
  Cases_on `t`
  >- (Cases_on `lookup_block h func.fn_blocks`
      >- (Cases_on `MEM lbl visited` >>
          simp[simplify_cfg_invoke_subset_refl])
      >> rename1 `lookup_block h func.fn_blocks = SOME next_bb`
      >> Cases_on `can_merge_blocks func bb next_bb`
      >- (gvs[] >>
          `bb.bb_label = lbl` by
            metis_tac[venomExecPropsTheory.lookup_block_label] >>
          `next_bb.bb_label = h` by
            metis_tac[venomExecPropsTheory.lookup_block_label] >>
          qmatch_goalsub_abbrev_tac
            `collapse_dfs merged_func merged_map visited lbl` >>
          irule collapse_dfs_result_invoke_subset_compose >>
          conj_tac
          >- (gvs[Abbr `merged_func`, Abbr `merged_map`] >>
              drule_all chain_merge_invoke_subset >> simp[]) >>
          `fn_result_events (fn_labels func) label_map merged_func merged_map` by
            (simp[Abbr `merged_func`, Abbr `merged_map`] >>
             drule_all chain_merge_fn_result_events >> simp[]) >>
          `ALL_DISTINCT (fn_labels merged_func)` by
            metis_tac[fn_result_events_all_distinct] >>
          first_x_assum drule >>
          simp[collapse_dfs_result_def])
      >> Cases_on `MEM lbl visited`
      >- simp[simplify_cfg_invoke_subset_refl]
      >> gvs[collapse_dfs_result_def])
  >> Cases_on `try_bypass func label_map bb (h::h'::t')`
  >> PairCases_on `r`
  >> Cases_on `r1`
  >- (gvs[] >>
      `bb.bb_label = lbl` by
        metis_tac[venomExecPropsTheory.lookup_block_label] >>
      `lookup_block bb.bb_label func.fn_blocks = SOME bb` by gvs[] >>
      `simplify_cfg_invoke_subset q func` by
        (simp[simplify_cfg_invoke_subset_def] >>
         metis_tac[try_bypass_invoke_labels]) >>
      `fn_result_events (fn_labels func) label_map q r0` by
        (drule_all try_bypass_events_at >> simp[]) >>
      `ALL_DISTINCT (fn_labels q)` by
        metis_tac[fn_result_events_all_distinct] >>
      metis_tac[collapse_dfs_result_invoke_subset_compose])
  >> gvs[] >>
  `bb.bb_label = lbl` by
    metis_tac[venomExecPropsTheory.lookup_block_label] >>
  `lookup_block bb.bb_label func.fn_blocks = SOME bb` by gvs[] >>
  `simplify_cfg_invoke_subset q func` by
    (simp[simplify_cfg_invoke_subset_def] >>
     metis_tac[try_bypass_invoke_labels]) >>
  `fn_result_events (fn_labels func) label_map q r0` by
    (drule_all try_bypass_events_at >> simp[]) >>
  `ALL_DISTINCT (fn_labels q)` by
    metis_tac[fn_result_events_all_distinct] >>
  Cases_on `MEM lbl visited`
  >- simp[] >>
  metis_tac[collapse_dfs_succs_result_invoke_subset_compose]
QED

Resume collapse_invoke_subset_joint[nil]:
  simp[collapse_dfs_succs_result_def, collapse_dfs_def,
       simplify_cfg_invoke_subset_refl]
QED

Resume collapse_invoke_subset_joint[succs]:
  rpt strip_tac >>
  simp[collapse_dfs_succs_result_def, Once collapse_dfs_def] >>
  Cases_on `collapse_dfs func label_map visited lbl` >>
  PairCases_on `r` >> gvs[collapse_dfs_result_def] >>
  `simplify_cfg_invoke_subset q func` by gvs[] >>
  `fn_result_events (fn_labels func) label_map q r0` by
    (metis_tac[collapse_dfs_result_def,
               collapse_result_events_pair,
               CONJUNCT1 collapse_events_joint]) >>
  `ALL_DISTINCT (fn_labels q)` by
    metis_tac[fn_result_events_all_distinct] >>
  metis_tac[collapse_dfs_succs_result_invoke_subset_compose]
QED

Finalise collapse_invoke_subset_joint


Theorem collapse_dfs_invoke_subset[local]:
  ALL_DISTINCT (fn_labels func) ==>
  simplify_cfg_invoke_subset
    (FST (collapse_dfs func label_map visited lbl)) func
Proof
  strip_tac >>
  drule (CONJUNCT1 collapse_invoke_subset_joint) >>
  simp[collapse_dfs_result_def]
QED

Theorem fix_all_phis_invoke_subset[local]:
  simplify_cfg_invoke_subset (fix_all_phis func) func
Proof
  simp[simplify_cfg_invoke_subset_def, fix_all_phis_invoke_labels]
QED

Theorem subst_block_labels_fn_invoke_subset[local]:
  simplify_cfg_invoke_subset (subst_block_labels_fn label_map func) func
Proof
  simp[simplify_cfg_invoke_subset_def,
       subst_block_labels_fn_invoke_labels]
QED

Theorem remove_unreachable_blocks_invoke_subset[local]:
  simplify_cfg_invoke_subset (remove_unreachable_blocks func) func
Proof
  simp[simplify_cfg_invoke_subset_def] >>
  metis_tac[remove_unreachable_blocks_invoke_labels_subset]
QED

Theorem simplify_cfg_round_with_labels_invoke_subset:
  ALL_DISTINCT (fn_labels func) ==>
  simplify_cfg_invoke_subset
    (FST (simplify_cfg_round_with_labels func)) func
Proof
  strip_tac >>
  Cases_on `fn_entry_label func`
  >- simp[simplify_cfg_round_with_labels_def,
          simplify_cfg_invoke_subset_refl] >>
  rename1 `fn_entry_label func = SOME entry` >>
  qabbrev_tac `func1 = remove_unreachable_blocks func` >>
  qabbrev_tac `func1a = fix_all_phis func1` >>
  Cases_on `collapse_dfs func1a [] [] entry` >>
  PairCases_on `r` >>
  rename1 `collapse_dfs func1a [] [] entry = (func2,label_map,visited)` >>
  `ALL_DISTINCT (fn_labels func1a)` by
    simp[Abbr `func1a`, Abbr `func1`, fn_labels_fix_all_phis,
         fn_labels_remove_unreachable_all_distinct] >>
  `simplify_cfg_invoke_subset
     (FST (collapse_dfs func1a [] [] entry)) func1a` by
    metis_tac[collapse_dfs_invoke_subset] >>
  `simplify_cfg_invoke_subset func2 func1a` by gvs[] >>
  qabbrev_tac `func3 = if label_map = [] then func2
                       else subst_block_labels_fn label_map func2` >>
  `simplify_cfg_invoke_subset func3 func2` by
    (simp[Abbr `func3`] >>
     metis_tac[subst_block_labels_fn_invoke_subset,
               simplify_cfg_invoke_subset_refl]) >>
  `simplify_cfg_invoke_subset
     (fix_all_phis (remove_unreachable_blocks func3)) func3` by
    metis_tac[fix_all_phis_invoke_subset,
              remove_unreachable_blocks_invoke_subset,
              simplify_cfg_invoke_subset_trans] >>
  `simplify_cfg_invoke_subset func1a func` by
    (simp[Abbr `func1a`, Abbr `func1`, simplify_cfg_invoke_subset_def,
          fix_all_phis_invoke_labels] >>
     metis_tac[remove_unreachable_blocks_invoke_labels_subset]) >>
  pure_once_rewrite_tac[simplify_cfg_round_with_labels_def] >>
  qpat_assum `fn_entry_label func = SOME entry`
    (fn th => rewrite_tac[th]) >>
  simp[Abbr `func1`, Abbr `func1a`] >>
  qpat_assum `collapse_dfs _ _ _ _ = _`
    (fn th => rewrite_tac[th]) >>
  simp[Abbr `func3`] >>
  metis_tac[simplify_cfg_invoke_subset_trans]
QED


Theorem simplify_cfg_iter_with_labels_invoke_subset:
  !n func. ALL_DISTINCT (fn_labels func) ==>
    simplify_cfg_invoke_subset
      (FST (simplify_cfg_iter_with_labels n func)) func
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def,
          simplify_cfg_invoke_subset_refl] >>
  rpt strip_tac >>
  Cases_on `simplify_cfg_round_with_labels func` >>
  rename1 `simplify_cfg_round_with_labels func = (func',round_map)` >>
  `simplify_cfg_invoke_subset
     (FST (simplify_cfg_round_with_labels func)) func` by
    metis_tac[simplify_cfg_round_with_labels_invoke_subset] >>
  `simplify_cfg_invoke_subset func' func` by gvs[] >>
  `label_map_transition (fn_labels func)
     (SND (simplify_cfg_round_with_labels func))
     (fn_labels (FST (simplify_cfg_round_with_labels func)))` by
    metis_tac[simplify_cfg_round_with_labels_transition] >>
  `ALL_DISTINCT (fn_labels func')` by
    (qpat_x_assum `label_map_transition _ _ _` mp_tac >>
     qpat_assum `simplify_cfg_round_with_labels func = (func',round_map)`
       (fn th => rewrite_tac[th]) >>
     simp[label_map_transition_def]) >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >>
  qpat_assum `simplify_cfg_round_with_labels func = (func',round_map)`
    (fn th => rewrite_tac[th]) >>
  simp[] >>
  IF_CASES_TAC
  >- simp[simplify_cfg_invoke_subset_refl] >>
  `simplify_cfg_invoke_subset
     (FST (simplify_cfg_iter_with_labels n func')) func'` by
    metis_tac[] >>
  Cases_on `simplify_cfg_iter_with_labels n func'` >>
  gvs[] >>
  metis_tac[simplify_cfg_invoke_subset_trans]
QED

Theorem simplify_cfg_fn_with_labels_invoke_subset:
  ALL_DISTINCT (fn_labels func) ==>
  simplify_cfg_invoke_subset
    (FST (simplify_cfg_fn_with_labels func)) func
Proof
  simp[simplify_cfg_fn_with_labels_def,
       simplify_cfg_iter_with_labels_invoke_subset]
QED

Theorem simplify_cfg_fn_with_labels_no_new_call_edges:
  ALL_DISTINCT (fn_labels func) ==>
  !callee.
    MEM callee
      (simplify_cfg_fn_invoke_labels
        (FST (simplify_cfg_fn_with_labels func))) ==>
    MEM callee (simplify_cfg_fn_invoke_labels func)
Proof
  strip_tac >>
  drule simplify_cfg_fn_with_labels_invoke_subset >>
  simp[simplify_cfg_invoke_subset_def]
QED


Definition simplify_cfg_metadata_eq_def:
  simplify_cfg_metadata_eq result original <=>
    fn_identity_metadata_eq result original /\
    fn_static_input_eq result original /\
    fn_static_layout_eq result original /\
    fn_fmp_convention_eq result original
End

Theorem simplify_cfg_metadata_eq_refl[local]:
  simplify_cfg_metadata_eq func func
Proof
  simp[simplify_cfg_metadata_eq_def,
       venomInstTheory.fn_identity_metadata_eq_def,
       venomInstTheory.fn_static_input_eq_def,
       venomInstTheory.fn_static_layout_eq_def,
       venomInstTheory.fn_fmp_convention_eq_def]
QED

Theorem simplify_cfg_metadata_eq_trans[local]:
  simplify_cfg_metadata_eq final middle /\
  simplify_cfg_metadata_eq middle initial ==>
  simplify_cfg_metadata_eq final initial
Proof
  simp[simplify_cfg_metadata_eq_def,
       venomInstTheory.fn_identity_metadata_eq_def,
       venomInstTheory.fn_static_input_eq_def,
       venomInstTheory.fn_static_layout_eq_def,
       venomInstTheory.fn_fmp_convention_eq_def] >>
  metis_tac[]
QED

Theorem collapse_dfs_result_metadata_compose[local]:
  simplify_cfg_metadata_eq middle initial ==>
  collapse_dfs_result
    (\result. simplify_cfg_metadata_eq (FST result) middle)
    middle label_map visited lbl ==>
  simplify_cfg_metadata_eq
    (FST (collapse_dfs middle label_map visited lbl)) initial
Proof
  simp[collapse_dfs_result_def] >>
  metis_tac[simplify_cfg_metadata_eq_trans]
QED

Theorem collapse_dfs_succs_result_metadata_compose[local]:
  simplify_cfg_metadata_eq middle initial ==>
  collapse_dfs_succs_result
    (\result. simplify_cfg_metadata_eq (FST result) middle)
    middle label_map visited succs ==>
  simplify_cfg_metadata_eq
    (FST (collapse_dfs_succs middle label_map visited succs)) initial
Proof
  simp[collapse_dfs_succs_result_def] >>
  metis_tac[simplify_cfg_metadata_eq_trans]
QED

Theorem collapse_metadata_joint[local]:
  (!func label_map visited lbl.
     collapse_dfs_result
       (\result. simplify_cfg_metadata_eq (FST result) func)
       func label_map visited lbl) /\
  (!func label_map visited succs.
     collapse_dfs_succs_result
       (\result. simplify_cfg_metadata_eq (FST result) func)
       func label_map visited succs)
Proof
  ho_match_mp_tac collapse_dfs_ind >>
  rpt conj_tac
  >- suspend "dfs"
  >- suspend "nil"
  >> suspend "succs"
QED

Resume collapse_metadata_joint[dfs]:
  rpt strip_tac >>
  simp[NoAsms, collapse_dfs_result_def, Once collapse_dfs_def] >>
  Cases_on `lookup_block lbl func.fn_blocks`
  >- simp[simplify_cfg_metadata_eq_refl] >>
  rename1 `lookup_block lbl func.fn_blocks = SOME bb` >>
  Cases_on `bb_succs bb`
  >- (Cases_on `MEM lbl visited`
      >- simp[try_bypass_def, simplify_cfg_metadata_eq_refl]
      >> gvs[try_bypass_def, collapse_dfs_succs_result_def]) >>
  Cases_on `t`
  >- (Cases_on `lookup_block h func.fn_blocks`
      >- (Cases_on `MEM lbl visited` >>
          simp[simplify_cfg_metadata_eq_refl])
      >> rename1 `lookup_block h func.fn_blocks = SOME next_bb`
      >> Cases_on `can_merge_blocks func bb next_bb`
      >- (gvs[] >>
          qmatch_goalsub_abbrev_tac
            `collapse_dfs merged_func merged_map visited lbl` >>
          irule collapse_dfs_result_metadata_compose >>
          conj_tac
          >- simp[Abbr `merged_func`, simplify_cfg_metadata_eq_def,
                  fn_blocks_update_metadata] >>
          first_x_assum irule)
      >> Cases_on `MEM lbl visited`
      >- simp[simplify_cfg_metadata_eq_refl]
      >> gvs[collapse_dfs_result_def])
  >> Cases_on `try_bypass func label_map bb (h::h'::t')`
  >> PairCases_on `r`
  >> Cases_on `r1`
  >- (gvs[] >>
      `simplify_cfg_metadata_eq q func` by
        (simp[simplify_cfg_metadata_eq_def] >>
         metis_tac[try_bypass_metadata]) >>
      metis_tac[collapse_dfs_result_metadata_compose])
  >> gvs[] >>
  `simplify_cfg_metadata_eq q func` by
    (simp[simplify_cfg_metadata_eq_def] >>
     metis_tac[try_bypass_metadata]) >>
  Cases_on `MEM lbl visited`
  >- simp[] >>
  metis_tac[collapse_dfs_succs_result_metadata_compose]
QED

Resume collapse_metadata_joint[nil]:
  simp[collapse_dfs_succs_result_def, collapse_dfs_def,
       simplify_cfg_metadata_eq_refl]
QED

Resume collapse_metadata_joint[succs]:
  rpt strip_tac >>
  simp[collapse_dfs_succs_result_def, Once collapse_dfs_def] >>
  Cases_on `collapse_dfs func label_map visited lbl` >>
  PairCases_on `r` >> gvs[collapse_dfs_result_def] >>
  `simplify_cfg_metadata_eq q func` by gvs[] >>
  metis_tac[collapse_dfs_succs_result_metadata_compose]
QED

Finalise collapse_metadata_joint


Theorem collapse_dfs_metadata:
  collapse_dfs func label_map visited lbl = (func',label_map',visited') ==>
  fn_identity_metadata_eq func' func /\
  fn_static_input_eq func' func /\
  fn_static_layout_eq func' func /\
  fn_fmp_convention_eq func' func
Proof
  strip_tac >>
  `collapse_dfs_result
     (\result. simplify_cfg_metadata_eq (FST result) func)
     func label_map visited lbl` by
    metis_tac[CONJUNCT1 collapse_metadata_joint] >>
  gvs[collapse_dfs_result_def, simplify_cfg_metadata_eq_def]
QED

Theorem collapse_dfs_succs_metadata:
  collapse_dfs_succs func label_map visited succs =
    (func',label_map',visited') ==>
  fn_identity_metadata_eq func' func /\
  fn_static_input_eq func' func /\
  fn_static_layout_eq func' func /\
  fn_fmp_convention_eq func' func
Proof
  strip_tac >>
  `collapse_dfs_succs_result
     (\result. simplify_cfg_metadata_eq (FST result) func)
     func label_map visited succs` by
    metis_tac[CONJUNCT2 collapse_metadata_joint] >>
  gvs[collapse_dfs_succs_result_def, simplify_cfg_metadata_eq_def]
QED


Theorem simplify_cfg_round_with_labels_metadata_eq[local]:
  simplify_cfg_metadata_eq
    (FST (simplify_cfg_round_with_labels func)) func
Proof
  Cases_on `fn_entry_label func`
  >- simp[simplify_cfg_round_with_labels_def,
          simplify_cfg_metadata_eq_refl] >>
  rename1 `fn_entry_label func = SOME entry` >>
  qabbrev_tac `func1 = remove_unreachable_blocks func` >>
  qabbrev_tac `func1a = fix_all_phis func1` >>
  Cases_on `collapse_dfs func1a [] [] entry` >>
  PairCases_on `r` >>
  rename1 `collapse_dfs func1a [] [] entry = (func2,label_map,visited)` >>
  qabbrev_tac `func3 = if label_map = [] then func2
                       else subst_block_labels_fn label_map func2` >>
  `simplify_cfg_metadata_eq func1 func` by
    simp[Abbr `func1`, simplify_cfg_metadata_eq_def,
         remove_unreachable_blocks_metadata] >>
  `simplify_cfg_metadata_eq func1a func1` by
    simp[Abbr `func1a`, simplify_cfg_metadata_eq_def,
         fix_all_phis_metadata] >>
  `simplify_cfg_metadata_eq func2 func1a` by
    (drule collapse_dfs_metadata >>
     simp[simplify_cfg_metadata_eq_def]) >>
  `simplify_cfg_metadata_eq func3 func2` by
    (Cases_on `label_map = []`
     >- simp[Abbr `func3`, simplify_cfg_metadata_eq_refl] >>
     simp[Abbr `func3`, simplify_cfg_metadata_eq_def,
          subst_block_labels_fn_metadata]) >>
  `simplify_cfg_metadata_eq
     (remove_unreachable_blocks func3) func3` by
    simp[simplify_cfg_metadata_eq_def,
         remove_unreachable_blocks_metadata] >>
  `simplify_cfg_metadata_eq
     (fix_all_phis (remove_unreachable_blocks func3))
     (remove_unreachable_blocks func3)` by
    simp[simplify_cfg_metadata_eq_def, fix_all_phis_metadata] >>
  `simplify_cfg_metadata_eq func1a func` by
    metis_tac[simplify_cfg_metadata_eq_trans] >>
  `simplify_cfg_metadata_eq func2 func` by
    metis_tac[simplify_cfg_metadata_eq_trans] >>
  `simplify_cfg_metadata_eq func3 func` by
    metis_tac[simplify_cfg_metadata_eq_trans] >>
  `simplify_cfg_metadata_eq
     (remove_unreachable_blocks func3) func` by
    metis_tac[simplify_cfg_metadata_eq_trans] >>
  `simplify_cfg_metadata_eq
     (fix_all_phis (remove_unreachable_blocks func3)) func` by
    metis_tac[simplify_cfg_metadata_eq_trans] >>
  pure_once_rewrite_tac[simplify_cfg_round_with_labels_def] >>
  qpat_assum `fn_entry_label func = SOME entry`
    (fn th => rewrite_tac[th]) >>
  simp[Abbr `func1`, Abbr `func1a`] >>
  qpat_assum `collapse_dfs _ _ _ _ = _`
    (fn th => rewrite_tac[th]) >>
  simp[Abbr `func3`]
QED

Theorem simplify_cfg_round_with_labels_metadata:
  simplify_cfg_round_with_labels func = (func',label_map) ==>
  fn_identity_metadata_eq func' func /\
  fn_static_input_eq func' func /\
  fn_static_layout_eq func' func /\
  fn_fmp_convention_eq func' func
Proof
  strip_tac >>
  `simplify_cfg_metadata_eq
     (FST (simplify_cfg_round_with_labels func)) func` by
    simp[simplify_cfg_round_with_labels_metadata_eq] >>
  gvs[simplify_cfg_metadata_eq_def]
QED

Theorem simplify_cfg_iter_with_labels_metadata_eq[local]:
  !n func. simplify_cfg_metadata_eq
    (FST (simplify_cfg_iter_with_labels n func)) func
Proof
  Induct_on `n`
  >- simp[simplify_cfg_iter_with_labels_def,
          simplify_cfg_metadata_eq_refl] >>
  gen_tac >>
  Cases_on `simplify_cfg_round_with_labels func` >>
  rename1 `simplify_cfg_round_with_labels func = (func',round_map)` >>
  `simplify_cfg_metadata_eq func' func` by
    (drule simplify_cfg_round_with_labels_metadata >>
     simp[simplify_cfg_metadata_eq_def]) >>
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >>
  qpat_assum `simplify_cfg_round_with_labels func = (func',round_map)`
    (fn th => rewrite_tac[th]) >>
  simp[] >>
  IF_CASES_TAC
  >- simp[simplify_cfg_metadata_eq_refl] >>
  `simplify_cfg_metadata_eq
     (FST (simplify_cfg_iter_with_labels n func')) func'` by
    metis_tac[] >>
  Cases_on `simplify_cfg_iter_with_labels n func'` >>
  gvs[] >>
  metis_tac[simplify_cfg_metadata_eq_trans]
QED

Theorem simplify_cfg_iter_with_labels_metadata:
  simplify_cfg_iter_with_labels n func = (func',label_map) ==>
  fn_identity_metadata_eq func' func /\
  fn_static_input_eq func' func /\
  fn_static_layout_eq func' func /\
  fn_fmp_convention_eq func' func
Proof
  strip_tac >>
  `simplify_cfg_metadata_eq
     (FST (simplify_cfg_iter_with_labels n func)) func` by
    metis_tac[simplify_cfg_iter_with_labels_metadata_eq] >>
  gvs[simplify_cfg_metadata_eq_def]
QED

Theorem simplify_cfg_fn_with_labels_metadata:
  simplify_cfg_fn_with_labels func = (func',label_map) ==>
  fn_identity_metadata_eq func' func /\
  fn_static_input_eq func' func /\
  fn_static_layout_eq func' func /\
  fn_fmp_convention_eq func' func
Proof
  simp[simplify_cfg_fn_with_labels_def] >>
  metis_tac[simplify_cfg_iter_with_labels_metadata]
QED

Theorem simplify_cfg_fn_metadata:
  fn_identity_metadata_eq (simplify_cfg_fn func) func /\
  fn_static_input_eq (simplify_cfg_fn func) func /\
  fn_static_layout_eq (simplify_cfg_fn func) func /\
  fn_fmp_convention_eq (simplify_cfg_fn func) func
Proof
  Cases_on `simplify_cfg_fn_with_labels func` >>
  drule simplify_cfg_fn_with_labels_metadata >>
  simp[simplify_cfg_fn_def]
QED

Definition simplify_cfg_duplicate_label_func_def:
  simplify_cfg_duplicate_label_func = mk_raw_function "f"
    [<| bb_label := "e";
        bb_instructions := [mk_inst 0 JMP [Label "x"] []] |>;
     <| bb_label := "x";
        bb_instructions := [mk_inst 1 STOP [] []] |>;
     <| bb_label := "x";
        bb_instructions := [mk_inst 2 INVOKE [Label "callee"] []] |>]
End

Theorem simplify_cfg_duplicate_label_edge[local]:
  fn_cfg_edge simplify_cfg_duplicate_label_func "e" "x"
Proof
  simp[venomWfTheory.fn_cfg_edge_def] >>
  qexists `<| bb_label := "e";
              bb_instructions := [mk_inst 0 JMP [Label "x"] []] |>` >>
  simp[simplify_cfg_duplicate_label_func_def,
       venomInstTheory.mk_raw_function_def, venomInstTheory.mk_inst_def,
       venomInstTheory.bb_succs_def, venomInstTheory.get_successors_def,
       venomInstTheory.is_terminator_def, venomStateTheory.get_label_def,
       listTheory.nub_def]
QED

Theorem simplify_cfg_duplicate_label_entry[local]:
  fn_entry_label simplify_cfg_duplicate_label_func = SOME "e"
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_reachable_labels[local]:
  fn_reachable simplify_cfg_duplicate_label_func "e" /\
  fn_reachable simplify_cfg_duplicate_label_func "x"
Proof
  conj_tac
  >- simp[venomWfTheory.fn_reachable_def,
          simplify_cfg_duplicate_label_entry, relationTheory.RTC_REFL] >>
  simp[venomWfTheory.fn_reachable_def,
       simplify_cfg_duplicate_label_entry] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists `"x"` >>
  simp[simplify_cfg_duplicate_label_edge, relationTheory.RTC_REFL]
QED

Theorem simplify_cfg_duplicate_label_member_label[local]:
  MEM bb simplify_cfg_duplicate_label_func.fn_blocks ==>
  bb.bb_label = "e" \/ bb.bb_label = "x"
Proof
  simp[simplify_cfg_duplicate_label_func_def,
       venomInstTheory.mk_raw_function_def] >>
  strip_tac >> gvs[]
QED

Theorem simplify_cfg_duplicate_label_all_reachable[local]:
  all_reachable simplify_cfg_duplicate_label_func
Proof
  rw[cfgWfTheory.all_reachable_def] >>
  drule simplify_cfg_duplicate_label_member_label >>
  strip_tac >> gvs[simplify_cfg_duplicate_label_reachable_labels]
QED

Theorem simplify_cfg_duplicate_label_has_call[local]:
  MEM "callee"
    (simplify_cfg_fn_invoke_labels simplify_cfg_duplicate_label_func)
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_fn_succ[local]:
  fn_succ simplify_cfg_duplicate_label_func "e" "x"
Proof
  simp[cfgTransformTheory.fn_succ_def] >>
  qexists `<| bb_label := "e";
              bb_instructions := [mk_inst 0 JMP [Label "x"] []] |>` >>
  simp[simplify_cfg_duplicate_label_func_def,
       venomInstTheory.mk_raw_function_def, venomInstTheory.mk_inst_def,
       venomInstTheory.lookup_block_def,
       venomInstTheory.bb_succs_def, venomInstTheory.get_successors_def,
       venomInstTheory.is_terminator_def, venomStateTheory.get_label_def,
       listTheory.nub_def] >> EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_reachable[local]:
  reachable simplify_cfg_duplicate_label_func "e" /\
  reachable simplify_cfg_duplicate_label_func "x"
Proof
  conj_tac
  >- simp[cfgTransformTheory.reachable_def,
          simplify_cfg_duplicate_label_entry, relationTheory.RTC_REFL] >>
  simp[cfgTransformTheory.reachable_def,
       simplify_cfg_duplicate_label_entry] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists `"x"` >>
  simp[simplify_cfg_duplicate_label_fn_succ, relationTheory.RTC_REFL]
QED

Theorem simplify_cfg_duplicate_label_remove_unreachable[local]:
  remove_unreachable_blocks simplify_cfg_duplicate_label_func =
  simplify_cfg_duplicate_label_func
Proof
  mp_tac simplify_cfg_duplicate_label_reachable >> strip_tac >>
  gvs[remove_unreachable_blocks_def, simplify_cfg_duplicate_label_entry,
      simplify_cfg_duplicate_label_func_def,
      venomInstTheory.mk_raw_function_def]
QED

Theorem simplify_cfg_duplicate_label_fix_all_phis[local]:
  fix_all_phis simplify_cfg_duplicate_label_func =
  simplify_cfg_duplicate_label_func
Proof
  EVAL_TAC
QED


Definition simplify_cfg_duplicate_label_result_def:
  simplify_cfg_duplicate_label_result = mk_raw_function "f"
    [<| bb_label := "e";
        bb_instructions := [mk_inst 1 STOP [] []] |>]
End

Theorem simplify_cfg_duplicate_label_result_lookup[local]:
  lookup_block "e" simplify_cfg_duplicate_label_result.fn_blocks =
  SOME <| bb_label := "e";
          bb_instructions := [mk_inst 1 STOP [] []] |>
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_result_succs[local]:
  bb_succs <| bb_label := "e";
              bb_instructions := [mk_inst 1 STOP [] []] |> = []
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_result_succs_empty[local]:
  collapse_dfs_succs simplify_cfg_duplicate_label_result
    [("x","e")] ["e"] [] =
  (simplify_cfg_duplicate_label_result, [("x","e")], ["e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >> simp[]
QED

Theorem simplify_cfg_duplicate_label_result_collapse[local]:
  collapse_dfs simplify_cfg_duplicate_label_result
    [("x","e")] [] "e" =
  (simplify_cfg_duplicate_label_result, [("x","e")], ["e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_duplicate_label_result_lookup,
       simplify_cfg_duplicate_label_result_succs,
       try_bypass_def,
       simplify_cfg_duplicate_label_result_succs_empty]
QED

Theorem simplify_cfg_duplicate_label_initial_facts[local]:
  lookup_block "e" simplify_cfg_duplicate_label_func.fn_blocks =
    SOME <| bb_label := "e";
            bb_instructions := [mk_inst 0 JMP [Label "x"] []] |> /\
  bb_succs <| bb_label := "e";
              bb_instructions := [mk_inst 0 JMP [Label "x"] []] |> = ["x"] /\
  lookup_block "x" simplify_cfg_duplicate_label_func.fn_blocks =
    SOME <| bb_label := "x";
            bb_instructions := [mk_inst 1 STOP [] []] |> /\
  can_merge_blocks simplify_cfg_duplicate_label_func
    <| bb_label := "e";
       bb_instructions := [mk_inst 0 JMP [Label "x"] []] |>
    <| bb_label := "x";
       bb_instructions := [mk_inst 1 STOP [] []] |>
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_merge_step[local]:
  (simplify_cfg_duplicate_label_func with fn_blocks :=
    update_succ_phi_labels "x" "e"
      (replace_block "e"
        (merge_blocks
          <| bb_label := "e";
             bb_instructions := [mk_inst 0 JMP [Label "x"] []] |>
          <| bb_label := "x";
             bb_instructions := [mk_inst 1 STOP [] []] |>)
        (remove_block "x" simplify_cfg_duplicate_label_func.fn_blocks))
      (bb_succs
        (merge_blocks
          <| bb_label := "e";
             bb_instructions := [mk_inst 0 JMP [Label "x"] []] |>
          <| bb_label := "x";
             bb_instructions := [mk_inst 1 STOP [] []] |>))) =
  simplify_cfg_duplicate_label_result
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_collapse[local]:
  collapse_dfs simplify_cfg_duplicate_label_func [] [] "e" =
  (simplify_cfg_duplicate_label_result, [("x","e")], ["e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_duplicate_label_initial_facts] >>
  pure_once_rewrite_tac[simplify_cfg_duplicate_label_merge_step] >>
  simp[simplify_cfg_duplicate_label_result_collapse]
QED


Theorem simplify_cfg_duplicate_label_result_reachable[local]:
  reachable simplify_cfg_duplicate_label_result "e"
Proof
  simp[cfgTransformTheory.reachable_def,
       simplify_cfg_duplicate_label_result_def,
       venomInstTheory.mk_raw_function_def,
       venomInstTheory.fn_entry_label_def, venomInstTheory.entry_block_def,
       relationTheory.RTC_REFL]
QED

Theorem simplify_cfg_duplicate_label_result_stages[local]:
  subst_block_labels_fn [("x","e")] simplify_cfg_duplicate_label_result =
    simplify_cfg_duplicate_label_result /\
  remove_unreachable_blocks simplify_cfg_duplicate_label_result =
    simplify_cfg_duplicate_label_result /\
  fix_all_phis simplify_cfg_duplicate_label_result =
    simplify_cfg_duplicate_label_result
Proof
  conj_tac >- EVAL_TAC >>
  conj_tac
  >- (mp_tac simplify_cfg_duplicate_label_result_reachable >> strip_tac >>
      gvs[remove_unreachable_blocks_def,
          simplify_cfg_duplicate_label_result_def,
          venomInstTheory.mk_raw_function_def,
          venomInstTheory.fn_entry_label_def,
          venomInstTheory.entry_block_def]) >>
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_round[local]:
  simplify_cfg_round_with_labels simplify_cfg_duplicate_label_func =
  (simplify_cfg_duplicate_label_result, [("x","e")])
Proof
  pure_once_rewrite_tac[simplify_cfg_round_with_labels_def] >>
  simp[simplify_cfg_duplicate_label_entry,
       simplify_cfg_duplicate_label_remove_unreachable,
       simplify_cfg_duplicate_label_fix_all_phis,
       simplify_cfg_duplicate_label_collapse,
       simplify_cfg_duplicate_label_result_stages]
QED


Theorem simplify_cfg_duplicate_label_result_succs_empty_nil[local]:
  collapse_dfs_succs simplify_cfg_duplicate_label_result [] ["e"] [] =
  (simplify_cfg_duplicate_label_result, [], ["e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >> simp[]
QED

Theorem simplify_cfg_duplicate_label_result_collapse_nil[local]:
  collapse_dfs simplify_cfg_duplicate_label_result [] [] "e" =
  (simplify_cfg_duplicate_label_result, [], ["e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_duplicate_label_result_lookup,
       simplify_cfg_duplicate_label_result_succs,
       try_bypass_def,
       simplify_cfg_duplicate_label_result_succs_empty_nil]
QED

Theorem simplify_cfg_duplicate_label_result_entry[local]:
  fn_entry_label simplify_cfg_duplicate_label_result = SOME "e"
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_result_round[local]:
  simplify_cfg_round_with_labels simplify_cfg_duplicate_label_result =
  (simplify_cfg_duplicate_label_result, [])
Proof
  pure_once_rewrite_tac[simplify_cfg_round_with_labels_def] >>
  simp[simplify_cfg_duplicate_label_result_entry,
       simplify_cfg_duplicate_label_result_stages,
       simplify_cfg_duplicate_label_result_collapse_nil]
QED

Theorem simplify_cfg_duplicate_label_result_iter_suc[local]:
  !n. simplify_cfg_iter_with_labels (SUC n)
    simplify_cfg_duplicate_label_result =
  (simplify_cfg_duplicate_label_result, [])
Proof
  gen_tac >> pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >>
  simp[simplify_cfg_duplicate_label_result_round]
QED

Theorem simplify_cfg_duplicate_label_result_iter_two[local]:
  simplify_cfg_iter_with_labels 2 simplify_cfg_duplicate_label_result =
  (simplify_cfg_duplicate_label_result, [])
Proof
  qspec_then `1` mp_tac simplify_cfg_duplicate_label_result_iter_suc >>
  simp[]
QED

Theorem simplify_cfg_duplicate_label_blocks_changed[local]:
  simplify_cfg_duplicate_label_result.fn_blocks <>
  simplify_cfg_duplicate_label_func.fn_blocks
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_iter_suc_two[local]:
  simplify_cfg_iter_with_labels (SUC 2)
    simplify_cfg_duplicate_label_func =
  (simplify_cfg_duplicate_label_result, [("x","e")])
Proof
  pure_once_rewrite_tac[simplify_cfg_iter_with_labels_def] >>
  simp[simplify_cfg_duplicate_label_round,
       simplify_cfg_duplicate_label_blocks_changed,
       simplify_cfg_duplicate_label_result_iter_two]
QED

Theorem simplify_cfg_duplicate_label_length[local]:
  LENGTH simplify_cfg_duplicate_label_func.fn_blocks = 3
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_duplicate_label_fn_result[local]:
  simplify_cfg_fn_with_labels simplify_cfg_duplicate_label_func =
  (simplify_cfg_duplicate_label_result, [("x","e")])
Proof
  simp[simplify_cfg_fn_with_labels_def,
       simplify_cfg_duplicate_label_length] >>
  mp_tac simplify_cfg_duplicate_label_iter_suc_two >> simp[]
QED

Theorem simplify_cfg_duplicate_label_result_has_no_call[local]:
  ~MEM "callee"
    (simplify_cfg_fn_invoke_labels simplify_cfg_duplicate_label_result)
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_all_reachable_duplicate_label_counterexample:
  all_reachable simplify_cfg_duplicate_label_func /\
  MEM "callee" (simplify_cfg_fn_invoke_labels simplify_cfg_duplicate_label_func) /\
  ~MEM "callee"
    (simplify_cfg_fn_invoke_labels
      (FST (simplify_cfg_fn_with_labels simplify_cfg_duplicate_label_func)))
Proof
  simp[simplify_cfg_duplicate_label_all_reachable,
       simplify_cfg_duplicate_label_has_call,
       simplify_cfg_duplicate_label_fn_result,
       simplify_cfg_duplicate_label_result_has_no_call]
QED


(* Unique-label entry-cycle probe: collapsing c -> e removes the original
   entry block, so the final unreachable-block pass may lose the merged call.
   The duplicate terminators make the no-PHI instruction lists palindromic;
   fix_all_phis' accumulator-based PARTITION therefore leaves them unchanged. *)
Definition simplify_cfg_entry_cycle_e_def:
  simplify_cfg_entry_cycle_e =
    <| bb_label := "e";
       bb_instructions :=
         [mk_inst 1 JNZ [Label "d"; Label "c"] [];
          mk_inst 0 INVOKE [Label "callee"] [];
          mk_inst 1 JNZ [Label "d"; Label "c"] []] |>
End

Definition simplify_cfg_entry_cycle_d_def:
  simplify_cfg_entry_cycle_d =
    <| bb_label := "d";
       bb_instructions := [mk_inst 2 STOP [] []] |>
End

Definition simplify_cfg_entry_cycle_c_def:
  simplify_cfg_entry_cycle_c =
    <| bb_label := "c";
       bb_instructions :=
         [mk_inst 4 JMP [Label "e"] [];
          mk_inst 4 JMP [Label "e"] []] |>
End

Definition simplify_cfg_entry_cycle_func_def:
  simplify_cfg_entry_cycle_func = mk_raw_function "f"
    [simplify_cfg_entry_cycle_e;
     simplify_cfg_entry_cycle_d;
     simplify_cfg_entry_cycle_c]
End

Theorem simplify_cfg_entry_cycle_basic_facts[local]:
  ALL_DISTINCT (fn_labels simplify_cfg_entry_cycle_func) /\
  fn_entry_label simplify_cfg_entry_cycle_func = SOME "e" /\
  MEM "callee"
    (simplify_cfg_fn_invoke_labels simplify_cfg_entry_cycle_func) /\
  bb_succs simplify_cfg_entry_cycle_e = ["c";"d"] /\
  bb_succs simplify_cfg_entry_cycle_c = ["e"]
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_entry_cycle_edges[local]:
  fn_cfg_edge simplify_cfg_entry_cycle_func "e" "c" /\
  fn_cfg_edge simplify_cfg_entry_cycle_func "e" "d" /\
  fn_cfg_edge simplify_cfg_entry_cycle_func "c" "e"
Proof
  simp[venomWfTheory.fn_cfg_edge_def] >> rpt conj_tac
  >- (qexists `simplify_cfg_entry_cycle_e` >>
      simp[simplify_cfg_entry_cycle_func_def,
           simplify_cfg_entry_cycle_e_def,
           simplify_cfg_entry_cycle_d_def,
           simplify_cfg_entry_cycle_c_def,
           venomInstTheory.mk_raw_function_def,
           venomInstTheory.mk_inst_def, venomInstTheory.bb_succs_def,
           venomInstTheory.get_successors_def,
           venomInstTheory.is_terminator_def,
           venomStateTheory.get_label_def, listTheory.nub_def])
  >- (qexists `simplify_cfg_entry_cycle_e` >>
      simp[simplify_cfg_entry_cycle_func_def,
           simplify_cfg_entry_cycle_e_def,
           simplify_cfg_entry_cycle_d_def,
           simplify_cfg_entry_cycle_c_def,
           venomInstTheory.mk_raw_function_def,
           venomInstTheory.mk_inst_def, venomInstTheory.bb_succs_def,
           venomInstTheory.get_successors_def,
           venomInstTheory.is_terminator_def,
           venomStateTheory.get_label_def, listTheory.nub_def]) >>
  qexists `simplify_cfg_entry_cycle_c` >>
  simp[simplify_cfg_entry_cycle_func_def,
       simplify_cfg_entry_cycle_e_def,
       simplify_cfg_entry_cycle_d_def,
       simplify_cfg_entry_cycle_c_def,
       venomInstTheory.mk_raw_function_def,
       venomInstTheory.mk_inst_def, venomInstTheory.bb_succs_def,
       venomInstTheory.get_successors_def,
       venomInstTheory.is_terminator_def,
       venomStateTheory.get_label_def, listTheory.nub_def]
QED

Theorem simplify_cfg_entry_cycle_reachable_labels[local]:
  fn_reachable simplify_cfg_entry_cycle_func "e" /\
  fn_reachable simplify_cfg_entry_cycle_func "c" /\
  fn_reachable simplify_cfg_entry_cycle_func "d"
Proof
  rpt conj_tac
  >- simp[venomWfTheory.fn_reachable_def,
          simplify_cfg_entry_cycle_basic_facts, relationTheory.RTC_REFL]
  >- (simp[venomWfTheory.fn_reachable_def,
           simplify_cfg_entry_cycle_basic_facts] >>
      irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
      qexists `"c"` >>
      simp[simplify_cfg_entry_cycle_edges, relationTheory.RTC_REFL]) >>
  simp[venomWfTheory.fn_reachable_def,
       simplify_cfg_entry_cycle_basic_facts] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists `"d"` >>
  simp[simplify_cfg_entry_cycle_edges, relationTheory.RTC_REFL]
QED

Theorem simplify_cfg_entry_cycle_member_label[local]:
  MEM bb simplify_cfg_entry_cycle_func.fn_blocks ==>
  bb.bb_label = "e" \/ bb.bb_label = "d" \/ bb.bb_label = "c"
Proof
  simp[simplify_cfg_entry_cycle_func_def,
       simplify_cfg_entry_cycle_e_def,
       simplify_cfg_entry_cycle_d_def,
       simplify_cfg_entry_cycle_c_def,
       venomInstTheory.mk_raw_function_def] >>
  strip_tac >> gvs[]
QED

Theorem simplify_cfg_entry_cycle_all_reachable[local]:
  all_reachable simplify_cfg_entry_cycle_func
Proof
  rw[cfgWfTheory.all_reachable_def] >>
  drule simplify_cfg_entry_cycle_member_label >>
  strip_tac >> gvs[simplify_cfg_entry_cycle_reachable_labels]
QED

Theorem simplify_cfg_entry_cycle_reachable[local]:
  reachable simplify_cfg_entry_cycle_func "e" /\
  reachable simplify_cfg_entry_cycle_func "c" /\
  reachable simplify_cfg_entry_cycle_func "d"
Proof
  mp_tac simplify_cfg_entry_cycle_reachable_labels >>
  simp[GSYM fn_reachable_iff_reachable,
       simplify_cfg_entry_cycle_basic_facts]
QED

Theorem simplify_cfg_entry_cycle_preprocess[local]:
  remove_unreachable_blocks simplify_cfg_entry_cycle_func =
    simplify_cfg_entry_cycle_func /\
  fix_all_phis simplify_cfg_entry_cycle_func = simplify_cfg_entry_cycle_func
Proof
  conj_tac
  >- (mp_tac simplify_cfg_entry_cycle_reachable >> strip_tac >>
      gvs[remove_unreachable_blocks_def,
          simplify_cfg_entry_cycle_basic_facts,
          simplify_cfg_entry_cycle_func_def,
          simplify_cfg_entry_cycle_e_def,
          simplify_cfg_entry_cycle_d_def,
          simplify_cfg_entry_cycle_c_def,
          venomInstTheory.mk_raw_function_def]) >>
  EVAL_TAC
QED

Theorem simplify_cfg_entry_cycle_collapse_facts[local]:
  lookup_block "e" simplify_cfg_entry_cycle_func.fn_blocks =
    SOME simplify_cfg_entry_cycle_e /\
  lookup_block "c" simplify_cfg_entry_cycle_func.fn_blocks =
    SOME simplify_cfg_entry_cycle_c /\
  simplify_cfg_entry_cycle_e.bb_label = "e" /\
  bb_succs
    (merge_blocks simplify_cfg_entry_cycle_c simplify_cfg_entry_cycle_e) =
    ["c";"d"] /\
  can_merge_blocks simplify_cfg_entry_cycle_func
    simplify_cfg_entry_cycle_c simplify_cfg_entry_cycle_e /\
  try_bypass simplify_cfg_entry_cycle_func []
    simplify_cfg_entry_cycle_e ["c";"d"] =
    (simplify_cfg_entry_cycle_func,[],F)
Proof
  EVAL_TAC
QED

Definition simplify_cfg_entry_cycle_merged_c_def:
  simplify_cfg_entry_cycle_merged_c =
    <| bb_label := "c";
       bb_instructions :=
         [mk_inst 4 JMP [Label "e"] [];
          mk_inst 1 JNZ [Label "d"; Label "c"] [];
          mk_inst 0 INVOKE [Label "callee"] [];
          mk_inst 1 JNZ [Label "d"; Label "c"] []] |>
End

Definition simplify_cfg_entry_cycle_merged_def:
  simplify_cfg_entry_cycle_merged = mk_raw_function "f"
    [simplify_cfg_entry_cycle_d;
     simplify_cfg_entry_cycle_merged_c]
End

Theorem simplify_cfg_entry_cycle_merge_step[local]:
  (simplify_cfg_entry_cycle_func with fn_blocks :=
    update_succ_phi_labels "e" "c"
      (replace_block "c"
        (merge_blocks simplify_cfg_entry_cycle_c
                      simplify_cfg_entry_cycle_e)
        (remove_block "e" simplify_cfg_entry_cycle_func.fn_blocks))
      ["c";"d"]) = simplify_cfg_entry_cycle_merged
Proof
  EVAL_TAC
QED


Theorem simplify_cfg_entry_cycle_merged_facts[local]:
  fn_entry_label simplify_cfg_entry_cycle_merged = SOME "d" /\
  lookup_block "c" simplify_cfg_entry_cycle_merged.fn_blocks =
    SOME simplify_cfg_entry_cycle_merged_c /\
  lookup_block "d" simplify_cfg_entry_cycle_merged.fn_blocks =
    SOME simplify_cfg_entry_cycle_d /\
  bb_succs simplify_cfg_entry_cycle_merged_c = ["c";"d"] /\
  bb_succs simplify_cfg_entry_cycle_d = [] /\
  try_bypass simplify_cfg_entry_cycle_merged [("e","c")]
    simplify_cfg_entry_cycle_merged_c ["c";"d"] =
    (simplify_cfg_entry_cycle_merged,[("e","c")],F)
Proof
  EVAL_TAC
QED

Theorem simplify_cfg_entry_cycle_merged_c_seen[local]:
  collapse_dfs simplify_cfg_entry_cycle_merged [("e","c")]
    ["c";"e"] "c" =
    (simplify_cfg_entry_cycle_merged,[("e","c")],["c";"e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_merged_facts]
QED

Theorem simplify_cfg_entry_cycle_merged_d_new[local]:
  collapse_dfs simplify_cfg_entry_cycle_merged [("e","c")]
    ["c";"e"] "d" =
    (simplify_cfg_entry_cycle_merged,[("e","c")],["d";"c";"e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_merged_facts, try_bypass_def] >>
  pure_once_rewrite_tac[collapse_dfs_def] >> simp[]
QED

Theorem simplify_cfg_entry_cycle_merged_d_seen[local]:
  collapse_dfs simplify_cfg_entry_cycle_merged [("e","c")]
    ["d";"c";"e"] "d" =
    (simplify_cfg_entry_cycle_merged,[("e","c")],["d";"c";"e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_merged_facts, try_bypass_def] >>
  pure_once_rewrite_tac[collapse_dfs_def] >> simp[]
QED


Theorem simplify_cfg_entry_cycle_merged_succs[local]:
  collapse_dfs_succs simplify_cfg_entry_cycle_merged [("e","c")]
    ["c";"e"] ["c";"d"] =
    (simplify_cfg_entry_cycle_merged,[("e","c")],["d";"c";"e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_merged_c_seen] >>
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_merged_d_new] >>
  pure_once_rewrite_tac[collapse_dfs_def] >> simp[]
QED

Theorem simplify_cfg_entry_cycle_merged_c_new[local]:
  collapse_dfs simplify_cfg_entry_cycle_merged [("e","c")]
    ["e"] "c" =
    (simplify_cfg_entry_cycle_merged,[("e","c")],["d";"c";"e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_merged_facts,
       simplify_cfg_entry_cycle_merged_succs]
QED


Theorem simplify_cfg_entry_cycle_c_merge[local]:
  collapse_dfs simplify_cfg_entry_cycle_func [] ["e"] "c" =
    (simplify_cfg_entry_cycle_merged,[("e","c")],["d";"c";"e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_basic_facts,
       simplify_cfg_entry_cycle_collapse_facts] >>
  pure_once_rewrite_tac[simplify_cfg_entry_cycle_merge_step] >>
  simp[simplify_cfg_entry_cycle_merged_c_new]
QED

Theorem simplify_cfg_entry_cycle_initial_succs[local]:
  collapse_dfs_succs simplify_cfg_entry_cycle_func []
    ["e"] ["c";"d"] =
    (simplify_cfg_entry_cycle_merged,[("e","c")],["d";"c";"e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_c_merge] >>
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_merged_d_seen] >>
  pure_once_rewrite_tac[collapse_dfs_def] >> simp[]
QED

Theorem simplify_cfg_entry_cycle_collapse[local]:
  collapse_dfs simplify_cfg_entry_cycle_func [] [] "e" =
    (simplify_cfg_entry_cycle_merged,[("e","c")],["d";"c";"e"])
Proof
  pure_once_rewrite_tac[collapse_dfs_def] >>
  simp[simplify_cfg_entry_cycle_basic_facts,
       simplify_cfg_entry_cycle_collapse_facts,
       simplify_cfg_entry_cycle_initial_succs]
QED


Theorem simplify_cfg_entry_cycle_collapse_output[local]:
  fn_entry_label simplify_cfg_entry_cycle_merged = SOME "d" /\
  ~MEM "e" (fn_labels simplify_cfg_entry_cycle_merged) /\
  MEM "callee"
    (simplify_cfg_fn_invoke_labels simplify_cfg_entry_cycle_merged)
Proof
  EVAL_TAC
QED
