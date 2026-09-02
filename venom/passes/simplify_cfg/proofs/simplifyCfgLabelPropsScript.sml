Theory simplifyCfgLabelProps
Ancestors
  simplifyCfgDefs cfgTransformProps unitLabelMap
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
