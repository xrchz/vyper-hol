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
