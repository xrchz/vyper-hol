(* Properties of the conservative FMP reclaim abstraction. *)

Theory fmpReclaimProps
Ancestors
  fmpReclaimDefs
  fmpAnalysisProps

Theorem analyze_fmp_reclaims_ready:
  fmp_info_valid ctx infos /\ MEM fn ctx.ctx_functions /\
  wf_function fn /\ fn_inst_wf fn /\ fn.fn_fmp_signature = NONE /\
  fmp_reclaim_states fn = SOME states /\
  fmp_candidate_plan infos ctx fn states = plan /\
  fmp_reclaim_plan_ok infos ctx fn plan ==>
  analyze_fmp_reclaims infos ctx fn = SOME plan
Proof
  simp[analyze_fmp_reclaims_def] >> metis_tac[]
QED


Theorem analyze_fmp_reclaims_checked:
  analyze_fmp_reclaims infos ctx fn = SOME plan ==>
  fmp_info_valid ctx infos /\
  MEM fn ctx.ctx_functions /\
  fmp_reclaim_plan_ok infos ctx fn plan
Proof
  simp[analyze_fmp_reclaims_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_reclaim_plan_ok_lookup:
  fmp_reclaim_plan_ok infos ctx fn plan /\
  FLOOKUP plan point = SOME target ==>
  fmp_reclaim_entry_ok infos ctx fn point target
Proof
  simp[fmp_reclaim_plan_ok_def] >> metis_tac[]
QED

Theorem analyze_fmp_reclaims_target_checked:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  FLOOKUP plan point = SOME target ==>
  ?bb def_lbl def_i dalloca.
    lookup_block (FST point) fn.fn_blocks = SOME bb /\
    SND point <= LENGTH bb.bb_instructions /\
    fmp_find_dalloca target fn.fn_blocks =
      SOME (def_lbl,def_i,dalloca) /\
    dalloca.inst_opcode = DALLOCA /\
    dalloca.inst_outputs = [target] /\
    fmp_definition_dominates fn def_lbl def_i point /\
    EVERY
      (\v. ~MEM v
        (live_vars_at (liveness_analyze fn) (FST point) (SND point)))
      (fmp_derived_vars fn target) /\
    ~fmp_target_pinned fn target /\
    EVERY
      (\cap. ~fmp_capture_veto fn (liveness_analyze fn) point cap)
      (FLAT (MAP fmp_getfmp_outputs (fn_insts fn)))
Proof
  rpt strip_tac >>
  drule analyze_fmp_reclaims_checked >> strip_tac >>
  drule fmp_reclaim_plan_ok_lookup >>
  disch_then drule >>
  simp[fmp_reclaim_entry_ok_def, fmp_restore_target_ok_def,
       fmp_point_well_located_def] >>
  metis_tac[]
QED

Theorem analyze_fmp_reclaims_deterministic:
  analyze_fmp_reclaims infos ctx fn = SOME p1 /\
  analyze_fmp_reclaims infos ctx fn = SOME p2 ==>
  p1 = p2
Proof
  rpt strip_tac >> gvs[]
QED

val _ = export_theory();
