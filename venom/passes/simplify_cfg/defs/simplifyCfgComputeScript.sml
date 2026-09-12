(*
 * Executable equations for SimplifyCFG specifications.
 *
 * Relational reachability remains the source-level specification.  On the
 * well-formed domain accepted by the pipeline, cfg_analyze supplies the
 * equivalent finite decision procedure used by computeLib.
 *)

Theory simplifyCfgCompute
Ancestors
  simplifyCfgDefs cfgTransform cfgDefs cfgAnalysisProps cfgHelpers
  venomExecProps venomWf venomInst

Theorem fn_succ_cfg_analyze:
  !fn src dst.
    wf_function fn ==>
    (fn_succ fn src dst <=>
     MEM dst (cfg_succs_of (cfg_analyze fn) src))
Proof
  rpt strip_tac >>
  simp[fn_succ_def] >>
  eq_tac >> rpt strip_tac
  >- (`MEM bb fn.fn_blocks` by
        metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
      `bb.bb_label = src` by
        metis_tac[venomExecPropsTheory.lookup_block_label] >>
      `cfg_succs_of (cfg_analyze fn) bb.bb_label = bb_succs bb` by
        metis_tac[cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs] >>
      gvs[])
  >- (`MEM src (fn_labels fn)` by
        (CCONTR_TAC >>
         `fmap_lookup_list (build_succs fn.fn_blocks) src = []` by
           (irule cfgHelpersTheory.cfg_succs_of_not_in_labels >>
            gvs[fn_labels_def]) >>
         gvs[cfgHelpersTheory.cfg_analyze_succs]) >>
      qpat_x_assum `MEM src (fn_labels fn)` mp_tac >>
      simp[fn_labels_def, listTheory.MEM_MAP] >>
      disch_then (qx_choose_then `bb` strip_assume_tac) >>
      `lookup_block src fn.fn_blocks = SOME bb` by
        (irule venomExecPropsTheory.MEM_lookup_block >>
         gvs[wf_function_def, fn_labels_def]) >>
      `cfg_succs_of (cfg_analyze fn) src = bb_succs bb` by
        metis_tac[cfgAnalysisPropsTheory.cfg_analyze_preserves_bb_succs] >>
      qexists_tac `bb` >> gvs[])
QED

Theorem reachable_cfg_analyze:
  !fn lbl.
    wf_function fn ==>
    (reachable fn lbl <=> cfg_reachable_of (cfg_analyze fn) lbl)
Proof
  rpt strip_tac >>
  `fn.fn_blocks <> []` by
    gvs[wf_function_def, fn_has_entry_def] >>
  `?bb. entry_block fn = SOME bb` by
    (Cases_on `fn.fn_blocks` >> gvs[entry_block_def]) >>
  `fn_entry_label fn = SOME bb.bb_label` by
    simp[fn_entry_label_def] >>
  `reachable fn lbl <=> RTC (fn_succ fn) bb.bb_label lbl` by
    simp[reachable_def] >>
  `cfg_reachable_of (cfg_analyze fn) lbl <=>
   RTC (λsrc dst. MEM dst (cfg_succs_of (cfg_analyze fn) src))
       bb.bb_label lbl` by
    (`cfg_reachable_of (cfg_analyze fn) lbl <=>
      cfg_path (cfg_analyze fn) bb.bb_label lbl` by
       metis_tac[cfgAnalysisPropsTheory.cfg_analyze_semantic_reachability] >>
     gvs[cfg_path_def]) >>
  `fn_succ fn =
   (λsrc dst. MEM dst (cfg_succs_of (cfg_analyze fn) src))` by
    simp[FUN_EQ_THM, fn_succ_cfg_analyze] >>
  gvs[]
QED

Theorem filter_reachable_cfg_analyze:
  !fn.
    wf_function fn ==>
    FILTER (λbb. reachable fn bb.bb_label) fn.fn_blocks =
    FILTER (λbb. cfg_reachable_of (cfg_analyze fn) bb.bb_label)
      fn.fn_blocks
Proof
  rpt strip_tac >>
  `(λbb. reachable fn bb.bb_label) =
   (λbb. cfg_reachable_of (cfg_analyze fn) bb.bb_label)` by
    simp[FUN_EQ_THM, reachable_cfg_analyze] >>
  gvs[]
QED

Theorem remove_unreachable_blocks_compute[compute]:
  remove_unreachable_blocks fn =
    if wf_function fn then
      case fn_entry_label fn of
        NONE => fn
      | SOME entry =>
          let cfg = cfg_analyze fn in
            fn with fn_blocks :=
              FILTER (λbb. cfg_reachable_of cfg bb.bb_label) fn.fn_blocks
    else
      case fn_entry_label fn of
        NONE => fn
      | SOME entry =>
          fn with fn_blocks :=
            FILTER (λbb. reachable fn bb.bb_label) fn.fn_blocks
Proof
  Cases_on `wf_function fn` >>
  Cases_on `fn_entry_label fn` >>
  simp[remove_unreachable_blocks_def, filter_reachable_cfg_analyze]
QED

val _ = export_theory();
