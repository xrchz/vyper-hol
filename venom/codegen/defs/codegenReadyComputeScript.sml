(*
 * Executable counterparts for the relational code-generation readiness guards.
 *
 * TOP-LEVEL:
 *   fn_dominates_cfg_analyze       — computed dominators match path dominance
 *   def_dominates_uses_compute     — finite executable SSA dominance check
 *)

Theory codegenReadyCompute
Ancestors
  stackPlanGen dominatorProofs dominatorDefs cfgAnalysisProps
  simplifyCfgCompute venomExecProps venomWf venomInst cfgTransform cfgDefs
  passSharedDefs fcgDefs relation rich_list

(* ===== Relational / computed CFG bridges ===== *)

Theorem fn_cfg_edge_iff_fn_succ:
  wf_function fn ==>
  (fn_cfg_edge fn src dst <=> fn_succ fn src dst)
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by gvs[wf_function_def] >>
  simp[fn_cfg_edge_def, fn_succ_def] >>
  eq_tac >> rpt strip_tac
  >- (qexists_tac `bb` >> simp[] >>
      irule venomExecPropsTheory.MEM_lookup_block >>
      simp[GSYM fn_labels_def])
  >> qexists_tac `bb` >>
  metis_tac[venomExecPropsTheory.lookup_block_MEM,
            venomExecPropsTheory.lookup_block_label]
QED

Theorem fn_cfg_edge_cfg_analyze:
  wf_function fn ==>
  (fn_cfg_edge fn src dst <=>
   MEM dst (cfg_succs_of (cfg_analyze fn) src))
Proof
  metis_tac[fn_cfg_edge_iff_fn_succ,
            simplifyCfgComputeTheory.fn_succ_cfg_analyze]
QED

Theorem fn_reachable_reachable:
  wf_function fn ==>
  (fn_reachable fn lbl <=> reachable fn lbl)
Proof
  rpt strip_tac >>
  `fn_cfg_edge fn = fn_succ fn` by
    simp[FUN_EQ_THM, fn_cfg_edge_iff_fn_succ] >>
  simp[fn_reachable_def, reachable_def]
QED

Theorem fn_reachable_cfg_analyze:
  wf_function fn ==>
  (fn_reachable fn lbl <=>
   cfg_reachable_of (cfg_analyze fn) lbl)
Proof
  metis_tac[fn_reachable_reachable,
            simplifyCfgComputeTheory.reachable_cfg_analyze]
QED

(* Convert between the list path representation used by venomWf and the LRC
 * representation used by the dominator correctness proof. *)
Theorem is_fn_path_to_lrc:
  !fn path.
    path <> [] /\ is_fn_path fn path ==>
    LRC (fn_cfg_edge fn) (FRONT path) (HD path) (LAST path)
Proof
  gen_tac >> Induct_on `path` >> simp[] >>
  Cases_on `path` >>
  simp[is_fn_path_def, listTheory.LRC_def, listTheory.FRONT_CONS] >>
  rpt strip_tac >> qexists_tac `h` >> simp[] >>
  qpat_x_assum `_ ==> LRC _ _ _ _` mp_tac >> simp[]
QED

Theorem lrc_to_is_fn_path:
  !fn ls x y.
    LRC (fn_cfg_edge fn) ls x y ==>
    is_fn_path fn (ls ++ [y]) /\ HD (ls ++ [y]) = x
Proof
  gen_tac >> Induct_on `ls`
  >- simp[listTheory.LRC_def, is_fn_path_def] >>
  rpt gen_tac >>
  simp[listTheory.LRC_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `ls` >>
  gvs[is_fn_path_def, listTheory.LRC_def]
QED

Theorem is_fn_path_rtc_compute:
  !fn path. is_fn_path fn path /\ path <> [] ==>
    (fn_cfg_edge fn)^* (HD path) (LAST path)
Proof
  Induct_on `path` >> simp[is_fn_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[is_fn_path_def] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists_tac `h'` >> simp[]
QED

Theorem rtc_to_fn_path_compute:
  !fn x y. (fn_cfg_edge fn)^* x y ==>
    ?path. is_fn_path fn path /\ path <> [] /\
           HD path = x /\ LAST path = y
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[]
  >- (qexists_tac `[x]` >> simp[is_fn_path_def])
  >- (qexists_tac `x::path` >> Cases_on `path` >> gvs[is_fn_path_def])
QED

Theorem is_fn_path_prefix_compute:
  !fn path d. is_fn_path fn path /\ MEM d path ==>
    ?pre. is_fn_path fn (pre ++ [d]) /\ HD (pre ++ [d]) = HD path
Proof
  Induct_on `path` >> simp[] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `[]` >> simp[is_fn_path_def])
  >- (Cases_on `path` >> gvs[is_fn_path_def]
      >- (qexists_tac `[h]` >> simp[is_fn_path_def])
      >- (first_x_assum (qspecl_then [`fn`, `d`] mp_tac) >> simp[] >>
          strip_tac >> qexists_tac `h::pre` >>
          Cases_on `pre` >> gvs[is_fn_path_def]))
QED

Theorem fn_dominates_dom_reachable_compute:
  !fn d n. fn_dominates fn d n ==> fn_reachable fn d
Proof
  rw[fn_dominates_def, fn_reachable_def] >>
  qexists_tac `entry` >> simp[] >>
  drule rtc_to_fn_path_compute >> strip_tac >>
  `MEM d path` by (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all is_fn_path_prefix_compute >> strip_tac >>
  drule is_fn_path_rtc_compute >>
  simp[listTheory.APPEND_eq_NIL]
QED

(* The executable dominator analysis is extensionally equal to the original
 * all-paths definition on well-formed functions. *)
Theorem fn_dominates_cfg_analyze:
  !fn d n.
    wf_function fn ==>
    (fn_dominates fn d n <=>
     cfg_reachable_of (cfg_analyze fn) n /\
     dominates (dom_analyze (cfg_analyze fn) fn) d n)
Proof
  rpt strip_tac >>
  `?entry_bb. entry_block fn = SOME entry_bb` by
    (fs[wf_function_def, fn_has_entry_def, entry_block_def] >>
     Cases_on `fn.fn_blocks` >> fs[]) >>
  `fn_entry_label fn = SOME entry_bb.bb_label` by
    simp[fn_entry_label_def] >>
  `fn_cfg_edge fn =
   (λa b. MEM b (cfg_succs_of (cfg_analyze fn) a))` by
    simp[FUN_EQ_THM, fn_cfg_edge_cfg_analyze] >>
  eq_tac
  >- (strip_tac >>
      `cfg_reachable_of (cfg_analyze fn) n` by
        metis_tac[fn_reachable_cfg_analyze, fn_dominates_def] >>
      conj_tac >- simp[] >>
      `fn_reachable fn d` by
        metis_tac[fn_dominates_dom_reachable_compute] >>
      `cfg_reachable_of (cfg_analyze fn) d` by
        metis_tac[fn_reachable_cfg_analyze] >>
      `MEM d (fn_labels fn)` by
        metis_tac[cfgAnalysisPropsTheory.cfg_analyze_reachable_in_labels] >>
      simp[dominatorDefsTheory.dominates_def] >>
      irule dominatorProofsTheory.on_every_path_dom >>
      simp[] >>
      rpt strip_tac >>
      `LRC (fn_cfg_edge fn) ls entry_bb.bb_label n` by fs[] >>
      drule lrc_to_is_fn_path >> strip_tac >>
      fs[fn_dominates_def] >>
      first_x_assum (qspec_then `ls ++ [n]` mp_tac) >>
      simp[] >> metis_tac[])
  >- (strip_tac >>
      simp[fn_dominates_def] >>
      conj_tac
      >- metis_tac[fn_reachable_cfg_analyze] >>
      rpt strip_tac >>
      mp_tac (Q.SPECL [`fn`, `path`] is_fn_path_to_lrc) >>
      simp[] >> strip_tac >>
      `LRC (λa b. MEM b (cfg_succs_of (cfg_analyze fn) a))
           (FRONT path) entry_bb.bb_label n` by metis_tac[] >>
      `d = n \/ MEM d (FRONT path)` by
        (mp_tac (Q.SPECL [`fn`, `entry_bb`, `FRONT path`, `n`]
                   dominatorProofsTheory.dom_on_every_path) >>
         simp[] >> strip_tac >>
         first_x_assum (qspec_then `d` mp_tac) >>
         fs[dominatorDefsTheory.dominates_def]) >>
      Cases_on `path` >>
      gvs[rich_listTheory.MEM_LAST, rich_listTheory.MEM_FRONT])
QED

(* ===== Finite def-dominates-uses checker ===== *)

Definition def_dominates_uses_exec_def:
  def_dominates_uses_exec fn <=>
    let cfg = cfg_analyze fn in
    let dom = dom_analyze cfg fn in
      EVERY
        (λbb.
          EVERY
            (λinst.
              EVERY
                (λop.
                  case op of
                    Var v =>
                      EXISTS
                        (λdef_bb.
                          EXISTS
                            (λdef_inst.
                              MEM v def_inst.inst_outputs /\
                              cfg_reachable_of cfg bb.bb_label /\
                              dominates dom def_bb.bb_label bb.bb_label /\
                              (def_bb = bb ==>
                               EXISTS
                                 (λi.
                                   EXISTS
                                     (λj. i < j /\
                                          EL i bb.bb_instructions = def_inst /\
                                          EL j bb.bb_instructions = inst)
                                     (GENLIST I (LENGTH bb.bb_instructions)))
                                 (GENLIST I (LENGTH bb.bb_instructions))))
                            def_bb.bb_instructions)
                        fn.fn_blocks
                  | _ => T)
                inst.inst_operands)
            bb.bb_instructions)
        fn.fn_blocks
End

Theorem def_dominates_uses_exec_correct:
  wf_function fn ==>
  (def_dominates_uses fn <=> def_dominates_uses_exec fn)
Proof
  strip_tac >>
  simp[def_dominates_uses_def, def_dominates_uses_exec_def,
       listTheory.EVERY_MEM, listTheory.EXISTS_MEM,
       listTheory.EXISTS_GENLIST] >>
  eq_tac
  >- (rpt strip_tac >> Cases_on `op` >> simp[] >>
      qpat_x_assum `!bb inst v. _`
        (qspecl_then [`bb`, `inst`, `s`] mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `def_bb` >> simp[] >>
      qexists_tac `def_inst` >> simp[] >>
      rpt conj_tac
      >- metis_tac[fn_dominates_cfg_analyze]
      >- metis_tac[fn_dominates_cfg_analyze]
      >- (strip_tac >>
          qpat_x_assum `def_bb = bb ==> _` mp_tac >> simp[] >>
          strip_tac >>
          qexists_tac `i` >> conj_tac >- decide_tac >>
          qexists_tac `j` >> simp[]))
  >- (rpt strip_tac >>
      qpat_x_assum `!bb. _` (qspec_then `bb` mp_tac) >> simp[] >>
      disch_then (qspec_then `inst` mp_tac) >> simp[] >>
      disch_then (qspec_then `Var v` mp_tac) >> simp[] >>
      strip_tac >>
      qexists_tac `def_bb` >> simp[] >>
      qexists_tac `def_inst` >> simp[] >>
      conj_tac
      >- metis_tac[fn_dominates_cfg_analyze] >>
      strip_tac >>
      qpat_x_assum `def_bb = bb ==> _` mp_tac >> simp[] >>
      strip_tac >>
      qexistsl_tac [`i`, `i'`] >> simp[])
QED

(* The malformed fallback is deliberately the original specification.  This
 * keeps the theorem unconditional while computeLib takes the finite branch in
 * codegen_ready_fn, where wf_function is checked before this conjunct. *)
Theorem def_dominates_uses_compute[compute]:
  def_dominates_uses fn <=>
    if wf_function fn then
      def_dominates_uses_exec fn
    else
      !bb inst v.
        MEM bb fn.fn_blocks /\
        MEM inst bb.bb_instructions /\
        MEM (Var v) inst.inst_operands ==>
        ?def_bb def_inst.
          MEM def_bb fn.fn_blocks /\
          MEM def_inst def_bb.bb_instructions /\
          MEM v def_inst.inst_outputs /\
          fn_dominates fn def_bb.bb_label bb.bb_label /\
          (def_bb = bb ==>
           ?i j.
             i < j /\ j < LENGTH bb.bb_instructions /\
             EL i bb.bb_instructions = def_inst /\
             EL j bb.bb_instructions = inst)
Proof
  Cases_on `wf_function fn`
  >- simp[def_dominates_uses_exec_correct]
  >- simp[def_dominates_uses_def]
QED
