(*
 * Memory Copy Elision — Correctness Statement
 *
 * States the main correctness theorem for the copy-elision pass:
 * running copy_elision_function produces an observationally equivalent
 * result whenever the preconditions (well-formedness, SSA, sound
 * analysis results) hold.
 *)

Theory memoryCopyElisionCorrectness
Ancestors
  memoryCopyElisionProofs memoryCopyElisionDefs
  passSimulationDefs passSimulationProps passSharedDefs passSharedProps
  venomWf venomInst venomEffects venomMemDefs basePtrProps
  list rich_list indexedLists
Libs
  pairLib BasicProvers

Theorem copy_elision_function_correct:
  !fuel ctx fn s.
    let cfg = cfg_analyze fn in
    let dfg = dfg_build_function fn in
    let bp = bp_analyze cfg fn in
    wf_function fn /\
    fn_inst_wf fn /\
    wf_ssa fn /\
    s.vs_inst_idx = 0 /\
    fn_entry_label fn = SOME s.vs_current_bb /\
    dfg_assigns_sound dfg s /\
    bp_ptr_sound bp s /\
    alloca_inv s /\
    allocas_in_word s /\
    bp_ptrs_bounded bp fn s /\
    bp_assigns_stable bp dfg /\
    (!bb s0 s_phi.
       MEM bb fn.fn_blocks /\
       MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
       eval_phis s0 bb.bb_instructions = OK s_phi /\
       dfg_assigns_sound dfg s0 ==>
       dfg_assigns_sound dfg s_phi) /\
    (!fuel' run_ctx bb inst s0 s1.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       inst_wf inst /\
       dfg_assigns_sound dfg (s0 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s0 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
       allocas_in_word (s0 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s0 with vs_inst_idx := 0) /\
       step_inst fuel' run_ctx inst s0 = OK s1 ==>
       dfg_assigns_sound dfg (s1 with vs_inst_idx := 0) /\
       bp_ptr_sound bp (s1 with vs_inst_idx := 0) /\
       allocas_non_overlapping (s1 with vs_inst_idx := 0) /\
       allocas_in_word (s1 with vs_inst_idx := 0) /\
       bp_ptrs_bounded bp fn (s1 with vs_inst_idx := 0)) /\
    LENGTH s.vs_memory < dimword (:256) ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (copy_elision_function fn) s)
Proof
  ACCEPT_TAC copy_elision_function_correct_proof
QED

(* ================================================================== *)
(* Part 1: load_store_step properties                                 *)
(* ================================================================== *)

(* load_store_step returns either the instruction unchanged or mk_nop_inst *)
Triviality lse_step_inst_or_nop:
  !aliases bp uc lf inst.
    SND (load_store_step aliases bp uc (lf, inst)) = inst \/
    SND (load_store_step aliases bp uc (lf, inst)) = mk_nop_inst inst
Proof
  rw[load_store_step_def, LET_THM] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* If an instruction is none of load/store/copy/volatile-memory-writer,
   load_store_step returns it unchanged *)
Triviality lse_step_identity:
  !aliases bp uc lf inst.
    ~is_load_fact_opcode inst.inst_opcode /\
    ~is_store_opcode inst.inst_opcode /\
    ~is_copy_opcode inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    SND (load_store_step aliases bp uc (lf, inst)) = inst
Proof
  rw[load_store_step_def, LET_THM]
QED

(* Terminators are always emitted unchanged, even when they update load facts. *)
Triviality terminator_lse_step_identity:
  !aliases bp uc lf inst.
    is_terminator inst.inst_opcode ==>
    SND (load_store_step aliases bp uc (lf, inst)) = inst
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def, load_store_step_def, LET_THM,
    is_load_fact_opcode_def, is_store_opcode_def, is_copy_opcode_def,
    write_effects_def, empty_effects_def]
QED

(* PHI satisfies the non-modifiable condition *)
Triviality phi_not_modifiable:
  ~is_load_fact_opcode PHI /\ ~is_store_opcode PHI /\
  ~is_copy_opcode PHI /\ Eff_MEMORY NOTIN write_effects PHI
Proof
  EVAL_TAC
QED

(* ================================================================== *)
(* Part 2: Combined FOLDL invariant                                   *)
(* ================================================================== *)

(* Append-FOLDL preserves prefix elements *)
Triviality foldl_append_prefix:
  !insts lf0 acc0 aliases bp uc lf' acc'.
    FOLDL (\(lf, acc) inst.
      let (lf', inst') = load_store_step aliases bp uc (lf, inst) in
      (lf', acc ++ [inst'])) (lf0, acc0) insts = (lf', acc') ==>
    !i. i < LENGTH acc0 ==> EL i acc' = EL i acc0
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  strip_tac >> rpt strip_tac >>
  first_x_assum drule >>
  disch_then (qspec_then `i` mp_tac) >>
  simp[EL_APPEND1]
QED

(* FOLDL length invariant *)
Triviality lse_foldl_length:
  !insts lf0 acc0 aliases bp uc lf' acc'.
    FOLDL (\(lf, acc) inst.
      let (lf', inst') = load_store_step aliases bp uc (lf, inst) in
      (lf', acc ++ [inst'])) (lf0, acc0) insts = (lf', acc') ==>
    LENGTH acc' = LENGTH acc0 + LENGTH insts
Proof
  Induct >> simp[] >> rpt gen_tac >>
  simp[LET_THM] >> pairarg_tac >> gvs[] >>
  strip_tac >> first_x_assum drule >> simp[]
QED

Triviality lse_foldl_el:
  !insts lf0 acc0 aliases bp uc lf' acc' i.
    FOLDL (\(lf, acc) inst.
      let (lf', inst') = load_store_step aliases bp uc (lf, inst) in
      (lf', acc ++ [inst'])) (lf0, acc0) insts = (lf', acc') ==>
    LENGTH acc0 <= i ==> i < LENGTH acc' ==>
    let inst' = EL i acc' in
    let orig = EL (i - LENGTH acc0) insts in
    inst'.inst_id = orig.inst_id /\
    (inst'.inst_outputs = orig.inst_outputs \/ inst'.inst_outputs = []) /\
    (inst'.inst_opcode = orig.inst_opcode \/ inst'.inst_opcode = NOP) /\
    (~is_load_fact_opcode orig.inst_opcode /\
     ~is_store_opcode orig.inst_opcode /\
     ~is_copy_opcode orig.inst_opcode /\
     Eff_MEMORY NOTIN write_effects orig.inst_opcode ==>
     inst' = orig) /\
    (is_terminator orig.inst_opcode ==> inst' = orig)
Proof
  Induct >> simp[LET_THM]
  >> rpt gen_tac >> simp[LET_THM] >> pairarg_tac >> gvs[]
  >> ntac 3 strip_tac
  >> Cases_on `i = LENGTH acc0`
  >- suspend "i_eq"
  >> suspend "i_neq"
QED

Resume lse_foldl_el[i_eq]:
  (* i = LENGTH acc0, so (h::insts)[0] = h, acc'[i] = inst' *)
  gvs[] >>
  (* acc'[LENGTH acc0] = (acc0 ++ [inst'])[LENGTH acc0] = inst' *)
  drule (REWRITE_RULE [LET_THM] foldl_append_prefix) >>
  disch_then (qspec_then `LENGTH acc0` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Rewrite asm: (acc0 ++ [inst'])[LENGTH acc0] = inst' *)
  qpat_x_assum `_ = EL _ (acc0 ++ [inst'])` mp_tac >>
  simp[EL_APPEND_EQN] >> strip_tac >> gvs[] >>
  (* inst' is either h or mk_nop_inst h *)
  qspecl_then [`aliases`,`bp`,`uc`,`lf0`,`h`] strip_assume_tac
    lse_step_inst_or_nop >>
  gvs[mk_nop_inst_def] >>
  conj_tac
  >- (strip_tac >>
      drule lse_step_identity >> simp[] >>
      disch_then (qspecl_then [`aliases`,`bp`,`uc`,`lf0`] mp_tac) >>
      simp[])
  >> strip_tac >>
  drule terminator_lse_step_identity >>
  disch_then (qspecl_then [`aliases`,`bp`,`uc`,`lf0`] mp_tac) >>
  simp[]
QED

Resume lse_foldl_el[i_neq]:
  first_x_assum (drule_then (qspec_then `i` mp_tac)) >>
  simp[] >>
  `i - LENGTH acc0 = SUC (i - (LENGTH acc0 + 1))` by simp[] >>
  pop_assum (fn th => rewrite_tac [th]) >> simp[]
QED

Finalise lse_foldl_el

Triviality lse_foldl_combined:
  !insts lf0 acc0 aliases bp uc lf' acc'.
    FOLDL (\(lf, acc) inst.
      let (lf', inst') = load_store_step aliases bp uc (lf, inst) in
      (lf', acc ++ [inst'])) (lf0, acc0) insts = (lf', acc') ==>
    LENGTH acc' = LENGTH acc0 + LENGTH insts /\
    (!i. LENGTH acc0 <= i /\ i < LENGTH acc' ==>
       let inst' = EL i acc' in
       let orig = EL (i - LENGTH acc0) insts in
       inst'.inst_id = orig.inst_id /\
       (inst'.inst_outputs = orig.inst_outputs \/ inst'.inst_outputs = []) /\
       (inst'.inst_opcode = orig.inst_opcode \/ inst'.inst_opcode = NOP) /\
       (~is_load_fact_opcode orig.inst_opcode /\
        ~is_store_opcode orig.inst_opcode /\
        ~is_copy_opcode orig.inst_opcode /\
        Eff_MEMORY NOTIN write_effects orig.inst_opcode ==>
        inst' = orig) /\
       (is_terminator orig.inst_opcode ==> inst' = orig))
Proof
  rpt strip_tac
  >- (drule lse_foldl_length >> simp[])
  >> (simp[LET_THM] >> drule lse_foldl_el >> simp[LET_THM])
QED

(* ================================================================== *)
(* Part 3: load_store_elim_block properties (derived from combined)   *)
(* ================================================================== *)

Triviality lse_block_label:
  !aliases bp uc bb.
    (load_store_elim_block aliases bp uc bb).bb_label = bb.bb_label
Proof
  rw[load_store_elim_block_def, LET_THM] >> pairarg_tac >> gvs[]
QED

Triviality lse_block_length:
  !aliases bp uc bb.
    LENGTH (load_store_elim_block aliases bp uc bb).bb_instructions =
    LENGTH bb.bb_instructions
Proof
  rw[load_store_elim_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule (REWRITE_RULE [LET_THM] lse_foldl_combined) >> simp[]
QED

(* Per-instruction trace: each output instruction traces to original *)
Triviality lse_block_trace:
  !aliases bp uc bb i.
    i < LENGTH (load_store_elim_block aliases bp uc bb).bb_instructions ==>
    let inst = EL i (load_store_elim_block aliases bp uc bb).bb_instructions in
    let orig = EL i bb.bb_instructions in
    inst.inst_id = orig.inst_id /\
    (inst.inst_outputs = orig.inst_outputs \/ inst.inst_outputs = []) /\
    (inst.inst_opcode = orig.inst_opcode \/ inst.inst_opcode = NOP) /\
    (~is_load_fact_opcode orig.inst_opcode /\
     ~is_store_opcode orig.inst_opcode /\
     ~is_copy_opcode orig.inst_opcode /\
     Eff_MEMORY NOTIN write_effects orig.inst_opcode ==>
     inst = orig) /\
    (is_terminator orig.inst_opcode ==> inst = orig)
Proof
  rpt strip_tac >>
  gvs[load_store_elim_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  drule (REWRITE_RULE [LET_THM] lse_foldl_combined) >> simp[LET_THM]
QED

(* PHI instructions pass through unchanged *)
Triviality lse_block_phi_preserved:
  !aliases bp uc bb i.
    i < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = PHI ==>
    EL i (load_store_elim_block aliases bp uc bb).bb_instructions =
    EL i bb.bb_instructions
Proof
  rpt strip_tac >>
  qspecl_then [`aliases`,`bp`,`uc`,`bb`,`i`] mp_tac
    (REWRITE_RULE [LET_THM] lse_block_trace) >>
  simp[lse_block_length] >> strip_tac >>
  qpat_x_assum `~is_load_fact_opcode _ /\ _ ==> _` irule >>
  simp[phi_not_modifiable]
QED

(* If the transformed instruction has opcode PHI, the original did too *)
Triviality lse_block_phi_reverse:
  !aliases bp uc bb i.
    i < LENGTH bb.bb_instructions /\
    (EL i (load_store_elim_block aliases bp uc bb).bb_instructions).inst_opcode
      = PHI ==>
    (EL i bb.bb_instructions).inst_opcode = PHI
Proof
  rpt strip_tac >>
  qspecl_then [`aliases`,`bp`,`uc`,`bb`,`i`] mp_tac
    (REWRITE_RULE [LET_THM] lse_block_trace) >>
  simp[lse_block_length] >> strip_tac >> gvs[]
QED

(* Terminators pass through unchanged *)
Triviality lse_block_last_eq:
  !aliases bp uc bb.
    bb_well_formed bb ==>
    LAST (load_store_elim_block aliases bp uc bb).bb_instructions =
    LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  qabbrev_tac `bb' = load_store_elim_block aliases bp uc bb` >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    simp[Abbr `bb'`, lse_block_length] >>
  `bb'.bb_instructions <> []` by
    (Cases_on `bb'.bb_instructions` >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  simp[LAST_EL] >>
  `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  qspecl_then [`aliases`,`bp`,`uc`,`bb`,
    `PRE (LENGTH bb.bb_instructions)`] mp_tac
    (REWRITE_RULE [LET_THM] lse_block_trace) >>
  simp[Abbr `bb'`, lse_block_length] >>
  `is_terminator (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode` by
    (gvs[bb_well_formed_def, LAST_EL]) >>
  simp[]
QED

Triviality lse_block_wf:
  !aliases bp uc bb.
    bb_well_formed bb ==>
    bb_well_formed (load_store_elim_block aliases bp uc bb)
Proof
  rpt strip_tac >>
  qabbrev_tac `bb' = load_store_elim_block aliases bp uc bb` >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    simp[Abbr `bb'`, lse_block_length] >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  simp[bb_well_formed_def] >> rpt conj_tac
  (* instructions <> [] *)
  >- (Cases_on `bb.bb_instructions` >> Cases_on `bb'.bb_instructions` >> gvs[])
  (* LAST is terminator *)
  >- (
    `LAST bb'.bb_instructions = LAST bb.bb_instructions` by
      simp[Abbr `bb'`, lse_block_last_eq] >>
    gvs[bb_well_formed_def])
  (* only one terminator *)
  >- (
    rpt strip_tac >>
    `i < LENGTH bb.bb_instructions` by gvs[] >>
    qspecl_then [`aliases`,`bp`,`uc`,`bb`,`i`] mp_tac
      (REWRITE_RULE [LET_THM] lse_block_trace) >>
    simp[Abbr `bb'`, lse_block_length] >> strip_tac >>
    `is_terminator bb.bb_instructions❲i❳.inst_opcode` by (
      qpat_x_assum
        `is_terminator (load_store_elim_block aliases bp uc bb).bb_instructions❲i❳.inst_opcode`
        mp_tac >>
      ASM_REWRITE_TAC[is_terminator_def]) >>
    qpat_x_assum `bb_well_formed bb`
      (STRIP_ASSUME_TAC o REWRITE_RULE [bb_well_formed_def]) >>
    qpat_x_assum `!k. _ ==> k = PRE (LENGTH bb.bb_instructions)`
      (qspec_then `i` mp_tac) >> simp[])
  (* PHI ordering: bb'[j] = PHI /\ i<j => bb'[i] = PHI *)
  >> (
    rpt strip_tac >>
    `i < LENGTH bb.bb_instructions` by simp[] >>
    (* Reverse: bb'[j].opcode = PHI => bb[j].opcode = PHI *)
    `(EL j bb.bb_instructions).inst_opcode = PHI` by
      (qspecl_then [`aliases`,`bp`,`uc`,`bb`,`j`] mp_tac lse_block_phi_reverse >>
       gvs[Abbr `bb'`]) >>
    (* Original PHI ordering: bb[i].opcode = PHI *)
    `(EL i bb.bb_instructions).inst_opcode = PHI` by
      (gvs[bb_well_formed_def] >>
       first_x_assum $ qspecl_then [`i`,`j`] mp_tac >> simp[]) >>
    (* Forward: bb[i].opcode = PHI => bb'[i] = bb[i] *)
    `EL i bb'.bb_instructions = EL i bb.bb_instructions` by
      (simp[Abbr `bb'`] >> irule lse_block_phi_preserved >> simp[]) >>
    gvs[])
QED

Triviality lse_block_succs:
  !aliases bp uc bb.
    bb_well_formed bb ==>
    bb_succs (load_store_elim_block aliases bp uc bb) = bb_succs bb
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by gvs[bb_well_formed_def] >>
  `LAST (load_store_elim_block aliases bp uc bb).bb_instructions =
   LAST bb.bb_instructions` by simp[lse_block_last_eq] >>
  `LENGTH (load_store_elim_block aliases bp uc bb).bb_instructions =
   LENGTH bb.bb_instructions` by simp[lse_block_length] >>
  simp[bb_succs_def] >>
  Cases_on `bb.bb_instructions` >>
  Cases_on `(load_store_elim_block aliases bp uc bb).bb_instructions` >> gvs[]
QED

(* ================================================================== *)
(* Part 4: fn_inst_ids_distinct preservation                          *)
(* ================================================================== *)

Triviality lse_fmt_preserves_ids_distinct:
  !aliases bp uc fn.
    fn_inst_ids_distinct fn ==>
    fn_inst_ids_distinct
      (function_map_transform (load_store_elim_block aliases bp uc) fn)
Proof
  rpt strip_tac >>
  gvs[fn_inst_ids_distinct_def, function_map_transform_def] >>
  `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
     (MAP (load_store_elim_block aliases bp uc) fn.fn_blocks) =
   MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks`
    suffices_by simp[] >>
  once_rewrite_tac[MAP_MAP_o] >>
  irule MAP_CONG >> simp[] >>
  rpt strip_tac >>
  irule listTheory.LIST_EQ >>
  simp[lse_block_length] >>
  rpt strip_tac >> simp[EL_MAP, lse_block_length] >>
  qspecl_then [`aliases`,`bp`,`uc`,`x`,`x'`] mp_tac
    (REWRITE_RULE [LET_THM] lse_block_trace) >>
  simp[lse_block_length]
QED

(* ================================================================== *)
(* Part 5: copy_elision_inst properties (extracted, used by WF + SSA) *)
(* ================================================================== *)

Triviality copy_opcode_not_term_phi:
  !op. is_copy_opcode op ==> ~is_terminator op /\ op <> PHI
Proof
  Cases >> simp[is_copy_opcode_def, is_terminator_def]
QED

Triviality copy_elision_inst_properties:
  (!bp dfg v inst. (copy_elision_inst bp dfg v inst).inst_id = inst.inst_id) /\
  (!bp dfg v inst. is_terminator inst.inst_opcode ==>
     copy_elision_inst bp dfg v inst = inst) /\
  (!bp dfg v inst. ~is_terminator inst.inst_opcode ==>
     ~is_terminator (copy_elision_inst bp dfg v inst).inst_opcode) /\
  (!bp dfg v inst. inst.inst_opcode = PHI ==>
     (copy_elision_inst bp dfg v inst).inst_opcode = PHI) /\
  (!bp dfg v inst. inst.inst_opcode <> PHI ==>
     (copy_elision_inst bp dfg v inst).inst_opcode <> PHI)
Proof
  rpt conj_tac >> rpt gen_tac >>
  simp[copy_elision_inst_def, LET_THM] >>
  rpt IF_CASES_TAC >> gvs[] >>
  BasicProvers.every_case_tac >>
  gvs[mk_nop_inst_def, is_terminator_def] >>
  metis_tac[copy_opcode_not_term_phi]
QED

(* copy_elision_inst: id + output property (for SSA trace-back) *)
Triviality copy_elision_inst_structural:
  !bp dfg v inst.
    (copy_elision_inst bp dfg v inst).inst_id = inst.inst_id /\
    ((copy_elision_inst bp dfg v inst).inst_outputs = inst.inst_outputs \/
     (copy_elision_inst bp dfg v inst).inst_outputs = [])
Proof
  rpt gen_tac >>
  simp[copy_elision_inst_def] >>
  rpt IF_CASES_TAC >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[mk_nop_inst_def]
QED

(* ================================================================== *)
(* Part 6: WF preservation                                            *)
(* ================================================================== *)

(* copy_elision_function preserves well-formedness:
   well-formed input produces a well-formed output function *)
Theorem copy_elision_preserves_wf_function:
  !fn. wf_function fn ==> wf_function (copy_elision_function fn)
Proof
  rpt strip_tac >>
  simp[copy_elision_function_def, LET_THM] >>
  (* Layer 3: clear_nops_function *)
  irule clear_nops_function_preserves_wf >>
  (* Layer 2: function_map_transform (load_store_elim_block ...) *)
  irule fmt_preserves_wf_function >>
  qmatch_goalsub_abbrev_tac `function_map_transform lse_b fn1` >>
  (* Layer 1: wf_function fn1 via aft_singleton_preserves_wf *)
  `wf_function fn1` by (
    simp[Abbr `fn1`] >>
    irule aft_singleton_preserves_wf >> simp[copy_elision_inst_properties]) >>
  rpt conj_tac
  >- simp[Abbr `lse_b`, lse_block_label]
  >- (rpt strip_tac >> simp[Abbr `lse_b`] >> irule lse_block_wf >> simp[])
  >- (rpt strip_tac >> simp[Abbr `lse_b`] >> irule lse_block_succs >> simp[])
  >- (simp[Abbr `lse_b`] >> irule lse_fmt_preserves_ids_distinct >>
      gvs[wf_function_def])
  >- simp[]
QED

(* ================================================================== *)
(* Part 7: SSA preservation                                           *)
(* ================================================================== *)

(* SSA form is preserved when copy_elision_inst is applied per-instruction *)
Triviality copy_elision_inst_preserves_ssa:
  !bottom result fn.
    wf_function fn /\ ssa_form fn ==>
    ssa_form (analysis_function_transform bottom result
               (\v inst. [copy_elision_inst bp dfg v inst]) fn)
Proof
  rpt strip_tac >>
  simp[aft_singleton_eq_fmt_mapi] >>
  irule fmt_preserves_ssa_form_general >>
  rpt conj_tac
  (* trace-back *)
  >- (rpt strip_tac >> gvs[] >>
      gvs[MEM_MAPi] >>
      rename1 `idx < LENGTH bb.bb_instructions` >>
      qexists `EL idx bb.bb_instructions` >>
      simp[MEM_EL] >>
      conj_tac >- (qexists `idx` >> simp[]) >>
      qspecl_then [`bp`,`dfg`,
        `df_at bottom result bb.bb_label idx`,
        `EL idx bb.bb_instructions`] strip_assume_tac copy_elision_inst_structural >>
      simp[])
  (* fn_inst_ids_distinct fn *)
  >- gvs[wf_function_def]
  (* fn_inst_ids_distinct (fmt ...) *)
  >- (simp[GSYM aft_singleton_eq_fmt_mapi] >>
      `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
      `wf_function (analysis_function_transform bottom result
         (\v inst. [copy_elision_inst bp dfg v inst]) fn)` by (
        irule aft_singleton_preserves_wf >> simp[copy_elision_inst_properties]) >>
      gvs[wf_function_def])
  (* ssa_form fn *)
  >> simp[]
QED

(* Trace-back for lse_block: each transformed inst traces to same-index original *)
Triviality lse_block_inst_traceback:
  !aliases bp uc bb inst.
    MEM inst (load_store_elim_block aliases bp uc bb).bb_instructions ==>
    ?orig. MEM orig bb.bb_instructions /\
           inst.inst_id = orig.inst_id /\
           (inst.inst_outputs = orig.inst_outputs \/ inst.inst_outputs = [])
Proof
  rpt strip_tac >>
  gvs[MEM_EL] >> rename1 `idx < _` >>
  qexists `EL idx bb.bb_instructions` >>
  conj_tac >- (simp[MEM_EL] >> qexists `idx` >> gvs[lse_block_length]) >>
  qspecl_then [`aliases`,`bp`,`uc`,`bb`,`idx`]
    mp_tac (REWRITE_RULE [LET_THM] lse_block_trace) >>
  (impl_tac >- simp[lse_block_length]) >>
  simp[]
QED

(* SSA form is preserved when load_store_elim_block is applied per-block *)
Triviality load_store_elim_preserves_ssa:
  !aliases bp uc fn.
    fn_inst_ids_distinct fn /\ ssa_form fn ==>
    ssa_form (function_map_transform (load_store_elim_block aliases bp uc) fn)
Proof
  rpt strip_tac >>
  irule fmt_preserves_ssa_form_general >>
  simp[lse_fmt_preserves_ids_distinct] >>
  rpt strip_tac >>
  drule_all lse_block_inst_traceback >> simp[]
QED

(* copy_elision_function preserves SSA form:
   given a well-formed SSA input, the output remains in SSA form *)
Theorem copy_elision_preserves_ssa_form:
  !fn. wf_function fn /\ ssa_form fn ==>
    ssa_form (copy_elision_function fn)
Proof
  rpt strip_tac >>
  simp[copy_elision_function_def, LET_THM] >>
  (* Layer 3: clear_nops *)
  irule clear_nops_function_preserves_ssa >>
  (* Layer 2: fmt(lse_block) *)
  qmatch_goalsub_abbrev_tac `function_map_transform lse_b fn1` >>
  simp[Abbr `lse_b`] >>
  irule load_store_elim_preserves_ssa >>
  conj_tac
  (* fn_inst_ids_distinct fn1 *)
  >- (`wf_function fn1` by (
        simp[Abbr `fn1`] >>
        irule aft_singleton_preserves_wf >> simp[copy_elision_inst_properties]) >>
      gvs[wf_function_def])
  (* ssa_form fn1 *)
  >- simp[Abbr `fn1`, copy_elision_inst_preserves_ssa]
QED
