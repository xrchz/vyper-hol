(*
 * DFT Pass — Correctness
 *
 * TOP-LEVEL:
 *   dft_pass_correct — DFT preserves execution semantics (pass_correct)
 *
 * Proof strategy:
 *   1. dft_fn only changes bb_instructions of each block (labels preserved)
 *   2. For each block, run_block on dft_block produces lift_result-compatible
 *      results: OK states are identical (run_insts_perm_ok), Abort/Halt have
 *      same constructor and abort type (state is T, irrelevant in EVM).
 *   3. run_function lift_result follows by induction on fuel
 *   4. pass_correct follows from lift_result bridge
 *
 * R_term = execution_equiv {} for Halt/IntRet (states identical).
 * R_abort = revert_equiv for Abort (only returndata survives EVM rollback).
 * DFT can reorder independent instructions past aborters, so variable
 * state at abort points may differ — but that state gets rolled back.
 *)

Theory dftCorrectness
Ancestors
  dftFrontEquiv dftTopoSort dftWf dftDefs dftHelpers stateEquiv stateEquivProps passSimulationDefs
  venomExecSemantics venomWf venomState finite_map venomInst
  analysisSimDefs analysisSimProofsBase dftPermSim dftCompleteness dftPipelineInvar
  dftStructural dftIdempotent venomEffects sorting
  list rich_list combin arithmetic
  venomExecProps passSimulationProofs crossBlockSimProps
  dftBlockSim passSharedProps venomInstProps
  passSharedFrame passSharedDefs relation
  dftCanonicalDep allocaRemapSSA dftContraHelpers
  pred_set pair
Libs
  wordsLib BasicProvers dep_rewrite

(* ===== Structural: dft_block preserves bb_label ===== *)

Triviality dft_block_label[simp]:
  (dft_block order bb).bb_label = bb.bb_label
Proof
  simp[dft_block_def, LET_THM]
QED

(* ===== Structural: dft_process_one preserves MAP bb_label ===== *)

Triviality map_replace_label:
  !lbl bb bbs.
    bb.bb_label = lbl ==>
    MAP (\b. b.bb_label)
        (MAP (\b. if b.bb_label = lbl then dft_block order bb else b) bbs) =
    MAP (\b. b.bb_label) bbs
Proof
  Induct_on `bbs` >> simp[] >> rpt strip_tac >> rw[]
QED

Triviality dft_process_one_labels:
  !cfg lr fn st lbl labels.
    MAP (\b. b.bb_label) st.dls_blocks = labels ==>
    MAP (\b. b.bb_label) (FST (dft_process_one cfg lr fn st lbl)).dls_blocks =
    labels
Proof
  rpt strip_tac >>
  simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  rename1 `SOME bb` >>
  imp_res_tac lookup_block_label >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[map_replace_label]
QED

(* ===== Structural: dft_loop_step preserves MAP bb_label ===== *)

Triviality dft_loop_step_labels:
  !cfg lr fn trip labels.
    MAP (\b. b.bb_label) (FST trip).dls_blocks = labels ==>
    MAP (\b. b.bb_label) (FST (dft_loop_step cfg lr fn trip)).dls_blocks =
    labels
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >>
  strip_tac >>
  pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`,`labels`] mp_tac
    dft_process_one_labels >>
  simp[]
QED

(* ===== Structural: dft_fn preserves MAP bb_label (FUNPOW invariant) ===== *)

Triviality funpow_dft_loop_labels:
  !n cfg lr fn trip labels.
    MAP (\b. b.bb_label) (FST trip).dls_blocks = labels ==>
    MAP (\b. b.bb_label)
      (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks = labels
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_labels >>
  first_x_assum irule >> simp[]
QED

Theorem dft_fn_labels_map:
  !fn. MAP (\b. b.bb_label) (dft_fn fn).fn_blocks =
       MAP (\b. b.bb_label) fn.fn_blocks
Proof
  gen_tac >> rewrite_tac[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[funpow_dft_loop_labels]
QED

(* ===== Corollaries of label preservation ===== *)

Triviality mem_label_from_map:
  !l1 l2 bb.
    MAP (\b. b.bb_label) l1 = MAP (\b. b.bb_label) l2 /\
    MEM bb l1 ==>
    ?bb'. MEM bb' l2 /\ bb.bb_label = bb'.bb_label
Proof
  Induct >> simp[] >> gen_tac >> Cases >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem dft_fn_labels:
  !fn bb. MEM bb (dft_fn fn).fn_blocks ==>
          ?bb'. MEM bb' fn.fn_blocks /\ bb.bb_label = bb'.bb_label
Proof
  metis_tac[mem_label_from_map, dft_fn_labels_map]
QED

Triviality MEM_P_FIND:
  !P l x. MEM x l /\ P x ==> ?y. FIND P l = SOME y
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >> gvs[]
  >- (Cases_on `FIND P l` >> simp[listTheory.FIND_thm])
  >> (simp[listTheory.FIND_thm] >> IF_CASES_TAC >> simp[] >>
      metis_tac[])
QED

Triviality lookup_block_map_labels:
  !l1 l2 lbl bb.
    MAP (\b. b.bb_label) l1 = MAP (\b. b.bb_label) l2 /\
    lookup_block lbl l1 = SOME bb ==>
    ?bb'. lookup_block lbl l2 = SOME bb'
Proof
  rpt strip_tac >>
  `MEM bb l1 /\ bb.bb_label = lbl` by
    (fs[lookup_block_def] >>
     imp_res_tac venomExecPropsTheory.FIND_MEM >>
     imp_res_tac venomExecPropsTheory.FIND_P >> gs[]) >>
  drule_all mem_label_from_map >> strip_tac >>
  simp[lookup_block_def] >> irule MEM_P_FIND >> metis_tac[]
QED

Theorem dft_fn_lookup_block:
  !fn lbl bb.
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    ?bb'. lookup_block lbl (dft_fn fn).fn_blocks = SOME bb'
Proof
  metis_tac[lookup_block_map_labels, dft_fn_labels_map]
QED

(* ===== Block-level: run_block equality ===== *)

(* A block is a permutation-variant of a block in fn: same phis,
   non-pseudos are from_block (= same or flip) of the original *)
Definition block_perm_of_def:
  block_perm_of fn bb <=>
    ?bb_orig. MEM bb_orig fn.fn_blocks /\
      bb.bb_label = bb_orig.bb_label /\
      FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions =
      FILTER (\i. is_pseudo i.inst_opcode) bb_orig.bb_instructions /\
      EVERY (\i. from_block bb_orig.bb_instructions i)
        (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions) /\
      PERM (MAP (\i. i.inst_id)
              (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))
           (MAP (\i. i.inst_id)
              (FILTER (\i. ~is_pseudo i.inst_opcode) bb_orig.bb_instructions))
End

(* PHI prefix is determined by the pseudo-filter when PHIs are prefix-formed. *)
Triviality no_phi_filter_phi_prefix_zero:
  !l. (!x. MEM x l ==> x.inst_opcode <> PHI) ==>
      phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) l) = 0
Proof
  Induct >> simp[FILTER, phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `is_pseudo h.inst_opcode` >> simp[phi_prefix_length_def] >>
  `h.inst_opcode <> PHI` by metis_tac[] >> simp[]
QED

Triviality phi_prefix_length_filter_pseudo:
  !l.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) ==>
    phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) l) =
    phi_prefix_length l
Proof
  Induct >> simp[FILTER, phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[is_pseudo_def, phi_prefix_length_def]
  >- (
    `!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI` by
      (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
       simp[]) >>
    first_x_assum drule >> simp[]) >>
  Cases_on `is_pseudo h.inst_opcode` >> simp[phi_prefix_length_def] >>
  `!x. MEM x l ==> x.inst_opcode <> PHI` by (
    rpt strip_tac >> spose_not_then assume_tac >>
    `?j. j < LENGTH l /\ EL j l = x` by metis_tac[MEM_EL] >>
    first_x_assum (qspecl_then [`0`, `SUC j`] mp_tac) >> simp[]) >>
  metis_tac[no_phi_filter_phi_prefix_zero]
QED

Triviality phi_prefix_el_filter_pseudo:
  !l i.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) /\
    i < phi_prefix_length l ==>
    EL i (FILTER (\i. is_pseudo i.inst_opcode) l) = EL i l
Proof
  Induct >> simp[FILTER, phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[is_pseudo_def, phi_prefix_length_def] >>
  Cases_on `i` >> simp[] >>
  `!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
         (EL i l).inst_opcode = PHI` by
    (rpt strip_tac >>
     qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH l) /\ _ ==> _`
       (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
     simp[]) >>
  qpat_x_assum `!i. _ ==> EL i (FILTER (\i. is_pseudo i.inst_opcode) l) = EL i l`
    (qspec_then `n` mp_tac) >>
  impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
  simp[]
QED


(* ===== Permutation lift_result for run_insts ===== *)

(* Non-terminator, non-INVOKE instructions never produce Halt or IntRet *)
(* run_insts on non-term/non-INVOKE/non-ext-call list can only return OK, Abort, or Error *)
(* Pre-compute: non-terminator non-INVOKE opcodes never produce Halt/IntRet.
   Uses same ML pre-computation pattern as dftPermSim.per_op_no_halt_abort. *)
local
  val nt_ni_ops = List.filter (fn op_tm =>
    let val nt = EVAL ``~is_terminator ^op_tm``
        val ni = EVAL ``^op_tm <> INVOKE``
    in aconv (rhs (concl nt)) T andalso aconv (rhs (concl ni)) T end
  ) (TypeBase.constructors_of ``:opcode``);

  val nt_ni_clauses = map (fn op_tm =>
    SIMP_CONV (srw_ss()) [step_inst_base_def]
      (mk_comb(mk_comb(``step_inst_base``,
        ``inst with inst_opcode := ^op_tm``), ``st:venom_state``))
  ) nt_ni_ops;

  val exec_helper_defs = [
    exec_pure1_def, exec_pure2_def, exec_pure3_def,
    exec_read0_def, exec_read1_def, exec_write2_def,
    exec_alloca_def, exec_ext_call_def, exec_create_def,
    exec_delegatecall_def, LET_THM, AllCaseEqs()];

  val per_op_not_halt_intret = map (fn (op_tm, clause) =>
    prove(
      ``inst.inst_opcode = ^op_tm ==>
        (!v. step_inst_base inst st <> Halt v) /\
        (!vals v. step_inst_base inst st <> IntRet vals v)``,
      strip_tac >>
      `inst with inst_opcode := ^op_tm = inst`
        by simp[instruction_component_equality] >>
      pop_assum (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
      ONCE_REWRITE_TAC [clause] >> simp exec_helper_defs)
  ) (ListPair.zip(nt_ni_ops, nt_ni_clauses));
in
  val step_inst_base_not_halt_intret_combined = LIST_CONJ per_op_not_halt_intret;
end

Triviality step_inst_base_not_halt_intret:
  !inst s.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    (!v. step_inst_base inst s <> Halt v) /\
    (!vals v. step_inst_base inst s <> IntRet vals v)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def, step_inst_base_not_halt_intret_combined]
QED

Triviality perm_every_imp:
  !P l1 l2. PERM l1 l2 /\ EVERY P l1 ==> EVERY P l2
Proof
  rw[EVERY_MEM] >> metis_tac[PERM_MEM_EQ]
QED

Triviality run_insts_no_halt_intret:
  !fuel ctx l s.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) l ==>
    (!v. run_insts fuel ctx l s <> Halt v) /\
    (!vals v. run_insts fuel ctx l s <> IntRet vals v)
Proof
  gen_tac >> gen_tac >> Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  simp[step_inst_non_invoke] >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  metis_tac[step_inst_base_not_halt_intret]
QED

(* Abort type is determined by opcode_fail_class for non-term/non-INVOKE *)
Triviality step_inst_base_abort_type:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    (opcode_fail_class inst.inst_opcode = CanRevert ==> a = Revert_abort) /\
    (opcode_fail_class inst.inst_opcode = CanExHalt ==> a = ExHalt_abort)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[opcode_fail_class_def, is_terminator_def] >>
  gvs[step_inst_base_def, AllCaseEqs()]
QED

(* Two abort_compatible non-term/non-INVOKE instructions that both abort
   produce the same abort type *)
Triviality abort_compatible_same_type:
  !i1 i2 s1 s2 a1 a2 s1' s2'.
    abort_compatible i1.inst_opcode i2.inst_opcode /\
    ~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode /\
    i1.inst_opcode <> INVOKE /\ i2.inst_opcode <> INVOKE /\
    step_inst_base i1 s1 = Abort a1 s1' /\
    step_inst_base i2 s2 = Abort a2 s2' ==>
    a1 = a2
Proof
  rpt strip_tac >>
  fs[abort_compatible_def] >> gvs[]
  >- metis_tac[step_inst_nofail_not_halt_abort]
  >- metis_tac[step_inst_nofail_not_halt_abort]
  >> (Cases_on `opcode_fail_class i1.inst_opcode` >> gvs[]
      >- metis_tac[step_inst_nofail_not_halt_abort]
      >- (`a1 = Revert_abort` by metis_tac[step_inst_base_abort_type] >>
          `a2 = Revert_abort` by metis_tac[step_inst_base_abort_type] >> gvs[])
      >- (`a1 = ExHalt_abort` by metis_tac[step_inst_base_abort_type] >>
          `a2 = ExHalt_abort` by metis_tac[step_inst_base_abort_type] >> gvs[])
      (* AnyFail: only INVOKE, excluded *)
      >> (Cases_on `i1.inst_opcode` >>
          gvs[opcode_fail_class_def]))
QED

(* step_inst_base abort always clears returndata for non-term/ext/INVOKE *)
Triviality step_inst_base_abort_returndata:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE ==>
    s'.vs_returndata = []
Proof
  rpt strip_tac >>
  Cases_on `opcode_fail_class inst.inst_opcode` >> gvs[]
  >- metis_tac[step_inst_nofail_not_halt_abort]
  >- ((* CanRevert — only ASSERT has this class among non-term/non-ext *)
      Cases_on `inst.inst_opcode` >>
      gvs[opcode_fail_class_def, is_terminator_def, is_ext_call_op_def] >>
      gvs[step_inst_base_def, AllCaseEqs(),
          revert_state_def, set_returndata_def])
  >- ((* CanExHalt — INVALID, ASSERT_UNREACHABLE, RETURNDATACOPY *)
      Cases_on `inst.inst_opcode` >>
      gvs[opcode_fail_class_def, is_terminator_def, is_ext_call_op_def] >>
      gvs[step_inst_base_def, AllCaseEqs(),
          halt_state_def, set_returndata_def])
  >> ((* AnyFail — only INVOKE, excluded *)
      Cases_on `inst.inst_opcode` >>
      gvs[opcode_fail_class_def, is_terminator_def, is_ext_call_op_def])
QED

(* Non-terminator non-ext-call aborters always set returndata = [] *)
Theorem run_insts_abort_clears_returndata:
  !fuel ctx l s a s'.
    run_insts fuel ctx l s = Abort a s' /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode /\
               i.inst_opcode <> INVOKE) l ==>
    s'.vs_returndata = []
Proof
  gen_tac >> gen_tac >> Induct >> rpt strip_tac >> gvs[run_insts_def] >>
  gvs[AllCaseEqs(), step_inst_non_invoke] >>
  metis_tac[step_inst_base_abort_returndata]
QED

(* For pairwise bi_independent permutations:
   - OK case: identical result (run_insts_perm_ok)
   - Non-OK case: both have same constructor, abort types match,
     returndata = [] (revert_equiv) *)
(* If instruction x OKs on s giving sx, and y is bi_independent of x,
   then y produces the same result constructor on sx as on s.
   Specifically: if y aborts on s, y also aborts on sx with the same type;
   if y doesn't error on s, y doesn't error on sx. *)
(* Helper: MEM (Var v) ops ==> MEM v (operand_vars ops) *)
Theorem MEM_operand_vars_iff:
  !ops v. MEM v (operand_vars ops) <=> MEM (Var v) ops
Proof
  Induct >> simp[operand_vars_def] >>
  rpt gen_tac >> Cases_on `operand_var h` >> simp[operand_var_def] >>
  Cases_on `h` >> gvs[operand_var_def]
QED

val MEM_Var_operand_vars =
  MEM_operand_vars_iff |> SPEC_ALL |> EQ_IMP_RULE |> snd
    |> GENL [``ops : operand list``, ``v : string``];

(* ML pre-computation: non-aborting opcodes can't produce Abort *)
local
  val nt_ni_nec_na_ops = List.filter (fn op_tm =>
    let val nt = EVAL ``~is_terminator ^op_tm``
        val ni = EVAL ``^op_tm <> INVOKE``
        val nec = EVAL ``~is_ext_call_op ^op_tm``
        val na = EVAL ``~is_alloca_op ^op_tm``
    in aconv (rhs (concl nt)) T andalso aconv (rhs (concl ni)) T
       andalso aconv (rhs (concl nec)) T andalso aconv (rhs (concl na)) T end
  ) (TypeBase.constructors_of ``:opcode``);
  val abort_ops = [``ASSERT``, ``ASSERT_UNREACHABLE``, ``RETURNDATACOPY``];
  val non_abort_ops = List.filter (fn op_tm =>
    not (List.exists (fn t => aconv t op_tm) abort_ops)) nt_ni_nec_na_ops;
  val nt_ni_clauses = map (fn op_tm =>
    SIMP_CONV (srw_ss()) [step_inst_base_def]
      (mk_comb(mk_comb(``step_inst_base``,
        ``inst with inst_opcode := ^op_tm``), ``st:venom_state``))
  ) non_abort_ops;
  val exec_helper_defs = [
    exec_pure1_def, exec_pure2_def, exec_pure3_def,
    exec_read0_def, exec_read1_def, exec_write2_def,
    exec_alloca_def, exec_ext_call_def, exec_create_def,
    exec_delegatecall_def, LET_THM, AllCaseEqs()];
  val per_op_no_abort = map (fn (op_tm, clause) =>
    prove(
      ``inst.inst_opcode = ^op_tm ==>
        (!a s'. step_inst_base inst st <> Abort a s')``,
      strip_tac >>
      `inst with inst_opcode := ^op_tm = inst`
        by simp[instruction_component_equality] >>
      pop_assum (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
      ONCE_REWRITE_TAC [clause] >> simp exec_helper_defs)
  ) (ListPair.zip(non_abort_ops, nt_ni_clauses));
in
  val step_inst_base_no_abort_combined = LIST_CONJ per_op_no_abort;
end

(* Helper: effects_independent with RETURNDATACOPY implies no returndata write *)
Triviality eff_ind_returndatacopy_no_write_rd:
  !op. effects_independent op RETURNDATACOPY ==>
       Eff_RETURNDATA NOTIN write_effects op
Proof
  rpt strip_tac >> gvs[effects_independent_def] >>
  spose_not_then assume_tac >>
  `Eff_RETURNDATA IN (read_effects RETURNDATACOPY UNION
                      write_effects RETURNDATACOPY)` by EVAL_TAC >>
  gvs[pred_setTheory.IN_DISJOINT] >>
  metis_tac[]
QED

(* Shared helper: if x OKs on s giving sx, and bi_independent x y,
   then y's operands evaluate identically on sx and s.
   This is THE core frame lemma for cross-instruction reasoning. *)
Triviality bi_ind_ok_preserves_eval_operand:
  !fuel ctx x y s sx op.
    bi_independent x y /\
    step_inst fuel ctx x s = OK sx /\
    MEM op y.inst_operands ==>
    eval_operand op sx = eval_operand op s
Proof
  rpt strip_tac >> fs[bi_independent_def] >>
  Cases_on `op` >> simp[eval_operand_def]
  (* Var case *)
  >- (`!v. ~MEM v x.inst_outputs ==> lookup_var v sx = lookup_var v s` by
        metis_tac[step_preserves_non_output_vars] >>
      first_x_assum irule >>
      `MEM s' (inst_uses y)` by
        (simp[inst_uses_def] >> irule MEM_Var_operand_vars >> simp[]) >>
      spose_not_then assume_tac >>
      `MEM s' (inst_defs x)` by fs[inst_defs_def] >>
      qpat_x_assum `DISJOINT (set (inst_defs x)) (set (inst_uses y))` mp_tac >>
      simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
      qexists_tac `s'` >> simp[])
  (* Label case *)
  >> (drule_all step_preserves_labels >> simp[])
QED

(* Corollary: all of y's operands evaluate the same on sx as s *)
Triviality bi_ind_ok_all_operands_same:
  !fuel ctx x y s sx.
    bi_independent x y /\
    step_inst fuel ctx x s = OK sx ==>
    MAP (\op. eval_operand op sx) y.inst_operands =
    MAP (\op. eval_operand op s) y.inst_operands
Proof
  rpt strip_tac >> irule MAP_CONG >> simp[] >>
  metis_tac[bi_ind_ok_preserves_eval_operand]
QED

(* Abort transfers between states with same operand values and returndata.
   If a non-term/non-alloca/non-ext/non-INVOKE instruction aborts from s,
   it also aborts (with the same abort type) from any s' that agrees on
   operand values and returndata. *)
Triviality step_inst_base_abort_transfer:
  !inst s s' a v.
    step_inst_base inst s = Abort a v /\
    ~is_terminator inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s' = eval_operand op s) /\
    (inst.inst_opcode = RETURNDATACOPY ==>
     s'.vs_returndata = s.vs_returndata) ==>
    ?v'. step_inst_base inst s' = Abort a v'
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
      step_inst_base_no_abort_combined] >>
  (* Only ASSERT, ASSERT_UNREACHABLE, RETURNDATACOPY remain *)
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >>
  simp[revert_state_def, halt_state_def] >>
  simp[set_returndata_def, LET_THM] >>
  rpt strip_tac >> gvs[]
QED

Triviality bi_independent_cross_abort:
  !fuel ctx x y s sx a s_ab.
    bi_independent x y /\
    step_inst fuel ctx x s = OK sx /\
    step_inst fuel ctx y s = Abort a s_ab ==>
    ?s_ab'. step_inst fuel ctx y sx = Abort a s_ab' /\
            s_ab'.vs_returndata = [] /\ s_ab.vs_returndata = []
Proof
  rpt strip_tac >>
  drule bi_ind_ok_all_operands_same >>
  disch_then drule >> strip_tac >>
  fs[bi_independent_def] >>
  (* Convert step_inst -> step_inst_base *)
  qpat_x_assum `step_inst _ _ y _ = Abort _ _` mp_tac >>
  simp[step_inst_non_invoke] >> strip_tac >>
  simp[step_inst_non_invoke] >>
  (* Only 3 opcodes can abort *)
  Cases_on `y.inst_opcode` >>
  gvs[is_terminator_def, is_ext_call_op_def, is_alloca_op_def,
      step_inst_base_no_abort_combined] >>
  (* Shared pattern: decompose abort on s, rebuild on sx using same evals.
     ONCE_REWRITE_TAC[step_inst_base_def] unfolds once with known opcode. *)
  qpat_x_assum `step_inst_base _ s = _` mp_tac >>
  ONCE_REWRITE_TAC [step_inst_base_def] >>
  ASM_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  simp[AllCaseEqs()] >>
  simp[revert_state_def, halt_state_def] >>
  simp[set_returndata_def, LET_THM] >>
  strip_tac >> gvs[] >>
  ONCE_REWRITE_TAC [step_inst_base_def] >>
  ASM_REWRITE_TAC[venomInstTheory.opcode_case_def] >>
  simp[revert_state_def, halt_state_def] >>
  simp[set_returndata_def, LET_THM] >>
  (* RETURNDATACOPY: also needs sx.vs_returndata = s.vs_returndata *)
  metis_tac[write_effects_sound_returndata,
            eff_ind_returndatacopy_no_write_rd]
QED

(* bi_independent is symmetric *)
Triviality bi_independent_sym:
  !x y. bi_independent x y ==> bi_independent y x
Proof
  rw[bi_independent_def, effects_independent_def, abort_compatible_def] >>
  metis_tac[pred_setTheory.DISJOINT_SYM]
QED

(* Chain: if inst aborts from s with type a, and we run a sequence of
   bi_independent instructions that all OK, inst still aborts with type a
   from the resulting state. *)
Triviality bi_ind_cross_abort_chain:
  !prefix fuel ctx inst s a v s'.
    EVERY (bi_independent inst) prefix /\
    step_inst fuel ctx inst s = Abort a v /\
    run_insts fuel ctx prefix s = OK s' ==>
    ?v'. step_inst fuel ctx inst s' = Abort a v'
Proof
  Induct >> simp[run_insts_def] >> rpt strip_tac >>
  gvs[EVERY_DEF] >>
  rename1 `bi_independent inst h` >>
  Cases_on `step_inst fuel ctx h s` >> gvs[] >>
  rename1 `step_inst _ _ h s = OK sh` >>
  drule bi_independent_sym >> strip_tac >>
  drule_all bi_independent_cross_abort >> strip_tac >>
  first_x_assum (qspecl_then [`fuel`,`ctx`,`inst`,`sh`,`a`,`s_ab'`,`s'`] mp_tac) >>
  simp[]
QED

(* Prefix of bi_independent OK steps preserves operands *)
Triviality eval_operand_bi_ind_prefix_invariant:
  !prefix fuel ctx inst s s'.
    EVERY (\e. bi_independent inst e) prefix /\
    EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
    run_insts fuel ctx prefix s = OK s' ==>
    !op. MEM op inst.inst_operands ==> eval_operand op s' = eval_operand op s
Proof
  Induct >> simp[run_insts_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `step_inst fuel ctx h s` >> gvs[run_insts_def] >>
  rename1 `step_inst _ _ h s = OK sh` >>
  rpt strip_tac >>
  `eval_operand op sh = eval_operand op s` by
    metis_tac[bi_ind_ok_preserves_eval_operand, bi_independent_sym] >>
  last_x_assum (qspecl_then [`fuel`, `ctx`, `inst`, `sh`, `s'`] mp_tac) >>
  simp[]
QED

(* Prefix of bi_independent OK steps preserves returndata when inst
   reads/writes returndata (e.g. RETURNDATACOPY barrier) *)
Triviality returndata_bi_ind_prefix_invariant:
  !prefix fuel ctx inst s s'.
    EVERY (\e. bi_independent inst e) prefix /\
    EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
    run_insts fuel ctx prefix s = OK s' /\
    Eff_RETURNDATA IN
      (read_effects inst.inst_opcode UNION write_effects inst.inst_opcode) ==>
    s'.vs_returndata = s.vs_returndata
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst fuel ctx h s` >> gvs[run_insts_def] >>
  rename1 `step_inst _ _ h s = OK sh` >>
  `Eff_RETURNDATA NOTIN write_effects h.inst_opcode` by
    (qpat_x_assum `bi_independent _ _` mp_tac >>
     simp[bi_independent_def, effects_independent_def,
          pred_setTheory.IN_DISJOINT] >> metis_tac[]) >>
  `~is_alloca_op h.inst_opcode` by
    (qpat_x_assum `bi_independent _ _` mp_tac >>
     simp[bi_independent_def]) >>
  `sh.vs_returndata = s.vs_returndata` by
    metis_tac[write_effects_sound_returndata] >>
  last_x_assum (qspecl_then [`fuel`, `ctx`, `inst`, `sh`, `s'`] mp_tac) >>
  simp[]
QED

(* Cross-step preserves OK: if both succeed on s and are bi_independent,
   each also succeeds on the other's result state *)
Triviality bi_ind_cross_step_ok:
  !fuel ctx x y s sx.
    bi_independent x y /\
    step_inst fuel ctx x s = OK sx /\
    step_inst fuel ctx y s = OK (sy : venom_state) ==>
    ?v. step_inst_base y sx = OK v
Proof
  rpt strip_tac >>
  drule_all bi_ind_ok_all_operands_same >> strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_alloca_op x.inst_opcode /\
   ~is_ext_call_op x.inst_opcode /\ x.inst_opcode <> INVOKE /\
   ~is_terminator y.inst_opcode /\ ~is_alloca_op y.inst_opcode /\
   ~is_ext_call_op y.inst_opcode /\ y.inst_opcode <> INVOKE /\
   effects_independent x.inst_opcode y.inst_opcode` by
    fs[bi_independent_def] >>
  `step_inst_base y s = OK sy` by fs[step_inst_non_invoke] >>
  `sx.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[step_inst_preserves_prev_bb, step_inst_non_invoke] >>
  `sx.vs_params = s.vs_params` by
    metis_tac[step_preserves_params, step_inst_non_invoke] >>
  qspecl_then [`y`,`s`,`sy`,`sx`] mp_tac step_inst_base_ok_transfer >>
  simp[] >> disch_then irule >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `MAP _ _ = MAP _ _` mp_tac >>
      simp[listTheory.MAP_EQ_f])
  >> (strip_tac >>
      `Eff_RETURNDATA NOTIN write_effects x.inst_opcode` by
        metis_tac[eff_ind_returndatacopy_no_write_rd] >>
      metis_tac[write_effects_sound_returndata, step_inst_non_invoke])
QED

(* Non-terminator, non-INVOKE bi_independent instructions never Halt or IntRet *)
Triviality bi_independent_no_halt_intret:
  !fuel ctx x y s.
    bi_independent x y ==>
    (!v. step_inst fuel ctx x s <> Halt v) /\
    (!v s'. step_inst fuel ctx x s <> IntRet v s') /\
    (!v. step_inst fuel ctx y s <> Halt v) /\
    (!v s'. step_inst fuel ctx y s <> IntRet v s')
Proof
  rw[bi_independent_def, step_inst_non_invoke] >>
  metis_tac[step_inst_base_not_halt_intret]
QED

(* Swap case helper: two bi_independent non-erroring instructions produce
   lift_result equivalent composed results. *)
Triviality step_swap_lift:
  !fuel ctx x y s.
    bi_independent x y /\
    (!e. step_inst fuel ctx x s <> Error e) /\
    (!e. step_inst fuel ctx y s <> Error e) ==>
    lift_result (=) (=) revert_equiv
      (case step_inst fuel ctx x s of
         OK sx => step_inst fuel ctx y sx
       | Halt v => Halt v | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s' | Error e => Error e)
      (case step_inst fuel ctx y s of
         OK sy => step_inst fuel ctx x sy
       | Halt v => Halt v | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s' | Error e => Error e)
Proof
  rpt strip_tac >>
  (* Get specific no-Halt/IntRet facts that gvs can use *)
  qspecl_then [`fuel`,`ctx`,`x`,`y`,`s`] mp_tac
    bi_independent_no_halt_intret >> (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `step_inst fuel ctx x s` >> gvs[] >>
  Cases_on `step_inst fuel ctx y s` >> gvs[]
  (* OK x, OK y: commute via independent_commute_eq *)
  >- suspend "ok_ok"
  (* OK x, Abort y: cross_abort *)
  >- (drule_all bi_independent_cross_abort >> strip_tac >>
      simp[lift_result_def, revert_equiv_def])
  (* Abort x, OK y: symmetric — use cross_abort with roles swapped *)
  >- (rename1 `step_inst _ _ y s = OK sy` >>
      rename1 `step_inst _ _ x s = Abort abt sab` >>
      `bi_independent y x` by metis_tac[bi_independent_sym] >>
      qspecl_then [`fuel`,`ctx`,`y`,`x`,`s`,`sy`,`abt`,`sab`] mp_tac
        bi_independent_cross_abort >>
      (impl_tac >- simp[]) >> strip_tac >>
      simp[lift_result_def, revert_equiv_def])
  (* Abort x, Abort y: same type + both clear returndata *)
  >> (simp[lift_result_def, revert_equiv_def] >>
      fs[bi_independent_def] >>
      conj_tac
      >- metis_tac[abort_compatible_same_type, step_inst_non_invoke]
      >> metis_tac[step_inst_base_abort_returndata, step_inst_non_invoke])
QED

Resume step_swap_lift[ok_ok]:
  rename1 `step_inst _ _ x s = OK sx` >>
  rename1 `step_inst _ _ y s = OK sy` >>
  fs[bi_independent_def] >>
  simp[step_inst_non_invoke] >>
  (* Cross-steps both give OK (by bi_ind_cross_step_ok) *)
  `?vy. step_inst_base y sx = OK vy` by
    metis_tac[bi_ind_cross_step_ok, bi_independent_def] >>
  `?vx. step_inst_base x sy = OK vx` by
    metis_tac[bi_ind_cross_step_ok, bi_independent_sym, bi_independent_def] >>
  simp[lift_result_def] >>
  qspecl_then [`fuel`,`ctx`,`x`,`y`,`s`,`sx`,`sy`] mp_tac
    independent_commute_eq >>
  simp[step_inst_non_invoke]
QED

Finalise step_swap_lift

(* bi_independent OK step preserves non-Error property *)
Triviality bi_ind_ok_preserves_no_error:
  !fuel ctx x i s s'.
    bi_independent x i /\
    step_inst fuel ctx x s = OK s' /\
    (!e. step_inst fuel ctx i s <> Error e) ==>
    (!e. step_inst fuel ctx i s' <> Error e)
Proof
  rpt strip_tac >>
  Cases_on `step_inst fuel ctx i s` >> gvs[] >>
  TRY (drule_all bi_ind_cross_step_ok >> strip_tac >>
       gvs[bi_independent_def, step_inst_non_invoke] >> NO_TAC) >>
  TRY (drule_all bi_independent_cross_abort >> strip_tac >>
       gvs[bi_independent_def, step_inst_non_invoke] >> NO_TAC) >>
  qspecl_then [`fuel`,`ctx`,`x`,`i`,`s`] mp_tac
    bi_independent_no_halt_intret >> simp[]
QED

(* Stepping a bi-independent instruction preserves no-Error in both
   directions. Subsumes bi_ind_ok_preserves_no_error. *)
Triviality bi_ind_ok_no_error_iff:
  !fuel ctx x i s s'.
    bi_independent x i /\
    step_inst fuel ctx x s = OK s' ==>
    ((!e. step_inst fuel ctx i s <> Error e) <=>
     (!e. step_inst fuel ctx i s' <> Error e))
Proof
  rpt strip_tac >> eq_tac >> strip_tac
  (* Forward: no-Error on s → no-Error on s' *)
  >- metis_tac[bi_ind_ok_preserves_no_error]
  (* Reverse: no-Error on s' → no-Error on s.
     We show step_inst i s gives the same constructor as step_inst i s'
     (which is not Error). Uses contrapositive on constructor case analysis. *)
  >> (rpt strip_tac >>
      (* Extract flags from bi_independent for BOTH x and i *)
      `~is_terminator x.inst_opcode /\ ~is_alloca_op x.inst_opcode /\
       ~is_ext_call_op x.inst_opcode /\ x.inst_opcode <> INVOKE /\
       ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode /\
       ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE` by
        (fs[bi_independent_def]) >>
      (* Derive operand equivalence *)
      drule_all bi_ind_ok_all_operands_same >> strip_tac >>
      (* Get state field preservation *)
      `s'.vs_prev_bb = s.vs_prev_bb` by
        (qspecl_then [`fuel`,`ctx`,`x`,`s`,`s'`] mp_tac
           step_inst_preserves_prev_bb >> simp[]) >>
      `s'.vs_params = s.vs_params` by
        (qspecl_then [`fuel`,`ctx`,`x`,`s`,`s'`] mp_tac
           step_preserves_params >> simp[]) >>
      (* Returndata: conditional on i being RETURNDATACOPY *)
      `i.inst_opcode = RETURNDATACOPY ==>
       s'.vs_returndata = s.vs_returndata` by
        (strip_tac >>
         `Eff_RETURNDATA NOTIN write_effects x.inst_opcode` by
           metis_tac[eff_ind_returndatacopy_no_write_rd,
                     bi_independent_def] >>
         metis_tac[write_effects_sound_returndata]) >>
      suspend "reverse")
QED

Resume bi_ind_ok_no_error_iff[reverse]:
  (* Convert step_inst → step_inst_base, derive pointwise operand equality *)
  fs[step_inst_non_invoke] >>
  `!op. MEM op i.inst_operands ==>
        eval_operand op s' = eval_operand op s` by (
    qpat_x_assum `MAP _ _ = MAP _ _` mp_tac >>
    simp[listTheory.MAP_EQ_f]) >>
  Cases_on `step_inst_base i s'` >> gvs[] >>
  TRY (metis_tac[step_inst_base_not_halt_intret])
  (* OK case: transfer OK from s' to s, contradicts Error *)
  >- (qspecl_then [`i`,`s'`,`v`,`s`] mp_tac
        passSharedPropsTheory.step_inst_base_ok_transfer >>
      simp[] >> strip_tac >> gvs[])
  (* Abort case: for each aborting opcode, unfold step_inst_base on both
     states; operand equality ensures same branch taken *)
  >> (Cases_on `i.inst_opcode` >>
      gvs[is_terminator_def, is_ext_call_op_def, is_alloca_op_def,
          step_inst_base_no_abort_combined] >>
      qpat_x_assum `step_inst_base _ s' = Abort _ _` mp_tac >>
      qpat_x_assum `step_inst_base _ s = Error _` mp_tac >>
      ntac 2 (ONCE_REWRITE_TAC [step_inst_base_def]) >>
      every_case_tac >> gvs[] >> IF_CASES_TAC >> gvs[])
QED

Finalise bi_ind_ok_no_error_iff;

(* PERM preserves pairwise_bi_independent and EVERY (bi_independent x) *)
Triviality perm_preserves_pairwise_bi_ind:
  !l1 l2.
    PERM l1 l2 ==>
    (pairwise_bi_independent l1 ==> pairwise_bi_independent l2) /\
    (!x. EVERY (bi_independent x) l1 ==> EVERY (bi_independent x) l2)
Proof
  ho_match_mp_tac PERM_IND >>
  rw[pairwise_bi_independent_def, EVERY_DEF] >>
  gvs[pairwise_bi_independent_def, EVERY_DEF] >>
  metis_tac[bi_independent_sym]
QED

(* Stepping a bi-independent instruction preserves no-error for an entire list *)
Triviality bi_ind_list_preserves_no_error:
  !fuel ctx x l s s'.
    EVERY (bi_independent x) l /\
    step_inst fuel ctx x s = OK s' /\
    EVERY (\i. !e. step_inst fuel ctx i s <> Error e) l ==>
    EVERY (\i. !e. step_inst fuel ctx i s' <> Error e) l
Proof
  rpt strip_tac >> gvs[EVERY_MEM] >> rpt gen_tac >> strip_tac >>
  irule bi_ind_ok_preserves_no_error >>
  qexistsl [`s`, `x`] >> simp[]
QED

(* Main PERM lift_result lemma — uses perm_preserves_pairwise_bi_ind *)
Theorem run_insts_perm_lift_strong:
  !l1 l2.
    PERM l1 l2 ==>
    !fuel ctx s.
       pairwise_bi_independent l1 /\
       EVERY (\i. !e. step_inst fuel ctx i s <> Error e) l1 ==>
       lift_result (=) (=) revert_equiv
         (run_insts fuel ctx l1 s) (run_insts fuel ctx l2 s)
Proof
  ho_match_mp_tac PERM_STRONG_IND >> rpt conj_tac
  (* nil *)
  >- simp[run_insts_def, lift_result_def]
  (* cons *)
  >- suspend "cons"
  (* swap *)
  >- suspend "swap"
  (* trans *)
  >> suspend "trans"
QED

Resume run_insts_perm_lift_strong[cons]:
  rpt strip_tac >>
  gvs[pairwise_bi_independent_def, EVERY_DEF, run_insts_def] >>
  Cases_on `step_inst fuel ctx x s` >> gvs[lift_result_def]
  >- (first_x_assum $ qspecl_then [`fuel`,`ctx`,`v`] mp_tac >>
      impl_tac
      >- suspend "cons_no_err"
      >> simp[])
  >> simp[revert_equiv_def]
QED

Resume run_insts_perm_lift_strong[cons_no_err]:
  irule bi_ind_list_preserves_no_error >>
  qexistsl [`s`, `x`] >> simp[]
QED

Resume run_insts_perm_lift_strong[swap]:
  rpt strip_tac >>
  gvs[pairwise_bi_independent_def, EVERY_DEF, run_insts_def] >>
  qspecl_then [`fuel`,`ctx`,`x`,`y`,`s`] mp_tac
    bi_independent_no_halt_intret >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `step_inst fuel ctx x s` >> gvs[] >>
  Cases_on `step_inst fuel ctx y s` >> gvs[]
  (* OK/OK *)
  >- suspend "swap_ok_ok"
  (* OK/Abort *)
  >- (gvs[step_inst_non_invoke] >>
      drule_all bi_independent_cross_abort >>
      strip_tac >> gvs[lift_result_def, revert_equiv_def])
  (* Abort/OK *)
  >- (`bi_independent y x` by metis_tac[bi_independent_sym] >>
      gvs[step_inst_non_invoke] >>
      drule_all bi_independent_cross_abort >>
      strip_tac >> gvs[lift_result_def, revert_equiv_def])
  (* Abort/Abort *)
  >> gvs[bi_independent_def, step_inst_non_invoke,
         lift_result_def, revert_equiv_def] >>
     metis_tac[step_inst_base_abort_returndata,
               abort_compatible_same_type]
QED

Resume run_insts_perm_lift_strong[swap_ok_ok]:
  (* 1. Cross-step OK results — keep bi_independent intact for helpers *)
  `?s12. step_inst_base y v = OK s12` by
    metis_tac[bi_ind_cross_step_ok] >>
  `bi_independent y x` by metis_tac[bi_independent_sym] >>
  `?s21. step_inst_base x v' = OK s21` by
    metis_tac[bi_ind_cross_step_ok] >>
  (* 2. Convert step_inst_base to step_inst using ¬INVOKE from bi_independent *)
  `y.inst_opcode <> INVOKE /\ x.inst_opcode <> INVOKE` by
    fs[bi_independent_def] >>
  `step_inst fuel ctx y v = OK s12` by simp[step_inst_non_invoke] >>
  `step_inst fuel ctx x v' = OK s21` by simp[step_inst_non_invoke] >>
  (* 3. No-error transfer: s -> v (through x) -> s12 (through y) *)
  `EVERY (\i. !e. step_inst fuel ctx i v <> Error e) l1` by
    (irule bi_ind_list_preserves_no_error >>
     qexistsl [`s`, `x`] >> simp[]) >>
  `EVERY (\i. !e. step_inst fuel ctx i s12 <> Error e) l1` by
    (irule bi_ind_list_preserves_no_error >>
     qexistsl [`v`, `y`] >> simp[]) >>
  (* 4. Diamond: s12 = s21, using independent_commute_eq *)
  `s12 = s21` by
    (qspecl_then [`fuel`,`ctx`,`x`,`y`,`s`,`v`,`v'`,`s12`,`s21`] mp_tac
       independent_commute_eq >>
     (impl_tac >- gvs[bi_independent_def, step_inst_non_invoke]) >>
     simp[]) >>
  gvs[]
QED

Resume run_insts_perm_lift_strong[trans]:
  rpt strip_tac >>
  imp_res_tac perm_preserves_pairwise_bi_ind >>
  `EVERY (\i. !e. step_inst fuel ctx i s <> Error e) l1'` by
    metis_tac[PERM_EVERY] >>
  `lift_result $= $= revert_equiv
     (run_insts fuel ctx l1 s) (run_insts fuel ctx l1' s)` by
    metis_tac[] >>
  `lift_result $= $= revert_equiv
     (run_insts fuel ctx l1' s) (run_insts fuel ctx l2 s)` by
    metis_tac[] >>
  irule (SRULE [] lift_result_trans_proof) >>
  simp[revert_equiv_def] >>
  qexists `run_insts fuel ctx l1' s` >> simp[]
QED

Finalise run_insts_perm_lift_strong


Theorem run_insts_perm_lift:
  !l1 l2 fuel ctx s.
    PERM l1 l2 /\ pairwise_bi_independent l1 /\
    EVERY (\i. !e. step_inst fuel ctx i s <> Error e) l1 ==>
    lift_result (=) (=) revert_equiv
      (run_insts fuel ctx l1 s) (run_insts fuel ctx l2 s)
Proof
  metis_tac[run_insts_perm_lift_strong]
QED

(* ===== Topo-sorted permutation lift_result ===== *)

(* When run_insts aborts, the abort type is determined by some instruction's
   opcode fail class. This instruction is MEM of the list. *)
Triviality run_insts_abort_fail_class:
  !fuel ctx l s a s'.
    run_insts fuel ctx l s = Abort a s' /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) l ==>
    ?i. MEM i l /\ opcode_fail_class i.inst_opcode <> NoFail /\
        (opcode_fail_class i.inst_opcode = CanRevert ==> a = Revert_abort) /\
        (opcode_fail_class i.inst_opcode = CanExHalt ==> a = ExHalt_abort)
Proof
  gen_tac >> gen_tac >> Induct >> rpt strip_tac >> gvs[run_insts_def] >>
  gvs[AllCaseEqs(), step_inst_non_invoke]
  >- ((* Recursive case: head OKs, tail aborts *)
      first_x_assum $ qspecl_then [`s''`, `a`, `s'`] mp_tac >>
      simp[] >> strip_tac >> qexists `i` >> simp[])
  >> ((* Base case: head aborts *)
      qexists `h` >> simp[] >>
      conj_tac >- metis_tac[step_inst_nofail_not_halt_abort] >>
      metis_tac[step_inst_base_abort_type])
QED

(* When both orderings abort and all non-NoFail instructions are dep-chained,
   the abort types must match. Argument: the aborters are both non-NoFail,
   both MEM of the same set (PERM), hence dep-chained, so topo_sorted forces
   same relative order. The abort type is determined by the fail class of the
   aborter, and dep-chained non-NoFail instructions that both abort must have
   abort_compatible fail classes.
   Simpler: bi_independent (from non-dep) requires abort_compatible, and the
   chaining hypothesis ensures non-NoFail pairs ARE dep-related. Since the
   aborter's fail class determines the abort type, and all non-NoFail
   instructions in l have consistent fail class (being chained), a = a'. *)

(* Case-split approach: OK case by run_insts_topo_equiv (symmetric),
   non-OK case by structure (no Halt/IntRet, both Abort → revert_equiv).
   Requires: no Error in either execution (added as hypothesis).
   The non-NoFail chaining hypothesis ensures abort type consistency. *)
(* Topo-sorted permutations produce same OK result and revert_equiv Abort.
   Does NOT claim abort types match — that requires the abort chaining
   property from build_full_eda, proved at the exec_block level. *)
Theorem run_insts_topo_lift:
  !l1 l2 dep fuel ctx s.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> bi_independent x y) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) l1 /\
    (!e. run_insts fuel ctx l1 s <> Error e) /\
    (!e. run_insts fuel ctx l2 s <> Error e) ==>
    (* OK case: identical results *)
    (!r. run_insts fuel ctx l1 s = OK r ==>
         run_insts fuel ctx l2 s = OK r) /\
    (!r. run_insts fuel ctx l2 s = OK r ==>
         run_insts fuel ctx l1 s = OK r) /\
    (* Same constructor: both OK, both Abort, or both Error *)
    (?r. run_insts fuel ctx l1 s = OK r) =
    (?r. run_insts fuel ctx l2 s = OK r) /\
    (* Abort case: revert_equiv *)
    (!a1 s1 a2 s2.
       run_insts fuel ctx l1 s = Abort a1 s1 /\
       run_insts fuel ctx l2 s = Abort a2 s2 ==>
       revert_equiv s1 s2)
Proof
  rpt gen_tac >> strip_tac >>
  rpt conj_tac
  >- suspend "fwd"
  >- suspend "rev"
  >- suspend "iff"
  >> suspend "abort"
QED

Resume run_insts_topo_lift[fwd]:
  rpt strip_tac >> irule run_insts_topo_equiv >>
  qexistsl [`dep`, `l1`] >> simp[]
QED

Resume run_insts_topo_lift[rev]:
  rpt strip_tac >> irule run_insts_topo_equiv >>
  qexistsl [`dep`, `l2`] >> simp[] >>
  `!x. MEM x l2 <=> MEM x l1` by metis_tac[PERM_MEM_EQ] >>
  simp[] >> metis_tac[ALL_DISTINCT_PERM, PERM_SYM]
QED

Resume run_insts_topo_lift[iff]:
  eq_tac >> rpt strip_tac >> gvs[]
  >- (`run_insts fuel ctx l2 s = OK r` by
        (irule run_insts_topo_equiv >>
         qexistsl [`dep`, `l1`] >> simp[]) >>
      metis_tac[])
  >> (`run_insts fuel ctx l1 s = OK r` by
        (irule run_insts_topo_equiv >>
         qexistsl [`dep`, `l2`] >> simp[] >>
         `!x. MEM x l2 <=> MEM x l1` by metis_tac[PERM_MEM_EQ] >>
         simp[] >> metis_tac[ALL_DISTINCT_PERM, PERM_SYM]) >>
      metis_tac[])
QED

Resume run_insts_topo_lift[abort]:
  rpt strip_tac >> simp[revert_equiv_def] >>
  `!x. MEM x l2 <=> MEM x l1` by metis_tac[PERM_MEM_EQ] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\
              ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) l2` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[run_insts_abort_clears_returndata]
QED

Finalise run_insts_topo_lift

(* Abort type is determined by the non-NoFail instruction that caused it.
   If all non-NoFail instructions in both permutations are pairwise
   abort_compatible, any two aborts have the same type. *)
(* ===== Generalized topo-sorted equivalence ===== *)

(* Parameterized by:
   - P: symmetric pairwise commutation predicate
   - Q: per-element property (e.g. inst_wf, ~is_pseudo)
   - swap: P a b /\ Q a /\ Q b /\ step a ok /\ step b ok ==>
           exists sb. step b s = OK sb /\ step a sb = OK sab *)

Triviality prefix_commutes_gen:
  !P prefix x suffix rest dep.
    PERM (prefix ++ [x] ++ suffix) (x :: rest) /\
    ALL_DISTINCT (prefix ++ [x] ++ suffix) /\
    topo_sorted dep (prefix ++ [x] ++ suffix) /\
    topo_sorted dep (x :: rest) /\
    (!a b. P a b ==> P b a) /\
    (!x' y. MEM x' (prefix ++ [x] ++ suffix) /\
            MEM y (prefix ++ [x] ++ suffix) /\
            x' <> y /\ ~dep x' y /\ ~dep y x' ==> P x' y) ==>
    EVERY (P x) prefix
Proof
  rw[EVERY_MEM] >>
  `?k. k < LENGTH prefix /\ e = EL k prefix` by metis_tac[MEM_EL] >> gvs[] >>
  `ALL_DISTINCT (x :: rest)` by metis_tac[ALL_DISTINCT_PERM] >>
  `~dep (EL k prefix) x` by
    (qpat_x_assum `topo_sorted _ (prefix ++ _ ++ _)` mp_tac >>
     rw[topo_sorted_def] >>
     first_x_assum (qspecl_then [`k`, `LENGTH prefix`] mp_tac) >>
     simp[EL_APPEND1, EL_APPEND2]) >>
  `MEM (EL k prefix) (x :: rest)` by
    (irule (iffLR PERM_MEM_EQ) >>
     qexists_tac `prefix ++ [x] ++ suffix` >>
     simp[MEM_APPEND, MEM_EL]) >>
  `EL k prefix <> x` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_EL]) >>
  `MEM (EL k prefix) rest` by gvs[MEM] >>
  `~dep x (EL k prefix)` by
    (qpat_x_assum `topo_sorted _ (x :: rest)` mp_tac >>
     rw[topo_sorted_def] >>
     `?m. m < LENGTH rest /\ EL k prefix = EL m rest` by metis_tac[MEM_EL] >>
     first_x_assum (qspecl_then [`0`, `SUC m`] mp_tac) >> simp[]) >>
  first_x_assum irule >> simp[MEM_APPEND]
QED

Triviality run_insts_bubble_to_front_gen:
  !P Q prefix fuel ctx x suffix s r.
    EVERY (P x) prefix /\
    (!a b s sa sab.
       P a b /\ Q a /\ Q b /\
       step_inst fuel ctx a s = OK sa /\
       step_inst fuel ctx b sa = OK sab ==>
       ?sb. step_inst fuel ctx b s = OK sb /\
            step_inst fuel ctx a sb = OK sab) /\
    (!a b. P a b ==> P b a) /\
    EVERY Q (x :: prefix) /\
    run_insts fuel ctx (prefix ++ [x] ++ suffix) s = OK r ==>
    run_insts fuel ctx ([x] ++ prefix ++ suffix) s = OK r
Proof
  Induct_on `prefix` >> simp[] >>
  rpt strip_tac >> gvs[EVERY_DEF] >>
  gvs[run_insts_def, AllCaseEqs()] >>
  rename1 `step_inst fuel ctx h s = OK sh` >>
  first_x_assum (qspecl_then [`P`, `Q`, `fuel`, `ctx`, `x`,
                              `suffix`, `sh`, `r`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `step_inst fuel ctx x sh = OK sx` >>
  `P h x` by metis_tac[] >>
  first_x_assum (qspecl_then [`h`, `x`, `s`, `sh`, `sx`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists `sb` >> simp[]
QED

Triviality run_insts_topo_equiv_gen_aux:
  !P Q n l1 l2 dep fuel ctx s r.
    LENGTH l2 = n /\
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!a b. P a b ==> P b a) /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> P x y) /\
    (!a b s sa sab.
       P a b /\ Q a /\ Q b /\
       step_inst fuel ctx a s = OK sa /\
       step_inst fuel ctx b sa = OK sab ==>
       ?sb. step_inst fuel ctx b s = OK sb /\
            step_inst fuel ctx a sb = OK sab) /\
    EVERY Q l1 /\
    run_insts fuel ctx l1 s = OK r ==>
    run_insts fuel ctx l2 s = OK r
Proof
  Induct_on `n` >> rpt strip_tac
  >- (gvs[LENGTH_NIL, PERM_NIL, run_insts_def])
  >>
  Cases_on `l2` >> gvs[] >>
  rename1 `PERM l1 (x :: rest)` >>
  `MEM x l1` by (imp_res_tac PERM_MEM_EQ >> gvs[]) >>
  pop_assum (strip_assume_tac o REWRITE_RULE[Once MEM_SPLIT]) >>
  rename1 `l1 = pfx ++ x :: sfx` >>
  `l1 = pfx ++ [x] ++ sfx` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  qpat_x_assum `_ = pfx ++ _ :: _` kall_tac >>
  (* Step 1: prefix elements commute with x *)
  `EVERY (P x) pfx` by
    (qspecl_then [`P`, `pfx`, `x`, `sfx`, `rest`, `dep`]
       mp_tac prefix_commutes_gen >> simp[]) >>
  (* Step 2: bubble x to front *)
  `EVERY Q (x :: pfx)` by gvs[EVERY_APPEND, EVERY_DEF] >>
  `run_insts fuel ctx ([x] ++ pfx ++ sfx) s = OK r` by
    (qspecl_then [`P`, `Q`, `pfx`, `fuel`, `ctx`, `x`, `sfx`, `s`, `r`]
       mp_tac run_insts_bubble_to_front_gen >>
     disch_then match_mp_tac >> simp[]) >>
  (* Step 3: split off head step *)
  gvs[run_insts_def, AllCaseEqs()] >>
  rename1 `step_inst fuel ctx x s = OK sx` >>
  (* Step 4: apply IH to tails *)
  first_x_assum
    (qspecl_then [`P`, `Q`, `pfx ++ sfx`, `rest`,
                  `dep`, `fuel`, `ctx`, `sx`, `r`] mp_tac) >>
  disch_then match_mp_tac >>
  gvs[EVERY_APPEND, ALL_DISTINCT_APPEND_3] >>
  rpt conj_tac
  >- metis_tac[perm_cons_delete]
  >- metis_tac[topo_sorted_delete]
  >- metis_tac[topo_sorted_tail]
  >> (rpt strip_tac >>
      qpat_x_assum `!x' y. _ ==> P x' y` match_mp_tac >>
      gvs[MEM_APPEND])
QED

Theorem run_insts_topo_equiv_gen:
  !P Q l1 l2 dep fuel ctx s r.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!a b. P a b ==> P b a) /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> P x y) /\
    (!a b s sa sab.
       P a b /\ Q a /\ Q b /\
       step_inst fuel ctx a s = OK sa /\
       step_inst fuel ctx b sa = OK sab ==>
       ?sb. step_inst fuel ctx b s = OK sb /\
            step_inst fuel ctx a sb = OK sab) /\
    EVERY Q l1 /\
    run_insts fuel ctx l1 s = OK r ==>
    run_insts fuel ctx l2 s = OK r
Proof
  rpt strip_tac >>
  qspecl_then [`P`, `Q`, `LENGTH l2`, `l1`, `l2`, `dep`, `fuel`, `ctx`, `s`, `r`]
    mp_tac run_insts_topo_equiv_gen_aux >>
  simp[]
QED

(* Instantiation: ext_bi_independent version *)
Theorem run_insts_topo_equiv_ext:
  !l1 l2 dep fuel ctx s r.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> ext_bi_independent x y) /\
    EVERY inst_wf l1 /\
    run_insts fuel ctx l1 s = OK r ==>
    run_insts fuel ctx l2 s = OK r
Proof
  rpt strip_tac >>
  qspecl_then [`ext_bi_independent`, `inst_wf`, `l1`, `l2`, `dep`,
               `fuel`, `ctx`, `s`, `r`]
    mp_tac run_insts_topo_equiv_gen >>
  simp[] >> metis_tac[ext_bi_independent_sym, step_swap_ok_ext]
QED

(* from_block gives step_inst equivalence (uses strengthened from_block) *)
Theorem all_distinct_map_mem_inj:
  !f l a b. ALL_DISTINCT (MAP f l) /\ MEM a l /\ MEM b l /\
            f a = f b ==> a = b
Proof
  rpt strip_tac >> gvs[MEM_EL] >>
  metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]
QED

(* Two blocks in fn_blocks with the same label must be equal (under wf_function) *)
Triviality wf_fn_same_label_eq:
  !fn bb1 bb2.
    wf_function fn /\ MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    bb1.bb_label = bb2.bb_label ==>
    bb1 = bb2
Proof
  rpt strip_tac >> gvs[MEM_EL] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `n < LENGTH (MAP (\b. b.bb_label) fn.fn_blocks)` by simp[] >>
  `n' < LENGTH (MAP (\b. b.bb_label) fn.fn_blocks)` by simp[] >>
  `EL n (MAP (\b. b.bb_label) fn.fn_blocks) =
   EL n' (MAP (\b. b.bb_label) fn.fn_blocks)` by simp[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

Triviality block_perm_of_same_phi_prefix:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' ==>
    phi_prefix_length bb'.bb_instructions =
    phi_prefix_length bb.bb_instructions /\
    (!i. i < phi_prefix_length bb.bb_instructions ==>
         EL i bb'.bb_instructions = EL i bb.bb_instructions)
Proof
  rpt strip_tac >>
  fs[block_perm_of_def] >>
  `bb_orig = bb` by
    (irule (GSYM wf_fn_same_label_eq) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) =
   phi_prefix_length bb'.bb_instructions` by
    (irule phi_prefix_length_filter_pseudo >> fs[bb_well_formed_def]) >>
  `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) =
   phi_prefix_length bb.bb_instructions` by
    (irule phi_prefix_length_filter_pseudo >> fs[bb_well_formed_def]) >>
  `phi_prefix_length bb'.bb_instructions =
   phi_prefix_length bb.bb_instructions` by (
    qpat_x_assum `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) = _`
      (fn th => rewrite_tac[GSYM th]) >>
    qpat_x_assum `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) = _`
      (fn th => rewrite_tac[GSYM th]) >>
    simp[]) >>
  simp[] >>
  rpt strip_tac >>
  `i < phi_prefix_length bb'.bb_instructions` by metis_tac[] >>
  `EL i (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) =
   EL i bb'.bb_instructions` by (
    qspecl_then [`bb'.bb_instructions`, `i`] mp_tac
      phi_prefix_el_filter_pseudo >> simp[] >>
    impl_tac >- fs[bb_well_formed_def] >> simp[]) >>
  `EL i (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) =
   EL i bb.bb_instructions` by (
    qspecl_then [`bb.bb_instructions`, `i`] mp_tac
      phi_prefix_el_filter_pseudo >> simp[] >>
    impl_tac >- fs[bb_well_formed_def] >> simp[]) >>
  metis_tac[]
QED

Triviality block_perm_of_eval_phis_same:
  !fn bb bb' s.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' ==>
    phi_prefix_length bb'.bb_instructions =
    phi_prefix_length bb.bb_instructions /\
    eval_phis s bb'.bb_instructions = eval_phis s bb.bb_instructions
Proof
  rpt strip_tac >>
  drule_all block_perm_of_same_phi_prefix >> strip_tac >>
  simp[] >>
  irule venomExecProofsTheory.eval_phis_same_phi_prefix >> simp[] >>
  metis_tac[]
QED

Triviality no_pseudo_filter_empty:
  !l. (!x. MEM x l ==> ~is_pseudo x.inst_opcode) ==>
      FILTER (\i. is_pseudo i.inst_opcode) l = []
Proof
  Induct >> simp[] >> rpt strip_tac
QED

Triviality pseudo_prefix_el_filter:
  !l i.
    (!i j. i < j /\ j < LENGTH l /\ is_pseudo (EL j l).inst_opcode ==>
           is_pseudo (EL i l).inst_opcode) /\
    i < LENGTH (FILTER (\i. is_pseudo i.inst_opcode) l) ==>
    EL i (FILTER (\i. is_pseudo i.inst_opcode) l) = EL i l
Proof
  Induct >> simp[FILTER] >> rpt strip_tac >>
  Cases_on `is_pseudo h.inst_opcode` >> gvs[]
  >- (
    Cases_on `i` >> simp[] >>
    `!i j. i < j /\ j < LENGTH l /\ is_pseudo (EL j l).inst_opcode ==>
           is_pseudo (EL i l).inst_opcode` by
      (rpt strip_tac >>
       qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH l) /\ _ ==> _`
         (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
    qpat_x_assum `!i. _ ==> EL i (FILTER (\i. is_pseudo i.inst_opcode) l) = EL i l`
      (qspec_then `n` mp_tac) >>
    impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >> simp[]) >>
  `!x. MEM x l ==> ~is_pseudo x.inst_opcode` by (
    rpt strip_tac >> spose_not_then assume_tac >>
    `?j. j < LENGTH l /\ EL j l = x` by metis_tac[MEM_EL] >>
    qpat_x_assum `!i j. i < j /\ j < SUC (LENGTH l) /\ _ ==> _`
      (qspecl_then [`0`, `SUC j`] mp_tac) >> simp[]) >>
  `FILTER (\i. is_pseudo i.inst_opcode) l = []` by
    (irule no_pseudo_filter_empty >> simp[]) >>
  qpat_x_assum `_ < LENGTH (FILTER (\i. is_pseudo i.inst_opcode) l)` mp_tac >>
  asm_rewrite_tac[] >> simp[]
QED

Triviality pseudo_prefix_nonterminator:
  !bb i.
    pseudos_prefix bb /\
    i < LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    ~is_terminator (EL i bb.bb_instructions).inst_opcode
Proof
  rpt strip_tac >>
  `EL i (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) =
   EL i bb.bb_instructions` by (
    qspecl_then [`bb.bb_instructions`, `i`] mp_tac pseudo_prefix_el_filter >>
    simp[] >> impl_tac >- fs[pseudos_prefix_def] >> simp[]) >>
  `MEM (EL i (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions))
       (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by
    metis_tac[MEM_EL] >>
  gvs[MEM_FILTER] >>
  Cases_on `(EL i bb.bb_instructions).inst_opcode` >>
  gvs[is_pseudo_def, is_terminator_def]
QED

Triviality block_perm_of_same_pseudo_prefix:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    pseudos_prefix bb /\ pseudos_prefix bb' ==>
    LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) =
    LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    (!i. i < LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
         EL i bb'.bb_instructions = EL i bb.bb_instructions)
Proof
  rpt strip_tac >> fs[block_perm_of_def] >>
  `bb_orig = bb` by
    (irule (GSYM wf_fn_same_label_eq) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  simp[] >>
  rpt strip_tac >>
  `i < LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions)` by simp[] >>
  `EL i (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) =
   EL i bb'.bb_instructions` by (
    qspecl_then [`bb'.bb_instructions`, `i`] mp_tac pseudo_prefix_el_filter >>
    simp[] >> impl_tac >- fs[pseudos_prefix_def] >> simp[]) >>
  `EL i (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) =
   EL i bb.bb_instructions` by (
    qspecl_then [`bb.bb_instructions`, `i`] mp_tac pseudo_prefix_el_filter >>
    simp[] >> impl_tac >- fs[pseudos_prefix_def] >> simp[]) >>
  qpat_x_assum `EL i (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) = _`
    (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `EL i (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) = _`
    (fn th => rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[]
QED

Triviality from_block_step_equiv:
  !bi i j fuel ctx s.
    from_block bi i /\ MEM j bi /\ ~is_pseudo j.inst_opcode /\
    i.inst_id = j.inst_id /\ ALL_DISTINCT (MAP (\x. x.inst_id) bi) ==>
    step_inst fuel ctx i s = step_inst fuel ctx j s
Proof
  rpt strip_tac >> gvs[from_block_def]
  >- (`i = j` by metis_tac[all_distinct_map_mem_inj] >> gvs[])
  >> (`j' = j` by metis_tac[all_distinct_map_mem_inj] >>
      gvs[flip_operands_step_inst])
QED

(* Core block-level theorem: original block and a block_perm_of variant
   produce lift_result-equivalent exec_block results.
   bb must be the original (from fn.fn_blocks); bb' is the variant.
   bb_well_formed bb' needed because exec_block behavior depends on
   terminator position — without it, exec_block might exit early.
   NOTE: Two arbitrary block_perm_of blocks can reorder aborters,
   giving different abort types. Comparing to original avoids this
   because abort chaining preserves aborter order. *)
(* Sub-lemma: extract body (non-pseudo, non-terminator) instructions *)
(* For a well-formed block, the body is the middle section:
   instructions = phis ++ body ++ [terminator] *)
Definition block_body_def:
  block_body bb =
    FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode)
      bb.bb_instructions
End

(*
 * Strategy: decompose into helpers, prove each independently.
 *
 * Helper 1: eda_non_dep_bi_independent
 *   If x,y are non-pseudo body instructions in a wf_ssa block, and
 *   not related by TC(eda_dep) in either direction, then bi_independent x y.
 *
 * Helper 2: block_perm_of_run_insts_body_lift
 *   run_insts on the body of bb and body of bb' produce lift_result
 *   equivalent results (OK → equal, Abort → revert_equiv).
 *
 * Main: compose helpers with exec_block_skip_prefix and
 *   run_insts_lift_exec_block.
 *)

(* Helper: execution_equiv {} implies revert_equiv *)
Triviality execution_equiv_imp_revert_equiv:
  !s1 s2. execution_equiv {} s1 s2 ==> revert_equiv s1 s2
Proof
  rw[execution_equiv_def, revert_equiv_def, state_equiv_def, FDOM_FEMPTY]
QED

(* Helper: lift_result monotonicity for R_abort weakening *)
Triviality lift_result_weaken_abort:
  !R_ok R_term R_abort R_abort' r1 r2.
    lift_result R_ok R_term R_abort r1 r2 /\
    (!s1 s2. R_abort s1 s2 ==> R_abort' s1 s2) ==>
    lift_result R_ok R_term R_abort' r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def]
QED

(* not volatile implies not ext_call and not INVOKE *)
Triviality not_volatile_imp:
  !op. ~is_volatile op ==> ~is_ext_call_op op /\ op <> INVOKE
Proof
  Cases >> simp[is_volatile_def, is_ext_call_op_def]
QED

(* not barrier implies not volatile and not alloca *)
Triviality not_barrier_imp:
  !inst. ~is_barrier inst ==>
    ~is_volatile inst.inst_opcode /\ ~is_alloca_op inst.inst_opcode
Proof
  rw[is_barrier_def]
QED

(* ===== run_insts pointwise equivalence ===== *)

(* If two instruction lists have the same step_inst for all states
   (pointwise), then run_insts produces the same result. *)
Theorem run_insts_pointwise_equiv:
  !l1 l2 fuel ctx s.
    LENGTH l1 = LENGTH l2 /\
    (!k s'. k < LENGTH l1 ==>
            step_inst fuel ctx (EL k l1) s' = step_inst fuel ctx (EL k l2) s') ==>
    run_insts fuel ctx l1 s = run_insts fuel ctx l2 s
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >> Cases_on `l2` >> simp[run_insts_def] >>
  strip_tac >>
  `step_inst fuel ctx h s = step_inst fuel ctx h' s` by
    (first_x_assum (qspecl_then [`0`, `s`] mp_tac) >> simp[]) >>
  simp[] >>
  Cases_on `step_inst fuel ctx h' s` >> simp[] >>
  first_x_assum irule >> simp[] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`SUC k`, `s'`] mp_tac) >> simp[]
QED

(* ===== EDA-level commutativity (wider than ext_bi_independent) ===== *)

(* is_effect_free_op implies not alloca, not ext_call, not INVOKE *)
Triviality effect_free_not_alloca_ext:
  !op. is_effect_free_op op ==>
    ~is_alloca_op op /\ ~is_ext_call_op op /\ op <> INVOKE
Proof
  Cases >> simp[is_effect_free_op_def, is_alloca_op_def,
                is_ext_call_op_def]
QED

(* EDA-level commutativity: either ext_bi_independent (handles effects_independent)
   or both effect-free with disjoint defs/uses (handles memory-read-only gap).
   This is the widest predicate under which two non-pseudo body instructions
   can be swapped while preserving the OK result. *)
Definition eda_commutes_def:
  eda_commutes i1 i2 <=>
    ext_bi_independent i1 i2 \/
    (is_effect_free_op i1.inst_opcode /\ is_effect_free_op i2.inst_opcode /\
     DISJOINT (set (inst_defs i1)) (set (inst_uses i2)) /\
     DISJOINT (set (inst_defs i2)) (set (inst_uses i1)) /\
     DISJOINT (set (inst_defs i1)) (set (inst_defs i2)) /\
     ~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode)
End

Triviality eda_commutes_sym:
  !i1 i2. eda_commutes i1 i2 <=> eda_commutes i2 i1
Proof
  rw[eda_commutes_def] >> eq_tac >> strip_tac
  >- (disj1_tac >> fs[ext_bi_independent_sym])
  >- (disj2_tac >> fs[inst_defs_def, inst_uses_def, pred_setTheory.DISJOINT_SYM])
  >- (disj1_tac >> fs[ext_bi_independent_sym])
  >> (disj2_tac >> fs[inst_defs_def, inst_uses_def, pred_setTheory.DISJOINT_SYM])
QED

(* Backward transfer for effect-free ops: if a is effect-free and
   step_inst b succeeds on (step a s), then step_inst b succeeds on s
   (given disjoint defs/uses). *)
Triviality effect_free_backward_transfer:
  !fuel ctx a b s sa sab.
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab /\
    is_effect_free_op a.inst_opcode /\
    DISJOINT (set (inst_defs a)) (set (inst_uses b)) /\
    is_effect_free_op b.inst_opcode /\
    ~is_terminator b.inst_opcode ==>
    ?sb. step_inst fuel ctx b s = OK sb
Proof
  rpt strip_tac >>
  imp_res_tac effect_free_not_alloca_ext >>
  (`step_inst_base b sa = OK sab` by gvs[step_inst_non_invoke]) >>
  (`state_equiv (set a.inst_outputs) s sa` by
    metis_tac[step_effect_free_state_equiv]) >>
  (* Extract field equalities from state_equiv (only 1 state_equiv, safe) *)
  gvs[state_equiv_def, execution_equiv_def] >>
  qspecl_then [`b`, `sa`, `sab`, `s`] mp_tac
    passSharedPropsTheory.step_inst_base_ok_transfer >>
  simp[] >> strip_tac >>
  `!op. MEM op b.inst_operands ==> eval_operand op sa = eval_operand op s` by
    (rpt strip_tac >>
     Cases_on `op` >> simp[eval_operand_def] >>
     rename1 `MEM (Var vv) _` >>
     `~MEM vv a.inst_outputs` by
       (gvs[inst_defs_def, inst_uses_def,
            pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
        metis_tac[mem_var_operand_vars, listTheory.MEM]) >>
     first_x_assum (qspec_then `vv` mp_tac) >> simp[]) >>
  (* Fire the conditional assumption to get ∃v'. step_inst_base b s = OK v' *)
  first_x_assum drule >>
  strip_tac >> qexists_tac `v'` >> gvs[step_inst_non_invoke]
QED

(* Forward transfer: if b is effect-free and step a succeeds on s,
   then step a also succeeds on (step b s), given disjoint defs/uses. *)
Triviality effect_free_forward_transfer:
  !fuel ctx a b s sa sb.
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b s = OK sb /\
    is_effect_free_op b.inst_opcode /\
    DISJOINT (set (inst_defs b)) (set (inst_uses a)) /\
    is_effect_free_op a.inst_opcode /\
    ~is_terminator a.inst_opcode ==>
    ?sba. step_inst fuel ctx a sb = OK sba
Proof
  rpt strip_tac >>
  imp_res_tac effect_free_not_alloca_ext >>
  (`step_inst_base a s = OK sa` by gvs[step_inst_non_invoke]) >>
  (`state_equiv (set b.inst_outputs) s sb` by
    metis_tac[step_effect_free_state_equiv]) >>
  gvs[state_equiv_def, execution_equiv_def] >>
  qspecl_then [`a`, `s`, `sa`, `sb`] mp_tac
    passSharedPropsTheory.step_inst_base_ok_transfer >>
  simp[] >> strip_tac >>
  `!op. MEM op a.inst_operands ==> eval_operand op s = eval_operand op sb` by
    (rpt strip_tac >>
     Cases_on `op` >> simp[eval_operand_def] >>
     rename1 `MEM (Var vv) _` >>
     `~MEM vv b.inst_outputs` by
       (gvs[inst_defs_def, inst_uses_def,
            pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
        metis_tac[mem_var_operand_vars, listTheory.MEM]) >>
     first_x_assum (qspec_then `vv` mp_tac) >> simp[]) >>
  first_x_assum drule >>
  strip_tac >> qexists_tac `v'` >> gvs[step_inst_non_invoke]
QED

(* The core swap lemma for eda_commutes: if a→b OK, then b→a OK with same result *)
Triviality step_swap_ok_eda:
  !fuel ctx a b s sa sab.
    eda_commutes a b /\
    inst_wf a /\ inst_wf b /\
    ~is_pseudo a.inst_opcode /\ ~is_pseudo b.inst_opcode /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rpt strip_tac >>
  gvs[eda_commutes_def]
  (* Case 1: ext_bi_independent *)
  >- (drule_all step_swap_ok_ext >> simp[])
  (* Case 2: both effect_free with disjoint defs/uses *)
  >> (
    (* backward: ∃sb. step b s = OK sb *)
    qspecl_then [`fuel`,`ctx`,`a`,`b`,`s`,`sa`,`sab`]
      strip_assume_tac effect_free_backward_transfer >> gvs[] >>
    (* forward: ∃sba. step a sb = OK sba *)
    qspecl_then [`fuel`,`ctx`,`a`,`b`,`s`,`sa`,`sb`]
      strip_assume_tac effect_free_forward_transfer >> gvs[] >>
    (* commute_eq: sba = sab *)
    qspecl_then [`fuel`, `ctx`, `a`, `b`, `s`, `sa`, `sb`, `sab`, `sba`]
      mp_tac effect_free_commute_eq >>
    simp[])
QED

(* Instantiation: eda_commutes version (requires inst_wf + ~is_pseudo) *)
Theorem run_insts_topo_equiv_eda:
  !l1 l2 dep fuel ctx s r.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> eda_commutes x y) /\
    EVERY inst_wf l1 /\
    EVERY (\i. ~is_pseudo i.inst_opcode) l1 /\
    run_insts fuel ctx l1 s = OK r ==>
    run_insts fuel ctx l2 s = OK r
Proof
  rpt strip_tac >>
  qspecl_then [`eda_commutes`,
               `\i. inst_wf i /\ ~is_pseudo i.inst_opcode`,
               `l1`, `l2`, `dep`, `fuel`, `ctx`, `s`, `r`]
    mp_tac run_insts_topo_equiv_gen >>
  simp[EVERY_MEM] >> disch_then match_mp_tac >>
  rpt strip_tac
  >- metis_tac[eda_commutes_sym]
  >- metis_tac[step_swap_ok_eda]
  >> gvs[EVERY_MEM]
QED

(* ===== Block body lift_result ===== *)

(* Helper: block_perm_of with matching label resolves to bb *)
Triviality block_perm_of_resolves:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label ==>
    FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions /\
    EVERY (\i. from_block bb.bb_instructions i)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions)
Proof
  rpt strip_tac >> gvs[block_perm_of_def] >>
  `bb_orig = bb` by
    (gvs[wf_function_def, fn_labels_def] >>
     `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
       (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
     `lookup_block bb.bb_label fn.fn_blocks = SOME bb_orig` by
       (irule venomExecPropsTheory.MEM_lookup_block >> simp[]) >>
     gvs[]) >>
  pop_assum SUBST_ALL_TAC >> gvs[]
QED

(* Helper: run_insts on body of bb' equals run_insts on body of bb
   when both OK (no Error case needed for OK). *)
Triviality from_block_step_inst_equiv:
  !bi i. from_block bi i ==>
    ?j. MEM j bi /\ ~is_pseudo j.inst_opcode /\
        i.inst_id = j.inst_id /\
        !fuel ctx s. step_inst fuel ctx i s = step_inst fuel ctx j s
Proof
  rw[from_block_def]
  >- (qexists_tac `i` >> simp[])
  >> qexists_tac `j` >> simp[flip_operands_inst_id, flip_operands_step_inst]
QED

(* Key: from_block instructions produce identical step_inst results, so
   run_insts on a from_block permutation = run_insts on originals in
   the same order. We reduce to run_insts_topo_equiv_eda via an
   intermediate "originals" list constructed by Hilbert choice. *)
Triviality flip_operands_not_terminator:
  !i. ~is_terminator (flip_operands i).inst_opcode ==>
    ~is_terminator i.inst_opcode
Proof
  rw[flip_operands_def] >> every_case_tac >> gvs[] >>
  gvs[is_terminator_def, passSharedDefsTheory.is_comparator_def,
      passSharedDefsTheory.flip_comparison_opcode_def]
QED

Triviality from_block_not_terminator:
  !bi i. from_block bi i /\ ~is_terminator i.inst_opcode ==>
    ?j. MEM j bi /\ ~is_pseudo j.inst_opcode /\
        ~is_terminator j.inst_opcode /\
        i.inst_id = j.inst_id /\
        !fuel ctx s. step_inst fuel ctx i s = step_inst fuel ctx j s
Proof
  rw[from_block_def]
  >- (qexists_tac `i` >> simp[])
  >> qexists_tac `j` >> simp[flip_operands_inst_id, flip_operands_step_inst] >>
  metis_tac[flip_operands_not_terminator]
QED

(* Choose an original instruction from l1 for each instruction in l2 *)
Definition choose_original_def:
  choose_original l1 i = @j. MEM j l1 /\ j.inst_id = i.inst_id
End

Triviality choose_original_correct:
  !l1 i j.
    MEM j l1 /\ j.inst_id = i.inst_id ==>
    MEM (choose_original l1 i) l1 /\
    (choose_original l1 i).inst_id = i.inst_id
Proof
  rw[choose_original_def] >> SELECT_ELIM_TAC >> metis_tac[]
QED

Triviality choose_original_unique:
  !l1 i j.
    MEM j l1 /\ j.inst_id = i.inst_id /\
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) ==>
    choose_original l1 i = j
Proof
  rw[choose_original_def] >> SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  metis_tac[all_distinct_map_mem_inj]
QED

(* EDA dependency relation: x depends on y iff some inst with y's inst_id
   is in x's dep list. Defined via inst_ids for transferability. *)
Definition eda_dep_def:
  eda_dep eda x y <=>
    ?d. MEM d (case FLOOKUP eda x.inst_id of NONE => [] | SOME ds => ds) /\
        d.inst_id = y.inst_id
End

(* eda_topo_compatible implies topo_sorted for non-pseudo instructions *)
Triviality eda_topo_compatible_topo_sorted:
  !bi eda order.
    eda_topo_compatible bi eda order /\
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    topo_sorted (eda_dep eda)
      (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)
Proof
  rw[topo_sorted_def, eda_dep_def] >>
  qabbrev_tac `fl = FILTER (\i. ~is_pseudo i.inst_opcode /\
                                 ~is_terminator i.inst_opcode) bi` >>
  spose_not_then strip_assume_tac >>
  (* d witnesses the eda_dep: MEM d (FLOOKUP eda fl[i].inst_id), d.inst_id = fl[j].inst_id *)
  (* d is MEM bi and non-pseudo from eda_wf *)
  `MEM d bi /\ ~is_pseudo d.inst_opcode` by
    (fs[eda_wf_def] >>
     Cases_on `FLOOKUP eda (EL i fl).inst_id` >> gvs[] >>
     metis_tac[]) >>
  (* fl elements are in bi *)
  `MEM (EL j fl) bi` by
    (`MEM (EL j fl) fl` by (simp[MEM_EL] >> qexists `j` >> simp[]) >>
     fs[Abbr `fl`, MEM_FILTER]) >>
  (* d = fl[j] by ALL_DISTINCT inst_ids *)
  `d = EL j fl` by metis_tac[all_distinct_map_mem_inj] >>
  (* fl[i] is MEM bi and non-pseudo *)
  `MEM (EL i fl) bi /\ ~is_pseudo (EL i fl).inst_opcode` by
    (`MEM (EL i fl) fl` by (simp[MEM_EL] >> qexists `i` >> simp[]) >>
     fs[Abbr `fl`, MEM_FILTER]) >>
  (* fl[j] is in inst_all_deps of fl[i] (via eda deps) *)
  `MEM (EL j fl) (inst_all_deps bi order eda (EL i fl))` by
    (simp[inst_all_deps_def, LET_THM, MEM_nub] >>
     Cases_on `FLOOKUP eda (EL i fl).inst_id` >> gvs[]) >>
  (* eda_topo_compatible: dep fl[j] before inst fl[i] in bi *)
  `?p q. p < q /\ q < LENGTH bi /\ p < LENGTH bi /\
         EL p bi = EL j fl /\ EL q bi = EL i fl` by
    (fs[eda_topo_compatible_def] >>
     first_x_assum (qspecl_then [`EL i fl`, `EL j fl`] mp_tac) >>
     simp[]) >>
  (* filter_el_mono: fl[i] before fl[j] in bi *)
  `?a b. a < b /\ b < LENGTH bi /\
         EL a bi = EL i fl /\ EL b bi = EL j fl` by
    (qspecl_then [`\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode`,
                  `bi`, `i`, `j`] mp_tac filter_el_mono >>
     simp[Abbr `fl`]) >>
  (* ALL_DISTINCT: bi[a] = bi[q] = fl[i], bi[b] = bi[p] = fl[j] *)
  `a = q /\ b = p` by
    (`a < LENGTH bi` by simp[] >>
     `EL a (MAP (\i. i.inst_id) bi) = EL q (MAP (\i. i.inst_id) bi)` by
       simp[EL_MAP] >>
     `EL b (MAP (\i. i.inst_id) bi) = EL p (MAP (\i. i.inst_id) bi)` by
       simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  (* a < b = p < q = a — contradiction *)
  simp[]
QED

(* Combined dependency: eda + data deps + output aliasing.
   full_dep eda x y means "x depends on y" = "y must come before x" *)
Definition full_dep_def:
  full_dep eda x y <=>
    eda_dep eda x y \/
    ~DISJOINT (set (inst_uses x)) (set (inst_defs y)) \/
    ~DISJOINT (set (inst_defs x)) (set (inst_defs y))
End

(* Strengthen topo_sorted with additional dep *)
Triviality topo_sorted_strengthen:
  !dep1 dep2 l.
    topo_sorted dep1 l /\
    (!i j. i < j /\ j < LENGTH l ==> ~dep2 (EL i l) (EL j l)) ==>
    topo_sorted (\x y. dep1 x y \/ dep2 x y) l
Proof
  rw[topo_sorted_def] >> metis_tac[]
QED

(* full_non_dep_commutes is FALSE in general (intervening writer scenario:
   MSTORE_A, MSTORE_B, MLOAD_C — no direct full_dep between A and C, but
   ~eda_commutes since ~effects_independent MSTORE MLOAD).
   We need TC (transitive closure) of full_dep to rule this out. *)

(* topo_sorted is preserved by transitive closure when dep is closed on l
   and l has no duplicates. Each dep step decreases position index;
   a TC chain from pos i can only reach positions ≤ i, contradicting j > i. *)
(* Helper: TC chain decreases position in a topo-sorted list *)
Triviality tc_decreases_position:
  !dep a b.
    TC dep a b ==>
    !l k.
      topo_sorted dep l /\
      (!x y. dep x y ==> MEM x l /\ MEM y l) /\
      k < LENGTH l /\ a = EL k l ==>
      ?m. m <= k /\ m < LENGTH l /\ b = EL m l
Proof
  gen_tac >> ho_match_mp_tac TC_INDUCT_RIGHT1 >> rpt conj_tac
  (* Base: dep a b *)
  >- (rpt strip_tac >>
      `MEM b l` by
        (qpat_x_assum `!x y. dep x y ==> _`
           (qspecl_then [`a`,`b`] mp_tac) >> simp[]) >>
      pop_assum (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
      rename1 `b = EL nb l` >>
      qexists `nb` >> simp[] >>
      spose_not_then assume_tac >>
      `k < nb` by simp[] >>
      fs[topo_sorted_def])
  (* Step: TC dep a b, dep b b' — IH gives b at pos mc <= k *)
  >> rpt strip_tac >>
     first_x_assum (qspecl_then [`l`, `k`] mp_tac) >>
     (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
     rename1 `b = EL mc l` >>
     `MEM b' l` by
       (qpat_x_assum `!x y. dep x y ==> _`
          (qspecl_then [`b`,`b'`] mp_tac) >> simp[]) >>
     pop_assum (strip_assume_tac o REWRITE_RULE [MEM_EL]) >>
     rename1 `b' = EL mb l` >>
     qexists `mb` >> simp[] >>
     spose_not_then assume_tac >>
     `mc < mb` by simp[] >>
     fs[topo_sorted_def]
QED

Theorem topo_sorted_tc_closed:
  !dep l.
    topo_sorted dep l /\ ALL_DISTINCT l /\
    (!x y. dep x y ==> MEM x l /\ MEM y l) ==>
    topo_sorted (TC dep) l
Proof
  rw[topo_sorted_def] >>
  spose_not_then strip_assume_tac >>
  drule tc_decreases_position >>
  disch_then (qspecl_then [`l`, `i`] mp_tac) >>
  (impl_tac >- (simp[topo_sorted_def] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* m ≤ i < j, m < LENGTH l, j < LENGTH l, l[j] = l[m], ALL_DISTINCT l *)
  `m = j` by
    (qspecl_then [`l`,`m`,`j`] mp_tac ALL_DISTINCT_EL_IMP >>
     simp[]) >>
  simp[]
QED

(* Every non-pseudo, non-terminator opcode is either effect_free or a barrier *)
Theorem effect_free_or_barrier:
  !i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode ==>
      is_effect_free_op i.inst_opcode \/ is_barrier i
Proof
  rpt strip_tac >> Cases_on `i.inst_opcode` >>
  gvs[is_effect_free_op_def, is_barrier_def, is_raw_fmp_opcode_def,
      is_volatile_def, is_alloca_op_def, is_pseudo_def, is_terminator_def]
QED

(* If both non-pseudo, non-terminator, and BOTH effect_free (hence
   non-barrier), and ~full_dep in both directions → eda_commutes
   via the effect_free disjunct *)
Triviality effect_free_non_dep_commutes:
  !eda x y.
    is_effect_free_op x.inst_opcode /\ is_effect_free_op y.inst_opcode /\
    ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
    ~full_dep eda x y /\ ~full_dep eda y x ==>
    eda_commutes x y
Proof
  rw[full_dep_def, eda_commutes_def] >>
  disj2_tac >> gvs[pred_setTheory.DISJOINT_SYM]
QED

(* ===== Barrier TC connectivity ===== *)

(* Subsequent EDA passes are monotone: add_chain_deps, add_barrier_deps, etc.
   only add entries, never remove existing deps. *)

(* FOLDL (\ds p. if MEM p ds then ds else p :: ds) preserves existing members *)
Theorem foldl_add_preserves_mem:
  !ps ds x. MEM x ds ==>
    MEM x (FOLDL (\ds p. if MEM p ds then ds else p :: ds) ds ps)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  IF_CASES_TAC >> simp[]
QED

(* add_deps_from_barrier preserves existing deps — let-expanded FOLDL body *)
Theorem add_deps_from_barrier_foldl_mono:
  !non_phis acc prev_insts id d.
    MEM d (case FLOOKUP acc id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (FST (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        (acc |+ (inst.inst_id,
           FOLDL (\ds p. if MEM p ds then ds else p :: ds)
             (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             prev_insts), prev_insts ++ [inst])
      else
        (acc, prev_insts ++ [inst]))
    (acc, prev_insts) non_phis)) id of NONE => [] | SOME ds => ds)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `is_barrier h` >> gvs[] >>
  first_x_assum irule >>
  Cases_on `h.inst_id = id` >> simp[FLOOKUP_UPDATE] >>
  irule foldl_add_preserves_mem >>
  Cases_on `FLOOKUP acc id` >> gvs[]
QED

Theorem add_deps_from_barrier_mono:
  !bi eda id d.
    MEM d (case FLOOKUP eda id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (add_deps_from_barrier bi eda) id of
             NONE => [] | SOME ds => ds)
Proof
  rw[add_deps_from_barrier_def, LET_THM] >>
  irule add_deps_from_barrier_foldl_mono >> simp[]
QED

(* add_deps_on_barrier: let-expanded FOLDL mono *)
Theorem add_deps_on_barrier_foldl_mono:
  !non_phis acc last_bar id d.
    MEM d (case FLOOKUP acc id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (FST (FOLDL (\(acc, last_bar) inst.
      if is_barrier inst then
        (acc, SOME inst)
      else
        (acc |+ (inst.inst_id,
           case last_bar of
             NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
           | SOME b =>
               if MEM b (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
               then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
               else b :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
         last_bar))
    (acc, last_bar) non_phis)) id of NONE => [] | SOME ds => ds)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `is_barrier h` >> gvs[] >>
  first_x_assum irule >>
  Cases_on `h.inst_id = id` >> simp[FLOOKUP_UPDATE] >>
  Cases_on `last_bar` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP acc id` >> gvs[]
QED

Theorem add_deps_on_barrier_mono:
  !bi eda id d.
    MEM d (case FLOOKUP eda id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (add_deps_on_barrier bi eda) id of
             NONE => [] | SOME ds => ds)
Proof
  rw[add_deps_on_barrier_def, LET_THM] >>
  irule add_deps_on_barrier_foldl_mono >> simp[]
QED

(* add_chain_deps: let-expanded FOLDL mono *)
Theorem add_chain_deps_foldl_mono:
  !matching acc prev id d.
    MEM d (case FLOOKUP acc id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (FST (FOLDL (\(acc, prev) inst.
      (acc |+ (inst.inst_id,
         case prev of
           NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
         | SOME p =>
             if MEM p (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             else p :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
       SOME inst))
    (acc, prev) matching)) id of NONE => [] | SOME ds => ds)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  Cases_on `h.inst_id = id` >> simp[FLOOKUP_UPDATE] >>
  Cases_on `prev` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `FLOOKUP acc id` >> gvs[]
QED

Theorem add_chain_deps_mono:
  !P bi eda id d.
    MEM d (case FLOOKUP eda id of NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (add_chain_deps P bi eda) id of
             NONE => [] | SOME ds => ds)
Proof
  rw[add_chain_deps_def, LET_THM] >>
  irule add_chain_deps_foldl_mono >> simp[]
QED

(* build_full_eda is monotone over add_barrier_deps *)
Triviality build_full_eda_mono_barrier:
  !bi id d.
    MEM d (case FLOOKUP (add_barrier_deps bi (add_abort_deps bi (build_eda bi))) id of
             NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (build_full_eda bi) id of NONE => [] | SOME ds => ds)
Proof
  rw[build_full_eda_def, add_alloca_deps_def] >>
  irule add_chain_deps_mono >> simp[]
QED

(* Combined: add_deps_from_barrier result survives to build_full_eda *)
Theorem build_full_eda_mono_from_barrier:
  !bi id d.
    MEM d (case FLOOKUP
      (add_deps_from_barrier bi
        (add_deps_on_barrier bi
          (add_abort_deps bi (build_eda bi)))) id of
             NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (build_full_eda bi) id of NONE => [] | SOME ds => ds)
Proof
  rw[build_full_eda_def, add_barrier_deps_def, add_alloca_deps_def] >>
  irule add_chain_deps_mono >> simp[]
QED

(* add_deps_on_barrier result survives through add_deps_from_barrier to build_full_eda *)
Theorem build_full_eda_mono_on_barrier:
  !bi id d.
    MEM d (case FLOOKUP
      (add_deps_on_barrier bi
        (add_abort_deps bi (build_eda bi))) id of
             NONE => [] | SOME ds => ds) ==>
    MEM d (case FLOOKUP (build_full_eda bi) id of NONE => [] | SOME ds => ds)
Proof
  rpt strip_tac >> irule build_full_eda_mono_from_barrier >>
  irule add_deps_from_barrier_mono >> simp[]
QED

(* ===== FOLDL add_if_absent: prev members end up in result ===== *)
Triviality foldl_add_includes_prev:
  !ps ds x. MEM x ps ==>
    MEM x (FOLDL (\ds p. if MEM p ds then ds else p :: ds) ds ps)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[] >>
  TRY (Cases_on `MEM h ds` >> simp[foldl_add_preserves_mem] >> NO_TAC) >>
  first_x_assum irule >> simp[]
QED

(* ===== add_deps_from_barrier spec: barrier gets deps on all preceding ===== *)

(* Helper: FOLDL prev_insts accumulates all processed elements *)
Triviality from_barrier_snd_accumulates:
  !non_phis acc prev_insts.
    SND (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        (acc |+ (inst.inst_id,
           FOLDL (\ds p. if MEM p ds then ds else p :: ds)
             (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             prev_insts), prev_insts ++ [inst])
      else (acc, prev_insts ++ [inst]))
    (acc, prev_insts) non_phis) = prev_insts ++ non_phis
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `is_barrier h` >> simp[]
QED

(* Helper: barrier x gets all prev_insts when processed *)
Theorem from_barrier_at_barrier:
  !non_phis acc prev_insts x suffix.
    non_phis = x :: suffix /\ is_barrier x ==>
    !y. MEM y prev_insts ==>
    MEM y (case FLOOKUP (FST (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        (acc |+ (inst.inst_id,
           FOLDL (\ds p. if MEM p ds then ds else p :: ds)
             (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             prev_insts), prev_insts ++ [inst])
      else (acc, prev_insts ++ [inst]))
    (acc, prev_insts) non_phis)) x.inst_id of NONE => [] | SOME ds => ds)
Proof
  rpt strip_tac >> gvs[] >> simp[FOLDL] >>
  irule add_deps_from_barrier_foldl_mono >>
  simp[FLOOKUP_UPDATE] >>
  irule foldl_add_includes_prev >> simp[]
QED

(* Main spec: after processing, barrier x has all preceding non-phis as deps.
   Split-based formulation: non_phis = prefix ++ [x] ++ suffix *)
Triviality add_deps_from_barrier_foldl_spec:
  !prefix x suffix acc prev_insts.
    ALL_DISTINCT (MAP (\i. i.inst_id) (prev_insts ++ prefix ++ [x] ++ suffix)) /\
    is_barrier x ==>
    !y. MEM y (prev_insts ++ prefix) ==>
    MEM y (case FLOOKUP (FST (FOLDL (\(acc, prev_insts) inst.
      if is_barrier inst then
        (acc |+ (inst.inst_id,
           FOLDL (\ds p. if MEM p ds then ds else p :: ds)
             (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
             prev_insts), prev_insts ++ [inst])
      else (acc, prev_insts ++ [inst]))
    (acc, prev_insts) (prefix ++ [x] ++ suffix))) x.inst_id of
      NONE => [] | SOME ds => ds)
Proof
  Induct >> rpt strip_tac
  >- suspend "base"
  >> suspend "step"
QED

Resume add_deps_from_barrier_foldl_spec[base]:
  gvs[] >>
  irule (SRULE [] from_barrier_at_barrier) >> simp[]
QED

Resume add_deps_from_barrier_foldl_spec[step]:
  (* Unfold one FOLDL step for h, then apply IH.
     Both barrier/non-barrier cases: prev_insts becomes prev_insts ++ [h],
     acc may change. IH universally quantifies both. *)
  simp[FOLDL] >>
  Cases_on `is_barrier h` >> simp[] >> (
    (* In both cases, apply IH with prev_insts := prev_insts ++ [h] *)
    first_x_assum irule >> simp[] >>
    fs[ALL_DISTINCT_APPEND, MAP_APPEND, MEM_MAP, MEM_APPEND] >>
    metis_tac[])
QED

Finalise add_deps_from_barrier_foldl_spec

(* ===== add_deps_on_barrier spec ===== *)

(* Helper: SND of add_deps_on_barrier's FOLDL tracks last_bar.
   After processing a list, last_bar = last barrier in list (or initial). *)
Triviality on_barrier_snd_last_bar:
  !non_phis acc last_bar.
    SND (FOLDL (\(acc, last_bar) inst.
      if is_barrier inst then (acc, SOME inst)
      else (acc |+ (inst.inst_id,
              case last_bar of
                NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
              | SOME b =>
                  if MEM b (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  else b :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
           last_bar))
    (acc, last_bar) non_phis) =
    case FILTER is_barrier non_phis of
      [] => last_bar
    | bs => SOME (LAST bs)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `is_barrier h` >> simp[] >>
  Cases_on `FILTER is_barrier non_phis` >> simp[]
QED

(* Helper: when processing non-barrier x with last_bar = SOME b,
   b ends up in x's deps in the result acc *)
Theorem on_barrier_at_inst:
  !x suffix acc b.
    ~is_barrier x ==>
    MEM b (case FLOOKUP (FST (FOLDL (\(acc, last_bar) inst.
      if is_barrier inst then (acc, SOME inst)
      else (acc |+ (inst.inst_id,
              case last_bar of
                NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
              | SOME b =>
                  if MEM b (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  else b :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
           last_bar))
    (acc, SOME b) (x :: suffix))) x.inst_id of NONE => [] | SOME ds => ds)
Proof
  rpt strip_tac >> simp[FOLDL] >>
  irule add_deps_on_barrier_foldl_mono >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on `MEM b (case FLOOKUP acc x.inst_id of NONE => [] | SOME ds => ds)` >>
  simp[]
QED

(* Main spec: if prefix contains a barrier and x is non-barrier,
   then the last barrier in prefix is in x's deps.
   FOLDL processes prefix ++ [x] ++ suffix starting with (acc, last_bar_init). *)
Theorem add_deps_on_barrier_foldl_spec:
  !prefix x suffix acc last_bar_init b.
    ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ [x] ++ suffix)) /\
    ~is_barrier x /\
    (case FILTER is_barrier prefix of
       [] => last_bar_init = SOME b
     | bs => LAST bs = b) ==>
    MEM b (case FLOOKUP (FST (FOLDL (\(acc, last_bar) inst.
      if is_barrier inst then (acc, SOME inst)
      else (acc |+ (inst.inst_id,
              case last_bar of
                NONE => (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
              | SOME b =>
                  if MEM b (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
                  else b :: (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
           last_bar))
    (acc, last_bar_init) (prefix ++ [x] ++ suffix))) x.inst_id of
      NONE => [] | SOME ds => ds)
Proof
  Induct >> rpt strip_tac
  >- ((* Base: prefix = [], last_bar_init = SOME b *)
      gvs[] >>
      qspecl_then [`x`, `suffix`, `acc`, `b`] mp_tac on_barrier_at_inst >>
      simp[])
  >> ((* Step: unfold one FOLDL step for h, apply IH *)
      Cases_on `is_barrier h` >> gvs[FILTER] >>
      simp[FOLDL] >>
      first_x_assum irule >> simp[] >>
      fs[ALL_DISTINCT_APPEND, MAP_APPEND, MEM_MAP, MEM_APPEND] >>
      Cases_on `FILTER is_barrier prefix` >> simp[])
QED

(* MAP choose_original preserves PERM of inst_ids *)
Triviality map_choose_original_perm:
  !l1 l2.
    PERM (MAP (\i. i.inst_id) l1) (MAP (\i. i.inst_id) l2) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) /\
    (!i. MEM i l2 ==> ?j. MEM j l1 /\ j.inst_id = i.inst_id) ==>
    PERM l1 (MAP (choose_original l1) l2)
Proof
  rpt strip_tac >>
  MATCH_MP_TAC PERM_ALL_DISTINCT >> rpt conj_tac
  >- suspend "ad_l1"
  >- suspend "ad_map"
  >> suspend "mem_eq"
QED

Resume map_choose_original_perm[ad_l1]:
  metis_tac[ALL_DISTINCT_MAP]
QED

Resume map_choose_original_perm[ad_map]:
  (`ALL_DISTINCT (MAP (\i. i.inst_id) l2)` by
    metis_tac[ALL_DISTINCT_PERM]) >>
  (`ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_MAP]) >>
  irule ALL_DISTINCT_MAP_INJ >> conj_tac
  >- (rpt strip_tac >>
      `(choose_original l1 x).inst_id = x.inst_id` by
        (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
      `(choose_original l1 y).inst_id = y.inst_id` by
        (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
      `x.inst_id = y.inst_id` by metis_tac[] >>
      metis_tac[all_distinct_map_mem_inj])
  >- simp[]
QED

Resume map_choose_original_perm[mem_eq]:
  gen_tac >> eq_tac >> strip_tac
  >- suspend "fwd"
  >> suspend "bwd"
QED

Resume map_choose_original_perm[fwd]:
  (* MEM x l1 → MEM x (MAP (choose_original l1) l2) *)
  simp[MEM_MAP] >>
  drule PERM_MEM_EQ >>
  disch_then (qspec_then `x.inst_id` mp_tac) >>
  simp[MEM_MAP] >>
  disch_then (mp_tac o #1 o EQ_IMP_RULE) >>
  (impl_tac >- (qexists `x` >> simp[])) >>
  strip_tac >> rename1 `MEM z l2` >>
  qexists `z` >> conj_tac >- metis_tac[choose_original_unique] >>
  simp[]
QED

Resume map_choose_original_perm[bwd]:
  (* MEM x (MAP (choose_original l1) l2) → MEM x l1 *)
  fs[MEM_MAP] >> metis_tac[choose_original_correct]
QED

Finalise map_choose_original_perm

(* MAP choose_original gives pointwise step_inst equivalence *)
Theorem map_choose_original_step_equiv:
  !l1 l2 fuel ctx.
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) /\
    (!i. MEM i l2 ==>
      ?j. MEM j l1 /\ j.inst_id = i.inst_id /\
          !fuel ctx s. step_inst fuel ctx i s = step_inst fuel ctx j s) ==>
    !k s. k < LENGTH l2 ==>
      step_inst fuel ctx (EL k l2) s =
      step_inst fuel ctx (EL k (MAP (choose_original l1) l2)) s
Proof
  rpt strip_tac >>
  simp[EL_MAP] >>
  `MEM (EL k l2) l2` by metis_tac[MEM_EL] >>
  res_tac >> rename1 `MEM j l1` >>
  `choose_original l1 (EL k l2) = j` by
    (irule choose_original_unique >> metis_tac[]) >>
  metis_tac[]
QED

(* topo_sorted transfers through choose_original mapping *)
Triviality map_choose_original_topo_sorted:
  !l1 l2 dep.
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) /\
    topo_sorted dep l2 /\
    (!i. MEM i l2 ==> ?j. MEM j l1 /\ j.inst_id = i.inst_id) /\
    (* dep only depends on inst_id *)
    (!x y x' y'. x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id ==>
       (dep x y <=> dep x' y')) ==>
    topo_sorted dep (MAP (choose_original l1) l2)
Proof
  rw[topo_sorted_def, LENGTH_MAP] >>
  simp[EL_MAP] >>
  `MEM (EL i l2) l2` by (simp[MEM_EL] >> qexists `i` >> simp[]) >>
  `MEM (EL j l2) l2` by (simp[MEM_EL] >> qexists `j` >> simp[]) >>
  `(choose_original l1 (EL i l2)).inst_id = (EL i l2).inst_id` by
    (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
  `(choose_original l1 (EL j l2)).inst_id = (EL j l2).inst_id` by
    (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
  metis_tac[]
QED

(* eda_dep only depends on inst_id *)
Theorem eda_dep_inst_id_only:
  !eda x y x' y'.
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id ==>
    (eda_dep eda x y <=> eda_dep eda x' y')
Proof
  rw[eda_dep_def]
QED

(* Effect-free swap: no inst_wf needed. If both effect-free with disjoint
   defs/uses, step a→b OK implies step b→a OK with same result. *)
Theorem step_swap_ok_effect_free:
  !fuel ctx a b s sa sab.
    is_effect_free_op a.inst_opcode /\ is_effect_free_op b.inst_opcode /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    DISJOINT (set (inst_defs a)) (set (inst_uses b)) /\
    DISJOINT (set (inst_defs b)) (set (inst_uses a)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b)) /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rpt strip_tac >>
  qspecl_then [`fuel`,`ctx`,`a`,`b`,`s`,`sa`,`sab`]
    strip_assume_tac effect_free_backward_transfer >> gvs[] >>
  qspecl_then [`fuel`,`ctx`,`a`,`b`,`s`,`sa`,`sb`]
    strip_assume_tac effect_free_forward_transfer >> gvs[] >>
  qspecl_then [`fuel`, `ctx`, `a`, `b`, `s`, `sa`, `sb`, `sab`, `sba`]
    mp_tac effect_free_commute_eq >>
  simp[]
QED

(* Effect-free commutation predicate — no inst_wf needed *)
Definition ef_commutes_def:
  ef_commutes a b <=>
    is_effect_free_op a.inst_opcode /\ is_effect_free_op b.inst_opcode /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    DISJOINT (set (inst_defs a)) (set (inst_uses b)) /\
    DISJOINT (set (inst_defs b)) (set (inst_uses a)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b))
End

Triviality ef_commutes_sym:
  !a b. ef_commutes a b ==> ef_commutes b a
Proof
  rw[ef_commutes_def, pred_setTheory.DISJOINT_SYM]
QED

(* Non-dep, non-barrier → ef_commutes *)
Triviality non_dep_non_barrier_ef_commutes:
  !eda x y.
    ~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
    is_effect_free_op x.inst_opcode /\ is_effect_free_op y.inst_opcode /\
    ~full_dep eda x y /\ ~full_dep eda y x ==>
    ef_commutes x y
Proof
  rw[full_dep_def, ef_commutes_def, pred_setTheory.DISJOINT_SYM]
QED

(* Instantiation: ef_commutes topo_equiv (no inst_wf) *)
Theorem run_insts_topo_equiv_ef:
  !l1 l2 dep fuel ctx s r.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> ef_commutes x y) /\
    run_insts fuel ctx l1 s = OK r ==>
    run_insts fuel ctx l2 s = OK r
Proof
  rpt strip_tac >>
  qspecl_then [`ef_commutes`,
               `\i:instruction. T`,
               `l1`, `l2`, `dep`, `fuel`, `ctx`, `s`, `r`]
    mp_tac run_insts_topo_equiv_gen >>
  simp[EVERY_MEM] >> disch_then match_mp_tac >>
  rpt strip_tac
  >- metis_tac[ef_commutes_sym]
  >> (gvs[ef_commutes_def] >> metis_tac[step_swap_ok_effect_free])
QED

(* ===== block_body_ok_equiv skeleton ===== *)

(* MEM x l ==> ?pfx sfx. l = pfx ++ [x] ++ sfx *)
Triviality last_split_sfx_nil:
  !pfx x sfx.
    x = LAST (pfx ++ [x] ++ sfx) /\ ALL_DISTINCT (pfx ++ [x] ++ sfx) ==>
    sfx = []
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  Cases_on `sfx` >- gvs[] >>
  `LAST (pfx ++ [x] ++ h::t) = LAST (h::t)` by
    (once_rewrite_tac [GSYM APPEND_ASSOC] >>
     simp[LAST_APPEND_CONS, LAST_CONS_cond]) >>
  `MEM x (h::t)` by metis_tac[MEM_LAST] >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM]
QED

Triviality last_split_sfx_nil_map:
  !f pfx x sfx.
    f x = LAST (MAP f (pfx ++ [x] ++ sfx)) /\
    ALL_DISTINCT (MAP f (pfx ++ [x] ++ sfx)) ==>
    sfx = []
Proof
  rpt strip_tac >>
  spose_not_then assume_tac >>
  Cases_on `sfx` >- gvs[] >>
  gvs[MAP_APPEND, LAST_APPEND_CONS] >>
  `MEM (f x) (MAP f (h::t))` by
    (qpat_assum `f x = _` SUBST1_TAC >>
     irule MEM_MAP_f >> simp[MEM_LAST]) >>
  gvs[ALL_DISTINCT_APPEND, MEM_MAP] >>
  metis_tac[MEM]
QED

Triviality mem_split_append:
  !x l. MEM x l ==> ?pfx sfx. l = pfx ++ [x] ++ sfx
Proof
  metis_tac[MEM_SPLIT_APPEND_first]
QED

Triviality fn_insts_blocks_flat_dft:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

Triviality flat_map_outputs_fn_insts_blocks:
  !bbs.
    FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) =
    FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* block body instructions have ALL_DISTINCT inst_ids *)
Triviality all_distinct_flat_mem:
  !ls l. ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

(* General: if ALL_DISTINCT (FLAT (MAP f ls)), distinct elements a,b of ls
   have disjoint images under f *)
Triviality all_distinct_flat_map_disjoint:
  !ls f a b x.
    ALL_DISTINCT (FLAT (MAP f ls)) /\
    MEM a ls /\ MEM b ls /\ a <> b /\
    MEM x (f a) ==> ~MEM x (f b)
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[MAP, FLAT, ALL_DISTINCT_APPEND]
  >> metis_tac[MEM_FLAT, MEM_MAP]
QED

Triviality all_distinct_flat_map_unique[local]:
  !ls f (a:'a) b (x:'b).
    ALL_DISTINCT (FLAT (MAP f ls)) /\
    MEM a ls /\ MEM b ls /\ MEM x (f a) /\ MEM x (f b) ==>
    a = b
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

Triviality all_distinct_flat_map_filter[local]:
  !f P l. ALL_DISTINCT (FLAT (MAP f l)) ==>
          ALL_DISTINCT (FLAT (MAP f (FILTER P l)))
Proof
  Induct_on `l` >> simp[] >> rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> simp[] >>
  fs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, MEM_FILTER] >>
  metis_tac[]
QED

Theorem block_body_all_distinct:
  !fn bb.
    wf_function fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (block_body bb))
Proof
  rpt strip_tac >>
  simp[block_body_def] >>
  irule all_distinct_map_filter >>
  irule all_distinct_flat_mem >>
  qexists `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks` >>
  gvs[wf_function_def, fn_inst_ids_distinct_def] >>
  simp[MEM_MAP] >> qexists `bb` >> simp[]
QED

(* Given wf_function with distinct labels, block_perm_of's witness
   bb_orig must equal any fn block with the same label *)
Triviality block_perm_of_orig_unique:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label ==>
    !bb_orig.
      MEM bb_orig fn.fn_blocks /\ bb'.bb_label = bb_orig.bb_label ==>
      bb_orig = bb
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  `lookup_block bb.bb_label fn.fn_blocks = SOME bb_orig` by
    (irule MEM_lookup_block >> simp[]) >>
  gvs[]
QED

(* Eliminate block_perm_of: replace bb_orig with bb *)
Theorem block_perm_of_elim:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label ==>
    EVERY (\i. from_block bb.bb_instructions i)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions) /\
    PERM (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions))
         (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)) /\
    FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions
Proof
  rpt strip_tac >>
  `!bb_orig. MEM bb_orig fn.fn_blocks /\
             bb'.bb_label = bb_orig.bb_label ==> bb_orig = bb` by
    (rpt strip_tac >> irule block_perm_of_orig_unique >> metis_tac[]) >>
  fs[block_perm_of_def] >>
  `bb_orig = bb` by (first_x_assum irule >> simp[]) >>
  gvs[]
QED

(* flip_operands preserves is_terminator *)
Triviality is_flippable_not_terminator:
  !op. is_flippable op ==> ~is_terminator op
Proof
  Cases >> simp[is_flippable_def, is_commutative_def, is_comparator_def,
                is_terminator_def]
QED

(* block_body bb' instructions have from_block equivalents *)
Theorem block_body_from_block:
  !fn bb bb' i.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    MEM i (block_body bb') ==>
    ?j. MEM j (block_body bb) /\ j.inst_id = i.inst_id /\
        !fuel ctx s. step_inst fuel ctx i s = step_inst fuel ctx j s
Proof
  rpt strip_tac >>
  gvs[block_body_def, MEM_FILTER] >>
  drule_all block_perm_of_elim >> strip_tac >>
  (* Instantiate EVERY for i, get from_block *)
  fs[EVERY_MEM, MEM_FILTER] >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  (* Case split: i = j (original) or i = flip_operands j *)
  fs[from_block_def] >> gvs[]
  >- (qexists `i` >> simp[])
  >> (qexists `j` >>
      simp[flip_operands_inst_id] >>
      conj_tac >- metis_tac[is_flippable_not_terminator] >>
      simp[flip_operands_step_inst])
QED

(* Per-block ALL_DISTINCT inst_ids from wf_function *)
Theorem bb_inst_ids_distinct:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)
Proof
  rpt strip_tac >>
  irule all_distinct_flat_mem >>
  qexists `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks` >>
  gvs[wf_function_def, fn_inst_ids_distinct_def] >>
  simp[MEM_MAP] >> qexists `bb` >> simp[]
QED

Triviality flip_operands_is_terminator:
  !i. is_terminator (flip_operands i).inst_opcode = is_terminator i.inst_opcode
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `i.inst_opcode` >> gvs[] >>
  EVAL_TAC
QED

(* Forward: for j in block_body bb, matching instruction in block_body bb' *)
Triviality block_body_from_block_rev:
  !fn bb bb' j.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb' /\
    MEM j (block_body bb) ==>
    ?k. MEM k (block_body bb') /\ k.inst_id = j.inst_id
Proof
  rpt strip_tac >>
  drule_all block_perm_of_elim >> strip_tac >>
  gvs[block_body_def, MEM_FILTER] >>
  (* Get ALL_DISTINCT inst_ids for bb.insts early *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  (* j.inst_id in MAP inst_id (FILTER ¬pseudo bb'.insts) via PERM *)
  `MEM j.inst_id (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions))` by
    (drule PERM_MEM_EQ >> disch_then (qspec_then `j.inst_id` mp_tac) >>
     simp[MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  gvs[MEM_MAP, MEM_FILTER] >>
  rename1 `MEM k bb'.bb_instructions` >>
  (* k is non-pseudo, from_block gives it comes from some orig in bb *)
  `from_block bb.bb_instructions k` by
    (fs[EVERY_MEM, MEM_FILTER]) >>
  gvs[from_block_def] >> rename1 `MEM orig bb.bb_instructions`
  >- ((* k = orig directly: orig.inst_id = j.inst_id + ALL_DISTINCT ⟹ orig = j *)
      `orig = j` by metis_tac[all_distinct_map_mem_inj] >>
      gvs[] >> qexists `j` >> simp[])
  >> ((* k = flip_operands orig *)
      `orig.inst_id = j.inst_id` by simp[flip_operands_inst_id] >>
      `orig = j` by metis_tac[all_distinct_map_mem_inj] >>
      gvs[] >>
      qexists `flip_operands j` >>
      simp[flip_operands_inst_id, flip_operands_is_terminator])
QED

(* ALL_DISTINCT for permuted block's block_body *)
Triviality block_body_all_distinct_perm:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (block_body bb'))
Proof
  rpt strip_tac >>
  drule_all block_perm_of_elim >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
       (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
    (irule all_distinct_map_filter >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
       (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions))` by
    metis_tac[ALL_DISTINCT_PERM, PERM_SYM] >>
  simp[block_body_def] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode)
     bb'.bb_instructions =
   FILTER (\i. ~is_terminator i.inst_opcode)
     (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions)` by
    (rewrite_tac[FILTER_FILTER] >> AP_THM_TAC >> AP_TERM_TAC >>
     simp[FUN_EQ_THM] >> metis_tac[CONJ_COMM]) >>
  simp[] >> irule all_distinct_map_filter >> simp[]
QED

(* PERM of inst_ids at block_body level *)
Triviality block_body_perm_inst_ids:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' ==>
    PERM (MAP (\i. i.inst_id) (block_body bb))
         (MAP (\i. i.inst_id) (block_body bb'))
Proof
  rpt strip_tac >>
  irule PERM_ALL_DISTINCT >>
  conj_tac
  >- (gen_tac >> simp[MEM_MAP] >> eq_tac >> strip_tac
      >- (drule_all block_body_from_block_rev >> strip_tac >>
          qexists `k` >> simp[])
      >> (drule_all block_body_from_block >> strip_tac >>
          qexists `j` >> simp[])) >>
  metis_tac[block_body_all_distinct, block_body_all_distinct_perm]
QED

(* PERM (block_body bb) (MAP (choose_original ...) (block_body bb')) *)
Theorem block_body_choose_perm:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' ==>
    PERM (block_body bb)
         (MAP (choose_original (block_body bb)) (block_body bb'))
Proof
  rpt strip_tac >>
  irule map_choose_original_perm >>
  rpt conj_tac
  >- (rpt strip_tac >> metis_tac[block_body_from_block])
  >- metis_tac[block_body_all_distinct]
  >> metis_tac[block_body_perm_inst_ids]
QED

(* topo_sorted for original block under full_dep eda (no TC needed).
   full_dep = eda_dep ∨ uses/defs overlap ∨ defs/defs overlap.
   Part 1 (eda_dep): from eda_topo_compatible_topo_sorted.
   Part 2 (uses/defs): from def_dominates_uses — user at i, definer at j>i impossible.
   Part 3 (defs/defs): from ssa_form — no two distinct instructions share outputs. *)
(* Use ssa_unique_output / mem_fn_insts_intro from allocaRemapSSATheory *)

(* If an instruction is MEM of two blocks, those blocks must be the same
   (by fn_inst_ids_distinct). *)
Triviality fn_inst_same_block:
  !fn bb1 bb2 inst.
    wf_function fn /\
    MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    MEM inst bb1.bb_instructions /\ MEM inst bb2.bb_instructions ==>
    bb1 = bb2
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
  fs[fn_inst_ids_distinct_def] >>
  `MEM inst.inst_id (MAP (\i. i.inst_id) bb2.bb_instructions)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  qspecl_then [`fn.fn_blocks`,
    `\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
    `bb1`, `bb2`, `inst.inst_id`] mp_tac all_distinct_flat_map_disjoint >>
  simp[MEM_MAP] >> metis_tac[]
QED

(* In block_body, a later element cannot define a variable used by an earlier
   element. This follows from def_dominates_uses + SSA uniqueness + filter
   preserving order. *)
Triviality block_body_defs_before_uses:
  !fn bb i j v.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ bb_well_formed bb /\
    i < j /\ j < LENGTH (block_body bb) /\
    MEM v (inst_defs (EL j (block_body bb))) /\
    MEM (Var v) (EL i (block_body bb)).inst_operands ==>
    F
Proof
  rpt strip_tac >>
  qabbrev_tac `bd = block_body bb` >>
  (* Step 1: EL i bd and EL j bd are distinct *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `ALL_DISTINCT bd` by
    (simp[Abbr `bd`] >> metis_tac[block_body_all_distinct, ALL_DISTINCT_MAP]) >>
  `i < LENGTH bd` by decide_tac >>
  `EL i bd <> EL j bd` by
    (`i <> j` by decide_tac >> metis_tac[ALL_DISTINCT_EL_IMP]) >>
  (* Step 2: Both are MEM of bb.bb_instructions *)
  `MEM (EL i bd) bb.bb_instructions /\ MEM (EL j bd) bb.bb_instructions` by
    (`MEM (EL i bd) bd /\ MEM (EL j bd) bd` by
       (simp[MEM_EL] >> metis_tac[]) >>
     unabbrev_all_tac >>
     fs[block_body_def, MEM_FILTER]) >>
  (* Step 3: Both are in fn_insts *)
  `MEM (EL i bd) (fn_insts fn) /\ MEM (EL j bd) (fn_insts fn)` by
    (conj_tac >> irule mem_fn_insts_intro >> qexists `bb` >> simp[]) >>
  (* Step 4: v is in inst_outputs of EL j bd *)
  `MEM v (EL j bd).inst_outputs` by fs[inst_defs_def] >>
  (* Step 5: def_dominates_uses gives us a defining instruction *)
  gvs[wf_ssa_def] >>
  qpat_x_assum `def_dominates_uses _`
    (strip_assume_tac o REWRITE_RULE[def_dominates_uses_def]) >>
  first_x_assum (qspecl_then [`bb`, `EL i bd`, `v`] mp_tac) >>
  impl_tac >- simp[inst_uses_def, MEM_operand_vars_iff] >>
  strip_tac >>
  (* Step 6: def_inst = EL j bd, and def_bb = bb *)
  `MEM def_inst (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists `def_bb` >> simp[]) >>
  `MEM (EL j bd) (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists `bb` >> simp[]) >>
  `def_inst = EL j bd` by metis_tac[ssa_unique_output] >>
  (* def_bb = bb: def_inst is MEM of both def_bb and bb (since def_inst = bd[j]).
     If def_bb ≠ bb, same inst_id in two blocks contradicts fn_inst_ids_distinct. *)
  `def_bb = bb` by
    metis_tac[fn_inst_same_block] >>
  gvs[] >>
  (* Now have: i' < j' with EL i' bb = definer (EL j bd),
     EL j' bb = user (EL i bd). But filter_el_mono gives
     fi < fj with EL fi bb = EL i bd, EL fj bb = EL j bd.
     By ALL_DISTINCT: fi = j' and fj = i', so j' < i'.
     Contradiction with i' < j'. *)
  `ALL_DISTINCT bb.bb_instructions` by
    metis_tac[ALL_DISTINCT_MAP] >>
  `i < LENGTH bd` by decide_tac >>
  `?fi fj. fi < fj /\ fj < LENGTH bb.bb_instructions /\
           EL fi bb.bb_instructions = EL i bd /\
           EL fj bb.bb_instructions = EL j bd` by
    (qspecl_then [`\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode`,
      `bb.bb_instructions`, `i`, `j`] mp_tac filter_el_mono >>
     unabbrev_all_tac >> simp[GSYM block_body_def]) >>
  `fi < LENGTH bb.bb_instructions` by decide_tac >>
  `i' < LENGTH bb.bb_instructions` by decide_tac >>
  `fi = j'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `fj = i'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  decide_tac
QED

Theorem block_body_topo_sorted:
  !fn bb.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    bb_well_formed bb ==>
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (block_body bb)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  `topo_sorted (eda_dep (build_full_eda bb.bb_instructions)) (block_body bb)` by
    suspend "eda_topo" >>
  simp[topo_sorted_def, full_dep_def] >>
  qabbrev_tac `bd = block_body bb` >>
  `ALL_DISTINCT bd` by
    (simp[Abbr `bd`] >> metis_tac[block_body_all_distinct, ALL_DISTINCT_MAP]) >>
  rpt strip_tac
  >- (gvs[topo_sorted_def] >> metis_tac[])
  >- suspend "case1"
  >> suspend "case2"
QED

Resume block_body_topo_sorted[eda_topo]:
  rewrite_tac[block_body_def] >>
  irule eda_topo_compatible_topo_sorted >>
  simp[] >> conj_tac
  >- metis_tac[build_full_eda_wf]
  >> metis_tac[eda_topo_compatible_original]
QED

Resume block_body_topo_sorted[case1]:
  (* DISJOINT (inst_uses bd[i]) (inst_defs bd[j]) when i < j *)
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  spose_not_then strip_assume_tac >> rename1 `MEM v _` >>
  `MEM (Var v) (EL i bd).inst_operands` by
    gvs[inst_uses_def, MEM_operand_vars_iff] >>
  `bd = block_body bb` by fs[markerTheory.Abbrev_def] >>
  metis_tac[block_body_defs_before_uses]
QED

Resume block_body_topo_sorted[case2]:
  (* DISJOINT (inst_defs bd[i]) (inst_defs bd[j]) when i < j:
     SSA says each var has one definer, so bd[i] = bd[j], contradicting ALL_DISTINCT *)
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  spose_not_then strip_assume_tac >> rename1 `MEM v _` >>
  `i < LENGTH bd` by decide_tac >>
  `MEM (EL i bd) bd /\ MEM (EL j bd) bd` by
    (simp[MEM_EL] >> metis_tac[]) >>
  `MEM (EL i bd) bb.bb_instructions /\ MEM (EL j bd) bb.bb_instructions` by
    (fs[markerTheory.Abbrev_def] >>
     metis_tac[MEM_FILTER, block_body_def]) >>
  `MEM (EL i bd) (fn_insts fn) /\ MEM (EL j bd) (fn_insts fn)` by
    (conj_tac >> irule mem_fn_insts_intro >> qexists `bb` >> simp[]) >>
  `MEM v (EL i bd).inst_outputs /\ MEM v (EL j bd).inst_outputs` by
    fs[inst_defs_def] >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  `EL i bd = EL j bd` by
    metis_tac[ssa_unique_output] >>
  `i < LENGTH bd /\ i <> j` by decide_tac >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

Finalise block_body_topo_sorted

(* flip_operands preserves set of inst_uses *)
Triviality flip_operands_inst_uses_set:
  !i. set (inst_uses (flip_operands i)) = set (inst_uses i)
Proof
  rw[inst_uses_def, flip_operands_def, pred_setTheory.EXTENSION] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[MEM_operand_vars_iff] >> metis_tac[]
QED

(* from_block source: unique original with inst_id, inst_outputs, ¬is_pseudo *)
Triviality from_block_source:
  !bi a.
    from_block bi a /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    ?j. MEM j bi /\ ~is_pseudo j.inst_opcode /\
        j.inst_id = a.inst_id /\ j.inst_outputs = a.inst_outputs
Proof
  rw[from_block_def] >> gvs[]
  >- (qexists `a` >> simp[])
  >> qexists `j` >>
     simp[flip_operands_inst_id, flip_operands_inst_outputs]
QED

(* from_block element preserves inst_uses set and inst_defs relative to source *)
Triviality from_block_preserves_uses_defs:
  !bi a.
    from_block bi a ==>
    ?j. MEM j bi /\ j.inst_id = a.inst_id /\
        set (inst_uses a) = set (inst_uses j) /\
        inst_defs a = inst_defs j
Proof
  rw[from_block_def] >> gvs[]
  >- (qexists `a` >> simp[])
  >> qexists `j` >>
     simp[flip_operands_inst_id, flip_operands_inst_uses_set,
          inst_defs_def, flip_operands_inst_outputs]
QED

Triviality from_block_list_outputs_distinct[local]:
  !bi l.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) l) /\
    EVERY (from_block bi) l ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) l))
Proof
  gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
  fs[ALL_DISTINCT_APPEND, EVERY_MEM] >> rpt conj_tac
  >- (drule_all from_block_source >> strip_tac >>
      irule all_distinct_flat_mem >>
      qexists_tac `MAP (\i. i.inst_outputs) bi` >>
      simp[MEM_MAP] >> metis_tac[])
  >- (spose_not_then strip_assume_tac >>
      gvs[MEM_FLAT, MEM_MAP] >> rename1 `MEM y l` >>
      `from_block bi h /\ from_block bi y` by simp[] >>
      `?src_h. MEM src_h bi /\ ~is_pseudo src_h.inst_opcode /\
               src_h.inst_id = h.inst_id /\
               src_h.inst_outputs = h.inst_outputs` by
        (mp_tac (Q.SPECL [`bi`, `h`] from_block_source) >> simp[]) >>
      `?src_y. MEM src_y bi /\ ~is_pseudo src_y.inst_opcode /\
               src_y.inst_id = y.inst_id /\
               src_y.inst_outputs = y.inst_outputs` by
        (mp_tac (Q.SPECL [`bi`, `y`] from_block_source) >> simp[]) >>
      `src_h = src_y` by metis_tac[all_distinct_flat_map_unique] >>
      `h.inst_id = y.inst_id` by gvs[] >>
      `h = y` by metis_tac[all_distinct_map_mem_inj, MEM] >>
      gvs[])
  >> (first_x_assum irule >> simp[] >> metis_tac[])
QED

Triviality all_distinct_flat_map_append_disjoint[local]:
  !f l1 l2.
    ALL_DISTINCT (FLAT (MAP f l1)) /\
    ALL_DISTINCT (FLAT (MAP f l2)) /\
    (!x a b. MEM a l1 /\ MEM b l2 /\ MEM x (f a) /\ MEM x (f b) ==> F) ==>
    ALL_DISTINCT (FLAT (MAP f l1) ++ FLAT (MAP f l2))
Proof
  rpt strip_tac >>
  simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Triviality pseudo_from_block_outputs_disjoint[local]:
  !bi sched p y e.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    EVERY (from_block bi) sched /\
    MEM p (FILTER (\i. is_pseudo i.inst_opcode) bi) /\
    MEM y sched /\
    MEM e p.inst_outputs /\ MEM e y.inst_outputs ==>
    F
Proof
  rpt strip_tac >>
  `from_block bi y` by fs[EVERY_MEM] >>
  `?src_y. MEM src_y bi /\ ~is_pseudo src_y.inst_opcode /\
           src_y.inst_id = y.inst_id /\
           src_y.inst_outputs = y.inst_outputs` by
    (mp_tac (Q.SPECL [`bi`, `y`] from_block_source) >> simp[]) >>
  `MEM p bi /\ is_pseudo p.inst_opcode` by fs[MEM_FILTER] >>
  `p = src_y` by metis_tac[all_distinct_flat_map_unique] >>
  gvs[]
QED

(* from_block preserves full_dep (biconditional) *)
Triviality from_block_full_dep:
  !bi x y x' y'.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    from_block bi x /\ from_block bi y /\
    from_block bi x' /\ from_block bi y' /\
    x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id ==>
    (full_dep (build_full_eda bi) x y <=> full_dep (build_full_eda bi) x' y')
Proof
  rpt strip_tac >>
  qpat_x_assum `from_block _ x`
    (qx_choose_then `jx` strip_assume_tac o MATCH_MP from_block_preserves_uses_defs) >>
  qpat_x_assum `from_block _ y`
    (qx_choose_then `jy` strip_assume_tac o MATCH_MP from_block_preserves_uses_defs) >>
  qpat_x_assum `from_block _ x'`
    (qx_choose_then `jx'` strip_assume_tac o MATCH_MP from_block_preserves_uses_defs) >>
  qpat_x_assum `from_block _ y'`
    (qx_choose_then `jy'` strip_assume_tac o MATCH_MP from_block_preserves_uses_defs) >>
  `jx.inst_id = jx'.inst_id` by gvs[] >>
  `jx = jx'` by
    (qspecl_then [`\i. i.inst_id`, `bi`, `jx`, `jx'`]
       mp_tac all_distinct_map_mem_inj >> simp[]) >>
  `jy.inst_id = jy'.inst_id` by gvs[] >>
  `jy = jy'` by
    (qspecl_then [`\i. i.inst_id`, `bi`, `jy`, `jy'`]
       mp_tac all_distinct_map_mem_inj >> simp[]) >>
  simp[full_dep_def] >>
  metis_tac[eda_dep_inst_id_only]
QED

(* Variant of map_choose_original_topo_sorted where condition 4
   is restricted to elements of l1 and l2 *)
Theorem map_choose_original_topo_sorted_restricted:
  !l1 l2 dep.
    ALL_DISTINCT (MAP (\i. i.inst_id) l1) /\
    topo_sorted dep l2 /\
    (!i. MEM i l2 ==> ?j. MEM j l1 /\ j.inst_id = i.inst_id) /\
    (!x y x' y'. MEM x l2 /\ MEM y l2 /\ MEM x' l1 /\ MEM y' l1 /\
       x.inst_id = x'.inst_id /\ y.inst_id = y'.inst_id ==>
       (dep x y <=> dep x' y')) ==>
    topo_sorted dep (MAP (choose_original l1) l2)
Proof
  rw[topo_sorted_def, LENGTH_MAP] >>
  simp[EL_MAP] >>
  `MEM (EL i l2) l2` by (simp[MEM_EL] >> qexists `i` >> simp[]) >>
  `MEM (EL j l2) l2` by (simp[MEM_EL] >> qexists `j` >> simp[]) >>
  `(choose_original l1 (EL i l2)).inst_id = (EL i l2).inst_id` by
    (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
  `(choose_original l1 (EL j l2)).inst_id = (EL j l2).inst_id` by
    (irule (cj 2 choose_original_correct) >> metis_tac[]) >>
  `MEM (choose_original l1 (EL i l2)) l1` by
    (irule (cj 1 choose_original_correct) >> metis_tac[]) >>
  `MEM (choose_original l1 (EL j l2)) l1` by
    (irule (cj 1 choose_original_correct) >> metis_tac[]) >>
  metis_tac[]
QED

(* NOTE: block_body_topo_sorted_co was FALSE as stated — block_perm_of
   does not carry ordering info. topo_sorted must come from the DFT pipeline
   (schedule_output_eda_before + schedule_output_producer_before).
   Now passed as hypothesis to block_body_ok_equiv. *)

(* Convert output_eda_before + output_producer_before → topo_sorted (full_dep eda).
   Key bridge from DFT topo sort results to the permutation simulation. *)
(* Per-block SSA: no two instructions share an output variable *)
Triviality schedule_topo_sorted_full_dep:
  !bi eda output.
    eda = build_full_eda bi /\
    output_eda_before eda output /\
    output_producer_before bi output /\
    ALL_DISTINCT (MAP (\i. i.inst_id) output) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    (!i. MEM i output ==> from_block bi i /\ ~is_pseudo i.inst_opcode) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) ==>
    topo_sorted (full_dep eda) output
Proof
  rw[topo_sorted_def, full_dep_def] >>
  spose_not_then strip_assume_tac >>
  gvs[]
  >- suspend "eda_case"
  >- suspend "uses_defs_case"
  >> suspend "defs_defs_case"
QED

(* Case 1: eda_dep(EL i, EL j) with i < j contradicts output_eda_before *)
Resume schedule_topo_sorted_full_dep[eda_case]:
  fs[output_eda_before_def, eda_dep_def] >>
  `eda_wf (build_full_eda bi) bi` by simp[build_full_eda_wf] >>
  `~is_pseudo d.inst_opcode` by
    (qpat_x_assum `eda_wf _ _` mp_tac >> rw[eda_wf_def] >>
     Cases_on `FLOOKUP (build_full_eda bi) (EL i output).inst_id` >> gvs[] >>
     res_tac >> simp[]) >>
  (* Apply output_eda_before with k=i, witness d *)
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >>
  qexists `d` >> simp[] >>
  rpt strip_tac >>
  (* m < i, (EL m output).inst_id = d.inst_id = (EL j output).inst_id *)
  (* ALL_DISTINCT → m = j → j < i, contradicts i < j *)
  `m < LENGTH output` by decide_tac >>
  `EL m (MAP (\i. i.inst_id) output) = EL j (MAP (\i. i.inst_id) output)` by
    simp[EL_MAP] >>
  qspecl_then [`MAP (\i. i.inst_id) output`, `m`, `j`] mp_tac
    ALL_DISTINCT_EL_IMP >> simp[]
QED

(* Case 2: uses(EL i) ∩ defs(EL j) with i < j contradicts output_producer_before *)
Resume schedule_topo_sorted_full_dep[uses_defs_case]:
  fs[pred_setTheory.IN_DISJOINT, inst_uses_def, inst_defs_def] >>
  rename1 `MEM v (operand_vars _)` >>
  `MEM (Var v) (EL i output).inst_operands` by metis_tac[MEM_operand_vars_iff] >>
  `MEM (EL j output) output` by (simp[MEM_EL] >> metis_tac[]) >>
  (* Get j_orig ∈ bi: inst_id, inst_outputs, ¬is_pseudo — no case split *)
  `from_block bi (EL j output)` by metis_tac[] >>
  `?j_orig. MEM j_orig bi /\ ~is_pseudo j_orig.inst_opcode /\
            j_orig.inst_id = (EL j output).inst_id /\
            j_orig.inst_outputs = (EL j output).inst_outputs` by
    metis_tac[from_block_source] >>
  `MEM v j_orig.inst_outputs` by gvs[] >>
  (* producing_inst bi v = SOME j_orig (unique definer under SSA) *)
  `producing_inst bi v = SOME j_orig` by
    (qspecl_then [`bi`, `v`, `j_orig`] mp_tac producing_inst_unique_definer >>
     simp[] >> disch_then irule >> rpt strip_tac >>
     rename1 `MEM other bi` >>
     qspecl_then [`bi`, `(\i. i.inst_outputs)`, `j_orig`, `other`, `v`]
       mp_tac all_distinct_flat_map_disjoint >> simp[]) >>
  (* Apply output_producer_before with k=i *)
  fs[output_producer_before_def] >>
  first_x_assum (qspecl_then [`i`, `v`, `j_orig`] mp_tac) >> simp[] >>
  strip_tac >>
  (* ALL_DISTINCT → m = j → j ≥ i, done *)
  rpt strip_tac >>
  spose_not_then assume_tac >> gvs[] >>
  `m < LENGTH output` by decide_tac >>
  `EL m (MAP (\i. i.inst_id) output) = EL j (MAP (\i. i.inst_id) output)` by
    simp[EL_MAP] >>
  qspecl_then [`MAP (\i. i.inst_id) output`, `m`, `j`] mp_tac
    ALL_DISTINCT_EL_IMP >> simp[]
QED

(* Case 3: defs(EL i) ∩ defs(EL j) with i < j contradicts SSA unique outputs *)
Resume schedule_topo_sorted_full_dep[defs_defs_case]:
  fs[pred_setTheory.IN_DISJOINT, inst_defs_def] >>
  rename1 `MEM v (EL j output).inst_outputs` >>
  (* Get originals from bi for both EL i and EL j *)
  `i < LENGTH output` by decide_tac >>
  `MEM (EL i output) output` by metis_tac[MEM_EL] >>
  `MEM (EL j output) output` by metis_tac[MEM_EL] >>
  `from_block bi (EL i output) /\ from_block bi (EL j output)` by metis_tac[] >>
  `?i_orig. MEM i_orig bi /\ i_orig.inst_id = (EL i output).inst_id /\
            i_orig.inst_outputs = (EL i output).inst_outputs` by
    metis_tac[from_block_source] >>
  `?j_orig. MEM j_orig bi /\ j_orig.inst_id = (EL j output).inst_id /\
            j_orig.inst_outputs = (EL j output).inst_outputs` by
    metis_tac[from_block_source] >>
  (* Both originals define v → must be same instruction under SSA *)
  `MEM v i_orig.inst_outputs /\ MEM v j_orig.inst_outputs` by gvs[] >>
  `i_orig = j_orig` by
    (spose_not_then assume_tac >>
     qspecl_then [`bi`, `(\i. i.inst_outputs)`, `i_orig`, `j_orig`, `v`]
       mp_tac all_distinct_flat_map_disjoint >> simp[]) >>
  (* Same original → same inst_id → i = j, contradicts i < j *)
  `(EL i output).inst_id = (EL j output).inst_id` by
    (qpat_x_assum `i_orig = j_orig` SUBST_ALL_TAC >> gvs[]) >>
  qspecl_then [`MAP (\i. i.inst_id) output`, `i`, `j`] mp_tac
    ALL_DISTINCT_EL_IMP >> simp[EL_MAP]
QED

Finalise schedule_topo_sorted_full_dep;

(* uncomparable under TC(full_dep eda) → ef_commutes *)
(* Barriers are TC-connected to all other block_body elements.
   If b is a barrier in block_body and y ≠ b is also in block_body,
   then TC(full_dep(build_full_eda insts)) connects them. *)
(* Helper: eda_dep from build_full_eda implies full_dep implies TC(full_dep) *)
Triviality eda_dep_imp_tc_full_dep:
  !bi x y. eda_dep (build_full_eda bi) x y ==>
    TC (full_dep (build_full_eda bi)) x y
Proof
  rpt strip_tac >> irule TC_SUBSET >> simp[full_dep_def]
QED

(* Helper: from_barrier result lifts to eda_dep of build_full_eda.
   If b is barrier at position after prefix in non_phis, and y is in prefix,
   then eda_dep(build_full_eda bi) b y. *)
Theorem from_barrier_to_eda_dep:
  !bi prefix b suffix y.
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = prefix ++ [b] ++ suffix /\
    is_barrier b /\ MEM y prefix /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    eda_dep (build_full_eda bi) b y
Proof
  rpt strip_tac >>
  simp[eda_dep_def] >> qexists `y` >> simp[] >>
  irule build_full_eda_mono_from_barrier >>
  (* add_deps_from_barrier bi eda = FST(FOLDL ... (eda,[]) non_phis) *)
  simp[add_deps_from_barrier_def, LET_THM] >>
  qspecl_then [`prefix`, `b`, `suffix`,
    `add_deps_on_barrier bi (add_abort_deps bi (build_eda bi))`, `[]`]
    mp_tac add_deps_from_barrier_foldl_spec >>
  simp[] >> disch_then irule >>
  conj_tac
  >- (`ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ [b] ++ suffix))` by
        (qpat_x_assum `FILTER _ _ = _` (SUBST1_TAC o SYM) >>
         irule all_distinct_map_filter >> simp[]) >>
      gvs[MAP_APPEND])
  >> simp[]
QED

(* Helper: on_barrier result lifts to eda_dep of build_full_eda.
   If y is non-barrier, and last barrier before y in non_phis is b',
   then eda_dep(build_full_eda bi) y b'. *)
Theorem on_barrier_to_eda_dep:
  !bi prefix y suffix b.
    FILTER (\i. ~is_pseudo i.inst_opcode) bi = prefix ++ [y] ++ suffix /\
    ~is_barrier y /\
    (case FILTER is_barrier prefix of
       [] => F  (* no barrier before y — vacuous *)
     | bs => LAST bs = b) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    eda_dep (build_full_eda bi) y b
Proof
  rpt strip_tac >>
  simp[eda_dep_def] >> qexists `b` >> simp[] >>
  irule build_full_eda_mono_on_barrier >>
  (* add_deps_on_barrier operates on non_phis *)
  simp[add_deps_on_barrier_def, LET_THM] >>
  qspecl_then [`prefix`, `y`, `suffix`,
    `add_abort_deps bi (build_eda bi)`, `NONE`, `b`]
    mp_tac add_deps_on_barrier_foldl_spec >>
  impl_tac
  >- (`ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ [y] ++ suffix))` by
        (qpat_x_assum `FILTER _ _ = _` (SUBST1_TAC o SYM) >>
         irule all_distinct_map_filter >> simp[]) >>
      gvs[MAP_APPEND, ALL_DISTINCT_APPEND] >>
      Cases_on `FILTER is_barrier prefix` >> gvs[])
  >> simp[]
QED

(* Barriers are TC-connected to all body elements via the restricted dep
   (full_dep restricted to block_body elements). Each eda_dep step in the
   chain has both endpoints in block_body, so we get TC of the restricted dep. *)
Theorem barrier_tc_connected:
  !bb b y dep.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    MEM b (block_body bb) /\ MEM y (block_body bb) /\ b <> y /\
    is_barrier b /\
    dep = (\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
                 MEM a (block_body bb) /\ MEM c (block_body bb)) ==>
    TC dep b y \/ TC dep y b
Proof
  rpt strip_tac >> gvs[] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bi)` by simp[Abbr `bi`] >>
  `MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by
    (fs[block_body_def, MEM_FILTER, Abbr `bi`] >> fs[]) >>
  `MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by
    (fs[block_body_def, MEM_FILTER, Abbr `bi`] >> fs[]) >>
  qpat_x_assum `MEM b (FILTER _ _)`
    (strip_assume_tac o MATCH_MP mem_split_append) >>
  `MEM y (pfx ++ [b] ++ sfx)` by metis_tac[] >>
  fs[MEM_APPEND, MEM]
  >- suspend "y_before_b"
  >- gvs[]
  >> suspend "y_after_b"
QED

Resume barrier_tc_connected[y_before_b]:
  (* y in pfx = before b. barrier b has eda_dep to all before it *)
  disj1_tac >> irule TC_SUBSET >>
  simp[full_dep_def] >> disj1_tac >>
  simp[Abbr `eda`] >>
  irule from_barrier_to_eda_dep >>
  simp[] >> qexistsl [`pfx`, `sfx`] >> simp[]
QED

Resume barrier_tc_connected[y_after_b]:
  (* y in sfx = after b *)
  disj2_tac >>
  qpat_x_assum `MEM y sfx` (strip_assume_tac o MATCH_MP mem_split_append) >>
  qabbrev_tac `pre_y = pfx ++ [b] ++ pfx'` >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) bi = pre_y ++ [y] ++ sfx'` by
    simp[Abbr `pre_y`] >>
  `MEM b (FILTER is_barrier pre_y)` by
    simp[Abbr `pre_y`, MEM_FILTER, MEM_APPEND] >>
  Cases_on `is_barrier y`
  >- suspend "y_barrier"
  >> suspend "y_not_barrier"
QED

Resume barrier_tc_connected[y_barrier]:
  (* y is also barrier — eda_dep from y to b, single step *)
  irule TC_SUBSET >> simp[full_dep_def] >> disj1_tac >>
  simp[Abbr `eda`] >>
  irule from_barrier_to_eda_dep >>
  simp[] >> qexistsl [`pre_y`, `sfx'`] >>
  simp[Abbr `pre_y`, MEM_APPEND]
QED

Resume barrier_tc_connected[y_not_barrier]:
  (* y not barrier — chain through last barrier b' in pre_y *)
  (* Unfold eda early so irule can match *)
  qpat_x_assum `Abbrev (eda = _)` (SUBST_ALL_TAC o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  `FILTER is_barrier pre_y <> []` by (strip_tac >> fs[MEM]) >>
  Cases_on `FILTER is_barrier pre_y` >- gvs[] >>
  qabbrev_tac `b' = LAST (h::t)` >>
  `eda_dep (build_full_eda bi) y b'` by
    (irule on_barrier_to_eda_dep >>
     simp[] >> qexistsl [`pre_y`, `sfx'`] >>
     simp[Abbr `b'`]) >>
  (* b' is in block_body: barrier in pre_y, not terminator *)
  `MEM b' (block_body bb)` by suspend "mem_b'_body" >>
  Cases_on `b' = b`
  >- (gvs[] >> irule TC_SUBSET >>
      simp[full_dep_def] >> disj1_tac >> simp[eda_dep_def] >>
      first_x_assum (fn th => qexists `b` >> mp_tac th) >> simp[])
  (* b' <> b: chain y -> b' -> b *)
  >> `MEM b' (FILTER is_barrier pre_y)` by
       (qpat_assum `FILTER is_barrier pre_y = h::t` SUBST1_TAC >>
        simp[Abbr `b'`, MEM_LAST]) >>
  `is_barrier b' /\ MEM b' pre_y` by fs[MEM_FILTER] >>
  qpat_x_assum `MEM b' pre_y`
    (CHOOSE_THEN (CHOOSE_THEN assume_tac) o MATCH_MP mem_split_append) >>
  rename1 `pre_y = pre_b' ++ [b'] ++ suf_b'` >>
  `FILTER is_barrier suf_b' = []` by
    (`FILTER is_barrier pre_b' ++ [b'] ++ FILTER is_barrier suf_b' = h::t` by
       (qpat_assum `pre_y = pre_b' ++ _ ++ _`
          (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        gvs[FILTER_APPEND_DISTRIB]) >>
     qpat_assum `ALL_DISTINCT (MAP _ bi)`
       (assume_tac o MATCH_MP ALL_DISTINCT_MAP o
        Q.SPEC `\i. ~is_pseudo i.inst_opcode` o
        MATCH_MP all_distinct_map_filter) >>
     `ALL_DISTINCT (pre_y ++ [y] ++ sfx')` by metis_tac[] >>
     `ALL_DISTINCT pre_y` by fs[ALL_DISTINCT_APPEND] >>
     `ALL_DISTINCT (h::t)` by
       (qpat_assum `FILTER is_barrier pre_y = h::t` (SUBST1_TAC o SYM) >>
        simp[FILTER_ALL_DISTINCT]) >>
     irule last_split_sfx_nil >>
     qexistsl [`FILTER is_barrier pre_b'`, `b'`] >>
     simp[Abbr `b'`]) >>
  `MEM b pre_b'` by
    (`FILTER is_barrier pre_b' ++ [b'] = h::t` by
       (qpat_assum `pre_y = pre_b' ++ _ ++ _`
          (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
        gvs[FILTER_APPEND_DISTRIB]) >>
     `MEM b (FILTER is_barrier pre_b' ++ [b'])` by
       (qpat_assum `FILTER is_barrier pre_b' ++ [b'] = h::t` SUBST1_TAC >>
        simp[]) >>
     `b <> b'` by metis_tac[] >>
     fs[MEM_APPEND, MEM, MEM_FILTER]) >>
  `eda_dep (build_full_eda bi) b' b` by
    (irule from_barrier_to_eda_dep >>
     simp[] >> qexistsl [`pre_b'`, `suf_b' ++ [y] ++ sfx'`] >>
     simp[MEM_APPEND]) >>
  (* Chain: TC dep y b via y -> b' -> b *)
  irule (CONJUNCT2 (SPEC_ALL TC_RULES)) >>
  qexists `b'` >> conj_tac >>
  irule TC_SUBSET >> simp[full_dep_def] >> disj1_tac >> simp[]
QED

(* Helper: element in prefix of FILTER is not at last position of original list.
   Used to show that a barrier appearing before y in the non-pseudo filter
   cannot be the terminator (which is always last in bi). *)
Triviality filter_prefix_not_last:
  !P l pre y sfx e.
    ALL_DISTINCT l /\ FILTER P l = pre ++ [y] ++ sfx /\
    MEM e pre /\ P e /\ MEM e l /\
    (!k. k < LENGTH l /\ is_terminator (EL k l).inst_opcode ==>
         k = PRE (LENGTH l)) /\
    l <> [] /\ is_terminator e.inst_opcode ==>
    F
Proof
  rpt strip_tac >>
  (* e is in pre, hence at index n < LENGTH pre in the filter *)
  `?n. n < LENGTH pre /\ EL n pre = e` by metis_tac[MEM_EL] >>
  (* y is at index LENGTH pre in the filter *)
  `n < LENGTH (FILTER P l)` by
    (pop_assum kall_tac >>
     qpat_assum `FILTER P l = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[LENGTH_APPEND, LENGTH] >> decide_tac) >>
  `LENGTH pre < LENGTH (FILTER P l)` by
    (qpat_assum `FILTER P l = _` (fn th => rewrite_tac[th]) >>
     rewrite_tac[LENGTH_APPEND, LENGTH] >> decide_tac) >>
  (* EL n (FILTER P l) = e, and EL (LENGTH pre) (FILTER P l) = y *)
  `EL n (FILTER P l) = e /\
   EL (LENGTH pre) (FILTER P l) = y` by
    (asm_rewrite_tac[] >> conj_tac >>
     simp[EL_APPEND_EQN]) >>
  (* filter_el_mono: n < LENGTH pre, so positions in l satisfy i' < j' *)
  drule_all filter_el_mono >>
  disch_then (qx_choosel_then [`ne`, `ny`] strip_assume_tac) >>
  (* ne is the position of e in l, ny is the position of y in l *)
  (* l[ne] = e, so ne = PRE(LENGTH l) since e is terminator *)
  `ne = PRE (LENGTH l)` by
    (first_x_assum irule >> gvs[]) >>
  (* But ny > ne and ny < LENGTH l => PRE(LENGTH l) < ny < LENGTH l.
     That means LENGTH l <= ny, contradiction. *)
  decide_tac
QED

Resume barrier_tc_connected[mem_b'_body]:
  (* b' = LAST(h::t) is in FILTER is_barrier pre_y, hence in pre_y.
     b' is not pseudo (from FILTER not_pseudo bi). Need: ~is_terminator.
     Use filter_prefix_not_last for the contradiction. *)
  `MEM b' (FILTER is_barrier pre_y)` by
    (qpat_assum `FILTER is_barrier pre_y = h::t` SUBST1_TAC >>
     simp[Abbr `b'`, MEM_LAST]) >>
  `is_barrier b' /\ MEM b' pre_y` by fs[MEM_FILTER] >>
  `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by
    (qpat_assum `FILTER _ bi = pre_y ++ _ ++ _` SUBST1_TAC >>
     simp[MEM_APPEND]) >>
  `~is_pseudo b'.inst_opcode /\ MEM b' bi` by fs[MEM_FILTER] >>
  `MEM y bi` by
    (qpat_assum `MEM y (block_body bb)` mp_tac >>
     rewrite_tac[block_body_def, MEM_FILTER] >> metis_tac[]) >>
  simp[block_body_def, MEM_FILTER] >>
  spose_not_then assume_tac >>
  `bi = bb.bb_instructions` by fs[markerTheory.Abbrev_def] >>
  `ALL_DISTINCT bi` by
    (qpat_x_assum `ALL_DISTINCT (MAP _ bi)` mp_tac >>
     metis_tac[ALL_DISTINCT_MAP]) >>
  qpat_x_assum `bb_well_formed bb`
    (strip_assume_tac o REWRITE_RULE [bb_well_formed_def]) >>
  irule filter_prefix_not_last >>
  qexistsl [`\i. ~is_pseudo i.inst_opcode`, `b'`, `bi`, `pre_y`, `sfx'`, `y`] >>
  BETA_TAC >> asm_rewrite_tac[]
QED

Finalise barrier_tc_connected

Theorem canonical_tc_incomp_ef_commutes_body_restricted:
  !bi x y.
    ALL_DISTINCT bi /\ bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) /\
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
    x <> y /\
    ~TC (\a c. canonical_dep bi a c /\
               MEM a (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
               MEM c (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)) x y /\
    ~TC (\a c. canonical_dep bi a c /\
               MEM a (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
               MEM c (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)) y x /\
    DISJOINT (set (inst_defs x)) (set (inst_defs y)) ==>
    ef_commutes x y
Proof
  rpt strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode`
    by (qpat_x_assum `MEM x (FILTER _ bi)` mp_tac >>
        qpat_x_assum `MEM y (FILTER _ bi)` mp_tac >>
        simp[MEM_FILTER]) >>
  `~is_barrier x /\ ~is_barrier y` by (
    conj_tac >| [
      strip_tac >>
      qspecl_then [`bi`,`x`,`y`] mp_tac
        dftCanonicalDepTheory.canonical_dep_barrier_tc_connected_restricted >>
      impl_tac >- simp[MEM_FILTER] >>
      metis_tac[],
      strip_tac >>
      qspecl_then [`bi`,`y`,`x`] mp_tac
        dftCanonicalDepTheory.canonical_dep_barrier_tc_connected_restricted >>
      impl_tac >- simp[MEM_FILTER] >>
      metis_tac[]
    ]) >>
  `is_effect_free_op x.inst_opcode /\ is_effect_free_op y.inst_opcode`
    by metis_tac[effect_free_or_barrier] >>
  `MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
   MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) bi)`
    by (imp_res_tac MEM_FILTER >> imp_res_tac MEM_FILTER >> simp[MEM_FILTER]) >>
  `~data_dep_body bi x y` by (
    CCONTR_TAC >>
    `canonical_dep bi x y` by metis_tac[data_dep_body_imp_canonical_dep] >>
    `TC (\a c. canonical_dep bi a c /\
       MEM a (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
       MEM c (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)) x y`
      by (irule TC_SUBSET >> BETA_TAC >> simp[]) >>
    metis_tac[]) >>
  `~data_dep_body bi y x` by (
    CCONTR_TAC >>
    `canonical_dep bi y x` by metis_tac[data_dep_body_imp_canonical_dep] >>
    `TC (\a c. canonical_dep bi a c /\
       MEM a (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi) /\
       MEM c (FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode) bi)) y x`
      by (irule TC_SUBSET >> BETA_TAC >> simp[]) >>
    metis_tac[]) >>
  simp[ef_commutes_def] >>
  fs[data_dep_body_def, MEM_FILTER] >>
  simp[DISJOINT_DEF, EXTENSION, inst_uses_def, inst_defs_def,
       MEM_operand_vars_iff] >>
  `in_np_body bi x` by (simp[in_np_body_def, MEM_FILTER, MEM_MAP] >> qexists `x` >> simp[]) >> `in_np_body bi y` by (simp[in_np_body_def, MEM_FILTER, MEM_MAP] >> qexists `y` >> simp[]) >> metis_tac[]
QED


(* TC-uncomparable body elements (under restricted dep) commute.
   Uses barrier_tc_connected for the barrier contradiction. *)
Triviality block_body_uncomp_ef_gen[local]:
  !bb x y dep.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    MEM x (block_body bb) /\ MEM y (block_body bb) /\ x <> y /\
    dep = (\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
                 MEM a (block_body bb) /\ MEM c (block_body bb)) /\
    ~TC dep x y /\ ~TC dep y x ==>
    ef_commutes x y
Proof
  rpt strip_tac >> gvs[] >>
  `is_effect_free_op x.inst_opcode \/ is_barrier x` by
    (fs[block_body_def, MEM_FILTER] >> metis_tac[effect_free_or_barrier]) >>
  `is_effect_free_op y.inst_opcode \/ is_barrier y` by
    (fs[block_body_def, MEM_FILTER] >> metis_tac[effect_free_or_barrier]) >>
  `~is_barrier x` by
    (strip_tac >>
     qspecl_then [`bb`, `x`, `y`,
       `\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
              MEM a (block_body bb) /\ MEM c (block_body bb)`]
       mp_tac barrier_tc_connected >>
     simp[] >> metis_tac[]) >>
  `~is_barrier y` by
    (strip_tac >>
     qspecl_then [`bb`, `y`, `x`,
       `\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
              MEM a (block_body bb) /\ MEM c (block_body bb)`]
       mp_tac barrier_tc_connected >>
     simp[] >> metis_tac[]) >>
  `~full_dep (build_full_eda bb.bb_instructions) x y` by
    (strip_tac >>
     `TC (\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
                MEM a (block_body bb) /\ MEM c (block_body bb)) x y`
       suffices_by metis_tac[] >>
     irule TC_SUBSET >> simp[]) >>
  `~full_dep (build_full_eda bb.bb_instructions) y x` by
    (strip_tac >>
     `TC (\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
                MEM a (block_body bb) /\ MEM c (block_body bb)) y x`
       suffices_by metis_tac[] >>
     irule TC_SUBSET >> simp[]) >>
  fs[block_body_def, MEM_FILTER] >>
  irule non_dep_non_barrier_ef_commutes >> simp[] >>
  qexists `build_full_eda bb.bb_instructions` >> simp[]
QED

Theorem block_body_uncomp_ef:
  !fn bb x y dep.
    wf_function fn /\ MEM bb fn.fn_blocks /\ bb_well_formed bb /\
    MEM x (block_body bb) /\ MEM y (block_body bb) /\ x <> y /\
    dep = (\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
                 MEM a (block_body bb) /\ MEM c (block_body bb)) /\
    ~TC dep x y /\ ~TC dep y x ==>
    ef_commutes x y
Proof
  rpt strip_tac >>
  qspecl_then [`bb`, `x`, `y`, `dep`] mp_tac block_body_uncomp_ef_gen >>
  simp[] >> metis_tac[bb_inst_ids_distinct]
QED

(* Unified step_inst idx-independence: OK result carries idx through.
   For INVOKE: invoke_step_inst_idx_OK_only. For non-INVOKE: step_inst_idx_indep.
   Both agree: step_inst OK s ⇒ step_inst (s with idx:=j) = OK (s' with idx:=j) *)
Triviality step_inst_idx_ok_general:
  !fuel ctx inst s j s'.
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst fuel ctx inst (s with vs_inst_idx := j) =
      OK (s' with vs_inst_idx := j)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[invoke_step_inst_idx_OK_only])
  >> (`step_inst fuel ctx inst (s with vs_inst_idx := j) =
       exec_result_map (\s'. s' with vs_inst_idx := j)
         (step_inst fuel ctx inst s)` by
        simp[step_inst_idx_indep] >>
      gvs[instIdxIndepTheory.exec_result_map_def])
QED

(* exec_block_skip_prefix generalized to allow INVOKE instructions. *)
(* exec_block_skip_prefix generalized to allow INVOKE instructions.
   Uses step_inst_idx_ok_general — only the OK case matters since
   run_insts OK forces all step_inst calls to be OK. *)
Triviality exec_block_skip_prefix_general:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s'
  ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  (* Since run_insts (h::prefix) s = OK s', the first step must be OK *)
  Cases_on `step_inst fuel ctx h s` >> gvs[run_insts_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  (* Use step_inst_idx_ok_general to handle both INVOKE and non-INVOKE *)
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
     OK (s1 with vs_inst_idx := j)` by
    (irule step_inst_idx_ok_general >> simp[]) >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  (* Now bb.bb_instructions[j] reappears — rewrite it to h *)
  `bb.bb_instructions❲j❳ = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  asm_rewrite_tac[] >> simp[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `s'`]
    mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES])
  >> simp[]
QED

(* Non-barrier → non-INVOKE ∧ non-ext-call (needed for abort/returndata reasoning) *)
Triviality not_barrier_not_invoke_ext:
  !inst. ~is_barrier inst ==>
    inst.inst_opcode <> INVOKE /\ ~is_ext_call_op inst.inst_opcode
Proof
  rpt strip_tac >> gvs[is_barrier_def] >>
  Cases_on `inst.inst_opcode` >> gvs[is_volatile_def, is_ext_call_op_def,
    is_alloca_op_def]
QED

(* In a topo_sorted ALL_DISTINCT list, for an element TC-connected to
   all others, elements before it satisfy TC dep b y, and after don't. *)
Triviality tc_connected_before_after:
  !l dep b k.
    ALL_DISTINCT l /\ topo_sorted (TC dep) l /\
    k < LENGTH l /\ EL k l = b /\
    (!y. MEM y l /\ y <> b ==> TC dep b y \/ TC dep y b) ==>
    EVERY (\y. TC dep b y) (TAKE k l) /\
    EVERY (\y. ~TC dep b y) (DROP (SUC k) l)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[EVERY_EL, EL_TAKE] >> rpt strip_tac >>
      `n < LENGTH l` by decide_tac >>
      `EL n l <> b` by
        (strip_tac >>
         qspecl_then [`l`, `n`, `k`] mp_tac ALL_DISTINCT_EL_IMP >>
         simp[]) >>
      `~TC dep (EL n l) (EL k l)` by
        (fs[topo_sorted_def] >> first_x_assum match_mp_tac >> decide_tac) >>
      `MEM (EL n l) l` by metis_tac[MEM_EL] >>
      gvs[] >> metis_tac[])
  >> (simp[EVERY_EL, EL_DROP] >> rpt strip_tac >>
      fs[topo_sorted_def] >>
      first_x_assum (qspecl_then [`k`, `SUC k + n`] mp_tac) >>
      simp[])
QED

(* Count of elements satisfying P in l, decomposed via TAKE/EL/DROP *)
Triviality filter_count_decompose:
  !P l k.
    k < LENGTH l ==>
    LENGTH (FILTER P l) =
      LENGTH (FILTER P (TAKE k l)) +
      (if P (EL k l) then 1 else 0) +
      LENGTH (FILTER P (DROP (SUC k) l))
Proof
  rpt strip_tac >>
  `l = TAKE k l ++ [EL k l] ++ DROP (SUC k) l` by
    simp[TAKE_DROP_SUC] >>
  pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[FILTER_APPEND_DISTRIB] >> IF_CASES_TAC >> simp[]
QED

(* Barriers are at the same positions in any two topo-sorted permutations.
   Proof: count predecessors (TC dep b y) using PERM_FILTER. *)
Triviality barriers_same_el:
  !l1 l2 dep k.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted (TC dep) l1 /\ topo_sorted (TC dep) l2 /\
    (!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
           TC dep b y \/ TC dep y b) /\
    k < LENGTH l1 /\ is_barrier (EL k l1) ==>
    EL k l2 = EL k l1
Proof
  rpt strip_tac >>
  qabbrev_tac `b = EL k l1` >>
  qabbrev_tac `P = \y:instruction. TC dep b y` >>
  `MEM b l2` by metis_tac[MEM_EL, PERM_MEM_EQ] >>
  `?k'. k' < LENGTH l2 /\ EL k' l2 = b` by metis_tac[MEM_EL] >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `k = k'` suffices_by simp[] >>
  `MEM b l1` by metis_tac[MEM_EL] >>
  (* b is TC-connected to all other elements *)
  `!y. MEM y l1 /\ y <> b ==> TC dep b y \/ TC dep y b` by
    (rpt strip_tac >>
     first_x_assum (qspecl_then [`b`, `y`] mp_tac) >> simp[]) >>
  `EVERY P (TAKE k l1) /\ EVERY (\y. ~P y) (DROP (SUC k) l1)` by
    (simp[Abbr `P`] >>
     qspecl_then [`l1`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[Abbr `b`]) >>
  `!y. MEM y l2 /\ y <> b ==> TC dep b y \/ TC dep y b` by
    metis_tac[PERM_MEM_EQ] >>
  `EVERY P (TAKE k' l2) /\ EVERY (\y. ~P y) (DROP (SUC k') l2)` by
    (simp[Abbr `P`] >>
     qspecl_then [`l2`, `dep`, `b`, `k'`] mp_tac tc_connected_before_after >>
     simp[]) >>
  (* Count P in l1: use decomposition + EVERY assumptions *)
  `FILTER P (TAKE k l1) = TAKE k l1` by
    simp[FILTER_EQ_ID] >>
  `FILTER P (DROP (SUC k) l1) = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `LENGTH (FILTER P l1) = k + (if P b then 1 else 0)` by
    (qspecl_then [`P`, `l1`, `k`] mp_tac filter_count_decompose >>
     simp[Abbr `b`]) >>
  (* Count P in l2 *)
  `FILTER P (TAKE k' l2) = TAKE k' l2` by
    simp[FILTER_EQ_ID] >>
  `FILTER P (DROP (SUC k') l2) = []` by
    (simp[FILTER_EQ_NIL] >> fs[EVERY_MEM] >> metis_tac[]) >>
  `LENGTH (FILTER P l2) = k' + (if P b then 1 else 0)` by
    (qspecl_then [`P`, `l2`, `k'`] mp_tac filter_count_decompose >>
     simp[]) >>
  (* PERM preserves FILTER length *)
  `LENGTH (FILTER P l1) = LENGTH (FILTER P l2)` by
    metis_tac[PERM_FILTER, PERM_LENGTH] >>
  fs[]
QED

(* If no barriers, both abort → returndata = [] → revert_equiv *)
Triviality no_barrier_abort_revert:
  !l1 l2 fuel ctx s a1 s1 a2 s2.
    EVERY (\i. ~is_barrier i) l1 /\
    EVERY (\i. ~is_barrier i) l2 /\
    EVERY (\i. ~is_terminator i.inst_opcode) l1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) l2 /\
    run_insts fuel ctx l1 s = Abort a1 s1 /\
    run_insts fuel ctx l2 s = Abort a2 s2 ==>
    revert_equiv s1 s2
Proof
  rpt strip_tac >> simp[revert_equiv_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode /\
              i.inst_opcode <> INVOKE) l1` by
    (fs[EVERY_MEM] >> rpt strip_tac >> metis_tac[not_barrier_not_invoke_ext]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ ~is_ext_call_op i.inst_opcode /\
              i.inst_opcode <> INVOKE) l2` by
    (fs[EVERY_MEM] >> rpt strip_tac >> metis_tac[not_barrier_not_invoke_ext]) >>
  metis_tac[run_insts_abort_clears_returndata]
QED

(* ===== Unified lift_result for topo-sorted permutations ===== *)

(* run_insts_append: decompose run_insts over concatenation *)
Triviality run_insts_append:
  !xs ys fuel ctx s.
    run_insts fuel ctx (xs ++ ys) s =
    case run_insts fuel ctx xs s of
      OK s' => run_insts fuel ctx ys s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | IntRet v s' => IntRet v s'
    | Error e => Error e
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[run_insts_def]
QED

Triviality run_insts_error_append:
  !fuel ctx l1 l2 s e.
    run_insts fuel ctx l1 s = Error e ==>
    run_insts fuel ctx (l1 ++ l2) s = Error e
Proof
  rpt strip_tac >> simp[run_insts_append]
QED

(* lift_result (=) (=) revert_equiv composes with identical continuations:
   if r1 lift_result r2 and both OK with equal states, then applying
   the same function f preserves lift_result. Non-OK propagates unchanged. *)
Triviality lift_result_eq_bind:
  !f r1 r2.
    lift_result $= $= revert_equiv r1 r2 ==>
    lift_result $= $= revert_equiv
      (case r1 of OK s => f s | Halt s => Halt s
       | Abort a s => Abort a s | IntRet v s => IntRet v s
       | Error e => Error e)
      (case r2 of OK s => f s | Halt s => Halt s
       | Abort a s => Abort a s | IntRet v s => IntRet v s
       | Error e => Error e)
Proof
  Cases_on `r1` >> Cases_on `r2` >> gvs[lift_result_def] >>
  (* OK-OK: equal states → same continuation → lift_result by refl *)
  rpt strip_tac >> gvs[] >>
  irule (SRULE [] lift_result_refl_proof) >> simp[revert_equiv_def]
QED

(* run_insts of a pair = case on first step then second step *)
Triviality run_insts_pair:
  !fuel ctx a b s.
    run_insts fuel ctx [a;b] s =
    case step_inst fuel ctx a s of
      OK sa => step_inst fuel ctx b sa
    | Halt v => Halt v | Abort a' s' => Abort a' s'
    | IntRet v s' => IntRet v s' | Error e => Error e
Proof
  rpt gen_tac >>
  REWRITE_TAC [run_insts_def] >>
  Cases_on `step_inst fuel ctx a s` >> simp[] >>
  Cases_on `step_inst fuel ctx b v` >> simp[]
QED

(* lift_result (=)(=) revert_equiv threads through a suffix:
   if the prefix produces lift_result, then appending the same suffix does too. *)
Triviality run_insts_lift_result_append:
  !fuel ctx l1 l2 suffix s.
    lift_result $= $= revert_equiv
      (run_insts fuel ctx l1 s) (run_insts fuel ctx l2 s) ==>
    lift_result $= $= revert_equiv
      (run_insts fuel ctx (l1 ++ suffix) s) (run_insts fuel ctx (l2 ++ suffix) s)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC [run_insts_append] >>
  Cases_on `run_insts fuel ctx l1 s` >>
  Cases_on `run_insts fuel ctx l2 s` >>
  gvs[lift_result_def] >>
  (* OK-OK: equal states -> same continuation -> lift_result by refl *)
  irule (SRULE [] lift_result_refl_proof) >> simp[revert_equiv_def]
QED

(* Swap adjacent bi_independent pair: lift_result.
   Two-sided no-Error required (one-sided is FALSE: counterexample
   a=ASSERT(abort), b=ADD(undef->Error)). *)
Triviality adj_swap_lift:
  !fuel ctx a b suffix s.
    bi_independent a b /\
    (!e. run_insts fuel ctx (a :: b :: suffix) s <> Error e) /\
    (!e. run_insts fuel ctx (b :: a :: suffix) s <> Error e) ==>
    lift_result $= $= revert_equiv
      (run_insts fuel ctx (a :: b :: suffix) s)
      (run_insts fuel ctx (b :: a :: suffix) s)
Proof
  rpt strip_tac >>
  (* Rewrite a::b::suffix as [a;b] ++ suffix *)
  `a :: b :: suffix = [a;b] ++ suffix` by simp[] >>
  `b :: a :: suffix = [b;a] ++ suffix` by simp[] >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  irule run_insts_lift_result_append >>
  (* Now show lift_result for just [a;b] vs [b;a] *)
  REWRITE_TAC [run_insts_pair] >>
  (* Extract step-level no-Error from run_insts-level no-Error *)
  `!e. step_inst fuel ctx a s <> Error e` by
    (CCONTR_TAC >> gvs[] >>
     qpat_x_assum `!e. run_insts _ _ (a::_) _ <> _`
       (qspec_then `e` mp_tac) >>
     simp[Once run_insts_def]) >>
  `!e. step_inst fuel ctx b s <> Error e` by
    (CCONTR_TAC >> gvs[] >>
     qpat_x_assum `!e. run_insts _ _ (b::_) _ <> _`
       (qspec_then `e` mp_tac) >>
     simp[Once run_insts_def]) >>
  (* Use step_swap_lift *)
  qspecl_then [`fuel`,`ctx`,`a`,`b`,`s`] mp_tac step_swap_lift >>
  simp[]
QED

(* Specialized transitivity for lift_result (=)(=) revert_equiv *)
Triviality lift_result_eq_revert_trans:
  !r1 r2 r3.
    lift_result $= $= revert_equiv r1 r2 /\
    lift_result $= $= revert_equiv r2 r3 ==>
    lift_result $= $= revert_equiv r1 r3
Proof
  rpt strip_tac >>
  qspecl_then [`$=`, `$=`, `revert_equiv`] mp_tac lift_result_trans_proof >>
  (impl_tac >- simp[revert_equiv_def]) >>
  metis_tac[]
QED

(* If h::L1 and h::L2 are both no-Error, and step h gives OK s',
   then L1 and L2 starting from s' are both no-Error *)
Triviality cons_no_error_tail:
  !fuel ctx h l s s'.
    step_inst fuel ctx h s = OK s' /\
    (!e. run_insts fuel ctx (h::l) s <> Error e) ==>
    (!e. run_insts fuel ctx l s' <> Error e)
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  first_x_assum (qspec_then `e` mp_tac) >>
  simp[Once run_insts_def]
QED

(* run_insts (h::l) not Error → step h not Error *)
Triviality cons_no_error_head:
  !fuel ctx h l s.
    (!e. run_insts fuel ctx (h::l) s <> Error e) ==>
    (!e. step_inst fuel ctx h s <> Error e)
Proof
  rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  first_x_assum (qspec_then `e` mp_tac) >> simp[Once run_insts_def]
QED

(* If step h s = OK v, and tails lift_result at v,
   then h::tails lift_result at s *)
Triviality cons_lift_result:
  !fuel ctx h l1 l2 s v.
    step_inst fuel ctx h s = OK v /\
    lift_result $= $= revert_equiv
      (run_insts fuel ctx l1 v) (run_insts fuel ctx l2 v) ==>
    lift_result $= $= revert_equiv
      (run_insts fuel ctx (h::l1) s) (run_insts fuel ctx (h::l2) s)
Proof
  rpt strip_tac >>
  `run_insts fuel ctx (h::l1) s = run_insts fuel ctx l1 v` by
    simp[Once run_insts_def] >>
  `run_insts fuel ctx (h::l2) s = run_insts fuel ctx l2 v` by
    simp[Once run_insts_def] >>
  gvs[]
QED

(* lift_result no-Error propagation: if lift_result holds and
   one side is not Error, the other is also not Error *)
Triviality lift_result_no_error:
  !r1 r2.
    lift_result $= $= revert_equiv r1 r2 ==>
    ((!e. r1 <> Error e) <=> (!e. r2 <> Error e))
Proof
  Cases >> Cases >> simp[lift_result_def]
QED

(* Diamond for bi_independent OK-OK: both cross-steps are OK (same result)
   or both are Abort. Extracted from effects_independent_commute. *)
Triviality bi_ind_ok_ok_cross:
  !fuel ctx h x s v sx.
    bi_independent h x /\
    step_inst fuel ctx h s = OK v /\
    step_inst fuel ctx x s = OK sx ==>
    (?xv. step_inst fuel ctx x v = OK xv /\
          step_inst fuel ctx h sx = OK xv) \/
    (?a1 s1 a2 s2. step_inst fuel ctx x v = Abort a1 s1 /\
                    step_inst fuel ctx h sx = Abort a2 s2)
Proof
  rpt gen_tac >> strip_tac >>
  (* No Error for cross-steps *)
  `!e. step_inst fuel ctx x v <> Error e` by (
    qspecl_then [`fuel`,`ctx`,`h`,`x`,`s`,`v`] mp_tac
      bi_ind_ok_no_error_iff >> simp[]) >>
  `!e. step_inst fuel ctx h sx <> Error e` by (
    qspecl_then [`fuel`,`ctx`,`x`,`h`,`s`,`sx`] mp_tac
      bi_ind_ok_no_error_iff >>
    simp[bi_independent_sym]) >>
  (* No Halt/IntRet for cross-steps *)
  `(!v'. step_inst fuel ctx x v <> Halt v') /\
   (!v' s'. step_inst fuel ctx x v <> IntRet v' s')` by
    metis_tac[bi_independent_no_halt_intret] >>
  `(!v'. step_inst fuel ctx h sx <> Halt v') /\
   (!v' s'. step_inst fuel ctx h sx <> IntRet v' s')` by
    metis_tac[bi_independent_no_halt_intret, bi_independent_sym] >>
  (* Case split on cross-steps *)
  Cases_on `step_inst fuel ctx x v` >> gvs[] >>
  Cases_on `step_inst fuel ctx h sx` >> gvs[]
  (* Both OK: use independent_commute_eq for equality *)
  >- metis_tac[independent_commute_eq, bi_independent_def]
  (* OK,Abort: impossible by commute table *)
  >- (qspecl_then [`fuel`,`ctx`,`h`,`x`,`s`] mp_tac
        effects_independent_commute >>
      fs[bi_independent_def, LET_THM])
  (* Abort,OK: impossible by commute table *)
  >> (qspecl_then [`fuel`,`ctx`,`h`,`x`,`s`] mp_tac
        effects_independent_commute >>
      fs[bi_independent_def, LET_THM])
QED


(* ===== Topo-sorted permutation lift_result ===== *)

(* Strategy: Use run_insts_topo_lift for OK<=>OK and Abort=>revert_equiv,
   then prove a1=a2 for the Abort case separately using:
   1. FILTER equality: dep-chained P-elements have same FILTER in topo-sorted perms
   2. bi_independent_cross_abort: abort type preserved through bi-ind OK steps
   3. The first non-NoFail aborter is the same instruction in both orderings *)

(* --- Helper: first P-element in topo-sorted list with pairwise-dep P-elements
   is the same regardless of list ordering --- *)

(* Helper: in a topo_sorted list, no P-element can appear before index i
   if i is the minimal P-index in a permutation *)
Triviality topo_sorted_no_earlier_P:
  !l1 l2 dep P i1 b.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\ P x /\ P y ==>
           dep x y \/ dep y x) /\
    i1 < LENGTH l1 /\ b = EL i1 l1 /\ P b /\
    (!j. j < i1 ==> ~P (EL j l1)) ==>
    !i2 j. i2 < LENGTH l2 /\ b = EL i2 l2 /\
           j < i2 ==> ~P (EL j l2)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `j < LENGTH l2` by simp[] >>
  `j <> i2` by simp[] >>
  `EL j l2 <> b` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `MEM (EL j l2) l1` by metis_tac[MEM_EL, PERM_MEM_EQ] >>
  `MEM b l1` by metis_tac[MEM_EL] >>
  `dep (EL j l2) b \/ dep b (EL j l2)` by
    (first_x_assum irule >> simp[]) >>
  `~dep (EL j l2) (EL i2 l2)` by
    (qpat_x_assum `topo_sorted dep l2` mp_tac >>
     rewrite_tac[topo_sorted_def] >>
     disch_then (qspecl_then [`j`, `i2`] mp_tac) >> simp[]) >>
  `~dep (EL j l2) b` by gvs[] >>
  `dep b (EL j l2)` by metis_tac[] >>
  `?k. k < LENGTH l1 /\ EL j l2 = EL k l1` by metis_tac[MEM_EL] >>
  `dep (EL i1 l1) (EL k l1)` by metis_tac[] >>
  `~(i1 < k)` by
    (strip_tac >>
     `~dep (EL i1 l1) (EL k l1)` suffices_by metis_tac[] >>
     qpat_x_assum `topo_sorted dep l1` mp_tac >>
     rewrite_tac[topo_sorted_def] >>
     disch_then (qspecl_then [`i1`, `k`] mp_tac) >> simp[]) >>
  `k < i1 \/ k = i1` by simp[]
  >- metis_tac[]
  >> metis_tac[]
QED

(* If all P-satisfying pairs are dep-related, the first P-element in any
   topo-sorted permutation is the same element. *)
Triviality topo_first_P_element:
  !l1 l2 dep P.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\ P x /\ P y ==>
           dep x y \/ dep y x) /\
    (?x. MEM x l1 /\ P x) ==>
    ?pfx1 sfx1 pfx2 sfx2 x.
      l1 = pfx1 ++ [x] ++ sfx1 /\ l2 = pfx2 ++ [x] ++ sfx2 /\
      P x /\ EVERY ($~ o P) pfx1 /\ EVERY ($~ o P) pfx2
Proof
  rpt strip_tac >>
  suspend "main"
QED

Resume topo_first_P_element[main]:
  (* Use WOP to find minimal P-index in l1 *)
  `?i1. i1 < LENGTH l1 /\ P (EL i1 l1) /\
        !j. j < i1 ==> ~P (EL j l1)` by
    (`?n. n < LENGTH l1 /\ P (EL n l1)` by metis_tac[MEM_EL] >>
     qspecl_then [`\i. i < LENGTH l1 /\ P (EL i l1)`] mp_tac WOP >>
     impl_tac >- metis_tac[] >>
     disch_then (qx_choose_then `i1` (strip_assume_tac o BETA_RULE)) >>
     qexists `i1` >> simp[] >>
     rpt strip_tac >>
     `j < LENGTH l1` suffices_by metis_tac[] >> simp[]) >>
  (* b = first P-element in l1; find its index in l2 *)
  `MEM (EL i1 l1) l2` by metis_tac[MEM_EL, PERM_MEM_EQ] >>
  `?i2. i2 < LENGTH l2 /\ EL i1 l1 = EL i2 l2` by metis_tac[MEM_EL] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  (* ~P before i2 in l2, using the extracted helper *)
  `!i2' j'. i2' < LENGTH l2 /\ EL i1 l1 = EL i2' l2 /\
            j' < i2' ==> ~P (EL j' l2)` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`l1`, `l2`, `dep`, `P`, `i1`, `EL i1 l1`]
       mp_tac topo_sorted_no_earlier_P >>
     impl_tac >- simp[] >>
     disch_then (qspecl_then [`i2'`, `j'`] mp_tac) >> simp[]) >>
  (* Decompose both lists *)
  qexistsl [`TAKE i1 l1`, `DROP (SUC i1) l1`,
            `TAKE i2 l2`, `DROP (SUC i2) l2`, `EL i1 l1`] >>
  simp[Once (GSYM TAKE_DROP_SUC)] >>
  simp[Once (GSYM TAKE_DROP_SUC)] >>
  simp[EVERY_EL, LENGTH_TAKE_EQ] >>
  rpt strip_tac >> gvs[EL_TAKE] >> metis_tac[]
QED

Finalise topo_first_P_element;

(* When run_insts on a non-terminator prefix aborts, exec_block at that
   position also aborts with the same abort type and revert_equiv state.
   The idx difference between run_insts (no idx) and exec_block (with idx)
   is harmless since revert_equiv only checks returndata. *)
(* Unified helper: non-terminator step with idx adjustment.
   Covers both INVOKE and non-INVOKE via case split.
   For non-OK: Abort state gets idx modified (non-INVOKE) or unchanged (INVOKE),
   but returndata is preserved either way. *)
(* Key property: for non-terminator instructions, step_inst with modified
   vs_inst_idx gives results where:
   - OK: mapped to OK with idx modified, and original preserves idx
   - Abort: same abort type, revert_equiv state *)
(* Non-terminator step with idx: OK case gives mapped OK + preserves idx.
   Abort case gives same abort type with revert_equiv state. *)
Triviality step_inst_idx_non_term_ok:
  !fuel ctx inst s j s'.
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK s' ==>
    step_inst fuel ctx inst (s with vs_inst_idx := j) =
      OK (s' with vs_inst_idx := j) /\
    s'.vs_inst_idx = s.vs_inst_idx
Proof
  rpt strip_tac
  >- (irule step_inst_idx_ok_general >> simp[])
  >> metis_tac[step_inst_preserves_inst_idx]
QED


(* Unified: non-terminator step with idx adjustment preserves lift_result
   for all non-OK results. Replaces step_inst_idx_non_term_{abort,error,halt,intret}. *)
Triviality step_inst_idx_non_term_non_ok:
  !fuel ctx inst s j.
    ~is_terminator inst.inst_opcode /\
    ~(?v. step_inst fuel ctx inst s = OK v) ==>
    lift_result (\_ _. T) (execution_equiv {}) revert_equiv
      (step_inst fuel ctx inst s)
      (step_inst fuel ctx inst (s with vs_inst_idx := j))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- ((* INVOKE: invoke_step_inst_idx_OK_only + non-OK case gives same result *)
      qspecl_then [`fuel`,`ctx`,`inst`,`s`,`j`] mp_tac
        invoke_step_inst_idx_OK_only >> simp[] >>
      Cases_on `step_inst fuel ctx inst s` >>
      gvs[lift_result_def, execution_equiv_def, FDOM_FEMPTY, revert_equiv_def])
  >> ((* Non-INVOKE: exec_result_map with idx *)
      `step_inst fuel ctx inst (s with vs_inst_idx := j) =
        exec_result_map (\s'. s' with vs_inst_idx := j)
          (step_inst fuel ctx inst s)` by simp[step_inst_idx_indep] >>
      Cases_on `step_inst fuel ctx inst s` >>
      gvs[instIdxIndepTheory.exec_result_map_def, lift_result_def,
          execution_equiv_def, FDOM_FEMPTY, revert_equiv_def, lookup_var_def])
QED


(* Unified: if run_insts on a prefix gives non-OK result, exec_block gives
   lift_result-related result. Replaces the 4 per-constructor versions. *)
Triviality exec_block_run_insts_lift:
  !prefix fuel ctx bb s j.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    ~(?v. run_insts fuel ctx prefix s = OK v) ==>
    lift_result (\_ _. T) (execution_equiv {}) revert_equiv
      (run_insts fuel ctx prefix s)
      (exec_block fuel ctx bb (s with vs_inst_idx := j))
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `_ :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `h = EL j bb.bb_instructions` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `~is_terminator h.inst_opcode` by gvs[] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[run_insts_def]
  >- (* OK: head succeeds, tail is non-OK *)
     (rename1 `step_inst _ _ _ s = OK s1` >>
      `step_inst fuel ctx bb.bb_instructions❲j❳ (s with vs_inst_idx := j) =
         OK (s1 with vs_inst_idx := j)` by
        (irule step_inst_idx_ok_general >> simp[]) >>
      `s1.vs_inst_idx = s.vs_inst_idx` by
        metis_tac[step_inst_preserves_inst_idx] >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`,
        `SUC j`] mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES] >>
      (impl_tac
       >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
           simp[arithmeticTheory.ADD_CLAUSES]))
      >> strip_tac >>
      ONCE_REWRITE_TAC [exec_block_def] >>
      simp[get_instruction_def])
  >> (* Non-OK: head step is non-OK — use step_inst_idx_non_term_non_ok *)
     (qspecl_then [`fuel`, `ctx`, `bb.bb_instructions❲j❳`, `s`, `j`]
        mp_tac step_inst_idx_non_term_non_ok >> simp[] >>
      Cases_on `step_inst fuel ctx bb.bb_instructions❲j❳
                  (s with vs_inst_idx := j)` >>
      gvs[lift_result_def, revert_equiv_def] >>
      rpt strip_tac >> gvs[] >>
      ONCE_REWRITE_TAC [exec_block_def] >>
      simp[get_instruction_def, revert_equiv_def, lift_result_def,
           execution_equiv_def, FDOM_FEMPTY])
QED


(* topo_sorted is preserved by TAKE *)
Triviality topo_sorted_take:
  !dep l n. topo_sorted dep l /\ n <= LENGTH l ==> topo_sorted dep (TAKE n l)
Proof
  rpt strip_tac >> simp[topo_sorted_def] >>
  rpt strip_tac >>
  `EL i (TAKE n l) = EL i l` by simp[EL_TAKE] >>
  `EL j (TAKE n l) = EL j l` by simp[EL_TAKE] >>
  gvs[] >>
  qpat_x_assum `topo_sorted dep l` mp_tac >>
  rewrite_tac[topo_sorted_def] >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >> simp[]
QED

(* topo_sorted is preserved by DROP *)
Triviality topo_sorted_drop:
  !dep l n. topo_sorted dep l /\ n <= LENGTH l ==> topo_sorted dep (DROP n l)
Proof
  rpt strip_tac >> simp[topo_sorted_def] >>
  rpt strip_tac >>
  `EL i (DROP n l) = EL (i + n) l` by simp[EL_DROP] >>
  `EL j (DROP n l) = EL (j + n) l` by simp[EL_DROP] >>
  gvs[] >>
  qpat_x_assum `topo_sorted dep l` mp_tac >>
  rewrite_tac[topo_sorted_def] >>
  disch_then (qspecl_then [`i + n`, `j + n`] mp_tac) >> simp[]
QED

(* Decompose run_insts abort into OK prefix + first aborting instruction *)
Triviality run_insts_first_abort:
  !fuel ctx l s a sa.
    run_insts fuel ctx l s = Abort a sa ==>
    ?k sk. k < LENGTH l /\
           run_insts fuel ctx (TAKE k l) s = OK sk /\
           ?sa'. step_inst fuel ctx (EL k l) sk = Abort a sa'
Proof
  gen_tac >> gen_tac >> Induct >> rpt strip_tac >>
  gvs[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[]
  >- ((* head OKs, tail aborts *)
      first_x_assum $ drule_then strip_assume_tac >>
      qexists `SUC k` >> simp[run_insts_def] >> metis_tac[])
  >> (* head aborts *)
     (qexists `0` >> simp[run_insts_def])
QED

(* non-barrier + non-terminator + non-INVOKE + non-ext_call => NoFail *)
Triviality not_barrier_nofail:
  !inst. ~is_barrier inst /\
         ~is_terminator inst.inst_opcode /\
         ~is_ext_call_op inst.inst_opcode /\
         inst.inst_opcode <> INVOKE ==>
         opcode_fail_class inst.inst_opcode = NoFail
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_barrier_def, is_volatile_def, is_alloca_op_def,
      is_terminator_def, is_ext_call_op_def, opcode_fail_class_def]
QED

(* ~is_barrier implies ~is_ext_call_op and <> INVOKE *)
Triviality not_barrier_implies:
  !inst. ~is_barrier inst ==>
    ~is_ext_call_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[is_barrier_def, is_volatile_def, is_ext_call_op_def, is_alloca_op_def]
QED

(* Prefix before a barrier in topo-sorted list: same elements in both orderings.
   By tc_connected_before_after, TAKE k l = FILTER (TC dep b) l for both lists.
   Since PERM l1 l2, FILTER on a predicate gives PERM of the filtered lists. *)
Triviality barrier_prefix_perm:
  !l1 l2 dep k.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted (TC dep) l1 /\ topo_sorted (TC dep) l2 /\
    (!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
           TC dep b y \/ TC dep y b) /\
    k < LENGTH l1 /\ is_barrier (EL k l1) ==>
    PERM (TAKE k l1) (TAKE k l2)
Proof
  rpt strip_tac >>
  qabbrev_tac `b = EL k l1` >>
  `EL k l2 = b` by metis_tac[barriers_same_el] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `MEM b l1` by metis_tac[MEM_EL] >>
  `!y. MEM y l1 /\ y <> b ==> TC dep b y \/ TC dep y b` by
    metis_tac[] >>
  `!y. MEM y l2 /\ y <> b ==> TC dep b y \/ TC dep y b` by
    metis_tac[PERM_MEM_EQ] >>
  (* tc_connected_before_after for l1 *)
  `EVERY (\y. TC dep b y) (TAKE k l1)` by
    (qspecl_then [`l1`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[Abbr `b`]) >>
  `EVERY (\y. ~TC dep b y) (DROP (SUC k) l1)` by
    (qspecl_then [`l1`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[Abbr `b`]) >>
  (* tc_connected_before_after for l2 *)
  `k < LENGTH l2` by simp[] >>
  `EVERY (\y. TC dep b y) (TAKE k l2)` by
    (qspecl_then [`l2`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[]) >>
  `EVERY (\y. ~TC dep b y) (DROP (SUC k) l2)` by
    (qspecl_then [`l2`, `dep`, `b`, `k`] mp_tac tc_connected_before_after >>
     simp[]) >>
  (* Core: TC dep b x forces x to appear before k in any topo_sorted list *)
  `!l' j'. topo_sorted (TC dep) l' /\ ALL_DISTINCT l' /\
           k < LENGTH l' /\ EL k l' = b /\
           j' < LENGTH l' /\ j' <> k /\ TC dep b (EL j' l') ==> j' < k` by
    (rpt gen_tac >> strip_tac >>
     spose_not_then assume_tac >>
     `k < j'` by simp[] >>
     qpat_assum `topo_sorted _ l'` mp_tac >>
     rewrite_tac[topo_sorted_def] >>
     disch_then (qspecl_then [`k`, `j'`] mp_tac) >> simp[]) >>
  (* Subset direction 1: TAKE k l1 ⊆ TAKE k l2 *)
  `!x. MEM x (TAKE k l1) ==> MEM x (TAKE k l2)` by
    suspend "dir1" >>
  (* Subset direction 2: TAKE k l2 ⊆ TAKE k l1 *)
  `!x. MEM x (TAKE k l2) ==> MEM x (TAKE k l1)` by
    suspend "dir2" >>
  (* Both directions + same length + ALL_DISTINCT => PERM *)
  irule PERM_ALL_DISTINCT >>
  simp[ALL_DISTINCT_TAKE] >>
  metis_tac[]
QED

(*
 * Shared helper: EL k l is NOT in TAKE k l when ALL_DISTINCT
 *)
Triviality el_not_mem_take:
  !l k. ALL_DISTINCT l /\ k < LENGTH l ==> ~MEM (EL k l) (TAKE k l)
Proof
  rpt strip_tac >>
  `MEM (EL k l) (DROP k l)` by
    (simp[MEM_DROP] >> qexists `0` >> simp[]) >>
  metis_tac[ALL_DISTINCT_TAKE_DROP]
QED

Resume barrier_prefix_perm[dir1]:
  rpt strip_tac >>
  `TC dep b x` by fs[EVERY_MEM] >>
  `x <> b` by
    (strip_tac >> gvs[Abbr `b`] >> metis_tac[el_not_mem_take]) >>
  `MEM x l2` by metis_tac[MEM_TAKE, PERM_MEM_EQ] >>
  `?j'. j' < LENGTH l2 /\ EL j' l2 = x` by metis_tac[MEM_EL] >>
  `j' <> k` by
    (strip_tac >> gvs[] >> metis_tac[el_not_mem_take]) >>
  `j' < k` by
    (qpat_x_assum `!l' j'. topo_sorted _ l' /\ _ ==> _`
       (qspecl_then [`l2`, `j'`] mp_tac) >> gvs[]) >>
  simp[MEM_EL] >> qexists `j'` >> simp[LENGTH_TAKE_EQ, EL_TAKE]
QED

Resume barrier_prefix_perm[dir2]:
  rpt strip_tac >>
  `TC dep b x` by fs[EVERY_MEM] >>
  `x <> b` by
    (strip_tac >> gvs[] >> metis_tac[el_not_mem_take]) >>
  `MEM x l1` by metis_tac[MEM_TAKE, PERM_MEM_EQ] >>
  `?j'. j' < LENGTH l1 /\ EL j' l1 = x` by metis_tac[MEM_EL] >>
  `j' <> k` by
    (strip_tac >> gvs[Abbr `b`] >> metis_tac[el_not_mem_take]) >>
  `j' < k` by
    (qpat_x_assum `!l' j'. topo_sorted _ l' /\ _ ==> _`
       (qspecl_then [`l1`, `j'`] mp_tac) >> gvs[Abbr `b`]) >>
  simp[MEM_EL] >> qexists `j'` >> simp[LENGTH_TAKE_EQ, EL_TAKE]
QED

Finalise barrier_prefix_perm

(* Bridge: non-barrier + non-term + non-ext + non-INVOKE => step_inst can't abort *)
Triviality step_inst_nofail_no_abort:
  !inst fuel ctx s a es.
    ~is_barrier inst /\ ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst s <> Abort a es
Proof
  rpt strip_tac >>
  `opcode_fail_class inst.inst_opcode = NoFail` by
    metis_tac[not_barrier_nofail] >>
  gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_nofail_not_halt_abort]
QED

(* If all instructions are non-barrier (NoFail), run_insts can't abort *)
Triviality run_insts_nofail_no_abort:
  !fuel ctx l s a sa.
    run_insts fuel ctx l s = Abort a sa /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) l /\
    EVERY (\i. ~is_barrier i) l ==>
    F
Proof
  rpt strip_tac >>
  drule run_insts_first_abort >>
  disch_then (qx_choose_then `k` strip_assume_tac) >>
  `~is_barrier (EL k l)` by gvs[EVERY_EL] >>
  `~is_terminator (EL k l).inst_opcode /\
   ~is_ext_call_op (EL k l).inst_opcode /\
   (EL k l).inst_opcode <> INVOKE` by gvs[EVERY_EL] >>
  metis_tac[step_inst_nofail_no_abort]
QED

(* Barrier-free, non-terminator instructions can only produce OK or Error *)
Triviality barrier_free_only_ok_or_error:
  !l fuel ctx s.
    EVERY (\i. ~is_barrier i) l /\
    EVERY (\i. ~is_terminator i.inst_opcode) l ==>
    (?v. run_insts fuel ctx l s = OK v) \/
    (?e. run_insts fuel ctx l s = Error e)
Proof
  rpt strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) l` by
    (gvs[EVERY_MEM] >> metis_tac[not_barrier_implies]) >>
  `EVERY (\i. ~is_ext_call_op i.inst_opcode) l` by
    (gvs[EVERY_MEM] >> metis_tac[not_barrier_implies]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) l` by
    (gvs[EVERY_MEM] >> metis_tac[not_barrier_implies]) >>
  Cases_on `run_insts fuel ctx l s` >> gvs[]
  >- metis_tac[run_insts_no_halt_intret]
  >- metis_tac[run_insts_nofail_no_abort]
  >> metis_tac[run_insts_no_halt_intret]
QED

(* Barrier-free topo-sorted perms produce identical OK or both Error *)
Triviality barrier_free_topo_perm_result:
  !l1 l2 dep fuel ctx s.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> bi_independent x y) /\
    EVERY (\i. ~is_barrier i) l1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) l1 ==>
    (?e1 e2. run_insts fuel ctx l1 s = Error e1 /\
             run_insts fuel ctx l2 s = Error e2) \/
    run_insts fuel ctx l1 s = run_insts fuel ctx l2 s
Proof
  rpt strip_tac >>
  `EVERY (\i. ~is_barrier i) l2 /\
   EVERY (\i. ~is_terminator i.inst_opcode) l2` by
    (gvs[EVERY_MEM] >> metis_tac[PERM_MEM_EQ]) >>
  `(?v. run_insts fuel ctx l1 s = OK v) \/
   (?e. run_insts fuel ctx l1 s = Error e)` by
    metis_tac[barrier_free_only_ok_or_error]
  >- (
    (* l1 OK → l2 OK with same result *)
    disj2_tac >>
    `run_insts fuel ctx l2 s = OK v` by (
      irule run_insts_topo_equiv >>
      qexistsl [`dep`, `l1`] >> simp[]) >>
    simp[]
  )
  >> (
    (* l1 Error → l2 not OK (by contrapositive of reverse topo_equiv) → l2 Error *)
    `!r. run_insts fuel ctx l2 s <> OK r` by (
      rpt strip_tac >>
      `run_insts fuel ctx l1 s = OK r` by (
        irule run_insts_topo_equiv >>
        qexistsl [`dep`, `l2`] >> simp[PERM_SYM] >>
        conj_tac
        >- (rpt strip_tac >>
            `MEM x l1 /\ MEM y l1` by metis_tac[PERM_MEM_EQ] >>
            first_x_assum irule >> simp[])
        >> metis_tac[ALL_DISTINCT_PERM]) >>
      gvs[]) >>
    `(?e2. run_insts fuel ctx l2 s = Error e2)` by
      metis_tac[barrier_free_only_ok_or_error] >>
    metis_tac[]
  )
QED

(* Like barrier_free_topo_perm_result but uses ef_commutes instead of
   bi_independent. Needed for FRONT-level proof where effects_independent prevents
   bi_independent for some effect_free pairs (MLOAD-MLOAD etc). *)
(* Parameterized: barrier-free topo-sorted perms with custom P, Q predicates
   produce identical OK or both Error. P = swap predicate, Q = element predicate. *)
Triviality barrier_free_topo_perm_result_gen:
  !P Q l1 l2 dep fuel ctx s.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!a b. P a b ==> P b a) /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> P x y) /\
    (!a b s sa sab.
       P a b /\ Q a /\ Q b /\
       step_inst fuel ctx a s = OK sa /\
       step_inst fuel ctx b sa = OK sab ==>
       ?sb. step_inst fuel ctx b s = OK sb /\
            step_inst fuel ctx a sb = OK sab) /\
    EVERY Q l1 /\
    EVERY (\i. ~is_barrier i) l1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) l1 ==>
    (?e1 e2. run_insts fuel ctx l1 s = Error e1 /\
             run_insts fuel ctx l2 s = Error e2) \/
    run_insts fuel ctx l1 s = run_insts fuel ctx l2 s
Proof
  rpt strip_tac >>
  `EVERY (\i. ~is_barrier i) l2 /\
   EVERY (\i. ~is_terminator i.inst_opcode) l2 /\
   EVERY Q l2` by
    (gvs[EVERY_MEM] >> metis_tac[PERM_MEM_EQ]) >>
  `(?v. run_insts fuel ctx l1 s = OK v) \/
   (?e. run_insts fuel ctx l1 s = Error e)` by
    metis_tac[barrier_free_only_ok_or_error]
  >- (
    disj2_tac >>
    `run_insts fuel ctx l2 s = OK v` by (
      irule run_insts_topo_equiv_gen >>
      qexistsl [`P`, `Q`, `dep`, `l1`] >> simp[]) >>
    simp[])
  >> (
    `!r. run_insts fuel ctx l2 s <> OK r` by (
      rpt strip_tac >>
      `run_insts fuel ctx l1 s = OK r` by (
        irule run_insts_topo_equiv_gen >>
        qexistsl [`P`, `Q`, `dep`, `l2`] >> simp[PERM_SYM] >>
        conj_tac
        >- (rpt strip_tac >>
            `MEM x l1 /\ MEM y l1` by metis_tac[PERM_MEM_EQ] >>
            first_x_assum irule >> simp[])
        >> metis_tac[ALL_DISTINCT_PERM]) >>
      gvs[]) >>
    `(?e2. run_insts fuel ctx l2 s = Error e2)` by
      metis_tac[barrier_free_only_ok_or_error] >>
    metis_tac[])
QED

(* ef_commutes instantiation *)
Theorem ef_commutes_swap:
  !fuel ctx a b s sa sab.
    ef_commutes a b /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rw[ef_commutes_def] >> irule step_swap_ok_effect_free >> metis_tac[]
QED

Triviality barrier_free_topo_perm_result_ef:
  !l1 l2 dep fuel ctx s.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> ef_commutes x y) /\
    EVERY (\i. ~is_barrier i) l1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) l1 ==>
    (?e1 e2. run_insts fuel ctx l1 s = Error e1 /\
             run_insts fuel ctx l2 s = Error e2) \/
    run_insts fuel ctx l1 s = run_insts fuel ctx l2 s
Proof
  rpt strip_tac >>
  mp_tac (SIMP_RULE (srw_ss()) [EVERY_MEM]
    (ISPECL [``ef_commutes``, ``\i:instruction. T``]
            barrier_free_topo_perm_result_gen)) >>
  disch_then irule >>
  rpt conj_tac
  >- metis_tac[ef_commutes_swap]
  >- metis_tac[ef_commutes_sym]
  >- gvs[EVERY_MEM]
  >- gvs[EVERY_MEM]
  >- simp[]
  >- simp[]
  >> qexists `dep` >> simp[]
QED

(* Core theorem: two topo-sorted permutations that both abort produce the
   same abort type. Direct argument (no induction needed):
   1. run_insts_first_abort on l1 gives first aborting instruction at index k
   2. That instruction must be a barrier (non-barriers are NoFail)
   3. barriers_same_el: EL k l2 = EL k l1
   4. barrier_prefix_perm + run_insts_topo_equiv: prefix in l2 also OKs to same state
   5. Same barrier at same state → same step_inst result → same abort type *)
Triviality barrier_induction_abort_type:
  !l1 l2 dep fuel ctx s a1 s1 a2 s2.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted (TC dep) l1 /\ topo_sorted (TC dep) l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~TC dep x y /\ ~TC dep y x ==> bi_independent x y) /\
    EVERY (\i. ~is_terminator i.inst_opcode /\
               ~is_ext_call_op i.inst_opcode /\ i.inst_opcode <> INVOKE) l1 /\
    (!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
           TC dep b y \/ TC dep y b) /\
    run_insts fuel ctx l1 s = Abort a1 s1 /\
    run_insts fuel ctx l2 s = Abort a2 s2 ==>
    a1 = a2
Proof
  rpt strip_tac >>
  (* Step 1: First aborting instruction in l1 *)
  qpat_x_assum `run_insts _ _ l1 _ = Abort a1 _` (strip_assume_tac o MATCH_MP run_insts_first_abort) >>
  rename1 `step_inst fuel ctx (EL k l1) sk = Abort a1 _` >>
  (* Step 2: Must be a barrier *)
  `is_barrier (EL k l1)` by
    (spose_not_then assume_tac >>
     `~is_terminator (EL k l1).inst_opcode /\
      ~is_ext_call_op (EL k l1).inst_opcode /\
      (EL k l1).inst_opcode <> INVOKE` by gvs[EVERY_EL] >>
     metis_tac[step_inst_nofail_no_abort]) >>
  (* Step 3: Same barrier at same index in l2 *)
  `EL k l2 = EL k l1` by metis_tac[barriers_same_el] >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `k < LENGTH l2` by simp[] >>
  (* Step 4: Prefix in l2 OKs to same state *)
  `PERM (TAKE k l1) (TAKE k l2)` by metis_tac[barrier_prefix_perm] >>
  `topo_sorted (TC dep) (TAKE k l1)` by (irule topo_sorted_take >> simp[]) >>
  `topo_sorted (TC dep) (TAKE k l2)` by (irule topo_sorted_take >> simp[]) >>
  `!x y. MEM x (TAKE k l1) /\ MEM y (TAKE k l1) /\ x <> y /\
         ~TC dep x y /\ ~TC dep y x ==> bi_independent x y` by
    (rpt strip_tac >>
     qpat_x_assum `!x y. MEM x l1 /\ _ ==> bi_independent x y`
       (fn th => irule th) >>
     imp_res_tac MEM_TAKE >> simp[]) >>
  `ALL_DISTINCT (TAKE k l1)` by simp[ALL_DISTINCT_TAKE] >>
  `run_insts fuel ctx (TAKE k l2) s = OK sk` by
    (irule run_insts_topo_equiv >>
     qexistsl [`TC dep`, `TAKE k l1`] >> simp[]) >>
  (* Step 5: Decompose l2 and use same barrier at same state *)
  `step_inst fuel ctx (EL k l2) sk = Abort a1 sa'` by simp[] >>
  (* l2's run_insts decomposes: prefix OK → barrier aborts *)
  qpat_x_assum `run_insts _ _ l2 _ = Abort a2 _` mp_tac >>
  `l2 = TAKE k l2 ++ [EL k l2] ++ DROP (SUC k) l2` by
    simp[TAKE_DROP_SUC] >>
  pop_assum (fn th => CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [th])))) >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  rewrite_tac[run_insts_append] >> simp[run_insts_def]
QED

(* Sorted-by-predicate list decomposes as FILTER P ++ FILTER ~P *)
Triviality sorted_pred_split:
  !l P. (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) ==>
    FILTER P l ++ FILTER ($~ o P) l = l
Proof
  Induct >> simp[] >> rpt strip_tac >>
  Cases_on `P h` >> simp[]
  >- (first_x_assum (qspec_then `P` mp_tac) >>
      impl_tac >- (rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
      simp[])
  >> (* h fails P. Then ALL elements fail P (if any passed, h would too) *)
     `EVERY (\x. ~P x) l` by
       (simp[EVERY_MEM, MEM_EL, PULL_EXISTS] >>
        rpt strip_tac >> spose_not_then assume_tac >>
        first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[]) >>
     `FILTER P l = []` by simp[FILTER_EQ_NIL] >>
     `FILTER ($~ o P) l = l` by
       (simp[FILTER_EQ_ID] >> fs[EVERY_MEM]) >>
     simp[]
QED

Triviality sorted_prefix_take_filter:
  !l P.
    (!i j. i < j /\ j < LENGTH l /\ P (EL j l) ==> P (EL i l)) ==>
    TAKE (LENGTH (FILTER P l)) l = FILTER P l
Proof
  rpt strip_tac >>
  `FILTER P l ++ FILTER ($~ o P) l = l` by metis_tac[sorted_pred_split] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM th])))) >>
  simp[TAKE_LENGTH_APPEND]
QED

Triviality pseudo_prefix_take_filter:
  !bb.
    pseudos_prefix bb ==>
    TAKE (LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions))
      bb.bb_instructions =
    FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions
Proof
  rpt strip_tac >>
  irule sorted_prefix_take_filter >>
  rpt strip_tac >>
  qpat_x_assum `pseudos_prefix bb` mp_tac >>
  simp[pseudos_prefix_def] >>
  disch_then (qspecl_then [`i`, `j`] mp_tac) >>
  impl_tac >- gvs[] >>
  simp[]
QED

Triviality pseudo_suffix_no_terminators:
  !bb p q.
    pseudos_prefix bb /\
    p <= q /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    EVERY (\i. ~is_terminator i.inst_opcode)
      (DROP p (TAKE q bb.bb_instructions))
Proof
  rpt strip_tac >> simp[EVERY_EL] >>
  rpt gen_tac >> strip_tac >>
  `q <= LENGTH bb.bb_instructions` by gvs[LENGTH_FILTER_LEQ] >>
  `n < q - p` by (
    qpat_x_assum `n < LENGTH (TAKE _ _) - p` mp_tac >>
    gvs[LENGTH_TAKE, MIN_DEF]) >>
  `n + p < q` by decide_tac >>
  `EL n (DROP p
      (TAKE (LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions))
        bb.bb_instructions)) =
   EL (n + p) bb.bb_instructions` by gvs[EL_DROP, EL_TAKE] >>
  pop_assum (fn th => rewrite_tac[th]) >>
  irule pseudo_prefix_nonterminator >> simp[]
QED

Triviality drop_take_prefix_el:
  !l p q k.
    p <= q /\ q <= LENGTH l /\ k < LENGTH (DROP p (TAKE q l)) ==>
    EL (p + k) l = EL k (DROP p (TAKE q l))
Proof
  rpt strip_tac >>
  `k + p < q` by (
    qpat_x_assum `k < LENGTH (DROP p (TAKE q l))` mp_tac >>
    simp[LENGTH_DROP, LENGTH_TAKE, MIN_DEF] >>
    decide_tac) >>
  simp[EL_DROP, EL_TAKE, ADD_COMM]
QED

Triviality drop_take_prefix_el_comm:
  !l p q k.
    p <= q /\ q <= LENGTH l /\ k < LENGTH (DROP p (TAKE q l)) ==>
    EL (k + p) l = EL k (DROP p (TAKE q l))
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[ADD_COMM] >>
  irule drop_take_prefix_el >> simp[]
QED

Triviality exec_block_skip_pseudo_suffix:
  !bb fuel ctx s p q s'.
    pseudos_prefix bb /\
    p <= q /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    run_insts fuel ctx (DROP p (TAKE q bb.bb_instructions)) s = OK s' ==>
    exec_block fuel ctx bb (s with vs_inst_idx := p) =
    exec_block fuel ctx bb (s' with vs_inst_idx := q)
Proof
  rpt strip_tac >>
  `q <= LENGTH bb.bb_instructions` by gvs[LENGTH_FILTER_LEQ] >>
  `p + LENGTH (DROP p (TAKE q bb.bb_instructions)) <=
   LENGTH bb.bb_instructions` by
    (simp[LENGTH_DROP, LENGTH_TAKE, MIN_DEF] >> decide_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
     (DROP p (TAKE q bb.bb_instructions))` by
    (irule pseudo_suffix_no_terminators >> simp[]) >>
  `!k. k < LENGTH (DROP p (TAKE q bb.bb_instructions)) ==>
       EL (p + k) bb.bb_instructions =
       EL k (DROP p (TAKE q bb.bb_instructions))` by
    (rpt strip_tac >> irule drop_take_prefix_el >> simp[]) >>
  qspecl_then [`DROP p (TAKE q bb.bb_instructions)`, `fuel`, `ctx`,
    `bb`, `s`, `p`, `s'`] mp_tac exec_block_skip_prefix_general >>
  simp[] >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  simp[LENGTH_DROP, LENGTH_TAKE, MIN_DEF] >>
  `p + (q - p) = q` by decide_tac >>
  simp[]
QED

Triviality exec_block_run_insts_pseudo_suffix_lift:
  !bb p q fuel ctx s.
    pseudos_prefix bb /\ p <= q /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    ~(?v. run_insts fuel ctx (DROP p (TAKE q bb.bb_instructions)) s = OK v) ==>
    lift_result (\_ _. T) (execution_equiv {}) revert_equiv
      (run_insts fuel ctx (DROP p (TAKE q bb.bb_instructions)) s)
      (exec_block fuel ctx bb (s with vs_inst_idx := p))
Proof
  rpt strip_tac >>
  `q <= LENGTH bb.bb_instructions` by simp[LENGTH_FILTER_LEQ] >>
  `p + LENGTH (DROP p (TAKE q bb.bb_instructions)) <= LENGTH bb.bb_instructions` by
    (simp[LENGTH_DROP, LENGTH_TAKE, MIN_DEF] >> decide_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (DROP p (TAKE q bb.bb_instructions))` by
    (irule pseudo_suffix_no_terminators >> simp[]) >>
  `!k. k < LENGTH (DROP p (TAKE q bb.bb_instructions)) ==>
       EL (p + k) bb.bb_instructions = EL k (DROP p (TAKE q bb.bb_instructions))` by
    (rpt strip_tac >> irule drop_take_prefix_el >> simp[]) >>
  irule exec_block_run_insts_lift >> simp[] >> metis_tac[]
QED

Triviality block_perm_of_same_pseudo_suffix:
  !fn bb bb' p q.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    p = phi_prefix_length bb.bb_instructions /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    DROP p (TAKE q bb'.bb_instructions) =
    DROP p (TAKE q bb.bb_instructions)
Proof
  rpt strip_tac >>
  `phi_prefix_length bb'.bb_instructions = p` by
    metis_tac[block_perm_of_same_phi_prefix] >>
  `LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) = q` by
    metis_tac[block_perm_of_same_pseudo_prefix] >>
  `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) <= q` by (
    qpat_x_assum `q = LENGTH (FILTER _ bb.bb_instructions)` (fn th => once_rewrite_tac[th]) >>
    simp[venomExecProofsTheory.phi_prefix_length_le]) >>
  `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) = p` by (
    qpat_x_assum `p = phi_prefix_length bb.bb_instructions` (fn th => once_rewrite_tac[th]) >>
    irule phi_prefix_length_filter_pseudo >> fs[bb_well_formed_def]) >>
  `p <= q` by decide_tac >>
  `q <= LENGTH bb.bb_instructions` by (
    qpat_x_assum `q = LENGTH (FILTER _ bb.bb_instructions)` (fn th => once_rewrite_tac[th]) >>
    simp[LENGTH_FILTER_LEQ]) >>
  `q <= LENGTH bb'.bb_instructions` by (
    qpat_x_assum `LENGTH (FILTER _ bb'.bb_instructions) = q` (fn th => once_rewrite_tac[GSYM th]) >>
    simp[LENGTH_FILTER_LEQ]) >>
  irule LIST_EQ >> simp[LENGTH_DROP, LENGTH_TAKE, MIN_DEF] >>
  rpt strip_tac >>
  `x + p < q` by decide_tac >>
  simp[EL_DROP, EL_TAKE] >>
  drule_all block_perm_of_same_pseudo_prefix >> strip_tac >>
  first_x_assum (qspec_then `x + p` mp_tac) >> simp[]
QED

Triviality block_perm_of_run_insts_pseudo_suffix_same:
  !fn bb bb' p q fuel ctx s.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    p = phi_prefix_length bb.bb_instructions /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    run_insts fuel ctx (DROP p (TAKE q bb'.bb_instructions)) s =
    run_insts fuel ctx (DROP p (TAKE q bb.bb_instructions)) s
Proof
  rpt strip_tac >>
  drule_all block_perm_of_same_pseudo_suffix >> simp[]
QED

(* ===== FRONT-based exec_block decomposition ===== *)

(* For a well-formed block, FRONT has no terminators and LAST is the terminator.
   exec_block = run_insts FRONT + step_inst LAST.
   If run_insts FRONT produces OK, exec_block reduces to stepping the terminator.
   If run_insts FRONT produces Abort/Error, exec_block propagates that. *)

(* FRONT elements of a well-formed block are non-terminators *)
Triviality front_no_terminators:
  !bb. bb_well_formed bb ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[EVERY_EL] >> rpt strip_tac >>
  spose_not_then assume_tac >>
  `~NULL bb.bb_instructions` by (Cases_on `bb.bb_instructions` >> gvs[]) >>
  `EL n (FRONT bb.bb_instructions) = EL n bb.bb_instructions` by
    simp[EL_FRONT] >>
  `n < LENGTH bb.bb_instructions` by
    (gvs[LENGTH_FRONT] >> Cases_on `bb.bb_instructions` >> gvs[]) >>
  `n = PRE (LENGTH bb.bb_instructions)` by
    (qpat_x_assum `bb_well_formed _` mp_tac >>
     simp[bb_well_formed_def] >> strip_tac >>
     first_x_assum irule >> gvs[]) >>
  gvs[LENGTH_FRONT]
QED

Triviality exec_block_front_ok:
  !bb fuel ctx s s'.
    bb_well_formed bb /\
    run_insts fuel ctx (FRONT bb.bb_instructions) s = OK s' ==>
    exec_block fuel ctx bb (s with vs_inst_idx := 0) =
      (let r = step_inst fuel ctx (LAST bb.bb_instructions)
                 (s' with vs_inst_idx := LENGTH (FRONT bb.bb_instructions)) in
       case r of
         OK s'' => if is_terminator (LAST bb.bb_instructions).inst_opcode
                   then if s''.vs_halted then Halt s'' else OK s''
                   else exec_block fuel ctx bb
                          (s'' with vs_inst_idx :=
                             SUC (LENGTH (FRONT bb.bb_instructions)))
       | IntRet v s'' => IntRet v s''
       | Halt s'' => Halt s''
       | Abort a s'' => Abort a s''
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule front_no_terminators >> strip_tac >>
  `exec_block fuel ctx bb (s with vs_inst_idx := 0) =
   exec_block fuel ctx bb
     (s' with vs_inst_idx := 0 + LENGTH (FRONT bb.bb_instructions))` by
    (qspecl_then [`FRONT bb.bb_instructions`, `fuel`, `ctx`, `bb`, `s`,
                   `0`, `s'`] mp_tac exec_block_skip_prefix_general >>
     simp[EL_FRONT, NULL_EQ, listTheory.LENGTH_FRONT]) >>
  simp[] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  `LENGTH (FRONT bb.bb_instructions) < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[FRONT_DEF] >> simp[LENGTH_FRONT]) >>
  simp[] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++
     [LAST bb.bb_instructions]` by metis_tac[APPEND_FRONT_LAST] >>
  `EL (LENGTH (FRONT bb.bb_instructions)) bb.bb_instructions =
     LAST bb.bb_instructions` by
    (`LENGTH (FRONT bb.bb_instructions) =
      PRE (LENGTH bb.bb_instructions)` by
       (Cases_on `bb.bb_instructions` >> gvs[FRONT_DEF] >> simp[LENGTH_FRONT]) >>
     simp[LAST_EL]) >>
  simp[LET_THM]
QED

Triviality exec_block_front_non_ok:
  !bb fuel ctx s.
    bb_well_formed bb /\
    ~(?v. run_insts fuel ctx (FRONT bb.bb_instructions) s = OK v) ==>
    lift_result (\_ _. T) (execution_equiv {}) revert_equiv
      (run_insts fuel ctx (FRONT bb.bb_instructions) s)
      (exec_block fuel ctx bb (s with vs_inst_idx := 0))
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule front_no_terminators >> strip_tac >>
  irule exec_block_run_insts_lift >>
  gvs[EL_FRONT, NULL_EQ, listTheory.LENGTH_FRONT]
QED

Triviality exec_block_same_front_ok:
  !bb bb' fuel ctx s v.
    bb_well_formed bb /\ bb_well_formed bb' /\
    LAST bb'.bb_instructions = LAST bb.bb_instructions /\
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    run_insts fuel ctx (FRONT bb.bb_instructions) s = OK v /\
    run_insts fuel ctx (FRONT bb'.bb_instructions) s = OK v ==>
    exec_block fuel ctx bb (s with vs_inst_idx := 0) =
    exec_block fuel ctx bb' (s with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> [] /\ bb'.bb_instructions <> []` by
    fs[bb_well_formed_def] >>
  `LENGTH (FRONT bb'.bb_instructions) =
   LENGTH (FRONT bb.bb_instructions)` by simp[LENGTH_FRONT] >>
  qspecl_then [`bb`, `fuel`, `ctx`, `s`, `v`] mp_tac exec_block_front_ok >>
  simp[] >> disch_then (fn th => once_rewrite_tac[th]) >>
  qspecl_then [`bb'`, `fuel`, `ctx`, `s`, `v`] mp_tac exec_block_front_ok >>
  simp[] >> disch_then (fn th => once_rewrite_tac[th]) >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  Cases_on `step_inst fuel ctx (LAST bb.bb_instructions)
              (v with vs_inst_idx := LENGTH (FRONT bb.bb_instructions))` >>
  simp[]
QED

Theorem exec_block_front_lr_lift:
  !bb bb' fuel ctx s.
    bb_well_formed bb /\ bb_well_formed bb' /\
    LAST bb'.bb_instructions = LAST bb.bb_instructions /\
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_insts fuel ctx (FRONT bb.bb_instructions) s)
      (run_insts fuel ctx (FRONT bb'.bb_instructions) s) ==>
    (?e. exec_block fuel ctx bb (s with vs_inst_idx := 0) = Error e) /\
    (?e. exec_block fuel ctx bb' (s with vs_inst_idx := 0) = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (exec_block fuel ctx bb (s with vs_inst_idx := 0))
      (exec_block fuel ctx bb' (s with vs_inst_idx := 0))
Proof
  rpt strip_tac >>
  Cases_on `run_insts fuel ctx (FRONT bb.bb_instructions) s` >>
  Cases_on `run_insts fuel ctx (FRONT bb'.bb_instructions) s` >>
  gvs[lift_result_def]
  >- (disj2_tac >>
      imp_res_tac state_equiv_empty_eq >> gvs[] >>
      drule_all exec_block_same_front_ok >>
      disch_then (fn th => rewrite_tac[th]) >>
      Cases_on `exec_block fuel ctx bb' (s with vs_inst_idx := 0)` >>
      simp[lift_result_def, state_equiv_refl, execution_equiv_refl,
           revert_equiv_def]) >>
  (`lift_result (\_ _. T) (execution_equiv {}) revert_equiv
       (run_insts fuel ctx (FRONT bb.bb_instructions) s)
       (exec_block fuel ctx bb (s with vs_inst_idx := 0))` by
       (irule exec_block_front_non_ok >> gs[]) >>
   `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
       (run_insts fuel ctx (FRONT bb'.bb_instructions) s)
       (exec_block fuel ctx bb' (s with vs_inst_idx := 0))` by
       (irule exec_block_front_non_ok >> gs[]) >>
   Cases_on `exec_block fuel ctx bb (s with vs_inst_idx := 0)` >>
   Cases_on `exec_block fuel ctx bb' (s with vs_inst_idx := 0)` >>
   gvs[lift_result_def, revert_equiv_def, execution_equiv_def])
QED

(* block_body = non-pseudo elements of FRONT *)
Triviality block_body_filter_front:
  !bb. bb_well_formed bb ==>
    block_body bb =
      FILTER (\i. ~is_pseudo i.inst_opcode) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  simp[block_body_def] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]` by
    metis_tac[APPEND_FRONT_LAST] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  simp[FILTER_APPEND_DISTRIB] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `~is_pseudo (LAST bb.bb_instructions).inst_opcode` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     gvs[is_pseudo_def, is_terminator_def]) >>
  simp[] >>
  drule front_no_terminators >> strip_tac >>
  simp[FILTER_EQ] >> rpt strip_tac >>
  res_tac >> gvs[EVERY_MEM]
QED

Triviality block_body_pseudo_prefix_nonpseudo_sched:
  !bb phis sched.
    sched <> [] /\
    EVERY (\i. is_pseudo i.inst_opcode) phis /\
    EVERY (\i. ~is_pseudo i.inst_opcode) sched /\
    bb_well_formed (bb with bb_instructions := phis ++ sched) ==>
    block_body (bb with bb_instructions := phis ++ sched) = FRONT sched
Proof
  rpt strip_tac >>
  drule block_body_filter_front >> strip_tac >> simp[] >>
  `FRONT (phis ++ sched) = phis ++ FRONT sched` by
    simp[rich_listTheory.FRONT_APPEND_NOT_NIL] >>
  simp[FILTER_APPEND_DISTRIB] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) phis = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  simp[] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) (FRONT sched)` by
    (fs[EVERY_MEM] >> metis_tac[rich_listTheory.MEM_FRONT_NOT_NIL]) >>
  simp[FILTER_EQ_ID]
QED

Triviality pseudo_count_front:
  !bb.
    bb_well_formed bb ==>
    LENGTH (FILTER (\i. is_pseudo i.inst_opcode) (FRONT bb.bb_instructions)) =
    LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)
Proof
  rpt strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]` by
    metis_tac[APPEND_FRONT_LAST] >>
  pop_assum (fn th => CONV_TAC (RAND_CONV (RAND_CONV (ONCE_REWRITE_CONV [th])))) >>
  simp[FILTER_APPEND_DISTRIB] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by fs[bb_well_formed_def] >>
  `~is_pseudo (LAST bb.bb_instructions).inst_opcode` by
    (Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     gvs[is_pseudo_def, is_terminator_def]) >>
  simp[]
QED

(* LENGTH l = LENGTH (FILTER P l) + LENGTH (FILTER (~P) l) *)
Triviality length_filter_complement:
  !P l. LENGTH l = LENGTH (FILTER P l) + LENGTH (FILTER ($~ o P) l)
Proof
  gen_tac >> Induct_on `l` >> simp[FILTER] >>
  rpt strip_tac >> Cases_on `P h` >> simp[]
QED

(* ===== FRONT-level PERM and topo_sorted for run_insts_topo_lift ===== *)

(* PERM l (FILTER P l ++ FILTER ~P l) — standard list theory *)
Triviality perm_filter_partition:
  !l P. PERM l (FILTER P l ++ FILTER (\x. ~P x) l)
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `P h` >> gvs[PERM_CONS_IFF] >>
  irule CONS_PERM >> simp[]
QED

(* Pseudos (PHI/PARAM) are bi_independent of non-dep instructions.
   Key facts: effect_free, NoFail, not terminator/alloca/ext/INVOKE,
   and ssa_form prevents data/output overlap for non-dep pairs. *)
Triviality pseudo_bi_independent:
  !p i.
    is_pseudo p.inst_opcode /\
    ~is_terminator i.inst_opcode /\
    ~is_alloca_op i.inst_opcode /\
    ~is_ext_call_op i.inst_opcode /\
    i.inst_opcode <> INVOKE /\
    DISJOINT (set (inst_defs p)) (set (inst_uses i)) /\
    DISJOINT (set (inst_defs i)) (set (inst_uses p)) /\
    DISJOINT (set (inst_defs p)) (set (inst_defs i)) ==>
    bi_independent p i
Proof
  rw[bi_independent_def] >>
  Cases_on `p.inst_opcode` >> gvs[is_pseudo_def] >>
  simp[effects_independent_def, abort_compatible_def,
       is_effect_free_op_def, read_effects_def, write_effects_def,
       is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
       opcode_fail_class_def, empty_effects_def]
QED

(* Two distinct instructions in fn_insts can't share an output variable *)
Triviality ssa_no_shared_output:
  !fn i1 i2 v.
    ssa_form fn /\ MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
    i1 <> i2 /\ MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==>
    F
Proof
  rw[ssa_form_def, fn_insts_def] >>
  metis_tac[all_distinct_flat_map_disjoint]
QED

(* Consequence: distinct same-block instructions have disjoint defs *)
Theorem ssa_disjoint_defs:
  !fn bb i1 i2.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    MEM i1 bb.bb_instructions /\ MEM i2 bb.bb_instructions /\ i1 <> i2 ==>
    DISJOINT (set (inst_defs i1)) (set (inst_defs i2))
Proof
  rpt strip_tac >>
  simp[inst_defs_def, pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  metis_tac[ssa_no_shared_output, mem_fn_insts_blocks, fn_insts_def]
QED

(* Key: pseudo inst_id is not among non-pseudo inst_ids *)
Triviality pseudo_id_not_in_nonpseudo:
  !bi p.
    is_pseudo p.inst_opcode /\ MEM p bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    ~MEM p.inst_id (MAP (\i. i.inst_id)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  rpt strip_tac >> gvs[MEM_MAP, MEM_FILTER] >>
  (* y is non-pseudo, MEM y bi, y.inst_id = p.inst_id *)
  (* By ALL_DISTINCT MAP inst_id, y = p. But y is non-pseudo, p is pseudo. *)
  gvs[MEM_EL] >>
  `EL n (MAP (\i. i.inst_id) bi) = EL n' (MAP (\i. i.inst_id) bi)` by
    simp[EL_MAP] >>
  `n < LENGTH (MAP (\i. i.inst_id) bi) /\
   n' < LENGTH (MAP (\i. i.inst_id) bi)` by simp[] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Helper: FOLDL with |+ from list elements has FDOM ⊆ initial ∪ list_ids.
   Stated without let to avoid IH matching issues. *)
Triviality fdom_chain_foldl:
  !l (eda:num |-> instruction list) prev.
    FDOM (FST (FOLDL (\(acc,prev) (inst:instruction).
      (acc |+ (inst.inst_id,
        case prev of NONE =>
          (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
        | SOME p =>
          if MEM p (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
          then (case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)
          else p::(case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds)),
       SOME inst)) (eda,prev) l))
    SUBSET (FDOM eda UNION set (MAP (\i. i.inst_id) l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  qmatch_goalsub_abbrev_tac `FOLDL _ (eda',_) l` >>
  first_x_assum (qspecl_then [`eda'`, `SOME h`] mp_tac) >>
  `FDOM eda' = h.inst_id INSERT FDOM eda` by
    simp[Abbr `eda'`, FDOM_FUPDATE] >>
  strip_tac >> irule SUBSET_TRANS >> qexists `FDOM eda' UNION set (MAP (\i. i.inst_id) l)` >>
  simp[] >> simp[SUBSET_DEF] >> metis_tac[]
QED

(* FDOM of build_eda FOLDL is subset of accumulator FDOM + list inst_ids *)
Triviality fdom_build_eda_foldl:
  !l (acc:num |-> instruction list) et.
    FDOM (FST (FOLDL (\(acc_map,et) inst.
      (\(deps,et'). (acc_map |+ (inst.inst_id, deps), et'))
        (compute_effect_deps et inst)) (acc,et) l))
    SUBSET (FDOM acc UNION set (MAP (\i. i.inst_id) l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `compute_effect_deps et h` >>
  first_x_assum (qspecl_then [`acc |+ (h.inst_id, q)`, `r`] mp_tac) >>
  simp[FDOM_FUPDATE, SUBSET_DEF] >> metis_tac[]
QED

(* FDOM of build_eda is subset of non-pseudo inst_ids *)
Triviality fdom_build_eda:
  !bi. FDOM (build_eda bi) SUBSET
       set (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  gen_tac >> simp[build_eda_def, LET_THM] >>
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`,
               `FEMPTY`, `empty_effect_track`]
    mp_tac fdom_build_eda_foldl >>
  simp[FDOM_FEMPTY]
QED

(* FDOM of add_deps_on_barrier: only adds keys from non-pseudo list *)
Triviality fdom_on_barrier_foldl:
  !l (eda:num |-> instruction list) lb.
    FDOM (FST (FOLDL (\(acc,last_bar) inst.
      let old_deps = case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds in
      if is_barrier inst then (acc, SOME inst)
      else let new_deps = case last_bar of NONE => old_deps
           | SOME b => if MEM b old_deps then old_deps else b::old_deps
           in (acc |+ (inst.inst_id, new_deps), last_bar))
      (eda,lb) l))
    SUBSET (FDOM eda UNION set (MAP (\i. i.inst_id) l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `is_barrier h` >> simp[LET_THM]
  >- (first_x_assum (qspecl_then [`eda`, `SOME h`] mp_tac) >>
      simp[LET_THM, SUBSET_DEF] >> metis_tac[])
  >> (qmatch_goalsub_abbrev_tac `FOLDL _ (eda',_) l` >>
      first_x_assum (qspecl_then [`eda'`, `lb`] mp_tac) >>
      simp[LET_THM] >>
      `FDOM eda' = h.inst_id INSERT FDOM eda` by
        simp[Abbr `eda'`, FDOM_FUPDATE] >>
      simp[SUBSET_DEF] >> metis_tac[])
QED

Triviality fdom_add_deps_on_barrier:
  !bi eda. FDOM (add_deps_on_barrier bi eda) SUBSET
           FDOM eda UNION set (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  rpt gen_tac >> simp[add_deps_on_barrier_def, LET_THM] >>
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`, `eda`, `NONE`]
    mp_tac fdom_on_barrier_foldl >> simp[]
QED

(* FDOM of add_deps_from_barrier: only adds keys from non-pseudo list *)
Triviality fdom_from_barrier_foldl:
  !l (eda:num |-> instruction list) pi.
    FDOM (FST (FOLDL (\(acc,prev_insts) inst.
      if is_barrier inst then
        let old_deps = case FLOOKUP acc inst.inst_id of NONE => [] | SOME ds => ds;
            new_deps = FOLDL (\ds p. if MEM p ds then ds else p::ds)
                       old_deps prev_insts
        in (acc |+ (inst.inst_id, new_deps), prev_insts ++ [inst])
      else (acc, prev_insts ++ [inst]))
      (eda,pi) l))
    SUBSET (FDOM eda UNION set (MAP (\i. i.inst_id) l))
Proof
  Induct >> simp[] >> rpt gen_tac >>
  first_x_assum (mp_tac o SIMP_RULE (srw_ss()) [LET_THM]) >>
  Cases_on `is_barrier h` >> simp[LET_THM]
  >- (disch_then (qspecl_then
        [`eda |+ (h.inst_id,
            FOLDL (\ds p. if MEM p ds then ds else p::ds)
              (case FLOOKUP eda h.inst_id of NONE => [] | SOME ds => ds) pi')`,
         `pi' ++ [h]`] mp_tac) >>
      simp[FDOM_FUPDATE, SUBSET_DEF] >> metis_tac[])
  >> (disch_then (qspecl_then [`eda`, `pi' ++ [h]`] mp_tac) >>
      simp[SUBSET_DEF] >> metis_tac[])
QED

Triviality fdom_add_deps_from_barrier:
  !bi eda. FDOM (add_deps_from_barrier bi eda) SUBSET
           FDOM eda UNION set (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  rpt gen_tac >> simp[add_deps_from_barrier_def, LET_THM] >>
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bi`, `eda`, `[]`]
    mp_tac fdom_from_barrier_foldl >> simp[]
QED

(* FDOM of add_chain_deps: only adds keys from non-pseudo list *)
Triviality fdom_add_chain_deps:
  !P' bi eda. FDOM (add_chain_deps P' bi eda) SUBSET
              FDOM eda UNION set (MAP (\i. i.inst_id)
                (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  rpt gen_tac >> simp[add_chain_deps_def, LET_THM] >>
  irule SUBSET_TRANS >> irule_at Any fdom_chain_foldl >>
  simp[UNION_SUBSET, SUBSET_DEF, MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* FDOM of build_full_eda: only contains non-pseudo inst_ids *)
Triviality fdom_build_full_eda:
  !bi. FDOM (build_full_eda bi) SUBSET
       set (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
Proof
  gen_tac >>
  simp[build_full_eda_def, add_alloca_deps_def,
       add_barrier_deps_def, add_abort_deps_def] >>
  qabbrev_tac `ids = set (MAP (\i. i.inst_id)
    (FILTER (\i. ~is_pseudo i.inst_opcode) bi))` >>
  (* Helper: each layer preserves SUBSET ids *)
  `!P eda. FDOM eda SUBSET ids ==> FDOM (add_chain_deps P bi eda) SUBSET ids` by
    (rpt strip_tac >> irule SUBSET_TRANS >>
     irule_at Any fdom_add_chain_deps >>
     simp[Abbr `ids`, UNION_SUBSET]) >>
  `!eda. FDOM eda SUBSET ids ==> FDOM (add_deps_on_barrier bi eda) SUBSET ids` by
    (rpt strip_tac >> irule SUBSET_TRANS >>
     irule_at Any fdom_add_deps_on_barrier >>
     simp[Abbr `ids`, UNION_SUBSET]) >>
  `!eda. FDOM eda SUBSET ids ==> FDOM (add_deps_from_barrier bi eda) SUBSET ids` by
    (rpt strip_tac >> irule SUBSET_TRANS >>
     irule_at Any fdom_add_deps_from_barrier >>
     simp[Abbr `ids`, UNION_SUBSET]) >>
  `FDOM (build_eda bi) SUBSET ids` by
    (irule SUBSET_TRANS >> irule_at Any fdom_build_eda >>
     simp[Abbr `ids`]) >>
  metis_tac[]
QED

(* EDA has no entry for pseudo instruction ids *)
Triviality build_full_eda_pseudo_none:
  !bi p.
    is_pseudo p.inst_opcode /\ MEM p bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) ==>
    FLOOKUP (build_full_eda bi) p.inst_id = NONE
Proof
  rpt strip_tac >>
  drule_all pseudo_id_not_in_nonpseudo >> strip_tac >>
  simp[FLOOKUP_DEF] >> strip_tac >>
  mp_tac (SPEC_ALL fdom_build_full_eda) >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

(* Helper: no forward data dependency in a well-formed SSA block.
   If i < j in a block, EL i cannot use a variable defined by EL j. *)
Triviality no_forward_data_dep:
  !fn bb i j.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
    i < j /\ j < LENGTH bb.bb_instructions ==>
    DISJOINT (set (inst_uses (EL i bb.bb_instructions)))
             (set (inst_defs (EL j bb.bb_instructions)))
Proof
  rpt strip_tac >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  spose_not_then strip_assume_tac >> rename1 `MEM v _` >>
  `MEM (Var v) (EL i bi).inst_operands` by
    gvs[inst_uses_def, MEM_operand_vars_iff] >>
  `MEM v (EL j bi).inst_outputs` by fs[inst_defs_def] >>
  (* EL i and EL j are distinct *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) bi)` by
    (simp[Abbr `bi`] >> metis_tac[bb_inst_ids_distinct]) >>
  `i < LENGTH bi` by decide_tac >>
  `EL i bi <> EL j bi` by
    (`ALL_DISTINCT bi` by metis_tac[ALL_DISTINCT_MAP] >>
     `i <> j` by decide_tac >> metis_tac[ALL_DISTINCT_EL_IMP]) >>
  (* Both are MEM of bb.bb_instructions *)
  `MEM (EL i bi) bi /\ MEM (EL j bi) bi` by metis_tac[MEM_EL] >>
  (* Both are in fn_insts *)
  `MEM (EL i bi) (fn_insts fn) /\ MEM (EL j bi) (fn_insts fn)` by
    (simp[Abbr `bi`] >>
     conj_tac >> irule mem_fn_insts_intro >> qexists `bb` >> simp[MEM_EL] >>
     metis_tac[]) >>
  (* def_dominates_uses gives us a defining instruction for v *)
  `def_dominates_uses fn` by gvs[wf_ssa_def] >>
  qpat_x_assum `def_dominates_uses _`
    (strip_assume_tac o REWRITE_RULE[def_dominates_uses_def]) >>
  first_x_assum (qspecl_then [`bb`, `EL i bi`, `v`] mp_tac) >>
  impl_tac >- (simp[Abbr `bi`, MEM_EL] >> metis_tac[MEM_EL]) >>
  strip_tac >>
  (* def_inst = EL j bi by ssa_form uniqueness *)
  `ssa_form fn` by gvs[wf_ssa_def] >>
  `MEM def_inst (fn_insts fn)` by
    (irule mem_fn_insts_intro >> qexists `def_bb` >> simp[]) >>
  `def_inst = EL j bi` by
    metis_tac[ssa_unique_output, inst_defs_def] >>
  gvs[] >>
  (* def_bb = bb: EL j bi is in both def_bb and bb.
     By fn_inst_ids_distinct, instruction IDs are unique across all blocks,
     so these must be the same block. *)
  `def_bb = bb` by
    (spose_not_then assume_tac >>
     qspecl_then [`fn.fn_blocks`,
       `\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
       `def_bb`, `bb`, `(EL j bi).inst_id`]
       mp_tac all_distinct_flat_map_disjoint >>
     simp[MEM_MAP] >>
     gvs[wf_function_def, fn_inst_ids_distinct_def] >>
     conj_tac >> qexists `EL j bi` >>
     simp[Abbr `bi`, MEM_EL] >> metis_tac[]) >>
  gvs[] >>
  (* Now: i' < j' < LENGTH bi, EL i' bi = EL j bi, EL j' bi = EL i bi
     By ALL_DISTINCT: i' = j, j' = i. So j < i. But i < j. *)
  `ALL_DISTINCT bi` by metis_tac[ALL_DISTINCT_MAP] >>
  `i' < LENGTH bi /\ i < LENGTH bi` by decide_tac >>
  `i' = j` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `j' = i` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

(* Reverse of filter_el_mono: positions in full list → positions in FILTER *)
Triviality filter_el_mono_rev:
  !P (l:'a list) i j. ALL_DISTINCT l /\ i < j /\ j < LENGTH l /\
    P (EL i l) /\ P (EL j l) ==>
    ?i' j'. i' < j' /\ j' < LENGTH (FILTER P l) /\
            EL i' (FILTER P l) = EL i l /\
            EL j' (FILTER P l) = EL j l
Proof
  rpt strip_tac >>
  `i < LENGTH l` by decide_tac >>
  qexistsl [`LENGTH (FILTER P (TAKE i l))`,
            `LENGTH (FILTER P (TAKE j l))`] >>
  `l = TAKE i l ++ EL i l :: DROP (SUC i) l` by
    metis_tac[DROP_CONS_EL, TAKE_DROP, APPEND_ASSOC, CONS_APPEND] >>
  `l = TAKE j l ++ EL j l :: DROP (SUC j) l` by
    metis_tac[DROP_CONS_EL, TAKE_DROP, APPEND_ASSOC, CONS_APPEND] >>
  rpt conj_tac
  >- suspend "lt_ij"
  >- suspend "lt_jl"
  >- suspend "el_i"
  >> suspend "el_j"
QED

Resume filter_el_mono_rev[lt_ij]:
  (* LENGTH (FILTER P (TAKE i l)) < LENGTH (FILTER P (TAKE j l)) *)
  `FILTER P (TAKE j l) = FILTER P (TAKE i l) ++
     FILTER P (DROP i (TAKE j l))` by
    (`TAKE j l = TAKE i (TAKE j l) ++ DROP i (TAKE j l)` by
       metis_tac[TAKE_DROP] >>
     `TAKE i (TAKE j l) = TAKE i l` by simp[TAKE_TAKE_T] >>
     pop_assum (fn th => SUBST1_TAC (GSYM th)) >>
     metis_tac[FILTER_APPEND_DISTRIB]) >>
  simp[] >>
  `DROP i (TAKE j l) = TAKE (j - i) (DROP i l)` by
    simp[DROP_TAKE] >>
  `DROP i l = EL i l :: DROP (SUC i) l` by simp[DROP_CONS_EL] >>
  Cases_on `j - i` >> gvs[]
QED

Resume filter_el_mono_rev[lt_jl]:
  (* LENGTH (FILTER P (TAKE j l)) < LENGTH (FILTER P l) *)
  `FILTER P l = FILTER P (TAKE j l) ++ FILTER P (DROP j l)` by
    metis_tac[TAKE_DROP, FILTER_APPEND_DISTRIB] >>
  `DROP j l = EL j l :: DROP (SUC j) l` by simp[DROP_CONS_EL] >>
  simp[]
QED

Resume filter_el_mono_rev[el_i]:
  qspecl_then [`P`, `l`, `TAKE i l`, `DROP (SUC i) l`, `EL i l`]
    mp_tac FILTER_EL_IMP >> simp[LET_THM]
QED

Resume filter_el_mono_rev[el_j]:
  qspecl_then [`P`, `l`, `TAKE j l`, `DROP (SUC j) l`, `EL j l`]
    mp_tac FILTER_EL_IMP >> simp[LET_THM]
QED

Finalise filter_el_mono_rev

(* FRONT of a well-formed block is topo_sorted under full_dep *)
Triviality front_topo_sorted:
  !fn bb eda.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    eda = build_full_eda bb.bb_instructions ==>
    topo_sorted (full_dep eda) (FRONT bb.bb_instructions)
Proof
  rpt strip_tac >>
  simp[topo_sorted_def] >>
  qx_gen_tac `p` >> qx_gen_tac `q` >> strip_tac >>
  `bb_well_formed bb` by
    (drule (iffLR wf_function_def) >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  drule_all bb_inst_ids_distinct >> strip_tac >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  simp[EL_FRONT, NULL_EQ] >>
  `q < LENGTH bi` by
    (qpat_x_assum `q < LENGTH (FRONT bi)` mp_tac >>
     simp[LENGTH_FRONT]) >>
  `p < LENGTH bi` by simp[] >>
  imp_res_tac ALL_DISTINCT_MAP >>
  simp[full_dep_def] >>
  rpt strip_tac
  >- suspend "eda_dep"
  >- suspend "data_dep"
  >> suspend "output_alias"
QED

Resume front_topo_sorted[eda_dep]:
  `MEM (EL p bi) bi /\ MEM (EL q bi) bi` by metis_tac[MEM_EL] >>
  Cases_on `is_pseudo (EL p bi).inst_opcode`
  >- (`FLOOKUP (build_full_eda bi) (EL p bi).inst_id = NONE` by
        (irule build_full_eda_pseudo_none >> simp[]) >>
      fs[eda_dep_def])
  >> Cases_on `is_pseudo (EL q bi).inst_opcode`
  >- (fs[eda_dep_def] >>
      Cases_on `FLOOKUP (build_full_eda bi) (EL p bi).inst_id` >> fs[] >>
      `eda_wf (build_full_eda bi) bi` by simp[build_full_eda_wf] >>
      fs[eda_wf_def] >>
      rename1 `FLOOKUP _ _ = SOME deps` >>
      rename1 `MEM d0 deps` >>
      `MEM d0 bi /\ ~is_pseudo d0.inst_opcode` by metis_tac[] >>
      `d0 = EL q bi` by metis_tac[all_distinct_map_mem_inj] >>
      fs[])
  >> (* Both non-pseudo: reduce to block_body_topo_sorted *)
  qabbrev_tac `bd = block_body bb` >>
  `bd = FILTER (\x. ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode) bi` by
    simp[Abbr `bd`, block_body_def, Abbr `bi`] >>
  (* Both EL p bi and EL q bi are non-terminators (in FRONT) *)
  `~is_terminator (EL p bi).inst_opcode /\ ~is_terminator (EL q bi).inst_opcode` by
    (`EVERY (\inst. ~is_terminator inst.inst_opcode) (FRONT bi)` by
       (simp[Abbr `bi`] >> metis_tac[front_no_terminators]) >>
     `p < LENGTH (FRONT bi)` by simp[] >>
     qpat_x_assum `EVERY _ (FRONT bi)` mp_tac >>
     simp[EVERY_EL, EL_FRONT, NULL_EQ]) >>
  `?pp qq. pp < qq /\ qq < LENGTH bd /\
           EL pp bd = EL p bi /\ EL qq bd = EL q bi` by
    (qspecl_then [`\x. ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode`,
                  `bi`, `p`, `q`]
       mp_tac filter_el_mono_rev >> simp[]) >>
  `topo_sorted (full_dep (build_full_eda bi)) bd` by
    (simp[Abbr `bd`, Abbr `bi`] >> metis_tac[block_body_topo_sorted]) >>
  fs[topo_sorted_def] >>
  first_x_assum (qspecl_then [`pp`, `qq`] mp_tac) >> simp[] >>
  simp[full_dep_def]
QED

Resume front_topo_sorted[data_dep]:
  qspecl_then [`fn`, `bb`, `p`, `q`] mp_tac no_forward_data_dep >>
  simp[Abbr `bi`]
QED

Resume front_topo_sorted[output_alias]:
  `EL p bi <> EL q bi` by
    (strip_tac >> `p = q` suffices_by simp[] >>
     metis_tac[ALL_DISTINCT_EL_IMP]) >>
  `MEM (EL p bi) bi /\ MEM (EL q bi) bi` by metis_tac[MEM_EL] >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  qspecl_then [`fn`, `bb`, `EL p bi`, `EL q bi`] mp_tac ssa_disjoint_defs >>
  simp[Abbr `bi`]
QED

Finalise front_topo_sorted

Triviality terminator_not_pseudo_not_flippable:
  !op. is_terminator op ==> ~is_pseudo op /\ ~is_flippable op
Proof
  Cases >> simp[is_terminator_def, is_pseudo_def, is_flippable_def,
                is_commutative_def, is_comparator_def]
QED

(* Helper: same terminator for block_perm_of blocks *)
Theorem block_perm_of_same_last:
  !fn bb bb'.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' ==>
    LAST bb'.bb_instructions = LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  (* 1. Get bb_orig = bb from block_perm_of *)
  fs[block_perm_of_def] >>
  `bb_orig = bb` by
    (irule (GSYM wf_fn_same_label_eq) >> simp[] >> metis_tac[]) >>
  gvs[] >>
  (* 2. LAST bb is a terminator, hence non-pseudo, non-flippable *)
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `~is_pseudo (LAST bb.bb_instructions).inst_opcode /\
   ~is_flippable (LAST bb.bb_instructions).inst_opcode` by
    metis_tac[terminator_not_pseudo_not_flippable] >>
  (* 3. LAST bb is in non-pseudo filter → its inst_id in PERM *)
  `MEM (LAST bb.bb_instructions)
     (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` by
    (simp[MEM_FILTER] >> irule MEM_LAST_NOT_NIL >> simp[]) >>
  (* 4. By PERM, some instruction y' in bb' has same inst_id *)
  `MEM (LAST bb.bb_instructions).inst_id
     (MAP (\i. i.inst_id)
       (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions))` by
    (imp_res_tac PERM_MEM_EQ >> gs[MEM_MAP] >> metis_tac[]) >>
  gvs[MEM_MAP] >>
  rename1 `MEM y' (FILTER _ bb'.bb_instructions)` >>
  (* 5. y' comes from_block bb, so exists j in bb with y'=j or y'=flip j *)
  `from_block bb.bb_instructions y'` by (gs[EVERY_MEM]) >>
  `ALL_DISTINCT (MAP (\x. x.inst_id) bb.bb_instructions)` by
    metis_tac[bb_inst_ids_distinct] >>
  fs[from_block_def]
  (* Case 1: y' = j (identity) *)
  >- (
    (* j.inst_id = (LAST bb).inst_id and both MEM in bb → j = LAST bb *)
    `j = LAST bb.bb_instructions` by
      metis_tac[all_distinct_map_mem_inj, MEM_LAST_NOT_NIL] >>
    gvs[] >>
    (* LAST bb is MEM in bb' (from MEM_FILTER), hence at LAST position *)
    `MEM (LAST bb.bb_instructions) bb'.bb_instructions` by
      fs[MEM_FILTER] >>
    `bb'.bb_instructions <> []` by fs[bb_well_formed_def] >>
    gs[MEM_EL] >>
    rename1 `k < LENGTH bb'.bb_instructions` >>
    `k = PRE (LENGTH bb'.bb_instructions)` by
      (qpat_x_assum `bb_well_formed bb'` mp_tac >>
       simp[bb_well_formed_def]) >>
    gs[LAST_EL]
  )
  (* Case 2: y' = flip_operands j, is_flippable j *)
  >> (
    (* (flip_operands j).inst_id = j.inst_id = (LAST bb).inst_id *)
    `j.inst_id = (LAST bb.bb_instructions).inst_id` by
      metis_tac[flip_operands_inst_id] >>
    `j = LAST bb.bb_instructions` by
      metis_tac[all_distinct_map_mem_inj, MEM_LAST_NOT_NIL] >>
    (* But is_flippable j contradicts ~is_flippable (LAST bb) *)
    gs[]
  )
QED

(* PERM of DROPs from PERM of full lists + PERM of TAKEs + same element at k *)
Triviality perm_drop_from_take:
  !l1 l2 k. PERM l1 l2 /\ PERM (TAKE k l1) (TAKE k l2) /\
    k < LENGTH l1 /\ LENGTH l2 = LENGTH l1 /\ EL k l1 = EL k l2 ==>
    PERM (DROP (SUC k) l1) (DROP (SUC k) l2)
Proof
  rpt strip_tac >>
  `l1 = TAKE k l1 ++ [EL k l1] ++ DROP (SUC k) l1` by simp[TAKE_DROP_SUC] >>
  `l2 = TAKE k l2 ++ [EL k l2] ++ DROP (SUC k) l2` by simp[TAKE_DROP_SUC] >>
  `PERM (TAKE k l1 ++ [EL k l1] ++ DROP (SUC k) l1)
        (TAKE k l2 ++ [EL k l2] ++ DROP (SUC k) l2)` by metis_tac[] >>
  gvs[] >>
  qabbrev_tac `tk1 = TAKE k l1` >>
  qabbrev_tac `tk2 = TAKE k l2` >>
  qabbrev_tac `dk1 = DROP (SUC k) l1` >>
  qabbrev_tac `dk2 = DROP (SUC k) l2` >>
  qabbrev_tac `b = EL k l2` >>
  `PERM (tk1 ++ [b] ++ dk1) (tk2 ++ [b] ++ dk2)` by metis_tac[] >>
  `PERM (tk2 ++ [b] ++ dk2) (tk1 ++ [b] ++ dk2)` by
    (once_rewrite_tac[GSYM APPEND_ASSOC] >>
     metis_tac[PERM_APPEND_IFF, PERM_SYM]) >>
  `PERM (tk1 ++ [b] ++ dk1) (tk1 ++ [b] ++ dk2)` by
    metis_tac[PERM_TRANS] >>
  metis_tac[PERM_APPEND_IFF, APPEND_ASSOC, PERM_CONS_IFF]
QED

(* Split run_insts at position k into prefix, element k, suffix *)
Triviality run_insts_split_at:
  !l k fuel ctx s.
    k < LENGTH l ==>
    run_insts fuel ctx l s =
      case run_insts fuel ctx (TAKE k l) s of
        OK v => (case step_inst fuel ctx (EL k l) v of
                   OK v' => run_insts fuel ctx (DROP (SUC k) l) v'
                 | Halt h => Halt h
                 | Abort a v2 => Abort a v2
                 | IntRet ir v3 => IntRet ir v3
                 | Error e => Error e)
      | r => r
Proof
  rpt strip_tac >>
  `l = TAKE k l ++ [EL k l] ++ DROP (SUC k) l` by simp[TAKE_DROP_SUC] >>
  pop_assum (fn th => CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [th]))) >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  rewrite_tac[run_insts_append] >> simp[run_insts_def] >>
  Cases_on `run_insts fuel ctx (TAKE k l) s` >> simp[] >>
  Cases_on `step_inst fuel ctx (EL k l) v` >> simp[]
QED

(* ===== Core barrier-segmentation theorem =====
   Two topo-sorted permutations of a non-terminator list produce either:
   - Both Error (possibly different error strings), OR
   - Identical run_insts results.
   Uses barrier_free_topo_perm_result for each barrier-free segment. *)
Triviality run_insts_topo_full_lift:
  !l1 l2 dep fuel ctx s.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted (TC dep) l1 /\ topo_sorted (TC dep) l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~TC dep x y /\ ~TC dep y x ==> bi_independent x y) /\
    EVERY (\i. ~is_terminator i.inst_opcode) l1 /\
    (!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
           TC dep b y \/ TC dep y b) ==>
    (?e1 e2. run_insts fuel ctx l1 s = Error e1 /\
             run_insts fuel ctx l2 s = Error e2) \/
    run_insts fuel ctx l1 s = run_insts fuel ctx l2 s
Proof
  measureInduct_on `LENGTH l1` >>
  rpt strip_tac >>
  Cases_on `l1 = []`
  >- (gvs[] >> imp_res_tac PERM_NIL >> simp[run_insts_def])
  >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) l2` by
    (gvs[EVERY_MEM] >> metis_tac[PERM_MEM_EQ]) >>
  Cases_on `EXISTS is_barrier l1`
  >- (
    (* === BARRIER CASE === *)
    `?k. k < LENGTH l1 /\ is_barrier (EL k l1) /\
         !m. m < k ==> ~is_barrier (EL m l1)` by
      (gvs[EXISTS_MEM, MEM_EL] >>
       rename1 `j < LENGTH l1` >>
       qexists `LEAST n. n < LENGTH l1 /\ is_barrier (EL n l1)` >>
       numLib.LEAST_ELIM_TAC >> conj_tac
       >- (qexists `j` >> simp[])
       >> rpt strip_tac >> gvs[] >>
          spose_not_then strip_assume_tac >>
          `m < LENGTH l1 /\ is_barrier (EL m l1)` suffices_by metis_tac[] >>
          simp[] >> first_x_assum (qspec_then `m` mp_tac) >> simp[]) >>
    `EL k l2 = EL k l1` by (
      qspecl_then [`l1`, `l2`, `dep`, `k`] mp_tac barriers_same_el >>
      (impl_tac >- ASM_REWRITE_TAC[]) >> simp[]) >>
    `k < LENGTH l2` by simp[] >>
    (* Barrier-free prefix: use barrier_free_topo_perm_result *)
    `PERM (TAKE k l1) (TAKE k l2)` by metis_tac[barrier_prefix_perm] >>
    `EVERY (\i. ~is_barrier i) (TAKE k l1)` by
      (simp[EVERY_EL, EL_TAKE] >> metis_tac[]) >>
    qspecl_then [`TAKE k l1`, `TAKE k l2`, `TC dep`, `fuel`, `ctx`, `s`]
      mp_tac barrier_free_topo_perm_result >>
    impl_tac >- (
      simp[ALL_DISTINCT_TAKE, EVERY_TAKE] >>
      rpt conj_tac
      >- (irule topo_sorted_take >> simp[])
      >- (irule topo_sorted_take >> simp[])
      >> (rpt strip_tac >> first_x_assum irule >>
          imp_res_tac MEM_TAKE >> simp[])) >>
    strip_tac
    >- (
      (* Prefix Error: propagate to full lists via run_insts_error_append *)
      disj1_tac >>
      `run_insts fuel ctx (TAKE k l1 ++ DROP k l1) s = Error e1` by
        (irule run_insts_error_append >> metis_tac[]) >>
      `run_insts fuel ctx (TAKE k l2 ++ DROP k l2) s = Error e2` by
        (irule run_insts_error_append >> metis_tac[]) >>
      gvs[TAKE_DROP]
    )
    >> (
      (* Prefix OK: split at barrier, use IH on suffix *)
      `(?v. run_insts fuel ctx (TAKE k l1) s = OK v) \/
       (?e. run_insts fuel ctx (TAKE k l1) s = Error e)` by
        (irule barrier_free_only_ok_or_error >> simp[EVERY_TAKE]) >>
      pop_assum strip_assume_tac
      >- (
        `run_insts fuel ctx (TAKE k l2) s = OK v` by fs[] >>
        qspecl_then [`l1`, `k`, `fuel`, `ctx`, `s`] assume_tac run_insts_split_at >>
        qspecl_then [`l2`, `k`, `fuel`, `ctx`, `s`] assume_tac run_insts_split_at >>
        gvs[] >>
        Cases_on `step_inst fuel ctx (EL k l1) v`
        >- (
          (* step_inst OK v' => IH on suffixes DROP (SUC k) *)
          gvs[] >>
          last_x_assum
            (qspec_then `DROP (SUC k) l1` mp_tac) >>
          (impl_tac >- simp[LENGTH_DROP]) >>
          disch_then (qspecl_then [`DROP (SUC k) l2`,
                                   `dep`, `fuel`, `ctx`, `v'`] mp_tac) >>
          simp[ALL_DISTINCT_DROP, EVERY_DROP] >>
          (impl_tac >- (
            conj_tac >- (irule perm_drop_from_take >> simp[]) >>
            conj_tac >- (irule topo_sorted_drop >> simp[]) >>
            conj_tac >- (irule topo_sorted_drop >> simp[]) >>
            conj_tac
            >- (rpt strip_tac >>
                qpat_x_assum `!x y. MEM x l1 /\ MEM y l1 /\ _ /\
                  ~TC dep x y /\ ~TC dep y x ==> bi_independent x y` irule >>
                imp_res_tac MEM_DROP_IMP >> simp[])
            >> (rpt strip_tac >>
                qpat_x_assum `!b y. MEM b l1 /\ MEM y l1 /\ _ /\ is_barrier b ==> _` irule >>
                imp_res_tac MEM_DROP_IMP >> simp[])
          )) >> simp[]
        )
        >> gvs[AllCaseEqs()] >> disj2_tac >> simp[]
      )
      >> (
        `run_insts fuel ctx (TAKE k l2) s = Error e` by fs[] >>
        disj1_tac >>
        qspecl_then [`l1`, `k`, `fuel`, `ctx`, `s`] mp_tac run_insts_split_at >>
        qspecl_then [`l2`, `k`, `fuel`, `ctx`, `s`] mp_tac run_insts_split_at >>
        simp[]
      )
    )
  )
  (* === NO BARRIERS === *)
  >> (
    `EVERY (\i. ~is_barrier i) l1` by gvs[NOT_EXISTS, EVERY_MEM] >>
    irule barrier_free_topo_perm_result >> simp[] >>
    qexists `TC dep` >> simp[]
  )
QED

(* Parameterized: topo-sorted perms with custom P, Q produce equal or both Error.
   Handles barriers by induction on barrier positions. *)
Triviality run_insts_topo_full_lift_gen:
  !P Q l1 l2 dep fuel ctx s.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted (TC dep) l1 /\ topo_sorted (TC dep) l2 /\
    (!a b. P a b ==> P b a) /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~TC dep x y /\ ~TC dep y x ==> P x y) /\
    (!a b s sa sab.
       P a b /\ Q a /\ Q b /\
       step_inst fuel ctx a s = OK sa /\
       step_inst fuel ctx b sa = OK sab ==>
       ?sb. step_inst fuel ctx b s = OK sb /\
            step_inst fuel ctx a sb = OK sab) /\
    EVERY Q l1 /\
    EVERY (\i. ~is_terminator i.inst_opcode) l1 /\
    (!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
           TC dep b y \/ TC dep y b) ==>
    (?e1 e2. run_insts fuel ctx l1 s = Error e1 /\
             run_insts fuel ctx l2 s = Error e2) \/
    run_insts fuel ctx l1 s = run_insts fuel ctx l2 s
Proof
  measureInduct_on `LENGTH l1` >>
  rpt strip_tac >>
  Cases_on `l1 = []`
  >- (gvs[] >> imp_res_tac PERM_NIL >> simp[run_insts_def])
  >>
  `LENGTH l2 = LENGTH l1` by metis_tac[PERM_LENGTH] >>
  `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) l2 /\ EVERY Q l2` by
    (gvs[EVERY_MEM] >> metis_tac[PERM_MEM_EQ]) >>
  Cases_on `EXISTS is_barrier l1`
  >- (
    `?k. k < LENGTH l1 /\ is_barrier (EL k l1) /\
         !m. m < k ==> ~is_barrier (EL m l1)` by
      (gvs[EXISTS_MEM, MEM_EL] >>
       rename1 `j < LENGTH l1` >>
       qexists `LEAST n. n < LENGTH l1 /\ is_barrier (EL n l1)` >>
       numLib.LEAST_ELIM_TAC >> conj_tac
       >- (qexists `j` >> simp[])
       >> rpt strip_tac >> gvs[] >>
          spose_not_then strip_assume_tac >>
          `m < LENGTH l1 /\ is_barrier (EL m l1)` suffices_by metis_tac[] >>
          simp[] >> first_x_assum (qspec_then `m` mp_tac) >> simp[]) >>
    `EL k l2 = EL k l1` by (
      qspecl_then [`l1`, `l2`, `dep`, `k`] mp_tac barriers_same_el >>
      (impl_tac >- ASM_REWRITE_TAC[]) >> simp[]) >>
    `k < LENGTH l2` by simp[] >>
    `PERM (TAKE k l1) (TAKE k l2)` by
      (qspecl_then [`l1`, `l2`, `dep`, `k`] mp_tac barrier_prefix_perm >>
       simp[]) >>
    `EVERY (\i. ~is_barrier i) (TAKE k l1)` by
      (simp[EVERY_EL, EL_TAKE] >> metis_tac[]) >>
    qspecl_then [`P`, `Q`, `TAKE k l1`, `TAKE k l2`, `TC dep`,
                 `fuel`, `ctx`, `s`]
      mp_tac barrier_free_topo_perm_result_gen >>
    impl_tac >- (
      simp[ALL_DISTINCT_TAKE, EVERY_TAKE] >>
      rpt conj_tac
      >- (irule topo_sorted_take >> simp[])
      >- (irule topo_sorted_take >> simp[])
      >> (rpt strip_tac >> first_x_assum irule >>
          imp_res_tac MEM_TAKE >> simp[])) >>
    strip_tac
    >- (
      disj1_tac >>
      `run_insts fuel ctx (TAKE k l1 ++ DROP k l1) s = Error e1` by
        (irule run_insts_error_append >> metis_tac[]) >>
      `run_insts fuel ctx (TAKE k l2 ++ DROP k l2) s = Error e2` by
        (irule run_insts_error_append >> metis_tac[]) >>
      gvs[TAKE_DROP])
    >> (
      `(?v. run_insts fuel ctx (TAKE k l1) s = OK v) \/
       (?e. run_insts fuel ctx (TAKE k l1) s = Error e)` by
        (irule barrier_free_only_ok_or_error >> simp[EVERY_TAKE]) >>
      pop_assum strip_assume_tac
      >- (
        `run_insts fuel ctx (TAKE k l2) s = OK v` by fs[] >>
        qspecl_then [`l1`, `k`, `fuel`, `ctx`, `s`] assume_tac run_insts_split_at >>
        qspecl_then [`l2`, `k`, `fuel`, `ctx`, `s`] assume_tac run_insts_split_at >>
        gvs[] >>
        Cases_on `step_inst fuel ctx (EL k l1) v`
        >- (
          gvs[] >>
          last_x_assum
            (qspec_then `DROP (SUC k) l1` mp_tac) >>
          (impl_tac >- simp[LENGTH_DROP]) >>
          disch_then (qspecl_then [`P`, `Q`, `DROP (SUC k) l2`,
                                   `dep`, `fuel`, `ctx`, `v'`] mp_tac) >>
          simp[ALL_DISTINCT_DROP, EVERY_DROP] >>
          (impl_tac >- (
            conj_tac >- (irule perm_drop_from_take >> simp[]) >>
            conj_tac >- (irule topo_sorted_drop >> simp[]) >>
            conj_tac >- (irule topo_sorted_drop >> simp[]) >>
            conj_tac
            >- (rpt strip_tac >>
                qpat_x_assum `!x y. MEM x l1 /\ MEM y l1 /\ _ /\
                  ~TC dep x y /\ ~TC dep y x ==> P x y` irule >>
                imp_res_tac MEM_DROP_IMP >> simp[])
            >> (rpt strip_tac >>
                qpat_x_assum `!b y. MEM b l1 /\ MEM y l1 /\ _ /\ is_barrier b ==> _` irule >>
                imp_res_tac MEM_DROP_IMP >> simp[])
          )) >> simp[])
        >> gvs[AllCaseEqs()] >> disj2_tac >> simp[])
      >> (
        `run_insts fuel ctx (TAKE k l2) s = Error e` by fs[] >>
        disj1_tac >>
        qspecl_then [`l1`, `k`, `fuel`, `ctx`, `s`] mp_tac run_insts_split_at >>
        qspecl_then [`l2`, `k`, `fuel`, `ctx`, `s`] mp_tac run_insts_split_at >>
        simp[])))
  >> (
    `EVERY (\i. ~is_barrier i) l1` by gvs[NOT_EXISTS, EVERY_MEM] >>
    qspecl_then [`P`, `Q`, `l1`, `l2`, `TC dep`, `fuel`, `ctx`, `s`]
      mp_tac barrier_free_topo_perm_result_gen >>
    simp[])
QED

(* ef_commutes instantiation *)
Theorem run_insts_topo_full_lift_ef:
  !l1 l2 dep fuel ctx s.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted (TC dep) l1 /\ topo_sorted (TC dep) l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~TC dep x y /\ ~TC dep y x ==> ef_commutes x y) /\
    EVERY (\i. ~is_terminator i.inst_opcode) l1 /\
    (!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
           TC dep b y \/ TC dep y b) ==>
    (?e1 e2. run_insts fuel ctx l1 s = Error e1 /\
             run_insts fuel ctx l2 s = Error e2) \/
    run_insts fuel ctx l1 s = run_insts fuel ctx l2 s
Proof
  rpt strip_tac >>
  mp_tac (SIMP_RULE (srw_ss()) [EVERY_MEM]
    (ISPECL [``ef_commutes``, ``\i:instruction. T``]
            run_insts_topo_full_lift_gen)) >>
  disch_then irule >>
  rpt conj_tac
  >- metis_tac[ef_commutes_swap]
  >- metis_tac[ef_commutes_sym]
  >- gvs[EVERY_MEM]
  >- simp[]
  >- simp[]
  >> qexists `dep` >> simp[]
QED

(* block_body_full_equiv: two topologically-sorted permutations of a block's
   body produce identical run_insts results, or both Error.
   Supersedes block_body_ok_equiv (which only handled the OK case). *)
Triviality block_body_full_equiv:
  !fn bb bb' fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (MAP (choose_original (block_body bb)) (block_body bb')) ==>
    (?e1 e2. run_insts fuel ctx (block_body bb) s = Error e1 /\
             run_insts fuel ctx (block_body bb') s = Error e2) \/
    run_insts fuel ctx (block_body bb) s =
    run_insts fuel ctx (block_body bb') s
Proof
  rpt strip_tac >>
  qabbrev_tac `l1 = block_body bb` >>
  qabbrev_tac `l2_raw = block_body bb'` >>
  qabbrev_tac `l2 = MAP (choose_original l1) l2_raw` >>
  (* Step 1: run_insts l2_raw = run_insts l2 (pointwise step_inst equiv) *)
  `run_insts fuel ctx l2_raw s = run_insts fuel ctx l2 s` by
    (simp[Abbr `l2`] >>
     irule run_insts_pointwise_equiv >> simp[LENGTH_MAP] >>
     rpt strip_tac >>
     irule map_choose_original_step_equiv >>
     simp[Abbr `l1`] >>
     conj_asm1_tac
     >- (rpt strip_tac >> simp[Abbr `l2_raw`] >>
         metis_tac[block_body_from_block])
     >> metis_tac[block_body_all_distinct]) >>
  (* Step 2: apply run_insts_topo_full_lift_ef *)
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  `PERM l1 l2` by
    (simp[Abbr `l2`, Abbr `l1`] >> metis_tac[block_body_choose_perm]) >>
  `ALL_DISTINCT l1` by
    (simp[Abbr `l1`] >> metis_tac[block_body_all_distinct, ALL_DISTINCT_MAP]) >>
  (* Use restricted dep: full_dep restricted to l1 elements *)
  qabbrev_tac `dep = \x y. full_dep eda x y /\ MEM x l1 /\ MEM y l1` >>
  `topo_sorted dep l1` by
    (simp[Abbr `dep`, topo_sorted_def] >> rpt strip_tac >>
     `~full_dep eda (EL i l1) (EL j l1)` suffices_by simp[] >>
     `topo_sorted (full_dep eda) l1` by
       (simp[Abbr `l1`, Abbr `bi`] >> metis_tac[block_body_topo_sorted]) >>
     fs[topo_sorted_def]) >>
  `topo_sorted dep l2` by
    (simp[Abbr `dep`, topo_sorted_def] >> rpt strip_tac >>
     `~full_dep eda (EL i l2) (EL j l2)` suffices_by
       (strip_tac >> gvs[] >> metis_tac[PERM_MEM_EQ, MEM_EL]) >>
     `topo_sorted (full_dep eda) l2` by
       simp[Abbr `l2`, Abbr `l1`, Abbr `bi`] >>
     fs[topo_sorted_def]) >>
  `topo_sorted (TC dep) l1` by
    (irule topo_sorted_tc_closed >> simp[Abbr `dep`]) >>
  `topo_sorted (TC dep) l2` by
    (irule topo_sorted_tc_closed >>
     simp[Abbr `dep`] >>
     `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
     simp[] >> metis_tac[PERM_MEM_EQ]) >>
  (* ef_commutes for TC-dep-uncomparable pairs via block_body_uncomp_ef *)
  `!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
         ~TC dep x y /\ ~TC dep y x ==>
         ef_commutes x y` by
    (rpt strip_tac >>
     qspecl_then [`fn`, `bb`, `x`, `y`,
       `\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
              MEM a (block_body bb) /\ MEM c (block_body bb)`]
       mp_tac block_body_uncomp_ef >>
     simp[Abbr `l1`, Abbr `dep`, Abbr `eda`, Abbr `bi`]) >>
  (* EVERY non-terminator: block_body has no terminators *)
  `EVERY (\i. ~is_terminator i.inst_opcode) l1` by
    simp[Abbr `l1`, block_body_def, EVERY_MEM, MEM_FILTER] >>
  (* Barriers TC-comparable to all other block_body elements *)
  `!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
         TC dep b y \/ TC dep y b` by
    (rpt strip_tac >>
     qspecl_then [`bb`, `b`, `y`, `dep`] mp_tac barrier_tc_connected >>
     simp[Abbr `l1`, Abbr `dep`, Abbr `eda`, Abbr `bi`] >>
     metis_tac[bb_inst_ids_distinct]) >>
  (* Apply run_insts_topo_full_lift_ef *)
  qspecl_then [`l1`, `l2`, `dep`, `fuel`, `ctx`, `s`]
    mp_tac run_insts_topo_full_lift_ef >>
  simp[]
QED

(* block_perm_of implies same instruction count *)
Theorem block_perm_of_same_length:
  !fn bb bb'.
    block_perm_of fn bb' /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    bb.bb_label = bb'.bb_label ==>
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions
Proof
  rw[block_perm_of_def] >>
  `bb = bb_orig` by metis_tac[wf_fn_same_label_eq] >>
  gvs[] >>
  `LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) bb'.bb_instructions) =
   LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` by
    metis_tac[PERM_LENGTH, LENGTH_MAP] >>
  `LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) =
   LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by
    simp[] >>
  metis_tac[length_filter_complement]
QED

Triviality pseudo_prefix_front_drop_body:
  !bb q.
    bb_well_formed bb /\ pseudos_prefix bb /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    DROP q (FRONT bb.bb_instructions) = block_body bb
Proof
  rpt strip_tac >>
  qabbrev_tac `P = \i:instruction. is_pseudo i.inst_opcode` >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `q = LENGTH (FILTER P (FRONT bb.bb_instructions))` by
    (simp[Abbr `P`] >> metis_tac[pseudo_count_front]) >>
  `block_body bb = FILTER ($~ o P) (FRONT bb.bb_instructions)` by
    (simp[Abbr `P`] >> metis_tac[block_body_filter_front]) >>
  `!i j. i < j /\ j < LENGTH (FRONT bb.bb_instructions) /\
         P (EL j (FRONT bb.bb_instructions)) ==>
         P (EL i (FRONT bb.bb_instructions))` by (
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `pseudos_prefix bb` mp_tac >>
    simp[pseudos_prefix_def, Abbr `P`] >>
    disch_then (qspecl_then [`i`, `j`] mp_tac) >>
    impl_tac >- (Cases_on `bb.bb_instructions` >> gvs[EL_FRONT]) >>
    Cases_on `bb.bb_instructions` >> gvs[EL_FRONT]) >>
  `TAKE q (FRONT bb.bb_instructions) =
   FILTER P (FRONT bb.bb_instructions)` by
    metis_tac[sorted_prefix_take_filter] >>
  `FILTER P (FRONT bb.bb_instructions) ++
   FILTER ($~ o P) (FRONT bb.bb_instructions) =
   FRONT bb.bb_instructions` by metis_tac[sorted_pred_split] >>
  `TAKE q (FRONT bb.bb_instructions) ++ DROP q (FRONT bb.bb_instructions) =
   FRONT bb.bb_instructions` by simp[TAKE_DROP] >>
  metis_tac[APPEND_11]
QED

Triviality el_drop_front:
  !l q k.
    l <> [] /\ q + k < LENGTH (FRONT l) ==>
    EL (q + k) l = EL k (DROP q (FRONT l))
Proof
  rpt strip_tac >>
  `k < LENGTH (DROP q (FRONT l))` by
    (simp[LENGTH_DROP] >> decide_tac) >>
  `EL k (DROP q (FRONT l)) = EL (q + k) (FRONT l)` by
    (simp[EL_DROP] >> AP_TERM_TAC >> decide_tac) >>
  qpat_x_assum `EL k (DROP q (FRONT l)) = _` (fn th => rewrite_tac[th]) >>
  `k + q < LENGTH (FRONT l)` by decide_tac >>
  qspecl_then [`l`, `q + k`] mp_tac EL_FRONT >>
  impl_tac >- (Cases_on `l` >> gvs[NULL]) >>
  disch_then (fn th => rewrite_tac[th]) >>
  simp[]
QED

Triviality block_body_at_pseudo_end_length:
  !bb q.
    bb_well_formed bb /\ pseudos_prefix bb /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    q + LENGTH (block_body bb) = PRE (LENGTH bb.bb_instructions)
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `DROP q (FRONT bb.bb_instructions) = block_body bb` by
    (irule pseudo_prefix_front_drop_body >> simp[]) >>
  `q <= LENGTH (FRONT bb.bb_instructions)` by (
    `q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode)
          (FRONT bb.bb_instructions))` by metis_tac[pseudo_count_front] >>
    simp[LENGTH_FILTER_LEQ]) >>
  `q + LENGTH (block_body bb) = LENGTH (FRONT bb.bb_instructions)` by
    (qpat_x_assum `DROP q _ = _` (fn th => rewrite_tac[GSYM th]) >>
     simp[LENGTH_DROP]) >>
  simp[LENGTH_FRONT]
QED

Triviality block_body_at_pseudo_end_le:
  !bb q.
    bb_well_formed bb /\ pseudos_prefix bb /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    q + LENGTH (block_body bb) <= LENGTH bb.bb_instructions
Proof
  rpt gen_tac >> strip_tac >>
  drule_all block_body_at_pseudo_end_length >> strip_tac >>
  Cases_on `bb.bb_instructions` >> gvs[]
QED

Triviality block_body_at_pseudo_end_nonterm:
  !bb q.
    bb_well_formed bb /\ pseudos_prefix bb /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    EVERY (\i. ~is_terminator i.inst_opcode) (block_body bb)
Proof
  rpt gen_tac >> strip_tac >>
  `DROP q (FRONT bb.bb_instructions) = block_body bb` by
    (irule pseudo_prefix_front_drop_body >> simp[]) >>
  qpat_x_assum `DROP q _ = _` (fn th => rewrite_tac[GSYM th]) >>
  irule EVERY_DROP >> irule front_no_terminators >> simp[]
QED

Triviality block_body_at_pseudo_end_el:
  !bb q k.
    bb_well_formed bb /\ pseudos_prefix bb /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    k < LENGTH (block_body bb) ==>
    EL (q + k) bb.bb_instructions = EL k (block_body bb)
Proof
  rpt gen_tac >> strip_tac >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `DROP q (FRONT bb.bb_instructions) = block_body bb` by
    (irule pseudo_prefix_front_drop_body >> simp[]) >>
  drule_all block_body_at_pseudo_end_length >> strip_tac >>
  `q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode)
          (FRONT bb.bb_instructions))` by metis_tac[pseudo_count_front] >>
  `q <= LENGTH (FRONT bb.bb_instructions)` by simp[LENGTH_FILTER_LEQ] >>
  `LENGTH (DROP q (FRONT bb.bb_instructions)) =
   LENGTH (FRONT bb.bb_instructions) - q` by simp[LENGTH_DROP] >>
  `LENGTH (block_body bb) = LENGTH (FRONT bb.bb_instructions) - q` by
    metis_tac[] >>
  `q + k < LENGTH (FRONT bb.bb_instructions)` by decide_tac >>
  qpat_x_assum `DROP q _ = _` (fn th => rewrite_tac[GSYM th]) >>
  irule el_drop_front >> simp[]
QED

Triviality block_body_at_pseudo_end:
  !bb q.
    bb_well_formed bb /\ pseudos_prefix bb /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    q + LENGTH (block_body bb) = PRE (LENGTH bb.bb_instructions) /\
    q + LENGTH (block_body bb) <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode) (block_body bb) /\
    (!k. k < LENGTH (block_body bb) ==>
         EL (q + k) bb.bb_instructions = EL k (block_body bb))
Proof
  metis_tac[block_body_at_pseudo_end_length, block_body_at_pseudo_end_le,
            block_body_at_pseudo_end_nonterm, block_body_at_pseudo_end_el]
QED

Triviality exec_block_same_body_ok:
  !bb bb' q fuel ctx s s'.
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    LAST bb'.bb_instructions = LAST bb.bb_instructions /\
    LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) /\
    run_insts fuel ctx (block_body bb) s = OK s' /\
    run_insts fuel ctx (block_body bb') s = OK s' ==>
    exec_block fuel ctx bb (s with vs_inst_idx := q) =
    exec_block fuel ctx bb' (s with vs_inst_idx := q)
Proof
  rpt strip_tac >>
  qspecl_then [`bb`, `q`] mp_tac block_body_at_pseudo_end >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`bb'`, `q`] mp_tac block_body_at_pseudo_end >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`block_body bb`, `fuel`, `ctx`, `bb`, `s`, `q`, `s'`]
    mp_tac exec_block_skip_prefix_general >> simp[] >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  qspecl_then [`block_body bb'`, `fuel`, `ctx`, `bb'`, `s`, `q`, `s'`]
    mp_tac exec_block_skip_prefix_general >> simp[] >>
  disch_then (fn th => once_rewrite_tac[th]) >>
  `q + LENGTH (block_body bb) = PRE (LENGTH bb.bb_instructions)` by simp[] >>
  `q + LENGTH (block_body bb') = PRE (LENGTH bb'.bb_instructions)` by simp[] >>
  simp[] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  sg `PRE (LENGTH bb.bb_instructions) < LENGTH bb.bb_instructions` >-
    (Cases_on `bb.bb_instructions` >> fs[bb_well_formed_def]) >>
  sg `PRE (LENGTH bb'.bb_instructions) < LENGTH bb'.bb_instructions` >-
    (Cases_on `bb'.bb_instructions` >> fs[bb_well_formed_def]) >>
  sg `EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions =
      LAST bb.bb_instructions` >-
    (Cases_on `bb.bb_instructions` >> fs[LAST_EL]) >>
  sg `EL (PRE (LENGTH bb'.bb_instructions)) bb'.bb_instructions =
      LAST bb'.bb_instructions` >-
    (Cases_on `bb'.bb_instructions` >> fs[LAST_EL]) >>
  simp[get_instruction_def] >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by fs[bb_well_formed_def] >>
  gvs[]
QED

Triviality lift_result_same_non_ok_trans:
  !r r1 r2.
    ~(?v. r = OK v) /\
    lift_result (\_ _. T) (execution_equiv {}) revert_equiv r r1 /\
    lift_result (\_ _. T) (execution_equiv {}) revert_equiv r r2 ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv r1 r2
Proof
  Cases >> Cases_on `r1` >> Cases_on `r2` >>
  gvs[lift_result_def, execution_equiv_def, state_equiv_def,
      revert_equiv_def, FDOM_FEMPTY] >>
  metis_tac[]
QED

Triviality exec_block_body_error_lift:
  !bb bb' q fuel ctx s e1 e2.
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) /\
    run_insts fuel ctx (block_body bb) s = Error e1 /\
    run_insts fuel ctx (block_body bb') s = Error e2 ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (exec_block fuel ctx bb (s with vs_inst_idx := q))
      (exec_block fuel ctx bb' (s with vs_inst_idx := q))
Proof
  rpt strip_tac >>
  qspecl_then [`bb`, `q`] mp_tac block_body_at_pseudo_end >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`bb'`, `q`] mp_tac block_body_at_pseudo_end >>
  impl_tac >- simp[] >> strip_tac >>
  sg `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
        (run_insts fuel ctx (block_body bb) s)
        (exec_block fuel ctx bb (s with vs_inst_idx := q))` >-
    (irule exec_block_run_insts_lift >> simp[]) >>
  sg `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
        (run_insts fuel ctx (block_body bb') s)
        (exec_block fuel ctx bb' (s with vs_inst_idx := q))` >-
    (irule exec_block_run_insts_lift >> simp[]) >>
  Cases_on `exec_block fuel ctx bb (s with vs_inst_idx := q)` >>
  Cases_on `exec_block fuel ctx bb' (s with vs_inst_idx := q)` >>
  gvs[lift_result_def]
QED

Triviality exec_block_body_non_ok_lift:
  !bb bb' q fuel ctx s.
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) /\
    run_insts fuel ctx (block_body bb) s =
    run_insts fuel ctx (block_body bb') s /\
    ~(?v. run_insts fuel ctx (block_body bb) s = OK v) ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (exec_block fuel ctx bb (s with vs_inst_idx := q))
      (exec_block fuel ctx bb' (s with vs_inst_idx := q))
Proof
  rpt strip_tac >>
  qspecl_then [`bb`, `q`] mp_tac block_body_at_pseudo_end >>
  impl_tac >- simp[] >> strip_tac >>
  qspecl_then [`bb'`, `q`] mp_tac block_body_at_pseudo_end >>
  impl_tac >- simp[] >> strip_tac >>
  sg `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
        (run_insts fuel ctx (block_body bb') s)
        (exec_block fuel ctx bb (s with vs_inst_idx := q))` >-
    (qpat_x_assum `run_insts fuel ctx (block_body bb) s = _`
       (fn th => rewrite_tac[GSYM th]) >>
     irule exec_block_run_insts_lift >> simp[] >> rpt strip_tac >> gvs[]) >>
  sg `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
        (run_insts fuel ctx (block_body bb') s)
        (exec_block fuel ctx bb' (s with vs_inst_idx := q))` >-
    (irule exec_block_run_insts_lift >> simp[] >> rpt strip_tac >> gvs[]) >>
  qspecl_then [`run_insts fuel ctx (block_body bb') s`,
    `exec_block fuel ctx bb (s with vs_inst_idx := q)`,
    `exec_block fuel ctx bb' (s with vs_inst_idx := q)`]
    mp_tac lift_result_same_non_ok_trans >>
  simp[] >>
  rpt strip_tac >> gvs[]
QED

Triviality exec_block_same_body_lift:
  !fn bb bb' q fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) /\
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (MAP (choose_original (block_body bb)) (block_body bb')) ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (exec_block fuel ctx bb (s with vs_inst_idx := q))
      (exec_block fuel ctx bb' (s with vs_inst_idx := q))
Proof
  rpt strip_tac >>
  `LAST bb'.bb_instructions = LAST bb.bb_instructions` by
    metis_tac[block_perm_of_same_last] >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    metis_tac[block_perm_of_same_length] >>
  drule_all block_body_full_equiv >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] strip_assume_tac)
  >- (irule exec_block_body_error_lift >> simp[]) >>
  Cases_on `run_insts fuel ctx (block_body bb) s` >> fs[]
  >- (`exec_block fuel ctx bb (s with vs_inst_idx := q) =
       exec_block fuel ctx bb' (s with vs_inst_idx := q)` by
        (irule exec_block_same_body_ok >> simp[] >>
         qexists_tac `v` >> gvs[]) >>
      gvs[] >> irule (SRULE [] lift_result_refl_proof) >>
      simp[state_equiv_refl, execution_equiv_refl, revert_equiv_def]) >>
  irule exec_block_body_non_ok_lift >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Triviality exec_block_skip_pseudo_suffix_lift:
  !fn bb bb' p q fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    p = phi_prefix_length bb.bb_instructions /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (MAP (choose_original (block_body bb)) (block_body bb')) ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (exec_block fuel ctx bb (s with vs_inst_idx := p))
      (exec_block fuel ctx bb' (s with vs_inst_idx := p))
Proof
  rpt strip_tac >>
  qspecl_then [`fn`, `bb`, `bb'`] mp_tac block_perm_of_same_phi_prefix >>
  simp[] >> strip_tac >>
  `phi_prefix_length bb'.bb_instructions = p` by simp[] >>
  qspecl_then [`fn`, `bb`, `bb'`] mp_tac block_perm_of_same_pseudo_prefix >>
  simp[] >> strip_tac >>
  `LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions) = q` by simp[] >>
  `p <= q` by (
    qpat_x_assum `p = phi_prefix_length bb.bb_instructions` (fn th => rewrite_tac[th]) >>
    qpat_x_assum `q = LENGTH (FILTER _ bb.bb_instructions)` (fn th => rewrite_tac[th]) >>
    `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) =
     phi_prefix_length bb.bb_instructions` by
      (irule phi_prefix_length_filter_pseudo >> fs[bb_well_formed_def]) >>
    pop_assum (fn th => rewrite_tac[GSYM th]) >>
    simp[venomExecProofsTheory.phi_prefix_length_le]) >>
  qabbrev_tac `suffix = DROP p (TAKE q bb.bb_instructions)` >>
  `DROP p (TAKE q bb'.bb_instructions) =
   DROP p (TAKE q bb.bb_instructions)` by
    metis_tac[block_perm_of_same_pseudo_suffix] >>
  `DROP p (TAKE q bb'.bb_instructions) = suffix` by metis_tac[] >>
  Cases_on `run_insts fuel ctx suffix s`
  >- (
    rename1 `run_insts _ _ suffix _ = OK s_after` >>
    `exec_block fuel ctx bb (s with vs_inst_idx := p) =
     exec_block fuel ctx bb (s_after with vs_inst_idx := q)` by
      (irule exec_block_skip_pseudo_suffix >> simp[Abbr `suffix`]) >>
    `exec_block fuel ctx bb' (s with vs_inst_idx := p) =
     exec_block fuel ctx bb' (s_after with vs_inst_idx := q)` by
      (irule exec_block_skip_pseudo_suffix >> simp[] >>
       qexists_tac `s_after` >> simp[]) >>
    gvs[] >>
    irule exec_block_same_body_lift >> simp[] >> metis_tac[]) >>
  `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
        (run_insts fuel ctx suffix s)
        (exec_block fuel ctx bb (s with vs_inst_idx := p))` by
    (qunabbrev_tac `suffix` >> irule exec_block_run_insts_pseudo_suffix_lift >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
        (run_insts fuel ctx suffix s)
        (exec_block fuel ctx bb' (s with vs_inst_idx := p))` by
    (qpat_x_assum `DROP p (TAKE q bb'.bb_instructions) = suffix`
       (fn th => rewrite_tac[GSYM th]) >>
     irule exec_block_run_insts_pseudo_suffix_lift >> simp[] >> metis_tac[]) >>
  qspecl_then [`run_insts fuel ctx suffix s`,
    `exec_block fuel ctx bb (s with vs_inst_idx := p)`,
    `exec_block fuel ctx bb' (s with vs_inst_idx := p)`]
    mp_tac lift_result_same_non_ok_trans >>
  simp[] >> disch_then irule >> simp[]
QED

Triviality block_perm_of_run_block_lift:
  !fn bb bb' fuel ctx s.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\ block_perm_of fn bb' /\
    bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    pseudos_prefix bb /\ pseudos_prefix bb' /\
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (MAP (choose_original (block_body bb)) (block_body bb')) ==>
    (((?e. run_block fuel ctx bb s = Error e) /\
      (?e. run_block fuel ctx bb' s = Error e)) \/
     lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
       (run_block fuel ctx bb s)
       (run_block fuel ctx bb' s))
Proof
  rpt strip_tac >>
  drule_all block_perm_of_eval_phis_same >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`]
    eval_phis_ok_or_error_defs)
  >- (first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >>
      `eval_phis s bb'.bb_instructions = OK s_phi` by metis_tac[] >>
      disj2_tac >>
      ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
      irule (Q.SPECL [`fn`, `bb`, `bb'`,
        `phi_prefix_length bb.bb_instructions`,
        `LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)`,
        `fuel`, `ctx`, `s_phi`] exec_block_skip_pseudo_suffix_lift) >>
      simp[] >> metis_tac[]) >>
  first_x_assum (qx_choose_then `e` strip_assume_tac) >>
  `eval_phis s bb'.bb_instructions = Error e` by metis_tac[] >>
  disj1_tac >>
  ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
  metis_tac[]
QED

(* For each instruction in FRONT bb', there's an instruction in FRONT bb
   with the same inst_id and same step_inst behavior *)
Triviality front_mem_step_equiv:
  !fn bb bb' i.
    wf_function fn /\ MEM bb fn.fn_blocks /\
    block_perm_of fn bb' /\ bb.bb_label = bb'.bb_label /\
    bb_well_formed bb /\ bb_well_formed bb' /\
    MEM i (FRONT bb'.bb_instructions) ==>
    ?j. MEM j (FRONT bb.bb_instructions) /\ j.inst_id = i.inst_id /\
        !fuel ctx s. step_inst fuel ctx i s = step_inst fuel ctx j s
Proof
  rpt strip_tac >>
  fs[block_perm_of_def] >>
  rename1 `MEM bb_orig fn.fn_blocks` >>
  `bb_orig = bb` by (irule wf_fn_same_label_eq >> metis_tac[]) >> gvs[] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `bb'.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `~is_terminator i.inst_opcode` by
    (drule_at (Pos last) front_no_terminators >> simp[EVERY_MEM]) >>
  `is_terminator (LAST bb.bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  `MEM i bb'.bb_instructions` by metis_tac[MEM_FRONT_NOT_NIL] >>
  Cases_on `is_pseudo i.inst_opcode`
  >- (
    qexists `i` >> simp[] >>
    `MEM i (FILTER (\i'. is_pseudo i'.inst_opcode) bb'.bb_instructions)` by
      simp[MEM_FILTER] >>
    `MEM i (FILTER (\i'. is_pseudo i'.inst_opcode) bb.bb_instructions)` by
      metis_tac[] >>
    fs[MEM_FILTER] >>
    `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]`
      by simp[APPEND_FRONT_LAST] >>
    `MEM i (FRONT bb.bb_instructions) \/ i = LAST bb.bb_instructions`
      by metis_tac[MEM_APPEND, MEM] >>
    gvs[])
  >>
  `from_block bb.bb_instructions i` by
    (qpat_x_assum `EVERY _ (FILTER _ _)` mp_tac >>
     simp[EVERY_MEM, MEM_FILTER]) >>
  gvs[from_block_def]
  >- (
    (* Identity case: i = j *)
    rename1 `MEM j bb.bb_instructions` >>
    qexists `j` >> simp[] >>
    `bb.bb_instructions = FRONT bb.bb_instructions ++ [LAST bb.bb_instructions]`
      by simp[APPEND_FRONT_LAST] >>
    `MEM j (FRONT bb.bb_instructions) \/ j = LAST bb.bb_instructions`
      by metis_tac[MEM_APPEND, MEM] >>
    gvs[])
  >>
  (* Flip case: i = flip_operands j *)
  rename1 `MEM j bb.bb_instructions` >>
  qexists `j` >> simp[flip_operands_inst_id] >>
  conj_tac
  >- (`~is_terminator j.inst_opcode` by gvs[flip_operands_is_terminator] >>
      `bb.bb_instructions = FRONT bb.bb_instructions ++
                            [LAST bb.bb_instructions]`
        by simp[APPEND_FRONT_LAST] >>
      `MEM j (FRONT bb.bb_instructions) \/ j = LAST bb.bb_instructions`
        by metis_tac[MEM_APPEND, MEM] >>
      gvs[])
  >>
  rpt strip_tac >> metis_tac[flip_operands_step_inst]
QED

(* Pseudo OK result is always update_var with one output. *)
Triviality pseudo_step_is_update_var:
  !fuel ctx a s sa.
    is_pseudo a.inst_opcode /\
    step_inst fuel ctx a s = OK sa ==>
    ?out val. a.inst_outputs = [out] /\ sa = update_var out val s
Proof
  rpt strip_tac >>
  `a.inst_opcode <> INVOKE` by
    (Cases_on `a.inst_opcode` >> gvs[is_pseudo_def]) >>
  gvs[step_inst_non_invoke] >>
  Cases_on `a.inst_opcode` >> gvs[is_pseudo_def]
  >- gvs[Once step_inst_base_def]
  >- (gvs[Once step_inst_base_def] >> gvs[AllCaseEqs()] >> metis_tac[])
  >- (gvs[Once step_inst_base_def] >> gvs[AllCaseEqs()] >> metis_tac[])
  >- (gvs[Once step_inst_base_def] >> gvs[AllCaseEqs()] >> metis_tac[])
QED

(* Pseudo swap: if pseudo a is data-independent from b, and a->b both OK,
   then b->a both OK with same result. Uses step_inst_ok_frame (works for
   all opcodes including ALLOCA/INVOKE). *)
Triviality step_swap_ok_pseudo:
  !fuel ctx a b s sa sab.
    is_pseudo a.inst_opcode /\
    ~is_terminator b.inst_opcode /\
    DISJOINT (set (inst_defs a)) (set (inst_uses b)) /\
    DISJOINT (set (inst_defs b)) (set (inst_uses a)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b)) /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rpt strip_tac >>
  (* Step 1: sa = update_var out val s *)
  drule_all pseudo_step_is_update_var >> strip_tac >> gvs[] >>
  rename1 `update_var out val s` >>
  (* Step 2: frame — b commutes past update_var *)
  `!y. MEM (Var y) b.inst_operands ==> out <> y` by
    (gvs[inst_defs_def, inst_uses_def,
         DISJOINT_DEF, EXTENSION] >>
     metis_tac[mem_var_operand_vars, MEM]) >>
  `~MEM out b.inst_outputs` by
    (gvs[inst_defs_def, DISJOINT_DEF, EXTENSION]) >>
  (* Use step_inst_frame (equality) for non-INVOKE, step_inst_invoke_frame for INVOKE *)
  `?sb. step_inst fuel ctx b s = OK sb /\
        sab = update_var out val sb` by
    (Cases_on `b.inst_opcode = INVOKE`
     >- (qspecl_then [`fuel`,`ctx`,`b`,`s`,`out`,`val`] mp_tac
           dftCommutationTheory.step_inst_invoke_frame >> simp[] >>
         strip_tac >> gvs[] >>
         Cases_on `step_inst fuel ctx b s` >> gvs[])
     >> (qspecl_then [`fuel`,`ctx`,`b`,`s`,`out`,`val`] mp_tac
           dftCommutationTheory.step_inst_frame >> simp[] >>
         strip_tac >> gvs[dftCommutationTheory.map_result_state_def] >>
         Cases_on `step_inst fuel ctx b s` >>
         gvs[dftCommutationTheory.map_result_state_def])) >>
  qexists `sb` >> simp[] >>
  (* Step 3: a on sb produces same update_var *)
  (* Field preservation from step b *)
  `sb.vs_labels = s.vs_labels` by
    metis_tac[step_preserves_labels] >>
  (* Operands of a evaluate the same on s and sb *)
  `sb.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[step_preserves_control_flow] >>
  `sb.vs_params = s.vs_params` by metis_tac[step_preserves_params] >>
  `sb.vs_return_pc_token = s.vs_return_pc_token` by
    (Cases_on `b.inst_opcode = INVOKE`
     >- metis_tac[invoke_preserves_structural]
     >> `step_inst_base b s = OK sb` by gvs[step_inst_non_invoke] >>
        drule venomInstProofs1Theory.step_inst_base_preserves_all >> simp[]) >>
  `!v. ~MEM v b.inst_outputs ==>
       lookup_var v sb = lookup_var v s` by
    metis_tac[step_preserves_non_output_vars] >>
  (* Step 3: replay pseudo a on sb *)
  `a.inst_opcode <> INVOKE` by
    (Cases_on `a.inst_opcode` >> gvs[is_pseudo_def]) >>
  `step_inst_base a s = OK (update_var out val s)` by
    gvs[step_inst_non_invoke] >>
  (* Show operands of a evaluate the same on sb and s *)
  `!op. MEM op a.inst_operands ==>
        eval_operand op sb = eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def]
     >- (rename1 `Var vv` >> first_x_assum irule >>
         gvs[inst_defs_def, inst_uses_def,
             DISJOINT_DEF, EXTENSION] >>
         metis_tac[mem_var_operand_vars, MEM])
     >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  Cases_on `a.inst_opcode` >> gvs[is_pseudo_def]
  (* PHI case *)
  >- (gvs[Once step_inst_base_def, AllCaseEqs()] >>
      (* Derive val from eval_operand: v = val *)
      `v = val` by
        gvs[update_var_def, venom_state_component_equality,
            FUPD11_SAME_KEY_AND_BASE] >>
      gvs[] >>
      ONCE_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      imp_res_tac dftCommutationTheory.resolve_phi_MEM >>
      first_x_assum drule >> simp[])
  (* PARAM case *)
  >- (gvs[Once step_inst_base_def, AllCaseEqs()] >>
      `EL (w2n idx) s.vs_params = val` by
        (fs[update_var_def, venom_state_component_equality] >>
         metis_tac[FUPD11_SAME_KEY_AND_BASE]) >>
      ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[])
  (* FMP_PARAM case *)
  >- (gvs[Once step_inst_base_def, AllCaseEqs()] >>
      `EL (w2n idx) s.vs_params = val` by
        (fs[update_var_def, venom_state_component_equality] >>
         metis_tac[FUPD11_SAME_KEY_AND_BASE]) >>
      ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[])
  (* RETPC_PARAM case *)
  >> (gvs[Once step_inst_base_def, AllCaseEqs()] >>
      `s.vs_return_pc_token = val` by
        (fs[update_var_def, venom_state_component_equality] >>
         metis_tac[FUPD11_SAME_KEY_AND_BASE]) >>
      ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[])
QED

(* Reverse direction of step_swap_ok_pseudo: given b (non-term) THEN a (pseudo)
   both OK, then a THEN b both OK with same result. *)
Triviality step_swap_ok_pseudo_rev:
  !fuel ctx a b s sb sba.
    is_pseudo a.inst_opcode /\
    ~is_terminator b.inst_opcode /\
    DISJOINT (set (inst_defs a)) (set (inst_uses b)) /\
    DISJOINT (set (inst_defs b)) (set (inst_uses a)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b)) /\
    step_inst fuel ctx b s = OK sb /\
    step_inst fuel ctx a sb = OK sba ==>
    ?sa. step_inst fuel ctx a s = OK sa /\
         step_inst fuel ctx b sa = OK sba
Proof
  rpt strip_tac >>
  (* Step 1: sba = update_var out val sb *)
  drule_all pseudo_step_is_update_var >>
  strip_tac >> rename1 `update_var out val sb` >>
  (* Step 2: data independence *)
  `~MEM out b.inst_outputs` by
    (fs[inst_defs_def, DISJOINT_DEF, EXTENSION, MEM_MAP] >>
     metis_tac[MEM]) >>
  `!y. MEM (Var y) b.inst_operands ==> out <> y` by
    (fs[inst_defs_def, inst_uses_def, DISJOINT_DEF, EXTENSION] >>
     metis_tac[mem_var_operand_vars, MEM]) >>
  (* Step 3: frame — step b on (update_var out val s) *)
  `step_inst fuel ctx b (update_var out val s) =
   OK (update_var out val sb)` by
    (irule dftCommutationTheory.step_inst_ok_frame >> metis_tac[]) >>
  (* Step 4: replay pseudo a on s *)
  `a.inst_opcode <> INVOKE` by
    (Cases_on `a.inst_opcode` >> gvs[is_pseudo_def]) >>
  (* Operands of a evaluate the same on s and sb *)
  `sb.vs_prev_bb = s.vs_prev_bb` by
    metis_tac[step_preserves_control_flow] >>
  `sb.vs_params = s.vs_params` by
    metis_tac[step_preserves_params] >>
  `sb.vs_labels = s.vs_labels` by
    metis_tac[step_preserves_labels] >>
  `sb.vs_return_pc_token = s.vs_return_pc_token` by
    (Cases_on `b.inst_opcode = INVOKE`
     >- metis_tac[invoke_preserves_structural]
     >> `step_inst_base b s = OK sb` by gvs[step_inst_non_invoke] >>
        drule venomInstProofs1Theory.step_inst_base_preserves_all >> simp[]) >>
  `!v. ~MEM v b.inst_outputs ==>
       lookup_var v sb = lookup_var v s` by
    metis_tac[step_preserves_non_output_vars] >>
  `!op. MEM op a.inst_operands ==>
        eval_operand op sb = eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >>
     simp[eval_operand_def] >>
     (* Only Var case remains *)
     rename1 `MEM (Var vn) _` >>
     `~MEM vn b.inst_outputs` by
       (fs[inst_defs_def, inst_uses_def,
           DISJOINT_DEF, EXTENSION] >>
        metis_tac[mem_var_operand_vars, MEM]) >>
     metis_tac[]) >>
  (* Now replay each executable pseudo opcode explicitly. *)
  fs[step_inst_non_invoke] >>
  Cases_on `a.inst_opcode` >> gvs[is_pseudo_def]
  (* PHI is impossible under final semantics. *)
  >- gvs[Once step_inst_base_def, AllCaseEqs()]
  (* PARAM case *)
  >- (gvs[Once step_inst_base_def, AllCaseEqs()] >>
      `EL (w2n idx) s.vs_params = val` by
        (fs[update_var_def, venom_state_component_equality] >>
         metis_tac[FUPD11_SAME_KEY_AND_BASE]) >>
      qexists `update_var out val s` >>
      conj_tac
      >- (ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[]) >>
      fs[])
  (* FMP_PARAM case *)
  >- (gvs[Once step_inst_base_def, AllCaseEqs()] >>
      `EL (w2n idx) s.vs_params = val` by
        (fs[update_var_def, venom_state_component_equality] >>
         metis_tac[FUPD11_SAME_KEY_AND_BASE]) >>
      qexists `update_var out val s` >>
      conj_tac
      >- (ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[]) >>
      fs[])
  (* RETPC_PARAM case *)
  >> (gvs[Once step_inst_base_def, AllCaseEqs()] >>
      `sb.vs_return_pc_token = val` by
        (fs[update_var_def, venom_state_component_equality] >>
         metis_tac[FUPD11_SAME_KEY_AND_BASE]) >>
      qexists `update_var out val s` >>
      conj_tac
      >- (ONCE_REWRITE_TAC[step_inst_base_def] >> gvs[]) >>
      fs[])
QED

(* Non-terminator non-INVOKE: can't produce Halt or IntRet from step_inst *)
Triviality non_term_non_invoke_not_halt_intret:
  !fuel ctx inst s.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    (!v. step_inst fuel ctx inst s <> Halt v) /\
    (!vals v. step_inst fuel ctx inst s <> IntRet vals v)
Proof
  rpt strip_tac >> gvs[step_inst_non_invoke] >>
  metis_tac[step_inst_base_not_halt_intret]
QED

(* Deriving frame conditions from inst_defs/inst_uses DISJOINT *)
Triviality frame_conds_from_disjoint:
  !h p.
    DISJOINT (set (inst_defs p)) (set (inst_uses h)) /\
    DISJOINT (set (inst_defs h)) (set (inst_defs p)) ==>
    !out. MEM out p.inst_outputs ==>
      (!y. MEM (Var y) h.inst_operands ==> out <> y) /\
      ~MEM out h.inst_outputs
Proof
  rw[inst_defs_def, inst_uses_def] >>
  fs[DISJOINT_DEF, EXTENSION, MEM_operand_vars_iff] >>
  metis_tac[]
QED

(* Key single-swap: h (non-pseudo, non-term) past p (pseudo).
   p always gives OK (update_var). On the p-first side, h runs on
   update_var state. Frame relates this to h on original state.
   OK-OK: step_swap_ok_pseudo_rev commutes. Non-OK h:
   INVOKE → non-OK unchanged. Non-INVOKE → map_result_state preserves
   revert_equiv (update_var preserves vs_returndata). *)
(* Frame property for run_insts over a list of pseudos:
   update_var x v commutes through a sequence of pseudo instructions,
   provided x is not read or written by any pseudo in the list.
   Non-INVOKE follows from step_inst_frame; pseudos are never INVOKE. *)
Triviality run_insts_pseudo_frame:
  !ps fuel ctx s x v.
    EVERY (\i. is_pseudo i.inst_opcode) ps /\
    (!p. MEM p ps ==>
         ~MEM x p.inst_outputs /\
         !y. MEM (Var y) p.inst_operands ==> x <> y) ==>
    run_insts fuel ctx ps (update_var x v s) =
    map_result_state (update_var x v) (run_insts fuel ctx ps s)
Proof
  Induct >> simp[run_insts_def, dftCommutationTheory.map_result_state_def] >>
  rpt strip_tac >>
  `h.inst_opcode <> INVOKE` by
    (fs[EVERY_MEM] >> Cases_on `h.inst_opcode` >>
     gvs[is_pseudo_def]) >>
  `step_inst fuel ctx h (update_var x v s) =
   map_result_state (update_var x v) (step_inst fuel ctx h s)` by
    (irule dftCommutationTheory.step_inst_frame >> fs[EVERY_MEM]) >>
  Cases_on `step_inst fuel ctx h s` >>
  gvs[dftCommutationTheory.map_result_state_def, run_insts_def] >>
  first_x_assum irule >> fs[EVERY_MEM]
QED

Theorem lift_result_refl:
  !x. lift_result (state_equiv {}) (execution_equiv {}) revert_equiv x x
Proof
  Cases >> simp[lift_result_def, state_equiv_refl, execution_equiv_refl,
                revert_equiv_def]
QED

(* Key single-swap: h (non-pseudo, non-term) past p (pseudo).
   Assumes p succeeds on s. *)
Triviality swap_nonpseudo_pseudo_lr:
  !fuel ctx h p rest s out val'.
    ~is_terminator h.inst_opcode /\ ~is_pseudo h.inst_opcode /\
    is_pseudo p.inst_opcode /\
    DISJOINT (set (inst_defs h)) (set (inst_defs p)) /\
    DISJOINT (set (inst_defs h)) (set (inst_uses p)) /\
    DISJOINT (set (inst_defs p)) (set (inst_uses h)) /\
    step_inst fuel ctx p s = OK (update_var out val' s) /\
    MEM out p.inst_outputs ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_insts fuel ctx (h :: p :: rest) s)
      (run_insts fuel ctx (p :: h :: rest) s)
Proof
  rpt strip_tac >>
  simp[run_insts_def] >>
  qspecl_then [`h`,`p`] mp_tac frame_conds_from_disjoint >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `out` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `step_inst fuel ctx h s`
  >- (
    rename1 `OK s1` >> simp[] >>
    drule_all dftCommutationTheory.step_inst_ok_frame >>
    disch_then (qspec_then `val'` assume_tac) >>
    simp[] >>
    (* Now apply step_swap_ok_pseudo to get step_inst p s1 *)
    qspecl_then [`fuel`,`ctx`,`p`,`h`,`s`,`update_var out val' s`,
                  `update_var out val' s1`]
      mp_tac step_swap_ok_pseudo >>
    impl_tac
    >- (fs[] >> once_rewrite_tac[DISJOINT_SYM] >> fs[]) >>
    strip_tac >> gvs[] >> simp[] >>
    MATCH_ACCEPT_TAC lift_result_refl
  )
  (* Non-OK: split INVOKE vs non-INVOKE *)
  >> (
    Cases_on `h.inst_opcode = INVOKE`
    >- (
      qspecl_then [`fuel`,`ctx`,`h`,`s`,`out`,`val'`] mp_tac
        dftCommutationTheory.step_inst_invoke_frame >>
      impl_tac >- fs[] >> strip_tac >>
      (* Invoke frame: non-OK result unchanged *)
      gvs[lift_result_def, execution_equiv_def, revert_equiv_def]
    )
    >> (
      qspecl_then [`fuel`,`ctx`,`h`,`s`,`out`,`val'`] mp_tac
        dftCommutationTheory.step_inst_frame >>
      impl_tac >- fs[] >> strip_tac >>
      gvs[dftCommutationTheory.map_result_state_def] >>
      TRY (qspecl_then [`fuel`,`ctx`,`h`,`s`] mp_tac
             non_term_non_invoke_not_halt_intret >> simp[] >> NO_TAC) >>
      simp[lift_result_def, revert_equiv_def,
           dftCommutationTheory.update_var_fields]
    )
  )
QED

(* lift_result lifted through a common prefix step:
   if for all s', A s' ≡_lr B s', then step;A ≡_lr step;B *)
Triviality lift_result_step_prefix:
  !fuel ctx inst s rest1 rest2.
    (!s'. lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
            (run_insts fuel ctx rest1 s')
            (run_insts fuel ctx rest2 s')) ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_insts fuel ctx (inst :: rest1) s)
      (run_insts fuel ctx (inst :: rest2) s)
Proof
  rpt strip_tac >>
  simp[run_insts_def] >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  MATCH_ACCEPT_TAC lift_result_refl
QED


(* Original blocks satisfy block_perm_of *)
Theorem original_block_perm_of:
  !fn bb. MEM bb fn.fn_blocks ==> block_perm_of fn bb
Proof
  rpt strip_tac >> simp[block_perm_of_def] >>
  qexists_tac `bb` >> simp[from_block_def] >>
  simp[EVERY_FILTER, EVERY_MEM] >> rpt strip_tac >>
  qexists_tac `i` >> simp[]
QED

(* from_block preserves inst_id *)
Triviality from_block_inst_id:
  !bi i. from_block bi i ==> ?j. MEM j bi /\ i.inst_id = j.inst_id
Proof
  rw[from_block_def] >> metis_tac[flip_operands_inst_id]
QED

(* dft_block produces a PERM of inst_ids of non-pseudo instructions *)
Theorem dft_block_perm_ids:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    PERM (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode)
               (dft_block order bb).bb_instructions))
         (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))
Proof
  rpt strip_tac >>
  simp[dft_block_def, LET_THM] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  qabbrev_tac `om = build_offspring_map bi order` >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `sched = schedule_from_entries bi order eda om entries` >>
  (* Standard preamble *)
  `eda_wf eda bi` by simp[Abbr `eda`, build_full_eda_wf] >>
  `eda_topo_compatible bi eda order` by
    (simp[Abbr `eda`] >>
     qspecl_then [`bi`, `order`] mp_tac eda_topo_compatible_gen_weak >>
     simp[] >> disch_then irule >>
     fs[bb_well_formed_def, non_pseudo_defs_before_uses_def, Abbr `bi`]) >>
  `bi <> []` by fs[bb_well_formed_def, Abbr `bi`] >>
  `np_defs_before_uses bi` by
    gvs[non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `EVERY (\i. MEM i bi) entries` by
    simp[Abbr `entries`, Abbr `bi`, entry_instructions_mem] >>
  `!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)` by fs[bb_well_formed_def, Abbr `bi`] >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) sched` by
    (simp[EVERY_MEM, Abbr `sched`] >> rpt strip_tac >>
     metis_tac[schedule_output_from_block]) >>
  `ALL_DISTINCT (MAP (\j. j.inst_id) sched)` by
    (simp[Abbr `sched`] >>
     irule schedule_output_all_distinct >> simp[Abbr `entries`]) >>
  (* non-pseudo of (phis ++ sched) = sched *)
  `FILTER (\i. ~is_pseudo i.inst_opcode)
     (FILTER (\i. is_pseudo i.inst_opcode) bi ++ sched) = sched` by
    (once_rewrite_tac[FILTER_APPEND_DISTRIB] >>
     (`FILTER (\i. ~is_pseudo i.inst_opcode)
         (FILTER (\i. is_pseudo i.inst_opcode) bi) = []` by
        simp[FILTER_EQ_NIL, EVERY_MEM, MEM_FILTER]) >>
     simp[FILTER_EQ_ID]) >>
  simp[] >>
  MATCH_MP_TAC PERM_ALL_DISTINCT >>
  conj_tac >- simp[] >>
  conj_tac
  >- (irule dftPipelineInvarTheory.all_distinct_map_filter >> simp[]) >>
  rpt strip_tac >> eq_tac >> strip_tac
  (* → : from sched to bb — via from_block *)
  >- (gvs[MEM_MAP, MEM_FILTER] >>
      rename1 `MEM j sched` >>
      `from_block bi j` by
        (qspecl_then [`bi`,`order`,`eda`,`om`,`entries`,`j`]
           mp_tac (cj 1 schedule_output_from_block) >>
         simp[Abbr `sched`]) >>
      gvs[from_block_def] >>
      simp[MEM_MAP, MEM_FILTER, flip_operands_inst_id] >>
      metis_tac[])
  (* ← : from bb to sched — completeness *)
  >> (gvs[MEM_MAP, MEM_FILTER] >>
      `MEM i.inst_id (MAP (\j. j.inst_id) sched)` by
        (qspecl_then [`bi`,`order`,`eda`,`om`] mp_tac
           schedule_output_complete >>
         simp[Abbr `sched`, Abbr `entries`] >>
         disch_then (qspec_then `i` mp_tac) >> simp[Abbr `bi`]) >>
      gvs[MEM_MAP] >>
      metis_tac[])
QED

(* dft_block preserves block_perm_of, given dft_inv conditions *)
Theorem dft_block_preserves_perm_of:
  !order fn bb.
    block_perm_of fn bb /\
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    block_perm_of fn (dft_block order bb)
Proof
  rw[block_perm_of_def] >>
  qexists_tac `bb_orig` >> simp[dft_block_phis] >>
  conj_tac
  (* from_block transitivity *)
  >- (fs[EVERY_MEM, listTheory.MEM_FILTER] >> rpt strip_tac >>
      `from_block bb.bb_instructions i` by
        (mp_tac (Q.SPECL [`order`, `bb`, `i`] dft_block_from_orig) >>
         simp[listTheory.MEM_FILTER]) >>
      irule from_block_trans >> qexists_tac `bb.bb_instructions` >> simp[])
  (* PERM: PERM_TRANS through bb *)
  >> irule PERM_TRANS >>
  qexists_tac `MAP (\i. i.inst_id)
                 (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` >>
  simp[dft_block_perm_ids]
QED


(* ===== dft_fn preserves bb_well_formed ===== *)

(* dft_block preserves bb_well_formed: terminator stays at end,
   phis stay as prefix, non-empty *)
(* dft_block preserves bb_well_formed when terminator isn't a dep target.
   wf_ssa ensures terminators have empty outputs (via def_dominates_uses),
   hence no instruction within the block depends on them. *)
(*  Helper: terminator is an entry instruction (has no dependents) *)
Triviality terminator_is_entry:
  !bi order eda.
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\ ~is_pseudo (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    MEM (LAST bi) (entry_instructions bi order eda)
Proof
  rpt strip_tac >>
  simp[entry_instructions_def, LET_THM, MEM_FILTER] >>
  conj_tac
  (* LAST bi's inst_id is not in any dep list *)
  >- (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      rpt strip_tac >> rename1 `MEM instr (FILTER _ bi)` >>
      qspecl_then [`bi`, `eda`, `order`, `instr`] mp_tac
        terminator_not_dep_target >>
      gvs[MEM_FILTER, MEM_MAP] >> metis_tac[])
  (* LAST bi is in bi *)
  >> imp_res_tac (DB.fetch "rich_list" "MEM_LAST_NOT_NIL")
QED

(* Helper: terminator is last among entries (FILTER preserves order) *)
Triviality filter_last_when_last_passes:
  !P l. l <> [] /\ P (LAST l) ==> FILTER P l <> [] /\ LAST (FILTER P l) = LAST l
Proof
  gen_tac >> Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `l = []`
  >- (gvs[LAST_DEF] >> simp[FILTER])
  >> (gvs[LAST_DEF] >>
      `FILTER P l <> [] /\ LAST (FILTER P l) = LAST l` by simp[] >>
      Cases_on `P h` >> gvs[FILTER, LAST_DEF])
QED

Triviality terminator_last_entry:
  !bi order eda.
    eda_wf eda bi /\
    eda_topo_compatible bi eda order /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\ ~is_pseudo (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    let entries = entry_instructions bi order eda in
    entries <> [] /\ LAST entries = LAST bi
Proof
  rpt strip_tac >> simp[LET_THM] >>
  `MEM (LAST bi) (entry_instructions bi order eda)` by
    (irule terminator_is_entry >> simp[]) >>
  simp[entry_instructions_def, LET_THM] >>
  qabbrev_tac `nps = FILTER (\i. ~is_pseudo i.inst_opcode) bi` >>
  (* Establish: nps <> [] /\ LAST nps = LAST bi *)
  `nps <> [] /\ LAST nps = LAST bi` by
    (simp[Abbr `nps`] >> irule filter_last_when_last_passes >> simp[]) >>
  (* Establish: LAST bi passes the dep filter *)
  `~MEM (LAST bi).inst_id
     (FLAT (MAP (\i. MAP (\d. d.inst_id) (inst_all_deps bi order eda i)) nps))` by
    (simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >> rpt strip_tac >>
     rename1 `MEM instr nps` >>
     qspecl_then [`bi`, `eda`, `order`, `instr`] mp_tac terminator_not_dep_target >>
     gvs[Abbr `nps`, MEM_FILTER, MEM_MAP] >> metis_tac[]) >>
  (* Now apply filter_last_when_last_passes *)
  qabbrev_tac `Q = \i:instruction. ~MEM i.inst_id
     (FLAT (MAP (\i. MAP (\d. d.inst_id) (inst_all_deps bi order eda i)) nps))` >>
  `Q (LAST nps)` by simp[Abbr `Q`] >>
  drule_all filter_last_when_last_passes >>
  simp[Abbr `Q`]
QED

(* Helper: ALL_DISTINCT preserved by MAP over FILTER *)
Theorem all_distinct_map_filter:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
  gen_tac >> gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  rw[] >> gvs[MEM_MAP, MEM_FILTER]
QED

(* Helper: terminator id not in FRONT entries' process stack *)
Triviality id_not_in_map_process:
  !l tid.
    id_not_in_stack tid (MAP DfsProcess l) <=>
    ~MEM tid (MAP (\i. i.inst_id) l)
Proof
  Induct >> simp[id_not_in_stack_def] >> metis_tac[]
QED

Triviality terminator_not_in_front_entries:
  !bi order eda.
    eda_wf eda bi /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\ ~is_pseudo (LAST bi).inst_opcode /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    let entries = entry_instructions bi order eda in
    entries <> [] ==>
    LAST entries = LAST bi ==>
    id_not_in_stack (LAST bi).inst_id (MAP DfsProcess (FRONT entries))
Proof
  rpt strip_tac >> simp[LET_THM] >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  rpt strip_tac >>
  (* entries is FILTER of FILTER of bi, so ALL_DISTINCT (MAP inst_id entries) *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) entries)` by
    (simp[Abbr `entries`, entry_instructions_def, LET_THM] >>
     irule all_distinct_map_filter >> irule all_distinct_map_filter >> simp[]) >>
  (* Use MEM_FRONT_NOT_LAST on MAP inst_id entries *)
  `~MEM (LAST entries).inst_id
        (MAP (\i. i.inst_id) (FRONT entries))` by
    (qspecl_then [`MAP (\i. i.inst_id) entries`] mp_tac
       (DB.fetch "rich_list" "MEM_FRONT_NOT_LAST") >>
     simp[LAST_MAP, MAP_FRONT]) >>
  gvs[] >>
  simp[id_not_in_map_process]
QED

(* If from_block bi i and i.inst_id matches some unique element j,
   then i = j or i = flip_operands j *)
Triviality from_block_id_unique:
  !bi i j.
    from_block bi i /\ MEM j bi /\ ~is_pseudo j.inst_opcode /\
    i.inst_id = j.inst_id /\ ALL_DISTINCT (MAP (\x. x.inst_id) bi) ==>
    i = j \/ i = flip_operands j
Proof
  rw[from_block_def] >> gvs[flip_operands_inst_id] >>
  gvs[MEM_EL] >>
  `n = n'` by
    (`fEL (MAP (\x. x.inst_id) bi) n = fEL (MAP (\x. x.inst_id) bi) n'` by
       simp[EL_MAP] >>
     metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP]) >>
  gvs[]
QED

Triviality from_block_terminator_id:
  !bi i.
    from_block bi i /\ is_terminator i.inst_opcode /\
    bi <> [] /\
    ALL_DISTINCT (MAP (\x. x.inst_id) bi) /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
         k = PRE (LENGTH bi)) ==>
    i.inst_id = (LAST bi).inst_id
Proof
  rpt strip_tac >>
  fs[from_block_def] >> (
    (* Both subgoals: i = j or i = flip_operands j, MEM j bi, ¬is_pseudo j.
       In the i=j case: is_terminator i = is_terminator j, direct.
       In the flip case: is_terminator (flip_operands j) = is_terminator j.
       Either way j is a terminator, hence j = LAST bi. *)
    `is_terminator j.inst_opcode` by gvs[flip_operands_is_terminator] >>
    `?n. n < LENGTH bi /\ EL n bi = j` by metis_tac[MEM_EL] >>
    `n = PRE (LENGTH bi)` by metis_tac[] >>
    `j = LAST bi` by
      (simp[LAST_EL] >> `0 < LENGTH bi` by (Cases_on `bi` >> gvs[]) >> gvs[]) >>
    gvs[flip_operands_inst_id])
QED

Triviality dft_block_wf_unique_terminator:
  !bi phis sched.
    phis = FILTER (\i. is_pseudo i.inst_opcode) bi /\
    bi <> [] /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)) /\
    sched <> [] /\
    (LAST sched).inst_id = (LAST bi).inst_id /\
    (!i. MEM i sched ==> from_block bi i /\ ~is_pseudo i.inst_opcode) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) sched) ==>
    !i. i < LENGTH phis + LENGTH sched /\
        is_terminator (EL i (phis ++ sched)).inst_opcode ==>
        i = PRE (LENGTH phis + LENGTH sched)
Proof
  rpt strip_tac >>
  qpat_x_assum `phis = FILTER (\i. is_pseudo i.inst_opcode) bi` SUBST_ALL_TAC >>
  Cases_on `i < LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bi)` >> gvs[]
  >- (`is_terminator (EL i (FILTER (\i. is_pseudo i.inst_opcode) bi)).inst_opcode` by
        gvs[EL_APPEND1] >>
      `MEM (EL i (FILTER (\i. is_pseudo i.inst_opcode) bi))
         (FILTER (\i. is_pseudo i.inst_opcode) bi)` by metis_tac[MEM_EL] >>
      `is_pseudo (EL i (FILTER (\i. is_pseudo i.inst_opcode) bi)).inst_opcode` by
        gvs[MEM_FILTER] >>
      metis_tac[terminator_not_pseudo_not_flippable]) >>
  `i - LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bi) < LENGTH sched` by simp[] >>
  `is_terminator
     (EL (i - LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bi)) sched).inst_opcode` by
    gvs[EL_APPEND2] >>
  qabbrev_tac `k = i - LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bi)` >>
  `MEM (EL k sched) sched` by metis_tac[MEM_EL] >>
  `from_block bi (EL k sched)` by metis_tac[] >>
  `(EL k sched).inst_id = (LAST bi).inst_id` by
    (irule from_block_terminator_id >> simp[] >> metis_tac[]) >>
  `0 < LENGTH sched` by (Cases_on `sched` >> gvs[]) >>
  `PRE (LENGTH sched) < LENGTH sched` by simp[] >>
  `EL k (MAP (\x. x.inst_id) sched) =
   EL (PRE (LENGTH sched)) (MAP (\x. x.inst_id) sched)` by
    (simp[EL_MAP] >> gvs[LAST_EL]) >>
  `k = PRE (LENGTH sched)` by
    (qspecl_then [`MAP (\x. x.inst_id) sched`, `k`, `PRE (LENGTH sched)`]
      mp_tac ALL_DISTINCT_EL_IMP >> simp[]) >>
  gvs[Abbr `k`]
QED

(* Generalized: dft_block preserves invariant triple.
   No dependency on fn or MEM bb fn.fn_blocks. *)
Theorem dft_block_well_formed_gen:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    bb_well_formed (dft_block order bb) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (dft_block order bb).bb_instructions) /\
    non_pseudo_defs_before_uses (dft_block order bb).bb_instructions
Proof
  rpt strip_tac >>
  simp[dft_block_def, LET_THM] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `phis = FILTER (\i. is_pseudo i.inst_opcode) bi` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  qabbrev_tac `om = build_offspring_map bi order` >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `sched = schedule_from_entries bi order eda om entries` >>
  (* Prerequisites — shared preamble *)
  `eda_wf eda bi` by simp[Abbr `eda`, build_full_eda_wf] >>
  `eda_topo_compatible bi eda order` by
    (simp[Abbr `eda`] >>
     qspecl_then [`bi`, `order`] mp_tac eda_topo_compatible_gen_weak >>
     simp[non_pseudo_defs_before_uses_def] >> disch_then irule >>
     fs[bb_well_formed_def, non_pseudo_defs_before_uses_def, Abbr `bi`]) >>
  `bi <> []` by (fs[bb_well_formed_def, Abbr `bi`]) >>
  `is_terminator (LAST bi).inst_opcode` by
    fs[bb_well_formed_def, Abbr `bi`] >>
  `~is_pseudo (LAST bi).inst_opcode` by
    (drule terminator_not_pseudo_not_flippable >> simp[]) >>
  `!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)` by
    fs[bb_well_formed_def, Abbr `bi`] >>
  `entries <> [] /\ LAST entries = LAST bi` by
    (mp_tac (Q.SPECL [`bi`, `order`, `eda`] terminator_last_entry) >>
     simp[LET_THM, Abbr `entries`]) >>
  `id_not_in_stack (LAST bi).inst_id (MAP DfsProcess (FRONT entries))` by
    (mp_tac (Q.SPECL [`bi`, `order`, `eda`] terminator_not_in_front_entries) >>
     simp[LET_THM, Abbr `entries`]) >>
  `!i'. MEM i' bi /\ ~is_pseudo i'.inst_opcode ==>
       ~MEM (LAST bi).inst_id
         (MAP (\d. d.inst_id) (inst_all_deps bi order eda i'))` by
    (rpt strip_tac >>
     qspecl_then [`bi`, `eda`, `order`, `i'`] mp_tac terminator_not_dep_target >>
     simp[]) >>
  `sched <> [] /\ (LAST sched).inst_id = (LAST bi).inst_id` by
    (qspecl_then [`bi`, `order`, `eda`, `om`] mp_tac
       (SIMP_RULE std_ss [LET_THM] schedule_terminator_last) >>
     simp[Abbr `entries`, Abbr `sched`]) >>
  `EVERY (\i. MEM i bi) entries` by
    simp[Abbr `entries`, Abbr `bi`, entry_instructions_mem] >>
  `!i. MEM i sched ==> from_block bi i /\ ~is_pseudo i.inst_opcode` by
    (rpt strip_tac >>
     qspecl_then [`bi`, `order`, `eda`, `om`, `entries`, `i`] mp_tac
       schedule_output_from_block >> simp[Abbr `sched`]) >>
  `MEM (LAST bi) bi` by
    (imp_res_tac (DB.fetch "rich_list" "MEM_LAST_NOT_NIL")) >>
  `np_defs_before_uses bi` by
    gvs[non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `ALL_DISTINCT (MAP (\j. j.inst_id) sched)` by
    (simp[Abbr `sched`] >>
     irule schedule_output_all_distinct >> simp[Abbr `entries`]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) phis)` by
    (simp[Abbr `phis`] >> irule all_distinct_map_filter >> simp[]) >>
  `output_producer_before bi sched` by
    (simp[Abbr `sched`] >>
     irule schedule_output_producer_before >> simp[Abbr `entries`]) >>
  rpt conj_tac
  (* ===== Part 1: bb_well_formed ===== *)
  >- suspend "wf"
  (* ===== Part 2: ALL_DISTINCT inst_ids ===== *)
  >- suspend "all_distinct"
  (* ===== Part 3: non_pseudo_defs_before_uses ===== *)
  >> suspend "np_defs_before"
QED

(* --- Part 1: bb_well_formed --- *)

Resume dft_block_well_formed_gen[wf]:
  CONV_TAC (REWRITE_CONV [bb_well_formed_def]) >> simp[] >>
  conj_tac
  (* LAST is terminator *)
  >- (simp[rich_listTheory.LAST_APPEND_NOT_NIL] >>
      `from_block bi (LAST sched)` by
        (first_x_assum (qspec_then `LAST sched` mp_tac) >>
         impl_tac >- (imp_res_tac (DB.fetch "rich_list" "MEM_LAST_NOT_NIL")) >>
         strip_tac) >>
      drule from_block_id_unique >>
      disch_then (qspec_then `LAST bi` mp_tac) >> simp[] >>
      strip_tac >> gvs[flip_operands_is_terminator]) >>
  conj_tac
  (* unique terminator position *)
  >- (qspecl_then [`bi`, `phis`, `sched`] mp_tac dft_block_wf_unique_terminator >>
      impl_tac
      >- (conj_tac >- simp[Abbr `phis`] >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          conj_tac >- first_assum ACCEPT_TAC >>
          first_assum ACCEPT_TAC) >>
      strip_tac >>
      first_assum ACCEPT_TAC) >>
  (* PHI prefix *)
  (
    rpt strip_tac >>
    Cases_on `j < LENGTH phis`
    >- (
      `i < LENGTH phis` by simp[] >>
      simp[EL_APPEND1] >>
      qspecl_then [`\i. is_pseudo i.inst_opcode`, `bi`, `i`, `j`]
        mp_tac filter_el_mono >>
      simp[Abbr `phis`] >> strip_tac >>
      `(!i'' j''.
          i'' < j'' /\ j'' < LENGTH bi /\
          (EL j'' bi).inst_opcode = PHI ==>
          (EL i'' bi).inst_opcode = PHI)` by
        fs[bb_well_formed_def, Abbr `bi`] >>
      `(EL j (FILTER (\i. is_pseudo i.inst_opcode) bi ++ sched)).inst_opcode = PHI`
        by gvs[] >>
      `(EL j (FILTER (\i. is_pseudo i.inst_opcode) bi)).inst_opcode = PHI`
        by gvs[EL_APPEND1] >>
      `(EL j' bi).inst_opcode = PHI` by gvs[] >>
      `(EL i' bi).inst_opcode = PHI` by metis_tac[] >>
      gvs[])
    >> (
      `j - LENGTH phis < LENGTH sched` by simp[] >>
      `EL j (phis ++ sched) = EL (j - LENGTH phis) sched` by simp[EL_APPEND2] >>
      `MEM (EL (j - LENGTH phis) sched) sched` by metis_tac[MEM_EL] >>
      `~is_pseudo (EL (j - LENGTH phis) sched).inst_opcode` by metis_tac[] >>
      `(EL (j - LENGTH phis) sched).inst_opcode = PHI` by gvs[] >>
      fs[is_pseudo_def]))
QED

(* --- Part 2: ALL_DISTINCT inst_ids --- *)

Resume dft_block_well_formed_gen[all_distinct]:
  simp[ALL_DISTINCT_APPEND, MAP_MAP_o] >>
  rpt strip_tac >>
  rename1 `MEM eid _` >>
  `?p. MEM p phis /\ p.inst_id = eid` by
    (gvs[MEM_MAP] >> metis_tac[]) >>
  `?s. MEM s sched /\ s.inst_id = eid` by
    (gvs[MEM_MAP] >> metis_tac[]) >>
  `is_pseudo p.inst_opcode` by gvs[Abbr `phis`, MEM_FILTER] >>
  `~is_pseudo s.inst_opcode` by metis_tac[] >>
  `from_block bi s` by metis_tac[] >>
  `?j. MEM j bi /\ ~is_pseudo j.inst_opcode /\ s.inst_id = j.inst_id` by
    (gvs[from_block_def] >> metis_tac[flip_operands_inst_id]) >>
  `MEM p bi` by gvs[Abbr `phis`, MEM_FILTER] >>
  `j.inst_id = p.inst_id` by gvs[] >>
  `?n1. n1 < LENGTH bi /\ EL n1 bi = p` by metis_tac[MEM_EL] >>
  `?n2. n2 < LENGTH bi /\ EL n2 bi = j` by metis_tac[MEM_EL] >>
  `EL n1 (MAP (\i. i.inst_id) bi) = EL n2 (MAP (\i. i.inst_id) bi)` by
    simp[EL_MAP] >>
  `n1 = n2` by
    (qspecl_then [`MAP (\i. i.inst_id) bi`, `n1`, `n2`]
      mp_tac ALL_DISTINCT_EL_IMP >> simp[]) >>
  gvs[]
QED

(* --- Part 3: defs_before_uses --- *)

(* Helper: producing_inst on append *)
Triviality producing_inst_append:
  !l1 l2 var inst. producing_inst (l1 ++ l2) var = SOME inst ==>
    producing_inst l1 var = SOME inst \/
    (producing_inst l1 var = NONE /\ producing_inst l2 var = SOME inst)
Proof
  Induct_on `l1` >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> gvs[producing_inst_def]
QED

(* Helper: reverse direction of producing_inst_append *)
Triviality producing_inst_append_none_some:
  !l1 l2 var inst.
    producing_inst l1 var = NONE /\ producing_inst l2 var = SOME inst ==>
    producing_inst (l1 ++ l2) var = SOME inst
Proof
  Induct_on `l1` >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> gvs[producing_inst_def]
QED

(* Helper: producing_inst gives an index *)
Triviality producing_inst_index:
  !insts var inst. producing_inst insts var = SOME inst ==>
    ?p. p < LENGTH insts /\ EL p insts = inst /\ MEM var inst.inst_outputs
Proof
  Induct_on `insts` >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> gvs[]
  >- (qexists `0` >> simp[])
  >> (res_tac >> qexists `SUC p` >> simp[])
QED

(* Helper: producing_inst finds earliest, so any earlier definer
   implies the result is at or before that position *)
Triviality producing_inst_earliest:
  !insts var inst p.
    producing_inst insts var = SOME inst /\
    p < LENGTH insts /\ MEM var (EL p insts).inst_outputs ==>
    ?q. q <= p /\ q < LENGTH insts /\ EL q insts = inst
Proof
  Induct_on `insts` >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> gvs[]
  >- (qexists `0` >> simp[])
  >> (Cases_on `p` >> gvs[] >>
      first_x_assum drule_all >> strip_tac >>
      qexists `SUC q` >> simp[])
QED

(* Helper: if a definer is in the list, producing_inst is not NONE *)
Triviality producing_inst_not_none:
  !insts var x. MEM x insts /\ MEM var x.inst_outputs ==>
    ?y. producing_inst insts var = SOME y
Proof
  Induct >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> simp[] >>
  gvs[] >> metis_tac[]
QED

(* Helper: producing_inst NONE means no definer in list *)
Triviality producing_inst_none_no_def:
  !insts var. producing_inst insts var = NONE ==>
    !x. MEM x insts ==> ~MEM var x.inst_outputs
Proof
  Induct >> simp[producing_inst_def] >> rpt strip_tac >>
  Cases_on `MEM var h.inst_outputs` >> gvs[]
QED

(* Helper: from_block preserves inst_outputs *)
Triviality from_block_inst_outputs:
  !bi i. from_block bi i ==>
    ?j. MEM j bi /\ i.inst_outputs = j.inst_outputs /\
        i.inst_id = j.inst_id
Proof
  rw[from_block_def] >> gvs[] >> metis_tac[flip_operands_inst_outputs,
    flip_operands_inst_id]
QED

Triviality output_var_unique_in_block[local]:
  !bi a b v.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) /\
    MEM a bi /\ MEM b bi /\
    MEM v a.inst_outputs /\ MEM v b.inst_outputs ==>
    a = b
Proof
  rpt strip_tac >> Cases_on `a = b` >> simp[] >>
  qspecl_then [`bi`, `\i. i.inst_outputs`, `a`, `b`, `v`]
    mp_tac all_distinct_flat_map_disjoint >>
  simp[]
QED

Triviality block_body_defs_before_uses_gen[local]:
  !bb i j v.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    i < j /\ j < LENGTH (block_body bb) /\
    MEM v (inst_defs (EL j (block_body bb))) /\
    MEM (Var v) (EL i (block_body bb)).inst_operands ==>
    F
Proof
  rpt strip_tac >>
  qabbrev_tac `bd = block_body bb` >>
  `i < LENGTH bd` by decide_tac >>
  `j < LENGTH (block_body bb)` by simp[Abbr `bd`] >>
  `ALL_DISTINCT bb.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  qabbrev_tac `P = \i:instruction. ~is_pseudo i.inst_opcode /\
                                      ~is_terminator i.inst_opcode` >>
  `j < LENGTH (FILTER P bb.bb_instructions)` by
    (qunabbrev_tac `P` >> fs[Abbr `bd`, block_body_def]) >>
  `?fi fj. fi < fj /\ fj < LENGTH bb.bb_instructions /\
           EL fi bb.bb_instructions = EL i (FILTER P bb.bb_instructions) /\
           EL fj bb.bb_instructions = EL j (FILTER P bb.bb_instructions)` by
    (irule filter_el_mono >> simp[]) >>
  `bd = FILTER P bb.bb_instructions` by
    (qunabbrev_tac `P` >> simp[Abbr `bd`, block_body_def]) >>
  `fi < LENGTH bb.bb_instructions` by decide_tac >>
  `MEM v (EL fj bb.bb_instructions).inst_outputs` by
    gvs[inst_defs_def] >>
  `?prod. producing_inst bb.bb_instructions v = SOME prod` by
    (mp_tac (Q.SPECL [`bb.bb_instructions`, `v`,
             `EL fj bb.bb_instructions`] producing_inst_not_none) >>
     impl_tac >- (simp[MEM_EL] >> qexists_tac `fj` >> simp[]) >>
     disch_then (qx_choose_then `prod0` strip_assume_tac) >>
     qexists_tac `prod0` >> simp[]) >>
  `MEM prod bb.bb_instructions /\ MEM v prod.inst_outputs` by
    (drule producing_inst_unique >> simp[]) >>
  `prod = EL fj bb.bb_instructions` by
    (mp_tac (Q.SPECL [`bb.bb_instructions`, `prod`,
             `EL fj bb.bb_instructions`, `v`] output_var_unique_in_block) >>
     simp[MEM_EL] >>
     impl_tac >- (qexists_tac `fj` >> simp[]) >>
     simp[]) >>
  `~is_pseudo (EL fi bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `EL fi _ = _` SUBST1_TAC >>
     `i < LENGTH (FILTER P bb.bb_instructions)` by decide_tac >>
     `MEM (EL i (FILTER P bb.bb_instructions))
          (FILTER P bb.bb_instructions)` by
       (simp[MEM_EL] >> qexists_tac `i` >> simp[]) >>
     gvs[MEM_FILTER, Abbr `P`]) >>
  fs[non_pseudo_defs_before_uses_def, np_defs_before_uses_def] >>
  first_x_assum (qspecl_then [`fi`, `v`, `prod`] mp_tac) >>
  impl_tac >- (gvs[] >> metis_tac[]) >>
  strip_tac >>
  rename1 `idx < fi` >>
  `idx = fj` by
    (`idx < LENGTH bb.bb_instructions` by decide_tac >>
     `EL idx bb.bb_instructions = EL fj bb.bb_instructions` by simp[] >>
     metis_tac[ALL_DISTINCT_EL_IMP]) >>
  decide_tac
QED

Triviality block_body_topo_sorted_gen[local]:
  !bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (block_body bb)
Proof
  rpt strip_tac >>
  simp[topo_sorted_def, full_dep_def] >>
  qabbrev_tac `bd = block_body bb` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bd)` by
    (simp[Abbr `bd`, block_body_def] >>
     irule all_distinct_map_filter >> simp[]) >>
  `ALL_DISTINCT bd` by metis_tac[ALL_DISTINCT_MAP] >>
  rpt strip_tac
  >- (mp_tac (Q.SPECL [`bb.bb_instructions`,
                       `build_full_eda bb.bb_instructions`, `[]`]
          eda_topo_compatible_topo_sorted) >>
      impl_tac
      >- (simp[build_full_eda_wf] >>
          irule eda_topo_compatible_gen_weak >>
          fs[bb_well_formed_def, non_pseudo_defs_before_uses_def]) >>
      strip_tac >>
      qpat_x_assum `topo_sorted _ _`
        (mp_tac o Q.SPECL [`i`, `j`] o REWRITE_RULE[topo_sorted_def]) >>
      simp[GSYM block_body_def, Abbr `bd`])
  >- (simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
      spose_not_then strip_assume_tac >> rename1 `MEM v _` >>
      `MEM (Var v) (EL i bd).inst_operands` by
        gvs[inst_uses_def, MEM_operand_vars_iff] >>
      `bd = block_body bb` by fs[markerTheory.Abbrev_def] >>
      metis_tac[block_body_defs_before_uses_gen])
  >> (simp[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
      spose_not_then strip_assume_tac >> rename1 `MEM v _` >>
      `i < LENGTH bd` by decide_tac >>
      `MEM (EL i bd) bd /\ MEM (EL j bd) bd` by
        (simp[MEM_EL] >> metis_tac[]) >>
      `MEM (EL i bd) bb.bb_instructions /\
       MEM (EL j bd) bb.bb_instructions` by
        (qpat_x_assum `MEM (EL i bd) bd` mp_tac >>
         qpat_x_assum `MEM (EL j bd) bd` mp_tac >>
         simp[Abbr `bd`, block_body_def, MEM_FILTER]) >>
      `MEM v (EL i bd).inst_outputs /\ MEM v (EL j bd).inst_outputs` by
        fs[inst_defs_def] >>
      `EL i bd = EL j bd` by metis_tac[output_var_unique_in_block] >>
      `i <> j` by decide_tac >>
      metis_tac[ALL_DISTINCT_EL_IMP])
QED

(* Local block_body_full_equiv core: two topologically-sorted permutations of a
   locally well-formed block body produce identical run_insts results, or both
   Error.  Function-level block_perm_of facts only discharge the explicit
   pointwise/PERM/topo premises in the wrapper above. *)
Triviality block_body_full_equiv_gen[local]:
  !bb bb' fuel ctx s.
    bb_well_formed bb /\ bb_well_formed bb' /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    (!i. MEM i (block_body bb') ==>
         ?j. MEM j (block_body bb) /\ j.inst_id = i.inst_id /\
             !fuel ctx s. step_inst fuel ctx i s = step_inst fuel ctx j s) /\
    PERM (block_body bb)
         (MAP (choose_original (block_body bb)) (block_body bb')) /\
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (MAP (choose_original (block_body bb)) (block_body bb')) ==>
    (?e1 e2. run_insts fuel ctx (block_body bb) s = Error e1 /\
             run_insts fuel ctx (block_body bb') s = Error e2) \/
    run_insts fuel ctx (block_body bb) s =
    run_insts fuel ctx (block_body bb') s
Proof
  rpt strip_tac >>
  qabbrev_tac `l1 = block_body bb` >>
  qabbrev_tac `l2_raw = block_body bb'` >>
  qabbrev_tac `l2 = MAP (choose_original l1) l2_raw` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) l1)` by
    (simp[Abbr `l1`, block_body_def] >>
     irule all_distinct_map_filter >> simp[]) >>
  `run_insts fuel ctx l2_raw s = run_insts fuel ctx l2 s` by
    (simp[Abbr `l2`] >>
     irule run_insts_pointwise_equiv >> simp[LENGTH_MAP] >>
     rpt strip_tac >>
     irule map_choose_original_step_equiv >> simp[Abbr `l1`] >>
     simp[Abbr `l2_raw`]) >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  `PERM l1 l2` by simp[Abbr `l1`, Abbr `l2`, Abbr `l2_raw`] >>
  `ALL_DISTINCT l1` by
    (simp[Abbr `l1`, block_body_def] >>
     metis_tac[all_distinct_map_filter, ALL_DISTINCT_MAP]) >>
  qabbrev_tac `dep = \x y. full_dep eda x y /\ MEM x l1 /\ MEM y l1` >>
  `topo_sorted dep l1` by
    (simp[Abbr `dep`, topo_sorted_def] >> rpt strip_tac >>
     `~full_dep eda (EL i l1) (EL j l1)` suffices_by simp[] >>
     `topo_sorted (full_dep eda) l1` by
       (qunabbrev_tac `l1` >> qunabbrev_tac `eda` >> qunabbrev_tac `bi` >>
        irule block_body_topo_sorted_gen >> simp[]) >>
     fs[topo_sorted_def]) >>
  `topo_sorted dep l2` by
    (simp[Abbr `dep`, topo_sorted_def] >> rpt strip_tac >>
     `~full_dep eda (EL i l2) (EL j l2)` suffices_by
       (strip_tac >> gvs[] >> metis_tac[PERM_MEM_EQ, MEM_EL]) >>
     `topo_sorted (full_dep eda) l2` by
       simp[Abbr `l2`, Abbr `l1`, Abbr `l2_raw`, Abbr `bi`] >>
     fs[topo_sorted_def]) >>
  `topo_sorted (TC dep) l1` by
    (irule topo_sorted_tc_closed >> simp[Abbr `dep`]) >>
  `topo_sorted (TC dep) l2` by
    (irule topo_sorted_tc_closed >>
     simp[Abbr `dep`] >>
     `ALL_DISTINCT l2` by metis_tac[ALL_DISTINCT_PERM] >>
     simp[] >> metis_tac[PERM_MEM_EQ]) >>
  `!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
         ~TC dep x y /\ ~TC dep y x ==>
         ef_commutes x y` by
    (rpt strip_tac >>
     qspecl_then [`bb`, `x`, `y`,
       `\a c. full_dep (build_full_eda bb.bb_instructions) a c /\
              MEM a (block_body bb) /\ MEM c (block_body bb)`]
       mp_tac block_body_uncomp_ef_gen >>
     simp[Abbr `l1`, Abbr `dep`, Abbr `eda`, Abbr `bi`]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) l1` by
    simp[Abbr `l1`, block_body_def, EVERY_MEM, MEM_FILTER] >>
  `!b y. MEM b l1 /\ MEM y l1 /\ b <> y /\ is_barrier b ==>
         TC dep b y \/ TC dep y b` by
    (rpt strip_tac >>
     qspecl_then [`bb`, `b`, `y`, `dep`] mp_tac barrier_tc_connected >>
     simp[Abbr `l1`, Abbr `dep`, Abbr `eda`, Abbr `bi`]) >>
  qspecl_then [`l1`, `l2`, `dep`, `fuel`, `ctx`, `s`]
    mp_tac run_insts_topo_full_lift_ef >>
  simp[]
QED

Resume dft_block_well_formed_gen[np_defs_before]:
  CONV_TAC (REWRITE_CONV [non_pseudo_defs_before_uses_def]) >>
  CONV_TAC (REWRITE_CONV [np_defs_before_uses_def]) >> simp[] >>
  rpt strip_tac >>
  (* User at index j is non-pseudo, so NOT in phis (phis only contain pseudos) *)
  `~(j < LENGTH phis)` by
    (spose_not_then assume_tac >>
     `EL j (phis ++ sched) = EL j phis` by simp[EL_APPEND1] >>
     `MEM (EL j phis) phis` by metis_tac[MEM_EL] >>
     `is_pseudo (EL j phis).inst_opcode` by fs[Abbr `phis`, MEM_FILTER] >>
     gvs[]) >>
  (* User is in sched at position k = j - LENGTH phis *)
  drule producing_inst_append >> strip_tac >>
  `j - LENGTH phis < LENGTH sched` by simp[] >>
  qabbrev_tac `k = j - LENGTH phis` >>
  Cases_on `producing_inst phis var` >> gvs[]
  >- (
    (* Sub-case a: producer in phis -> witness at position p *)
    drule producing_inst_index >> strip_tac >>
    qexists `p` >> simp[EL_APPEND1])
  >> (
    (* Sub-case b: producer in sched, use output_producer_before *)
    `producing_inst sched var = SOME prod` by gvs[] >>
    `EL j (phis ++ sched) = EL k sched` by simp[Abbr `k`, EL_APPEND2] >>
    `MEM (Var var) (EL k sched).inst_operands` by metis_tac[] >>
    `MEM (EL k sched) sched` by metis_tac[MEM_EL] >>
    imp_res_tac producing_inst_unique >>
    `MEM prod sched` by metis_tac[] >>
    `from_block bi prod` by metis_tac[] >>
    drule from_block_inst_outputs >> strip_tac >>
    rename1 `MEM j_orig bi` >>
    `MEM var j_orig.inst_outputs` by metis_tac[] >>
    `?prod_bi. producing_inst bi var = SOME prod_bi` by
      metis_tac[producing_inst_not_none] >>
    (* prod_bi is non-pseudo: if pseudo, it'd be in phis, contradicting
       producing_inst phis var = NONE *)
    `~is_pseudo prod_bi.inst_opcode` by
      (spose_not_then assume_tac >>
       imp_res_tac producing_inst_unique >>
       `MEM prod_bi phis` by fs[Abbr `phis`, MEM_FILTER] >>
       `?z. producing_inst phis var = SOME z` by
         metis_tac[producing_inst_not_none] >>
       gvs[]) >>
    (* output_producer_before gives exists m < k with matching inst_id *)
    qpat_x_assum `output_producer_before _ _`
      (fn th => assume_tac (REWRITE_RULE [output_producer_before_def] th)) >>
    first_x_assum (qspecl_then [`k`, `var`, `prod_bi`] mp_tac) >>
    (impl_tac >- simp[]) >> strip_tac >>
    rename1 `m < k` >>
    `m < LENGTH sched` by simp[] >>
    `MEM (EL m sched) sched` by metis_tac[MEM_EL] >>
    `from_block bi (EL m sched)` by metis_tac[] >>
    drule from_block_inst_outputs >> strip_tac >>
    rename1 `MEM j2 bi` >>
    `j2.inst_id = prod_bi.inst_id` by metis_tac[] >>
    `MEM prod_bi bi` by (imp_res_tac producing_inst_unique >> simp[]) >>
    (* ALL_DISTINCT inst_ids: j2 = prod_bi *)
    `?n1. n1 < LENGTH bi /\ EL n1 bi = j2` by metis_tac[MEM_EL] >>
    `?n2. n2 < LENGTH bi /\ EL n2 bi = prod_bi` by metis_tac[MEM_EL] >>
    `EL n1 (MAP (\i. i.inst_id) bi) = EL n2 (MAP (\i. i.inst_id) bi)` by
      simp[EL_MAP] >>
    `n1 = n2` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
    `j2 = prod_bi` by gvs[] >>
    `MEM var (EL m sched).inst_outputs` by
      (imp_res_tac producing_inst_unique >> gvs[]) >>
    drule_all producing_inst_earliest >>
    strip_tac >> rename1 `q <= m` >>
    qexists `LENGTH phis + q` >> simp[EL_APPEND2, Abbr `k`])
QED

Finalise dft_block_well_formed_gen

(* Original: dft_block preserves well-formedness for original blocks *)
Theorem dft_block_well_formed:
  !fn order bb.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks ==>
    bb_well_formed (dft_block order bb)
Proof
  rpt strip_tac >>
  `bb_well_formed bb` by (gvs[wf_function_def, EVERY_MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (irule wf_fn_block_inst_ids_distinct >> metis_tac[]) >>
  `non_pseudo_defs_before_uses bb.bb_instructions` by
    (simp[non_pseudo_defs_before_uses_def] >>
     irule defs_before_implies_np >>
     irule wf_ssa_defs_before_uses >> metis_tac[]) >>
  metis_tac[dft_block_well_formed_gen]
QED

Triviality dft_block_body_topo_sorted[local]:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (block_body (dft_block order bb))
Proof
  rpt strip_tac >>
  simp[dft_block_def, LET_THM] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `phis = FILTER (\i. is_pseudo i.inst_opcode) bi` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  qabbrev_tac `om = build_offspring_map bi order` >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `sched = schedule_from_entries bi order eda om entries` >>
  `eda_wf eda bi` by simp[Abbr `eda`, build_full_eda_wf] >>
  `np_defs_before_uses bi` by
    gvs[non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `eda_topo_compatible bi eda order` by
    (simp[Abbr `eda`] >>
     qspecl_then [`bi`, `order`] mp_tac eda_topo_compatible_gen_weak >>
     simp[] >> disch_then irule >> fs[bb_well_formed_def, Abbr `bi`]) >>
  `bi <> []` by fs[bb_well_formed_def, Abbr `bi`] >>
  `!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)` by fs[bb_well_formed_def, Abbr `bi`] >>
  `~is_pseudo (LAST bi).inst_opcode` by
    (fs[bb_well_formed_def, Abbr `bi`] >>
     Cases_on `(LAST bb.bb_instructions).inst_opcode` >>
     gs[is_terminator_def, is_pseudo_def]) >>
  `entries <> [] /\ LAST entries = LAST bi` by
    (mp_tac (Q.SPECL [`bi`, `order`, `eda`] terminator_last_entry) >>
     simp[LET_THM, Abbr `entries`]) >>
  `id_not_in_stack (LAST bi).inst_id (MAP DfsProcess (FRONT entries))` by
    (mp_tac (Q.SPECL [`bi`, `order`, `eda`] terminator_not_in_front_entries) >>
     simp[LET_THM, Abbr `entries`]) >>
  `!i'. MEM i' bi /\ ~is_pseudo i'.inst_opcode ==>
       ~MEM (LAST bi).inst_id
         (MAP (\d. d.inst_id) (inst_all_deps bi order eda i'))` by
    (rpt strip_tac >>
     qspecl_then [`bi`, `eda`, `order`, `i'`] mp_tac terminator_not_dep_target >>
     simp[]) >>
  `EVERY (\i. MEM i bi) entries` by
    simp[Abbr `entries`, Abbr `bi`, entry_instructions_mem] >>
  `sched <> []` by
    (qspecl_then [`bi`, `order`, `eda`, `om`] mp_tac
       (SIMP_RULE std_ss [LET_THM] schedule_terminator_last) >>
     simp[Abbr `entries`, Abbr `sched`]) >>
  `EVERY (\i. ~is_pseudo i.inst_opcode) sched` by
    (simp[EVERY_MEM, Abbr `sched`] >> rpt strip_tac >>
     metis_tac[schedule_output_from_block]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) sched)` by
    (simp[Abbr `sched`] >>
     irule schedule_output_all_distinct >> simp[Abbr `entries`]) >>
  `output_eda_before eda sched` by
    (simp[Abbr `sched`] >>
     irule schedule_output_eda_before >> simp[Abbr `entries`]) >>
  `output_producer_before bi sched` by
    (simp[Abbr `sched`] >>
     irule schedule_output_producer_before >> simp[Abbr `entries`]) >>
  `!i. MEM i sched ==> from_block bi i /\ ~is_pseudo i.inst_opcode` by
    (rpt strip_tac >>
     qspecl_then [`bi`, `order`, `eda`, `om`, `entries`, `i`] mp_tac
       schedule_output_from_block >> simp[Abbr `sched`]) >>
  `topo_sorted (full_dep eda) sched` by
    (qspecl_then [`bi`, `eda`, `sched`] mp_tac schedule_topo_sorted_full_dep >>
     simp[Abbr `eda`]) >>
  `bb_well_formed ((bb with bb_instructions := phis ++ sched))` by
    (mp_tac (Q.SPECL [`order`, `bb`] dft_block_well_formed_gen) >>
     simp[dft_block_def, LET_THM, Abbr `phis`, Abbr `sched`, Abbr `eda`,
          Abbr `om`, Abbr `entries`]) >>
  `EVERY (\i. is_pseudo i.inst_opcode) phis` by
    simp[Abbr `phis`, EVERY_MEM, MEM_FILTER] >>
  `block_body ((bb with bb_instructions := phis ++ sched)) = FRONT sched` by
    (irule block_body_pseudo_prefix_nonpseudo_sched >> simp[]) >>
  simp[] >>
  `FRONT sched = TAKE (PRE (LENGTH sched)) sched` by
    metis_tac[rich_listTheory.TAKE_PRE_LENGTH] >>
  pop_assum SUBST1_TAC >>
  irule topo_sorted_take >> simp[]
QED

Triviality dft_block_preserves_output_distinct[local]:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs)
      (dft_block order bb).bb_instructions))
Proof
  rpt strip_tac >>
  simp[dft_block_def, LET_THM] >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `phis = FILTER (\i. is_pseudo i.inst_opcode) bi` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  qabbrev_tac `om = build_offspring_map bi order` >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `sched = schedule_from_entries bi order eda om entries` >>
  `eda_wf eda bi` by simp[Abbr `eda`, build_full_eda_wf] >>
  `eda_topo_compatible bi eda order` by
    (fs[Abbr `eda`, Abbr `bi`, bb_well_formed_def,
        non_pseudo_defs_before_uses_def] >>
     metis_tac[eda_topo_compatible_gen_weak]) >>
  `np_defs_before_uses bi` by
    gvs[non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `bi <> []` by fs[bb_well_formed_def, Abbr `bi`] >>
  `!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)` by fs[bb_well_formed_def, Abbr `bi`] >>
  `EVERY (\i. MEM i bi) entries` by
    simp[Abbr `entries`, Abbr `bi`, entry_instructions_mem] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) sched)` by
    (simp[Abbr `sched`] >>
     irule schedule_output_all_distinct >> simp[Abbr `entries`]) >>
  `EVERY (from_block bi) sched` by
    (simp[EVERY_MEM, Abbr `sched`] >> rpt strip_tac >>
     metis_tac[schedule_output_from_block]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) phis))` by
    (simp[Abbr `phis`] >> irule all_distinct_flat_map_filter >> simp[Abbr `bi`]) >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) sched))` by
    (mp_tac (Q.SPECL [`bi`, `sched`] from_block_list_outputs_distinct) >>
     simp[Abbr `bi`]) >>
  `!x a b.
     MEM a phis /\ MEM b sched /\
     MEM x a.inst_outputs /\ MEM x b.inst_outputs ==> F` by
    (simp[Abbr `phis`] >> metis_tac[pseudo_from_block_outputs_disjoint]) >>
  metis_tac[all_distinct_flat_map_append_disjoint]
QED

Triviality dft_block_body_topo_sorted_fn[local]:
  !fn order bb.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks ==>
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (block_body (dft_block order bb))
Proof
  rpt strip_tac >>
  irule dft_block_body_topo_sorted >>
  rpt conj_tac
  >- (`ALL_DISTINCT
        (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
                fn.fn_blocks))` by
        gvs[wf_ssa_def, ssa_form_def, fn_insts_def,
            flat_map_outputs_fn_insts_blocks] >>
      irule all_distinct_flat_mem >>
      qexists_tac `MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
                    fn.fn_blocks` >>
      simp[MEM_MAP] >> metis_tac[])
  >- (irule wf_fn_block_inst_ids_distinct >> metis_tac[])
  >- (gvs[wf_function_def, EVERY_MEM])
  >> (simp[non_pseudo_defs_before_uses_def] >>
      irule defs_before_implies_np >>
      irule wf_ssa_defs_before_uses >> metis_tac[])
QED

(* Helper: MAP with conditional replacement preserves EVERY *)
Theorem every_map_replace:
  !P bbs lbl bb'.
    EVERY P bbs /\ P bb' ==>
    EVERY P (MAP (\b. if b.bb_label = lbl then bb' else b) bbs)
Proof
  Induct_on `bbs` >> simp[] >> rpt strip_tac >> rw[]
QED

(* FUNPOW invariant predicate *)
Definition dft_inv_def:
  dft_inv bbs <=>
    EVERY (\bb. bb_well_formed bb /\
                ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
                non_pseudo_defs_before_uses bb.bb_instructions /\
                ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))) bbs
End

(* dft_process_one preserves dft_inv *)
Theorem dft_process_one_preserves_inv:
  !cfg lr fn st lbl.
    dft_inv st.dls_blocks ==>
    dft_inv (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  rw[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[dft_inv_def] >>
  irule every_map_replace >> simp[] >>
  fs[dft_inv_def] >>
  `MEM x st.dls_blocks` by
    (fs[lookup_block_def] >> imp_res_tac venomExecPropsTheory.FIND_MEM) >>
  `bb_well_formed x /\ ALL_DISTINCT (MAP (\i. i.inst_id) x.bb_instructions) /\
   non_pseudo_defs_before_uses x.bb_instructions /\
   ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) x.bb_instructions))` by fs[EVERY_MEM] >>
  drule_all dft_block_well_formed_gen >> strip_tac >>
  drule_all dft_block_preserves_output_distinct >> strip_tac >>
  simp[]
QED

(* dft_loop_step preserves dft_inv *)
Theorem dft_loop_step_preserves_inv:
  !cfg lr fn trip.
    dft_inv (FST trip).dls_blocks ==>
    dft_inv (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >>
  Cases_on `r` >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`]
    mp_tac dft_process_one_preserves_inv >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

(* FUNPOW preserves dft_inv *)
Theorem funpow_dft_loop_preserves_inv:
  !n cfg lr fn trip.
    dft_inv (FST trip).dls_blocks ==>
    dft_inv (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_preserves_inv >>
  first_x_assum irule >> simp[]
QED

(* Core: dft_fn preserves dft_inv *)
(* Original blocks satisfy dft_inv *)
Theorem wf_fn_initial_dft_inv:
  !fn. wf_ssa fn /\ wf_function fn ==> dft_inv fn.fn_blocks
Proof
  rpt strip_tac >> simp[dft_inv_def, EVERY_MEM] >> rpt strip_tac
  >- (gvs[wf_function_def, EVERY_MEM])
  >- (irule wf_fn_block_inst_ids_distinct >> metis_tac[])
  >- (simp[non_pseudo_defs_before_uses_def] >>
      irule defs_before_implies_np >>
      irule wf_ssa_defs_before_uses >> metis_tac[])
  >> (`ALL_DISTINCT
        (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
                fn.fn_blocks))` by
        gvs[wf_ssa_def, ssa_form_def, fn_insts_def,
            flat_map_outputs_fn_insts_blocks] >>
      irule all_distinct_flat_mem >>
      qexists_tac `MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
                    fn.fn_blocks` >>
      simp[MEM_MAP] >> metis_tac[])
QED

(* dft_fn output satisfies dft_inv *)
Theorem dft_fn_dft_inv:
  !fn. wf_ssa fn /\ wf_function fn ==> dft_inv (dft_fn fn).fn_blocks
Proof
  rpt strip_tac >>
  simp[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[] >>
  MATCH_MP_TAC funpow_dft_loop_preserves_inv >>
  drule_all wf_fn_initial_dft_inv >> simp[]
QED

(* ===== FUNPOW invariant: blocks maintain block_perm_of ===== *)

(* Predicate: every block in bbs is block_perm_of fn *)
Definition all_blocks_perm_of_def:
  all_blocks_perm_of fn bbs <=>
    EVERY (block_perm_of fn) bbs
End

(* dft_process_one preserves all_blocks_perm_of, given dft_inv *)
Theorem dft_process_one_preserves_perm:
  !cfg lr fn st lbl.
    all_blocks_perm_of fn st.dls_blocks /\ dft_inv st.dls_blocks ==>
    all_blocks_perm_of fn (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  rw[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  simp[all_blocks_perm_of_def] >>
  irule every_map_replace >> simp[] >>
  fs[all_blocks_perm_of_def, dft_inv_def] >>
  irule dft_block_preserves_perm_of >>
  fs[lookup_block_def] >>
  imp_res_tac venomExecPropsTheory.FIND_MEM >>
  fs[EVERY_MEM]
QED

(* FUNPOW lifting: dft_loop_step preserves all_blocks_perm_of *)
Theorem dft_loop_step_preserves_perm:
  !cfg lr fn trip.
    all_blocks_perm_of fn (FST trip).dls_blocks /\
    dft_inv (FST trip).dls_blocks ==>
    all_blocks_perm_of fn (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >>
  Cases_on `r` >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`]
    mp_tac dft_process_one_preserves_perm >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Theorem funpow_dft_loop_preserves_perm:
  !n cfg lr fn trip.
    all_blocks_perm_of fn (FST trip).dls_blocks /\
    dft_inv (FST trip).dls_blocks ==>
    all_blocks_perm_of fn
      (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  MATCH_MP_TAC (SRULE [] dft_loop_step_preserves_perm) >>
  conj_tac
  >- (first_x_assum MATCH_MP_TAC >> simp[] >>
      MATCH_MP_TAC funpow_dft_loop_preserves_inv >> simp[])
  >> (MATCH_MP_TAC funpow_dft_loop_preserves_inv >> simp[])
QED

(* Core: dft_fn blocks are all block_perm_of fn *)
Theorem dft_fn_all_perm_of:
  !fn.
    wf_ssa fn /\ wf_function fn ==>
    all_blocks_perm_of fn (dft_fn fn).fn_blocks
Proof
  rpt strip_tac >> simp[dft_fn_def, LET_THM] >>
  rewrite_tac[LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[] >>
  irule funpow_dft_loop_preserves_perm >>
  simp[all_blocks_perm_of_def, EVERY_MEM, original_block_perm_of] >>
  irule wf_fn_initial_dft_inv >> simp[]
QED

(* Key bridge: lookup in dft_fn blocks gives a block_perm_of fn *)
Theorem dft_fn_lookup_perm_of:
  !fn lbl bb'.
    wf_ssa fn /\ wf_function fn /\
    lookup_block lbl (dft_fn fn).fn_blocks = SOME bb' ==>
    block_perm_of fn bb'
Proof
  rpt strip_tac >>
  `MEM bb' (dft_fn fn).fn_blocks` by
    (fs[lookup_block_def] >>
     imp_res_tac venomExecPropsTheory.FIND_MEM) >>
  `all_blocks_perm_of fn (dft_fn fn).fn_blocks` by
    (irule dft_fn_all_perm_of >> simp[]) >>
  fs[all_blocks_perm_of_def, EVERY_MEM]
QED


(* All blocks in dft_fn are well-formed *)
Theorem dft_fn_blocks_well_formed:
  !fn bb'.
    wf_ssa fn /\ wf_function fn /\ MEM bb' (dft_fn fn).fn_blocks ==>
    bb_well_formed bb'
Proof
  rpt strip_tac >>
  drule_all dft_fn_dft_inv >> strip_tac >>
  gvs[dft_inv_def, EVERY_MEM]
QED

(* lookup_block NONE is preserved by dft_fn *)
Theorem dft_fn_lookup_block_none:
  !fn lbl.
    lookup_block lbl fn.fn_blocks = NONE ==>
    lookup_block lbl (dft_fn fn).fn_blocks = NONE
Proof
  spose_not_then strip_assume_tac >>
  Cases_on `lookup_block lbl (dft_fn fn).fn_blocks` >> gvs[] >>
  fs[lookup_block_def] >>
  imp_res_tac venomExecPropsTheory.FIND_MEM >>
  imp_res_tac venomExecPropsTheory.FIND_P >> gvs[] >>
  drule dft_fn_labels >> strip_tac >>
  `?y. FIND (\bb. bb.bb_label = x.bb_label) fn.fn_blocks = SOME y` by
    (irule MEM_P_FIND >> qexists_tac `bb'` >> simp[]) >>
  gvs[]
QED

(* ===== DFT output topo_sorted w.r.t. original deps ===== *)

(* topo_sorted_map: subsumed by map_choose_original_topo_sorted_restricted *)

(* flip_operands_inst_outputs: already in dftStructuralTheory *)

(* flip_operands preserves set of operand_vars *)
Triviality flip_operands_operand_vars_set:
  !i. set (operand_vars (flip_operands i).inst_operands) =
      set (operand_vars i.inst_operands)
Proof
  rw[flip_operands_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[LET_THM] >>
  TRY (IF_CASES_TAC >> simp[]) >>
  (* Two-operand case: [a; b] → [b; a] *)
  simp[operand_vars_def] >>
  every_case_tac >> gvs[EXTENSION] >> metis_tac[]
QED

(* full_dep only depends on inst_id for from_block elements:
   from_block preserves inst_id, set(inst_defs), and set(inst_uses).
   So full_dep(eda)(x, y) ⟺ full_dep(eda)(x', y') when inst_ids match
   and all instructions are from_block elements of the same block.
   Proof: eda_dep only uses inst_id (proven as eda_dep_inst_id_only).
          inst_defs = inst_outputs preserved by flip_operands_inst_outputs.
          set(inst_uses) = set(operand_vars) preserved by flip_operands_operand_vars_set.
   This condition is exactly what map_choose_original_topo_sorted_restricted needs. *)


(* ===== Function-level: run_blocks lift_result ===== *)

(* Specialized rewrite for run_blocks (SUC fuel) — avoids hanging issues
   with simp/ONCE_REWRITE_TAC on the recursive definition *)
val run_blocks_SUC = let
  val rb = run_blocks_def
  val (vars, _) = strip_forall (concl rb)
  val [sv,fv,fnv,cv] = vars
  val inst = SPECL [sv, mk_comb(``SUC``, fv), fnv, cv] rb
in SIMP_RULE (srw_ss()) [] inst |> GENL [sv, fv, fnv, cv] end;

(* DFT preserves fn_pseudos_prefix: dft_block outputs pseudos ++ scheduled,
   and scheduled contains only non-pseudo instructions. *)
Triviality dft_block_pseudos_prefix[local]:
  !order bb. pseudos_prefix (dft_block order bb)
Proof
  rpt strip_tac >>
  simp[pseudos_prefix_def, dft_block_def, LET_THM] >>
  qabbrev_tac `phis = FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions` >>
  qabbrev_tac `sched = schedule_from_entries bb.bb_instructions order
    (build_full_eda bb.bb_instructions)
    (build_offspring_map bb.bb_instructions order)
    (entry_instructions bb.bb_instructions order
      (build_full_eda bb.bb_instructions))` >>
  rpt strip_tac >>
  Cases_on `j < LENGTH phis`
  >- (
    `i < LENGTH phis` by decide_tac >>
    `EL i (phis ++ sched) = EL i phis` by simp[EL_APPEND1] >>
    `MEM (EL i phis) phis` by metis_tac[MEM_EL] >>
    gvs[Abbr `phis`, MEM_FILTER]) >>
  `j - LENGTH phis < LENGTH sched` by simp[] >>
  `EL j (phis ++ sched) = EL (j - LENGTH phis) sched` by simp[EL_APPEND2] >>
  `MEM (EL (j - LENGTH phis) sched) sched` by metis_tac[MEM_EL] >>
  `~is_pseudo (EL (j - LENGTH phis) sched).inst_opcode` by
    metis_tac[schedule_output_from_block, build_full_eda_wf,
              entry_instructions_mem] >>
  gvs[]
QED

Triviality dft_block_body_topo_sorted_mapped_gen[local]:
  !bb order.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (MAP (choose_original (block_body bb)) (block_body (dft_block order bb)))
Proof
  rpt strip_tac >>
  irule map_choose_original_topo_sorted_restricted >>
  rpt conj_tac
  >- (rpt strip_tac >>
      `from_block bb.bb_instructions x /\ from_block bb.bb_instructions y` by
        (conj_tac
         >- (`MEM x (FILTER (\i. ~is_pseudo i.inst_opcode)
                  (dft_block order bb).bb_instructions)` by
               fs[block_body_def, listTheory.MEM_FILTER] >>
             metis_tac[dft_block_from_orig])
         >> (`MEM y (FILTER (\i. ~is_pseudo i.inst_opcode)
                  (dft_block order bb).bb_instructions)` by
               fs[block_body_def, listTheory.MEM_FILTER] >>
             metis_tac[dft_block_from_orig])) >>
      `from_block bb.bb_instructions x' /\ from_block bb.bb_instructions y'` by
        (fs[block_body_def, MEM_FILTER, from_block_def] >> metis_tac[]) >>
      metis_tac[from_block_full_dep])
  >- (rpt strip_tac >>
      `from_block bb.bb_instructions i` by
        (`MEM i (FILTER (\i. ~is_pseudo i.inst_opcode)
             (dft_block order bb).bb_instructions)` by
           fs[block_body_def, listTheory.MEM_FILTER] >>
         metis_tac[dft_block_from_orig]) >>
      gvs[from_block_def, block_body_def, MEM_FILTER,
          flip_operands_inst_id, flip_operands_is_terminator] >>
      metis_tac[])
  >- (simp[block_body_def] >> irule all_distinct_map_filter >> simp[])
  >> (irule dft_block_body_topo_sorted >> simp[])
QED

Triviality dft_block_body_topo_sorted_mapped[local]:
  !fn bb order.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks ==>
    topo_sorted (full_dep (build_full_eda bb.bb_instructions))
      (MAP (choose_original (block_body bb)) (block_body (dft_block order bb)))
Proof
  rpt strip_tac >>
  irule dft_block_body_topo_sorted_mapped_gen >>
  rpt conj_tac
  >- (`ALL_DISTINCT
        (FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
                fn.fn_blocks))` by
        gvs[wf_ssa_def, ssa_form_def, fn_insts_def,
            flat_map_outputs_fn_insts_blocks] >>
      irule all_distinct_flat_mem >>
      qexists_tac `MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
        fn.fn_blocks` >>
      simp[MEM_MAP] >> qexists_tac `bb` >> simp[])
  >- (irule wf_fn_block_inst_ids_distinct >> metis_tac[])
  >- (gvs[wf_function_def, EVERY_MEM])
  >> (simp[non_pseudo_defs_before_uses_def] >>
      irule defs_before_implies_np >>
      irule wf_ssa_defs_before_uses >> metis_tac[])
QED

Triviality dft_block_body_from_block[local]:
  !order bb i.
    MEM i (block_body (dft_block order bb)) ==>
    ?j. MEM j (block_body bb) /\ j.inst_id = i.inst_id /\
        !fuel ctx s. step_inst fuel ctx i s = step_inst fuel ctx j s
Proof
  rpt strip_tac >>
  `from_block bb.bb_instructions i` by
    (`MEM i (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions)` by
       fs[block_body_def, MEM_FILTER] >>
     metis_tac[dft_block_from_orig]) >>
  gvs[from_block_def, block_body_def, MEM_FILTER]
  >- (qexists_tac `i` >> simp[])
  >> (qexists_tac `j` >> simp[flip_operands_inst_id, flip_operands_step_inst] >>
      metis_tac[flip_operands_is_terminator])
QED

Triviality dft_block_body_from_block_rev[local]:
  !order bb j.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    MEM j (block_body bb) ==>
    ?k. MEM k (block_body (dft_block order bb)) /\ k.inst_id = j.inst_id
Proof
  rpt strip_tac >>
  `PERM (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode)
               (dft_block order bb).bb_instructions))
         (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions))` by
    (irule dft_block_perm_ids >> simp[]) >>
  `MEM j.inst_id (MAP (\i. i.inst_id)
            (FILTER (\i. ~is_pseudo i.inst_opcode)
               (dft_block order bb).bb_instructions))` by
    (imp_res_tac PERM_MEM_EQ >> fs[block_body_def, MEM_FILTER, MEM_MAP] >>
     metis_tac[]) >>
  gvs[MEM_MAP, MEM_FILTER] >> rename1 `MEM k _` >>
  `from_block bb.bb_instructions k` by
    (`MEM k (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions)` by simp[MEM_FILTER] >>
     metis_tac[dft_block_from_orig]) >>
  `~is_terminator k.inst_opcode` by
    (gvs[block_body_def, MEM_FILTER, from_block_def,
         flip_operands_inst_id, flip_operands_is_terminator] >>
     metis_tac[all_distinct_map_mem_inj]) >>
  qexists_tac `k` >> simp[block_body_def, MEM_FILTER]
QED

Triviality dft_block_body_inst_ids_perm[local]:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    PERM (MAP (\i. i.inst_id) (block_body bb))
         (MAP (\i. i.inst_id) (block_body (dft_block order bb)))
Proof
  rpt strip_tac >>
  irule PERM_ALL_DISTINCT >>
  conj_tac
  >- (gen_tac >> simp[MEM_MAP] >> eq_tac >> strip_tac
      >- (mp_tac (Q.SPECL [`order`, `bb`, `i`] dft_block_body_from_block_rev) >>
          simp[] >> strip_tac >> qexists_tac `k` >> simp[])
      >> (mp_tac (Q.SPECL [`order`, `bb`, `i`] dft_block_body_from_block) >>
          simp[] >> strip_tac >> qexists_tac `j` >> simp[])) >>
  conj_tac
  >- (simp[block_body_def] >> irule all_distinct_map_filter >> simp[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id)
       (FILTER (\i. ~is_pseudo i.inst_opcode)
          (dft_block order bb).bb_instructions))` by
    (mp_tac (Q.SPECL [`order`, `bb`] dft_block_perm_ids) >> simp[] >>
     strip_tac >> metis_tac[ALL_DISTINCT_PERM, PERM_SYM,
                            all_distinct_map_filter]) >>
  simp[block_body_def] >>
  `FILTER (\i. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode)
     (dft_block order bb).bb_instructions =
   FILTER (\i. ~is_terminator i.inst_opcode)
     (FILTER (\i. ~is_pseudo i.inst_opcode)
        (dft_block order bb).bb_instructions)` by
    (rewrite_tac[FILTER_FILTER] >> AP_THM_TAC >> AP_TERM_TAC >>
     simp[FUN_EQ_THM] >> metis_tac[CONJ_COMM]) >>
  simp[] >> irule all_distinct_map_filter >> simp[]
QED

Triviality dft_block_body_choose_perm[local]:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    PERM (block_body bb)
         (MAP (choose_original (block_body bb))
              (block_body (dft_block order bb)))
Proof
  rpt strip_tac >>
  irule map_choose_original_perm >>
  rpt conj_tac
  >- (rpt strip_tac >> metis_tac[dft_block_body_from_block])
  >- (simp[block_body_def] >> irule all_distinct_map_filter >> simp[]) >>
  irule dft_block_body_inst_ids_perm >> simp[]
QED

Triviality dft_block_same_length[local]:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    LENGTH (dft_block order bb).bb_instructions = LENGTH bb.bb_instructions
Proof
  rpt strip_tac >>
  `LENGTH (FILTER (\i. is_pseudo i.inst_opcode)
      (dft_block order bb).bb_instructions) =
   LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)` by
    simp[dft_block_phis] >>
  `LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode)
      (dft_block order bb).bb_instructions) =
   LENGTH (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)` by
    (mp_tac (Q.SPECL [`order`, `bb`] dft_block_perm_ids) >> simp[] >>
     strip_tac >> drule PERM_LENGTH >> simp[]) >>
  metis_tac[length_filter_complement]
QED

Triviality dft_block_same_last[local]:
  !order bb.
    bb_well_formed bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    LAST (dft_block order bb).bb_instructions = LAST bb.bb_instructions
Proof
  rpt strip_tac >>
  `bb_well_formed (dft_block order bb)` by
    (mp_tac (Q.SPECL [`order`, `bb`] dft_block_well_formed_gen) >> simp[]) >>
  `LENGTH (dft_block order bb).bb_instructions = LENGTH bb.bb_instructions` by
    (irule dft_block_same_length >> simp[]) >>
  `MEM (LAST (dft_block order bb).bb_instructions)
     (FILTER (\i. ~is_pseudo i.inst_opcode)
        (dft_block order bb).bb_instructions)` by
    (simp[MEM_FILTER] >> conj_tac
     >- (fs[bb_well_formed_def] >> metis_tac[terminator_not_pseudo_not_flippable])
     >> irule MEM_LAST_NOT_NIL >> fs[bb_well_formed_def]) >>
  `from_block bb.bb_instructions (LAST (dft_block order bb).bb_instructions)` by
    (mp_tac (Q.SPECL [`order`, `bb`,
       `LAST (dft_block order bb).bb_instructions`] dft_block_from_orig) >>
     simp[]) >>
  `is_terminator (LAST (dft_block order bb).bb_instructions).inst_opcode` by
    fs[bb_well_formed_def] >>
  qpat_x_assum `from_block bb.bb_instructions _` mp_tac >>
  simp[from_block_def] >> strip_tac >> rename1 `MEM j bb.bb_instructions` >>
  gvs[]
  >- (`LAST (dft_block order bb).bb_instructions = LAST bb.bb_instructions` by
        (fs[bb_well_formed_def, MEM_EL] >>
         `n' = PRE (LENGTH bb.bb_instructions)` by metis_tac[] >>
         `EL n' bb.bb_instructions = LAST bb.bb_instructions` by
           (Cases_on `bb.bb_instructions` >> fs[LAST_EL]) >>
         gvs[]) >>
      simp[])
  >> (`~is_terminator j.inst_opcode` by metis_tac[is_flippable_not_terminator] >>
      fs[flip_operands_is_terminator])
QED

Triviality dft_block_same_phi_prefix[local]:
  !order bb.
    bb_well_formed bb /\ pseudos_prefix bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions ==>
    phi_prefix_length (dft_block order bb).bb_instructions =
    phi_prefix_length bb.bb_instructions /\
    (!i. i < phi_prefix_length bb.bb_instructions ==>
         EL i (dft_block order bb).bb_instructions = EL i bb.bb_instructions)
Proof
  rpt strip_tac >>
  `bb_well_formed (dft_block order bb)` by
    (mp_tac (Q.SPECL [`order`, `bb`] dft_block_well_formed_gen) >> simp[]) >>
  `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode)
      (dft_block order bb).bb_instructions) =
   phi_prefix_length (dft_block order bb).bb_instructions` by
    (irule phi_prefix_length_filter_pseudo >> fs[bb_well_formed_def]) >>
  `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) =
   phi_prefix_length bb.bb_instructions` by
    (irule phi_prefix_length_filter_pseudo >> fs[bb_well_formed_def]) >>
  `phi_prefix_length (dft_block order bb).bb_instructions =
   phi_prefix_length bb.bb_instructions` by
    (qpat_x_assum `phi_prefix_length (FILTER _ (dft_block _ _).bb_instructions) = _`
       (fn th => rewrite_tac[GSYM th]) >>
     qpat_x_assum `phi_prefix_length (FILTER _ bb.bb_instructions) = _`
       (fn th => rewrite_tac[GSYM th]) >>
     simp[dft_block_phis]) >>
  simp[] >> rpt strip_tac >>
  `i < phi_prefix_length (dft_block order bb).bb_instructions` by metis_tac[] >>
  `EL i (FILTER (\i. is_pseudo i.inst_opcode)
      (dft_block order bb).bb_instructions) =
   EL i (dft_block order bb).bb_instructions` by
    (qspecl_then [`(dft_block order bb).bb_instructions`, `i`]
       mp_tac phi_prefix_el_filter_pseudo >> simp[] >>
     impl_tac >- fs[bb_well_formed_def] >> simp[]) >>
  `EL i (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) =
   EL i bb.bb_instructions` by
    (qspecl_then [`bb.bb_instructions`, `i`]
       mp_tac phi_prefix_el_filter_pseudo >> simp[] >>
     impl_tac >- fs[bb_well_formed_def] >> simp[]) >>
  metis_tac[dft_block_phis]
QED

Triviality dft_block_same_pseudo_suffix[local]:
  !order bb p q.
    pseudos_prefix bb /\
    p = phi_prefix_length bb.bb_instructions /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    DROP p (TAKE q (dft_block order bb).bb_instructions) =
    DROP p (TAKE q bb.bb_instructions)
Proof
  rpt strip_tac >>
  qabbrev_tac `P = \i:instruction. is_pseudo i.inst_opcode` >>
  `TAKE q bb.bb_instructions = FILTER P bb.bb_instructions` by
    (qpat_x_assum `q = LENGTH (FILTER P bb.bb_instructions)` SUBST1_TAC >>
     qunabbrev_tac `P` >> irule pseudo_prefix_take_filter >> simp[]) >>
  `q = LENGTH (FILTER P (dft_block order bb).bb_instructions)` by
    (qpat_x_assum `q = LENGTH (FILTER P bb.bb_instructions)` SUBST1_TAC >>
     simp[Abbr `P`, dft_block_phis]) >>
  `TAKE q (dft_block order bb).bb_instructions =
   FILTER P (dft_block order bb).bb_instructions` by
    (pop_assum SUBST1_TAC >> qunabbrev_tac `P` >>
     irule pseudo_prefix_take_filter >> simp[dft_block_pseudos_prefix]) >>
  simp[Abbr `P`, dft_block_phis]
QED

Triviality dft_block_exec_block_same_body_lift_gen[local]:
  !bb order q fuel ctx s.
    bb_well_formed bb /\ pseudos_prefix bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (exec_block fuel ctx bb (s with vs_inst_idx := q))
      (exec_block fuel ctx (dft_block order bb) (s with vs_inst_idx := q))
Proof
  rpt strip_tac >>
  qabbrev_tac `bb' = dft_block order bb` >>
  `bb_well_formed bb'` by
    (qunabbrev_tac `bb'` >>
     mp_tac (Q.SPECL [`order`, `bb`] dft_block_well_formed_gen) >> simp[]) >>
  `pseudos_prefix bb'` by simp[Abbr `bb'`, dft_block_pseudos_prefix] >>
  `LAST bb'.bb_instructions = LAST bb.bb_instructions` by
    (simp[Abbr `bb'`] >> irule dft_block_same_last >> simp[]) >>
  `LENGTH bb'.bb_instructions = LENGTH bb.bb_instructions` by
    (simp[Abbr `bb'`] >> irule dft_block_same_length >> simp[]) >>
  `q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb'.bb_instructions)` by
    simp[Abbr `bb'`, dft_block_phis] >>
  `(?e1 e2. run_insts fuel ctx (block_body bb) s = Error e1 /\
            run_insts fuel ctx (block_body bb') s = Error e2) \/
   run_insts fuel ctx (block_body bb) s =
   run_insts fuel ctx (block_body bb') s` by
    (mp_tac (Q.SPECL [`bb`, `bb'`, `fuel`, `ctx`, `s`]
       block_body_full_equiv_gen) >>
     simp[Abbr `bb'`] >>
     impl_tac >- (
       rpt conj_tac
       >- (rpt strip_tac >> metis_tac[dft_block_body_from_block])
       >- (irule dft_block_body_choose_perm >> simp[])
       >> (irule dft_block_body_topo_sorted_mapped_gen >> simp[])) >>
     simp[]) >>
  pop_assum strip_assume_tac
  >- (irule exec_block_body_error_lift >> simp[]) >>
  Cases_on `run_insts fuel ctx (block_body bb) s` >> fs[]
  >- (`exec_block fuel ctx bb (s with vs_inst_idx := q) =
       exec_block fuel ctx bb' (s with vs_inst_idx := q)` by
        (irule exec_block_same_body_ok >> simp[] >>
         qexists_tac `v` >> simp[]) >>
      gvs[] >> irule (SRULE [] lift_result_refl_proof) >>
      simp[state_equiv_refl, execution_equiv_refl, revert_equiv_def]) >>
  irule exec_block_body_non_ok_lift >> simp[] >>
  rpt strip_tac >> gvs[]
QED

Triviality dft_block_exec_block_run_insts_pseudo_suffix_lift[local]:
  !bb order p q fuel ctx s suffix.
    pseudos_prefix bb /\ p <= q /\
    p = phi_prefix_length bb.bb_instructions /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) /\
    suffix = DROP p (TAKE q bb.bb_instructions) /\
    ~(?v. run_insts fuel ctx suffix s = OK v) ==>
    lift_result (\_ _. T) (execution_equiv {}) revert_equiv
      (run_insts fuel ctx suffix s)
      (exec_block fuel ctx (dft_block order bb) (s with vs_inst_idx := p))
Proof
  rpt strip_tac >>
  `pseudos_prefix (dft_block order bb)` by simp[dft_block_pseudos_prefix] >>
  `q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode)
      (dft_block order bb).bb_instructions)` by simp[dft_block_phis] >>
  `DROP p (TAKE q (dft_block order bb).bb_instructions) = suffix` by
    (qpat_x_assum `suffix = _` (fn th => rewrite_tac[th]) >>
     irule dft_block_same_pseudo_suffix >> simp[]) >>
  qspecl_then [`dft_block order bb`, `p`, `q`, `fuel`, `ctx`, `s`]
    mp_tac exec_block_run_insts_pseudo_suffix_lift >>
  simp[] >>
  impl_tac >- (
    qpat_x_assum `p = phi_prefix_length bb.bb_instructions`
      (fn th => rewrite_tac[GSYM th]) >>
    qpat_x_assum `q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions)`
      (fn th => rewrite_tac[GSYM th]) >>
    qpat_x_assum `DROP p (TAKE q (dft_block order bb).bb_instructions) = suffix`
      (fn th => rewrite_tac[th]) >>
    qpat_x_assum `q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions)`
      (fn th => rewrite_tac[GSYM th]) >>
    qpat_x_assum `suffix = DROP p (TAKE q bb.bb_instructions)`
      (fn th => rewrite_tac[GSYM th]) >>
    simp[] >> metis_tac[]) >>
  qpat_x_assum `DROP p (TAKE q (dft_block order bb).bb_instructions) = suffix`
    (fn th => rewrite_tac[th]) >>
  simp[]
QED

Triviality dft_block_exec_block_lift_gen[local]:
  !bb order p q fuel ctx s.
    bb_well_formed bb /\ pseudos_prefix bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
    p = phi_prefix_length bb.bb_instructions /\
    q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (exec_block fuel ctx bb (s with vs_inst_idx := p))
      (exec_block fuel ctx (dft_block order bb) (s with vs_inst_idx := p))
Proof
  rpt strip_tac >>
  `bb_well_formed (dft_block order bb)` by
    (mp_tac (Q.SPECL [`order`, `bb`] dft_block_well_formed_gen) >> simp[]) >>
  `pseudos_prefix (dft_block order bb)` by simp[dft_block_pseudos_prefix] >>
  `q = LENGTH (FILTER (\i. is_pseudo i.inst_opcode)
      (dft_block order bb).bb_instructions)` by simp[dft_block_phis] >>
  `p <= q` by (
    qpat_x_assum `p = phi_prefix_length bb.bb_instructions` (fn th => rewrite_tac[th]) >>
    qpat_x_assum `q = LENGTH (FILTER _ bb.bb_instructions)` (fn th => rewrite_tac[th]) >>
    `phi_prefix_length (FILTER (\i. is_pseudo i.inst_opcode) bb.bb_instructions) =
     phi_prefix_length bb.bb_instructions` by
      (irule phi_prefix_length_filter_pseudo >> fs[bb_well_formed_def]) >>
    pop_assum (fn th => rewrite_tac[GSYM th]) >>
    simp[venomExecProofsTheory.phi_prefix_length_le]) >>
  qabbrev_tac `suffix = DROP p (TAKE q bb.bb_instructions)` >>
  `DROP p (TAKE q (dft_block order bb).bb_instructions) = suffix` by
    (qunabbrev_tac `suffix` >> irule dft_block_same_pseudo_suffix >> simp[]) >>
  Cases_on `run_insts fuel ctx suffix s`
  >- (rename1 `run_insts _ _ suffix _ = OK s_after` >>
      `exec_block fuel ctx bb (s with vs_inst_idx := p) =
       exec_block fuel ctx bb (s_after with vs_inst_idx := q)` by
        (irule exec_block_skip_pseudo_suffix >> simp[Abbr `suffix`]) >>
      `exec_block fuel ctx (dft_block order bb) (s with vs_inst_idx := p) =
       exec_block fuel ctx (dft_block order bb) (s_after with vs_inst_idx := q)` by
        (irule exec_block_skip_pseudo_suffix >> simp[] >>
         qexists_tac `s_after` >> simp[]) >>
      gvs[] >> irule dft_block_exec_block_same_body_lift_gen >> simp[]) >>
  `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
        (run_insts fuel ctx suffix s)
        (exec_block fuel ctx bb (s with vs_inst_idx := p))` by
    (qunabbrev_tac `suffix` >> irule exec_block_run_insts_pseudo_suffix_lift >>
     simp[] >> rpt strip_tac >> gvs[]) >>
  `lift_result (\_ _. T) (execution_equiv {}) revert_equiv
        (run_insts fuel ctx suffix s)
        (exec_block fuel ctx (dft_block order bb) (s with vs_inst_idx := p))` by
    (irule dft_block_exec_block_run_insts_pseudo_suffix_lift >> simp[] >>
     rpt strip_tac >> gvs[]) >>
  qspecl_then [`run_insts fuel ctx suffix s`,
    `exec_block fuel ctx bb (s with vs_inst_idx := p)`,
    `exec_block fuel ctx (dft_block order bb) (s with vs_inst_idx := p)`]
    mp_tac lift_result_same_non_ok_trans >>
  simp[] >> disch_then irule >> simp[]
QED

Triviality dft_block_run_block_lift_gen[local]:
  !bb order fuel ctx s.
    bb_well_formed bb /\ pseudos_prefix bb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
    non_pseudo_defs_before_uses bb.bb_instructions /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_block fuel ctx bb s)
      (run_block fuel ctx (dft_block order bb) s)
Proof
  rpt strip_tac >>
  drule_all dft_block_same_phi_prefix >> strip_tac >>
  `eval_phis s (dft_block order bb).bb_instructions =
   eval_phis s bb.bb_instructions` by
    (irule venomExecProofsTheory.eval_phis_same_phi_prefix >> simp[] >>
     metis_tac[]) >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`]
    eval_phis_ok_or_error_defs)
  >- (first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >>
      `eval_phis s (dft_block order bb).bb_instructions = OK s_phi` by metis_tac[] >>
      ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
      irule dft_block_exec_block_lift_gen >> simp[]) >>
  first_x_assum (qx_choose_then `e` strip_assume_tac) >>
  `eval_phis s (dft_block order bb).bb_instructions = Error e` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_block_def] >> simp[lift_result_def]
QED

Triviality dft_block_run_block_lift[local]:
  !fn bb order fuel ctx s.
    wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\ pseudos_prefix bb ==>
    (((?e. run_block fuel ctx bb s = Error e) /\
      (?e. run_block fuel ctx (dft_block order bb) s = Error e)) \/
     lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
       (run_block fuel ctx bb s)
       (run_block fuel ctx (dft_block order bb) s))
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`, `bb`, `dft_block order bb`, `fuel`, `ctx`, `s`]
    block_perm_of_run_block_lift) >>
  impl_tac >- (
    simp[] >>
    rpt conj_tac
    >- (mp_tac (Q.SPECL [`order`, `fn`, `bb`] dft_block_preserves_perm_of) >>
        simp[] >>
        impl_tac >- (rpt conj_tac
          >- (irule original_block_perm_of >> simp[])
          >- (gvs[wf_function_def, EVERY_MEM])
          >- (irule wf_fn_block_inst_ids_distinct >> metis_tac[])
          >> (simp[non_pseudo_defs_before_uses_def] >>
              irule defs_before_implies_np >>
              irule wf_ssa_defs_before_uses >> metis_tac[])) >>
        simp[])
    >- (gvs[wf_function_def, EVERY_MEM])
    >- (mp_tac (Q.SPECL [`fn`, `order`, `bb`] dft_block_well_formed) >> simp[])
    >- (irule dft_block_pseudos_prefix >> simp[])
    >> (mp_tac (Q.SPECL [`fn`, `bb`, `order`] dft_block_body_topo_sorted_mapped) >>
        simp[])) >>
  simp[]
QED

Triviality error_or_lift_trans[local]:
  !r1 r2 r3.
    (((?e. r1 = Error e) /\ (?e. r2 = Error e)) \/
     lift_result (state_equiv {}) (execution_equiv {}) revert_equiv r1 r2) /\
    (((?e. r2 = Error e) /\ (?e. r3 = Error e)) \/
     lift_result (state_equiv {}) (execution_equiv {}) revert_equiv r2 r3) ==>
    (((?e. r1 = Error e) /\ (?e. r3 = Error e)) \/
     lift_result (state_equiv {}) (execution_equiv {}) revert_equiv r1 r3)
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  gvs[lift_result_def, revert_equiv_def] >>
  metis_tac[state_equiv_trans, execution_equiv_trans]
QED

Triviality dft_process_one_pseudos_prefix[local]:
  !cfg lr fn st lbl.
    (!bb. MEM bb st.dls_blocks ==> pseudos_prefix bb) ==>
    !bb. MEM bb (FST (dft_process_one cfg lr fn st lbl)).dls_blocks ==>
         pseudos_prefix bb
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `MEM bb _` mp_tac >>
  simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  TRY (Cases_on `so_analyze_block cfg lr st.dls_from_to lbl x.bb_instructions` >> simp[] >>
       Cases_on `so_get_stack cfg lr (fn with fn_blocks := st.dls_blocks)
         (so_record_from_to cfg st.dls_from_to lbl q) lbl` >> simp[] >>
       BasicProvers.TOP_CASE_TAC >> simp[] >>
       gvs[MEM_MAP] >> metis_tac[dft_block_pseudos_prefix] >> NO_TAC) >>
  metis_tac[]
QED

Triviality dft_loop_step_pseudos_prefix[local]:
  !cfg lr fn trip.
    (!bb. MEM bb (FST trip).dls_blocks ==> pseudos_prefix bb) ==>
    !bb. MEM bb (FST (dft_loop_step cfg lr fn trip)).dls_blocks ==>
         pseudos_prefix bb
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def] >>
  IF_CASES_TAC >> simp[] >>
  TRY (Cases_on `trip1` >> simp[] >>
       TRY (rpt strip_tac >>
            `!bb. MEM bb (FST (dft_process_one cfg lr fn trip0 h)).dls_blocks ==>
                  pseudos_prefix bb` by
              (mp_tac (Q.SPECL [`cfg`, `lr`, `fn`, `trip0`, `h`]
                 dft_process_one_pseudos_prefix) >> simp[]) >>
            Cases_on `dft_process_one cfg lr fn trip0 h` >>
            Cases_on `r` >> Cases_on `q'` >>
            gvs[] >> metis_tac[] >> NO_TAC) >>
       metis_tac[] >> NO_TAC) >>
  metis_tac[]
QED

Triviality funpow_dft_loop_pseudos_prefix[local]:
  !n cfg lr fn trip.
    (!bb. MEM bb (FST trip).dls_blocks ==> pseudos_prefix bb) ==>
    !bb. MEM bb (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks ==>
         pseudos_prefix bb
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  qabbrev_tac `tripn = FUNPOW (dft_loop_step cfg lr fn) n trip` >>
  `!bb. MEM bb (FST tripn).dls_blocks ==> pseudos_prefix bb` by
    (qunabbrev_tac `tripn` >>
     qpat_x_assum `!cfg lr fn trip. _`
       (qspecl_then [`cfg`, `lr`, `fn`, `trip`] mp_tac) >>
     simp[]) >>
  mp_tac (Q.SPECL [`cfg`, `lr`, `fn`, `tripn`]
    dft_loop_step_pseudos_prefix) >>
  simp[] >> disch_then (qspec_then `bb` mp_tac) >> simp[Abbr `tripn`]
QED

Triviality dft_fn_pseudos_prefix:
  !fn. fn_pseudos_prefix fn ==> fn_pseudos_prefix (dft_fn fn)
Proof
  rw[dft_fn_def, fn_pseudos_prefix_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qabbrev_tac `steps = LENGTH fn.fn_blocks * LENGTH fn.fn_blocks` >>
  qabbrev_tac `trip = (<|dls_blocks := fn.fn_blocks; dls_from_to := FEMPTY;
                         dls_last_order := FEMPTY|>,
                       (cfg_analyze fn).cfg_dfs_post,F)` >>
  qabbrev_tac `res = FUNPOW (dft_loop_step (cfg_analyze fn)
      (liveness_analyze fn) fn) steps trip` >>
  `!bb. MEM bb (FST res).dls_blocks ==> pseudos_prefix bb` by
    (qunabbrev_tac `res` >>
     mp_tac (Q.SPECL [`steps`, `cfg_analyze fn`, `liveness_analyze fn`, `fn`, `trip`]
       funpow_dft_loop_pseudos_prefix) >>
     simp[Abbr `trip`, Abbr `steps`, fn_pseudos_prefix_def]) >>
  PairCases_on `res` >> gvs[]
QED

Definition run_block_compare_def:
  run_block_compare bb bb' <=>
    !fuel ctx s.
      (((?e. run_block fuel ctx bb s = Error e) /\
        (?e. run_block fuel ctx bb' s = Error e)) \/
       lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
         (run_block fuel ctx bb s)
         (run_block fuel ctx bb' s))
End

Definition all_blocks_run_rel_def:
  all_blocks_run_rel fn bbs <=>
    !bb bb'.
      MEM bb fn.fn_blocks /\ MEM bb' bbs /\
      bb.bb_label = bb'.bb_label ==>
      run_block_compare bb bb'
End

Triviality initial_all_blocks_run_rel[local]:
  !fn. wf_function fn ==> all_blocks_run_rel fn fn.fn_blocks
Proof
  rw[all_blocks_run_rel_def, run_block_compare_def] >>
  `bb = bb'` by (irule wf_fn_same_label_eq >> metis_tac[]) >>
  gvs[] >> disj2_tac >>
  irule (SRULE [] lift_result_refl_proof) >>
  simp[state_equiv_refl, execution_equiv_refl, revert_equiv_def]
QED

Triviality dft_process_one_preserves_run_rel[local]:
  !cfg lr fn st lbl.
    all_blocks_run_rel fn st.dls_blocks /\
    dft_inv st.dls_blocks /\
    (!bb. MEM bb st.dls_blocks ==> pseudos_prefix bb) ==>
    all_blocks_run_rel fn (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  rpt gen_tac >> strip_tac >>
  simp[all_blocks_run_rel_def, run_block_compare_def] >>
  rpt strip_tac >>
  qpat_x_assum `MEM bb' _` mp_tac >>
  simp[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[]
  >- (strip_tac >>
      qpat_x_assum `all_blocks_run_rel _ _` mp_tac >>
      simp[all_blocks_run_rel_def, run_block_compare_def] >>
      disch_then (qspecl_then [`bb`, `bb'`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  rename1 `lookup_block lbl st.dls_blocks = SOME cur` >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
  >- (strip_tac >>
      qpat_x_assum `all_blocks_run_rel _ _` mp_tac >>
      simp[all_blocks_run_rel_def, run_block_compare_def] >>
      disch_then (qspecl_then [`bb`, `bb'`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  simp[MEM_MAP] >> strip_tac >> gvs[] >>
  rename1 `MEM b st.dls_blocks` >>
  Cases_on `b.bb_label = lbl` >> gvs[]
  >- (`MEM cur st.dls_blocks` by
        (fs[lookup_block_def] >> imp_res_tac venomExecPropsTheory.FIND_MEM) >>
      `(((?e. run_block fuel ctx bb s = Error e) /\
         (?e. run_block fuel ctx cur s = Error e)) \/
        lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
          (run_block fuel ctx bb s)
          (run_block fuel ctx cur s))` by
        (qpat_x_assum `all_blocks_run_rel _ _` mp_tac >>
         simp[all_blocks_run_rel_def, run_block_compare_def] >>
         disch_then (qspecl_then [`bb`, `cur`, `fuel`, `ctx`, `s`] mp_tac) >>
         simp[]) >>
      `bb_well_formed cur /\
       ALL_DISTINCT (MAP (\i. i.inst_id) cur.bb_instructions) /\
       non_pseudo_defs_before_uses cur.bb_instructions /\
       ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) cur.bb_instructions))` by
        (qpat_x_assum `dft_inv _` mp_tac >> simp[dft_inv_def, EVERY_MEM] >>
         metis_tac[]) >>
      `pseudos_prefix cur` by metis_tac[] >>
      `lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
        (run_block fuel ctx cur s)
        (run_block fuel ctx (dft_block (REVERSE order) cur) s)` by
        (irule dft_block_run_block_lift_gen >> simp[]) >>
      qspecl_then [`run_block fuel ctx bb s`, `run_block fuel ctx cur s`,
                   `run_block fuel ctx (dft_block (REVERSE order) cur) s`]
        mp_tac error_or_lift_trans >> simp[]) >>
  qpat_x_assum `all_blocks_run_rel _ _` mp_tac >>
  simp[all_blocks_run_rel_def, run_block_compare_def] >>
  disch_then (qspecl_then [`bb`, `b`, `fuel`, `ctx`, `s`] mp_tac) >>
  simp[]
QED

Triviality dft_loop_step_preserves_run_rel[local]:
  !cfg lr fn trip.
    all_blocks_run_rel fn (FST trip).dls_blocks /\
    dft_inv (FST trip).dls_blocks /\
    (!bb. MEM bb (FST trip).dls_blocks ==> pseudos_prefix bb) ==>
    all_blocks_run_rel fn (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >>
  Cases_on `r` >> simp[] >>
  qspecl_then [`cfg`, `lr`, `fn`, `trip0`, `h`]
    mp_tac dft_process_one_preserves_run_rel >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Triviality funpow_dft_loop_preserves_run_rel[local]:
  !n cfg lr fn trip.
    all_blocks_run_rel fn (FST trip).dls_blocks /\
    dft_inv (FST trip).dls_blocks /\
    (!bb. MEM bb (FST trip).dls_blocks ==> pseudos_prefix bb) ==>
    all_blocks_run_rel fn
      (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  irule dft_loop_step_preserves_run_rel >>
  rpt conj_tac
  >- (mp_tac (Q.SPECL [`n`, `cfg`, `lr`, `fn`, `trip`]
        funpow_dft_loop_pseudos_prefix) >> simp[])
  >- (mp_tac (Q.SPECL [`n`, `cfg`, `lr`, `fn`, `trip`]
        funpow_dft_loop_preserves_inv) >> simp[])
  >> (first_x_assum irule >> simp[])
QED

Triviality dft_fn_all_run_rel[local]:
  !fn.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
    all_blocks_run_rel fn (dft_fn fn).fn_blocks
Proof
  rpt strip_tac >> simp[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[] >>
  irule funpow_dft_loop_preserves_run_rel >>
  simp[initial_all_blocks_run_rel] >>
  conj_tac >- gvs[fn_pseudos_prefix_def] >>
  irule wf_fn_initial_dft_inv >> simp[]
QED

(* run_blocks with DFT-transformed blocks produces lift_result-equivalent
   results. Fuel induction on run_blocks. *)
Theorem dft_fn_run_blocks_lift:
  !fuel ctx fn s.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dft_fn fn) s)
Proof
  Induct_on `fuel`
  >- simp[Ntimes run_blocks_def 2, lift_result_def]
  >> rpt strip_tac >>
     simp[Once run_blocks_unfold] >>
     simp[Once run_blocks_unfold] >>
     Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
  (* NONE case: block not found in fn *)
  >- (`lookup_block s.vs_current_bb (dft_fn fn).fn_blocks = NONE` by
        (irule dft_fn_lookup_block_none >> simp[]) >>
      simp[lift_result_def])
  (* SOME x case: block found in fn *)
  >> rename1 `SOME bb` >>
     `?bb'. lookup_block s.vs_current_bb (dft_fn fn).fn_blocks = SOME bb'` by
       (irule dft_fn_lookup_block >> metis_tac[]) >>
     simp[] >>
     (* Get MEM bb, block_perm_of bb', bb_well_formed bb' *)
     `MEM bb fn.fn_blocks` by
       (fs[lookup_block_def] >> imp_res_tac venomExecPropsTheory.FIND_MEM) >>
     `bb.bb_label = bb'.bb_label` by
       (fs[lookup_block_def] >>
        imp_res_tac venomExecPropsTheory.FIND_P >> gvs[]) >>
     `block_perm_of fn bb'` by
       (irule dft_fn_lookup_perm_of >> metis_tac[]) >>
     `MEM bb' (dft_fn fn).fn_blocks` by
       (fs[lookup_block_def] >> imp_res_tac venomExecPropsTheory.FIND_MEM) >>
     `bb_well_formed bb'` by
       (irule dft_fn_blocks_well_formed >> metis_tac[]) >>
     `pseudos_prefix bb` by
       (gvs[fn_pseudos_prefix_def]) >>
     `pseudos_prefix bb'` by
       (`fn_pseudos_prefix (dft_fn fn)` by
          (irule dft_fn_pseudos_prefix >> simp[]) >>
        gvs[fn_pseudos_prefix_def]) >>
     `((?e. run_block fuel ctx bb s = Error e) /\
       (?e. run_block fuel ctx bb' s = Error e)) \/
      lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
        (run_block fuel ctx bb s)
        (run_block fuel ctx bb' s)` by
       (`all_blocks_run_rel fn (dft_fn fn).fn_blocks` by
          (irule dft_fn_all_run_rel >> simp[]) >>
        qpat_x_assum `all_blocks_run_rel _ _` mp_tac >>
        simp[all_blocks_run_rel_def, run_block_compare_def] >>
        disch_then (qspecl_then [`bb`, `bb'`, `fuel`, `ctx`, `s`] mp_tac) >>
        simp[]) >>
     gvs[] >>
     TRY (simp[lift_result_def] >> NO_TAC) >>
     Cases_on `run_block fuel ctx bb s` >>
     Cases_on `run_block fuel ctx bb' s` >>
     gvs[lift_result_def, execution_equiv_def, revert_equiv_def] >>
     imp_res_tac state_equiv_empty_eq >> gvs[] >>
     IF_CASES_TAC >> gvs[lift_result_def, execution_equiv_def] >>
     qpat_x_assum `!ctx fn' s'. wf_ssa fn' /\ _ ==> _`
       (qspecl_then [`ctx`, `fn`, `v`] mp_tac) >>
     simp[] >>
     disch_then irule >>
     simp[]
QED

(* ===== Function-level: run_function lift_result ===== *)

Triviality dft_fn_run_function_lift:
  !fuel ctx fn s.
    wf_ssa fn /\ wf_function fn /\ fn_pseudos_prefix fn /\
    s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    lift_result (state_equiv {}) (execution_equiv {}) revert_equiv
      (run_function fuel ctx fn s)
      (run_function fuel ctx (dft_fn fn) s)

Proof
  rpt strip_tac >>
  simp[run_function_def] >>
  `fn_entry_label (dft_fn fn) = fn_entry_label fn` by (
    simp[fn_entry_label_def, entry_block_def] >>
    `~NULL (dft_fn fn).fn_blocks = ~NULL fn.fn_blocks` by (
      `MAP (\b. b.bb_label) (dft_fn fn).fn_blocks =
       MAP (\b. b.bb_label) fn.fn_blocks` by simp[dft_fn_labels_map] >>
      Cases_on `fn.fn_blocks` >> Cases_on `(dft_fn fn).fn_blocks` >>
      gvs[]) >>
    Cases_on `NULL fn.fn_blocks` >> simp[] >>
    `MAP (\b. b.bb_label) (dft_fn fn).fn_blocks =
     MAP (\b. b.bb_label) fn.fn_blocks` by simp[dft_fn_labels_map] >>
    Cases_on `fn.fn_blocks` >> Cases_on `(dft_fn fn).fn_blocks` >>
    gvs[]) >>
  simp[] >>
  Cases_on `fn_entry_label fn` >> simp[lift_result_def] >>
  irule dft_fn_run_blocks_lift >> simp[]
QED


Triviality np_defs_gives_earlier_index[local]:
  !l x y v jx iy.
    EL jx l = x /\ jx < LENGTH l /\
    EL iy l = y /\ iy < LENGTH l /\
    x <> y /\
    producing_inst l v = SOME y /\
    non_pseudo_defs_before_uses l /\
    MEM v y.inst_outputs /\
    MEM (Var v) x.inst_operands /\
    ~is_pseudo x.inst_opcode /\
    ALL_DISTINCT (MAP (\i:instruction. i.inst_id) l) ==>
    iy < jx
Proof
  rpt strip_tac >>
  `ALL_DISTINCT l` by metis_tac[ALL_DISTINCT_MAP] >>
  `?i. i < jx /\ EL i l = y` by (
    qpat_assum `non_pseudo_defs_before_uses l`
      (mp_tac o REWRITE_RULE[non_pseudo_defs_before_uses_def, np_defs_before_uses_def]) >>
    simp[] >> metis_tac[]) >>
  `i < LENGTH l` by decide_tac >>
  `i = iy` by metis_tac[EL_ALL_DISTINCT_EL_EQ] >>
  simp[]
QED

Theorem data_dep_preserved_dft_fn:
  !fn bb bb' x y.
    wf_ssa fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    MEM bb' (dft_fn fn).fn_blocks /\
    bb.bb_label = bb'.bb_label /\
    MEM x (block_body bb') /\ MEM y (block_body bb') /\
    x <> y /\
    (?v. MEM (Var v) x.inst_operands /\ MEM v y.inst_outputs) ==>
    ?i j. i < j /\ j < LENGTH (block_body bb') /\
          EL i (block_body bb') = y /\ EL j (block_body bb') = x
Proof
  rpt strip_tac >>
  imp_res_tac dft_fn_dft_inv >>
  fs[dft_inv_def, EVERY_MEM] >>
  first_x_assum (qspec_then `bb'` mp_tac) >> simp[] >> strip_tac >>
  fs[block_body_def, MEM_FILTER] >>
  `producing_inst bb'.bb_instructions v = SOME y` by (
    qspecl_then [`bb'.bb_instructions`, `v`, `y`] mp_tac
      (INST_TYPE [alpha|-> ``:instruction``] producing_inst_unique_definer) >>
    simp[] >> metis_tac[all_distinct_flat_map_unique]) >>
  `?jx. jx < LENGTH bb'.bb_instructions /\ EL jx bb'.bb_instructions = x` by
    metis_tac[MEM_EL] >>
  `?iy. iy < LENGTH bb'.bb_instructions /\ EL iy bb'.bb_instructions = y` by
    metis_tac[MEM_EL] >>
  `iy < jx` by metis_tac[np_defs_gives_earlier_index] >>
  `ALL_DISTINCT bb'.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  qspecl_then
    [`\i:instruction. ~is_pseudo i.inst_opcode /\ ~is_terminator i.inst_opcode`,
     `bb'.bb_instructions`, `iy`, `jx`]
    mp_tac filter_el_mono_rev >>
  simp[GSYM block_body_def]
QED

(* ===== Canonical dependency chain ===== *)

(* MAP_INST_ID_APPEND_SPLIT_exists: if MAP f l = pfx ++ [x] ++ sfx,
   then l = prefix ++ [b] ++ suffix with matching. *)
Triviality MAP_INST_ID_APPEND_SPLIT_exists_local[local]:
  !fl pfx xid sfx.
    MAP (\i. i.inst_id) fl = pfx ++ [xid] ++ sfx ==>
    ?prefix b suffix.
      fl = prefix ++ [b] ++ suffix /\
      MAP (\i. i.inst_id) prefix = pfx /\ b.inst_id = xid /\
      MAP (\i. i.inst_id) suffix = sfx
Proof
  Induct_on `pfx` >> rpt strip_tac
  >- (Cases_on `fl` >> gvs[MAP_EQ_CONS] >>
      qexistsl_tac [`[]`,`h`,`t`] >> simp[])
  >> (Cases_on `fl` >> gvs[MAP_EQ_CONS] >>
      last_x_assum $ qspecl_then [`t`,`xid`,`sfx`] mp_tac >> simp[] >>
      strip_tac >>
      qexistsl_tac [`h'::prefix`,`b`,`suffix`] >> simp[])
QED

(* Replaces the FALSE full_dep version. canonical_dep is WEAKER than full_dep,
   so topo_sorted(canonical_dep) is a WEAKER (easier to prove) property.
   The simulation theorems work with canonical_dep. *)

(* from_block implies in_np_body *)
Theorem from_block_imp_in_np_body_local:
  !bi x. from_block bi x ==> in_np_body bi x
Proof
  simp[from_block_def, in_np_body_def, MEM_MAP, MEM_FILTER, PULL_EXISTS] >>
  metis_tac[flip_operands_inst_id]
QED

(* Bridge: same inst_id in FILTER ~is_pseudo => same is_barrier *)
Triviality is_barrier_from_inst_id_local[local]:
  !bi b x.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    from_block bi x /\ b.inst_id = x.inst_id ==>
    is_barrier b = is_barrier x
Proof
  rpt strip_tac >>
  `MEM b bi` by fs[MEM_FILTER] >>
  fs[from_block_def] >>
  metis_tac[all_distinct_map_mem_inj, flip_operands_is_barrier,
            flip_operands_inst_id]
QED

(* canonical_dep ⊆ full_dep for from_block elements.
   Each disjunct of canonical_dep implies full_dep. *)
Triviality data_dep_body_imp_full_dep_local[local]:
  !bi x y.
    data_dep_body bi x y ==> full_dep (build_full_eda bi) x y
Proof
  rpt strip_tac >> fs[full_dep_def] >> disj2_tac >> disj1_tac >>
  fs[data_dep_body_def, inst_uses_def, inst_defs_def, IN_DISJOINT] >>
  qexists `v` >> fs[MEM_operand_vars_iff]
QED

(* Bridge: from_barrier_dep → eda_dep → full_dep *)
Triviality from_barrier_dep_imp_full_dep_local[local]:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    from_barrier_dep bi x y /\ from_block bi x /\ from_block bi y ==>
    full_dep (build_full_eda bi) x y
Proof
  rpt strip_tac >> fs[from_barrier_dep_def] >>
  simp[full_dep_def] >> disj1_tac >>
  qabbrev_tac `fl = FILTER (\i. ~is_pseudo i.inst_opcode) bi` >>
  `?prefix b suffix. fl = prefix ++ [b] ++ suffix /\
                      MAP (\i. i.inst_id) prefix = pfx /\
                      b.inst_id = x.inst_id /\
                      MAP (\i. i.inst_id) suffix = sfx` by
    (drule MAP_INST_ID_APPEND_SPLIT_exists_local >> simp[]) >>
  `?yb. MEM yb prefix /\ yb.inst_id = y.inst_id` by
    (`MEM y.inst_id (MAP (\i. i.inst_id) prefix)` by simp[] >>
     imp_res_tac MEM_MAP >> metis_tac[]) >>
  `is_barrier b` by
    (`MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by
       (fs[Abbr `fl`, MEM_APPEND] >> metis_tac[]) >>
     metis_tac[is_barrier_from_inst_id_local]) >>
  `eda_dep (build_full_eda bi) b yb` by
    (qunabbrev_tac `fl` >>
     match_mp_tac from_barrier_to_eda_dep >>
     qexistsl_tac [`prefix`, `suffix`] >> simp[]) >>
  metis_tac[eda_dep_inst_id_only]
QED

(* Bridge: on_barrier_dep → eda_dep → full_dep *)
Triviality on_barrier_dep_imp_full_dep_local[local]:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    on_barrier_dep bi x y /\ from_block bi x /\ from_block bi y ==>
    full_dep (build_full_eda bi) x y
Proof
  rpt strip_tac >> fs[on_barrier_dep_def] >>
  simp[full_dep_def] >> disj1_tac >>
  qabbrev_tac `b_last = LAST (FILTER is_barrier pfx)` >>
  `MEM mid (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by
    (qpat_x_assum `FILTER _ _ = _` (fn th => rewrite_tac[th]) >>
     simp[MEM_APPEND]) >>
  `is_barrier mid = is_barrier x` by
    metis_tac[is_barrier_from_inst_id_local] >>
  `~is_barrier mid` by metis_tac[] >>
  `b_last.inst_id = y.inst_id` by fs[Abbr `b_last`] >>
  `eda_dep (build_full_eda bi) mid b_last` by
    (match_mp_tac on_barrier_to_eda_dep >>
     qexistsl_tac [`pfx`, `sfx`] >> simp[] >>
     Cases_on `FILTER is_barrier pfx` >> fs[Abbr `b_last`]) >>
  metis_tac[eda_dep_inst_id_only]
QED

(* Main bridge: canonical_dep ⊆ full_dep for from_block elements *)
Theorem canonical_dep_imp_full_dep_local:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    canonical_dep bi x y /\
    from_block bi x /\ from_block bi y ==>
    full_dep (build_full_eda bi) x y
Proof
  rpt strip_tac >> fs[canonical_dep_def, in_np_body_def] >-
  metis_tac[data_dep_body_imp_full_dep_local] >-
  metis_tac[from_barrier_dep_imp_full_dep_local] >>
  metis_tac[on_barrier_dep_imp_full_dep_local]
QED

(* topo_sorted weakens when deps shrink *)
Triviality topo_sorted_mono_restricted_local[local]:
  !dep1 dep2 l.
    (!x y. MEM x l /\ MEM y l /\ dep2 x y ==> dep1 x y) /\
    topo_sorted dep1 l ==>
    topo_sorted dep2 l
Proof
  rw[topo_sorted_def] >> rpt strip_tac >>
  `i < LENGTH l` by decide_tac >> imp_res_tac EL_MEM >> metis_tac[]
QED

(* fn_insts_blocks distributes over APPEND *)
Triviality fn_insts_blocks_APPEND_local[local]:
  !l1 l2. fn_insts_blocks (l1 ++ l2) = fn_insts_blocks l1 ++ fn_insts_blocks l2
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* SSA: per-block outputs are distinct.
   Proof by induction on blocks: ALL_DISTINCT(FLAT(MAP outputs blocks))
   means each block's output list is a component of a distinct append. *)
Triviality ssa_block_outputs_distinct_local[local]:
  !bbs bb.
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs))) /\
    MEM bb bbs ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  Induct >> simp[fn_insts_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `bb = h` >> gvs[] >>
  fs[ALL_DISTINCT_APPEND]
QED

(* MEM in FILTER implies in_np_body *)
Triviality mem_filter_in_np_body_local[local]:
  !bi x. MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi) ==> in_np_body bi x
Proof
  simp[in_np_body_def, MEM_MAP, MEM_FILTER, PULL_EXISTS] >> metis_tac[]
QED

(* Original block's non-pseudo filter is topo_sorted(canonical_dep).
   Direct proof: in program order, no earlier instruction can depend on
   a later one via canonical_dep (data deps need def before use,
   barrier deps need barrier first). Contrapositive of topo_sorted. *)
Triviality orig_filter_canonical_topo_sorted_local[local]:
  !fn bb. wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\ bb_well_formed bb ==>
    topo_sorted (canonical_dep bb.bb_instructions)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)
Proof
  simp[topo_sorted_def] >> rpt strip_tac >>
  qabbrev_tac `bi = bb.bb_instructions` >>
  qabbrev_tac `fl = FILTER (\i. ~is_pseudo i.inst_opcode) bi` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bi)` by metis_tac[wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) fl)` by metis_tac[all_distinct_map_filter] >>
  `defs_before_uses bi` by metis_tac[wf_ssa_defs_before_uses] >>
  `MEM (EL i fl) fl` by (irule EL_MEM >> decide_tac) >>
  `MEM (EL j fl) fl` by metis_tac[EL_MEM] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi))` by
    metis_tac[ssa_block_outputs_distinct_local, fn_insts_def, ssa_form_def, wf_ssa_def] >>
  `in_np_body bi (EL i fl) /\ in_np_body bi (EL j fl)` by
    metis_tac[mem_filter_in_np_body_local] >>
  Cases_on `data_dep_body bi (EL i fl) (EL j fl)`
  >- (fs[data_dep_body_def] >> metis_tac[orig_data_dep_contra_filtered]) >>
  Cases_on `from_barrier_dep bi (EL i fl) (EL j fl)`
  >- (`is_barrier (EL i fl)` by metis_tac[from_barrier_dep_def] >>
      metis_tac[orig_from_barrier_contra]) >>
  `on_barrier_dep bi (EL i fl) (EL j fl)` by metis_tac[canonical_dep_def] >>
  `~is_barrier (EL i fl) /\ is_barrier (EL j fl)` by metis_tac[on_barrier_dep_def] >>
  metis_tac[orig_on_barrier_contra]
QED

(* ===== canonical_topo_inv for dft_fn loop ===== *)

Definition canonical_topo_inv_def:
  canonical_topo_inv fn blocks <=>
    !bb. MEM bb blocks ==>
      ?bb_orig. MEM bb_orig fn.fn_blocks /\
        bb.bb_label = bb_orig.bb_label /\
        topo_sorted (canonical_dep bb_orig.bb_instructions)
          (FILTER (\i. ~is_pseudo i.inst_opcode) bb.bb_instructions)
End

Triviality wf_fn_initial_canonical_topo_local[local]:
  !fn. wf_ssa fn /\ wf_function fn ==> canonical_topo_inv fn fn.fn_blocks
Proof
  simp[canonical_topo_inv_def] >> rpt strip_tac >>
  qexists_tac `bb` >> simp[] >>
  irule orig_filter_canonical_topo_sorted_local >>
  fs[wf_function_def] >> metis_tac[]
QED

(* dft_block output satisfies canonical_topo_inv for a single block *)
(* ===== block_perm_of_inst_outputs_distinct helpers ===== *)

(* Two from_block elements with same inst_id have same inst_outputs *)
Triviality from_block_same_inst_id_outputs_early[local]:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    from_block bi x /\ from_block bi y /\ x.inst_id = y.inst_id ==>
    x.inst_outputs = y.inst_outputs
Proof
  rw[from_block_def] >>
  metis_tac[all_distinct_map_mem_inj, flip_operands_inst_outputs,
            flip_operands_inst_id]
QED

(* Two from_block elements with same inst_id have same operand_vars set *)
Triviality from_block_same_inst_id_operand_vars_local[local]:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    from_block bi x /\ from_block bi y /\ x.inst_id = y.inst_id ==>
    set (operand_vars x.inst_operands) = set (operand_vars y.inst_operands)
Proof
  rw[from_block_def] >>
  metis_tac[all_distinct_map_mem_inj, flip_operands_operand_vars_set,
            flip_operands_inst_id]
QED

(* Two from_block elements with same inst_id have same is_barrier *)
Triviality from_block_same_inst_id_barrier_local[local]:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    from_block bi x /\ from_block bi y /\ x.inst_id = y.inst_id ==>
    (is_barrier x <=> is_barrier y)
Proof
  rw[from_block_def] >>
  metis_tac[all_distinct_map_mem_inj, flip_operands_is_barrier,
            flip_operands_inst_id]
QED

(* PERM on inst_id + from_block gives PERM on inst_outputs *)
Triviality PERM_inst_id_inst_outputs_perm_local[local]:
  !np_cur np_orig orig_bi.
    EVERY (\i. from_block orig_bi i) np_cur /\
    EVERY (\i. from_block orig_bi i) np_orig /\
    PERM (MAP (\i. i.inst_id) np_cur) (MAP (\i. i.inst_id) np_orig) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) np_cur) ==>
    PERM (MAP (\i. i.inst_outputs) np_cur) (MAP (\i. i.inst_outputs) np_orig)
Proof
  rpt strip_tac >>
  `∀x y:instruction.
      MEM x np_cur ∧ MEM y np_orig ∧ x.inst_id = y.inst_id ⇒
      x.inst_outputs = y.inst_outputs` by (
    rpt strip_tac >>
    qspecl_then [`orig_bi`, `x`, `y`] mp_tac from_block_same_inst_id_outputs_early >>
    fs[EVERY_MEM]) >>
  irule PERM_TRANSFER_inst_id_inst_outputs >>
  simp[]
QED

(* block_perm_of preserves ALL_DISTINCT of FLAT (MAP inst_outputs) *)
Triviality block_perm_of_inst_outputs_distinct_local[local]:
  !fn bb_orig bb_cur.
    wf_ssa fn /\ wf_function fn /\
    MEM bb_orig fn.fn_blocks /\
    block_perm_of fn bb_cur /\
    bb_cur.bb_label = bb_orig.bb_label ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb_cur.bb_instructions))
Proof
  rpt strip_tac >>
  qpat_x_assum `block_perm_of fn bb_cur` (mp_tac o REWRITE_RULE [block_perm_of_def]) >>
  strip_tac >>
  `bb_orig' = bb_orig` by
    metis_tac[all_distinct_map_mem_inj, fn_labels_def, wf_function_def] >>
  fs[] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb_orig.bb_instructions))` by
    metis_tac[ssa_block_outputs_distinct_local, fn_insts_def, ssa_form_def, wf_ssa_def] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb_orig.bb_instructions)` by
    metis_tac[wf_fn_block_inst_ids_distinct] >>
  (* Key: PERM of MAP inst_outputs for non-pseudos *)
  qspecl_then [`FILTER (\i. ~is_pseudo i.inst_opcode) bb_cur.bb_instructions`,
                `FILTER (\i. ~is_pseudo i.inst_opcode) bb_orig.bb_instructions`,
                `bb_orig.bb_instructions`] mp_tac
    PERM_inst_id_inst_outputs_perm_local >>
  impl_keep_tac >- (
    conj_tac >- fs[EVERY_MEM, MEM_FILTER] >>
    conj_tac >- (simp[EVERY_MEM, MEM_FILTER, from_block_def] >> metis_tac[]) >>
    conj_tac >- fs[] >>
    conj_tac >- metis_tac[wf_fn_block_inst_ids_distinct] >>
    metis_tac[all_distinct_map_filter, ALL_DISTINCT_PERM]) >>
  strip_tac >>
  (* Full list PERM via PERM_SPLIT + PERM_MAP + PERM_CONG *)
  `PERM (MAP (\i. i.inst_outputs) bb_cur.bb_instructions)
        (MAP (\i. i.inst_outputs)
          (FILTER (\i. is_pseudo i.inst_opcode) bb_cur.bb_instructions ++
           FILTER (\i. ~is_pseudo i.inst_opcode) bb_cur.bb_instructions))` by
    metis_tac[PERM_MAP, PERM_SPLIT] >>
  `PERM (MAP (\i. i.inst_outputs) bb_orig.bb_instructions)
        (MAP (\i. i.inst_outputs)
          (FILTER (\i. is_pseudo i.inst_opcode) bb_orig.bb_instructions ++
           FILTER (\i. ~is_pseudo i.inst_opcode) bb_orig.bb_instructions))` by
    metis_tac[PERM_MAP, PERM_SPLIT] >>
  `MAP (\i. i.inst_outputs)
      (FILTER (\i. is_pseudo i.inst_opcode) bb_cur.bb_instructions ++
       FILTER (\i. ~is_pseudo i.inst_opcode) bb_cur.bb_instructions) =
   MAP (\i. i.inst_outputs)
      (FILTER (\i. is_pseudo i.inst_opcode) bb_cur.bb_instructions) ++
   MAP (\i. i.inst_outputs)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb_cur.bb_instructions)` by
    simp[MAP_APPEND] >>
  `MAP (\i. i.inst_outputs)
      (FILTER (\i. is_pseudo i.inst_opcode) bb_orig.bb_instructions ++
       FILTER (\i. ~is_pseudo i.inst_opcode) bb_orig.bb_instructions) =
   MAP (\i. i.inst_outputs)
      (FILTER (\i. is_pseudo i.inst_opcode) bb_orig.bb_instructions) ++
   MAP (\i. i.inst_outputs)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb_orig.bb_instructions)` by
    simp[MAP_APPEND] >>
  `PERM (MAP (\i. i.inst_outputs)
      (FILTER (\i. is_pseudo i.inst_opcode) bb_cur.bb_instructions))
   (MAP (\i. i.inst_outputs)
      (FILTER (\i. is_pseudo i.inst_opcode) bb_orig.bb_instructions))` by
    simp[PERM_REFL] >>
  `PERM (MAP (\i. i.inst_outputs)
      (FILTER (\i. is_pseudo i.inst_opcode) bb_cur.bb_instructions) ++
   MAP (\i. i.inst_outputs)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb_cur.bb_instructions))
   (MAP (\i. i.inst_outputs)
      (FILTER (\i. is_pseudo i.inst_opcode) bb_orig.bb_instructions) ++
   MAP (\i. i.inst_outputs)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb_orig.bb_instructions))` by
    metis_tac[PERM_CONG] >>
  `PERM (MAP (\i. i.inst_outputs) bb_cur.bb_instructions)
        (MAP (\i. i.inst_outputs) bb_orig.bb_instructions)` by
    metis_tac[PERM_TRANS, PERM_SYM] >>
  `PERM (FLAT (MAP (\i. i.inst_outputs) bb_cur.bb_instructions))
        (FLAT (MAP (\i. i.inst_outputs) bb_orig.bb_instructions))` by
    metis_tac[PERM_FLAT] >>
  metis_tac[ALL_DISTINCT_PERM]
QED

(* dft_block output satisfies canonical_topo_inv for a single block *)
(* Helper: from_block transfers from cur_bi to orig_bi via block_perm_of *)
Triviality from_block_sched_via_perm_of[local]:
  !fn bb_orig bb_cur x.
    wf_function fn /\
    MEM bb_orig fn.fn_blocks /\
    block_perm_of fn bb_cur /\
    bb_cur.bb_label = bb_orig.bb_label /\
    from_block bb_cur.bb_instructions x ==>
    from_block bb_orig.bb_instructions x
Proof
  rpt strip_tac >>
  qpat_x_assum `block_perm_of fn bb_cur` mp_tac >>
  simp[block_perm_of_def] >> strip_tac >>
  `bb_orig' = bb_orig` by
    metis_tac[all_distinct_map_mem_inj, fn_labels_def, wf_function_def] >>
  fs[] >>
  match_mp_tac from_block_trans >>
  qexists_tac `bb_cur.bb_instructions` >> simp[] >>
  rpt strip_tac >>
  fs[EVERY_MEM, MEM_FILTER] >>
  metis_tac[]
QED

(* FILTER: non-pseudo filter of (pseudos ++ non-pseudos) = non-pseudos *)
Triviality filter_nonpseudo_pseudo_append[local]:
  !P l1 l2.
    FILTER P l1 = [] /\ FILTER P l2 = l2 ==>
    FILTER P (l1 ++ l2) = l2
Proof
  once_rewrite_tac[FILTER_APPEND_DISTRIB] >> simp[]
QED

(* Bridge: canonical_dep orig_bi ⊆ TC (full_dep cur_eda) for elements in cur.
   This is the key lemma enabling the topo-sorted proof.
   For data_dep_body: uses/defs overlap → full_dep directly (structural).
   For from_barrier_dep: barrier x after y in orig. By IH topo_sorted, y
     before x in cur's non-pseudo ordering. from_barrier_to_eda_dep on cur_bi
     gives eda_dep → full_dep → TC full_dep.
   For on_barrier_dep: last barrier y before x in orig. In cur, y is before
     x (by IH). Let b_last = last barrier before x in cur. on_barrier_to_eda_dep
     gives full_dep x b_last. If b_last = y, done. If not, y is a barrier
     before b_last in cur (since b_last is LAST barrier, y ∈ barriers, y≠b_last).
     from_barrier_to_eda_dep gives full_dep b_last y. TC chains: x→b_last→y. *)

(* Helper: topo_sorted D l ⟹ if D a b and a ≠ b, then a appears after b in l.
   Because: if a at position i, b at position j, and i < j, then D (EL i l) (EL j l) = D a b
   contradicts ~D (EL i l) (EL j l). If i = j then a = b (same position), contradicting a ≠ b.
   So i > j, meaning a appears after b. *)
Triviality topo_sorted_dep_after_local[local]:
  !dep l a b i j.
    topo_sorted dep l /\ dep a b /\ a <> b /\
    i < LENGTH l /\ EL i l = a /\
    j < LENGTH l /\ EL j l = b ==>
    j < i
Proof
  rpt strip_tac >> CCONTR_TAC >> `i <= j` by decide_tac >>
  Cases_on `i = j` >- fs[] >>
  `i < j` by decide_tac >>
  fs[topo_sorted_def] >> metis_tac[]
QED

(* from_barrier_dep is irreflexive: if ALL_DISTINCT inst_ids in orig_bi's
   non-pseudo filter, from_barrier_dep bi x x is impossible because
   x.inst_id would appear both in pfx and at the [x.inst_id] position,
   contradicting ALL_DISTINCT. *)
Triviality from_barrier_dep_irrefl_local[local]:
  !bi x pfx sfx.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
    MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi) = pfx ++ [x.inst_id] ++ sfx /\
    MEM x.inst_id pfx ==> F
Proof
  rpt strip_tac >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  simp[ALL_DISTINCT_APPEND_3, ALL_DISTINCT, MEM_APPEND] >>
  metis_tac[]
QED

(* from_barrier_dep case: barrier x depends on y in orig_bi.
   Since topo_sorted preserves ordering, y appears before x in cur_bi's
   non-pseudo filter. Split at x's position; y in prefix.
   from_barrier_to_eda_dep gives eda_dep. *)
Triviality from_barrier_dep_imp_canonical_dep_local[local]:
  !bi x y. from_barrier_dep bi x y ==> canonical_dep bi x y
Proof
  rw[canonical_dep_def] >>
  imp_res_tac from_barrier_dep_def >>
  simp[] >> disj2_tac >> disj1_tac >>
  simp[from_barrier_dep_def]
QED

Triviality on_barrier_dep_imp_canonical_dep_local[local]:
  !bi x y. on_barrier_dep bi x y ==> canonical_dep bi x y
Proof
  rw[canonical_dep_def] >>
  imp_res_tac on_barrier_dep_def >>
  simp[] >> disj2_tac >> disj2_tac >>
  simp[on_barrier_dep_def]
QED

Triviality from_barrier_dep_neq_local[local]:
  !orig_bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    from_barrier_dep orig_bi x y ==> x <> y
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `?pfx sfx. MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi) =
              pfx ++ [x.inst_id] ++ sfx /\ MEM y.inst_id pfx` by (
    pop_assum (fn th =>
      qspecl_then [`orig_bi`, `x`, `y`] mp_tac (iffLR from_barrier_dep_def) >>
      simp[th])) >>
  `MEM x.inst_id pfx` by metis_tac[] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  simp[ALL_DISTINCT_APPEND_3, MEM_APPEND] >>
  metis_tac[]
QED

(* If dep x y and x,y are in a topo-sorted list, y comes before x.
   Extracted as standalone to avoid nested by-blocks. *)
Triviality topo_sorted_MEM_impEl_local[local]:
  !dep l x y.
    topo_sorted dep l /\ dep x y /\ MEM x l /\ MEM y l /\ x <> y ==>
    ?yi. yi < LENGTH l /\ EL yi l = y
Proof
  metis_tac[topo_sorted_dep_after_local, MEM_EL]
QED

Triviality topo_sorted_MEM_x_impEl_local[local]:
  !dep l x.
    topo_sorted dep l /\ MEM x l ==>
    ?xi. xi < LENGTH l /\ EL xi l = x
Proof
  metis_tac[MEM_EL]
QED

(* If dep x y and topo_sorted, y must come before x. But ~MEM y pfx
   means y is in sfx (after x) — contradiction.
   Key insight: construct indices directly instead of using MEM_EL existentials.
   x is at index LENGTH pfx; y is at index LENGTH pfx + SUC k in sfx.
   Then topo_sorted gives LENGTH pfx + SUC k < LENGTH pfx → F. *)
Triviality mem_y_in_sfx_contra_local[local]:
  !dep fl x y pfx sfx.
    ALL_DISTINCT (MAP (\i. i.inst_id) fl) /\
    topo_sorted dep fl /\
    dep x y /\
    MEM x fl /\ MEM y fl /\
    fl = pfx ++ [x] ++ sfx /\
    ~MEM x pfx /\
    x <> y /\
    ~MEM y pfx ==> F
Proof
  rpt strip_tac >>
  `MEM y sfx` by metis_tac[MEM_APPEND, MEM] >>
  `?k. k < LENGTH sfx /\ EL k sfx = y` by metis_tac[MEM_EL] >>
  `EL (LENGTH pfx) fl = x` by simp[EL_APPEND_EQN] >>
  `EL (LENGTH pfx + SUC k) fl = y` by simp[EL_APPEND_EQN] >>
  `LENGTH pfx < LENGTH fl` by simp[] >>
  `LENGTH pfx + SUC k < LENGTH fl` by simp[] >>
  imp_res_tac topo_sorted_dep_after_local >>
  decide_tac
QED

(* Positive version: if dep x y and topo_sorted, then y comes before x.
   So splitting at y, x must be in the suffix. *)
Triviality dep_imp_mem_sfx_local[local]:
  !dep fl x y pfx sfx.
    topo_sorted dep fl /\
    dep x y /\
    MEM x fl /\ MEM y fl /\
    fl = pfx ++ [y] ++ sfx /\
    ~MEM y pfx /\
    x <> y ==> MEM x sfx
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  `MEM x pfx` by metis_tac[MEM_APPEND, MEM] >>
  `?ix. ix < LENGTH pfx /\ EL ix pfx = x` by metis_tac[MEM_EL] >>
  `EL ix fl = x` by simp[EL_APPEND_EQN] >>
  `ix < LENGTH fl` by simp[] >>
  `EL (LENGTH pfx) fl = y` by simp[EL_APPEND_EQN] >>
  `LENGTH pfx < LENGTH fl` by simp[] >>
  imp_res_tac topo_sorted_dep_after_local >>
  decide_tac
QED

(* from_barrier_dep case: barrier x depends on y in orig_bi.
   Since topo_sorted preserves ordering, y appears before x in cur_bi's
   non-pseudo filter. Split at x's position; y in prefix.
   from_barrier_to_eda_dep gives eda_dep. *)
Triviality from_barrier_dep_tc_case_local[local]:
  !cur_bi orig_bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    from_barrier_dep orig_bi x y /\
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==>
    eda_dep (build_full_eda cur_bi) x y
Proof
  rpt strip_tac >>
  qabbrev_tac `fl = FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi` >>
  `canonical_dep orig_bi x y` by
    metis_tac[from_barrier_dep_imp_canonical_dep_local] >>
  `is_barrier x` by fs[from_barrier_dep_def] >>
  `x <> y` by metis_tac[from_barrier_dep_neq_local] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) fl)` by metis_tac[all_distinct_map_filter] >>
  `?pfx sfx. fl = pfx ++ [x] ++ sfx /\ ~MEM x pfx`
    by metis_tac[MEM_SPLIT_APPEND_first, MEM_FILTER] >>
  Cases_on `MEM y pfx` >- (
    irule from_barrier_to_eda_dep >>
    simp[Abbr `fl`] >>
    CONV_TAC SWAP_EXISTS_CONV >> CONV_TAC SWAP_EXISTS_CONV >>
    qexistsl_tac [`pfx`, `sfx`] >>
    simp[]) >>
  metis_tac[mem_y_in_sfx_contra_local]
QED

(* on_barrier_dep case: non-barrier x depends on last-barrier y in orig_bi.
   In cur_bi, find last barrier b_last before x. Two sub-cases:
   (a) b_last has y's inst_id: on_barrier_to_eda_dep gives eda_dep x b_last,
       then inst_id bridge to y.
   (b) b_last has different inst_id: TC chain x -> b_last -> y via
       on_barrier_to_eda_dep and from_barrier_to_eda_dep. *)
(* Helper A: on_barrier_to_eda_dep wrapper for x -> b_last chain *)
Triviality on_barrier_eda_dep_x_blast[local]:
  !cur_bi pfx x sfx b_last bar_pfx.
    FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = pfx ++ [x] ++ sfx /\
    ~is_barrier x /\
    bar_pfx = FILTER is_barrier pfx /\
    bar_pfx <> [] /\ b_last = LAST bar_pfx /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) ==>
    eda_dep (build_full_eda cur_bi) x b_last
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`cur_bi`, `pfx`, `x`, `sfx`, `b_last`]
            on_barrier_to_eda_dep) >>
  simp[] >> Cases_on `FILTER is_barrier pfx` >> gvs[]
QED

(* Helper B: from_barrier_to_eda_dep wrapper for b_last -> y chain *)
Triviality on_barrier_eda_dep_blast_y[local]:
  !cur_bi bpfx b_last bsfx_x_sfx y.
    FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = bpfx ++ [b_last] ++ bsfx_x_sfx /\
    is_barrier b_last /\ MEM y bpfx /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) ==>
    eda_dep (build_full_eda cur_bi) b_last y
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`cur_bi`, `bpfx`, `b_last`, `bsfx_x_sfx`, `y`]
            from_barrier_to_eda_dep) >>
  simp[]
QED

(* Helper C: y (a barrier) in FILTER is_barrier pfx must appear before b_last
   in bpfx when b_last ≠ y by inst_id and b_last = LAST(FILTER is_barrier pfx) *)
(* ALL_DISTINCT on MAP f (l1 ++ l2) gives ALL_DISTINCT on MAP f l1 *)
Triviality all_distinct_map_append_left[local]:
  !f l1 l2. ALL_DISTINCT (MAP f (l1 ++ l2)) ==> ALL_DISTINCT (MAP f l1)
Proof
  simp[MAP_APPEND, ALL_DISTINCT_APPEND]
QED

(* Key sub-lemma: if LAST (FILTER is_barrier pfx) = b_last where
   pfx = bpfx ++ [b_last] ++ bsfx, ~MEM b_last bpfx, ALL_DISTINCT inst_ids,
   then FILTER is_barrier bsfx = []. Otherwise LAST would come from bsfx,
   contradicting ALL_DISTINCT since b_last already appears earlier. *)
Triviality last_barrier_no_suffix_barrier[local]:
  !pfx bpfx b_last bsfx.
    pfx = bpfx ++ [b_last] ++ bsfx /\
    is_barrier b_last /\ ~MEM b_last bpfx /\
    ALL_DISTINCT (MAP (\i. i.inst_id) pfx) /\
    LAST (FILTER is_barrier pfx) = b_last /\
    FILTER is_barrier pfx <> [] ==>
    FILTER is_barrier bsfx = []
Proof
  rpt strip_tac >>
  `FILTER is_barrier pfx =
    FILTER is_barrier bpfx ++ [b_last] ++ FILTER is_barrier bsfx`
    by (simp[FILTER_APPEND_DISTRIB] >> metis_tac[]) >>
  spose_not_then assume_tac >>
  `FILTER is_barrier bpfx ++ [b_last] ≠ []` by simp[] >>
  `LAST (FILTER is_barrier pfx) = LAST (FILTER is_barrier bsfx)`
    by metis_tac[rich_listTheory.LAST_APPEND_NOT_NIL] >>
  `LAST (FILTER is_barrier bsfx) = b_last` by metis_tac[] >>
  `MEM b_last (FILTER is_barrier bsfx)`
    by metis_tac[rich_listTheory.LAST_MEM] >>
  `MEM b_last bsfx` by metis_tac[MEM_FILTER] >>
  (* b_last in both [b_last] and bsfx parts of pfx, contradicts ALL_DISTINCT *)
  qpat_x_assum `ALL_DISTINCT _` mp_tac >>
  simp[MAP_APPEND, ALL_DISTINCT_APPEND, MEM_MAP] >>
  metis_tac[]
QED

Triviality on_barrier_mem_y_before_blast[local]:
  !pfx b_last bpfx bsfx y.
    pfx = bpfx ++ [b_last] ++ bsfx /\
    is_barrier b_last /\ ~MEM b_last bpfx /\
    ALL_DISTINCT (MAP (\i. i.inst_id) pfx) /\
    LAST (FILTER is_barrier pfx) = b_last /\
    FILTER is_barrier pfx <> [] /\
    MEM y (FILTER is_barrier pfx) /\
    b_last.inst_id <> y.inst_id ==>
    MEM y bpfx
Proof
  rpt strip_tac >>
  `FILTER is_barrier bsfx = []` by metis_tac[last_barrier_no_suffix_barrier] >>
  `FILTER is_barrier pfx = FILTER is_barrier bpfx ++ [b_last]`
    by (simp[FILTER_APPEND_DISTRIB] >> metis_tac[]) >>
  `MEM y (FILTER is_barrier bpfx ++ [b_last])` by metis_tac[] >>
  Cases_on `MEM y [b_last]` >- (
    fs[] >> metis_tac[]) >>
  metis_tac[MEM_APPEND, MEM_FILTER]
QED

Triviality tc_chain[local]:
  !(R:'a->'a->bool) x y z. TC R x y /\ TC R y z ==> TC R x z
Proof
  metis_tac[TC_RULES]
QED

Triviality eda_dep_imp_full_dep_local[local]:
  !eda x y. eda_dep eda x y ==> full_dep eda x y
Proof
  simp[full_dep_def] >> metis_tac[eda_dep_inst_id_only]
QED

Triviality on_barrier_dep_tc_case_local[local]:
  !cur_bi orig_bi x y fl.
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    on_barrier_dep orig_bi x y /\
    from_block orig_bi x /\ from_block orig_bi y /\
    fl = FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi /\
    MEM x fl /\ MEM y fl /\
    topo_sorted (canonical_dep orig_bi) fl ==>
    TC (\a b. full_dep (build_full_eda cur_bi) a b) x y
Proof
  rpt strip_tac >>
  `is_barrier y /\ ~is_barrier x` by fs[on_barrier_dep_def] >>
  `x <> y` by metis_tac[] >>
  `canonical_dep orig_bi x y` by metis_tac[on_barrier_dep_imp_canonical_dep_local] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) fl)` by metis_tac[all_distinct_map_filter] >>
  `?pfx_y sfx_y. fl = pfx_y ++ [y] ++ sfx_y /\ ~MEM y pfx_y`
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  `MEM x sfx_y` by metis_tac[dep_imp_mem_sfx_local] >>
  `?pfx_x sfx_x. sfx_y = pfx_x ++ [x] ++ sfx_x /\ ~MEM x pfx_x`
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  qabbrev_tac `pfx = pfx_y ++ [y] ++ pfx_x` >>
  qabbrev_tac `sfx = sfx_x` >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = pfx ++ [x] ++ sfx` by
    fs[Abbr `pfx`, Abbr `sfx`, APPEND_ASSOC] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (pfx ++ [x] ++ sfx))`
    by metis_tac[all_distinct_map_filter] >>
  qabbrev_tac `bar_pfx = FILTER is_barrier pfx` >>
  `MEM y bar_pfx` by (
    simp[Abbr `bar_pfx`, Abbr `pfx`, MEM_FILTER, MEM_APPEND] >> metis_tac[]) >>
  Cases_on `bar_pfx = []` >- gvs[] >>
  qabbrev_tac `b_last = LAST bar_pfx` >>
  `MEM b_last bar_pfx` by metis_tac[rich_listTheory.LAST_MEM] >>
  `is_barrier b_last` by fs[Abbr `bar_pfx`, MEM_FILTER] >>
  `MEM b_last pfx` by fs[Abbr `bar_pfx`, MEM_FILTER] >>
  `eda_dep (build_full_eda cur_bi) x b_last` by (
    mp_tac (Q.SPECL [`cur_bi`, `pfx`, `x`, `sfx`, `b_last`]
              on_barrier_to_eda_dep) >>
    simp[Abbr `bar_pfx`] >>
    Cases_on `FILTER is_barrier pfx` >> gvs[]) >>
  `full_dep (build_full_eda cur_bi) x b_last` by
    metis_tac[eda_dep_imp_full_dep_local] >>
  Cases_on `b_last.inst_id = y.inst_id` >- (
    `full_dep (build_full_eda cur_bi) x y` by
      metis_tac[eda_dep_inst_id_only, eda_dep_imp_full_dep_local] >>
    irule TC_SUBSET >> simp[]) >>
  `?bpfx bsfx. pfx = bpfx ++ [b_last] ++ bsfx /\ ~MEM b_last bpfx`
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) pfx)` by metis_tac[all_distinct_map_append_left] >>
  `FILTER is_barrier bsfx = []` by (
    mp_tac (Q.SPECL [`pfx`, `bpfx`, `b_last`, `bsfx`]
              last_barrier_no_suffix_barrier) >>
    simp[]) >>
  `FILTER is_barrier pfx = FILTER is_barrier bpfx ++ [b_last]` by (
    fs[FILTER_APPEND_DISTRIB]) >>
  `MEM y (FILTER is_barrier bpfx ++ [b_last])` by metis_tac[] >>
  `MEM y bpfx` by (
    Cases_on `MEM y [b_last]` >- (
      fs[] >> metis_tac[]) >>
    metis_tac[MEM_APPEND, MEM_FILTER]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = bpfx ++ [b_last] ++ (bsfx ++ [x] ++ sfx)`
    by (simp[] >> metis_tac[APPEND_ASSOC]) >>
  `eda_dep (build_full_eda cur_bi) b_last y` by (
    mp_tac (Q.SPECL [`cur_bi`, `bpfx`, `b_last`, `bsfx ++ [x] ++ sfx`, `y`]
              from_barrier_to_eda_dep) >>
    simp[]) >>
  `full_dep (build_full_eda cur_bi) b_last y` by
    metis_tac[eda_dep_imp_full_dep_local] >>
  `(λa b. full_dep (build_full_eda cur_bi) a b)⁺ b_last y`
    by (irule TC_SUBSET >> simp[]) >>
  `full_dep (build_full_eda cur_bi) x b_last` by
    metis_tac[eda_dep_imp_full_dep_local] >>
  `(λa b. full_dep (build_full_eda cur_bi) a b)⁺ x b_last`
    by (irule TC_SUBSET >> simp[]) >>
  match_mp_tac tc_chain >> qexists_tac `b_last` >> simp[]
QED

Triviality canonical_dep_tc_full_dep_local[local]:
  !cur_bi orig_bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    canonical_dep orig_bi x y /\ from_block orig_bi x /\ from_block orig_bi y /\
    MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    MEM y (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==>
    TC (\a b. full_dep (build_full_eda cur_bi) a b) x y
Proof
  rpt strip_tac >> fs[canonical_dep_def] >-
  (* data_dep_body: structural via uses/defs overlap *)
  (irule TC_SUBSET >> simp[full_dep_def] >> disj2_tac >> disj1_tac >>
   fs[data_dep_body_def, inst_uses_def, inst_defs_def, IN_DISJOINT] >>
   qexists `v` >> fs[MEM_operand_vars_iff]) >-
  (* from_barrier_dep: eda_dep from lemma, then lift to full_dep, then TC *)
  (`eda_dep (build_full_eda cur_bi) x y` by metis_tac[from_barrier_dep_tc_case_local] >>
   irule TC_SUBSET >> metis_tac[eda_dep_imp_full_dep_local]) >>
  (* on_barrier_dep: use standalone lemma *)
  mp_tac (Q.SPECL [`cur_bi`, `orig_bi`, `x`, `y`,
                    `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi`]
            on_barrier_dep_tc_case_local) >>
  simp[]
QED
Triviality sched_output_nonpseudo[local]:
  !block_insts order eda om entries i.
    eda_wf eda block_insts /\
    EVERY (\i. MEM i block_insts) entries /\
    MEM i (schedule_from_entries block_insts order eda om entries) ==>
    ~is_pseudo i.inst_opcode
Proof
  rpt strip_tac >> imp_res_tac schedule_output_from_block >> simp[]
QED

(* If MAP f l is ALL_DISTINCT and f is injective on l, then l is ALL_DISTINCT *)
Triviality map_inj_all_distinct[local]:
  !f l. ALL_DISTINCT (MAP f l) /\
        (!a b. MEM a l /\ MEM b l /\ f a = f b ==> a = b) ==>
        ALL_DISTINCT l
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `MEM (f h) (MAP f l)` by metis_tac[MEM_MAP] >>
  fs[ALL_DISTINCT] >> first_x_assum irule >> simp[]
QED

(* STANDALONE HELPERS: extracted from the proofs below to avoid by-block issues *)

(* from_block via MEM + inst_id: ALL_DISTINCT inst_ids + from_block bi y + MEM x bi +
   same inst_id ⟹ from_block bi x. *)
Triviality from_block_MEM_inst_id[local]:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    from_block bi y /\ MEM x bi /\ x.inst_id = y.inst_id ==>
    from_block bi x
Proof
  rpt strip_tac >>
  qpat_x_assum `from_block bi y` mp_tac >> simp[from_block_def] >>
  rpt strip_tac >> rename1 `MEM j bi` >>
  `y.inst_id = j.inst_id` by
    (Cases_on `y = j` >- simp[] >> metis_tac[flip_operands_inst_id]) >>
  `j = x` by metis_tac[all_distinct_map_mem_inj] >>
  fs[] >>
  simp[from_block_def] >> qexists_tac `x` >> simp[]
QED

(* full_dep is preserved under from_block equivalence:
   from_block elements with same inst_id have same full_dep behavior *)
Triviality full_dep_from_block_equiv_local[local]:
  !cur_bi x y x' y'.
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    from_block cur_bi x /\ from_block cur_bi y /\
    MEM x' cur_bi /\ x'.inst_id = x.inst_id /\
    MEM y' cur_bi /\ y'.inst_id = y.inst_id ==>
    (full_dep (build_full_eda cur_bi) x y <=> full_dep (build_full_eda cur_bi) x' y')
Proof
  rpt strip_tac >>
  `from_block cur_bi x'` by metis_tac[from_block_MEM_inst_id] >>
  `from_block cur_bi y'` by metis_tac[from_block_MEM_inst_id] >>
  `x.inst_outputs = x'.inst_outputs` by metis_tac[from_block_same_inst_id_outputs_early] >>
  `y.inst_outputs = y'.inst_outputs` by metis_tac[from_block_same_inst_id_outputs_early] >>
  `set (operand_vars x.inst_operands) = set (operand_vars x'.inst_operands)`
    by metis_tac[from_block_same_inst_id_operand_vars_local] >>
  `set (operand_vars y.inst_operands) = set (operand_vars y'.inst_operands)`
    by metis_tac[from_block_same_inst_id_operand_vars_local] >>
  simp[full_dep_def] >>
  `eda_dep (build_full_eda cur_bi) x y = eda_dep (build_full_eda cur_bi) x' y'`
    by (simp[GSYM eda_dep_inst_id_only] >>
        metis_tac[flip_operands_inst_id, from_block_def]) >>
  simp[inst_uses_def, inst_defs_def]
QED

(* One-sided congruence: full_dep with same inst_id/outputs/operand_vars
   on the FIRST argument agrees for any second argument. *)
Triviality full_dep_left_cong_local[local]:
  !eda x x' a.
    x.inst_id = x'.inst_id /\
    x.inst_outputs = x'.inst_outputs /\
    set (operand_vars x.inst_operands) = set (operand_vars x'.inst_operands) ==>
    (full_dep eda x a <=> full_dep eda x' a)
Proof
  rpt strip_tac >> simp[full_dep_def] >>
  `eda_dep eda x a = eda_dep eda x' a`
    by metis_tac[eda_dep_inst_id_only] >>
  simp[inst_uses_def, inst_defs_def]
QED

(* One-sided congruence: full_dep with same inst_id/outputs/operand_vars
   on the SECOND argument agrees for any first argument. *)
Triviality full_dep_right_cong_local[local]:
  !eda y y' a.
    y.inst_id = y'.inst_id /\
    y.inst_outputs = y'.inst_outputs /\
    set (operand_vars y.inst_operands) = set (operand_vars y'.inst_operands) ==>
    (full_dep eda a y <=> full_dep eda a y')
Proof
  rpt strip_tac >> simp[full_dep_def] >>
  `eda_dep eda a y = eda_dep eda a y'`
    by metis_tac[eda_dep_inst_id_only] >>
  simp[inst_uses_def, inst_defs_def]
QED

(* from_block gives a literal MEM witness with same inst_id and ~is_pseudo *)
Triviality from_block_MEM_witness[local]:
  !bi i. from_block bi i ==> ?j. MEM j bi /\ j.inst_id = i.inst_id /\ ~is_pseudo j.inst_opcode
Proof
  simp[from_block_def] >> metis_tac[flip_operands_inst_id]
QED

(* TC endpoint replacement: if TC R x' y' and we can replace x'→x and y'→y
   at the endpoints of one-step relations, then TC R x y.
   Proof: by TC induction. Base: R x' y' → R x y'.
   Step: TC R x' y' ∧ R y' z → TC R x' z, plus R y' z → R y z. *)
(* TC left endpoint replacement: if ∀a. R x' a ⇒ R x a, then
   TC R x' y ⇒ TC R x y.
   Proof: by TC_CASES1_E, either R x' y (base, use left_cong + TC_SUBSET)
   or ∃z. R x' z ∧ TC R z y (step, use left_cong to get R x z → TC x z,
   then tc_chain with TC R z y). *)
Triviality tc_left_replace[local]:
  !R x x' y.
    (!a. R x' a ==> R x a) ==>
    TC R x' y ==> TC R x y
Proof
  rpt gen_tac >> disch_tac >> disch_tac >>
  qhdtm_x_assum `TC` mp_tac >>
  simp[Once TC_CASES1] >>
  rpt strip_tac
  >- (irule TC_SUBSET >> pop_assum mp_tac >> metis_tac[])
  >- (rename1 `R x' z` >> rename1 `TC R z y` >>
      metis_tac[tc_chain, TC_SUBSET])
QED

(* TC right endpoint replacement: if ∀b. R b y' ⇒ R b y, then
   TC R x y' ⇒ TC R x y. *)
Triviality tc_right_replace[local]:
  !R y y' x.
    (!b. R b y' ==> R b y) ==>
    TC R x y' ==> TC R x y
Proof
  rpt gen_tac >> disch_tac >> disch_tac >>
  qhdtm_x_assum `TC` mp_tac >>
  simp[Once TC_CASES2] >>
  rpt strip_tac
  >- (irule TC_SUBSET >> pop_assum mp_tac >> metis_tac[])
  >- (rename1 `R z y'` >> rename1 `TC R x z` >>
      metis_tac[TC_RIGHT1_I, TC_SUBSET])
QED

(* TC endpoint replacement: combination of left and right replace *)
Triviality tc_endpoint_replace[local]:
  !R x y x' y'.
    TC R x' y' /\
    (!a. R x' a ==> R x a) /\
    (!b. R b y' ==> R b y) ==>
    TC R x y
Proof
  metis_tac[tc_left_replace, tc_right_replace]
QED

(* Bridge: EVERY from_block orig (FILTER ~is_pseudo cur) + from_block cur x' + MEM + ~is_pseudo
   implies from_block orig x'. Uses from_block_trans with universal antecedent. *)
Triviality from_block_cur_to_orig_local[local]:
  !cur_bi orig_bi x'.
    EVERY (\i. from_block orig_bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    from_block cur_bi x' /\ MEM x' cur_bi /\ ~is_pseudo x'.inst_opcode ==>
    from_block orig_bi x'
Proof
  rpt strip_tac >>
  match_mp_tac from_block_trans >>
  qexists_tac `cur_bi` >> simp[] >>
  qpat_x_assum `EVERY _ _` mp_tac >>
  simp[EVERY_FILTER, EVERY_MEM, PULL_FORALL] >>
  metis_tac[]
QED

(* Filtered-ALL_DISTINCT variant: when ALL_DISTINCT is only on FILTER ~is_pseudo bi,
   from_block same inst_id still gives same outputs *)
Theorem from_block_same_inst_id_outputs_filtered_local:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
    from_block bi x /\ from_block bi y /\ x.inst_id = y.inst_id ==>
    x.inst_outputs = y.inst_outputs
Proof
  rw[from_block_def] >>
  `MEM j (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by simp[MEM_FILTER] >>
  `MEM j' (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by simp[MEM_FILTER] >>
  `j = j'` by metis_tac[flip_operands_inst_id, all_distinct_map_mem_inj, MEM_FILTER] >>
  metis_tac[flip_operands_inst_outputs]
QED

Theorem from_block_same_inst_id_operand_vars_filtered_local:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
    from_block bi x /\ from_block bi y /\ x.inst_id = y.inst_id ==>
    set (operand_vars x.inst_operands) = set (operand_vars y.inst_operands)
Proof
  rw[from_block_def] >>
  `MEM j (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by simp[MEM_FILTER] >>
  `MEM j' (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by simp[MEM_FILTER] >>
  `j = j'` by metis_tac[flip_operands_inst_id, all_distinct_map_mem_inj, MEM_FILTER] >>
  metis_tac[flip_operands_operand_vars_set]
QED

Theorem from_block_same_inst_id_barrier_filtered_local:
  !bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
    from_block bi x /\ from_block bi y /\ x.inst_id = y.inst_id ==>
    (is_barrier x <=> is_barrier y)
Proof
  rw[from_block_def] >>
  `MEM j (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by simp[MEM_FILTER] >>
  `MEM j' (FILTER (\i. ~is_pseudo i.inst_opcode) bi)` by simp[MEM_FILTER] >>
  `j = j'` by metis_tac[flip_operands_inst_id, all_distinct_map_mem_inj, MEM_FILTER] >>
  metis_tac[flip_operands_is_barrier]
QED

(* canonical_dep transfers across inst_id-equivalent from_block pairs
   with FILTER-level ALL_DISTINCT (the version we actually have in hypotheses) *)
Theorem canonical_dep_inst_id_equiv_filtered:
  !bi x y x' y'.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
    canonical_dep bi x y /\
    from_block bi x /\ from_block bi y /\
    from_block bi x' /\ from_block bi y' /\
    x'.inst_id = x.inst_id /\ y'.inst_id = y.inst_id ==>
    canonical_dep bi x' y'
Proof
  rpt strip_tac >>
  `in_np_body bi x` by metis_tac[from_block_imp_in_np_body_local] >>
  `in_np_body bi y` by metis_tac[from_block_imp_in_np_body_local] >>
  `in_np_body bi x'` by metis_tac[from_block_imp_in_np_body_local] >>
  `in_np_body bi y'` by metis_tac[from_block_imp_in_np_body_local] >>
  `x.inst_outputs = x'.inst_outputs` by metis_tac[from_block_same_inst_id_outputs_filtered_local] >>
  `y.inst_outputs = y'.inst_outputs` by metis_tac[from_block_same_inst_id_outputs_filtered_local] >>
  `set (operand_vars x.inst_operands) = set (operand_vars x'.inst_operands)`
    by metis_tac[from_block_same_inst_id_operand_vars_filtered_local] >>
  `set (operand_vars y.inst_operands) = set (operand_vars y'.inst_operands)`
    by metis_tac[from_block_same_inst_id_operand_vars_filtered_local] >>
  `(is_barrier x <=> is_barrier x')` by metis_tac[from_block_same_inst_id_barrier_filtered_local] >>
  `(is_barrier y <=> is_barrier y')` by metis_tac[from_block_same_inst_id_barrier_filtered_local] >>
  assume_tac canonical_dep_inst_id_equiv >>
  pop_assum (fn th => mp_tac (SPECL [``bi:instruction list``, ``x:instruction``,
    ``y:instruction``, ``x':instruction``, ``y':instruction``] th)) >>
  simp[]
QED

(* Bridge: canonical_dep orig → TC full_dep cur for from_block elements.
   Uses the already-proved canonical_dep_tc_full_dep_local for literal MEM
   representatives x', y' in cur_bi, then transfers the TC result to x, y
   via full_dep_from_block_equiv_local + tc_endpoint_replace.
   full_dep is a congruence for inst_id-equivalent pairs, so we can replace
   the endpoints of the TC chain without affecting intermediate steps. *)
Triviality canonical_dep_tc_full_dep_from_block_local[local]:
  !cur_bi orig_bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    EVERY (\i. from_block orig_bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    canonical_dep orig_bi x y /\ from_block orig_bi x /\ from_block orig_bi y /\
    from_block cur_bi x /\ from_block cur_bi y /\
    ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==>
    TC (\a b. full_dep (build_full_eda cur_bi) a b) x y
Proof
  rpt strip_tac >>
  (* Step 1: Find literal counterparts x', y' in cur_bi with same inst_id *)
  `?x'. MEM x' cur_bi /\ x'.inst_id = x.inst_id /\ ~is_pseudo x'.inst_opcode`
    by metis_tac[from_block_MEM_witness] >>
  `?y'. MEM y' cur_bi /\ y'.inst_id = y.inst_id /\ ~is_pseudo y'.inst_opcode`
    by metis_tac[from_block_MEM_witness] >>
  (* Step 2: x', y' are from_block cur_bi and orig_bi *)
  `from_block cur_bi x'` by metis_tac[from_block_MEM_inst_id] >>
  `from_block cur_bi y'` by metis_tac[from_block_MEM_inst_id] >>
  `from_block orig_bi x'` by metis_tac[from_block_cur_to_orig_local] >>
  `from_block orig_bi y'` by metis_tac[from_block_cur_to_orig_local] >>
  (* Step 3: Transfer canonical_dep to x', y' via inst_id equivalence *)
  `canonical_dep orig_bi x' y'`
    by metis_tac[canonical_dep_inst_id_equiv_filtered] >>
  (* Step 4: x', y' are literal non-pseudo members of cur_bi *)
  `MEM x' (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by simp[MEM_FILTER] >>
  `MEM y' (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by simp[MEM_FILTER] >>
  (* Step 5: Apply the already-proved literal-MEM version *)
  `TC (\a b. full_dep (build_full_eda cur_bi) a b) x' y'`
    by metis_tac[canonical_dep_tc_full_dep_local] >>
  (* Step 6: Transfer TC endpoints via inst_id congruence *)
  `x.inst_outputs = x'.inst_outputs`
    by metis_tac[from_block_same_inst_id_outputs_filtered_local] >>
  `y.inst_outputs = y'.inst_outputs`
    by metis_tac[from_block_same_inst_id_outputs_filtered_local] >>
  `set (operand_vars x.inst_operands) = set (operand_vars x'.inst_operands)`
    by metis_tac[from_block_same_inst_id_operand_vars_filtered_local] >>
  `set (operand_vars y.inst_operands) = set (operand_vars y'.inst_operands)`
    by metis_tac[from_block_same_inst_id_operand_vars_filtered_local] >>
  match_mp_tac tc_endpoint_replace >>
  qexists_tac `x'` >> qexists_tac `y'` >> simp[] >>
  rpt strip_tac >-
  metis_tac[full_dep_left_cong_local] >>
  metis_tac[full_dep_right_cong_local]
QED

(* FILTER decomposition: dft_block non-pseudo instructions = schedule output *)
Triviality dft_block_filter_nonpseudo[local]:
  !order bb.
    FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb).bb_instructions =
    schedule_from_entries bb.bb_instructions order (build_full_eda bb.bb_instructions)
      (build_offspring_map bb.bb_instructions order)
      (entry_instructions bb.bb_instructions order (build_full_eda bb.bb_instructions))
Proof
  simp[dft_block_def, LET_THM, FILTER_APPEND_DISTRIB, FILTER_FILTER,
       FILTER_EQ_NIL, FILTER_EQ_ID, EVERY_MEM] >>
  rpt strip_tac >>
  metis_tac[sched_output_nonpseudo, build_full_eda_wf, entry_instructions_mem]
QED


(* Extracted by-block: ALL_DISTINCT inst_outputs for perm-of block *)
Triviality block_perm_inst_outputs_local[local]:
  !fn bb_orig bb_cur.
    wf_ssa fn /\ wf_function fn /\
    MEM bb_orig fn.fn_blocks /\
    block_perm_of fn bb_cur /\ bb_cur.bb_label = bb_orig.bb_label ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb_cur.bb_instructions))
Proof
  metis_tac[block_perm_of_inst_outputs_distinct_local]
QED

(* Schedule output lemma pack — avoid irule on multi-antecedent theorems in by-blocks *)
Triviality sched_output_distinct_local[local]:
  !bi order eda om entries.
    eda_wf eda bi /\ eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==> k = PRE (LENGTH bi)) /\
    EVERY (\i. MEM i bi) entries ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (schedule_from_entries bi order eda om entries))
Proof
  rpt strip_tac >>
  irule schedule_output_all_distinct >> simp[]
QED

Triviality sched_output_producer_local[local]:
  !bi order eda om entries.
    eda_wf eda bi /\ eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==> k = PRE (LENGTH bi)) /\
    EVERY (\i. MEM i bi) entries ==>
    output_producer_before bi (schedule_from_entries bi order eda om entries)
Proof
  rpt strip_tac >>
  irule schedule_output_producer_before >> simp[]
QED

Triviality sched_output_eda_local[local]:
  !bi order eda om entries.
    eda_wf eda bi /\ eda_topo_compatible bi eda order /\
    np_defs_before_uses bi /\ ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    bi <> [] /\
    (!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==> k = PRE (LENGTH bi)) /\
    EVERY (\i. MEM i bi) entries ==>
    output_eda_before eda (schedule_from_entries bi order eda om entries)
Proof
  rpt strip_tac >>
  irule schedule_output_eda_before >> simp[]
QED

Triviality sched_topo_sorted_local[local]:
  !bi eda om entries sched.
    eda = build_full_eda bi /\
    output_eda_before eda sched /\ output_producer_before bi sched /\
    ALL_DISTINCT (MAP (\i. i.inst_id) sched) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) bi) /\
    (!i. MEM i sched ==> from_block bi i /\ ~is_pseudo i.inst_opcode) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi)) ==>
    topo_sorted (full_dep eda) sched
Proof
  rpt strip_tac >>
  qspecl_then [`bi`,`eda`,`sched`] mp_tac schedule_topo_sorted_full_dep >>
  simp[]
QED

(* Helper: schedule elements originate from cur block *)
Triviality sched_mem_from_block_cur_local[local]:
  !bi order eda om entries i.
    eda_wf eda bi /\ EVERY (\i. MEM i bi) entries /\
    MEM i (schedule_from_entries bi order eda om entries) ==>
    from_block bi i /\ ~is_pseudo i.inst_opcode
Proof
  metis_tac[schedule_output_from_block]
QED

(* Helper: schedule elements originate from orig block *)
Triviality sched_mem_from_block_orig_local[local]:
  !fn bb_orig bb_cur order eda om entries i.
    wf_function fn /\ MEM bb_orig fn.fn_blocks /\
    block_perm_of fn bb_cur /\ bb_cur.bb_label = bb_orig.bb_label /\
    eda_wf eda bb_cur.bb_instructions /\
    EVERY (\i. MEM i bb_cur.bb_instructions) entries /\
    MEM i (schedule_from_entries bb_cur.bb_instructions order eda om entries) ==>
    from_block bb_orig.bb_instructions i
Proof
  metis_tac[schedule_output_from_block, from_block_sched_via_perm_of]
QED


(* ===== Cross-bi bridge helpers (ported from dftCanonicalSimScript) ===== *)

(* Cross-bi version: from_block on both sides, with ALL_DISTINCT inst_ids *)
Triviality is_barrier_from_inst_id_cross_bi[local]:
  !orig_bi b x.
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    from_block orig_bi b /\ from_block orig_bi x /\ b.inst_id = x.inst_id ==>
    is_barrier b = is_barrier x
Proof
  rpt strip_tac >> fs[from_block_def] >>
  metis_tac[all_distinct_map_mem_inj, flip_operands_is_barrier, flip_operands_inst_id]
QED

(* MEM in FILTER implies from_block *)
Triviality from_block_MEM_filter[local]:
  !bi x. MEM x (FILTER (\i. ~is_pseudo i.inst_opcode) bi) ==> from_block bi x
Proof
  rpt strip_tac >>
  fs[MEM_FILTER] >>
  simp[from_block_def] >>
  qexists_tac `x` >> simp[]
QED

(* MEM in FILTER split: if b is in the filtered list and its inst_id <> mid.inst_id,
   then b is in pfx or sfx (not in [mid]) *)
Triviality mem_orig_filter_split[local]:
  !orig_bi pfx mid sfx b.
    ALL_DISTINCT (MAP (\i:instruction. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi = pfx ++ [mid] ++ sfx /\
    MEM b (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi) /\
    b.inst_id <> mid.inst_id ==>
    MEM b pfx \/ MEM b sfx
Proof
  rpt strip_tac >> qpat_x_assum `MEM b (FILTER _ _)` mp_tac >>
  qpat_x_assum `FILTER _ _ = _` (fn th => REWRITE_TAC [th]) >>
  simp[MEM_APPEND] >> metis_tac[]
QED

(* ===== Single-step bridge: canonical_dep ⊆ full_dep (cross-bi) ===== *)
(* Ported and adapted from dftCanonicalSimScript lines 272-900. *)

(* If dep(a,b) and a is at split point and b in suffix, topo_sorted is violated *)
Triviality topo_sorted_suffix_dep[local]:
  !dep l pfx a sfx b.
    topo_sorted dep l /\ l = pfx ++ [a] ++ sfx /\ dep a b /\ MEM b sfx ==> F
Proof
  rpt strip_tac >> qpat_x_assum `MEM b sfx` (mp_tac o REWRITE_RULE[MEM_EL]) >> strip_tac >>
  `EL (LENGTH pfx) l = a` by (simp[el_append3] >> metis_tac[]) >>
  `EL (LENGTH pfx + 1 + n) l = b` by (
    simp[EL_APPEND2] >>
    simp[LENGTH_APPEND] >>
    decide_tac) >>
  qpat_x_assum `topo_sorted dep l` (fn th =>
    mp_tac (REWRITE_RULE [topo_sorted_def] th) >>
    disch_then (qspecl_then [`LENGTH pfx`, `LENGTH pfx + 1 + n`] mp_tac)) >> simp[] >>
  qpat_x_assum `dep a b` mp_tac >> simp[]
QED

Triviality data_dep_body_imp_full_dep_any_eda[local]:
  !orig_bi cur_bi x y.
    data_dep_body orig_bi x y /\
    from_block orig_bi x /\ from_block orig_bi y ==>
    full_dep (build_full_eda cur_bi) x y
Proof
  rpt strip_tac >> simp[full_dep_def] >> disj2_tac >> disj1_tac >>
  fs[data_dep_body_def, inst_uses_def, inst_defs_def, IN_DISJOINT] >>
  qexists `v` >> fs[MEM_operand_vars_iff]
QED

(* If MAP inst_id of FILTER ~pseudo bi = pfx++[xid]++sfx with ALL_DISTINCT, and MEM yid pfx, then xid <> yid *)
Triviality all_distinct_split_inst_id_neq[local]:
  !bi xid yid pfx sfx.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi)) /\
    MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi) = pfx ++ [xid] ++ sfx /\
    MEM yid pfx ==> xid <> yid
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (pfx ++ [xid] ++ sfx)` by metis_tac[] >>
  gvs[ALL_DISTINCT_APPEND_3, MEM_APPEND]
QED

(* Helper: yb_c exists in px_c with y.inst_id, via topo_sorted contradiction if in sfx_x *)
Triviality yb_c_in_px_c[local]:
  !orig_bi fl px_c px_b sfx_x x y.
  ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
  fl = px_c ++ [px_b] ++ sfx_x /\
  px_b.inst_id = x.inst_id /\
  MEM y.inst_id (MAP (\i. i.inst_id) fl) /\
  x.inst_id <> y.inst_id /\
  topo_sorted (canonical_dep orig_bi) fl /\
  canonical_dep orig_bi x y /\
  from_block orig_bi x /\ from_block orig_bi y /\
  (!z. MEM z fl ==> from_block orig_bi z) ==>
  ?yb_c. MEM yb_c px_c /\ yb_c.inst_id = y.inst_id
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM y.inst_id (MAP (λi. i.inst_id) fl)` (mp_tac o REWRITE_RULE [MEM_MAP]) >> strip_tac >>
  Cases_on `MEM y' px_c` >- (qexists `y'` >> simp[]) >>
  `MEM y' sfx_x` by (
    qpat_x_assum `MEM y' fl` mp_tac >>
    qpat_x_assum `fl = px_c ++ [px_b] ++ sfx_x` (fn th => REWRITE_TAC[th]) >>
    simp[MEM_APPEND] >>
    Cases_on `MEM y' [px_b]` >- (
      fs[] >> pop_assum mp_tac >> simp[MEM] >>
      metis_tac[]) >>
    metis_tac[]) >>
  `from_block orig_bi px_b` by (
    first_x_assum (qspec_then `px_b` mp_tac) >>
    simp[MEM_APPEND] >> metis_tac[]) >>
  `from_block orig_bi y'` by metis_tac[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by metis_tac[all_distinct_map_filter] >>
  `canonical_dep orig_bi px_b y'` by (
    irule canonical_dep_inst_id_equiv_filtered >>
    simp[] >> metis_tac[]) >>
  metis_tac[topo_sorted_suffix_dep]
QED

(* Case 2: from_barrier_dep under PERM + topo_sorted *)
Triviality from_barrier_dep_imp_full_dep_current[local]:
  !orig_bi cur_bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    from_barrier_dep orig_bi x y /\
    from_block orig_bi x /\ from_block orig_bi y /\
    PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi))
         (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    (!z. MEM z (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==> from_block orig_bi z) ==>
    full_dep (build_full_eda cur_bi) x y
Proof
  rpt strip_tac >>
  `canonical_dep orig_bi x y` by metis_tac[from_barrier_dep_imp_canonical_dep_local] >>
  simp[full_dep_def] >> disj1_tac >>
  fs[from_barrier_dep_def] >>
  qabbrev_tac `fl = FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by metis_tac[all_distinct_map_filter] >>
  `MEM x.inst_id (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (fs[in_np_body_def, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  `MEM y.inst_id (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (fs[in_np_body_def, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  `MEM x.inst_id (MAP (\i. i.inst_id) fl)`
    by metis_tac[PERM_MEM_EQ, Abbr `fl`] >>
  `MEM y.inst_id (MAP (\i. i.inst_id) fl)`
    by metis_tac[PERM_MEM_EQ, Abbr `fl`] >>
  `?pfx_fl sfx_fl. MAP (\i. i.inst_id) fl = pfx_fl ++ [x.inst_id] ++ sfx_fl`
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  `?px_c px_b sfx_x. fl = px_c ++ [px_b] ++ sfx_x /\
                       MAP (\i. i.inst_id) px_c = pfx_fl /\
                       px_b.inst_id = x.inst_id /\
                       MAP (\i. i.inst_id) sfx_x = sfx_fl`
    by metis_tac[MAP_INST_ID_APPEND_SPLIT_exists_local] >>
  `x.inst_id <> y.inst_id` by metis_tac[all_distinct_split_inst_id_neq] >>
  `?yb_c. MEM yb_c px_c /\ yb_c.inst_id = y.inst_id`
    by metis_tac[yb_c_in_px_c] >>
  `is_barrier px_b` by (
    `from_block orig_bi px_b` by (
      first_x_assum $ qspecl_then [`px_b`] mp_tac >>
      simp[Abbr `fl`, MEM_APPEND] >> metis_tac[]) >>
    metis_tac[is_barrier_from_inst_id_cross_bi]
  ) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
    by (simp[Abbr `fl`]) >>
  `eda_dep (build_full_eda cur_bi) px_b yb_c` by (
    mp_tac (from_barrier_to_eda_dep |> Q.SPECL [`cur_bi`, `px_c`, `px_b`, `sfx_x`, `yb_c`]) >>
    simp[]
  ) >>
  metis_tac[eda_dep_inst_id_only]
QED

(* Apply on_barrier_to_eda_dep: specialize and discharge case expression *)
Triviality on_barrier_to_eda_dep_apply[local]:
  !cur_bi px_c px_b sfx_x yb_c.
    FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x /\
    ~is_barrier px_b /\
    FILTER is_barrier px_c <> [] /\
    LAST (FILTER is_barrier px_c) = yb_c /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) ==>
    eda_dep (build_full_eda cur_bi) px_b yb_c
Proof
  rpt strip_tac >>
  irule on_barrier_to_eda_dep >> simp[] >>
  qexistsl_tac [`px_c`,`sfx_x`] >> simp[] >>
  Cases_on `FILTER is_barrier px_c` >> gvs[LAST_CONS]
QED

(* If l = pfx++[a]++sfx and b MEM sfx, ALL_DISTINCT (MAP f l), then for any
   split of MAP f l at f b, f a is in the prefix before f b *)
Triviality map_split_mem_before[local]:
  !f pfx a sfx b l1 l2.
    ALL_DISTINCT (MAP f l) /\ l = pfx ++ [a] ++ sfx /\ MEM b sfx /\
    MAP f l = l1 ++ [f b] ++ l2 ==>
    MEM (f a) l1
Proof
  rpt strip_tac >>
  qpat_x_assum `MEM b sfx` (fn th => mp_tac (MATCH_MP (iffLR MEM_EL) th)) >>
  strip_tac >>
  `EL (LENGTH pfx) l = a` by (fs[el_append3]) >>
  `EL (LENGTH pfx + 1 + n) l = b` by (
    simp[EL_APPEND2, ADD1] >>
    qpat_x_assum `l = pfx ++ [a] ++ sfx` (assume_tac o GSYM) >>
    simp[Once EL_APPEND2, ADD1] >>
    simp[EL_APPEND1, ADD1] >>
    simp[EL_CONS, ADD1] >> simp[]) >>
  `EL (LENGTH pfx) (MAP f l) = f a` by simp[EL_MAP] >>
  `EL (LENGTH pfx + 1 + n) (MAP f l) = f b` by simp[EL_MAP] >>
  `LENGTH pfx + 1 + n < LENGTH l` by (simp[LENGTH_APPEND] >> decide_tac) >>
  `LENGTH l = LENGTH (l1 ++ [f b] ++ l2)` by metis_tac[LENGTH_MAP] >>
  qpat_x_assum `MAP f l = l1 ++ [f b] ++ l2` (fn th => RULE_ASSUM_TAC (ONCE_REWRITE_RULE [th])) >>
  `EL (LENGTH l1) (l1 ++ [f b] ++ l2) = f b` by simp[APPEND_ASSOC, el_append3] >>
  `LENGTH l1 < LENGTH (l1 ++ [f b] ++ l2)` by simp[LENGTH_APPEND] >>
  `LENGTH l1 = LENGTH pfx + 1 + n` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  `LENGTH pfx < LENGTH l1` by decide_tac >>
  `EL (LENGTH pfx) (l1 ++ [f b] ++ l2) = f a` by fs[EL_APPEND1] >>
  `EL (LENGTH pfx) l1 = f a` by fs[EL_APPEND1] >>
  metis_tac[EL_MEM]
QED

(* If dep b a and b is in pfx (before a in l = pfx++[a]++sfx), topo_sorted is violated *)
Triviality topo_sorted_prefix_dep[local]:
  !dep l pfx a sfx b.
    topo_sorted dep l /\ l = pfx ++ [a] ++ sfx /\ dep b a /\ MEM b pfx ==> F
Proof
  rpt strip_tac >> qpat_x_assum `MEM b pfx` (mp_tac o REWRITE_RULE[MEM_EL]) >> strip_tac >>
  `EL (LENGTH pfx) l = a` by (simp[el_append3] >> metis_tac[]) >>
  `EL n l = b` by simp[EL_APPEND1, EL_APPEND2] >>
  `n < LENGTH pfx` by (simp[LENGTH_APPEND] >> decide_tac) >>
  qpat_x_assum `topo_sorted dep l` (fn th =>
    mp_tac (REWRITE_RULE [topo_sorted_def] th) >>
    disch_then (qspecl_then [`n`, `LENGTH pfx`] mp_tac)) >> simp[] >>
  qpat_x_assum `dep b a` mp_tac >> simp[]
QED

(* If LAST(FILTER P l) = b and a is in FILTER P l with a <> b,
   then FILTER P l = front ++ [b] with MEM a front *)
Triviality last_filter_mem_front[local]:
  !P l a b.
    FILTER P l <> [] /\ LAST (FILTER P l) = b /\
    MEM a (FILTER P l) /\ a <> b ==>
    ?front. FILTER P l = front ++ [b] /\ MEM a front
Proof
  rpt strip_tac >>
  `FILTER P l = FRONT (FILTER P l) ++ [LAST (FILTER P l)]` by (
    drule SNOC_LAST_FRONT >> simp[SNOC_APPEND]) >>
  qexists_tac `FRONT (FILTER P l)` >>
  simp[] >> CCONTR_TAC >> fs[MEM_APPEND] >> rfs[MEM_APPEND] >>
  fs[LAST_APPEND, LAST_CONS] >> Cases_on `FRONT (FILTER P l)` >> fs[LAST_CONS]
QED

(* Helper: FILTER is_barrier post = [] when last barrier not in post *)
Triviality filter_barrier_post_nil[local]:
  !l pre post front.
    l = pre ++ [LAST (FILTER is_barrier l)] ++ post /\
    FILTER is_barrier l = front ++ [LAST (FILTER is_barrier l)] /\
    ~MEM (LAST (FILTER is_barrier l)) post ==>
    FILTER is_barrier post = []
Proof
  rpt strip_tac >> CCONTR_TAC >>
  qabbrev_tac `x = LAST (FILTER is_barrier l)` >>
  `MEM x (FILTER is_barrier l)` by simp[MEM_APPEND, MEM] >>
  `is_barrier x` by metis_tac[iffLR MEM_FILTER] >>
  `FILTER is_barrier l = FILTER is_barrier pre ++ [x] ++ FILTER is_barrier post` by (
    qpat_x_assum `l = pre ++ [x] ++ post` (fn th =>
      once_rewrite_tac[th] >>
      simp[FILTER_APPEND_DISTRIB, FILTER_EQ_ID, EVERY_MEM, MEM])) >>
  qpat_x_assum `FILTER is_barrier l = front ++ [x]` (fn th1 =>
  qpat_x_assum `FILTER is_barrier l = FILTER is_barrier pre ++ [x] ++ FILTER is_barrier post` (fn th2 =>
    `FILTER is_barrier pre ++ [x] ++ FILTER is_barrier post = front ++ [x]` by
      metis_tac[th2, SYM th1])) >>
  `LAST (front ++ [x]) = x` by metis_tac[LAST_APPEND_NOT_NIL, LAST_CONS] >>
  `LAST ((FILTER is_barrier pre ++ [x]) ++ FILTER is_barrier post) =
    LAST (FILTER is_barrier post)` by metis_tac[LAST_APPEND_NOT_NIL] >>
  pop_assum mp_tac >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  metis_tac[LAST_MEM, MEM_FILTER]
QED

(* If b is a barrier in l and b is not the LAST barrier, then b appears before LAST barrier in l *)
Triviality barrier_before_last_barrier[local]:
  !l b.
    MEM b l /\ is_barrier b /\
    FILTER is_barrier l <> [] /\
    LAST (FILTER is_barrier l) <> b ==>
    ?pre post. l = pre ++ [LAST (FILTER is_barrier l)] ++ post /\ MEM b pre
Proof
  rpt strip_tac >>
  qabbrev_tac `x = LAST (FILTER is_barrier l)` >>
  `MEM b (FILTER is_barrier l)` by metis_tac[MEM_FILTER] >>
  `is_barrier x` by metis_tac[iffLR MEM_FILTER, LAST_MEM] >>
  `?front. FILTER is_barrier l = front ++ [x] /\
           MEM b front`
    by (irule last_filter_mem_front >> simp[]) >>
  `MEM x l` by metis_tac[iffLR MEM_FILTER, LAST_MEM] >>
  `?pre post. l = pre ++ [x] ++ post /\
              ~MEM x post`
    by metis_tac[iffLR MEM_SPLIT_APPEND_last] >>
  `FILTER is_barrier post = []` by metis_tac[filter_barrier_post_nil] >>
  `MEM b pre` by metis_tac[MEM_APPEND, MEM, MEM_FILTER, NOT_CONS_NIL] >>
  qexistsl_tac [`pre`, `post`] >> simp[Abbr `x`]
QED

(* Reverse of map_split_mem_before: if b is in element-level prefix before a,
   then f b is in MAP-level prefix before f a *)
Triviality map_split_mem_before_rev[local]:
  !f pfx a sfx b l1 l2.
    ALL_DISTINCT (MAP f l) /\ l = pfx ++ [a] ++ sfx /\ MEM b pfx /\
    MAP f l = l1 ++ [f a] ++ l2 ==>
    MEM (f b) l1
Proof
  rpt strip_tac >>
  `?pfx1 sfx1. pfx = pfx1 ++ [b] ++ sfx1 /\
               ~MEM b pfx1`
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  `l = pfx1 ++ [b] ++ (sfx1 ++ [a] ++ sfx)`
    by simp[] >>
  `MEM a (sfx1 ++ [a] ++ sfx)`
    by simp[MEM_APPEND] >>
  metis_tac[map_split_mem_before]
QED

(* Case A: b_orig in pfx -- y depends on b_orig (barrier dep),
   transfer to yb_c->b', but yb_c before b' in cur_bi (since b' = LAST barrier) -> topo_sorted violation *)
Triviality contra_b_orig_in_pfx[local]:
  !orig_bi cur_bi x y pfx sfx mid px_c px_b sfx_x yb_c b' b_orig.
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi = pfx ++ [mid] ++ sfx /\
    mid.inst_id = x.inst_id /\
    FILTER is_barrier pfx <> [] /\
    (LAST (FILTER is_barrier pfx)).inst_id = y.inst_id /\
    ~is_barrier x /\ is_barrier y /\
    from_block orig_bi x /\ from_block orig_bi y /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x /\
    MEM yb_c px_c /\ yb_c.inst_id = y.inst_id /\
    is_barrier b' /\ from_block orig_bi b' /\ MEM b' px_c /\
    b'.inst_id <> y.inst_id /\
    MEM b_orig (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi) /\
    b_orig.inst_id = b'.inst_id /\
    is_barrier b_orig /\ from_block orig_bi b_orig /\
    MEM b_orig pfx /\
    ALL_DISTINCT (MAP (\i:instruction. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)) /\
    from_block orig_bi yb_c /\ from_block orig_bi px_b /\
    FILTER is_barrier px_c <> [] /\
    LAST (FILTER is_barrier px_c) = b' ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  `b_orig.inst_id <> y.inst_id` by fs[] >>
  `in_np_body orig_bi y` by metis_tac[from_block_imp_in_np_body_local] >>
  `in_np_body orig_bi b_orig` by metis_tac[from_block_imp_in_np_body_local] >>
  `ALL_DISTINCT (MAP (\i:instruction. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by metis_tac[all_distinct_map_filter] >>
  `MEM (LAST (FILTER is_barrier pfx)) pfx`
    by metis_tac[LAST_MEM, MEM_FILTER] >>
  `MEM b_orig (FILTER is_barrier pfx)` by metis_tac[MEM_FILTER] >>
  `b_orig <> LAST (FILTER is_barrier pfx)` by (
    CCONTR_TAC >> fs[] >> metis_tac[]) >>
  `?pfx_pre pfx_post. pfx = pfx_pre ++ [LAST (FILTER is_barrier pfx)] ++ pfx_post /\
                      MEM b_orig pfx_pre`
    by (irule barrier_before_last_barrier >> simp[]) >>
  `MEM y.inst_id (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (fs[in_np_body_def] >> metis_tac[]) >>
  `MEM b_orig.inst_id (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (simp[MEM_MAP] >> qexists_tac `b_orig` >> simp[MEM_FILTER]) >>
  `?pre post. MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi) =
              pre ++ [y.inst_id] ++ post /\ MEM b_orig.inst_id pre`
    by (
      `FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi =
       pfx_pre ++ [LAST (FILTER is_barrier pfx)] ++ (pfx_post ++ [mid] ++ sfx)`
        by simp[] >>
      qexistsl_tac [`MAP (\i:instruction. i.inst_id) pfx_pre`,
                    `MAP (\i:instruction. i.inst_id) (pfx_post ++ [mid] ++ sfx)`] >>
      conj_tac >- (
        once_rewrite_tac[MAP_APPEND] >> simp[MAP_APPEND]) >>
      simp[MEM_MAP] >> qexists_tac `b_orig` >> simp[]) >>
  `from_barrier_dep orig_bi y b_orig` by (
    metis_tac[iffRL from_barrier_dep_def]) >>
  `canonical_dep orig_bi y b_orig` by metis_tac[from_barrier_dep_imp_canonical_dep_local] >>
  `canonical_dep orig_bi yb_c b'` by (
    irule canonical_dep_inst_id_equiv_filtered >> simp[] >>
    qexistsl_tac [`y`, `b_orig`] >> simp[]) >>
  `is_barrier yb_c` by metis_tac[is_barrier_from_inst_id_cross_bi] >>
  `b' <> yb_c` by (
    CCONTR_TAC >> fs[] >>
    `b'.inst_id = yb_c.inst_id` by fs[] >>
    `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by (
      qpat_assum `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
        (fn th => simp[th, MEM_APPEND])) >>
    `MEM yb_c (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by (
      qpat_assum `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
        (fn th => simp[th, MEM_APPEND])) >>
    metis_tac[all_distinct_map_mem_inj]) >>
  `LAST (FILTER is_barrier px_c) <> yb_c` by simp[] >>
  `?px_c_pre px_c_post. px_c = px_c_pre ++ [b'] ++ px_c_post /\ MEM yb_c px_c_pre`
    by metis_tac[barrier_before_last_barrier] >>
  `?cpfx csfx. FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = cpfx ++ [b'] ++ csfx /\
               MEM yb_c cpfx`
    by (qexistsl_tac [`px_c_pre`, `px_c_post ++ [px_b] ++ sfx_x`] >> simp[]) >>
  metis_tac[topo_sorted_prefix_dep]
QED

(* Helper: barrier in sfx implies from_barrier_dep to x *)
Triviality barrier_in_sfx_from_barrier_dep[local]:
  !orig_bi pfx mid sfx b_orig x l1 l2.
    ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi = pfx ++ [mid] ++ sfx /\
    mid.inst_id = x.inst_id /\
    in_np_body orig_bi b_orig /\ in_np_body orig_bi x /\
    is_barrier b_orig /\
    MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi) = l1 ++ [b_orig.inst_id] ++ l2 /\
    MEM b_orig sfx /\
    b_orig.inst_id <> x.inst_id ==>
    MEM x.inst_id l1
Proof
  rpt gen_tac >> strip_tac >>
  metis_tac[map_split_mem_before]
QED

(* Case B: b_orig in sfx -- b_orig depends on mid (barrier dep),
   transfer to b'->px_b, but b' before px_b in cur_bi -> topo_sorted violation *)
Triviality contra_b_orig_in_sfx[local]:
  !orig_bi cur_bi x y pfx sfx mid px_c px_b sfx_x yb_c b' b_orig.
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi = pfx ++ [mid] ++ sfx /\
    mid.inst_id = x.inst_id /\
    ~is_barrier x /\ is_barrier y /\
    from_block orig_bi x /\ from_block orig_bi y /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x /\
    px_b.inst_id = x.inst_id /\
    is_barrier b' /\ from_block orig_bi b' /\ MEM b' px_c /\
    b'.inst_id <> y.inst_id /\
    MEM b_orig (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi) /\
    b_orig.inst_id = b'.inst_id /\
    is_barrier b_orig /\ from_block orig_bi b_orig /\
    MEM b_orig sfx /\
    from_block orig_bi px_b ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  `b_orig.inst_id <> x.inst_id` by metis_tac[is_barrier_from_inst_id_cross_bi] >>
  `in_np_body orig_bi b_orig` by metis_tac[from_block_imp_in_np_body_local] >>
  `in_np_body orig_bi x` by metis_tac[from_block_imp_in_np_body_local] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by metis_tac[all_distinct_map_filter] >>
  `MEM b_orig.inst_id (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (simp[MEM_MAP] >> qexists_tac `b_orig` >> simp[]) >>
  `?l1 l2.
     MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi) =
       l1 ++ [b_orig.inst_id] ++ l2`
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  `MEM x.inst_id l1` by
    (drule_all barrier_in_sfx_from_barrier_dep >> simp[]) >>
  `canonical_dep orig_bi b_orig x` by (
    irule from_barrier_dep_imp_canonical_dep_local >>
    simp[from_barrier_dep_def] >>
    qexistsl_tac [`l1`, `l2`] >> simp[]) >>
  `canonical_dep orig_bi b' px_b` by (
    irule canonical_dep_inst_id_equiv_filtered >> simp[] >>
    qexistsl_tac [`b_orig`,`x`] >> simp[]) >>
  metis_tac[topo_sorted_prefix_dep]
QED

Triviality last_barrier_not_y_contra[local]:
  !orig_bi cur_bi x y pfx sfx mid px_c px_b sfx_x yb_c b'.
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi = pfx ++ [mid] ++ sfx /\
    mid.inst_id = x.inst_id /\
    FILTER is_barrier pfx <> [] /\
    (LAST (FILTER is_barrier pfx)).inst_id = y.inst_id /\
    ~is_barrier x /\ is_barrier y /\
    from_block orig_bi x /\ from_block orig_bi y /\
    PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi))
         (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    (!z. MEM z (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==> from_block orig_bi z) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x /\
    px_b.inst_id = x.inst_id /\
    MEM yb_c px_c /\ yb_c.inst_id = y.inst_id /\
    is_barrier b' /\ from_block orig_bi b' /\ MEM b' px_c /\
    b'.inst_id <> y.inst_id /\
    FILTER is_barrier px_c <> [] /\
    LAST (FILTER is_barrier px_c) = b' ==>
    F
Proof
  rpt gen_tac >> strip_tac >>
  `b'.inst_id <> x.inst_id` by metis_tac[is_barrier_from_inst_id_cross_bi] >>
  `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by (
    qpat_assum `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
      (fn th => simp[th, MEM_APPEND])) >>
  `MEM yb_c (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by (
    qpat_assum `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
      (fn th => simp[th, MEM_APPEND])) >>
  `MEM px_b (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by (
    qpat_assum `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
      (fn th => simp[th, MEM_APPEND])) >>
  `from_block orig_bi yb_c` by metis_tac[] >>
  `from_block orig_bi px_b` by metis_tac[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by metis_tac[all_distinct_map_filter] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi))`
    by metis_tac[all_distinct_map_filter] >>
  `MEM b'.inst_id (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))` by (
    qpat_x_assum `PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi))
         (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
      (fn th => mp_tac (MATCH_MP PERM_MEM_EQ th)) >>
    simp[MEM_MAP, PULL_EXISTS] >> metis_tac[MEM_FILTER]) >>
  `?b_orig. MEM b_orig (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi) /\ b_orig.inst_id = b'.inst_id`
    by metis_tac[MEM_MAP, PULL_EXISTS] >>
  `from_block orig_bi b_orig` by metis_tac[from_block_MEM_filter] >>
  `is_barrier b_orig` by metis_tac[is_barrier_from_inst_id_cross_bi] >>
  `MEM b_orig pfx \/ MEM b_orig sfx` by metis_tac[mem_orig_filter_split] >>
  Cases_on `MEM b_orig pfx`
  >- (qspecl_then [`orig_bi`, `cur_bi`, `x`, `y`, `pfx`, `sfx`, `mid`,
        `px_c`, `px_b`, `sfx_x`, `yb_c`, `b'`, `b_orig`] mp_tac
        contra_b_orig_in_pfx >>
      (impl_tac >- ASM_REWRITE_TAC[]) >> simp[]) >>
  `MEM b_orig sfx` by fs[] >>
  qspecl_then [`orig_bi`, `cur_bi`, `x`, `y`, `pfx`, `sfx`, `mid`,
    `px_c`, `px_b`, `sfx_x`, `yb_c`, `b'`, `b_orig`] mp_tac
    contra_b_orig_in_sfx >>
  (impl_tac >- ASM_REWRITE_TAC[]) >> simp[]
QED

Triviality last_barrier_in_prefix_eq_y[local]:
  !orig_bi cur_bi x y pfx sfx mid px_c px_b sfx_x yb_c.
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi = pfx ++ [mid] ++ sfx /\
    mid.inst_id = x.inst_id /\
    FILTER is_barrier pfx <> [] /\
    (LAST (FILTER is_barrier pfx)).inst_id = y.inst_id /\
    ~is_barrier x /\ is_barrier y /\
    from_block orig_bi x /\ from_block orig_bi y /\
    PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi))
         (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    (!z. MEM z (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==> from_block orig_bi z) /\
    FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x /\
    px_b.inst_id = x.inst_id /\
    MEM yb_c px_c /\ yb_c.inst_id = y.inst_id /\
    FILTER is_barrier px_c <> [] ==>
    LAST (FILTER is_barrier px_c) = yb_c
Proof
  rpt strip_tac >>
  qabbrev_tac `b' = LAST (FILTER is_barrier px_c)` >>
  `MEM b' (FILTER is_barrier px_c)` by metis_tac[LAST_MEM] >>
  `MEM b' px_c` by fs[MEM_FILTER] >>
  `MEM b' (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by (
    qpat_assum `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
      (fn th => simp[th, MEM_APPEND])) >>
  `from_block orig_bi b'` by metis_tac[] >>
  `is_barrier b'` by fs[MEM_FILTER] >>
  `b'.inst_id <> x.inst_id` by metis_tac[is_barrier_from_inst_id_cross_bi] >>
  `FILTER is_barrier px_c <> []` by (Cases_on `FILTER is_barrier px_c` >> fs[]) >>
  `LAST (FILTER is_barrier px_c) = b'` by simp[Abbr `b'`] >>
  Cases_on `b'.inst_id = y.inst_id` >- (
    `ALL_DISTINCT (MAP (\i:instruction. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi))`
      by metis_tac[all_distinct_map_filter] >>
    `MEM yb_c (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi)` by (
      qpat_assum `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
        (fn th => simp[th, MEM_APPEND])) >>
    `b'.inst_id = yb_c.inst_id` by metis_tac[] >>
    `b' = yb_c` by (
      qspecl_then [`\i:instruction. i.inst_id`,
        `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi`,`b'`,`yb_c`]
        mp_tac all_distinct_map_mem_inj >> simp[]) >>
    simp[Abbr `b'`]
  ) >>
  metis_tac[last_barrier_not_y_contra]
QED

(* Case 3: on_barrier_dep under PERM + topo_sorted *)
Triviality on_barrier_dep_imp_full_dep_current[local]:
  !orig_bi cur_bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    on_barrier_dep orig_bi x y /\
    from_block orig_bi x /\ from_block orig_bi y /\
    PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi))
         (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    topo_sorted (canonical_dep orig_bi)
      (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) /\
    (!z. MEM z (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==>
       from_block orig_bi z) ==>
    full_dep (build_full_eda cur_bi) x y
Proof
  rpt strip_tac >>
  `canonical_dep orig_bi x y` by metis_tac[on_barrier_dep_imp_canonical_dep_local] >>
  simp[full_dep_def] >> disj1_tac >>
  fs[on_barrier_dep_def] >>
  qabbrev_tac `fl = FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi` >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by metis_tac[all_distinct_map_filter] >>
  `MEM x.inst_id (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (fs[in_np_body_def, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  `MEM y.inst_id (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (fs[in_np_body_def, MEM_MAP, MEM_FILTER] >> metis_tac[]) >>
  `MEM x.inst_id (MAP (\i. i.inst_id) fl)`
    by metis_tac[PERM_MEM_EQ, Abbr `fl`] >>
  `MEM y.inst_id (MAP (\i. i.inst_id) fl)`
    by metis_tac[PERM_MEM_EQ, Abbr `fl`] >>
  `?pfx_fl sfx_fl. MAP (\i. i.inst_id) fl = pfx_fl ++ [x.inst_id] ++ sfx_fl`
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  `?px_c px_b sfx_x. fl = px_c ++ [px_b] ++ sfx_x /\
                       MAP (\i. i.inst_id) px_c = pfx_fl /\
                       px_b.inst_id = x.inst_id /\
                       MAP (\i. i.inst_id) sfx_x = sfx_fl`
    by metis_tac[MAP_INST_ID_APPEND_SPLIT_exists_local] >>
  `from_block orig_bi px_b` by (
    first_x_assum $ qspecl_then [`px_b`] mp_tac >>
    simp[Abbr `fl`, MEM_APPEND] >> metis_tac[]) >>
  `~is_barrier px_b` by metis_tac[is_barrier_from_inst_id_cross_bi] >>
  `x.inst_id <> y.inst_id` by metis_tac[is_barrier_from_inst_id_cross_bi] >>
  `?yb_c. MEM yb_c px_c /\ yb_c.inst_id = y.inst_id`
    by metis_tac[yb_c_in_px_c] >>
  `from_block orig_bi yb_c` by (
    first_x_assum $ qspecl_then [`yb_c`] mp_tac >>
    simp[Abbr `fl`, MEM_APPEND] >> metis_tac[]) >>
  `is_barrier yb_c` by metis_tac[is_barrier_from_inst_id_cross_bi] >>
  `FILTER is_barrier px_c <> []` by (
    `MEM yb_c (FILTER is_barrier px_c)` by simp[MEM_FILTER] >>
    Cases_on `FILTER is_barrier px_c` >> fs[]) >>
  `LAST (FILTER is_barrier px_c) = yb_c` by (
    irule last_barrier_in_prefix_eq_y >> simp[] >> metis_tac[]) >>
  `FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi = px_c ++ [px_b] ++ sfx_x`
    by (simp[Abbr `fl`]) >>
  `eda_dep (build_full_eda cur_bi) px_b yb_c` by metis_tac[on_barrier_to_eda_dep_apply] >>
  metis_tac[eda_dep_inst_id_only]
QED

(* THE MASTER BRIDGE: canonical_dep ⊆ full_dep (cross-bi) *)
Triviality canonical_dep_imp_full_dep_current[local]:
  !orig_bi cur_bi x y.
    ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) cur_bi) /\
    canonical_dep orig_bi x y /\
    from_block orig_bi x /\ from_block orig_bi y /\
    (!z. MEM z (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==> from_block orig_bi z) /\
    PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi))
         (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi)) /\
    topo_sorted (canonical_dep orig_bi) (FILTER (\i. ~is_pseudo i.inst_opcode) cur_bi) ==>
    full_dep (build_full_eda cur_bi) x y
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `canonical_dep _ _ _` mp_tac >>
  simp[canonical_dep_def] >> rpt strip_tac
  (* Case 1: data_dep_body -- order-independent *)
  >- (simp[full_dep_def] >> disj2_tac >> disj1_tac >>
      fs[data_dep_body_def, inst_uses_def, inst_defs_def, IN_DISJOINT] >>
      qexists `v` >> fs[MEM_operand_vars_iff])
  (* Case 2: from_barrier_dep -- extracted helper *)
  >- metis_tac[from_barrier_dep_imp_full_dep_current]
  (* Case 3: on_barrier_dep -- extracted helper *)
  >- metis_tac[on_barrier_dep_imp_full_dep_current]
QED



(* dft_block output satisfies canonical_topo_inv for a single block *)
Triviality dft_block_preserves_canonical_topo_local[local]:
  !fn bb_orig bb_cur order.
    wf_ssa fn /\ wf_function fn /\
    MEM bb_orig fn.fn_blocks /\
    block_perm_of fn bb_cur /\
    bb_cur.bb_label = bb_orig.bb_label /\
    dft_inv [bb_cur] /\
    topo_sorted (canonical_dep bb_orig.bb_instructions)
      (FILTER (\i. ~is_pseudo i.inst_opcode) bb_cur.bb_instructions) ==>
    topo_sorted (canonical_dep bb_orig.bb_instructions)
      (FILTER (\i. ~is_pseudo i.inst_opcode)
         (dft_block order bb_cur).bb_instructions)
Proof
  rpt strip_tac >>
  qabbrev_tac `bi = bb_cur.bb_instructions` >>
  qabbrev_tac `orig_bi = bb_orig.bb_instructions` >>
  qabbrev_tac `eda = build_full_eda bi` >>
  qabbrev_tac `om = build_offspring_map bi order` >>
  qabbrev_tac `entries = entry_instructions bi order eda` >>
  qabbrev_tac `sched = schedule_from_entries bi order eda om entries` >>
  (* Step 1: dft_block filter decomposition *)
  `FILTER (\i. ~is_pseudo i.inst_opcode) (dft_block order bb_cur).bb_instructions = sched`
    by (simp[Abbr `bi`, Abbr `sched`, Abbr `eda`, Abbr `om`,
             Abbr `entries`, dft_block_filter_nonpseudo]) >>
  (* Step 2: Pre-conditions for scheduler lemmas *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) bi)` by fs[dft_inv_def, Abbr `bi`] >>
  `eda_wf eda bi` by simp[Abbr `eda`, Abbr `bi`, build_full_eda_wf] >>
  `eda_topo_compatible bi eda order` by
    (simp[Abbr `eda`] >>
     qspecl_then [`bi`, `order`] mp_tac eda_topo_compatible_gen_weak >>
     simp[Abbr `bi`, non_pseudo_defs_before_uses_def] >> disch_then irule >> fs[dft_inv_def, bb_well_formed_def, non_pseudo_defs_before_uses_def]) >>
  `EVERY (\i. MEM i bi) entries`
    by simp[Abbr `entries`, Abbr `bi`, entry_instructions_mem] >>
  `bi <> []` by fs[dft_inv_def, bb_well_formed_def, Abbr `bi`] >>
  `!k. k < LENGTH bi /\ is_terminator (EL k bi).inst_opcode ==>
       k = PRE (LENGTH bi)`
    by fs[dft_inv_def, bb_well_formed_def, Abbr `bi`] >>
  `np_defs_before_uses bi`
    by gvs[dft_inv_def, non_pseudo_defs_before_uses_def, Abbr `bi`] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bi))`
    by metis_tac[block_perm_inst_outputs_local] >>
  (* Step 3: Schedule output properties — all via extracted Trivialities *)
  `ALL_DISTINCT (MAP (\j. j.inst_id) sched)`
    by metis_tac[sched_output_distinct_local] >>
  `output_producer_before bi sched`
    by metis_tac[sched_output_producer_local] >>
  `output_eda_before eda sched`
    by metis_tac[sched_output_eda_local] >>
  `!i. MEM i sched ==> from_block bi i /\ ~is_pseudo i.inst_opcode`
    by metis_tac[sched_mem_from_block_cur_local] >>
  (* Step 4: Topo-sorted from scheduler — already have this *)
  `topo_sorted (full_dep eda) sched`
    by metis_tac[sched_topo_sorted_local] >>
  (* Step 5: Single-step bridge: canonical_dep < full_dep, no TC *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (simp[Abbr `orig_bi`] >>
        `ALL_DISTINCT (MAP (\i. i.inst_id) bb_orig.bb_instructions)`
          by metis_tac[wf_fn_block_inst_ids_distinct] >>
        metis_tac[all_distinct_map_filter]) >>
  `EVERY (\i. from_block orig_bi i) (FILTER (\i. ~is_pseudo i.inst_opcode) bi) /\
    PERM (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) bi))
         (MAP (\i. i.inst_id) (FILTER (\i. ~is_pseudo i.inst_opcode) orig_bi))`
    by (unabbrev_all_tac >>
        metis_tac[block_perm_of_elim]) >>
  `!i. MEM i sched ==> from_block orig_bi i`
    by metis_tac[sched_mem_from_block_orig_local] >>
  `!i. MEM i sched ==> from_block bi i`
    by metis_tac[sched_mem_from_block_cur_local] >>
  `!i. MEM i sched ==> ~is_pseudo i.inst_opcode`
    by metis_tac[sched_mem_from_block_cur_local] >>
  (* Final: monotonicity with single-step bridge *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) orig_bi)`
    by (simp[Abbr `orig_bi`] >>
        metis_tac[wf_fn_block_inst_ids_distinct]) >>
  irule topo_sorted_mono_restricted_local >>
  qexists_tac `full_dep eda` >> simp[] >>
  rpt strip_tac >>
  `from_block orig_bi x` by metis_tac[sched_mem_from_block_orig_local] >>
  `from_block orig_bi y` by metis_tac[sched_mem_from_block_orig_local] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bi)` by fs[dft_inv_def, Abbr `bi`] >>
  `!z. MEM z (FILTER (\i. ~is_pseudo i.inst_opcode) bi) ==> from_block orig_bi z`
    by metis_tac[EVERY_MEM] >>
  simp[Abbr `eda`] >>
  drule_all canonical_dep_imp_full_dep_current >> simp[]
QED
(* dft_process_one preserves canonical_topo_inv *)
Triviality every_map_replace_canonical[local]:
  !fn bbs lbl bb'.
    wf_ssa fn /\ wf_function fn /\
    canonical_topo_inv fn bbs /\ all_blocks_perm_of fn bbs /\
    dft_inv bbs /\ MEM bb' bbs /\ bb'.bb_label = lbl ==>
    canonical_topo_inv fn
      (MAP (\b. if b.bb_label = lbl then dft_block order bb' else b) bbs)
Proof
  simp[canonical_topo_inv_def] >> rpt strip_tac >>
  qpat_x_assum `MEM b (MAP _ bbs)` mp_tac >>
  simp[MEM_MAP, PULL_EXISTS] >> qx_gen_tac `a` >> strip_tac >>
  Cases_on `a.bb_label = bb'.bb_label` >> simp[]
  >- ((* changed block: b = dft_block order bb' *)
      qpat_x_assum `!bb. MEM bb bbs ==> _` (qspec_then `bb'` mp_tac) >>
      simp[] >> strip_tac >>
      qexists_tac `bb_orig` >> simp[dft_block_label] >>
      `block_perm_of fn bb'` by metis_tac[all_blocks_perm_of_def, EVERY_MEM] >>
      `bb_well_formed bb'` by fs[dft_inv_def, EVERY_MEM] >>
      `ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions)`
        by fs[dft_inv_def, EVERY_MEM] >>
      `non_pseudo_defs_before_uses bb'.bb_instructions`
        by fs[dft_inv_def, EVERY_MEM] >>
      irule dft_block_preserves_canonical_topo_local >>
      conj_tac >- fs[dft_inv_def, EVERY_MEM] >>
      conj_tac >- simp[] >>
      conj_tac >- (qexists_tac `fn` >> simp[]) >>
      simp[])
  >> ((* unchanged block: b = a *)
      qpat_x_assum `!bb. MEM bb bbs ==> _` (qspec_then `a` assume_tac) >>
      fs[] >> qexists_tac `bb_orig` >> simp[])
QED

Triviality dft_process_one_preserves_canonical_topo[local]:
  !cfg lr fn st lbl.
    wf_ssa fn /\ wf_function fn /\
    canonical_topo_inv fn st.dls_blocks /\ all_blocks_perm_of fn st.dls_blocks /\
    dft_inv st.dls_blocks ==>
    canonical_topo_inv fn (FST (dft_process_one cfg lr fn st lbl)).dls_blocks
Proof
  rw[dft_process_one_def, LET_THM] >>
  Cases_on `lookup_block lbl st.dls_blocks` >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  ho_match_mp_tac every_map_replace_canonical >>
  simp[] >>
  imp_res_tac lookup_block_label >> simp[] >>
  fs[lookup_block_def] >>
  imp_res_tac venomExecPropsTheory.FIND_MEM >> simp[]
QED

Triviality dft_loop_step_preserves_canonical_topo[local]:
  !cfg lr fn trip.
    wf_ssa fn /\ wf_function fn /\
    canonical_topo_inv fn (FST trip).dls_blocks /\
    all_blocks_perm_of fn (FST trip).dls_blocks /\
    dft_inv (FST trip).dls_blocks ==>
    canonical_topo_inv fn (FST (dft_loop_step cfg lr fn trip)).dls_blocks
Proof
  rpt gen_tac >> PairCases_on `trip` >>
  simp[dft_loop_step_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `trip1` >> simp[] >> strip_tac >>
  Cases_on `dft_process_one cfg lr fn trip0 h` >>
  Cases_on `r` >> simp[] >>
  qspecl_then [`cfg`,`lr`,`fn`,`trip0`,`h`]
    mp_tac dft_process_one_preserves_canonical_topo >>
  simp[] >> strip_tac >>
  IF_CASES_TAC >> simp[]
QED

Triviality funpow_dft_loop_preserves_canonical_topo[local]:
  !n cfg lr fn trip.
    wf_ssa fn /\ wf_function fn /\
    canonical_topo_inv fn (FST trip).dls_blocks /\
    all_blocks_perm_of fn (FST trip).dls_blocks /\
    dft_inv (FST trip).dls_blocks ==>
    canonical_topo_inv fn
      (FST (FUNPOW (dft_loop_step cfg lr fn) n trip)).dls_blocks
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  MATCH_MP_TAC dft_loop_step_preserves_canonical_topo >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (first_x_assum MATCH_MP_TAC >> simp[] >>
      MATCH_MP_TAC funpow_dft_loop_preserves_perm >> simp[]) >>
  conj_tac >- (MATCH_MP_TAC funpow_dft_loop_preserves_perm >> simp[]) >>
  MATCH_MP_TAC funpow_dft_loop_preserves_inv >> simp[]
QED

Theorem dft_fn_canonical_topo_inv:
  !fn. wf_ssa fn /\ wf_function fn ==>
    canonical_topo_inv fn (dft_fn fn).fn_blocks
Proof
  rpt strip_tac >>
  simp[dft_fn_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[] >>
  MATCH_MP_TAC funpow_dft_loop_preserves_canonical_topo >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- (simp[canonical_topo_inv_def, EVERY_MEM] >>
      rpt strip_tac >> qexists_tac `bb` >> simp[] >>
      irule orig_filter_canonical_topo_sorted_local >>
      fs[wf_function_def] >> metis_tac[]) >>
  conj_tac >- simp[all_blocks_perm_of_def, EVERY_MEM, original_block_perm_of] >>
  simp[] >> irule wf_fn_initial_dft_inv >> simp[]
QED

(* Filtering a topologically sorted list preserves topo_sorted.
   FILTER preserves relative order, so for i < j in the filtered list,
   there exist i' < j' in the original list with the same elements. *)
Theorem topo_sorted_FILTER:
  !dep P l. topo_sorted dep l ==> topo_sorted dep (FILTER P l)
Proof
  rw[topo_sorted_def] >>
  qspecl_then [`P`, `l`, `i`, `j`] mp_tac filter_el_mono >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [`i'`, `j'`] mp_tac) >>
  simp[]
QED
