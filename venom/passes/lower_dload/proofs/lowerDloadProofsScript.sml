(*
 * Lower DLOAD Pass -- Proofs
 *
 * Direct fuel-induction proof. No dependency on passSimulationProps
 * (avoids expensive rebuild). Inlines the block_sim_function_rel
 * argument: fuel induction, R_ok-related two-state IH.
 *
 * Key precondition: ld_no_mem_read -- no original instruction reads
 * vs_memory (or allocas/returndata-dependent state). With this, no
 * mem_compat needed in the cross-block invariant (ld_ok).
 *)

Theory lowerDloadProofs
Ancestors
  lowerDloadClassify venomWf analysisSimDefs
  lowerDloadDefs stateEquiv venomExecSemantics passSimulationDefs
  venomExecProps venomInst venomState venomInstProps instIdxIndep
  finite_map words list rich_list

val dim256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

(* dimword(:256) = 2^256 and related facts *)
val dimword_256_ss = simpLib.rewrites
  [dim256, dimword_def];

(* ===== Transform structure ===== *)

Theorem lower_dload_block_label[local]:
  !bb. (lower_dload_block bb).bb_label = bb.bb_label
Proof
  simp[lower_dload_block_def]
QED

Theorem lookup_block_map[local]:
  !lbl bbs bt.
    (!bb. (bt bb).bb_label = bb.bb_label) ==>
    lookup_block lbl (MAP bt bbs) =
      OPTION_MAP bt (lookup_block lbl bbs)
Proof
  gen_tac >> Induct >>
  simp[lookup_block_def, listTheory.FIND_thm] >>
  rw[] >> res_tac >> fs[lookup_block_def]
QED

Theorem lookup_block_lower_dload:
  !lbl bbs.
    lookup_block lbl (MAP lower_dload_block bbs) =
      OPTION_MAP lower_dload_block (lookup_block lbl bbs)
Proof
  rpt gen_tac >> irule lookup_block_map >> simp[lower_dload_block_def]
QED

Theorem lower_dload_function_blocks:
  !fn. (lower_dload_function fn).fn_blocks =
       MAP lower_dload_block fn.fn_blocks
Proof
  simp[lower_dload_function_def, function_map_transform_def]
QED

Theorem lookup_block_MEM:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >>
  rw[lookup_block_def, listTheory.FIND_thm] >>
  DISJ2_TAC >>
  first_x_assum (qspecl_then [`lbl`, `bb`] mp_tac) >>
  simp[lookup_block_def]
QED

(* ===== code_layout_valid preservation ===== *)

Theorem step_jmp_ok_preserves_layout:
  !fuel ctx inst s s'.
    inst.inst_opcode = JMP /\
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_def] >> ASM_REWRITE_TAC[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >> simp[jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >> rw[] >> gvs[]
QED

Theorem step_jnz_ok_preserves_layout[local]:
  !fuel ctx inst s s'.
    inst.inst_opcode = JNZ /\
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_def] >> ASM_REWRITE_TAC[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >> simp[jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >> rw[] >> gvs[]
QED

Theorem step_djmp_ok_preserves_layout[local]:
  !fuel ctx inst s s'.
    inst.inst_opcode = DJMP /\
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst fuel ctx inst s = OK s'` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_def] >> ASM_REWRITE_TAC[] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >> simp[jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >> rw[] >> gvs[]
QED

val term_ok_jump_tac =
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[eval_operands_def, eval_operand_def, AllCaseEqs()] >>
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

Theorem step_non_ok_terminator[local]:
  !fuel ctx inst s s'.
    (inst.inst_opcode = RET \/
     inst.inst_opcode = RETURN \/
     inst.inst_opcode = REVERT \/
     inst.inst_opcode = STOP \/
     inst.inst_opcode = SINK \/
     inst.inst_opcode = SELFDESTRUCT \/
     inst.inst_opcode = INVALID) ==>
    step_inst fuel ctx inst s <> OK s'
Proof
  rpt strip_tac >> CCONTR_TAC >>
  `is_terminator inst.inst_opcode` by gvs[is_terminator_def] >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  `step_inst_base inst s = OK s'` by
    metis_tac[step_inst_non_invoke] >>
  drule_all step_inst_base_ok_terminator_jump >>
  strip_tac >> gvs[]
QED

Theorem step_term_ok_preserves[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (strip_tac >> gvs[is_terminator_def]) >>
  `step_inst_base inst s = OK s'` by
    metis_tac[step_inst_non_invoke] >>
  `inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
   inst.inst_opcode = DJMP` by
    metis_tac[step_inst_base_ok_terminator_jump] >>
  metis_tac[step_jmp_ok_preserves_layout,
            step_jnz_ok_preserves_layout,
            step_djmp_ok_preserves_layout]
QED

Theorem step_inst_preserves_layout:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==>
    s'.vs_code = s.vs_code /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_labels = s.vs_labels
Proof
  metis_tac[step_term_ok_preserves,
            step_preserves_code, step_preserves_data_section,
            step_inst_preserves_labels_always]
QED

(* exec_block preserves layout: strong induction on remaining instructions *)
Theorem exec_block_preserves_layout_aux[local]:
  !n f c bb st st'.
    n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
    exec_block f c bb st = OK st' ==>
    st'.vs_code = st.vs_code /\
    st'.vs_data_section = st.vs_data_section /\
    st'.vs_labels = st.vs_labels
Proof
  completeInduct_on `n` >> rw[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def] >>
  Cases_on `st.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[] >>
  Cases_on `step_inst f c (EL st.vs_inst_idx bb.bb_instructions) st` >>
  simp[] >>
  Cases_on `is_terminator (EL st.vs_inst_idx bb.bb_instructions).inst_opcode` >>
  simp[] >>
  TRY (Cases_on `v.vs_halted` >> gvs[] >>
       metis_tac[step_inst_preserves_layout]) >>
  strip_tac >>
  drule step_inst_preserves_layout >> strip_tac >>
  first_x_assum (qspecl_then
    [`LENGTH bb.bb_instructions - SUC st.vs_inst_idx`] mp_tac) >>
  simp[] >>
  disch_then (qspecl_then
    [`f`, `c`, `bb`,
     `v with vs_inst_idx := SUC st.vs_inst_idx`, `st'`]
    mp_tac) >> simp[]
QED

Theorem exec_block_preserves_layout_fields:
  !fuel ctx bb s v.
    exec_block fuel ctx bb s = OK v ==>
    v.vs_code = s.vs_code /\
    v.vs_data_section = s.vs_data_section /\
    v.vs_labels = s.vs_labels
Proof
  metis_tac[exec_block_preserves_layout_aux]
QED

Theorem exec_block_preserves_code_layout_valid:
  !fuel ctx bb s v.
    exec_block fuel ctx bb s = OK v /\
    code_layout_valid s ==>
    code_layout_valid v
Proof
  rpt strip_tac >>
  drule exec_block_preserves_layout_fields >> strip_tac >>
  gvs[code_layout_valid_def] >>
  qexists_tac `prefix` >> simp[]
QED

Theorem step_inst_preserves_code_layout_valid:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    code_layout_valid s ==>
    code_layout_valid s'
Proof
  rpt strip_tac >>
  drule step_inst_preserves_layout >> strip_tac >>
  gvs[code_layout_valid_def] >> qexists_tac `prefix` >> simp[]
QED

(* ===== run_insts infrastructure (local) ===== *)

(* step_inst for non-term non-INVOKE is idx-independent *)
Theorem step_inst_idx_indep_local:
  !fuel ctx inst s n.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (step_inst fuel ctx inst s)
Proof
  rw[step_inst_non_invoke, step_inst_inst_idx_indep]
QED

(* run_insts on non-term non-INVOKE instructions is idx-independent *)
Theorem run_insts_idx_indep_local[local]:
  !insts fuel ctx s n.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    run_insts fuel ctx insts (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (run_insts fuel ctx insts s)
Proof
  Induct >> simp[run_insts_def, exec_result_map_def] >>
  rpt gen_tac >> strip_tac >>
  simp[run_insts_def, step_inst_idx_indep_local] >>
  Cases_on `step_inst fuel ctx h s` >>
  simp[exec_result_map_def] >>
  `v.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `n`] mp_tac) >>
  simp[] >> strip_tac >> simp[exec_result_map_def]
QED

(* exec_block_skip_prefix: if run_insts succeeds on prefix, skip it *)
Theorem exec_block_skip_prefix_local:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
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
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep_local] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`,
    `SUC j`, `s'`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac >- (
    rw[] >>
    first_x_assum (qspec_then `SUC k` mp_tac) >> simp[arithmeticTheory.ADD_CLAUSES]
  ) >> simp[]
QED

(* run_insts preserves layout fields *)
Theorem run_insts_preserves_layout[local]:
  !insts fuel ctx s v.
    run_insts fuel ctx insts s = OK v ==>
    v.vs_code = s.vs_code /\
    v.vs_data_section = s.vs_data_section /\
    v.vs_labels = s.vs_labels
Proof
  Induct >> simp[run_insts_def] >> rpt gen_tac >>
  Cases_on `step_inst fuel ctx h s` >> simp[] >>
  strip_tac >>
  drule step_inst_preserves_layout >> strip_tac >>
  res_tac >> simp[]
QED

Theorem run_insts_preserves_code_layout_valid:
  !insts fuel ctx s v.
    run_insts fuel ctx insts s = OK v /\
    code_layout_valid s ==>
    code_layout_valid v
Proof
  rpt strip_tac >>
  drule run_insts_preserves_layout >> strip_tac >>
  gvs[code_layout_valid_def] >> qexists_tac `prefix` >> simp[]
QED

(* ===== Terminator simulation ===== *)

(* Running the same terminator from ld_ok states gives lift_result results. *)
(* Shared tactics for terminator proof *)
fun ld_agree_op q =
  drule ld_eval_operand_agree >>
  disch_then (qspec_then q mp_tac) >>
  (impl_tac >- (rw[] >> res_tac)) >>
  strip_tac >> gvs[];

fun ld_agree_all_tac (asl, w) = let
  val ldok = valOf (List.find (can (match_term ``ld_ok vars s1 s2``)) asl)
  val (_, args) = strip_comb ldok
  val s1_tm = el 2 args
  val eval_pat = ``eval_operand (op:operand) ^s1_tm = SOME (v:bytes32)``
  val evals = List.filter (can (match_term eval_pat)) asl
  fun agree_one eval_asm = let
    val (_, args2) = strip_comb (lhs eval_asm)
    val op_tm = el 1 args2
  in (* agree_one let body *)
    drule ld_eval_operand_agree >>
    disch_then (qspec_then [QUOTE (term_to_string op_tm)] mp_tac) >>
    (impl_tac >- (rw[] >> res_tac)) >>
    strip_tac >> gvs[]
  end
in
  (EVERY (map agree_one evals)) (asl, w)
end;

(* Helper: jump_to preserves ld_ok *)
Theorem ld_ok_jump_to[local]:
  !vars lbl s1 s2.
    ld_ok vars s1 s2 ==>
    ld_ok vars (jump_to lbl s1) (jump_to lbl s2)
Proof
  rw[ld_ok_def, jump_to_def, lookup_var_def]
QED

(* Helper: halt_state preserves ld_equiv *)
Theorem ld_equiv_halt_state[local]:
  !vars s1 s2.
    ld_ok vars s1 s2 ==>
    ld_equiv vars (halt_state s1) (halt_state s2)
Proof
  rw[ld_ok_def, ld_equiv_def, halt_state_def, lookup_var_def]
QED

(* Helper: set_returndata + halt/revert preserves ld_equiv *)
Theorem ld_equiv_set_returndata_halt[local]:
  !vars rd1 rd2 s1 s2.
    ld_ok vars s1 s2 ==>
    ld_equiv vars (halt_state (set_returndata rd1 s1))
                  (halt_state (set_returndata rd2 s2))
Proof
  rw[ld_ok_def, ld_equiv_def, halt_state_def, set_returndata_def,
     lookup_var_def]
QED

Theorem ld_equiv_set_returndata_revert[local]:
  !vars rd1 rd2 s1 s2.
    ld_ok vars s1 s2 ==>
    ld_equiv vars (revert_state (set_returndata rd1 s1))
                  (revert_state (set_returndata rd2 s2))
Proof
  rw[ld_ok_def, ld_equiv_def, revert_state_def, set_returndata_def,
     lookup_var_def]
QED

(* Helper: accounts update preserves ld_equiv for SELFDESTRUCT *)
Theorem ld_equiv_accounts_update[local]:
  !vars f s1 s2.
    ld_ok vars s1 s2 ==>
    ld_equiv vars (halt_state (s1 with vs_accounts := f))
                  (halt_state (s2 with vs_accounts := f))
Proof
  rw[ld_ok_def, ld_equiv_def, halt_state_def, lookup_var_def]
QED

(* pack_dret_dynamic changes only memory, which ld_ok deliberately omits. *)
Theorem ld_ok_mcopy[local]:
  !vars dst src sz s1 s2.
    ld_ok vars s1 s2 ==>
    ld_ok vars (mcopy dst src sz s1) (mcopy dst src sz s2)
Proof
  rw[ld_ok_def, mcopy_def, write_memory_with_expansion_def, lookup_var_def]
QED

Theorem pack_dret_dynamic_ld_ok[local]:
  !pairs cursor s1 s2 ptrs1 final1 t1 ptrs2 final2 t2 vars.
    ld_ok vars s1 s2 /\
    pack_dret_dynamic cursor pairs s1 = (ptrs1,final1,t1) /\
    pack_dret_dynamic cursor pairs s2 = (ptrs2,final2,t2) ==>
    ptrs1 = ptrs2 /\ final1 = final2 /\ ld_ok vars t1 t2
Proof
  Induct_on `pairs`
  >- simp[pack_dret_dynamic_def]
  >> rpt gen_tac >> PairCases_on `h`
  >> simp[Once pack_dret_dynamic_def]
  >> Cases_on `pack_dret_dynamic
       (cursor + n2w (ceil32 (w2n h1))) pairs
       (mcopy (w2n cursor) (w2n h0) (w2n h1) s1)`
  >> Cases_on `r`
  >> Cases_on `pack_dret_dynamic
       (cursor + n2w (ceil32 (w2n h1))) pairs
       (mcopy (w2n cursor) (w2n h0) (w2n h1) s2)`
  >> Cases_on `r` >> gvs[pack_dret_dynamic_def]
  >> rpt strip_tac >> gvs[]
  >> `ld_ok vars
        (mcopy (w2n cursor) (w2n h0) (w2n h1) s1)
        (mcopy (w2n cursor) (w2n h0) (w2n h1) s2)` by
       (irule ld_ok_mcopy >> simp[])
  >> first_x_assum drule_all
  >> simp[]
QED
Theorem pack_dret_dynamic_lift_result[local]:
  !vars pairs s1 s2 vals.
    ld_ok vars s1 s2 ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      ((\(ptrs,final_cursor,s').
          IntRet <|iret_values := vals ++ ptrs;
                   iret_adopt_fmp := SOME final_cursor|>
            (s' with vs_fmp := final_cursor))
       (pack_dret_dynamic s1.vs_call_entry_fmp pairs s1))
      ((\(ptrs,final_cursor,s').
          IntRet <|iret_values := vals ++ ptrs;
                   iret_adopt_fmp := SOME final_cursor|>
            (s' with vs_fmp := final_cursor))
       (pack_dret_dynamic s2.vs_call_entry_fmp pairs s2))
Proof
  rpt strip_tac >>
  `s1.vs_call_entry_fmp = s2.vs_call_entry_fmp` by fs[ld_ok_def] >>
  Cases_on `pack_dret_dynamic s1.vs_call_entry_fmp pairs s1` >>
  Cases_on `r` >>
  Cases_on `pack_dret_dynamic s2.vs_call_entry_fmp pairs s2` >>
  Cases_on `r` >> gvs[] >>
  drule_all pack_dret_dynamic_ld_ok >> strip_tac >>
  gvs[lift_result_def, ld_ok_def, ld_equiv_def, lookup_var_def]
QED


(* Shared tactic for terminator opcodes: unfold, case-split, derive
   operand agreements, close with ld_ok/ld_equiv helpers *)
(* Key lemma: under ld_ok, eval_operand agrees for non-exempt vars *)
Theorem ld_eval_operand_eq[local]:
  !op s1 s2 vars.
    ld_ok vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases >> rw[eval_operand_def, ld_ok_def]
QED

(* Core technique: derive operand agreement, unfold, case-split, close *)
val ld_derive_agree_tac =
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2` by
    (rpt strip_tac >> irule ld_eval_operand_eq >>
     qexists_tac `vars` >> rw[] >>
     first_x_assum irule >> gvs[]);

val ld_derive_fields_tac =
  `s2.vs_labels = s1.vs_labels` by fs[ld_ok_def] >>
  `s2.vs_accounts = s1.vs_accounts` by fs[ld_ok_def] >>
  `s2.vs_call_ctx = s1.vs_call_ctx` by fs[ld_ok_def];

Theorem ld_ok_implies_ld_equiv_and_fmp[local]:
  !vars s1 s2.
    ld_ok vars s1 s2 ==>
    ld_equiv vars s1 s2 /\ s1.vs_fmp = s2.vs_fmp
Proof
  rw[ld_ok_def, ld_equiv_def]
QED

val ld_close_tac =
  TRY (irule ld_ok_implies_ld_equiv_and_fmp >> simp[] >> NO_TAC) >>
  TRY (irule pack_dret_dynamic_lift_result >> simp[] >> NO_TAC) >>
  TRY (irule ld_ok_jump_to >> simp[] >> NO_TAC) >>
  TRY (irule ld_equiv_halt_state >> simp[] >> NO_TAC) >>
  TRY (irule ld_equiv_set_returndata_halt >> simp[] >> NO_TAC) >>
  TRY (irule ld_equiv_set_returndata_revert >> simp[] >> NO_TAC) >>
  TRY (irule ld_equiv_accounts_update >> simp[] >> NO_TAC) >>
  TRY (irule ld_ok_implies_ld_equiv >> simp[] >> NO_TAC) >>
  TRY (simp[ld_ok_def, ld_equiv_def, halt_state_def, revert_state_def,
            set_returndata_def, lookup_var_def] >> NO_TAC);

(* eval_operands agrees when each operand agrees *)
Theorem eval_operands_agree[local]:
  !ops s1 s2.
    (!op. MEM op ops ==> eval_operand op s1 = eval_operand op s2) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct >> simp[eval_operands_def] >>
  rpt strip_tac >>
  `eval_operand h s1 = eval_operand h s2` by (res_tac >> gvs[]) >>
  `eval_operands ops s1 = eval_operands ops s2` by
    (first_x_assum irule >> metis_tac[]) >>
  simp[]
QED

(* Per-terminator tactic: unfold, case-split with agreement, close *)
val ld_terminator_tac =
  rpt strip_tac >>
  ld_derive_agree_tac >> ld_derive_fields_tac >>
  simp[step_inst_base_def, LET_THM] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >>
       gvs[] >> TRY (res_tac >> gvs[])) >>
  TRY (`eval_operands inst.inst_operands s1 =
        eval_operands inst.inst_operands s2` by
        (irule eval_operands_agree >> rpt strip_tac >> res_tac >> gvs[]) >>
       gvs[]) >>
  gvs[lift_result_def] >> ld_close_tac;

Theorem step_inst_base_ld_ok_jnz:
  !inst s1 s2 vars.
    inst.inst_opcode = JNZ /\
    ld_ok vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  ld_derive_agree_tac >> ld_derive_fields_tac >>
  simp[step_inst_base_def, LET_THM] >>
  BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def] >>
  TRY (res_tac >> gvs[]) >>
  BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def] >>
  TRY (res_tac >> gvs[]) >>
  BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def] >>
  TRY (res_tac >> gvs[]) >>
  BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def] >>
  TRY (res_tac >> gvs[]) >>
  BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def] >>
  TRY (res_tac >> gvs[]) >>
  BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def] >>
  TRY (res_tac >> gvs[]) >>
  BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def] >>
  TRY (res_tac >> gvs[]) >>
  BasicProvers.PURE_FULL_CASE_TAC >> gvs[lift_result_def] >>
  TRY (res_tac >> gvs[]) >>
  gvs[lift_result_def] >> ld_close_tac
QED

Theorem step_inst_base_ld_ok_dret_success[local]:
  !inst s1 s2 vars q r vals pairs.
    inst.inst_opcode = DRET /\ inst.inst_outputs = [] /\
    ld_ok vars s1 s2 /\
    parse_dret_shape inst = SOME (q,r) /\
    eval_operands inst.inst_operands s1 = SOME vals /\
    eval_operands inst.inst_operands s2 = SOME vals /\
    pair_dret_words (TAKE (2 * r) (DROP (1 + q) vals)) = SOME pairs ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[] >> simp[] >>
  qspecl_then [`vars`, `pairs`, `s1`, `s2`, `TAKE q (DROP 1 vals)`]
    mp_tac pack_dret_dynamic_lift_result >> simp[]
QED

Theorem step_inst_base_ld_ok_dret[local]:
  !inst s1 s2 vars.
    inst.inst_opcode = DRET /\
    ld_ok vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  ld_derive_agree_tac >>
  `eval_operands inst.inst_operands s1 =
   eval_operands inst.inst_operands s2` by
    (irule eval_operands_agree >> rpt strip_tac >> res_tac) >>
  reverse (Cases_on `inst.inst_outputs`)
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[] >> simp[lift_result_def]) >>
  Cases_on `parse_dret_shape inst`
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[] >> simp[lift_result_def]) >>
  Cases_on `THE (parse_dret_shape inst)` >> gvs[] >>
  Cases_on `eval_operands inst.inst_operands s2`
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[] >> gvs[lift_result_def]) >>
  gvs[] >>
  Cases_on `pair_dret_words
    (TAKE (2 * r) (DROP (1 + q) x))`
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[] >> gvs[lift_result_def]) >>
  irule step_inst_base_ld_ok_dret_success >> gvs[]
QED

Theorem step_inst_base_ld_ok_terminator:
  !inst s1 s2 vars.
    ld_ok vars s1 s2 /\
    is_terminator inst.inst_opcode /\
    ~reads_memory inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (step_inst_base inst s1)
      (step_inst_base inst s2)
Proof
  gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def, reads_memory_def]
  >- ld_terminator_tac
  >- (rpt strip_tac >> drule_all step_inst_base_ld_ok_jnz >> simp[])
  >- ld_terminator_tac
  >- ld_terminator_tac
  >- ld_terminator_tac
  >- ld_terminator_tac
  >- ld_terminator_tac
  >- ld_terminator_tac
  >- (rpt strip_tac >> irule step_inst_base_ld_ok_dret >> simp[])
  >- ld_terminator_tac
  >- ld_terminator_tac
  >- ld_terminator_tac
QED

Theorem ld_terminator_sim[local]:
  !inst fuel ctx s1 s2 vars.
    ld_ok vars s1 s2 /\
    is_terminator inst.inst_opcode /\
    ~reads_memory inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    lift_result (ld_ok vars) (ld_equiv vars) (ld_equiv vars)
      (step_inst fuel ctx inst s1)
      (step_inst fuel ctx inst s2)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  simp[step_inst_non_invoke] >>
  irule step_inst_base_ld_ok_terminator >> metis_tac[]
QED

(* run_insts composes over list append *)
Theorem run_insts_append:
  !xs ys fuel ctx s.
    run_insts fuel ctx (xs ++ ys) s =
      case run_insts fuel ctx xs s of
        OK s' => run_insts fuel ctx ys s'
      | Halt v => Halt v
      | Abort e v => Abort e v
      | IntRet v1 v2 => IntRet v1 v2
      | Error e => Error e
Proof
  Induct >> simp[run_insts_def] >>
  rpt gen_tac >>
  Cases_on `step_inst fuel ctx h s` >> simp[]
QED

(* ===== Per-opcode step helpers for run_insts simulation ===== *)

(* ALLOCA: passes through unchanged. Output is in exempt set (different
   values allowed). vs_allocas differs but is not in ld_ok. *)
Theorem ld_alloca_step:
  !inst fuel ctx s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    inst.inst_opcode = ALLOCA /\
    inst_wf inst /\
    (!out. MEM out inst.inst_outputs ==> out IN vars) /\
    step_inst fuel ctx inst s1 = OK s1' ==>
    ?s2'. step_inst fuel ctx inst s2 = OK s2' /\
          ld_ok vars s1' s2'
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  fs[step_inst_non_invoke] >>
  `?sz. inst.inst_operands = [Lit sz] /\ LENGTH inst.inst_outputs = 1`
    by gvs[inst_wf_def] >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[] >>
     Cases_on `t` >> fs[]) >>
  gvs[step_inst_base_def, LET_THM, exec_alloca_def, eval_operand_def] >>
  Cases_on `FLOOKUP s1.vs_allocas inst.inst_id` >> gvs[] >>
  Cases_on `FLOOKUP s2.vs_allocas inst.inst_id` >> gvs[] >>
  TRY (Cases_on `x` >> gvs[]) >> TRY (Cases_on `x'` >> gvs[]) >>
  irule ld_ok_update_exempt >> simp[] >>
  fs[ld_ok_def, lookup_var_def]
QED

(* Helper: DROP off (TAKE off xs ++ ys) = ys when off <= LENGTH xs *)
Theorem drop_take_append[local]:
  !off xs ys. off <= LENGTH xs ==>
    DROP off (TAKE off xs ++ ys) = ys
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[listTheory.DROP_APPEND] >>
  REWRITE_TAC[rich_listTheory.DROP_TAKE_EQ_NIL] >>
  simp[listTheory.LENGTH_TAKE]
QED

(* Memory write-read roundtrip: writing 32 bytes at any offset,
   then mloading at the same offset gives back the same bytes.
   Works for all offsets — write_memory_with_expansion expands as needed. *)
Theorem write_then_mload[local]:
  !off (bs:word8 list) s. LENGTH bs = 32 ==>
    mload off (write_memory_with_expansion off bs s) = word_of_bytes T 0w bs
Proof
  rpt strip_tac >>
  simp[mload_def, write_memory_with_expansion_def, LET_THM] >>
  qabbrev_tac `mem = s.vs_memory` >>
  (* Both if-branches reduce to DROP off (TAKE off X ++ bs ++ tail) *)
  (* where X has length >= off, so DROP off (TAKE off X ++ ...) = bs ++ tail *)
  (* then TAKE 32 (bs ++ tail ++ REPLICATE 32 0w) = bs *)
  Cases_on `0 < off + 32 - LENGTH mem`
  >- (simp[] >>
      qabbrev_tac `expanded = mem ++ REPLICATE (off + 32 - LENGTH mem) 0w` >>
      `LENGTH expanded = off + 32` by
        (simp[Abbr `expanded`] >> decide_tac) >>
      `off <= LENGTH expanded` by decide_tac >>
      `DROP (off + 32) expanded = []` by
        metis_tac[rich_listTheory.DROP_LENGTH_NIL] >>
      simp[] >>
      `DROP off (TAKE off expanded ++ bs) = bs` by
        (irule drop_take_append >> simp[]) >>
      simp[listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt])
  >- (simp[] >>
      `off + 32 <= LENGTH mem` by decide_tac >>
      `off <= LENGTH mem` by decide_tac >>
      ONCE_REWRITE_TAC[GSYM listTheory.APPEND_ASSOC] >>
      `DROP off (TAKE off mem ++ (bs ++ DROP (off + 32) mem)) =
       bs ++ DROP (off + 32) mem` by
        (irule drop_take_append >> simp[]) >>
      simp[listTheory.TAKE_APPEND1, listTheory.TAKE_LENGTH_ID_rwt])
QED

(* write_memory_with_expansion preserves non-memory fields *)
Theorem wmwe_vars[local,simp]:
  (write_memory_with_expansion off bs s).vs_vars = s.vs_vars
Proof
  simp[write_memory_with_expansion_def, LET_THM]
QED

Theorem wmwe_labels[local,simp]:
  (write_memory_with_expansion off bs s).vs_labels = s.vs_labels
Proof
  simp[write_memory_with_expansion_def, LET_THM]
QED

Theorem wmwe_code[local,simp]:
  (write_memory_with_expansion off bs s).vs_code = s.vs_code
Proof
  simp[write_memory_with_expansion_def, LET_THM]
QED

Theorem wmwe_data_section[local,simp]:
  (write_memory_with_expansion off bs s).vs_data_section = s.vs_data_section
Proof
  simp[write_memory_with_expansion_def, LET_THM]
QED

(* Fresh variable names are distinct *)
Theorem ld_vars_distinct[local,simp]:
  ld_add_var id <> ld_alloca_var id /\
  ld_alloca_var id <> ld_add_var id
Proof
  simp[ld_add_var_def, ld_alloca_var_def]
QED

(* Shared helper: code offset arithmetic for DLOAD/DLOADBYTES lowering.
   Given code_layout_valid and no-overflow, the word addition is correct
   and DROP shifts from absolute code offset to data section offset. *)
Theorem ld_code_offset[local]:
  !s (v:256 word) pad.
    code_layout_valid s /\
    w2n v + (LENGTH s.vs_code - LENGTH s.vs_data_section) < dimword(:256) ==>
    let plen = LENGTH s.vs_code - LENGTH s.vs_data_section in
      w2n (v + n2w plen) = w2n v + plen /\
      DROP (w2n v + plen) (s.vs_code ++ pad) =
        DROP (w2n v) (s.vs_data_section ++ pad)
Proof
  rw[LET_THM] >> rpt strip_tac
  >- (* w2n (v + n2w plen) = w2n v + plen *)
     (simp[word_add_def, w2n_n2w] >>
      fs[code_layout_valid_def]) >>
  (* DROP (w2n v + plen) (code ++ pad) = DROP (w2n v) (data ++ pad) *)
  qabbrev_tac `plen = LENGTH s.vs_code - LENGTH s.vs_data_section` >>
  (Q.SUBGOAL_THEN
    `?prefix. s.vs_code = prefix ++ s.vs_data_section /\
              LENGTH prefix = plen` STRIP_ASSUME_TAC >-
    (fs[code_layout_valid_def, Abbr `plen`] >>
     qexists_tac `TAKE (LENGTH s.vs_code - LENGTH s.vs_data_section) s.vs_code` >>
     simp[TAKE_LENGTH_APPEND, LENGTH_TAKE_EQ] >>
     metis_tac[TAKE_LENGTH_APPEND])) >>
  (* Substitute vs_code, reassociate APPEND, use DROP_APPEND2 *)
  qpat_x_assum `s.vs_code = _` SUBST_ALL_TAC >>
  ONCE_REWRITE_TAC[GSYM APPEND_ASSOC] >>
  qpat_x_assum `LENGTH prefix = _` (SUBST_ALL_TAC o GSYM) >>
  (Q.SUBGOAL_THEN `LENGTH prefix <= w2n v + LENGTH prefix`
    ASSUME_TAC >- decide_tac) >>
  drule DROP_APPEND2 >> disch_then (fn th => REWRITE_TAC[th]) >>
  simp[]
QED

(* DLOAD: expands to [ALLOCA 32; ADD ptr code_end; CODECOPY; MLOAD].
   Under code_layout_valid and no overflow, produces same output value. *)
Theorem ld_dload_step[local]:
  !inst fuel ctx s1 s2 vars s1' v.
    ld_ok vars s1 s2 /\
    code_layout_valid s1 /\ code_layout_valid s2 /\
    inst.inst_opcode = DLOAD /\
    inst_wf inst /\
    inst.inst_operands = [Lit v] /\
    w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) < dimword(:256) /\
    ld_alloca_var inst.inst_id IN vars /\
    ld_add_var inst.inst_id IN vars /\
    step_inst fuel ctx inst s1 = OK s1' ==>
    ?s2'. run_insts fuel ctx (lower_dload_inst inst) s2 = OK s2' /\
          ld_ok vars s1' s2'
Proof
  rpt strip_tac >>
  (* Unfold s1 side: DLOAD via exec_read1 *)
  `inst.inst_opcode <> INVOKE` by simp[] >>
  fs[step_inst_non_invoke] >>
  `LENGTH inst.inst_outputs = 1` by gvs[inst_wf_def] >>
  `?out. inst.inst_outputs = [out]` by
    (Cases_on `inst.inst_outputs` >> fs[] >>
     Cases_on `t` >> fs[]) >>
  gvs[step_inst_base_def, LET_THM, exec_read1_def, eval_operand_def] >>
  (* Unfold s2 side: lower_dload_inst produces 4 instructions *)
  simp[lower_dload_inst_def, LET_THM] >>
  (* eval_operand (Label "code_end") via code_layout_valid *)
  `FLOOKUP s2.vs_labels "code_end" =
     SOME (n2w (LENGTH s2.vs_code - LENGTH s2.vs_data_section))` by
    fs[code_layout_valid_def] >>
  (* Step through all 4 instructions with dimword and var distinctness *)
  ONCE_REWRITE_TAC[run_insts_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[LET_THM, exec_alloca_def, eval_operand_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  ONCE_REWRITE_TAC[run_insts_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[] >>
  simp[LET_THM, exec_pure2_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  ONCE_REWRITE_TAC[run_insts_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[LET_THM, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE] >>
  ONCE_REWRITE_TAC[run_insts_def] >>
  qmatch_goalsub_abbrev_tac `step_inst fuel ctx _ mload_state` >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  simp[] >>
  simp[LET_THM, exec_read1_def, eval_operand_def, run_insts_def] >>
  qunabbrev_tac `mload_state` >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  simp[FLOOKUP_UPDATE] >>
  (* Step 1: Simplify 32 MOD dimword(:256) -> 32 *)
  simp_tac (srw_ss() ++ dimword_256_ss) [] >>
  (* Step 2: Simplify code offset arithmetic *)
  `s2.vs_code = s1.vs_code /\ s2.vs_data_section = s1.vs_data_section /\
   s2.vs_labels = s1.vs_labels` by fs[ld_ok_def] >>
  gvs[] >>  (* propagate s2→s1 rewrites into goal *)
  qabbrev_tac `plen = LENGTH s1.vs_code - LENGTH s1.vs_data_section` >>
  `w2n (v + n2w plen) = w2n v + plen` by
    (simp[word_add_def, w2n_n2w, Abbr `plen`] >>
     fs[code_layout_valid_def]) >>
  `DROP (w2n v + plen) s1.vs_code = DROP (w2n v) s1.vs_data_section` by
    (fs[code_layout_valid_def, Abbr `plen`] >>
     `LENGTH prefix = LENGTH s1.vs_code - LENGTH s1.vs_data_section` by
       simp[] >>
     pop_assum (SUBST1_TAC o GSYM) >>
     simp[rich_listTheory.DROP_APPEND2]) >>
  pop_assum (fn drop_th =>
    pop_assum (fn w2n_th =>
      REWRITE_TAC [w2n_th, drop_th])) >>
  (* Step 3: Apply write_then_mload *)
  qabbrev_tac `dload_bytes =
    TAKE 32 (DROP (w2n v) s1.vs_data_section ++ REPLICATE 32 0w)` >>
  `LENGTH dload_bytes = 32` by
    (simp[Abbr `dload_bytes`] >>
     irule LENGTH_TAKE >> simp[]) >>
  `!off s_inner.
   mload off (write_memory_with_expansion off dload_bytes s_inner) =
   word_of_bytes T 0w dload_bytes` by
    (rpt gen_tac >> irule write_then_mload >> simp[]) >>
  ASM_REWRITE_TAC[] >>
  (* Step 4: Close ld_ok — wmwe only changes vs_memory *)
  simp[ld_ok_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       write_memory_with_expansion_def, LET_THM] >>
  fs[ld_ok_def, lookup_var_def] >>
  rpt strip_tac >>
  Cases_on `out = v'` >- simp[] >>
  simp[] >>
  `ld_add_var inst.inst_id <> v'` by (CCONTR_TAC >> gvs[]) >>
  `ld_alloca_var inst.inst_id <> v'` by (CCONTR_TAC >> gvs[]) >>
  simp[]
QED

(* eval_operand is unaffected by update_var on a different variable *)
Theorem eval_operand_update_var_other:
  !op v w s.
    (!x. op = Var x ==> x <> v) ==>
    eval_operand op (update_var v w s) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

(* DLOADBYTES: expands to [ADD src code_end; CODECOPY dst add_v size].
   Under code_layout_valid and no overflow, writes same bytes. *)
Theorem ld_dloadbytes_step:
  !inst fuel ctx s1 s2 vars s1' dst_op v size_op.
    ld_ok vars s1 s2 /\
    code_layout_valid s1 /\ code_layout_valid s2 /\
    inst.inst_opcode = DLOADBYTES /\
    inst_wf inst /\
    inst.inst_operands = [dst_op; Lit v; size_op] /\
    w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) < dimword(:256) /\
    ld_add_var inst.inst_id IN vars /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    step_inst fuel ctx inst s1 = OK s1' ==>
    ?s2'. run_insts fuel ctx (lower_dload_inst inst) s2 = OK s2' /\
          ld_ok vars s1' s2'
Proof
  rpt strip_tac >>
  (* s1 side: DLOADBYTES via step_inst_base *)
  `inst.inst_opcode <> INVOKE` by simp[] >>
  fs[step_inst_non_invoke] >>
  `inst.inst_outputs = []` by gvs[inst_wf_def] >>
  gvs[step_inst_base_def, LET_THM, eval_operand_def] >>
  (* Extract operand evaluations on s1 *)
  `?dst_val. eval_operand dst_op s1 = SOME dst_val` by
    (Cases_on `eval_operand dst_op s1` >> gvs[AllCaseEqs()]) >>
  `?sz_val. eval_operand size_op s1 = SOME sz_val` by
    (Cases_on `eval_operand size_op s1` >> gvs[AllCaseEqs()]) >>
  gvs[] >>
  (* Derive operand agreement *)
  `eval_operand dst_op s1 = eval_operand dst_op s2` by
    (irule ld_eval_operand_eq >> qexists_tac `vars` >>
     simp[] >> Cases_on `dst_op` >> gvs[]) >>
  `eval_operand size_op s1 = eval_operand size_op s2` by
    (irule ld_eval_operand_eq >> qexists_tac `vars` >>
     simp[] >> Cases_on `size_op` >> gvs[]) >>
  (* s2 side: lower_dload_inst produces [ADD; CODECOPY] *)
  simp[lower_dload_inst_def, LET_THM] >>
  `FLOOKUP s2.vs_labels "code_end" =
     SOME (n2w (LENGTH s2.vs_code - LENGTH s2.vs_data_section))` by
    fs[code_layout_valid_def] >>
  (* Step through ADD *)
  ONCE_REWRITE_TAC[run_insts_def] >>
  simp[step_inst_non_invoke, step_inst_base_def, LET_THM,
       exec_pure2_def, eval_operand_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  (* Derive that dst_op and size_op eval unchanged after update_var add_v *)
  `!w s0. eval_operand dst_op (update_var (ld_add_var inst.inst_id) w s0) =
          eval_operand dst_op s0` by
    (rpt gen_tac >> irule eval_operand_update_var_other >>
     rpt strip_tac >> gvs[]) >>
  `!w s0. eval_operand size_op (update_var (ld_add_var inst.inst_id) w s0) =
          eval_operand size_op s0` by
    (rpt gen_tac >> irule eval_operand_update_var_other >>
     rpt strip_tac >> gvs[]) >>
  (* Normalize s2→s1 and derive code offset before stepping CODECOPY *)
  `s2.vs_code = s1.vs_code /\ s2.vs_data_section = s1.vs_data_section /\
   s2.vs_labels = s1.vs_labels` by fs[ld_ok_def] >>
  qabbrev_tac `plen = LENGTH s1.vs_code - LENGTH s1.vs_data_section` >>
  `w2n (v + n2w plen) = w2n v + plen` by
    (simp[word_add_def, w2n_n2w, Abbr `plen`] >> fs[code_layout_valid_def]) >>
  `!pad. DROP (w2n v + plen) (s1.vs_code ++ pad) =
         DROP (w2n v) (s1.vs_data_section ++ pad)` by
    (drule ld_code_offset >> simp[Abbr `plen`] >>
     strip_tac >> gen_tac >> first_x_assum (qspec_then `pad` mp_tac) >>
     simp[]) >>
  gvs[] >>  (* propagate s2→s1 rewrites *)
  (* Step through CODECOPY — use update_var facts as rewrites *)
  ONCE_REWRITE_TAC[run_insts_def] >>
  simp[step_inst_non_invoke, LET_THM, run_insts_def] >>
  (* Unfold step_inst_base for CODECOPY *)
  simp[step_inst_base_def, LET_THM,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  (* Fold record updates back to update_var, then resolve eval_operand *)
  REWRITE_TAC[GSYM update_var_def] >>
  ASM_REWRITE_TAC[] >> simp[] >>
  (* Close ld_ok: wmwe on both sides, update_var on s2 only *)
  irule ld_ok_write_memory >>
  irule ld_ok_update_var_s2_exempt >> simp[]
QED

(* lower_dload_inst for non-DLOAD/DLOADBYTES is identity *)
Theorem lower_dload_inst_passthrough:
  !inst. inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> DLOADBYTES ==>
         lower_dload_inst inst = [inst]
Proof
  rw[lower_dload_inst_def]
QED

(* run_insts for a singleton list *)
Theorem run_insts_sing:
  run_insts fuel ctx [h] s =
  case step_inst fuel ctx h s of
    OK s' => OK s'
  | Halt v => Halt v
  | Abort e v' => Abort e v'
  | IntRet v1 v2 => IntRet v1 v2
  | Error e' => Error e'
Proof
  simp[run_insts_def] >> Cases_on `step_inst fuel ctx h s` >> simp[run_insts_def]
QED

(* Single instruction step: dispatches to per-opcode lemmas *)
Theorem ld_single_inst_step:
  !h fuel ctx s1 s2 vars s1_mid.
    ld_ok vars s1 s2 /\
    code_layout_valid s1 /\ code_layout_valid s2 /\
    ~is_terminator h.inst_opcode /\
    h.inst_opcode <> INVOKE /\
    ~reads_memory h.inst_opcode /\
    inst_wf h /\
    (!x. MEM (Var x) h.inst_operands ==> x NOTIN vars) /\
    (!out. h.inst_opcode = ALLOCA /\ MEM out h.inst_outputs ==> out IN vars) /\
    (h.inst_opcode = DLOAD ==>
      ?v. h.inst_operands = [Lit v] /\
          w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) < dimword(:256) /\
          ld_alloca_var h.inst_id IN vars /\
          ld_add_var h.inst_id IN vars) /\
    (h.inst_opcode = DLOADBYTES ==>
      ?dst_op v size_op. h.inst_operands = [dst_op; Lit v; size_op] /\
          w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) < dimword(:256) /\
          ld_add_var h.inst_id IN vars) /\
    step_inst fuel ctx h s1 = OK s1_mid ==>
    ?s2_mid. run_insts fuel ctx (lower_dload_inst h) s2 = OK s2_mid /\
             ld_ok vars s1_mid s2_mid
Proof
  rpt strip_tac >>
  Cases_on `h.inst_opcode = DLOAD`
  >- (gvs[] >> res_tac >>
      `?s2'. run_insts fuel ctx (lower_dload_inst h) s2 = OK s2' /\
             ld_ok vars s1_mid s2'` by
        (irule ld_dload_step >> simp[] >> metis_tac[]) >>
      qexists_tac `s2'` >> simp[]) >>
  Cases_on `h.inst_opcode = DLOADBYTES`
  >- (gvs[] >> res_tac >>
      `?s2'. run_insts fuel ctx (lower_dload_inst h) s2 = OK s2' /\
             ld_ok vars s1_mid s2'` by
        (irule ld_dloadbytes_step >> simp[] >> metis_tac[]) >>
      qexists_tac `s2'` >> simp[]) >>
  simp[lower_dload_inst_passthrough, run_insts_sing] >>
  Cases_on `h.inst_opcode = ALLOCA`
  >- (`?s2'. step_inst fuel ctx h s2 = OK s2' /\ ld_ok vars s1_mid s2'` by
        (irule ld_alloca_step >> simp[] >> metis_tac[]) >>
      qexists_tac `s2'` >> simp[]) >>
  (* passthrough: same instruction on both sides *)
  `?s2'. step_inst fuel ctx h s2 = OK s2' /\ ld_ok vars s1_mid s2'` by
    (irule ld_step_passthrough >> simp[] >> metis_tac[]) >>
  qexists_tac `s2'` >> simp[]
QED

(* DLOAD always returns OK when inst_wf holds and operand is Lit v *)
Theorem step_inst_base_dload_ok:
  !inst s v.
    inst.inst_opcode = DLOAD /\ inst_wf inst /\
    inst.inst_operands = [Lit v] ==>
    step_inst_base inst s =
      OK (update_var (HD inst.inst_outputs)
        (word_of_bytes T 0w (TAKE 32 (DROP (w2n v)
          s.vs_data_section ++ REPLICATE 32 0w))) s)
Proof
  rpt strip_tac >>
  simp[step_inst_base_def, exec_read1_def] >>
  `LENGTH inst.inst_outputs = 1` by gvs[inst_wf_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  simp[eval_operand_def]
QED

(* ALLOCA always returns OK under inst_wf *)
Theorem step_inst_base_alloca_ok:
  !inst s.
    inst.inst_opcode = ALLOCA /\ inst_wf inst ==>
    ?s'. step_inst_base inst s = OK s'
Proof
  rpt strip_tac >>
  gvs[inst_wf_def] >>
  simp[step_inst_base_def, eval_operand_def, exec_alloca_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  BasicProvers.EVERY_CASE_TAC
QED

(* DLOADBYTES: only returns OK or Error (never Halt/IntRet/Abort) *)
Theorem step_inst_base_dloadbytes_no_halt:
  !inst s.
    inst.inst_opcode = DLOADBYTES ==>
    (!v. step_inst_base inst s <> Halt v) /\
    (!w v. step_inst_base inst s <> IntRet w v) /\
    (!a v. step_inst_base inst s <> Abort a v)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[])
QED
