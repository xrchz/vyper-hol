(*
 * Pass Shared Properties (API)
 *
 * Re-exports theorems from proof files. Inline proofs only for
 * trivial one-liners or cheated stubs.
 *
 * TOP-LEVEL:
 *   Instruction builders:
 *     mk_nop_inst_correct        — NOP replacement is identity on state
 *     mk_assign_inst_correct     — ASSIGN replacement evaluates and binds output
 *
 *   NOP clearing:
 *     clear_nops_block_correct    — removing NOPs preserves execution (result_equiv)
 *     clear_nops_function_correct — removing NOPs preserves execution (result_equiv)
 *
 *   Operand substitution:
 *     subst_operand_eval           — single substitution preserves eval_operand
 *     subst_op_map_eval            — map substitution preserves eval_operand
 *     subst_operand_eval_operands  — single substitution preserves eval_operands
 *     subst_op_map_eval_operands   — map substitution preserves eval_operands
 *     subst_operands_correct       — single substitution preserves step_inst
 *     subst_operands_map_correct   — map substitution preserves step_inst
 *     step_inst_operands_equiv     — positional operand equivalence preserves step_inst
 *
 *   State preservation:
 *     step_inst_preserves_all              — 18-conjunct field preservation
 *     step_base_preserves_tracked          — step_inst_base field preservation
 *     eligible_no_write_balance_extcode    — eligible ops don't write BALANCE/EXTCODE
 *
 *   Transfer/determinism:
 *     step_inst_base_ok_transfer           — OK transfers across agreeing states
 *     step_inst_base_output_determined_fields — per-field output determinism
 *     step_inst_base_effect_free_output_determined_vars — effect-free: output vars determined by operands + read state
 *
 *   Variable frame:
 *     step_inst_base_var_frame_full        — step_inst_base preserves non-output vars
 *     step_inst_var_frame_full             — step_inst preserves non-output vars
 *
 *   Commutativity:
 *     effects_independent_commute          — independent instructions commute
 *
 *   Copy forwarding equivalence:
 *     copy_fwd_cross_equiv                — mcopy vs nop establishes cross-region equiv
 *     copy_fwd_rel_observable_equiv       — simulation invariant implies observable equiv
 *     copy_fwd_read_equiv                 — rewritten read (dst→src) gives same output
 *     copy_fwd_write_equiv                — rewritten write preserves observable + vars + src equiv
 *     copy_fwd_terminator_equiv           — RETURN/REVERT with rewritten operand
 *     copy_fwd_rel_preserved_identical_inst — identical non-clobbering inst preserves invariant
 *     assign_transparent                  — ASSIGN forwards value unchanged
 *     phi_transparent                     — PHI forwards value unchanged
 *)

Theory passSharedProps
Ancestors
  passSharedDefs venomExecSemantics venomExecProofs venomEffects stateEquiv venomInstProofs
  venomInstProps
  passSharedField passSharedTransfer passSharedVarFrame passSharedFrame
  passSharedSubst instIdxIndep venomState venomInst venomWf
  copyFwdEquiv pred_set list rich_list



(* ===================================================================== *)
(* ===== Well-formedness shape lemmas ================================== *)
(* ===================================================================== *)

(* Read-1 opcodes: 1 operand, 1 output *)
Theorem inst_wf_read1_shape:
  !inst. inst_wf inst /\
    inst.inst_opcode IN {MLOAD; SLOAD; TLOAD; DLOAD; CALLDATALOAD} ==>
    ?addr_op out_var. inst.inst_operands = [addr_op] /\
                      inst.inst_outputs = [out_var]
Proof
  rpt strip_tac >>
  gvs[inst_wf_def, IN_INSERT, NOT_IN_EMPTY] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `inst.inst_outputs` >> fs[] >>
  Cases_on `t` >> fs[]
QED

(* Store opcodes: 2 operands *)
Theorem inst_wf_store_shape:
  !inst. inst_wf inst /\
    inst.inst_opcode IN {MSTORE; MSTORE8; SSTORE; TSTORE} ==>
    ?op1 op2. inst.inst_operands = [op1; op2]
Proof
  rpt strip_tac >>
  gvs[inst_wf_def, IN_INSERT, NOT_IN_EMPTY] >>
  Cases_on `inst.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[] >>
  Cases_on `t'` >> fs[]
QED

(* ===================================================================== *)
(* ===== Instruction builders (trivial) ================================ *)
(* ===================================================================== *)

Theorem mk_nop_inst_correct:
  !fuel ctx inst s.
    step_inst fuel ctx (mk_nop_inst inst) s = OK s
Proof
  rw[mk_nop_inst_def, step_inst_def, step_inst_base_def]
QED

Theorem mk_assign_inst_correct:
  !fuel ctx inst src_op s v out.
    eval_operand src_op s = SOME v /\
    inst.inst_outputs = [out] ==>
    step_inst fuel ctx (mk_assign_inst inst src_op) s =
      OK (update_var out v s)
Proof
  rw[mk_assign_inst_def, step_inst_def, step_inst_base_def] >> rw[]
QED

(* ===================================================================== *)
(* ===== NOP clearing ================================================= *)
(* ===================================================================== *)

(* FILTER/TAKE helpers for index correspondence *)

Triviality filter_take_el:
  !l (P:'a -> bool) i. i < LENGTH l /\ P (EL i l) ==>
    EL (LENGTH (FILTER P (TAKE i l))) (FILTER P l) = EL i l
Proof
  Induct >> simp[] >> rw[] >> Cases_on `i` >> gvs[]
QED

Triviality filter_take_nop:
  !l (P:'a -> bool) i. i < LENGTH l /\ ~P (EL i l) ==>
    LENGTH (FILTER P (TAKE (SUC i) l)) = LENGTH (FILTER P (TAKE i l))
Proof
  Induct >> simp[] >> rw[] >> Cases_on `i` >> gvs[]
QED

Triviality filter_take_keep:
  !l (P:'a -> bool) i. i < LENGTH l /\ P (EL i l) ==>
    LENGTH (FILTER P (TAKE (SUC i) l)) = SUC (LENGTH (FILTER P (TAKE i l)))
Proof
  Induct >> simp[] >> rw[] >> Cases_on `i` >> gvs[]
QED

Triviality filter_take_lt:
  !l (P:'a -> bool) i. i < LENGTH l /\ P (EL i l) ==>
    LENGTH (FILTER P (TAKE i l)) < LENGTH (FILTER P l)
Proof
  Induct >> simp[] >> rw[] >> Cases_on `i` >> gvs[]
QED

Triviality filter_take_all:
  !l (P:'a -> bool) i. LENGTH l <= i ==> FILTER P (TAKE i l) = FILTER P l
Proof
  Induct >> simp[]
QED

(* Combined helpers: NOP-skip and non-NOP index correspondence.
   Pre-specialized to avoid beta-redex issues with irule/metis_tac. *)
Triviality nop_skip_facts:
  !bb s fuel ctx.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = NOP ==>
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) =
     LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE s.vs_inst_idx bb.bb_instructions))) /\
    exec_block fuel ctx bb s =
    exec_block fuel ctx bb (s with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac
  >- (irule filter_take_nop >> simp[])
  >- (CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      simp[get_instruction_def, step_nop_identity] >> EVAL_TAC)
QED

Triviality non_nop_idx_facts:
  !bb s.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode <> NOP ==>
    (EL (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                        (TAKE s.vs_inst_idx bb.bb_instructions)))
        (FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions) =
     EL s.vs_inst_idx bb.bb_instructions) /\
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE s.vs_inst_idx bb.bb_instructions)) <
     LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions)) /\
    (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) =
     SUC (LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                         (TAKE s.vs_inst_idx bb.bb_instructions))))
Proof
  rpt strip_tac
  >- (irule filter_take_el >> simp[])
  >- (irule filter_take_lt >> simp[])
  >- (irule filter_take_keep >> simp[])
QED

Triviality filter_take_all_nop:
  !bb i. LENGTH bb.bb_instructions <= i ==>
    LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                   (TAKE i bb.bb_instructions)) =
    LENGTH (FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions)
Proof
  rw[] >> AP_TERM_TAC >> irule filter_take_all >> simp[]
QED

(* Past-end case: both sides get NONE from get_instruction *)
Triviality clear_nops_past_end:
  !fuel ctx bb s.
    ~(s.vs_inst_idx < LENGTH bb.bb_instructions) ==>
    exec_block fuel ctx (clear_nops_block bb)
      (s with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                       (TAKE s.vs_inst_idx bb.bb_instructions))) =
    exec_block fuel ctx bb s
Proof
  rpt strip_tac >>
  `LENGTH bb.bb_instructions <= s.vs_inst_idx` by DECIDE_TAC >>
  imp_res_tac filter_take_all_nop >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  gvs[get_instruction_def, clear_nops_block_def]
QED

(* NOP case: skip in original, filtered index unchanged, apply IH *)
Triviality clear_nops_nop_step:
  !fuel ctx bb s.
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = NOP /\
    exec_block fuel ctx (clear_nops_block bb)
      ((s with vs_inst_idx := SUC s.vs_inst_idx) with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                       (TAKE (SUC s.vs_inst_idx) bb.bb_instructions))) =
    exec_block fuel ctx bb (s with vs_inst_idx := SUC s.vs_inst_idx) ==>
    exec_block fuel ctx (clear_nops_block bb)
      (s with vs_inst_idx :=
        LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                       (TAKE s.vs_inst_idx bb.bb_instructions))) =
    exec_block fuel ctx bb s
Proof
  rpt strip_tac >>
  imp_res_tac nop_skip_facts >> gvs[]
QED

(* NOP removal preserves execution up to vs_inst_idx.
   Why true: step_inst on NOP returns OK s (identity). exec_block increments
   vs_inst_idx after each non-terminator, so skipping a NOP just skips an
   idx increment. For OK results (JMP/JNZ terminators), jump_to resets
   vs_inst_idx := 0 so state_equiv {} holds. For Halt/Revert, vs_inst_idx
   differs but execution_equiv {} ignores it.

   Proof approach: induction on exec_block (or on instruction list length).
   Key facts: step_inst NOP = OK s (from step_inst_base_def),
   FILTER removes NOPs, result_equiv = lift_result state_equiv execution_equiv.

   The block-level result propagates to function-level by fuel induction:
   run_blocks calls exec_block then recurses. The OK case has vs_inst_idx=0
   (from jump_to), so the inductive hypothesis applies. Terminal cases use
   execution_equiv which ignores vs_inst_idx. *)
(* Non-terminator step_inst at different idx: OK results agree modulo idx.
   Covers both INVOKE and non-INVOKE non-terminator instructions.
   Why: step_inst never reads vs_inst_idx; it only reads/writes other fields. *)
Triviality foldl_update_var_idx:
  !ps st j.
    FOLDL (\s' (out,val). update_var out val s') (st with vs_inst_idx := j) ps =
    FOLDL (\s' (out,val). update_var out val s') st ps with vs_inst_idx := j
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >> rpt gen_tac >>
  `update_var p_1 p_2 (st with vs_inst_idx := j) =
   update_var p_1 p_2 st with vs_inst_idx := j` by
    simp[update_var_def] >>
  simp[]
QED

Triviality bind_outputs_idx:
  !outs vals st j.
    bind_outputs outs vals (st with vs_inst_idx := j) =
    OPTION_MAP (\s'. s' with vs_inst_idx := j) (bind_outputs outs vals st)
Proof
  rw[bind_outputs_def, foldl_update_var_idx]
QED


Triviality adopt_return_fmp_idx:
  !ir st j.
    adopt_return_fmp ir (st with vs_inst_idx := j) =
    adopt_return_fmp ir st with vs_inst_idx := j
Proof
  rpt gen_tac >>
  Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def]
QED
(* Non-terminator step_inst at different idx:
   - OK results: state shifted by idx
   - Non-OK results: execution_equiv {} (ignores idx)
   This is what clear_nops_block_gen needs. *)
Triviality step_inst_non_term_idx:
  !fuel ctx inst s j.
    ~is_terminator inst.inst_opcode ==>
    (case step_inst fuel ctx inst s of
       OK v =>
         step_inst fuel ctx inst (s with vs_inst_idx := j) =
         OK (v with vs_inst_idx := j)
     | _ =>
         result_equiv {}
           (step_inst fuel ctx inst (s with vs_inst_idx := j))
           (step_inst fuel ctx inst s))
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    simp[step_inst_def, eval_ops_inst_idx] >>
    Cases_on `decode_invoke inst` >> simp[result_equiv_def, revert_equiv_def] >>
    Cases_on `x` >> simp[] >>
    Cases_on `lookup_function q ctx.ctx_functions` >>
    simp[result_equiv_def, revert_equiv_def] >>
    Cases_on `eval_operands r s` >> simp[result_equiv_def, revert_equiv_def] >>
    rename1 `eval_operands _ s = SOME args` >>
    rename1 `lookup_function _ _ = SOME callee_fn` >>
    `setup_callee callee_fn args (s with vs_inst_idx := j) =
     setup_callee callee_fn args s` by simp[setup_callee_def] >>
    simp[] >>
    Cases_on `setup_callee callee_fn args s` >>
    simp[result_equiv_def, revert_equiv_def] >>
    rename1 `setup_callee _ _ s = SOME callee_s` >>
    Cases_on `run_blocks fuel ctx callee_fn callee_s` >>
    simp[result_equiv_def, execution_equiv_def, lookup_var_def,
         venom_state_component_equality] >>
    (* IntRet case *)
    rename1 `run_blocks _ _ _ _ = IntRet ret_vals callee_s'` >>
    `merge_callee_state (s with vs_inst_idx := j) callee_s' =
     merge_callee_state s callee_s' with vs_inst_idx := j` by
      simp[merge_callee_state_def, venom_state_component_equality] >>
    simp[adopt_return_fmp_idx, bind_outputs_idx] >>
    Cases_on `bind_outputs inst.inst_outputs ret_vals.iret_values
                (adopt_return_fmp ret_vals
                  (merge_callee_state s callee_s'))` >>
    simp[result_equiv_def, execution_equiv_def, revert_equiv_def, lookup_var_def,
         venom_state_component_equality]
  ) >>
  (* Non-INVOKE: step_inst = step_inst_base, use idx_indep *)
  simp[step_inst_non_invoke, step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base inst s` >>
  simp[exec_result_map_def, result_equiv_def, execution_equiv_def, revert_equiv_def,
       lookup_var_def, venom_state_component_equality]
QED

(* Terminator step_inst_base at different idx gives result_equiv {}.
   Key insight: normalization (rw) MUST come before Cases_on. *)
Triviality step_inst_base_term_result_equiv:
  !inst s j.
    is_terminator inst.inst_opcode ==>
    result_equiv {}
      (case step_inst_base inst s of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s'
       | Error e => Error e)
      (case step_inst_base inst (s with vs_inst_idx := j) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet v s' => IntRet v s'
       | Error e => Error e)
Proof
  rpt strip_tac >>
  qabbrev_tac `r1 = step_inst_base inst s` >>
  qabbrev_tac `r2 = step_inst_base inst (s with vs_inst_idx := j)` >>
  `exec_result_map (\s'. s' with vs_inst_idx := 0) r2 =
   exec_result_map (\s'. s' with vs_inst_idx := 0) r1` by
    simp[Abbr `r1`, Abbr `r2`, terminator_step_inst_base_idx_norm0] >>
  Cases_on `r1` >> Cases_on `r2` >>
  gvs[exec_result_map_def] >>
  (* All cross-constructor cases eliminated by gvs. Remaining: same constructor. *)
  (* From v' with idx:=0 = v with idx:=0, extract all non-idx fields equal *)
  gvs[venom_state_component_equality] >>
  simp[result_equiv_def, execution_equiv_def, revert_equiv_def, lookup_var_def] >>
  (* OK-OK case: use terminator_OK_inst_idx_0 to get idx=0 *)
  imp_res_tac terminator_OK_inst_idx_0 >> gvs[] >>
  Cases_on `v.vs_halted` >>
  simp[result_equiv_def, state_equiv_def, execution_equiv_def,
       lookup_var_def, venom_state_component_equality]
QED

(* Generalized: relates exec_block at any idx to exec_block on filtered block
   at the corresponding filtered index. *)
Theorem clear_nops_block_gen:
  !fuel ctx bb s.
    result_equiv {}
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (clear_nops_block bb)
        (s with vs_inst_idx :=
          LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                         (TAKE s.vs_inst_idx bb.bb_instructions))))
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  (* Unroll one step of exec_block on the original side *)
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (
    (* Past end: both sides get NONE *)
    `~(s.vs_inst_idx < LENGTH bb.bb_instructions)` by
      fs[get_instruction_def] >>
    `LENGTH bb.bb_instructions <= s.vs_inst_idx` by DECIDE_TAC >>
    imp_res_tac filter_take_all_nop >>
    simp[Once exec_block_def, get_instruction_def, clear_nops_block_def,
         result_equiv_def]
  ) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    fs[get_instruction_def] >>
  `EL s.vs_inst_idx bb.bb_instructions = inst` by
    fs[get_instruction_def] >>
  Cases_on `inst.inst_opcode = NOP`
  >- (
    (* NOP case: original steps identity, filtered index unchanged *)
    `step_inst fuel ctx inst s = OK s` by
      simp[step_nop_identity] >>
    `~is_terminator NOP` by EVAL_TAC >>
    simp[] >>
    `LENGTH (FILTER (\i. i.inst_opcode <> NOP)
                    (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)) =
     LENGTH (FILTER (\i. i.inst_opcode <> NOP)
                    (TAKE s.vs_inst_idx bb.bb_instructions))` by
      (irule filter_take_nop >> gvs[]) >>
    first_x_assum (qspecl_then [`inst`, `s`] mp_tac) >>
    gvs[]
  ) >>
  (* Non-NOP case: both sides execute the same instruction *)
  imp_res_tac non_nop_idx_facts >> rfs[] >>
  qabbrev_tac `j = LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
                    (TAKE s.vs_inst_idx bb.bb_instructions))` >>
  `get_instruction (clear_nops_block bb) j = SOME inst` by
    simp[get_instruction_def, clear_nops_block_def] >>
  Cases_on `is_terminator inst.inst_opcode` >- (
    (* Terminator case *)
    `inst.inst_opcode <> INVOKE` by
      (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
    simp[step_inst_non_invoke] >>
    simp[Once exec_block_def, step_inst_non_invoke] >>
    irule step_inst_base_term_result_equiv >> simp[]
  ) >>
  (* Non-terminator case *)
  mp_tac (Q.SPECL [`fuel`, `ctx`, `inst`, `s`, `j`] step_inst_non_term_idx) >>
  simp[] >> Cases_on `step_inst fuel ctx inst s` >> simp[]
  (* OK case: have step_inst ... (s with idx:=j) = OK (v with idx:=j) *)
  >- (
    strip_tac >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[] >> fs[] >>
    first_x_assum match_mp_tac >> simp[]
  ) >>
  (* Non-OK cases: have result_equiv {} (step_inst ... shifted) (original) *)
  disch_then assume_tac >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[] >>
  Cases_on `step_inst fuel ctx inst (s with vs_inst_idx := j)` >>
  fs[result_equiv_def, execution_equiv_def, revert_equiv_def, lookup_var_def,
     venom_state_component_equality]
QED

Theorem clear_nops_block_correct:
  !fuel ctx bb s.
    s.vs_inst_idx = 0 ==>
    result_equiv {}
      (exec_block fuel ctx bb s)
      (exec_block fuel ctx (clear_nops_block bb) s)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`, `s`] clear_nops_block_gen) >>
  `s with vs_inst_idx := 0 = s` by gvs[venom_state_component_equality] >>
  simp[]
QED

Triviality lookup_block_clear_nops:
  !lbl bbs. lookup_block lbl (MAP clear_nops_block bbs) =
            OPTION_MAP clear_nops_block (lookup_block lbl bbs)
Proof
  gen_tac >> Induct >>
  simp[lookup_block_def, listTheory.FIND_thm, clear_nops_block_def] >>
  rw[] >> fs[lookup_block_def, clear_nops_block_def]
QED

Triviality exec_block_ok_inst_idx_0:
  !fuel ctx bb s v.
    exec_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  pop_assum mp_tac >> simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  rw[] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  fs[step_inst_non_invoke] >>
  imp_res_tac terminator_OK_inst_idx_0
QED

Triviality state_equiv_empty_eq:
  !s1 s2. state_equiv {} s1 s2 ==> s1 = s2
Proof
  rw[state_equiv_def, execution_equiv_def, venom_state_component_equality,
     lookup_var_def] >>
  `!v. FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v` by metis_tac[] >>
  metis_tac[finite_mapTheory.FLOOKUP_EXT, EQ_EXT]
QED

Triviality result_equiv_empty_ok:
  !s1 s2.
    result_equiv {} (OK s1) (OK s2) ==> s1 = s2
Proof
  rw[result_equiv_def, state_equiv_def, execution_equiv_def,
     venom_state_component_equality, lookup_var_def] >>
  `!v. FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v` by metis_tac[] >>
  metis_tac[finite_mapTheory.FLOOKUP_EXT, EQ_EXT]
QED

(* If no element in the list is PHI, phi_prefix_length = 0 *)
Triviality no_phi_prefix_length_0:
  !l. EVERY (\inst. inst.inst_opcode <> PHI) l ==> phi_prefix_length l = 0
Proof
  Induct_on `l` >> simp[phi_prefix_length_def] >> Cases >> simp[phi_prefix_length_def]
QED

(* NOP is not PHI, so FILTER removing NOPs preserves phi_prefix_length
   when PHIs form a prefix (which bb_well_formed guarantees). *)
Triviality phi_prefix_length_filter_nop:
  !l. (!i j. i < j /\ j < LENGTH l /\
        (EL j l).inst_opcode = PHI ==>
        (EL i l).inst_opcode = PHI) ==>
    phi_prefix_length (FILTER (\inst. inst.inst_opcode <> NOP) l) = phi_prefix_length l
Proof
  Induct >- simp[phi_prefix_length_def]
  >> rpt gen_tac >> rpt disch_tac >>
  Cases_on `h.inst_opcode = NOP`
  >- (
    (* h is NOP: FILTER removes it, phi_prefix_length (h::l) = 0 *)
    simp[phi_prefix_length_def] >>
    irule no_phi_prefix_length_0 >>
    simp[EVERY_FILTER, EVERY_MEM] >>
    gen_tac >> strip_tac >>
    CCONTR_TAC >> fs[] >>
    `?n. n < LENGTH l /\ EL n l = inst` by (
      qspecl_then [`l`,`inst`] mp_tac MEM_EL >> simp[] >> strip_tac >>
      qexists_tac `n` >> simp[]) >>
    first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >>
    simp[EL_CONS] >> fs[])
  >- (
    (* h is not NOP: FILTER keeps it *)
    Cases_on `h.inst_opcode = PHI`
    >- (
      (* h is PHI (and not NOP): both sides get SUC, use IH *)
      simp[phi_prefix_length_def] >>
      first_x_assum irule >> rpt strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
      simp[EL_CONS] >> decide_tac)
    >- (
      (* h is neither PHI nor NOP: both sides are 0 *)
      simp[phi_prefix_length_def]))
QED

Triviality phi_prefix_length_el_phi:
  !l i. i < phi_prefix_length l ==> (EL i l).inst_opcode = PHI
Proof
  Induct_on `l` >> simp[phi_prefix_length_def] >> rw[] >>
  Cases_on `i` >> simp[phi_prefix_length_def]
QED

(* In the PHI prefix, all instructions are PHI, hence not NOP *)
Triviality phi_prefix_no_nop:
  !l i. i < phi_prefix_length l ==> (EL i l).inst_opcode <> NOP
Proof
  rpt strip_tac >> drule phi_prefix_length_el_phi >> simp[]
QED

(* If no element of l is PHI, then eval_phis on FILTER of l returns OK s *)
Triviality eval_phis_filter_no_phi:
  !s P l.
    (!i. i < LENGTH l ==> (EL i l).inst_opcode <> PHI) ==>
    eval_phis s (FILTER P l) = OK s
Proof
  Induct_on `l` >- simp[eval_phis_def] >>
  rpt strip_tac >>
  Cases_on `P h` >> gvs[] >>
  `h.inst_opcode <> PHI` by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[eval_phis_def] >>
  first_x_assum irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

(* With PHI-prefix well-formedness, FILTER out NOPs preserves eval_phis *)
Triviality eval_phis_filter_nop_wf:
  !s l.
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
           (EL i l).inst_opcode = PHI) ==>
    eval_phis s (FILTER (\inst. inst.inst_opcode <> NOP) l) = eval_phis s l
Proof
  gen_tac >> Induct
  >- simp[eval_phis_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    simp[eval_phis_def] >>
    `eval_phis s (FILTER (\inst. inst.inst_opcode <> NOP) l) = eval_phis s l` by (
      first_x_assum irule >> rpt strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
      simp[rich_listTheory.EL_CONS]) >>
    simp[]) >>
  Cases_on `h.inst_opcode = NOP`
  >- (
    simp[eval_phis_def] >>
    irule eval_phis_filter_no_phi >> rpt strip_tac >>
    CCONTR_TAC >>
    first_x_assum (qspecl_then [`0`, `SUC i`] mp_tac) >>
    simp[rich_listTheory.EL_CONS]) >>
  simp[eval_phis_def]
QED

Triviality filter_take_phi_prefix_length:
  !l.
    LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
              (TAKE (phi_prefix_length l) l)) = phi_prefix_length l
Proof
  rpt strip_tac >>
  `EVERY (\inst. inst.inst_opcode <> NOP) (TAKE (phi_prefix_length l) l)` by (
    simp[listTheory.EVERY_EL] >> rpt strip_tac >>
    `n < phi_prefix_length l` by
      gvs[LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le] >>
    `EL n (TAKE (phi_prefix_length l) l) = EL n l` by
      simp[EL_TAKE] >>
    metis_tac[phi_prefix_no_nop]) >>
  `FILTER (\inst. inst.inst_opcode <> NOP) (TAKE (phi_prefix_length l) l) =
   TAKE (phi_prefix_length l) l` by simp[FILTER_EQ_ID] >>
  simp[LENGTH_TAKE_EQ, venomExecProofsTheory.phi_prefix_length_le]
QED

Theorem clear_nops_run_block_equiv:
  !fuel ctx bb s.
    bb_well_formed bb ==> result_equiv {}
      (run_block fuel ctx bb s) (run_block fuel ctx (clear_nops_block bb) s)
Proof
  rpt strip_tac >>
  `phi_prefix_length (clear_nops_block bb).bb_instructions = phi_prefix_length bb.bb_instructions` by (
    simp[clear_nops_block_def] >> irule phi_prefix_length_filter_nop >>
    fs[bb_well_formed_def]) >>
  `eval_phis s (clear_nops_block bb).bb_instructions = eval_phis s bb.bb_instructions` by (
    simp[clear_nops_block_def] >> irule eval_phis_filter_nop_wf >>
    fs[bb_well_formed_def]) >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (
    qpat_x_assum `?s_phi. eval_phis s bb.bb_instructions = OK s_phi`
      (qx_choose_then `s_phi` assume_tac) >>
    ASM_REWRITE_TAC[] >> simp[] >>
    mp_tac (Q.SPECL [`fuel`, `ctx`, `bb`,
      `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`]
      clear_nops_block_gen) >>
    simp[filter_take_phi_prefix_length]) >>
  qpat_x_assum `?e. eval_phis s bb.bb_instructions = Error e`
    strip_assume_tac >>
  ASM_REWRITE_TAC[] >> simp[result_equiv_def]
QED

(* ===================================================================== *)
(* ===================================================================== *)
(* ===== clear_nops structural preservation ============================ *)
(* ===================================================================== *)

(* LAST of FILTER P l = LAST l when l non-empty and P holds on LAST *)
Triviality last_filter_last:
  !P l. l <> [] /\ P (LAST l) ==> LAST (FILTER P l) = LAST l
Proof
  rpt strip_tac >>
  `l = FRONT l ++ [LAST l]` by metis_tac[APPEND_FRONT_LAST] >>
  `FILTER P l = FILTER P (FRONT l) ++ FILTER P [LAST l]` by
    metis_tac[FILTER_APPEND_DISTRIB] >>
  `FILTER P [LAST l] = [LAST l]` by simp[] >>
  simp[LAST_APPEND_NOT_NIL]
QED

(* Terminators are not NOP *)
Triviality terminator_not_nop:
  !op. is_terminator op ==> op <> NOP
Proof
  Cases >> simp[is_terminator_def]
QED

(* ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l)) *)
Triviality all_distinct_map_filter:
  !f P l. ALL_DISTINCT (MAP f l) ==> ALL_DISTINCT (MAP f (FILTER P l))
Proof
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  IF_CASES_TAC >> fs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED

(* FILTER prefix property: if Q forms a prefix (downward-closed by index) in l
   and all Q-elements pass P, then Q forms a prefix in FILTER P l. *)
Triviality filter_preserves_prefix:
  !P Q l.
    (!x. Q x ==> P x) /\
    (!i j. i < j /\ j < LENGTH l /\ Q (EL j l) ==> Q (EL i l))
    ==>
    !i j. i < j /\ j < LENGTH (FILTER P l) /\
          Q (EL j (FILTER P l)) ==> Q (EL i (FILTER P l))
Proof
  ntac 2 gen_tac >> Induct >> simp[] >>
  rpt strip_tac >>
  (* Derive prefix property for l from h::l *)
  `!i' j'. i' < j' /\ j' < LENGTH l /\ Q (EL j' l) ==> Q (EL i' l)` by
    (rpt strip_tac >>
     qpat_x_assum `!i j. i < j /\ _ ==> _`
       (qspecl_then [`SUC i'`, `SUC j'`] mp_tac) >> simp[]) >>
  (* Apply IH to get prefix property for FILTER P l *)
  `!i' j'. i' < j' /\ j' < LENGTH (FILTER P l) /\ Q (EL j' (FILTER P l))
           ==> Q (EL i' (FILTER P l))` by metis_tac[] >>
  IF_CASES_TAC >> gvs[]
  (* P h: h :: FILTER P l *)
  >- (Cases_on `i` >> gvs[]
      >- (Cases_on `j` >> gvs[] >>
          `MEM (EL n (FILTER P l)) (FILTER P l)` by metis_tac[MEM_EL] >>
          fs[MEM_FILTER] >>
          `?k. k < LENGTH l /\ EL k l = EL n (FILTER P l)` by metis_tac[MEM_EL] >>
          qpat_x_assum `!i j. i < j /\ j < SUC _ /\ Q (h::l)❲j❳ ==> _`
            (qspecl_then [`0`, `SUC k`] mp_tac) >> simp[])
      >- (Cases_on `j` >> gvs[] >> metis_tac[]))
  (* ~P h: FILTER P l directly *)
  >- metis_tac[]
QED

(* clear_nops_block preserves bb_well_formed.
   Strategy: decompose insts = FRONT insts ++ [LAST insts],
   then FILTER = FILTER(FRONT) ++ [LAST] since LAST is terminator (not NOP). *)
(* filter_preserves_prefix fully specialized for clear_nops PHI prefix.
   P = not-NOP, Q = is-PHI. Built at ML level to avoid parser issues. *)
local
  val x = mk_var("x", ``:instruction``)
  val opcode = #1 (dest_comb ``(z:instruction).inst_opcode``)
  val phi_check = mk_abs(x, mk_eq(mk_comb(opcode, x), ``PHI``))
  val nop_check = mk_abs(x, mk_neg(mk_eq(mk_comb(opcode, x), ``NOP``)))
in
  val filter_preserves_phi_prefix = filter_preserves_prefix
    |> INST_TYPE [alpha |-> ``:instruction``]
    |> ISPECL [nop_check, phi_check]
    |> SIMP_RULE (srw_ss()) []
end;

(* General: bb_well_formed preserved by length-preserving transforms
   that preserve terminator and PHI status at each position *)
Theorem bb_well_formed_transfer:
  !insts insts'.
    LENGTH insts' = LENGTH insts /\
    (!i. i < LENGTH insts ==>
       (is_terminator (EL i insts').inst_opcode <=>
        is_terminator (EL i insts).inst_opcode)) /\
    (!i. i < LENGTH insts ==>
       ((EL i insts').inst_opcode = PHI <=>
        (EL i insts).inst_opcode = PHI))
    ==>
    bb_well_formed (bb with bb_instructions := insts) ==>
    bb_well_formed (bb with bb_instructions := insts')
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def] >>
  sg `insts' <> []` >- (Cases_on `insts'` >> fs[]) >>
  sg `PRE (LENGTH insts) < LENGTH insts`
  >- (Cases_on `insts` >> fs[]) >>
  sg `LAST insts = EL (PRE (LENGTH insts)) insts` >- fs[LAST_EL] >>
  sg `LAST insts' = EL (PRE (LENGTH insts)) insts'` >- fs[LAST_EL] >>
  rpt conj_tac >> rpt strip_tac >> res_tac >> fs[]
QED

Theorem clear_nops_block_preserves_wf:
  !bb. bb_well_formed bb ==> bb_well_formed (clear_nops_block bb)
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def, clear_nops_block_def] >>
  qmatch_goalsub_abbrev_tac `FILTER P _` >>
  qabbrev_tac `insts = bb.bb_instructions` >>
  qabbrev_tac `filt = FILTER P insts` >>
  (* LAST is terminator hence not NOP, so it passes filter *)
  `P (LAST insts)` by
    (simp[Abbr `P`] >> metis_tac[terminator_not_nop]) >>
  (* Decompose: insts = FRONT ++ [LAST], filt = FILTER(FRONT) ++ [LAST] *)
  `insts = FRONT insts ++ [LAST insts]` by metis_tac[APPEND_FRONT_LAST] >>
  `filt = FILTER P (FRONT insts) ++ [LAST insts]` by
    (simp[Abbr `filt`] >>
     `FILTER P insts = FILTER P (FRONT insts) ++ FILTER P [LAST insts]` by
       metis_tac[FILTER_APPEND_DISTRIB] >>
     simp[]) >>
  qabbrev_tac `fpre = FILTER P (FRONT insts)` >>
  rpt conj_tac
  (* 1. non-empty *)
  >- simp[]
  (* 2. LAST is terminator *)
  >- simp[LAST_APPEND_NOT_NIL]
  (* 3. terminator only at end *)
  >- (rpt strip_tac >>
      `LENGTH filt = SUC (LENGTH fpre)` by simp[] >>
      Cases_on `i = LENGTH fpre` >- simp[] >>
      `i < LENGTH fpre` by decide_tac >>
      `EL i filt = EL i fpre` by simp[EL_APPEND1] >>
      `MEM (EL i fpre) fpre` by metis_tac[MEM_EL] >>
      `MEM (EL i fpre) (FRONT insts)` by fs[MEM_FILTER, Abbr `fpre`] >>
      `?k. k < LENGTH (FRONT insts) /\ EL k (FRONT insts) = EL i fpre`
        by metis_tac[MEM_EL] >>
      `LENGTH (FRONT insts) = PRE (LENGTH insts)` by simp[FRONT_LENGTH] >>
      `k < LENGTH insts` by decide_tac >>
      `EL k (FRONT insts) = EL k insts`
        by (irule EL_FRONT >> simp[NULL_EQ]) >>
      `k = PRE (LENGTH insts)` by metis_tac[] >>
      decide_tac)
  (* 4. PHI prefix *)
  >- (simp_tac std_ss [Abbr `filt`, Abbr `P`, Abbr `insts`] >>
      match_mp_tac filter_preserves_phi_prefix >> fs[])
QED

(* clear_nops_block preserves bb_succs *)
Triviality clear_nops_succs:
  !bb. bb_well_formed bb ==> bb_succs (clear_nops_block bb) = bb_succs bb
Proof
  rpt strip_tac >>
  fs[bb_well_formed_def, clear_nops_block_def, bb_succs_def] >>
  `(LAST bb.bb_instructions).inst_opcode <> NOP` by
    metis_tac[terminator_not_nop] >>
  `FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions <> []` by
    (CCONTR_TAC >> fs[FILTER_EQ_NIL, EVERY_MEM] >>
     `MEM (LAST bb.bb_instructions) bb.bb_instructions` by
       metis_tac[MEM_LAST_NOT_NIL] >>
     metis_tac[]) >>
  `LAST (FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions) =
   LAST bb.bb_instructions` by
    (irule last_filter_last >> simp[]) >>
  Cases_on `FILTER (\inst. inst.inst_opcode <> NOP) bb.bb_instructions` >> fs[] >>
  Cases_on `bb.bb_instructions` >> fs[]
QED

(* clear_nops_function preserves fn_labels *)
Triviality clear_nops_fn_labels:
  !fn. fn_labels (clear_nops_function fn) = fn_labels fn
Proof
  simp[fn_labels_def, clear_nops_function_def, MAP_MAP_o, combinTheory.o_DEF,
       clear_nops_block_def]
QED

(* clear_nops_function preserves fn_has_entry *)
Triviality clear_nops_fn_has_entry:
  !fn. fn_has_entry (clear_nops_function fn) = fn_has_entry fn
Proof
  simp[fn_has_entry_def, clear_nops_function_def]
QED

(* clear_nops_function preserves fn_inst_ids_distinct.
   Key: ALL_DISTINCT (MAP f l) preserved by FILTER via all_distinct_map_filter,
   extended to FLAT structure by induction on blocks. *)
Triviality flat_map_filter_all_distinct:
  !f P g (ls:'a list).
    ALL_DISTINCT (FLAT (MAP (\x. MAP f (g x)) ls)) ==>
    ALL_DISTINCT (FLAT (MAP (\x. MAP f (FILTER P (g x))) ls))
Proof
  ntac 3 gen_tac >> Induct >> simp[] >> rpt strip_tac >>
  fs[ALL_DISTINCT_APPEND] >> rpt conj_tac
  >- (irule all_distinct_map_filter >> simp[])
  >- (rpt strip_tac >>
      fs[MEM_FLAT, MEM_MAP, PULL_EXISTS, MEM_FILTER] >>
      CCONTR_TAC >> fs[] >> res_tac >> fs[MEM_MAP] >> metis_tac[])
QED

Triviality clear_nops_fn_inst_ids_distinct:
  !fn. fn_inst_ids_distinct fn ==>
       fn_inst_ids_distinct (clear_nops_function fn)
Proof
  simp[fn_inst_ids_distinct_def, clear_nops_function_def, clear_nops_block_def,
       MAP_MAP_o, combinTheory.o_DEF] >>
  metis_tac[flat_map_filter_all_distinct]
QED

(* Main result *)
Theorem clear_nops_function_preserves_wf:
  !fn. wf_function fn ==> wf_function (clear_nops_function fn)
Proof
  rpt strip_tac >> fs[wf_function_def] >> rpt conj_tac
  >- simp[clear_nops_fn_labels]
  >- simp[clear_nops_fn_has_entry, clear_nops_function_def]
  >- (rpt strip_tac >>
      fs[clear_nops_function_def, MEM_MAP] >>
      rename1 `clear_nops_block bb0` >>
      irule clear_nops_block_preserves_wf >> metis_tac[])
  >- (fs[fn_succs_closed_def, clear_nops_fn_labels] >>
      rpt strip_tac >>
      fs[clear_nops_function_def, MEM_MAP] >>
      rename1 `clear_nops_block bb0` >>
      `bb_succs (clear_nops_block bb0) = bb_succs bb0` by
        (irule clear_nops_succs >> metis_tac[]) >>
      metis_tac[])
  >- (irule clear_nops_fn_inst_ids_distinct >> simp[])
QED

Triviality find_some_mem[local]:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >>
  rpt strip_tac >> Cases_on `P h` >> fs[] >> metis_tac[]
QED

Theorem clear_nops_function_correct:
  !fuel ctx fn s.
    wf_function fn /\ s.vs_inst_idx = 0 ==>
    result_equiv {}
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (clear_nops_function fn) s)
Proof
  Induct_on `fuel` >- (
    rpt strip_tac >> simp[run_blocks_def, result_equiv_def]) >>
  rpt strip_tac >>
  once_rewrite_tac[run_blocks_unfold] >>
  simp[clear_nops_function_def, lookup_block_clear_nops] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >-
    simp[result_equiv_def] >>
  rename1 `SOME bb` >>
  `bb_well_formed bb` by (
    fs[wf_function_def, lookup_block_def] >>
    drule find_some_mem >> metis_tac[]) >>
  `result_equiv {} (run_block fuel ctx bb s)
     (run_block fuel ctx (clear_nops_block bb) s)` by
    simp[clear_nops_run_block_equiv] >>
  (* Now we need: result_equiv on both sides of the case-match on run_block *)
  Cases_on `run_block fuel ctx bb s`
  >- (
    (* OK case *)
    Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
    gvs[result_equiv_def] >>
    TRY (imp_res_tac state_equiv_empty_eq >> gvs[result_equiv_def]) >>
    (* Only OK-OK survives *)
    imp_res_tac state_equiv_empty_eq >> gvs[] >>
    imp_res_tac run_block_OK_inst_idx_0 >>
    Cases_on `v.vs_halted` >> gvs[result_equiv_def]
    >- simp[result_equiv_def, execution_equiv_def] >>
    once_rewrite_tac[GSYM clear_nops_function_def] >>
    first_x_assum irule >> simp[] >>
    irule clear_nops_function_preserves_wf >> simp[])
  >- (
    (* Halt case *)
    Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
    gvs[result_equiv_def])
  >- (
    (* Abort case *)
    Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
    gvs[result_equiv_def])
  >- (
    (* IntRet case *)
    Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
    gvs[result_equiv_def])
  >>
  (* Error case *)
  Cases_on `run_block fuel ctx (clear_nops_block bb) s` >>
  gvs[result_equiv_def]
QED


(* fn_insts_blocks is FLAT (MAP bb_instructions) *)
Theorem fn_insts_blocks_flat[local]:
  !l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* clear_nops_function only removes instructions *)
Theorem clear_nops_fn_insts_subset:
  !fn inst. MEM inst (fn_insts (clear_nops_function fn)) ==>
            MEM inst (fn_insts fn)
Proof
  rpt strip_tac >>
  fs[fn_insts_def, fn_insts_blocks_flat, clear_nops_function_def,
     MEM_FLAT, MEM_MAP] >>
  qexists_tac `y.bb_instructions` >>
  (conj_tac >- metis_tac[]) >>
  gvs[clear_nops_block_def, MEM_FILTER]
QED

(* Helper: clear_nops produces a sublist of instructions *)
Theorem clear_nops_fn_insts_sublist[local]:
  !blocks. sublist
    (fn_insts_blocks (MAP clear_nops_block blocks))
    (fn_insts_blocks blocks)
Proof
  Induct >> simp[fn_insts_blocks_def, rich_listTheory.sublist_def] >>
  gen_tac >>
  irule rich_listTheory.sublist_append_pair >>
  simp[clear_nops_block_def, rich_listTheory.FILTER_sublist]
QED

Theorem clear_nops_function_preserves_ssa:
  !fn. ssa_form fn ==> ssa_form (clear_nops_function fn)
Proof
  rpt strip_tac >>
  irule passSimulationProofsTheory.ssa_form_sublist_proof >>
  qexists_tac `fn` >> simp[fn_insts_def, clear_nops_function_def] >>
  simp[clear_nops_fn_insts_sublist]
QED

(* ===================================================================== *)
(* ===== Re-exported proof results ===================================== *)
(* ===================================================================== *)

(* Operand substitution *)
Theorem subst_operand_eval =
  passSharedSubstTheory.subst_operand_eval

Theorem subst_op_map_eval =
  passSharedSubstTheory.subst_op_map_eval

Theorem subst_operand_eval_operands =
  passSharedSubstTheory.subst_operand_eval_operands

Theorem subst_op_map_eval_operands =
  passSharedSubstTheory.subst_op_map_eval_operands

Theorem subst_operands_correct =
  passSharedSubstTheory.subst_operands_correct

(* Supersedes passSharedSubstTheory.subst_operands_map_correct:
   inst_wf handles structural positions (Lit in PARAM/ALLOCA/LOG),
   so per-opcode exclusions unnecessary — only PHI excluded. *)
Theorem subst_operands_map_correct:
  !fuel ctx inst s subs.
    (!v new_op. FLOOKUP subs v = SOME new_op ==>
                eval_operand new_op s = eval_operand (Var v) s) /\
    inst_wf inst /\
    inst.inst_opcode <> PHI ==>
    step_inst fuel ctx (subst_operands_map subs inst) s =
    step_inst fuel ctx inst s
Proof
  rpt strip_tac >>
  irule passSharedSubstTheory.subst_operands_map_correct_wf >> simp[]
QED

(* State field preservation *)
Theorem step_inst_preserves_all =
  passSharedFieldTheory.step_inst_preserves_all

Theorem step_inst_no_memory_write_preserves_memory:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ∧
    ¬is_terminator inst.inst_opcode ∧
    ¬is_alloca_op inst.inst_opcode ∧
    ¬is_ext_call_op inst.inst_opcode ∧
    inst.inst_opcode ≠ INVOKE ⇒
    s'.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  drule_all step_inst_preserves_all >> simp[]
QED

Theorem step_base_preserves_tracked =
  passSharedFieldTheory.step_base_preserves_tracked

Theorem eligible_no_write_balance_extcode =
  passSharedFieldTheory.eligible_no_write_balance_extcode

(* Transient frame *)
Theorem step_inst_base_trans_frame =
  passSharedFieldTheory.step_inst_base_trans_frame

Theorem step_inst_base_trans_error_frame =
  passSharedFieldTheory.step_inst_base_trans_error_frame

(* Account storage-only frame *)
Theorem step_inst_base_acct_frame =
  passSharedFieldTheory.step_inst_base_acct_frame

Theorem step_inst_base_acct_error_frame =
  passSharedFieldTheory.step_inst_base_acct_error_frame

(* Transfer/determinism *)
Theorem step_inst_base_ok_transfer =
  passSharedTransferTheory.step_inst_base_ok_transfer

Theorem step_inst_base_output_determined_fields =
  passSharedTransferTheory.step_inst_base_output_determined_fields

(* Variable frame *)
Theorem step_inst_base_var_frame_full =
  passSharedVarFrameTheory.step_inst_base_var_frame_full

Theorem step_inst_var_frame_full =
  passSharedVarFrameTheory.step_inst_var_frame_full

(* Commutativity *)
Theorem effects_independent_commute =
  passSharedFrameTheory.effects_independent_commute

Theorem step_inst_base_effect_free_output_determined_vars =
  passSharedTransferTheory.step_inst_base_effect_free_output_determined_vars

(* Operand equivalence *)
Theorem step_inst_operands_equiv =
  passSharedSubstTheory.step_inst_operands_equiv

(* ===================================================================== *)
(* ===== Copy forwarding equivalence =================================== *)
(* ===================================================================== *)

Theorem copy_fwd_cross_equiv =
  copyFwdEquivTheory.copy_fwd_cross_equiv

Theorem copy_fwd_rel_observable_equiv =
  copyFwdEquivTheory.copy_fwd_rel_observable_equiv

Theorem copy_fwd_read_equiv =
  copyFwdEquivTheory.copy_fwd_read_equiv

Theorem copy_fwd_write_equiv =
  copyFwdEquivTheory.copy_fwd_write_equiv

Theorem copy_fwd_terminator_equiv =
  copyFwdEquivTheory.copy_fwd_terminator_equiv

Theorem copy_fwd_rel_preserved_identical_inst =
  copyFwdEquivTheory.copy_fwd_rel_preserved_identical_inst

Theorem assign_transparent =
  copyFwdEquivTheory.assign_transparent

Theorem phi_transparent =
  copyFwdEquivTheory.phi_transparent
