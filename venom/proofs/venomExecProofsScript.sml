(*
 * Venom Semantic Properties
 *
 * General semantic lemmas useful for any optimization pass.
 * Contains properties of bool_to_word and instruction behavior lemmas.
 *
 * After the step_inst refactor, step_inst_base handles individual opcodes
 * (no INVOKE), while step_inst fuel ctx handles all opcodes including INVOKE.
 * Most behavior lemmas are about step_inst_base; the new step_inst delegates
 * to step_inst_base for non-INVOKE via step_inst_non_invoke.
 *)

Theory venomExecProofs
Ancestors
  venomExecSemantics venomInst venomInstProofs venomState venomWf rich_list list finite_map stateEquiv passSimulationDefs

(* ==========================================================================
   bool_to_word Properties
   ========================================================================== *)

Theorem bool_to_word_T:
  bool_to_word T = 1w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_F:
  bool_to_word F = 0w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_eq_0w[local]:
  (bool_to_word b = 0w) <=> ~b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

Theorem bool_to_word_neq_0w[local]:
  (bool_to_word b <> 0w) <=> b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

(* ==========================================================================
   step_inst_base Behavior Lemmas (specific opcodes)
   ========================================================================== *)

Theorem step_iszero_value:
  !s cond_op out id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst_base <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
Proof
  rpt strip_tac >>
  simp[step_inst_base_def] >>
  simp[exec_pure1_def]
QED

Theorem step_assert_behavior:
  !s cond_op id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst_base <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    if cond = 0w then
      Abort Revert_abort (revert_state (set_returndata [] s))
    else OK s
Proof
  rw[step_inst_base_def]
QED

Theorem step_revert_behavior:
  !s off_op sz_op id off sz.
    eval_operand off_op s = SOME off /\
    eval_operand sz_op s = SOME sz ==>
    step_inst_base <| inst_id := id; inst_opcode := REVERT;
                 inst_operands := [off_op; sz_op]; inst_outputs := [] |> s =
    Abort Revert_abort
      (revert_state
        (set_returndata
          (TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w))
          s))
Proof
  rw[step_inst_base_def]
QED

Theorem step_jmp_behavior:
  !s lbl id.
    step_inst_base <| inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := [] |> s =
    OK (jump_to lbl s)
Proof
  rw[step_inst_base_def]
QED

Theorem step_jnz_behavior:
  !s cond_op if_nonzero if_zero id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst_base <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    if cond <> 0w then OK (jump_to if_nonzero s)
    else OK (jump_to if_zero s)
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[opcode_case_def]
QED

(* ==========================================================================
   block_step / exec_block Properties
   ========================================================================== *)

Theorem block_step_increments_idx:
  !bb s v.
    block_step bb s = (OK v, F)
    ==>
    v.vs_inst_idx = SUC s.vs_inst_idx
Proof
  rw[block_step_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  Cases_on `step_inst_base x s` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[next_inst_def] >>
  `v'.vs_inst_idx = s.vs_inst_idx` by (
    drule_all step_inst_base_preserves_inst_idx >> simp[]
  ) >>
  simp[]
QED

Theorem exec_block_OK_not_halted:
  !fuel ctx bb s v. exec_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rw[] >> gvs[]
QED

val step_term_ok_jump_fields_tac =
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  rw[] >> gvs[lookup_var_def] >> NO_TAC;

Triviality step_inst_ok_terminator_jump_fields[local]:
  !fuel ctx inst s v.
    step_inst fuel ctx inst s = OK v /\
    is_terminator inst.inst_opcode ==>
    v.vs_inst_idx = 0 /\ v.vs_prev_bb = SOME s.vs_current_bb /\
    v.vs_halted = s.vs_halted /\
    (!x. lookup_var x v = lookup_var x s) /\
    v.vs_labels = s.vs_labels
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
  >- (qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[Once step_inst_def, step_inst_base_def, jump_to_def] >>
      gvs[AllCaseEqs(), PULL_EXISTS] >> rpt gen_tac >> strip_tac >>
      pairarg_tac >> gvs[])
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
  >- step_term_ok_jump_fields_tac
QED

Theorem exec_block_OK_inst_idx_0:
  !fuel ctx bb s v. exec_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rw[] >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `v`] mp_tac
    step_inst_ok_terminator_jump_fields >>
  impl_tac >- gvs[] >> gvs[]
QED

(* exec_block OK implies prev_bb was set by jump_to (JMP/JNZ/DJMP) *)
Theorem exec_block_ok_sets_prev_bb:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==>
    s'.vs_prev_bb <> NONE
Proof
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `SOME inst` >>
  Cases_on `step_inst fuel ctx inst s` >> simp[] >>
  rw[] >> gvs[] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
    step_inst_ok_terminator_jump_fields >>
  impl_tac >- gvs[] >> gvs[]
QED

(* bind_outputs preserves vs_prev_bb *)
Triviality foldl_update_var_prev_bb:
  !kvs s.
    (FOLDL (\s' (k,v). update_var k v s') s kvs).vs_prev_bb =
    s.vs_prev_bb
Proof
  Induct >> simp[] >> Cases >> simp[update_var_def]
QED

Triviality bind_outputs_prev_bb:
  bind_outputs outs vals s = SOME s' ==> s'.vs_prev_bb = s.vs_prev_bb
Proof
  rw[bind_outputs_def, AllCaseEqs()] >> simp[foldl_update_var_prev_bb]
QED

(* step_inst OK preserves vs_prev_bb for non-terminators (including INVOKE) *)
Theorem step_inst_preserves_prev_bb:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode ==>
    s'.vs_prev_bb = s.vs_prev_bb
Proof
  metis_tac[step_preserves_control_flow]
QED

(* step_inst_base returns Error for INVOKE *)
Theorem step_inst_base_OK_not_INVOKE:
  step_inst_base inst s = OK s' ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_Halt_not_INVOKE:
  step_inst_base inst s = Halt v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_Abort_not_INVOKE:
  step_inst_base inst s = Abort a v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_IntRet_not_INVOKE:
  step_inst_base inst s = IntRet vals v ==> inst.inst_opcode <> INVOKE
Proof
  strip_tac >> strip_tac >> gvs[step_inst_base_def]
QED

(* Backward compat aliases (about step_inst_base, not the new step_inst) *)
Theorem step_inst_OK_not_INVOKE:
  step_inst_base inst s = OK s' ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC step_inst_base_OK_not_INVOKE
QED

Theorem step_inst_Halt_not_INVOKE:
  step_inst_base inst s = Halt v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC step_inst_base_Halt_not_INVOKE
QED

Theorem step_inst_Abort_not_INVOKE:
  step_inst_base inst s = Abort a v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC step_inst_base_Abort_not_INVOKE
QED

Theorem step_inst_IntRet_not_INVOKE:
  step_inst_base inst s = IntRet vals v ==> inst.inst_opcode <> INVOKE
Proof
  ACCEPT_TAC step_inst_base_IntRet_not_INVOKE
QED

(* extract_venom_result preserves vs_halted *)
Triviality extract_venom_result_preserves_halted:
  extract_venom_result s ov ro rs rr = SOME (out, s') ==>
  s'.vs_halted = s.vs_halted
Proof
  simp[extract_venom_result_def, AllCaseEqs()] >> rw[] >> gvs[] >>
  pairarg_tac >> gvs[]
QED

Triviality is_terminator_not_invoke[local]:
  !op. is_terminator op ==> op <> INVOKE
Proof
  Cases >> EVAL_TAC
QED

(* step_inst_base OK preserves vs_halted *)
Theorem step_inst_base_OK_preserves_halted:
  step_inst_base inst s = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (`inst.inst_opcode <> INVOKE` by
        metis_tac[is_terminator_not_invoke] >>
      `step_inst ARB ARB inst s = OK s'` by simp[Once step_inst_def] >>
      qspecl_then [`ARB`, `ARB`, `inst`, `s`, `s'`] mp_tac
        step_inst_ok_terminator_jump_fields >>
      impl_tac >- gvs[] >> gvs[])
  >- (`inst.inst_opcode <> INVOKE` by
        (drule step_inst_base_OK_not_INVOKE >> simp[]) >>
      `step_inst ARB ARB inst s = OK s'` by simp[Once step_inst_def] >>
      qspecl_then [`ARB`, `ARB`, `inst`, `s`, `s'`] mp_tac
        venomInstProofsTheory.step_preserves_halted >>
      impl_tac >- gvs[] >> gvs[])
QED

(* Backward compat alias *)
Theorem step_inst_OK_preserves_halted:
  step_inst_base inst s = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  ACCEPT_TAC step_inst_base_OK_preserves_halted
QED

(* For non-INVOKE blocks, exec_block unfolds through block_step *)
Theorem exec_block_block_step:
  !fuel ctx bb s.
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions ==>
    exec_block fuel ctx bb s =
      let (r, t) = block_step bb s in
      case r of
        OK s' => if t then (if s'.vs_halted then Halt s' else OK s')
                 else exec_block fuel ctx bb s'
      | Halt s' => Halt s'
      | Abort a s' => Abort a s'
      | Error e => Error e
      | IntRet vals s' => IntRet vals s'
Proof
  rw[block_step_def, LET_THM] >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by
    (gvs[listTheory.EVERY_MEM, get_instruction_def] >>
     first_x_assum irule >> irule listTheory.EL_MEM >> simp[]) >>
  simp[Once step_inst_def] >>
  Cases_on `step_inst_base inst s` >> simp[] >>
  Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
  (* non-terminator OK: relate new continuation to next_inst *)
  `v.vs_inst_idx = s.vs_inst_idx` by
    (drule step_inst_base_preserves_inst_idx >> simp[]) >>
  simp[next_inst_def, arithmeticTheory.ADD1]
QED

(* ==========================================================================
   FIND Lemmas
   ========================================================================== *)

Theorem FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

Theorem FIND_P:
  !P l x. FIND P l = SOME x ==> P x
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> metis_tac[]
QED

Triviality FIND_NONE:
  !P l. FIND P l = NONE ==> ~EXISTS P l
Proof
  Induct_on `l` >> simp[FIND_thm] >> rw[] >> gvs[]
QED

(* ==========================================================================
   Lookup Helpers
   ========================================================================== *)

Theorem lookup_block_MEM:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  rw[lookup_block_def] >> drule FIND_MEM >> simp[]
QED

(* lookup_block returns a block whose label matches the query *)
Theorem lookup_block_label:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> bb.bb_label = lbl
Proof
  rw[lookup_block_def] >> drule FIND_P >> simp[]
QED

Theorem exec_block_invoke_cases:
  !fuel ctx bb1 bb2 s inst.
    get_instruction bb1 s.vs_inst_idx = SOME inst /\
    get_instruction bb2 s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE ==>
    (exec_block fuel ctx bb1 s = exec_block fuel ctx bb2 s) \/
    (?s'. exec_block fuel ctx bb1 s = exec_block fuel ctx bb1 (next_inst s') /\
          exec_block fuel ctx bb2 s = exec_block fuel ctx bb2 (next_inst s') /\
          s'.vs_inst_idx = s.vs_inst_idx /\
          s'.vs_halted = s.vs_halted)
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `res = step_inst fuel ctx inst s` >>
  `exec_block fuel ctx bb1 s =
    case res of
      OK s' =>
        if is_terminator inst.inst_opcode then
          if s'.vs_halted then Halt s' else OK s'
        else exec_block fuel ctx bb1 (s' with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v s' => IntRet v s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | Error e => Error e`
    by simp[Once exec_block_def, Abbr `res`] >>
  `exec_block fuel ctx bb2 s =
    case res of
      OK s' =>
        if is_terminator inst.inst_opcode then
          if s'.vs_halted then Halt s' else OK s'
        else exec_block fuel ctx bb2 (s' with vs_inst_idx := SUC s.vs_inst_idx)
    | IntRet v s' => IntRet v s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | Error e => Error e`
    by simp[Once exec_block_def, Abbr `res`] >>
  Cases_on `res` >> gvs[]
  >- ((* OK: INVOKE is not a terminator *)
      `~is_terminator inst.inst_opcode` by simp[is_terminator_def] >> gvs[] >>
      DISJ2_TAC >>
      rename1 `step_inst fuel ctx inst s = OK v` >>
      qexists_tac `v` >>
      imp_res_tac step_inst_preserves_inst_idx >> gvs[] >>
      simp[next_inst_def, arithmeticTheory.ADD1] >>
      (* vs_halted: need step_inst INVOKE OK preserves halted *)
      qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
      simp[Once step_inst_def] >>
      gvs[AllCaseEqs()] >> rw[] >>
      imp_res_tac bind_outputs_inst_idx >>
      gvs[merge_callee_state_def, bind_outputs_def] >>
      qsuff_tac
        `!l acc. acc.vs_halted = s.vs_halted ==>
           (FOLDL (\s' (out,val). update_var out val s') acc l).vs_halted =
           s.vs_halted`
      >- (disch_then irule >> simp[])
      >> Induct >> simp[] >> Cases >> simp[update_var_def])
  >> (* IntRet/Halt/Abort/Error: both sides equal *)
     DISJ1_TAC >> simp[]
QED

Theorem block_step_prefix_same:
  !bb1 bb2 s n.
    TAKE (SUC n) bb1.bb_instructions = TAKE (SUC n) bb2.bb_instructions /\
    s.vs_inst_idx = n /\
    n < LENGTH bb1.bb_instructions /\
    n < LENGTH bb2.bb_instructions
  ==>
    block_step bb1 s = block_step bb2 s
Proof
  rw[block_step_def, get_instruction_def] >>
  `EL s.vs_inst_idx bb1.bb_instructions = EL s.vs_inst_idx bb2.bb_instructions` by (
    `EL s.vs_inst_idx (TAKE (SUC s.vs_inst_idx) bb1.bb_instructions) =
     EL s.vs_inst_idx (TAKE (SUC s.vs_inst_idx) bb2.bb_instructions)` by simp[] >>
    metis_tac[EL_TAKE, DECIDE ``n < SUC n``]
  ) >>
  simp[]
QED

(* ==========================================================================
   Shared block-level semantic theorems
   ========================================================================== *)

(* Terminator OK preserves vs_vars *)
Theorem step_terminator_preserves_vars:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
    step_inst_ok_terminator_jump_fields >>
  impl_tac >- gvs[] >> rw[]
QED

(* step_inst ALWAYS preserves vs_labels (both terminator and non-terminator) *)
Theorem step_inst_preserves_labels_always:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ==> s'.vs_labels = s.vs_labels
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s'`] mp_tac
      step_inst_ok_terminator_jump_fields >>
    impl_tac >- gvs[] >> rw[])
  >- metis_tac[step_preserves_labels]
QED

(* MEM + ALL_DISTINCT labels ==> lookup_block finds the block *)
Theorem MEM_lookup_block:
  !lbl bbs (bb:basic_block).
    MEM bb bbs /\ bb.bb_label = lbl /\
    ALL_DISTINCT (MAP (\bb. bb.bb_label) bbs) ==>
    lookup_block lbl bbs = SOME bb
Proof
  Induct_on `bbs` >> simp[lookup_block_def, FIND_thm] >>
  rpt strip_tac >> gvs[MEM_MAP] >> rw[] >> gvs[lookup_block_def]
QED

Theorem extract_labels_eq_map:
  !ops lbls. EVERY (\op. IS_SOME (get_label op)) ops /\
    extract_labels ops = SOME lbls ==>
    MAP (THE o get_label) ops = lbls
Proof
  Induct >> rw[extract_labels_def] >>
  Cases_on `h` >> fs[get_label_def, extract_labels_def] >>
  Cases_on `extract_labels ops` >> fs[]
QED

(* After a well-formed terminator executes OK without halting,
   vs_current_bb is in get_successors of that instruction. *)
val term_succ_basic_tac =
  fs[step_inst_base_def, inst_wf_def, get_successors_def,
     get_label_def, jump_to_def, is_terminator_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  rw[] >> gvs[];

val term_succ_djmp_tac =
  term_succ_basic_tac >>
  `MAP (THE o get_label) label_ops = labels` by
    metis_tac[extract_labels_eq_map] >>
  `FILTER IS_SOME (MAP get_label label_ops) = MAP get_label label_ops` by
    simp[FILTER_EQ_ID, EVERY_MAP] >>
  `MAP THE (MAP get_label label_ops) = labels` by
    fs[MAP_MAP_o] >>
  Cases_on `IS_SOME (get_label sel)` >> asm_rewrite_tac[MAP, MEM] >>
  fs[MEM_EL] >> metis_tac[MEM_EL];

Theorem step_inst_base_term_succs:
  !inst s s'.
    inst_wf inst /\ is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' /\ ~s'.vs_halted ==>
    MEM s'.vs_current_bb (get_successors inst)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> fs[is_terminator_def]
  >- term_succ_basic_tac
  >- term_succ_basic_tac
  >- term_succ_djmp_tac
  >- term_succ_basic_tac
  >- term_succ_basic_tac
  >- term_succ_basic_tac
  >- term_succ_basic_tac
  >- term_succ_basic_tac
  >- term_succ_basic_tac
  >- term_succ_basic_tac
  >- term_succ_basic_tac
  >- term_succ_basic_tac
QED

(* After a terminator step_inst_base returns OK,
   vs_prev_bb = SOME (input vs_current_bb).
   Only JMP/JNZ/DJMP return OK; all use jump_to which sets this. *)
Theorem step_inst_base_term_prev_bb:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    s'.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by metis_tac[is_terminator_not_invoke] >>
  `step_inst ARB ARB inst s = OK s'` by simp[Once step_inst_def] >>
  qspecl_then [`ARB`, `ARB`, `inst`, `s`, `s'`] mp_tac
    step_inst_ok_terminator_jump_fields >>
  impl_tac >- gvs[] >> gvs[]
QED

(* exec_block OK with vs_inst_idx=0 implies nonempty block *)
Theorem exec_block_ok_nonempty:
  !fuel ctx bb s v. s.vs_inst_idx = 0 /\ exec_block fuel ctx bb s = OK v ==>
    bb.bb_instructions <> []
Proof
  rpt gen_tac >> strip_tac >>
  spose_not_then assume_tac >>
  `bb.bb_instructions = []` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def]
QED

(* After exec_block OK, vs_current_bb is in bb_succs bb *)
Theorem exec_block_current_bb_in_succs:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    exec_block fuel ctx bb s = OK s1 ==>
    MEM s1.vs_current_bb (bb_succs bb)
Proof
  rpt strip_tac >>
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     exec_block fuel ctx bb s = OK s1 ==>
     MEM s1.vs_current_bb (bb_succs bb)`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    strip_tac >>
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> gvs[]
    >- (
      Cases_on `v.vs_halted` >> gvs[] >>
      `~(i < LENGTH bb.bb_instructions - 1)` by metis_tac[] >>
      `i = PRE (LENGTH bb.bb_instructions)` by fs[] >> gvs[] >>
      `inst_wf (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions)` by
        (fs[EVERY_EL]) >>
      `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode
         <> INVOKE` by
        (CCONTR_TAC >> gvs[is_terminator_def]) >>
      `step_inst_base
         (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) s' = OK s1` by
        gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_term_succs >> strip_tac >>
      simp[bb_succs_def] >>
      Cases_on `bb.bb_instructions` >> gvs[LAST_EL, MEM_nub, MEM_REVERSE]
    )
    >- (
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- simp[Abbr `i`] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `v with vs_inst_idx := SUC i`] mp_tac) >>
      simp[]
    )
  )
QED

(* After exec_block OK, vs_prev_bb = SOME (initial vs_current_bb).
   Terminators (JMP/JNZ/DJMP) all use jump_to which sets vs_prev_bb. *)
Theorem exec_block_ok_prev_bb:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    s.vs_inst_idx = 0 /\
    exec_block fuel ctx bb s = OK s1 ==>
    s1.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  `!n fuel ctx s'.
     n = LENGTH bb.bb_instructions - s'.vs_inst_idx /\
     s'.vs_inst_idx <= LENGTH bb.bb_instructions /\
     s'.vs_current_bb = s.vs_current_bb /\
     exec_block fuel ctx bb s' = OK s1 ==>
     s1.vs_prev_bb = SOME s.vs_current_bb`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    strip_tac >>
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> gvs[]
    >- (
      Cases_on `v.vs_halted` >> gvs[] >>
      `~(i < LENGTH bb.bb_instructions - 1)` by metis_tac[] >>
      `i = PRE (LENGTH bb.bb_instructions)` by fs[] >> gvs[] >>
      `(EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions).inst_opcode
         <> INVOKE` by
        (CCONTR_TAC >> gvs[is_terminator_def]) >>
      `step_inst_base
         (EL (PRE (LENGTH bb.bb_instructions)) bb.bb_instructions) s' = OK s1` by
        gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_term_prev_bb >> simp[]
    )
    >- (
      `v.vs_current_bb = s'.vs_current_bb` by
        (drule_all step_preserves_control_flow >> simp[]) >>
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- simp[Abbr `i`] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `v with vs_inst_idx := SUC i`] mp_tac) >>
      simp[]
    )
  )
QED

(* Generalized version: works from any starting index, not just vs_inst_idx = 0.
   Key for run_block proofs where exec_block starts at phi_prefix_length. *)
Theorem exec_block_ok_prev_bb_general:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    exec_block fuel ctx bb s = OK s1 ==>
    s1.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  `!n fuel ctx s'.
     n = LENGTH bb.bb_instructions - s'.vs_inst_idx /\
     s'.vs_inst_idx <= LENGTH bb.bb_instructions /\
     s'.vs_current_bb = s.vs_current_bb /\
     exec_block fuel ctx bb s' = OK s1 ==>
     s1.vs_prev_bb = SOME s.vs_current_bb`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel' ctx' (EL i bb.bb_instructions) s'` >>
  gvs[]
  >- (
    strip_tac >>
    Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> gvs[]
    >- (
      Cases_on `v.vs_halted` >> gvs[] >>
      `(EL i bb.bb_instructions).inst_opcode <> INVOKE` by
        (CCONTR_TAC >> gvs[is_terminator_def] >>
         fs[Abbr `i`]) >>
      `step_inst_base
         (EL i bb.bb_instructions) s' = OK s1` by
        gvs[step_inst_non_invoke] >>
      drule_all step_inst_base_term_prev_bb >> simp[]
    )
    >- (
      `v.vs_current_bb = s'.vs_current_bb` by
        (drule_all step_preserves_control_flow >> simp[]) >>
      qpat_x_assum `!m. m < _ ==> _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- simp[Abbr `i`] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `v with vs_inst_idx := SUC i`] mp_tac) >>
      simp[]
    )
  )
QED

(* ==========================================================================
   Variable Preservation Across Block Execution

   If a variable v is not in ANY instruction's outputs within a block,
   then exec_block preserves lookup_var v.
   ========================================================================== *)

Theorem exec_block_preserves_non_output_vars:
  !fuel ctx bb s s'.
    exec_block fuel ctx bb s = OK s' ==>
    !v. ~MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) ==>
    lookup_var v s' = lookup_var v s
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  (* Strong induction on remaining instructions *)
  `!n f c st st'.
     n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
     exec_block f c bb st = OK st' ==>
     lookup_var v st' = lookup_var v st`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`, `s'`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  (* Case split: idx past end or within block *)
  Cases_on `idx >= LENGTH bb.bb_instructions`
  >- (
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  `idx < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst f c (EL idx bb.bb_instructions) st` >> gvs[] >>
  Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode` >> gvs[]
  >- (
    (* Terminator: halted contradicts OK, so st' = v' *)
    Cases_on `v'.vs_halted` >> gvs[] >>
    metis_tac[step_terminator_preserves_vars]
  ) >>
  (* Non-terminator: step preserves v, then IH *)
  strip_tac >>
  `~MEM v (EL idx bb.bb_instructions).inst_outputs` by (
    fs[MEM_FLAT, MEM_MAP] >> metis_tac[MEM_EL]) >>
  `lookup_var v v' = lookup_var v st` by
    metis_tac[step_preserves_non_output_vars] >>
  `lookup_var v st' = lookup_var v (v' with vs_inst_idx := SUC idx)` by (
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
    (impl_tac >- simp[Abbr `idx`]) >>
    disch_then (qspecl_then [`f`, `c`,
      `v' with vs_inst_idx := SUC idx`, `st'`] mp_tac) >>
    simp[]) >>
  fs[lookup_var_def]
QED

(* ==========================================================================
   Block Equivalence Under Shared Instructions

   If two blocks agree on all instructions from current index onwards
   (within bb1's range), then exec_block gives the same result.
   ========================================================================== *)

Theorem exec_block_same_insts:
  !fuel ctx bb1 bb2 s.
    s.vs_inst_idx < LENGTH bb1.bb_instructions /\
    LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    (!i. s.vs_inst_idx <= i /\ i < LENGTH bb1.bb_instructions ==>
      EL i bb1.bb_instructions = EL i bb2.bb_instructions) ==>
    exec_block fuel ctx bb1 s = exec_block fuel ctx bb2 s
Proof
  rpt gen_tac >> strip_tac >>
  `!n f c st.
     n = LENGTH bb1.bb_instructions - st.vs_inst_idx /\
     st.vs_inst_idx < LENGTH bb1.bb_instructions /\
     (!i. st.vs_inst_idx <= i /\ i < LENGTH bb1.bb_instructions ==>
       EL i bb1.bb_instructions = EL i bb2.bb_instructions) ==>
     exec_block f c bb1 st = exec_block f c bb2 st`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb1.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`] mp_tac) >> simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  `idx < LENGTH bb2.bb_instructions` by simp[Abbr `idx`] >>
  `EL idx bb1.bb_instructions = EL idx bb2.bb_instructions` by (
    first_x_assum (qspec_then `idx` mp_tac) >> simp[Abbr `idx`]) >>
  (* Expand exec_block on both sides; both see the same instruction *)
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  (* Case split on step_inst result — common to both sides *)
  Cases_on `step_inst f c (EL idx bb2.bb_instructions) st` >> simp[] >>
  (* OK case: check terminator *)
  Cases_on `is_terminator (EL idx bb2.bb_instructions).inst_opcode` >>
  simp[] >>
  (* Non-terminator: apply IH or show idx was last instruction *)
  Cases_on `SUC idx < LENGTH bb1.bb_instructions`
  >- (
    qpat_x_assum `!m. m < _ ==> _` (qspec_then
      `LENGTH bb1.bb_instructions - SUC idx` mp_tac) >>
    (impl_tac >- simp[Abbr `idx`]) >>
    disch_then (qspecl_then [`f`, `c`,
      `v with vs_inst_idx := SUC idx`] mp_tac) >>
    simp[Abbr `idx`]) >>
  (* idx was last instruction: both blocks have no instruction at SUC idx *)
  `~(SUC idx < LENGTH bb2.bb_instructions)` by simp[] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[Once exec_block_def, get_instruction_def]
QED

(* ==========================================================================
   Fuel Monotonicity
   ==========================================================================
   If a computation terminates with result R (not Error) using fuel n,
   then it also terminates with R using any fuel m >= n.
   This is the key compositionality property for simulation proofs where
   the transformed program may use different fuel than the original.
   ========================================================================== *)

Theorem fuel_mono:
  (!n m ctx inst s r.
     step_inst n ctx inst s = r /\ (!e. r <> Error e) /\ n <= m ==>
     step_inst m ctx inst s = r) /\
  (!n m ctx bb s r.
     exec_block n ctx bb s = r /\ (!e. r <> Error e) /\ n <= m ==>
     exec_block m ctx bb s = r) /\
  (!n m ctx fn s r.
     run_blocks n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
     run_blocks m ctx fn s = r)
Proof
  (* Reshape for run_defs_ind: P(fuel, ctx, X, s) = !m r. ... *)
  `(!fuel ctx inst s.
      !m r. step_inst fuel ctx inst s = r /\ (!e. r <> Error e) /\
             fuel <= m ==> step_inst m ctx inst s = r) /\
   (!fuel ctx bb s.
      !m r. exec_block fuel ctx bb s = r /\ (!e. r <> Error e) /\
             fuel <= m ==> exec_block m ctx bb s = r) /\
   (!fuel ctx fn s.
      !m r. run_blocks fuel ctx fn s = r /\ (!e. r <> Error e) /\
             fuel <= m ==> run_blocks m ctx fn s = r)`
    suffices_by (rpt strip_tac >> res_tac >> simp[]) >>
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  (* --- step_inst case --- *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    Cases_on `inst.inst_opcode = INVOKE`
    >- (
      qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
      ASM_REWRITE_TAC[step_inst_def] >>
      BasicProvers.every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
      (* Derive run_blocks m = run_blocks fuel for the callee *)
      first_x_assum (qspecl_then [`(q, r')`, `q`, `r'`, `x'`, `x`, `x''`] mp_tac) >>
      simp[] >>
      disch_then (qspecl_then [`m`, `run_blocks fuel ctx x' x''`] mp_tac) >>
      simp[] >> strip_tac >> fs[] >> gvs[]
    )
    >- gvs[step_inst_non_invoke]
  )
  (* --- exec_block case --- *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    simp[Once exec_block_def] >>
    Cases_on `get_instruction bb s.vs_inst_idx`
    >- (simp[] >> strip_tac >> gvs[]) >>
    rename1 `SOME inst` >> simp[] >>
    (* Derive step_inst fuel_mono from step_inst IH *)
    `!si_r. step_inst fuel ctx inst s = si_r /\ (!e. si_r <> Error e) ==>
            step_inst m ctx inst s = si_r` by
      (rpt strip_tac >>
       qpat_x_assum `!inst'. _ ==> _` (qspec_then `inst` mp_tac) >> simp[] >>
       disch_then (qspecl_then [`m`, `si_r`] mp_tac) >> simp[]) >>
    Cases_on `step_inst fuel ctx inst s` >> simp[]
    >- (
      `step_inst m ctx inst s = OK v` by
        (first_x_assum (qspec_then `OK v` mp_tac) >> simp[]) >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[]
      >- (strip_tac >> gvs[] >> simp[Once exec_block_def])
      >- (
        strip_tac >> simp[Once exec_block_def] >>
        (* Use exec_block continuation IH *)
        qpat_x_assum `!inst' s''. _ /\ _ /\ _ ==> _`
          (qspecl_then [`inst`, `v`] mp_tac) >> simp[] >>
        disch_then (qspecl_then [`m`, `r`] mp_tac) >> simp[]
      )
    )
    >- (`step_inst m ctx inst s = Halt v` by
          (first_x_assum (qspec_then `Halt v` mp_tac) >> simp[]) >>
        strip_tac >> gvs[] >> simp[Once exec_block_def])
    >- (`step_inst m ctx inst s = Abort a v` by
          (first_x_assum (qspec_then `Abort a v` mp_tac) >> simp[]) >>
        strip_tac >> gvs[] >> simp[Once exec_block_def])
    >- (`step_inst m ctx inst s = IntRet i v` by
          (first_x_assum (qspec_then `IntRet i v` mp_tac) >> simp[]) >>
        strip_tac >> gvs[] >> simp[Once exec_block_def])
  )
  (* --- run_blocks case --- *)
  >- (
    rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
    Cases_on `fuel`
    >- gvs[run_blocks_def] >>
    rename1 `SUC fuel'` >>
    (* Expand source run_blocks assumption *)
    qpat_x_assum `run_blocks _ _ _ _ = _`
      (fn th => assume_tac (ONCE_REWRITE_RULE [run_blocks_def] th)) >>
    fs[] >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> fs[] >>
    rename1 `SOME bb` >>
    Cases_on `eval_phis s bb.bb_instructions` >> fs[]
    (* OK s_phi *)
    >- (
      rename1 `OK s_phi` >>
      (* Derive exec_block mono from P1 IH *)
      `!m' r'. exec_block fuel' ctx bb
                 (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r' /\
               (!e. r' <> Error e) /\ fuel' <= m' ==>
               exec_block m' ctx bb
                 (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r'` by
        (rpt strip_tac >>
         qpat_x_assum `!m'. _ ==> run_block_non_phis m' ctx bb _ = _`
           (qspec_then `m'` mp_tac) >> simp[]) >>
      Cases_on `exec_block fuel' ctx bb
                  (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> gvs[]
      (* -- OK case -- *)
      >- (
        Cases_on `v.vs_halted` >> gvs[]
        (* halted *)
        >- (
          Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
          `exec_block m'' ctx bb
             (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK v` by
            (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
          simp[Once run_blocks_def]
        )
        (* not halted *)
        >- (
          Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
          `exec_block m'' ctx bb
             (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK v` by
            (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
          simp[Once run_blocks_def] >>
          qpat_x_assum `!s''. _ /\ ~_ ==> _` (qspec_then `v` mp_tac) >> simp[] >>
          disch_then (qspecl_then [`m''`, `r`] mp_tac) >> simp[]
        )
      )
      (* -- Halt case -- *)
      >- (
        Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
        `exec_block m'' ctx bb
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Halt v` by
          (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
        simp[Once run_blocks_def]
      )
      (* -- Abort case -- *)
      >- (
        Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
        `exec_block m'' ctx bb
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Abort a v` by
          (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
        simp[Once run_blocks_def]
      )
      (* -- IntRet case -- *)
      >- (
        Cases_on `m` >- gvs[] >> rename1 `SUC m''` >>
        `exec_block m'' ctx bb
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = IntRet i v` by
          (first_x_assum (qspec_then `m''` mp_tac) >> simp[]) >>
        simp[Once run_blocks_def]
      )
    )
    (* Halt/Abort/IntRet from eval_phis — these are ARB cases, impossible
       since eval_phis only returns OK or Error *)
    >> (
      `(?s'. eval_phis s bb.bb_instructions = OK s') \/
       (?e'. eval_phis s bb.bb_instructions = Error e')` by
        metis_tac[eval_phis_ok_or_error_defs] >> fs[]
    )
    (* Error from eval_phis — contradicts !e. r <> Error e *)
    >> gvs[]
  )
QED

(* run_block fuel monotonicity: boundary lemma lifting exec_block fuel_mono
   through the eval_phis wrapper. *)
Theorem run_block_fuel_mono:
  !fuel fuel' ctx bb st res.
    run_block fuel ctx bb st = res /\ (!e. res <> Error e) /\ fuel <= fuel' ==>
    run_block fuel' ctx bb st = res
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`st`,`bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE[run_block_def]) >>
  ONCE_REWRITE_TAC[run_block_def] >>
  gvs[AllCaseEqs()] >>
  metis_tac[cj 2 fuel_mono]
QED


(* ==========================================================================
   Operand FDOM Properties
   ========================================================================== *)



(* For non-excluded opcodes with inst_wf:
   if a Var operand is not in FDOM (eval returns NONE), step_inst_base returns Error.
   Contrapositive: non-Error implies all Var operands are in FDOM. *)
Triviality eval_operands_mem_none[local]:
  !ops s op. MEM op ops /\ eval_operand op s = NONE ==>
    eval_operands ops s = NONE
Proof
  Induct >> simp[eval_operands_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `op = h` >> gvs[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  BasicProvers.TOP_CASE_TAC >> simp[] >>
  metis_tac[optionTheory.NOT_NONE_SOME]
QED



(* General: if eval_operands returns NONE for the full operand list,
   step_inst_base returns Error for non-excluded opcodes.
   Note: DJMP/OFFSET excluded because they don't eval all operands via
   eval_operands (DJMP uses extract_labels, OFFSET has Label operand).
   JMP/PARAM/ALLOCA also excluded because their operands are Lit/Label only. *)
(* Split into two parts to stay under 5s per tactic step *)

Triviality exec_pure1_operands_none_error[local]:
  !f inst s.
    LENGTH inst.inst_operands = 1 /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. exec_pure1 f inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >>
  gvs[LENGTH_EQ_NUM_compute, eval_operands_def, exec_pure1_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality exec_pure2_operands_none_error[local]:
  !f inst s.
    LENGTH inst.inst_operands = 2 /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. exec_pure2 f inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >>
  gvs[LENGTH_EQ_NUM_compute, eval_operands_def, exec_pure2_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality exec_pure3_operands_none_error[local]:
  !f inst s.
    LENGTH inst.inst_operands = 3 /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. exec_pure3 f inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >>
  gvs[LENGTH_EQ_NUM_compute, eval_operands_def, exec_pure3_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality exec_read1_operands_none_error[local]:
  !f inst s.
    LENGTH inst.inst_operands = 1 /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. exec_read1 f inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >>
  gvs[LENGTH_EQ_NUM_compute, eval_operands_def, exec_read1_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality exec_write2_operands_none_error[local]:
  !f inst s.
    LENGTH inst.inst_operands = 2 /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. exec_write2 f inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_operands` >>
  gvs[LENGTH_EQ_NUM_compute, eval_operands_def, exec_write2_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

val operands_none_wrapper_tac =
  gvs[inst_wf_def, step_inst_base_def] >>
  FIRST [
    drule_all exec_pure1_operands_none_error >> simp[] >> NO_TAC,
    drule_all exec_pure2_operands_none_error >> simp[] >> NO_TAC,
    drule_all exec_pure3_operands_none_error >> simp[] >> NO_TAC,
    drule_all exec_read1_operands_none_error >> simp[] >> NO_TAC,
    drule_all exec_write2_operands_none_error >> simp[] >> NO_TAC
  ];

(* Part 1: "uniform" opcodes that go through exec_pure/read/write wrappers *)
Triviality step_inst_base_operands_none_uniform[local]:
  !inst s.
    MEM inst.inst_opcode [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp;
      ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT; ISZERO;
      AND; OR; XOR; NOT; SHL; SHR; SAR; SIGNEXTEND; BYTE;
      MLOAD; MSTORE; MSTORE8; SLOAD; SSTORE; TLOAD; TSTORE;
      BLOCKHASH; BLOBHASH; BALANCE; CALLDATALOAD;
      EXTCODESIZE; EXTCODEHASH; ILOAD; DLOAD] /\
    inst_wf inst /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[MEM]
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
  >- operands_none_wrapper_tac
QED

val operands_none_custom_tac =
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      step_inst_base_def,
      eval_operands_def, eval_operand_def, lookup_var_def] >>
  BasicProvers.every_case_tac >> gvs[];

(* Part 2: custom opcodes with inline operand handling.
   JNZ excluded: its Label operands cause eval_operands=NONE but
   step_inst_base only evaluates the condition, so it can succeed. *)
Triviality step_inst_base_operands_none_custom[local]:
  !inst s.
    MEM inst.inst_opcode [MCOPY; ISTORE; RET; RETURN; REVERT;
      ASSIGN; INVOKE; CALLDATACOPY; RETURNDATACOPY; CODECOPY;
      EXTCODECOPY; SHA3; CALL; STATICCALL; DELEGATECALL;
      CREATE; CREATE2; SELFDESTRUCT; ASSERT; ASSERT_UNREACHABLE;
      DLOADBYTES; DALLOCA; DRET; GETFMP; SETFMP; RETFMP;
      INITIAL_FMP; BUMP; FMP_PARAM; RETPC_PARAM] /\
    inst_wf inst /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >> gvs[MEM]
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
  >- operands_none_custom_tac
QED

(* Part 3: LOG — needs special handling because inst_wf gives parametric-length
   operand list (Lit tc :: rest with LENGTH rest = w2n tc + 2).
   The key insight: eval_operand (Lit tc) s = SOME tc always, so
   eval_operands returning NONE means some element of rest evals to NONE.
   step_inst_base for LOG evaluates all of rest, so it must hit the NONE and error. *)
Triviality step_inst_base_operands_none_log[local]:
  !inst s.
    inst.inst_opcode = LOG /\
    inst_wf inst /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >>
  gvs[inst_wf_def] >>
  (* Now: inst.inst_operands = Lit tc :: rest, LENGTH rest = w2n tc + 2,
     eval_operands (Lit tc :: rest) s = NONE *)
  (* Lit tc always evaluates, so eval_operands rest s = NONE *)
  gvs[eval_operands_def, eval_operand_def] >>
  (* rest has length >= 2, so destructure it *)
  `?h1 h2 tl. rest = h1 :: h2 :: tl` by
    (Cases_on `rest` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  gvs[step_inst_base_def, eval_operands_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality step_inst_base_operands_none[local]:
  !inst s.
    inst_wf inst /\
    ~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MEMTOP;
      DJMP; JMP; JNZ; PARAM; ALLOCA; OFFSET] /\
    eval_operands inst.inst_operands s = NONE ==>
    ?e. step_inst_base inst s = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[MEM] >>
  FIRST
    [irule step_inst_base_operands_none_uniform >> simp[MEM] >> NO_TAC,
     irule step_inst_base_operands_none_custom >> simp[MEM] >> NO_TAC,
     irule step_inst_base_operands_none_log >> simp[]]
QED

Theorem step_inst_base_nonerr_var_fdom:
  !inst s x.
    inst_wf inst /\
    ~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MEMTOP] /\
    MEM (Var x) inst.inst_operands /\
    (!e. step_inst_base inst s <> Error e) ==>
    x IN FDOM s.vs_vars
Proof
  SPOSE_NOT_THEN STRIP_ASSUME_TAC >>
  `eval_operand (Var x) s = NONE` by
    simp[eval_operand_def, lookup_var_def, finite_mapTheory.flookup_thm] >>
  qpat_x_assum `!e. _ <> _` mp_tac >> simp[] >>
  imp_res_tac eval_operands_mem_none >>
  (* DJMP: Var x is sel => eval NONE => Error;
     Var x in label_ops => contradicts EVERY IS_SOME get_label *)
  Cases_on `inst.inst_opcode = DJMP` >-
    (gvs[inst_wf_def] >>
     (* gvs splits MEM: subgoals with sel=Var x close via step_inst_base *)
     TRY (gvs[step_inst_base_def, eval_operand_def, lookup_var_def] >> NO_TAC) >>
     (* remaining: MEM Var x label_ops contradicts EVERY IS_SOME get_label *)
     gvs[listTheory.EVERY_MEM] >> res_tac >> fs[get_label_def]) >>
  (* JMP/PARAM/ALLOCA: no Var operands possible *)
  Cases_on `inst.inst_opcode = JMP` >-
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM] >>
  Cases_on `inst.inst_opcode = PARAM` >-
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM] >>
  Cases_on `inst.inst_opcode = ALLOCA` >-
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM] >>
  (* OFFSET: Var x must be offset_op, eval_operand NONE => Error *)
  Cases_on `inst.inst_opcode = OFFSET` >-
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM, step_inst_base_def,
        exec_pure2_def] >>
  (* JNZ: ops = [c; Label l1; Label l2], only Var is c, eval_operand c NONE => Error *)
  Cases_on `inst.inst_opcode = JNZ` >-
    (gvs[inst_wf_def, LENGTH_EQ_NUM_compute, MEM, step_inst_base_def,
        eval_operand_def, lookup_var_def] >>
     BasicProvers.every_case_tac >> gvs[]) >>
  (* All other opcodes: use step_inst_base_operands_none *)
  `~MEM inst.inst_opcode [NOP; PHI; STOP; SINK; INVALID;
      CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
      ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
      SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
      CODESIZE; MEMTOP; DJMP; JMP; JNZ; PARAM; ALLOCA; OFFSET]` by
    gvs[MEM] >>
  drule_all step_inst_base_operands_none >> metis_tac[]
QED

(* ==========================================================================
   FDOM Monotonicity for step_inst_base

   After a successful non-terminator step_inst_base:
   1. All existing FDOM vars remain in FDOM
   2. All inst_outputs are in FDOM
   Combined: FDOM s'.vs_vars = FDOM s.vs_vars ∪ set inst.inst_outputs

   Proof by opcode case split, grouped to stay under 5s per step.
   Every non-terminator opcode with outputs uses update_var, giving |+.
   Every non-terminator opcode without outputs preserves vs_vars.
   ========================================================================== *)

(* Helper: update_var adds output to FDOM and preserves existing *)
Triviality update_var_fdom[local]:
  !x v s. FDOM (update_var x v s).vs_vars = x INSERT FDOM s.vs_vars
Proof
  simp[update_var_def, finite_mapTheory.FDOM_FUPDATE]
QED

(* Helper: FOLDL update_var adds all outputs *)
Triviality foldl_update_var_fdom[local]:
  !kvs s.
    FDOM (FOLDL (\s' (k,v). update_var k v s') s kvs).vs_vars =
    FDOM s.vs_vars UNION set (MAP FST kvs)
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >>
  rpt gen_tac >> simp[update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

(* extract_venom_result preserves vs_vars *)
Triviality extract_venom_result_preserves_vars[local]:
  !s out ro rs r output s'.
    extract_venom_result s out ro rs r = SOME (output, s') ==>
    s'.vs_vars = s.vs_vars
Proof
  rpt gen_tac >>
  simp[extract_venom_result_def] >>
  BasicProvers.every_case_tac >> simp[] >>
  strip_tac >> gvs[]
QED

(* All groups share this tactic pattern *)
fun prove_fdom_group opcode_list = prove(
  ``!inst s s'.
     MEM inst.inst_opcode ^opcode_list /\
     inst_wf inst /\ step_inst_base inst s = OK s' ==>
     FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs``,
  rpt strip_tac >> gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute,
      step_inst_base_def, exec_pure2_def, exec_pure1_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      exec_alloca_def,
      istore_def, mstore_def, mstore8_def, sstore_def, tstore_def] >>
  BasicProvers.every_case_tac >>
  gvs[update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]);

val step_inst_base_fdom_pure2 = prove_fdom_group
  ``[ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp;
     ADDMOD; MULMOD; EQ; LT; GT; SLT; SGT;
     AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE]``;

val step_inst_base_fdom_pure1 = prove_fdom_group
  ``[ISZERO; NOT]``;

val step_inst_base_fdom_read0 = prove_fdom_group
  ``[CALLER; ADDRESS; CALLVALUE; GAS; GASLIMIT;
     ORIGIN; GASPRICE; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO; CHAINID;
     SELFBALANCE; BASEFEE; BLOBBASEFEE; CALLDATASIZE; RETURNDATASIZE;
     CODESIZE; MEMTOP]``;

val step_inst_base_fdom_read1 = prove_fdom_group
  ``[MLOAD; SLOAD; TLOAD; ILOAD; DLOAD;
     CALLDATALOAD; BALANCE; BLOCKHASH; BLOBHASH;
     EXTCODESIZE; EXTCODEHASH]``;

val step_inst_base_fdom_write2 = prove_fdom_group
  ``[MSTORE; MSTORE8; SSTORE; TSTORE; ISTORE]``;

(* Zero-output group needs a different tactic: the state changes are
   to memory/storage/logs, not vs_vars, so record accessor simp suffices *)
val step_inst_base_fdom_no_output = prove(
  ``!inst s s'.
     MEM inst.inst_opcode [NOP; MCOPY; LOG; CALLDATACOPY; CODECOPY;
       RETURNDATACOPY; EXTCODECOPY; DLOADBYTES;
       ASSERT; ASSERT_UNREACHABLE] /\
     inst_wf inst /\ step_inst_base inst s = OK s' ==>
     FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs``,
  rpt strip_tac >> gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, step_inst_base_def] >>
  BasicProvers.every_case_tac >>
  gvs[mstore_def, sstore_def, tstore_def,
      mcopy_def, write_memory_with_expansion_def]);

val step_inst_base_fdom_custom1 = prove_fdom_group
  ``[ASSIGN; SHA3; PARAM; ALLOCA; OFFSET; DALLOCA; GETFMP; SETFMP;
     INITIAL_FMP; BUMP; FMP_PARAM; RETPC_PARAM]``;

(* External calls: extract_venom_result preserves vs_vars, then update_var adds output *)
val step_inst_base_fdom_external = prove(
  ``!inst s s'.
     MEM inst.inst_opcode [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2] /\
     inst_wf inst /\ step_inst_base inst s = OK s' ==>
     FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs``,
  rpt strip_tac >> gvs[MEM] >>
  gvs[inst_wf_def, LENGTH_EQ_NUM_compute, step_inst_base_def] >>
  BasicProvers.every_case_tac >>
  gvs[exec_ext_call_def, exec_delegatecall_def, exec_create_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  imp_res_tac extract_venom_result_preserves_vars >> gvs[] >>
  gvs[update_var_def, finite_mapTheory.FDOM_FUPDATE] >>
  simp[pred_setTheory.EXTENSION] >> metis_tac[]);

(* INVOKE: step_inst_base returns Error, so premise is vacuously false *)
val step_inst_base_fdom_invoke = prove(
  ``!inst s s'.
     inst.inst_opcode = INVOKE /\
     inst_wf inst /\ step_inst_base inst s = OK s' ==>
     FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs``,
  rpt strip_tac >> gvs[step_inst_base_def]);

(* Main theorem: combine all parts *)
Theorem step_inst_base_fdom:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    inst_wf inst /\
    inst.inst_opcode <> PHI /\
    ~is_terminator inst.inst_opcode ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  FIRST [
    metis_tac[step_inst_base_fdom_pure2, MEM],
    metis_tac[step_inst_base_fdom_pure1, MEM],
    metis_tac[step_inst_base_fdom_read0, MEM],
    metis_tac[step_inst_base_fdom_read1, MEM],
    metis_tac[step_inst_base_fdom_write2, MEM],
    metis_tac[step_inst_base_fdom_no_output, MEM],
    metis_tac[step_inst_base_fdom_custom1, MEM],
    metis_tac[step_inst_base_fdom_external, MEM],
    metis_tac[step_inst_base_fdom_invoke]]
QED

(* bind_outputs FDOM: outputs added to vs_vars *)
Theorem bind_outputs_fdom:
  !outs vals s s'.
    bind_outputs outs vals s = SOME s' ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set outs
Proof
  simp[bind_outputs_def] >> rpt strip_tac >>
  BasicProvers.every_case_tac >> gvs[] >>
  metis_tac[foldl_update_var_fdom, listTheory.MAP_ZIP]
QED

(* Lift to step_inst: covers both INVOKE and non-INVOKE *)
Theorem step_inst_fdom:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    inst_wf inst /\
    inst.inst_opcode <> PHI /\
    ~is_terminator inst.inst_opcode ==>
    FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE case: merge_callee preserves vs_vars, bind_outputs adds outputs *)
    gvs[Once step_inst_def] >>
    BasicProvers.every_case_tac >> gvs[] >>
    Cases_on `i.iret_adopt_fmp` >> gvs[adopt_return_fmp_def] >>
    imp_res_tac bind_outputs_fdom >>
    gvs[merge_callee_state_def])
  >- (
    (* Non-INVOKE: delegate to step_inst_base_fdom *)
    `step_inst_base inst s = OK s'` by gvs[step_inst_non_invoke] >>
    metis_tac[step_inst_base_fdom])
QED

(* Well-formed terminators have no outputs. *)
Theorem terminator_no_outputs:
  !inst. inst_wf inst /\ is_terminator inst.inst_opcode ==>
    inst.inst_outputs = []
Proof
  rw[inst_wf_def] >> Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]
QED

(* IS_SOME(lookup_var v s) is monotone across step_inst OK.
   Non-terminator: step_inst_fdom says FDOM grows.
   Terminator: step_terminator_preserves_vars says all vars preserved. *)
Theorem step_inst_lookup_mono:
  !fuel ctx inst s s' v.
    step_inst fuel ctx inst s = OK s' /\ inst_wf inst /\
    inst.inst_opcode <> PHI /\
    IS_SOME (lookup_var v s) ==>
    IS_SOME (lookup_var v s')
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (`lookup_var v s' = lookup_var v s`
        by metis_tac[step_terminator_preserves_vars] >> gvs[])
  >> (Cases_on `MEM v inst.inst_outputs`
      >- (drule_all step_inst_fdom >> strip_tac >>
          fs[lookup_var_def, FLOOKUP_DEF])
      >> (`lookup_var v s' = lookup_var v s` by
            metis_tac[step_preserves_non_output_vars] >>
          gvs[]))
QED

(* PHI instruction execution is always an error in step_inst_base.
   PHIs are evaluated in parallel at block entry by eval_phis,
   never reached through normal sequential execution. *)
Theorem step_inst_base_phi_error:
  !inst s. inst.inst_opcode = PHI ==>
            step_inst_base inst s = Error "phi outside prefix"
Proof
  rpt strip_tac >> simp[step_inst_base_def]
QED

(* step_inst on PHI always gives Error *)
Theorem step_inst_phi_error:
  !fuel ctx inst s. inst.inst_opcode = PHI ==>
    step_inst fuel ctx inst s = Error "phi outside prefix"
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by fs[] >>
  drule step_inst_non_invoke >>
  simp[step_inst_base_phi_error]
QED

Theorem step_inst_ok_imp_not_phi:
  !fuel ctx inst s v. step_inst fuel ctx inst s = OK v ==> inst.inst_opcode <> PHI
Proof
  rpt strip_tac >> CCONTR_TAC >>
  `step_inst fuel ctx inst s = Error "phi outside prefix"` by
    metis_tac[step_inst_phi_error] >>
  fs[]
QED

(* IS_SOME(lookup_var v s) is monotone across step_inst OK.
   PHI case is impossible: step_inst on PHI gives Error, contradicting OK. *)
Triviality step_inst_lookup_mono_with_phi[local]:
  !fuel ctx inst s s' v.
    step_inst fuel ctx inst s = OK s' /\ inst_wf inst /\
    IS_SOME (lookup_var v s) ==>
    IS_SOME (lookup_var v s')
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (`lookup_var v s' = lookup_var v s` by metis_tac[step_terminator_preserves_vars] >>
      gvs[])
  >> Cases_on `inst.inst_opcode = PHI`
  >- (fs[step_inst_phi_error])
  >> Cases_on `MEM v inst.inst_outputs`
  >- (drule_all step_inst_fdom >> strip_tac >> fs[lookup_var_def, FLOOKUP_DEF])
  >> `lookup_var v s' = lookup_var v s` by metis_tac[step_preserves_non_output_vars] >>
     gvs[]
QED


(* IS_SOME(lookup_var v s) is monotone across exec_block OK.
   Proof by strong induction on remaining instructions,
   same structure as exec_block_preserves_non_output_vars. *)
Theorem exec_block_lookup_mono:
  !fuel ctx bb s s' v.
    exec_block fuel ctx bb s = OK s' /\
    EVERY inst_wf bb.bb_instructions /\
    IS_SOME (lookup_var v s) ==>
    IS_SOME (lookup_var v s')
Proof
  rpt gen_tac >> strip_tac >>
  `!n f c st st'.
     n = LENGTH bb.bb_instructions - st.vs_inst_idx /\
     EVERY inst_wf bb.bb_instructions /\
     exec_block f c bb st = OK st' /\
     IS_SOME (lookup_var v st) ==>
     IS_SOME (lookup_var v st')`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`,
         `fuel`, `ctx`, `s`, `s'`] mp_tac) >> simp[]) >>
  completeInduct_on `n` >> rw[] >>
  qabbrev_tac `idx = st.vs_inst_idx` >>
  Cases_on `idx >= LENGTH bb.bb_instructions`
  >- (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def]) >>
  `idx < LENGTH bb.bb_instructions` by fs[] >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  ONCE_REWRITE_TAC[exec_block_def] >> simp[get_instruction_def] >>
  Cases_on `step_inst f c (EL idx bb.bb_instructions) st` >> gvs[] >>
  `inst_wf (EL idx bb.bb_instructions)` by fs[EVERY_EL] >>
  Cases_on `is_terminator (EL idx bb.bb_instructions).inst_opcode` >> gvs[]
  >- (Cases_on `v'.vs_halted` >> gvs[] >>
      metis_tac[step_inst_lookup_mono_with_phi]) >>
  strip_tac >>
  `IS_SOME (lookup_var v v')` by metis_tac[step_inst_lookup_mono_with_phi] >>
  `IS_SOME (lookup_var v (v' with vs_inst_idx := SUC idx))` by
    fs[lookup_var_def] >>
  first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC idx` mp_tac) >>
  (impl_tac >- simp[Abbr `idx`]) >>
  disch_then (qspecl_then [`f`, `c`,
    `v' with vs_inst_idx := SUC idx`, `st'`] mp_tac) >>
  simp[]
QED

(* ALL_DISTINCT distributes through FLAT: each member is ALL_DISTINCT *)
Triviality all_distinct_flat_mem:
  !ls l. ALL_DISTINCT (FLAT ls) /\ MEM l ls ==> ALL_DISTINCT l
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[ALL_DISTINCT_APPEND]
QED

(* Same instruction record at two positions in same block ⟹ same index.
   Uses fn_inst_ids_distinct (part of wf_function). *)
Theorem inst_ids_el_eq:
  !fn bb j idx.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
    j < LENGTH bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions /\
    EL j bb.bb_instructions = EL idx bb.bb_instructions ==>
    j = idx
Proof
  rpt strip_tac >>
  fs[fn_inst_ids_distinct_def] >>
  `MEM (MAP (\i. i.inst_id) bb.bb_instructions)
       (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[all_distinct_flat_mem] >>
  `ALL_DISTINCT bb.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* ===== CFG path / dominance helpers ===== *)

Theorem is_fn_path_rtc:
  !fn path. is_fn_path fn path /\ path <> [] ==>
    (fn_cfg_edge fn)^* (HD path) (LAST path)
Proof
  Induct_on `path` >> simp[is_fn_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[is_fn_path_def] >>
  irule (CONJUNCT2 (SPEC_ALL relationTheory.RTC_RULES)) >>
  qexists_tac `h'` >> simp[]
QED

Theorem rtc_to_fn_path:
  !fn x y. (fn_cfg_edge fn)^* x y ==>
    ?path. is_fn_path fn path /\ path <> [] /\ HD path = x /\ LAST path = y
Proof
  gen_tac >> ho_match_mp_tac relationTheory.RTC_INDUCT >> rw[]
  >- (qexists_tac `[x]` >> simp[is_fn_path_def])
  >- (qexists_tac `x::path` >> Cases_on `path` >> gvs[is_fn_path_def])
QED

Theorem is_fn_path_prefix:
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

Theorem fn_dominates_dom_reachable:
  !fn d n. fn_dominates fn d n ==> fn_reachable fn d
Proof
  rw[fn_dominates_def, fn_reachable_def] >>
  qexists_tac `entry` >> simp[] >>
  drule rtc_to_fn_path >> strip_tac >>
  `MEM d path` by (first_x_assum irule >> simp[] >> metis_tac[]) >>
  drule_all is_fn_path_prefix >> strip_tac >>
  drule is_fn_path_rtc >>
  simp[listTheory.APPEND_eq_NIL]
QED

Theorem is_fn_path_snoc:
  !fn path lbl. is_fn_path fn path /\ path <> [] /\
    fn_cfg_edge fn (LAST path) lbl ==>
    is_fn_path fn (path ++ [lbl])
Proof
  Induct_on `path` >> simp[is_fn_path_def] >>
  rpt strip_tac >> Cases_on `path` >> gvs[is_fn_path_def]
QED

Theorem fn_dominates_predecessor:
  !fn d n p.
    fn_dominates fn d n /\ d <> n /\
    fn_cfg_edge fn p n /\ fn_reachable fn p ==>
    fn_dominates fn d p
Proof
  rw[fn_dominates_def] >> rpt strip_tac >>
  `is_fn_path fn (path ++ [n])` by (
    irule is_fn_path_snoc >> simp[]) >>
  `MEM d (path ++ [n])` by (
    first_x_assum (qspec_then `path ++ [n]` mp_tac) >>
    impl_tac >- (
      simp[listTheory.LAST_APPEND_CONS] >>
      Cases_on `path` >> gvs[]) >>
    simp[]) >>
  gvs[listTheory.MEM_APPEND]
QED

(* ===== General wf_function helpers ===== *)

Theorem same_label_same_block:
  !f bb1 bb2.
    wf_function f /\ MEM bb1 f.fn_blocks /\ MEM bb2 f.fn_blocks /\
    bb1.bb_label = bb2.bb_label ==>
    bb1 = bb2
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) f.fn_blocks)` by
    fs[wf_function_def, fn_labels_def] >>
  `lookup_block bb1.bb_label f.fn_blocks = SOME bb1` by
    (irule MEM_lookup_block >> simp[]) >>
  `lookup_block bb1.bb_label f.fn_blocks = SOME bb2` by
    (irule MEM_lookup_block >> gvs[]) >>
  gvs[]
QED

Theorem wf_function_bb_well_formed:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==> bb_well_formed bb
Proof simp[wf_function_def] >> metis_tac[]
QED

Theorem fn_inst_wf_every_bb:
  !fn bb. fn_inst_wf fn /\ MEM bb fn.fn_blocks ==>
    EVERY inst_wf bb.bb_instructions
Proof simp[fn_inst_wf_def] >> metis_tac[EVERY_MEM]
QED

Theorem phi_before_non_phi:
  !bb i idx.
    bb_well_formed bb /\
    i < LENGTH bb.bb_instructions /\
    idx < LENGTH bb.bb_instructions /\
    (EL i bb.bb_instructions).inst_opcode = PHI /\
    (EL idx bb.bb_instructions).inst_opcode <> PHI ==>
    i < idx
Proof
  rpt strip_tac >>
  CCONTR_TAC >> fs[arithmeticTheory.NOT_LESS] >>
  `idx = i \/ idx < i` by DECIDE_TAC
  >- gvs[]
  >- (fs[bb_well_formed_def] >> metis_tac[])
QED

(* ===== FDOM monotonicity helpers ===== *)

Theorem lookup_var_fdom:
  !x s s'.
    lookup_var x s' = lookup_var x s /\ x IN FDOM s.vs_vars ==>
    x IN FDOM s'.vs_vars
Proof
  rw[lookup_var_def] >>
  `FLOOKUP s.vs_vars x <> NONE` by metis_tac[flookup_thm] >>
  Cases_on `FLOOKUP s.vs_vars x` >> gvs[flookup_thm]
QED

Theorem fn_reachable_step:
  !f lbl lbl'.
    fn_reachable f lbl /\ fn_cfg_edge f lbl lbl' ==>
    fn_reachable f lbl'
Proof
  rpt strip_tac >>
  qpat_x_assum `fn_reachable _ _`
    (strip_assume_tac o REWRITE_RULE[fn_reachable_def]) >>
  simp[fn_reachable_def] >>
  metis_tac[relationTheory.RTC_CASES2]
QED

(* ===== Layer 2: Block chaining in run_blocks ===== *)

Theorem run_blocks_step_proof:
  ∀ fuel ctx fn bb ss ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    run_block fuel ctx bb ss = OK ss' ∧
    ¬ss'.vs_halted
    ⇒
    run_blocks (SUC fuel) ctx fn ss = run_blocks fuel ctx fn ss'
Proof
  rw[run_blocks_unfold]
QED

Theorem run_blocks_two_blocks_proof:
  ∀ fuel ctx fn bb_A ss ss_mid result.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb_A ∧
    run_block fuel ctx bb_A ss = OK ss_mid ∧
    ¬ss_mid.vs_halted ∧
    run_blocks fuel ctx fn ss_mid = result
    ⇒
    run_blocks (SUC fuel) ctx fn ss = result
Proof
  rw[run_blocks_unfold]
QED

Theorem run_blocks_halt_proof:
  ∀ fuel ctx fn bb ss ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    run_block fuel ctx bb ss = OK ss' ∧
    ss'.vs_halted
    ⇒
    run_blocks (SUC fuel) ctx fn ss = Halt ss'
Proof
  rw[run_blocks_unfold]
QED

Theorem run_blocks_abort_proof:
  ∀ fuel ctx fn bb ss a ss'.
    lookup_block ss.vs_current_bb fn.fn_blocks = SOME bb ∧
    run_block fuel ctx bb ss = Abort a ss'
    ⇒
    run_blocks (SUC fuel) ctx fn ss = Abort a ss'
Proof
  rw[run_blocks_unfold]
QED

Theorem eval_phis_preserves_alloca_fields:
  !s insts s'. eval_phis s insts = OK s' ==> s'.vs_allocas = s.vs_allocas /\ s'.vs_alloca_next = s.vs_alloca_next
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> fs[eval_phis_def])
  >> rpt strip_tac >> fs[eval_phis_def]
  >> Cases_on `h.inst_opcode = PHI` >> fs[] >> rfs[]
  >> Cases_on `eval_one_phi s h` >> fs[]
  >> PairCases_on `x` >> fs[]
  >> Cases_on `eval_phis s insts` >> fs[]
  >> `v.vs_allocas = s.vs_allocas ∧ v.vs_alloca_next = s.vs_alloca_next`
     by (qsuff_tac `∀s''. eval_phis s insts = OK s'' ⇒ s''.vs_allocas = s.vs_allocas ∧ s''.vs_alloca_next = s.vs_alloca_next`
         >- metis_tac[] >> metis_tac[])
  >> fs[update_var_def]
  >> `s' = v with vs_vars := v.vs_vars⟨x0 ↦ x1⟩` by metis_tac[]
  >> fs[]
QED

Theorem eval_phis_preserves_inst_idx:
  !s insts s'. eval_phis s insts = OK s' ==> s'.vs_inst_idx = s.vs_inst_idx
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> fs[eval_phis_def])
  >> rpt strip_tac >> fs[eval_phis_def]
  >> Cases_on `h.inst_opcode = PHI` >> fs[] >> rfs[]
  >> Cases_on `eval_one_phi s h` >> fs[]
  >> PairCases_on `x` >> fs[]
  >> Cases_on `eval_phis s insts` >> fs[]
  >> `v.vs_inst_idx = s.vs_inst_idx` by metis_tac[]
  >> metis_tac[update_var_inst_idx]
QED

Theorem eval_phis_preserves_current_bb:
  !s insts s'. eval_phis s insts = OK s' ==> s'.vs_current_bb = s.vs_current_bb
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> fs[eval_phis_def])
  >> rpt strip_tac >> fs[eval_phis_def]
  >> Cases_on `h.inst_opcode = PHI` >> fs[] >> rfs[]
  >> Cases_on `eval_one_phi s h` >> fs[]
  >> PairCases_on `x` >> fs[]
  >> Cases_on `eval_phis s insts` >> fs[]
  >> `v.vs_current_bb = s.vs_current_bb`
     by (qsuff_tac `∀s''. eval_phis s insts = OK s'' ⇒ s''.vs_current_bb = s.vs_current_bb`
         >- metis_tac[] >> metis_tac[])
  >> fs[update_var_def]
  >> `s' = v with vs_vars := v.vs_vars⟨x0 ↦ x1⟩` by metis_tac[]
  >> fs[]
QED

Theorem eval_phis_preserves_halted:
  !s insts s'. eval_phis s insts = OK s' ==> s'.vs_halted = s.vs_halted
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> fs[eval_phis_def])
  >> rpt strip_tac >> fs[eval_phis_def]
  >> Cases_on `h.inst_opcode = PHI` >> fs[] >> rfs[]
  >> Cases_on `eval_one_phi s h` >> fs[]
  >> PairCases_on `x` >> fs[]
  >> Cases_on `eval_phis s insts` >> fs[]
  >> `v.vs_halted = s.vs_halted`
     by (qsuff_tac `∀s''. eval_phis s insts = OK s'' ⇒ s''.vs_halted = s.vs_halted`
         >- metis_tac[] >> metis_tac[])
  >> fs[update_var_def]
  >> `s' = v with vs_vars := v.vs_vars⟨x0 ↦ x1⟩` by metis_tac[]
  >> fs[]
QED

(* ==========================================================================
   eval_phis State Equivalence
   ========================================================================== *)

Triviality resolve_phi_MEM_el[local]:
  !prev ops op. resolve_phi prev ops = SOME op ==> MEM op ops
Proof
  recInduct resolve_phi_ind >>
  simp[resolve_phi_def] >>
  rpt gen_tac >> strip_tac >>
  IF_CASES_TAC >> gvs[]
QED

Triviality eval_operand_equiv_not_in_vars[local]:
  !op s1 s2 vars v.
    execution_equiv vars s1 s2 /\
    eval_operand op s1 = SOME v /\
    (!x. op = Var x ==> x NOTIN vars)
    ==> eval_operand op s2 = SOME v
Proof
  Cases_on `op` >> simp[eval_operand_def] >>
  fs[execution_equiv_def] >>
  metis_tac[]
QED

Triviality update_var_execution_equiv[local]:
  !vars x v s1 s2.
    execution_equiv vars s1 s2 ==>
    execution_equiv vars (update_var x v s1) (update_var x v s2)
Proof
  rw[execution_equiv_def, update_var_def] >>
  rw[lookup_var_def, FLOOKUP_UPDATE] >>
  fs[lookup_var_def]
QED

Triviality update_var_state_equiv[local]:
  !vars x v s1 s2.
    state_equiv vars s1 s2 ==>
    state_equiv vars (update_var x v s1) (update_var x v s2)
Proof
  rw[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED


Triviality eval_one_phi_equiv[local]:
  !s1 s2 vars inst out v.
    execution_equiv vars s1 s2 /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    eval_one_phi s1 inst = SOME (out, v) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars)
    ==> eval_one_phi s2 inst = SOME (out, v)
Proof
  rpt strip_tac >>
  fs[eval_one_phi_def, AllCaseEqs()] >>
  `MEM val_op inst.inst_operands` by metis_tac[resolve_phi_MEM_el] >>
  `!x. val_op = Var x ==> x NOTIN vars` by metis_tac[] >>
  `eval_operand val_op s2 = SOME v` by metis_tac[eval_operand_equiv_not_in_vars] >>
  fs[] >> qexists_tac `prev` >> simp[]
QED

Theorem eval_phis_state_equiv:
  !s1 s2 vars insts s1'.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode = PHI ==>
              !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) insts /\
    eval_phis s1 insts = OK s1'
    ==> ?s2'. eval_phis s2 insts = OK s2' /\ state_equiv vars s1' s2'
Proof
  Induct_on `insts` >>
  rpt strip_tac >> fs[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> rfs[] >>
  Cases_on `eval_one_phi s1 h` >> gvs[] >>
  PairCases_on `x` >> gvs[]
  >> Cases_on `eval_phis s1 insts` >> gvs[]
  >> `execution_equiv vars s1 s2 ∧ s1.vs_prev_bb = s2.vs_prev_bb`
     by fs[state_equiv_def]
  >> `eval_one_phi s2 h = SOME (x0,x1)`
     by metis_tac[eval_one_phi_equiv]
  >> `∃s2'. eval_phis s2 insts = OK s2' ∧ state_equiv vars v s2'`
     by (qsuff_tac `∀s''. eval_phis s1 insts = OK s'' ⇒ ∃s2'. eval_phis s2 insts = OK s2' ∧ state_equiv vars s'' s2'`
         >- metis_tac[] >> metis_tac[])
  >> qexists `update_var x0 x1 s2'` >> simp[eval_phis_def] >>
  metis_tac[update_var_state_equiv]
QED

Theorem phi_prefix_length_le:
  !insts. phi_prefix_length insts <= LENGTH insts
Proof
  Induct
  >- simp[phi_prefix_length_def] >>
  simp[phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >> decide_tac
QED

Theorem no_phis_phi_prefix_length_zero:
  !l. EVERY (\inst. inst.inst_opcode <> PHI) l ==> phi_prefix_length l = 0
Proof
  Induct >> simp[phi_prefix_length_def]
QED

Theorem eval_phis_no_phis:
  !s l. EVERY (\inst. inst.inst_opcode <> PHI) l ==> eval_phis s l = OK s
Proof
  gen_tac >> Induct_on `l` >> simp[eval_phis_def]
QED

Theorem run_block_no_phis_eq_exec_block:
  !fuel ctx bb s.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions ==>
    run_block fuel ctx bb s = exec_block fuel ctx bb (s with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  simp[eval_phis_no_phis, no_phis_phi_prefix_length_zero]
QED

Theorem run_block_eq_from_exec_block_eq:
  !fuel ctx bb1 bb2 s.
    phi_prefix_length bb1.bb_instructions = phi_prefix_length bb2.bb_instructions /\
    (!s. eval_phis s bb1.bb_instructions = eval_phis s bb2.bb_instructions) /\
    (!s. exec_block fuel ctx bb1 s = exec_block fuel ctx bb2 s) ==>
    run_block fuel ctx bb1 s = run_block fuel ctx bb2 s
Proof
  rpt strip_tac >>
  simp[run_block_def]
QED

Theorem run_blocks_eq_from_run_block_eq:
  !fuel ctx fn1 fn2 s.
    fn1.fn_blocks = fn2.fn_blocks /\
    (!bb. MEM bb fn1.fn_blocks ==>
      !fuel ctx s. run_block fuel ctx bb s = run_block fuel ctx bb s) ==>
    run_blocks fuel ctx fn1 s = run_blocks fuel ctx fn2 s
Proof
  rw[] >> qid_spec_tac `s` >>
  Induct_on `fuel` >-
  (gen_tac >> simp[run_blocks_def]) >>
  gen_tac >> gvs[run_blocks_unfold]
QED


Theorem eval_phis_map_congruent:
  !s insts f.
    (!inst. MEM inst insts ==> (f inst).inst_opcode = inst.inst_opcode) /\
    (!inst. MEM inst insts /\ inst.inst_opcode = PHI ==> f inst = inst) ==>
    eval_phis s (MAP f insts) = eval_phis s insts
Proof
  Induct_on `insts` >> simp[eval_phis_def]
QED

Theorem phi_prefix_length_map_congruent:
  !insts f.
    (!inst. MEM inst insts ==> (f inst).inst_opcode = inst.inst_opcode) ==>
    phi_prefix_length (MAP f insts) = phi_prefix_length insts
Proof
  Induct >> simp[phi_prefix_length_def]
QED


(* Re-export passSimulationDefs$block_map_transform for convenience.
   The local definition was removed to avoid constant shadowing that broke
   pass proofs (two different block_map_transform constants from different
   theories with the same name but different module paths). *)
Overload block_map_transform = ``passSimulationDefs$block_map_transform``

Theorem run_block_block_map_transform:
  !fuel ctx bb f s.
    EVERY (\inst. (f inst).inst_opcode = inst.inst_opcode) bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = PHI ==> f inst = inst) bb.bb_instructions /\
    (!s. exec_block fuel ctx (block_map_transform f bb) s = exec_block fuel ctx bb s) ==>
    run_block fuel ctx (block_map_transform f bb) s = run_block fuel ctx bb s
Proof
  rpt strip_tac >>
  irule run_block_eq_from_exec_block_eq >>
  simp[passSimulationDefsTheory.block_map_transform_def] >>
  conj_tac >- (irule eval_phis_map_congruent >> fs[EVERY_MEM]) >>
  irule phi_prefix_length_map_congruent >> fs[EVERY_MEM]
QED

Triviality phi_prefix_length_phi_boundary[local]:
  !insts f.
    (!inst. MEM inst insts ==>
      (inst.inst_opcode = PHI <=> (f inst).inst_opcode = PHI)) ==>
    phi_prefix_length (MAP f insts) = phi_prefix_length insts
Proof
  Induct >> simp[phi_prefix_length_def]
QED

Triviality eval_phis_phi_preserving[local]:
  !s insts f.
    (!inst. MEM inst insts ==>
      (inst.inst_opcode = PHI <=> (f inst).inst_opcode = PHI)) /\
    (!inst. MEM inst insts ==> inst.inst_opcode = PHI ==> f inst = inst) ==>
    eval_phis s (MAP f insts) = eval_phis s insts
Proof
  Induct_on `insts` >> simp[eval_phis_def]
QED

Theorem run_block_block_map_transform_phi_preserving:
  !fuel ctx bb f s.
    EVERY (\inst. inst.inst_opcode = PHI ==> f inst = inst) bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode = PHI ==> (f inst).inst_opcode = PHI) bb.bb_instructions /\
    EVERY (\inst. inst.inst_opcode <> PHI ==> (f inst).inst_opcode <> PHI) bb.bb_instructions /\
    (!s. exec_block fuel ctx (block_map_transform f bb) s = exec_block fuel ctx bb s) ==>
    run_block fuel ctx (block_map_transform f bb) s = run_block fuel ctx bb s
Proof
  rpt strip_tac >>
  `phi_prefix_length (MAP f bb.bb_instructions) =
    phi_prefix_length bb.bb_instructions` by
    (irule phi_prefix_length_phi_boundary >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `eval_phis s (MAP f bb.bb_instructions) =
    eval_phis s bb.bb_instructions` by
    (irule eval_phis_phi_preserving >>
     fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[run_block_def, passSimulationDefsTheory.block_map_transform_def]
QED


Theorem eval_phis_same_phi_prefix:
  !s insts1 insts2.
    phi_prefix_length insts1 = phi_prefix_length insts2 /\
    (!i. i < phi_prefix_length insts1 ==> EL i insts1 = EL i insts2) ==>
    eval_phis s insts1 = eval_phis s insts2
Proof
  Induct_on `insts1` >> rpt strip_tac >> gvs[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `insts2` >> gvs[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `h'.inst_opcode = PHI` >> gvs[eval_phis_def, phi_prefix_length_def] >>
  `h = h'` by (
    first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac)
  >> fs[]
  >> `∀i. i < phi_prefix_length t ⇒ EL i insts1 = EL i t` by (
    gen_tac >> strip_tac >>
    first_x_assum (qspec_then `SUC i` mp_tac) >> simp[])
  >> first_x_assum (qspecl_then [`s`,`t`] mp_tac) >>
  simp[]
QED


(* Boundary lemmas for run_block: lift exec_block properties through eval_phis wrapper *)

Theorem run_block_OK_inst_idx_0:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  rpt strip_tac >>
  qspecl_then [`s`,`bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE[run_block_def]) >>
  gvs[] >>
  imp_res_tac exec_block_OK_inst_idx_0 >> simp[]
QED

Theorem run_block_ok_sets_prev_bb:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_prev_bb <> NONE
Proof
  rpt strip_tac >>
  qspecl_then [`s`,`bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE[run_block_def]) >>
  gvs[] >>
  imp_res_tac exec_block_ok_sets_prev_bb >> fs[]
QED

(* run_block OK gives exact prev_bb: the predecessor is the entry vs_current_bb.
   This is the run_block-level boundary lemma that consumers should use
   instead of unfolding run_block_def + exec_block_ok_prev_bb directly. *)
Theorem run_block_ok_prev_bb_exact:
  !fuel ctx bb s s1.
    EVERY inst_wf bb.bb_instructions /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    bb.bb_instructions <> [] /\
    run_block fuel ctx bb s = OK s1 ==>
    s1.vs_prev_bb = SOME s.vs_current_bb
Proof
  rpt strip_tac >>
  qspecl_then [`s`,`bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE[run_block_def]) >>
  gvs[AllCaseEqs()] >>
  (`phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
     metis_tac[phi_prefix_length_le]) >>
  qabbrev_tac `s_input = s' with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `s_input.vs_current_bb = s.vs_current_bb` by (
    simp[Abbr `s_input`] >>
    qspecl_then [`s`,`bb.bb_instructions`,`s'`] mp_tac eval_phis_preserves_current_bb >>
    simp[]) >>
  `s1.vs_prev_bb = SOME s_input.vs_current_bb` by (
    qspecl_then [`fuel`,`ctx`,`bb`,`s_input`,`s1`] mp_tac
      exec_block_ok_prev_bb_general >>
    simp[Abbr `s_input`] >>
    decide_tac) >>
  fs[Abbr `s_input`]
QED

(* eval_one_phi returns an output that is a member of inst.inst_outputs *)
Theorem eval_one_phi_output_mem:
  !s inst out v. eval_one_phi s inst = SOME (out,v) ==> MEM out inst.inst_outputs
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[eval_one_phi_def] >>
  Cases_on `t` >> gvs[eval_one_phi_def] >>
  Cases_on `s.vs_prev_bb` >> gvs[eval_one_phi_def] >>
  gvs[AllCaseEqs()]
QED

(* Boundary lemma: eval_phis only modifies vs_vars.
   ALL other venom_state fields are preserved.
   This subsumes eval_phis_preserves_alloca_fields, eval_phis_preserves_inst_idx,
   eval_phis_preserves_current_bb, and makes pass-level preservation proofs trivial. *)

Triviality eval_phis_only_updates_vs_vars_ind[local]:
  !insts st s'. eval_phis st insts = OK s' ==> s' = st with vs_vars := s'.vs_vars
Proof
  gen_tac >> Induct_on `insts`
  >> rw[eval_phis_def, update_var_def, eval_one_phi_def, AllCaseEqs()]
  >> TRY (fs[venom_state_component_equality])
  >> rpt strip_tac
  >> first_x_assum drule >> rw[venom_state_component_equality]
QED

Theorem eval_phis_only_updates_vs_vars:
  !st insts s'. eval_phis st insts = OK s' ==> s' = st with vs_vars := s'.vs_vars
Proof
  metis_tac[eval_phis_only_updates_vs_vars_ind]
QED

(* eval_phis preserves lookup for variables that are not PHI outputs
   of any instruction in the list. *)
Theorem eval_phis_flookup_not_phi_output:
  !s insts x s'.
    eval_phis s insts = OK s' /\
    (!inst. MEM inst insts ==> inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs) ==>
    FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct_on `insts`
  >- (rpt strip_tac >> fs[eval_phis_def])
  >> rpt strip_tac >> fs[eval_phis_def]
  >> Cases_on `h.inst_opcode = PHI` >> fs[] >> rfs[]
  >> Cases_on `eval_one_phi s h` >> fs[]
  >> PairCases_on `x'` >> fs[]
  >> Cases_on `eval_phis s insts` >> fs[update_var_def, FLOOKUP_UPDATE]
  >> `FLOOKUP v.vs_vars x = FLOOKUP s.vs_vars x`
     by (qsuff_tac `∀s''. eval_phis s insts = OK s'' ⇒
           FLOOKUP s''.vs_vars x = FLOOKUP s.vs_vars x`
         >- metis_tac[] >> metis_tac[])
  >> `x'0 ≠ x` by (
       CCONTR_TAC >> fs[] >>
       first_x_assum (qspec_then `h` mp_tac) >> simp[] >>
       metis_tac[eval_one_phi_output_mem])
  >> `s' = v with vs_vars := v.vs_vars⟨x'0 ↦ x'1⟩` by metis_tac[eval_phis_only_updates_vs_vars]
  >> fs[FLOOKUP_UPDATE]
QED

(* eval_phis preserves FDOM for variables that are not PHI outputs *)
Theorem eval_phis_fdom_not_phi_output:
  !s insts x s'.
    eval_phis s insts = OK s' /\
    x IN FDOM s.vs_vars /\
    (!inst. MEM inst insts ==> inst.inst_opcode = PHI ==> ~MEM x inst.inst_outputs) ==>
    x IN FDOM s'.vs_vars
Proof
  rpt strip_tac >>
  imp_res_tac eval_phis_flookup_not_phi_output >>
  fs[TO_FLOOKUP]
QED

Theorem run_block_OK_not_halted:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> ~v.vs_halted
Proof
  rpt strip_tac >>
  qspecl_then [`s`,`bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  RULE_ASSUM_TAC (ONCE_REWRITE_RULE[run_block_def]) >>
  gvs[] >>
  imp_res_tac exec_block_OK_not_halted >> fs[]
QED

(* Boundary lemma: lift_result for run_block from exec_block-level simulation.
   KEY INSIGHT: run_block feeds exec_block from s_phi (result of eval_phis), NOT from s.
   So the hypothesis must quantify over s_phi, or be about exec_block from that state.
   The hypothesis uses "s_phi with vs_inst_idx := phi_prefix_length" which by
   exec_block_skip_phis equals "s_phi with vs_inst_idx := 0". *)
Theorem run_block_lift_result:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term1 : venom_state -> venom_state -> bool)
   (R_term2 : venom_state -> venom_state -> bool)
   fuel ctx bb1 bb2 s.
    phi_prefix_length bb1.bb_instructions = phi_prefix_length bb2.bb_instructions /\
    eval_phis s bb1.bb_instructions = eval_phis s bb2.bb_instructions /\
    (!s_phi.
       eval_phis s bb1.bb_instructions = OK s_phi ==>
       (?e. exec_block fuel ctx bb1
              (s_phi with vs_inst_idx := phi_prefix_length bb1.bb_instructions) = Error e) \/
       lift_result R_ok R_term1 R_term2
         (exec_block fuel ctx bb1
            (s_phi with vs_inst_idx := phi_prefix_length bb1.bb_instructions))
         (exec_block fuel ctx bb2
            (s_phi with vs_inst_idx := phi_prefix_length bb2.bb_instructions))) ==>
    (?e. run_block fuel ctx bb1 s = Error e) \/
    lift_result R_ok R_term1 R_term2
      (run_block fuel ctx bb1 s)
      (run_block fuel ctx bb2 s)
Proof
  rpt gen_tac >> strip_tac >>
  DISJ_CASES_TAC (Q.SPECL [`s`,`bb1.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >>
      `eval_phis s bb2.bb_instructions = OK s_phi` by metis_tac[] >>
      ONCE_REWRITE_TAC[run_block_def] >>
      qpat_x_assum `phi_prefix_length bb1.bb_instructions = phi_prefix_length bb2.bb_instructions` kall_tac >>
      simp[])
  >- (first_x_assum (qx_choose_then `e` strip_assume_tac) >>
      disj1_tac >>
      ONCE_REWRITE_TAC[run_block_def] >> simp[] >>
      qexists_tac `e` >> simp[])
QED

(* eval_phis only grows FDOM vs_vars (monotone) *)
Theorem eval_phis_vars_grow:
  !s insts s'.
    eval_phis s insts = OK s' ==> FDOM s.vs_vars SUBSET FDOM s'.vs_vars
Proof
  Induct_on `insts`
  >- (* base case: eval_phis s [] = OK s, so s' = s *)
     (rpt gen_tac >> ONCE_REWRITE_TAC[eval_phis_def] >> simp[]) >>
  rpt gen_tac >>
  ONCE_REWRITE_TAC[eval_phis_def] >>
  reverse (Cases_on `h.inst_opcode = PHI`)
  >- (* non-PHI: returns OK s, so s' = s, trivially SUBSET *)
     (strip_tac >> gvs[Excl "eval_phis_def", Excl "eval_one_phi_def"]) >>
  strip_tac >>
  Cases_on `eval_one_phi s h`
  >- (* NONE: Error "phi evaluation failed", contradicts OK *)
     (DISJ_CASES_TAC (Q.SPECL [`s`,`insts`] eval_phis_ok_or_error_defs) >>
      gvs[Excl "eval_phis_def", Excl "eval_one_phi_def"]) >>
  PairCases_on `x` >>
  DISJ_CASES_TAC (Q.SPECL [`s`,`insts`] eval_phis_ok_or_error_defs)
  >- (* OK s_phi: IH gives FDOM s.vs_vars ⊆ FDOM s_phi.vs_vars,
       update_var adds key to FDOM, so transitivity *)
     (first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >>
      gvs[update_var_def, finite_mapTheory.FDOM_FUPDATE,
          pred_setTheory.SUBSET_DEF, Excl "eval_phis_def",
          Excl "eval_one_phi_def"] >>
      metis_tac[])
  >- (* Error: contradicts OK *)
     (first_x_assum (qx_choose_then `e` strip_assume_tac) >>
      gvs[Excl "eval_phis_def", Excl "eval_one_phi_def"])
QED

(* eval_one_phi returning SOME implies single output matching *)
Theorem eval_one_phi_imp_inst_outputs:
  !s inst out v.
    eval_one_phi s inst = SOME (out, v) ==> inst.inst_outputs = [out]
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs` >> gvs[eval_one_phi_def] >>
  Cases_on `t` >> gvs[eval_one_phi_def] >>
  Cases_on `s.vs_prev_bb` >> gvs[eval_one_phi_def] >>
  Cases_on `resolve_phi x inst.inst_operands` >> gvs[] >>
  Cases_on `eval_operand x' s` >> gvs[]
QED

(* PHI output vars from prefix are in FDOM after eval_phis (MEM-based version) *)
Theorem eval_phis_outputs_in_fdom_mem:
  !s insts s' inst out.
    eval_phis s insts = OK s' /\
    MEM inst (TAKE (phi_prefix_length insts) insts) /\
    MEM out inst.inst_outputs ==>
    out IN FDOM s'.vs_vars
Proof
  Induct_on `insts` >> rpt gen_tac >- (
    strip_tac >> fs[phi_prefix_length_def, eval_phis_def]
  ) >> strip_tac >>
  ONCE_REWRITE_TAC[eval_phis_def] >>
  reverse (Cases_on `h.inst_opcode = PHI`)
  >- suspend "non_phi_case"
  >>
  Cases_on `eval_one_phi s h`
  >- suspend "eval_none_case"
  >>
  PairCases_on `x` >>
  DISJ_CASES_TAC (Q.SPECL [`s`,`insts`] eval_phis_ok_or_error_defs)
  >- suspend "ok_case"
  >- suspend "error_case"
QED

Resume eval_phis_outputs_in_fdom_mem[non_phi_case]:
  fs[phi_prefix_length_def] >>
  Cases_on `inst = h` >> fs[]
QED

Resume eval_phis_outputs_in_fdom_mem[eval_none_case]:
  fs[eval_phis_def] >> Cases_on `eval_phis s insts` >> fs[]
QED

Resume eval_phis_outputs_in_fdom_mem[error_case]:
  first_x_assum (qx_choose_then `e` strip_assume_tac) >>
  fs[eval_phis_def] >>
  Cases_on `eval_phis s insts` >> fs[]
QED

Resume eval_phis_outputs_in_fdom_mem[ok_case]:
  first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >>
  fs[eval_phis_def, update_var_def] >>
  qpat_x_assum `s_phi with vs_vars := _ = s'` (assume_tac o SYM) >>
  Cases_on `inst = h`
  >- (* inst = h: output var is x0 *)
     (`h.inst_outputs = [x0]` by metis_tac[eval_one_phi_imp_inst_outputs] >>
      fs[finite_mapTheory.FDOM_FUPDATE,
          pred_setTheory.IN_INSERT])
  >- (* inst ≠ h: use IH for rest of prefix *)
     (fs[phi_prefix_length_def] >>
      `TAKE (SUC (phi_prefix_length insts)) (h::insts) =
        h :: TAKE (phi_prefix_length insts) insts` by simp[] >>
      fs[] >>
      `out IN FDOM s_phi.vs_vars` by (
        last_x_assum (qspecl_then [`s`, `s_phi`, `inst`, `out`] mp_tac) >>
        simp[]
      ) >>
      fs[pred_setTheory.IN_INSERT,
          finite_mapTheory.FDOM_FUPDATE])
QED

Finalise eval_phis_outputs_in_fdom_mem

(* Derived: indexed version using EL *)
Theorem eval_phis_outputs_in_fdom_idx:
  !s insts s' i out.
    eval_phis s insts = OK s' /\ i < phi_prefix_length insts /\
    MEM out (EL i insts).inst_outputs ==>
    out IN FDOM s'.vs_vars
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `insts`, `s'`, `EL i insts`, `out`] mp_tac
    eval_phis_outputs_in_fdom_mem >>
  impl_tac >- (
    simp[listTheory.MEM_EL] >>
    qexists_tac `i` >>
    simp[rich_listTheory.EL_TAKE] >>
    simp[listTheory.LENGTH_TAKE_EQ, phi_prefix_length_le]
  ) >>
  simp[]
QED

(* When eval_phis succeeds, run_block_entry = exec_block from phi_prefix_length *)
Theorem run_block_entry_eval_phis_OK:
  !fuel ctx bb s s_phi.
    eval_phis s bb.bb_instructions = OK s_phi ==>
    run_block_entry fuel ctx bb s =
      exec_block fuel ctx bb (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[run_block_def] >> simp[]
QED

(* When eval_phis fails, run_block_entry = Error *)
Theorem run_block_entry_eval_phis_Error:
  !fuel ctx bb s e.
    eval_phis s bb.bb_instructions = Error e ==>
    run_block_entry fuel ctx bb s = Error e
Proof
  rpt strip_tac >> ONCE_REWRITE_TAC[run_block_def] >> simp[]
QED

(* Decompose run_block OK result into eval_phis + exec_block *)
Theorem run_block_OK_decompose:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v ==>
    ?s_phi.
      eval_phis s bb.bb_instructions = OK s_phi /\
      exec_block fuel ctx bb (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK v
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_TAC (Q.SPECL [`s`,`bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >> simp[])
  >- (first_x_assum (qx_choose_then `e` strip_assume_tac) >> simp[])
QED

(* Decompose run_block Error: comes from eval_phis or exec_block *)
Theorem run_block_Error_decompose:
  !fuel ctx bb s e.
    run_block fuel ctx bb s = Error e ==>
    (eval_phis s bb.bb_instructions = Error e) \/
    (?s_phi.
      eval_phis s bb.bb_instructions = OK s_phi /\
      exec_block fuel ctx bb (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Error e)
Proof
  rpt strip_tac >>
  pop_assum mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_TAC (Q.SPECL [`s`,`bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >>
      simp[] >> disj2_tac >> qexists_tac `s_phi` >> simp[])
  >- (first_x_assum (qx_choose_then `e'` strip_assume_tac) >>
      simp[] >> disj1_tac >> metis_tac[])
QED
