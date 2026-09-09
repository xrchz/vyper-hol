(*
 * Block Simulation Helpers
 *
 * Core lemmas for gen_block_simulation:
 *   - run_block_step: peeling one instruction from run_block
 *   - run_block_terminator: terminator classification
 *   - label_op_sim: SOLabel preserves venom_asm_rel
 *   - foldl_inst_sim: FOLDL composition of gen_inst_simulation
 *
 * These compose per-instruction simulation (gen_inst_simulation)
 * into block-level simulation (gen_block_simulation).
 *)


Theory blockSimHelpers
Ancestors
  asmSem planExec stackModel codegenRel stackPlanTypes stackPlanGen venomExecSemantics venomExecProofs venomState venomInst list rich_list arithmetic indexedLists stackOpSim instSimHelpers venomWf
Libs
  BasicProvers

(* ===== run_block peeling ===== *)

(* Peel one non-terminator instruction from exec_block.
   If the current instruction executes successfully and isn't a terminator,
   exec_block continues with the next instruction index. *)
Theorem exec_block_step:
  !fuel ctx bb vs inst vs'.
    get_instruction bb vs.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst vs = OK vs' /\
    ~is_terminator inst.inst_opcode ==>
    exec_block fuel ctx bb vs =
    exec_block fuel ctx bb (vs' with vs_inst_idx := SUC vs.vs_inst_idx)
Proof
  rpt strip_tac >>
  simp[Once exec_block_def] >> fs[]
QED

(* Corollary: run_block = exec_block stepping one instruction
   Requires no PHIs in the block (codegen blocks don't have PHIs) *)
Theorem run_block_step:
  !fuel ctx bb vs inst vs'.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    get_instruction bb 0 = SOME inst /\
    step_inst fuel ctx inst (vs with vs_inst_idx := 0) = OK vs' /\
    ~is_terminator inst.inst_opcode ==>
    run_block fuel ctx bb vs =
    exec_block fuel ctx bb (vs' with vs_inst_idx := 1)
Proof
  rpt strip_tac >>
  simp[run_block_no_phis_eq_exec_block, Excl "exec_block_def"] >>
  MP_TAC (Q.SPECL [`fuel`, `ctx`, `bb`,
    `vs with vs_inst_idx := 0`, `inst`, `vs'`] exec_block_step) >>
  impl_tac >- simp[Excl "exec_block_def"] >>
  simp[Excl "exec_block_def"]
QED

(* When exec_block hits a terminator, classify the result *)
Theorem exec_block_terminator:
  !fuel ctx bb vs inst r.
    get_instruction bb vs.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst vs = OK r /\
    is_terminator inst.inst_opcode ==>
    exec_block fuel ctx bb vs =
    (if r.vs_halted then Halt r else OK r)
Proof
  rpt strip_tac >>
  simp[Once exec_block_def] >> fs[]
QED

(* When run_block hits a terminator, classify the result (no-PHI variant) *)
Theorem run_block_terminator:
  !fuel ctx bb vs inst r.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    get_instruction bb 0 = SOME inst /\
    step_inst fuel ctx inst (vs with vs_inst_idx := 0) = OK r /\
    is_terminator inst.inst_opcode ==>
    run_block fuel ctx bb vs =
    (if r.vs_halted then Halt r else OK r)
Proof
  rpt strip_tac >>
  simp[run_block_no_phis_eq_exec_block, Excl "exec_block_def"] >>
  irule exec_block_terminator >> simp[Excl "exec_block_def"]
QED
(* When step_inst returns non-OK, exec_block propagates *)
Theorem exec_block_propagate:
  !fuel ctx bb vs inst.
    get_instruction bb vs.vs_inst_idx = SOME inst ==>
    ((!vs'. step_inst fuel ctx inst vs = Halt vs' ==>
        exec_block fuel ctx bb vs = Halt vs') /\
     (!a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
        exec_block fuel ctx bb vs = Abort a vs') /\
     (!vals vs'. step_inst fuel ctx inst vs = IntRet vals vs' ==>
        exec_block fuel ctx bb vs = IntRet vals vs') /\
     (!e. step_inst fuel ctx inst vs = Error e ==>
        exec_block fuel ctx bb vs = Error e))
Proof
  rpt strip_tac >> simp[Once exec_block_def] >> fs[] >>
  Cases_on `step_inst fuel ctx inst vs` >> fs[]
QED

(* When step_inst returns non-OK in run_block, the result propagates (no-PHI variant) *)
Theorem run_block_propagate:
  !fuel ctx bb vs inst.
    EVERY (\inst. inst.inst_opcode <> PHI) bb.bb_instructions /\
    get_instruction bb 0 = SOME inst ==>
    ((!vs'. step_inst fuel ctx inst (vs with vs_inst_idx := 0) = Halt vs' ==>
        run_block fuel ctx bb vs = Halt vs') /\
     (!a vs'. step_inst fuel ctx inst (vs with vs_inst_idx := 0) = Abort a vs' ==>
        run_block fuel ctx bb vs = Abort a vs') /\
     (!vals vs'. step_inst fuel ctx inst (vs with vs_inst_idx := 0) = IntRet vals vs' ==>
        run_block fuel ctx bb vs = IntRet vals vs') /\
     (!e. step_inst fuel ctx inst (vs with vs_inst_idx := 0) = Error e ==>
        run_block fuel ctx bb vs = Error e))
Proof
  rpt strip_tac >>
  simp[run_block_no_phis_eq_exec_block, Excl "exec_block_def"] >>
  MP_TAC (Q.SPECL [`fuel`, `ctx`, `bb`, `vs with vs_inst_idx := 0`, `inst`]
    exec_block_propagate) >>
  simp[Excl "exec_block_def"]
QED

(* ===== venom_asm_rel stability under PC changes ===== *)

(* venom_asm_rel doesn't constrain as_pc, so updating it is free *)
Theorem venom_asm_rel_pc_update:
  !lo ps vs as pc'.
    venom_asm_rel lo ps vs as ==>
    venom_asm_rel lo ps vs (as with as_pc := pc')
Proof
  rw[venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def,
     memory_rel_def]
QED

(* operand_val is independent of vs_inst_idx *)
Theorem operand_val_inst_idx[simp]:
  !vs lo op idx.
    operand_val (vs with vs_inst_idx := idx) lo op = operand_val vs lo op
Proof
  rpt gen_tac >> Cases_on `op` >> simp[operand_val_def]
QED

(* venom_asm_rel doesn't constrain vs_inst_idx *)
Theorem venom_asm_rel_inst_idx_update:
  !lo ps vs as idx.
    venom_asm_rel lo ps vs as ==>
    venom_asm_rel lo ps (vs with vs_inst_idx := idx) as
Proof
  rw[venom_asm_rel_def, plan_stack_rel_def, plan_spill_rel_def,
     memory_rel_def]
QED

(* venom_asm_terminal_rel doesn't constrain as_pc, so updating it is free *)
Theorem venom_asm_terminal_rel_pc_update:
  !vs as pc'.
    venom_asm_terminal_rel vs as ==>
    venom_asm_terminal_rel vs (as with as_pc := pc')
Proof
  rw[venom_asm_terminal_rel_def]
QED

(* ===== Label op simulation ===== *)

(* AsmLabel advances PC by 1, preserves everything else *)
Theorem asm_step_label:
  !lo o2pc lbl as.
    asm_step lo o2pc (AsmLabel lbl) as = AsmOK (asm_next as)
Proof
  simp[asm_step_def]
QED

(* asm_steps 1 for a label instruction advances PC by 1 *)
Theorem label_op_asm_steps:
  !lo o2pc prog as lbl.
    asm_block_at prog as.as_pc [AsmLabel lbl] ==>
    asm_steps lo o2pc prog 1 as =
    AsmOK (as with as_pc := as.as_pc + 1)
Proof
  rw[asm_block_at_def] >>
  `1 = SUC 0` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[asm_steps_def, asm_step_def, asm_next_def] >>
  fs[]
QED

(* SOLabel simulation: executing the label plan step preserves
   venom_asm_rel and advances asm PC *)
Theorem label_op_sim:
  !lo o2pc prog ps vs as lbl.
    venom_asm_rel lo ps vs as /\
    asm_block_at prog as.as_pc [AsmLabel lbl] ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo ps vs as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt strip_tac >>
  drule label_op_asm_steps >> strip_tac >>
  qexists_tac `as with as_pc := as.as_pc + 1` >>
  ASM_REWRITE_TAC[] >>
  conj_tac >- (irule venom_asm_rel_pc_update >> fs[]) >>
  SIMP_TAC (srw_ss()) []
QED

(* ===== FOLDL plan accumulation properties ===== *)

(* The FOLDL in generate_block_plan accumulates ops by appending.
   If it succeeds, every prefix also succeeds. *)

(* Helper: the FOLDL used in generate_block_plan *)
Definition block_foldl_def:
  block_foldl gen_plan acc [] = acc /\
  block_foldl gen_plan acc ((i, inst) :: rest) =
    case acc of
      NONE => NONE
    | SOME (ops, ps) =>
        case gen_plan i inst ps of
          NONE => NONE
        | SOME (step_ops, ps') =>
            block_foldl gen_plan (SOME (ops ++ step_ops, ps')) rest
End

(* SNOC decomposition: if block_foldl succeeds on xs ++ [(i,inst)],
   then it succeeds on xs and the last step works *)
Theorem block_foldl_snoc:
  !gen_plan xs i inst acc ops_final ps_final.
    block_foldl gen_plan acc (xs ++ [(i, inst)]) =
      SOME (ops_final, ps_final) ==>
    ?ops_mid ps_mid step_ops.
      block_foldl gen_plan acc xs = SOME (ops_mid, ps_mid) /\
      gen_plan i inst ps_mid = SOME (step_ops, ps_final) /\
      ops_final = ops_mid ++ step_ops
Proof
  Induct_on `xs`
  >- (rw[block_foldl_def] >> every_case_tac >> fs[]) >>
  rw[] >> PairCases_on `h` >>
  fs[block_foldl_def] >> every_case_tac >> fs[]
QED

(* CONS decomposition: peel off the first element *)
Theorem block_foldl_cons:
  !gen_plan i inst rest ops0 ps0.
    block_foldl gen_plan (SOME (ops0, ps0)) ((i, inst) :: rest) =
    case gen_plan i inst ps0 of
      NONE => NONE
    | SOME (step_ops, ps') =>
        block_foldl gen_plan (SOME (ops0 ++ step_ops, ps')) rest
Proof
  simp[block_foldl_def]
QED

(* ===== MAPi/DROP interaction ===== *)

(* DROP k (MAPi f l) = MAPi (λi x. f (i + k) x) (DROP k l) *)
Theorem drop_mapi:
  !l k f. k <= LENGTH l ==>
    DROP k (MAPi f l) = MAPi (\i x. f (i + k) x) (DROP k l)
Proof
  Induct >> simp[] >>
  rpt strip_tac >> Cases_on `k` >> fs[MAPi_def] >>
  irule MAPi_CONG >> simp[combinTheory.o_DEF, ADD_CLAUSES]
QED

(* Specialization: MAPi (λi inst. (i, inst)) *)
Theorem drop_mapi_pair:
  !k (l : 'a list). k <= LENGTH l ==>
    DROP k (MAPi (\i inst. (i, inst)) l) =
    MAPi (\i inst. (i + k, inst)) (DROP k l)
Proof
  simp[drop_mapi]
QED

(* Accumulator factoring: FOLDL with non-empty prefix =
   prefix ++ FOLDL with empty prefix *)
Theorem block_foldl_acc:
  !pairs gen_plan prefix ps.
    block_foldl gen_plan (SOME (prefix, ps)) pairs =
    OPTION_MAP (\(ops, ps'). (prefix ++ ops, ps'))
      (block_foldl gen_plan (SOME ([], ps)) pairs)
Proof
  Induct
  \\ rewrite_tac[block_foldl_def] \\ simp[]
  \\ rpt gen_tac \\ PairCases_on `h`
  \\ pop_assum mp_tac  (* hide IH from simp *)
  \\ ONCE_REWRITE_TAC[block_foldl_cons]
  \\ Cases_on `gen_plan h0 h1 ps`
  \\ ASM_REWRITE_TAC[optionTheory.option_case_def,
                      optionTheory.OPTION_MAP_DEF]
  \\ PairCases_on `x`
  \\ ASM_REWRITE_TAC[pairTheory.pair_case_thm, APPEND_NIL]
  \\ disch_then (fn ih =>
       mp_tac (Q.SPECL [`gen_plan`, `prefix ++ x0`, `x1`] ih) >>
       mp_tac (Q.SPECL [`gen_plan`, `x0`, `x1`] ih))
  \\ BETA_TAC
  \\ REWRITE_TAC[pairTheory.pair_case_thm, APPEND_NIL]
  \\ REWRITE_TAC[GSYM APPEND_ASSOC]
  \\ rpt strip_tac
  \\ Cases_on `block_foldl gen_plan (SOME ([],x1)) pairs`
  \\ fs[]
  \\ PairCases_on `x` \\ fs[]
QED

(* MAPi cons simplification for indexed pairs *)
Theorem mapi_pair_cons:
  !k h (remaining : 'a list).
    MAPi (\i inst. (i + k, inst)) (h :: remaining) =
    (k, h) :: MAPi (\i inst. (i + (k + 1), inst)) remaining
Proof
  rpt gen_tac >>
  simp[MAPi_def, combinTheory.o_DEF, ADD_CLAUSES] >>
  irule MAPi_CONG >> simp[]
QED

(* ===== asm_steps composition helpers ===== *)

(* Compose two sequences of asm_steps where the first succeeds (AsmOK) *)
Theorem asm_steps_compose_ok:
  !lo o2pc prog n1 n2 s s1 s2.
    asm_steps lo o2pc prog n1 s = AsmOK s1 /\
    asm_steps lo o2pc prog n2 s1 = AsmOK s2 ==>
    asm_steps lo o2pc prog (n1 + n2) s = AsmOK s2
Proof
  rpt strip_tac >>
  imp_res_tac asm_steps_add_ok >> ASM_REWRITE_TAC[]
QED

Theorem asm_steps_compose_halt:
  !lo o2pc prog n1 n2 s s1 s2.
    asm_steps lo o2pc prog n1 s = AsmOK s1 /\
    asm_steps lo o2pc prog n2 s1 = AsmHalt s2 ==>
    asm_steps lo o2pc prog (n1 + n2) s = AsmHalt s2
Proof
  rpt strip_tac >>
  imp_res_tac asm_steps_add_ok >> ASM_REWRITE_TAC[]
QED

Theorem asm_steps_compose_revert:
  !lo o2pc prog n1 n2 s s1 s2.
    asm_steps lo o2pc prog n1 s = AsmOK s1 /\
    asm_steps lo o2pc prog n2 s1 = AsmRevert s2 ==>
    asm_steps lo o2pc prog (n1 + n2) s = AsmRevert s2
Proof
  rpt strip_tac >>
  imp_res_tac asm_steps_add_ok >> ASM_REWRITE_TAC[]
QED

Theorem asm_steps_compose_fault:
  !lo o2pc prog n1 n2 s s1 s2.
    asm_steps lo o2pc prog n1 s = AsmOK s1 /\
    asm_steps lo o2pc prog n2 s1 = AsmFault s2 ==>
    asm_steps lo o2pc prog (n1 + n2) s = AsmFault s2
Proof
  rpt strip_tac >>
  imp_res_tac asm_steps_add_ok >> ASM_REWRITE_TAC[]
QED

(* 3-way simulation composition:
   If the first n1 asm steps succeed (AsmOK as1), and running the block
   from the intermediate state satisfies the 3-way sim, then running the
   block from the original state also satisfies the 3-way sim. *)
Theorem three_way_sim_compose:
  !lo o2pc prog n1 as as1 ps_final rb rb'.
    asm_steps lo o2pc prog n1 as = AsmOK as1 /\
    rb = rb' /\
    (!vs'. rb' = OK vs' ==>
      ?n as'. asm_steps lo o2pc prog n as1 = AsmOK as' /\
              venom_asm_rel lo ps_final vs' as') /\
    (!vs'. rb' = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n as1 = AsmHalt as' /\
              venom_asm_terminal_rel vs' as') /\
    (!a vs'. rb' = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\
          asm_steps lo o2pc prog n as1 = AsmRevert as') \/
         (a = ExHalt_abort /\
          asm_steps lo o2pc prog n as1 = AsmFault as')) /\
        venom_asm_terminal_rel vs' as')
    ==>
    (!vs'. rb = OK vs' ==>
      ?n as'. asm_steps lo o2pc prog n as = AsmOK as' /\
              venom_asm_rel lo ps_final vs' as') /\
    (!vs'. rb = Halt vs' ==>
      ?n as'. asm_steps lo o2pc prog n as = AsmHalt as' /\
              venom_asm_terminal_rel vs' as') /\
    (!a vs'. rb = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\
          asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\
          asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as')
Proof
  rpt gen_tac >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  >- ( (* OK *)
    res_tac >>
    qexistsl_tac [`n1 + n`, `as'`] >>
    imp_res_tac asm_steps_compose_ok >> ASM_REWRITE_TAC[])
  >- ( (* Halt *)
    res_tac >>
    qexistsl_tac [`n1 + n`, `as'`] >>
    imp_res_tac asm_steps_compose_halt >> ASM_REWRITE_TAC[])
  >> ( (* Abort *)
    res_tac >>
    qexistsl_tac [`n1 + n`, `as'`] >>
    imp_res_tac asm_steps_add_ok >>
    conj_tac >- (
      first_x_assum (qspec_then `n` (fn th => REWRITE_TAC[th])) >>
      fs[])
    >> ASM_REWRITE_TAC[])
QED

(* ===== Block instruction simulation (inductive core) ===== *)

(* This is the inductive heart of gen_block_simulation.
   It says: if we have a per-instruction simulation property,
   and block_foldl generates a plan for the remaining instructions,
   then exec_block on those remaining instructions corresponds to
   executing the plan via asm_steps.

   The per-instruction property is passed as 5 universally quantified
   hypotheses (one for each step_inst outcome × terminator combination).
*)
Theorem block_insts_sim:
  !remaining.  (* induction variable: remaining instruction list *)
  !initial_fmp fuel ctx lo o2pc prog bb k gen_plan ps_k vs as inst_ops ps_final.
    (* Structural *)
    bb_well_formed bb /\
    remaining = DROP k bb.bb_instructions /\
    vs.vs_inst_idx = k /\
    (* Plan generation *)
    block_foldl gen_plan (SOME ([], ps_k))
      (MAPi (\i inst. (i + k, inst)) remaining) =
      SOME (inst_ops, ps_final) /\
    (* State *)
    ~vs.vs_halted /\
    venom_asm_rel lo ps_k vs as /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp inst_ops) /\
    (* OK steps preserve vs_halted (needed to propagate ~vs_halted) *)
    (!inst vs_0 vs_0'.
       step_inst fuel ctx inst vs_0 = OK vs_0' ==>
       (vs_0'.vs_halted = vs_0.vs_halted)) /\
    (* === Per-instruction simulation hypotheses === *)
    (* OK + not terminator — also tracks PC for composition *)
    (!i inst ps_i ops_i ps_next vs_i as_i vs_i'.
       i < LENGTH bb.bb_instructions /\
       EL i bb.bb_instructions = inst /\
       gen_plan i inst ps_i = SOME (ops_i, ps_next) /\
       venom_asm_rel lo ps_i vs_i as_i /\
       asm_block_at prog as_i.as_pc (execute_plan initial_fmp ops_i) /\
       step_inst fuel ctx inst vs_i = OK vs_i' /\
       ~is_terminator inst.inst_opcode ==>
       ?n as_i'.
         asm_steps lo o2pc prog n as_i = AsmOK as_i' /\
         venom_asm_rel lo ps_next vs_i' as_i' /\
         as_i'.as_pc = as_i.as_pc + LENGTH (execute_plan initial_fmp ops_i)) /\
    (* OK + terminator + not halted *)
    (!i inst ps_i ops_i ps_next vs_i as_i vs_i'.
       i < LENGTH bb.bb_instructions /\
       EL i bb.bb_instructions = inst /\
       gen_plan i inst ps_i = SOME (ops_i, ps_next) /\
       venom_asm_rel lo ps_i vs_i as_i /\
       asm_block_at prog as_i.as_pc (execute_plan initial_fmp ops_i) /\
       step_inst fuel ctx inst vs_i = OK vs_i' /\
       is_terminator inst.inst_opcode /\ ~vs_i'.vs_halted ==>
       ?n as_i'.
         asm_steps lo o2pc prog n as_i = AsmOK as_i' /\
         venom_asm_rel lo ps_next vs_i' as_i') /\
    (* Halt *)
    (!i inst ps_i ops_i ps_next vs_i as_i vs_i'.
       i < LENGTH bb.bb_instructions /\
       EL i bb.bb_instructions = inst /\
       gen_plan i inst ps_i = SOME (ops_i, ps_next) /\
       venom_asm_rel lo ps_i vs_i as_i /\
       asm_block_at prog as_i.as_pc (execute_plan initial_fmp ops_i) /\
       step_inst fuel ctx inst vs_i = Halt vs_i' ==>
       ?n as_i'.
         asm_steps lo o2pc prog n as_i = AsmHalt as_i' /\
         venom_asm_terminal_rel vs_i' as_i') /\
    (* Abort *)
    (!i inst ps_i ops_i ps_next vs_i as_i a vs_i'.
       i < LENGTH bb.bb_instructions /\
       EL i bb.bb_instructions = inst /\
       gen_plan i inst ps_i = SOME (ops_i, ps_next) /\
       venom_asm_rel lo ps_i vs_i as_i /\
       asm_block_at prog as_i.as_pc (execute_plan initial_fmp ops_i) /\
       step_inst fuel ctx inst vs_i = Abort a vs_i' ==>
       ?n as_i'.
         ((a = Revert_abort /\
           asm_steps lo o2pc prog n as_i = AsmRevert as_i') \/
          (a = ExHalt_abort /\
           asm_steps lo o2pc prog n as_i = AsmFault as_i')) /\
         venom_asm_terminal_rel vs_i' as_i')
    ==>
    (* === Conclusion: 3-way simulation === *)
    (!vs'. exec_block fuel ctx bb vs = OK vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        venom_asm_rel lo ps_final vs' as') /\
    (!vs'. exec_block fuel ctx bb vs = Halt vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as') /\
    (!a vs'. exec_block fuel ctx bb vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\
          asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\
          asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as')
Proof
  Induct
  >- (
    (* Base case: remaining = [] *)
    rpt gen_tac >> strip_tac >>
    `~(k < LENGTH bb.bb_instructions)` by (
      strip_tac >> imp_res_tac DROP_CONS_EL >> fs[]
    ) >>
    rpt conj_tac >> rpt gen_tac >> strip_tac >>
    `get_instruction bb (vs.vs_inst_idx) = NONE` by simp[get_instruction_def] >>
    fs[Once exec_block_def]
  )
  >> (
    (* Step case: h :: remaining *)
    rpt gen_tac >> strip_tac >>
    `k < LENGTH bb.bb_instructions`
      by (CCONTR_TAC >> fs[NOT_LESS, DROP_LENGTH_TOO_LONG, DROP_EQ_NIL]) >>
    `EL k bb.bb_instructions = h /\
     remaining = DROP (SUC k) bb.bb_instructions`
      by (imp_res_tac DROP_CONS_EL >> fs[]) >>
    (* Decompose block_foldl *)
    qpat_x_assum `block_foldl _ _ _ = _` mp_tac >>
    ONCE_REWRITE_TAC[mapi_pair_cons] >>
    ONCE_REWRITE_TAC[block_foldl_cons] >>
    Cases_on `gen_plan k h ps_k` >- simp[] >>
    PairCases_on `x` >>
    simp_tac bool_ss [optionTheory.option_case_def,
      pairTheory.pair_case_thm, APPEND_NIL] >>
    disch_tac >>
    `?tail_ops. block_foldl gen_plan (SOME ([], x1))
       (MAPi (\i inst. (i + (k + 1), inst)) remaining) =
       SOME (tail_ops, ps_final) /\ inst_ops = x0 ++ tail_ops`
      by (
        qpat_x_assum `block_foldl _ _ _ = _` mp_tac >>
        ONCE_REWRITE_TAC[block_foldl_acc] >>
        REWRITE_TAC[optionTheory.OPTION_MAP_DEF] >>
        Cases_on `block_foldl gen_plan (SOME ([],x1))
          (MAPi (\i inst. (i + (k + 1),inst)) remaining)` >>
        simp[] >> PairCases_on `x` >> simp[]
      ) >>
    `asm_block_at prog as.as_pc (execute_plan initial_fmp x0) /\
     asm_block_at prog (as.as_pc + LENGTH (execute_plan initial_fmp x0))
       (execute_plan initial_fmp tail_ops)`
      by (qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp inst_ops)` mp_tac >>
          ASM_REWRITE_TAC[execute_plan_append, asm_block_at_append]) >>
    `get_instruction bb k = SOME h`
      by (rw[get_instruction_def]) >>
    `get_instruction bb vs.vs_inst_idx = SOME h`
      by ASM_REWRITE_TAC[] >>
    Cases_on `step_inst fuel ctx h vs`
    >- suspend "ok"
    >- suspend "halt"
    >- suspend "abort"
    >- suspend "intret"
    >> suspend "error"
  )
QED

(* === Resume: IntRet case (vacuously true) === *)
Resume block_insts_sim[intret]:
  imp_res_tac exec_block_propagate >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FULL_SIMP_TAC bool_ss [exec_result_distinct]
QED

(* === Resume: Error case (vacuously true) === *)
Resume block_insts_sim[error]:
  imp_res_tac exec_block_propagate >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FULL_SIMP_TAC bool_ss [exec_result_distinct]
QED

(* === Resume: Halt case === *)
Resume block_insts_sim[halt]:
  rename1 `step_inst _ _ _ _ = Halt vs1` >>
  imp_res_tac exec_block_propagate >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FULL_SIMP_TAC bool_ss [exec_result_distinct, exec_result_11] >>
  qpat_x_assum `!i ps_i ops_i ps_next vs_i as_i vs_i'.
    _ /\ _ /\ _ /\ _ /\ step_inst _ _ _ _ = Halt _ ==> _`
    (qspecl_then [`k`, `ps_k`, `x0`, `x1`,
      `vs`, `as`, `vs1`] mp_tac) >>
  ASM_REWRITE_TAC[]
QED

(* === Resume: Abort case === *)
Resume block_insts_sim[abort]:
  rename1 `step_inst _ _ _ _ = Abort a1 vs1` >>
  imp_res_tac exec_block_propagate >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  FULL_SIMP_TAC bool_ss [exec_result_distinct, exec_result_11] >>
  qpat_x_assum `!i ps_i ops_i ps_next vs_i as_i a vs_i'.
    _ /\ _ /\ _ /\ _ /\ step_inst _ _ _ _ = Abort _ _ ==> _`
    (qspecl_then [`k`, `ps_k`, `x0`, `x1`,
      `vs`, `as`, `a1`, `vs1`] mp_tac) >>
  ASM_REWRITE_TAC[]
QED

(* === Resume: OK case === *)
Resume block_insts_sim[ok]:
  rename1 `step_inst _ _ _ _ = OK vs1` >>
  Cases_on `is_terminator h.inst_opcode`
  >- suspend "ok_term"
  >> suspend "ok_nonterm"
QED

(* OK + terminator *)
Resume block_insts_sim[ok_term]:
  `k = PRE (LENGTH bb.bb_instructions)`
    by (FULL_SIMP_TAC bool_ss [bb_well_formed_def] >>
        first_x_assum (qspec_then `k` mp_tac) >>
        ASM_REWRITE_TAC[] >> decide_tac)
  \\ `SUC k = LENGTH bb.bb_instructions` by decide_tac
  \\ `remaining = []`
       by (ASM_REWRITE_TAC[] >> irule DROP_LENGTH_TOO_LONG >> decide_tac)
  \\ `tail_ops = [] /\ x1 = ps_final`
       by (qpat_x_assum `block_foldl _ (SOME ([],x1)) _ = SOME _` mp_tac >>
           ASM_REWRITE_TAC[MAPi_def] >>
           REWRITE_TAC[block_foldl_def] >> strip_tac >> fs[])
  \\ suspend "ok_term_run_block"
QED

Resume block_insts_sim[ok_term_run_block]:
  mp_tac exec_block_terminator
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `bb`, `vs`, `h`, `vs1`]
       mp_tac)
  \\ (impl_tac >- ASM_REWRITE_TAC[])
  \\ disch_then (fn th => REWRITE_TAC[th])
  \\ IF_CASES_TAC
  >- suspend "ok_term_halted"
  >> suspend "ok_term_not_halted"
QED

Resume block_insts_sim[ok_term_halted]:
  (* Contradiction: vs1.vs_halted (IF_CASES_TAC), ~vs.vs_halted,
     H0 gives vs1.vs_halted <=> vs.vs_halted *)
  qpat_x_assum `!inst vs_0 vs_0'. step_inst _ _ _ _ = OK _ ==> _`
    (qspecl_then [`h`, `vs`, `vs1`] mp_tac)
  \\ (impl_tac >- ASM_REWRITE_TAC[])
  (* Now have: vs1.vs_halted <=> vs.vs_halted *)
  \\ strip_tac
  (* Assumptions: vs1.vs_halted, ~vs.vs_halted, vs1.vs_halted <=> vs.vs_halted *)
  \\ metis_tac[]
QED

Resume block_insts_sim[ok_term_not_halted]:
  rpt conj_tac
  >- ( (* OK conjunct *)
    gen_tac >> strip_tac >>
    qpat_assum `!i inst ps_i ops_i ps_next vs_i as_i vs_i'.
         _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ ~vs_i'.vs_halted ==> _`
         (qspecl_then [`k`, `h`, `ps_k`, `x0`, `x1`,
           `vs`, `as`, `vs'`] mp_tac) >>
    FULL_SIMP_TAC bool_ss [exec_result_11] >>
    ASM_REWRITE_TAC[])
  >- (gen_tac >> strip_tac
      >> FULL_SIMP_TAC bool_ss [exec_result_distinct])
  >> (rpt gen_tac >> strip_tac
      >> FULL_SIMP_TAC bool_ss [exec_result_distinct])
QED

(* OK + non-terminator: use H1 then IH *)
Resume block_insts_sim[ok_nonterm]:
  (* Rewrite run_block *)
  `exec_block fuel ctx bb vs =
   exec_block fuel ctx bb (vs1 with vs_inst_idx := SUC k)`
    by (
      `exec_block fuel ctx bb vs =
       exec_block fuel ctx bb (vs1 with vs_inst_idx := SUC vs.vs_inst_idx)`
        suffices_by (ASM_REWRITE_TAC[]) >>
      irule exec_block_step >> qexists_tac `h` >> ASM_REWRITE_TAC[])
  (* Apply H1 -- keep hypothesis for IH *)
  \\ qpat_assum `!i inst ps_i ops_i ps_next vs_i as_i vs_i'.
       _ /\ _ /\ _ /\ _ /\ _ /\ _ /\ ~is_terminator _ ==> _`
       (qspecl_then [`k`, `h`, `ps_k`, `x0`, `x1`,
         `vs`, `as`, `vs1`] mp_tac)
  \\ (impl_tac >- ASM_REWRITE_TAC[])
  \\ strip_tac
  \\ rename1 `asm_steps lo o2pc prog n1 as = AsmOK as1`
  (* Apply IH *)
  \\ first_x_assum (qspecl_then [
       `initial_fmp`, `fuel`, `ctx`, `lo`, `o2pc`, `prog`, `bb`, `SUC k`,
       `gen_plan`, `x1`, `vs1 with vs_inst_idx := SUC k`,
       `as1`, `tail_ops`, `ps_final`] mp_tac)
  \\ (impl_tac >- suspend "ok_nonterm_ih")
  \\ suspend "ok_nonterm_compose"
QED

Resume block_insts_sim[ok_nonterm_ih]:
  rpt conj_tac
  \\ TRY (FIRST_ASSUM ACCEPT_TAC)
  >- SIMP_TAC (srw_ss()) []
  >- (ONCE_REWRITE_TAC[ADD1] >> ASM_REWRITE_TAC[])
  >- (SIMP_TAC (srw_ss()) []
      >> qpat_x_assum `!inst vs_0 vs_0'. step_inst _ _ _ _ = OK _ ==> _`
           (qspecl_then [`h`, `vs`, `vs1`] mp_tac)
      >> ASM_REWRITE_TAC[]
      >> strip_tac >> metis_tac[])
  >- (irule venom_asm_rel_inst_idx_update >> ASM_REWRITE_TAC[])
  >- ASM_REWRITE_TAC[]
QED

Resume block_insts_sim[ok_nonterm_compose]:
  strip_tac
  \\ irule three_way_sim_compose
  \\ qexistsl_tac [`as1`, `n1`,
       `exec_block fuel ctx bb (vs1 with vs_inst_idx := SUC k)`]
  \\ ASM_REWRITE_TAC[]
QED

Finalise block_insts_sim;
