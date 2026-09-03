(*
 * Emit Input Plan Simulation
 *
 * Proves that emit_one_input (which arranges one operand on the asm
 * stack) preserves venom_asm_rel. For the restricted case (non-INVOKE,
 * no spilled operand, var at depth <= 15), all emitted ops are simple,
 * so simple_prefix_venom_asm_rel suffices.
 *
 * Key results:
 *   emit_one_input_sim   — per-operand simulation
 *   emit_input_plan_cons — FOLDL decomposition (structural)
 *
 * Callers compose per-step simulations for their specific arity
 * (e.g., pure2: two applications of emit_one_input_sim +
 * asm_steps_compose_ok).
 *)

Theory emitInputSim
Ancestors
  strongPrefixSim planWf instSimHelpers blockSimHelpers
  doSwapSim foldlSim
  stackPlanGen stackPlanOps stackPlanTypes stackModel
  codegenRel asmSem venomInst
  list rich_list finite_map arithmetic

(* =========================================================================
   FOLDL decomposition: emit_input_plan cons
   ========================================================================= *)

(* 2-element unrolling for pure2 *)
Theorem emit_input_plan_two:
  !opc op1 op2 nl ps.
    emit_input_plan opc [op1; op2] nl ps =
    let (ops1, ps1) = emit_one_input opc nl op1 ps in
    let (ops2, ps2) = emit_one_input opc nl op2 ps1 in
    (ops1 ++ ops2, ps2)
Proof
  rpt gen_tac >>
  simp[emit_input_plan_def, FOLDL] >>
  Cases_on `emit_one_input opc nl op1 ps` >>
  rename1 `(ops1, ps1)` >>
  Cases_on `emit_one_input opc nl op2 ps1` >>
  rename1 `(ops2, ps2)` >>
  simp[]
QED

(* 1-element for pure1 *)
Theorem emit_input_plan_one:
  !opc op nl ps.
    emit_input_plan opc [op] nl ps = emit_one_input opc nl op ps
Proof
  rpt gen_tac >>
  simp[emit_input_plan_def, FOLDL] >>
  Cases_on `emit_one_input opc nl op ps` >> simp[]
QED

(* 3-element for pure3 *)
Theorem emit_input_plan_three:
  !opc op1 op2 op3 nl ps.
    emit_input_plan opc [op1; op2; op3] nl ps =
    let (ops1, ps1) = emit_one_input opc nl op1 ps in
    let (ops2, ps2) = emit_one_input opc nl op2 ps1 in
    let (ops3, ps3) = emit_one_input opc nl op3 ps2 in
    (ops1 ++ ops2 ++ ops3, ps3)
Proof
  rpt gen_tac >>
  simp[emit_input_plan_def, FOLDL] >>
  Cases_on `emit_one_input opc nl op1 ps` >>
  rename1 `(ops1, ps1)` >>
  Cases_on `emit_one_input opc nl op2 ps1` >>
  rename1 `(ops2, ps2)` >>
  Cases_on `emit_one_input opc nl op3 ps2` >>
  rename1 `(ops3, ps3)` >>
  simp[APPEND_ASSOC]
QED

(* =========================================================================
   emit_one_input: ops are all simple when no spill involved
   ========================================================================= *)

Theorem emit_one_input_all_simple:
  !opc nl op ps.
    opc <> INVOKE /\
    ~(is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!v dist. op = Var v /\
              stack_get_depth (Var v) ps.ps_stack = SOME dist ==>
              dist <= 15) ==>
    EVERY is_simple_stack_op (FST (emit_one_input opc nl op ps))
Proof
  rpt gen_tac >> strip_tac >>
  simp[emit_one_input_def] >>
  Cases_on `op` >> gvs[is_var_operand_def] >>
  TRY (simp[is_simple_stack_op_def] >> NO_TAC) >>
  (* Var case *)
  rename1 `Var v` >>
  Cases_on `MEM v nl` >> gvs[] >>
  Cases_on `stack_get_depth (Var v) ps.ps_stack` >> gvs[] >>
  rename1 `_ = SOME dist` >>
  `dist <= 15` by metis_tac[] >>
  simp[do_dup_def, is_simple_stack_op_def]
QED

(* =========================================================================
   emit_one_input: prefix_wf
   ========================================================================= *)

Theorem emit_one_input_prefix_wf:
  !opc nl op ps lo.
    opc <> INVOKE /\
    (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) ==>
    prefix_wf lo (LENGTH ps.ps_stack)
      (FST (emit_one_input opc nl op ps))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`opc`, `nl`, `op`, `ps`, `lo`]
    mp_tac emit_one_input_wf_len >>
  simp[]
QED

(* =========================================================================
   State bridge: apply_simple_ops agrees with emit_one_input
   for the non-spilled case
   ========================================================================= *)

Theorem emit_one_input_state_bridge:
  !opc nl op ps lo.
    opc <> INVOKE /\
    ~(is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!v dist. op = Var v /\
              stack_get_depth (Var v) ps.ps_stack = SOME dist ==>
              dist <= 15) /\
    (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) ==>
    (apply_simple_ops lo
       (FST (emit_one_input opc nl op ps)) ps).ps_stack =
      (SND (emit_one_input opc nl op ps)).ps_stack /\
    (apply_simple_ops lo
       (FST (emit_one_input opc nl op ps)) ps).ps_spilled =
      ps.ps_spilled /\
    (apply_simple_ops lo
       (FST (emit_one_input opc nl op ps)) ps).ps_alloc =
      ps.ps_alloc /\
    (SND (emit_one_input opc nl op ps)).ps_spilled =
      ps.ps_spilled /\
    (SND (emit_one_input opc nl op ps)).ps_alloc = ps.ps_alloc
Proof
  rpt gen_tac >> strip_tac >>
  simp[emit_one_input_def] >>
  Cases_on `op` >> gvs[is_var_operand_def] >>
  TRY (simp[apply_simple_ops_def, apply_simple_op_def, stack_push_def] >>
       NO_TAC) >>
  (* Var case *)
  rename1 `Var v` >>
  Cases_on `MEM v nl` >> gvs[]
  >- (
    Cases_on `stack_get_depth (Var v) ps.ps_stack` >> gvs[]
    >- simp[apply_simple_ops_def]
    >> rename1 `_ = SOME dist` >>
    `dist <= 15` by metis_tac[] >>
    simp[do_dup_def, apply_simple_ops_def, apply_simple_op_def,
         stack_dup_def, stack_peek_def] >>
    `dist + 1 <= LENGTH ps.ps_stack` by
      (imp_res_tac stack_get_depth_bound >> decide_tac) >>
    simp[]
  )
  >- simp[apply_simple_ops_def]
QED

(* =========================================================================
   Stack length monotonicity: emit_one_input never shrinks the stack
   ========================================================================= *)

Theorem do_dup_stack_length[local]:
  !dist ps ops ps'.
    dist < LENGTH ps.ps_stack /\
    do_dup dist ps = (ops, ps') ==>
    LENGTH ps'.ps_stack = LENGTH ps.ps_stack + 1
Proof
  rpt gen_tac >>
  simp[do_dup_def] >>
  IF_CASES_TAC
  >- (strip_tac >> gvs[stack_dup_def]) >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  qabbrev_tac `fres = FOLDL
    (\(ops,offs,al) item.
      let (off,al') = alloc_spill_slot al in
        (ops ++ [SOSpill off], SNOC off offs, al'))
    ([],[],ps.ps_alloc) (top_n (dist + 1) ps.ps_stack)` >>
  PairCases_on `fres` >> simp[] >>
  strip_tac >> gvs[]
QED

Theorem do_restore_stack_length[local]:
  !op ps ops ps'.
    do_restore op ps = (ops, ps') ==>
    LENGTH ps'.ps_stack >= LENGTH ps.ps_stack
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[stack_push_def]
QED

(*
 * Var case helper: avoids pair-lambda issues by splitting into
 * spilled/not-spilled and live/not-live sub-cases at the definition level.
 *)
Theorem emit_one_input_var_not_spilled_stack[local]:
  !opc nl v ps.
    ~IS_SOME (FLOOKUP ps.ps_spilled (Var v)) ==>
    LENGTH (SND (emit_one_input opc nl (Var v) ps)).ps_stack >=
    LENGTH ps.ps_stack
Proof
  rpt strip_tac >>
  simp[emit_one_input_def, is_var_operand_def] >>
  Cases_on `MEM v nl` >> simp[] >>
  Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[] >>
  Cases_on `do_dup x ps` >> simp[] >>
  imp_res_tac stack_get_depth_bound >>
  imp_res_tac do_dup_stack_length >> decide_tac
QED

Theorem emit_one_input_var_spilled_stack[local]:
  !opc nl v ps.
    IS_SOME (FLOOKUP ps.ps_spilled (Var v)) ==>
    LENGTH (SND (emit_one_input opc nl (Var v) ps)).ps_stack >=
    LENGTH ps.ps_stack
Proof
  rpt strip_tac >>
  simp[emit_one_input_def, is_var_operand_def] >>
  Cases_on `do_restore (Var v) ps` >> simp[] >>
  imp_res_tac do_restore_stack_length >>
  Cases_on `MEM v nl` >> simp[] >>
  (* only MEM v nl case remains *)
  Cases_on `stack_get_depth (Var v) r.ps_stack` >> simp[] >>
  TRY decide_tac >>
  Cases_on `do_dup x r` >> simp[] >>
  imp_res_tac stack_get_depth_bound >>
  imp_res_tac do_dup_stack_length >> decide_tac
QED

Theorem emit_one_input_label_stack[local]:
  !opc nl l ps.
    LENGTH (SND (emit_one_input opc nl (Label l) ps)).ps_stack >=
    LENGTH ps.ps_stack
Proof
  rpt gen_tac >>
  simp[emit_one_input_def, is_var_operand_def, stack_push_def] >>
  IF_CASES_TAC >> simp[]
QED

Theorem emit_one_input_lit_stack[local]:
  !opc nl v ps.
    LENGTH (SND (emit_one_input opc nl (Lit v) ps)).ps_stack >=
    LENGTH ps.ps_stack
Proof
  rpt gen_tac >>
  simp[emit_one_input_def, is_var_operand_def, stack_push_def]
QED

Theorem emit_one_input_stack_mono:
  !opc nl op ps.
    LENGTH (SND (emit_one_input opc nl op ps)).ps_stack >=
    LENGTH ps.ps_stack
Proof
  rpt gen_tac >> Cases_on `op` >>
  metis_tac[emit_one_input_lit_stack,
            emit_one_input_var_not_spilled_stack,
            emit_one_input_var_spilled_stack,
            emit_one_input_label_stack]
QED

(* Helper: FOLDL stack monotonicity in fully-reduced FST/SND form *)
Theorem emit_input_foldl_stack_mono[local]:
  !ops opc nl acc ps.
    LENGTH (SND (FOLDL (\(acc_ops, ps) op.
               (acc_ops ++ FST (emit_one_input opc nl op ps),
                SND (emit_one_input opc nl op ps)))
             (acc, ps) ops)).ps_stack >=
    LENGTH ps.ps_stack
Proof
  Induct >> simp[] >> rpt gen_tac >>
  SUBGOAL_THEN ``LENGTH (SND (FOLDL (\(acc_ops,ps) op.
             (acc_ops ++ FST (emit_one_input opc nl op ps),
              SND (emit_one_input opc nl op ps)))
           (acc ++ FST (emit_one_input opc nl h ps),
            SND (emit_one_input opc nl h ps)) ops)).ps_stack >=
   LENGTH (SND (emit_one_input opc nl h ps)).ps_stack``
    ASSUME_TAC >- metis_tac[] >>
  SUBGOAL_THEN ``LENGTH (SND (emit_one_input opc nl h ps)).ps_stack >=
   LENGTH ps.ps_stack`` ASSUME_TAC
  >- metis_tac[emit_one_input_stack_mono] >>
  decide_tac
QED

Theorem emit_input_plan_stack_mono:
  !opc ops nl ps.
    LENGTH (SND (emit_input_plan opc ops nl ps)).ps_stack >=
    LENGTH ps.ps_stack
Proof
  rpt gen_tac >>
  PURE_REWRITE_TAC[emit_input_plan_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV LET_THM)) >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  metis_tac[emit_input_foldl_stack_mono]
QED

(* =========================================================================
   Per-operand simulation: emit_one_input_sim
   ========================================================================= *)

Theorem emit_one_input_sim:
  !opc nl op ps ops ps' lo o2pc prog vs st.
    opc <> INVOKE /\
    ~(is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!v dist. op = Var v /\
              stack_get_depth (Var v) ps.ps_stack = SOME dist ==>
              dist <= 15) /\
    (!l. op = Label l ==> IS_SOME (FLOOKUP lo l)) /\
    emit_one_input opc nl op ps = (ops, ps') /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  (* Key: keep equation emit_one_input ... = (ops, ps') intact.
     Derive FST/SND facts BEFORE substituting. *)
  `FST (emit_one_input opc nl op ps) = ops /\
   SND (emit_one_input opc nl op ps) = ps'` by
    (Cases_on `emit_one_input opc nl op ps` >> gvs[]) >>
  (* Derive: all ops are simple *)
  `EVERY is_simple_stack_op ops` by
    (qspecl_then [`opc`, `nl`, `op`, `ps`]
       mp_tac emit_one_input_all_simple >>
     (impl_tac >- ASM_REWRITE_TAC[]) >> gvs[]) >>
  (* Derive: prefix_wf *)
  `prefix_wf lo (LENGTH ps.ps_stack) ops` by
    (qspecl_then [`opc`, `nl`, `op`, `ps`, `lo`]
       mp_tac emit_one_input_prefix_wf >>
     (impl_tac >- ASM_REWRITE_TAC[]) >> gvs[]) >>
  (* Derive: state bridge *)
  `(apply_simple_ops lo ops ps).ps_stack = ps'.ps_stack /\
   (apply_simple_ops lo ops ps).ps_spilled = ps.ps_spilled /\
   (apply_simple_ops lo ops ps).ps_alloc = ps.ps_alloc /\
   ps'.ps_spilled = ps.ps_spilled /\
   ps'.ps_alloc = ps.ps_alloc` by
    (qspecl_then [`opc`, `nl`, `op`, `ps`, `lo`]
       mp_tac emit_one_input_state_bridge >>
     (impl_tac >- ASM_REWRITE_TAC[]) >> gvs[]) >>
  (* Apply simple_prefix_venom_asm_rel *)
  qspecl_then [`ops`, `initial_fmp`, `lo`, `o2pc`, `prog`, `ps`, `vs`, `st`]
    mp_tac simple_prefix_venom_asm_rel >>
  (impl_tac >- ASM_REWRITE_TAC[]) >> strip_tac >>
  qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  (* Bridge: apply_simple_ops lo ops ps ↔ ps' *)
  irule venom_asm_rel_ps_transfer >>
  qexists_tac `apply_simple_ops lo ops ps` >>
  ASM_REWRITE_TAC[]
QED

(* =========================================================================
   Bridge: emit_input_plan = plan_steps (emit_one_input ...)
   ========================================================================= *)

(* The FOLDL in emit_input_plan matches plan_steps with the right body *)
Theorem emit_input_foldl_body_eq[local]:
  !opc nl.
    foldl_body (\op ps. emit_one_input opc nl op ps) =
    (\(acc_ops, ps) op.
      let (step_ops, ps') = emit_one_input opc nl op ps in
      (acc_ops ++ step_ops, ps'))
Proof
  rpt gen_tac >>
  simp[FUN_EQ_THM, foldl_body_def, pairTheory.FORALL_PROD]
QED

(* emit_input_plan = plan_steps with emit_one_input as step function *)
Theorem emit_input_plan_eq_plan_steps:
  !opc operands nl ps.
    emit_input_plan opc operands nl ps =
    plan_steps (\op ps. emit_one_input opc nl op ps) operands ps
Proof
  rpt gen_tac >>
  REWRITE_TAC[emit_input_plan_def] >>
  REWRITE_TAC[GSYM emit_input_foldl_body_eq] >>
  REWRITE_TAC[GSYM plan_steps_eq_foldl]
QED


