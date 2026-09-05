(*
 * Emit Step Simulation
 *
 * Proves that the SOEmit step (the actual opcode execution) preserves
 * venom_asm_rel. The plan's pop-operands/push-outputs (steps 5-6 of
 * generate_regular_inst_plan) model what the asm instruction does.
 *
 * Key results:
 *   emit_popn_push1_sim — generic: any 1-step that pops n, pushes 1 result
 *   emit_pure2_sim      — binary pure ops (ADD, SUB, MUL, ...)
 *   emit_pure1_sim      — unary pure ops (ISZERO, NOT)
 *   emit_pure3_sim      — ternary pure ops (ADDMOD, MULMOD)
 *
 * Strategy: compose plan_stack_rel_pop + plan_stack_rel_update_var +
 *   plan_stack_rel_push. The tricky index arithmetic is handled by
 *   existing stackOpSim lemmas.
 *)

Theory emitSim
Ancestors
  codegenRel asmSem planExec stackPlanGen stackPlanTypes stackModel
  venomExecSemantics venomState venomInst
  instSimHelpers stackOpSim blockSimHelpers asmToBytecodeProofs
  strongPrefixSim list rich_list finite_map
Libs
  BasicProvers

Theorem initial_fmp_emit_update_var:
  !lo o2pc prog ps vs as initial_fmp out.
    venom_asm_rel lo ps vs as /\
    ~MEM (Var out) ps.ps_stack /\
    Var out NOTIN FDOM ps.ps_spilled /\
    n2w initial_fmp = vs.vs_initial_fmp /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp [SOInitialFmp]) ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack := SNOC (Var out) ps.ps_stack)
        (update_var out vs.vs_initial_fmp vs) as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt strip_tac >>
  qspecl_then [`lo`, `o2pc`, `prog`, `ps`, `vs`, `as`, `initial_fmp`]
    mp_tac initial_fmp_push_venom_asm_rel >>
  (impl_tac >-
    (qpat_x_assum `asm_block_at _ _ (execute_plan _ _)` mp_tac >>
     simp[execute_plan_def, exec_stack_op_def])) >>
  strip_tac >> qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  gvs[venom_asm_rel_def, update_var_def] >>
  conj_tac
  >- (`plan_stack_rel lo (update_var out vs.vs_initial_fmp vs)
          (SNOC (Lit vs.vs_initial_fmp) ps.ps_stack) st'.as_stack` by
        (irule plan_stack_rel_update_var >>
         simp[EVERY_MEM] >> rpt strip_tac >>
         Cases_on `op` >> gvs[] >> metis_tac[]) >>
      qpat_x_assum `plan_stack_rel lo (update_var out vs.vs_initial_fmp vs)
          (SNOC (Lit vs.vs_initial_fmp) ps.ps_stack) st'.as_stack` mp_tac >>
      simp[update_var_def, plan_stack_rel_def, LENGTH_SNOC] >> strip_tac >>
      rw[plan_stack_rel_def, LENGTH_SNOC] >>
      first_x_assum (qspec_then `i` mp_tac) >>
      Cases_on `i` >>
      simp[REVERSE_SNOC, operand_val_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE])
  >- (`plan_spill_rel lo (update_var out vs.vs_initial_fmp vs)
          ps.ps_spilled st'.as_memory` by
        (irule plan_spill_rel_update_var >>
         simp[] >> rpt strip_tac >> Cases_on `op` >> gvs[] >>
         metis_tac[]) >>
      gvs[update_var_def])
QED

(* =========================================================================
   Rounded BUMP boundary
   ========================================================================= *)

Theorem dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem ceil32_div_mul[local]:
  !n. ceil32 n = ((n + 31) DIV 32) * 32
Proof
  gen_tac >>
  mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >>
  simp[] >> disch_then (qspec_then `n` strip_assume_tac) >>
  Cases_on `n MOD 32 = 0`
  >- (`n + 31 = n DIV 32 * 32 + 31` by decide_tac >>
      simp[venomLayoutTheory.ceil32_def, arithmeticTheory.DIV_MULT]) >>
  `0 < n MOD 32` by decide_tac >>
  `n + 31 = (n DIV 32 + 1) * 32 + (n MOD 32 - 1)` by decide_tac >>
  `n MOD 32 < 32` by (irule arithmeticTheory.MOD_LESS >> simp[]) >>
  `n MOD 32 - 1 < 32` by decide_tac >>
  `(n + 31) DIV 32 = n DIV 32 + 1` by
    (once_rewrite_tac [ASSUME ``n + 31 = (n DIV 32 + 1) * 32 + (n MOD 32 - 1)``] >>
     irule arithmeticTheory.DIV_MULT >> simp[]) >>
  rw[venomLayoutTheory.ceil32_def] >>
  decide_tac
QED

Theorem bump_round_mod_no_wrap[local]:
  !n. n <= dimword (:256) - 32 ==>
      32 * (((n + 31) MOD dimword (:256)) DIV 32) MOD dimword (:256) =
      ceil32 n MOD dimword (:256)
Proof
  rpt strip_tac >>
  `n + 31 < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  simp[arithmeticTheory.LESS_MOD, ceil32_div_mul,
       arithmeticTheory.MULT_COMM]
QED

Theorem bump_round_mod_wrap_zero[local]:
  !n. dimword (:256) - 32 < n /\ n < dimword (:256) ==>
      32 * (((n + 31) MOD dimword (:256)) DIV 32) MOD dimword (:256) = 0
Proof
  rpt strip_tac >>
  `dimword (:256) <= n + 31` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `n + 31 - dimword (:256) < 32` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `n + 31 - dimword (:256) < dimword (:256)` by
    (gvs[wordsTheory.dimword_def] >> decide_tac) >>
  `n + 31 = 1 * dimword (:256) + (n + 31 - dimword (:256))` by
    decide_tac >>
  `(n + 31) MOD dimword (:256) = n + 31 - dimword (:256)` by
    (irule arithmeticTheory.MOD_UNIQUE >>
     qexists `1` >> simp[]) >>
  simp[arithmeticTheory.LESS_DIV_EQ_ZERO]
QED


Theorem ceil32_wrap_mod_zero[local]:
  !n. dimword (:256) - 32 < n /\ n < dimword (:256) ==>
      ceil32 n MOD dimword (:256) = 0
Proof
  rpt strip_tac >>
  `(n + 31) DIV 32 = dimword (:256) DIV 32` by
    (rw[arithmeticTheory.DIV_EQ_X] >>
     gvs[wordsTheory.dimword_def] >> decide_tac) >>
  simp[ceil32_div_mul, wordsTheory.dimword_def]
QED

Theorem bump_round_word_correct:
  !sz:bytes32. bump_round_word sz = n2w (ceil32 (w2n sz))
Proof
  gen_tac >>
  PURE_REWRITE_TAC[bump_round_word_def] >>
  qmatch_goalsub_abbrev_tac `word_lsl q 5` >>
  `q = n2w (w2n q)` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[wordsTheory.word_lsl_n2w, wordsTheory.w2n_lsr,
       wordsTheory.word_add_def, Abbr `q`] >>
  Cases_on `w2n sz <= dimword (:256) - 32`
  >- metis_tac[bump_round_mod_no_wrap] >>
  `w2n sz < dimword (:256)` by simp[wordsTheory.w2n_lt] >>
  `dimword (:256) - 32 < w2n sz` by decide_tac >>
  metis_tac[bump_round_mod_wrap_zero, ceil32_wrap_mod_zero]
QED

Theorem word_of_bytes_encode_num_bytes_256[local]:
  !n. n < dimword (:256) ==>
      word_of_bytes F (0w:bytes32) (REVERSE (encode_num_bytes n)) = n2w n
Proof
  rpt strip_tac >>
  mp_tac (INST_TYPE [alpha |-> ``:256``]
            asmToBytecodeProofsTheory.word_of_bytes_encode_roundtrip) >>
  simp[dimindex_256, dividesTheory.divides_def] >>
  disch_then (qspec_then `(n2w n):bytes32` mp_tac) >>
  simp[wordsTheory.w2n_n2w]
QED

Theorem bump_emit_ops_asm_trace:
  !initial_fmp lo o2pc prog as sz base_val rest.
    asm_block_at prog as.as_pc (execute_plan initial_fmp bump_emit_ops) /\
    as.as_stack = sz :: base_val :: rest ==>
    asm_steps lo o2pc prog 8 as =
      AsmOK
        (as with <| as_stack := base_val + bump_round_word sz :: base_val :: rest;
                    as_pc := as.as_pc + 8 |>)
Proof
  rpt strip_tac >>
  fs[bump_emit_ops_def, execute_plan_def, exec_stack_op_def,
     asm_block_at_cons] >>
  `31 MOD dimword (:256) = 31` by
    (irule arithmeticTheory.LESS_MOD >> simp[wordsTheory.dimword_def]) >>
  `5 MOD dimword (:256) = 5` by
    (irule arithmeticTheory.LESS_MOD >> simp[wordsTheory.dimword_def]) >>
  `8 = SUC 7` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_def, asm_next_def,
       word_of_bytes_encode_num_bytes_256] >>
  `7 = SUC 6` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_binop_def, asm_next_def] >>
  `6 = SUC 5` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_def, asm_next_def,
       word_of_bytes_encode_num_bytes_256] >>
  `5 = SUC 4` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
       asm_binop_def, asm_next_def] >>
  `4 = SUC 3` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_def, asm_next_def,
       word_of_bytes_encode_num_bytes_256] >>
  `3 = SUC 2` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
       asm_binop_def, asm_next_def] >>
  `2 = SUC 1` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_step_compare_def, asm_step_bitwise_def,
       asm_step_memory_def, asm_step_control_def, asm_step_extcall_def,
       asm_step_copy_def, asm_step_context_def, asm_dup_def, asm_next_def,
       dup_table_def, dup_name_def, swap_table_def, log_table_def] >>
  `1 = SUC 0` by decide_tac >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def, asm_step_def, asm_step_op_def,
       asm_step_arith_def, asm_binop_def, asm_next_def,
       bump_round_word_def, word_of_bytes_encode_num_bytes_256,
       wordsTheory.dimword_def, wordsTheory.WORD_ADD_COMM]
QED


(* =========================================================================
   Connection: eval_operand vs operand_val
   ========================================================================= *)

Theorem eval_operand_var_eq:
  !x vs lo.
    operand_val vs lo (Var x) = eval_operand (Var x) vs
Proof
  simp[operand_val_def, eval_operand_def, lookup_var_def]
QED

Theorem eval_operand_lit_eq:
  !w vs lo.
    operand_val vs lo (Lit w) = eval_operand (Lit w) vs
Proof
  simp[operand_val_def, eval_operand_def]
QED

(* For non-Label operands, operand_val and eval_operand agree *)
Theorem operand_val_eq_eval:
  !vs lo op.
    ~is_label_operand op ==>
    operand_val vs lo op = eval_operand op vs
Proof
  Cases_on `op` >>
  simp[operand_val_def, eval_operand_def, lookup_var_def,
       is_label_operand_def]
QED

(* If both are SOME, values must agree (for non-Label operands) *)
Theorem operand_eval_agree:
  !vs lo op a v.
    ~is_label_operand op /\
    operand_val vs lo op = SOME a /\
    eval_operand op vs = SOME v ==>
    a = v
Proof
  rpt strip_tac >>
  imp_res_tac operand_val_eq_eval >> gvs[]
QED

(* =========================================================================
   Core helper: plan_stack_rel after pop-n / push-1-output
   ========================================================================= *)

Theorem plan_stack_rel_emit_step:
  !lo vs ps_stack asm_stack n out result.
    plan_stack_rel lo vs ps_stack asm_stack /\
    n <= LENGTH ps_stack /\
    EVERY (\op. case op of Var x => x <> out | _ => T)
      (TAKE (LENGTH ps_stack - n) ps_stack) ==>
    plan_stack_rel lo (update_var out result vs)
      (SNOC (Var out) (TAKE (LENGTH ps_stack - n) ps_stack))
      (result :: DROP n asm_stack)
Proof
  rpt strip_tac >>
  `plan_stack_rel lo vs
     (TAKE (LENGTH ps_stack - n) ps_stack)
     (DROP n asm_stack)` by
    (irule plan_stack_rel_pop >> simp[]) >>
  `plan_stack_rel lo (update_var out result vs)
     (TAKE (LENGTH ps_stack - n) ps_stack)
     (DROP n asm_stack)` by
    (irule plan_stack_rel_update_var >> simp[]) >>
  irule plan_stack_rel_push >> simp[] >>
  simp[operand_val_update_var_eq]
QED

(* =========================================================================
   exec_pure decomposition lemmas (extract update_var from exec_pureN)
   ========================================================================= *)

Theorem exec_pure2_update_var:
  !f inst vs vs' op1 op2 out.
    exec_pure2 f inst vs = OK vs' /\
    inst.inst_operands = [op1; op2] /\
    inst.inst_outputs = [out] ==>
    ?v1 v2.
      eval_operand op1 vs = SOME v1 /\
      eval_operand op2 vs = SOME v2 /\
      vs' = update_var out (f v1 v2) vs
Proof
  rw[exec_pure2_def] >> gvs[] >>
  Cases_on `eval_operand op1 vs` >> gvs[] >>
  Cases_on `eval_operand op2 vs` >> gvs[]
QED

Theorem exec_pure1_update_var:
  !f inst vs vs' op1 out.
    exec_pure1 f inst vs = OK vs' /\
    inst.inst_operands = [op1] /\
    inst.inst_outputs = [out] ==>
    ?v1.
      eval_operand op1 vs = SOME v1 /\
      vs' = update_var out (f v1) vs
Proof
  rw[exec_pure1_def] >> gvs[] >>
  Cases_on `eval_operand op1 vs` >> gvs[]
QED

Theorem exec_pure3_update_var:
  !f inst vs vs' op1 op2 op3 out.
    exec_pure3 f inst vs = OK vs' /\
    inst.inst_operands = [op1; op2; op3] /\
    inst.inst_outputs = [out] ==>
    ?v1 v2 v3.
      eval_operand op1 vs = SOME v1 /\
      eval_operand op2 vs = SOME v2 /\
      eval_operand op3 vs = SOME v3 /\
      vs' = update_var out (f v1 v2 v3) vs
Proof
  rw[exec_pure3_def] >> gvs[] >>
  Cases_on `eval_operand op1 vs` >> gvs[] >>
  Cases_on `eval_operand op2 vs` >> gvs[] >>
  Cases_on `eval_operand op3 vs` >> gvs[]
QED

(* =========================================================================
   Generic emit: 1 asm step that pops n and pushes 1 result

   This is the shared core for all pure emit lemmas.
   The caller provides:
   - The asm result of the step (must be AsmOK with stack = result :: DROP n)
   - The Venom result (must be update_var out result vs)
   ========================================================================= *)

Theorem emit_popn_push1_sim:
  !lo o2pc prog ps vs as n out result.
    venom_asm_rel lo ps vs as /\
    n <= LENGTH ps.ps_stack /\
    (* SSA freshness *)
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) /\
    (* Asm instruction executes: pops n, pushes result *)
    as.as_pc < LENGTH prog /\
    asm_step lo o2pc (EL as.as_pc prog) as =
      AsmOK (asm_next (as with as_stack := result :: DROP n as.as_stack))
    ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var out) (stack_pop n ps.ps_stack))
        (update_var out result vs) as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `asm_next (as with as_stack :=
    result :: DROP n as.as_stack)` >>
  rpt conj_tac
  >- (
    (* asm_steps 1 = AsmOK *)
    PURE_REWRITE_TAC[GSYM (EVAL ``SUC 0``)] >>
    simp[Once asm_steps_def] >>
    simp[asm_steps_def]
  )
  >- (
    simp[asm_next_def] >>
    qpat_x_assum `venom_asm_rel _ _ _ _`
      (strip_assume_tac o REWRITE_RULE[venom_asm_rel_def]) >>
    simp[venom_asm_rel_def, update_var_def] >>
    rpt conj_tac
    >- (
      simp[stack_push_def, stack_pop_def, GSYM update_var_def] >>
      irule plan_stack_rel_emit_step >> simp[] >>
      irule EVERY_TAKE >> simp[]
    )
    >- (
      simp[GSYM update_var_def] >>
      irule plan_spill_rel_update_var >> simp[]
    )
  )
  >- simp[asm_next_def]
QED

(* =========================================================================
   Stack top extraction from plan_stack_rel

   When plan stack ends with [opN; ...; op1], asm stack starts with
   v1 :: ... :: vN :: rest where vi = operand_val vs lo opi.
   ========================================================================= *)

Theorem asm_stack_top1_from_plan:
  !lo vs ps_stack as_stack op1 base.
    plan_stack_rel lo vs ps_stack as_stack /\
    ps_stack = base ++ [op1] ==>
    ?v1 rest.
      as_stack = v1 :: rest /\
      operand_val vs lo op1 = SOME v1
Proof
  rpt strip_tac >> fs[plan_stack_rel_def] >>
  Cases_on `as_stack` >> gvs[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
  simp[REVERSE_APPEND]
QED

Theorem asm_stack_top2_from_plan:
  !lo vs ps_stack as_stack op1 op2 base.
    plan_stack_rel lo vs ps_stack as_stack /\
    ps_stack = base ++ [op2; op1] ==>
    ?v1 v2 rest.
      as_stack = v1 :: v2 :: rest /\
      operand_val vs lo op1 = SOME v1 /\
      operand_val vs lo op2 = SOME v2
Proof
  rpt strip_tac >> fs[plan_stack_rel_def] >>
  Cases_on `as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  conj_tac
  >- (
    first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND]
  )
  >- (
    first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND] >> simp[EL_APPEND2]
  )
QED

Theorem asm_stack_top3_from_plan:
  !lo vs ps_stack as_stack op1 op2 op3 base.
    plan_stack_rel lo vs ps_stack as_stack /\
    ps_stack = base ++ [op3; op2; op1] ==>
    ?v1 v2 v3 rest.
      as_stack = v1 :: v2 :: v3 :: rest /\
      operand_val vs lo op1 = SOME v1 /\
      operand_val vs lo op2 = SOME v2 /\
      operand_val vs lo op3 = SOME v3
Proof
  rpt strip_tac >> fs[plan_stack_rel_def] >>
  Cases_on `as_stack` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  rpt conj_tac
  >- (
    first_x_assum (qspec_then `0` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND]
  )
  >- (
    first_x_assum (qspec_then `1` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND] >> simp[EL_APPEND2]
  )
  >- (
    first_x_assum (qspec_then `2` mp_tac) >> simp[] >>
    simp[REVERSE_APPEND] >> simp[EL_APPEND2]
  )
QED

(* Semantic relational boundary for the fixed two-output BUMP encoding. *)
Theorem bump_emit_sim_from_stack:
  !lo o2pc prog initial_fmp ps vs as rest ptr_out next_out base_val sz.
    venom_asm_rel lo ps vs as /\
    as.as_stack = sz :: base_val :: rest /\
    ptr_out <> next_out /\
    EVERY (\op. case op of Var x => x <> ptr_out /\ x <> next_out | _ => T)
      ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> ptr_out /\ x <> next_out | _ => T) /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp bump_emit_ops) ==>
    ?as'.
      asm_steps lo o2pc prog 8 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var next_out)
             (stack_push (Var ptr_out) (stack_pop 2 ps.ps_stack)))
        (update_var next_out (base_val + n2w (ceil32 (w2n sz)))
          (update_var ptr_out base_val vs)) as' /\
      as'.as_pc = as.as_pc + 8
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac
    `as with <| as_stack :=
       base_val + bump_round_word sz :: base_val :: rest;
       as_pc := as.as_pc + 8 |>` >>
  conj_tac
  >- metis_tac[bump_emit_ops_asm_trace] >>
  conj_tac
  >- (`plan_stack_rel lo vs (stack_pop 2 ps.ps_stack) rest` by
        (qspecl_then [`lo`, `vs`, `ps.ps_stack`, `as.as_stack`, `2`]
           mp_tac plan_stack_rel_pop >>
         impl_tac
         >- (fs[venom_asm_rel_def] >>
             imp_res_tac plan_stack_rel_length >> simp[]) >>
         simp[stack_pop_def]) >>
      `plan_stack_rel lo (update_var ptr_out base_val vs)
         (stack_pop 2 ps.ps_stack) rest` by
        (irule plan_stack_rel_update_var >>
         conj_tac
         >- (simp[stack_pop_def] >> irule EVERY_TAKE >>
             qpat_assum `EVERY _ ps.ps_stack` mp_tac >>
             PURE_REWRITE_TAC[EVERY_MEM] >> rpt strip_tac >>
             qpat_assum `!e. MEM e ps.ps_stack ==> _`
               (qspec_then `e` mp_tac) >>
             Cases_on `e` >> gvs[] >> res_tac >> gvs[])
         >- first_assum ACCEPT_TAC) >>
      `plan_stack_rel lo (update_var ptr_out base_val vs)
         (stack_push (Var ptr_out) (stack_pop 2 ps.ps_stack))
         (base_val :: rest)` by
        (qspecl_then [`lo`, `update_var ptr_out base_val vs`,
          `stack_pop 2 ps.ps_stack`, `rest`, `Var ptr_out`, `base_val`]
          mp_tac plan_stack_rel_push >>
         simp[stack_push_def, operand_val_update_var_eq]) >>
      `plan_stack_rel lo
         (update_var next_out (base_val + n2w (ceil32 (w2n sz)))
           (update_var ptr_out base_val vs))
         (stack_push (Var ptr_out) (stack_pop 2 ps.ps_stack))
         (base_val :: rest)` by
        (irule plan_stack_rel_update_var >> conj_tac
         >- (simp[stack_push_def, stack_pop_def] >>
             irule EVERY_TAKE >>
             qpat_assum `EVERY _ ps.ps_stack` mp_tac >>
             PURE_REWRITE_TAC[EVERY_MEM] >> rpt strip_tac >>
             qpat_assum `!e. MEM e ps.ps_stack ==> _`
               (qspec_then `e` mp_tac) >>
             Cases_on `e` >> gvs[] >> res_tac >> gvs[])
         >- first_assum ACCEPT_TAC) >>
      `plan_stack_rel lo
         (update_var next_out (base_val + n2w (ceil32 (w2n sz)))
           (update_var ptr_out base_val vs))
         (stack_push (Var next_out)
           (stack_push (Var ptr_out) (stack_pop 2 ps.ps_stack)))
         (base_val + n2w (ceil32 (w2n sz)) :: base_val :: rest)` by
        (qspecl_then [`lo`,
          `update_var next_out (base_val + n2w (ceil32 (w2n sz)))
             (update_var ptr_out base_val vs)`,
          `stack_push (Var ptr_out) (stack_pop 2 ps.ps_stack)`,
          `base_val :: rest`, `Var next_out`,
          `base_val + n2w (ceil32 (w2n sz))`]
          mp_tac plan_stack_rel_push >>
         simp[stack_push_def, operand_val_update_var_eq]) >>
      qpat_x_assum `venom_asm_rel _ _ _ _`
        (strip_assume_tac o REWRITE_RULE[venom_asm_rel_def]) >>
      `plan_spill_rel lo (update_var ptr_out base_val vs)
         ps.ps_spilled as.as_memory` by
        (qspecl_then [`lo`, `vs`, `ps.ps_spilled`, `as.as_memory`,
          `ptr_out`, `base_val`] mp_tac plan_spill_rel_update_var >>
         impl_tac
         >- (conj_tac
             >- first_assum ACCEPT_TAC
             >- (rpt strip_tac >>
                 qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
                   (qspec_then `op` mp_tac) >>
                 Cases_on `op` >> gvs[])) >>
         simp[]) >>
      `plan_spill_rel lo
         (update_var next_out (base_val + n2w (ceil32 (w2n sz)))
           (update_var ptr_out base_val vs))
         ps.ps_spilled as.as_memory` by
        (qspecl_then [`lo`, `update_var ptr_out base_val vs`,
          `ps.ps_spilled`, `as.as_memory`, `next_out`,
          `base_val + n2w (ceil32 (w2n sz))`]
          mp_tac plan_spill_rel_update_var >>
         impl_tac
         >- (conj_tac
             >- first_assum ACCEPT_TAC
             >- (rpt strip_tac >>
                 qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
                   (qspec_then `op` mp_tac) >>
                 Cases_on `op` >> gvs[])) >>
         simp[]) >>
      simp[venom_asm_rel_def, bump_round_word_correct] >>
      conj_tac >- simp[update_var_def] >>
      simp[update_var_def]) >>
  simp[]
QED

(* Syntactic planner-stack wrapper retained for existing consumers. *)
Theorem bump_emit_sim:
  !lo o2pc prog initial_fmp ps vs as stk base_op size_op
   ptr_out next_out base_val sz.
    venom_asm_rel lo ps vs as /\
    ps.ps_stack = stk ++ [base_op; size_op] /\
    operand_val vs lo base_op = SOME base_val /\
    operand_val vs lo size_op = SOME sz /\
    ptr_out <> next_out /\
    EVERY (\op. case op of Var x => x <> ptr_out /\ x <> next_out | _ => T)
      ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> ptr_out /\ x <> next_out | _ => T) /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp bump_emit_ops) ==>
    ?as'.
      asm_steps lo o2pc prog 8 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var next_out)
             (stack_push (Var ptr_out) (stack_pop 2 ps.ps_stack)))
        (update_var next_out (base_val + n2w (ceil32 (w2n sz)))
          (update_var ptr_out base_val vs)) as' /\
      as'.as_pc = as.as_pc + 8
Proof
  rpt gen_tac >> strip_tac >>
  `?rest. as.as_stack = sz :: base_val :: rest` by
    (`?v1 v2 rest.
        as.as_stack = v1 :: v2 :: rest /\
        operand_val vs lo size_op = SOME v1 /\
        operand_val vs lo base_op = SOME v2` by
       (irule asm_stack_top2_from_plan >>
        fs[venom_asm_rel_def] >> metis_tac[]) >>
     gvs[]) >>
  irule bump_emit_sim_from_stack >>
  simp[] >> qexists_tac `initial_fmp` >> simp[]
QED

(* =========================================================================
   Pure binary emit simulation (exec_pure2 / asm_binop)

   Covers: ADD, SUB, MUL, DIV, SDIV, MOD, SMOD, EXP, LT, GT, SLT, SGT,
           EQ, AND, OR, XOR, SHL, SHR, SAR, SIGNEXTEND, BYTE
   ========================================================================= *)

Theorem emit_pure2_sim:
  !lo o2pc prog ps vs as f name inst op1 op2 out vs' base.
    venom_asm_rel lo ps vs as /\
    inst.inst_operands = [op1; op2] /\
    inst.inst_outputs = [out] /\
    ~is_label_operand op1 /\ ~is_label_operand op2 /\
    (* Plan stack has operands at top *)
    ps.ps_stack = base ++ [op2; op1] /\
    (* SSA: output variable fresh *)
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) /\
    (* Asm instruction *)
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    asm_step_op o2pc name as = asm_binop f as /\
    (* Venom execution *)
    exec_pure2 f inst vs = OK vs' ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var out) (stack_pop 2 ps.ps_stack))
        vs' as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exec_pure2_update_var >> strip_tac >>
  (* Get asm stack top 2 = operand values *)
  `?a b rest. as.as_stack = a :: b :: rest /\
    operand_val vs lo op1 = SOME a /\
    operand_val vs lo op2 = SOME b` by (
    irule asm_stack_top2_from_plan >>
    fs[venom_asm_rel_def] >>
    metis_tac[]
  ) >>
  (* Bridge operand_val to eval_operand *)
  `a = v1` by metis_tac[operand_eval_agree] >>
  `b = v2` by metis_tac[operand_eval_agree] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* Now apply the generic emit sim *)
  irule emit_popn_push1_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >>
  simp[asm_step_def, asm_binop_def]
QED

(* =========================================================================
   Pure unary emit simulation (exec_pure1 / asm_unop)
   ========================================================================= *)

Theorem emit_pure1_sim:
  !lo o2pc prog ps vs as f name inst op1 out vs' base.
    venom_asm_rel lo ps vs as /\
    inst.inst_operands = [op1] /\
    inst.inst_outputs = [out] /\
    ~is_label_operand op1 /\
    (* Plan stack has operand at top *)
    ps.ps_stack = base ++ [op1] /\
    (* SSA: output variable fresh *)
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) /\
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    asm_step_op o2pc name as = asm_unop f as /\
    exec_pure1 f inst vs = OK vs' ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var out) (stack_pop 1 ps.ps_stack))
        vs' as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exec_pure1_update_var >> strip_tac >>
  `?a rest. as.as_stack = a :: rest /\
    operand_val vs lo op1 = SOME a` by (
    irule asm_stack_top1_from_plan >>
    fs[venom_asm_rel_def] >>
    metis_tac[]
  ) >>
  `a = v1` by metis_tac[operand_eval_agree] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  irule emit_popn_push1_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >>
  simp[asm_step_def, asm_unop_def]
QED

(* =========================================================================
   Pure ternary emit simulation (exec_pure3 / asm_ternop)
   ========================================================================= *)

Theorem emit_pure3_sim:
  !lo o2pc prog ps vs as f name inst op1 op2 op3 out vs' base.
    venom_asm_rel lo ps vs as /\
    inst.inst_operands = [op1; op2; op3] /\
    inst.inst_outputs = [out] /\
    ~is_label_operand op1 /\ ~is_label_operand op2 /\ ~is_label_operand op3 /\
    (* Plan stack has operands at top *)
    ps.ps_stack = base ++ [op3; op2; op1] /\
    (* SSA: output variable fresh *)
    EVERY (\op. case op of Var x => x <> out | _ => T) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
       case op of Var x => x <> out | _ => T) /\
    as.as_pc < LENGTH prog /\
    EL as.as_pc prog = AsmOp name /\
    asm_step_op o2pc name as = asm_ternop f as /\
    exec_pure3 f inst vs = OK vs' ==>
    ?as'.
      asm_steps lo o2pc prog 1 as = AsmOK as' /\
      venom_asm_rel lo
        (ps with ps_stack :=
           stack_push (Var out) (stack_pop 3 ps.ps_stack))
        vs' as' /\
      as'.as_pc = as.as_pc + 1
Proof
  rpt gen_tac >> strip_tac >>
  drule_all exec_pure3_update_var >> strip_tac >>
  `?a b c rest. as.as_stack = a :: b :: c :: rest /\
    operand_val vs lo op1 = SOME a /\
    operand_val vs lo op2 = SOME b /\
    operand_val vs lo op3 = SOME c` by (
    irule asm_stack_top3_from_plan >>
    fs[venom_asm_rel_def] >>
    metis_tac[]
  ) >>
  `a = v1` by metis_tac[operand_eval_agree] >>
  `b = v2` by metis_tac[operand_eval_agree] >>
  `c = v3` by metis_tac[operand_eval_agree] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  irule emit_popn_push1_sim >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >>
  simp[asm_step_def, asm_ternop_def]
QED

