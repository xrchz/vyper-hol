(*
 * Stack Operation Simulation Lemmas
 *
 * Foundational lemmas for Venom->Asm correctness:
 * Each stack_op (from stackPlanGen) executed as asm instructions
 * preserves venom_asm_rel.
 *
 * Contents:
 *   - Table lookups: swap_table, dup_table roundtrip
 *   - asm_steps composition
 *   - plan_stack_rel maintenance under push/pop/swap/dup
 *
 * TOP-LEVEL:
 *   swap_table_lookup    -- ALOOKUP swap_table (swap_name n) = SOME n
 *   dup_table_lookup     -- ALOOKUP dup_table (dup_name (n+1)) = SOME n
 *   asm_steps_add        -- asm_steps (n+m) = asm_steps n >> asm_steps m
 *   plan_stack_rel_push  -- push preserves plan_stack_rel
 *   plan_stack_rel_pop   -- pop preserves plan_stack_rel
 *)


Theory stackOpSim
Ancestors
  asmSem planExec stackModel codegenRel list rich_list arithmetic
Libs
  BasicProvers

(* ===== Table Lookup Lemmas ===== *)

(* swap_name n produces a string that swap_table maps back to n *)
Theorem swap_table_lookup:
  !n. 1 <= n /\ n <= 16 ==>
    ALOOKUP swap_table (swap_name n) = SOME n
Proof
  rpt strip_tac >>
  `n < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (0)))))))))))))))))` by decide_tac >>
  pop_assum mp_tac >>
  PURE_REWRITE_TAC[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0] >>
  strip_tac >>
  gvs[swap_name_def, swap_table_def]
QED

(* dup_name (n+1) produces a string that dup_table maps to n.
   Note: dup_name is 1-indexed (DUP1..DUP16), dup_table is 0-indexed.
   do_dup uses SODup (dist+1), so n here is dist+1. *)
Theorem dup_table_lookup:
  !n. n <= 15 ==>
    ALOOKUP dup_table (dup_name (n + 1)) = SOME n
Proof
  rpt strip_tac >>
  `n < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (0))))))))))))))))` by decide_tac >>
  pop_assum mp_tac >>
  PURE_REWRITE_TAC[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0] >>
  strip_tac >>
  gvs[dup_name_def, dup_table_def]
QED

(* ===== Asm Steps Composition ===== *)

(* asm_steps composition: n + m steps = n steps then m steps *)
Theorem asm_steps_add:
  !lo o2pc prog n m s.
    asm_steps lo o2pc prog (n + m) s =
    case asm_steps lo o2pc prog n s of
      AsmOK s1 => asm_steps lo o2pc prog m s1
    | AsmHalt s1 => AsmHalt s1
    | AsmRevert s1 => AsmRevert s1
    | AsmFault s1 => AsmFault s1
    | AsmError e => AsmError e
Proof
  Induct_on `n`
  >- simp[asm_steps_def]
  >> rpt gen_tac >>
  `SUC n + m = SUC (n + m)` by decide_tac >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  simp[Once asm_steps_def] >>
  simp[Once asm_steps_def] >>
  IF_CASES_TAC >> simp[] >>
  CASE_TAC >> simp[]
QED

(* asm_steps 0 is identity *)
Theorem asm_steps_zero[simp]:
  !lo o2pc prog s. asm_steps lo o2pc prog 0 s = AsmOK s
Proof
  rw[asm_steps_def]
QED

(* If asm_steps n gives AsmOK, extending by m is just asm_steps m *)
Theorem asm_steps_add_ok:
  !lo o2pc prog n m s s1.
    asm_steps lo o2pc prog n s = AsmOK s1 ==>
    asm_steps lo o2pc prog (n + m) s =
    asm_steps lo o2pc prog m s1
Proof
  rw[asm_steps_add]
QED

(* ===== plan_stack_rel: Basic Properties ===== *)

(* Empty stacks are trivially related *)
Theorem plan_stack_rel_nil[simp]:
  !lo vs. plan_stack_rel lo vs [] []
Proof
  rw[plan_stack_rel_def]
QED

(* Push preserves plan_stack_rel when the pushed value matches *)
Theorem plan_stack_rel_push:
  !lo vs ps_stk as_stk op v.
    plan_stack_rel lo vs ps_stk as_stk /\
    operand_val vs lo op = SOME v ==>
    plan_stack_rel lo vs (SNOC op ps_stk) (v :: as_stk)
Proof
  rpt strip_tac >>
  gvs[plan_stack_rel_def, LET_THM, LENGTH_SNOC] >>
  rpt strip_tac >>
  Cases_on `i` >> simp[REVERSE_SNOC]
QED

(* Key list lemma: EL in REVERSE of TAKE *)
Theorem el_reverse_take:
  !i n (l:'a list).
    i < n /\ n <= LENGTH l ==>
    EL i (REVERSE (TAKE n l)) = EL (n - 1 - i) l
Proof
  rw[] >>
  `i < LENGTH (TAKE n l)` by simp[LENGTH_TAKE] >>
  simp[EL_REVERSE] >>
  `LENGTH (TAKE n l) = n` by simp[LENGTH_TAKE] >>
  `PRE (n - i) = n - (i + 1)` by decide_tac >>
  simp[EL_TAKE]
QED

(* Pop preserves plan_stack_rel: removing top n from both sides.
   plan stack: TAKE (len-n) removes the last n (TOS).
   asm stack:  DROP n removes the first n (TOS). *)
Theorem plan_stack_rel_pop:
  !lo vs ps_stk as_stk n.
    plan_stack_rel lo vs ps_stk as_stk /\
    n <= LENGTH ps_stk ==>
    plan_stack_rel lo vs
      (TAKE (LENGTH ps_stk - n) ps_stk)
      (DROP n as_stk)
Proof
  rpt strip_tac >>
  gvs[plan_stack_rel_def, LET_THM, LENGTH_TAKE, LENGTH_DROP] >>
  rpt strip_tac >>
  simp[el_reverse_take, EL_DROP] >>
  `i + n < LENGTH as_stk` by decide_tac >>
  first_x_assum (qspec_then `i + n` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[EL_REVERSE, LENGTH_REVERSE] >>
  `PRE (LENGTH as_stk - (i + n)) = LENGTH as_stk - (i + (n + 1))` by decide_tac >>
  simp[]
QED

(* plan_stack_rel extracts element at a given position *)
Theorem plan_stack_rel_el:
  !lo vs ps_stk as_stk i.
    plan_stack_rel lo vs ps_stk as_stk /\
    i < LENGTH ps_stk ==>
    operand_val vs lo (EL i (REVERSE ps_stk)) = SOME (EL i as_stk)
Proof
  rw[plan_stack_rel_def] >> res_tac
QED

(* plan_stack_rel gives LENGTH equality *)
Theorem plan_stack_rel_length:
  !lo vs ps_stk as_stk.
    plan_stack_rel lo vs ps_stk as_stk ==>
    LENGTH ps_stk = LENGTH as_stk
Proof
  rw[plan_stack_rel_def]
QED

(* plan_stack_rel at position 0: LAST of plan stack = HD of asm stack *)
Theorem plan_stack_rel_hd:
  !lo vs ps_stk as_stk.
    plan_stack_rel lo vs ps_stk as_stk /\ ps_stk <> [] ==>
    operand_val vs lo (LAST ps_stk) = SOME (HD as_stk)
Proof
  rpt strip_tac >>
  `0 < LENGTH ps_stk` by (Cases_on `ps_stk` >> fs[]) >>
  imp_res_tac plan_stack_rel_length >>
  `0 < LENGTH as_stk` by decide_tac >>
  qspecl_then [`lo`,`vs`,`ps_stk`,`as_stk`,`0`] mp_tac plan_stack_rel_el >>
  simp[] >> disch_then (fn th => REWRITE_TAC[GSYM th]) >>
  simp[HD_REVERSE]
QED

(* Swap preserves plan_stack_rel.
   Plan side: stack_swap dist swaps top (last) with element at depth dist.
   Asm side: LUPDATE swaps index 0 (TOS) with index dist.
   REVERSE maps plan's top (last) to asm's index 0, and
   plan's (top - dist) to asm's index dist. *)
Theorem plan_stack_rel_swap:
  !lo vs ps_stk as_stk dist.
    plan_stack_rel lo vs ps_stk as_stk /\
    0 < dist /\ dist < LENGTH ps_stk ==>
    plan_stack_rel lo vs (stack_swap dist ps_stk)
      (LUPDATE (EL dist as_stk) 0
        (LUPDATE (HD as_stk) dist as_stk))
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac plan_stack_rel_length >>
  fs[plan_stack_rel_def, LET_THM, stack_swap_def] >>
  simp[LENGTH_LUPDATE] >>
  rpt strip_tac >>
  `i < LENGTH as_stk` by simp[] >>
  simp[EL_LUPDATE] >>
  `i < LENGTH (LUPDATE (EL (LENGTH as_stk - 1) ps_stk)
                (LENGTH as_stk - 1 - dist)
                (LUPDATE (EL (LENGTH as_stk - 1 - dist) ps_stk)
                  (LENGTH as_stk - 1) ps_stk))` by
    simp[LENGTH_LUPDATE] >>
  simp[EL_REVERSE, LENGTH_LUPDATE, EL_LUPDATE] >>
  `PRE (LENGTH as_stk - i) = LENGTH as_stk - (i + 1)` by decide_tac >>
  simp[] >>
  Cases_on `i = 0`
  >- (
    gvs[] >>
    `LENGTH as_stk - 1 <> LENGTH as_stk - 1 - dist` by decide_tac >>
    simp[] >>
    first_x_assum (qspec_then `dist` mp_tac) >>
    simp[EL_REVERSE] >>
    `PRE (LENGTH as_stk - dist) = LENGTH as_stk - (dist + 1)` by
      decide_tac >>
    simp[]
  ) >>
  Cases_on `i = dist`
  >- (
    gvs[] >>
    `LENGTH as_stk - (dist + 1) = LENGTH as_stk - 1 - dist` by
      decide_tac >>
    simp[] >>
    first_x_assum (qspec_then `0` mp_tac) >>
    simp[EL_REVERSE] >>
    `PRE (LENGTH as_stk) = LENGTH as_stk - 1` by decide_tac >>
    simp[] >>
    Cases_on `as_stk` >> fs[]
  ) >>
  `LENGTH as_stk - (i + 1) <> LENGTH as_stk - 1` by decide_tac >>
  `LENGTH as_stk - (i + 1) <> LENGTH as_stk - 1 - dist` by decide_tac >>
  simp[] >>
  first_x_assum (qspec_then `i` mp_tac) >>
  simp[EL_REVERSE]
QED

(* ===== asm_block_at: Decomposition ===== *)

(* asm_block_at decomposes over append *)
Theorem asm_block_at_append:
  !prog pc xs ys.
    asm_block_at prog pc (xs ++ ys) <=>
    asm_block_at prog pc xs /\
    asm_block_at prog (pc + LENGTH xs) ys
Proof
  rpt gen_tac >> simp[asm_block_at_def, EL_APPEND_EQN] >>
  eq_tac >> rpt strip_tac >> gvs[]
  >- (first_x_assum (qspec_then `j + LENGTH xs` mp_tac) >> simp[])
  >> Cases_on `j < LENGTH xs`
  >- (first_x_assum (qspec_then `j` mp_tac) >> simp[])
  >> first_x_assum (qspec_then `j - LENGTH xs` mp_tac) >> simp[]
QED

(* asm_block_at with cons *)
Theorem asm_block_at_cons:
  !prog pc x xs.
    asm_block_at prog pc (x::xs) <=>
    pc < LENGTH prog /\ EL pc prog = x /\
    asm_block_at prog (pc + 1) xs
Proof
  rpt gen_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [CONS_APPEND])) >>
  rewrite_tac[asm_block_at_append] >> simp[asm_block_at_def] >>
  eq_tac >> simp[]
QED

(* asm_block_at empty is trivial *)
Theorem asm_block_at_nil[simp]:
  !prog pc. asm_block_at prog pc [] <=> pc <= LENGTH prog
Proof
  rw[asm_block_at_def]
QED

(* execute_plan distributes over append *)
Theorem execute_plan_append:
  !initial_fmp ops1 ops2. execute_plan initial_fmp (ops1 ++ ops2) =
              execute_plan initial_fmp ops1 ++ execute_plan initial_fmp ops2
Proof
  rw[execute_plan_def, MAP_APPEND, FLAT_APPEND]
QED

(* ===== venom_asm_rel: Decomposition ===== *)

(* venom_asm_rel with updated stack (plan state and asm state):
   if the non-stack parts are unchanged, only need to re-establish
   plan_stack_rel for the new stacks. *)
Theorem venom_asm_rel_update_stack:
  !lo ps vs as new_ps_stk new_as_stk.
    venom_asm_rel lo ps vs as /\
    plan_stack_rel lo vs new_ps_stk new_as_stk ==>
    venom_asm_rel lo (ps with ps_stack := new_ps_stk)
                     vs
                     (as with as_stack := new_as_stk)
Proof
  rw[venom_asm_rel_def] >> gvs[plan_spill_rel_def, memory_rel_def]
QED

(* ===== PC Advance ===== *)

(* Every asm_step that returns AsmOK advances PC by 1,
   EXCEPT AsmOp "JUMP" and AsmOp "JUMPI" which set PC to target. *)

(* Helper: tactic for proving pc advance through asm_next *)
val asm_next_pc_tac =
  every_case_tac >> gvs[asm_next_def, LET_THM] >>
  every_case_tac >> gvs[];

(* Per-group PC advance lemmas (local — only used to compose asm_step_pc) *)
Theorem asm_step_arith_pc[local]:
  !name s1 s2. asm_step_arith name s1 = SOME (AsmOK s2) ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_step_arith_def, asm_binop_def, asm_unop_def, asm_ternop_def] >>
  asm_next_pc_tac
QED

Theorem asm_step_compare_pc[local]:
  !name s1 s2. asm_step_compare name s1 = SOME (AsmOK s2) ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_step_compare_def, asm_binop_def, asm_unop_def] >> asm_next_pc_tac
QED

Theorem asm_step_bitwise_pc[local]:
  !name s1 s2. asm_step_bitwise name s1 = SOME (AsmOK s2) ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_step_bitwise_def, asm_binop_def, asm_unop_def] >> asm_next_pc_tac
QED

Theorem asm_step_memory_pc[local]:
  !name s1 s2. asm_step_memory name s1 = SOME (AsmOK s2) ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rpt gen_tac >> simp[asm_step_memory_def] >>
  rpt IF_CASES_TAC >> simp[] >> strip_tac >>
  gvs[asm_mload_def, asm_mstore_def, asm_mstore8_def,
      asm_sload_def, asm_sstore_def,
      asm_tload_def, asm_tstore_def, asm_sha3_def, asm_state_unop_def,
      asm_binop_def, asm_pop_def, asm_push_val_def, asm_copy_to_mem_def,
      asm_mcopy_def, asm_next_def, LET_THM] >>
  every_case_tac >> gvs[]
QED

Theorem asm_step_control_pc[local]:
  !o2pc name s1 s2. asm_step_control o2pc name s1 = SOME (AsmOK s2) /\
    name <> "JUMP" /\ name <> "JUMPI" ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_step_control_def, asm_return_op_def, asm_revert_op_def] >>
  asm_next_pc_tac
QED

Theorem asm_step_extcall_pc[local]:
  !name s1 s2. asm_step_extcall name s1 = SOME (AsmOK s2) ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_step_extcall_def, asm_exec_call_def, asm_exec_staticcall_def,
     asm_exec_delegatecall_def, asm_exec_create_def, asm_exec_create2_def,
     asm_selfdestruct_def, extract_asm_result_def, asm_to_tx_params_def,
     asm_next_def, LET_THM] >>
  asm_next_pc_tac
QED

Theorem asm_step_copy_pc[local]:
  !name s1 s2. asm_step_copy name s1 = SOME (AsmOK s2) ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_step_copy_def, asm_copy_to_mem_def, asm_returndatacopy_def,
     asm_extcodecopy_def, asm_next_def, LET_THM] >>
  asm_next_pc_tac
QED

Theorem asm_step_context_pc[local]:
  !name s1 s2. asm_step_context name s1 = SOME (AsmOK s2) ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_step_context_def, asm_push_val_def, asm_state_unop_def,
     asm_next_def, LET_THM] >>
  simp[] >>
  every_case_tac >> gvs[]
QED

Theorem asm_dup_pc[local]:
  !n s1 s2. asm_dup n s1 = AsmOK s2 ==> s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_dup_def, asm_next_def] >> asm_next_pc_tac
QED

Theorem asm_swap_pc[local]:
  !n s1 s2. asm_swap n s1 = AsmOK s2 ==> s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_swap_def, asm_next_def, LET_THM] >> asm_next_pc_tac
QED

Theorem asm_log_pc[local]:
  !n s1 s2. asm_log n s1 = AsmOK s2 ==> s2.as_pc = s1.as_pc + 1
Proof
  rw[asm_log_def, asm_next_def, LET_THM] >> asm_next_pc_tac
QED

(* Main per-step PC advance theorem *)
Theorem asm_step_pc_advance:
  !lo o2pc inst s1 s2.
    asm_step lo o2pc inst s1 = AsmOK s2 /\
    inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI" ==>
    s2.as_pc = s1.as_pc + 1
Proof
  rpt gen_tac >> Cases_on `inst` >>
  simp[asm_step_def, asm_next_def] >>
  strip_tac
  (* AsmOp: dispatch through asm_step_op *)
  >- (fs[asm_step_op_def] >>
      reverse (Cases_on `asm_step_arith s s1`) >-
        (gvs[] >> imp_res_tac asm_step_arith_pc >> gvs[]) >>
      reverse (Cases_on `asm_step_compare s s1`) >-
        (gvs[] >> imp_res_tac asm_step_compare_pc >> gvs[]) >>
      reverse (Cases_on `asm_step_bitwise s s1`) >-
        (gvs[] >> imp_res_tac asm_step_bitwise_pc >> gvs[]) >>
      reverse (Cases_on `asm_step_memory s s1`) >-
        (gvs[] >> imp_res_tac asm_step_memory_pc >> gvs[]) >>
      reverse (Cases_on `asm_step_control o2pc s s1`) >-
        (gvs[] >> imp_res_tac asm_step_control_pc >> gvs[]) >>
      reverse (Cases_on `asm_step_extcall s s1`) >-
        (gvs[] >> imp_res_tac asm_step_extcall_pc >> gvs[]) >>
      reverse (Cases_on `asm_step_copy s s1`) >-
        (gvs[] >> imp_res_tac asm_step_copy_pc >> gvs[]) >>
      reverse (Cases_on `asm_step_context s s1`) >-
        (gvs[] >> imp_res_tac asm_step_context_pc >> gvs[]) >>
      reverse (Cases_on `ALOOKUP dup_table s`) >-
        (gvs[] >> imp_res_tac asm_dup_pc >> gvs[]) >>
      reverse (Cases_on `ALOOKUP swap_table s`) >-
        (gvs[] >> imp_res_tac asm_swap_pc >> gvs[]) >>
      reverse (Cases_on `ALOOKUP log_table s`) >-
        (gvs[] >> imp_res_tac asm_log_pc >> gvs[]) >>
      gvs[])
  (* Non-AsmOp cases: FLOOKUP + asm_next *)
  >> every_case_tac >> gvs[]
QED

(* Multi-step PC advance: if we execute n AsmOK steps over instructions
   placed by asm_block_at (none of which are JUMP/JUMPI),
   PC advances by exactly n. *)
Theorem asm_steps_pc_advance:
  !n lo o2pc prog s1 s2 insts.
    asm_steps lo o2pc prog n s1 = AsmOK s2 /\
    asm_block_at prog s1.as_pc insts /\
    n <= LENGTH insts /\
    EVERY (\i. i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI") insts ==>
    s2.as_pc = s1.as_pc + n
Proof
  Induct >- simp[asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  fs[Once asm_steps_def] >>
  `~(s1.as_pc >= LENGTH prog)` by
    (fs[asm_block_at_def] >> decide_tac) >>
  fs[] >>
  Cases_on `asm_step lo o2pc (EL s1.as_pc prog) s1` >> fs[] >>
  (* Remaining AsmOK case *)
  rename1 `asm_step _ _ _ s1 = AsmOK s_mid` >>
  `EL s1.as_pc prog = EL 0 insts` by
    (fs[asm_block_at_def] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `EL 0 insts <> AsmOp "JUMP" /\ EL 0 insts <> AsmOp "JUMPI"` by
    (Cases_on `insts` >> fs[EVERY_DEF]) >>
  `s_mid.as_pc = s1.as_pc + 1` by
    metis_tac[asm_step_pc_advance] >>
  `asm_block_at prog s_mid.as_pc (TL insts)` by
    (Cases_on `insts` >> fs[asm_block_at_cons]) >>
  `EVERY (\i. i <> AsmOp "JUMP" /\ i <> AsmOp "JUMPI") (TL insts)` by
    (Cases_on `insts` >> fs[]) >>
  `n <= LENGTH (TL insts)` by
    (Cases_on `insts` >> fs[]) >>
  first_x_assum drule >> disch_then drule >>
  simp[]
QED
