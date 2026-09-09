(*
 * Prefix Execution — proving prefix stack ops always produce AsmOK
 *
 * Key theorem: prefix_sim — if prefix_wf holds and asm_block_at
 * places the instructions, then asm_steps produces AsmOK with
 * predictable stack length and side-field preservation.
 *)


Theory prefixExec
Ancestors
  asmSem asmIR planExec stackOpAsmSim stackOpSim stackPlanTypes blockSimHelpers prefixSim list rich_list arithmetic
Libs
  BasicProvers

(* ===== Stack op well-formedness ===== *)

Definition stack_op_wf_def:
  stack_op_wf lo (SOPush (Lit v)) n = (T, n + 1) /\
  stack_op_wf lo (SOPush (Var v')) n = (T, n) /\
  stack_op_wf lo (SOPush (Label l)) n =
    (IS_SOME (FLOOKUP lo l), n + 1) /\
  stack_op_wf lo (SOPop k) n = (k <= n, n - k) /\
  stack_op_wf lo (SODup k) n =
    (0 < k /\ k <= 16 /\ k <= n, n + 1) /\
  stack_op_wf lo (SOSwap k) n =
    (0 < k /\ k <= 16 /\ k < n, n) /\
  stack_op_wf lo (SOSpill off) n = (1 <= n, n - 1) /\
  stack_op_wf lo (SORestore off) n = (T, n + 1) /\
  stack_op_wf lo SOInitialFmp n = (T, n + 1) /\
  stack_op_wf lo (SOEmit name) n = (F, n) /\
  stack_op_wf lo (SOLabel lbl) n = (T, n) /\
  stack_op_wf lo (SOPushLabel lbl) n =
    (IS_SOME (FLOOKUP lo lbl), n + 1) /\
  stack_op_wf lo (SOPushOfst lbl delta) n =
    (IS_SOME (FLOOKUP lo lbl), n + 1) /\
  stack_op_wf lo (SOPoke v1 v2) n = (T, n)
End

Definition prefix_wf_def:
  prefix_wf lo n [] = T /\
  prefix_wf lo n (op :: rest) =
    let (ok, n') = stack_op_wf lo op n in
    ok /\ prefix_wf lo n' rest
End

Definition prefix_end_len_def:
  prefix_end_len lo n [] = n /\
  prefix_end_len lo n (op :: rest) =
    let (_, n') = stack_op_wf lo op n in
    prefix_end_len lo n' rest
End

(* ===== Side-field preservation for specific asm ops ===== *)

val asm_dispatch_ss =
  [asm_step_def, asm_step_op_def, asm_step_arith_def,
   asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def];

Theorem asm_step_mstore_side[local]:
  !lo o2pc (st:asm_state) st'.
    asm_step lo o2pc (AsmOp "MSTORE") st = AsmOK st' ==>
    st'.as_accounts = st.as_accounts /\
    st'.as_transient = st.as_transient /\
    st'.as_returndata = st.as_returndata /\
    st'.as_logs = st.as_logs
Proof
  rpt gen_tac >>
  Cases_on `st.as_stack` >>
  simp (asm_mstore_def :: LET_THM :: asm_next_def :: asm_dispatch_ss) >>
  Cases_on `t` >>
  simp[asm_mstore_def, LET_THM, asm_next_def] >>
  strip_tac >> gvs[]
QED

Theorem asm_step_mload_side[local]:
  !lo o2pc (st:asm_state) st'.
    asm_step lo o2pc (AsmOp "MLOAD") st = AsmOK st' ==>
    st'.as_accounts = st.as_accounts /\
    st'.as_transient = st.as_transient /\
    st'.as_returndata = st.as_returndata /\
    st'.as_logs = st.as_logs
Proof
  rpt gen_tac >>
  Cases_on `st.as_stack` >>
  simp (asm_mload_def :: LET_THM :: asm_next_def :: asm_dispatch_ss) >>
  strip_tac >> gvs[]
QED

(* ===== SOPop k: induction ===== *)

Theorem pop_k_exec_ok[local]:
  !k lo o2pc prog st.
    k <= LENGTH st.as_stack /\
    asm_block_at prog st.as_pc (REPLICATE k (AsmOp "POP")) ==>
    ?st'. asm_steps lo o2pc prog k st = AsmOK st' /\
          LENGTH st'.as_stack = LENGTH st.as_stack - k /\
          st'.as_pc = st.as_pc + k /\
          st'.as_accounts = st.as_accounts /\
          st'.as_transient = st.as_transient /\
          st'.as_returndata = st.as_returndata /\
          st'.as_logs = st.as_logs
Proof
  Induct >- simp[asm_steps_def] >>
  rpt strip_tac >>
  fs[Once REPLICATE, asm_block_at_cons] >>
  `st.as_stack <> []` by (Cases_on `st.as_stack` >> fs[]) >>
  drule asm_step_pop_ok >>
  disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
  qabbrev_tac `s1 = asm_next (st with as_stack := stk)` >>
  `asm_steps lo o2pc prog 1 st = AsmOK s1` by (
    `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
    simp[Once asm_steps_def] >>
    fs[asm_block_at_def] >>
    `st.as_pc < LENGTH prog` by decide_tac >>
    `EL st.as_pc prog = AsmOp "POP"` by (
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
    simp[asm_steps_def, Abbr `s1`]) >>
  first_x_assum (qspecl_then [`lo`, `o2pc`, `prog`, `s1`] mp_tac) >>
  impl_tac >- simp[Abbr `s1`, asm_next_def] >>
  strip_tac >>
  rename1 `asm_steps _ _ prog k s1 = AsmOK sfin` >>
  `SUC k = 1 + k` by simp[] >> pop_assum SUBST1_TAC >>
  `asm_steps lo o2pc prog (1 + k) st =
   asm_steps lo o2pc prog k s1` by
    (irule asm_steps_add_ok >> ASM_REWRITE_TAC[]) >>
  qexists_tac `sfin` >> simp[Abbr `s1`, asm_next_def]
QED

(* ===== Spill/Restore helpers ===== *)

(* SOSpill: push offset bytes then MSTORE *)
Theorem spill_exec_ok[local]:
  !lo o2pc prog (st:asm_state) off.
    1 <= LENGTH st.as_stack /\
    asm_block_at prog st.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MSTORE"] ==>
    ?st'. asm_steps lo o2pc prog 2 st = AsmOK st' /\
          LENGTH st'.as_stack = LENGTH st.as_stack - 1 /\
          st'.as_pc = st.as_pc + 2 /\
          st'.as_accounts = st.as_accounts /\
          st'.as_transient = st.as_transient /\
          st'.as_returndata = st.as_returndata /\
          st'.as_logs = st.as_logs
Proof
  rpt gen_tac >> strip_tac >> fs[asm_block_at_def] >>
  qpat_x_assum `!j. _` (fn th =>
    assume_tac (SPEC ``0:num`` th) >> assume_tac (SPEC ``1:num`` th)) >>
  rfs[] >>
  `2 = SUC (SUC 0)` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_push_ok, asm_next_def] >>
  qspecl_then [`lo`, `o2pc`,
    `st with <| as_stack :=
      word_of_bytes F 0w (REVERSE (encode_num_bytes off)) :: st.as_stack;
      as_pc := st.as_pc + 1 |>`] mp_tac asm_step_mstore_ok >>
  simp[] >> strip_tac >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def] >>
  imp_res_tac asm_step_mstore_side >> simp[]
QED

(* SORestore: push offset bytes then MLOAD *)
Theorem restore_exec_ok[local]:
  !lo o2pc prog (st:asm_state) off.
    asm_block_at prog st.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MLOAD"] ==>
    ?st'. asm_steps lo o2pc prog 2 st = AsmOK st' /\
          LENGTH st'.as_stack = LENGTH st.as_stack + 1 /\
          st'.as_pc = st.as_pc + 2 /\
          st'.as_accounts = st.as_accounts /\
          st'.as_transient = st.as_transient /\
          st'.as_returndata = st.as_returndata /\
          st'.as_logs = st.as_logs
Proof
  rpt gen_tac >> strip_tac >> fs[asm_block_at_def] >>
  qpat_x_assum `!j. _` (fn th =>
    assume_tac (SPEC ``0:num`` th) >> assume_tac (SPEC ``1:num`` th)) >>
  rfs[] >>
  `2 = SUC (SUC 0)` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_step_push_ok, asm_next_def] >>
  qspecl_then [`lo`, `o2pc`,
    `st with <| as_stack :=
      word_of_bytes F 0w (REVERSE (encode_num_bytes off)) :: st.as_stack;
      as_pc := st.as_pc + 1 |>`] mp_tac asm_step_mload_ok >>
  simp[] >> strip_tac >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def, asm_steps_def] >>
  imp_res_tac asm_step_mload_side >> simp[]
QED

(* ===== Per-stack-op execution ===== *)

Theorem stack_op_exec_ok:
  !initial_fmp lo o2pc prog op st n n'.
    is_prefix_op op /\
    stack_op_wf lo op n = (T, n') /\
    LENGTH st.as_stack = n /\
    asm_block_at prog st.as_pc (exec_stack_op initial_fmp op) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (exec_stack_op initial_fmp op)) st =
            AsmOK st' /\
          LENGTH st'.as_stack = n' /\
          st'.as_pc = st.as_pc + LENGTH (exec_stack_op initial_fmp op) /\
          st'.as_accounts = st.as_accounts /\
          st'.as_transient = st.as_transient /\
          st'.as_returndata = st.as_returndata /\
          st'.as_logs = st.as_logs
Proof
  Cases_on `op` >> simp[is_prefix_op_def, stack_op_wf_def, exec_stack_op_def]
  (* SOPush *)
  >- (
    Cases_on `o'` >>
    simp[stack_op_wf_def, exec_stack_op_def, asm_steps_def] >>
    rpt strip_tac >> (
      fs[asm_block_at_def] >>
      `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
      simp[Once asm_steps_def, asm_steps_def] >>
      fs[asm_step_def, asm_next_def] >>
      every_case_tac >> gvs[asm_next_def]
    )
  )
  (* SOPop *)
  >- (
    rpt strip_tac >> gvs[] >>
    drule_all pop_k_exec_ok >> simp[LENGTH_REPLICATE]
  )
  (* SOSwap *)
  >- (
    rpt gen_tac >> strip_tac >> fs[asm_block_at_def] >>
    `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
    simp[Once asm_steps_def, asm_steps_def] >>
    fs[asm_step_swap_ok, asm_next_def, LENGTH_LUPDATE]
  )
  (* SODup *)
  >- (
    rpt gen_tac >> strip_tac >>
    fs[asm_block_at_def] >>
    `n - 1 < 16 /\ n - 1 < LENGTH st.as_stack` by decide_tac >>
    qspecl_then [`lo`, `o2pc`, `n - 1`, `st`] mp_tac asm_step_dup_ok >>
    simp[] >> strip_tac >>
    `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
    simp[Once asm_steps_def, asm_steps_def] >>
    simp[asm_next_def]
  )
  (* SOSpill: use spill_exec_ok *)
  >- (rpt strip_tac >> gvs[] >> drule_all spill_exec_ok >> simp[])
  (* SORestore: use restore_exec_ok *)
  >- (rpt strip_tac >> drule_all restore_exec_ok >> simp[])
  (* SOInitialFmp: one concrete AsmPush of the caller-supplied value *)
  >- (
    rpt gen_tac >> strip_tac >> fs[asm_block_at_def] >>
    `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
    simp[Once asm_steps_def, asm_steps_def, asm_step_push_ok, asm_next_def]
  )
  (* SOLabel *)
  >- (
    rpt gen_tac >> strip_tac >> fs[asm_block_at_def] >>
    `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
    simp[Once asm_steps_def, asm_steps_def, asm_step_def, asm_next_def]
  )
  (* SOPushLabel *)
  >- (
    rpt gen_tac >> strip_tac >> fs[asm_block_at_def] >>
    `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
    simp[Once asm_steps_def, asm_steps_def, asm_step_def, asm_next_def] >>
    every_case_tac >> gvs[asm_next_def]
  )
  (* SOPushOfst *)
  >- (
    rpt gen_tac >> strip_tac >> fs[asm_block_at_def] >>
    `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
    simp[Once asm_steps_def, asm_steps_def, asm_step_def, asm_next_def] >>
    every_case_tac >> gvs[asm_next_def]
  )
QED

(* ===== Combined: prefix AsmOK + side preservation ===== *)

Theorem prefix_sim:
  !ops initial_fmp lo o2pc prog st n.
    prefix_wf lo n ops /\
    EVERY is_prefix_op ops /\
    LENGTH st.as_stack = n /\
    asm_block_at prog st.as_pc (FLAT (MAP (exec_stack_op initial_fmp) ops)) ==>
    ?st'. asm_steps lo o2pc prog
            (LENGTH (FLAT (MAP (exec_stack_op initial_fmp) ops))) st =
            AsmOK st' /\
          LENGTH st'.as_stack = prefix_end_len lo n ops /\
          st'.as_pc = st.as_pc + LENGTH (FLAT (MAP (exec_stack_op initial_fmp) ops)) /\
          st'.as_accounts = st.as_accounts /\
          st'.as_transient = st.as_transient /\
          st'.as_returndata = st.as_returndata /\
          st'.as_logs = st.as_logs
Proof
  Induct >- simp[prefix_wf_def, prefix_end_len_def, asm_steps_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[prefix_wf_def, prefix_end_len_def, EVERY_DEF] >>
  pairarg_tac >> gvs[] >>
  `asm_block_at prog st.as_pc (exec_stack_op initial_fmp h) /\
   asm_block_at prog (st.as_pc + LENGTH (exec_stack_op initial_fmp h))
     (FLAT (MAP (exec_stack_op initial_fmp) ops))` by
    fs[asm_block_at_append, FLAT, MAP] >>
  qspecl_then [`initial_fmp`, `lo`, `o2pc`, `prog`, `h`, `st`,
    `LENGTH st.as_stack`, `n'`] mp_tac stack_op_exec_ok >>
  simp[] >> strip_tac >>
  `asm_steps lo o2pc prog
     (LENGTH (exec_stack_op initial_fmp h) +
      LENGTH (FLAT (MAP (exec_stack_op initial_fmp) ops))) st =
   asm_steps lo o2pc prog
     (LENGTH (FLAT (MAP (exec_stack_op initial_fmp) ops))) st'` by
    (irule asm_steps_add_ok >> fs[]) >>
  first_x_assum (qspecl_then [`initial_fmp`, `lo`, `o2pc`, `prog`, `st'`] mp_tac) >>
  `LENGTH (exec_stack_op initial_fmp h) + st.as_pc =
   st.as_pc + LENGTH (exec_stack_op initial_fmp h)` by simp[] >>
  fs[] >> strip_tac >>
  rename1 `AsmOK sfin` >>
  qexists_tac `sfin` >>
  simp[FLAT, MAP] >> gvs[]
QED
