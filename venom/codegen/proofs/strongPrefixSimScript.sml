(*
 * Strong Prefix Simulation: stack_op list preserves full venom_asm_rel.
 *
 * prefix_sim only preserves side fields and stack LENGTH.
 * This theory tracks plan_stack_rel, plan_spill_rel, and memory_rel
 * through each stack operation.
 *
 * SCOPE: "simple" stack ops that only affect the stack (not memory):
 *   SOPush (Lit/Label), SOPop, SOSwap, SODup, SOLabel, SOPushLabel
 *
 * Key results:
 *   simple_op_venom_asm_rel  — single op preserves venom_asm_rel
 *   simple_prefix_venom_asm_rel — op list preserves venom_asm_rel
 *)

Theory strongPrefixSim
Ancestors
  codegenRel stackOpSim stackOpAsmSim prefixExec
  asmSem stackPlanTypes planExec stackModel
  asmToBytecodeProofs blockSimHelpers planWf
  instSimHelpers
  list rich_list
Libs BasicProvers

(* =========================================================================
   Memory helpers
   ========================================================================= *)

Theorem read_byte_expand:
  !i n mem. read_byte i (asm_expand_memory n mem) = read_byte i mem
Proof
  rpt gen_tac >>
  simp[asm_expand_memory_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  simp[read_byte_def] >>
  Cases_on `i < LENGTH mem`
  >- simp[EL_APPEND1]
  >> (Cases_on `i < LENGTH mem + (32 * ((n + 31) DIV 32) - LENGTH mem)` >>
      simp[EL_APPEND2, LENGTH_REPLICATE, EL_REPLICATE])
QED

Theorem memory_rel_expand:
  !alloc vm am n.
    memory_rel alloc vm am ==>
    memory_rel alloc vm (asm_expand_memory n am)
Proof
  rw[memory_rel_def, read_byte_expand]
QED

(* =========================================================================
   Plan state transformation for simple stack ops
   ========================================================================= *)

Definition apply_simple_op_def:
  apply_simple_op lo (SOPush (Lit v)) ps =
    ps with ps_stack := SNOC (Lit v) ps.ps_stack /\
  apply_simple_op lo (SOPush (Var _)) ps = ps /\
  apply_simple_op lo (SOPush (Label l)) ps =
    ps with ps_stack := SNOC (Label l) ps.ps_stack /\
  apply_simple_op lo (SOPop k) ps =
    ps with ps_stack := TAKE (LENGTH ps.ps_stack - k) ps.ps_stack /\
  apply_simple_op lo (SOSwap k) ps =
    ps with ps_stack := stack_swap k ps.ps_stack /\
  apply_simple_op lo (SODup k) ps =
    ps with ps_stack :=
      SNOC (EL (LENGTH ps.ps_stack - k) ps.ps_stack) ps.ps_stack /\
  apply_simple_op lo (SOLabel _) ps = ps /\
  apply_simple_op lo (SOPushLabel l) ps =
    ps with ps_stack := SNOC (Label l) ps.ps_stack /\
  apply_simple_op lo (SOPushOfst l d) ps =
    ps with ps_stack :=
      SNOC (Lit (n2w (THE (FLOOKUP lo l) + d))) ps.ps_stack /\
  apply_simple_op lo (SOSpill _) ps = ps /\
  apply_simple_op lo (SORestore _) ps = ps /\
  apply_simple_op lo (SOEmit _) ps = ps /\
  apply_simple_op lo SOInitialFmp ps = ps /\
  apply_simple_op lo (SOPoke _ _) ps = ps
End

Definition apply_simple_ops_def:
  apply_simple_ops lo [] ps = ps /\
  apply_simple_ops lo (op::rest) ps =
    apply_simple_ops lo rest (apply_simple_op lo op ps)
End

(* Simple op: doesn't modify memory, is a prefix op *)
Definition is_simple_stack_op_def:
  is_simple_stack_op (SOPush (Lit _)) = T /\
  is_simple_stack_op (SOPush (Var _)) = F /\
  is_simple_stack_op (SOPush (Label _)) = T /\
  is_simple_stack_op (SOPop _) = T /\
  is_simple_stack_op (SOSwap _) = T /\
  is_simple_stack_op (SODup _) = T /\
  is_simple_stack_op (SOPoke _ _) = F /\
  is_simple_stack_op (SOSpill _) = F /\
  is_simple_stack_op (SORestore _) = F /\
  is_simple_stack_op (SOEmit _) = F /\
  is_simple_stack_op SOInitialFmp = F /\
  is_simple_stack_op (SOLabel _) = T /\
  is_simple_stack_op (SOPushLabel _) = T /\
  is_simple_stack_op (SOPushOfst _ _) = F
End

(* =========================================================================
   Concrete pop: k POPs give DROP k
   ========================================================================= *)

Theorem pop_k_concrete[local]:
  !k lo o2pc prog st.
    k <= LENGTH st.as_stack /\
    asm_block_at prog st.as_pc (REPLICATE k (AsmOp "POP")) ==>
    ?st'. asm_steps lo o2pc prog k st = AsmOK st' /\
          st'.as_stack = DROP k st.as_stack /\
          st'.as_memory = st.as_memory /\
          st'.as_pc = st.as_pc + k /\
          st'.as_accounts = st.as_accounts /\
          st'.as_transient = st.as_transient /\
          st'.as_returndata = st.as_returndata /\
          st'.as_logs = st.as_logs /\
          st'.as_call_ctx = st.as_call_ctx /\
          st'.as_tx_ctx = st.as_tx_ctx /\
          st'.as_block_ctx = st.as_block_ctx /\
          st'.as_code = st.as_code /\
          st'.as_prev_hashes = st.as_prev_hashes
Proof
  Induct_on `k`
  >- (rpt strip_tac >> simp[asm_steps_def] >>
      qexists_tac `st` >> simp[])
  >> rpt gen_tac >> strip_tac >>
  `st.as_stack <> []` by (Cases_on `st.as_stack` >> fs[]) >>
  (* Decompose asm_block_at for REPLICATE (SUC k) *)
  `asm_block_at prog st.as_pc [AsmOp "POP"] /\
   asm_block_at prog (st.as_pc + 1) (REPLICATE k (AsmOp "POP"))` by (
    qpat_x_assum `asm_block_at _ _ _` mp_tac >>
    `REPLICATE (SUC k) (AsmOp "POP") =
     [AsmOp "POP"] ++ REPLICATE k (AsmOp "POP")` by
      simp[REPLICATE] >>
    pop_assum SUBST1_TAC >>
    REWRITE_TAC[asm_block_at_append] >> simp[]
  ) >>
  (* First step: POP gives TL *)
  Cases_on `st.as_stack` >> gvs[] >>
  rename1 `h :: rest` >>
  (* asm_step POP: dispatch resolves to asm_pop *)
  `asm_step lo o2pc (AsmOp "POP") st =
   AsmOK (asm_next (st with as_stack := rest))` by (
    qpat_x_assum `asm_block_at _ _ [_]` (K ALL_TAC) >>
    simp[asm_step_def, asm_step_op_def] >>
    (* Dispatch chain: each sub-dispatcher returns NONE for POP *)
    simp[asm_step_arith_def, asm_step_compare_def,
         asm_step_bitwise_def, asm_step_memory_def,
         asm_step_extcall_def, asm_step_copy_def,
         asm_step_context_def] >>
    simp[asm_pop_def]
  ) >>
  (* Unfold asm_steps (SUC k) using this *)
  simp[Once asm_steps_def] >>
  qpat_x_assum `asm_block_at _ _ [_]` mp_tac >>
  simp[asm_block_at_def, asm_next_def] >>
  strip_tac >>
  (* Apply IH *)
  first_x_assum (qspecl_then [`lo`, `o2pc`, `prog`,
    `st with <| as_stack := rest; as_pc := st.as_pc + 1 |>`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `st''` >> gvs[]
QED

(* =========================================================================
   Encode roundtrip for push
   ========================================================================= *)

val dim256 = fcpLib.INDEX_CONV ``dimindex(:256)``;

Theorem push_encode_roundtrip[local]:
  word_of_bytes F (0w:bytes32)
    (REVERSE (encode_num_bytes (w2n (v:bytes32)))) = v
Proof
  mp_tac (INST_TYPE [alpha |-> ``:256``]
    word_of_bytes_encode_roundtrip) >>
  simp[dim256, dividesTheory.divides_def] >>
  qexists_tac `32` >> simp[]
QED

Theorem push_encode_num_roundtrip[local]:
  word_of_bytes F (0w:bytes32)
    (REVERSE (encode_num_bytes n)) = n2w n
Proof
  rewrite_tac[GSYM byteTheory.word_of_bytes_le_def] >>
  mp_tac (INST [``bs:word8 list`` |->
                  ``REVERSE (encode_num_bytes n)``]
    (INST_TYPE [alpha |-> ``:256``]
      cv_stdTheory.word_of_bytes_le_eq_num_of_bytes)) >>
  simp[dim256, num_of_bytes_encode_roundtrip,
       dividesTheory.divides_def] >>
  qexists_tac `32` >> simp[]
QED

(* =========================================================================
   Single-step asm_steps helper
   ========================================================================= *)

Theorem LUPDATE_commutes[local]:
  !a b i j (l:'a list). i <> j ==>
    LUPDATE a i (LUPDATE b j l) = LUPDATE b j (LUPDATE a i l)
Proof
  rpt strip_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_LUPDATE, EL_LUPDATE] >>
  rpt strip_tac >> rw[]
QED

(* Single asm instruction: produces AsmOK st' with all side fields preserved.
   The asm_step must produce AsmOK (asm_next (st with as_stack := new_stack)). *)
Theorem asm_single_step_rel[local]:
  !lo o2pc prog inst st new_stack.
    asm_block_at prog st.as_pc [inst] /\
    asm_step lo o2pc inst st =
      AsmOK (asm_next (st with as_stack := new_stack)) ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          st'.as_stack = new_stack /\
          st'.as_memory = st.as_memory /\
          st'.as_pc = st.as_pc + 1 /\
          st'.as_accounts = st.as_accounts /\
          st'.as_transient = st.as_transient /\
          st'.as_returndata = st.as_returndata /\
          st'.as_logs = st.as_logs /\
          st'.as_call_ctx = st.as_call_ctx /\
          st'.as_tx_ctx = st.as_tx_ctx /\
          st'.as_block_ctx = st.as_block_ctx /\
          st'.as_code = st.as_code /\
          st'.as_prev_hashes = st.as_prev_hashes
Proof
  rpt strip_tac >>
  qexists_tac `asm_next (st with as_stack := new_stack)` >>
  simp[asm_next_def] >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[asm_block_at_def, asm_steps_def, asm_next_def]
QED

(* =========================================================================
   Combined single-instruction helper: asm_step + venom_asm_rel
   ========================================================================= *)

(* Core pattern: a single asm instruction that only changes the stack
   preserves venom_asm_rel with updated plan stack. *)
Theorem single_inst_venom_asm_rel[local]:
  !lo o2pc prog inst ps vs st new_as_stack new_ps_stack.
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc [inst] /\
    asm_step lo o2pc inst st =
      AsmOK (asm_next (st with as_stack := new_as_stack)) /\
    plan_stack_rel lo vs new_ps_stack new_as_stack ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          venom_asm_rel lo (ps with ps_stack := new_ps_stack) vs st' /\
          st'.as_pc = st.as_pc + 1
Proof
  rpt strip_tac >>
  drule_all asm_single_step_rel >> strip_tac >>
  qexists_tac `st'` >> simp[] >>
  gvs[venom_asm_rel_def]
QED

(* Stack length from venom_asm_rel — avoids repeated gvs[venom_asm_rel_def] *)
Theorem venom_asm_rel_stack_length[local]:
  !lo ps vs st.
    venom_asm_rel lo ps vs st ==>
    LENGTH ps.ps_stack = LENGTH st.as_stack
Proof
  rw[venom_asm_rel_def] >> imp_res_tac plan_stack_rel_length
QED

(* =========================================================================
   Per-case standalone theorems for simple_op_venom_asm_rel
   ========================================================================= *)

(* SOPush (Lit c) *)
Theorem simple_op_push_lit[local]:
  !lo o2pc prog ps vs st c.
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc [AsmPush (encode_num_bytes (w2n c))] ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          venom_asm_rel lo (ps with ps_stack := SNOC (Lit c) ps.ps_stack)
            vs st' /\
          st'.as_pc = st.as_pc + 1
Proof
  rpt strip_tac >>
  irule single_inst_venom_asm_rel >> conj_tac
  >- (qexistsl_tac [`AsmPush (encode_num_bytes (w2n c))`,
                     `word_of_bytes F 0w
                        (REVERSE (encode_num_bytes (w2n c))) :: st.as_stack`] >>
      simp[asm_step_push_ok] >>
      irule plan_stack_rel_push >>
      gvs[venom_asm_rel_def] >>
      simp[operand_val_def, push_encode_roundtrip])
  >> first_assum ACCEPT_TAC
QED


Theorem initial_fmp_push_venom_asm_rel:
  !lo o2pc prog ps vs st initial_fmp.
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc [AsmPush (encode_num_bytes initial_fmp)] ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          venom_asm_rel lo
            (ps with ps_stack := SNOC (Lit (n2w initial_fmp)) ps.ps_stack)
            vs st' /\
          st'.as_pc = st.as_pc + 1
Proof
  rpt strip_tac >>
  irule single_inst_venom_asm_rel >> conj_tac
  >- (qexistsl_tac [`AsmPush (encode_num_bytes initial_fmp)`,
                     `n2w initial_fmp :: st.as_stack`] >>
      simp[asm_step_push_ok, push_encode_num_roundtrip] >>
      irule plan_stack_rel_push >>
      gvs[venom_asm_rel_def] >>
      simp[operand_val_def])
  >> first_assum ACCEPT_TAC
QED
(* SOPush (Label _) / SOPushLabel *)
Theorem simple_op_push_label[local]:
  !lo o2pc prog ps vs st lbl.
    IS_SOME (FLOOKUP lo lbl) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc [AsmPushLabel lbl] ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          venom_asm_rel lo (ps with ps_stack := SNOC (Label lbl) ps.ps_stack)
            vs st' /\
          st'.as_pc = st.as_pc + 1
Proof
  rpt strip_tac >>
  `?off. FLOOKUP lo lbl = SOME off` by
    (Cases_on `FLOOKUP lo lbl` >> gvs[]) >>
  irule single_inst_venom_asm_rel >> conj_tac
  >- (qexistsl_tac [`AsmPushLabel lbl`, `n2w off :: st.as_stack`] >>
      simp[asm_step_pushlabel_ok] >>
      irule plan_stack_rel_push >>
      gvs[venom_asm_rel_def] >>
      simp[operand_val_def])
  >> first_assum ACCEPT_TAC
QED

(* SOPushOfst *)
Theorem simple_op_push_ofst:
  !lo o2pc prog ps vs st lbl delta off.
    FLOOKUP lo lbl = SOME off /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc [AsmPushOfst lbl delta] ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          venom_asm_rel lo
            (ps with ps_stack :=
               SNOC (Lit (n2w (off + delta))) ps.ps_stack)
            vs st' /\
          st'.as_pc = st.as_pc + 1
Proof
  rpt strip_tac >>
  irule single_inst_venom_asm_rel >> conj_tac
  >- (qexistsl_tac [`AsmPushOfst lbl delta`,
                     `n2w (off + delta) :: st.as_stack`] >>
      simp[asm_step_pushofst_ok] >>
      irule plan_stack_rel_push >>
      gvs[venom_asm_rel_def] >>
      simp[operand_val_def])
  >> first_assum ACCEPT_TAC
QED

(* SOPop *)
Theorem simple_op_pop[local]:
  !lo o2pc prog ps vs st k.
    k <= LENGTH ps.ps_stack /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (REPLICATE k (AsmOp "POP")) ==>
    ?st'. asm_steps lo o2pc prog k st = AsmOK st' /\
          venom_asm_rel lo
            (ps with ps_stack := TAKE (LENGTH ps.ps_stack - k) ps.ps_stack)
            vs st' /\
          st'.as_pc = k + st.as_pc
Proof
  rpt strip_tac >>
  `k <= LENGTH st.as_stack` by
    metis_tac[venom_asm_rel_stack_length] >>
  drule_all pop_k_concrete >>
  disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
  qexists_tac `st'` >>
  gvs[venom_asm_rel_def] >>
  irule plan_stack_rel_pop >> simp[]
QED

(* SOSwap *)
Theorem simple_op_swap[local]:
  !lo o2pc prog ps vs st dist.
    0 < dist /\ dist <= 16 /\ dist < LENGTH ps.ps_stack /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc [AsmOp (swap_name dist)] ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          venom_asm_rel lo
            (ps with ps_stack := stack_swap dist ps.ps_stack) vs st' /\
          st'.as_pc = st.as_pc + 1
Proof
  rpt strip_tac >>
  imp_res_tac venom_asm_rel_stack_length >>
  qexists_tac `asm_next (st with as_stack :=
    LUPDATE (HD st.as_stack) dist
      (LUPDATE (EL dist st.as_stack) 0 st.as_stack))` >>
  simp[asm_next_def] >>
  `1 = SUC 0` by simp[] >> pop_assum SUBST1_TAC >>
  simp[Once asm_steps_def] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[asm_block_at_def] >> strip_tac >>
  fs[asm_step_swap_ok, asm_steps_def, asm_next_def] >>
  gvs[venom_asm_rel_def] >>
  simp[Once LUPDATE_commutes] >>
  irule plan_stack_rel_swap >> simp[]
QED

(* SODup *)
Theorem simple_op_dup[local]:
  !lo o2pc prog ps vs st dist.
    0 < dist /\ dist <= 16 /\ dist <= LENGTH ps.ps_stack /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc [AsmOp (dup_name dist)] ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          venom_asm_rel lo
            (ps with ps_stack :=
               SNOC (EL (LENGTH ps.ps_stack - dist) ps.ps_stack)
                    ps.ps_stack)
            vs st' /\
          st'.as_pc = st.as_pc + 1
Proof
  rpt strip_tac >>
  imp_res_tac venom_asm_rel_stack_length >>
  qexists_tac `asm_next (st with as_stack :=
    EL (dist - 1) st.as_stack :: st.as_stack)` >>
  simp[asm_next_def] >>
  SUBST1_TAC (DECIDE ``1 = SUC 0``) >>
  simp[Once asm_steps_def] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[asm_block_at_def] >> strip_tac >>
  `dist = (dist - 1) + 1` by decide_tac >>
  pop_assum (fn eq => ONCE_REWRITE_TAC[eq]) >>
  fs[asm_step_dup_ok, asm_steps_def, asm_next_def] >>
  gvs[venom_asm_rel_def] >>
  irule plan_stack_rel_push >> simp[] >>
  imp_res_tac plan_stack_rel_el >>
  first_x_assum (qspec_then `dist - 1` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `operand_val _ _ (EL _ (REVERSE _)) = _` mp_tac >>
  simp[EL_REVERSE, arithmeticTheory.PRE_SUB1]
QED

(* SOLabel *)
Theorem simple_op_label[local]:
  !lo o2pc prog ps vs st lbl.
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc [AsmLabel lbl] ==>
    ?st'. asm_steps lo o2pc prog 1 st = AsmOK st' /\
          venom_asm_rel lo ps vs st' /\
          st'.as_pc = st.as_pc + 1
Proof
  rpt strip_tac >>
  qexists_tac `asm_next st` >>
  simp[asm_next_def] >>
  SUBST1_TAC (DECIDE ``1 = SUC 0``) >>
  simp[Once asm_steps_def] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  simp[asm_block_at_def] >> strip_tac >>
  simp[asm_step_label_ok, asm_steps_def, asm_next_def] >>
  gvs[venom_asm_rel_def]
QED

(* =========================================================================
   Single-op venom_asm_rel preservation (main theorem)
   ========================================================================= *)

Theorem simple_op_venom_asm_rel:
  !initial_fmp lo o2pc prog op ps vs st.
    is_simple_stack_op op /\
    FST (stack_op_wf lo op (LENGTH ps.ps_stack)) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (exec_stack_op initial_fmp op) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (exec_stack_op initial_fmp op)) st =
            AsmOK st' /\
          venom_asm_rel lo (apply_simple_op lo op ps) vs st' /\
          st'.as_pc = st.as_pc + LENGTH (exec_stack_op initial_fmp op)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >>
  gvs[is_simple_stack_op_def] >>
  TRY (Cases_on `o'` >> gvs[is_simple_stack_op_def]) >>
  gvs[stack_op_wf_def, exec_stack_op_def, apply_simple_op_def] >>
  metis_tac[simple_op_push_lit, simple_op_push_label, simple_op_pop,
            simple_op_swap, simple_op_dup, simple_op_label]
QED

(* The length of ps_stack after apply_simple_op matches stack_op_wf's SND *)
Theorem apply_simple_op_length[local]:
  !lo op ps.
    is_simple_stack_op op ==>
    LENGTH (apply_simple_op lo op ps).ps_stack =
    SND (stack_op_wf lo op (LENGTH ps.ps_stack))
Proof
  Cases_on `op` >>
  simp[is_simple_stack_op_def] >>
  TRY (Cases_on `o'` >> simp[is_simple_stack_op_def]) >>
  simp[apply_simple_op_def, stack_op_wf_def, stack_swap_def,
       LENGTH_LUPDATE]
QED

(* =========================================================================
   Composition: list of simple ops preserves venom_asm_rel
   ========================================================================= *)

Theorem simple_prefix_venom_asm_rel:
  !ops initial_fmp lo o2pc prog ps vs st.
    EVERY is_simple_stack_op ops /\
    prefix_wf lo (LENGTH ps.ps_stack) ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo (apply_simple_ops lo ops ps) vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct_on `ops`
  >- (rpt strip_tac >>
      simp[asm_steps_def, execute_plan_def, apply_simple_ops_def])
  >> rpt gen_tac >> strip_tac >>
  rename1 `op :: ops` >>
  fs[EVERY_DEF, apply_simple_ops_def, execute_plan_def] >>
  (* Decompose prefix_wf for cons: get FST + tail prefix_wf *)
  `FST (stack_op_wf lo op (LENGTH ps.ps_stack)) /\
   prefix_wf lo (SND (stack_op_wf lo op (LENGTH ps.ps_stack))) ops` by
    (fs[prefix_wf_cons] >> pairarg_tac >> gvs[]) >>
  (* Decompose asm_block_at for append *)
  `asm_block_at prog st.as_pc (exec_stack_op initial_fmp op) /\
   asm_block_at prog (st.as_pc + LENGTH (exec_stack_op initial_fmp op))
     (FLAT (MAP (exec_stack_op initial_fmp) ops))` by
    (qpat_x_assum `asm_block_at _ _ (exec_stack_op initial_fmp op ++ _)` mp_tac >>
     REWRITE_TAC[asm_block_at_append] >> simp[]) >>
  (* Apply single-op lemma *)
  mp_tac simple_op_venom_asm_rel >>
  disch_then (qspecl_then [`initial_fmp`, `lo`, `o2pc`, `prog`, `op`, `ps`, `vs`, `st`]
    mp_tac) >>
  simp[] >> strip_tac >>
  `LENGTH (apply_simple_op lo op ps).ps_stack =
   SND (stack_op_wf lo op (LENGTH ps.ps_stack))`
    by simp[apply_simple_op_length] >>
  (* Apply IH *)
  first_x_assum (qspecl_then [`initial_fmp`, `lo`, `o2pc`, `prog`,
    `apply_simple_op lo op ps`, `vs`, `st'`] mp_tac) >>
  gvs[] >> strip_tac >>
  (* Compose asm_steps *)
  qexists_tac `st''` >> gvs[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  irule asm_steps_compose_ok >>
  qexists_tac `st'` >> simp[]
QED
