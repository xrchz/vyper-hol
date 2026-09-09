(*
 * Spill/Restore Simulation: SOSpill and SORestore preserve venom_asm_rel.
 *
 * SOSpill off: AsmPush (encode_num_bytes off) + AsmOp "MSTORE"
 *   - Pops TOS value, writes 32 bytes to asm memory at offset `off`
 *
 * SORestore off: AsmPush (encode_num_bytes off) + AsmOp "MLOAD"
 *   - Reads 32 bytes from asm memory at offset `off`, pushes onto stack
 *
 * Key roundtrip: word_of_bytes T 0w (word_to_bytes v T) = v
 *)

Theory spillSim
Ancestors
  codegenRel stackOpSim stackOpAsmSim
  asmSem stackPlanTypes planExec stackModel
  strongPrefixSim instSimHelpers blockSimHelpers
  asmToBytecodeProofs venomState
  list rich_list byte
Libs BasicProvers

val dim256 = fcpLib.INDEX_CONV ``dimindex(:256)``;
val len_w2b = REWRITE_RULE [dim256] (INST_TYPE [alpha |-> ``:256``]
  byteTheory.LENGTH_word_to_bytes);

(* =========================================================================
   asm_expand_memory properties
   ========================================================================= *)

(* Rounding: needed ≤ word-size-rounded value *)
Theorem n_le_round_up_32:
  !n:num. n <= 32 * ((n + 31) DIV 32)
Proof
  gen_tac >>
  `(n + 31) = (n + 31) DIV 32 * 32 + (n + 31) MOD 32 /\
   (n+31) MOD 32 < 32` by
    (mp_tac (Q.SPEC `32` arithmeticTheory.DIVISION) >> simp[]) >>
  decide_tac
QED

(* Fundamental length property: expansion always produces at least n elements *)
Theorem asm_expand_memory_length[simp]:
  !n mem. n <= LENGTH (asm_expand_memory n mem)
Proof
  rpt gen_tac >> simp[asm_expand_memory_def, LET_THM] >>
  IF_CASES_TAC >> simp[]
  >- (mp_tac (Q.SPEC `n` n_le_round_up_32) >> decide_tac)
  >- (mp_tac (Q.SPEC `n` n_le_round_up_32) >> decide_tac)
QED

(* Corollary: LENGTH of TAKE from expanded memory *)
Theorem take_expand_length[local,simp]:
  !off k mem. off <= k ==>
    LENGTH (TAKE off (asm_expand_memory k mem)) = off
Proof
  rpt strip_tac >> simp[LENGTH_TAKE_EQ] >>
  `k <= LENGTH (asm_expand_memory k mem)` by simp[] >>
  decide_tac
QED

(* =========================================================================
   word_of_bytes with trailing zeros
   ========================================================================= *)

(* set_byte of 0 into 0 gives 0 — key base case *)
Theorem set_byte_zero[local]:
  !a be. set_byte a (0w:byte) (0w:'a word) be = 0w
Proof
  simp[byteTheory.set_byte_def, byteTheory.word_slice_alt_zero,
       wordsTheory.w2w_0, wordsTheory.WORD_OR_CLAUSES,
       wordsTheory.ZERO_SHIFT]
QED

(* Appending a single 0w byte doesn't change word_of_bytes *)
Theorem word_of_bytes_snoc_zero[local]:
  !be a (l:byte list). word_of_bytes be a (l ++ [0w]) = word_of_bytes be a l
Proof
  Induct_on `l`
  >- simp[byteTheory.word_of_bytes_def, set_byte_zero]
  >> rpt gen_tac >>
  simp[byteTheory.word_of_bytes_def]
QED

(* Appending any all-zero suffix doesn't change word_of_bytes *)
Theorem word_of_bytes_append_zeros:
  !be a (l:byte list) (zs:byte list).
    EVERY ($= 0w) zs ==>
    word_of_bytes be a (l ++ zs) = word_of_bytes be a l
Proof
  rpt gen_tac >>
  qid_spec_tac `l` >>
  qid_spec_tac `a` >>
  qid_spec_tac `be` >>
  Induct_on `zs` using SNOC_INDUCT
  >- simp[]
  >> rpt strip_tac >>
  gvs[EVERY_SNOC] >>
  simp[APPEND_SNOC] >>
  simp[SNOC_APPEND, word_of_bytes_snoc_zero]
QED

(* word_of_bytes of all-zero bytes gives 0w *)
Theorem word_of_bytes_all_zero[local]:
  !be a (bs:byte list). EVERY ($= 0w) bs ==>
    word_of_bytes be a bs = 0w
Proof
  Induct_on `bs` >>
  simp[byteTheory.word_of_bytes_def] >>
  rpt strip_tac >> gvs[set_byte_zero]
QED

(* word_of_bytes on TAKE/DROP of expanded memory = on original memory.
   Key insight: expansion only adds trailing 0w bytes, which don't
   change word_of_bytes (via word_of_bytes_append_zeros). *)
Theorem word_of_bytes_take_drop_expand:
  !be a off n k mem.
    word_of_bytes be a (TAKE n (DROP off (asm_expand_memory k mem))) =
    word_of_bytes be a (TAKE n (DROP off mem))
Proof
  rpt gen_tac >>
  simp[asm_expand_memory_def, LET_THM] >>
  IF_CASES_TAC >> simp[] >>
  (* expanded = mem ++ REPLICATE (rounded - LENGTH mem) 0w *)
  Cases_on `LENGTH mem <= off`
  >- (
    (* off beyond original: DROP off mem = [] *)
    simp[DROP_LENGTH_TOO_LONG] >>
    simp[rich_listTheory.DROP_APPEND2] >>
    simp[rich_listTheory.DROP_REPLICATE] >>
    (* Both sides reduce to 0w *)
    simp[byteTheory.word_of_bytes_def] >>
    irule word_of_bytes_all_zero >>
    irule rich_listTheory.EVERY_TAKE >>
    simp[EVERY_REPLICATE]
  ) >>
  (* off within original *)
  `off < LENGTH mem` by decide_tac >>
  simp[rich_listTheory.DROP_APPEND1] >>
  Cases_on `off + n <= LENGTH mem`
  >- simp[rich_listTheory.TAKE_APPEND1, LENGTH_DROP]
  >> (* n extends into zero region *)
  simp[rich_listTheory.TAKE_APPEND2, LENGTH_DROP] >>
  `TAKE n (DROP off mem) = DROP off mem` by
    simp[TAKE_LENGTH_ID_rwt2, LENGTH_DROP] >>
  simp[] >>
  irule word_of_bytes_append_zeros >>
  irule rich_listTheory.EVERY_TAKE >>
  simp[EVERY_REPLICATE]
QED

(* =========================================================================
   Memory write/read helpers
   ========================================================================= *)

(* The memory after a 32-byte write at offset off *)
Definition mem_write32_def:
  mem_write32 off (v:bytes32) mem =
    let expanded = asm_expand_memory (off + 32) mem in
    TAKE off expanded ++ word_to_bytes v T ++ DROP (off + 32) expanded
End

(* Reading back at the same offset gives the written value *)
Theorem mem_write32_read_same:
  !off (v:bytes32) mem.
    word_of_bytes T 0w (TAKE 32 (DROP off (mem_write32 off v mem))) = v
Proof
  rpt gen_tac >>
  simp[mem_write32_def, LET_THM] >>
  simp[rich_listTheory.DROP_APPEND1,
       rich_listTheory.DROP_TAKE_EQ_NIL] >>
  simp[rich_listTheory.TAKE_APPEND1, len_w2b,
       TAKE_LENGTH_ID_rwt] >>
  simp[vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED

(* Helper: EL through asm_expand_memory equals read_byte *)
Theorem el_expand_read_byte[local]:
  !i n mem. i < LENGTH (asm_expand_memory n mem) ==>
    EL i (asm_expand_memory n mem) =
    (if i < LENGTH mem then EL i mem else 0w)
Proof
  rpt strip_tac >>
  simp[asm_expand_memory_def, LET_THM] >>
  IF_CASES_TAC
  >- (
    (* rounded <= LENGTH mem: no expansion *)
    fs[asm_expand_memory_def, LET_THM] >> IF_CASES_TAC >> simp[]
  )
  >- (
    (* expansion happened: mem ++ REPLICATE *)
    fs[asm_expand_memory_def, LET_THM] >>
    Cases_on `i < LENGTH mem`
    >- simp[EL_APPEND1]
    >- simp[EL_APPEND2, EL_REPLICATE]
  )
QED

(* read_byte outside the written region is unchanged *)
Theorem read_byte_mem_write32_outside:
  !off (v:bytes32) mem i.
    ~(off <= i /\ i < off + 32) ==>
    read_byte i (mem_write32 off v mem) = read_byte i mem
Proof
  rpt strip_tac >>
  simp[read_byte_def, mem_write32_def, LET_THM, len_w2b] >>
  qabbrev_tac `expanded = asm_expand_memory (off + 32) mem` >>
  `off + 32 <= LENGTH expanded` by simp[Abbr `expanded`] >>
  `off + (32 + (LENGTH expanded - (off + 32))) = LENGTH expanded`
    by decide_tac >>
  simp[] >>
  Cases_on `i < LENGTH expanded`
  >- (
    simp[] >>
    Cases_on `i < off`
    >- (
      simp[EL_APPEND1, LENGTH_APPEND] >>
      simp[EL_TAKE] >>
      fs[el_expand_read_byte, Abbr `expanded`]
    ) >>
    `i >= off + 32` by decide_tac >>
    simp[EL_APPEND2, LENGTH_APPEND, LENGTH_DROP, len_w2b] >>
    `~(i < off + 32)` by decide_tac >> simp[] >>
    simp[EL_DROP] >>
    fs[el_expand_read_byte, Abbr `expanded`]
  )
  >- (
    `~(i < LENGTH mem)` suffices_by simp[] >>
    `LENGTH mem <= LENGTH expanded` by
      (simp[Abbr `expanded`, asm_expand_memory_def, LET_THM] >>
       IF_CASES_TAC >> simp[LENGTH_APPEND, LENGTH_REPLICATE]) >>
    decide_tac
  )
QED

Theorem el_mstore_expand_read_byte[local]:
  !i off mem.
    i < LENGTH
      (if off + 32 > LENGTH mem then
         mem ++ REPLICATE (off + 32 - LENGTH mem) 0w
       else mem) ==>
    EL i
      (if off + 32 > LENGTH mem then
         mem ++ REPLICATE (off + 32 - LENGTH mem) 0w
       else mem) =
    (if i < LENGTH mem then EL i mem else 0w)
Proof
  rpt strip_tac >> IF_CASES_TAC >> gvs[] >>
  Cases_on `i < LENGTH mem`
  >- simp[EL_APPEND1]
  >> simp[EL_APPEND2, EL_REPLICATE]
QED

Theorem read_byte_mstore_outside:
  !off (v:bytes32) s i.
    ~(off <= i /\ i < off + 32) ==>
    read_byte i (mstore off v s).vs_memory = read_byte i s.vs_memory
Proof
  rpt strip_tac >>
  simp[read_byte_def, mstore_def, LET_THM, len_w2b] >>
  qabbrev_tac `expanded =
    if off + 32 > LENGTH s.vs_memory then
      s.vs_memory ++ REPLICATE (off + 32 - LENGTH s.vs_memory) 0w
    else s.vs_memory` >>
  `off + 32 <= LENGTH expanded` by
    (simp[Abbr `expanded`] >> IF_CASES_TAC >> simp[]) >>
  `off + (32 + (LENGTH expanded - (off + 32))) = LENGTH expanded`
    by decide_tac >>
  simp[] >>
  Cases_on `i < LENGTH expanded`
  >- (simp[] >> Cases_on `i < off`
      >- (simp[EL_APPEND1, LENGTH_APPEND, EL_TAKE] >>
          unabbrev_all_tac >> irule el_mstore_expand_read_byte >> simp[])
      >> `i >= off + 32` by decide_tac >>
         simp[EL_APPEND2, LENGTH_APPEND, LENGTH_DROP, len_w2b] >>
         `~(i < off + 32)` by decide_tac >> simp[EL_DROP] >>
         unabbrev_all_tac >> irule el_mstore_expand_read_byte >> simp[])
  >> `~(i < LENGTH s.vs_memory)` suffices_by simp[] >>
     `LENGTH s.vs_memory <= LENGTH expanded` by
       (simp[Abbr `expanded`] >> IF_CASES_TAC >> simp[LENGTH_APPEND]) >>
     decide_tac
QED


Theorem read_byte_splice_inside[local]:
  !expanded bytes off n i.
    LENGTH bytes = n /\ off + n <= LENGTH expanded /\
    off <= i /\ i < off + n ==>
    read_byte i (TAKE off expanded ++ bytes ++ DROP (off + n) expanded) =
    EL (i - off) bytes
Proof
  rpt strip_tac >>
  `LENGTH (TAKE off expanded) = off` by simp[LENGTH_TAKE_EQ] >>
  `i < LENGTH (TAKE off expanded ++ bytes ++ DROP (off + n) expanded)` by
    simp[LENGTH_APPEND] >>
  simp[read_byte_def, EL_APPEND2, EL_APPEND1, LENGTH_APPEND]
QED

Theorem read_byte_mstore_mem_write32_inside:
  !off (v:bytes32) s am i.
    off <= i /\ i < off + 32 ==>
    read_byte i (mstore off v s).vs_memory =
    read_byte i (mem_write32 off v am)
Proof
  rpt strip_tac >>
  qabbrev_tac `sexpanded =
    if off + 32 > LENGTH s.vs_memory then
      s.vs_memory ++ REPLICATE (off + 32 - LENGTH s.vs_memory) 0w
    else s.vs_memory` >>
  qabbrev_tac `aexpanded = asm_expand_memory (off + 32) am` >>
  `off + 32 <= LENGTH sexpanded` by
    (simp[Abbr `sexpanded`] >> IF_CASES_TAC >> simp[]) >>
  `off + 32 <= LENGTH aexpanded` by simp[Abbr `aexpanded`] >>
  simp[mstore_def, mem_write32_def, LET_THM] >>
  `read_byte i
      (TAKE off sexpanded ++ word_to_bytes v T ++
       DROP (off + 32) sexpanded) = EL (i - off) (word_to_bytes v T)` by
    (irule read_byte_splice_inside >> simp[len_w2b]) >>
  `read_byte i
      (TAKE off aexpanded ++ word_to_bytes v T ++
       DROP (off + 32) aexpanded) = EL (i - off) (word_to_bytes v T)` by
    (irule read_byte_splice_inside >> simp[len_w2b]) >>
  metis_tac[]
QED

Theorem memory_rel_mstore_mem_write32:
  !alloc off (v:bytes32) s am.
    memory_rel alloc s.vs_memory am ==>
    memory_rel alloc (mstore off v s).vs_memory
                     (mem_write32 off v am)
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[memory_rel_def] >> rpt strip_tac >>
  Cases_on `off <= i /\ i < off + 32`
  >- (irule read_byte_mstore_mem_write32_inside >> simp[]) >>
  `read_byte i s.vs_memory = read_byte i am` by
    (qpat_x_assum `memory_rel alloc s.vs_memory am` mp_tac >>
     rewrite_tac[memory_rel_def] >>
     disch_then (qspec_then `i` irule) >> simp[]) >>
  metis_tac[read_byte_mstore_outside, read_byte_mem_write32_outside]
QED
(* memory_rel preserved: writes to spill region don't affect outside *)
Theorem memory_rel_mem_write32:
  !alloc vm am off (v:bytes32).
    memory_rel alloc vm am /\
    alloc.sa_spill_base <= off /\
    off + 32 <= alloc.sa_next_offset ==>
    memory_rel alloc vm (mem_write32 off v am)
Proof
  rw[memory_rel_def] >> rpt strip_tac >>
  simp[read_byte_mem_write32_outside] >>
  decide_tac
QED

(* Non-overlapping 32-byte read through mem_write32 (at word_of_bytes level) *)
Theorem mem_write32_read32_disjoint:
  !off off2 (v:bytes32) mem.
    (off2 + 32 <= off \/ off + 32 <= off2) ==>
    word_of_bytes T 0w (TAKE 32 (DROP off2 (mem_write32 off v mem))) =
    word_of_bytes T 0w (TAKE 32 (DROP off2 mem))
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[mem_write32_def, LET_THM] >>
  `off + 32 <= LENGTH (asm_expand_memory (off + 32) mem)` by simp[] >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  gvs[]
  >- (
    (* off2 + 32 <= off: window inside TAKE off expanded *)
    simp[rich_listTheory.DROP_APPEND1, LENGTH_APPEND] >>
    simp[rich_listTheory.TAKE_APPEND1, LENGTH_DROP] >>
    simp[DROP_TAKE] >>
    simp[rich_listTheory.TAKE_TAKE_T] >>
    simp[GSYM rich_listTheory.TAKE_DROP_SWAP] >>
    simp[word_of_bytes_take_drop_expand]
  )
  >- (
    (* off + 32 <= off2: window past word_to_bytes region *)
    simp[rich_listTheory.DROP_APPEND2, LENGTH_APPEND, len_w2b] >>
    simp[rich_listTheory.DROP_APPEND2] >>
    simp[DROP_DROP_T] >>
    simp[word_of_bytes_take_drop_expand]
  )
QED

(* =========================================================================
   plan_spill_rel maintenance under mem_write32
   ========================================================================= *)

(* Spill write preserves existing spill entries if slots don't overlap *)
Theorem plan_spill_rel_write_disjoint:
  !lo vs spilled am off (v:bytes32).
    plan_spill_rel lo vs spilled am /\
    (!op off2. FLOOKUP spilled op = SOME off2 ==>
               off2 + 32 <= off \/ off + 32 <= off2) ==>
    plan_spill_rel lo vs spilled (mem_write32 off v am)
Proof
  rw[plan_spill_rel_def] >> rpt strip_tac >>
  res_tac >> simp[] >>
  metis_tac[mem_write32_read32_disjoint]
QED

(* Spill write adds a new entry to plan_spill_rel *)
Theorem plan_spill_rel_add_entry:
  !lo vs spilled am off (v:bytes32) op.
    plan_spill_rel lo vs spilled am /\
    operand_val vs lo op = SOME v /\
    (!op2 off2. FLOOKUP spilled op2 = SOME off2 ==>
                off2 + 32 <= off \/ off + 32 <= off2) ==>
    plan_spill_rel lo vs (spilled |+ (op, off)) (mem_write32 off v am)
Proof
  rw[plan_spill_rel_def] >> rpt strip_tac >>
  gvs[finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `op' = op` >> gvs[]
  >- simp[mem_write32_read_same]
  >- (res_tac >> simp[] >> metis_tac[mem_write32_read32_disjoint])
QED

(* Removing a spill entry preserves plan_spill_rel *)
Theorem plan_spill_rel_remove_entry:
  !lo vs spilled am op.
    plan_spill_rel lo vs spilled am ==>
    plan_spill_rel lo vs (spilled \\ op) am
Proof
  rw[plan_spill_rel_def] >> rpt strip_tac >>
  gvs[finite_mapTheory.DOMSUB_FLOOKUP_THM] >> metis_tac[]
QED

(* plan_spill_rel preserved through memory expansion *)
Theorem plan_spill_rel_expand:
  !lo vs spilled am n.
    plan_spill_rel lo vs spilled am ==>
    plan_spill_rel lo vs spilled (asm_expand_memory n am)
Proof
  rw[plan_spill_rel_def] >> rpt strip_tac >>
  res_tac >> simp[word_of_bytes_take_drop_expand]
QED

(* =========================================================================
   Encode roundtrip for spill offsets (num → bytes32)
   ========================================================================= *)

(* For any num n, pushing encode_num_bytes n gives n2w n on stack *)
val push_encode_256 =
  let val inst = INST_TYPE [alpha |-> ``:256``]
        asmToBytecodeProofsTheory.word_of_bytes_encode_roundtrip
      val r1 = REWRITE_RULE [dim256] inst
      val div_thm = EVAL ``divides 8 256``
      val leq_thm = numLib.REDUCE_CONV ``(8:num) <= 256``
  in REWRITE_RULE [div_thm, leq_thm] r1 end;

Theorem push_encode_num_roundtrip[local]:
  !n. n < dimword(:256) ==>
      word_of_bytes F (0w:bytes32)
        (REVERSE (encode_num_bytes n)) = n2w n
Proof
  rpt strip_tac >>
  qspec_then `n2w n : bytes32` mp_tac push_encode_256 >>
  simp[wordsTheory.w2n_n2w]
QED

(* =========================================================================
   MSTORE dispatch chain: asm_step (AsmOp "MSTORE") evaluates to asm_mstore
   ========================================================================= *)

Theorem asm_step_op_mstore[local]:
  !o2pc st. asm_step_op o2pc "MSTORE" st = asm_mstore st
Proof
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def]
QED

Theorem asm_step_op_mload[local]:
  !o2pc st. asm_step_op o2pc "MLOAD" st = asm_mload st
Proof
  simp[asm_step_op_def, asm_step_arith_def, asm_step_compare_def,
       asm_step_bitwise_def, asm_step_memory_def]
QED

(* =========================================================================
   SOSpill: 2 asm steps (AsmPush + MSTORE) — asm-level execution
   ========================================================================= *)

(* SOSpill off executes as 2 steps: push n2w off, then MSTORE.
   Result: TOS popped, value written to memory at off. *)
Theorem spill_asm_steps[local]:
  !lo o2pc prog off st.
    off < dimword(:256) /\
    LENGTH st.as_stack >= 1 /\
    asm_block_at prog st.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MSTORE"] ==>
    ?st'. asm_steps lo o2pc prog 2 st = AsmOK st' /\
          st'.as_stack = TL st.as_stack /\
          st'.as_memory = mem_write32 off (HD st.as_stack) st.as_memory /\
          st'.as_pc = st.as_pc + 2 /\
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
  Cases_on `st.as_stack` >> gvs[] >>
  fs[asm_block_at_def] >>
  `EL st.as_pc prog = AsmPush (encode_num_bytes off)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `EL (st.as_pc + 1) prog = AsmOp "MSTORE"` by
    (first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  (* Unfold both steps: 2 = SUC (SUC 0) *)
  SUBST1_TAC (DECIDE ``2 = SUC (SUC 0)``) >>
  simp[Once asm_steps_def] >>
  (* After step 1 unfold, simp reduces asm_step but normalizes SUC 0 to 1.
     Use SUBST to re-establish SUC 0 before unfolding step 2. *)
  simp[asm_step_def, push_encode_num_roundtrip, asm_next_def] >>
  SUBST1_TAC (DECIDE ``1 = SUC 0``) >>
  simp[Once asm_steps_def] >>
  simp[asm_step_def, asm_step_op_mstore, asm_mstore_def,
       asm_next_def, asm_steps_def, mem_write32_def]
QED

(* =========================================================================
   SORestore: 2 asm steps (AsmPush + MLOAD) — asm-level execution
   ========================================================================= *)

Theorem restore_asm_steps[local]:
  !lo o2pc prog off st.
    off < dimword(:256) /\
    asm_block_at prog st.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MLOAD"] ==>
    ?st'. asm_steps lo o2pc prog 2 st = AsmOK st' /\
          st'.as_stack =
            word_of_bytes T (0w:bytes32)
              (TAKE 32 (DROP off
                (asm_expand_memory (off + 32) st.as_memory)))
            :: st.as_stack /\
          st'.as_memory = asm_expand_memory (off + 32) st.as_memory /\
          st'.as_pc = st.as_pc + 2 /\
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
  fs[asm_block_at_def] >>
  `EL st.as_pc prog = AsmPush (encode_num_bytes off)` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `EL (st.as_pc + 1) prog = AsmOp "MLOAD"` by
    (first_x_assum (qspec_then `1` mp_tac) >> simp[]) >>
  SUBST1_TAC (DECIDE ``2 = SUC (SUC 0)``) >>
  simp[Once asm_steps_def] >>
  simp[asm_step_def, push_encode_num_roundtrip, asm_next_def] >>
  SUBST1_TAC (DECIDE ``1 = SUC 0``) >>
  simp[Once asm_steps_def] >>
  simp[asm_step_def, asm_step_op_mload, asm_mload_def,
       asm_next_def, asm_steps_def]
QED

(* =========================================================================
   memory_rel through MSTORE in spill region
   ========================================================================= *)

(* memory_rel through asm_expand_memory *)
Theorem memory_rel_expand[local]:
  !alloc vm am n.
    memory_rel alloc vm am ==>
    memory_rel alloc vm (asm_expand_memory n am)
Proof
  rw[memory_rel_def] >> rpt strip_tac >>
  res_tac >> simp[read_byte_expand]
QED

(* =========================================================================
   SOSpill preserves venom_asm_rel
   ========================================================================= *)

(* SOSpill off: pops TOS, writes to memory at off.
   Preconditions:
   - Stack has at least 1 element
   - off in valid range (fn_eom <= off, off < dimword)
   - off doesn't overlap existing spill entries
   - asm_block_at for the 2 instructions
   Output alloc has sa_next_offset bumped to MAX(old, off+32). *)
Theorem spill_op_venom_asm_rel:
  !lo o2pc prog off op ps vs st.
    venom_asm_rel lo ps vs st /\
    LENGTH ps.ps_stack >= 1 /\
    off < dimword(:256) /\
    op = stack_peek 0 ps.ps_stack /\
    ps.ps_alloc.sa_spill_base <= off /\
    (!op2 off2. FLOOKUP ps.ps_spilled op2 = SOME off2 ==>
                off2 + 32 <= off \/ off + 32 <= off2) /\
    asm_block_at prog st.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MSTORE"] ==>
    ?st'.
      asm_steps lo o2pc prog 2 st = AsmOK st' /\
      venom_asm_rel lo
        (ps with <| ps_stack := stack_pop 1 ps.ps_stack;
                    ps_spilled := ps.ps_spilled |+ (op, off);
                    ps_alloc := ps.ps_alloc with sa_next_offset :=
                      MAX ps.ps_alloc.sa_next_offset (off + 32) |>)
        vs st' /\
      st'.as_pc = st.as_pc + 2
Proof
  rpt gen_tac >> strip_tac >>
  fs[venom_asm_rel_def] >>
  imp_res_tac plan_stack_rel_length >>
  `0 < LENGTH ps.ps_stack` by decide_tac >>
  (* Get TOS operand_val from plan_stack_rel *)
  qspecl_then [`lo`, `vs`, `ps.ps_stack`, `st.as_stack`, `0`]
    mp_tac plan_stack_rel_el >> (impl_tac >- simp[]) >> strip_tac >>
  (* Normalize: EL 0 (REVERSE stk) = stack_peek 0 stk, EL 0 l = HD l *)
  `EL 0 (REVERSE ps.ps_stack) = stack_peek 0 ps.ps_stack` by
    (fs[stack_peek_def, EL_REVERSE, arithmeticTheory.PRE_SUB1]) >>
  `EL 0 st.as_stack = HD st.as_stack` by
    (Cases_on `st.as_stack` >> gvs[]) >>
  (* Execute 2 asm steps *)
  qspecl_then [`lo`, `o2pc`, `prog`, `off`, `st`] mp_tac spill_asm_steps >>
  (impl_tac >- (Cases_on `st.as_stack` >> gvs[])) >>
  strip_tac >>
  qexists_tac `st'` >> simp[] >>
  PURE_REWRITE_TAC[venom_asm_rel_def] >>
  (* Normalize stack_pop and TL to TAKE/DROP forms *)
  PURE_REWRITE_TAC[stack_pop_def] >>
  SUBGOAL_THEN ``TL (st.as_stack : bytes32 list) = DROP 1 st.as_stack``
    (fn th => REWRITE_TAC[th])
  >- (Cases_on `st.as_stack` >> gvs[]) >>
  rpt conj_tac
  >- (irule plan_stack_rel_pop >> simp[])
  >- (irule plan_spill_rel_add_entry >> gvs[] >> metis_tac[])
  >- (
    (* memory_rel with widened exclusion range *)
    simp[memory_rel_def] >> rpt strip_tac >>
    `read_byte i st.as_memory = read_byte i (mem_write32 off (HD st.as_stack) st.as_memory)` by
      (simp[read_byte_mem_write32_outside] >>
       CCONTR_TAC >> fs[arithmeticTheory.MAX_DEF] >> decide_tac) >>
    pop_assum (fn th => REWRITE_TAC[GSYM th]) >>
    fs[memory_rel_def] >>
    first_x_assum match_mp_tac >>
    CCONTR_TAC >> fs[arithmeticTheory.MAX_DEF] >> decide_tac
  )
QED

(* =========================================================================
   SORestore preserves venom_asm_rel
   ========================================================================= *)

(* SORestore off: reads from memory at off, pushes value onto stack.
   Preconditions:
   - op is in ps_spilled at offset off
   - asm_block_at for the 2 instructions *)
Theorem restore_op_venom_asm_rel:
  !lo o2pc prog off op ps vs st.
    venom_asm_rel lo ps vs st /\
    off < dimword(:256) /\
    FLOOKUP ps.ps_spilled op = SOME off /\
    asm_block_at prog st.as_pc
      [AsmPush (encode_num_bytes off); AsmOp "MLOAD"] ==>
    ?st'.
      asm_steps lo o2pc prog 2 st = AsmOK st' /\
      venom_asm_rel lo
        (ps with <| ps_stack := stack_push op ps.ps_stack;
                    ps_spilled := ps.ps_spilled \\ op |>)
        vs st' /\
      st'.as_pc = st.as_pc + 2
Proof
  rpt gen_tac >> strip_tac >>
  (* Execute 2 asm steps *)
  qspecl_then [`lo`, `o2pc`, `prog`, `off`, `st`] mp_tac restore_asm_steps >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  qexists_tac `st'` >> simp[] >>
  fs[venom_asm_rel_def] >>
  (* Get the value at the spill offset *)
  SUBGOAL_THEN ``operand_val vs lo op = SOME
    (word_of_bytes T 0w (TAKE 32 (DROP off st.as_memory)))``
    ASSUME_TAC
  >- (fs[plan_spill_rel_def] >> res_tac) >>
  simp[venom_asm_rel_def, stack_push_def] >>
  rpt conj_tac
  >- (
    irule plan_stack_rel_push >>
    simp[word_of_bytes_take_drop_expand]
  )
  >- (
    irule plan_spill_rel_remove_entry >>
    irule plan_spill_rel_expand >>
    simp[]
  )
  >- (match_mp_tac memory_rel_expand >> simp[])
QED
