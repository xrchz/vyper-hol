(*
 * Builtin Function Properties (consolidated)
 *
 * Covers: hashing, math, simple, bytes, system, misc, create, convert, abi
 *
 * TOP-LEVEL:
 *   compile_keccak256_word_correct — compiled keccak256 outputs hash of word_to_bytes(w)
 *   compile_unsafe_add_correct     — compiled unsafe_add outputs truncated wrapping add
 *   compile_shift_correct          — compiled shift outputs asr/lsr/lsl based on sign of shift amount
 *   compile_builtin_min_correct    — compiled min outputs smaller value via cmp+branchless select
 *   compile_builtin_max_correct    — compiled max outputs larger value via cmp+branchless select
 *   compile_builtin_abs_correct    — compiled abs outputs |v| via neg+select; reverts on MIN_INT
 *   compile_builtin_len_correct    — compiled len outputs stored length via ptr_load
 *   compile_raw_call_correct       — compiled raw_call: OK or revert [CHEATED]
 *   compile_raw_create_correct     — compiled raw_create: OK or revert [CHEATED]
 *   lower_abi_encode_correct       — compiled abi.encode produces buffer [BLOCKED/CHEATED]
 *   lower_abi_decode_correct       — compiled abi.decode: validates+decodes ABI data [BLOCKED/CHEATED]
 *
 * Source: builtins/*.py
 * Lowering: builtin*Script.sml
 *)

Theory builtinProps
Ancestors
  exprLoweringProps exprLowering emitHelperProps emitHelper
  builtinHashing builtinMath builtinSimple builtinBytes
  builtinStrings builtinSystem builtinMisc builtinCreate
  builtinAbi context
  compileEnv venomExecSemantics venomState venomInst venomMemProps
  valueEncoding abiEncoder
  logroot
Libs
  dep_rewrite

(* dimindex(:256) = 256, needed for word_to_bytes length etc. *)
Theorem dimindex_256[local,simp]:
  dimindex(:256) = 256
Proof
  simp[fcpTheory.index_bit0, wordsTheory.dimindex_128,
       fcpTheory.finite_bit0, wordsTheory.finite_128,
       fcpTheory.index_one, fcpTheory.finite_one]
QED

(* ===== Shared infrastructure for weak-spec proofs ===== *)

(* eval_operand definedness is preserved through update_var.
   Key for weak-spec proofs: we don't track exact values, just that
   operands remain defined through a chain of instruction steps. *)
Theorem eval_operand_update_not_none[local]:
  ∀ op ss v (w:bytes32).
    eval_operand op ss ≠ NONE ⇒
    eval_operand op (update_var v w ss) ≠ NONE
Proof
  Cases_on `op` >>
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> Cases_on `s = v` >> simp[]
QED

(* Monadic definition set for unfolding compile_* functions *)
val compile_defs = [emit_op_def, emit_void_def, emit_inst_def, comp_bind_def,
  comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def, emit_def,
  LET_THM];

(* Tactic: compute emitted_insts for a fully-evaluated compile state.
   Unfolds emitted_insts_def, reassociates APPEND, applies DROP_LENGTH_APPEND. *)
val emitted_insts_tac =
  simp[emitted_insts_def] >>
  CONV_TAC (DEPTH_CONV (REWR_CONV (GSYM listTheory.APPEND_ASSOC))) >>
  simp[rich_listTheory.DROP_LENGTH_APPEND];

(* Unconditional eval_operand through update_var for Var operands.
   Rewrites to if-then-else so simp can resolve name equality/inequality. *)
Theorem eval_operand_update_var_if[local]:
  ∀ v v' (w:bytes32) ss.
    eval_operand (Var v) (update_var v' w ss) =
    if v = v' then SOME w else eval_operand (Var v) ss
Proof
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> rw[]
QED

(* eval_operand is preserved through mstore (NOT_NONE form for metis) *)
Theorem eval_operand_mstore_not_none[local]:
  ∀ op addr (val:bytes32) ss.
    eval_operand op ss ≠ NONE ⇒
    eval_operand op (mstore addr val ss) ≠ NONE
Proof
  Cases_on `op` >>
  simp[eval_operand_def, mstore_def, lookup_var_def, LET_THM]
QED

(* eval_operand ignores vs_allocas and vs_alloca_next —
   only depends on vs_vars and vs_labels. Used after ALLOCA. *)
Theorem eval_operand_alloca_fields[local]:
  ∀ op ss a n.
    eval_operand op (ss with <| vs_allocas := a;
                                vs_alloca_next := n |>) =
    eval_operand op ss
Proof
  Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def]
QED

(* ALLOCA always succeeds: both FLOOKUP branches produce OK.
   The resulting state preserves eval_operand for non-output operands,
   and the output variable becomes defined. *)
Theorem step_ALLOCA[local]:
  ∀ id size out ss.
    ∃ ss'.
      step_inst_base (mk_inst id ALLOCA [Lit size] [out]) ss = OK ss' ∧
      (∀ op v. eval_operand op ss = SOME v ∧ (∀ x. op = Var x ⇒ x ≠ out) ⇒
               eval_operand op ss' = SOME v) ∧
      eval_operand (Var out) ss' ≠ NONE
Proof
  rw[step_inst_base_def, exec_alloca_def, mk_inst_def, LET_THM] >>
  Cases_on `FLOOKUP ss.vs_allocas id` >>
  simp[eval_operand_alloca_fields, eval_operand_update_var] >>
  TRY (rename1 `SOME p` >> PairCases_on `p` >>
       simp[eval_operand_alloca_fields, eval_operand_update_var]) >>
  rw[] >> Cases_on `op` >>
  gvs[eval_operand_def, update_var_def, lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED

(* SHA3 step lemma: given two defined operands, SHA3 computes the hash
   of the selected memory range. *)
Theorem step_SHA3[local]:
  ∀ op1 op2 v1 v2 id out ss.
    eval_operand op1 ss = SOME v1 ∧ eval_operand op2 ss = SOME v2 ⇒
    step_inst_base (mk_inst id SHA3 [op1; op2] [out]) ss =
      OK (update_var out
        (word_of_bytes T 0w
          (Keccak_256_w64
            (TAKE (w2n v2)
              (DROP (w2n v1) ss.vs_memory ++ REPLICATE (w2n v2) 0w)))) ss)
Proof
  rpt gen_tac >> strip_tac >>
  PURE_REWRITE_TAC[mk_inst_def] >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[]
QED

(* Tactic for weak-spec proofs of pure instruction chains (≤10 instructions).
   Unfolds everything and case-splits on eval_operand results. *)
val pure_chain_tac =
  simp[run_inst_seq_def, step_inst_base_def,
       exec_pure2_def, exec_pure1_def, exec_read1_def, mk_inst_def,
       eval_operand_lit, eval_operand_update_var_if] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       TRY (metis_tac[eval_operand_update_not_none,
                       optionTheory.NOT_NONE_SOME])) >>
  gvs[eval_operand_update_var_if];

(* Extended tactic: handles MLOAD, MSTORE, SHA3, and ASSERT in addition
   to pure ops. Useful for weak-spec proofs (∃ss'. OK ∨ Abort).
   WARNING: Do NOT include exec_alloca_def — causes FLOOKUP case splits
   that lead to exponential blowup. Peel ALLOCA separately. *)
val weak_spec_chain_tac =
  simp[run_inst_seq_def, step_inst_base_def,
       exec_pure2_def, exec_pure1_def, exec_read1_def,
       exec_write2_def, mk_inst_def,
       eval_operand_lit, eval_operand_update_var_if] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       TRY (metis_tac[eval_operand_update_not_none,
                       eval_operand_mstore_not_none,
                       optionTheory.NOT_NONE_SOME])) >>
  gvs[eval_operand_update_var_if];


(* Peel an ALLOCA instruction from the front of a chain.
   ALLOCA causes weak_spec_chain_tac to timeout (FLOOKUP case split),
   so we handle it separately via step_ALLOCA, then prove the operand
   is preserved through the fresh variable update.
   After: assumptions include eval_operand <input_op> ss1 = SOME <w>
   and eval_operand (Var <fresh>) ss1 ≠ NONE.
   Expects: fresh_vars_wrt st ss, eval_operand <op> ss = SOME <w>.
   Usage: emitted_insts_tac >> peel_alloca_tac >> weak_spec_chain_tac *)
val peel_alloca_impl_tac =
  simp[] >> rpt strip_tac >> CCONTR_TAC >> gvs[] >>
  qpat_x_assum `eval_operand _ ss = SOME _` mp_tac >>
  simp[eval_operand_def, lookup_var_def] >>
  gvs[fresh_vars_wrt_def] >>
  first_x_assum (qspec_then `st.cs_next_var` mp_tac) >>
  simp[finite_mapTheory.FLOOKUP_DEF];

(* ===== Hashing ===== *)

(* keccak256 of a word-sized value: alloc buffer, mstore, sha3 *)
(* Semantic helper: the value a ptr_load reads from the given location.
   Mirrors compile_ptr_load dispatch but on the semantic side. *)
Definition ptr_load_val_def:
  ptr_load_val is_ctor LocMemory addr ss = mload (w2n addr) ss ∧
  ptr_load_val is_ctor LocStorage addr ss = sload addr ss ∧
  ptr_load_val is_ctor LocTransient addr ss = tload addr ss ∧
  ptr_load_val is_ctor LocCalldata addr ss =
    (let data = ss.vs_call_ctx.cc_calldata in
     let bytes = TAKE 32 (DROP (w2n addr) data ++ REPLICATE 32 0w) in
     word_of_bytes T (0w:bytes32) bytes) ∧
  ptr_load_val T LocCode addr ss =
    (case FLOOKUP ss.vs_immutables (w2n addr) of SOME v => v | NONE => 0w) ∧
  ptr_load_val F LocCode addr ss =
    (let bytes = TAKE 32 (DROP (w2n addr) ss.vs_data_section ++
                          REPLICATE 32 0w) in
     word_of_bytes T (0w:bytes32) bytes)
End

Theorem compile_keccak256_word_correct:
  ∀ val_op w ss st op st'.
    compile_keccak256_word val_op st = (op, st') ∧
    eval_operand val_op ss = SOME w ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (word_of_bytes T (0w:bytes32)
                (Keccak_256_w64 (word_to_bytes w T)))
Proof
  (* ALLOCA 32 → buf; MSTORE [buf; w] → writes word_to_bytes w T;
     SHA3 [buf; 32] → hashes those bytes. Round-trip: MSTORE then
     TAKE 32 from same offset = word_to_bytes w T. *)
  rpt strip_tac >>
gvs[compile_keccak256_word_def, compile_alloc_buffer_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
pairarg_tac >> gvs[] >>
pairarg_tac >> gvs[] >>
pairarg_tac >> gvs[] >>
  drule_all emit_op_ALLOCA_correct >> strip_tac >>
  first_x_assum (qspecl_then [`val_op`, `w`] mp_tac) >> (impl_tac >- simp[]) >> strip_tac >> drule_all emit_void_MSTORE_correct >> strip_tac >>
  qpat_x_assum `emit_op SHA3 _ _ = _` (fn th => assume_tac (MATCH_MP emitted_insts_emit_op th) >> assume_tac (MATCH_MP emit_op_extends th)) >> gvs[] >>
  (* Simplify w2n expressions in SHA3 run result *)
  `w2n (32w:bytes32) = 32` by simp[wordsTheory.dimword_def] >>
  `w2n ((n2w offset):bytes32) = offset MOD dimword (:256)` by simp[] >>
  (* Establish SHA3 step *)
  `run_inst_seq (emitted_insts cs'' st') (mstore (offset MOD dimword (:256)) w ss') =
   OK (update_var (STRING #"%" (toString cs''.cs_next_var))
     (word_of_bytes T 0w
        (Keccak_256_w64
           (TAKE 32
              (DROP (offset MOD dimword (:256))
                 (mstore (offset MOD dimword (:256)) w ss').vs_memory ++
               REPLICATE 32 0w))))
     (mstore (offset MOD dimword (:256)) w ss'))` by (
    qpat_x_assum `emitted_insts cs'' st' = _` (fn th => rewrite_tac [th]) >>
    `eval_operand op' (mstore (offset MOD dimword (:256)) w ss') = SOME (n2w offset)` by (
      first_x_assum (qspecl_then [`op'`, `n2w offset`] mp_tac) >> simp[]
    ) >>
    `step_inst_base
       (mk_inst cs''.cs_next_id SHA3 [op'; Lit 32w]
          [STRING #"%" (toString cs''.cs_next_var)])
       (mstore (offset MOD dimword (:256)) w ss') =
     OK (update_var (STRING #"%" (toString cs''.cs_next_var))
       (word_of_bytes T 0w
         (Keccak_256_w64
           (TAKE 32
             (DROP (offset MOD dimword (:256))
                (mstore (offset MOD dimword (:256)) w ss').vs_memory ++
              REPLICATE 32 0w))))
       (mstore (offset MOD dimword (:256)) w ss'))` by (
      qspecl_then
        [`op'`, `Lit 32w`, `n2w offset`, `32w`, `cs''.cs_next_id`,
         `STRING #"%" (toString cs''.cs_next_var)`,
         `mstore (offset MOD dimword (:256)) w ss'`]
        mp_tac step_SHA3 >>
      impl_tac >- simp[eval_operand_lit] >> simp[]
    ) >>
    simp[run_inst_seq_def]
  ) >>
  (* Key data equality via mload_mstore_same *)
  `TAKE 32
     (DROP (offset MOD dimword (:256))
        (mstore (offset MOD dimword (:256)) w ss').vs_memory ++
      REPLICATE 32 0w) = word_to_bytes w T` by (
    `word_of_bytes T (0w:bytes32)
       (TAKE 32
          (DROP (offset MOD dimword (:256))
             (mstore (offset MOD dimword (:256)) w ss').vs_memory ++
           REPLICATE 32 0w)) = w` by
      rewrite_tac[GSYM (SIMP_RULE (srw_ss()) [LET_THM] mload_def),
                  mload_mstore_same] >>
    `word_to_bytes (word_of_bytes T (0w:bytes32)
       (TAKE 32
          (DROP (offset MOD dimword (:256))
             (mstore (offset MOD dimword (:256)) w ss').vs_memory ++
           REPLICATE 32 0w))) T =
     TAKE 32
       (DROP (offset MOD dimword (:256))
          (mstore (offset MOD dimword (:256)) w ss').vs_memory ++
        REPLICATE 32 0w)` by (
      irule word_bytes_roundtrip >>
      simp[wordsTheory.dimword_def, dividesTheory.divides_def] >>
      irule listTheory.LENGTH_TAKE >>
      simp[rich_listTheory.LENGTH_REPLICATE]
    ) >>
    metis_tac[]
  ) >>
  gvs[] >>
  (* Compose 3 segments and provide witness *)
  qexists_tac `update_var (STRING #"%" (toString cs''.cs_next_var))
    (word_of_bytes T 0w (Keccak_256_w64 (word_to_bytes w T)))
    (mstore (offset MOD dimword (:256)) w ss')` >>
  conj_tac
  >- (
    `run_inst_seq (emitted_insts st cs'') ss = OK (mstore (offset MOD dimword (:256)) w ss')` by (
      irule run_emitted_compose2 >>
      MAP_EVERY qexists_tac [`ss'`, `cs'`] >>
      imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
      asm_rewrite_tac[]
    ) >>
    `cs''.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs''` by (
      irule emit_extends_trans >> qexists_tac `cs'` >>
      imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
      asm_rewrite_tac[]
    ) >>
    irule run_emitted_compose2 >>
    MAP_EVERY qexists_tac [`mstore (offset MOD dimword (:256)) w ss'`, `cs''`] >>
    asm_rewrite_tac[]
  )
  >- simp[eval_operand_update_var]
QED

(* ===== Unsafe Math ===== *)

(* Truncation to bit width: unsigned masks, signed sign-extends.
   Matches compile_unsafe_binop post-processing. *)
Definition truncate_to_bits_def:
  truncate_to_bits bits is_signed (w:bytes32) =
    if bits ≥ 256 then w
    else if is_signed then sign_extend (n2w (bits DIV 8 - 1)) w
    else word_and w (n2w (2 ** bits - 1))
End

(* Generic unsafe binop correctness: given opcode opc whose exec_pure2
   implements word operation f, compile_unsafe_binop opc x y bits is_signed
   emits instructions that compute truncate_to_bits bits is_signed (f a b). *)
Theorem compile_unsafe_binop_correct[local]:
  ∀ opc f x y bits is_signed ss st op st' a b.
    compile_unsafe_binop opc x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    (* The opcode implements f via exec_pure2 *)
    (∀ id out s. eval_operand x s = SOME a ∧ eval_operand y s = SOME b ⇒
       step_inst_base (mk_inst id opc [x; y] [out]) s =
         OK (update_var out (f a b) s))
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed (f a b))
Proof
  rpt strip_tac >>
  gvs[compile_unsafe_binop_def, comp_return_def,
      comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >>
  rename [`emit_op opc [x; y] st = (result, cs')`] >>
  Cases_on `bits < 256` >> gvs[comp_return_def]
  >- ((* trunc case: bits < 256 *)
    Cases_on `is_signed` >> gvs[]
    >- ((* signed: SIGNEXTEND *)
      imp_res_tac emitted_insts_emit_op >> gvs[] >>
      simp[emitted_insts_def, rich_listTheory.DROP_APPEND2,
           run_inst_seq_def, truncate_to_bits_def] >>
      first_x_assum (qspecl_then [`st.cs_next_id`,
        `STRING #"%" (toString st.cs_next_var)`, `ss`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >> simp[] >>
      qmatch_goalsub_abbrev_tac `step_inst_base inst2 ss1` >>
      `step_inst_base inst2 ss1 =
         OK (update_var (STRING #"%" (toString (st.cs_next_var + 1)))
             (sign_extend (n2w (bits DIV 8 - 1)) (f a b)) ss1)`
        by (simp[Abbr `inst2`, Abbr `ss1`] >>
            irule step_SIGNEXTEND >>
            simp[eval_operand_update_var, eval_operand_lit_update]) >>
      simp[Abbr `ss1`, eval_operand_update_var])
    >- ((* unsigned: AND *)
      imp_res_tac emitted_insts_emit_op >> gvs[] >>
      simp[emitted_insts_def, rich_listTheory.DROP_APPEND2,
           run_inst_seq_def, truncate_to_bits_def] >>
      first_x_assum (qspecl_then [`st.cs_next_id`,
        `STRING #"%" (toString st.cs_next_var)`, `ss`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >> simp[] >>
      qmatch_goalsub_abbrev_tac `step_inst_base inst2 ss1` >>
      `step_inst_base inst2 ss1 =
         OK (update_var (STRING #"%" (toString (st.cs_next_var + 1)))
             ((f a b) && n2w (2 ** bits - 1)) ss1)`
        by (unabbrev_all_tac >>
            irule step_AND >>
            simp[eval_operand_update_var, eval_operand_lit_update]) >>
      simp[Abbr `ss1`, eval_operand_update_var]))
  >- ((* nop case: bits >= 256 *)
    imp_res_tac emitted_insts_emit_op >> gvs[] >>
    simp[run_inst_seq_def, truncate_to_bits_def] >>
    first_x_assum (qspecl_then [`st.cs_next_id`,
      `STRING #"%" (toString st.cs_next_var)`, `ss`] mp_tac) >>
    simp[] >> strip_tac >> simp[eval_operand_update_var])
QED

(* Shared tactic for all unsafe_* instantiation proofs.
   Uses asm_rewrite_tac to avoid simplifier normalizing word ops (e.g. word_sub). *)
val unsafe_binop_inst_tac = fn def => fn step_thm =>
  rewrite_tac[def] >>
  rpt strip_tac >>
  irule compile_unsafe_binop_correct >>
  goal_assum $ drule_at (Pat `compile_unsafe_binop`) >> asm_rewrite_tac[] >>
  rpt strip_tac >> irule step_thm >> asm_rewrite_tac[];

(* unsafe_add: wrapping addition truncated to bit width *)
Theorem compile_unsafe_add_correct:
  ∀ x y bits is_signed ss st op st' a b.
    compile_unsafe_add x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed (word_add a b))
Proof
  unsafe_binop_inst_tac compile_unsafe_add_def step_ADD
QED

(* unsafe_sub: wrapping subtraction truncated to bit width *)
Theorem compile_unsafe_sub_correct:
  ∀ x y bits is_signed ss st op st' a b.
    compile_unsafe_sub x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed (word_sub a b))
Proof
  unsafe_binop_inst_tac compile_unsafe_sub_def step_SUB
QED

(* unsafe_mul: wrapping multiplication truncated to bit width *)
Theorem compile_unsafe_mul_correct:
  ∀ x y bits is_signed ss st op st' a b.
    compile_unsafe_mul x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed (word_mul a b))
Proof
  unsafe_binop_inst_tac compile_unsafe_mul_def step_MUL
QED

(* unsafe_div: division truncated to bit width.
   Precondition: divisor ≠ 0. Uses SDIV for signed, DIV for unsigned. *)
Theorem compile_unsafe_div_correct:
  ∀ x y bits is_signed ss st op st' a b.
    compile_unsafe_div x y bits is_signed st = (op, st') ∧
    eval_operand x ss = SOME a ∧
    eval_operand y ss = SOME b ∧
    b ≠ 0w
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (truncate_to_bits bits is_signed
          (if is_signed then safe_sdiv a b else safe_div a b))
Proof
  rpt strip_tac >>
  gvs[compile_unsafe_div_def] >>
  Cases_on `is_signed` >> gvs[]
  >- (
    irule compile_unsafe_binop_correct >>
    goal_assum $ drule_at (Pat `compile_unsafe_binop`) >> asm_rewrite_tac[] >>
    rpt strip_tac >> irule step_SDIV >> asm_rewrite_tac[]
  )
  >- (
    irule compile_unsafe_binop_correct >>
    goal_assum $ drule_at (Pat `compile_unsafe_binop`) >> asm_rewrite_tac[] >>
    rpt strip_tac >> irule step_Div >> asm_rewrite_tac[]
  )
QED

(* ===== Shift ===== *)

(* eval_operand_fresh_step: peel one update_var off eval_operand AND bump
   fresh_vars_wrt. Designed for forward chaining: after one application,
   the assumptions contain the updated eval_operand and the bumped
   fresh_vars_wrt, enabling the next step. *)
Theorem eval_operand_fresh_step[local]:
  ∀ op v (w:bytes32) ss st.
    eval_operand op ss = SOME v ∧
    fresh_vars_wrt st ss
    ⇒
    eval_operand op
      (update_var (STRING #"%" (toString st.cs_next_var)) w ss) = SOME v ∧
    fresh_vars_wrt (st with cs_next_var := st.cs_next_var + 1)
      (update_var (STRING #"%" (toString st.cs_next_var)) w ss)
Proof
  rpt strip_tac
  >- (irule eval_operand_update_fresh >>
      conj_tac >- simp[] >>
      qexistsl [`st.cs_next_var`, `st`] >> simp[])
  >> irule fresh_vars_wrt_advance >>
  qexistsl [`st.cs_next_var`, `st`] >> simp[]
QED

(* Chain of 3 fresh update_vars: preserves operands and advances fresh_vars_wrt.
   Uses eval_operand_fresh_step which handles one step at a time. *)
Theorem fresh_update_chain3[local]:
  ∀ cst ss (w0 w1 w2 : bytes32).
    fresh_vars_wrt cst ss
    ⇒
    let v0 = STRING #"%" (toString cst.cs_next_var) in
    let v1 = STRING #"%" (toString (cst.cs_next_var + 1)) in
    let v2 = STRING #"%" (toString (cst.cs_next_var + 2)) in
    let ss3 = update_var v2 w2
                (update_var v1 w1
                  (update_var v0 w0 ss)) in
    fresh_vars_wrt (cst with cs_next_var := cst.cs_next_var + 3) ss3 ∧
    (∀ op v. eval_operand op ss = SOME v ⇒ eval_operand op ss3 = SOME v)
Proof
  rpt gen_tac >> strip_tac >> simp[] >>
  (* Rename to avoid shadowing: cst is our compile state *)
  qabbrev_tac `n = cst.cs_next_var` >>
  (* fresh_vars_wrt: 3 applications of fresh_vars_wrt_advance *)
  `fresh_vars_wrt (cst with cs_next_var := n + 1)
    (update_var (STRING #"%" (toString n)) w0 ss)` by (
    mp_tac (Q.SPECL [`cst`,`cst with cs_next_var := n + 1`]
            fresh_vars_wrt_advance) >>
    simp[Abbr `n`]) >>
  `fresh_vars_wrt (cst with cs_next_var := n + 2)
    (update_var (STRING #"%" (toString (n + 1))) w1
      (update_var (STRING #"%" (toString n)) w0 ss))` by (
    mp_tac (Q.SPECL [`cst with cs_next_var := n + 1`,
                      `cst with cs_next_var := n + 2`]
            fresh_vars_wrt_advance) >>
    simp[Abbr `n`]) >>
  conj_tac >- (
    mp_tac (Q.SPECL [`cst with cs_next_var := n + 2`,
                      `cst with cs_next_var := n + 3`]
            fresh_vars_wrt_advance) >>
    simp[Abbr `n`]) >>
  (* eval_operand: use DEP_REWRITE, then provide witnesses *)
  rpt strip_tac >>
  DEP_REWRITE_TAC[eval_operand_update_fresh] >>
  rpt conj_tac
  >- (qexistsl [`n`, `cst`] >> simp[Abbr `n`])
  >- (qexistsl [`n + 1`, `cst with cs_next_var := n + 1`] >> simp[Abbr `n`])
  >> qexistsl [`n + 2`, `cst with cs_next_var := n + 2`] >> simp[Abbr `n`]
QED

(* ===== Definedness-propagation framework for long pure chains ===== *)

(* For pure opcodes (1-operand and 2-operand), step_inst_base produces
   OK (update_var out result ss) when operands are defined. We don't need
   to know the exact result — just that it succeeds and preserves definedness.

   Key idea: step_inst_base i ss = OK ss' implies
   ∀op. eval_operand op ss ≠ NONE ⇒ eval_operand op ss' ≠ NONE
   for instructions that only change state via update_var. *)

(* Expected operand count for each pure chain opcode.
   Returns the arity so check_chain can verify well-formedness. *)
Definition pure_opc_arity_def:
  pure_opc_arity ADD = SOME 2 ∧
  pure_opc_arity SUB = SOME 2 ∧
  pure_opc_arity MUL = SOME 2 ∧
  pure_opc_arity Div = SOME 2 ∧
  pure_opc_arity SDIV = SOME 2 ∧
  pure_opc_arity LT = SOME 2 ∧
  pure_opc_arity GT = SOME 2 ∧
  pure_opc_arity SLT = SOME 2 ∧
  pure_opc_arity SGT = SOME 2 ∧
  pure_opc_arity EQ = SOME 2 ∧
  pure_opc_arity AND = SOME 2 ∧
  pure_opc_arity OR = SOME 2 ∧
  pure_opc_arity XOR = SOME 2 ∧
  pure_opc_arity SHL = SOME 2 ∧
  pure_opc_arity SHR = SOME 2 ∧
  pure_opc_arity SAR = SOME 2 ∧
  pure_opc_arity SIGNEXTEND = SOME 2 ∧
  pure_opc_arity ISZERO = SOME 1 ∧
  pure_opc_arity NOT = SOME 1 ∧
  pure_opc_arity ASSIGN = SOME 1 ∧
  (* Non-pure opcodes: not in pure chains (all enumerated, no catch-all) *)
  pure_opc_arity Mod = NONE ∧
  pure_opc_arity SMOD = NONE ∧
  pure_opc_arity Exp = NONE ∧
  pure_opc_arity ADDMOD = NONE ∧
  pure_opc_arity MULMOD = NONE ∧
  pure_opc_arity BYTE = NONE ∧
  (* Memory *)
  pure_opc_arity MLOAD = NONE ∧
  pure_opc_arity MSTORE = NONE ∧
  pure_opc_arity MSTORE8 = NONE ∧
  pure_opc_arity MCOPY = NONE ∧
  pure_opc_arity MSIZE = NONE ∧
  (* Storage *)
  pure_opc_arity SLOAD = NONE ∧
  pure_opc_arity SSTORE = NONE ∧
  (* Transient storage *)
  pure_opc_arity TLOAD = NONE ∧
  pure_opc_arity TSTORE = NONE ∧
  (* Immutables *)
  pure_opc_arity ILOAD = NONE ∧
  pure_opc_arity ISTORE = NONE ∧
  (* Control flow *)
  pure_opc_arity JMP = NONE ∧
  pure_opc_arity JNZ = NONE ∧
  pure_opc_arity DJMP = NONE ∧
  pure_opc_arity RET = NONE ∧
  pure_opc_arity RETURN = NONE ∧
  pure_opc_arity REVERT = NONE ∧
  pure_opc_arity STOP = NONE ∧
  pure_opc_arity SINK = NONE ∧
  (* SSA/IR-specific *)
  pure_opc_arity PHI = NONE ∧
  pure_opc_arity PARAM = NONE ∧
  pure_opc_arity NOP = NONE ∧
  (* Allocation *)
  pure_opc_arity ALLOCA = NONE ∧
  (* Internal function calls *)
  pure_opc_arity INVOKE = NONE ∧
  (* Environment *)
  pure_opc_arity CALLER = NONE ∧
  pure_opc_arity CALLVALUE = NONE ∧
  pure_opc_arity CALLDATALOAD = NONE ∧
  pure_opc_arity CALLDATASIZE = NONE ∧
  pure_opc_arity CALLDATACOPY = NONE ∧
  pure_opc_arity ADDRESS = NONE ∧
  pure_opc_arity ORIGIN = NONE ∧
  pure_opc_arity GASPRICE = NONE ∧
  pure_opc_arity GAS = NONE ∧
  pure_opc_arity GASLIMIT = NONE ∧
  pure_opc_arity COINBASE = NONE ∧
  pure_opc_arity TIMESTAMP = NONE ∧
  pure_opc_arity NUMBER = NONE ∧
  pure_opc_arity PREVRANDAO = NONE ∧
  pure_opc_arity CHAINID = NONE ∧
  pure_opc_arity SELFBALANCE = NONE ∧
  pure_opc_arity BALANCE = NONE ∧
  pure_opc_arity BLOCKHASH = NONE ∧
  pure_opc_arity BASEFEE = NONE ∧
  pure_opc_arity CODESIZE = NONE ∧
  pure_opc_arity CODECOPY = NONE ∧
  pure_opc_arity EXTCODESIZE = NONE ∧
  pure_opc_arity EXTCODEHASH = NONE ∧
  pure_opc_arity EXTCODECOPY = NONE ∧
  pure_opc_arity RETURNDATASIZE = NONE ∧
  pure_opc_arity RETURNDATACOPY = NONE ∧
  pure_opc_arity BLOBHASH = NONE ∧
  pure_opc_arity BLOBBASEFEE = NONE ∧
  (* Hashing *)
  pure_opc_arity SHA3 = NONE ∧
  (* External calls *)
  pure_opc_arity CALL = NONE ∧
  pure_opc_arity STATICCALL = NONE ∧
  pure_opc_arity DELEGATECALL = NONE ∧
  pure_opc_arity CREATE = NONE ∧
  pure_opc_arity CREATE2 = NONE ∧
  (* Logging *)
  pure_opc_arity LOG = NONE ∧
  (* Other *)
  pure_opc_arity SELFDESTRUCT = NONE ∧
  pure_opc_arity INVALID = NONE ∧
  (* Assertions *)
  pure_opc_arity ASSERT = NONE ∧
  pure_opc_arity ASSERT_UNREACHABLE = NONE ∧
  (* Data section access *)
  pure_opc_arity DLOAD = NONE ∧
  pure_opc_arity DLOADBYTES = NONE ∧
  pure_opc_arity OFFSET = NONE
End

Triviality exec_pure1_update_ok[local]:
  !f inst ss.
    LENGTH inst.inst_operands = 1 /\
    LENGTH inst.inst_outputs = 1 /\
    EVERY (λop. eval_operand op ss <> NONE) inst.inst_operands ==>
    ?w. exec_pure1 f inst ss = OK (update_var (HD inst.inst_outputs) w ss)
Proof
  rpt strip_tac >>
  gvs[exec_pure1_def, listTheory.LENGTH_EQ_NUM_compute,
      listTheory.EVERY_DEF] >>
  Cases_on `eval_operand h ss` >> gvs[] >>
  metis_tac[]
QED

Triviality exec_pure2_update_ok[local]:
  !f inst ss.
    LENGTH inst.inst_operands = 2 /\
    LENGTH inst.inst_outputs = 1 /\
    EVERY (λop. eval_operand op ss <> NONE) inst.inst_operands ==>
    ?w. exec_pure2 f inst ss = OK (update_var (HD inst.inst_outputs) w ss)
Proof
  rpt strip_tac >>
  gvs[exec_pure2_def, listTheory.LENGTH_EQ_NUM_compute,
      listTheory.EVERY_DEF] >>
  Cases_on `eval_operand h ss` >> gvs[] >>
  Cases_on `eval_operand h' ss` >> gvs[] >>
  metis_tac[]
QED

val pure_chain_pure_tac =
  simp[Once step_inst_base_def] >>
  FIRST [irule exec_pure2_update_ok, irule exec_pure1_update_ok] >>
  simp[];

val pure_chain_assign_tac =
  simp[Once step_inst_base_def] >>
  gvs[listTheory.LENGTH_EQ_NUM_compute, listTheory.EVERY_DEF] >>
  Cases_on `eval_operand h ss` >> gvs[] >>
  metis_tac[];

(* Master step lemma: for pure chain opcodes with correct arity and 1 output,
   if all operands are defined then step returns OK (update_var ...). *)
Theorem pure_chain_step_ok[local]:
  ∀ inst ss n.
    pure_opc_arity inst.inst_opcode = SOME n ∧
    LENGTH inst.inst_operands = n ∧
    LENGTH inst.inst_outputs = 1 ∧
    EVERY (λop. eval_operand op ss ≠ NONE) inst.inst_operands
    ⇒
    ∃ w. step_inst_base inst ss =
         OK (update_var (HD inst.inst_outputs) w ss)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[pure_opc_arity_def]
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_pure_tac
  >- pure_chain_assign_tac
QED

(* Chain check: verify well-formedness of instruction chain against a set
   of known-defined variable names. Returns the set augmented with outputs.
   Labels and Lits are accepted unconditionally (they don't depend on known).
   NONE means ill-formed (wrong opcode, wrong arity, or Var operand not in known). *)
Definition check_chain_def:
  check_chain [] known = SOME known ∧
  check_chain (i::is) known =
    case pure_opc_arity i.inst_opcode of
      NONE => NONE
    | SOME n =>
      if LENGTH i.inst_operands = n ∧
         LENGTH i.inst_outputs = 1 ∧
         EVERY (λop. case op of Lit _ => T
                              | Var v => MEM v known
                              | Label _ => T) i.inst_operands
      then check_chain is (HD i.inst_outputs :: known)
      else NONE
End

(* Helper: extract check_chain conditions cleanly *)
Theorem check_chain_cons[local]:
  check_chain (i::is) known ≠ NONE ⇒
  ∃n. pure_opc_arity i.inst_opcode = SOME n ∧
      LENGTH i.inst_operands = n ∧
      LENGTH i.inst_outputs = 1 ∧
      EVERY (λop. case op of Lit _ => T | Var v => MEM v known
                  | Label _ => T) i.inst_operands ∧
      check_chain is (HD i.inst_outputs :: known) ≠ NONE
Proof
  simp[Once check_chain_def] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* Helper: label eval_operand is preserved through update_var *)
Theorem eval_operand_label_update_var[local]:
  ∀ lbl v w ss.
    eval_operand (Label lbl) (update_var v w ss) = eval_operand (Label lbl) ss
Proof
  simp[eval_operand_def, update_var_def]
QED

(* Helper: operands in checked chain are defined when known vars are
   defined and all label operands in the chain are defined (FILTER form).
   Labels don't track names in known; they're valid by separate hypothesis. *)
Theorem check_chain_operands_defined[local]:
  ∀ ops known ss.
    EVERY (λop. case op of Lit _ => T | Var v => MEM v known
                | Label _ => T) ops ∧
    EVERY (λv. eval_operand (Var v) ss ≠ NONE) known ∧
    EVERY (λop. eval_operand op ss ≠ NONE)
      (FILTER (λop. case op of Label _ => T | _ => F) ops)
    ⇒
    EVERY (λop. eval_operand op ss ≠ NONE) ops
Proof
  Induct >> simp[] >>
  rpt gen_tac >>
  Cases_on `h` >> simp[eval_operand_lit]
  >- (strip_tac >> first_x_assum (qspecl_then [`known`, `ss`] mp_tac) >> simp[])
  >- (strip_tac >> fs[listTheory.EVERY_MEM] >>
      first_x_assum (qspecl_then [`known`, `ss`] mp_tac) >>
      impl_tac >- fs[] >> simp[])
  >> (strip_tac >>
      first_x_assum (qspecl_then [`known`, `ss`] mp_tac) >>
      impl_tac >- fs[] >> simp[])
QED

(* All label operands in a chain remain defined after update_var *)
Theorem labels_preserved_by_update_var[local]:
  ∀ ops v w ss.
    EVERY (λop. case op of Label _ => eval_operand op ss ≠ NONE | _ => T) ops
    ⇒
    EVERY (λop. case op of Label _ => eval_operand op (update_var v w ss) ≠ NONE | _ => T) ops
Proof
  rw[listTheory.EVERY_MEM] >> res_tac >>
  Cases_on `op` >> gvs[eval_operand_label_update_var]
QED

(* Collect all label-definedness requirements from an instruction chain *)
Definition chain_labels_def:
  chain_labels [] = [] ∧
  chain_labels (i::is) =
    FILTER (λop. case op of Label _ => T | _ => F) i.inst_operands ++
    chain_labels is
End

(* Merged step lemma: check_chain conditions → step succeeds.
   Combines check_chain_operands_defined with pure_chain_step_ok
   to avoid an intermediate EVERY eval_operand fact. *)
Theorem check_chain_step_ok[local]:
  ∀ inst ss n known.
    pure_opc_arity inst.inst_opcode = SOME n ∧
    LENGTH inst.inst_operands = n ∧
    LENGTH inst.inst_outputs = 1 ∧
    EVERY (λop. case op of Lit _ => T | Var v => MEM v known
                | Label _ => T) inst.inst_operands ∧
    EVERY (λv. eval_operand (Var v) ss ≠ NONE) known ∧
    EVERY (λop. eval_operand op ss ≠ NONE)
      (FILTER (λop. case op of Label _ => T | _ => F) inst.inst_operands)
    ⇒
    ∃ w. step_inst_base inst ss =
         OK (update_var (HD inst.inst_outputs) w ss)
Proof
  rpt strip_tac >>
  irule pure_chain_step_ok >> simp[] >>
  mp_tac (Q.SPECL [`inst.inst_operands`, `known`, `ss`]
            check_chain_operands_defined) >>
  simp[]
QED

(* Chain correctness: if check_chain succeeds, run_inst_seq succeeds.
   Also: all variables in the output known list are defined in ss'.
   Requires that all Label operands in the chain are defined initially. *)
Theorem run_inst_seq_check_chain[local]:
  ∀ insts known ss known'.
    check_chain insts known = SOME known' ∧
    EVERY (λv. eval_operand (Var v) ss ≠ NONE) known ∧
    EVERY (λop. eval_operand op ss ≠ NONE) (chain_labels insts)
    ⇒
    ∃ ss'. run_inst_seq insts ss = OK ss' ∧
           EVERY (λv. eval_operand (Var v) ss' ≠ NONE) known'
Proof
  Induct_on `insts`
  >- simp[check_chain_def, run_inst_seq_def]
  >> rpt strip_tac >>
  gvs[chain_labels_def] >>
  qpat_x_assum `check_chain _ _ = _` mp_tac >>
  simp[Once check_chain_def] >>
  BasicProvers.every_case_tac >> simp[] >> strip_tac >>
  (* Step head instruction using merged lemma *)
  mp_tac (Q.SPECL [`h`, `ss`, `x`, `known`] check_chain_step_ok) >>
  (impl_tac >- gvs[]) >>
  strip_tac >>
  simp[run_inst_seq_def] >>
  (* Apply IH to tail *)
  first_x_assum (qspecl_then
    [`HD h.inst_outputs :: known`,
     `update_var (HD h.inst_outputs) w ss`, `known'`] mp_tac) >>
  (impl_tac
   >- (
    (conj_tac >- fs[]) >>
    (conj_tac >- (
      simp[listTheory.EVERY_DEF, eval_operand_update_var] >>
      fs[listTheory.EVERY_MEM] >> rw[] >>
      irule eval_operand_update_not_none >> simp[]
    )) >>
    (* All operands (Lit, Var, Label) preserved through update_var *)
    fs[listTheory.EVERY_MEM, listTheory.MEM_FILTER, listTheory.MEM_APPEND] >>
    rw[] >> first_x_assum drule >> strip_tac >>
    Cases_on `op` >>
    gvs[eval_operand_label_update_var, eval_operand_lit_update] >>
    irule eval_operand_update_not_none >> simp[]
  )) >>
  simp[]
QED

(* Wrapper: if check_chain succeeds and output var is in known',
   then run_inst_seq produces a state where the output operand is defined. *)
Theorem run_inst_seq_check_chain_output[local]:
  ∀ insts known ss v.
    check_chain insts known ≠ NONE ∧
    EVERY (λv. eval_operand (Var v) ss ≠ NONE) known ∧
    EVERY (λop. eval_operand op ss ≠ NONE) (chain_labels insts) ∧
    MEM v (THE (check_chain insts known))
    ⇒
    ∃ ss' r. run_inst_seq insts ss = OK ss' ∧
             eval_operand (Var v) ss' = SOME r
Proof
  rpt strip_tac >>
  Cases_on `check_chain insts known` >> gvs[] >>
  drule_all run_inst_seq_check_chain >> strip_tac >>
  qexistsl [`ss'`, `THE (eval_operand (Var v) ss')`] >>
  simp[] >>
  fs[listTheory.EVERY_MEM] >> res_tac >>
  Cases_on `eval_operand (Var v) ss'` >> fs[]
QED

(* Shift: defer to after compile_select infrastructure is defined *)
Theorem compile_shift_correct_weak[local]:
  ∀ val_op bits_op is_signed ss st op st' v b.
    compile_shift val_op bits_op is_signed st = (op, st') ∧
    eval_operand val_op ss = SOME v ∧
    eval_operand bits_op ss = SOME b
    ⇒
    ∃ ss' w.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME w
Proof
  rpt strip_tac >>
  Cases_on `is_signed` >>
  gvs[compile_shift_def, compile_select_def] >>
  gvs compile_defs >>
  emitted_insts_tac >>
  qmatch_goalsub_abbrev_tac `run_inst_seq insts ss` >>
  qmatch_goalsub_abbrev_tac `eval_operand (Var out) _` >>
  irule (Q.SPECL [`insts`, `operand_vars [val_op; bits_op]`, `ss`, `out`]
          run_inst_seq_check_chain_output) >>
  simp[Abbr`insts`, Abbr`out`, check_chain_def, chain_labels_def,
       pure_opc_arity_def, mk_inst_def, operand_vars_def] >>
  rpt conj_tac >>
  TRY (MAP_EVERY qexists_tac [`bits_op`, `val_op`]) >>
  Cases_on `val_op` >> Cases_on `bits_op` >>
  rw[operand_vars_def, operand_var_def, eval_operand_def] >>
  fs[eval_operand_def]
QED

(* ===== Simple Builtins ===== *)

(* compile_select: branchless ternary via XOR/MUL/XOR.
   When cond = bool_to_word b:
     b=T → result = then_val, b=F → result = else_val *)
Theorem compile_select_correct[local]:
  ∀ cond_op then_op else_op cv tv ev b ss st op st'.
    compile_select cond_op then_op else_op st = (op, st') ∧
    eval_operand cond_op ss = SOME cv ∧
    eval_operand then_op ss = SOME tv ∧
    eval_operand else_op ss = SOME ev ∧
    cv = bool_to_word b ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (if b then tv else ev) ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)
Proof
  rpt strip_tac >>
  gvs[compile_select_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename [`emit_op XOR [then_op; else_op] st = (diff_op, cs1)`,
          `emit_op MUL [cond_op; diff_op] cs1 = (scaled_op, cs2)`,
          `emit_op XOR [else_op; scaled_op] cs2 = (op, st')`] >>
  (* Step 1: XOR(then, else) → diff *)
  `step_inst_base (mk_inst st.cs_next_id XOR [then_op; else_op]
     [STRING #"%" (toString st.cs_next_var)]) ss =
   OK (update_var (STRING #"%" (toString st.cs_next_var)) (tv ⊕ ev) ss)`
    by (irule step_XOR >> simp[]) >>
  mp_tac (Q.SPECL [`XOR`, `word_xor`, `then_op`, `else_op`, `tv`, `ev`,
    `st`, `diff_op`, `cs1`, `ss`] emit_op_pure2_correct) >>
  simp[] >> disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  (* Step 2: MUL(cond, diff) → scaled *)
  `eval_operand cond_op ss1 = SOME (bool_to_word b)`
    by (first_x_assum irule >> simp[]) >>
  `step_inst_base (mk_inst cs1.cs_next_id MUL [cond_op; diff_op]
     [STRING #"%" (toString cs1.cs_next_var)]) ss1 =
   OK (update_var (STRING #"%" (toString cs1.cs_next_var))
       (bool_to_word b * (tv ⊕ ev)) ss1)`
    by (irule step_MUL >> simp[]) >>
  mp_tac (Q.SPECL [`MUL`, `word_mul`, `cond_op`, `diff_op`,
    `bool_to_word b`, `tv ⊕ ev`,
    `cs1`, `scaled_op`, `cs2`, `ss1`] emit_op_pure2_correct) >>
  simp[] >> disch_then (qx_choose_then `ss2` strip_assume_tac) >>
  (* Step 3: XOR(else, scaled) → result *)
  `eval_operand else_op ss2 = SOME ev`
    by (first_x_assum irule >> first_x_assum irule >> simp[]) >>
  `step_inst_base (mk_inst cs2.cs_next_id XOR [else_op; scaled_op]
     [STRING #"%" (toString cs2.cs_next_var)]) ss2 =
   OK (update_var (STRING #"%" (toString cs2.cs_next_var))
       (ev ⊕ (bool_to_word b * (tv ⊕ ev))) ss2)`
    by (irule step_XOR >> simp[]) >>
  mp_tac (Q.SPECL [`XOR`, `word_xor`, `else_op`, `scaled_op`,
    `ev`, `bool_to_word b * (tv ⊕ ev)`,
    `cs2`, `op`, `st'`, `ss2`] emit_op_pure2_correct) >>
  simp[] >> disch_then (qx_choose_then `ss3` strip_assume_tac) >>
  (* Compose + conclude *)
  qexists `ss3` >> rpt conj_tac
  >- (irule run_emitted_compose3 >>
      qexistsl [`ss1`, `ss2`, `cs1`, `cs2`] >> simp[] >>
      imp_res_tac emit_op_extends >> gvs[])
  >- (Cases_on `b` >> gvs[bool_to_word_def] >>
      simp[wordsTheory.WORD_XOR_CLAUSES, wordsTheory.WORD_MULT_CLAUSES] >>
      metis_tac[wordsTheory.WORD_XOR_ASSOC, wordsTheory.WORD_XOR_COMM,
                wordsTheory.WORD_XOR_CLAUSES])
  >- simp[]
  >> rpt strip_tac >>
  first_x_assum irule >> first_x_assum irule >> first_x_assum irule >> simp[]
QED

(* compile_select extends cs_current_insts (follows from 3x emit_op_extends) *)
Triviality compile_select_extends:
  ∀ a b c st op st'.
    compile_select a b c st = (op, st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rw[compile_select_def, comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  imp_res_tac emit_op_extends >>
  (* Chain: cs' extends st, cs'' extends cs', st' extends cs'' *)
  `cs''.cs_current_insts =
     st.cs_current_insts ++ emitted_insts st cs''`
    by (qspecl_then [`st`, `cs'`, `cs''`] mp_tac emitted_insts_append >>
        simp[]) >>
  `st'.cs_current_insts =
     st.cs_current_insts ++ emitted_insts st st'`
    by (qspecl_then [`st`, `cs''`, `st'`] mp_tac emitted_insts_append >>
        simp[]) >>
  imp_res_tac same_blocks_trans
QED

(* Shared tactic pattern: emit_op for comparison + compile_select.
   The comparison produces a bool_to_word result, which compile_select uses.
   Works for min(LT/SLT), max(GT/SGT), and potentially abs(SLT). *)
Triviality cmp_then_select_correct:
  ∀ opc cmp_f a b av bv ss st cmp_op cs1 op st'.
    emit_op opc [a; b] st = (cmp_op, cs1) ∧
    compile_select cmp_op a b cs1 = (op, st') ∧
    (∀ id out s.
       eval_operand a s = SOME av ∧ eval_operand b s = SOME bv ⇒
       step_inst_base (mk_inst id opc [a; b] [out]) s =
       OK (update_var out (bool_to_word (cmp_f av bv)) s)) ∧
    eval_operand a ss = SOME av ∧
    eval_operand b ss = SOME bv ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if cmp_f av bv then av else bv)
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id opc [a; b]
     [STRING #"%" (toString st.cs_next_var)]) ss =
   OK (update_var (STRING #"%" (toString st.cs_next_var))
       (bool_to_word (cmp_f av bv)) ss)` by simp[] >>
  mp_tac (Q.SPECL [`opc`, `λx y. bool_to_word (cmp_f x y)`,
    `a`, `b`, `av`, `bv`, `st`, `cmp_op`, `cs1`, `ss`]
    emit_op_pure2_correct) >>
  simp[] >> disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  `eval_operand a ss1 = SOME av` by (first_x_assum irule >> simp[]) >>
  `eval_operand b ss1 = SOME bv` by (first_x_assum irule >> simp[]) >>
  qspecl_then [`cmp_op`, `a`, `b`,
    `bool_to_word (cmp_f av bv)`, `av`, `bv`,
    `cmp_f av bv`, `ss1`, `cs1`, `op`, `st'`]
    mp_tac compile_select_correct >>
  simp[] >>
  disch_then (qx_choose_then `ss2` strip_assume_tac) >>
  qexists `ss2` >>
  `emitted_insts st st' = emitted_insts st cs1 ++ emitted_insts cs1 st'`
    by (imp_res_tac emit_op_extends >>
        imp_res_tac compile_select_extends >>
        imp_res_tac emitted_insts_append >> simp[]) >>
  qpat_x_assum `run_inst_seq (emitted_insts st cs1) _ = _`
    (fn th => simp[MATCH_MP run_inst_seq_append th])
QED

(* min with branchless select *)
Theorem compile_builtin_min_correct:
  ∀ a b use_unsigned ss st op st' av bv.
    compile_builtin_min a b use_unsigned st = (op, st') ∧
    eval_operand a ss = SOME av ∧
    eval_operand b ss = SOME bv ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if (if use_unsigned then w2n av ≤ w2n bv
                  else w2i av ≤ w2i bv)
              then av else bv)
Proof
  rpt strip_tac >>
  gvs[compile_builtin_min_def, comp_bind_def] >>
  Cases_on `use_unsigned` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename [`emit_op _ [a; b] st = (cmp_op, cs1)`]
  >- suspend "unsigned"
  >> suspend "signed"
QED

Resume compile_builtin_min_correct[unsigned]:
  `∀ id out s.
     eval_operand a s = SOME av ∧ eval_operand b s = SOME bv ⇒
     step_inst_base (mk_inst id LT [a; b] [out]) s =
     OK (update_var out (bool_to_word (w2n av < w2n bv)) s)`
    by (rpt strip_tac >> irule step_LT >> simp[]) >>
  qspecl_then [`LT`, `λx y. w2n x < w2n y`, `a`, `b`, `av`, `bv`, `ss`,
    `st`, `cmp_op`, `cs1`, `op`, `st'`]
    mp_tac cmp_then_select_correct >>
  simp[] >> strip_tac >>
  qexists `ss'` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  `w2n av = w2n bv` by decide_tac >>
  gvs[wordsTheory.w2n_11]
QED

Resume compile_builtin_min_correct[signed]:
  `∀ id out s.
     eval_operand a s = SOME av ∧ eval_operand b s = SOME bv ⇒
     step_inst_base (mk_inst id SLT [a; b] [out]) s =
     OK (update_var out (bool_to_word (word_lt av bv)) s)`
    by (rpt strip_tac >> irule step_SLT >> simp[]) >>
  qspecl_then [`SLT`, `word_lt`, `a`, `b`, `av`, `bv`, `ss`,
    `st`, `cmp_op`, `cs1`, `op`, `st'`]
    mp_tac cmp_then_select_correct >>
  simp[] >> strip_tac >>
  qexists `ss'` >> simp[] >>
  simp[GSYM integer_wordTheory.WORD_LTi, GSYM integer_wordTheory.WORD_LEi] >>
  IF_CASES_TAC >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  gvs[wordsTheory.WORD_LESS_OR_EQ]
QED

Finalise compile_builtin_min_correct

(* max with branchless select *)
Theorem compile_builtin_max_correct:
  ∀ a b use_unsigned ss st op st' av bv.
    compile_builtin_max a b use_unsigned st = (op, st') ∧
    eval_operand a ss = SOME av ∧
    eval_operand b ss = SOME bv ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if (if use_unsigned then w2n av ≤ w2n bv
                  else w2i av ≤ w2i bv)
              then bv else av)
Proof
  rpt strip_tac >>
  gvs[compile_builtin_max_def, comp_bind_def] >>
  Cases_on `use_unsigned` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename [`emit_op _ [a; b] st = (cmp_op, cs1)`]
  >- ( (* unsigned: GT → if w2n a > w2n b then a else b *)
    `∀ id out s.
       eval_operand a s = SOME av ∧ eval_operand b s = SOME bv ⇒
       step_inst_base (mk_inst id GT [a; b] [out]) s =
       OK (update_var out (bool_to_word (w2n av > w2n bv)) s)`
      by (rpt strip_tac >> irule step_GT >> simp[]) >>
    qspecl_then [`GT`, `λx y. w2n x > w2n y`, `a`, `b`, `av`, `bv`, `ss`,
      `st`, `cmp_op`, `cs1`, `op`, `st'`]
      mp_tac cmp_then_select_correct >>
    simp[] >> strip_tac >>
    qexists `ss'` >> simp[] >>
    IF_CASES_TAC >> gvs[])
  >> (* signed: SGT *)
  `∀ id out s.
     eval_operand a s = SOME av ∧ eval_operand b s = SOME bv ⇒
     step_inst_base (mk_inst id SGT [a; b] [out]) s =
     OK (update_var out (bool_to_word (word_gt av bv)) s)`
    by (rpt strip_tac >> irule step_SGT >> simp[]) >>
  qspecl_then [`SGT`, `word_gt`, `a`, `b`, `av`, `bv`, `ss`,
    `st`, `cmp_op`, `cs1`, `op`, `st'`]
    mp_tac cmp_then_select_correct >>
  simp[] >> strip_tac >>
  qexists `ss'` >> simp[] >>
  simp[GSYM integer_wordTheory.WORD_LEi] >>
  once_rewrite_tac[GSYM wordsTheory.WORD_NOT_GREATER] >>
  IF_CASES_TAC >> simp[]
QED

(* Shared tactics for multi-step proofs *)

(* Apply emit_op_pure2_correct by chaining MATCH_MP through assumptions.
   Avoids simp[] normalization of word operations (the root cause of
   the "type variable leak" issue with Q.SPECL + word_and/word_xor).
   Usage: prove step_inst_base, set up eval_operand + fresh_vars_wrt in
   assumptions, then call apply_emit_op2_tac.
   The tactic removes the matched emit_op and step_inst_base assumptions. *)
val eop2_unchained =
  REWRITE_RULE [GSYM AND_IMP_INTRO] emit_op_pure2_correct;

(* Helper: try MATCH_MP, return NONE on failure *)
val try_match_mp = fn th1 => fn th2 =>
  SOME (MATCH_MP th1 th2) handle HOL_ERR _ => NONE;

(* Chain: match emit_op (outer), then find eval×2, fresh, step *)
(* NOTE: first_x_assum for eop removes matched emit_op to prevent re-matching.
   apply_emit_op2_tac: for constant-function ops (word_sub, word_and, etc.)
   apply_emit_op2_f_tac: for lambda ops (e.g. `\x y. bool_to_word (x < y)`)
   apply_emit_op1_tac: for 1-operand ops (ISZERO, NOT) *)
val emit_op2_chain = fn thm =>
  first_x_assum (fn eop =>
    let val after_eop = MATCH_MP thm eop
    in first_assum (fn ev1 =>
       case try_match_mp (SPEC_ALL after_eop) ev1 of NONE => fail()
       | SOME after_ev1 =>
       first_assum (fn ev2 =>
       case try_match_mp after_ev1 ev2 of NONE => fail()
       | SOME after_ev2 =>
       first_assum (fn fresh =>
       case try_match_mp after_ev2 fresh of NONE => fail()
       | SOME after_fresh =>
       first_assum (fn step =>
       case try_match_mp after_fresh step of NONE => fail()
       | SOME result => strip_assume_tac result))))
    end);
val apply_emit_op2_tac = emit_op2_chain eop2_unchained;
(* For higher-order f: pre-instantiate, BETA_RULE, then chain *)
val eop2_peeled = Q.SPEC `opc` eop2_unchained;
val apply_emit_op2_f_tac = fn f_q =>
  emit_op2_chain (Q.SPEC f_q eop2_peeled |> BETA_RULE);

(* Same for emit_op_pure1_correct (ISZERO, NOT, etc.) *)
val eop1_unchained =
  REWRITE_RULE [GSYM AND_IMP_INTRO] emit_op_pure1_correct;
val emit_op1_chain = fn thm =>
  first_x_assum (fn eop =>
    let val after_eop = MATCH_MP thm eop
    in first_assum (fn ev1 =>
       case try_match_mp (SPEC_ALL after_eop) ev1 of NONE => fail()
       | SOME after_ev1 =>
       first_assum (fn fresh =>
       case try_match_mp after_ev1 fresh of NONE => fail()
       | SOME after_fresh =>
       first_assum (fn step =>
       case try_match_mp after_fresh step of NONE => fail()
       | SOME result => strip_assume_tac result)))
    end);
val apply_emit_op1_tac = emit_op1_chain eop1_unchained;
val eop1_peeled = Q.SPEC `opc` eop1_unchained;
val apply_emit_op1_f_tac = fn f_q =>
  emit_op1_chain (Q.SPEC f_q eop1_peeled |> BETA_RULE);

val preserve_tac =
  simp[] ORELSE
  (first_assum irule >> simp[]) ORELSE
  (first_assum irule >> first_assum irule >> simp[]) ORELSE
  (first_assum irule >> first_assum irule >> first_assum irule >> simp[]) ORELSE
  (first_assum irule >> first_assum irule >> first_assum irule >>
   first_assum irule >> simp[]) ORELSE
  (rpt (first_assum irule) >> simp[]);
val compose_runs_tac = rpt (first_assum
  (fn th => mp_tac (MATCH_MP run_inst_seq_append th) >> simp[]));

(* Incremental composition: compose run_inst_seq for consecutive segments.
   Uses run_emitted_compose2 and emit_extends_trans from emitHelperPropsTheory.
   Call after each emit_op step + imp_res_tac emit_op_extends.
   Repeatable: `rpt compose_inc_tac` chains N segments. *)
(* rec2_unc order: run1 ⇒ run2 ⇒ ext1 ⇒ ext2 ⇒ conclusion *)
val rec2_unc = REWRITE_RULE [GSYM AND_IMP_INTRO] run_emitted_compose2;
(* ext_unc order: ext1 ⇒ ext2 ⇒ conclusion *)
val ext_unc = REWRITE_RULE [GSYM AND_IMP_INTRO] emit_extends_trans;
(* compose_inc_tac: compose prefix with newest segment.
   Uses first_x_assum for run1 to consume+replace the old prefix.
   First tries each run assumption as run1; if MATCH_MP with rec2_unc
   succeeds and run2 is found, produces the composed result.
   Also produces the transitive extension fact. *)
val compose_inc_tac =
  first_x_assum (fn run1 =>
    let val step1 = MATCH_MP rec2_unc run1
    in first_assum (fn run2 =>
       case try_match_mp (SPEC_ALL step1) run2 of NONE => fail()
       | SOME step2 =>
       first_assum (fn ext1 =>
       case try_match_mp step2 ext1 of NONE => fail()
       | SOME step3 =>
       first_assum (fn ext2 =>
       case try_match_mp step3 ext2 of NONE => fail()
       | SOME result => assume_tac result)))
    end) >>
  (* Produce transitive extension: ext1 ⇒ ext2 ⇒ combined *)
  first_x_assum (fn ext1 =>
    let val step1 = MATCH_MP ext_unc ext1
    in first_assum (fn ext2 =>
       case try_match_mp (SPEC_ALL step1) ext2 of NONE => fail()
       | SOME result => assume_tac result)
    end);

(* Abort composition: OK prefix + abort → abort for combined range *)
Theorem run_emitted_compose2_abort[local]:
  ∀ st st1 st2 ss ss1 e ss_err.
    run_inst_seq (emitted_insts st st1) ss = OK ss1 ∧
    run_inst_seq (emitted_insts st1 st2) ss1 = Abort e ss_err ∧
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2
    ⇒
    run_inst_seq (emitted_insts st st2) ss = Abort e ss_err
Proof
  rpt strip_tac >>
  `emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2`
    by (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  drule run_inst_seq_append >> disch_then (fn th => rewrite_tac[th]) >>
  asm_rewrite_tac[]
QED

(* Abort extension: abort propagates through additional instructions *)
Theorem run_emitted_abort_extend[local]:
  ∀ st st1 st2 ss e ss_err.
    run_inst_seq (emitted_insts st st1) ss = Abort e ss_err ∧
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2
    ⇒
    run_inst_seq (emitted_insts st st2) ss = Abort e ss_err
Proof
  rpt strip_tac >>
  `emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2`
    by (irule emitted_insts_append >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[] >>
  `∀s. run_inst_seq (emitted_insts st st1) ss ≠ OK s` by gvs[] >>
  drule run_inst_seq_append_err >>
  disch_then (fn th => rewrite_tac[th]) >>
  asm_rewrite_tac[]
QED

(* Tactic: prove composition + extension in one shot.
   Usage: `run ... ∧ cs.insts = ...` by compose_ok_tac (`ss_mid`, `cs_mid`)
   Requires: run_inst_seq (emitted_insts st cs_mid) ss = OK ss_mid
             cs_mid.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs_mid
             run_inst_seq (emitted_insts cs_mid cs_next) ss_mid = OK ss_next
             cs_next.cs_current_insts = cs_mid.cs_current_insts ++ emitted_insts cs_mid cs_next
   in assumptions. *)
val compose_ok_tac = fn (ss_mid, cs_mid) =>
  conj_tac >- (irule run_emitted_compose2 >>
    qexistsl [ss_mid, cs_mid] >> asm_rewrite_tac[]) >>
  irule emit_extends_trans >> qexists cs_mid >> asm_rewrite_tac[];

(* abs with branchless select — needs fresh_vars_wrt to prevent clobber *)
Theorem compile_builtin_abs_correct:
  ∀ val_op ss st op st' v.
    compile_builtin_abs val_op st = (op, st') ∧
    eval_operand val_op ss = SOME v ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' =
         SOME (if word_msb v then word_sub 0w v else v)) ∨
      (* MIN_INT case → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_builtin_abs_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename [`emit_op SUB [Lit 0w; val_op] st = (neg_op, cs1)`,
          `emit_op SLT [val_op; Lit 0w] cs1 = (isneg_op, cs2)`,
          `emit_op EQ [val_op; neg_op] cs2 = (ismin_op, cs3)`,
          `emit_op AND [isneg_op; ismin_op] cs3 = (bad_op, cs4)`,
          `emit_op ISZERO [bad_op] cs4 = (notbad_op, cs5)`,
          `emit_void ASSERT [notbad_op] cs5 = (_, cs6)`,
          `compile_select isneg_op neg_op val_op cs6 = (op, st')`] >>
  imp_res_tac emit_op_extends >>
  imp_res_tac emit_void_extends >>
  imp_res_tac compile_select_extends >>
  (* Step 1: SUB → neg = 0w - v *)
  `eval_operand (Lit 0w) ss = SOME 0w` by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst st.cs_next_id SUB [Lit 0w; val_op]
     [STRING #"%" (toString st.cs_next_var)]) ss =
   OK (update_var (STRING #"%" (toString st.cs_next_var)) (0w - v) ss)`
    by (irule step_SUB >> simp[eval_operand_lit]) >>
  apply_emit_op2_tac >>
  (* Step 2: SLT → is_neg = bool_to_word (v < 0w) *)
  `eval_operand val_op ss' = SOME v` by preserve_tac >>
  `eval_operand (Lit 0w) ss' = SOME 0w` by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst cs1.cs_next_id SLT [val_op; Lit 0w]
     [STRING #"%" (toString cs1.cs_next_var)]) ss' =
   OK (update_var (STRING #"%" (toString cs1.cs_next_var))
       (bool_to_word (v < 0w)) ss')`
    by (irule step_SLT >> simp[eval_operand_lit]) >>
  apply_emit_op2_f_tac `\x y. bool_to_word (x < y)` >>
  (* Step 3: EQ → is_min = bool_to_word (v = 0w - v) *)
  `eval_operand val_op ss'' = SOME v` by preserve_tac >>
  `eval_operand neg_op ss'' = SOME (0w - v)` by preserve_tac >>
  `step_inst_base (mk_inst cs2.cs_next_id EQ [val_op; neg_op]
     [STRING #"%" (toString cs2.cs_next_var)]) ss'' =
   OK (update_var (STRING #"%" (toString cs2.cs_next_var))
       (bool_to_word (v = 0w - v)) ss'')`
    by (irule step_EQ >> simp[]) >>
  apply_emit_op2_f_tac `\x y. bool_to_word (x = y)` >>
  (* Step 4: AND → bad = is_neg && is_min *)
  `eval_operand isneg_op ss''' = SOME (bool_to_word (v < 0w))`
    by preserve_tac >>
  `eval_operand ismin_op ss''' = SOME (bool_to_word (v = 0w - v))`
    by preserve_tac >>
  `step_inst_base (mk_inst cs3.cs_next_id AND [isneg_op; ismin_op]
     [STRING #"%" (toString cs3.cs_next_var)]) ss''' =
   OK (update_var (STRING #"%" (toString cs3.cs_next_var))
       (bool_to_word (v < 0w) && bool_to_word (v = 0w - v)) ss''')`
    by (irule step_AND >> simp[]) >>
  apply_emit_op2_tac >>
  (* Step 5: ISZERO → notbad = bool_to_word (bad = 0w) *)
  qabbrev_tac `bad_val = bool_to_word (v < 0w) &&
                          bool_to_word (v = 0w - v)` >>
  qmatch_asmsub_abbrev_tac `fresh_vars_wrt cs4 st4` >>
  `eval_operand bad_op st4 = SOME bad_val` by preserve_tac >>
  `step_inst_base (mk_inst cs4.cs_next_id ISZERO [bad_op]
     [STRING #"%" (toString cs4.cs_next_var)]) st4 =
   OK (update_var (STRING #"%" (toString cs4.cs_next_var))
       (bool_to_word (bad_val = 0w)) st4)`
    by (irule step_ISZERO >> simp[Abbr `bad_val`]) >>
  apply_emit_op1_f_tac `\x. bool_to_word (x = 0w)` >>
  qmatch_asmsub_abbrev_tac `fresh_vars_wrt cs5 st5` >>
  (* Compose 5 segments: st→cs2→cs3→cs4→cs5 *)
  `run_inst_seq (emitted_insts st cs2) ss = OK ss'' ∧
   cs2.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2`
    by compose_ok_tac (`ss'`, `cs1`) >>
  `run_inst_seq (emitted_insts st cs3) ss = OK ss''' ∧
   cs3.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs3`
    by compose_ok_tac (`ss''`, `cs2`) >>
  `run_inst_seq (emitted_insts st cs4) ss = OK st4 ∧
   cs4.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs4`
    by compose_ok_tac (`ss'''`, `cs3`) >>
  `run_inst_seq (emitted_insts st cs5) ss = OK st5`
    by (irule run_emitted_compose2 >>
        qexistsl [`st4`, `cs4`] >> asm_rewrite_tac[]) >>
  (* Step 6: ASSERT — case split on bad_val *)
  Cases_on `bad_val = 0w`
  >- suspend "ok_case"
  >> suspend "abort_case"
QED

Resume compile_builtin_abs_correct[ok_case]:
  `eval_operand notbad_op st5 = SOME 1w`
    by gvs[bool_to_word_def] >>
  `(1w:bytes32) <> 0w` by simp[] >>
  drule_all emit_void_ASSERT_ok >> strip_tac >>
  `eval_operand isneg_op st5 = SOME (bool_to_word (v < 0w))`
    by preserve_tac >>
  `eval_operand neg_op st5 = SOME (0w - v)` by preserve_tac >>
  `eval_operand val_op st5 = SOME v` by preserve_tac >>
  `fresh_vars_wrt cs6 st5` by
    metis_tac[fresh_vars_wrt_emit_void] >>
  qspecl_then [`isneg_op`, `neg_op`, `val_op`,
    `bool_to_word (v < 0w)`, `0w - v`, `v`, `v < 0w`,
    `st5`, `cs6`, `op`, `st'`] mp_tac compile_select_correct >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `ss_final` strip_assume_tac) >>
  qexists `ss_final` >> disj1_tac >>
  conj_tac
  >- (
    `cs5.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs5` by
      (irule emit_extends_trans >> qexists `cs4` >> asm_rewrite_tac[]) >>
    `run_inst_seq (emitted_insts st cs6) ss = OK st5 /\
     cs6.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs6`
      by compose_ok_tac (`st5`, `cs5`) >>
    qspecl_then [`st`, `cs6`, `st'`, `ss`, `st5`, `ss_final`]
      mp_tac run_emitted_compose2 >>
    (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
    simp[])
  >> gvs[wordsTheory.word_msb_neg]
QED


Resume compile_builtin_abs_correct[abort_case]:
  (* bad_val != 0w -> notbad_op evaluates to 0w -> ASSERT reverts *)
  `bool_to_word (bad_val = 0w) = 0w`
    by simp[bool_to_word_def] >>
  `eval_operand notbad_op st5 = SOME 0w`
    by (qpat_x_assum `eval_operand notbad_op st5 = _` mp_tac >>
        asm_rewrite_tac[]) >>
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  (* Derive extension facts *)
  `cs5.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs5` by
    (irule emit_extends_trans >> qexists `cs4` >> asm_rewrite_tac[]) >>
  `cs6.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs6` by
    (irule emit_extends_trans >> qexists `cs5` >> asm_rewrite_tac[]) >>
  `st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    (irule emit_extends_trans >> qexists `cs6` >> asm_rewrite_tac[]) >>
  (* Compose: OK prefix st->cs5 + abort cs5->cs6 -> abort st->cs6 *)
  qspecl_then [`st`, `cs5`, `cs6`, `ss`, `st5`, `Revert_abort`,
    `revert_state (set_returndata [] st5)`]
    mp_tac run_emitted_compose2_abort >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Extend cs6->st' -> abort st->st' *)
  qexists `revert_state (set_returndata [] st5)` >> disj2_tac >>
  qspecl_then [`st`, `cs6`, `st'`, `ss`, `Revert_abort`,
    `revert_state (set_returndata [] st5)`]
    mp_tac run_emitted_abort_extend >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

Finalise compile_builtin_abs_correct;

(* ===== Shift (strong spec) ===== *)
(* Shift: 4 emit_ops + compile_select.
   Proof: step through each emit_op using emit_op_pure2_correct,
   then use compile_select_correct for the selection. *)
(* Shift strong spec: TODO - emit_op_pure2_correct MATCH_MP fails after
   pairarg_tac rewriting. Need to investigate the interaction.
   The weak spec (compile_shift_correct_weak) is proved above. *)
Theorem compile_shift_correct:
  ∀ val_op bits_op is_signed ss st op st' v b.
    compile_shift val_op bits_op is_signed st = (op, st') ∧
    eval_operand val_op ss = SOME v ∧
    eval_operand bits_op ss = SOME b ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (if word_lt b 0w then
                (if is_signed then word_asr v (w2n (0w - b))
                 else word_lsr v (w2n (0w - b)))
              else word_lsl v (w2n b))
Proof
  rpt strip_tac >>
  Cases_on `is_signed` >> gvs[compile_shift_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac compile_select_extends
  >- suspend "sar_case"
  >> suspend "shr_case"
QED

Resume compile_shift_correct[sar_case]:
  (* Step 1: SLT *)
  `eval_operand (Lit 0w) ss = SOME 0w` by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst st.cs_next_id SLT [bits_op; Lit 0w]
     [STRING #"%" (toString st.cs_next_var)]) ss =
   OK (update_var (STRING #"%" (toString st.cs_next_var))
       (bool_to_word (b < 0w)) ss)`
    by (irule step_SLT >> simp[eval_operand_lit]) >>
  apply_emit_op2_f_tac `\x y. bool_to_word (x < y)` >>
  (* Step 2: SUB *)
  `eval_operand (Lit 0w) ss' = SOME 0w` by simp[eval_operand_lit] >>
  `eval_operand bits_op ss' = SOME b` by preserve_tac >>
  `step_inst_base (mk_inst cs'.cs_next_id SUB [Lit 0w; bits_op]
     [STRING #"%" (toString cs'.cs_next_var)]) ss' =
   OK (update_var (STRING #"%" (toString cs'.cs_next_var)) (0w - b) ss')`
    by (irule step_SUB >> simp[eval_operand_lit]) >>
  apply_emit_op2_tac >>
  (* Step 3: SAR *)
  `eval_operand neg_bits ss'' = SOME (0w - b)` by preserve_tac >>
  `eval_operand val_op ss'' = SOME v` by preserve_tac >>
  `step_inst_base (mk_inst cs''.cs_next_id SAR [neg_bits; val_op]
     [STRING #"%" (toString cs''.cs_next_var)]) ss'' =
   OK (update_var (STRING #"%" (toString cs''.cs_next_var))
       (word_asr v (w2n (0w - b))) ss'')`
    by (irule step_SAR >> simp[]) >>
  mp_tac (Q.SPECL [`SAR`, `\x y. word_asr y (w2n x)`, `neg_bits`,
    `val_op`, `0w - b`, `v`, `cs''`, `right_shifted`, `cs'3'`, `ss''`]
    emit_op_pure2_correct |> BETA_RULE) >>
  asm_rewrite_tac[] >> strip_tac >>
  (* Step 4: SHL *)
  `eval_operand bits_op ss''' = SOME b` by preserve_tac >>
  `eval_operand val_op ss''' = SOME v` by preserve_tac >>
  `step_inst_base (mk_inst cs'''.cs_next_id SHL [bits_op; val_op]
     [STRING #"%" (toString cs'''.cs_next_var)]) ss''' =
   OK (update_var (STRING #"%" (toString cs'''.cs_next_var))
       (word_lsl v (w2n b)) ss''')`
    by (irule step_SHL >> simp[]) >>
  mp_tac (Q.SPECL [`SHL`, `\x y. word_lsl y (w2n x)`, `bits_op`,
    `val_op`, `b`, `v`, `cs'''`, `left_shifted`, `cs''''`, `ss'''`]
    emit_op_pure2_correct |> BETA_RULE) >>
  asm_rewrite_tac[] >> strip_tac >>
  `run_inst_seq (emitted_insts st cs'') ss = OK ss'' /\ cs''.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs''` by
  (conj_tac >- (irule run_emitted_compose2 >> qexistsl [`ss'`, `cs'`] >> asm_rewrite_tac[]) >>
   irule emit_extends_trans >> qexists `cs'` >> asm_rewrite_tac[]) >>
`run_inst_seq (emitted_insts st cs'³') ss = OK ss'³' /\ cs'³'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs'³'` by
  (conj_tac >- (irule run_emitted_compose2 >> qexistsl [`ss''`, `cs''`] >> asm_rewrite_tac[]) >>
   irule emit_extends_trans >> qexists `cs''` >> asm_rewrite_tac[]) >>
`run_inst_seq (emitted_insts st cs'⁴') ss = OK ss'⁴' /\ cs'⁴'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs'⁴'` by
  (conj_tac >- (irule run_emitted_compose2 >> qexistsl [`ss'³'`, `cs'³'`] >> asm_rewrite_tac[]) >>
   irule emit_extends_trans >> qexists `cs'³'` >> asm_rewrite_tac[]) >>
  `eval_operand is_neg ss'⁴' = SOME (bool_to_word (b < 0w))` by (
  ntac 3 (first_assum irule) >> first_assum ACCEPT_TAC
) >>
  `eval_operand right_shifted ss'⁴' = SOME (v ≫ w2n (0w − b))` by (first_assum irule >> first_assum ACCEPT_TAC) >>
  mp_tac compile_select_correct >> disch_then (qspecl_then [`is_neg`, `right_shifted`, `left_shifted`, `bool_to_word (b < 0w)`, `v >> w2n (0w - b)`, `v << w2n b`, `b < 0w`] mp_tac) >> disch_then (qspecl_then [`ss'⁴'`, `cs'⁴'`, `op`, `st'`] mp_tac) >> (impl_tac >- asm_rewrite_tac[]) >> disch_then (qx_choose_then `ss_final` strip_assume_tac) >>
  qexists `ss_final` >> conj_tac >- (
  irule run_emitted_compose2 >> qexists `ss'⁴'` >> qexists `cs'⁴'` >> gvs[]
) >> gvs[]
QED

Resume compile_shift_correct[shr_case]:
  (* Step 1: SLT *)
  `eval_operand (Lit 0w) ss = SOME 0w` by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst st.cs_next_id SLT [bits_op; Lit 0w]
     [STRING #"%" (toString st.cs_next_var)]) ss =
   OK (update_var (STRING #"%" (toString st.cs_next_var))
       (bool_to_word (b < 0w)) ss)`
    by (irule step_SLT >> simp[eval_operand_lit]) >>
  apply_emit_op2_f_tac `\x y. bool_to_word (x < y)` >>
  (* Step 2: SUB *)
  `eval_operand (Lit 0w) ss' = SOME 0w` by simp[eval_operand_lit] >>
  `eval_operand bits_op ss' = SOME b` by preserve_tac >>
  `step_inst_base (mk_inst cs'.cs_next_id SUB [Lit 0w; bits_op]
     [STRING #"%" (toString cs'.cs_next_var)]) ss' =
   OK (update_var (STRING #"%" (toString cs'.cs_next_var)) (0w - b) ss')`
    by (irule step_SUB >> simp[eval_operand_lit]) >>
  apply_emit_op2_tac >>
  (* Step 3: SHR *)
  `eval_operand neg_bits ss'' = SOME (0w - b)` by preserve_tac >>
  `eval_operand val_op ss'' = SOME v` by preserve_tac >>
  `step_inst_base (mk_inst cs''.cs_next_id SHR [neg_bits; val_op]
     [STRING #"%" (toString cs''.cs_next_var)]) ss'' =
   OK (update_var (STRING #"%" (toString cs''.cs_next_var))
       (word_lsr v (w2n (0w - b))) ss'')`
    by (irule step_SHR >> simp[]) >>
  mp_tac (Q.SPECL [`SHR`, `\x y. word_lsr y (w2n x)`, `neg_bits`,
    `val_op`, `0w - b`, `v`, `cs''`, `right_shifted`, `cs'3'`, `ss''`]
    emit_op_pure2_correct |> BETA_RULE) >>
  asm_rewrite_tac[] >> strip_tac >>
  (* Step 4: SHL *)
  `eval_operand bits_op ss''' = SOME b` by preserve_tac >>
  `eval_operand val_op ss''' = SOME v` by preserve_tac >>
  `step_inst_base (mk_inst cs'''.cs_next_id SHL [bits_op; val_op]
     [STRING #"%" (toString cs'''.cs_next_var)]) ss''' =
   OK (update_var (STRING #"%" (toString cs'''.cs_next_var))
       (word_lsl v (w2n b)) ss''')`
    by (irule step_SHL >> simp[]) >>
  mp_tac (Q.SPECL [`SHL`, `\x y. word_lsl y (w2n x)`, `bits_op`,
    `val_op`, `b`, `v`, `cs'''`, `left_shifted`, `cs''''`, `ss'''`]
    emit_op_pure2_correct |> BETA_RULE) >>
  asm_rewrite_tac[] >> strip_tac >>
  (* Compose 4 segments *)
  `run_inst_seq (emitted_insts st cs'') ss = OK ss'' /\ cs''.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs''` by
  (conj_tac >- (irule run_emitted_compose2 >> qexistsl [`ss'`, `cs'`] >> asm_rewrite_tac[]) >>
   irule emit_extends_trans >> qexists `cs'` >> asm_rewrite_tac[]) >>
`run_inst_seq (emitted_insts st cs'³') ss = OK ss'³' /\ cs'³'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs'³'` by
  (conj_tac >- (irule run_emitted_compose2 >> qexistsl [`ss''`, `cs''`] >> asm_rewrite_tac[]) >>
   irule emit_extends_trans >> qexists `cs''` >> asm_rewrite_tac[]) >>
`run_inst_seq (emitted_insts st cs'⁴') ss = OK ss'⁴' /\ cs'⁴'.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs'⁴'` by
  (conj_tac >- (irule run_emitted_compose2 >> qexistsl [`ss'³'`, `cs'³'`] >> asm_rewrite_tac[]) >>
   irule emit_extends_trans >> qexists `cs'³'` >> asm_rewrite_tac[]) >>
  (* Preserve evals to ss'4' *)
  `eval_operand is_neg ss'⁴' = SOME (bool_to_word (b < 0w))` by (
  ntac 3 (first_assum irule) >> first_assum ACCEPT_TAC
) >>
  `eval_operand right_shifted ss'⁴' = SOME (word_lsr v (w2n (0w − b)))` by (first_assum irule >> first_assum ACCEPT_TAC) >>
  (* compile_select *)
  mp_tac compile_select_correct >> disch_then (qspecl_then [`is_neg`, `right_shifted`, `left_shifted`, `bool_to_word (b < 0w)`, `word_lsr v (w2n (0w - b))`, `v << w2n b`, `b < 0w`] mp_tac) >> disch_then (qspecl_then [`ss'⁴'`, `cs'⁴'`, `op`, `st'`] mp_tac) >> (impl_tac >- asm_rewrite_tac[]) >> disch_then (qx_choose_then `ss_final` strip_assume_tac) >>
  qexists `ss_final` >> conj_tac >- (
  irule run_emitted_compose2 >> qexists `ss'⁴'` >> qexists `cs'⁴'` >> gvs[]
) >> gvs[]
QED

Finalise compile_shift_correct;

(* Generic step lemma for exec_read1-based opcodes *)
Theorem step_read1[local]:
  ∀ f opc op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ∧
    (∀ inst s. inst.inst_opcode = opc ⇒
       step_inst_base inst s = exec_read1 f inst s)
    ⇒
    step_inst_base (mk_inst id opc [op1] [out]) ss =
      OK (update_var out (f v1 ss) ss)
Proof
  rw[exec_read1_def, mk_inst_def]
QED

Theorem step_MLOAD_result[local]:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    (case step_inst_base (mk_inst id MLOAD [op1] [out]) ss of
       OK ss' => OK ss'
     | Halt ss' => Halt ss'
     | Abort a ss' => Abort a ss'
     | IntRet vs ss' => IntRet vs ss'
     | Error e => Error e) =
      OK (update_var out (mload (w2n v1) ss) ss)
Proof
  rw[] >> drule_all step_MLOAD >> simp[]
QED

Theorem step_SLOAD_result[local]:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    (case step_inst_base (mk_inst id SLOAD [op1] [out]) ss of
       OK ss' => OK ss'
     | Halt ss' => Halt ss'
     | Abort a ss' => Abort a ss'
     | IntRet vs ss' => IntRet vs ss'
     | Error e => Error e) =
      OK (update_var out (sload v1 ss) ss)
Proof
  rw[] >> drule_all step_SLOAD >> simp[]
QED

Theorem step_TLOAD_result[local]:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    (case step_inst_base (mk_inst id TLOAD [op1] [out]) ss of
       OK ss' => OK ss'
     | Halt ss' => Halt ss'
     | Abort a ss' => Abort a ss'
     | IntRet vs ss' => IntRet vs ss'
     | Error e => Error e) =
      OK (update_var out (tload v1 ss) ss)
Proof
  rw[step_inst_base_def, exec_read1_def, mk_inst_def]
QED

Theorem step_CALLDATALOAD_result[local]:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    (case step_inst_base (mk_inst id CALLDATALOAD [op1] [out]) ss of
       OK ss' => OK ss'
     | Halt ss' => Halt ss'
     | Abort a ss' => Abort a ss'
     | IntRet vs ss' => IntRet vs ss'
     | Error e => Error e) =
      OK (update_var out
        (word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n v1) ss.vs_call_ctx.cc_calldata ++ REPLICATE 32 0w))) ss)
Proof
  rw[] >> drule_all step_CALLDATALOAD >> simp[LET_THM]
QED

Theorem step_ILOAD_result[local]:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    (case step_inst_base (mk_inst id ILOAD [op1] [out]) ss of
       OK ss' => OK ss'
     | Halt ss' => Halt ss'
     | Abort a ss' => Abort a ss'
     | IntRet vs ss' => IntRet vs ss'
     | Error e => Error e) =
      OK (update_var out
        (case FLOOKUP ss.vs_immutables (w2n v1) of SOME v => v | NONE => 0w) ss)
Proof
  rw[step_inst_base_def, exec_read1_def, mk_inst_def]
QED

Theorem step_DLOAD_result[local]:
  ∀ op1 v1 id out ss.
    eval_operand op1 ss = SOME v1 ⇒
    (case step_inst_base (mk_inst id DLOAD [op1] [out]) ss of
       OK ss' => OK ss'
     | Halt ss' => Halt ss'
     | Abort a ss' => Abort a ss'
     | IntRet vs ss' => IntRet vs ss'
     | Error e => Error e) =
      OK (update_var out
        (word_of_bytes T (0w:bytes32)
           (TAKE 32 (DROP (w2n v1) ss.vs_data_section ++ REPLICATE 32 0w))) ss)
Proof
  rw[step_inst_base_def, exec_read1_def, mk_inst_def]
QED

(* len for dynarray: reads stored length *)
Theorem compile_builtin_len_correct:
  ∀ is_ctor ptr_op loc ss st op st' addr.
    compile_builtin_len is_ctor ptr_op loc st = (op, st') ∧
    eval_operand ptr_op ss = SOME addr
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (ptr_load_val is_ctor loc addr ss)
Proof
  rpt strip_tac >>
  gvs[compile_builtin_len_def] >>
  Cases_on `loc` >>
  gvs[compile_ptr_load_def, ptr_load_val_def] >>
  TRY (Cases_on `is_ctor` >> gvs[compile_ptr_load_def, ptr_load_val_def]) >>
  imp_res_tac emitted_insts_emit_op >> gvs[] >>
  qmatch_goalsub_abbrev_tac `eval_operand (Var out) _ = SOME val` >>
  qexists_tac `update_var out val ss` >>
  simp[run_inst_seq_def, eval_operand_update_var] >>
  unabbrev_all_tac >>
  simp[step_MLOAD_result, step_SLOAD_result, step_TLOAD_result,
       step_CALLDATALOAD_result, step_ILOAD_result, step_DLOAD_result]
QED

(* empty: zero-initializes a primitive value *)
Theorem compile_builtin_empty_prim_correct:
  ∀ st op st'.
    compile_builtin_empty_prim st = (op, st')
    ⇒
    op = Lit 0w ∧ emitted_insts st st' = []
Proof
  rw[compile_builtin_empty_prim_def, emitted_insts_def, comp_return_def,
     comp_bind_def, comp_ignore_bind_def]
QED

(* ===== Misc Builtins ===== *)

(* ===== Check-chain tactic for long pure instruction chains ===== *)

(* Rewrite theorems for check_chain computation.
   toString_inj is critical for symbolic variable name MEM checks (~5s for 87 insts).
   Without it: >50s TIMEOUT. *)
val check_chain_simp_thms = [check_chain_def, pure_opc_arity_def, mk_inst_def,
  ASCIInumbersTheory.toString_inj];



(* floor: rounds toward negative infinity.
   floor(x, d) = sdiv(if x < 0 then x - (d-1) else x, d) *)
Theorem compile_floor_correct:
  ∀ val_op divisor x ss st op st'.
    compile_floor val_op divisor st = (op, st') ∧
    eval_operand val_op ss = SOME x ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (safe_sdiv
                (if word_lt x 0w then x - n2w (divisor - 1) else x)
                (n2w divisor))
Proof
  rpt strip_tac >>
  gvs[compile_floor_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac compile_select_extends >>
  rename [`emit_op SLT [val_op; Lit 0w] st = (is_neg_op, cs1)`,
          `emit_op SUB [val_op; Lit (n2w (divisor - 1))] cs1 = (adj_op, cs2)`,
          `compile_select is_neg_op adj_op val_op cs2 = (input_op, cs3)`,
          `emit_op SDIV [input_op; Lit (n2w divisor)] cs3 = (op, st')`] >>
  (* Step 1: SLT *)
  `eval_operand (Lit 0w) ss = SOME 0w` by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst st.cs_next_id SLT [val_op; Lit 0w]
     [STRING #"%" (toString st.cs_next_var)]) ss =
   OK (update_var (STRING #"%" (toString st.cs_next_var))
       (bool_to_word (word_lt x 0w)) ss)`
    by (irule step_SLT >> simp[eval_operand_lit]) >>
  apply_emit_op2_f_tac `\a b. bool_to_word (word_lt a b)` >>
  (* Step 2: SUB *)
  `eval_operand val_op ss' = SOME x` by preserve_tac >>
  `eval_operand (Lit (n2w (divisor - 1))) ss' = SOME (n2w (divisor - 1))`
    by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst cs1.cs_next_id SUB
     [val_op; Lit (n2w (divisor - 1))]
     [STRING #"%" (toString cs1.cs_next_var)]) ss' =
   OK (update_var (STRING #"%" (toString cs1.cs_next_var))
       (x - n2w (divisor - 1)) ss')`
    by (irule step_SUB >> simp[eval_operand_lit]) >>
  apply_emit_op2_tac >>
  (* Step 3: compile_select *)
  `eval_operand is_neg_op ss'' = SOME (bool_to_word (word_lt x 0w))`
    by preserve_tac >>
  `eval_operand adj_op ss'' = SOME (x - n2w (divisor - 1))`
    by preserve_tac >>
  `eval_operand val_op ss'' = SOME x` by preserve_tac >>
  qspecl_then [`is_neg_op`, `adj_op`, `val_op`,
    `bool_to_word (word_lt x 0w)`,
    `x - n2w (divisor - 1)`, `x`,
    `word_lt x 0w`, `ss''`, `cs2`, `input_op`, `cs3`]
    mp_tac compile_select_correct >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `ss3` strip_assume_tac) >>
  (* Step 4: SDIV *)
  `eval_operand (Lit (n2w divisor)) ss3 = SOME (n2w divisor)`
    by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst cs3.cs_next_id SDIV
     [input_op; Lit (n2w divisor)]
     [STRING #"%" (toString cs3.cs_next_var)]) ss3 =
   OK (update_var (STRING #"%" (toString cs3.cs_next_var))
       (safe_sdiv (if word_lt x 0w then x - n2w (divisor - 1) else x)
                  (n2w divisor)) ss3)`
    by (irule step_SDIV >> simp[eval_operand_lit]) >>
  apply_emit_op2_tac >>
  (* Compose all segments *)
  qexists `ss'''` >>
  conj_tac
  >- (
    `run_inst_seq (emitted_insts st cs2) ss = OK ss'' ∧
     cs2.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2`
      by compose_ok_tac (`ss'`, `cs1`) >>
    `run_inst_seq (emitted_insts st cs3) ss = OK ss3 ∧
     cs3.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs3`
      by compose_ok_tac (`ss''`, `cs2`) >>
    irule run_emitted_compose2 >>
    qexistsl [`ss3`, `cs3`] >> asm_rewrite_tac[])
  >> asm_rewrite_tac[]
QED

(* ceil: rounds toward positive infinity.
   ceil(x, d) = sdiv(if x > 0 then x + (d-1) else x, d) *)
Theorem compile_ceil_correct:
  ∀ val_op divisor x ss st op st'.
    compile_ceil val_op divisor st = (op, st') ∧
    eval_operand val_op ss = SOME x ∧
    fresh_vars_wrt st ss
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' =
        SOME (safe_sdiv
                (if word_gt x 0w then x + n2w (divisor - 1) else x)
                (n2w divisor))
Proof
  rpt strip_tac >>
  gvs[compile_ceil_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emit_op_extends >>
  imp_res_tac compile_select_extends >>
  rename [`emit_op SGT [val_op; Lit 0w] st = (is_pos_op, cs1)`,
          `emit_op ADD [val_op; Lit (n2w (divisor - 1))] cs1 = (adj_op, cs2)`,
          `compile_select is_pos_op adj_op val_op cs2 = (input_op, cs3)`,
          `emit_op SDIV [input_op; Lit (n2w divisor)] cs3 = (op, st')`] >>
  (* Step 1: SGT *)
  `eval_operand (Lit 0w) ss = SOME 0w` by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst st.cs_next_id SGT [val_op; Lit 0w]
     [STRING #"%" (toString st.cs_next_var)]) ss =
   OK (update_var (STRING #"%" (toString st.cs_next_var))
       (bool_to_word (word_gt x 0w)) ss)`
    by (irule step_SGT >> simp[eval_operand_lit]) >>
  apply_emit_op2_f_tac `\a b. bool_to_word (word_gt a b)` >>
  (* Step 2: ADD *)
  `eval_operand val_op ss' = SOME x` by preserve_tac >>
  `eval_operand (Lit (n2w (divisor - 1))) ss' = SOME (n2w (divisor - 1))`
    by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst cs1.cs_next_id ADD
     [val_op; Lit (n2w (divisor - 1))]
     [STRING #"%" (toString cs1.cs_next_var)]) ss' =
   OK (update_var (STRING #"%" (toString cs1.cs_next_var))
       (x + n2w (divisor - 1)) ss')`
    by (irule step_ADD >> simp[eval_operand_lit]) >>
  apply_emit_op2_tac >>
  (* Step 3: compile_select *)
  `eval_operand is_pos_op ss'' = SOME (bool_to_word (word_gt x 0w))`
    by preserve_tac >>
  `eval_operand adj_op ss'' = SOME (x + n2w (divisor - 1))`
    by preserve_tac >>
  `eval_operand val_op ss'' = SOME x` by preserve_tac >>
  qspecl_then [`is_pos_op`, `adj_op`, `val_op`,
    `bool_to_word (word_gt x 0w)`,
    `x + n2w (divisor - 1)`, `x`,
    `word_gt x 0w`, `ss''`, `cs2`, `input_op`, `cs3`]
    mp_tac compile_select_correct >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `ss3` strip_assume_tac) >>
  (* Step 4: SDIV *)
  `eval_operand (Lit (n2w divisor)) ss3 = SOME (n2w divisor)`
    by simp[eval_operand_lit] >>
  `step_inst_base (mk_inst cs3.cs_next_id SDIV
     [input_op; Lit (n2w divisor)]
     [STRING #"%" (toString cs3.cs_next_var)]) ss3 =
   OK (update_var (STRING #"%" (toString cs3.cs_next_var))
       (safe_sdiv (if word_gt x 0w then x + n2w (divisor - 1) else x)
                  (n2w divisor)) ss3)`
    by (irule step_SDIV >> simp[eval_operand_lit]) >>
  apply_emit_op2_tac >>
  (* Compose all segments *)
  qexists `ss'''` >>
  conj_tac
  >- (
    `run_inst_seq (emitted_insts st cs2) ss = OK ss'' ∧
     cs2.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2`
      by compose_ok_tac (`ss'`, `cs1`) >>
    `run_inst_seq (emitted_insts st cs3) ss = OK ss3 ∧
     cs3.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs3`
      by compose_ok_tac (`ss''`, `cs2`) >>
    irule run_emitted_compose2 >>
    qexistsl [`ss3`, `cs3`] >> asm_rewrite_tac[])
  >> asm_rewrite_tac[]
QED

(* ===== System Builtins ===== *)

(* TODO: compile_raw_call_correct, compile_send_correct, and
   compile_raw_create_correct need proofs that reason about
   exec_ext_call / exec_ext_create, which invoke verifereum's `run`.
   Note: `run` always terminates (run_eq_tr from vfmDecreasesGasTheory),
   so the NONE branch in extract_venom_result is dead for the run result.
   The remaining difficulty is showing extract_venom_result returns SOME,
   which requires the callee's context stack to be a singleton on return. *)

(* raw_call: low-level CALL with optional output buffer *)
Theorem compile_raw_call_correct:
  ∀ to_op data_ptr data_len gas_op value_op
    call_ty max_outsize revert_on_failure ss st op st'
    tv dv dlv gv vv.
    compile_raw_call to_op data_ptr data_len gas_op value_op
      call_ty max_outsize revert_on_failure st = (op, st') ∧
    eval_operand to_op ss = SOME tv ∧
    eval_operand data_ptr ss = SOME dv ∧
    eval_operand data_len ss = SOME dlv ∧
    eval_operand gas_op ss = SOME gv ∧
    eval_operand value_op ss = SOME vv ∧
    fresh_vars_wrt st ss ⇒
    ∃ ss'.
      (* Either succeeds or reverts *)
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∨
       run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss')
Proof
  cheat
QED

(* send: CALL with zero-length data, asserts success *)
Theorem compile_send_correct:
  ∀ to_op value_op gas_op ss st st' tv vv gv.
    compile_send to_op value_op gas_op st = ((), st') ∧
    eval_operand to_op ss = SOME tv ∧
    eval_operand value_op ss = SOME vv ∧
    eval_operand gas_op ss = SOME gv ∧
    fresh_vars_wrt st ss ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Create Builtins ===== *)

(* NOTE: compile_raw_create_correct was ILL-TYPED as originally stated.
   compile_raw_create takes 5 args (bytecode_op, value_op, salt_opt,
   revert_on_failure, ctor_args_info) but the original had 6 positional args
   (code_ptr, code_len, value_op, salt_opt, revert_on_failure), making
   value_op (operand) land in the salt_opt (operand option) position.
   Corrected statement below pending task owner review. *)
Theorem compile_raw_create_correct:
  ∀ bytecode_op value_op salt_opt revert_on_failure ctor_args_info
    ss st op st' bv vv.
    compile_raw_create bytecode_op value_op salt_opt
      revert_on_failure ctor_args_info st = (op, st') ∧
    eval_operand bytecode_op ss = SOME bv ∧
    eval_operand value_op ss = SOME vv ∧
    fresh_vars_wrt st ss ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      (* CREATE failure with revert_on_failure → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED

(* ===== Bytes Builtins ===== *)

(* extract32: bounds-checked 32-byte load from bytestring *)
(* extract32: reads 32 bytes from src_ptr + 32 + start.
   OK path: start + 32 ≤ length at src_ptr → result = mload at data + start.
   Revert path: start + 32 > length → ASSERT fails. *)
Theorem compile_extract32_correct:
  ∀ src_ptr start_op ss st op st' pv sv.
    compile_extract32 src_ptr start_op st = (op, st') ∧
    eval_operand src_ptr ss = SOME pv ∧
    eval_operand start_op ss = SOME sv ∧
    fresh_vars_wrt st ss ⇒
    ∃ ss'.
      (run_inst_seq (emitted_insts st st') ss = OK ss' ∧
       eval_operand op ss' =
         SOME (mload (w2n (pv + 32w + sv)) ss)) ∨
      (* Out of bounds → revert *)
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  rpt strip_tac >>
  gvs[compile_extract32_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rename [`emit_op MLOAD [src_ptr] st = (src_len, cs1)`,
          `emit_op ADD [src_ptr; Lit 32w] cs1 = (src_data, cs2)`,
          `emit_op ADD [start_op; Lit 32w] cs2 = (end_op, cs3)`,
          `emit_op GT [end_op; src_len] cs3 = (oob, cs4)`,
          `emit_op ISZERO [oob] cs4 = (ok_op, cs5)`,
          `emit_void ASSERT [ok_op] cs5 = (_, cs6)`,
          `emit_op ADD [src_data; start_op] cs6 = (load_ptr, cs7)`,
          `emit_op MLOAD [load_ptr] cs7 = (op, st')`] >>
  imp_res_tac emit_op_extends >>
  imp_res_tac emit_void_extends >>
  (* Step 1: MLOAD[src_ptr] → src_len = mload(w2n pv) ss *)
  drule_all emit_op_MLOAD_correct >>
  disch_then (qx_choose_then `ss1` strip_assume_tac) >>
  (* Step 2: ADD[src_ptr; 32] → src_data = pv + 32w *)
  `eval_operand src_ptr ss1 = SOME pv` by preserve_tac >>
  `eval_operand (Lit 32w) ss1 = SOME 32w` by simp[eval_operand_lit] >>
  drule_all emit_op_ADD_correct >>
  disch_then (qx_choose_then `ss2` strip_assume_tac) >>
  (* Step 3: ADD[start_op; 32] → end_op = sv + 32w *)
  `eval_operand start_op ss2 = SOME sv` by preserve_tac >>
  `eval_operand (Lit 32w) ss2 = SOME 32w` by simp[eval_operand_lit] >>
  drule_all emit_op_ADD_correct >>
  disch_then (qx_choose_then `ss3` strip_assume_tac) >>
  (* Step 4: GT[end_op; src_len] → oob *)
  `eval_operand end_op ss3 = SOME (sv + 32w)` by preserve_tac >>
  `eval_operand src_len ss3 = SOME (mload (w2n pv) ss)` by preserve_tac >>
  drule_all emit_op_GT_correct >>
  disch_then (qx_choose_then `ss4` strip_assume_tac) >>
  (* Step 5: ISZERO[oob] → ok *)
  `eval_operand oob ss4 =
     SOME (bool_to_word (w2n (sv + 32w) > w2n (mload (w2n pv) ss)))` by
    preserve_tac >>
  drule_all emit_op_ISZERO_correct_mem >>
  disch_then (qx_choose_then `ss5` strip_assume_tac) >>
  (* Compose steps 1-5: st→cs5 *)
  `run_inst_seq (emitted_insts st cs2) ss = OK ss2 /\
   cs2.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs2`
    by compose_ok_tac (`ss1`, `cs1`) >>
  `run_inst_seq (emitted_insts st cs3) ss = OK ss3 /\
   cs3.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs3`
    by compose_ok_tac (`ss2`, `cs2`) >>
  `run_inst_seq (emitted_insts st cs4) ss = OK ss4 /\
   cs4.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs4`
    by compose_ok_tac (`ss3`, `cs3`) >>
  `run_inst_seq (emitted_insts st cs5) ss = OK ss5`
    by (irule run_emitted_compose2 >>
        qexistsl [`ss4`, `cs4`] >> asm_rewrite_tac[]) >>
  (* Step 6: ASSERT[ok] — case split *)
  `eval_operand ok_op ss5 =
     SOME (bool_to_word (bool_to_word (w2n (sv + 32w) > w2n (mload (w2n pv) ss)) = 0w))` by
    preserve_tac >>
  qabbrev_tac `oob_val = (w2n (sv + 32w) > w2n (mload (w2n pv) ss))` >>
  drule_all emit_void_ASSERT_ok_or_revert >> strip_tac >>
  gvs[]
  >- suspend "ok_case"
  >> suspend "revert_case"
QED

Resume compile_extract32_correct[ok_case]:
  (* Re-derive SHORT ext facts from emit_op/emit_void facts *)
  imp_res_tac emit_op_extends >>
  imp_res_tac emit_void_extends >>
  (* Step 7: ADD[src_data; start_op] → load_ptr = pv + 32w + sv *)
  `eval_operand src_data ss5 = SOME (pv + 32w)` by metis_tac[] >>
  `eval_operand start_op ss5 = SOME sv` by metis_tac[] >>
  drule_all emit_op_ADD_correct >>
  disch_then (qx_choose_then `ss6` strip_assume_tac) >>
  (* Step 8: MLOAD[load_ptr] → result *)
  `eval_operand load_ptr ss6 = SOME (pv + 32w + sv)` by preserve_tac >>
  qpat_x_assum `emit_op MLOAD [load_ptr] cs7 = (op, st')` mp_tac >>
  disch_then (fn mload8 =>
    qpat_x_assum `fresh_vars_wrt cs7 ss6` (fn fv =>
      qpat_x_assum `eval_operand load_ptr ss6 = _` (fn ev =>
        assume_tac ev >> assume_tac fv >>
        mp_tac (MATCH_MP (MATCH_MP (MATCH_MP
          (REWRITE_RULE [GSYM AND_IMP_INTRO] emit_op_MLOAD_correct)
          mload8) ev) fv)))) >>
  disch_then (qx_choose_then `ss7` strip_assume_tac) >>
  (* Memory preserved: ss5.vs_memory = ss.vs_memory, then chain through ss6 *)
  `ss5.vs_memory = ss.vs_memory` by
    (irule listTheory.LIST_EQ >>
     conj_tac >- fs[] >>
     rpt strip_tac >> fs[]) >>
  `ss6.vs_memory = ss5.vs_memory` by
    (irule listTheory.LIST_EQ >>
     conj_tac >- fs[] >>
     rpt strip_tac >> gvs[]) >>
  `ss6.vs_memory = ss.vs_memory` by asm_rewrite_tac[] >>
  (* Witness *)
  qexists `ss7` >> disj1_tac >>
  conj_tac
  >- (
    (* Derive short ext: cs4→cs5 and cs5 from st *)
    `cs5.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs5` by
      (irule emit_extends_trans >>
       qexists `cs4` >>
       conj_tac >- (
         irule emit_extends_trans >>
         qexists `cs3` >>
         conj_tac >- (
           irule emit_extends_trans >>
           qexists `cs2` >>
           conj_tac >- (
             irule emit_extends_trans >>
             qexists `cs1` >>
             asm_rewrite_tac[]) >>
           asm_rewrite_tac[]) >>
         asm_rewrite_tac[]) >>
       asm_rewrite_tac[]) >>
    (* Compose st→cs5 with cs5→cs6 using run_emitted_compose2 *)
    `run_inst_seq (emitted_insts st cs6) ss = OK ss5` by
      (irule run_emitted_compose2 >>
       qexistsl [`ss5`, `cs5`] >> asm_rewrite_tac[]) >>
    `cs6.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs6` by
      (irule emit_extends_trans >> qexists `cs5` >> asm_rewrite_tac[]) >>
    (* Compose st→cs6 with cs6→cs7 *)
    `cs7.cs_current_insts = cs6.cs_current_insts ++ emitted_insts cs6 cs7` by
      asm_rewrite_tac[] >>
    `run_inst_seq (emitted_insts st cs7) ss = OK ss6` by
      (irule run_emitted_compose2 >>
       qexistsl [`ss5`, `cs6`] >> asm_rewrite_tac[]) >>
    `cs7.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs7` by
      (irule emit_extends_trans >> qexists `cs6` >> asm_rewrite_tac[]) >>
    (* Compose st→cs7 with cs7→st' *)
    irule run_emitted_compose2 >>
    qexistsl [`ss6`, `cs7`] >> asm_rewrite_tac[])
  >> (* eval_operand op ss7 = SOME (mload ...) *)
    gvs[mload_def]
QED

Resume compile_extract32_correct[revert_case]:
  (* ok_op evaluates to 0w → ASSERT reverts *)
  drule_all emit_void_ASSERT_revert_full >> strip_tac >>
  (* Re-derive SHORT ext facts *)
  imp_res_tac emit_op_extends >>
  imp_res_tac emit_void_extends >>
  (* Derive cs5 ext from st *)
  `cs5.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs5` by
    (irule emit_extends_trans >> qexists `cs4` >>
     conj_tac >- (
       irule emit_extends_trans >> qexists `cs3` >>
       conj_tac >- (
         irule emit_extends_trans >> qexists `cs2` >>
         conj_tac >- (
           irule emit_extends_trans >> qexists `cs1` >>
           asm_rewrite_tac[]) >>
         asm_rewrite_tac[]) >>
       asm_rewrite_tac[]) >>
     asm_rewrite_tac[]) >>
  `cs6.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs6` by
    (irule emit_extends_trans >> qexists `cs5` >> asm_rewrite_tac[]) >>
  `cs7.cs_current_insts = st.cs_current_insts ++ emitted_insts st cs7` by
    (irule emit_extends_trans >> qexists `cs6` >> asm_rewrite_tac[]) >>
  `st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'` by
    (irule emit_extends_trans >> qexists `cs7` >> asm_rewrite_tac[]) >>
  (* Compose: OK prefix st→cs5 + abort cs5→cs6 → abort st→cs6 *)
  qspecl_then [`st`, `cs5`, `cs6`, `ss`, `ss5`, `Revert_abort`,
    `revert_state (set_returndata [] ss5)`]
    mp_tac run_emitted_compose2_abort >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Extend abort st→cs6 through cs7 *)
  qspecl_then [`st`, `cs6`, `cs7`, `ss`, `Revert_abort`,
    `revert_state (set_returndata [] ss5)`]
    mp_tac run_emitted_abort_extend >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  (* Extend abort st→cs7 through st' *)
  qexists `revert_state (set_returndata [] ss5)` >> disj2_tac >>
  qspecl_then [`st`, `cs7`, `st'`, `ss`, `Revert_abort`,
    `revert_state (set_returndata [] ss5)`]
    mp_tac run_emitted_abort_extend >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

Finalise compile_extract32_correct;

(* ===== Type Conversion ===== *)
(* compile_type_convert_correct moved to builtinTypeConvertPropsScript.sml
   for build time reasons (49 case arms × step_inst_base_def = slow). *)

(* ===== ABI Builtins ===== *)

(* BLOCKED: lower_abi_encode_correct and lower_abi_decode_correct depend on
   abiEncoderPropsTheory, which has 11 cheat lines (4 cheated theorems).
   These cannot be proved until the upstream cheats are resolved. *)

(* abi_encode: encode data into buffer with optional method_id *)
Theorem lower_abi_encode_correct:
  ∀ ensure_tuple method_id_opt src_op enc_info maxlen ss st op st' sv.
    lower_abi_encode ensure_tuple method_id_opt src_op enc_info maxlen st =
      (op, st') ∧
    eval_operand src_op ss = SOME sv ∧
    fresh_vars_wrt st ss ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss'
Proof
  cheat
QED

(* abi_decode: validate + decode ABI data into output buffer *)
Theorem lower_abi_decode_correct:
  ∀ data_op dec_info abi_min_size abi_max_size output_size ss st op st' dv.
    lower_abi_decode data_op dec_info abi_min_size abi_max_size output_size st =
      (op, st') ∧
    eval_operand data_op ss = SOME dv ∧
    fresh_vars_wrt st ss ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∨
      run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  cheat
QED
