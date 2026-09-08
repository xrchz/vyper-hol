(*
 * Lower DLOAD Pass -- Classification Theorem
 *
 * Proves step_inst_base_ld_ok_classify: for non-special opcodes,
 * stepping from ld_ok-related states preserves ld_ok.
 * Split from lowerDloadProofsScript.sml for build caching.
 *)

Theory lowerDloadClassify
Ancestors
  lowerDloadDefs stateEquiv venomExecProps venomInstProps instIdxIndep
  venomExecSemantics venomInst venomState finite_map opcodeClass

(* ===== Cross-block invariant ===== *)

Definition ld_ok_def:
  ld_ok vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_halted = s2.vs_halted /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_bb = s2.vs_prev_bb
End

(* ===== Basic ld_ok properties ===== *)

Theorem ld_ok_refl:
  !vars s. ld_ok vars s s
Proof
  simp[ld_ok_def]
QED

Theorem ld_ok_implies_ld_equiv:
  !vars s1 s2. ld_ok vars s1 s2 ==> ld_equiv vars s1 s2
Proof
  simp[ld_ok_def, ld_equiv_def]
QED

Theorem ld_ok_update_var:
  !vars v val s1 s2.
    ld_ok vars s1 s2 ==>
    ld_ok vars (update_var v val s1) (update_var v val s2)
Proof
  rw[ld_ok_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[] >> res_tac
QED

Theorem ld_ok_update_exempt:
  !vars v val1 val2 s1 s2.
    ld_ok vars s1 s2 /\ v IN vars ==>
    ld_ok vars (update_var v val1 s1) (update_var v val2 s2)
Proof
  rw[ld_ok_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[] >> res_tac
QED

Theorem ld_ok_update_var_s2_exempt:
  !vars v val s1 s2.
    ld_ok vars s1 s2 /\ v IN vars ==>
    ld_ok vars s1 (update_var v val s2)
Proof
  rw[ld_ok_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[] >> CCONTR_TAC >> gvs[] >> res_tac
QED

Theorem ld_ok_update_memory:
  !vars m1 m2 s1 s2.
    ld_ok vars s1 s2 ==>
    ld_ok vars (s1 with vs_memory := m1) (s2 with vs_memory := m2)
Proof
  rw[ld_ok_def, lookup_var_def]
QED

Theorem ld_ok_write_memory:
  !vars off bytes1 bytes2 s1 s2.
    ld_ok vars s1 s2 ==>
    ld_ok vars (write_memory_with_expansion off bytes1 s1)
               (write_memory_with_expansion off bytes2 s2)
Proof
  rw[ld_ok_def, write_memory_with_expansion_def, LET_THM,
     lookup_var_def]
QED

Theorem ld_ok_istore:
  !vars off val s1 s2.
    ld_ok vars s1 s2 ==>
    ld_ok vars (istore off val s1) (istore off val s2)
Proof
  rw[ld_ok_def, istore_def, mstore_def, lookup_var_def]
QED

(* ===== eval_operand agreement under ld_ok ===== *)

Theorem ld_eval_operand_agree:
  !op s1 s2 vars.
    ld_ok vars s1 s2 /\
    (!x. op = Var x ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases >> simp[eval_operand_def, ld_ok_def]
QED

Theorem resolve_phi_MEM:
  !prev ops val_op.
    resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  ho_match_mp_tac venomExecSemanticsTheory.resolve_phi_ind >>
  rw[resolve_phi_def] >> gvs[] >> res_tac >> simp[]
QED

(* ===== exec_* ld_ok preservation helpers ===== *)

fun ld_agree_op q =
  drule ld_eval_operand_agree >>
  disch_then (qspec_then q mp_tac) >>
  (impl_tac >- (rw[] >> res_tac)) >>
  strip_tac >> gvs[];

Theorem exec_pure1_ld_ok[local]:
  !f inst s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    exec_pure1 f inst s1 = OK s1' ==>
    ?s2'. exec_pure1 f inst s2 = OK s2' /\ ld_ok vars s1' s2'
Proof
  rw[exec_pure1_def, AllCaseEqs()] >> gvs[] >>
  ld_agree_op `op1` >>
  irule ld_ok_update_var >> simp[]
QED

Theorem exec_pure2_ld_ok[local]:
  !f inst s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    exec_pure2 f inst s1 = OK s1' ==>
    ?s2'. exec_pure2 f inst s2 = OK s2' /\ ld_ok vars s1' s2'
Proof
  rw[exec_pure2_def, AllCaseEqs()] >> gvs[] >>
  ld_agree_op `op1` >> ld_agree_op `op2` >>
  irule ld_ok_update_var >> simp[]
QED

Theorem exec_pure3_ld_ok[local]:
  !f inst s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    exec_pure3 f inst s1 = OK s1' ==>
    ?s2'. exec_pure3 f inst s2 = OK s2' /\ ld_ok vars s1' s2'
Proof
  rw[exec_pure3_def, AllCaseEqs()] >> gvs[] >>
  ld_agree_op `op1` >> ld_agree_op `op2` >> ld_agree_op `op3` >>
  irule ld_ok_update_var >> simp[]
QED

Theorem exec_read0_ld_ok[local]:
  !f inst s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    f s1 = f s2 /\
    exec_read0 f inst s1 = OK s1' ==>
    ?s2'. exec_read0 f inst s2 = OK s2' /\ ld_ok vars s1' s2'
Proof
  rw[exec_read0_def, AllCaseEqs()] >> gvs[] >>
  irule ld_ok_update_var >> simp[]
QED

Theorem exec_read1_ld_ok[local]:
  !f inst s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    (!v. f v s1 = f v s2) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    exec_read1 f inst s1 = OK s1' ==>
    ?s2'. exec_read1 f inst s2 = OK s2' /\ ld_ok vars s1' s2'
Proof
  rw[exec_read1_def, AllCaseEqs()] >> gvs[] >>
  ld_agree_op `op1` >>
  irule ld_ok_update_var >> simp[]
QED

Theorem exec_write2_ld_ok[local]:
  !f inst s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    (!v1 v2. ld_ok vars (f v1 v2 s1) (f v1 v2 s2)) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    exec_write2 f inst s1 = OK s1' ==>
    ?s2'. exec_write2 f inst s2 = OK s2' /\ ld_ok vars s1' s2'
Proof
  rw[exec_write2_def, AllCaseEqs()] >> gvs[] >>
  ld_agree_op `op1` >> ld_agree_op `op2` >>
  simp[]
QED


(* ===== Generic operand agreement tactic ===== *)

(* Derives eval_operand agreement for ALL operands in assumptions.
   After this, eval_operand calls on s2 are rewritten to match s1 values. *)
fun ld_agree_all_tac (asl, w) = let
  val ldok = valOf (List.find (can (match_term ``ld_ok vars s1 s2``)) asl)
  val (_, args) = strip_comb ldok
  val s1_tm = el 2 args
  val eval_pat = ``eval_operand (op:operand) ^s1_tm = SOME (v:bytes32)``
  val evals = List.filter (can (match_term eval_pat)) asl
  fun agree_one eval_asm = let
    val (_, args2) = strip_comb (lhs eval_asm)
    val op_tm = el 1 args2
  in
    drule ld_eval_operand_agree >>
    disch_then (qspec_then [QUOTE (term_to_string op_tm)] mp_tac) >>
    (impl_tac >- (rw[] >> res_tac)) >>
    strip_tac >> gvs[]
  end
in
  (EVERY (map agree_one evals)) (asl, w)
end;

(* ===== Main classification theorem ===== *)

(* Strategy: unfold step_inst_base for s1 (in assumptions) and s2 (in goal),
   then for each opcode class, dispatch to the right helper.
   The key insight: for the "special" opcodes handled by the generic fallback,
   we case-split and then derive operand agreement to close each branch. *)
val ld_classify_one_tac =
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >> strip_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  (* Fast path: exec_pure helpers (ADD, SUB, MUL, ...) ~45 opcodes *)
  TRY (
    (drule_all exec_pure1_ld_ok ORELSE
     drule_all exec_pure2_ld_ok ORELSE
     drule_all exec_pure3_ld_ok) >> simp[] >> NO_TAC) >>
  (* exec_read0: state-read, no operands *)
  TRY (
    irule exec_read0_ld_ok >> rpt (first_assum (irule_at Any)) >>
    gvs[ld_ok_def] >> NO_TAC) >>
  (* exec_read1: state-read with 1 operand *)
  TRY (
    irule exec_read1_ld_ok >> rpt (first_assum (irule_at Any)) >>
    rw[sload_def, tload_def, contract_storage_def, contract_transient_def] >>
    gvs[ld_ok_def] >> NO_TAC) >>
  (* exec_write2: MSTORE/MSTORE8/SSTORE/TSTORE *)
  TRY (
    irule exec_write2_ld_ok >> rpt (first_assum (irule_at Any)) >>
    simp[mstore_def, mstore8_def, sstore_def, tstore_def, LET_THM] >>
    rpt strip_tac >> fs[ld_ok_def, lookup_var_def] >> NO_TAC) >>
  (* NOP: OK s unchanged *)
  TRY (gvs[] >> NO_TAC) >>
  (* PHI: resolve_phi gives same val_op on both sides, derive agreement *)
  TRY (
    gvs[AllCaseEqs()] >>
    imp_res_tac resolve_phi_MEM >>
    drule ld_eval_operand_agree >>
    disch_then (qspec_then `val_op` mp_tac) >>
    (impl_tac >- (rw[] >> res_tac)) >>
    strip_tac >>
    simp[step_inst_base_def] >>
    gvs[] >>
    qexists_tac `update_var out v s2` >>
    gvs[ld_ok_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
    metis_tac[] >> NO_TAC) >>
  (* Generic fallback: ASSERT, ASSERT_UNREACHABLE, CODECOPY, CALLDATACOPY,
     ISTORE, PARAM, OFFSET — derive agreements, resolve cases, close.
     Key: gvs[AllCaseEqs()] resolves s1 case assumptions, ld_agree_all_tac
     derives eval_operand agreement, then structured closers handle result. *)
  gvs[AllCaseEqs()] >>
  TRY (imp_res_tac resolve_phi_MEM) >>
  TRY ld_agree_all_tac >>
  gvs[] >>
  TRY (irule ld_ok_update_var >> gvs[ld_ok_def] >> NO_TAC) >>
  TRY (irule ld_ok_write_memory >> gvs[ld_ok_def] >> NO_TAC) >>
  TRY (irule ld_ok_istore >> gvs[ld_ok_def] >> NO_TAC) >>
  gvs[ld_ok_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE];

Theorem hidden_output_ld_ok_probe[local]:
  !inst s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    (inst.inst_opcode = GETFMP \/
     inst.inst_opcode = INITIAL_FMP \/
     inst.inst_opcode = RETPC_PARAM \/
     inst.inst_opcode = DALLOCA) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    step_inst_base inst s1 = OK s1' ==>
    ?s2'. step_inst_base inst s2 = OK s2' /\ ld_ok vars s1' s2'
Proof
  gen_tac >> Cases_on `inst.inst_opcode` >> simp[] >> ld_classify_one_tac
QED

Theorem step_inst_base_ld_ok_classify:
  !inst s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> DLOAD /\
    inst.inst_opcode <> DLOADBYTES /\
    inst.inst_opcode <> ALLOCA /\
    ~reads_memory inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    step_inst_base inst s1 = OK s1' ==>
    ?s2'. step_inst_base inst s2 = OK s2' /\ ld_ok vars s1' s2'
Proof
  gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[is_terminator_def, reads_memory_def]
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
  >- ld_classify_one_tac
QED

Theorem ld_step_passthrough:
  !inst fuel ctx s1 s2 vars s1'.
    ld_ok vars s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> DLOAD /\
    inst.inst_opcode <> DLOADBYTES /\
    inst.inst_opcode <> ALLOCA /\
    ~reads_memory inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    step_inst fuel ctx inst s1 = OK s1' ==>
    ?s2'. step_inst fuel ctx inst s2 = OK s2' /\
          ld_ok vars s1' s2'
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke] >>
  irule step_inst_base_ld_ok_classify >>
  metis_tac[]
QED

(* ===== ld_ok symmetry ===== *)

Theorem ld_ok_sym:
  !vars s1 s2. ld_ok vars s1 s2 ==> ld_ok vars s2 s1
Proof
  simp[ld_ok_def] >> metis_tac[]
QED

(* ===== Full simulation (all result types) ===== *)

(* Derive from step_inst_base_ld_ok_classify + ld_ok_sym:
   If s1 returns non-OK, then s2 also returns non-OK.
   Proof: if s2 returned OK, by classify applied to s2->s1 (via ld_ok_sym),
   s1 would also return OK -- contradiction. *)
Theorem step_inst_base_ld_ok_non_ok:
  !inst s1 s2 vars.
    ld_ok vars s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> DLOAD /\
    inst.inst_opcode <> DLOADBYTES /\
    inst.inst_opcode <> ALLOCA /\
    ~reads_memory inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    (!s1'. step_inst_base inst s1 <> OK s1') ==>
    (!s2'. step_inst_base inst s2 <> OK s2')
Proof
  rpt strip_tac >>
  imp_res_tac ld_ok_sym >>
  drule_all step_inst_base_ld_ok_classify >>
  strip_tac >> gvs[]
QED

(* For the full version, we also need to classify non-OK results.
   Non-terminator non-INVOKE opcodes produce only OK, Error, or Abort.
   When both sides are non-OK, we need to show they match (Error/Error
   or Abort/Abort with same type and ld_equiv).

   Strategy: case split on step_inst_base results for both sides.
   - OK/OK: handled by step_inst_base_ld_ok_classify
   - non-OK/OK or OK/non-OK: impossible by step_inst_base_ld_ok_non_ok
   - Error/Error: trivially lift_result
   - Abort/Abort: need same abort type + ld_equiv
   - Halt/IntRet: impossible for non-terminators
   - Error/Abort or Abort/Error: need to rule out

   The Error/Abort mismatch is the tricky part. We handle it by
   observing that step_inst_base evaluates the same way on ld_ok states
   (same operands, same branches), so the result constructor must match.

   Rather than re-doing 65-opcode dispatch, we observe:
   - Only ASSERT and ASSERT_UNREACHABLE can Abort (among non-terminators)
   - For those 2 opcodes, prove the full classification directly
*)

(* ASSERT/ASSERT_UNREACHABLE: direct full classification *)
Theorem step_inst_base_assert_full[local]:
  !inst s1 s2 vars.
    ld_ok vars s1 s2 /\
    (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    (?s1' s2'. step_inst_base inst s1 = OK s1' /\
               step_inst_base inst s2 = OK s2' /\ ld_ok vars s1' s2') \/
    (?e1 e2. step_inst_base inst s1 = Error e1 /\
             step_inst_base inst s2 = Error e2) \/
    (?a v1 v2. step_inst_base inst s1 = Abort a v1 /\
               step_inst_base inst s2 = Abort a v2 /\
               ld_equiv vars v1 v2)
Proof
  rpt strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  drule ld_eval_operand_agree >>
  disch_then (qspec_then `h` mp_tac) >>
  (impl_tac >- (rw[] >> res_tac)) >> strip_tac >> gvs[] >>
  Cases_on `eval_operand h s2` >> gvs[] >>
  Cases_on `x = 0w` >> gvs[] >>
  simp[ld_equiv_def, halt_state_def, revert_state_def,
       set_returndata_def, lookup_var_def] >>
  gvs[ld_ok_def, lookup_var_def]
QED

(* For "boring" opcodes (non-terminator, non-INVOKE, non-DLOAD/DLOADBYTES/ALLOCA,
   non-reads_memory, non-ASSERT/ASSERT_UNREACHABLE), step_inst_base only returns
   OK or Error. This covers Halt, IntRet AND Abort impossibility in one theorem. *)
Triviality exec_result_helpers_no_halt_abort_ld[simp]:
  (!f inst s s'. exec_pure1 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure1 f inst s <> Abort a s') /\
  (!f inst s s'. exec_pure2 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure2 f inst s <> Abort a s') /\
  (!f inst s s'. exec_pure3 f inst s <> Halt s') /\
  (!f inst s a s'. exec_pure3 f inst s <> Abort a s') /\
  (!f inst s s'. exec_read0 f inst s <> Halt s') /\
  (!f inst s a s'. exec_read0 f inst s <> Abort a s') /\
  (!f inst s s'. exec_read1 f inst s <> Halt s') /\
  (!f inst s a s'. exec_read1 f inst s <> Abort a s') /\
  (!f inst s s'. exec_write2 f inst s <> Halt s') /\
  (!f inst s a s'. exec_write2 f inst s <> Abort a s') /\
  (!inst s alloc_size s'. exec_alloca inst s alloc_size <> Halt s') /\
  (!inst s alloc_size a s'. exec_alloca inst s alloc_size <> Abort a s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_result_helpers_not_intret_ld[simp]:
  (!f inst s vs s'. exec_pure1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure2 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_pure3 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read0 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_read1 f inst s <> IntRet vs s') /\
  (!f inst s vs s'. exec_write2 f inst s <> IntRet vs s') /\
  (!inst s alloc_size vs s'. exec_alloca inst s alloc_size <> IntRet vs s')
Proof
  rw[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_alloca_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_not_intret_ld[simp]:
  (!inst s g a v ao as_ ro rs is_s vs s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> IntRet vs s') /\
  (!inst s g a ao as_ ro rs vs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> IntRet vs s') /\
  (!inst s v off sz salt vs s'.
     exec_create inst s v off sz salt <> IntRet vs s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Triviality exec_call_helpers_no_halt_abort_ld[simp]:
  (!inst s g a v ao as_ ro rs is_s s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Halt s') /\
  (!inst s g a v ao as_ ro rs is_s ab s'.
     exec_ext_call inst s g a v ao as_ ro rs is_s <> Abort ab s') /\
  (!inst s g a ao as_ ro rs s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Halt s') /\
  (!inst s g a ao as_ ro rs ab s'.
     exec_delegatecall inst s g a ao as_ ro rs <> Abort ab s') /\
  (!inst s v off sz salt s'.
     exec_create inst s v off sz salt <> Halt s') /\
  (!inst s v off sz salt ab s'.
     exec_create inst s v off sz salt <> Abort ab s')
Proof
  rw[exec_ext_call_def, exec_delegatecall_def, exec_create_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()]
QED

Theorem step_inst_base_no_halt_ld[local]:
  !inst s s'.
    step_inst_base inst s = Halt s' ==>
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  drule step_inst_base_halt_opcodes >> strip_tac >>
  gvs[is_terminator_def]
QED

Theorem step_inst_base_no_intret_ld[local]:
  !inst s vs s'.
    step_inst_base inst s = IntRet vs s' ==>
    is_terminator inst.inst_opcode
Proof
  rpt strip_tac >>
  drule step_inst_base_intret_opcodes >> strip_tac >>
  gvs[is_terminator_def]
QED

Theorem step_inst_base_abort_opcode_ld[local]:
  !inst s a s'.
    step_inst_base inst s = Abort a s' /\
    ~is_terminator inst.inst_opcode ==>
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY
Proof
  rpt strip_tac >>
  drule step_inst_base_abort_opcodes >> strip_tac >>
  gvs[is_terminator_def]
QED

Theorem step_inst_base_not_halt_abort[local]:
  !inst s.
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> DLOAD /\
    inst.inst_opcode <> DLOADBYTES /\
    inst.inst_opcode <> ALLOCA /\
    ~reads_memory inst.inst_opcode /\
    inst.inst_opcode <> ASSERT /\
    inst.inst_opcode <> ASSERT_UNREACHABLE ==>
    (!v. step_inst_base inst s <> Halt v) /\
    (!w v. step_inst_base inst s <> IntRet w v) /\
    (!a v. step_inst_base inst s <> Abort a v)
Proof
  rpt strip_tac
  >- metis_tac[step_inst_base_no_halt_ld]
  >- metis_tac[step_inst_base_no_intret_ld] >>
  drule_all step_inst_base_abort_opcode_ld >>
  strip_tac >>
  gvs[reads_memory_def]
QED

(* Main full classification: derived from classify + sym + assert + not_halt_abort *)
Theorem step_inst_base_ld_ok_full:
  !inst s1 s2 vars.
    ld_ok vars s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode <> DLOAD /\
    inst.inst_opcode <> DLOADBYTES /\
    inst.inst_opcode <> ALLOCA /\
    ~reads_memory inst.inst_opcode /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    (?s1' s2'. step_inst_base inst s1 = OK s1' /\
               step_inst_base inst s2 = OK s2' /\ ld_ok vars s1' s2') \/
    (?e1 e2. step_inst_base inst s1 = Error e1 /\
             step_inst_base inst s2 = Error e2) \/
    (?a v1 v2. step_inst_base inst s1 = Abort a v1 /\
               step_inst_base inst s2 = Abort a v2 /\
               ld_equiv vars v1 v2)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ASSERT \/
            inst.inst_opcode = ASSERT_UNREACHABLE`
  >- (drule_all step_inst_base_assert_full >> metis_tac[]) >>
  (* For all other "boring" opcodes, only OK or Error possible *)
  `(!v. step_inst_base inst s1 <> Halt v) /\
   (!w v. step_inst_base inst s1 <> IntRet w v) /\
   (!a v. step_inst_base inst s1 <> Abort a v)` by
    (irule step_inst_base_not_halt_abort >> gvs[]) >>
  `(!v. step_inst_base inst s2 <> Halt v) /\
   (!w v. step_inst_base inst s2 <> IntRet w v) /\
   (!a v. step_inst_base inst s2 <> Abort a v)` by
    (irule step_inst_base_not_halt_abort >> gvs[]) >>
  Cases_on `step_inst_base inst s1` >> gvs[]
  >- ((* OK s1' — goal is ∃s2'. ... = OK s2' /\ ld_ok ... *)
      drule_all step_inst_base_ld_ok_classify >> metis_tac[])
  >- ((* Error e1 — goal is ∃e2. ... = Error e2 *)
      `!s1'. step_inst_base inst s1 <> OK s1'` by gvs[] >>
      drule_all step_inst_base_ld_ok_non_ok >> strip_tac >>
      Cases_on `step_inst_base inst s2` >> gvs[])
QED

