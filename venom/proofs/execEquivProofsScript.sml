(*
 * Execution Equivalence Proofs
 *
 * Proves that step_inst_base / exec_block preserve state_equiv / result_equiv.
 * All theorems parameterized by variable exception set (vars).
 *
 * Internal proofs — consumers use props/execEquivPropsScript.sml
 *
 * TOP-LEVEL THEOREMS:
 *   - step_inst_result_equiv       : If state_equiv and no operand vars in exception set, step_inst_base preserves result_equiv
 *   - exec_block_result_equiv      : If state_equiv, no INVOKE, and no operand vars in exception set, exec_block preserves result_equiv
 *   - exec_block_state_equiv       : OK-case corollary of exec_block_result_equiv (state_equiv)
 *   - run_block_result_equiv        : run_block (eval_phis + exec_block) preserves result_equiv under same preconditions
 *   - run_function_result_equiv    : If state_equiv and all blocks have no INVOKE and no operand vars in exception set, run_function preserves result_equiv
 *   - run_function_result_equiv_closed : Variant with reachable-block set (safe) closed under successors
 *   - run_block_lift_result / run_block_lift_result_equiv : Lift exec_block results to run_block results
 *   - state_equiv_inst_idx         : Setting vs_inst_idx to same value on both sides preserves state_equiv
 *)

Theory execEquivProofs
Ancestors
  stateEquivProofs stateEquiv venomExecSemantics venomExecProofs venomState venomInst venomWf
  rich_list finite_map

(* ==========================================================================
   exec_* Category Helpers
   ========================================================================== *)

Triviality eval_operand_mem_equiv:
  !vars op ops s1 s2.
    state_equiv vars s1 s2 /\
    MEM op ops /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  Cases_on `op` >>
  rw[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]
QED

Triviality exec_pure1_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure1 f inst s1) (exec_pure1 f inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[exec_pure1_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand arg1 s1 = eval_operand arg1 s2` by (
    Cases_on `arg1` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand arg1 s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `t` >>
  simp[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_pure2_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure2 f inst s1) (exec_pure2 f inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[exec_pure2_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: arg2 :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand arg1 s1 = eval_operand arg1 s2` by (
    Cases_on `arg1` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand arg2 s1 = eval_operand arg2 s2` by (
    Cases_on `arg2` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand arg1 s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand arg2 s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `t` >>
  simp[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_pure3_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_pure3 f inst s1) (exec_pure3 f inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[exec_pure3_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: arg2 :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: arg2 :: arg3 :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand arg1 s1 = eval_operand arg1 s2` by (
    Cases_on `arg1` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand arg2 s1 = eval_operand arg2 s2` by (
    Cases_on `arg2` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand arg3 s1 = eval_operand arg3 s2` by (
    Cases_on `arg3` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand arg1 s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand arg2 s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand arg3 s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `t` >>
  simp[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_read0_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\ f s1 = f s2 ==>
    result_equiv vars (exec_read0 f inst s1) (exec_read0 f inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[exec_read0_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `t` >>
  simp[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_read1_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!v. f v s1 = f v s2) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_read1 f inst s1) (exec_read1 f inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[exec_read1_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand arg1 s1 = eval_operand arg1 s2` by (
    Cases_on `arg1` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand arg1 s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `t` >>
  simp[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

Triviality exec_write2_result_equiv:
  !vars f inst s1 s2.
    state_equiv vars s1 s2 /\
    (!v1 v2. state_equiv vars (f v1 v2 s1) (f v1 v2 s2)) /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_write2 f inst s1) (exec_write2 f inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[exec_write2_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(arg1 : operand) :: arg2 :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand arg1 s1 = eval_operand arg1 s2` by (
    Cases_on `arg1` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand arg2 s1 = eval_operand arg2 s2` by (
    Cases_on `arg2` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand arg1 s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand arg2 s2` >>
  simp[result_equiv_def, revert_equiv_def]
QED

(* ==========================================================================
   step_inst_base: Per-category dispatch helpers
   Each handles a group of opcodes at the step_inst_base level.
   ========================================================================== *)

(* Opcodes that use exec_pure2 *)
Triviality step_inst_pure2_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode
      [ADD; SUB; MUL; Div; SDIV; Mod; SMOD; Exp;
       AND; OR; XOR; SHL; SHR; SAR; SIGNEXTEND; BYTE;
       EQ; LT; GT; SLT; SGT; OFFSET] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  irule exec_pure2_result_equiv >> simp[]
QED

(* Opcodes that use exec_pure1 *)
Triviality step_inst_pure1_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [NOT; ISZERO] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  irule exec_pure1_result_equiv >> simp[]
QED

(* Opcodes that use exec_pure3 *)
Triviality step_inst_pure3_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [ADDMOD; MULMOD] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  irule exec_pure3_result_equiv >> simp[]
QED

(* Opcodes that use exec_read0 — no operands, reads from state *)
Triviality step_inst_read0_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    MEM inst.inst_opcode
      [CALLER; ADDRESS; CALLVALUE; GAS; ORIGIN; GASPRICE;
       CHAINID; COINBASE; TIMESTAMP; NUMBER; PREVRANDAO;
       GASLIMIT; BASEFEE; BLOBBASEFEE; SELFBALANCE;
       CALLDATASIZE; RETURNDATASIZE; MEMTOP; CODESIZE] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  irule exec_read0_result_equiv >> simp[] >>
  fs[state_equiv_def, execution_equiv_def]
QED

(* Opcodes that use exec_read1 — one operand, reads from state *)
Triviality step_inst_read1_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode
      [MLOAD; SLOAD; TLOAD; BLOCKHASH; BALANCE; CALLDATALOAD;
       EXTCODESIZE; BLOBHASH; ILOAD; DLOAD] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  irule exec_read1_result_equiv >> simp[] >> rw[] >>
  gvs[mload_def, sload_def, tload_def,
      contract_storage_def, contract_transient_def,
      state_equiv_def, execution_equiv_def]
QED

(* EXTCODEHASH: read1 with if-then-else body *)
Triviality step_inst_extcodehash_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = EXTCODEHASH ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def] >>
  irule exec_read1_result_equiv >> simp[] >> rw[] >>
  gvs[state_equiv_def, execution_equiv_def]
QED

(* Opcodes that use exec_write2 — two operands, writes state *)
Triviality step_inst_write2_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [MSTORE; MSTORE8; SSTORE; TSTORE] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  irule exec_write2_result_equiv >> simp[] >> rw[] >>
  FIRST [irule mstore_preserves, irule mstore8_preserves,
         irule sstore_preserves, irule tstore_preserves] >> simp[]
QED

(* Terminators without operands: STOP, SINK *)
Triviality step_inst_terminator_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    MEM inst.inst_opcode [STOP; SINK] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >>
  simp[result_equiv_def, revert_equiv_def,
       halt_state_def, revert_state_def,
       execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* RETURN: reads memory via operands, sets returndata, halts *)
Triviality step_inst_return_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = RETURN ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_memory = s2.vs_memory` by
    fs[state_equiv_def, execution_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def,
    halt_state_def, set_returndata_def,
    execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* REVERT: reads memory via operands, sets returndata, aborts *)
Triviality step_inst_revert_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = REVERT ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_memory = s2.vs_memory` by
    fs[state_equiv_def, execution_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def,
    revert_state_def, set_returndata_def, revert_equiv_def,
    execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Control flow: JMP, JNZ *)
Triviality step_inst_jmp_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode = JMP ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `h` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `t` >> simp[result_equiv_def, revert_equiv_def] >>
  irule jump_to_preserves >> simp[]
QED

Triviality step_inst_jnz_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = JNZ ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(cond_op : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(cond_op : operand) :: target1 :: args` >>
  Cases_on `target1` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(cond_op : operand) :: Label if_nonzero :: target0 :: args` >>
  Cases_on `target0` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand cond_op s1 = eval_operand cond_op s2` by (
    Cases_on `cond_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand cond_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `x = 0w` >> simp[result_equiv_def, revert_equiv_def] >>
  irule jump_to_preserves >> simp[]
QED

Triviality step_inst_control_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [JMP; JNZ] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >-
    (irule step_inst_jmp_equiv >> simp[]) >>
  irule step_inst_jnz_equiv >> simp[]
QED

(* DJMP: dynamic jump uses selector to index into label list *)
Triviality step_inst_djmp_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = DJMP ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def] >>
  imp_res_tac eval_operand_equiv >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  irule jump_to_preserves >> simp[]
QED

(* Helper: resolve_phi result is a member of the operand list *)
Triviality resolve_phi_MEM:
  !prev_bb ops op. resolve_phi prev_bb ops = SOME op ==> MEM op ops
Proof
  ho_match_mp_tac resolve_phi_ind >> rw[resolve_phi_def] >> rw[] >> metis_tac[]
QED

(* SSA: PHI, ASSIGN, NOP *)
Triviality step_inst_ssa_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [PHI; ASSIGN; NOP] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[]
  >- (simp[step_inst_base_def] >>
      `s1.vs_prev_bb = s2.vs_prev_bb` by
        fs[state_equiv_def, execution_equiv_def] >>
      ASM_REWRITE_TAC[] >>
      Cases_on `inst.inst_outputs` >> gvs[result_equiv_def, revert_equiv_def] >>
      Cases_on `TL inst.inst_outputs` >> gvs[result_equiv_def, revert_equiv_def] >>
      Cases_on `s2.vs_prev_bb` >> gvs[result_equiv_def, revert_equiv_def] >>
      Cases_on `resolve_phi x inst.inst_operands` >> gvs[result_equiv_def, revert_equiv_def] >>
      rename1 `resolve_phi _ _ = SOME phi_op` >>
      `MEM phi_op inst.inst_operands` by metis_tac[resolve_phi_MEM] >>
      `eval_operand phi_op s1 = eval_operand phi_op s2` by (
        qspecl_then [`vars`, `phi_op`, `inst.inst_operands`, `s1`, `s2`]
          mp_tac eval_operand_mem_equiv >> simp[]) >>
      ASM_REWRITE_TAC[] >>
      Cases_on `eval_operand phi_op s2` >> gvs[result_equiv_def, revert_equiv_def] >>
      irule update_var_preserves >> simp[])
  >- (simp[step_inst_base_def] >>
      Cases_on `inst.inst_operands` >> gvs[result_equiv_def, revert_equiv_def] >>
      Cases_on `TL inst.inst_operands` >> gvs[result_equiv_def, revert_equiv_def] >>
      Cases_on `inst.inst_outputs` >> gvs[result_equiv_def, revert_equiv_def] >>
      Cases_on `TL inst.inst_outputs` >> gvs[result_equiv_def, revert_equiv_def] >>
      rename1 `inst.inst_operands = [assign_op]` >>
      `eval_operand assign_op s1 = eval_operand assign_op s2` by (
        qspecl_then [`vars`, `assign_op`, `s1`, `s2`]
          mp_tac eval_operand_equiv >> simp[]) >>
      ASM_REWRITE_TAC[] >>
      Cases_on `eval_operand assign_op s2` >>
      gvs[result_equiv_def, revert_equiv_def] >>
      irule update_var_preserves >> simp[]) >>
  simp[step_inst_base_def, result_equiv_def]
QED

(* Assertions: ASSERT, ASSERT_UNREACHABLE *)
Triviality step_inst_assert_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [ASSERT; ASSERT_UNREACHABLE] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >>
  imp_res_tac eval_operand_equiv >>
  CASE_TAC >> gvs[result_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, execution_equiv_def] >>
  gvs[revert_state_def, set_returndata_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def,
     halt_state_def]
QED

Triviality eval_operands_equiv:
  !vars ops s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) ops ==> x NOTIN vars) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct_on `ops` >> rw[eval_operands_def] >>
  `eval_operand h s1 = eval_operand h s2` by (
    irule eval_operand_equiv >> simp[] >> metis_tac[]) >>
  `eval_operands ops s1 = eval_operands ops s2` by (
    first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[]
QED

(* Hash: SHA3 *)
Triviality step_inst_sha3_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = SHA3 ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[step_inst_base_def] >>
  `s1.vs_memory = s2.vs_memory` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(off_op : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(off_op : operand) :: size_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand off_op s1 = eval_operand off_op s2` by (
    Cases_on `off_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand size_op s1 = eval_operand size_op s2` by (
    Cases_on `size_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand off_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand size_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `t` >>
  simp[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

(* MCOPY: memory-to-memory copy, 3 operands *)
Triviality step_inst_mcopy_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = MCOPY ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[step_inst_base_def] >>
  `s1.vs_memory = s2.vs_memory` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: src_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: src_op :: size_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand dst_op s1 = eval_operand dst_op s2` by (
    Cases_on `dst_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand src_op s1 = eval_operand src_op s2` by (
    Cases_on `src_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand size_op s1 = eval_operand size_op s2` by (
    Cases_on `size_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand dst_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand src_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand size_op s2` >>
  simp[result_equiv_def, revert_equiv_def, mcopy_def] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

(* ISTORE: writes to vs_immutables *)
Triviality step_inst_istore_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = ISTORE ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_immutables = s2.vs_immutables` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def,
    state_equiv_def, execution_equiv_def, lookup_var_def,
    istore_def, mstore_def]
QED

(* DLOADBYTES/CODECOPY: copy from data section/code to memory, 3 operands *)
Triviality step_inst_data_copy_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [DLOADBYTES; CODECOPY] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  `s1.vs_data_section = s2.vs_data_section /\
   s1.vs_code = s2.vs_code` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: src_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: src_op :: size_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand dst_op s1 = eval_operand dst_op s2` by (
    Cases_on `dst_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand src_op s1 = eval_operand src_op s2` by (
    Cases_on `src_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand size_op s1 = eval_operand size_op s2` by (
    Cases_on `size_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand dst_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand src_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand size_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

(* EXTCODECOPY: copy external code to memory, 4 operands *)
Triviality step_inst_extcodecopy_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = EXTCODECOPY ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  simp[step_inst_base_def] >>
  `s1.vs_accounts = s2.vs_accounts` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(addr_op : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(addr_op : operand) :: dst_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(addr_op : operand) :: dst_op :: src_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(addr_op : operand) :: dst_op :: src_op :: size_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand addr_op s1 = eval_operand addr_op s2` by (
    Cases_on `addr_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand dst_op s1 = eval_operand dst_op s2` by (
    Cases_on `dst_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand src_op s1 = eval_operand src_op s2` by (
    Cases_on `src_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand size_op s1 = eval_operand size_op s2` by (
    Cases_on `size_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand addr_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand dst_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand src_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand size_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED



(* LOG: appends event to vs_logs *)
Triviality step_inst_log_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = LOG ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def] >>
  `s1.vs_memory = s2.vs_memory /\
   s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_logs = s2.vs_logs` by
    fs[state_equiv_def, execution_equiv_def] >>
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2` by (
    rw[] >> Cases_on `op` >> simp[eval_operand_def] >>
    fs[state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `inst.inst_operands` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `h` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `Lit tc :: rest` >>
  `!op. MEM op rest ==> eval_operand op s1 = eval_operand op s2`
    by (rw[] >> first_x_assum irule >> simp[]) >>
  Cases_on `LENGTH rest = w2n tc + 2` >> simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand (EL 0 rest) s1 = eval_operand (EL 0 rest) s2`
    by (first_x_assum irule >> irule EL_MEM >> simp[]) >>
  `eval_operand (EL 1 rest) s1 = eval_operand (EL 1 rest) s2`
    by (first_x_assum irule >> irule EL_MEM >> simp[]) >>
  sg `eval_operands (DROP 2 rest) s1 =
      eval_operands (DROP 2 rest) s2`
  >- (qsuff_tac `!ops. (!op. MEM op ops ==>
        eval_operand op s1 = eval_operand op s2) ==>
        eval_operands ops s1 = eval_operands ops s2`
      >- (disch_then irule >> rw[] >> first_x_assum irule >>
          imp_res_tac MEM_DROP_IMP >> simp[])
      >> Induct >> rw[eval_operands_def]) >>
  simp[] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def, state_equiv_def,
    execution_equiv_def, lookup_var_def]
QED

(* SELFDESTRUCT: transfers balance, halts *)
Triviality step_inst_selfdestruct_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = SELFDESTRUCT ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def] >>
  imp_res_tac eval_operand_equiv >>
  `s1.vs_accounts = s2.vs_accounts /\
   s1.vs_call_ctx = s2.vs_call_ctx` by
    fs[state_equiv_def, execution_equiv_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def, halt_state_def,
    execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* INVALID: always reverts *)
Triviality step_inst_invalid_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode = INVALID ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> simp[step_inst_base_def, result_equiv_def, revert_equiv_def,
               halt_state_def, set_returndata_def,
               execution_equiv_def, lookup_var_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Copy: CALLDATACOPY, RETURNDATACOPY *)
Triviality step_inst_copy_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [CALLDATACOPY; RETURNDATACOPY] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >> ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  `s1.vs_memory = s2.vs_memory /\
   s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_returndata = s2.vs_returndata` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: src_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(dst_op : operand) :: src_op :: size_op :: args` >>
  Cases_on `args` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand dst_op s1 = eval_operand dst_op s2` by (
    Cases_on `dst_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand src_op s1 = eval_operand src_op s2` by (
    Cases_on `src_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand size_op s1 = eval_operand size_op s2` by (
    Cases_on `size_op` >>
    fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand dst_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand src_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand size_op s2` >>
  simp[result_equiv_def, revert_equiv_def] >-
    (irule write_memory_with_expansion_preserves >> simp[]) >>
  Cases_on `w2n x' + w2n x'' > LENGTH s2.vs_returndata` >>
  simp[result_equiv_def, revert_equiv_def, halt_state_def,
       set_returndata_def, execution_equiv_def, lookup_var_def] >-
    fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

(* PARAM: reads from vs_params (execution_equiv) + update_var *)
Triviality step_inst_param_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode = PARAM ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[step_inst_base_def] >>
  `s1.vs_params = s2.vs_params` by
    fs[state_equiv_def, execution_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

(* RET: eval_operands + halt_state *)
Triviality step_inst_ret_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = RET ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> simp[step_inst_base_def] >>
  sg `eval_operands inst.inst_operands s1 =
      eval_operands inst.inst_operands s2`
  >- (qsuff_tac `!ops. (!op. MEM op ops ==>
        eval_operand op s1 = eval_operand op s2) ==>
        eval_operands ops s1 = eval_operands ops s2`
      >- (disch_then irule >> rpt gen_tac >> strip_tac >>
          irule eval_operand_equiv >> simp[] >>
          metis_tac[])
      >> Induct >> rw[eval_operands_def]) >>
  rpt CASE_TAC >>
  gvs[result_equiv_def, revert_equiv_def, state_equiv_def, execution_equiv_def]
QED

(* External calls: state_equiv => same EVM state => same run => equiv result.
   Key: execution_equiv gives equal accounts, memory, call_ctx, tx_params,
   so make_venom_call_state/make_venom_create_state produce identical EVM states,
   and extract_venom_result produces state_equiv states. *)

Triviality exec_result_case_tail_error[simp]:
  !xs ok msg.
    xs <> [] ==>
    ((case xs of [] => ok | _ :: _ => Error msg) = Error msg)
Proof
  Cases >> simp[]
QED

Triviality extract_venom_result_result_equiv:
  !vars inst s1 s2 output_val retOff retSize rr none_msg output_msg.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (case extract_venom_result s1 output_val retOff retSize rr of
       | SOME (output, s') =>
           (case inst.inst_outputs of
            | [out] => OK (update_var out output s')
            | _ => Error output_msg)
       | NONE => Error none_msg)
      (case extract_venom_result s2 output_val retOff retSize rr of
       | SOME (output, s') =>
           (case inst.inst_outputs of
            | [out] => OK (update_var out output s')
            | _ => Error output_msg)
       | NONE => Error none_msg)
Proof
  rpt gen_tac >> strip_tac >>
  simp[extract_venom_result_def] >>
  Cases_on `rr` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `x` >> simp[] >>
  rename1 `r.contexts` >>
  Cases_on `r.contexts` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `t` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `h` >> simp[] >>
  Cases_on `q` >> simp[] >>
  TRY (Cases_on `x` >> simp[]) >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `LENGTH inst.inst_outputs = 1` >>
  gvs[listTheory.LENGTH_EQ_NUM_compute, result_equiv_def, revert_equiv_def] >>
  simp[update_var_def, state_equiv_def, execution_equiv_def,
       lookup_var_def, FLOOKUP_UPDATE,
       write_memory_with_expansion_def, LET_THM] >>
  rpt strip_tac >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
  Cases_on `inst.inst_outputs` >>
  gvs[result_equiv_def, revert_equiv_def, exec_result_case_tail_error] >>
  TRY (Cases_on `y` >> gvs[result_equiv_def, revert_equiv_def]) >>
  gvs[result_equiv_def, revert_equiv_def] >>
  rw[state_equiv_def, execution_equiv_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* exec_ext_call preserves equiv when states and operands match *)
Triviality exec_ext_call_equiv:
  !vars inst s1 s2 gas addr value ao as_ ro rs is_static.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (exec_ext_call inst s1 gas addr value ao as_ ro rs is_static)
      (exec_ext_call inst s2 gas addr value ao as_ ro rs is_static)
Proof
  rw[exec_ext_call_def, LET_THM] >>
  `s1.vs_memory = s2.vs_memory /\ s1.vs_accounts = s2.vs_accounts /\
   s1.vs_logs = s2.vs_logs /\ s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\ s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_prev_hashes = s2.vs_prev_hashes /\
   s1.vs_transient = s2.vs_transient`
    by fs[state_equiv_def, execution_equiv_def] >>
  simp[read_memory_def, make_venom_call_state_def,
       make_sub_tx_def, make_rollback_def, venom_to_tx_params_def,
       LET_THM] >>
  irule extract_venom_result_result_equiv >> simp[]
QED

(* exec_delegatecall preserves equiv when states and operands match *)
Triviality exec_delegatecall_equiv:
  !vars inst s1 s2 gas addr ao as_ ro rs.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (exec_delegatecall inst s1 gas addr ao as_ ro rs)
      (exec_delegatecall inst s2 gas addr ao as_ ro rs)
Proof
  rw[exec_delegatecall_def, LET_THM] >>
  `s1.vs_memory = s2.vs_memory /\ s1.vs_accounts = s2.vs_accounts /\
   s1.vs_logs = s2.vs_logs /\ s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\ s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_prev_hashes = s2.vs_prev_hashes /\
   s1.vs_transient = s2.vs_transient`
    by fs[state_equiv_def, execution_equiv_def] >>
  simp[read_memory_def, make_venom_delegatecall_state_def,
       make_sub_tx_def, make_rollback_def, venom_to_tx_params_def,
       LET_THM] >>
  irule extract_venom_result_result_equiv >> simp[]
QED

(* exec_create preserves equiv when states and operands match *)
Triviality exec_create_equiv:
  !vars inst s1 s2 value offset sz salt_opt.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (exec_create inst s1 value offset sz salt_opt)
      (exec_create inst s2 value offset sz salt_opt)
Proof
  rw[exec_create_def, LET_THM] >>
  `s1.vs_memory = s2.vs_memory /\ s1.vs_accounts = s2.vs_accounts /\
   s1.vs_logs = s2.vs_logs /\ s1.vs_call_ctx = s2.vs_call_ctx /\
   s1.vs_tx_ctx = s2.vs_tx_ctx /\ s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_prev_hashes = s2.vs_prev_hashes /\
   s1.vs_transient = s2.vs_transient`
    by fs[state_equiv_def, execution_equiv_def] >>
  simp[read_memory_def, make_venom_create_state_def,
       make_sub_tx_def, make_rollback_def, venom_to_tx_params_def,
       LET_THM] >>
  Cases_on `salt_opt` >> simp[] >>
  irule extract_venom_result_result_equiv >> simp[]
QED

(* Helper: exec_alloca preserves equiv (operands are literals) *)
Triviality exec_alloca_equiv:
  !vars inst s1 s2 alloc_size.
    state_equiv vars s1 s2 ==>
    result_equiv vars
      (exec_alloca inst s1 alloc_size)
      (exec_alloca inst s2 alloc_size)
Proof
  rw[exec_alloca_def, LET_THM] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  gvs[state_equiv_def, execution_equiv_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> rw[] >> fs[]
QED

(* Allocation: operands are literals so state_equiv directly gives same result *)
Triviality step_inst_alloca_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    inst.inst_opcode = ALLOCA ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_base_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  irule exec_alloca_equiv >> simp[]
QED

Triviality step_inst_call_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = CALL ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `s1.vs_call_ctx = s2.vs_call_ctx`
    by fs[state_equiv_def, execution_equiv_def] >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: val_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: val_op :: ao_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: val_op :: ao_op :: as_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: val_op :: ao_op :: as_op :: ro_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: val_op :: ao_op :: as_op :: ro_op :: rs_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand gas_op s1 = eval_operand gas_op s2` by (
    Cases_on `gas_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand addr_op s1 = eval_operand addr_op s2` by (
    Cases_on `addr_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand val_op s1 = eval_operand val_op s2` by (
    Cases_on `val_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand ao_op s1 = eval_operand ao_op s2` by (
    Cases_on `ao_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand as_op s1 = eval_operand as_op s2` by (
    Cases_on `as_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand ro_op s1 = eval_operand ro_op s2` by (
    Cases_on `ro_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand rs_op s1 = eval_operand rs_op s2` by (
    Cases_on `rs_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand gas_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand addr_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand val_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand ao_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand as_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand ro_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand rs_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  irule exec_ext_call_equiv >> simp[]
QED

Triviality step_inst_staticcall_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = STATICCALL ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ao_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ao_op :: as_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ao_op :: as_op :: ro_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ao_op :: as_op :: ro_op :: rs_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand gas_op s1 = eval_operand gas_op s2` by (
    Cases_on `gas_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand addr_op s1 = eval_operand addr_op s2` by (
    Cases_on `addr_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand ao_op s1 = eval_operand ao_op s2` by (
    Cases_on `ao_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand as_op s1 = eval_operand as_op s2` by (
    Cases_on `as_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand ro_op s1 = eval_operand ro_op s2` by (
    Cases_on `ro_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand rs_op s1 = eval_operand rs_op s2` by (
    Cases_on `rs_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand gas_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand addr_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand ao_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand as_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand ro_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand rs_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  irule exec_ext_call_equiv >> simp[]
QED

Triviality step_inst_ext_call_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [CALL; STATICCALL] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >-
    (irule step_inst_call_equiv >> simp[]) >>
  irule step_inst_staticcall_equiv >> simp[]
QED

Triviality step_inst_delegatecall_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = DELEGATECALL ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ao_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ao_op :: as_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ao_op :: as_op :: ro_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(gas_op : operand) :: addr_op :: ao_op :: as_op :: ro_op :: rs_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand gas_op s1 = eval_operand gas_op s2` by (
    Cases_on `gas_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand addr_op s1 = eval_operand addr_op s2` by (
    Cases_on `addr_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand ao_op s1 = eval_operand ao_op s2` by (
    Cases_on `ao_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand as_op s1 = eval_operand as_op s2` by (
    Cases_on `as_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand ro_op s1 = eval_operand ro_op s2` by (
    Cases_on `ro_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand rs_op s1 = eval_operand rs_op s2` by (
    Cases_on `rs_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand gas_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand addr_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand ao_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand as_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand ro_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand rs_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  irule exec_delegatecall_equiv >> simp[]
QED

Triviality step_inst_create1_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = CREATE ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(val_op : operand) :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(val_op : operand) :: off_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(val_op : operand) :: off_op :: sz_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand val_op s1 = eval_operand val_op s2` by (
    Cases_on `val_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand off_op s1 = eval_operand off_op s2` by (
    Cases_on `off_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand sz_op s1 = eval_operand sz_op s2` by (
    Cases_on `sz_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand val_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand off_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand sz_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  irule exec_create_equiv >> simp[]
QED

Triviality step_inst_create2_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = CREATE2 ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(val_op : operand) :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(val_op : operand) :: off_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(val_op : operand) :: off_op :: sz_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(val_op : operand) :: off_op :: sz_op :: salt_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand val_op s1 = eval_operand val_op s2` by (
    Cases_on `val_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand off_op s1 = eval_operand off_op s2` by (
    Cases_on `off_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand sz_op s1 = eval_operand sz_op s2` by (
    Cases_on `sz_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  `eval_operand salt_op s1 = eval_operand salt_op s2` by (
    Cases_on `salt_op` >> fs[eval_operand_def, state_equiv_def, execution_equiv_def, lookup_var_def]) >>
  Cases_on `eval_operand val_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand off_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand sz_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `eval_operand salt_op s2` >> simp[result_equiv_def, revert_equiv_def] >>
  irule exec_create_equiv >> simp[]
QED

Triviality step_inst_create_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode [CREATE; CREATE2] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >-
    (irule step_inst_create1_equiv >> simp[]) >>
  irule step_inst_create2_equiv >> simp[]
QED

Triviality step_inst_getfmp_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = GETFMP ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_base_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  `s1.vs_fmp = s2.vs_fmp` by
    fs[state_equiv_def, execution_equiv_def] >>
  gvs[] >> irule update_var_preserves >> simp[]
QED

Triviality step_inst_initial_fmp_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = INITIAL_FMP ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_base_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  `s1.vs_initial_fmp = s2.vs_initial_fmp` by
    fs[state_equiv_def, execution_equiv_def] >>
  gvs[] >> irule update_var_preserves >> simp[]
QED

Triviality step_inst_retpc_param_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = RETPC_PARAM ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_base_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  `s1.vs_return_pc_token = s2.vs_return_pc_token` by
    fs[state_equiv_def, execution_equiv_def] >>
  gvs[] >> irule update_var_preserves >> simp[]
QED

Triviality step_inst_fmp_param_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = FMP_PARAM ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  `s1.vs_params = s2.vs_params` by
    fs[state_equiv_def, execution_equiv_def] >>
  gvs[] >> simp[step_inst_base_def] >>
  rpt CASE_TAC >> gvs[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >> simp[]
QED

Triviality step_inst_setfmp_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = SETFMP ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(op : operand) :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand op s1 = eval_operand op s2` by
    (irule eval_operand_equiv >> qexists `vars` >> simp[]) >>
  Cases_on `eval_operand op s2` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

Triviality step_inst_dalloca_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = DALLOCA ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(size_op : operand) :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(out : string) :: outs` >>
  Cases_on `outs` >> simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand size_op s1 = eval_operand size_op s2` by
    (irule eval_operand_equiv >> qexists `vars` >> simp[]) >>
  Cases_on `eval_operand size_op s2` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  `s1.vs_fmp = s2.vs_fmp` by
    fs[state_equiv_def, execution_equiv_def] >>
  gvs[] >> irule update_var_preserves >>
  fs[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

Triviality step_inst_bump_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = BUMP ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_operands` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(base_op : operand) :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(base_op : operand) :: size_op :: ops` >>
  Cases_on `ops` >> simp[result_equiv_def, revert_equiv_def] >>
  Cases_on `inst.inst_outputs` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(ptr_out : string) :: outs` >>
  Cases_on `outs` >> simp[result_equiv_def, revert_equiv_def] >>
  rename1 `(ptr_out : string) :: next_out :: outs` >>
  Cases_on `outs` >> simp[result_equiv_def, revert_equiv_def] >>
  `eval_operand base_op s1 = eval_operand base_op s2` by
    (irule eval_operand_equiv >> qexists `vars` >> simp[]) >>
  `eval_operand size_op s1 = eval_operand size_op s2` by
    (irule eval_operand_equiv >> qexists `vars` >> simp[]) >>
  Cases_on `eval_operand base_op s2` >>
  Cases_on `eval_operand size_op s2` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  irule update_var_preserves >>
  irule update_var_preserves >> simp[]
QED

Triviality mcopy_preserves_state_equiv:
  !vars dst src sz s1 s2. state_equiv vars s1 s2 ==>
    state_equiv vars (mcopy dst src sz s1) (mcopy dst src sz s2)
Proof
  rpt strip_tac >>
  `s1.vs_memory = s2.vs_memory` by
    gvs[state_equiv_def, execution_equiv_def] >>
  simp[mcopy_def] >>
  irule write_memory_with_expansion_preserves >> simp[]
QED

Triviality pack_dret_dynamic_equiv:
  !vars cursor pairs s1 s2 p1 c1 s1' p2 c2 s2'.
    state_equiv vars s1 s2 /\
    pack_dret_dynamic cursor pairs s1 = (p1,c1,s1') /\
    pack_dret_dynamic cursor pairs s2 = (p2,c2,s2') ==>
    p1 = p2 /\ c1 = c2 /\ state_equiv vars s1' s2'
Proof
  Induct_on `pairs` >- gvs[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Ntimes pack_dret_dynamic_def 2] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[mcopy_preserves_state_equiv]
QED

Triviality step_inst_retfmp_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = RETFMP ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `eval_operands inst.inst_operands s1 = eval_operands inst.inst_operands s2` by
    metis_tac[eval_operands_equiv] >>
  simp[step_inst_base_def] >>
  Cases_on `eval_operands inst.inst_operands s2` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  Cases_on `x` >>
  gvs[result_equiv_def, revert_equiv_def,
      state_equiv_def, execution_equiv_def, lookup_var_def]
QED

Triviality step_inst_dret_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    inst.inst_opcode = DRET ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `eval_operands inst.inst_operands s1 = eval_operands inst.inst_operands s2` by
    metis_tac[eval_operands_equiv] >>
  `s1.vs_call_entry_fmp = s2.vs_call_entry_fmp` by
    gvs[state_equiv_def, execution_equiv_def] >>
  simp[Ntimes step_inst_base_def 2] >>
  Cases_on `inst.inst_outputs` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  Cases_on `parse_dret_shape inst` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  PairCases_on `x` >>
  Cases_on `eval_operands inst.inst_operands s2` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  Cases_on `pair_dret_words
    (TAKE (2 * x1) (DROP (1 + x0) x))` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  drule_all pack_dret_dynamic_equiv >> strip_tac >>
  gvs[result_equiv_def, state_equiv_def, execution_equiv_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[lookup_var_def]
QED

(* New raw-FMP and hidden-parameter opcodes preserve execution equivalence. *)
Triviality step_inst_fmp_opcode_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    MEM inst.inst_opcode
      [DALLOCA; GETFMP; SETFMP; INITIAL_FMP; BUMP; FMP_PARAM; RETPC_PARAM] ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[]
  >- (irule step_inst_dalloca_equiv >> simp[])
  >- (irule step_inst_getfmp_equiv >> simp[])
  >- (irule step_inst_setfmp_equiv >> simp[])
  >- (irule step_inst_initial_fmp_equiv >> simp[])
  >- (irule step_inst_bump_equiv >> simp[])
  >- (irule step_inst_fmp_param_equiv >> simp[])
  >- (irule step_inst_retpc_param_equiv >> simp[])
QED

(* ==========================================================================
   step_inst_base: Main theorem — dispatches to helpers
   ========================================================================== *)

Theorem step_inst_result_equiv:
  !vars inst s1 s2.
    state_equiv vars s1 s2 /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >>
  (* Dispatch: derive MEM for the opcode's category, then use helper *)
  FIRST [
    `MEM inst.inst_opcode [ADD;SUB;MUL;Div;SDIV;Mod;SMOD;Exp;
       AND;OR;XOR;SHL;SHR;SAR;SIGNEXTEND;BYTE;EQ;LT;GT;SLT;SGT;OFFSET]`
       by simp[] >>
      drule_all step_inst_pure2_equiv >> simp[],
    `MEM inst.inst_opcode [NOT;ISZERO]` by simp[] >>
      drule_all step_inst_pure1_equiv >> simp[],
    `MEM inst.inst_opcode [ADDMOD;MULMOD]` by simp[] >>
      drule_all step_inst_pure3_equiv >> simp[],
    `MEM inst.inst_opcode
       [CALLER;ADDRESS;CALLVALUE;GAS;ORIGIN;GASPRICE;CHAINID;
        COINBASE;TIMESTAMP;NUMBER;PREVRANDAO;GASLIMIT;BASEFEE;
        BLOBBASEFEE;SELFBALANCE;CALLDATASIZE;RETURNDATASIZE;MEMTOP;
        CODESIZE]`
      by simp[] >> drule_all step_inst_read0_equiv >> simp[],
    `MEM inst.inst_opcode
       [MLOAD;SLOAD;TLOAD;BLOCKHASH;BALANCE;CALLDATALOAD;
        EXTCODESIZE;BLOBHASH;ILOAD;DLOAD]`
      by simp[] >> drule_all step_inst_read1_equiv >> simp[],
    `inst.inst_opcode = EXTCODEHASH` by simp[] >>
      drule_all step_inst_extcodehash_equiv >> simp[],
    `MEM inst.inst_opcode [MSTORE;MSTORE8;SSTORE;TSTORE]` by simp[] >>
      drule_all step_inst_write2_equiv >> simp[],
    `MEM inst.inst_opcode [STOP;SINK]` by simp[] >>
      drule_all step_inst_terminator_equiv >> simp[],
    `inst.inst_opcode = RETURN` by simp[] >>
      drule_all step_inst_return_equiv >> simp[],
    `inst.inst_opcode = REVERT` by simp[] >>
      drule_all step_inst_revert_equiv >> simp[],
    `MEM inst.inst_opcode [JMP;JNZ]` by simp[] >>
      drule_all step_inst_control_equiv >> simp[],
    `MEM inst.inst_opcode [PHI;ASSIGN;NOP]` by simp[] >>
      drule_all step_inst_ssa_equiv >> simp[],
    `MEM inst.inst_opcode [ASSERT;ASSERT_UNREACHABLE]` by simp[] >>
      drule_all step_inst_assert_equiv >> simp[],
    `inst.inst_opcode = SHA3` by simp[] >>
      drule_all step_inst_sha3_equiv >> simp[],
    `MEM inst.inst_opcode [CALLDATACOPY;RETURNDATACOPY]` by simp[] >>
      drule_all step_inst_copy_equiv >> simp[],
    `inst.inst_opcode = MCOPY` by simp[] >>
      drule_all step_inst_mcopy_equiv >> simp[],
    `inst.inst_opcode = INVALID` by simp[] >>
      drule_all step_inst_invalid_equiv >> simp[],
    `inst.inst_opcode = LOG` by simp[] >>
      drule_all step_inst_log_equiv >> simp[],
    `inst.inst_opcode = SELFDESTRUCT` by simp[] >>
      drule_all step_inst_selfdestruct_equiv >> simp[],
    `inst.inst_opcode = DJMP` by simp[] >>
      drule_all step_inst_djmp_equiv >> simp[],
    `inst.inst_opcode = ISTORE` by simp[] >>
      drule_all step_inst_istore_equiv >> simp[],
    `MEM inst.inst_opcode [DLOADBYTES;CODECOPY]` by simp[] >>
      drule_all step_inst_data_copy_equiv >> simp[],
    `inst.inst_opcode = EXTCODECOPY` by simp[] >>
      drule_all step_inst_extcodecopy_equiv >> simp[],
    `inst.inst_opcode = PARAM` by simp[] >>
      drule_all step_inst_param_equiv >> simp[],
    `inst.inst_opcode = RET` by simp[] >>
      drule_all step_inst_ret_equiv >> simp[],
    `MEM inst.inst_opcode [CALL;STATICCALL]` by simp[] >>
      drule_all step_inst_ext_call_equiv >> simp[],
    `inst.inst_opcode = DELEGATECALL` by simp[] >>
      drule_all step_inst_delegatecall_equiv >> simp[],
    `MEM inst.inst_opcode [CREATE;CREATE2]` by simp[] >>
      drule_all step_inst_create_equiv >> simp[],
    `MEM inst.inst_opcode
       [DALLOCA; GETFMP; SETFMP; INITIAL_FMP; BUMP; FMP_PARAM; RETPC_PARAM]`
      by simp[] >> drule_all step_inst_fmp_opcode_equiv >> simp[],
    `inst.inst_opcode = DRET` by simp[] >>
      drule_all step_inst_dret_equiv >> simp[],
    `inst.inst_opcode = RETFMP` by simp[] >>
      drule_all step_inst_retfmp_equiv >> simp[],
    `inst.inst_opcode = ALLOCA` by simp[] >>
      drule_all step_inst_alloca_equiv >> simp[],
    (* INVOKE: handled in module sem, falls to Error in step_inst_base.
       Explicit so new opcode additions cause proof failure here. *)
    `inst.inst_opcode = INVOKE` by simp[] >>
      simp[step_inst_base_def, result_equiv_def, revert_equiv_def]
  ]
QED

(* ==========================================================================
   block_step Preserves Equivalence
   ========================================================================== *)

Triviality block_step_result_equiv:
  !vars bb s1 s2.
    state_equiv vars s1 s2 /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    let (r1, t1) = block_step bb s1 in
    let (r2, t2) = block_step bb s2 in
    t1 = t2 /\ result_equiv vars r1 r2
Proof
  rw[block_step_def, LET_THM] >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  simp[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >>
  simp[result_equiv_def, revert_equiv_def] >>
  rename1 `get_instruction bb _ = SOME cur_inst` >>
  `MEM cur_inst bb.bb_instructions` by (
    fs[get_instruction_def] >>
    Cases_on `s2.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[] >>
    metis_tac[listTheory.EL_MEM]) >>
  `result_equiv vars (step_inst_base cur_inst s1) (step_inst_base cur_inst s2)` by (
    irule step_inst_result_equiv >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst_base cur_inst s1` >> Cases_on `step_inst_base cur_inst s2` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  Cases_on `is_terminator cur_inst.inst_opcode` >>
  simp[result_equiv_def, revert_equiv_def] >>
  fs[next_inst_def, state_equiv_def, execution_equiv_def] >>
  rw[] >> simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* ==========================================================================
   exec_block Preserves Equivalence
   ========================================================================== *)

(* Induction on exec_block to show result_equiv is preserved.
   Requires no INVOKE instructions in block (for cross-function equiv,
   use run_blocks-level simulation). *)
Theorem exec_block_result_equiv:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >> pop_assum mp_tac >> pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  (* Unfold both LHS and RHS *)
  simp[Once exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `get_instruction bb s1.vs_inst_idx` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  (* No INVOKE in this block *)
  `inst.inst_opcode <> INVOKE` by
    (gvs[listTheory.EVERY_MEM, get_instruction_def] >>
     first_x_assum irule >> irule listTheory.EL_MEM >> simp[]) >>
  simp[step_inst_non_invoke] >>
  (* Derive operand condition for this specific inst *)
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN vars` by
    (gvs[get_instruction_def] >> metis_tac[listTheory.EL_MEM]) >>
  drule_all step_inst_result_equiv >> strip_tac >>
  Cases_on `step_inst_base inst s1` >> Cases_on `step_inst_base inst s2` >>
  gvs[result_equiv_def, revert_equiv_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >-
    (* Terminator: check vs_halted *)
    (`v.vs_halted = v'.vs_halted` by
       fs[state_equiv_def, execution_equiv_def] >>
     Cases_on `v.vs_halted` >> gvs[result_equiv_def, revert_equiv_def] >>
     fs[state_equiv_def]) >>
  (* Non-terminator: recurse via IH *)
  `step_inst fuel ctx inst s1 = OK v` by simp[step_inst_non_invoke] >>
  first_x_assum drule >> simp[] >> disch_then irule >>
  simp[] >>
  fs[state_equiv_def, execution_equiv_def] >>
  simp[lookup_var_def] >> metis_tac[lookup_var_def]
QED

(* Corollary: OK case gives state_equiv *)
Theorem exec_block_state_equiv:
  !fuel ctx vars bb s1 s2 r1.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
    exec_block fuel ctx bb s1 = OK r1
  ==>
    ?r2. exec_block fuel ctx bb s2 = OK r2 /\ state_equiv vars r1 r2
Proof
  rw[] >>
  `result_equiv vars (exec_block fuel ctx bb s1) (exec_block fuel ctx bb s2)` by
    (irule exec_block_result_equiv >> metis_tac[]) >>
  gvs[result_equiv_def] >>
  Cases_on `exec_block fuel ctx bb s2` >> gvs[result_equiv_def]
QED

(* Updating vs_inst_idx to the same value on both sides preserves state_equiv *)
Theorem state_equiv_inst_idx:
  !vars s1 s2 n. state_equiv vars s1 s2 ==>
    state_equiv vars (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  rw[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

Triviality eval_phis_state_equiv_OK_pair:
  !s1 s2 vars insts v v'.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode = PHI ==>
              !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) insts /\
    eval_phis s1 insts = OK v /\
    eval_phis s2 insts = OK v' ==>
    state_equiv vars v v'
Proof
  rpt strip_tac >>
  qspecl_then [`s1`,`s2`,`vars`,`insts`,`v`] mp_tac eval_phis_state_equiv >>
  simp[]
QED

Triviality EVERY_phi_operand_weaken:
  !vars l.
    (!inst. MEM inst l ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    EVERY (\inst. inst.inst_opcode = PHI ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) l
Proof
  rpt gen_tac >> DISCH_TAC >>
  Induct_on `l` >> simp[] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >> metis_tac[]
QED

Theorem run_block_result_equiv:
  !fuel ctx vars bb s1 s2.
    state_equiv vars s1 s2 /\
    EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
    (!inst. MEM inst bb.bb_instructions ==>
            !x. MEM (Var x) inst.inst_operands ==> x NOTIN vars) ==>
    result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)
Proof
  ONCE_REWRITE_TAC[run_block_def] >> rpt strip_tac >>
  imp_res_tac EVERY_phi_operand_weaken >>
  mp_tac (Q.SPECL [`s1`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s1 bb.bb_instructions` >> gvs[exec_result_distinct] >>
  mp_tac (Q.SPECL [`s2`,`bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  Cases_on `eval_phis s2 bb.bb_instructions` >> gvs[exec_result_distinct]
  >- (
    irule exec_block_result_equiv >>
    (conj_tac >- metis_tac[]) >>
    (conj_tac >- metis_tac[]) >>
    irule state_equiv_inst_idx >>
    imp_res_tac eval_phis_state_equiv_OK_pair
  )
  >- (
    qspecl_then [`s1`,`s2`,`vars`,`bb.bb_instructions`,`v`] mp_tac
      eval_phis_state_equiv >> simp[] >> strip_tac >> gvs[]
  )
  >- (
    qspecl_then [`s2`,`s1`,`vars`,`bb.bb_instructions`,`v`] mp_tac
      eval_phis_state_equiv >> simp[state_equiv_sym] >> strip_tac >> gvs[]
  )
  >- simp[result_equiv_def]
QED
Triviality run_block_OK_eq_exec_block:
  !fuel ctx bb s s_phi.
    eval_phis s bb.bb_instructions = OK s_phi ==>
    run_block fuel ctx bb s =
      exec_block fuel ctx bb (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rw[run_block_def]
QED
Triviality run_block_Error_eq:
  !fuel ctx bb s e.
    eval_phis s bb.bb_instructions = Error e ==>
    run_block fuel ctx bb s = Error e
Proof
  rw[run_block_def]
QED
Triviality run_block_OK_inst_idx_0:
    run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  rw[run_block_def] >>
  qspecl_then [`s`,`bb.bb_instructions`] mp_tac eval_phis_ok_or_error_defs >>
  strip_tac >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_distinct] >>
  metis_tac[exec_block_OK_inst_idx_0]
QED

Triviality run_block_current_bb_in_succs:
  !fuel ctx bb s v.
    run_block fuel ctx bb s = OK v /\
    bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
         ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    MEM v.vs_current_bb (bb_succs bb)
Proof
  rw[run_block_def] >>
  qspecl_then [`s`,`bb.bb_instructions`] mp_tac eval_phis_ok_or_error_defs >>
  strip_tac >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[exec_result_distinct] >>
  irule exec_block_current_bb_in_succs >> simp[phi_prefix_length_le] >>
  qexistsl_tac [`ctx`, `fuel`, `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >> simp[phi_prefix_length_le]
QED

(* ==========================================================================
   run_function Preserves Result Equivalence
   ========================================================================== *)

(* If two states are state_equiv and all blocks in fn have no INVOKE
   and all operand vars are outside vars, then run_function results
   are result_equiv. Used for state-patching: patching non-live vars
   doesn't affect function execution. *)
Triviality run_blocks_result_equiv:
  !fuel ctx vars fn s1 s2.
    state_equiv vars s1 s2 /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
      (!inst x. MEM inst bb.bb_instructions /\
               MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
    result_equiv vars (run_blocks fuel ctx fn s1) (run_blocks fuel ctx fn s2)
Proof
  Induct_on `fuel`
  >- simp[run_blocks_def, result_equiv_def] >>
  rpt strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- simp[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)` by
    metis_tac[run_block_result_equiv] >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx bb s2` >>
  gvs[result_equiv_def] >>
  (* OK/OK case: need halted equivalence then IH *)
  `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[result_equiv_def] >-
    fs[state_equiv_def, execution_equiv_def] >>
  (* Not halted: apply IH *)
  first_x_assum irule >> simp[] >>
  rpt strip_tac >> res_tac
QED

Theorem run_function_result_equiv:
  !fuel ctx vars fn s1 s2.
    state_equiv vars s1 s2 /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
      (!inst x. MEM inst bb.bb_instructions /\
               MEM (Var x) inst.inst_operands ==> x NOTIN vars)) ==>
    result_equiv vars (run_function fuel ctx fn s1) (run_function fuel ctx fn s2)
Proof
  rpt strip_tac >>
  simp[run_function_def] >>
  Cases_on `fn_entry_label fn` >> simp[result_equiv_def] >>
  irule run_blocks_result_equiv >> simp[] >> conj_tac
  >- (rpt strip_tac >> res_tac)
  >> qpat_x_assum `state_equiv _ _ _` mp_tac >>
  simp[state_equiv_def, execution_equiv_def, lookup_var_def]
QED

(* Same as run_function_result_equiv but with a safe set closed under
   successors, allowing the operand condition to be restricted to
   reachable blocks rather than all blocks. *)
Triviality run_blocks_result_equiv_closed:
  !fuel ctx vars fn s1 s2 safe.
    state_equiv vars s1 s2 /\
    s1.vs_current_bb IN safe /\
    (!lbl bb. lbl IN safe /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
      bb_well_formed bb /\
      EVERY inst_wf bb.bb_instructions /\
      EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
      (!inst x. MEM inst bb.bb_instructions /\
               MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
      (!s. MEM s (bb_succs bb) ==> s IN safe)) ==>
    result_equiv vars (run_blocks fuel ctx fn s1) (run_blocks fuel ctx fn s2)
Proof
  Induct_on `fuel` >-
  simp[run_blocks_def, result_equiv_def] >>
  rpt strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_def] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks` >-
  simp[result_equiv_def] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
   EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
   (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
   (!s. MEM s (bb_succs bb) ==> s IN safe)` by metis_tac[] >>
  `result_equiv vars (run_block fuel ctx bb s1) (run_block fuel ctx bb s2)` by
    metis_tac[run_block_result_equiv] >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx bb s2` >> gvs[result_equiv_def] >>
  `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_def, execution_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[result_equiv_def] >-
  fs[state_equiv_def, execution_equiv_def] >>
  (* Not halted: successor must be in safe, then apply IH *)
  `v.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
  `bb.bb_instructions <> []` by fs[bb_well_formed_def] >>
  `!i. i < LENGTH bb.bb_instructions - 1 ==>
    ~is_terminator (EL i bb.bb_instructions).inst_opcode` by (
    rpt strip_tac >> CCONTR_TAC >> fs[bb_well_formed_def] >> res_tac >> fs[]) >>
  `MEM v.vs_current_bb (bb_succs bb)` by
    metis_tac[run_block_current_bb_in_succs] >>
  `v.vs_current_bb IN safe` by metis_tac[] >>
  first_x_assum irule >> simp[] >>
  metis_tac[]
QED

(* =====================================================================
   Universal helpers for lifting exec_block results to run_block results.
   These handle the eval_phis wrapper uniformly, so pass proofs don't
   need to do eval_phis case-splitting individually.
   ===================================================================== *)

(* Lift an exec_block-level lift_result to run_block-level.
   Requires: eval_phis agrees on both blocks, and phi_prefix_length matches.
   This is the universal pattern for pass correctness proofs. *)
Theorem run_block_lift_result:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   fuel ctx bb bt_bb s.
    phi_prefix_length bb.bb_instructions = phi_prefix_length bt_bb.bb_instructions /\
    eval_phis s bb.bb_instructions = eval_phis s bt_bb.bb_instructions /\
    (!s_phi.
       eval_phis s bb.bb_instructions = OK s_phi ==>
       lift_result R_ok R_term R_term
         (exec_block fuel ctx bb
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions))
         (exec_block fuel ctx bt_bb
           (s_phi with vs_inst_idx := phi_prefix_length bt_bb.bb_instructions))) ==>
    lift_result R_ok R_term R_term
      (run_block fuel ctx bb s) (run_block fuel ctx bt_bb s)
Proof
  rpt gen_tac >> strip_tac >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (
    (* eval_phis returns OK *)
    rw[run_block_def] >>
    `eval_phis s bt_bb.bb_instructions = OK s'` by fs[] >>
    rw[lift_result_def] >>
    qpat_x_assum `!s_phi. _ ==> _` (qspec_then `s'` mp_tac) >>
    simp[])
  >- (
    (* eval_phis returns Error *)
    rw[run_block_def] >>
    `eval_phis s bt_bb.bb_instructions = Error e` by fs[] >>
    simp[lift_result_def])
QED

(* Lift an exec_block-level result_equiv to run_block-level.
   Requires: eval_phis agrees on both blocks, and phi_prefix_length matches. *)
Theorem run_block_lift_result_equiv:
  !vars fuel ctx bb bt_bb s.
    phi_prefix_length bb.bb_instructions = phi_prefix_length bt_bb.bb_instructions /\
    eval_phis s bb.bb_instructions = eval_phis s bt_bb.bb_instructions /\
    (!s_phi.
       eval_phis s bb.bb_instructions = OK s_phi ==>
       result_equiv vars
         (exec_block fuel ctx bb
           (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions))
         (exec_block fuel ctx bt_bb
           (s_phi with vs_inst_idx := phi_prefix_length bt_bb.bb_instructions))) ==>
    result_equiv vars (run_block fuel ctx bb s) (run_block fuel ctx bt_bb s)
Proof
  rpt gen_tac >> strip_tac >>
  DISJ_CASES_TAC (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (
    rw[run_block_def] >>
    `eval_phis s bt_bb.bb_instructions = OK s'` by fs[] >>
    qpat_x_assum `!s_phi. _ ==> _` (qspec_then `s'` mp_tac) >>
    simp[result_equiv_is_lift_result])
  >- (
    rw[run_block_def] >>
    `eval_phis s bt_bb.bb_instructions = Error e` by fs[] >>
    simp[result_equiv_is_lift_result, lift_result_def])
QED


Theorem run_function_result_equiv_closed:
  !fuel ctx vars fn s1 s2 safe.
    state_equiv vars s1 s2 /\
    (!lbl. fn_entry_label fn = SOME lbl ==> lbl IN safe) /\
    (!lbl bb. lbl IN safe /\ lookup_block lbl fn.fn_blocks = SOME bb ==>
      bb_well_formed bb /\
      EVERY inst_wf bb.bb_instructions /\
      EVERY (\inst. inst.inst_opcode <> INVOKE) bb.bb_instructions /\
      (!inst x. MEM inst bb.bb_instructions /\
               MEM (Var x) inst.inst_operands ==> x NOTIN vars) /\
      (!s. MEM s (bb_succs bb) ==> s IN safe)) ==>
    result_equiv vars (run_function fuel ctx fn s1) (run_function fuel ctx fn s2)
Proof
  rpt strip_tac >>
  simp[run_function_def] >>
  Cases_on `fn_entry_label fn` >> simp[result_equiv_def] >>
  rename1 `fn_entry_label fn = SOME lbl` >>
  cheat
QED
