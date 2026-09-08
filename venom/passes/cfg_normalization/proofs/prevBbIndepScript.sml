(*
 * step_inst_base is independent of vs_prev_bb for non-PHI opcodes.
 *
 * Only the PHI case of step_inst_base reads s.vs_prev_bb (via resolve_phi).
 * All other opcodes produce identical results regardless of vs_prev_bb.
 *
 * Built as a separate theory because the 93-opcode case split is expensive.
 *)

Theory prevBbIndep
Ancestors
  venomExecSemantics venomState venomInst
Libs
  finite_mapTheory listTheory BasicProvers pairTheory

(* ================================================================
   Commutation helpers for vs_prev_bb
   ================================================================ *)

Theorem eval_op_prev_bb[local]:
  !op s p. eval_operand op (s with vs_prev_bb := p) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem eval_ops_prev_bb[local]:
  !ops s p.
    eval_operands ops (s with vs_prev_bb := p) = eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, eval_op_prev_bb]
QED

Theorem update_var_prev_bb[local]:
  !x v s p.
    update_var x v (s with vs_prev_bb := p) =
    (update_var x v s) with vs_prev_bb := p
Proof
  simp[update_var_def]
QED

Theorem write_mem_prev_bb[local]:
  !off bytes s p.
    write_memory_with_expansion off bytes (s with vs_prev_bb := p) =
    (write_memory_with_expansion off bytes s) with vs_prev_bb := p
Proof
  simp[write_memory_with_expansion_def, LET_THM]
QED

Theorem read_mem_prev_bb[local]:
  !off sz s p. read_memory off sz (s with vs_prev_bb := p) = read_memory off sz s
Proof
  simp[read_memory_def]
QED

Theorem jump_to_prev_bb[local]:
  !lbl s p. jump_to lbl (s with vs_prev_bb := p) = jump_to lbl s
Proof
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem halt_state_prev_bb[local]:
  !s p. halt_state (s with vs_prev_bb := p) =
        (halt_state s) with vs_prev_bb := p
Proof
  simp[halt_state_def]
QED

Theorem revert_state_prev_bb[local]:
  !s p. revert_state (s with vs_prev_bb := p) =
        (revert_state s) with vs_prev_bb := p
Proof
  simp[revert_state_def]
QED

Theorem set_returndata_prev_bb[local]:
  !rd s p. set_returndata rd (s with vs_prev_bb := p) =
           (set_returndata rd s) with vs_prev_bb := p
Proof
  simp[set_returndata_def]
QED

Theorem mstore_prev_bb[local]:
  !off v s p. mstore off v (s with vs_prev_bb := p) =
              (mstore off v s) with vs_prev_bb := p
Proof
  simp[mstore_def, LET_THM]
QED

Theorem istore_prev_bb[local]:
  !off v s p. istore off v (s with vs_prev_bb := p) =
              (istore off v s) with vs_prev_bb := p
Proof
  simp[istore_def, mstore_prev_bb]
QED

Theorem mstore8_prev_bb[local]:
  !off v s p. mstore8 off v (s with vs_prev_bb := p) =
              (mstore8 off v s) with vs_prev_bb := p
Proof
  simp[mstore8_def, LET_THM]
QED

Theorem sstore_prev_bb[local]:
  !k v s p. sstore k v (s with vs_prev_bb := p) =
            (sstore k v s) with vs_prev_bb := p
Proof
  simp[sstore_def, contract_storage_def, LET_THM]
QED

Theorem tstore_prev_bb[local]:
  !k v s p. tstore k v (s with vs_prev_bb := p) =
            (tstore k v s) with vs_prev_bb := p
Proof
  simp[tstore_def, contract_transient_def, LET_THM]
QED

Theorem mcopy_prev_bb[local]:
  !dst src sz s p.
    mcopy dst src sz (s with vs_prev_bb := p) =
    (mcopy dst src sz s) with vs_prev_bb := p
Proof
  simp[mcopy_def, LET_THM, write_memory_with_expansion_def]
QED

Theorem mload_prev_bb[local]:
  !off s p. mload off (s with vs_prev_bb := p) = mload off s
Proof
  simp[mload_def]
QED

Theorem sload_prev_bb[local]:
  !k s p. sload k (s with vs_prev_bb := p) = sload k s
Proof
  simp[sload_def, contract_storage_def]
QED

Theorem tload_prev_bb[local]:
  !k s p. tload k (s with vs_prev_bb := p) = tload k s
Proof
  simp[tload_def, contract_transient_def]
QED

(* ================================================================
   exec helper commutations
   ================================================================ *)

Definition exec_result_map_prev_bb_def:
  (exec_result_map_prev_bb f (OK s) = OK (f s)) /\
  (exec_result_map_prev_bb f (Halt s) = Halt (f s)) /\
  (exec_result_map_prev_bb f (Abort a s) = Abort a (f s)) /\
  (exec_result_map_prev_bb f (IntRet l s) = IntRet l (f s)) /\
  (exec_result_map_prev_bb f (Error e) = Error e)
End

Theorem exec_pure1_prev_bb[local]:
  !f inst s p.
    exec_pure1 f inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_pure1 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure1_def, eval_op_prev_bb, update_var_prev_bb,
       exec_result_map_prev_bb_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[exec_result_map_prev_bb_def]
QED

Theorem exec_pure2_prev_bb[local]:
  !f inst s p.
    exec_pure2 f inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_pure2 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure2_def, eval_op_prev_bb, update_var_prev_bb,
       exec_result_map_prev_bb_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[exec_result_map_prev_bb_def]
QED

Theorem exec_pure3_prev_bb[local]:
  !f inst s p.
    exec_pure3 f inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_pure3 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure3_def, eval_op_prev_bb, update_var_prev_bb,
       exec_result_map_prev_bb_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[exec_result_map_prev_bb_def]
QED

Theorem exec_read0_prev_bb[local]:
  !g inst s p.
    (!s p. g (s with vs_prev_bb := p) = g s) ==>
    exec_read0 g inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_read0 g inst s)
Proof
  rpt strip_tac >>
  simp[exec_read0_def, update_var_prev_bb, exec_result_map_prev_bb_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[exec_result_map_prev_bb_def]
QED

Theorem exec_read1_prev_bb[local]:
  !g inst s p.
    (!v s p. g v (s with vs_prev_bb := p) = g v s) ==>
    exec_read1 g inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_read1 g inst s)
Proof
  rpt strip_tac >>
  simp[exec_read1_def, eval_op_prev_bb, update_var_prev_bb,
       exec_result_map_prev_bb_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[exec_result_map_prev_bb_def]
QED

Theorem exec_write2_prev_bb[local]:
  !f inst s p.
    (!v1 v2 s p. f v1 v2 (s with vs_prev_bb := p) =
                 (f v1 v2 s) with vs_prev_bb := p) ==>
    exec_write2 f inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p) (exec_write2 f inst s)
Proof
  rpt strip_tac >>
  simp[exec_write2_def, eval_op_prev_bb, exec_result_map_prev_bb_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[exec_result_map_prev_bb_def]
QED

Theorem exec_alloca_prev_bb[local]:
  !inst s alloc_size p.
    exec_alloca inst (s with vs_prev_bb := p) alloc_size =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
                    (exec_alloca inst s alloc_size)
Proof
  rpt gen_tac >> simp[exec_alloca_def, LET_THM] >>
  BasicProvers.EVERY_CASE_TAC >> simp[exec_result_map_prev_bb_def] >>
  simp[update_var_def, venom_state_component_equality]
QED

(* ================================================================
   Utility: case-OPTION_MAP fusion
   ================================================================ *)

Theorem option_case_OPTION_MAP_prev_bb[local]:
  !f x n g.
    option_CASE (OPTION_MAP f x) n g = option_CASE x n (g o f)
Proof
  Cases_on `x` >> simp[]
QED

(* ================================================================
   External call helpers
   ================================================================ *)

Theorem venom_to_tx_params_prev_bb[local]:
  !s p. venom_to_tx_params (s with vs_prev_bb := p) = venom_to_tx_params s
Proof
  simp[venom_to_tx_params_def]
QED

Theorem make_venom_call_state_prev_bb[local]:
  !s target gas value calldata code is_static p.
    make_venom_call_state (s with vs_prev_bb := p) target gas value
      calldata code is_static =
    make_venom_call_state s target gas value calldata code is_static
Proof
  simp[make_venom_call_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

Theorem make_venom_delegatecall_state_prev_bb[local]:
  !s target gas calldata code is_static p.
    make_venom_delegatecall_state (s with vs_prev_bb := p) target gas
      calldata code is_static =
    make_venom_delegatecall_state s target gas calldata code is_static
Proof
  simp[make_venom_delegatecall_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

Theorem make_venom_create_state_prev_bb[local]:
  !s new_address gas value init_code p.
    make_venom_create_state (s with vs_prev_bb := p) new_address gas
      value init_code =
    make_venom_create_state s new_address gas value init_code
Proof
  simp[make_venom_create_state_def, LET_THM, venom_to_tx_params_prev_bb]
QED

Theorem extract_venom_result_prev_bb[local]:
  !s output_val retOff retSize run_result p.
    extract_venom_result (s with vs_prev_bb := p) output_val retOff retSize
      run_result =
    OPTION_MAP (\q. (FST q, (SND q) with vs_prev_bb := p))
               (extract_venom_result s output_val retOff retSize run_result)
Proof
  rpt gen_tac >> simp[extract_venom_result_def, LET_THM] >>
  Cases_on `run_result` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `x1.contexts` >> simp[] >>
  Cases_on `h` >> Cases_on `t` >> simp[] >>
  Cases_on `x0` >>
  simp[write_memory_with_expansion_def, LET_THM,
       venom_state_component_equality] >>
  Cases_on `y` >>
  simp[write_memory_with_expansion_def, LET_THM,
       venom_state_component_equality]
QED

val ext_call_rw_prev_bb =
  [LET_THM, read_mem_prev_bb, extract_venom_result_prev_bb,
   option_case_OPTION_MAP_prev_bb, update_var_prev_bb];

Theorem exec_ext_call_prev_bb[local]:
  !inst s gas addr value ao as_ ro rs is_static p.
    exec_ext_call inst (s with vs_prev_bb := p) gas addr value ao as_ ro rs
      is_static =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (exec_ext_call inst s gas addr value ao as_ ro rs is_static)
Proof
  rpt gen_tac >>
  simp([exec_ext_call_def, make_venom_call_state_prev_bb] @ ext_call_rw_prev_bb) >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[exec_result_map_prev_bb_def, update_var_prev_bb, venom_state_component_equality]
QED

Theorem exec_delegatecall_prev_bb[local]:
  !inst s gas addr ao as_ ro rs p.
    exec_delegatecall inst (s with vs_prev_bb := p) gas addr ao as_ ro rs =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (exec_delegatecall inst s gas addr ao as_ ro rs)
Proof
  rpt gen_tac >>
  simp([exec_delegatecall_def, make_venom_delegatecall_state_prev_bb]
       @ ext_call_rw_prev_bb) >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[exec_result_map_prev_bb_def, update_var_prev_bb, venom_state_component_equality]
QED

Theorem exec_create_prev_bb[local]:
  !inst s value offset sz salt_opt p.
    exec_create inst (s with vs_prev_bb := p) value offset sz salt_opt =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (exec_create inst s value offset sz salt_opt)
Proof
  rpt gen_tac >>
  simp([exec_create_def, make_venom_create_state_prev_bb] @ ext_call_rw_prev_bb) >>
  Cases_on `salt_opt` >> simp[] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[exec_result_map_prev_bb_def, update_var_prev_bb, venom_state_component_equality]
QED

(* ================================================================
   Rewrite sets for the main proof
   ================================================================ *)

val prev_bb_rw = [eval_op_prev_bb, eval_ops_prev_bb, update_var_prev_bb,
              write_mem_prev_bb, read_mem_prev_bb, jump_to_prev_bb,
              halt_state_prev_bb, revert_state_prev_bb, set_returndata_prev_bb,
              mstore_prev_bb, istore_prev_bb, mstore8_prev_bb,
              sstore_prev_bb, tstore_prev_bb, mcopy_prev_bb,
              mload_prev_bb, sload_prev_bb, tload_prev_bb,
              exec_result_map_prev_bb_def];

(* ================================================================
   MAIN THEOREM 1: For non-PHI, non-terminator opcodes,
   step_inst_base commutes with vs_prev_bb update.
   ================================================================ *)

val prev_bb_opcode_tac =
  strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[is_terminator_def,
      exec_pure1_prev_bb, exec_pure2_prev_bb, exec_pure3_prev_bb,
      exec_alloca_prev_bb] >>
  TRY (irule exec_read0_prev_bb >> simp prev_bb_rw) >>
  TRY (irule exec_read1_prev_bb >> simp prev_bb_rw) >>
  TRY (irule exec_write2_prev_bb >> simp prev_bb_rw) >>
  simp[eval_op_prev_bb, eval_ops_prev_bb,
       exec_ext_call_prev_bb, exec_delegatecall_prev_bb,
       exec_create_prev_bb] >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp(prev_bb_rw @ [venom_state_component_equality])) >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp(prev_bb_rw @ [venom_state_component_equality])) >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp(prev_bb_rw @ [venom_state_component_equality])) >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp(prev_bb_rw @ [venom_state_component_equality])) >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp(prev_bb_rw @ [venom_state_component_equality])) >>
  TRY (BasicProvers.TOP_CASE_TAC >> simp(prev_bb_rw @ [venom_state_component_equality])) >>
  simp(prev_bb_rw @ [venom_state_component_equality]);

Theorem step_inst_base_prev_bb_indep:
  !inst s p.
    inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    exec_result_map_prev_bb (\s'. s' with vs_prev_bb := p)
      (step_inst_base inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode`
  >- prev_bb_opcode_tac (* ADD *)
  >- prev_bb_opcode_tac (* SUB *)
  >- prev_bb_opcode_tac (* MUL *)
  >- prev_bb_opcode_tac (* Div *)
  >- prev_bb_opcode_tac (* SDIV *)
  >- prev_bb_opcode_tac (* Mod *)
  >- prev_bb_opcode_tac (* SMOD *)
  >- prev_bb_opcode_tac (* Exp *)
  >- prev_bb_opcode_tac (* ADDMOD *)
  >- prev_bb_opcode_tac (* MULMOD *)
  >- prev_bb_opcode_tac (* EQ *)
  >- prev_bb_opcode_tac (* LT *)
  >- prev_bb_opcode_tac (* GT *)
  >- prev_bb_opcode_tac (* SLT *)
  >- prev_bb_opcode_tac (* SGT *)
  >- prev_bb_opcode_tac (* ISZERO *)
  >- prev_bb_opcode_tac (* AND *)
  >- prev_bb_opcode_tac (* OR *)
  >- prev_bb_opcode_tac (* XOR *)
  >- prev_bb_opcode_tac (* NOT *)
  >- prev_bb_opcode_tac (* SHL *)
  >- prev_bb_opcode_tac (* SHR *)
  >- prev_bb_opcode_tac (* SAR *)
  >- prev_bb_opcode_tac (* SIGNEXTEND *)
  >- prev_bb_opcode_tac (* BYTE *)
  >- prev_bb_opcode_tac (* MLOAD *)
  >- prev_bb_opcode_tac (* MSTORE *)
  >- prev_bb_opcode_tac (* MSTORE8 *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, mcopy_prev_bb] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* MCOPY *)
  >- prev_bb_opcode_tac (* MEMTOP *)
  >- prev_bb_opcode_tac (* SLOAD *)
  >- prev_bb_opcode_tac (* SSTORE *)
  >- prev_bb_opcode_tac (* TLOAD *)
  >- prev_bb_opcode_tac (* TSTORE *)
  >- prev_bb_opcode_tac (* ILOAD *)
  >- prev_bb_opcode_tac (* ISTORE *)
  >- prev_bb_opcode_tac (* JMP *)
  >- prev_bb_opcode_tac (* JNZ *)
  >- prev_bb_opcode_tac (* DJMP *)
  >- prev_bb_opcode_tac (* RET *)
  >- prev_bb_opcode_tac (* RETURN *)
  >- prev_bb_opcode_tac (* REVERT *)
  >- prev_bb_opcode_tac (* STOP *)
  >- prev_bb_opcode_tac (* SINK *)
  >- prev_bb_opcode_tac (* PHI *)
  >- prev_bb_opcode_tac (* PARAM *)
  >- prev_bb_opcode_tac (* ASSIGN *)
  >- prev_bb_opcode_tac (* NOP *)
  >- prev_bb_opcode_tac (* ALLOCA *)
  >- prev_bb_opcode_tac (* DALLOCA *)
  >- prev_bb_opcode_tac (* DRET *)
  >- prev_bb_opcode_tac (* GETFMP *)
  >- prev_bb_opcode_tac (* SETFMP *)
  >- prev_bb_opcode_tac (* RETFMP *)
  >- prev_bb_opcode_tac (* INITIAL_FMP *)
  >- (strip_tac >> gvs[] >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, exec_result_map_prev_bb_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp[update_var_def, exec_result_map_prev_bb_def]) (* BUMP *)
  >- prev_bb_opcode_tac (* INVOKE *)
  >- prev_bb_opcode_tac (* FMP_PARAM *)
  >- prev_bb_opcode_tac (* RETPC_PARAM *)
  >- prev_bb_opcode_tac (* CALLER *)
  >- prev_bb_opcode_tac (* CALLVALUE *)
  >- prev_bb_opcode_tac (* CALLDATALOAD *)
  >- prev_bb_opcode_tac (* CALLDATASIZE *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, write_mem_prev_bb,
           exec_result_map_prev_bb_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* CALLDATACOPY *)
  >- prev_bb_opcode_tac (* ADDRESS *)
  >- prev_bb_opcode_tac (* ORIGIN *)
  >- prev_bb_opcode_tac (* GASPRICE *)
  >- prev_bb_opcode_tac (* GAS *)
  >- prev_bb_opcode_tac (* GASLIMIT *)
  >- prev_bb_opcode_tac (* COINBASE *)
  >- prev_bb_opcode_tac (* TIMESTAMP *)
  >- prev_bb_opcode_tac (* NUMBER *)
  >- prev_bb_opcode_tac (* PREVRANDAO *)
  >- prev_bb_opcode_tac (* CHAINID *)
  >- prev_bb_opcode_tac (* SELFBALANCE *)
  >- prev_bb_opcode_tac (* BALANCE *)
  >- prev_bb_opcode_tac (* BLOCKHASH *)
  >- prev_bb_opcode_tac (* BASEFEE *)
  >- prev_bb_opcode_tac (* CODESIZE *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, write_mem_prev_bb,
           exec_result_map_prev_bb_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* CODECOPY *)
  >- prev_bb_opcode_tac (* EXTCODESIZE *)
  >- prev_bb_opcode_tac (* EXTCODEHASH *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, write_mem_prev_bb,
           exec_result_map_prev_bb_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* EXTCODECOPY *)
  >- prev_bb_opcode_tac (* RETURNDATASIZE *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, write_mem_prev_bb, halt_state_prev_bb,
           set_returndata_prev_bb, exec_result_map_prev_bb_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* RETURNDATACOPY *)
  >- prev_bb_opcode_tac (* BLOBHASH *)
  >- prev_bb_opcode_tac (* BLOBBASEFEE *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, read_mem_prev_bb, update_var_prev_bb,
           exec_result_map_prev_bb_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* SHA3 *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, exec_ext_call_prev_bb] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* CALL *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, exec_ext_call_prev_bb] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* STATICCALL *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, exec_delegatecall_prev_bb] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* DELEGATECALL *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, exec_create_prev_bb] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* CREATE *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, exec_create_prev_bb] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* CREATE2 *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, eval_ops_prev_bb, read_mem_prev_bb,
           exec_result_map_prev_bb_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* LOG *)
  >- prev_bb_opcode_tac (* SELFDESTRUCT *)
  >- prev_bb_opcode_tac (* INVALID *)
  >- prev_bb_opcode_tac (* ASSERT *)
  >- prev_bb_opcode_tac (* ASSERT_UNREACHABLE *)
  >- prev_bb_opcode_tac (* DLOAD *)
  >- (strip_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      simp[eval_op_prev_bb, write_mem_prev_bb,
           exec_result_map_prev_bb_def] >>
      BasicProvers.EVERY_CASE_TAC >>
      simp(prev_bb_rw @ [venom_state_component_equality])) (* DLOADBYTES *)
  >- prev_bb_opcode_tac (* OFFSET *)
QED

(* ================================================================
   JUMP TERMINATORS: step_inst_base ignores vs_prev_bb entirely
   (plain equality). jump_to sets vs_prev_bb from vs_current_bb.
   ================================================================ *)

Theorem step_inst_base_jump_prev_bb:
  !inst s p.
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) ==>
    step_inst_base inst (s with vs_prev_bb := p) =
    step_inst_base inst s
Proof
  rpt strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  simp[eval_op_prev_bb, eval_ops_prev_bb] >>
  BasicProvers.EVERY_CASE_TAC >>
  simp[jump_to_prev_bb]
QED

