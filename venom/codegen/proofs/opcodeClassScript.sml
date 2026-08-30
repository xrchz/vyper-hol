(*
 * Opcode result classification helpers
 *
 * Classifies which opcodes can produce Halt/Abort results.
 * Shared by gen_inst_halt_sim and gen_inst_abort_sim.
 *)


Theory opcodeClass
Ancestors
  venomExecSemantics venomInst venomEffects
Libs
  BasicProvers

(* ===== exec_* result type lemmas ===== *)
(* Each exec wrapper only returns OK or Error — never Halt/Abort/IntRet.
   Proving these individually is fast; using them as [simp] makes the
   opcode case split in the main theorems fast. *)

(* Reusable tactic for exec_* not_halt/not_abort proofs *)
val exec_case_tac = rpt gen_tac >> simp[] >> every_case_tac >> simp[];

(* --- Not Halt --- *)

val exec_pure1_not_halt = store_thm("exec_pure1_not_halt[local,simp]",
  ``!f inst s vs'. exec_pure1 f inst s <> Halt vs'``,
  simp[exec_pure1_def] >> exec_case_tac);
val exec_pure2_not_halt = store_thm("exec_pure2_not_halt[local,simp]",
  ``!f inst s vs'. exec_pure2 f inst s <> Halt vs'``,
  simp[exec_pure2_def] >> exec_case_tac);
val exec_pure3_not_halt = store_thm("exec_pure3_not_halt[local,simp]",
  ``!f inst s vs'. exec_pure3 f inst s <> Halt vs'``,
  simp[exec_pure3_def] >> exec_case_tac);
val exec_read0_not_halt = store_thm("exec_read0_not_halt[local,simp]",
  ``!f inst s vs'. exec_read0 f inst s <> Halt vs'``,
  simp[exec_read0_def] >> exec_case_tac);
val exec_read1_not_halt = store_thm("exec_read1_not_halt[local,simp]",
  ``!f inst s vs'. exec_read1 f inst s <> Halt vs'``,
  simp[exec_read1_def] >> exec_case_tac);
val exec_write2_not_halt = store_thm("exec_write2_not_halt[local,simp]",
  ``!f inst s vs'. exec_write2 f inst s <> Halt vs'``,
  simp[exec_write2_def] >> exec_case_tac);
val exec_ext_call_not_halt = store_thm("exec_ext_call_not_halt[local,simp]",
  ``!inst s g a v ao as_ ro rs st vs'.
    exec_ext_call inst s g a v ao as_ ro rs st <> Halt vs'``,
  simp[exec_ext_call_def] >> exec_case_tac);
val exec_delegatecall_not_halt = store_thm(
  "exec_delegatecall_not_halt[local,simp]",
  ``!inst s g a ao as_ ro rs vs'.
    exec_delegatecall inst s g a ao as_ ro rs <> Halt vs'``,
  simp[exec_delegatecall_def] >> exec_case_tac);
val exec_create_not_halt = store_thm("exec_create_not_halt[local,simp]",
  ``!inst s v off sz salt vs'.
    exec_create inst s v off sz salt <> Halt vs'``,
  simp[exec_create_def] >> exec_case_tac);
val exec_alloca_not_halt = store_thm("exec_alloca_not_halt[local,simp]",
  ``!inst s a vs'. exec_alloca inst s a <> Halt vs'``,
  simp[exec_alloca_def] >> exec_case_tac);

(* --- Not Abort --- *)

val exec_pure1_not_abort = store_thm("exec_pure1_not_abort[local,simp]",
  ``!f inst s a vs'. exec_pure1 f inst s <> Abort a vs'``,
  simp[exec_pure1_def] >> exec_case_tac);
val exec_pure2_not_abort = store_thm("exec_pure2_not_abort[local,simp]",
  ``!f inst s a vs'. exec_pure2 f inst s <> Abort a vs'``,
  simp[exec_pure2_def] >> exec_case_tac);
val exec_pure3_not_abort = store_thm("exec_pure3_not_abort[local,simp]",
  ``!f inst s a vs'. exec_pure3 f inst s <> Abort a vs'``,
  simp[exec_pure3_def] >> exec_case_tac);
val exec_read0_not_abort = store_thm("exec_read0_not_abort[local,simp]",
  ``!f inst s a vs'. exec_read0 f inst s <> Abort a vs'``,
  simp[exec_read0_def] >> exec_case_tac);
val exec_read1_not_abort = store_thm("exec_read1_not_abort[local,simp]",
  ``!f inst s a vs'. exec_read1 f inst s <> Abort a vs'``,
  simp[exec_read1_def] >> exec_case_tac);
val exec_write2_not_abort = store_thm("exec_write2_not_abort[local,simp]",
  ``!f inst s a vs'. exec_write2 f inst s <> Abort a vs'``,
  simp[exec_write2_def] >> exec_case_tac);
val exec_ext_call_not_abort = store_thm(
  "exec_ext_call_not_abort[local,simp]",
  ``!inst s g a v ao as_ ro rs st ab vs'.
    exec_ext_call inst s g a v ao as_ ro rs st <> Abort ab vs'``,
  simp[exec_ext_call_def] >> exec_case_tac);
val exec_delegatecall_not_abort = store_thm(
  "exec_delegatecall_not_abort[local,simp]",
  ``!inst s g a ao as_ ro rs ab vs'.
    exec_delegatecall inst s g a ao as_ ro rs <> Abort ab vs'``,
  simp[exec_delegatecall_def] >> exec_case_tac);
val exec_create_not_abort = store_thm("exec_create_not_abort[local,simp]",
  ``!inst s v off sz salt ab vs'.
    exec_create inst s v off sz salt <> Abort ab vs'``,
  simp[exec_create_def] >> exec_case_tac);
val exec_alloca_not_abort = store_thm("exec_alloca_not_abort[local,simp]",
  ``!inst s a ab vs'. exec_alloca inst s a <> Abort ab vs'``,
  simp[exec_alloca_def] >> exec_case_tac);


(* --- Not IntRet --- *)

Triviality exec_pure1_not_intret[local,simp]:
  !f inst s vals vs'. exec_pure1 f inst s <> IntRet vals vs'
Proof
  simp[exec_pure1_def] >> exec_case_tac
QED

Triviality exec_pure2_not_intret[local,simp]:
  !f inst s vals vs'. exec_pure2 f inst s <> IntRet vals vs'
Proof
  simp[exec_pure2_def] >> exec_case_tac
QED

Triviality exec_pure3_not_intret[local,simp]:
  !f inst s vals vs'. exec_pure3 f inst s <> IntRet vals vs'
Proof
  simp[exec_pure3_def] >> exec_case_tac
QED

Triviality exec_read0_not_intret[local,simp]:
  !f inst s vals vs'. exec_read0 f inst s <> IntRet vals vs'
Proof
  simp[exec_read0_def] >> exec_case_tac
QED

Triviality exec_read1_not_intret[local,simp]:
  !f inst s vals vs'. exec_read1 f inst s <> IntRet vals vs'
Proof
  simp[exec_read1_def] >> exec_case_tac
QED

Triviality exec_write2_not_intret[local,simp]:
  !f inst s vals vs'. exec_write2 f inst s <> IntRet vals vs'
Proof
  simp[exec_write2_def] >> exec_case_tac
QED

Triviality exec_ext_call_not_intret[local,simp]:
  !inst s g a v ao as_ ro rs st vals vs'.
    exec_ext_call inst s g a v ao as_ ro rs st <> IntRet vals vs'
Proof
  simp[exec_ext_call_def] >> exec_case_tac
QED

Triviality exec_delegatecall_not_intret[local,simp]:
  !inst s g a ao as_ ro rs vals vs'.
    exec_delegatecall inst s g a ao as_ ro rs <> IntRet vals vs'
Proof
  simp[exec_delegatecall_def] >> exec_case_tac
QED

Triviality exec_create_not_intret[local,simp]:
  !inst s v off sz salt vals vs'.
    exec_create inst s v off sz salt <> IntRet vals vs'
Proof
  simp[exec_create_def] >> exec_case_tac
QED

Triviality exec_alloca_not_intret[local,simp]:
  !inst s a vals vs'. exec_alloca inst s a <> IntRet vals vs'
Proof
  simp[exec_alloca_def] >> exec_case_tac
QED
(* ===== Main classification theorems ===== *)

Triviality terminator_opcode_cases[local]:
  !op.
    is_terminator op ==>
    op = JMP \/ op = JNZ \/ op = DJMP \/ op = RET \/
    op = RETURN \/ op = REVERT \/ op = STOP \/ op = SINK \/
    op = DRET \/ op = RETFMP \/ op = SELFDESTRUCT \/ op = INVALID
Proof
  Cases >> gvs[is_terminator_def]
QED

Triviality step_inst_base_halt_terminator_opcodes[local]:
  !inst vs vs'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst vs = Halt vs' ==>
    inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
    inst.inst_opcode = SINK \/ inst.inst_opcode = SELFDESTRUCT
Proof
  rpt strip_tac >>
  drule terminator_opcode_cases >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst vs = Halt vs'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def]
  >- gvs[AllCaseEqs()]
  >- gvs[AllCaseEqs()]
  >- gvs[AllCaseEqs()]
  >- gvs[AllCaseEqs()]
  >- gvs[AllCaseEqs()]
  >- (gvs[AllCaseEqs()] >> rpt strip_tac >> pairarg_tac >> gvs[])
  >- gvs[AllCaseEqs()]
  >- gvs[AllCaseEqs()]
QED

Triviality step_inst_base_abort_terminator_opcodes[local]:
  !inst vs a vs'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst vs = Abort a vs' ==>
    inst.inst_opcode = REVERT \/ inst.inst_opcode = INVALID
Proof
  rpt strip_tac >>
  drule terminator_opcode_cases >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst vs = Abort a vs'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >> pairarg_tac >> gvs[]
QED

Triviality nonterminator_opcode_class[local]:
  !op. ~is_terminator op ==>
    is_effect_free_op op \/
    is_mem_write_op op \/
    is_alloca_op op \/
    is_ext_call_op op \/
    op = SSTORE \/ op = TSTORE \/ op = ISTORE \/ op = LOG \/
    op = SETFMP \/ op = DALLOCA \/
    op = ASSERT \/ op = ASSERT_UNREACHABLE \/ op = INVOKE
Proof
  Cases >> EVAL_TAC
QED

Definition ef_pure1_def:
  ef_pure1 op <=> op = NOT \/ op = ISZERO
End

Definition ef_arith1_def:
  ef_arith1 op <=> op = ADD \/ op = SUB \/ op = MUL \/ op = Div
End

Definition ef_arith2_def:
  ef_arith2 op <=> op = SDIV \/ op = Mod \/ op = SMOD \/ op = Exp
End

Definition ef_cmp_def:
  ef_cmp op <=> op = EQ \/ op = LT \/ op = GT \/ op = SLT \/ op = SGT
End

Definition ef_bits_def:
  ef_bits op <=> op = AND \/ op = OR \/ op = XOR \/ op = SHL \/
    op = SHR \/ op = SAR \/ op = SIGNEXTEND \/ op = BYTE \/ op = OFFSET
End

Definition ef_pure3_def:
  ef_pure3 op <=> op = ADDMOD \/ op = MULMOD
End

Definition ef_read0_def:
  ef_read0 op <=> op = CALLER \/ op = ADDRESS \/ op = CALLVALUE \/
    op = GAS \/ op = ORIGIN \/ op = GASPRICE \/ op = CHAINID \/
    op = COINBASE \/ op = TIMESTAMP \/ op = NUMBER \/ op = PREVRANDAO \/
    op = GASLIMIT \/ op = BASEFEE \/ op = BLOBBASEFEE \/
    op = SELFBALANCE \/ op = CALLDATASIZE \/ op = RETURNDATASIZE \/
    op = MEMTOP \/ op = CODESIZE
End

Definition ef_read1_def:
  ef_read1 op <=> op = MLOAD \/ op = SLOAD \/ op = TLOAD \/
    op = ILOAD \/ op = DLOAD \/ op = BLOCKHASH \/ op = BLOBHASH \/
    op = BALANCE \/ op = CALLDATALOAD \/ op = EXTCODESIZE \/
    op = EXTCODEHASH
End

Definition ef_misc_def:
  ef_misc op <=> op = SHA3 \/ op = PHI \/ op = ASSIGN \/ op = PARAM \/ op = NOP \/
    op = GETFMP \/ op = INITIAL_FMP \/ op = BUMP \/
    op = FMP_PARAM \/ op = RETPC_PARAM
End

Triviality effect_free_group_cases[local]:
  !op. is_effect_free_op op ==>
    ef_pure1 op \/ ef_arith1 op \/ ef_arith2 op \/ ef_cmp op \/
    ef_bits op \/ ef_pure3 op \/ ef_read0 op \/ ef_read1 op \/ ef_misc op
Proof
  Cases >> EVAL_TAC
QED

Triviality effect_free_opcode_cases[local]:
  !op. is_effect_free_op op ==>
    (op = NOT \/ op = ISZERO) \/
    (op = ADD \/ op = SUB \/ op = MUL \/ op = Div \/ op = SDIV \/
     op = Mod \/ op = SMOD \/ op = Exp) \/
    (op = EQ \/ op = LT \/ op = GT \/ op = SLT \/ op = SGT) \/
    (op = AND \/ op = OR \/ op = XOR \/ op = SHL \/
     op = SHR \/ op = SAR \/ op = SIGNEXTEND \/ op = BYTE \/
     op = OFFSET) \/
    (op = ADDMOD \/ op = MULMOD) \/
    (op = CALLER \/ op = ADDRESS \/ op = CALLVALUE \/ op = GAS \/
     op = ORIGIN \/ op = GASPRICE \/ op = CHAINID \/
     op = COINBASE \/ op = TIMESTAMP \/ op = NUMBER \/
     op = PREVRANDAO \/ op = GASLIMIT \/ op = BASEFEE \/
     op = BLOBBASEFEE \/ op = SELFBALANCE \/ op = CALLDATASIZE \/
     op = RETURNDATASIZE \/ op = MEMTOP \/ op = CODESIZE) \/
    (op = MLOAD \/ op = SLOAD \/ op = TLOAD \/ op = ILOAD \/
     op = DLOAD \/ op = BLOCKHASH \/ op = BLOBHASH \/ op = BALANCE \/
     op = CALLDATALOAD \/ op = EXTCODESIZE \/ op = EXTCODEHASH) \/
    (op = SHA3 \/ op = PHI \/ op = ASSIGN \/ op = PARAM \/ op = NOP \/
     op = GETFMP \/ op = INITIAL_FMP \/ op = BUMP \/
     op = FMP_PARAM \/ op = RETPC_PARAM)
Proof
  Cases >> EVAL_TAC
QED

Triviality effect_free_not_intret[local]:
  !inst s vals vs'.
    is_effect_free_op inst.inst_opcode ==>
    step_inst_base inst s <> IntRet vals vs'
Proof
  rpt strip_tac >>
  drule effect_free_group_cases >> strip_tac
  >- (gvs[ef_pure1_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (gvs[ef_arith1_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (gvs[ef_arith2_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (gvs[ef_cmp_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (gvs[ef_bits_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (gvs[ef_pure3_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (gvs[ef_read0_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (gvs[ef_read1_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (gvs[ef_misc_def] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      gvs[AllCaseEqs(), extract_venom_result_def])
QED

Triviality effect_free_pure1_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = NOT \/ inst.inst_opcode = ISZERO) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  every_case_tac >> gvs[]
QED

Triviality effect_free_pure2_arith1_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
     inst.inst_opcode = MUL \/ inst.inst_opcode = Div) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  every_case_tac >> gvs[]
QED

Triviality effect_free_pure2_arith2_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = SDIV \/ inst.inst_opcode = Mod \/
     inst.inst_opcode = SMOD \/ inst.inst_opcode = Exp) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  every_case_tac >> gvs[]
QED

Triviality effect_free_pure2_cmp_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
     inst.inst_opcode = SLT \/ inst.inst_opcode = SGT) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  every_case_tac >> gvs[]
QED

Triviality effect_free_pure2_bits_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = AND \/ inst.inst_opcode = OR \/ inst.inst_opcode = XOR \/
     inst.inst_opcode = SHL \/ inst.inst_opcode = SHR \/ inst.inst_opcode = SAR \/
     inst.inst_opcode = SIGNEXTEND \/ inst.inst_opcode = BYTE \/
     inst.inst_opcode = OFFSET) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  every_case_tac >> gvs[]
QED

Triviality effect_free_pure3_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = ADDMOD \/ inst.inst_opcode = MULMOD) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  every_case_tac >> gvs[]
QED

Triviality effect_free_read0_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = CALLER \/ inst.inst_opcode = ADDRESS \/
     inst.inst_opcode = CALLVALUE \/ inst.inst_opcode = GAS \/
     inst.inst_opcode = ORIGIN \/ inst.inst_opcode = GASPRICE \/
     inst.inst_opcode = CHAINID \/ inst.inst_opcode = COINBASE \/
     inst.inst_opcode = TIMESTAMP \/ inst.inst_opcode = NUMBER \/
     inst.inst_opcode = PREVRANDAO \/ inst.inst_opcode = GASLIMIT \/
     inst.inst_opcode = BASEFEE \/ inst.inst_opcode = BLOBBASEFEE \/
     inst.inst_opcode = SELFBALANCE \/ inst.inst_opcode = CALLDATASIZE \/
     inst.inst_opcode = RETURNDATASIZE \/ inst.inst_opcode = MEMTOP \/
     inst.inst_opcode = CODESIZE) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  every_case_tac >> gvs[]
QED

Triviality effect_free_read1_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = MLOAD \/ inst.inst_opcode = SLOAD \/
     inst.inst_opcode = TLOAD \/ inst.inst_opcode = ILOAD \/
     inst.inst_opcode = DLOAD \/ inst.inst_opcode = BLOCKHASH \/
     inst.inst_opcode = BLOBHASH \/ inst.inst_opcode = BALANCE \/
     inst.inst_opcode = CALLDATALOAD \/ inst.inst_opcode = EXTCODESIZE \/
     inst.inst_opcode = EXTCODEHASH) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      first_x_assum mp_tac >> gvs[] >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[]) >>
  strip_tac >>
  first_x_assum mp_tac >> gvs[] >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  every_case_tac >> gvs[]
QED

Triviality effect_free_misc_result_class[local]:
  !inst s vs' a.
    (inst.inst_opcode = SHA3 \/ inst.inst_opcode = PHI \/
     inst.inst_opcode = ASSIGN \/ inst.inst_opcode = PARAM \/
     inst.inst_opcode = NOP \/ inst.inst_opcode = GETFMP \/
     inst.inst_opcode = INITIAL_FMP \/ inst.inst_opcode = BUMP \/
     inst.inst_opcode = FMP_PARAM \/ inst.inst_opcode = RETPC_PARAM) ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
  gvs[AllCaseEqs()]
QED

Triviality effect_free_not_halt_abort[local]:
  !inst s vs' a.
    is_effect_free_op inst.inst_opcode ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      drule effect_free_group_cases >> strip_tac
      >- (gvs[ef_pure1_def] >> metis_tac[effect_free_pure1_result_class])
      >- (gvs[ef_arith1_def] >> metis_tac[effect_free_pure2_arith1_result_class])
      >- (gvs[ef_arith2_def] >> metis_tac[effect_free_pure2_arith2_result_class])
      >- (gvs[ef_cmp_def] >> metis_tac[effect_free_pure2_cmp_result_class])
      >- (gvs[ef_bits_def] >> metis_tac[effect_free_pure2_bits_result_class])
      >- (gvs[ef_pure3_def] >> metis_tac[effect_free_pure3_result_class])
      >- (gvs[ef_read0_def] >> metis_tac[effect_free_read0_result_class])
      >- (gvs[ef_read1_def] >> metis_tac[effect_free_read1_result_class])
      >- (gvs[ef_misc_def] >> metis_tac[effect_free_misc_result_class])) >>
  strip_tac >>
  drule effect_free_group_cases >> strip_tac
  >- (gvs[ef_pure1_def] >> metis_tac[effect_free_pure1_result_class])
  >- (gvs[ef_arith1_def] >> metis_tac[effect_free_pure2_arith1_result_class])
  >- (gvs[ef_arith2_def] >> metis_tac[effect_free_pure2_arith2_result_class])
  >- (gvs[ef_cmp_def] >> metis_tac[effect_free_pure2_cmp_result_class])
  >- (gvs[ef_bits_def] >> metis_tac[effect_free_pure2_bits_result_class])
  >- (gvs[ef_pure3_def] >> metis_tac[effect_free_pure3_result_class])
  >- (gvs[ef_read0_def] >> metis_tac[effect_free_read0_result_class])
  >- (gvs[ef_read1_def] >> metis_tac[effect_free_read1_result_class])
  >- (gvs[ef_misc_def] >> metis_tac[effect_free_misc_result_class])
QED

Triviality mem_write_opcode_cases[local]:
  !op. is_mem_write_op op ==>
    op = MSTORE \/ op = MSTORE8 \/ op = MCOPY \/ op = CALLDATACOPY \/
    op = RETURNDATACOPY \/ op = CODECOPY \/ op = EXTCODECOPY \/
    op = DLOADBYTES \/ op = DRET
Proof
  Cases >> EVAL_TAC
QED

Triviality mem_write_not_halt[local]:
  !inst s vs'.
    is_mem_write_op inst.inst_opcode ==>
    step_inst_base inst s <> Halt vs'
Proof
  rpt strip_tac >>
  drule mem_write_opcode_cases >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = Halt vs'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >> pairarg_tac >> gvs[]
QED

Triviality mem_write_abort_opcode[local]:
  !inst s a vs'.
    is_mem_write_op inst.inst_opcode /\
    step_inst_base inst s = Abort a vs' ==>
    inst.inst_opcode = RETURNDATACOPY
Proof
  rpt strip_tac >>
  drule mem_write_opcode_cases >> strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = Abort a vs'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[AllCaseEqs()] >>
  rpt strip_tac >> pairarg_tac >> gvs[]
QED

Triviality mem_write_result_class[local]:
  !inst s vs' a.
    is_mem_write_op inst.inst_opcode ==>
    step_inst_base inst s <> Halt vs' /\
    (step_inst_base inst s = Abort a vs' ==> inst.inst_opcode = RETURNDATACOPY)
Proof
  metis_tac[mem_write_not_halt, mem_write_abort_opcode]
QED

Triviality alloca_not_halt_abort[local]:
  !inst s vs' a.
    is_alloca_op inst.inst_opcode ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (strip_tac >>
      Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
      qpat_x_assum `step_inst_base inst s = Halt vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >>
      gvs[AllCaseEqs()]) >>
  strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
  qpat_x_assum `step_inst_base inst s = Abort a vs'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[AllCaseEqs()]
QED

Triviality ext_call_opcode_cases[local]:
  !op. is_ext_call_op op ==>
    op = CALL \/ op = STATICCALL \/ op = DELEGATECALL \/
    op = CREATE \/ op = CREATE2
Proof
  Cases >> EVAL_TAC
QED

Triviality ext_call_not_halt_abort[local]:
  !inst s vs' a.
    is_ext_call_op inst.inst_opcode ==>
    step_inst_base inst s <> Halt vs' /\
    step_inst_base inst s <> Abort a vs'
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >> (strip_tac >>
      drule ext_call_opcode_cases >>
      gvs[step_inst_base_def, AllCaseEqs()])
QED

Triviality storage_imm_log_assert_not_halt[local]:
  !inst s vs'.
    (inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE \/
     inst.inst_opcode = ISTORE \/ inst.inst_opcode = LOG \/
     inst.inst_opcode = SETFMP \/ inst.inst_opcode = DALLOCA \/
     inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE \/
     inst.inst_opcode = INVOKE) ==>
    step_inst_base inst s <> Halt vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = Halt vs'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[AllCaseEqs()]
QED

Triviality nofail_storage_imm_log_not_abort[local]:
  !inst s a vs'.
    (inst.inst_opcode = SSTORE \/ inst.inst_opcode = TSTORE \/
     inst.inst_opcode = ISTORE \/ inst.inst_opcode = LOG \/
     inst.inst_opcode = SETFMP \/ inst.inst_opcode = DALLOCA \/
     inst.inst_opcode = INVOKE) ==>
    step_inst_base inst s <> Abort a vs'
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `step_inst_base inst s = Abort a vs'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  gvs[AllCaseEqs()]
QED


Triviality step_inst_base_nonterminator_not_intret[local]:
  !inst s vals vs'.
    ~is_terminator inst.inst_opcode ==>
    step_inst_base inst s <> IntRet vals vs'
Proof
  rpt strip_tac >>
  drule nonterminator_opcode_class >> strip_tac
  >- metis_tac[effect_free_not_intret]
  >- (drule mem_write_opcode_cases >> strip_tac >>
      gvs[is_terminator_def] >>
      qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
      qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >- (drule ext_call_opcode_cases >> strip_tac >> gvs[] >>
      qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
  >> (gvs[] >> qpat_x_assum `step_inst_base inst s = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      every_case_tac >> gvs[extract_venom_result_def])
QED

Theorem step_inst_base_intret_opcodes:
  !inst vs vals vs'.
    step_inst_base inst vs = IntRet vals vs' ==>
    inst.inst_opcode = RET \/
    inst.inst_opcode = RETFMP \/
    inst.inst_opcode = DRET
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule terminator_opcode_cases >> strip_tac >> gvs[] >>
      qpat_x_assum `step_inst_base inst vs = IntRet vals vs'` mp_tac >>
      ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >>
      gvs[AllCaseEqs(), extract_venom_result_def]) >>
  metis_tac[step_inst_base_nonterminator_not_intret]
QED
Theorem step_inst_base_halt_opcodes:
  !inst vs vs'.
    step_inst_base inst vs = Halt vs' ==>
    inst.inst_opcode = STOP \/
    inst.inst_opcode = RETURN \/
    inst.inst_opcode = SINK \/
    inst.inst_opcode = SELFDESTRUCT
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all step_inst_base_halt_terminator_opcodes >> strip_tac >> simp[]) >>
  drule nonterminator_opcode_class >> strip_tac >>
  metis_tac[effect_free_not_halt_abort, mem_write_result_class,
            alloca_not_halt_abort, ext_call_not_halt_abort,
            storage_imm_log_assert_not_halt]
QED

Theorem step_inst_halt_opcodes:
  !fuel ctx inst vs vs'.
    step_inst fuel ctx inst vs = Halt vs' ==>
    inst.inst_opcode = STOP \/
    inst.inst_opcode = RETURN \/
    inst.inst_opcode = SINK \/
    inst.inst_opcode = SELFDESTRUCT \/
    inst.inst_opcode = INVOKE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- simp[] >>
  `step_inst fuel ctx inst vs = step_inst_base inst vs`
    by fs[step_inst_non_invoke] >>
  fs[] >> imp_res_tac step_inst_base_halt_opcodes >> simp[]
QED

Theorem step_inst_base_abort_opcodes:
  !inst vs a vs'.
    step_inst_base inst vs = Abort a vs' ==>
    inst.inst_opcode = REVERT \/
    inst.inst_opcode = INVALID \/
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (drule_all step_inst_base_abort_terminator_opcodes >> strip_tac >> simp[]) >>
  drule nonterminator_opcode_class >> strip_tac >>
  metis_tac[effect_free_not_halt_abort, mem_write_result_class,
            alloca_not_halt_abort, ext_call_not_halt_abort,
            nofail_storage_imm_log_not_abort]
QED

Theorem step_inst_abort_opcodes:
  !fuel ctx inst vs a vs'.
    step_inst fuel ctx inst vs = Abort a vs' ==>
    inst.inst_opcode = REVERT \/
    inst.inst_opcode = INVALID \/
    inst.inst_opcode = ASSERT \/
    inst.inst_opcode = ASSERT_UNREACHABLE \/
    inst.inst_opcode = RETURNDATACOPY \/
    inst.inst_opcode = INVOKE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >- simp[] >>
  `step_inst fuel ctx inst vs = step_inst_base inst vs`
    by fs[step_inst_non_invoke] >>
  fs[] >> imp_res_tac step_inst_base_abort_opcodes >> simp[]
QED
