(*
 * Codegen End-to-End Correctness — Theorem Statements
 *
 * Composes venomToAsm and asmToBytecode to state: if Venom IR
 * execution halts/reverts, then EVM execution of the codegen output
 * (byte list) produces a corresponding result.
 *
 * TOP-LEVEL:
 *   codegen_correct    — whole-context correctness (run_context vs run)
 *   codegen_fn_correct — per-function correctness (run_blocks vs run)
 *
 * STATUS: Final codegen correctness theorems are currently open/cheated and
 * depend on closing/stabilizing Venom→Asm and Asm→EVM simulation layers.
 * See docs/compiler-proof-roadmap.md.
 *
 * MEMTOP Exclusion
 * ===============
 * MEMTOP correspondence is excluded: asm/EVM memory may be longer
 * than Venom memory due to spill slot expansion. Vyper never exposes
 * MEMTOP to user code (used internally for free memory pointer).
 * See memory_rel in codegenRelScript.sml.
 *
 * EVM Exception Classification
 * ============================
 * How each EVM exception is handled in the correctness argument:
 *
 * OutOfGas — undischargeable in general. Requires gas_sufficient
 *   hypothesis at the top-level entry point (call_vyper_contract).
 *   Only exception that needs an explicit disjunct in theorem statements.
 *
 * StackOverflow — discharged by asm_stack_bounded precondition.
 *   The compiler should reject programs where the stack model exceeds
 *   1024. NOTE: if this fires, the proper fix is depth-aware spilling
 *   (spill to memory when stack depth approaches limit), but that is
 *   an algorithmic change to the codegen, not yet implemented.
 *
 * StackUnderflow — discharged by construction (codegen stack model
 *   tracks height; well-formed plans never underflow).
 *
 * InvalidJumpDest — discharged by construction (label_offset_consistent,
 *   assemble_parse_correct ensure all jump targets are valid JUMPDESTs).
 *
 * Reverted — handled explicitly (separate case in theorem conclusion).
 *
 * WriteInStaticContext — when the call context is static, writes
 *   (SSTORE, LOG, CREATE, SELFDESTRUCT) are demoted to nops. This is
 *   defined as an allowed optimization: the Venom semantics can
 *   execute the write, but the EVM silently fails. The correctness
 *   theorem treats this as an exception disjunct (subsumed by SOME exc).
 *   TODO: formalize static-context demotion as a separate pass/property.
 *
 * OutOfBoundsRead — RETURNDATACOPY past returndata length. Should be
 *   discharged by construction: Venom ExHalt maps to this. The proof
 *   that Vyper lowering never generates OOB reads is a separate
 *   lowering correctness obligation. NOTE: if future Vyper versions
 *   expose raw returndata access to users, this may require a runtime
 *   bounds check instead.
 *
 * AddressCollision — CREATE-specific. Handled by a separate entry
 *   point (create_vyper_contract) that includes the collision check.
 *   TODO: define create_vyper_contract alongside call_vyper_contract.
 *
 * InvalidContractPrefix — CREATE code starts with 0xEF. Similar to
 *   AddressCollision: handled via create_vyper_contract.
 *
 * InvalidParameter, KZGProofError — precompile-internal failures.
 *   Contained within the CALL frame (returns 0 on stack). Never
 *   propagates to the calling contract's execution.
 *)

Theory codegenCorrectness
Ancestors
  asmToBytecodeProps venomToAsmProps codegen vfmExecution
  codegenRel asmSem asmWf stackPlanGen stackPlanTypes planExec
  symbolResolve venomExecSemantics venomState venomInst contextCodegenRel
  stackOpSim fnPlanDecomp list rich_list finite_map arithmetic
Libs
  BasicProvers

(* ===== Context Correspondence Helpers ===== *)

(* Call context correspondence: Venom call context matches EVM message params *)
Definition call_ctx_rel_def:
  call_ctx_rel cc mp ⇔
    cc.cc_caller = mp.caller ∧
    cc.cc_address = mp.callee ∧
    cc.cc_callvalue = n2w mp.value ∧
    cc.cc_calldata = mp.data ∧
    cc.cc_static = mp.static
End

(* Tx context correspondence: Venom tx context matches EVM tx parameters *)
Definition tx_ctx_rel_def:
  tx_ctx_rel tc tp ⇔
    tc.tc_origin = tp.origin ∧
    tc.tc_gasprice = n2w tp.gasPrice ∧
    tc.tc_chainid = n2w tp.chainId ∧
    tc.tc_blobhashes = tp.blobHashes
End

(* Block context correspondence: Venom block context matches EVM block parameters *)
Definition block_ctx_rel_def:
  block_ctx_rel bc tp ⇔
    bc.bc_coinbase = tp.blockCoinBase ∧
    bc.bc_timestamp = n2w tp.blockTimeStamp ∧
    bc.bc_number = n2w tp.blockNumber ∧
    bc.bc_prevrandao = tp.prevRandao ∧
    bc.bc_gaslimit = n2w tp.blockGasLimit ∧
    bc.bc_basefee = n2w tp.baseFeePerGas ∧
    bc.bc_blobbasefee = n2w tp.baseFeePerBlobGas
End

(* Blockhash correspondence: Venom blockhash lookup matches EVM prevHashes.
   Requires blockNumber < dimword(:256) for well-formed n2w conversion. *)
Definition blockhash_rel_def:
  blockhash_rel vs tp ⇔
    vs.vs_prev_hashes = tp.prevHashes ∧
    tp.blockNumber < dimword (:256) ∧
    ∀n. vs.vs_block_ctx.bc_blockhash n =
      let bn = w2n vs.vs_block_ctx.bc_number in
      let idx = bn - n - 1 in
      if n < bn ∧ bn − 256 ≤ n ∧
         idx < LENGTH vs.vs_prev_hashes
      then EL idx vs.vs_prev_hashes
      else 0w
End

(* Stack parameter correspondence: function PARAM variables match EVM stack.
   First param deepest, last param TOS. *)
Definition stack_params_rel_def:
  stack_params_rel fn vs stack ⇔
    let params = get_params (HD fn.fn_blocks).bb_instructions in
    LENGTH params = LENGTH stack ∧
    ∀i. i < LENGTH params ⇒
      FLOOKUP vs.vs_vars (HD (EL i params).inst_outputs) =
        SOME (EL i (REVERSE stack))
End

(* ===== Initial State Correspondence ===== *)

(* At a selected function-region entry, Venom and EVM states agree on
   shared fields.  [off] is an assembly-instruction index; the EVM PC is
   the corresponding byte offset in [prog]. *)
Definition initial_state_rel_def:
  initial_state_rel cp prog off fn vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         stack_params_rel fn vs ctxt.stack ∧
         (* Live accounts and transient storage *)
         es.rollback.accounts = vs.vs_accounts ∧
         es.rollback.tStorage = vs.vs_transient ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         (* Equality is required only outside every context spill region. *)
         context_memory_rel cp vs.vs_memory ctxt.memory ∧
         (* Translate the selected instruction index to an EVM byte PC. *)
         ctxt.pc = asm_pc_to_offset prog off ∧
         ctxt.jumpDest = NONE ∧
         (* Venom state: not halted, at instruction 0 *)
         vs.vs_halted = F ∧
         vs.vs_inst_idx = 0 ∧
         call_ctx_rel vs.vs_call_ctx ctxt.msgParams ∧
         tx_ctx_rel vs.vs_tx_ctx es.txParams ∧
         block_ctx_rel vs.vs_block_ctx es.txParams ∧
         blockhash_rel vs es.txParams ∧
         vs.vs_code = ctxt.msgParams.code ∧
         (∀a. ctxt.msgParams.outputTo ≠ Code a)
     | [] => F)
End

Theorem initial_state_rel_entry_clauses[local]:
  ∀cp prog off fn vs es ctxt rb rest.
    initial_state_rel cp prog off fn vs es /\
    es.contexts = (ctxt, rb) :: rest ==>
    context_memory_rel cp vs.vs_memory ctxt.memory /\
    ctxt.pc = asm_pc_to_offset prog off
Proof
  rpt strip_tac >> gvs[initial_state_rel_def]
QED

(* ===== Return Value Correspondence ===== *)

(* After execution: return data and side effects match. *)
Definition final_state_rel_def:
  final_state_rel vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         es.rollback.accounts = vs.vs_accounts ∧
         es.rollback.tStorage = vs.vs_transient
     | [] => F)
End

(* entry_fn_no_ret is defined in contextCodegenRel so context-wide
   obligations and this correctness interface share one constant. *)

(* ===== Composition Helpers ===== *)

(* Terminal state composition: venom_asm_terminal_rel + asm_evm_rel → final_state_rel.
   After asm execution ends at a terminal, the asm state relates to both Venom (terminal_rel)
   and EVM (evm_rel). Composing these gives the end-to-end final_state_rel. *)
Theorem terminal_asm_evm_final[local]:
  !prog vs' as' es'.
    venom_asm_terminal_rel vs' as' /\
    asm_evm_rel prog as' es' ==>
    final_state_rel vs' es'
Proof
  rpt gen_tac >> strip_tac >>
  fs[venom_asm_terminal_rel_def, asm_evm_rel_def, final_state_rel_def] >>
  every_case_tac >> gvs[]
QED

(* The obsolete single-function codegen unfolding is intentionally absent:
   context codegen is exposed through [codegen_assembly] and the selected
   region is located by [ops_contain_at]. *)

(* Prefix of a list is an asm_block_at position 0 *)
Theorem asm_block_at_prefix[local]:
  !xs ys. asm_block_at (xs ++ ys) 0 xs
Proof
  Induct >> simp[asm_block_at_def, EL_APPEND1]
QED

(* Bridge from a positioned context-region entry to an assembly state. *)
Theorem initial_state_bridge[local]:
  ∀cp prog off fn vs es ctx i r unit lo.
    initial_state_rel cp prog off fn vs es /\
    generate_context_plan ctx = SOME cp /\
    i < LENGTH ctx.ctx_functions /\
    EL i ctx.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    prog = execute_plan cp.cp_initial_fmp (context_plan_ops cp) ++
           data_segment_asm unit.cu_data_segment /\
    lo = SND (compute_label_offsets prog) /\
    (case es.contexts of
       (ctxt, rb) :: _ =>
         ctxt.msgParams.code = assemble prog /\
         ctxt.msgParams.parsed = parse_code 0 FEMPTY (assemble prog)
     | [] => F) ==>
    ∃as0.
      context_venom_asm_rel cp lo
        (fn_init_ps fn r.sr_spill_base) vs as0 /\
      asm_evm_rel prog as0 es /\
      asm_block_at prog off
        (execute_plan cp.cp_initial_fmp r.sr_plan) /\
      as0.as_pc = off
Proof
  rpt gen_tac >> strip_tac >>
  every_case_tac >> gvs[] >>
  rename1 `es.contexts = (ctxt, rb) :: rest` >>
  qexists_tac `<| as_stack := ctxt.stack;
                   as_memory := ctxt.memory;
                   as_accounts := vs.vs_accounts;
                   as_transient := vs.vs_transient;
                   as_returndata := vs.vs_returndata;
                   as_logs := vs.vs_logs;
                   as_pc := off;
                   as_call_ctx := vs.vs_call_ctx;
                   as_tx_ctx := vs.vs_tx_ctx;
                   as_block_ctx := vs.vs_block_ctx;
                   as_code := vs.vs_code;
                   as_prev_hashes := vs.vs_prev_hashes |>` >>
  gvs[initial_state_rel_def, call_ctx_rel_def, tx_ctx_rel_def,
      block_ctx_rel_def, blockhash_rel_def, stack_params_rel_def,
      context_venom_asm_rel_def, fn_init_ps_def,
      init_plan_state_def, init_spill_alloc_def, LET_THM,
      plan_spill_rel_def, FLOOKUP_DEF, asm_evm_rel_def] >>
  conj_tac >- suspend "plan_stack" >>
  conj_tac >- (rpt gen_tac >> simp[CONJ_ASSOC]) >>
  gvs[asm_block_at_def, ops_contain_at_def, EL_APPEND1]
QED

Resume initial_state_bridge[plan_stack]:
  simp[plan_stack_rel_def, operand_val_def] >>
  rpt strip_tac >>
  rename1 `j < LENGTH ctxt.stack` >>
  simp[EL_REVERSE, EL_MAP, operand_val_def, FLOOKUP_DEF] >>
  qpat_x_assum `!k. k < LENGTH ctxt.stack ==> _`
    (qspec_then `PRE (LENGTH ctxt.stack - j)` mp_tac) >>
  simp[EL_REVERSE] >>
  `PRE (LENGTH ctxt.stack - PRE (LENGTH ctxt.stack - j)) = j` by simp[] >>
  simp[]
QED

Finalise initial_state_bridge

(* run_blocks never returns OK — it always terminates with
   Halt/Abort/IntRet/Error. Induction on fuel: base returns Error,
   step either recurses (smaller fuel) or passes through non-OK. *)
Theorem run_blocks_never_ok[local]:
  !fuel ctx fn s vs1. run_blocks fuel ctx fn s <> OK vs1
Proof
  Induct >- simp[Once run_blocks_def] >>
  simp[Once run_blocks_unfold] >>
  rpt gen_tac >> every_case_tac
QED

(* run_function never returns OK — unfolds to run_blocks. *)
Theorem run_function_never_ok[local]:
  !fuel ctx fn vs vs1. run_function fuel ctx fn vs <> OK vs1
Proof
  simp[run_function_def] >>
  rpt gen_tac >> every_case_tac >> simp[run_blocks_never_ok]
QED

(* run_context also never returns OK — it either dispatches to
   run_function (which never returns OK) or returns Error. *)
Theorem run_context_never_ok[local]:
  !fuel ctx vs vs1. run_context fuel ctx vs <> OK vs1
Proof
  rpt gen_tac >> simp[Once run_context_def] >>
  every_case_tac >> simp[run_function_never_ok]
QED

(* ===== Per-Function Codegen Correctness ===== *)

(* Conditional correctness for a selected function region in a complete
   compilation unit.  The selected entry may occur at nonzero instruction
   offset [off] in the emitted context program. *)
Theorem codegen_fn_correct:
  ∀fuel rpolicy unit cp prog i r fn off Inv vs.
    generate_context_plan unit.cu_context = SOME cp ∧
    codegen_assembly rpolicy unit = SOME prog ∧
    i < LENGTH unit.cu_context.ctx_functions ∧
    EL i unit.cu_context.ctx_functions = fn ∧
    EL i cp.cp_regions = r ∧
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) ∧
    codegen_context_obligations Inv unit.cu_context cp ∧
    codegen_reachability_package Inv unit.cu_context vs ⇒
    ∃gas_needed.
      ∀es. initial_state_rel cp prog off fn vs es ∧
           (case es.contexts of
              (ctxt, rb) :: _ =>
                ctxt.msgParams.gasLimit ≥ gas_needed ∧
                ctxt.msgParams.code = assemble prog ∧
                ctxt.msgParams.parsed = parse_code 0 FEMPTY (assemble prog)
            | [] => F) ⇒
        (case run_blocks fuel unit.cu_context fn vs of
           Halt vs' =>
             ∃es'. run es = SOME (INR NONE, es') ∧
                   final_state_rel vs' es'
         | Abort Revert_abort vs' =>
             ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
                   final_state_rel vs' es'
         | Abort ExHalt_abort vs' =>
             ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                       exc ≠ Reverted ∧
                       final_state_rel vs' es'
         | OK _ => F
         | IntRet _ _ => T
         | Error _ => T)
Proof
  cheat
QED

(* ===== Whole-Context Codegen Correctness ===== *)

(* Initial correspondence at the selected context-entry region.  [off] is
   an assembly-instruction index and the EVM PC is its byte offset. *)
Definition initial_ctx_rel_def:
  initial_ctx_rel cp prog off ctx vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         rb.accounts = vs.vs_accounts ∧
         rb.tStorage = vs.vs_transient ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         ctxt.stack = [] ∧
         context_memory_rel cp vs.vs_memory ctxt.memory ∧
         ctxt.pc = asm_pc_to_offset prog off
     | [] => F)
End

(* Conditional whole-context correctness for an explicitly positioned named
   entry function in a complete compilation unit. *)
Theorem codegen_correct:
  ∀fuel rpolicy unit cp prog name i r fn off Inv vs.
    generate_context_plan unit.cu_context = SOME cp ∧
    codegen_assembly rpolicy unit = SOME prog ∧
    unit.cu_context.ctx_entry = SOME name ∧
    lookup_function name unit.cu_context.ctx_functions = SOME fn ∧
    i < LENGTH unit.cu_context.ctx_functions ∧
    EL i unit.cu_context.ctx_functions = fn ∧
    EL i cp.cp_regions = r ∧
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) ∧
    codegen_context_obligations Inv unit.cu_context cp ∧
    codegen_reachability_package Inv unit.cu_context vs ⇒
    ∃gas_needed.
      ∀es. initial_ctx_rel cp prog off unit.cu_context vs es ∧
           (case es.contexts of
              (ctxt, rb) :: _ =>
                ctxt.msgParams.gasLimit ≥ gas_needed ∧
                ctxt.msgParams.code = assemble prog ∧
                ctxt.msgParams.parsed = parse_code 0 FEMPTY (assemble prog)
            | [] => F) ⇒
        (case run_context fuel unit.cu_context vs of
           Halt vs' =>
             ∃es'. run es = SOME (INR NONE, es') ∧
                   final_state_rel vs' es'
         | Abort Revert_abort vs' =>
             ∃es'. run es = SOME (INR (SOME Reverted), es') ∧
                   final_state_rel vs' es'
         | Abort ExHalt_abort vs' =>
             ∃es' exc. run es = SOME (INR (SOME exc), es') ∧
                       exc ≠ Reverted ∧
                       final_state_rel vs' es'
         | OK _ => F
         | IntRet _ _ => F
         | Error _ => T)
Proof
  cheat
QED
