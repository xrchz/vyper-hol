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
  stackOpSim list rich_list finite_map arithmetic
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

(* At function entry: Venom state and EVM state agree on shared fields,
   EVM stack holds function arguments matching PARAM variables,
   all memory is shared (no spill slots allocated yet). *)
Definition initial_state_rel_def:
  initial_state_rel fn vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         stack_params_rel fn vs ctxt.stack ∧
         (* Live accounts and transient storage *)
         es.rollback.accounts = vs.vs_accounts ∧
         es.rollback.tStorage = vs.vs_transient ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         (* Memory fully shared at function entry (no spills yet).
            read_byte zero-pads, so this handles different lengths. *)
         (∀i. read_byte i vs.vs_memory = read_byte i ctxt.memory) ∧
         (* EVM starts at pc = 0, no pending jump *)
         ctxt.pc = 0 ∧
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

(* Codegen unfold for single function: codegen with ctx_functions := [fn]
   gives generate_fn_plan fn fn_eom 0 and assembles the plan. *)
Theorem codegen_single_fn_unfold[local]:
  !ctx fn fn_eom data_seg bytecode.
    fn.fn_eom = SOME fn_eom /\
    ctx.ctx_global_reserved = [] /\
    codegen (ctx with ctx_functions := [fn])
            (FEMPTY |+ (fn.fn_name, fn_eom))
            data_seg = SOME bytecode ==>
    ?fn_ops ps_final.
      generate_fn_plan fn fn_eom 0 = SOME (fn_ops, ps_final) /\
      bytecode = assemble (execute_plan (fn_ops ++ revert_postamble) ++
                           data_segment_asm data_seg)
Proof
  rpt strip_tac >>
  fs[codegen_def] >>
  every_case_tac >> gvs[] >>
  fs[generate_context_plan_def, generate_context_plan_with_def,
     max_live_eom_def, collect_fn_eoms_def, generate_context_regions_def,
     finish_context_plan_def, context_plan_ops_def,
     staticLayoutDefsTheory.reserved_intervals_wf_def,
     staticLayoutDefsTheory.global_reserved_end_def, LET_THM] >>
  every_case_tac >>
  gvs[staticLayoutDefsTheory.reserved_intervals_wf_def,
      staticLayoutDefsTheory.global_reserved_end_def]
QED

(* Prefix of a list is an asm_block_at position 0 *)
Theorem asm_block_at_prefix[local]:
  !xs ys. asm_block_at (xs ++ ys) 0 xs
Proof
  Induct >> simp[asm_block_at_def, EL_APPEND1]
QED

(* Bridge from initial state to asm state:
   At function entry, we can construct an asm_state that simultaneously
   satisfies venom_asm_rel (linking plan state to asm state) and
   asm_evm_rel (linking asm state to EVM state). *)
Theorem initial_state_bridge[local]:
  !fn fn_eom fn_ops ps_final prog lo vs es data_seg.
    initial_state_rel fn vs es /\
    generate_fn_plan fn fn_eom 0 = SOME (fn_ops, ps_final) /\
    prog = execute_plan (fn_ops ++ revert_postamble) ++
           data_segment_asm data_seg /\
    lo = SND (compute_label_offsets prog) /\
    (case es.contexts of
       (ctxt, rb) :: _ =>
         ctxt.msgParams.code = assemble prog /\
         ctxt.msgParams.parsed = parse_code 0 FEMPTY (assemble prog)
     | [] => F) ==>
    ?as0.
      venom_asm_rel lo (fn_init_ps fn fn_eom) vs as0 /\
      asm_evm_rel prog as0 es /\
      asm_block_at prog 0 (execute_plan fn_ops) /\
      as0.as_pc = 0
Proof
  rpt gen_tac >> strip_tac >>
  (* Extract ctxt, rb from es.contexts *)
  every_case_tac >> gvs[] >>
  rename1 `es.contexts = (ctxt, rb) :: rest` >>
  (* Construct the asm witness *)
  qexists_tac `<| as_stack := ctxt.stack;
                   as_memory := ctxt.memory;
                   as_accounts := vs.vs_accounts;
                   as_transient := vs.vs_transient;
                   as_returndata := vs.vs_returndata;
                   as_logs := vs.vs_logs;
                   as_pc := 0;
                   as_call_ctx := vs.vs_call_ctx;
                   as_tx_ctx := vs.vs_tx_ctx;
                   as_block_ctx := vs.vs_block_ctx;
                   as_code := vs.vs_code;
                   as_prev_hashes := vs.vs_prev_hashes |>` >>
  gvs[initial_state_rel_def, call_ctx_rel_def, tx_ctx_rel_def,
      block_ctx_rel_def, blockhash_rel_def, stack_params_rel_def,
      venom_asm_rel_def, fn_init_ps_def,
      init_plan_state_def, init_spill_alloc_def, LET_THM,
      plan_spill_rel_def, FLOOKUP_DEF, memory_rel_def,
      asm_evm_rel_def, asm_pc_to_offset_def] >>
  (* Remaining: plan_stack_rel ∧ blockhash ∧ asm_block_at *)
  conj_tac >- suspend "plan_stack" >>
  conj_tac >- (rpt gen_tac >> simp[CONJ_ASSOC]) >>
  rewrite_tac[execute_plan_append, GSYM APPEND_ASSOC] >>
  simp[asm_block_at_prefix]
QED

Resume initial_state_bridge[plan_stack]:
  simp[plan_stack_rel_def, operand_val_def] >>
  rpt strip_tac >>
  simp[EL_REVERSE, EL_MAP, operand_val_def, FLOOKUP_DEF] >>
  qpat_x_assum `!i. i < LENGTH ctxt.stack ==> _`
    (qspec_then `PRE (LENGTH ctxt.stack - i)` mp_tac) >>
  simp[EL_REVERSE] >>
  `PRE (LENGTH ctxt.stack - PRE (LENGTH ctxt.stack - i)) = i` by simp[] >>
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

(* If codegen produces bytecode for a function, and the function
   halts/reverts in the Venom semantics, then EVM execution of
   the bytecode produces a corresponding result.

   Preconditions:
     - codegen_ready_fn: SSA, SUE, normalized CFG, valid opcodes
     - codegen succeeds (SOME bytecode)
     - initial states correspond (stack has args, shared state matches)
     - spill safety: Venom execution doesn't clobber spill region

   Gas: existential — there exists a gas bound such that with enough
   gas, EVM results correspond to Venom results. This proves the
   theorem is non-vacuous (the success case is always reachable).
   The gas bound depends on the Venom execution trace (each Venom
   step maps to finitely many EVM instructions with known gas costs).

   StackOverflow is excluded by asm_stack_bounded (codegen must
   produce stack-bounded asm). TODO: add explicit stack height check
   to codegen (return NONE if plan_max_height >= 1024).

   Spill safety: step_mem_safe for every Venom step. This is a
   property of the INPUT PROGRAM — the codegen can't establish it.
   For Vyper-generated code, the memory allocator ensures fn_eom is
   above all user allocations. For other frontends, must be assumed.

   Note: this theorem covers a single function. Multi-function
   contexts compose via the dispatch mechanism (selector table). *)
Theorem codegen_fn_correct:
  ∀fuel ctx fn fn_eom data_seg bytecode spill_hwm vs.
    codegen_ready_fn fn ∧
    fn.fn_eom = SOME fn_eom ∧
    ctx.ctx_global_reserved = [] ∧
    codegen (ctx with ctx_functions := [fn])
            (FEMPTY |+ (fn.fn_name, fn_eom))
            data_seg = SOME bytecode ∧
    (∀inst vs1 vs2 fuel'.
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe <| sa_spill_base := fn_eom;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2) ⇒
    ∃gas_needed.
      ∀es. initial_state_rel fn vs es ∧
           (case es.contexts of
              (ctxt, rb) :: _ =>
                ctxt.msgParams.gasLimit ≥ gas_needed ∧
                ctxt.msgParams.code = bytecode ∧
                ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
            | [] => F) ⇒
        (case run_blocks fuel ctx fn vs of
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
  rpt gen_tac >> strip_tac >>
  (* Unfold codegen to get generate_fn_plan *)
  drule_all codegen_single_fn_unfold >> strip_tac >>
  rename1 `generate_fn_plan fn fn_eom 0 = SOME (fn_ops, ps_final)` >>
  (* Define the assembly program *)
  qabbrev_tac `prog = execute_plan (fn_ops ++ revert_postamble) ++
                       data_segment_asm data_seg` >>
  qabbrev_tac `lo = SND (compute_label_offsets prog)` >>
  qabbrev_tac `o2p = build_offset_to_pc prog` >>
  (* Choose gas_needed — cheat for now.
     Real proof: sum of gas costs for each EVM step in the trace. *)
  qexists_tac `0` >>
  rpt gen_tac >> strip_tac >>
  (* Case split on run_function — IntRet/Error are trivial *)
  Cases_on `run_function fuel ctx fn vs` >> gvs[] >>
  (* OK case: run_function never returns OK *)
  TRY (rename1 `run_function _ _ _ _ = OK _` >> metis_tac[run_function_never_ok]) >>
  (* IntRet, Error: conclusion is T — discharged by gvs *)
  (* Halt and Abort cases: compose gen_fn_simulation + asm_bytecode_sim *)
  (* Construct initial asm state via bridge *)
  `?as0. venom_asm_rel lo (fn_init_ps fn fn_eom) vs as0 /\
         asm_evm_rel prog as0 es /\
         asm_block_at prog 0 (execute_plan fn_ops) /\
         as0.as_pc = 0` by (
    qspecl_then [`fn`, `fn_eom`, `fn_ops`, `ps_final`,
                 `prog`, `lo`, `vs`, `es`, `data_seg`]
      mp_tac initial_state_bridge >>
    impl_tac >- (fs[Abbr `prog`, Abbr `lo`] >>
                  Cases_on `es.contexts` >> gvs[]) >>
    metis_tac[]) >>
  (* Apply gen_fn_simulation to get asm execution.
     step_mem_safe alloc mismatch between codegen_fn_correct (spill_hwm)
     and gen_fn_simulation (fn_init_ps alloc). Need monotonicity.
     Then: asm_bytecode_sim composition. *)
  cheat
QED

(* ===== Whole-Context Codegen Correctness ===== *)

(* Initial state correspondence at context entry: Venom initial state
   and EVM execution state agree on environment, memory, calldata, etc.
   No function params on the EVM stack (entry starts with empty stack). *)
Definition initial_ctx_rel_def:
  initial_ctx_rel ctx vs es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         rb.accounts = vs.vs_accounts ∧
         rb.tStorage = vs.vs_transient ∧
         ctxt.returnData = vs.vs_returndata ∧
         ctxt.logs = vs.vs_logs ∧
         ctxt.stack = [] ∧
         (∀i. read_byte i vs.vs_memory = read_byte i ctxt.memory) ∧
         ctxt.pc = 0
     | [] => F)
End

(* Top-level codegen correctness: if a well-formed Venom context is
   compiled to bytecode, and run_context halts/reverts, then EVM
   execution of the bytecode produces a corresponding result.

   This composes codegen_fn_correct with run_context's dispatch to
   the entry function. *)
Theorem codegen_correct:
  ∀fuel ctx fn_eom_map data_seg bytecode spill_hwm vs.
    codegen_ready ctx ∧
    ctx_wf ctx ∧
    (* Entry function never uses RET (only internal functions do) *)
    (∀name efn. ctx.ctx_entry = SOME name ∧
                lookup_function name ctx.ctx_functions = SOME efn ⇒
                entry_fn_no_ret efn) ∧
    codegen ctx fn_eom_map data_seg = SOME bytecode ∧
    (∀fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions ∧
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe <| sa_spill_base := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2) ⇒
    ∃gas_needed.
      ∀es. initial_ctx_rel ctx vs es ∧
           (case es.contexts of
              (ctxt, rb) :: _ =>
                ctxt.msgParams.gasLimit ≥ gas_needed ∧
                ctxt.msgParams.code = bytecode ∧
                ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
            | [] => F) ⇒
        (case run_context fuel ctx vs of
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
  rpt gen_tac >> strip_tac >>
  (* Choose gas_needed *)
  qexists_tac `0` >>
  rpt gen_tac >> strip_tac >>
  (* Unfold run_context to dispatch to run_function *)
  simp[Once run_context_def] >>
  every_case_tac >> gvs[]
  (* Error cases from run_context dispatch: ctx_entry = NONE,
     entry function not found, empty entry function.
     Conclusion is T for Error. *)
  (* Remaining: run_function on the entry function *)
  (* OK case: impossible since run_function never returns OK *)
  >- metis_tac[run_function_never_ok]
  (* Halt, Abort, IntRet cases: compose gen_fn_simulation + asm_bytecode_sim *)
  >> cheat
QED
