(*
 * Codegen State Relations
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Defines the relations connecting Venom IR state, plan_state
 * (stack model abstraction), asm execution state, and EVM state.
 *
 * Three layers:
 *   1. plan_state_rel: plan_state accurately tracks the asm stack
 *      (loop invariant for block-by-block simulation)
 *   2. venom_asm_rel:  full Venom ↔ asm state relation (uses plan_state)
 *   3. asm_evm_rel:    asm execution ↔ EVM bytecode execution
 *
 * Terminal state relations (no plan_state, no memory details):
 *   venom_asm_terminal_rel — observable effects match at halt/revert
 *   asm_venom_result_rel   — result type + terminal state
 *
 * TOP-LEVEL:
 *   plan_stack_rel          — ps_stack matches concrete stack
 *   plan_spill_rel          — ps_spilled matches memory contents
 *   spill_mem_covered       — initial memory covers spill high-water mark
 *   venom_asm_rel           — full Venom ↔ asm state relation
 *   venom_asm_terminal_rel  — shared state match (for terminal results)
 *   fn_init_ps              — initial plan state with params pre-loaded
 *   asm_evm_rel             — asm ↔ EVM bytecode state relation
 *   asm_pc_to_offset        — asm index → byte offset
 *)

Theory codegenRel
Ancestors
  asmWf asmSem stackPlanGen

(* ===== Operand Evaluation in Venom State ===== *)

(* Evaluate an operand to bytes32, given venom vars and label offsets.
   Labels resolve to byte offsets from assembly. *)
Definition operand_val_def:
  operand_val vs label_offsets (Var v) = FLOOKUP vs.vs_vars v ∧
  operand_val vs label_offsets (Lit w) = SOME w ∧
  operand_val vs label_offsets (Label l) =
    OPTION_MAP n2w (FLOOKUP label_offsets l)
End

(* ===== Plan State ↔ Concrete Stack ===== *)

(* ps_stack (LAST=TOS) matches asm stack (HD=TOS).
   Each operand in ps_stack evaluates to the corresponding stack entry. *)
Definition plan_stack_rel_def:
  plan_stack_rel label_offsets vs ps_stack asm_stack ⇔
    LENGTH ps_stack = LENGTH asm_stack ∧
    ∀i. i < LENGTH ps_stack ⇒
      let op = EL i (REVERSE ps_stack) in
      let val = EL i asm_stack in
      operand_val vs label_offsets op = SOME val
End

(* Each spilled operand's value is stored at its memory offset.
   Spill slots hold 32-byte big-endian values.
   word_of_bytes on a short list zero-pads implicitly (accumulator 0w),
   so no memory length assertion is needed here — that's an
   implementation detail of MSTORE having expanded memory. *)
Definition plan_spill_rel_def:
  plan_spill_rel label_offsets vs ps_spilled asm_memory ⇔
    ∀op off.
      FLOOKUP ps_spilled op = SOME off ⇒
      ∃v. operand_val vs label_offsets op = SOME v ∧
          word_of_bytes T (0w:bytes32)
            (TAKE 32 (DROP off asm_memory)) = v
End

(* ===== Venom State ↔ Asm State ===== *)

(* Read byte with implicit zero-padding (EVM memory is zero-initialized) *)
Definition read_byte_def:
  read_byte i (mem : byte list) =
    if i < LENGTH mem then EL i mem else (0w : byte)
End

(* Memories agree outside the spill region [sa_spill_base, sa_next_offset).
   The spill allocator starts at sa_spill_base and grows upward to
   sa_next_offset. This range may contain active or freed spill data
   that differs between Venom and asm. Everywhere else must agree:
   - below sa_spill_base: user memory
   - at/above sa_next_offset: both zero or user-written

   NOTE: lengths may differ (asm memory may be longer due to spill
   expansion). This means MEMTOP returns different values on the Venom
   and asm sides. MEMTOP correspondence is explicitly excluded from
   the codegen correctness theorem. Vyper never exposes MEMTOP to
   user code — it is used internally by the compiler for the free
   memory pointer, which the compiler controls. *)
Definition memory_rel_def:
  memory_rel (alloc : spill_alloc) venom_mem asm_mem ⇔
    ∀i. ¬(alloc.sa_spill_base ≤ i ∧ i < alloc.sa_next_offset) ⇒
      read_byte i venom_mem = read_byte i asm_mem
End

(* ===== Source Memory Write Footprints ===== *)

(* A direct source write is described by its destination byte offset and
   length.  These footprints are computed from the pre-state operands, not
   from a pre/post memory diff, so idempotent writes are still represented. *)
Definition fixed_source_write_range_def:
  fixed_source_write_range s dst_op value_op len =
    case (eval_operand dst_op s, eval_operand value_op s) of
      (SOME dst,SOME value) => [(w2n dst,len)]
    | _ => []
End

Definition sized_source_write_range_def:
  sized_source_write_range s dst_op src_op size_op =
    case (eval_operand dst_op s, eval_operand src_op s,
          eval_operand size_op s) of
      (SOME dst,SOME src,SOME sz) => [(w2n dst,w2n sz)]
    | _ => []
End

(* DRET copies each dynamic return value to a distinct destination cursor;
   the cursor advances by the padded size, while the actual write length is
   the unpadded size used by pack_dret_dynamic. *)
Definition dret_source_write_ranges_def:
  dret_source_write_ranges (cursor:bytes32) [] = [] /\
  dret_source_write_ranges cursor ((src,sz)::rest) =
    (w2n cursor,w2n sz) ::
    dret_source_write_ranges
      (cursor + n2w (ceil32 (w2n sz))) rest
End

Definition source_memory_write_ranges_def:
  source_memory_write_ranges inst s =
    case inst.inst_opcode of
      MSTORE =>
        (case inst.inst_operands of
           [dst_op; value_op] => fixed_source_write_range s dst_op value_op 32
         | _ => [])
    | MSTORE8 =>
        (case inst.inst_operands of
           [dst_op; value_op] => fixed_source_write_range s dst_op value_op 1
         | _ => [])
    | ISTORE =>
        (case inst.inst_operands of
           [dst_op; value_op] => fixed_source_write_range s dst_op value_op 32
         | _ => [])
    | MCOPY =>
        (case inst.inst_operands of
           [dst_op; src_op; size_op] =>
             sized_source_write_range s dst_op src_op size_op
         | _ => [])
    | CALLDATACOPY =>
        (case inst.inst_operands of
           [dst_op; src_op; size_op] =>
             sized_source_write_range s dst_op src_op size_op
         | _ => [])
    | RETURNDATACOPY =>
        (case inst.inst_operands of
           [dst_op; src_op; size_op] =>
             sized_source_write_range s dst_op src_op size_op
         | _ => [])
    | DLOADBYTES =>
        (case inst.inst_operands of
           [dst_op; src_op; size_op] =>
             sized_source_write_range s dst_op src_op size_op
         | _ => [])
    | CODECOPY =>
        (case inst.inst_operands of
           [dst_op; src_op; size_op] =>
             sized_source_write_range s dst_op src_op size_op
         | _ => [])
    | EXTCODECOPY =>
        (case inst.inst_operands of
           [addr_op; dst_op; src_op; size_op] =>
             (case eval_operand addr_op s of
                SOME addr => sized_source_write_range s dst_op src_op size_op
              | NONE => [])
         | _ => [])
    | CALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; value_op; args_off_op; args_size_op;
            ret_off_op; ret_size_op] =>
             (case (eval_operand gas_op s, eval_operand addr_op s,
                    eval_operand value_op s, eval_operand args_off_op s,
                    eval_operand args_size_op s, eval_operand ret_off_op s,
                    eval_operand ret_size_op s) of
                (SOME gas,SOME addr,SOME value,SOME args_off,SOME args_size,
                 SOME ret_off,SOME ret_size) => [(w2n ret_off,w2n ret_size)]
              | _ => [])
         | _ => [])
    | STATICCALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; args_off_op; args_size_op;
            ret_off_op; ret_size_op] =>
             (case (eval_operand gas_op s, eval_operand addr_op s,
                    eval_operand args_off_op s, eval_operand args_size_op s,
                    eval_operand ret_off_op s, eval_operand ret_size_op s) of
                (SOME gas,SOME addr,SOME args_off,SOME args_size,
                 SOME ret_off,SOME ret_size) => [(w2n ret_off,w2n ret_size)]
              | _ => [])
         | _ => [])
    | DELEGATECALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; args_off_op; args_size_op;
            ret_off_op; ret_size_op] =>
             (case (eval_operand gas_op s, eval_operand addr_op s,
                    eval_operand args_off_op s, eval_operand args_size_op s,
                    eval_operand ret_off_op s, eval_operand ret_size_op s) of
                (SOME gas,SOME addr,SOME args_off,SOME args_size,
                 SOME ret_off,SOME ret_size) => [(w2n ret_off,w2n ret_size)]
              | _ => [])
         | _ => [])
    | DRET =>
        (case parse_dret_shape inst of
           NONE => []
         | SOME (ordinary,dynamic) =>
             (case eval_operands inst.inst_operands s of
                NONE => []
              | SOME vals =>
                  (case pair_dret_words
                    (TAKE (2 * dynamic) (DROP (1 + ordinary) vals)) of
                     NONE => []
                   | SOME pairs =>
                       dret_source_write_ranges s.vs_call_entry_fmp pairs)))
    | _ => []
End
(* Every nonempty source-write interval is disjoint from the compiler-owned
   half-open spill interval [sa_spill_base,sa_next_offset). *)
Definition source_memory_writes_disjoint_def:
  source_memory_writes_disjoint (alloc:spill_alloc) inst s <=>
    EVERY (\(off,len).
      len = 0 \/ off + len <= alloc.sa_spill_base \/
      alloc.sa_next_offset <= off)
      (source_memory_write_ranges inst s)
End

(* ===== Spill Safety Conditions ===== *)

(* A Venom step doesn't modify memory in the spill region.
   Checked post-hoc: spill region bytes unchanged from vs to vs'.
   Required per-instruction so plan_spill_rel is maintained.
   For Vyper-generated code, the memory allocator places all user
   allocations below fn_eom, so this holds. For arbitrary Venom
   programs, it must be assumed. *)
Definition step_mem_safe_def:
  step_mem_safe (alloc : spill_alloc) vs vs' ⇔
    ∀i. alloc.sa_spill_base ≤ i ∧ i < alloc.sa_next_offset ⇒
      read_byte i vs.vs_memory = read_byte i vs'.vs_memory
End

(* Simulation safety keeps post-hoc source preservation and intentional
   write/spill disjointness as independent obligations. *)
Definition inst_memory_safe_def:
  inst_memory_safe (alloc:spill_alloc) inst vs vs' <=>
    step_mem_safe alloc vs vs' /\
    source_memory_writes_disjoint alloc inst vs
End

Theorem source_memory_write_ranges_ISTORE_lit[simp]:
  source_memory_write_ranges
    (instruction id ISTORE [Lit off; Lit value] []) s = [(w2n off,32)]
Proof
  simp[source_memory_write_ranges_def, fixed_source_write_range_def,
       venomStateTheory.eval_operand_def]
QED

Theorem source_memory_write_ranges_ADD[simp]:
  source_memory_write_ranges
    (instruction id ADD operands outputs) s = []
Proof
  simp[source_memory_write_ranges_def]
QED

Theorem source_memory_write_ranges_MSTORE8_lit[simp]:
  source_memory_write_ranges
    (instruction id MSTORE8 [Lit off; Lit value] []) s = [(w2n off,1)]
Proof
  simp[source_memory_write_ranges_def, fixed_source_write_range_def,
       venomStateTheory.eval_operand_def]
QED

Theorem source_memory_write_ranges_MCOPY_lit[simp]:
  source_memory_write_ranges
    (instruction id MCOPY [Lit dst; Lit src; Lit sz] []) s =
    [(w2n dst,w2n sz)]
Proof
  simp[source_memory_write_ranges_def, sized_source_write_range_def,
       venomStateTheory.eval_operand_def]
QED

(* Memory is pre-expanded to cover the spill high-water mark.
   Ensures MEMTOP agrees between Venom and asm from the start.
   Established at context entry by emitting a memory-touching op
   up to the maximum sa_next_offset across all functions.
   spill_hwm is the maximum sa_next_offset reached during execution
   (known from codegen output, since spill allocation is deterministic). *)
Definition spill_mem_covered_def:
  spill_mem_covered spill_hwm (mem : byte list) ⇔
    spill_hwm ≤ LENGTH mem
End

(* Full Venom ↔ asm state relation.
   This is the LOOP INVARIANT for block-by-block simulation.
   Parameterized by plan_state which tracks stack layout.
   NOT used for terminal states — see venom_asm_terminal_rel.

   Memory model:
   - plan_spill_rel: active spill slots have correct values
   - memory_rel: memories agree outside [sa_spill_base, sa_next_offset)
   - step_mem_safe: Venom steps don't modify the spill region

   The spill region boundary (sa_spill_base) comes from the pipeline
   (concretize_mem_loc sets it). step_mem_safe is a precondition
   on the input program / initial state.

   NOTE: MEMTOP correspondence is excluded — asm memory may be longer
   than Venom memory due to spill slots. See memory_rel comment. *)
Definition venom_asm_rel_def:
  venom_asm_rel label_offsets ps vs as ⇔
    plan_stack_rel label_offsets vs ps.ps_stack as.as_stack ∧
    plan_spill_rel label_offsets vs ps.ps_spilled as.as_memory ∧
    memory_rel ps.ps_alloc vs.vs_memory as.as_memory ∧
    (* Shared mutable state *)
    as.as_accounts = vs.vs_accounts ∧
    as.as_transient = vs.vs_transient ∧
    as.as_returndata = vs.vs_returndata ∧
    as.as_logs = vs.vs_logs ∧
    (* Shared environment *)
    as.as_call_ctx = vs.vs_call_ctx ∧
    as.as_tx_ctx = vs.vs_tx_ctx ∧
    as.as_block_ctx = vs.vs_block_ctx ∧
    as.as_code = vs.vs_code ∧
    as.as_prev_hashes = vs.vs_prev_hashes
End

(* Terminal state: observable effects match at halt/revert.
   No plan_state, no stack layout, no memory details.
   Only what matters for the end-to-end theorem. *)
Definition venom_asm_terminal_rel_def:
  venom_asm_terminal_rel vs as ⇔
    as.as_accounts = vs.vs_accounts ∧
    as.as_transient = vs.vs_transient ∧
    as.as_returndata = vs.vs_returndata ∧
    as.as_logs = vs.vs_logs
End

(* venom_asm_rel implies venom_asm_terminal_rel (for proof use) *)
Theorem venom_asm_rel_terminal:
  ∀lo ps vs as.
    venom_asm_rel lo ps vs as ⇒
    venom_asm_terminal_rel vs as
Proof
  rw[venom_asm_rel_def, venom_asm_terminal_rel_def]
QED

(* ===== Function Entry ===== *)

(* Initial plan state with function parameters pre-loaded on ps_stack.
   At function entry, the asm stack has args (first param deepest,
   last param TOS). prepare_params_plan in generate_block_plan
   records these in ps_stack then pops dead params.
   This definition captures the stack state BEFORE dead-param cleanup. *)
Definition fn_init_ps_def:
  fn_init_ps fn fn_eom =
    let params = get_params (HD fn.fn_blocks).bb_instructions in
    (init_plan_state fn_eom) with
      ps_stack := MAP (λinst. Var (HD inst.inst_outputs)) params
End

(* ===== Asm State ↔ EVM Bytecode State ===== *)

(* Asm instruction index → byte offset in assembled bytecode *)
Definition asm_pc_to_offset_def:
  asm_pc_to_offset prog pc =
    SUM (MAP asm_inst_size (TAKE pc prog))
End

(* EVM context matches asm_state.
   Assumes single-frame execution (head of contexts list).
   Key differences from raw EVM:
     - PC: asm uses instruction index, EVM uses byte offset
     - Code/parsed: EVM needs bytecode and pre-parsed opname map
   Gas is NOT tracked — correctness theorems use OOG disjunction. *)
Definition asm_evm_rel_def:
  asm_evm_rel prog as es ⇔
    (case es.contexts of
       (ctxt, rb) :: _ =>
         (* Code and parsed map match assembled program *)
         ctxt.msgParams.code = assemble prog ∧
         ctxt.msgParams.parsed =
           parse_code 0 FEMPTY (assemble prog) ∧
         (* Stack, memory, PC, jumpDest *)
         ctxt.stack = as.as_stack ∧
         ctxt.memory = as.as_memory ∧
         ctxt.pc = asm_pc_to_offset prog as.as_pc ∧
         ctxt.jumpDest = NONE ∧
         (* Return data and logs *)
         ctxt.returnData = as.as_returndata ∧
         ctxt.logs = as.as_logs ∧
         (* Live accounts and transient storage (NOT per-frame checkpoint) *)
         es.rollback.accounts = as.as_accounts ∧
         es.rollback.tStorage = as.as_transient ∧
         (* Call context *)
         as.as_call_ctx.cc_caller = ctxt.msgParams.caller ∧
         as.as_call_ctx.cc_address = ctxt.msgParams.callee ∧
         as.as_call_ctx.cc_callvalue = n2w ctxt.msgParams.value ∧
         as.as_call_ctx.cc_calldata = ctxt.msgParams.data ∧
         as.as_call_ctx.cc_static = ctxt.msgParams.static ∧
         (* Tx context *)
         as.as_tx_ctx.tc_origin = es.txParams.origin ∧
         as.as_tx_ctx.tc_gasprice = n2w es.txParams.gasPrice ∧
         as.as_tx_ctx.tc_chainid = n2w es.txParams.chainId ∧
         as.as_tx_ctx.tc_blobhashes = es.txParams.blobHashes ∧
         (* Block context *)
         as.as_block_ctx.bc_coinbase = es.txParams.blockCoinBase ∧
         as.as_block_ctx.bc_timestamp = n2w es.txParams.blockTimeStamp ∧
         as.as_block_ctx.bc_number = n2w es.txParams.blockNumber ∧
         as.as_block_ctx.bc_prevrandao = es.txParams.prevRandao ∧
         as.as_block_ctx.bc_gaslimit = n2w es.txParams.blockGasLimit ∧
         as.as_block_ctx.bc_basefee = n2w es.txParams.baseFeePerGas ∧
         as.as_block_ctx.bc_blobbasefee = n2w es.txParams.baseFeePerBlobGas ∧
         (* Blockhash: bc_blockhash matches EVM prevHashes-based computation *)
         as.as_prev_hashes = es.txParams.prevHashes ∧
         (* Blockhash: asm formula uses asm-only fields *)
         es.txParams.blockNumber < dimword (:256) ∧
         (∀n. as.as_block_ctx.bc_blockhash n =
           let bn = w2n as.as_block_ctx.bc_number in
           let idx = bn - n - 1 in
           if (n < bn ∧ bn − 256 ≤ n) ∧
              idx < LENGTH as.as_prev_hashes
           then EL idx as.as_prev_hashes
           else 0w) ∧
         (* Code *)
         as.as_code = assemble prog ∧
         (* OutputTo: single-context execution requires non-Create output *)
         (∀a. ctxt.msgParams.outputTo ≠ Code a)
     | [] => F)
End

(* Gas model: Venom IR does not track gas. EVM does.
   Correctness theorems use a disjunctive form:
     "either results correspond, or EVM ran out of gas (OutOfGas)."
   No gas precondition is needed — the OOG disjunct absorbs it. *)

(* ===== Result Correspondence ===== *)

(* asm_result corresponds to Venom exec_result.
   Uses terminal_rel: at halt/revert, only observable effects matter. *)
Definition asm_venom_result_rel_def:
  asm_venom_result_rel ar vr ⇔
    case (ar, vr) of
      (AsmHalt as, Halt vs) =>
        venom_asm_terminal_rel vs as
    | (AsmRevert as, Abort Revert_abort vs) =>
        venom_asm_terminal_rel vs as
    | (AsmFault as, Abort ExHalt_abort vs) =>
        venom_asm_terminal_rel vs as
    | _ => F
End

(* ===== Stack Boundedness ===== *)

(* The generated asm program never exceeds the EVM stack limit (1024).
   Stated operationally: for any reachable AsmOK state, the stack has
   fewer than stack_limit elements.

   NOTE: If this fails, the correct fix is to spill excess stack values
   to memory (extending the spiller). Currently the compiler has no
   stack-depth-aware spilling — it only spills for DUP/SWAP range (16).
   Adding depth-aware spilling is an algorithmic change to the codegen. *)
Definition asm_stack_bounded_def:
  asm_stack_bounded lo otp prog init_depth ⇔
    ∀n as as'.
      LENGTH as.as_stack = init_depth ∧
      asm_steps lo otp prog n as = AsmOK as' ⇒
      LENGTH as'.as_stack < vfmConstants$stack_limit
End

(* ===== Asm ↔ EVM Result Correspondence ===== *)

(* asm_result corresponds to EVM execution result.
   run returns SOME (INR result, es) on termination:
     INR NONE          = clean halt (STOP/RETURN)
     INR (SOME Reverted) = revert
     INR (SOME exc)    = exceptional halt (OOG, invalid, etc.)
   INL never appears in run output (OWHILE exits on INR). *)
Definition asm_evm_result_rel_def:
  asm_evm_result_rel prog ar er ⇔
    case (ar, er) of
      (AsmHalt as, SOME (INR NONE, es)) =>
        asm_evm_rel prog as es
    | (AsmRevert as, SOME (INR (SOME Reverted), es)) =>
        asm_evm_rel prog as es
    | (AsmFault as, SOME (INR (SOME exc), es)) =>
        exc ≠ Reverted ∧ asm_evm_rel prog as es
    | _ => F
End
