(*
 * Venom Semantics
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * This theory defines the operational semantics for Venom IR execution.
 * It includes the effects system and instruction stepping.
 *)

Theory venomExecSemantics
Ancestors
  venomState venomInst venomLayout dretShapeDefs keccak vfmExecution

(* --------------------------------------------------------------------------
   Arithmetic/Logic Operations (using bytes32 = 256 word)
   -------------------------------------------------------------------------- *)

(* Division with zero check *)
Definition safe_div_def:
  safe_div (x:bytes32) (y:bytes32) : bytes32 =
    if y = 0w then 0w else x // y
End

Definition safe_mod_def:
  safe_mod (x:bytes32) (y:bytes32) : bytes32 =
    if y = 0w then 0w else word_mod x y
End

(* Signed division *)
Definition safe_sdiv_def:
  safe_sdiv (x:bytes32) (y:bytes32) : bytes32 =
    if y = 0w then 0w else x / y
End

Definition safe_smod_def:
  safe_smod (x:bytes32) (y:bytes32) : bytes32 =
    if y = 0w then 0w else word_rem x y
End

(* Modular arithmetic *)
Definition addmod_def:
  addmod (a:bytes32) (b:bytes32) (n:bytes32) : bytes32 =
    if n = 0w then 0w else n2w ((w2n a + w2n b) MOD w2n n)
End

Definition mulmod_def:
  mulmod (a:bytes32) (b:bytes32) (n:bytes32) : bytes32 =
    if n = 0w then 0w else n2w ((w2n a * w2n b) MOD w2n n)
End

(* Sign extension: extend byte n of w to 256 bits.
   If n >= 31, w is already fully represented.
   Otherwise, extend sign bit of byte n across higher bytes.
   Matches EVM SIGNEXTEND semantics. *)
(* EVM BYTE: extract n-th byte (big-endian) from value.
   byte(n, x) = if n >= 32 then 0 else (x >> ((31-n)*8)) & 0xFF *)
Definition evm_byte_def:
  evm_byte (n : bytes32) (x : bytes32) : bytes32 =
    if w2n n >= 32 then 0w
    else word_and (word_lsr x ((31 - w2n n) * 8))
                  (n2w 255)
End

Definition sign_extend_def:
  sign_extend (n:bytes32) (w:bytes32) : bytes32 =
    if w2n n > 30 then w
    else
      let byte_pos = w2n n in
      let bit_pos = byte_pos * 8 + 7 in
      let mask = (1w:bytes32) << (bit_pos + 1) - 1w in
      let sign_bit = (w >>> bit_pos) && 1w in
      if sign_bit = 1w then w || ¬mask
      else w && mask
End

(* Memory copy: copy sz bytes from src to dst in memory.
   Snapshots source before write (handles overlapping regions correctly).
   Pure equivalent of verifereum's monadic copy_to_memory with NONE source. *)
Definition mcopy_def:
  mcopy (dst:num) (src:num) (sz:num) (s:venom_state) =
    let data = TAKE sz (DROP src s.vs_memory ++ REPLICATE sz 0w) in
    write_memory_with_expansion dst data s
End

(* Immutable stores lower to MSTORE.  The finite map is retained only as
   source-level bookkeeping; executable behavior is carried by vs_memory. *)
Definition istore_def:
  istore offset (value:bytes32) s =
    (mstore offset value s with
       vs_immutables := s.vs_immutables |+ (offset, value))
End

Theorem istore_memory[simp]:
  (istore offset value s).vs_memory = (mstore offset value s).vs_memory
Proof
  simp[istore_def]
QED

Theorem istore_shared_fields[simp]:
  (istore offset value s).vs_accounts = s.vs_accounts /\
  (istore offset value s).vs_transient = s.vs_transient /\
  (istore offset value s).vs_returndata = s.vs_returndata /\
  (istore offset value s).vs_logs = s.vs_logs /\
  (istore offset value s).vs_call_ctx = s.vs_call_ctx /\
  (istore offset value s).vs_tx_ctx = s.vs_tx_ctx /\
  (istore offset value s).vs_block_ctx = s.vs_block_ctx /\
  (istore offset value s).vs_code = s.vs_code /\
  (istore offset value s).vs_prev_hashes = s.vs_prev_hashes
Proof
  simp[istore_def, mstore_def]
QED


Definition pair_dret_words_def:
  pair_dret_words [] = SOME [] /\
  pair_dret_words (src::sz::rest) =
    OPTION_MAP (CONS (src,sz)) (pair_dret_words rest) /\
  pair_dret_words _ = NONE
End
(* Pack dynamic return values left-to-right from an explicit destination cursor. *)
Definition pack_dret_dynamic_def:
  pack_dret_dynamic (cursor:bytes32) [] (s:venom_state) = ([], cursor, s) /\
  pack_dret_dynamic cursor ((src,sz)::rest) s =
    let s1 = mcopy (w2n cursor) (w2n src) (w2n sz) s in
    let next = cursor + n2w (ceil32 (w2n sz)) in
    let (ptrs, final_cursor, s2) = pack_dret_dynamic next rest s1 in
      (cursor::ptrs, final_cursor, s2)
End

Theorem pack_dret_dynamic_nil[simp]:
  pack_dret_dynamic cursor [] s = ([], cursor, s)
Proof
  simp[pack_dret_dynamic_def]
QED

Theorem mcopy_preserves_frame_metadata[simp]:
  (mcopy dst src sz s).vs_fmp = s.vs_fmp /\
  (mcopy dst src sz s).vs_call_entry_fmp = s.vs_call_entry_fmp /\
  (mcopy dst src sz s).vs_return_pc_token = s.vs_return_pc_token
Proof
  simp[mcopy_def, write_memory_with_expansion_def]
QED

(* Boolean to word *)
Definition bool_to_word_def:
  bool_to_word T = (1w:bytes32) /\
  bool_to_word F = (0w:bytes32)
End

(* --------------------------------------------------------------------------
   Execution Result Type
   -------------------------------------------------------------------------- *)

(* Abort reason: distinguishes clean revert from exceptional halt.
   Matters for EVM lowering (gas refund, returndata availability). *)
Datatype:
  abort_type =
    | Revert_abort        (* REVERT: refunds remaining gas, has returndata *)
    | ExHalt_abort        (* INVALID/out-of-gas: consumes all gas, no returndata *)
End

Datatype:
  internal_return = <|
    iret_values : bytes32 list;
    iret_adopt_fmp : bytes32 option
  |>
End

Datatype:
  exec_result =
    | OK venom_state              (* Normal continuation *)
    | Halt venom_state            (* Normal termination (STOP/RETURN) *)
    | Abort abort_type venom_state  (* Aborted execution *)
    | IntRet internal_return venom_state  (* Internal function return *)
    | Error string                (* Execution error *)
End

(* --------------------------------------------------------------------------
   PHI Node Resolution

   PHI nodes select a value based on which predecessor block we came from.
   Format: %out = phi @pred1, %val1, @pred2, %val2, ...
   -------------------------------------------------------------------------- *)

(* Find the value for a PHI based on predecessor block *)
Definition resolve_phi_def:
  resolve_phi prev_bb [] = NONE /\
  resolve_phi prev_bb [_] = NONE /\
  resolve_phi prev_bb (Label lbl :: val_op :: rest) =
    (if lbl = prev_bb then SOME val_op else resolve_phi prev_bb rest) /\
  resolve_phi prev_bb (_ :: _ :: rest) = resolve_phi prev_bb rest
End

(* Extract label names from operand list (for DJMP target list) *)
Definition extract_labels_def:
  extract_labels [] = SOME [] /\
  extract_labels (Label lbl :: rest) =
    (case extract_labels rest of
       SOME lbls => SOME (lbl :: lbls)
     | NONE => NONE) /\
  extract_labels _ = NONE
End

(* --------------------------------------------------------------------------
   Instruction Semantics
   -------------------------------------------------------------------------- *)

(* --------------------------------------------------------------------------
   Instruction Execution Helpers

   Categorized by operand count and state dependency:
     exec_pure{1,2,3} : pure computation (f doesn't depend on state)
     exec_read{0,1}   : state-reading (f depends on state)
     exec_write2      : state-mutating (2 operands, no output)
   -------------------------------------------------------------------------- *)

(* Pure 1-operand: eval operand, apply pure f, update output *)
Definition exec_pure1_def:
  exec_pure1 f inst s =
    case inst.inst_operands of
      [op1] =>
        (case eval_operand op1 s of
          SOME v =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v) s)
            | _ => Error "pure1 requires single output")
        | NONE => Error "undefined operand")
    | _ => Error "pure1 requires 1 operand"
End

(* Pure 2-operand: eval both operands, apply pure f, update output *)
Definition exec_pure2_def:
  exec_pure2 f inst s =
    case inst.inst_operands of
      [op1; op2] =>
        (case (eval_operand op1 s, eval_operand op2 s) of
          (SOME v1, SOME v2) =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v1 v2) s)
            | _ => Error "pure2 requires single output")
        | _ => Error "undefined operand")
    | _ => Error "pure2 requires 2 operands"
End

(* Pure 3-operand: eval all operands, apply pure f, update output *)
Definition exec_pure3_def:
  exec_pure3 f inst s =
    case inst.inst_operands of
      [op1; op2; op3] =>
        (case (eval_operand op1 s, eval_operand op2 s, eval_operand op3 s) of
          (SOME v1, SOME v2, SOME v3) =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v1 v2 v3) s)
            | _ => Error "pure3 requires single output")
        | _ => Error "undefined operand")
    | _ => Error "pure3 requires 3 operands"
End

(* State-read 0-operand: read value from state, update output *)
Definition exec_read0_def:
  exec_read0 f inst s =
    case inst.inst_outputs of
      [out] => OK (update_var out (f s) s)
    | _ => Error "read0 requires single output"
End

(* State-read 1-operand: eval operand, read from state, update output *)
Definition exec_read1_def:
  exec_read1 f inst s =
    case inst.inst_operands of
      [op1] =>
        (case eval_operand op1 s of
          SOME v =>
            (case inst.inst_outputs of
              [out] => OK (update_var out (f v s) s)
            | _ => Error "read1 requires single output")
        | NONE => Error "undefined operand")
    | _ => Error "read1 requires 1 operand"
End

(* State-write 2-operand: eval both operands, mutate state, no output *)
Definition exec_write2_def:
  exec_write2 f inst s =
    case inst.inst_operands of
      [op1; op2] =>
        (case (eval_operand op1 s, eval_operand op2 s) of
          (SOME v1, SOME v2) => OK (f v1 v2 s)
        | _ => Error "undefined operand")
    | _ => Error "write2 requires 2 operands"
End

(* --------------------------------------------------------------------------
   External Call Helpers (using verifereum EVM semantics)

   External calls build an EVM execution_state, run the callee's bytecode
   via vfmExecution$run, and extract the result. This matches the approach
   used in the Vyper source-level semantics (run_ext_call).

   CALL/STATICCALL/DELEGATECALL: make_venom_call_state + extract_venom_call_result
   CREATE/CREATE2: make_venom_create_state + extract_venom_create_result
   -------------------------------------------------------------------------- *)

(* Build transaction_parameters from venom state for EVM sub-execution.
   Mirrors vyper_to_tx_params in vyperInterpreterScript.sml.
   prevHashes comes from vs_prev_hashes; authRefund defaults to 0. *)
Definition venom_to_tx_params_def:
  venom_to_tx_params s : transaction_parameters =
    <| origin := s.vs_tx_ctx.tc_origin;
       gasPrice := w2n s.vs_tx_ctx.tc_gasprice;
       baseFeePerGas := w2n s.vs_block_ctx.bc_basefee;
       baseFeePerBlobGas := w2n s.vs_block_ctx.bc_blobbasefee;
       blockNumber := w2n s.vs_block_ctx.bc_number;
       blockTimeStamp := w2n s.vs_block_ctx.bc_timestamp;
       blockCoinBase := s.vs_block_ctx.bc_coinbase;
       blockGasLimit := w2n s.vs_block_ctx.bc_gaslimit;
       prevRandao := s.vs_block_ctx.bc_prevrandao;
       prevHashes := s.vs_prev_hashes;
       blobHashes := s.vs_tx_ctx.tc_blobhashes;
       chainId := w2n s.vs_tx_ctx.tc_chainid;
       authRefund := 0 |>
End

(* Shared: build a sub-context transaction record *)
Definition make_sub_tx_def:
  make_sub_tx (caller:address) (target:address) value gas calldata =
    <| from := caller; to := SOME target;
       data := calldata; nonce := 0; value := value;
       gasLimit := gas; gasPrice := 0;
       accessList := [];
       blobVersionedHashes := [];
       maxFeePerBlobGas := NONE;
       maxFeePerGas := NONE;
       authorizationList := [] |>
End

(* Shared: build initial rollback and accesses.
   ts = caller's transient storage, wrapped per-address so the EVM
   sub-execution can TLOAD/TSTORE correctly. *)
Definition make_rollback_def:
  make_rollback accounts (ts : transient_storage)
                (caller:address) (target:address) =
    let accesses = <| addresses := fINSERT caller (fINSERT target fEMPTY);
                      storageKeys := fEMPTY |> in
    <| accounts := accounts;
       tStorage := ts;
       accesses := accesses;
       toDelete := [] |>
End



(* Build an EVM execution_state for CALL/STATICCALL.
   vs_accounts already has the current contract's latest SSTORE writes
   (sstore writes through vs_accounts directly). *)
Definition make_venom_call_state_def:
  make_venom_call_state s (target:address) gas value calldata code is_static =
    let caller = s.vs_call_ctx.cc_address in
    let tx = make_sub_tx caller target value gas calldata in
    let ctxt = initial_context target code is_static
                 empty_return_destination tx in
    let accounts = transfer_value caller target value s.vs_accounts in
    let ts = s.vs_transient in
    let rb = make_rollback accounts ts caller target in
    <| contexts := [(ctxt, rb)];
       txParams := venom_to_tx_params s;
       rollback := rb;
       msdomain := Collect empty_domain |>
End

(* Build an EVM execution_state for DELEGATECALL.
   Key differences from CALL/STATICCALL:
   - Executes target's code in caller's context (ADDRESS returns caller)
   - msg.sender is caller's original caller (not caller itself)
   - msg.value is inherited from current call (not re-sent)
   - No value transfer occurs *)
Definition make_venom_delegatecall_state_def:
  make_venom_delegatecall_state s (target:address) gas calldata code is_static =
    let caller = s.vs_call_ctx.cc_address in
    let original_caller = s.vs_call_ctx.cc_caller in
    let call_value = w2n s.vs_call_ctx.cc_callvalue in
    let tx = make_sub_tx original_caller caller call_value gas calldata in
    let ctxt = initial_context caller code is_static
                 empty_return_destination tx in
    let ts = s.vs_transient in
    let rb = make_rollback s.vs_accounts ts caller target in
    <| contexts := [(ctxt, rb)];
       txParams := venom_to_tx_params s;
       rollback := rb;
       msdomain := Collect empty_domain |>
End

(* Build an EVM execution_state for CREATE/CREATE2.
   Mirrors verifereum's proceed_create: transfers value, uses Code address
   as return destination so handle_create deploys the init code's output. *)
Definition make_venom_create_state_def:
  make_venom_create_state s (new_address:address) gas value init_code =
    let caller = s.vs_call_ctx.cc_address in
    let tx = make_sub_tx caller new_address value gas [] in
    let ctxt = initial_context new_address init_code F
                 (Code new_address) tx in
    let accounts = transfer_value caller new_address value s.vs_accounts in
    let ts = s.vs_transient in
    let rb = make_rollback accounts ts caller new_address in
    <| contexts := [(ctxt, rb)];
       txParams := venom_to_tx_params s;
       rollback := rb;
       msdomain := Collect empty_domain |>
End

(* Extract result from verifereum execution into Venom state update.
   output_val: function mapping success to output word
     (CALL: \_ => 1w, CREATE: \addr => w2w addr)

   Contract storage lives in vs_accounts (the account's storage field).
   On success, vs_accounts gets the post-execution accounts from
   rollback.accounts (includes reentrancy/DELEGATECALL storage changes).
   On revert, vs_accounts is restored to s.vs_accounts (pre-call).

   Transient storage (EIP-1153) is tracked separately in rollback.tStorage.
   On success we extract the caller's transient storage; on revert we
   keep the pre-call value. *)
Definition extract_venom_result_def:
  extract_venom_result s output_val retOff retSize run_result =
    case run_result of
    | NONE => NONE
    | SOME (result, final_state) =>
      (case final_state.contexts of
       | [(ctxt, _)] =>
           let returndata = ctxt.returnData in
           let (success, accounts) =
             (case result of
              | INR NONE => (T, final_state.rollback.accounts)
              | INR (SOME Reverted) => (F, s.vs_accounts)
              | _ => (F, s.vs_accounts)) in
           let new_logs =
             (case result of
              | INR NONE => ctxt.logs
              | _ => []) in
           let output : bytes32 =
             if success then output_val else 0w in
           let new_transient =
             if success then final_state.rollback.tStorage
             else s.vs_transient in
           let s' = s with <|
             vs_returndata := returndata;
             vs_accounts := accounts;
             vs_logs := s.vs_logs ++ new_logs;
             vs_memory := (write_memory_with_expansion retOff
                             (TAKE retSize returndata) s).vs_memory;
             vs_transient := new_transient
           |> in
           SOME (output, s')
       | _ => NONE)
End

(* Execute CALL/STATICCALL via verifereum EVM semantics.
   CALL: operands = [gas; addr; value; argsOff; argsSize; retOff; retSize]
   STATICCALL: operands = [gas; addr; argsOff; argsSize; retOff; retSize]
*)
Definition exec_ext_call_def:
  exec_ext_call inst s gas addr_w value argsOff argsSize retOff retSize is_static =
    let calldata = read_memory (w2n argsOff) (w2n argsSize) s in
    let target : address = w2w addr_w in
    let code = (lookup_account target s.vs_accounts).code in
    let evm_s = make_venom_call_state s target (w2n gas) (w2n value)
                  calldata code is_static in
    case extract_venom_result s 1w (w2n retOff) (w2n retSize) (run evm_s) of
    | SOME (output, s') =>
        (case inst.inst_outputs of
           [out] => OK (update_var out output s')
         | _ => Error "ext_call requires single output")
    | NONE => Error "ext_call: non-terminating or invalid state"
End

(* Execute DELEGATECALL via verifereum EVM semantics.
   Runs target's code in caller's own context (storage, address, balance).
   msg.sender = caller's original caller; msg.value = inherited.
   Operands: [gas; addr; argsOff; argsSize; retOff; retSize] *)
Definition exec_delegatecall_def:
  exec_delegatecall inst s gas addr_w argsOff argsSize retOff retSize =
    let calldata = read_memory (w2n argsOff) (w2n argsSize) s in
    let target : address = w2w addr_w in
    let code = (lookup_account target s.vs_accounts).code in
    let evm_s = make_venom_delegatecall_state s target (w2n gas)
                  calldata code s.vs_call_ctx.cc_static in
    case extract_venom_result s 1w (w2n retOff) (w2n retSize) (run evm_s) of
    | SOME (output, s') =>
        (case inst.inst_outputs of
           [out] => OK (update_var out output s')
         | _ => Error "delegatecall requires single output")
    | NONE => Error "delegatecall: non-terminating or invalid state"
End

(* Execute CREATE/CREATE2 via verifereum EVM semantics.
   CREATE: salt_opt = NONE, address from sender + nonce
   CREATE2: salt_opt = SOME salt, address from sender + salt + code hash
*)
Definition exec_create_def:
  exec_create inst s value offset sz salt_opt =
    let init_code = read_memory (w2n offset) (w2n sz) s in
    let sender = s.vs_call_ctx.cc_address in
    let sender_acct = lookup_account sender s.vs_accounts in
    let new_address =
      (case salt_opt of
         NONE => address_for_create sender sender_acct.nonce
       | SOME salt => address_for_create2 sender salt init_code) in
    let gas = s.vs_call_ctx.cc_gas - s.vs_call_ctx.cc_gas DIV 64 in
    let evm_s = make_venom_create_state s new_address gas (w2n value)
                  init_code in
    case extract_venom_result s (w2w new_address) 0 0 (run evm_s) of
    | SOME (output, s') =>
        (case inst.inst_outputs of
           [out] => OK (update_var out output s')
         | _ => Error "create requires single output")
    | NONE => Error "create: non-terminating or invalid state"
End

(* Bump-allocate: record region in vs_allocas without touching vs_memory.
   Memory is extended lazily by mstore when the region is actually written.
   vs_allocas is per-frame (keyed by inst_id, unique within a function).
   vs_alloca_next is global (bump pointer across all call frames).
   Idempotent: if inst_id already allocated, return existing offset. *)
Definition exec_alloca_def:
  exec_alloca inst s alloc_size =
    case inst.inst_outputs of
      [out] =>
        (case FLOOKUP s.vs_allocas inst.inst_id of
          SOME (offset, sz) =>
            (* Already allocated — return existing base address *)
            OK (update_var out (n2w offset) s)
        | NONE =>
            let offset = s.vs_alloca_next in
            let sz = w2n alloc_size in
            let s' = s with <|
              vs_allocas := s.vs_allocas |+ (inst.inst_id, (offset, sz));
              vs_alloca_next := offset + sz
            |> in
            OK (update_var out (n2w offset) s'))
    | _ => Error "alloca requires single output"
End

(* Step a single instruction.
   OPERAND CONVENTION: All operands are in semantic (EVM documentation) order.
   E.g., SUB [a; b] = a - b, MSTORE [offset; value], CALL [gas; addr; ...].
   The Venom IR internally reverses EVM operands via _emit_evm (stack order);
   our model uses semantic order for readability and proof clarity. *)
Definition step_inst_base_def:
  step_inst_base inst s =
    case inst.inst_opcode of
    (* Arithmetic *)
    | ADD => exec_pure2 word_add inst s
    | SUB => exec_pure2 word_sub inst s
    | MUL => exec_pure2 word_mul inst s
    | Div => exec_pure2 safe_div inst s
    | Mod => exec_pure2 safe_mod inst s
    | SDIV => exec_pure2 safe_sdiv inst s
    | SMOD => exec_pure2 safe_smod inst s
    | Exp => exec_pure2 word_exp inst s
    | ADDMOD => exec_pure3 addmod inst s
    | MULMOD => exec_pure3 mulmod inst s

    (* Comparison *)
    | EQ => exec_pure2 (\x y. bool_to_word (x = y)) inst s
    | LT => exec_pure2 (\x y. bool_to_word (w2n x < w2n y)) inst s
    | GT => exec_pure2 (\x y. bool_to_word (w2n x > w2n y)) inst s
    | SLT => exec_pure2 (\x y. bool_to_word (word_lt x y)) inst s
    | SGT => exec_pure2 (\x y. bool_to_word (word_gt x y)) inst s
    | ISZERO => exec_pure1 (\x. bool_to_word (x = 0w)) inst s

    (* Bitwise *)
    | AND => exec_pure2 word_and inst s
    | OR => exec_pure2 word_or inst s
    | XOR => exec_pure2 word_xor inst s
    | NOT => exec_pure1 word_1comp inst s
    | SHL => exec_pure2 (\n w. word_lsl w (w2n n)) inst s
    | SHR => exec_pure2 (\n w. word_lsr w (w2n n)) inst s
    | SAR => exec_pure2 (\n w. word_asr w (w2n n)) inst s
    | SIGNEXTEND => exec_pure2 sign_extend inst s
    | BYTE => exec_pure2 evm_byte inst s

    (* Memory
       Convention: all operands in semantic (EVM doc) order.
       MSTORE(offset, value), MCOPY(dst, src, size), etc.
       The Venom IR internally reverses EVM args via _emit_evm;
       our model uses semantic order for readability. *)
    | MLOAD => exec_read1 (\addr s. mload (w2n addr) s) inst s
    | MSTORE => exec_write2 (\addr val s. mstore (w2n addr) val s) inst s
    | MSTORE8 => exec_write2 (\addr val s. mstore8 (w2n addr) val s) inst s
    | MCOPY =>
        (case inst.inst_operands of
          [op_dst; op_src; op_size] =>
            (case (eval_operand op_dst s, eval_operand op_src s,
                   eval_operand op_size s) of
              (SOME dst, SOME src, SOME sz) =>
                OK (mcopy (w2n dst) (w2n src) (w2n sz) s)
            | _ => Error "undefined operand")
        | _ => Error "mcopy requires 3 operands")

    (* Storage *)
    | SLOAD => exec_read1 (\key s. sload key s) inst s
    | SSTORE => exec_write2 (\key val s. sstore key val s) inst s

    (* Transient storage *)
    | TLOAD => exec_read1 (\key s. tload key s) inst s
    | TSTORE => exec_write2 (\key val s. tstore key val s) inst s

    (* Control flow - JMP *)
    | JMP =>
        (case inst.inst_operands of
          [Label lbl] => OK (jump_to lbl s)
        | _ => Error "jmp requires label operand")

    (* Control flow - JNZ (conditional) *)
    | JNZ =>
        (case inst.inst_operands of
          [cond_op; Label if_nonzero; Label if_zero] =>
            (case eval_operand cond_op s of
              SOME cond =>
                if cond <> 0w then OK (jump_to if_nonzero s)
                else OK (jump_to if_zero s)
            | NONE => Error "undefined condition")
        | _ => Error "jnz requires cond and 2 labels")

    (* Control flow - DJMP (dynamic jump / jump table) *)
    | DJMP =>
        (case inst.inst_operands of
          selector_op :: label_ops =>
            (case (eval_operand selector_op s, extract_labels label_ops) of
              (SOME idx, SOME labels) =>
                let i = w2n idx in
                if i < LENGTH labels then
                  OK (jump_to (EL i labels) s)
                else Error "djmp: index out of range"
            | _ => Error "djmp: undefined operand or invalid labels")
        | _ => Error "djmp requires selector and labels")

    (* Raw free-memory-pointer operations *)
    | GETFMP =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([], [out]) => OK (update_var out s.vs_fmp s)
        | _ => Error "getfmp requires no operands and one output")

    | SETFMP =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([op], []) =>
            (case eval_operand op s of
              SOME value => OK (s with vs_fmp := value)
            | NONE => Error "setfmp: undefined operand")
        | _ => Error "setfmp requires one operand and no outputs")

    | DALLOCA =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([size_op], [out]) =>
            (case eval_operand size_op s of
              SOME sz =>
                OK (update_var out s.vs_fmp
                  (s with vs_fmp :=
                    s.vs_fmp + n2w (ceil32 (w2n sz))))
            | NONE => Error "dalloca: undefined operand")
        | _ => Error "dalloca requires one operand and one output")

    | INITIAL_FMP =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([], [out]) => OK (update_var out s.vs_initial_fmp s)
        | _ => Error "initial_fmp requires no operands and one output")

    (* Lowered explicit-base bump arithmetic; deliberately FMP-independent. *)
    | BUMP =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([base_op; size_op], [ptr_out; next_out]) =>
            (case (eval_operand base_op s, eval_operand size_op s) of
              (SOME base_val, SOME sz) =>
                OK (update_var next_out
                  (word_add base_val (n2w (ceil32 (w2n sz)) : bytes32))
                  (update_var ptr_out base_val s))
            | _ => Error "bump: undefined operand")
        | _ => Error "bump requires two operands and two outputs")

    (* Hidden invoke parameters. *)
    | FMP_PARAM =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([Lit idx], [out]) =>
            let i = w2n idx in
            if i < LENGTH s.vs_params then
              OK (update_var out (EL i s.vs_params) s)
            else Error "fmp_param: index out of range"
        | _ => Error "fmp_param requires literal index and one output")

    | RETPC_PARAM =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([Lit idx], [out]) =>
            OK (update_var out s.vs_return_pc_token s)
        | _ => Error "retpc_param requires literal index and one output")

    (* Function parameter access *)
    | PARAM =>
        (case inst.inst_operands of
          [Lit idx] =>
            let i = w2n idx in
            if i < LENGTH s.vs_params then
              (case inst.inst_outputs of
                [out] => OK (update_var out (EL i s.vs_params) s)
              | _ => Error "param requires single output")
            else Error "param: index out of range"
        | _ => Error "param requires literal index")

    (* Return from internal function.  The final operand is the return-PC token. *)
    | RET =>
        (case eval_operands inst.inst_operands s of
          SOME [] => Error "ret requires a return pc"
        | SOME ret_vals =>
            IntRet <| iret_values := FRONT ret_vals;
                      iret_adopt_fmp := NONE |> s
        | NONE => Error "ret: undefined return value")

    | RETFMP =>
        (case eval_operands inst.inst_operands s of
          SOME [] => Error "retfmp requires a return pc"
        | SOME ret_vals =>
            IntRet <| iret_values := FRONT ret_vals;
                      iret_adopt_fmp := SOME s.vs_fmp |> s
        | NONE => Error "retfmp: undefined return value")

    | DRET =>
        if inst.inst_outputs <> [] then Error "dret requires no outputs"
        else
          (case parse_dret_shape inst of
            NONE => Error "dret: malformed operand envelope"
          | SOME (ordinary,dynamic) =>
              case eval_operands inst.inst_operands s of
                NONE => Error "dret: undefined operand"
              | SOME vals =>
                  case pair_dret_words
                    (TAKE (2 * dynamic) (DROP (1 + ordinary) vals)) of
                    NONE => Error "dret: malformed dynamic operands"
                  | SOME pairs =>
                      let ordinary_vals = TAKE ordinary (DROP 1 vals) in
                      let (ptrs,final_cursor,s') =
                        pack_dret_dynamic s.vs_call_entry_fmp pairs s in
                      let s'' = s' with vs_fmp := final_cursor in
                        IntRet
                          <| iret_values := ordinary_vals ++ ptrs;
                             iret_adopt_fmp := SOME final_cursor |> s'')

    (* Termination *)
    | STOP => Halt (halt_state s)

    | RETURN =>
        (case inst.inst_operands of
          [off_op; sz_op] =>
            (case (eval_operand off_op s, eval_operand sz_op s) of
              (SOME off, SOME sz) =>
                let rd = TAKE (w2n sz)
                  (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w) in
                Halt (halt_state (set_returndata rd s))
            | _ => Error "return: undefined operand")
        | _ => Error "return requires 2 operands")

    | REVERT =>
        (case inst.inst_operands of
          [off_op; sz_op] =>
            (case (eval_operand off_op s, eval_operand sz_op s) of
              (SOME off, SOME sz) =>
                let rd = TAKE (w2n sz)
                  (DROP (w2n off) s.vs_memory ++ REPLICATE (w2n sz) 0w) in
                Abort Revert_abort (revert_state (set_returndata rd s))
            | _ => Error "revert: undefined operand")
        | _ => Error "revert requires 2 operands")

    | SINK => Halt (halt_state s)

    (* Assertions — on failure, clear returndata (matches revert("") / invalid) *)
    | ASSERT =>
        (case inst.inst_operands of
          [cond_op] =>
            (case eval_operand cond_op s of
              SOME cond =>
                if cond = 0w then
                  Abort Revert_abort (revert_state (set_returndata [] s))
                else OK s
            | NONE => Error "undefined operand")
        | _ => Error "assert requires 1 operand")

    | ASSERT_UNREACHABLE =>
        (case inst.inst_operands of
          [cond_op] =>
            (case eval_operand cond_op s of
              SOME cond =>
                if cond = 0w then
                  Abort ExHalt_abort (halt_state (set_returndata [] s))
                else OK s
            | NONE => Error "undefined operand")
        | _ => Error "assert_unreachable requires 1 operand")

    (* SSA - PHI node.
       PHIs are evaluated in parallel by eval_phis at block entry.
       Reaching a PHI through normal sequential execution means the block
       has a non-prefix PHI and is malformed; fail loudly. *)
    | PHI => Error "phi outside prefix"

    (* SSA - ASSIGN *)
    | ASSIGN =>
        (case (inst.inst_operands, inst.inst_outputs) of
          ([op1], [out]) =>
            (case eval_operand op1 s of
              SOME v => OK (update_var out v s)
            | NONE => Error "undefined operand")
        | _ => Error "assign requires 1 operand and single output")

    (* NOP *)
    | NOP => OK s

    (* Environment - Call context *)
    | CALLER => exec_read0 (\s. w2w s.vs_call_ctx.cc_caller) inst s
    | ADDRESS => exec_read0 (\s. w2w s.vs_call_ctx.cc_address) inst s
    | CALLVALUE => exec_read0 (\s. s.vs_call_ctx.cc_callvalue) inst s
    | GAS => exec_read0 (\s. n2w s.vs_call_ctx.cc_gas) inst s

    (* Environment - Transaction context *)
    | ORIGIN => exec_read0 (\s. w2w s.vs_tx_ctx.tc_origin) inst s
    | GASPRICE => exec_read0 (\s. s.vs_tx_ctx.tc_gasprice) inst s
    | CHAINID => exec_read0 (\s. s.vs_tx_ctx.tc_chainid) inst s

    (* Environment - Block context *)
    | COINBASE => exec_read0 (\s. w2w s.vs_block_ctx.bc_coinbase) inst s
    | TIMESTAMP => exec_read0 (\s. s.vs_block_ctx.bc_timestamp) inst s
    | NUMBER => exec_read0 (\s. s.vs_block_ctx.bc_number) inst s
    | PREVRANDAO => exec_read0 (\s. s.vs_block_ctx.bc_prevrandao) inst s
    | GASLIMIT => exec_read0 (\s. s.vs_block_ctx.bc_gaslimit) inst s
    | BASEFEE => exec_read0 (\s. s.vs_block_ctx.bc_basefee) inst s
    | BLOBBASEFEE => exec_read0 (\s. s.vs_block_ctx.bc_blobbasefee) inst s
    | BLOCKHASH => exec_read1 (\v s. s.vs_block_ctx.bc_blockhash (w2n v)) inst s
    | BLOBHASH => exec_read1
        (\v s. let idx = w2n v in
               let hashes = s.vs_tx_ctx.tc_blobhashes in
               if idx < LENGTH hashes then EL idx hashes else 0w) inst s

    (* Environment - Balance *)
    | BALANCE => exec_read1
        (\addr s. n2w (lookup_account (w2w addr) s.vs_accounts).balance) inst s
    | SELFBALANCE => exec_read0
        (\s. n2w (lookup_account s.vs_call_ctx.cc_address s.vs_accounts).balance) inst s

    (* Calldata *)
    | CALLDATASIZE => exec_read0 (\s. n2w (LENGTH s.vs_call_ctx.cc_calldata)) inst s
    | CALLDATALOAD => exec_read1
        (\offset s. let data = s.vs_call_ctx.cc_calldata in
                    let bytes = TAKE 32 (DROP (w2n offset) data ++ REPLICATE 32 0w) in
                    word_of_bytes T (0w:bytes32) bytes) inst s

    | CALLDATACOPY =>
        (case inst.inst_operands of
          [op_destOffset; op_offset; op_size] =>
            (case (eval_operand op_destOffset s, eval_operand op_offset s, eval_operand op_size s) of
              (SOME destOffset, SOME offset, SOME size_val) =>
                let data = s.vs_call_ctx.cc_calldata in
                let size = w2n size_val in
                let src_offset = w2n offset in
                let bytes = TAKE size (DROP src_offset data ++ REPLICATE size 0w) in
                OK (write_memory_with_expansion (w2n destOffset) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "calldatacopy requires 3 operands")

    (* Return data *)
    | RETURNDATASIZE => exec_read0 (\s. n2w (LENGTH s.vs_returndata)) inst s

    | RETURNDATACOPY =>
        (case inst.inst_operands of
          [op_destOffset; op_offset; op_size] =>
            (case (eval_operand op_destOffset s, eval_operand op_offset s, eval_operand op_size s) of
              (SOME destOffset, SOME offset, SOME size_val) =>
                let size = w2n size_val in
                let src_offset = w2n offset in
                (* OOB access is exceptional halt per EIP-211 *)
                if src_offset + size > LENGTH s.vs_returndata then
                  Abort ExHalt_abort (halt_state (set_returndata [] s))
                else
                  let bytes = TAKE size (DROP src_offset s.vs_returndata) in
                  OK (write_memory_with_expansion (w2n destOffset) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "returndatacopy requires 3 operands")

    (* Memory top (lowers to EVM MSIZE at assembly) *)
    | MEMTOP => exec_read0
        (\s. let size = LENGTH s.vs_memory in
             let words = (size + 31) DIV 32 in
             n2w (words * 32)) inst s

    (* Hashing - using Keccak256 like EVM *)
    | SHA3 =>
        (case inst.inst_operands of
          [op_offset; op_size] =>
            (case (eval_operand op_offset s, eval_operand op_size s) of
              (SOME offset, SOME size_val) =>
                (case inst.inst_outputs of
                  [out] =>
                    let size = w2n size_val in
                    let off = w2n offset in
                    let data = TAKE size (DROP off s.vs_memory ++ REPLICATE size 0w) in
                    let hash = word_of_bytes T (0w:bytes32) (Keccak_256_w64 data) in
                    OK (update_var out hash s)
                | _ => Error "sha3 requires single output")
            | _ => Error "undefined operand")
        | _ => Error "sha3 requires 2 operands")

    (* Code introspection *)
    | CODESIZE => exec_read0 (\s. n2w (LENGTH s.vs_code)) inst s
    | EXTCODESIZE => exec_read1
        (\addr s. n2w (LENGTH (lookup_account (w2w addr)
                                              s.vs_accounts).code)) inst s
    | EXTCODEHASH =>
        exec_read1
          (\addr s.
            let acct = lookup_account (w2w addr) s.vs_accounts in
            if account_empty acct then 0w
            else word_of_bytes T (0w:bytes32)
                   (Keccak_256_w64 acct.code)) inst s

    (* Immutables are lowered to ordinary EVM memory operations.  Keep the
       finite map as source-level bookkeeping, but make executable reads and
       writes use the same byte memory represented by assembly semantics. *)
    | ILOAD => exec_read1 (\off s. mload (w2n off) s) inst s
    | ISTORE =>
        (case inst.inst_operands of
          [offset_op; val_op] =>
            (case (eval_operand offset_op s, eval_operand val_op s) of
              (SOME off, SOME v) => OK (istore (w2n off) v s)
            | _ => Error "undefined operand")
        | _ => Error "istore requires 2 operands")

    (* Data section reads *)
    | DLOAD => exec_read1
        (\off s.
          let bytes = TAKE 32 (DROP (w2n off) s.vs_data_section ++
                               REPLICATE 32 0w) in
          word_of_bytes T (0w:bytes32) bytes) inst s

    | DLOADBYTES =>
        (case inst.inst_operands of
          [op_dst; op_src; op_size] =>
            (case (eval_operand op_dst s, eval_operand op_src s,
                   eval_operand op_size s) of
              (SOME dst, SOME src, SOME size_val) =>
                let size = w2n size_val in
                let bytes = TAKE size (DROP (w2n src) s.vs_data_section ++
                                      REPLICATE size 0w) in
                OK (write_memory_with_expansion (w2n dst) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "dloadbytes requires 3 operands")

    (* Code access *)
    | CODECOPY =>
        (case inst.inst_operands of
          [op_dst; op_src; op_size] =>
            (case (eval_operand op_dst s, eval_operand op_src s,
                   eval_operand op_size s) of
              (SOME dst, SOME src, SOME size_val) =>
                let size = w2n size_val in
                let bytes = TAKE size (DROP (w2n src) s.vs_code ++
                                      REPLICATE size 0w) in
                OK (write_memory_with_expansion (w2n dst) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "codecopy requires 3 operands")

    | EXTCODECOPY =>
        (case inst.inst_operands of
          [op_addr; op_dst; op_src; op_size] =>
            (case (eval_operand op_addr s, eval_operand op_dst s,
                   eval_operand op_src s, eval_operand op_size s) of
              (SOME addr, SOME dst, SOME src, SOME size_val) =>
                let code = (lookup_account (w2w addr) s.vs_accounts).code in
                let size = w2n size_val in
                let bytes = TAKE size (DROP (w2n src) code ++
                                      REPLICATE size 0w) in
                OK (write_memory_with_expansion (w2n dst) bytes s)
            | _ => Error "undefined operand")
        | _ => Error "extcodecopy requires 4 operands")

    (* Label offset computation - semantically identical to ADD.
       Kept as separate opcode for codegen: venom_to_assembly emits PUSH_OFST
       for OFFSET, letting the assembler resolve the label. At IR level,
       labels resolve via vs_labels (eval_operand handles Label operands).
       Operand order matches Python builder: offset(operand, label). *)
    | OFFSET => exec_pure2 word_add inst s

    (* Logging - variable operand count.
       Semantic order: log topic_count, offset, size, topic_0, ..., topic_{n-1}
       First operand is Lit topic_count (metadata), then offset, size, topics. *)
    | LOG =>
        (case inst.inst_operands of
          Lit tc :: rest =>
            let n = w2n tc in
            (* rest should be: offset, size, n topics *)
            if LENGTH rest <> n + 2 then Error "log: wrong operand count"
            else
              let offset_op = EL 0 rest in
              let size_op = EL 1 rest in
              let topic_ops = DROP 2 rest in
              (case (eval_operand offset_op s,
                     eval_operand size_op s,
                     eval_operands topic_ops s) of
                (SOME off, SOME sz, SOME topics) =>
                  let data = TAKE (w2n sz) (DROP (w2n off) s.vs_memory ++
                                            REPLICATE (w2n sz) 0w) in
                  let ev = <| logger := w2w s.vs_call_ctx.cc_address;
                              topics := topics;
                              data := data |> in
                  OK (s with vs_logs := s.vs_logs ++ [ev])
              | _ => Error "log: undefined operand")
        | _ => Error "log requires Lit topic_count as first operand")

    (* Selfdestruct: transfer balance to beneficiary, then halt.
       Deprecated post-Cancun but still defined in Venom IR. *)
    | SELFDESTRUCT =>
        (case inst.inst_operands of
          [addr_op] =>
            (case eval_operand addr_op s of
              SOME addr =>
                let self = s.vs_call_ctx.cc_address in
                let bal = (lookup_account self s.vs_accounts).balance in
                let beneficiary = w2w addr in
                let accts = s.vs_accounts in
                let self_acct = lookup_account self accts in
                let ben_acct = lookup_account beneficiary accts in
                let accts' = (\a. if a = self then
                                    self_acct with balance := 0
                                  else if a = beneficiary then
                                    ben_acct with balance := ben_acct.balance + bal
                                  else accts a) in
                Halt (halt_state (s with vs_accounts := accts'))
            | NONE => Error "selfdestruct: undefined operand")
        | _ => Error "selfdestruct requires 1 operand")

    (* Invalid opcode — exceptional halt (EVM: consumes all gas, no returndata) *)
    | INVALID => Abort ExHalt_abort (halt_state (set_returndata [] s))

    (* ----------------------------------------------------------------
       External calls
       ---------------------------------------------------------------- *)
    | CALL =>
        (case inst.inst_operands of
          [gas_op; addr_op; val_op; ao_op; as_op; ro_op; rs_op] =>
            (case (eval_operand gas_op s, eval_operand addr_op s,
                   eval_operand val_op s, eval_operand ao_op s,
                   eval_operand as_op s, eval_operand ro_op s,
                   eval_operand rs_op s) of
              (SOME gas, SOME addr, SOME value, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_ext_call inst s gas addr value ao as_ ro rs
                  s.vs_call_ctx.cc_static
            | _ => Error "undefined operand")
        | _ => Error "call requires 7 operands")

    | STATICCALL =>
        (case inst.inst_operands of
          [gas_op; addr_op; ao_op; as_op; ro_op; rs_op] =>
            (case (eval_operand gas_op s, eval_operand addr_op s,
                   eval_operand ao_op s, eval_operand as_op s,
                   eval_operand ro_op s, eval_operand rs_op s) of
              (SOME gas, SOME addr, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_ext_call inst s gas addr (0w:bytes32) ao as_ ro rs T
            | _ => Error "undefined operand")
        | _ => Error "staticcall requires 6 operands")

    | DELEGATECALL =>
        (case inst.inst_operands of
          [gas_op; addr_op; ao_op; as_op; ro_op; rs_op] =>
            (case (eval_operand gas_op s, eval_operand addr_op s,
                   eval_operand ao_op s, eval_operand as_op s,
                   eval_operand ro_op s, eval_operand rs_op s) of
              (SOME gas, SOME addr, SOME ao, SOME as_, SOME ro, SOME rs) =>
                exec_delegatecall inst s gas addr ao as_ ro rs
            | _ => Error "undefined operand")
        | _ => Error "delegatecall requires 6 operands")

    | CREATE =>
        (case inst.inst_operands of
          [val_op; off_op; sz_op] =>
            (case (eval_operand val_op s, eval_operand off_op s,
                   eval_operand sz_op s) of
              (SOME value, SOME offset, SOME sz) =>
                exec_create inst s value offset sz NONE
            | _ => Error "undefined operand")
        | _ => Error "create requires 3 operands")

    | CREATE2 =>
        (case inst.inst_operands of
          [val_op; off_op; sz_op; salt_op] =>
            (case (eval_operand val_op s, eval_operand off_op s,
                   eval_operand sz_op s, eval_operand salt_op s) of
              (SOME value, SOME offset, SOME sz, SOME salt) =>
                exec_create inst s value offset sz (SOME salt)
            | _ => Error "undefined operand")
        | _ => Error "create2 requires 4 operands")

    (* ----------------------------------------------------------------
       Memory Allocation: ALLOCA

       Bump-allocate a region in the alloca area (beyond vs_memory)
       and record in vs_allocas.

       Operands: [Lit size]
       Output: [out] = base address (word256) of allocated region
       ---------------------------------------------------------------- *)
    | ALLOCA =>
        (case inst.inst_operands of
          [Lit alloc_size] =>
            exec_alloca inst s alloc_size
        | _ => Error "alloca requires 1 literal operand")

    (* Default - truly unknown opcode *)
    | _ => Error "unknown opcode"
End

Theorem step_inst_base_ILOAD:
  eval_operand op s = SOME off ==>
  step_inst_base (instruction id ILOAD [op] [out]) s =
    OK (update_var out (mload (w2n off) s) s)
Proof
  simp[step_inst_base_def, exec_read1_def]
QED

Theorem step_inst_base_ISTORE:
  eval_operand offset_op s = SOME off /\
  eval_operand value_op s = SOME value ==>
  step_inst_base (instruction id ISTORE [offset_op; value_op] []) s =
    OK (istore (w2n off) value s)
Proof
  simp[step_inst_base_def, exec_write2_def]
QED

Theorem step_inst_base_NOT:
  inst.inst_opcode = NOT ==>
  step_inst_base inst s = exec_pure1 word_1comp inst s
Proof
  Cases_on `inst` >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_ISZERO:
  inst.inst_opcode = ISZERO ==>
  step_inst_base inst s =
    exec_pure1 (\x. bool_to_word (x = 0w)) inst s
Proof
  Cases_on `inst` >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_RETFMP:
  inst.inst_opcode = RETFMP ==>
  step_inst_base inst s =
    case eval_operands inst.inst_operands s of
      SOME [] => Error "retfmp requires a return pc"
    | SOME ret_vals =>
        IntRet <| iret_values := FRONT ret_vals;
                  iret_adopt_fmp := SOME s.vs_fmp |> s
    | NONE => Error "retfmp: undefined return value"
Proof
  Cases_on `inst` >> gvs[step_inst_base_def]
QED

Theorem step_inst_base_DRET:
  inst.inst_opcode = DRET ==>
  step_inst_base inst s =
    if inst.inst_outputs <> [] then Error "dret requires no outputs"
    else
      case parse_dret_shape inst of
        NONE => Error "dret: malformed operand envelope"
      | SOME (ordinary,dynamic) =>
          case eval_operands inst.inst_operands s of
            NONE => Error "dret: undefined operand"
          | SOME vals =>
              case pair_dret_words
                (TAKE (2 * dynamic) (DROP (1 + ordinary) vals)) of
                NONE => Error "dret: malformed dynamic operands"
              | SOME pairs =>
                  let ordinary_vals = TAKE ordinary (DROP 1 vals) in
                  let (ptrs,final_cursor,s') =
                    pack_dret_dynamic s.vs_call_entry_fmp pairs s in
                  let s'' = s' with vs_fmp := final_cursor in
                    IntRet
                      <| iret_values := ordinary_vals ++ ptrs;
                         iret_adopt_fmp := SOME final_cursor |> s''
Proof
  Cases_on `inst` >> gvs[step_inst_base_def]
QED

(* --------------------------------------------------------------------------
   Block and Function Execution
   -------------------------------------------------------------------------- *)

(* Non-terminator instructions preserve inst_idx.
   Co-located with run_block definition because run_block's
   termination proof depends on this theorem. *)
Theorem step_inst_base_preserves_inst_idx:
  !inst s s'.
    step_inst_base inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    s'.vs_inst_idx = s.vs_inst_idx
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  PURE_REWRITE_TAC[step_inst_base_def] >>
  ASM_REWRITE_TAC[opcode_case_def] >>
  gvs[AllCaseEqs(), exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, exec_write2_def,
      exec_ext_call_def, exec_delegatecall_def,
      exec_create_def, exec_alloca_def,
      extract_venom_result_def] >>
  rpt strip_tac >> gvs[] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  fs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     istore_def, write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def]
QED

(* --------------------------------------------------------------------------
   Block Step (single instruction within a block)

   Does NOT handle INVOKE — use run_block for cross-function execution.
   Useful as a single-step abstraction for pass correctness proofs.
   -------------------------------------------------------------------------- *)

Definition block_step_def:
  block_step bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => (Error "block not terminated", T)
    | SOME inst =>
        case step_inst_base inst s of
          OK s' =>
            if is_terminator inst.inst_opcode then (OK s', T)
            else (OK (next_inst s'), F)
        | Halt s' => (Halt s', T)
        | Abort a s' => (Abort a s', T)
        
        | IntRet vals s' => (IntRet vals s', T)
        | Error e => (Error e, T)
End

(* --------------------------------------------------------------------------
   INVOKE Helpers
   -------------------------------------------------------------------------- *)

(* Merge callee's side effects back into caller after INVOKE.
   Internal function calls share the same contract, so mutable state
   (memory, transient storage, accounts, returndata, logs, immutables)
   propagates from callee to caller.  vs_alloca_next propagates too
   (global bump pointer).  vs_allocas stays as caller's (per-frame).
   Caller-local fields (vars, params, control flow, contexts) are kept. *)
Definition merge_callee_state_def:
  merge_callee_state caller callee =
    caller with <|
      vs_memory     := callee.vs_memory;
      vs_transient  := callee.vs_transient;
      vs_accounts   := callee.vs_accounts;
      vs_returndata := callee.vs_returndata;
      vs_logs       := callee.vs_logs;
      vs_immutables := callee.vs_immutables;
      vs_alloca_next := callee.vs_alloca_next
      (* vs_allocas NOT copied — caller keeps its own frame's allocas *)
    |>
End

(* Prepare callee state: fresh frame rooted at the caller's current FMP.
   The final evaluated argument is the logical return-PC token; the complete
   argument vector is retained for indexed PARAM/FMP_PARAM semantics. *)
Definition setup_callee_def:
  setup_callee fn args s =
    if NULL fn.fn_blocks \/ NULL args then NONE
    else SOME (s with <|
      vs_vars            := FEMPTY;
      vs_params          := args;
      vs_current_bb      := (HD fn.fn_blocks).bb_label;
      vs_inst_idx        := 0;
      vs_prev_bb         := NONE;
      vs_halted          := F;
      vs_allocas         := FEMPTY;
      vs_fmp             := s.vs_fmp;
      vs_call_entry_fmp  := s.vs_fmp;
      vs_return_pc_token := LAST args
    |>)
End

Definition adopt_return_fmp_def:
  adopt_return_fmp ir s =
    case ir.iret_adopt_fmp of
      NONE => s
    | SOME p => s with vs_fmp := p
End

(* Decode INVOKE operands: first is Label (callee name), rest are args *)
Definition decode_invoke_def:
  decode_invoke inst =
    case inst.inst_operands of
      (Label callee_name :: arg_ops) => SOME (callee_name, arg_ops)
    | _ => NONE
End

(* Bind return values to output variables *)
Definition bind_outputs_def:
  bind_outputs outs vals s =
    if LENGTH outs = LENGTH vals then
      SOME (FOLDL (\s' (out, val). update_var out val s') s (ZIP (outs, vals)))
    else NONE
End

(* --------------------------------------------------------------------------
   Preservation lemmas (needed by run_block/run_function termination proof)
   -------------------------------------------------------------------------- *)

Theorem merge_callee_state_inst_idx:
  (merge_callee_state c e).vs_inst_idx = c.vs_inst_idx
Proof
  simp[merge_callee_state_def]
QED


Theorem setup_callee_frame:
  setup_callee fn args caller = SOME callee ==>
  callee.vs_fmp = caller.vs_fmp /\
  callee.vs_call_entry_fmp = caller.vs_fmp /\
  callee.vs_return_pc_token = LAST args /\
  callee.vs_params = args
Proof
  rw[setup_callee_def] >> gvs[]
QED

Theorem merge_callee_state_frame[simp]:
  (merge_callee_state caller callee).vs_fmp = caller.vs_fmp /\
  (merge_callee_state caller callee).vs_call_entry_fmp = caller.vs_call_entry_fmp /\
  (merge_callee_state caller callee).vs_return_pc_token = caller.vs_return_pc_token
Proof
  simp[merge_callee_state_def]
QED

Theorem adopt_return_fmp_frame[simp]:
  (adopt_return_fmp ir s).vs_call_entry_fmp = s.vs_call_entry_fmp /\
  (adopt_return_fmp ir s).vs_return_pc_token = s.vs_return_pc_token
Proof
  Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem adopt_return_fmp_allocas[simp]:
  !ir s. (adopt_return_fmp ir s).vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >> Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem adopt_return_fmp_halted[simp]:
  (adopt_return_fmp ir s).vs_halted = s.vs_halted
Proof
  Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem adopt_return_fmp_NONE[simp]:
  adopt_return_fmp <| iret_values := vals; iret_adopt_fmp := NONE |> s = s
Proof
  simp[adopt_return_fmp_def]
QED

Theorem adopt_return_fmp_SOME[simp]:
  adopt_return_fmp <| iret_values := vals; iret_adopt_fmp := SOME p |> s =
    s with vs_fmp := p
Proof
  simp[adopt_return_fmp_def]
QED
Theorem adopt_return_fmp_inst_idx[simp]:
  (adopt_return_fmp ir s).vs_inst_idx = s.vs_inst_idx
Proof
  Cases_on `ir.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem update_var_inst_idx:
  (update_var x v s).vs_inst_idx = s.vs_inst_idx
Proof
  simp[update_var_def]
QED

Theorem foldl_update_var_inst_idx:
  !kvs s. (FOLDL (\s' (k,v). update_var k v s') s kvs).vs_inst_idx =
          s.vs_inst_idx
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >>
  rw[Once update_var_def] >> simp[update_var_inst_idx]
QED

Theorem bind_outputs_inst_idx:
  bind_outputs outs vals s = SOME s' ==> s'.vs_inst_idx = s.vs_inst_idx
Proof
  rw[bind_outputs_def] >> gvs[foldl_update_var_inst_idx]
QED

(* --------------------------------------------------------------------------
   Parallel PHI evaluation

   PHIs have parallel semantics: all sources are read from the pre-PHI
   state, then all outputs are written.  eval_phis processes the PHI
   prefix of a block, reading every source from the original state s
   and accumulating writes into the result state.
   -------------------------------------------------------------------------- *)

(* Evaluate one PHI instruction against state s.
   Returns (output_var, value) or NONE on error. *)
Definition eval_one_phi_def:
  eval_one_phi s inst =
    case (inst.inst_outputs, s.vs_prev_bb) of
      ([out], SOME prev) =>
        (case resolve_phi prev inst.inst_operands of
           NONE => NONE
         | SOME val_op =>
             case eval_operand val_op s of
               SOME v => SOME (out, v)
             | NONE => NONE)
    | _ => NONE
End

(* Batch-evaluate PHI prefix: read all from s, write all into result.
   Stops at first non-PHI instruction. *)
Definition eval_phis_def:
  eval_phis s [] = OK s /\
  eval_phis s (inst::rest) =
    if inst.inst_opcode <> PHI then OK s
    else
      case eval_one_phi s inst of
        NONE => Error "phi evaluation failed"
      | SOME (out, v) =>
          case eval_phis s rest of
            OK s' => OK (update_var out v s')
          | err => err
End

(* Length of the PHI prefix of an instruction list. *)
Definition phi_prefix_length_def:
  phi_prefix_length [] = 0 /\
  phi_prefix_length (inst::rest) =
    if inst.inst_opcode = PHI then SUC (phi_prefix_length rest)
    else 0
End

(* --------------------------------------------------------------------------
   Execution (3-way mutually recursive: step_inst / exec_block / run_blocks)

   step_inst handles ALL opcodes including INVOKE (which calls run_blocks).
   exec_block sequences instructions within a basic block from vs_inst_idx.
   run_blocks dispatches blocks using fuel.

   Fuel bounds function-call depth (not instruction count).  Within a
   block, termination is structural (inst_idx increases toward block end).

   exec_block explicitly sets vs_inst_idx := SUC s.vs_inst_idx for the
   continuation, decoupling termination from step_inst's behavior.

   run_blocks evaluates PHIs in parallel (via eval_phis) at block entry,
   then delegates to exec_block starting past the PHI prefix.

   Public wrappers (defined below):
     run_block    — eval_phis + exec_block (matching run_blocks behavior)
     run_function — run_blocks with entry-block setup
   -------------------------------------------------------------------------- *)

Definition run_defs:
  (step_inst fuel ctx inst s =
    if inst.inst_opcode = INVOKE then
      case decode_invoke inst of
        NONE => Error "invoke: bad operand format"
      | SOME (callee_name, arg_ops) =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => Error "invoke: function not found"
          | SOME callee_fn =>
              case eval_operands arg_ops s of
                NONE => Error "invoke: undefined argument"
              | SOME args =>
                  case setup_callee callee_fn args s of
                    NONE => Error "invoke: empty function"
                  | SOME callee_s =>
                      case run_blocks fuel ctx callee_fn callee_s of
                        IntRet ret callee_s' =>
                          (case bind_outputs inst.inst_outputs ret.iret_values
                                  (adopt_return_fmp ret
                                    (merge_callee_state s callee_s')) of
                            SOME s' => OK s'
                          | NONE => Error "invoke: return arity mismatch")
                      | Halt s' => Halt s'
                      | Abort a s' => Abort a s'
                      | Error e => Error e
                      | OK _ => Error "invoke: callee did not return"
    else step_inst_base inst s)
  /\
  (exec_block fuel ctx bb s =
    case get_instruction bb s.vs_inst_idx of
      NONE => Error "block not terminated"
    | SOME inst =>
        case step_inst fuel ctx inst s of
          OK s' =>
            if is_terminator inst.inst_opcode then
              if s'.vs_halted then Halt s' else OK s'
            else exec_block fuel ctx bb
                   (s' with vs_inst_idx := SUC s.vs_inst_idx)
        | IntRet vals s' => IntRet vals s'
        | Halt s' => Halt s'
        | Abort a s' => Abort a s'
        | Error e => Error e)
  /\
  (run_blocks fuel ctx fn s =
    case fuel of
      0 => Error "out of fuel"
    | SUC fuel' =>
        case lookup_block s.vs_current_bb fn.fn_blocks of
          NONE => Error "block not found"
        | SOME bb =>
            case eval_phis s bb.bb_instructions of
              Error e => Error e
            | OK s_phi =>
                case exec_block fuel' ctx bb
                       (s_phi with vs_inst_idx :=
                          phi_prefix_length bb.bb_instructions) of
                  OK s' =>
                    if s'.vs_halted then Halt s'
                    else run_blocks fuel' ctx fn s'
                | IntRet vals s' => IntRet vals s'
                | other => other)
Termination
  WF_REL_TAC `inv_image ($< LEX $<)
    (\x. case x of
      | INL (fuel, ctx, inst, s) => (fuel, 1)
      | INR (INL (fuel, ctx, bb, s)) =>
          (fuel, 2 + (LENGTH bb.bb_instructions - s.vs_inst_idx))
      | INR (INR (fuel, ctx, fn, s)) => (fuel, 0))` >>
  rpt strip_tac >> gvs[get_instruction_def]
End

(* Extract individual definitions for downstream use *)
val step_inst_def = save_thm("step_inst_def", cj 1 run_defs);
val exec_block_def = save_thm("exec_block_def", cj 2 run_defs);
val run_blocks_def = save_thm("run_blocks_def", cj 3 run_defs);

(* --------------------------------------------------------------------------
   Block Entry Point

   run_block evaluates PHIs in parallel (via eval_phis) then executes
   the rest of the block via exec_block starting past the PHI prefix.
   Matches the behavior inlined into run_blocks.
   -------------------------------------------------------------------------- *)

(* run_block: full block execution including parallel PHI evaluation.
   Matches the per-iteration behavior inlined in run_blocks.
   eval_phis evaluates PHIs in parallel, then exec_block runs
   the remaining instructions starting past the PHI prefix. *)
Definition run_block_def:
  run_block fuel ctx bb s =
    case eval_phis s bb.bb_instructions of
      OK s_phi =>
        exec_block fuel ctx bb
          (s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    | Error e => Error e
End

(* Backward compat: run_block_entry = run_block *)
Overload run_block_entry = ``run_block``
val run_block_entry_def = save_thm("run_block_entry_def", run_block_def);

(* eval_phis only returns OK or Error — needed to close ARB arms in run_blocks_unfold *)
Theorem eval_phis_ok_or_error_defs:
  !s insts. (?s'. eval_phis s insts = OK s') \/
            (?e. eval_phis s insts = Error e)
Proof
  Induct_on `insts` >> rw[eval_phis_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  first_x_assum (qspec_then `s` strip_assume_tac) >> gvs[]
QED

(* run_blocks_unfold: unfold one iteration of run_blocks using run_block.
   Unconditional version for use as a CONV rewrite.
   This is the primary rewrite rule for block-iteration proofs. *)
Theorem run_blocks_unfold:
  run_blocks (SUC fuel) ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => Error "block not found"
    | SOME bb =>
        case run_block fuel ctx bb s of
          OK s' =>
            if s'.vs_halted then Halt s'
            else run_blocks fuel ctx fn s'
        | IntRet vals s' => IntRet vals s'
        | Halt s' => Halt s'
        | Abort a s' => Abort a s'
        | Error e => Error e
Proof
  simp[Once run_blocks_def, run_block_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  mp_tac (Q.SPECL [`s`, `x.bb_instructions`] eval_phis_ok_or_error_defs) >>
  strip_tac >> gvs[]
QED

(* Alias: run_block_non_phis is exec_block (for backward compat with
   proofs written against the pre-merge 4-way mutual recursion).
   Use exec_block / run_block_non_phis for instruction-level reasoning
   (no PHI evaluation, respects vs_inst_idx). *)
Overload run_block_non_phis = ``exec_block``
val run_block_non_phis_def = save_thm("run_block_non_phis_def", exec_block_def);

(* step_inst preserves inst_idx for non-terminators (all opcodes incl INVOKE) *)
Theorem step_inst_preserves_inst_idx:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\ ~is_terminator inst.inst_opcode ==>
    s'.vs_inst_idx = s.vs_inst_idx
Proof
  rw[Once step_inst_def] >>
  gvs[AllCaseEqs(), is_terminator_def] >-
  (* INVOKE case *)
  (imp_res_tac bind_outputs_inst_idx >>
   gvs[merge_callee_state_inst_idx]) >>
  (* Non-INVOKE: delegate to step_inst_base *)
  imp_res_tac step_inst_base_preserves_inst_idx >>
  gvs[is_terminator_def]
QED

(* step_inst agrees with step_inst_base for non-INVOKE opcodes *)
Theorem step_inst_non_invoke:
  !fuel ctx inst s.
    inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst s = step_inst_base inst s
Proof
  rw[Once step_inst_def]
QED

Theorem step_inst_param_ok_or_error:
  !inst fuel ctx s.
    is_param_opcode inst.inst_opcode ==>
    (?s'. step_inst fuel ctx inst s = OK s') \/
    (?e. step_inst fuel ctx inst s = Error e)
Proof
  rpt strip_tac >>
  fs[is_param_opcode_iff] >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst` >>
  simp[step_inst_base_def] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >> gvs[step_inst_base_def])
QED

(* --------------------------------------------------------------------------
   Function Entry Point

   run_function sets up the entry block and inst_idx, then delegates to
   run_blocks.  This separates "start executing a function" from
   "continue iterating blocks within a function".
   -------------------------------------------------------------------------- *)

Definition run_function_def:
  run_function fuel ctx fn s =
    case fn_entry_label fn of
      NONE => Error "no entry block"
    | SOME lbl =>
        run_blocks fuel ctx fn
          (s with <| vs_current_bb := lbl; vs_inst_idx := 0 |>)
End

(* --------------------------------------------------------------------------
   Context Entry Point
   -------------------------------------------------------------------------- *)

Definition run_context_def:
  run_context fuel ctx s =
    case ctx.ctx_entry of
      NONE => Error "no entry function"
    | SOME entry_name =>
        case lookup_function entry_name ctx.ctx_functions of
          NONE => Error "entry function not found"
        | SOME entry_fn =>
            run_function fuel ctx entry_fn
              (s with vs_prev_bb := NONE)
End
