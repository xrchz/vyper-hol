(*
 * Contract Creation Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_raw_create        — full raw_create with optional ctor args
 *   compile_create_proxy      — create_minimal_proxy_to (EIP-1167)
 *   compile_create_copy       — create_copy_of (extcodecopy + preamble)
 *   compile_create_blueprint  — create_from_blueprint (ERC-5202, with ctor args)
 *
 * Helper:
 *   compile_create_dispatch   — inner CREATE/CREATE2 + result check
 *   compile_check_create_result — validate CREATE result
 *
 * Each returns the new contract address.
 * Salt parameter triggers CREATE2 instead of CREATE.
 *
 * Mirrors Python: vyper/codegen_venom/builtins/create.py
 *)

Theory builtinCreate
Ancestors
  emitHelper context abiEncoder compileEnv venomInst
Libs
  monadsyntax

(* ===== Check CREATE result ===== *)
(* Mirrors Python: create.py _check_create_result
   If revert_on_failure:
     JNZ addr → ok_label / fail_label
     fail: returndatacopy revert data, REVERT
     ok: continue
   Else: just return addr (0 on failure).
   This matches the Python's branch+revert-bubble pattern. *)
Definition compile_check_create_result_def:
  compile_check_create_result result revert_on_failure =
    if revert_on_failure then
      do fail_lbl <- fresh_label "create_fail";
         ok_lbl <- fresh_label "create_ok";
         emit_inst JNZ
           [result; Label ok_lbl; Label fail_lbl] [];
         (* Failure path: bubble up revert data *)
         new_block fail_lbl;
         rds <- emit_op RETURNDATASIZE [];
         emit_void RETURNDATACOPY [Lit 0w; Lit 0w; rds];
         emit_inst REVERT [Lit 0w; rds] [];
         (* Success path *)
         new_block ok_lbl;
         return result
      od
    else
      return result
End

(* ===== CREATE/CREATE2 dispatch ===== *)
(* Inner dispatch: emit CREATE or CREATE2 + check result.
   Used by compile_raw_create, compile_create_proxy, compile_create_copy. *)
Definition compile_create_dispatch_def:
  compile_create_dispatch code_ptr code_len value_op salt_opt
                     revert_on_failure =
    do result <-
         (case salt_opt of
            NONE => emit_op CREATE [value_op; code_ptr; code_len]
          | SOME salt_op => emit_op CREATE2
              [value_op; code_ptr; code_len; salt_op]);
       compile_check_create_result result revert_on_failure
    od
End

(* ===== raw_create ===== *)
(* Full raw_create pipeline with optional ABI-encoded constructor arguments.
   Mirrors Python: create.py lower_raw_create

   bytecode_op: pointer to bytestring [length][data] in memory.
     Caller must materialize from storage/transient before calling.
     Python copies bytecode to a fresh buffer to avoid overlap with
     subsequent expressions (value, salt, ctor args). We take the
     bytecode already materialized to memory.
   ctor_args_info: NONE for no ctor args, or
     SOME (args_ptr, args_enc_info, abi_size, bytecode_maxlen) for ctor args.
     args_ptr: pointer to ctor args tuple in Vyper memory layout.
     args_enc_info: ABI encoding info for the ctor args tuple type.
     abi_size: abi_type.size_bound() for the ctor args tuple.
     bytecode_maxlen: max length of bytecode (for buffer sizing). *)
Definition compile_raw_create_def:
  compile_raw_create bytecode_op value_op salt_opt
                     revert_on_failure ctor_args_info =
    do (* Get bytecode length and data pointer *)
       bytecode_len <- emit_op MLOAD [bytecode_op];
       bytecode_ptr <- emit_op ADD [bytecode_op; Lit 32w];
       (case ctor_args_info of
          NONE =>
            (* No ctor args: CREATE directly from bytecode *)
            compile_create_dispatch bytecode_ptr bytecode_len
              value_op salt_opt revert_on_failure
        | SOME (args_ptr, args_enc_info, abi_size, bytecode_maxlen) =>
            (* With ctor args: alloc buffer, copy bytecode, ABI-encode args, append *)
            do buf_alloc <- compile_alloc_buffer (bytecode_maxlen + abi_size);
               buf <- return buf_alloc.buf_operand;
               (* Copy bytecode to buffer *)
               compile_copy_memory_dynamic buf bytecode_ptr bytecode_len;
               (* ABI encode ctor args after bytecode *)
               args_start <- emit_op ADD [buf; bytecode_len];
               args_len <- compile_abi_encode_to_buf args_start args_ptr
                             args_enc_info;
               (* Total length = bytecode_len + args_len *)
               total_len <- emit_op ADD [bytecode_len; args_len];
               compile_create_dispatch buf total_len
                 value_op salt_opt revert_on_failure
            od)
    od
End

(* ===== create_minimal_proxy_to ===== *)
(* Mirrors Python: create.py lower_create_minimal_proxy_to
   EIP-1167 minimal proxy: deploys a small proxy contract that
   delegatecalls to the target address.

   Proxy bytecode layout (54 bytes total):
   [loader: 9B] [forwarder_pre: 10B] [address: 20B] [forwarder_post: 15B]
   Loader:        602d3d8160093d39f3
   Forwarder_pre: 363d3d373d3d3d363d73
   Forwarder_post: 5af43d82803e903d91602b57fd5bf3

   Address must be left-aligned via SHL(96, addr).
   Uses 3x MSTORE (96 bytes buffer) to write all components. *)
Definition compile_create_proxy_def:
  compile_create_proxy target_op value_op salt_opt revert_on_failure =
    do (* Allocate 96-byte buffer for 3 x 32-byte stores *)
       buf_alloc <- compile_alloc_buffer 96;
       buf <- return buf_alloc.buf_operand;
       (* Store preamble (loader + forwarder_pre = 19 bytes, left-aligned in 32B)
          Exact bytes: 602d3d8160093d39f3 363d3d373d3d3d363d73 *)
       emit_void MSTORE [buf;
         Lit 0x602d3d8160093d39f3363d3d373d3d3d363d7300000000000000000000000000w];
       (* Left-align target address: SHL(96, addr) — 20 bytes, left-aligned *)
       aligned_target <- emit_op SHL [Lit 96w; target_op];
       (* Store aligned target at buf + 19 (preamble_length) *)
       buf_preamble <- emit_op ADD [buf; Lit 19w];
       emit_void MSTORE [buf_preamble; aligned_target];
       (* Store forwarder suffix at buf + 39 (preamble 19 + address 20) *)
       buf_post <- emit_op ADD [buf; Lit 39w];
       (* Exact bytes: 5af43d82803e903d91602b57fd5bf3 (15 bytes) *)
       emit_void MSTORE [buf_post;
         Lit 0x5af43d82803e903d91602b57fd5bf30000000000000000000000000000000000w];
       (* Create with 54 bytes total (19 + 20 + 15) *)
       compile_create_dispatch buf (Lit 54w) value_op salt_opt revert_on_failure
    od
End

(* ===== create_copy_of ===== *)
(* Mirrors Python:
   vyper/codegen_venom/builtins/create.py:CreateCopyOf.build_IR
   Clone existing contract bytecode:
   1. Get code size via EXTCODESIZE, assert non-zero
   2. Reserve code_size + 32 runtime bytes for the preamble word and code
   3. Build 11-byte initcode preamble (PUSH3 codesize, codecopy, return)
   4. MSTORE preamble (with codesize embedded), EXTCODECOPY code after
   5. CREATE/CREATE2 from allocation+21 with preamble_len+codesize

   Preamble bytes (11): encodes PUSH3(sz) + CODECOPY + RETURN pattern.
   Codesize is embedded in the preamble via SHL+OR. *)
Definition compile_create_copy_def:
  compile_create_copy target_op value_op salt_opt revert_on_failure =
    let preamble_len = 11 in
    let shl_bits = (preamble_len - 4) * 8 in  (* 56 bits *)
    do (* Get target code size *)
       code_size <- emit_op EXTCODESIZE [target_op];
       (* Assert target has code *)
       emit_void ASSERT [code_size];
       (* Reserve the full preamble word plus copied runtime code. *)
       alloc_size <- emit_op ADD [code_size; Lit 32w];
       mem_ofst <- compile_alloc_dynamic alloc_size;
       (* Build preamble with embedded codesize: shift codesize into position.
          Preamble template (11 bytes): 62 00 00 00 3d 81 60 0b 3d 39 f3
          PUSH3(sz) RDS DUP2 PUSH1(0x0B) RDS CODECOPY RETURN
          Codesize goes at bits [7*8:4*8] → SHL 56 bits. *)
       shifted_sz <- emit_op SHL [Lit (n2w shl_bits); code_size];
       (* OR with base constant: 0x620000003d81600b3d39f3 (right-aligned in 32B).
          MSTORE stores this right-aligned: preamble occupies bytes 21..31.
          SHL(56, codesize) places codesize at bytes 22-24 (PUSH3 argument). *)
       preamble <- emit_op OR
         [Lit 0x000000000000000000000000000000000000000000620000003d81600b3d39f3w;
          shifted_sz];
       (* Store preamble at mem_ofst (32-byte word, preamble at bytes 21-31) *)
       emit_void MSTORE [mem_ofst; preamble];
       (* Copy target code to mem_ofst + 32 *)
       code_dst <- emit_op ADD [mem_ofst; Lit 32w];
       emit_void EXTCODECOPY [target_op; code_dst; Lit 0w; code_size];
       (* Buffer starts at mem_ofst + (32 - preamble_len) = mem_ofst + 21 *)
       buf <- emit_op ADD [mem_ofst; Lit 21w];
       (* Total length = preamble_len + code_size *)
       buf_len <- emit_op ADD [code_size; Lit (n2w preamble_len)];
       (* Create *)
       result <-
         (case salt_opt of
            NONE => emit_op CREATE [value_op; buf; buf_len]
          | SOME salt_op => emit_op CREATE2
              [value_op; buf; buf_len; salt_op]);
       compile_check_create_result result revert_on_failure
    od
End

(* ===== create_from_blueprint ===== *)
(* Mirrors Python:
   vyper/codegen_venom/builtins/create.py:CreateFromBlueprint.build_IR
   Deploy from ERC-5202 blueprint contract:
   1. Read bytecode from blueprint (skipping code_offset prefix)
   2. Compute and reserve the complete runtime CREATE extent
   3. Append ABI-encoded ctor args if any (or raw args)
   4. CREATE or CREATE2

   args_ptr / args_len: pre-encoded constructor arguments to append.
     NONE means no ctor args.
   code_offset_op: offset into blueprint code (usually 3 for ERC-5202).
     Can be literal or runtime value. *)
Definition compile_create_blueprint_def:
  compile_create_blueprint target_op value_op salt_opt code_offset_op
                           args_info revert_on_failure =
    do (* Get blueprint code size, skipping preamble *)
       full_size <- emit_op EXTCODESIZE [target_op];
       code_size <- emit_op SUB [full_size; code_offset_op];
       (* Assert blueprint has code after preamble (sgt because underflow) *)
       has_code <- emit_op SGT [code_size; Lit 0w];
       emit_void ASSERT [has_code];
       (* Compute the complete contiguous CREATE extent before allocating. *)
       total_len <-
         (case args_info of
            NONE => return code_size
          | SOME (_, args_len) => emit_op ADD [code_size; args_len]);
       mem_ofst <- compile_alloc_dynamic total_len;
       (* Copy blueprint code (skipping preamble) to mem_ofst *)
       emit_void EXTCODECOPY
         [target_op; mem_ofst; code_offset_op; code_size];
       (* Append constructor args if present *)
       (case args_info of
          NONE => return ()
        | SOME (args_ptr, args_len) =>
            do args_dest <- emit_op ADD [mem_ofst; code_size];
               emit_void MCOPY [args_dest; args_ptr; args_len]
            od);
       (* Create *)
       result <-
         (case salt_opt of
            NONE => emit_op CREATE [value_op; mem_ofst; total_len]
          | SOME salt_op => emit_op CREATE2
              [value_op; mem_ofst; total_len; salt_op]);
       compile_check_create_result result revert_on_failure
    od
End
