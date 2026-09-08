(*
 * Codegen Context: data locations, VyperValue, buffer/ptr, memory operations
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 *
 * TOP-LEVEL:
 *   data_location      — where a value lives (MEMORY, STORAGE, TRANSIENT, CODE, CALLDATA)
 *   vyper_value      — StackValue type operand | LocatedValue type ptr
 *   vv_type          — extract type
 *   vv_operand       — extract raw operand
 *   vv_location      — extract location (NONE for stack)
 *   vv_is_stack      — predicate: is stack value?
 *   base_ptr         — buffer → ptr (LocMemory with provenance)
 *   mk_ptr           — convenience: ptr for non-memory locations
 *   ptr                 — pointer with location tag
 *   buffer              — allocated memory region
 *   word_scale          — addressing scale for a location (1 for slots, 32 for bytes)
 *   ptr_load            — dispatch load by location
 *   ptr_store           — dispatch store by location
 *   copy_memory         — copy memory region (mcopy or word-by-word)
 *   word_copy_loop      — parameterized loop for slot↔memory copies
 *   store_memory        — store value to memory (handles prim vs complex)
 *   store_memory_typed  — layout-aware copy (when src_typ ≠ dst_typ)
 *   copy_sarray_typed   — per-element SArray copy with different layouts
 *   copy_dynarray_typed — per-element DynArray copy with different layouts
 *
 * Mirrors Python: vyper/codegen_venom/context.py:Context,
 *                 vyper/codegen_venom/buffer.py:Buffer,
 *                 vyper/codegen_venom/value.py:VyperValue
 *)

Theory context
Ancestors
  emitHelper compileEnv venomInst
Libs
  monadsyntax

(* data_location, word_scale, is_slot_addressed now in compileEnvScript
   (shared so exprLowering can use them without circular dependency) *)

(* ===== Buffer ===== *)
(* An allocated memory region. Mirrors Python: buffer.py Buffer
   buf.base_ptr() gives a Ptr to the start with provenance. *)
Datatype:
  buffer = <|
    buf_operand : operand;   (* the alloca result operand *)
    buf_size : num            (* allocation size in bytes *)
  |>
End

(* ===== Ptr ===== *)
(* A pointer with location tag. Mirrors Python: buffer.py Ptr
   Invariant: ptr_buf is SOME iff ptr_location = LocMemory.
   Every memory pointer tracks its buffer provenance for non-aliasing proofs. *)
Datatype:
  ptr = <|
    ptr_operand : operand;
    ptr_location : data_location;
    ptr_buf : buffer option   (* provenance — SOME for memory, NONE otherwise *)
  |>
End

(* Create a Ptr from a Buffer (always LocMemory, always has provenance).
   Mirrors Python: buffer.py Buffer.base_ptr() *)
Definition base_ptr_def:
  base_ptr buf = <| ptr_operand := buf.buf_operand;
                    ptr_location := LocMemory;
                    ptr_buf := SOME buf |>
End

(* Convenience: make a ptr for non-memory locations (no buffer provenance) *)
Definition mk_ptr_def:
  mk_ptr op loc = <| ptr_operand := op; ptr_location := loc; ptr_buf := NONE |>
End

(* ===== VyperValue ===== *)
(* Location-aware wrapper for IR operands.
   Mirrors Python: vyper/codegen_venom/value.py VyperValue
   Carries type so unwrap_value is self-contained (no separate ty parameter).
   - StackValue ty op: operand IS the value (no load needed)
   - LocatedValue ty p: operand is a POINTER via ptr record (needs load for prims)
   Factoring: prove unwrap_value correct ONCE; each compile_expr case
   only proves "I tagged correctly"; every consumer applies unwrap theorem. *)
Datatype:
  vyper_value = StackValue type operand | LocatedValue type ptr
End

(* Get the type from a VyperValue *)
Definition vv_type_def:
  vv_type (StackValue ty _) = ty ∧
  vv_type (LocatedValue ty _) = ty
End

(* Get the raw operand from a VyperValue *)
Definition vv_operand_def:
  vv_operand (StackValue _ op) = op ∧
  vv_operand (LocatedValue _ p) = p.ptr_operand
End

(* Get the location (NONE for stack values) *)
Definition vv_location_def:
  vv_location (StackValue _ _) = NONE ∧
  vv_location (LocatedValue _ p) = SOME p.ptr_location
End

(* Is this a stack value? *)
Definition vv_is_stack_def:
  vv_is_stack (StackValue _ _) = T ∧
  vv_is_stack (LocatedValue _ _) = F
End

(* ===== Load/Store by Location ===== *)

(* Emit a load instruction based on location.
   is_ctor: T in constructor context — LocCode uses ILOAD (staging area).
            F in runtime context — LocCode uses DLOAD (deployed bytecode).
   Mirrors Python: context.py ptr_load + unwrap() is_ctor dispatch. *)
Definition compile_ptr_load_def:
  compile_ptr_load is_ctor LocMemory op = emit_op MLOAD [op] ∧
  compile_ptr_load is_ctor LocStorage op = emit_op SLOAD [op] ∧
  compile_ptr_load is_ctor LocTransient op = emit_op TLOAD [op] ∧
  compile_ptr_load is_ctor LocCalldata op = emit_op CALLDATALOAD [op] ∧
  compile_ptr_load is_ctor LocCode op =
    if is_ctor then emit_op ILOAD [op]
    else emit_op DLOAD [op]
End

(* Emit a store instruction based on location.
   is_ctor: T in constructor context — LocCode uses ISTORE (staging area).
            F in runtime context — LocCode store is invalid (read-only).
   Mirrors Python: context.py ptr_store + is_ctor dispatch. *)
Definition compile_ptr_store_def:
  compile_ptr_store is_ctor LocMemory dst val =
    emit_void MSTORE [dst; val] ∧
  compile_ptr_store is_ctor LocStorage dst val =
    emit_void SSTORE [dst; val] ∧
  compile_ptr_store is_ctor LocTransient dst val =
    emit_void TSTORE [dst; val] ∧
  compile_ptr_store is_ctor LocCode dst val =
    (if is_ctor then emit_void ISTORE [dst; val]
     else emit_void INVALID []) ∧  (* runtime: code is read-only *)
  (* Python raises CompilerPanic("cannot store to: CALLDATA").
     Emit INVALID instead of silent no-op. Unreachable for well-typed programs. *)
  compile_ptr_store is_ctor LocCalldata _ _ = emit_void INVALID []
End

(* ===== Memory Copy ===== *)

(* Copy memory region via MCOPY (Cancun+).
   Mirrors Python: context.py copy_memory *)
Definition compile_copy_memory_def:
  compile_copy_memory dst src 0 = return () ∧
  compile_copy_memory dst src size =
    emit_void MCOPY [dst; src; Lit (n2w size)]
End

(* Parameterized word-copy loop between two address spaces.
   Mirrors Python: context.py _word_copy_loop
   Used for storage↔memory and transient↔memory bulk copies. *)
Definition compile_word_copy_loop_def:
  compile_word_copy_loop src_op dst_op word_count load_loc store_loc is_ctor =
    let src_scale = word_scale load_loc in
    let dst_scale = word_scale store_loc in
    do
      (* Create blocks: cond, body, exit *)
      cond_lbl <- fresh_label "wcopy_cond";
      body_lbl <- fresh_label "wcopy_body";
      exit_lbl <- fresh_label "wcopy_exit";
      (* Initialize counter *)
      counter_var <- fresh_var;
      emit_inst ASSIGN [Lit 0w] [counter_var];
      emit_inst JMP [Label cond_lbl] [];
      (* Cond block *)
      new_block cond_lbl;
      done_op <- emit_op EQ [Var counter_var; Lit (n2w word_count)];
      emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
      (* Body block *)
      new_block body_lbl;
      (* Compute source offset *)
      src_off <- (if src_scale = 1 then
        emit_op ADD [src_op; Var counter_var]
      else do
        scaled <- emit_op MUL [Var counter_var; Lit (n2w src_scale)];
        emit_op ADD [src_op; scaled]
      od);
      (* Load from source *)
      val_loaded <- compile_ptr_load is_ctor load_loc src_off;
      (* Compute dest offset *)
      dst_off <- (if dst_scale = 1 then
        emit_op ADD [dst_op; Var counter_var]
      else do
        scaled <- emit_op MUL [Var counter_var; Lit (n2w dst_scale)];
        emit_op ADD [dst_op; scaled]
      od);
      (* Store to dest *)
      compile_ptr_store is_ctor store_loc dst_off val_loaded;
      (* Increment counter *)
      new_ctr <- emit_op ADD [Var counter_var; Lit 1w];
      emit_inst ASSIGN [new_ctr] [counter_var];
      emit_inst JMP [Label cond_lbl] [];
      (* Exit block *)
      new_block exit_lbl
    od
End

(* ===== Store Memory ===== *)
(* Store value to memory pointer.
   Mirrors Python: context.py store_memory
   Primitive word types: direct mstore.
   Complex types: memory copy (val is src ptr).
   Bytestring case handled separately in compile_store_bytestring.
   Callers must dispatch bytestrings to compile_store_bytestring. *)
(* Simple store memory (no typed copy). Used when src_typ = dst_typ.
   For layout-aware copy when src_typ ≠ dst_typ, see
   compile_store_memory_typed and compile_assign_value. *)
Definition compile_store_memory_def:
  compile_store_memory val_op dst_op is_prim_word mem_size =
    if is_prim_word then
      emit_void MSTORE [dst_op; val_op]
    else
      compile_copy_memory dst_op val_op mem_size
End

(* ===== Load from Storage/Transient to Memory ===== *)
(* Mirrors Python: context.py _load_storage_to_memory *)
Definition compile_storage_to_memory_def:
  compile_storage_to_memory slot buf word_count =
    compile_word_copy_loop slot buf word_count LocStorage LocMemory F
End

(* Mirrors Python: context.py _store_memory_to_storage *)
Definition compile_memory_to_storage_def:
  compile_memory_to_storage buf slot word_count =
    compile_word_copy_loop buf slot word_count LocMemory LocStorage F
End

(* Mirrors Python: context.py _load_transient_to_memory *)
Definition compile_transient_to_memory_def:
  compile_transient_to_memory slot buf word_count =
    compile_word_copy_loop slot buf word_count LocTransient LocMemory F
End

(* Mirrors Python: context.py _store_memory_to_transient *)
Definition compile_memory_to_transient_def:
  compile_memory_to_transient buf slot word_count =
    compile_word_copy_loop buf slot word_count LocMemory LocTransient F
End

(* ===== Allocate Buffer ===== *)
(* Allocate a fixed-capacity memory buffer with provenance tracking.
   Returns buffer in monad.
   buffer.buf_operand is the IR operand; buffer.buf_size is the allocation size.
   Use base_ptr buf for a LocatedValue with provenance.
   Mirrors Python: vyper/codegen_venom/context.py:Context.new_internal_variable *)
Definition compile_alloc_buffer_def:
  compile_alloc_buffer size =
    do op <- emit_op ALLOCA [Lit (n2w size)];
       return <| buf_operand := op; buf_size := size |>
    od
End

(* Runtime-sized allocation boundary.  The size is an SSA operand, so this
   returns only the allocated pointer rather than fabricating a static buffer
   capacity.  Mirrors Python:
   vyper/codegen_venom/context.py:Context.new_internal_variable. *)
Definition compile_alloc_dynamic_def:
  compile_alloc_dynamic (size_op:operand) = emit_op DALLOCA [size_op]
End

Theorem compile_alloc_dynamic_result:
  !(size_op:operand) (st:compile_state) (ptr:operand) (st':compile_state).
  compile_alloc_dynamic size_op st = (ptr, st') ==>
  ptr = Var ("%" ++ toString st.cs_next_var) /\
  st'.cs_next_id = st.cs_next_id + 1 /\
  st'.cs_next_var = st.cs_next_var + 1 /\
  st'.cs_current_insts =
    st.cs_current_insts ++
      [mk_inst st.cs_next_id DALLOCA [size_op]
         ["%" ++ toString st.cs_next_var]]
Proof
  simp[compile_alloc_dynamic_def, emit_op_def, fresh_id_def, fresh_var_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

(* Static allocation boundary.  Unlike compile_alloc_buffer, this exposes the
   instruction ID as a separate result so fixed-placement metadata is keyed by
   the emitted ALLOCA, never by its SSA output variable. *)
Definition compile_alloc_buffer_with_id_def:
  compile_alloc_buffer_with_id size =
    do id <- fresh_id;
       out <- fresh_var;
       emit (mk_inst id ALLOCA [Lit (n2w size)] [out]);
       return (id, <| buf_operand := Var out; buf_size := size |>)
    od
End

Theorem compile_alloc_buffer_with_id_result:
  !(size:num) (st:compile_state) (id:num) (buf:buffer) (st':compile_state).
  compile_alloc_buffer_with_id size st = ((id, buf), st') ==>
  id = st.cs_next_id /\
  buf.buf_operand = Var ("%" ++ toString st.cs_next_var) /\
  buf.buf_size = size /\
  st'.cs_next_id = st.cs_next_id + 1 /\
  st'.cs_next_var = st.cs_next_var + 1 /\
  st'.cs_current_insts =
    st.cs_current_insts ++
      [mk_inst st.cs_next_id ALLOCA [Lit (n2w size)]
         ["%" ++ toString st.cs_next_var]]
Proof
  simp[compile_alloc_buffer_with_id_def, fresh_id_def, fresh_var_def,
       emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]
QED

(* ===== Load/Store Storage ===== *)
(* Mirrors Python: context.py load_storage
   Primitive: sload directly.
   Complex: allocate buffer, copy from storage to memory. *)
Definition compile_load_storage_def:
  compile_load_storage slot is_prim_word word_count alloca_size =
    if is_prim_word then
      emit_op SLOAD [slot]
    else if word_count = 1 then
      do buf_op_alloc <- compile_alloc_buffer alloca_size;
         let buf_op = buf_op_alloc.buf_operand in
         do loaded <- emit_op SLOAD [slot];
            emit_void MSTORE [buf_op; loaded];
            return buf_op
         od
      od
    else
      do buf_op_alloc <- compile_alloc_buffer alloca_size;
         let buf_op = buf_op_alloc.buf_operand in
         do compile_storage_to_memory slot buf_op word_count;
            return buf_op
         od
      od
End

(* Mirrors Python: context.py store_storage *)
Definition compile_store_storage_def:
  compile_store_storage val slot is_prim_word word_count =
    if is_prim_word then
      emit_void SSTORE [slot; val]
    else if word_count = 1 then
      do loaded <- emit_op MLOAD [val];
         emit_void SSTORE [slot; loaded]
      od
    else
      do _ <- compile_memory_to_storage val slot word_count;
         return ()
      od
End

(* ===== Load/Store Transient ===== *)
Definition compile_load_transient_def:
  compile_load_transient slot is_prim_word word_count alloca_size =
    if is_prim_word then
      emit_op TLOAD [slot]
    else if word_count = 1 then
      do buf_op_alloc <- compile_alloc_buffer alloca_size;
         let buf_op = buf_op_alloc.buf_operand in
         do loaded <- emit_op TLOAD [slot];
            emit_void MSTORE [buf_op; loaded];
            return buf_op
         od
      od
    else
      do buf_op_alloc <- compile_alloc_buffer alloca_size;
         let buf_op = buf_op_alloc.buf_operand in
         do compile_transient_to_memory slot buf_op word_count;
            return buf_op
         od
      od
End

(* Mirrors Python: context.py code_to_memory
   Always uses DLOAD (reads from code section), never ILOAD.
   Python: code_to_memory always calls dload, even in ctor context.
   ILOAD is only used for single-word immutables in load_immutable_ctor. *)
Definition compile_code_to_memory_def:
  compile_code_to_memory (offset:operand) (dst:operand) (word_count:num) =
    if word_count = 0 then (return () : unit compiler)
    else
      do compile_word_copy_loop offset dst word_count LocCode LocMemory F;
         return ()
      od
End

(* ===== Load/Store Immutables ===== *)
(* Mirrors Python: context.py load_immutable
   is_ctor: T → ILOAD (ctor staging), F → DLOAD (deployed bytecode). *)
Definition compile_load_immutable_def:
  compile_load_immutable offset is_prim_word word_count alloca_size is_ctor =
    if is_prim_word then
      (if is_ctor then emit_op ILOAD [offset]
       else emit_op DLOAD [offset])
    else
      do buf_op_alloc <- compile_alloc_buffer alloca_size;
         let buf_op = buf_op_alloc.buf_operand in
         do compile_code_to_memory offset buf_op word_count;
            return buf_op
         od
      od
End

(* ===== Nonreentrant Lock ===== *)
(* Mirrors Python: context.py emit_nonreentrant_lock/unlock
   is_view: T for view functions — check lock but don't acquire it.
   Python: if func_t.mutability != VIEW: STORE(key, temp_value) *)
Definition compile_nonreentrant_lock_def:
  compile_nonreentrant_lock nkey use_transient is_view =
    if use_transient then
      do current <- emit_op TLOAD [Lit (n2w nkey)];
         locked <- emit_op EQ [current; Lit 1w];
         not_locked <- emit_op ISZERO [locked];
         emit_void ASSERT [not_locked];
         if is_view then return ()
         else emit_void TSTORE [Lit (n2w nkey); Lit 1w]
      od
    else
      do current <- emit_op SLOAD [Lit (n2w nkey)];
         locked <- emit_op EQ [current; Lit 2w];
         not_locked <- emit_op ISZERO [locked];
         emit_void ASSERT [not_locked];
         if is_view then return ()
         else emit_void SSTORE [Lit (n2w nkey); Lit 2w]
      od
End

(* Python: if func_t.mutability == VIEW: return (no unlock needed)
   is_view: T → no-op *)
Definition compile_nonreentrant_unlock_def:
  compile_nonreentrant_unlock nkey use_transient is_view =
    if is_view then return ()
    else if use_transient then
      emit_void TSTORE [Lit (n2w nkey); Lit 0w]
    else
      emit_void SSTORE [Lit (n2w nkey); Lit 3w]
End

(* ===== Zero Memory ===== *)
(* Mirrors Python: builtins/simple.py _zero_memory *)
(* Zero memory: emit MSTORE(ptr+i*32, 0) for each 32-byte word.
   i: current word index, words: total words to zero.
   Mirrors Python: context.py zero_memory *)
Definition compile_zero_memory_loop_def:
  compile_zero_memory_loop ptr_op i words =
    if i >= words then return ()
    else
      do dst <- (if i = 0 then return ptr_op
                 else emit_op ADD [ptr_op; Lit (n2w (i * 32))]);
         emit_void MSTORE [dst; Lit 0w];
         compile_zero_memory_loop ptr_op (i + 1) words
      od
Termination
  WF_REL_TAC `measure (λ(ptr,i,words). words - i)`
End

Definition compile_zero_memory_def:
  compile_zero_memory ptr_op 0 = return () ∧
  compile_zero_memory ptr_op size =
    let words = (size + 31) DIV 32 in
    compile_zero_memory_loop ptr_op 0 words
End

(* ===== Bytestring Operations ===== *)
(* Mirrors Python: context.py ensure_bytestring_in_memory,
   bytes_data_ptr, bytestring_length *)

(* Get data pointer from bytestring pointer: ptr + word_scale.
   Memory/None: +32 (byte-addressed). Storage/Transient: +1 (slot-addressed).
   Mirrors Python: context.py bytes_data_ptr *)
Definition compile_bytes_data_ptr_def:
  compile_bytes_data_ptr ptr_op loc =
    let scale = word_scale loc in
    emit_op ADD [ptr_op; Lit (n2w scale)]
End

(* Get bytestring length: dispatches on location.
   Mirrors Python: context.py bytestring_length *)
(* Load bytestring length from first slot at pointer.
   is_ctor needed for LocCode: ctor uses ILOAD, runtime uses DLOAD. *)
Definition compile_bytestring_length_def:
  compile_bytestring_length is_ctor ptr_op loc =
    compile_ptr_load is_ctor loc ptr_op
End

(* Ensure bytestring is in memory. If from storage/transient/code,
   copy to memory first. *)
(* Ensure a value is in memory. If already in memory, return ptr.
   Otherwise allocate buffer and copy from source location.
   mem_bytes: memory_bytes_required (allocation size).
   word_count: storage_size_in_words (number of 32-byte slots to copy).
   Mirrors Python: context.py ensure_in_memory *)
Definition compile_ensure_in_memory_def:
  compile_ensure_in_memory ptr_op loc mem_bytes word_count is_ctor =
    case loc of
      LocMemory => return ptr_op
    | LocStorage =>
        do buf_op_alloc <- compile_alloc_buffer (mem_bytes + 32);
           let buf_op = buf_op_alloc.buf_operand in
           do compile_storage_to_memory ptr_op buf_op word_count;
              return buf_op
           od
        od
    | LocTransient =>
        do buf_op_alloc <- compile_alloc_buffer (mem_bytes + 32);
           let buf_op = buf_op_alloc.buf_operand in
           do compile_transient_to_memory ptr_op buf_op word_count;
              return buf_op
           od
        od
    | LocCode =>
        (* Always DLOAD: code_to_memory reads from code section.
           Mirrors Python: ensure_bytestring_in_memory → code_to_memory → dload. *)
        do buf_op_alloc <- compile_alloc_buffer (mem_bytes + 32);
           let buf_op = buf_op_alloc.buf_operand in
           do compile_code_to_memory ptr_op buf_op word_count;
              return buf_op
           od
        od
    | LocCalldata =>
        (* Load actual length from calldata (ptr_op points to length word).
           Allocate buffer, copy length + data. mem_bytes is max size. *)
        do len_op <- emit_op CALLDATALOAD [ptr_op];
           buf_op_alloc <- compile_alloc_buffer (mem_bytes + 32);
           let buf_op = buf_op_alloc.buf_operand in
           do emit_void MSTORE [buf_op; len_op];
              data_ptr <- emit_op ADD [buf_op; Lit 32w];
              src_data <- emit_op ADD [ptr_op; Lit 32w];
              emit_void CALLDATACOPY [data_ptr; src_data; len_op];
              return buf_op
           od
        od
End

(* ===== Slot-to-Memory Copy ===== *)
(* Copy multi-slot data from storage/transient to memory.
   Used in iter loop for complex element types.
   Mirrors Python: context.py slot_to_memory *)
Definition compile_slot_to_memory_def:
  compile_slot_to_memory src_slot dst_ptr num_slots loc =
    compile_word_copy_loop src_slot dst_ptr num_slots loc LocMemory F
End

(* ===== Store Immutable ===== *)
(* Store multi-word value to immutable location during constructor.
   is_ctor=T because store_immutable only runs in constructor context.
   Mirrors Python: context.py store_immutable *)
Definition compile_store_immutable_def:
  compile_store_immutable src_ptr dst_offset num_words =
    compile_word_copy_loop src_ptr (Lit (n2w dst_offset)) num_words
      LocMemory LocCode T
End

(* ===== Dynamic Array to Storage Copy ===== *)
(* Copy only length + actual elements from memory to storage.
   Mirrors Python: stmt.py _copy_dynarray_to_storage *)
(* ===== Load Calldata ===== *)
(* Mirrors Python: context.py load_calldata *)
Definition compile_load_calldata_def:
  compile_load_calldata offset is_prim_word word_count alloca_size =
    if is_prim_word then
      emit_op CALLDATALOAD [offset]
    else if word_count = 1 then
      do buf_op_alloc <- compile_alloc_buffer alloca_size;
         let buf_op = buf_op_alloc.buf_operand in
         do loaded <- emit_op CALLDATALOAD [offset];
            emit_void MSTORE [buf_op; loaded];
            return buf_op
         od
      od
    else
      do buf_op_alloc <- compile_alloc_buffer alloca_size;
         let buf_op = buf_op_alloc.buf_operand in
         do (* calldatacopy from offset to buf, size bytes *)
            emit_void CALLDATACOPY [buf_op; offset; Lit (n2w alloca_size)];
            return buf_op
         od
      od
End

(* ===== Copy Memory Dynamic ===== *)
(* Mirrors Python: context.py copy_memory_dynamic *)
Definition compile_copy_memory_dynamic_def:
  compile_copy_memory_dynamic dst src length_op =
    emit_void MCOPY [dst; src; length_op]
End

(* NOTE: compile_load_by_loc deleted — duplicate of compile_ptr_load *)

(* ===== With Byte Offset ===== *)
(* Add byte offset to base pointer. Mirrors Python: context.py _with_byte_offset *)
Definition compile_with_byte_offset_def:
  compile_with_byte_offset base 0 = return base ∧
  compile_with_byte_offset base offset =
    emit_op ADD [base; Lit (n2w offset)]
End

(* ===== Store Memory for Bytestrings ===== *)
(* Compute 32 + ceil32(actual_length), the exact memory range occupied by an
   in-memory bytes/string value.  This boundary is also used by DRET lowering,
   which publishes the same source range without first copying it. *)
Definition compile_bytestring_copy_len_def:
  compile_bytestring_copy_len val_op =
    do src_len <- emit_op MLOAD [val_op];
       padded_len <- emit_op ADD [src_len; Lit 31w];
       let mask = i2w (- &32) : bytes32 in
       do rounded <- emit_op AND [padded_len; Lit mask];
          emit_op ADD [rounded; Lit 32w]
       od
    od
End

(* Copy bytestring to memory: copies 32 + ceil32(actual_length) bytes.
   Mirrors Python: context.py store_memory for _BytestringT.
   Placed before typed copy defs since they dispatch to it. *)
Definition compile_store_bytestring_def:
  compile_store_bytestring val_op dst_op =
    do copy_len <- compile_bytestring_copy_len val_op;
       emit_void MCOPY [dst_op; val_op; copy_len]
    od
End

(* ===== Layout-Aware Memory Copy ===== *)
(* Copy between memory regions where source and destination types may have
   different memory layouts. For example, DynArray[Bytes[540]] (elem=572B)
   → DynArray[Bytes[704]] (elem=736B) needs per-element bytestring copy.
   Mirrors Python: context.py _store_memory_typed *)

(* ===== Mutually Recursive Typed Copy ===== *)
(* compile_store_memory_typed dispatches by type structure:
     TupleT → compile_typed_copy_fields (per-field, recursive)
     SArrayT → compile_copy_sarray_typed (fast batch or per-element loop)
     DynArrayT → compile_copy_dynarray_typed (length check + per-element loop)
     StructT → compile_struct_typed_copy (per-field by name, recursive)
   All dispatch functions RECURSE into compile_store_memory_typed.
   Terminates because sub-type depth strictly decreases (requires
   well_formed_sft acyclicity for struct recursion through cenv).
   Mirrors Python: context.py _store_memory_typed (recursive) *)
val compile_store_memory_typed_defn = Defn.Hol_defn "compile_store_memory_typed" `
  (* Top-level dispatch *)
  compile_store_memory_typed cenv dst dst_ty src src_ty =
    (if is_word_type dst_ty then
      do val_op <- emit_op MLOAD [src];
         emit_void MSTORE [dst; val_op]
      od
    else if is_bytestring_type dst_ty ∧ is_bytestring_type src_ty then
      compile_store_bytestring src dst
    else
      case (dst_ty, src_ty) of
        (ArrayT dst_elem (Dynamic dst_cap), ArrayT src_elem (Dynamic _)) =>
          compile_copy_dynarray_typed cenv dst dst_elem dst_cap src src_elem
      | (ArrayT dst_elem (Fixed n), ArrayT src_elem (Fixed _)) =>
          compile_copy_sarray_typed cenv dst dst_elem src src_elem n
      | (TupleT dst_tys, TupleT src_tys) =>
          compile_typed_copy_fields cenv dst src dst_tys src_tys 0 0
      | (StructT dst_nsid, StructT src_nsid) =>
          let dst_fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string dst_nsid) in
          let src_fields = get_struct_fields cenv.ce_struct_fields (nsid_to_string src_nsid) in
          compile_struct_typed_copy cenv
            dst src dst_fields src_fields 0 0
      | _ =>
          compile_copy_memory dst src (type_memory_bytes cenv dst_ty)) ∧

  (* Tuple/struct per-field copy: recursive per-field.
     Mirrors Python: _store_memory_typed TupleT branch. *)
  compile_typed_copy_fields cenv dst src [] (src_tys : type list)
                            dst_off src_off = return () ∧
  compile_typed_copy_fields cenv dst src (dst_ty::dst_rest) []
                            dst_off src_off = return () ∧
  compile_typed_copy_fields cenv dst src (dst_ty::dst_rest) (src_ty::src_rest)
                            dst_off src_off =
    (do dst_ptr <- compile_with_byte_offset dst dst_off;
        src_ptr <- compile_with_byte_offset src src_off;
        let dst_sz = type_memory_bytes cenv dst_ty in
        let src_sz = type_memory_bytes cenv src_ty in
        do (* Recurse into compile_store_memory_typed for full type-aware copy *)
           compile_store_memory_typed cenv dst_ptr dst_ty src_ptr src_ty;
           compile_typed_copy_fields cenv dst src dst_rest src_rest
                               (dst_off + dst_sz) (src_off + src_sz)
        od
     od) ∧

  (* SArray typed copy: fast path or per-element loop.
     Mirrors Python: context.py _copy_sarray_memory_typed *)
  compile_copy_sarray_typed cenv dst dst_elem_ty src src_elem_ty count =
    (let dst_elem_sz = type_memory_bytes cenv dst_elem_ty in
    let src_elem_sz = type_memory_bytes cenv src_elem_ty in
    if dst_elem_sz = src_elem_sz ∧ ¬is_abi_dynamic cenv.ce_struct_fields dst_elem_ty then
      compile_copy_memory dst src (count * dst_elem_sz)
    else
      do cond_lbl <- fresh_label "typed_sa_cond";
         body_lbl <- fresh_label "typed_sa_body";
         exit_lbl <- fresh_label "typed_sa_exit";
         counter <- fresh_var;
         emit_inst ASSIGN [Lit 0w] [counter];
         emit_inst JMP [Label cond_lbl] [];
         new_block cond_lbl;
         lt_op <- emit_op LT [Var counter; Lit (n2w count)];
         done_op <- emit_op ISZERO [lt_op];
         emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
         new_block body_lbl;
         src_off <- emit_op MUL [Var counter; Lit (n2w src_elem_sz)];
         dst_off <- emit_op MUL [Var counter; Lit (n2w dst_elem_sz)];
         src_elem <- emit_op ADD [src; src_off];
         dst_elem <- emit_op ADD [dst; dst_off];
         (* Recurse on element type for full type-aware copy *)
         compile_store_memory_typed cenv dst_elem dst_elem_ty src_elem src_elem_ty;
         new_ctr <- emit_op ADD [Var counter; Lit 1w];
         emit_inst ASSIGN [new_ctr] [counter];
         emit_inst JMP [Label cond_lbl] [];
         _ <- new_block exit_lbl;
         return ()
      od) ∧

  (* DynArray typed copy: length + capacity check + per-element loop.
     Mirrors Python: context.py _copy_dynarray_memory_typed *)
  compile_copy_dynarray_typed cenv dst dst_elem_ty dst_capacity
                              src src_elem_ty =
    (let dst_elem_sz = type_memory_bytes cenv dst_elem_ty in
    let src_elem_sz = type_memory_bytes cenv src_elem_ty in
    do length <- emit_op MLOAD [src];
       too_long <- emit_op GT [length; Lit (n2w dst_capacity)];
       ok <- emit_op ISZERO [too_long];
       emit_void ASSERT [ok];
       emit_void MSTORE [dst; length];
       src_data <- emit_op ADD [src; Lit 32w];
       dst_data <- emit_op ADD [dst; Lit 32w];
       if dst_elem_sz = src_elem_sz ∧ dst_elem_ty = src_elem_ty then
         do data_sz <- emit_op MUL [length; Lit (n2w dst_elem_sz)];
            compile_copy_memory_dynamic dst_data src_data data_sz
         od
       else
         do cond_lbl <- fresh_label "typed_dyn_cond";
            body_lbl <- fresh_label "typed_dyn_body";
            exit_lbl <- fresh_label "typed_dyn_exit";
            counter <- fresh_var;
            emit_inst ASSIGN [Lit 0w] [counter];
            emit_inst JMP [Label cond_lbl] [];
            new_block cond_lbl;
            lt_op <- emit_op LT [Var counter; length];
            done_op <- emit_op ISZERO [lt_op];
            emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
            new_block body_lbl;
            src_off <- emit_op MUL [Var counter; Lit (n2w src_elem_sz)];
            dst_off <- emit_op MUL [Var counter; Lit (n2w dst_elem_sz)];
            src_elem <- emit_op ADD [src_data; src_off];
            dst_elem <- emit_op ADD [dst_data; dst_off];
            (* Recurse on element type for full type-aware copy *)
            compile_store_memory_typed cenv dst_elem dst_elem_ty src_elem src_elem_ty;
            new_ctr <- emit_op ADD [Var counter; Lit 1w];
            emit_inst ASSIGN [new_ctr] [counter];
            emit_inst JMP [Label cond_lbl] [];
            _ <- new_block exit_lbl;
            return ()
         od
    od) ∧

  (* Struct per-field copy: per-field by name, fully recursive.
     Each field recurses into compile_store_memory_typed for layout-aware copy.
     Mirrors Python: _store_memory_typed StructT branch. *)
  compile_struct_typed_copy cenv dst src [] src_fields
                            dst_off src_off = return () ∧
  compile_struct_typed_copy cenv dst src ((name, dst_fty, dst_sz)::dst_rest)
                            src_fields dst_off src_off =
    (let (src_fty, src_sz) = (case ALOOKUP src_fields name of
                                SOME (ft, sz) => (ft, sz)
                              | NONE => (dst_fty, dst_sz)) in
     do dst_ptr <- compile_with_byte_offset dst dst_off;
        src_ptr <- compile_with_byte_offset src src_off;
        (* Recurse into compile_store_memory_typed for full type-aware copy *)
        compile_store_memory_typed cenv dst_ptr dst_fty src_ptr src_fty;
        compile_struct_typed_copy cenv dst src dst_rest src_fields
                               (dst_off + dst_sz) (src_off + src_sz)
     od)
`;

(* Termination: struct recursion through cenv.ce_struct_fields requires
   well_formed_sft (acyclic struct graph). Same root cause as the 3
   compileEnv termination cheats. Provable with struct_type_depth measure. *)
val _ = Defn.save_defn compile_store_memory_typed_defn;

(* NOTE: compile_store_complex_type and compile_copy_complex_type deleted —
   dead code. Actual callers use compile_word_copy_loop / compile_ptr_load
   directly with explicit is_ctor from cenv.ce_is_ctor. *)

(* ===== Encode Log Topic ===== *)
(* Mirrors Python: stmt.py _encode_log_topic
   Primitive words: use directly. Bytestrings: keccak256 hash. *)
Definition compile_encode_log_topic_def:
  compile_encode_log_topic val_op is_bytestring =
    if is_bytestring then
      do data_ptr <- emit_op ADD [val_op; Lit 32w];
         length <- emit_op MLOAD [val_op];
         emit_op SHA3 [data_ptr; length]
      od
    else
      return val_op
End

(* compile_store_bytestring moved before typed copy defs (forward ref) *)

(* ===== Load Memory ===== *)
(* Pinned convention (VYPER_PIN cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c;
   introduced by vyperlang/vyper@61507a045f34ab8ee5776de04c5b40ee1d1310e4,
   vyper/codegen_venom/context.py:VenomCodegenContext.load_memory): MLOAD
   primitive words and complex values whose memory representation is exactly
   one 32-byte word; retain a pointer for larger complex values. *)
Definition compile_load_memory_def:
  compile_load_memory ptr_op is_prim_word mem_size =
    if is_prim_word \/ mem_size = 32 then
      emit_op MLOAD [ptr_op]
    else
      return ptr_op
End

(* ===== Store Transient ===== *)
(* Full store_transient: primitive vs complex.
   Mirrors Python: context.py store_transient *)
Definition compile_store_transient_def:
  compile_store_transient val slot is_prim_word word_count =
    if is_prim_word then
      emit_void TSTORE [slot; val]
    else if word_count = 1 then
      do loaded <- emit_op MLOAD [val];
         emit_void TSTORE [slot; loaded]
      od
    else
      do _ <- compile_memory_to_transient val slot word_count;
         return ()
      od
End

Definition compile_dynarray_to_storage_def:
  compile_dynarray_to_storage src_ptr dst_slot elem_words elem_mem_size transient =
    do (* Load length *)
       len_op <- emit_op MLOAD [src_ptr];
       (* Create loop blocks *)
       cond_lbl <- fresh_label "dyn_cond";
       body_lbl <- fresh_label "dyn_body";
       exit_lbl <- fresh_label "dyn_exit";
       (* Entry: counter = 0 *)
       counter <- fresh_var;
       emit_inst ASSIGN [Lit 0w] [counter];
       emit_inst JMP [Label cond_lbl] [];
       (* Cond: counter < length *)
       new_block cond_lbl;
       lt_op <- emit_op LT [Var counter; len_op];
       done_op <- emit_op ISZERO [lt_op];
       emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
       (* Body: copy one element *)
       new_block body_lbl;
       if elem_words = 1 then
         (* Simple case: single word per element.
            src_offset = 32 + counter * 32, dst = dst_slot + 1 + counter *)
         do mul_op <- emit_op MUL [Var counter; Lit 32w];
            src_off <- emit_op ADD [Lit 32w; mul_op];
            src_elem <- emit_op ADD [src_ptr; src_off];
            val_op <- emit_op MLOAD [src_elem];
            slot_off <- emit_op ADD [Var counter; Lit 1w];
            dst_elem <- emit_op ADD [dst_slot; slot_off];
            (if transient then emit_void TSTORE [dst_elem; val_op]
             else emit_void SSTORE [dst_elem; val_op]);
            (* Increment counter *)
            new_ctr <- emit_op ADD [Var counter; Lit 1w];
            emit_inst ASSIGN [new_ctr] [counter];
            emit_inst JMP [Label cond_lbl] [];
            (* Exit: store length *)
            new_block exit_lbl;
            (if transient then emit_void TSTORE [dst_slot; len_op]
             else emit_void SSTORE [dst_slot; len_op])
         od
       else
         (* Multi-word elements: src_offset = 32 + counter * elem_mem_size,
            dst_slot_i = dst_slot + 1 + counter * elem_words.
            Uses word_copy_loop for each element.
            Mirrors Python: stmt.py _copy_dynarray_to_storage complex case *)
         do mul_op <- emit_op MUL [Var counter; Lit (n2w elem_mem_size)];
            src_off <- emit_op ADD [Lit 32w; mul_op];
            src_elem <- emit_op ADD [src_ptr; src_off];
            slot_mul <- emit_op MUL [Var counter; Lit (n2w elem_words)];
            slot_off <- emit_op ADD [Lit 1w; slot_mul];
            dst_elem <- emit_op ADD [dst_slot; slot_off];
            compile_word_copy_loop src_elem dst_elem elem_words
                         LocMemory (if transient then LocTransient else LocStorage)
                         F;
            (* Increment counter *)
            new_ctr <- emit_op ADD [Var counter; Lit 1w];
            emit_inst ASSIGN [new_ctr] [counter];
            emit_inst JMP [Label cond_lbl] [];
            (* Exit: store length *)
            new_block exit_lbl;
            (if transient then emit_void TSTORE [dst_slot; len_op]
             else emit_void SSTORE [dst_slot; len_op])
         od
    od
End

(* Helper: ILOAD word-by-word to memory buffer (ctor, no immutables_alloca).
   Python: load_immutable_ctor without alloca uses iload per word.
   Can't use compile_word_copy_loop because LocCode dispatches to DLOAD. *)
Definition compile_iload_to_memory_def:
  compile_iload_to_memory src_offset dst_buf 0 = return () ∧
  compile_iload_to_memory src_offset dst_buf (SUC n) =
    let byte_off = n * 32 in
    do imm_off <- emit_op ADD [src_offset; Lit (n2w byte_off)];
       word_op <- emit_op ILOAD [imm_off];
       mem_ptr <- emit_op ADD [dst_buf; Lit (n2w byte_off)];
       emit_void MSTORE [mem_ptr; word_op];
       compile_iload_to_memory src_offset dst_buf n
    od
End

(* Helper: copy from ADD-based source to memory buffer, word by word.
   Mirrors the loop in Python load_immutable_ctor for complex types. *)
Definition compile_gep_to_memory_def:
  compile_gep_to_memory src_base src_offset dst_buf 0 = return () ∧
  compile_gep_to_memory src_base src_offset dst_buf (SUC n) =
    let byte_off_val = n * 32 in
    do imm_off <- emit_op ADD [src_offset; Lit (n2w byte_off_val)];
       ptr <- emit_op ADD [src_base; imm_off];
       word_op <- emit_op MLOAD [ptr];
       mem_ptr <- emit_op ADD [dst_buf; Lit (n2w byte_off_val)];
       emit_void MSTORE [mem_ptr; word_op];
       compile_gep_to_memory src_base src_offset dst_buf n
    od
End

(* ===== Load Immutable (Constructor) ===== *)
(* Mirrors Python: context.py load_immutable_ctor
   During constructor, immutables live in an alloca'd buffer.
   If immutables_alloca is available, use ADD + MLOAD.
   Otherwise, fall back to ILOAD (same as runtime).
   NOTE: Currently unused — will be wired in when constructor immutable
   loading is added to compile_expr. The SOME imm_alloca (ADD) path
   has no direct Python equivalent; Python always uses iload/dload. *)
Definition compile_load_immutable_ctor_def:
  compile_load_immutable_ctor offset is_prim_word word_count alloca_size
                              imm_alloca_opt =
    case imm_alloca_opt of
      NONE =>
        (* No immutables_alloca: use ILOAD (ctor pseudo-instruction).
           Python: load_immutable_ctor without alloca uses iload, NOT dload.
           DLOAD reads deployed CODE — doesn't exist during constructor. *)
        if is_prim_word then
          emit_op ILOAD [offset]
        else
          do buf_op_alloc <- compile_alloc_buffer alloca_size;
             let buf_op = buf_op_alloc.buf_operand in
             do (* Use iload_to_memory — word_copy_loop with LocCode uses DLOAD *)
                compile_iload_to_memory offset buf_op word_count;
                return buf_op
             od
          od
    | SOME imm_alloca =>
      if is_prim_word then
        do ptr <- emit_op ADD [imm_alloca; offset];
           emit_op MLOAD [ptr]
        od
      else
        do buf_op_alloc <- compile_alloc_buffer alloca_size;
           let buf_op = buf_op_alloc.buf_operand in
           do compile_gep_to_memory imm_alloca offset buf_op word_count;
              return buf_op
           od
        od
End
