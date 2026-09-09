(*
 * Statement Lowering: Vyper statements → Venom IR instructions
 *
 * TOP-LEVEL:
 *   compile_stmt       — compile a single statement
 *   compile_stmts      — compile a list of statements
 *
 * Helper:
 *   compile_if         — if/else multi-block control flow
 *   compile_for_range  — for-range loop (5-block CFG)
 *   compile_assert     — assertion with revert
 *   compile_return     — return value or stop
 *
 * Mirrors Python codegen: vyper/codegen_venom/stmt.py:Stmt
 * Phase 1 scope: primitive types only (uint256, int256, int128, bool, address, bytes32)
 *)

Theory stmtLowering
Ancestors
  exprLowering context compileEnv venomInst abiEncoder dretShapeDefs
Libs
  monadsyntax

(* ===== Target Compilation ===== *)

(* ===== Statement Compilation ===== *)

(* Loop context: tracks break/continue targets *)
Datatype:
  loop_ctx =
    NoLoop
  | InLoop string string   (* break_label, continue_label *)
End

(* ===== Log args: evaluate all exprs first, then split ===== *)
(* CRITICAL: All log args must be evaluated in AST order first, then split
   into indexed (topics) and non-indexed (data). This matches Python which
   evaluates all args before splitting. *)

(* Evaluate all log arg expressions in AST order.
   Returns list of (operand, type) pairs preserving AST order. *)
Definition compile_log_eval_all_def:
  compile_log_eval_all cenv [] = return ([] : (operand # type) list) ∧
  compile_log_eval_all cenv (e::es) =
    (let arg_ty = expr_type e in
     do v <- lower_value compile_expr cenv arg_ty e;
        rest <- compile_log_eval_all cenv es;
        return ((v, arg_ty) :: rest)
     od)
Termination
  WF_REL_TAC `measure (λ(cenv,es). LENGTH es)`
End

(* Split already-evaluated operands into indexed topics and non-indexed data.
   indexed_flags: bool list parallel to evaluated ops. *)
Definition split_log_ops_def:
  split_log_ops [] [] = ([] : (operand # bool) list,
                          [] : (operand # type) list) ∧
  split_log_ops ((op, ty) :: rest) (T :: flags) =
    (let (topics, data) = split_log_ops rest flags in
     let is_bs = is_bytestring_type ty in
     ((op, is_bs) :: topics, data)) ∧
  split_log_ops ((op, ty) :: rest) (F :: flags) =
    (let (topics, data) = split_log_ops rest flags in
     (topics, (op, ty) :: data)) ∧
  split_log_ops _ _ = ([], [])
End

(* Hash indexed topic operands (bytestrings need keccak256).
   Input: list of (operand, is_bytestring) *)
Definition compile_log_topic_ops_def:
  compile_log_topic_ops [] = return ([] : operand list) ∧
  compile_log_topic_ops (x :: rest) =
    do topic_op <- compile_encode_log_topic (FST x) (SND x);
       rest_ops <- compile_log_topic_ops rest;
       return (topic_op :: rest_ops)
    od
Termination
  WF_REL_TAC `measure (λops. LENGTH ops)`
End

(* Store already-evaluated data operands to buffer.
   Input: list of (operand, type) *)
Definition compile_log_store_data_def:
  compile_log_store_data cenv [] buf_op offset = return () ∧
  compile_log_store_data cenv (x :: rest) buf_op offset =
    (let v = FST x in let arg_ty = SND x in
     let mem_size = type_memory_bytes cenv arg_ty in
     let is_prim = is_word_type arg_ty in
     do dst <- (if offset = 0 then return buf_op
                else emit_op ADD [buf_op; Lit (n2w offset)]);
        (if is_prim then emit_void MSTORE [dst; v]
         else if is_bytestring_type arg_ty then
           compile_store_bytestring v dst
         else emit_void MCOPY [dst; v; Lit (n2w mem_size)]);
        compile_log_store_data cenv rest buf_op (offset + mem_size)
     od)
Termination
  WF_REL_TAC `measure (λ(cenv,ops,buf,off). LENGTH ops)`
End

(* Extract target name as string for metadata lookup *)
Definition target_to_string_def:
  target_to_string (NameTarget id) = id ∧
  target_to_string (TopLevelNameTarget nsid) = nsid_to_string nsid ∧
  target_to_string (SubscriptTarget bt _) = target_to_string bt ∧
  target_to_string (AttributeTarget bt _) = target_to_string bt
End

(* Convert assignment target to expression for location inference *)
Definition target_to_expr_def:
  target_to_expr (NameTarget id) = Name NoneT id ∧
  target_to_expr (TopLevelNameTarget nsid) =
    TopLevelName NoneT nsid ∧
  target_to_expr (SubscriptTarget bt idx) =
    Subscript NoneT (target_to_expr bt) idx ∧
  target_to_expr (AttributeTarget bt fld) =
    Attribute NoneT (target_to_expr bt) fld
End

(* ===== Revert with Reason ===== *)
(* Emit revert with Error(string) encoding.
   Error(string) selector: 0x08c379a0
   Buffer layout: buf+0: selector word, buf+32: ABI-encoded (string,) tuple.
   Final revert from buf+28 with length 4 + encoded_len.
   Mirrors Python: vyper/codegen_venom/stmt.py:_revert_with_reason *)
  (* KNOWN LIMITATION: Manual ABI encoding. Assumes msg_op is a memory pointer
     to [length][data] layout (correct for in-memory string literals).
     Python uses abi_encode_to_buf which handles storage/transient unwrap.
     Vyper only allows string literals as assert/revert reasons, so this is
     correct in practice. *)
(* Revert with Error(string) encoding using shared ABI encoder.
   Wraps message in TupleT((msg_typ,)) and uses compile_abi_encode_to_buf.
   Mirrors Python: vyper/codegen_venom/stmt.py:_revert_with_reason.
   msg_op: pointer to message in memory.
   msg_type: type of the message (usually StringT).
   msg_enc_info: ABI encoding info for the message type. *)
Definition compile_revert_with_reason_def:
  compile_revert_with_reason cenv msg_op msg_type msg_mem_size =
    (* Wrap message type as tuple: (msg_type,) for ABI encoding.
       Mirrors Python: wrapped_typ = TupleT((msg_typ,)) *)
    let wrapped_type = TupleT [msg_type] in
    let wrapped_enc_info = type_to_abi_enc_info cenv.ce_struct_fields cenv wrapped_type in
    let wrapped_abi_size = abi_size_bound cenv.ce_struct_fields wrapped_type in
    (* Allocate buffer: 32 (selector word) + encoded payload *)
    let buf_size = 32 + wrapped_abi_size in
    do buf_op_alloc <- compile_alloc_buffer buf_size;
       buf_op <- return buf_op_alloc.buf_operand;
       (* Store Error(string) selector at buf: 0x08c379a0 *)
       emit_void MSTORE [buf_op; Lit (0x08c379a0w : bytes32)];
       (* Payload starts at buf + 32 *)
       payload_buf <- emit_op ADD [buf_op; Lit 32w];
       (* Store message pointer into a tuple buffer (single-element tuple) *)
       tuple_buf_alloc <- compile_alloc_buffer msg_mem_size;
       tuple_buf <- return tuple_buf_alloc.buf_operand;
       compile_copy_memory tuple_buf msg_op msg_mem_size;
       (* ABI encode the wrapped tuple to payload buffer *)
       encoded_len <-
         compile_abi_encode_to_buf payload_buf tuple_buf wrapped_enc_info;
       (* Revert from buf+28 (selector at bytes 0-3) with length 4 + encoded_len *)
       revert_offset <- emit_op ADD [buf_op; Lit 28w];
       revert_len <- emit_op ADD [Lit 4w; encoded_len];
       emit_inst REVERT [revert_offset; revert_len] []
    od
End

(* ===== Internal Return ===== *)
(* Pinned frontend convention (VYPER_PIN cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c,
   vyper/codegen_venom/stmt.py:_lower_internal_return): ordinary RET operands
   are the user values followed by the separate return PC.  A dynamic DRET is
   [Lit dynamic_count] ++ ordinary values ++ flattened (pointer,size) pairs in
   source order ++ [return_pc], with dynamic_count > 0.  The count and return
   PC are raw control operands, not user return values.  DRET lowering copies
   the dynamic ranges with MCOPY, so the resolved frontend policy must reject a
   target without CapMcopy before this raw form is emitted.

   returns_count: number of stack-returned user values.
   return_pc: operand holding the separate return address.
   return_buf: SOME ptr for memory return, NONE otherwise. *)
(* ===== Load Tuple Elements for Stack Return ===== *)
(* Load n elements from a memory pointer, each at 32-byte intervals.
   Returns list of loaded operands.
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_internal_return tuple case *)
(* Load tuple elements from memory. Returns list of operands.
   Uses type_memory_bytes per element for proper stride.
   For word types: MLOAD the value.
   For complex types: computes pointer (base + offset).
   Python: offset += elem_typ.memory_bytes_required per element.
   NOTE: returns_stack_count guarantees ≤ MAX_STACK_RETURNS and all word,
   so for stack-returned tuples all elements are word-type. Complex elements
   always use memory return (returns_count = 0). *)
Definition compile_load_tuple_elements_def:
  compile_load_tuple_elements cenv base_op [] offset = return [] ∧
  compile_load_tuple_elements cenv base_op (ty :: tys) offset =
    (let elem_size = type_memory_bytes cenv ty in
     do elem_ptr <-
          (if offset = 0 then return base_op
           else emit_op ADD [base_op; Lit (n2w offset)]);
        val_op <- emit_op MLOAD [elem_ptr];
        rest <- compile_load_tuple_elements cenv base_op tys
                  (offset + elem_size);
        return (val_op :: rest)
     od)
End

Definition mk_dret_operands_def:
  mk_dret_operands (ordinary : operand list)
                   (dynamic : (operand # operand) list) return_pc =
    if 0 < LENGTH dynamic /\ LENGTH dynamic < dimword(:256) then
      SOME (Lit (n2w (LENGTH dynamic)) ::
            ordinary ++
            FLAT (MAP (\p. [FST p; SND p]) dynamic) ++
            [return_pc])
    else NONE
End

Theorem mk_dret_dynamic_payload_length:
  LENGTH (FLAT (MAP (\p. [FST p; SND p]) dynamic)) =
  2 * LENGTH dynamic
Proof
  Induct_on `dynamic` >> simp[]
QED

Theorem mk_dret_operands_parse:
  mk_dret_operands ordinary dynamic return_pc = SOME ops ==>
  parse_dret_shape (mk_inst id DRET ops outs) =
    SOME (LENGTH ordinary, LENGTH dynamic)
Proof
  simp[mk_dret_operands_def, parse_dret_shape_def, mk_inst_def,
       mk_dret_dynamic_payload_length] >>
  strip_tac >> gvs[] >>
  simp[mk_dret_dynamic_payload_length]
QED

Theorem mk_dret_operands_zero[simp]:
  mk_dret_operands ordinary [] return_pc = NONE
Proof
  simp[mk_dret_operands_def]
QED

Theorem mk_dret_operands_overflow:
  dimword(:256) <= LENGTH dynamic ==>
  mk_dret_operands ordinary dynamic return_pc = NONE
Proof
  simp[mk_dret_operands_def]
QED
Definition compile_mcopy_guard_def:
  compile_mcopy_guard cenv (supported : unit compiler) =
    if cenv.ce_target CapMcopy then supported
    else emit_inst INVALID [] []
End

Theorem compile_mcopy_guard_supported[simp]:
  cenv.ce_target CapMcopy ==>
  compile_mcopy_guard cenv supported = supported
Proof
  simp[compile_mcopy_guard_def]
QED

Theorem compile_mcopy_guard_unsupported[simp]:
  ~cenv.ce_target CapMcopy ==>
  compile_mcopy_guard cenv supported = emit_inst INVALID [] []
Proof
  simp[compile_mcopy_guard_def]
QED

Definition compile_internal_return_def:
  compile_internal_return cenv ret_val return_pc returns_count
                          ret_type src_type elem_types return_buf =
    if returns_count > 0 then
      (* Stack return: pass ret_val(s) on stack *)
      case ret_val of
        NONE => emit_inst RET [return_pc] []
      | SOME val_op =>
          if returns_count = 1 then
            (* Single value: RET val, return_pc *)
            emit_inst RET [val_op; return_pc] []
          else
            (* Tuple/struct: load each element from memory, pass all on stack.
               NOTE: returns_count > 1 only for TupleT with all word types
               (from returns_stack_count), so all elements are 32 bytes. *)
            do elems <- compile_load_tuple_elements cenv val_op
                          elem_types 0;
               emit_inst RET (elems ++ [return_pc]) []
            od
    else if is_abi_dynamic cenv.ce_struct_fields ret_type then
      (* At this boundary only a top-level bytes/string has one directly
         representable dynamic source range.  Nested dynamic layouts are
         rejected rather than being emitted with a malformed envelope. *)
      case (return_buf, ret_val) of
        (SOME buf_op, SOME val_op) =>
          if is_bytestring_type ret_type /\
             is_bytestring_type src_type then
            (* The guard surrounds the complete size/DRET computation, so an
               unsupported target emits INVALID before any MCOPY-dependent
               raw behavior. *)
            compile_mcopy_guard cenv
              (do copy_len <- compile_bytestring_copy_len val_op;
                  (case mk_dret_operands [] [(val_op, copy_len)] return_pc of
                     SOME ops => emit_inst DRET ops []
                   | NONE => emit_inst INVALID [] [])
               od)
          else emit_inst INVALID [] []
      | _ => emit_inst INVALID [] []
    else
      case return_buf of
        SOME buf_op =>
          (case ret_val of
             NONE => emit_inst RET [return_pc] []
           | SOME val_op =>
               (* Fixed-size memory return: retain the ordinary buffered RET
                  path. *)
               do compile_store_memory_typed cenv buf_op ret_type
                                             val_op src_type;
                  emit_inst RET [return_pc] []
               od)
      | NONE => emit_inst RET [return_pc] []
End

(* ===== External Return ===== *)
(* Lower external function return with ABI encoding.
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_external_return *)
Definition compile_external_return_def:
  compile_external_return ret_val is_prim_word is_raw_return
                          (ret_enc_info:abi_enc_info)
                          max_return_size is_nonreentrant nkey use_transient is_view =
    (* Nonreentrant unlock (view functions skip) *)
    do (if is_nonreentrant then compile_nonreentrant_unlock nkey use_transient is_view
        else return ());
       (case ret_val of
          NONE => emit_inst STOP [] []
        | SOME val_op =>
            if is_raw_return then
              (* Raw return: val is ptr to [length][data] *)
              do return_len <- emit_op MLOAD [val_op];
                 return_offset <- emit_op ADD [val_op; Lit 32w];
                 emit_inst RETURN [return_offset; return_len] []
              od
            else if is_prim_word then
              (* Primitive word: direct mstore + return 32 bytes *)
              do buf_op_alloc <- compile_alloc_buffer 32;
                 buf_op <- return buf_op_alloc.buf_operand;
                 emit_void MSTORE [buf_op; val_op];
                 emit_inst RETURN [buf_op; Lit 32w] []
              od
            else
              (* Complex: ABI encode to buffer, RETURN encoded_len bytes.
                 Mirrors Python: vyper/codegen_venom/stmt.py:lower_Return → vyper/codegen_venom/context.py:Context.return_external
                 Uses compile_abi_encode_to_buf for proper ABI encoding. *)
              do buf_op_alloc <- compile_alloc_buffer max_return_size;
                 buf_op <- return buf_op_alloc.buf_operand;
                 encoded_len <-
                   compile_abi_encode_to_buf buf_op val_op ret_enc_info;
                 emit_inst RETURN [buf_op; encoded_len] []
              od)
    od
End

(* ===== Get Target Ptr ===== *)
(* Full target pointer dispatch for assignments.
   Mirrors Python: vyper/codegen_venom/stmt.py:_get_target_ptr
   Returns (operand, data_location option, type option).
   The type is threaded through for nested access (SubscriptTarget,
   AttributeTarget) to correctly resolve element/field types. *)
Definition compile_get_target_ptr_def:
  (* Name target: local variable in memory *)
  compile_get_target_ptr cenv (NameTarget id) =
    (case FLOOKUP cenv.ce_vars id of
       SOME (MemLoc offset _) =>
         return (Lit (n2w offset), SOME LocMemory, cenv.ce_var_type id)
     | SOME (PtrVar ptr_op _) =>
         return (ptr_op, SOME LocMemory, cenv.ce_var_type id)
     | SOME (ImmutableLoc offset) =>
         return (Lit (n2w offset), SOME LocCode, cenv.ce_var_type id)
     | _ => return (Lit 0w, NONE, NONE)) ∧
  (* TopLevelName: storage, transient, or immutable variable *)
  compile_get_target_ptr cenv (TopLevelNameTarget nsid) =
    (let name = nsid_to_string nsid in
     case FLOOKUP cenv.ce_vars name of
       SOME (StorageLoc slot) =>
         return (Lit slot, SOME LocStorage, cenv.ce_var_type name)
     | SOME (TransientLoc slot) =>
         return (Lit slot, SOME LocTransient, cenv.ce_var_type name)
     | SOME (ImmutableLoc offset) =>
         return (Lit (n2w offset), SOME LocCode, cenv.ce_var_type name)
     | _ => return (Lit 0w, NONE, NONE)) ∧
  (* Subscript target: compute element pointer from base + index.
     Uses compile_array_subscript for location-aware access.
     Mirrors Python: _get_target_ptr → Expr(target).lower().ptr()
     Uses base_type from recursive call instead of root variable lookup. *)
  compile_get_target_ptr cenv (SubscriptTarget bt idx_e) =
    (let var_name = target_to_string bt in
     (* HashMap dispatch: uses compile_mapping_subscript for keccak256 slot.
        Mirrors Python: Expr(target, self.ctx).lower().ptr() which goes
        through compile_subscript → isinstance(base_typ, HashMapT).
        Must check BEFORE the array subscript path.
        For nested hashmaps (map[k1][k2]):
        - Recursively evaluate base target to get intermediate slot
        - Then keccak256(intermediate_slot || key) for outer subscript *)
     if cenv.ce_is_hashmap var_name then
       do key_op <- lower_value compile_expr cenv (BaseT (UintT 256)) idx_e;
          (* Get base slot: for NameTarget, direct lookup.
             For SubscriptTarget (nested hashmap), recurse to get intermediate slot. *)
          base_slot <-
            (case bt of
               NameTarget _ =>
                 return (case FLOOKUP cenv.ce_vars var_name of
                           SOME (StorageLoc slot) => Lit slot
                         | _ => Lit 0w)
             | _ =>
                 do result <- compile_get_target_ptr cenv bt;
                    return (FST result)
                 od);
          slot_op <- compile_mapping_subscript base_slot key_op;
          (* HashMap values are always in storage.
             TODO: Value type not tracked — returns NONE for type. *)
          return (slot_op, SOME LocStorage, NONE)
       od
     else
     do result <- compile_get_target_ptr cenv bt;
        base_op <- return (FST result);
        loc_opt <- return (FST (SND result));
        base_type_opt <- return (SND (SND result));
        idx_op <- lower_value compile_expr cenv (BaseT (UintT 256)) idx_e;
        loc <- return (case loc_opt of SOME l => l | NONE => LocMemory);
        is_dynamic <- return (case base_type_opt of
                                SOME (ArrayT _ (Dynamic _)) => T
                              | _ => F);
        elem_ty <- return (case base_type_opt of
                             SOME (ArrayT t _) => t
                           | _ => BaseT (UintT 256));
        ws <- return (word_scale loc);
        elem_sz <- return (elem_size_in_location cenv loc elem_ty);
        static_count <- return (case base_type_opt of
                                  SOME (ArrayT _ (Fixed n)) => n
                                | _ => 0);
        is_signed_idx <- return (is_signed_type (expr_type idx_e));
        load_opc <- return (case loc of
                              LocStorage => SLOAD
                            | LocTransient => TLOAD
                            | _ => MLOAD);
        elem_ptr <-
          compile_array_subscript base_op idx_op is_dynamic static_count
                                  ws elem_sz is_signed_idx load_opc;
        return (elem_ptr, loc_opt, SOME elem_ty)
     od) ∧
  (* Attribute target: add struct field offset to base.
     Mirrors Python: _get_target_ptr for struct.field
     Uses base_type from recursive call to resolve struct name. *)
  compile_get_target_ptr cenv (AttributeTarget bt field) =
    do result <- compile_get_target_ptr cenv bt;
       base_op <- return (FST result);
       loc_opt <- return (FST (SND result));
       base_type_opt <- return (SND (SND result));
       struct_name <- return (case base_type_opt of
                                SOME (StructT sn) => nsid_to_string sn
                              | _ => "");
       fields <- return (get_struct_fields cenv.ce_struct_fields struct_name);
       is_storage <- return (case loc_opt of
                               SOME LocStorage => T
                             | SOME LocTransient => T
                             | _ => F);
       field_offset <- return
         (if is_storage then struct_field_offset_slots fields field
          else struct_field_offset fields field);
       field_type <- return (case ALOOKUP fields field of
                               SOME (fty, _) => SOME fty | NONE => NONE);
       if field_offset = 0 then return (base_op, loc_opt, field_type)
       else
         do ptr <- emit_op ADD [base_op; Lit (n2w field_offset)];
            return (ptr, loc_opt, field_type)
         od
    od
End

(* ===== Assign Value ===== *)
(* Dispatch assign by location and type.

   Mirrors Python: vyper/codegen_venom/stmt.py:_assign_value *)
(* Store value to target with location-aware dispatch.
   For memory-to-memory complex types, stages through temp buffer for
   overlap safety. Skips staging when source was not originally in memory
   (e.g., materialized from storage → fresh buffer, no aliasing possible).
   Mirrors Python: vyper/codegen_venom/stmt.py:_assign_value + _copy_complex_type
   NOTE: val_op is assumed to be a memory pointer for complex types.
   Callers use lower_value (unwrap_value handles materialization). *)
(* src_loc: source data_location option (for staging decision).
   SOME LocMemory means source is in memory → may alias destination.
   NONE means stack/computed value → no aliasing possible.
   Mirrors Python: src_vv.location (None for stack, DataLocation.X for located).
   dynarray_info: NONE for non-dynarray types, SOME (elem_words, elem_mem_size) for DynArray.
   When SOME, uses dynarray_to_storage (copies only length + actual elems).
   When NONE, uses bulk word copy (copies all words).
   Mirrors Python: vyper/codegen_venom/context.py:Context.store_variable *)
Definition compile_assign_value_def:
  compile_assign_value cenv dst_op dst_loc val_op is_prim_word
                       (src_loc : data_location option)
                       (dst_ty : type) (src_ty : type)
                       (dynarray_info : (num # num) option) mem_size =
    case dst_loc of
      LocMemory =>
        if is_prim_word then emit_void MSTORE [dst_op; val_op]
        else if src_loc = SOME LocMemory then
          (* Both memory: stage through temp buffer for overlap safety.
             Python: flat copy src→tmp (preserving src layout), then
             typed copy tmp→dst (converting layout if needed).
             Mirrors Python: vyper/codegen_venom/stmt.py:_copy_complex_type + _store_complex_type *)
          let src_mem_size = type_memory_bytes cenv src_ty in
          do tmp_op_alloc <- compile_alloc_buffer src_mem_size;
             tmp_op <- return tmp_op_alloc.buf_operand;
             (* Step 1: flat copy src→tmp (preserving src layout) *)
             compile_copy_memory tmp_op val_op src_mem_size;
             (* Step 2: typed copy or flat copy tmp→dst *)
             if dst_ty ≠ src_ty then
               compile_store_memory_typed cenv dst_op dst_ty tmp_op src_ty
             else
               compile_copy_memory dst_op tmp_op mem_size
          od
        else if dst_ty ≠ src_ty then
          (* Different layouts: use typed copy (no staging needed — src is
             from a fresh buffer or non-memory source).
             Mirrors Python: vyper/codegen_venom/context.py:Context.store_memory *)
          compile_store_memory_typed cenv dst_op dst_ty val_op src_ty
        else
          (* Same layout, non-aliasing → flat copy *)
          compile_copy_memory dst_op val_op mem_size
    | LocStorage =>
        (* Normalize source layout when types differ (non-bytestring).
           Storage/transient only understand destination layout, so convert
           src→dst layout in memory first.
           Mirrors Python: vyper/codegen_venom/stmt.py:_store_complex_type normalization *)
        do val_op' <-
             (if ¬is_prim_word ∧ dst_ty ≠ src_ty
                 ∧ ¬(is_bytestring_type dst_ty ∧ is_bytestring_type src_ty) then
                do norm_alloc <- compile_alloc_buffer mem_size;
                   compile_store_memory_typed cenv
                     norm_alloc.buf_operand dst_ty val_op src_ty;
                   return norm_alloc.buf_operand
                od
              else return val_op);
           if is_prim_word then emit_void SSTORE [dst_op; val_op']
           else
             (case dynarray_info of
                SOME (ew, ems) =>
                  (* DynArray→storage: copy only length + actual elements.
                     Mirrors Python: vyper/codegen_venom/context.py:Context.copy_dynarray_to_storage *)
                  compile_dynarray_to_storage val_op' dst_op ew ems F
              | NONE =>
                if mem_size ≤ 32 then
                  do loaded <- emit_op MLOAD [val_op'];
                     emit_void SSTORE [dst_op; loaded]
                  od
                else
                  do compile_memory_to_storage val_op' dst_op
                                               (mem_size DIV 32);
                     return ()
                  od)
        od
    | LocTransient =>
        do val_op' <-
             (if ¬is_prim_word ∧ dst_ty ≠ src_ty
                 ∧ ¬(is_bytestring_type dst_ty ∧ is_bytestring_type src_ty) then
                do norm_alloc <- compile_alloc_buffer mem_size;
                   compile_store_memory_typed cenv
                     norm_alloc.buf_operand dst_ty val_op src_ty;
                   return norm_alloc.buf_operand
                od
              else return val_op);
           if is_prim_word then emit_void TSTORE [dst_op; val_op']
           else
             (case dynarray_info of
                SOME (ew, ems) =>
                  compile_dynarray_to_storage val_op' dst_op ew ems T
              | NONE =>
                if mem_size ≤ 32 then
                  do loaded <- emit_op MLOAD [val_op'];
                     emit_void TSTORE [dst_op; loaded]
                  od
                else
                  do compile_memory_to_transient val_op' dst_op
                                                 (mem_size DIV 32);
                     return ()
                  od)
        od
    | LocCode =>
        if is_prim_word then emit_void ISTORE [dst_op; val_op]
        else if mem_size ≤ 32 then
          do loaded <- emit_op MLOAD [val_op];
             emit_void ISTORE [dst_op; loaded]
          od
        else
          do compile_word_copy_loop val_op dst_op
               (mem_size DIV 32) LocMemory LocCode T;
             return ()
          od
    | LocCalldata =>
        (* Calldata is read-only — store is invalid *)
        do emit_inst INVALID [] [];
           return ()
        od
End

(* ===== Tuple unpack: two-pass for overlap safety ===== *)
(* Pass 1: load all elements from source.
   For word types: MLOAD the value.
   For complex types: compute pointer to element (base + offset).
   Uses type_memory_bytes per element for proper stride.
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_tuple_unpack pass 1 *)
Definition compile_tuple_load_all_def:
  compile_tuple_load_all cenv src_op [] offset = return [] ∧
  compile_tuple_load_all cenv src_op (ty :: tys) offset =
    (let mem_size = type_memory_bytes cenv ty in
     do src_elem <-
          (if offset = 0 then return src_op
           else emit_op ADD [src_op; Lit (n2w offset)]);
        elem_op <- compile_load_memory src_elem (is_word_type ty) mem_size;
        rest_ops <- compile_tuple_load_all cenv src_op tys
                      (offset + mem_size);
        return (elem_op :: rest_ops)
     od)
End

(* Store a single value to a target at a given location.
   Dispatches store opcode based on location.
   Mirrors Python: ctx.ptr_store dispatching by location. *)
Definition compile_store_at_loc_def:
  compile_store_at_loc dst_op val_op NONE =
    emit_void MSTORE [dst_op; val_op] ∧
  compile_store_at_loc dst_op val_op (SOME LocMemory) =
    emit_void MSTORE [dst_op; val_op] ∧
  compile_store_at_loc dst_op val_op (SOME LocStorage) =
    emit_void SSTORE [dst_op; val_op] ∧
  compile_store_at_loc dst_op val_op (SOME LocTransient) =
    emit_void TSTORE [dst_op; val_op] ∧
  compile_store_at_loc dst_op val_op (SOME LocCode) =
    (* Code location: use ISTORE for immutables in constructor context *)
    emit_void ISTORE [dst_op; val_op] ∧
  compile_store_at_loc dst_op val_op (SOME LocCalldata) =
    (* Calldata is read-only — emit INVALID *)
    emit_void INVALID []
End

(* Pass 2: store loaded values to targets.
   Uses compile_get_target_ptr for full target support (storage, subscript, etc.).
   Dispatches by element type: word types use compile_store_at_loc (single store),
   complex types use compile_assign_value (multi-word location-aware copy).
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_tuple_unpack pass 2 *)
(* Store unpacked tuple elements to targets.
   src_tys: types from the RHS tuple (source element types).
   Each target may have a different declared type (dst_ty from get_target_ptr).
   Tuple elements are memory pointers → src_loc = SOME LocMemory.
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_tuple_unpack pass 2 *)
Definition compile_tuple_store_all_def:
  compile_tuple_store_all cenv [] [] [] = return () ∧
  compile_tuple_store_all cenv (src_ty :: src_tys) (BaseTarget bt :: targets) (val_op :: vals) =
    do result <- compile_get_target_ptr cenv bt;
       dst_op <- return (FST result);
       loc_opt <- return (FST (SND result));
       dst_ty_opt <- return (SND (SND result));
       dst_loc <- return (case loc_opt of SOME l => l | NONE => LocMemory);
       (* dst_ty from target, falls back to src_ty if unknown *)
       dst_ty <- return (case dst_ty_opt of SOME t => t | NONE => src_ty);
       is_prim <- return (is_word_type dst_ty);
       mem_sz <- return (type_memory_bytes cenv dst_ty);
       src_mem_sz <- return (type_memory_bytes cenv src_ty);
       src_is_word <- return (is_word_type src_ty \/ src_mem_sz = 32);
       dst_is_word <- return (is_prim \/ mem_sz = 32);
       (* Pass 1 materializes primitive and exactly-one-word complex values.
          Consume that representation directly; larger complex values remain
          pointers into the staged tuple. *)
       (if src_is_word then
          if dst_is_word then compile_store_at_loc dst_op val_op loc_opt
          else emit_void INVALID []
        else
          compile_assign_value cenv dst_op dst_loc val_op is_prim
                        NONE dst_ty src_ty NONE mem_sz);
       compile_tuple_store_all cenv src_tys targets vals
    od ∧
  (* Non-BaseTarget element: emit INVALID (shouldn't occur in valid AST) *)
  compile_tuple_store_all cenv (_ :: tys) (_ :: targets) (_ :: vals) =
    do emit_void INVALID [];
       compile_tuple_store_all cenv tys targets vals
    od ∧
  compile_tuple_store_all cenv _ _ _ = return ()
End

(* Two-pass tuple unpack: load ALL values first, then store ALL.
   This ensures a, b = b, a works correctly (no aliasing issues).
   When any member is complex (!is_word_type), stage entire source
   tuple to temp buffer first to prevent aliasing corruption.
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_tuple_unpack *)
Definition compile_tuple_unpack_def:
  compile_tuple_unpack cenv ty targets src_op =
    let elem_types = (case ty of
        TupleT tys => tys
      | StructT nsid =>
          MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
      | _ => REPLICATE (LENGTH targets) (BaseT (UintT 256))) in
    (* Stage source tuple to prevent aliasing when complex members present.
       Python stages when source_is_memory_view ∧ any(!_is_prim_word).
       We always stage when complex members exist (conservative but correct). *)
    let has_complex = EXISTS (λt. ¬is_word_type t) elem_types in
    let total_mem = SUM (MAP (type_memory_bytes cenv) elem_types) in
    if has_complex /\ total_mem > 0 /\
       ~cenv.ce_target CapMcopy then
      (* Reject before allocation or MCOPY-dependent staging. *)
      emit_inst INVALID [] []
    else
      do staged_op <-
           (if has_complex /\ total_mem > 0 then
              do staged_buf <- compile_alloc_buffer total_mem;
                 staged_ptr <- return staged_buf.buf_operand;
                 emit_void MCOPY [staged_ptr; src_op; Lit (n2w total_mem)];
                 return staged_ptr
              od
            else return src_op);
         vals <- compile_tuple_load_all cenv staged_op elem_types 0;
         compile_tuple_store_all cenv elem_types targets vals
      od
End

(* ===== Range Loop Bound Checks ===== *)
(* Emit bound checks for dynamic range loops.
   For signed types: assert start <= end using SGT.
   For unsigned: assert start <= end using GT.
   Also assert rounds <= rounds_bound.
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_range_loop bound checks *)
Definition compile_range_bound_checks_def:
  compile_range_bound_checks start_op end_op rounds_op rounds_bound
                             is_signed =
    do (* Check start <= end *)
       invalid_order <-
         (if is_signed then emit_op SGT [start_op; end_op]
          else emit_op GT [start_op; end_op]);
       valid_order <- emit_op ISZERO [invalid_order];
       emit_void ASSERT [valid_order];
       (* Check rounds <= rounds_bound *)
       invalid_rounds <- emit_op GT [rounds_op; Lit (n2w rounds_bound)];
       valid_rounds <- emit_op ISZERO [invalid_rounds];
       emit_void ASSERT [valid_rounds]
    od
End

(* ===== Iter Loop Element Copy ===== *)
(* Copy element from array to loop variable, location-aware.
   For memory: single mload/mcopy depending on size.
   For storage/transient: sload/tload for single slot, multi-slot loop.
   loc: source data_location (LocMemory, LocStorage, LocTransient, etc.)
   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_iter_loop body element copy *)
(* Copy one for-loop element from source to loop variable (in memory).
   Dispatches by source location and element type.

   For memory complex types with type mismatch: uses compile_store_memory_typed
   for layout-aware copy (e.g., DynArray[Bytes[540]] → Bytes[704]).
   For memory bytestrings: uses compile_store_bytestring for runtime-length copy.
   For calldata/code >32B: uses CALLDATACOPY/CODECOPY (not MCOPY).

   Mirrors Python: vyper/codegen_venom/stmt.py:_lower_iter_loop element copy dispatch *)
Definition compile_iter_elem_copy_def:
  compile_iter_elem_copy cenv elem_ptr item_ptr elem_size
                         loc is_slot_addressed
                         (target_ty : type) (elem_ty : type) =
    if is_slot_addressed then
      if elem_size = 1 then
        (* Single slot: load from storage/transient, mstore to memory *)
        let load_opc = case loc of LocStorage => SLOAD
                                 | LocTransient => TLOAD
                                 | LocCode => DLOAD
                                 | _ => MLOAD in
        do val_op <- emit_op load_opc [elem_ptr];
           emit_void MSTORE [item_ptr; val_op]
        od
      else
        (* Multi-slot: use compile_slot_to_memory from contextScript *)
        do compile_slot_to_memory elem_ptr item_ptr elem_size loc;
           return ()
        od
    else if loc ≠ LocMemory then
      (* Non-memory, byte-addressed: calldata/code/immutables.
         For ≤32B, single load+mstore. For >32B, location-specific bulk copy.
         Mirrors Python: self.ctx.copy_to_memory(dst, elem_addr, elem_size, location) *)
      if elem_size ≤ 32 then
        let load_opc = case loc of
                          LocCalldata => CALLDATALOAD
                        | LocCode => DLOAD
                        | _ => MLOAD in
        do val_op <- emit_op load_opc [elem_ptr];
           emit_void MSTORE [item_ptr; val_op]
        od
      else
        (case loc of
           LocCalldata =>
             emit_void CALLDATACOPY [item_ptr; elem_ptr; Lit (n2w elem_size)]
         | LocCode =>
             emit_void CODECOPY [item_ptr; elem_ptr; Lit (n2w elem_size)]
         | _ =>
             compile_copy_memory item_ptr elem_ptr elem_size)
    else if is_word_type target_ty then
      (* Memory, primitive word: mload + mstore *)
      do val_op <- emit_op MLOAD [elem_ptr];
         emit_void MSTORE [item_ptr; val_op]
      od
    else if target_ty ≠ elem_ty then
      (* Memory, complex, type mismatch: layout-aware copy.
         Handles cases like DynArray[Bytes[540]] → Bytes[704].
         Mirrors Python: self.ctx.store_memory(elem_addr, dst, target_type,
                          src_typ=array_typ.value_type) *)
      compile_store_memory_typed cenv item_ptr target_ty elem_ptr elem_ty
    else if is_bytestring_type target_ty then
      (* Memory, bytestring, same type: copy actual runtime length.
         Mirrors Python: store_memory → _BytestringT branch *)
      compile_store_bytestring elem_ptr item_ptr
    else
      (* Memory, complex, same type: flat copy *)
      compile_copy_memory item_ptr elem_ptr elem_size
End

(* infer_array_location, infer_array_is_dynamic defined in exprLoweringScript.
   type_memory_bytes, elem_size_in_location, is_bytestring_type in compileEnvScript.
   (shared between compile_expr, for-iter loops, and typed copy) *)

(* NOTE: is_word_type deleted — unified with is_word_type in compileEnv *)

Definition compile_stmt_def:
  (* Pass: no-op *)
  compile_stmt cenv lctx ty (Pass : stmt) = return () ∧

  (* Expression statement: compile for side effects, discard result.
     Use expr_type e, not function return type ty. *)
  compile_stmt cenv lctx ty (Expr e) =
    do compile_expr cenv (expr_type e) e;
       return ()
    od ∧

  (* AnnAssign: variable declaration with initialization.
     Variable is already in ce_vars (alloca pre-allocated).
     Dispatches to compile_assign_value for proper complex type handling.
     dst_ty = vtyp (declared type), src_ty = expr_type e (expression type).
     These may differ for subtype assignments (e.g. Bytes[540] → Bytes[704]).
     Mirrors Python: vyper/codegen_venom/stmt.py:lower_AnnAssign → _assign_value *)
  compile_stmt cenv lctx ty (AnnAssign id vtyp e) =
    (let src_ty = expr_type e in
     do vlwl_result <- lower_value_with_loc compile_expr cenv vtyp e;
        val_op <- return (FST vlwl_result);
        src_loc <- return (SND vlwl_result);
        (case FLOOKUP cenv.ce_vars id of
           SOME (MemLoc offset _) =>
             let is_prim = is_word_type vtyp in
             let mem_size = type_memory_bytes cenv vtyp in
             let da_info = (case vtyp of
                ArrayT elem_ty (Dynamic _) =>
                  let ems = type_memory_bytes cenv elem_ty in
                  SOME ((ems + 31) DIV 32, ems)
              | _ => NONE) in
             compile_assign_value cenv (Lit (n2w offset)) LocMemory val_op
                                  is_prim src_loc vtyp src_ty da_info mem_size
         | _ =>
             (* Unsupported: AnnAssign without its preallocated memory binding. *)
             emit_void INVALID [])
     od) ∧

  (* Assign: store to target (memory, storage, transient, code).
     LHS target evaluated before RHS expr (matches interpreter eval order).
     dst_ty from compile_get_target_ptr (target's declared type),
     src_ty from expr_type e (expression's type). These may differ
     for subtype assignments (e.g., DynArray[Bytes[540]] → DynArray[Bytes[704]]).
     Mirrors Python: vyper/codegen_venom/stmt.py:lower_Assign with _assign_value *)
  compile_stmt cenv lctx ty (Assign (BaseTarget bt) e) =
    (let src_ty = expr_type e in
     do tgt_result <- compile_get_target_ptr cenv bt;
        dst_op <- return (FST tgt_result);
        dst_loc_opt <- return (FST (SND tgt_result));
        dst_ty_opt <- return (SND (SND tgt_result));
        vlwl_result <- lower_value_with_loc compile_expr cenv src_ty e;
        val_op <- return (FST vlwl_result);
        src_loc <- return (SND vlwl_result);
        (* dst_ty: target's declared type. Falls back to src_ty if unknown. *)
        dst_ty <- return (case dst_ty_opt of SOME t => t | NONE => src_ty);
        is_prim <- return (is_word_type dst_ty);
        mem_size <- return (type_memory_bytes cenv dst_ty);
        da_info <- return (case dst_ty of
           ArrayT elem_ty (Dynamic _) =>
             let ems = type_memory_bytes cenv elem_ty in
             SOME ((ems + 31) DIV 32, ems)
         | _ => NONE);
        (case dst_loc_opt of
           SOME loc => compile_assign_value cenv dst_op loc val_op is_prim
                        src_loc dst_ty src_ty da_info mem_size
         | NONE =>
             (* Unsupported: unresolved assignment targets must not disappear. *)
             emit_void INVALID [])
     od) ∧

  (* AugAssign: load + binop + store.
     Handles memory, storage, transient targets.
     Mirrors Python: vyper/codegen_venom/stmt.py:lower_AugAssign *)
  compile_stmt cenv lctx ty (AugAssign target_ty bt bop e) =
    do tgt_result <- compile_get_target_ptr cenv bt;
       dst_op <- return (FST tgt_result);
       dst_loc_opt <- return (FST (SND tgt_result));
       (* Python order: get_target → load current → eval RHS → binop → store *)
       (case dst_loc_opt of
          NONE =>
            (* Unsupported: unresolved augmented-assignment target. *)
            emit_void INVALID []
        | SOME loc =>
            do load_opc <- return (case loc of
                                      LocStorage => SLOAD
                                    | LocTransient => TLOAD
                                    | _ => MLOAD);
               store_opc <- return (case loc of
                                       LocStorage => SSTORE
                                     | LocTransient => TSTORE
                                     | _ => MSTORE);
               cur_op <- emit_op load_opc [dst_op];
               rhs_op <- lower_value compile_expr cenv target_ty e;
               res_op <- compile_binop bop cur_op rhs_op target_ty;
               emit_void store_opc [dst_op; res_op]
            od)
    od ∧

  (* Assert: evaluate condition, handle failure.
     Three cases: bare assert, UNREACHABLE, or with reason string.
     Mirrors Python: vyper/codegen_venom/stmt.py:lower_Assert, _assert_with_reason *)
  compile_stmt cenv lctx ty (Assert cond_e AssertBare) =
    (* Bare assert: revert 0,0 on failure *)
    do cond_op <- lower_value compile_expr cenv (BaseT BoolT) cond_e;
       ok_lbl <- fresh_label "assert_ok";
       fail_lbl <- fresh_label "assert_fail";
       emit_inst JNZ [cond_op; Label ok_lbl; Label fail_lbl] [];
       new_block fail_lbl;
       emit_inst REVERT [Lit 0w; Lit 0w] [];
       new_block ok_lbl;
       return ()
    od ∧
  compile_stmt cenv lctx ty (Assert cond_e AssertUnreachable) =
    (* UNREACHABLE: INVALID opcode on failure *)
    do cond_op <- lower_value compile_expr cenv (BaseT BoolT) cond_e;
       ok_lbl <- fresh_label "assert_ok";
       fail_lbl <- fresh_label "assert_fail";
       emit_inst JNZ [cond_op; Label ok_lbl; Label fail_lbl] [];
       new_block fail_lbl;
       emit_inst INVALID [] [];
       new_block ok_lbl;
       return ()
    od ∧
  compile_stmt cenv lctx ty (Assert cond_e (AssertReason reason_e)) =
    (* Assert with reason: compile reason, encode Error(string), revert *)
    do cond_op <- lower_value compile_expr cenv (BaseT BoolT) cond_e;
       ok_lbl <- fresh_label "assert_ok";
       fail_lbl <- fresh_label "assert_fail";
       emit_inst JNZ [cond_op; Label ok_lbl; Label fail_lbl] [];
       new_block fail_lbl;
       reason_ty <- return (expr_type reason_e);
       msg_mem_size <- return (type_memory_bytes cenv reason_ty);
       msg_op <- lower_value compile_expr cenv reason_ty reason_e;
       compile_revert_with_reason cenv msg_op reason_ty msg_mem_size;
       new_block ok_lbl;
       return ()
    od ∧

  (* Log: event emission with indexed topics + ABI-encoded data.
     Mirrors Python: vyper/codegen_venom/stmt.py:lower_Log.
     CRITICAL: evaluate ALL args in AST order first (for side-effect ordering),
     then split into indexed (topics) and non-indexed (data).
     1. Evaluate all args in AST order
     2. Split evaluated ops into topics and data
     3. Hash bytestring topics
     4. Store data to buffer, ABI-encode
     5. Emit LOG *)
  compile_stmt cenv lctx ty (Log event_id args) =
    (let event_name = nsid_to_string event_id in
     case cenv.ce_event_info event_name of
       NONE => emit_inst INVALID [] []
     | SOME (event_hash, arg_types, indexed_flags) =>
         do eval_ops <- compile_log_eval_all cenv args;
            log_split <- return (split_log_ops eval_ops indexed_flags);
            raw_topics <- return (FST log_split);
            data_ops <- return (SND log_split);
            topic_ops <- compile_log_topic_ops raw_topics;
            all_topics <- return (Lit (n2w event_hash) :: topic_ops);
            n_topics <- return (LENGTH all_topics);
            if NULL data_ops then
              emit_inst (LOG : opcode)
                (Lit (n2w n_topics) :: Lit 0w :: Lit 0w :: all_topics) []
            else
              let data_types = MAP SND data_ops in
              let data_tuple_t = TupleT data_types in
              let data_mem_size = SUM (MAP (type_memory_bytes cenv) data_types) in
              do data_buf_alloc <- compile_alloc_buffer (MAX 32 data_mem_size);
                 data_buf <- return data_buf_alloc.buf_operand;
                 compile_log_store_data cenv data_ops data_buf 0;
                 abi_size <- return (abi_size_bound cenv.ce_struct_fields data_tuple_t);
                 data_enc_info <- return (type_to_abi_enc_info cenv.ce_struct_fields cenv data_tuple_t);
                 abi_buf_alloc <- compile_alloc_buffer (MAX 32 abi_size);
                 abi_buf <- return abi_buf_alloc.buf_operand;
                 encoded_len <-
                   compile_abi_encode_to_buf abi_buf data_buf data_enc_info;
                 emit_inst (LOG : opcode)
                   (Lit (n2w n_topics) :: abi_buf :: encoded_len :: all_topics) []
              od
         od) ∧


  (* Raise: revert with optional reason.
     Mirrors Python: vyper/codegen_venom/stmt.py:lower_Raise
     Three cases: bare raise (revert 0,0), UNREACHABLE (INVALID),
     or with reason (Error(string) encoding). *)
  compile_stmt cenv lctx ty (Raise RaiseBare) =
    emit_inst REVERT [Lit 0w; Lit 0w] [] ∧
  compile_stmt cenv lctx ty (Raise RaiseUnreachable) =
    emit_inst INVALID [] [] ∧
  compile_stmt cenv lctx ty (Raise (RaiseReason reason_e)) =
    (let reason_ty = expr_type reason_e in
     let msg_mem_size = type_memory_bytes cenv reason_ty in
     do msg_op <- lower_value compile_expr cenv reason_ty reason_e;
        compile_revert_with_reason cenv msg_op reason_ty msg_mem_size
     od) ∧

  (* Return NONE: emit STOP for external (with unlock), RET for internal.
     Mirrors Python: vyper/codegen_venom/stmt.py:lower_Return → _lower_external_return (unlocks first) *)
  compile_stmt cenv lctx ty (Return NONE) =
    (case FLOOKUP cenv.ce_vars "__return_pc__" of
       SOME (MemLoc rpc_off _) =>
         (* Internal: ret to return_pc *)
         do rpc <- emit_op MLOAD [Lit (n2w rpc_off)];
            emit_inst RET [rpc] []
         od
     | _ =>
         (* External: nonreentrant unlock + STOP *)
         let (is_nonreentrant, nkey, use_transient, is_view) =
           cenv.ce_nonreentrant in
         do (if is_nonreentrant then
               compile_nonreentrant_unlock nkey use_transient is_view
             else return ());
            emit_inst STOP [] []
         od) ∧

  (* Return (SOME e): compile value, dispatch internal vs external.
     Mirrors Python: vyper/codegen_venom/stmt.py:lower_Return.
     Internal functions: uses compile_internal_return with returns_count from cenv.
     External functions: uses compile_external_return with ABI encoding. *)
  compile_stmt cenv lctx ty (Return (SOME e)) =
    do val_op <- lower_value compile_expr cenv ty e;
       (case FLOOKUP cenv.ce_vars "__return_pc__" of
          SOME (MemLoc rpc_off _) =>
            (* Internal return: dispatch via compile_internal_return.
               Handles single-value, tuple, and memory return paths. *)
            do rpc <- emit_op MLOAD [Lit (n2w rpc_off)];
               (* Load return buffer pointer from __return_buf__ local.
                  The PARAM for the caller's buffer is stored there at function entry.
                  compile_internal_return dispatches MCOPY for complex types. *)
               ret_buf <-
                 (case FLOOKUP cenv.ce_vars "__return_buf__" of
                    SOME (MemLoc rbuf_off _) =>
                      do buf_ptr <- emit_op MLOAD [Lit (n2w rbuf_off)];
                         return (SOME buf_ptr)
                      od
                  | _ => return NONE);
               (* elem_types: for tuple/struct returns, use element types.
                  Python: hasattr(ret_typ, "tuple_items") matches TupleT + StructT.
                  Mirrors Python: vyper/codegen_venom/stmt.py:_lower_internal_return *)
               elem_types <- return (case ty of
                   TupleT tys => tys
                 | StructT nsid =>
                     MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
                 | _ => []);
               src_ty <- return (expr_type e);
               compile_internal_return cenv (SOME val_op) rpc
                 cenv.ce_returns_count ty src_ty elem_types ret_buf
            od
        | _ =>
            (* External return: ABI encoding + nonreentrant unlock.
               Mirrors Python: vyper/codegen_venom/stmt.py:_lower_external_return which unlocks
               before encoding/returning.
               Normalize when ret_src_typ ≠ ret_typ for non-prim,
               non-bytestring-to-bytestring. Python lines 936-945. *)
            let is_prim = is_word_type ty in
            let src_ty = expr_type e in
            let needs_normalize =
              (¬is_prim ∧
               ¬(is_bytestring_type ty ∧ is_bytestring_type src_ty) ∧
               src_ty ≠ ty) in
            let nr_info = cenv.ce_nonreentrant in
            let is_nonreentrant = FST nr_info in
            let nkey = FST (SND nr_info) in
            let use_transient = FST (SND (SND nr_info)) in
            let is_view = SND (SND (SND nr_info)) in
            do ret_op <-
                 (if needs_normalize then
                    let norm_size = type_memory_bytes cenv ty in
                    do norm_buf <- compile_alloc_buffer norm_size;
                       norm_ptr <- return norm_buf.buf_operand;
                       compile_store_memory_typed cenv norm_ptr ty val_op src_ty;
                       return norm_ptr
                    od
                  else return val_op);
               compile_external_return (SOME ret_op) is_prim cenv.ce_raw_return
                 cenv.ce_ret_enc_info cenv.ce_max_return_size
                 is_nonreentrant nkey use_transient is_view
            od)
    od ∧

  (* Append: dynarray append — location-aware.
     Delegates to compile_dynarray_append for correct opcode dispatch.
     Mirrors Python: expr.py _lower_dynarray_append *)
  compile_stmt cenv lctx ty (Append target val_e) =
    (let target_op = compile_target_base cenv target in
     let target_name = target_to_string target in
     (* Use array element type, not threading ty.
        Python: elem_typ = darray_typ.value_type *)
     let elem_ty = (case cenv.ce_var_type target_name of
                      SOME (ArrayT t _) => t | _ => ty) in
     let is_prim = is_word_type elem_ty in
     let capacity = cenv.ce_dynarray_capacity target_name in
     let loc = infer_array_location cenv (target_to_expr target) in
     let ws = word_scale loc in
     let elem_size = elem_size_in_location cenv loc elem_ty in
     let load_opc = load_opc_for loc in
     let store_opc = store_opc_for loc in
     do val_op_raw <- lower_value compile_expr cenv elem_ty val_e;
        (* Stage complex elements through temp buffer to guard against aliasing
           (e.g., arr.append(arr[0])). MemoryCopyElisionPass elides when safe.
           Mirrors Python: if not elem_typ._is_prim_word: stage through temp_buf *)
        staged_val <-
          (if is_prim then return val_op_raw
           else
             let mem_sz = type_memory_bytes cenv elem_ty in
             do tmp_alloc <- compile_alloc_buffer mem_sz;
                compile_copy_memory tmp_alloc.buf_operand val_op_raw mem_sz;
                return tmp_alloc.buf_operand
             od);
        src_elem_ty <- return (expr_type val_e);
        (* For storage/transient destination with type mismatch,
           normalize source layout to destination layout in memory first.
           Without this, word_copy_loop reads source-layout bytes into
           destination-layout storage slots, corrupting data.
           Mirrors Python: if data_loc in (STORAGE, TRANSIENT) and
           elem_src_typ != elem_typ: normalize through store_memory *)
        norm_result <-
          (if is_prim ∨ loc = LocMemory ∨ src_elem_ty = elem_ty then
             return (staged_val, src_elem_ty)
           else
             let norm_sz = type_memory_bytes cenv elem_ty in
             do norm_alloc <- compile_alloc_buffer norm_sz;
                compile_store_memory_typed cenv
                  norm_alloc.buf_operand elem_ty
                  staged_val src_elem_ty;
                return (norm_alloc.buf_operand, elem_ty)
             od);
        final_val <- return (FST norm_result);
        final_src_ty <- return (SND norm_result);
        compile_dynarray_append cenv target_op final_val ws elem_size
                                     elem_ty final_src_ty
                                     capacity is_prim
                                     load_opc store_opc
     od) ∧

  (* Assign with TupleTarget: tuple unpacking.
     Mirrors Python: vyper/codegen_venom/stmt.py:_lower_tuple_unpack
     First evaluate RHS, then assign each element to its target. *)
  compile_stmt cenv lctx ty (Assign (TupleTarget targets) e) =
    do src_op <- lower_value compile_expr cenv ty e;
       compile_tuple_unpack cenv ty targets src_op
    od ∧

  (* If: multi-block control flow *)
  compile_stmt cenv lctx ty (If cond_e then_body else_body) =
    do cond_op <- lower_value compile_expr cenv (BaseT BoolT) cond_e;
       then_lbl <- fresh_label "then";
       else_lbl <- fresh_label "else";
       exit_lbl <- fresh_label "if_exit";
       emit_inst JNZ [cond_op; Label then_lbl; Label else_lbl] [];
       (* Then branch — only JMP to exit if not already terminated (e.g. by Return) *)
       new_block then_lbl;
       compile_stmts cenv lctx ty then_body;
       cs_after_then <- comp_get;
       then_terminated <- return (block_is_terminated cs_after_then);
       emit_jmp_if_not_terminated exit_lbl;
       (* Else branch — same terminator check *)
       new_block else_lbl;
       compile_stmts cenv lctx ty else_body;
       cs_after_else <- comp_get;
       else_terminated <- return (block_is_terminated cs_after_else);
       emit_jmp_if_not_terminated exit_lbl;
       (* Exit block: only needed if at least one branch is non-terminated.
          Mirrors Python: vyper/codegen_venom/stmt.py:L488-494 *)
       if ¬then_terminated ∨ ¬else_terminated then
         do new_block exit_lbl; return () od
       else return ()
    od ∧

  (* For: range loop — for id in range(start, end) with bound n
     Creates 5-block CFG: entry → cond → body → incr → exit
     In the Vyper AST: For id typ (Range start end) n body
     Handles both static and dynamic ranges, signed and unsigned.
     For dynamic ranges (bound > 0): rounds = end - start, assert start <= end,
     assert rounds <= bound.
     For static ranges (bound = 0): no runtime checks — relies on type checker
     having validated start <= end at compile time. Loop uses EQ termination
     (counter != end_val), matching Python exactly.
     PRECONDITION (static ranges): start <= end for unsigned, start <=_s end for
     signed. If violated, the loop would run ~2^256 iterations until fuel exhausts.
     Vyper's type checker guarantees this for static ranges (both are literals).
     Mirrors Python: vyper/codegen_venom/stmt.py:_lower_range_loop *)
  compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound body) =
    (let is_signed = is_signed_type fty in
     do start_op <- lower_value compile_expr cenv fty start_e;
        end_op <- lower_value compile_expr cenv fty end_e;
        entry_lbl <- fresh_label "for_entry";
        cond_lbl <- fresh_label "for_cond";
        body_lbl <- fresh_label "for_body";
        incr_lbl <- fresh_label "for_incr";
        exit_lbl <- fresh_label "for_exit";
        (* Jump to entry *)
        emit_inst JMP [Label entry_lbl] [];
        (* Entry: initialize counter, bound checks for dynamic ranges *)
        new_block entry_lbl;
        counter_var <- fresh_var;
        emit_inst ASSIGN [start_op] [counter_var];
        (* Compute rounds and end_val.
           If bound > 0, this is a dynamic range: rounds = end - start.
           Otherwise static: end_val = end_op directly. *)
        end_val <-
          (if bound > 0 then
             do rounds <- emit_op SUB [end_op; start_op];
                compile_range_bound_checks start_op end_op rounds
                                            bound is_signed;
                emit_op ADD [start_op; rounds]
             od
           else
             return end_op);
        emit_inst JMP [Label cond_lbl] [];
        (* Cond: check counter != end *)
        new_block cond_lbl;
        done_op <- emit_op EQ [Var counter_var; end_val];
        emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
        (* Body: store counter to loop var, execute body *)
        new_block body_lbl;
        (case FLOOKUP cenv.ce_vars id of
           SOME (MemLoc offset _) =>
             emit_void MSTORE [Lit (n2w offset); Var counter_var]
         | _ =>
             (* Unsupported: a range loop variable requires a memory binding. *)
             emit_void INVALID []);
        compile_stmts cenv (InLoop exit_lbl incr_lbl) ty body;
        (* Only JMP to incr if body didn't terminate (e.g. via break/return) *)
        emit_jmp_if_not_terminated incr_lbl;
        (* Incr: counter = counter + 1 *)
        new_block incr_lbl;
        new_counter <- emit_op ADD [Var counter_var; Lit 1w];
        emit_inst ASSIGN [new_counter] [counter_var];
        emit_inst JMP [Label cond_lbl] [];
        (* Exit block *)
        new_block exit_lbl;
        return ()
     od) ∧

  (* For: iter loop — for id in array
     Creates 5-block CFG: entry → cond → body → incr → exit
     Location-aware: handles memory, storage, transient, code, calldata.
     is_dynamic: T for DynArray (has length word), F for SArray
     word_scale: 1 for storage/transient, 32 for memory/code/calldata
     elem_size: size of element in location units
     load_opc: MLOAD/SLOAD/TLOAD/CALLDATALOAD/DLOADN
     is_slot_addressed: T for storage/transient
     SEMANTIC DIFFERENCE: The Vyper interpreter materializes the entire array
     to a value list before iterating (eval_iterator → materialise → extract_elements).
     The lowering reads elements from source on each iteration. If the loop body
     modifies the source array, the interpreter sees original values but the lowering
     sees modified values. Vyper's type checker forbids mutation of the iterated
     array during the loop, so this is correct for well-typed programs.
     Correctness theorem needs precondition: loop body does not modify arr_e.
     Mirrors Python: vyper/codegen_venom/stmt.py:_lower_iter_loop *)
  compile_stmt cenv lctx ty (For id fty (Array arr_e) bound body) =
    (let is_dynamic = infer_array_is_dynamic cenv arr_e in
     let loc = infer_array_location cenv arr_e in
     let slot_addr = is_slot_addressed loc in
     let ws = word_scale loc in
     let elem_size = elem_size_in_location cenv loc fty in
     let load_opc = load_opc_for loc in
     do arr_vv <- compile_expr cenv (expr_type arr_e) arr_e;
        arr_op <- return (vv_operand arr_vv);
        (* Load array length *)
        len_op <-
          (if is_dynamic then emit_op load_opc [arr_op]
           else return (Lit (n2w bound)));
        (* Bound check for DynArrays: length <= bound *)
        (if is_dynamic ∧ bound > 0 then
           do invalid <- emit_op GT [len_op; Lit (n2w bound)];
              valid <- emit_op ISZERO [invalid];
              emit_void ASSERT [valid]
           od
         else return ());
        entry_lbl <- fresh_label "iter_entry";
        cond_lbl <- fresh_label "iter_cond";
        body_lbl <- fresh_label "iter_body";
        incr_lbl <- fresh_label "iter_incr";
        exit_lbl <- fresh_label "iter_exit";
        (* Jump to entry *)
        emit_inst JMP [Label entry_lbl] [];
        (* Entry: initialize index = 0 *)
        new_block entry_lbl;
        idx_var <- fresh_var;
        emit_inst ASSIGN [Lit 0w] [idx_var];
        emit_inst JMP [Label cond_lbl] [];
        (* Cond: check index == length *)
        new_block cond_lbl;
        done_op <- emit_op EQ [Var idx_var; len_op];
        emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
        (* Body: compute element address, copy to loop var, execute body *)
        new_block body_lbl;
        (* offset_base: skip length word for DynArray *)
        offset_base <- return (if is_dynamic then ws else 0);
        idx_offset <- emit_op MUL [Var idx_var; Lit (n2w elem_size)];
        total_offset <-
          (if offset_base > 0 then
             emit_op ADD [Lit (n2w offset_base); idx_offset]
           else return idx_offset);
        elem_ptr <- emit_op ADD [arr_op; total_offset];
        (* Copy element to loop variable (in memory).
           target_ty = fty (loop variable type), elem_ty = array value_type.
           These can differ (e.g., for x: Bytes[704] in arr where
           arr: DynArray[Bytes[540], 10]).
           Mirrors Python: store_memory(elem_addr, dst, target_type,
                            src_typ=array_typ.value_type) *)
        arr_elem_ty <- return (case expr_type arr_e of
                                  ArrayT et _ => et | _ => fty);
        (case FLOOKUP cenv.ce_vars id of
           SOME (MemLoc off _) =>
             compile_iter_elem_copy cenv elem_ptr (Lit (n2w off)) elem_size
                                    loc slot_addr fty arr_elem_ty
         | _ =>
             (* Unsupported: an iteration variable requires a memory binding. *)
             emit_void INVALID []);
        compile_stmts cenv (InLoop exit_lbl incr_lbl) ty body;
        (* Only JMP to incr if body didn't terminate *)
        emit_jmp_if_not_terminated incr_lbl;
        (* Incr: index = index + 1 *)
        new_block incr_lbl;
        new_idx <- emit_op ADD [Var idx_var; Lit 1w];
        emit_inst ASSIGN [new_idx] [idx_var];
        emit_inst JMP [Label cond_lbl] [];
        (* Exit block *)
        new_block exit_lbl;
        return ()
     od) ∧

  (* Break: jump to loop exit *)
  compile_stmt cenv (InLoop exit_lbl _) ty Break =
    emit_inst JMP [Label exit_lbl] [] ∧

  (* Continue: jump to loop increment *)
  compile_stmt cenv (InLoop _ incr_lbl) ty Continue =
    emit_inst JMP [Label incr_lbl] [] ∧

  (* Catch-all for unsupported statements: emit INVALID *)
  compile_stmt cenv lctx ty _ =
    do emit_inst INVALID [] [];
       return ()
    od ∧

  (* Compile a list of statements.
     Skips dead code after terminating statements (return, raise, break, continue).
     Mirrors Python: vyper/codegen_venom/stmt.py:_lower_body with is_terminated check *)
  compile_stmts cenv lctx ty [] = return () ∧
  compile_stmts cenv lctx ty (s::ss) =
    do cs <- comp_get;
       if block_is_terminated cs then return ()
       else
         do compile_stmt cenv lctx ty s;
            compile_stmts cenv lctx ty ss
         od
    od
Termination
  WF_REL_TAC `measure (λx. case x of
    INL (cenv, lctx, ty, s) => 2 * stmt_size s + 2
  | INR (cenv, lctx, ty, ss) => 2 * list_size stmt_size ss + 1)`
End
