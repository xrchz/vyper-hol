(*
 * System-Level Built-in Functions
 *
 * TOP-LEVEL:
 *   compile_raw_call    — low-level external call with full control
 *   compile_send        — send ether to address
 *   compile_raw_log     — raw event emission (LOG0-LOG4)
 *   compile_raw_revert  — revert with custom data
 *   compile_selfdestruct — destroy contract
 *
 * Mirrors Python: vyper/codegen_venom/builtins/system.py
 *)

Theory builtinSystem
Ancestors
  emitHelper context compileEnv builtinSimple venomInst
Libs
  monadsyntax

(* ===== raw_call ===== *)
(* Mirrors Python: system.py lower_raw_call
   raw_call(to, data, max_outsize=0, gas=gas, value=0,
            is_delegate_call=F, is_static_call=F, revert_on_failure=T)

   Data layout: src is [32-byte length][data...]
   Outputs depend on max_outsize and revert_on_failure. *)

(* Which EVM call opcode to use *)
Datatype:
  call_type = RegularCall | DelegateCall | StaticCall
End

(* ===== msg.data special case ===== *)
(* Mirrors Python:
   vyper/codegen_venom/builtins/system.py:_is_msg_data and
   vyper/codegen_venom/context.py:Context.new_internal_variable.
   When raw_call data is msg.data, reserve its runtime calldata length and copy
   all calldata into that fresh region. Returns (data_ptr, data_len). *)
Definition compile_msg_data_to_memory_def:
  compile_msg_data_to_memory =
    do data_len <- emit_op CALLDATASIZE [];
       data_ptr <- compile_alloc_dynamic data_len;
       emit_void CALLDATACOPY [data_ptr; Lit 0w; data_len];
       return (data_ptr, data_len)
    od
End

Definition compile_raw_call_def:
  compile_raw_call to_op data_ptr data_len gas_op value_op
                   call_ty max_outsize revert_on_failure =
    do (* Allocate output buffer if needed *)
       (out_ptr, out_len) <-
         (if max_outsize > 0 then
            (* Buffer: 32 (length) + ceil32(max_outsize) (data).
               Mirrors Python: BytesT(max_outsize).memory_bytes_required *)
            let padded_outsize = ((max_outsize + 31) DIV 32) * 32 in
            do buf_alloc <- compile_alloc_buffer (padded_outsize + 32);
               buf <- return buf_alloc.buf_operand;
               out_data <- emit_op ADD [buf; Lit 32w];
               return (out_data, Lit (n2w max_outsize))
            od
          else
            return (Lit 0w, Lit 0w));
       (* Emit call instruction *)
       success <-
         (case call_ty of
            DelegateCall =>
              emit_op DELEGATECALL
                [gas_op; to_op; data_ptr; data_len; out_ptr; out_len]
          | StaticCall =>
              emit_op STATICCALL
                [gas_op; to_op; data_ptr; data_len; out_ptr; out_len]
          | RegularCall =>
              emit_op CALL
                [gas_op; to_op; value_op; data_ptr; data_len; out_ptr; out_len]);
       if revert_on_failure then
         do (* Propagate callee revert reason *)
            fail_lbl <- fresh_label "call_fail";
            ok_lbl <- fresh_label "call_ok";
            emit_inst JNZ [success; Label ok_lbl; Label fail_lbl] [];
            new_block fail_lbl;
            rds <- emit_op RETURNDATASIZE [];
            emit_void RETURNDATACOPY [Lit 0w; Lit 0w; rds];
            emit_inst REVERT [Lit 0w; rds] [];
            new_block ok_lbl;
            if max_outsize > 0 then
              do (* Cap return size: min(returndatasize, max_outsize) *)
                 rds2 <- emit_op RETURNDATASIZE [];
                 cmp <- emit_op LT [rds2; Lit (n2w max_outsize)];
                 (* min(rds, max): cmp=1 when rds<max → take rds *)
                 capped <- compile_select cmp rds2
                             (Lit (n2w max_outsize));
                 (* Store capped length before output data *)
                 len_ptr <- emit_op SUB [out_ptr; Lit 32w];
                 emit_void MSTORE [len_ptr; capped];
                 return len_ptr
              od
            else
              return (Lit 0w)
         od
       else
         if max_outsize > 0 then
           let bytes_mem_size = 32 + ((max_outsize + 31) DIV 32) * 32 in
           let tuple_size = 32 + bytes_mem_size in
           do (* Cap return size even in non-revert path *)
              rds2 <- emit_op RETURNDATASIZE [];
              cmp <- emit_op LT [rds2; Lit (n2w max_outsize)];
              (* min(rds, max): cmp=1 when rds<max → take rds *)
              capped <- compile_select cmp rds2
                          (Lit (n2w max_outsize));
              (* Store capped length at out_buf base (= out_ptr - 32) *)
              len_ptr <- emit_op SUB [out_ptr; Lit 32w];
              emit_void MSTORE [len_ptr; capped];
              (* Build return tuple: (success:uint256, data:Bytes[N])
                 Layout: [success (32B)][length (32B)][data (ceil32(max_outsize)B)]
                 Allocate tuple buffer and copy. *)
              tuple_buf_alloc <- compile_alloc_buffer tuple_size;
              tuple_buf <- return tuple_buf_alloc.buf_operand;
              (* Store success at offset 0 *)
              emit_void MSTORE [tuple_buf; success];
              (* Copy bytes (length + data) at offset 32 *)
              bytes_dst <- emit_op ADD [tuple_buf; Lit 32w];
              emit_void MCOPY
                [bytes_dst; len_ptr; Lit (n2w bytes_mem_size)];
              return tuple_buf
           od
         else
           return success
    od
End

(* ===== send ===== *)
(* Mirrors Python: system.py lower_send
   send(to, value, gas=0): CALL with no data, assert success *)
Definition compile_send_def:
  compile_send to_op value_op gas_op =
    do success <- emit_op CALL
         [gas_op; to_op; value_op; Lit 0w; Lit 0w; Lit 0w; Lit 0w];
       emit_void ASSERT [success]
    od
End

(* ===== raw_log ===== *)
(* Mirrors Python: system.py lower_raw_log
   raw_log(topics, data): LOG with 0-4 topics *)
Definition compile_raw_log_def:
  compile_raw_log n_topics data_ptr data_len topic_ops =
    emit_void LOG (Lit (n2w n_topics) :: data_ptr :: data_len :: topic_ops)
End

(* ===== raw_revert ===== *)
(* Mirrors Python: system.py lower_raw_revert
   Revert with custom data bytes *)
Definition compile_raw_revert_def:
  compile_raw_revert data_ptr =
    do data_len <- emit_op MLOAD [data_ptr];
       data_start <- emit_op ADD [data_ptr; Lit 32w];
       emit_inst REVERT [data_start; data_len] []
    od
End

(* ===== selfdestruct ===== *)
Definition compile_selfdestruct_def:
  compile_selfdestruct to_op =
    emit_void SELFDESTRUCT [to_op]
End
