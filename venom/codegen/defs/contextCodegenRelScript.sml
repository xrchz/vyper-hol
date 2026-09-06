(*
 * Context-wide code-generation memory relations.
 *
 * The existing codegenRel$memory_rel remains the allocator-local relation
 * used by single-function simulation.  This theory adds the ambient relation
 * needed while caller spill regions remain live across internal calls.
 *)

Theory contextCodegenRel
Ancestors
  codegenRel venomExecSemantics venomWf fcgDefs

(* A byte in any function's half-open spill interval. *)
Definition context_spill_byte_def:
  context_spill_byte cp i <=>
    ?r. MEM r cp.cp_regions /\
        r.sr_spill_base <= i /\ i < r.sr_spill_end
End

(* Ambient memories may differ throughout the union of planned spill regions,
   but agree at every other byte (with the usual implicit zero padding). *)
Definition context_memory_rel_def:
  context_memory_rel cp venom_mem asm_mem <=>
    !i. ~context_spill_byte cp i ==>
        read_byte i venom_mem = read_byte i asm_mem
End
(* Context-facing Venom/assembly relation.  Unlike venom_asm_rel, its memory
   mask covers every spill region in the complete context plan. *)
Definition context_venom_asm_rel_def:
  context_venom_asm_rel cp label_offsets ps vs as <=>
    plan_stack_rel label_offsets vs ps.ps_stack as.as_stack /\
    plan_spill_rel label_offsets vs ps.ps_spilled as.as_memory /\
    context_memory_rel cp vs.vs_memory as.as_memory /\
    as.as_accounts = vs.vs_accounts /\
    as.as_transient = vs.vs_transient /\
    as.as_returndata = vs.vs_returndata /\
    as.as_logs = vs.vs_logs /\
    as.as_call_ctx = vs.vs_call_ctx /\
    as.as_tx_ctx = vs.vs_tx_ctx /\
    as.as_block_ctx = vs.vs_block_ctx /\
    as.as_code = vs.vs_code /\
    as.as_prev_hashes = vs.vs_prev_hashes
End

Theorem context_venom_asm_rel_terminal:
  context_venom_asm_rel cp lo ps vs as ==>
  venom_asm_terminal_rel vs as
Proof
  simp[context_venom_asm_rel_def, venom_asm_terminal_rel_def]
QED

Theorem context_venom_asm_rel_memory:
  context_venom_asm_rel cp lo ps vs as ==>
  context_memory_rel cp vs.vs_memory as.as_memory
Proof
  simp[context_venom_asm_rel_def]
QED


(* A source step preserves every byte reserved for compiler spills. *)
Definition context_spill_step_safe_def:
  context_spill_step_safe cp vs vs' <=>
    !i. context_spill_byte cp i ==>
        read_byte i vs.vs_memory = read_byte i vs'.vs_memory
End

(* Membership in a half-open source-memory read range.  In particular a
   zero-length range contains no byte. *)
Definition byte_in_memory_range_def:
  byte_in_memory_range (off:num,len:num) (i:num) <=>
    off <= i /\ i < off + len
End

Definition memory_range_of_operands_def:
  memory_range_of_operands off_op len_op vs =
    case (eval_operand off_op vs, eval_operand len_op vs) of
      (SOME off, SOME len) => [(w2n off,w2n len)]
    | _ => []
End

Definition dret_memory_read_ranges_def:
  dret_memory_read_ranges inst vs =
    case parse_dret_shape inst of
      NONE => []
    | SOME (ordinary,dynamic) =>
        case eval_operands inst.inst_operands vs of
          NONE => []
        | SOME vals =>
            case pair_dret_words
              (TAKE (2 * dynamic) (DROP (1 + ordinary) vals)) of
              NONE => []
            | SOME pairs => MAP (\(src,len). (w2n src,w2n len)) pairs
End

(* Exactly the byte ranges consumed from vs_memory by step_inst_base.
   INVOKE has no direct caller-memory range here: its nested execution is
   covered separately by the aggregate INVOKE closure obligation.  Copies
   whose source is calldata, returndata, code, or the data section are not
   source-memory reads and therefore intentionally have no range here. *)
Definition source_memory_read_ranges_def:
  source_memory_read_ranges inst vs =
    case inst.inst_opcode of
      MLOAD =>
        (case inst.inst_operands of
           [off_op] =>
             (case eval_operand off_op vs of
                SOME off => [(w2n off,32)]
              | NONE => [])
         | _ => [])
    | MCOPY =>
        (case inst.inst_operands of
           [dst_op; src_op; len_op] =>
             (case (eval_operand dst_op vs, eval_operand src_op vs,
                    eval_operand len_op vs) of
                (SOME dst, SOME src, SOME len) => [(w2n src,w2n len)]
              | _ => [])
         | _ => [])
    | DRET => dret_memory_read_ranges inst vs
    | RETURN =>
        (case inst.inst_operands of
           [off_op; len_op] => memory_range_of_operands off_op len_op vs
         | _ => [])
    | REVERT =>
        (case inst.inst_operands of
           [off_op; len_op] => memory_range_of_operands off_op len_op vs
         | _ => [])
    | SHA3 =>
        (case inst.inst_operands of
           [off_op; len_op] => memory_range_of_operands off_op len_op vs
         | _ => [])
    | LOG =>
        (case inst.inst_operands of
           Lit tc :: rest =>
             let n = w2n tc in
             if LENGTH rest <> n + 2 then []
             else
               let off_op = EL 0 rest in
               let len_op = EL 1 rest in
               let topic_ops = DROP 2 rest in
               (case eval_operands topic_ops vs of
                  NONE => []
                | SOME topics => memory_range_of_operands off_op len_op vs)
         | _ => [])
    | CALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; val_op; off_op; len_op; ret_off_op; ret_len_op] =>
             (case (eval_operand gas_op vs, eval_operand addr_op vs,
                    eval_operand val_op vs, eval_operand ret_off_op vs,
                    eval_operand ret_len_op vs) of
                (SOME gas, SOME addr, SOME value, SOME ret_off, SOME ret_len) =>
                  memory_range_of_operands off_op len_op vs
              | _ => [])
         | _ => [])
    | STATICCALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; off_op; len_op; ret_off_op; ret_len_op] =>
             (case (eval_operand gas_op vs, eval_operand addr_op vs,
                    eval_operand ret_off_op vs, eval_operand ret_len_op vs) of
                (SOME gas, SOME addr, SOME ret_off, SOME ret_len) =>
                  memory_range_of_operands off_op len_op vs
              | _ => [])
         | _ => [])
    | DELEGATECALL =>
        (case inst.inst_operands of
           [gas_op; addr_op; off_op; len_op; ret_off_op; ret_len_op] =>
             (case (eval_operand gas_op vs, eval_operand addr_op vs,
                    eval_operand ret_off_op vs, eval_operand ret_len_op vs) of
                (SOME gas, SOME addr, SOME ret_off, SOME ret_len) =>
                  memory_range_of_operands off_op len_op vs
              | _ => [])
         | _ => [])
    | CREATE =>
        (case inst.inst_operands of
           [value_op; off_op; len_op] =>
             (case eval_operand value_op vs of
                SOME value => memory_range_of_operands off_op len_op vs
              | NONE => [])
         | _ => [])
    | CREATE2 =>
        (case inst.inst_operands of
           [value_op; off_op; len_op; salt_op] =>
             (case (eval_operand value_op vs, eval_operand salt_op vs) of
                (SOME value, SOME salt) =>
                  memory_range_of_operands off_op len_op vs
              | _ => [])
         | _ => [])
    | _ => []
End

Definition source_memory_read_byte_def:
  source_memory_read_byte inst vs i <=>
    ?range. MEM range (source_memory_read_ranges inst vs) /\
            byte_in_memory_range range i
End

Definition source_memory_reads_disjoint_def:
  source_memory_reads_disjoint cp inst vs <=>
    !i. source_memory_read_byte inst vs i ==>
        ~context_spill_byte cp i
End

(* Every source write range avoids every context-owned spill region.  Keeping
   the endpoint form here makes projection to a function-local allocator a
   direct boundary theorem rather than repeated bytewise arithmetic. *)
Definition context_source_memory_writes_disjoint_def:
  context_source_memory_writes_disjoint cp inst vs <=>
    EVERY (\(off,len).
      len = 0 \/
      !r. MEM r cp.cp_regions ==>
          off + len <= r.sr_spill_base \/ r.sr_spill_end <= off)
      (source_memory_write_ranges inst vs)
End
(* The entry dispatcher must not return through the internal-call protocol. *)
Definition entry_fn_no_ret_def:
  entry_fn_no_ret fn <=>
    EVERY (\bb. EVERY (\inst. inst.inst_opcode <> RET)
                      bb.bb_instructions) fn.fn_blocks
End

(* Connect an invariant point to the state's current executable instruction. *)
Definition active_inst_def:
  active_inst fn inst vs <=>
    ?bb. MEM bb fn.fn_blocks /\
         bb.bb_label = vs.vs_current_bb /\
         vs.vs_inst_idx < LENGTH bb.bb_instructions /\
         EL vs.vs_inst_idx bb.bb_instructions = inst
End

(* A non-vacuous initial witness at the context's actual entry function. *)
Definition initial_entry_satisfies_def:
  initial_entry_satisfies Inv ctx initial_vs <=>
    ?name fn inst.
      ctx.ctx_entry = SOME name /\
      lookup_function name ctx.ctx_functions = SOME fn /\
      active_inst fn inst initial_vs /\
      Inv ctx fn inst initial_vs
End

(* Closure across an ordinary successful instruction step, when the result
   exposes another active instruction in the same function. *)
Definition reachable_inv_closed_under_steps_def:
  reachable_inv_closed_under_steps Inv ctx <=>
    !fn inst next_inst vs vs' fuel.
      Inv ctx fn inst vs /\ active_inst fn inst vs /\
      inst.inst_opcode <> INVOKE /\
      step_inst fuel ctx inst vs = OK vs' /\
      active_inst fn next_inst vs' ==>
      Inv ctx fn next_inst vs'
End

(* Closure when an INVOKE transfers control into a freshly set-up callee. *)
Definition reachable_inv_closed_under_calls_def:
  reachable_inv_closed_under_calls Inv ctx <=>
    !caller_fn invoke caller_vs callee_name arg_ops callee_fn args callee_vs
     callee_inst.
      Inv ctx caller_fn invoke caller_vs /\
      active_inst caller_fn invoke caller_vs /\
      invoke.inst_opcode = INVOKE /\
      decode_invoke invoke = SOME (callee_name,arg_ops) /\
      lookup_function callee_name ctx.ctx_functions = SOME callee_fn /\
      eval_operands arg_ops caller_vs = SOME args /\
      setup_callee callee_fn args caller_vs = SOME callee_vs /\
      active_inst callee_fn callee_inst callee_vs ==>
      Inv ctx callee_fn callee_inst callee_vs
End

(* Closure across the explicit return-state plumbing used by INVOKE. *)
Definition reachable_inv_closed_under_returns_def:
  reachable_inv_closed_under_returns Inv ctx <=>
    !caller_fn invoke caller_vs callee_fn callee_inst callee_vs callee_done
     ret merged adopted returned_vs.
      Inv ctx caller_fn invoke caller_vs /\
      Inv ctx callee_fn callee_inst callee_vs /\
      active_inst callee_fn callee_inst callee_vs /\
      step_inst_base callee_inst callee_vs = IntRet ret callee_done /\
      merged = merge_callee_state caller_vs callee_done /\
      adopted = adopt_return_fmp ret merged /\
      bind_outputs invoke.inst_outputs ret.iret_values adopted = SOME returned_vs ==>
      Inv ctx caller_fn invoke returned_vs
End

(* INVOKE is aggregate in step_inst: callee run, merge, FMP adoption, and
   output binding occur inside one successful semantic step. *)
Definition reachable_inv_closed_under_invoke_def:
  reachable_inv_closed_under_invoke Inv ctx <=>
    !fn inst vs vs' fuel.
      Inv ctx fn inst vs /\ active_inst fn inst vs /\
      inst.inst_opcode = INVOKE /\
      step_inst fuel ctx inst vs = OK vs' ==>
      Inv ctx fn inst vs'
End

Definition codegen_memory_obligations_def:
  codegen_memory_obligations Inv ctx cp <=>
    !fn inst vs1 vs2 fuel.
      Inv ctx fn inst vs1 /\
      MEM fn ctx.ctx_functions /\
      MEM inst (fn_insts fn) ==>
      source_memory_reads_disjoint cp inst vs1 /\
      context_source_memory_writes_disjoint cp inst vs1 /\
      (step_inst fuel ctx inst vs1 = OK vs2 ==>
       context_spill_step_safe cp vs1 vs2)
End

Definition reachable_call_graph_acyclic_def:
  reachable_call_graph_acyclic ctx <=>
    reachable_fcg_acyclic ctx (fcg_analyze ctx)
End

Definition codegen_reachability_package_def:
  codegen_reachability_package Inv ctx initial_vs <=>
    initial_entry_satisfies Inv ctx initial_vs /\
    reachable_inv_closed_under_steps Inv ctx /\
    reachable_inv_closed_under_calls Inv ctx /\
    reachable_inv_closed_under_returns Inv ctx /\
    reachable_inv_closed_under_invoke Inv ctx
End

Definition codegen_context_obligations_def:
  codegen_context_obligations Inv ctx cp <=>
    generate_context_plan ctx = SOME cp /\
    context_plan_layout_wf cp /\
    codegen_ready ctx /\ ctx_wf ctx /\
    reachable_call_graph_acyclic ctx /\
    (!name efn. ctx.ctx_entry = SOME name /\
       lookup_function name ctx.ctx_functions = SOME efn ==>
       entry_fn_no_ret efn) /\
    codegen_memory_obligations Inv ctx cp
End

Theorem initial_entry_satisfies_false[simp]:
  ~initial_entry_satisfies (\ctx fn inst vs. F) ctx initial_vs
Proof
  simp[initial_entry_satisfies_def]
QED

Theorem byte_in_memory_range_zero[simp]:
  ~byte_in_memory_range (off,0) i
Proof
  simp[byte_in_memory_range_def]
QED

Theorem source_memory_read_ranges_INVOKE[simp]:
  source_memory_read_ranges (inst with inst_opcode := INVOKE) vs = []
Proof
  simp[source_memory_read_ranges_def]
QED

Theorem source_memory_read_byte_INVOKE[simp]:
  ~source_memory_read_byte (inst with inst_opcode := INVOKE) vs i
Proof
  simp[source_memory_read_byte_def]
QED

val _ = export_theory();
