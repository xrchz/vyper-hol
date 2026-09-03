(*
 * Context-wide code-generation memory relations.
 *
 * The existing codegenRel$memory_rel remains the allocator-local relation
 * used by single-function simulation.  This theory adds the ambient relation
 * needed while caller spill regions remain live across internal calls.
 *)

Theory contextCodegenRel
Ancestors
  codegenRel venomExecSemantics

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
