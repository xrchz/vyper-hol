(*
 * Pointer Confinement Definitions
 *
 * Structural properties ensuring alloca pointer values don't affect
 * observable program behavior. Used as preconditions for passes that
 * change alloca layout (remove_unused, function_inliner, concretize).
 *
 * TOP-LEVEL:
 *   is_pointer_preserving_op — opcodes that propagate pointer derivation
 *   pointer_use_step         — one step of pointer-specific use chain
 *   pointer_derived_vars     — variables reachable from roots via
 *                              pointer-preserving def-use chains
 *   pointer_confined         — pointer vars only in mem address positions
 *   all_mem_via_pointer      — all memory ops address through pointer vars
 *   alloca_roots             — alloca output variables in a function
 *   alloca_pointer_confined  — pointer_confined specialized to alloca roots
 *
 * pointer_confined requires pointer-derived vars to only appear in
 * memory address positions (via iao_ofst from mem_write_ops/mem_read_ops)
 * or pointer-preserving operations (ADD/SUB/ASSIGN/PHI whose outputs
 * remain pointer-derived).
 *
 * pointer_derived_vars follows only pointer-preserving operations,
 * NOT all def-use chains. MLOAD output from a pointer address is DATA,
 * not a pointer — it can be freely used in any computation.
 *
 * Always true for Vyper-compiled code: alloca outputs are abstract
 * memory offsets used only for MSTORE/MLOAD/MCOPY via ADD.
 *)

Theory pointerConfinedDefs
Ancestors
  passSharedDefs memLocDefs

(* ===== Immutable Operations ===== *)

(* ILOAD/ISTORE retain this classification for pass-specific dispatch, but
   executable semantics now reads and writes ordinary memory. Their address
   operands therefore follow the same pointer-confinement rules as other
   memory operations. *)
Definition is_immutable_op_def:
  is_immutable_op ILOAD = T /\
  is_immutable_op ISTORE = T /\
  is_immutable_op _ = F
End

(* ===== Pointer-Preserving Operations ===== *)

(* Instructions that propagate pointer derivation: their output is
   pointer-derived if any input is. Other instructions (MLOAD, MUL, EQ, ...)
   consume pointer values but produce non-pointer results. *)
Definition is_pointer_preserving_op_def:
  is_pointer_preserving_op ADD = T /\
  is_pointer_preserving_op SUB = T /\
  is_pointer_preserving_op ASSIGN = T /\
  is_pointer_preserving_op PHI = T /\
  is_pointer_preserving_op _ = F
End

(* ===== Pointer-Derived Variables ===== *)

(* One step of pointer-specific use chain: collect outputs of
   pointer-preserving instructions that read a pointer-derived var.
   Unlike use_step (which follows ALL def-use), this only follows
   instructions that propagate pointer identity. *)
Definition pointer_use_step_def:
  pointer_use_step fn vars =
    FLAT (MAP (\bb.
      FLAT (MAP (\inst.
        if is_pointer_preserving_op inst.inst_opcode /\
           EXISTS (\op. case op of Var v => MEM v vars | _ => F)
                  inst.inst_operands
        then inst.inst_outputs
        else [])
        bb.bb_instructions))
      fn.fn_blocks)
End

(* Single step of pointer transitive closure: add newly reachable vars. *)
Definition pointer_use_step_step_def:
  pointer_use_step_step fn vars =
    let new_vars = FILTER (\v. ~MEM v vars) (pointer_use_step fn vars) in
    if new_vars = [] then NONE
    else SOME (vars ++ new_vars)
End

(* Compute transitive closure of pointer-preserving use chain.
   Iterates until fixpoint via OWHILE. *)
Definition pointer_use_vars_def:
  pointer_use_vars fn vars =
    case OWHILE ISL (\v. case pointer_use_step_step fn (OUTL v) of
                           NONE => INR (OUTL v)
                         | SOME vs => INL vs)
                (INL vars) of
      SOME (INR result) => result
    | _ => vars
End

(* Variables transitively reachable from roots via pointer-preserving
   def-use chains only. Root variables are typically alloca outputs.
   Unlike transitive_use_vars, this does NOT follow through MLOAD,
   MUL, EQ, etc. — those consume pointers but don't produce them. *)
Definition pointer_derived_vars_def:
  pointer_derived_vars fn (roots : string set) =
    set (pointer_use_vars fn (SET_TO_LIST roots))
End

(* ===== Pointer Confinement ===== *)

(* Pointer-derived variables are only used in safe positions:
   1. Memory address position (iao_ofst of mem_write_ops/mem_read_ops)
   2. Pointer-preserving operation with outputs still pointer-derived

   This ensures pointer values never reach control flow (JNZ condition),
   storage (SSTORE value), external calls (CALL gas/addr/val), or
   other observable positions.

   Key: checks operand POSITION, not just instruction type.
   MSTORE [addr, value] — pointer in addr (position 0) is fine,
   pointer in value (position 1) is rejected because it could be
   MLOAD'd back and escape through non-memory operations.

   Limitation: rejects programs that apply non-linear operations to
   pointers (AND for alignment, MUL for scaling, EQ for comparison).
   These break the alloca remapping theorem because e.g.
   AND(base+delta, mask) gives different results for different bases.
   pointer_confined correctly rejects them: the pointer-derived var
   appears in a non-mem, non-preserving instruction.
   Vyper never does this — alloca offsets are only manipulated via ADD.
   If future IR needs pointer alignment, the remapping approach would
   need extension (e.g. alignment-preserving remap constraints). *)
Definition pointer_confined_def:
  pointer_confined fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst v.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands /\
      v IN pv ==>
      (?ops. mem_write_ops inst = SOME ops /\ Var v = ops.iao_ofst) \/
      (?ops. mem_read_ops inst = SOME ops /\ Var v = ops.iao_ofst) \/
      (is_pointer_preserving_op inst.inst_opcode /\
        set inst.inst_outputs SUBSET pv)
End

(* ===== All Memory Via Pointer ===== *)

(* Every memory operation's address operand is a pointer-derived variable.
   Complementary to pointer_confined: pointer_confined says pointer vars
   only appear in memory address positions; all_mem_via_pointer says
   memory address positions only contain pointer vars.
   Together: pointer-derived vars <=> memory address operands.
   True for Vyper-compiled code (all memory goes through alloca).
   Becomes false after concretize_mem_loc (which makes offsets literal). *)
Definition all_mem_via_pointer_def:
  all_mem_via_pointer fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst ops.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) ==>
      ?v. ops.iao_ofst = Var v /\ v IN pv
End

(* ===== Alloca Roots ===== *)

(* The set of variables produced by ALLOCA instructions in a function. *)
Definition alloca_roots_def:
  alloca_roots fn =
    { out | ∃inst. MEM inst (fn_insts fn) ∧
                   inst.inst_opcode = ALLOCA ∧
                   inst_output inst = SOME out }
End

(* ===== Affine Pointer Operations ===== *)

(* For ADD and SUB instructions, at most one operand is pointer-derived.
   Prevents ADD(ptr1, ptr2) which produces a value with no well-defined
   displacement from any single alloca region.
   True for Vyper-compiled code: pointer arithmetic is always ptr + const
   or ptr - const, never ptr + ptr or const - ptr. *)
Definition affine_pointer_ops_def:
  affine_pointer_ops fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst op1 op2.
      MEM bb fn.fn_blocks /\
      MEM inst bb.bb_instructions /\
      (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
      inst.inst_operands = [op1; op2] ==>
      ~(?v1 v2. op1 = Var v1 /\ op2 = Var v2 /\ v1 IN pv /\ v2 IN pv) /\
      (inst.inst_opcode = SUB ==>
       !v. op2 = Var v ==> v NOTIN pv)
End

(* ===== PHI Pointer-Variable All-Var ===== *)

(* For PHI instructions where any Var operand is pointer-derived,
   ALL Var operands must also be pointer-derived, and all non-Label
   operands must be Var (no Lit operands).
   Labels are branch selectors (paired with the preceding value operand),
   so they are fine.

   This prevents two counterexamples:
   1. PHI mixes a pv Var branch with a Lit branch: pointer_derived_vars
      marks the output as pv (ANY pv input propagates), but the Lit branch
      delivers a concrete value with no well-defined displacement.
   2. PHI mixes a pv Var branch with a non-pv Var branch: the non-pv Var
      has the same value in both states, but the displacement invariant
      requires it to differ by the remap offset.

   True for Vyper-compiled code: PHI operands come from SSA
   construction, which never mixes alloca-derived and non-alloca-derived
   values in the same PHI. *)
Definition phi_pv_all_var_def:
  phi_pv_all_var fn (roots : string set) <=>
    let pv = pointer_derived_vars fn roots in
    !bb inst.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = PHI /\
      (?v. MEM (Var v) inst.inst_operands /\ v IN pv) ==>
      (!v. MEM (Var v) inst.inst_operands ==> v IN pv) /\
      (!op. MEM op inst.inst_operands ==>
           (?v. op = Var v) \/ (?l. op = Label l))
End

(* ===== Function-Level Pointer Confinement ===== *)

(* A function's alloca pointers are confined: no alloca-derived value
   reaches observable state (control flow, external calls, storage). *)
Definition alloca_pointer_confined_def:
  alloca_pointer_confined fn <=>
    pointer_confined fn (alloca_roots fn)
End
