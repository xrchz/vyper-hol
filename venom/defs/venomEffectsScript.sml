(*
 * Venom Effects System
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * Effects track what state an instruction reads or writes.
 * This is crucial for optimization passes (CSE, DCE, reordering).
 *
 * Ported from vyper/venom/effects.py.
 *
 * TOP-LEVEL:
 *   effect, read_effects, write_effects, effects_independent,
 *   has_conflicting_effects, is_nonidempotent,
 *   fail_class, opcode_fail_class, abort_compatible,
 *   addr_space, effect_of_addr_space
 *
 * Removed (MSIZE sunset #4909): Eff_MSIZE, strip_msize, adj_effects,
 *   read_effects_adj, write_effects_adj, overlap_effects_adj, all_effects_adj
 *)

Theory venomEffects
Ancestors
  venomInst

(* ===== Effect Categories ===== *)

Datatype:
  effect =
    | Eff_STORAGE
    | Eff_TRANSIENT
    | Eff_MEMORY
    | Eff_FMP
    | Eff_IMMUTABLES
    | Eff_RETURNDATA
    | Eff_LOG
    | Eff_BALANCE
    | Eff_EXTCODE
End

Type effects = ``:effect set``

Definition empty_effects_def:
  empty_effects : effects = {}
End

Definition all_effects_def:
  all_effects : effects =
    {Eff_STORAGE; Eff_TRANSIENT; Eff_MEMORY; Eff_FMP;
     Eff_IMMUTABLES; Eff_RETURNDATA; Eff_LOG; Eff_BALANCE; Eff_EXTCODE}
End

(* ===== Read Effects ===== *)

(* Which state components an opcode may read.
 * Matches Python _reads table in effects.py. *)
Definition read_effects_def:
  read_effects SLOAD = {Eff_STORAGE} /\
  read_effects TLOAD = {Eff_TRANSIENT} /\
  read_effects ILOAD = {Eff_IMMUTABLES; Eff_MEMORY} /\
  read_effects MLOAD = {Eff_MEMORY} /\
  read_effects MCOPY = {Eff_MEMORY} /\
  read_effects CALL = all_effects /\
  read_effects DELEGATECALL = all_effects /\
  read_effects STATICCALL = all_effects /\
  read_effects CREATE = all_effects /\
  read_effects CREATE2 = all_effects /\
  read_effects INVOKE = all_effects /\
  read_effects RETURNDATASIZE = {Eff_RETURNDATA} /\
  read_effects RETURNDATACOPY = {Eff_RETURNDATA} /\
  read_effects BALANCE = {Eff_BALANCE} /\
  read_effects SELFBALANCE = {Eff_BALANCE} /\
  read_effects EXTCODECOPY = {Eff_EXTCODE} /\
  read_effects EXTCODESIZE = {Eff_EXTCODE} /\
  read_effects EXTCODEHASH = {Eff_EXTCODE} /\
  read_effects SELFDESTRUCT = {Eff_BALANCE} /\
  read_effects LOG = {Eff_MEMORY} /\
  read_effects REVERT = {Eff_MEMORY} /\
  read_effects SHA3 = {Eff_MEMORY} /\
  read_effects MEMTOP = {Eff_MEMORY} /\
  read_effects RETURN = {Eff_MEMORY} /\
  (* Frame-memory-pointer operations *)
  read_effects GETFMP = {Eff_FMP} /\
  read_effects DALLOCA = {Eff_FMP} /\
  read_effects INITIAL_FMP = {Eff_FMP} /\
  read_effects RETFMP = {Eff_FMP} /\
  read_effects DRET = {Eff_FMP; Eff_MEMORY} /\
  read_effects SETFMP = empty_effects /\
  read_effects BUMP = empty_effects /\
  (* Parameter and data-section metadata are explicit pure reads. *)
  read_effects PARAM = empty_effects /\
  read_effects FMP_PARAM = empty_effects /\
  read_effects RETPC_PARAM = empty_effects /\
  read_effects DLOAD = empty_effects /\
  read_effects DLOADBYTES = empty_effects /\
  read_effects OFFSET = empty_effects /\
  read_effects _ = empty_effects
End

(* ===== Write Effects ===== *)

(* Which state components an opcode may write.
 * Matches Python _writes table in effects.py.
 * ISTORE writes MEMORY (immutables live in memory region).
 * After MSIZE sunset (#4909), no Eff_MSIZE — memory ops just have Eff_MEMORY. *)
Definition write_effects_def:
  (* Storage/transient: no memory involvement *)
  write_effects SSTORE = {Eff_STORAGE} /\
  write_effects TSTORE = {Eff_TRANSIENT} /\
  (* Memory writes *)
  write_effects MSTORE = {Eff_MEMORY} /\
  write_effects MSTORE8 = {Eff_MEMORY} /\
  write_effects ISTORE = {Eff_IMMUTABLES; Eff_MEMORY} /\
  (* External calls *)
  write_effects CALL = all_effects DIFF {Eff_IMMUTABLES} /\
  write_effects DELEGATECALL = all_effects DIFF {Eff_IMMUTABLES} /\
  write_effects STATICCALL = {Eff_MEMORY; Eff_RETURNDATA} /\
  write_effects CREATE = all_effects DIFF {Eff_MEMORY; Eff_IMMUTABLES} /\
  write_effects CREATE2 = all_effects DIFF {Eff_MEMORY; Eff_IMMUTABLES} /\
  write_effects INVOKE = all_effects /\
  (* Logging *)
  write_effects LOG = {Eff_LOG} /\
  (* Memory-writing bulk ops *)
  write_effects DLOADBYTES = {Eff_MEMORY} /\
  (* DLOAD: conservative — at EVM lowering, DLOAD expands memory *)
  write_effects DLOAD = {Eff_MEMORY} /\
  write_effects RETURNDATACOPY = {Eff_MEMORY} /\
  write_effects CALLDATACOPY = {Eff_MEMORY} /\
  write_effects CODECOPY = {Eff_MEMORY} /\
  write_effects EXTCODECOPY = {Eff_MEMORY} /\
  write_effects MCOPY = {Eff_MEMORY} /\
  (* SELFDESTRUCT: transfers balance to beneficiary, zeros own balance *)
  write_effects SELFDESTRUCT = {Eff_BALANCE} /\
  (* Frame-memory-pointer operations *)
  write_effects SETFMP = {Eff_FMP} /\
  write_effects DALLOCA = {Eff_FMP} /\
  write_effects DRET = {Eff_FMP; Eff_MEMORY} /\
  write_effects GETFMP = empty_effects /\
  write_effects RETFMP = empty_effects /\
  write_effects INITIAL_FMP = empty_effects /\
  write_effects BUMP = empty_effects /\
  (* Pure parameter/offset metadata has no state write effect. *)
  write_effects PARAM = empty_effects /\
  write_effects FMP_PARAM = empty_effects /\
  write_effects RETPC_PARAM = empty_effects /\
  write_effects OFFSET = empty_effects /\
  write_effects _ = empty_effects
End

(* ===== Derived Predicates ===== *)

(* Two opcodes can be safely reordered *)
Definition effects_independent_def:
  effects_independent op1 op2 <=>
    DISJOINT (write_effects op1) (read_effects op2 UNION write_effects op2) /\
    DISJOINT (write_effects op2) (read_effects op1 UNION write_effects op1)
End

(* Opcode has conflicting read/write effects on same component *)
Definition has_conflicting_effects_def:
  has_conflicting_effects op <=>
    read_effects op INTER write_effects op <> {}
End

(* Side-effecting opcodes that are never available for CSE *)
Definition is_nonidempotent_def:
  is_nonidempotent CALL = T /\
  is_nonidempotent DELEGATECALL = T /\
  is_nonidempotent STATICCALL = T /\
  is_nonidempotent CREATE = T /\
  is_nonidempotent CREATE2 = T /\
  is_nonidempotent INVOKE = T /\
  is_nonidempotent LOG = T /\
  is_nonidempotent _ = F
End

(* Commutative opcodes: operand order does not affect result.
 * Matches Python COMMUTATIVE_INSTRUCTIONS =
 *   frozenset(["add", "mul", "smul", "or", "xor", "and", "eq"])
 * Note: Python has "smul" but our IR uses MUL for both (SDIV/SMOD are
 * separate but smul is just MUL with sign-extension handled elsewhere). *)
Definition is_commutative_def:
  is_commutative ADD = T /\
  is_commutative MUL = T /\
  is_commutative OR = T /\
  is_commutative XOR = T /\
  is_commutative AND = T /\
  is_commutative EQ = T /\
  is_commutative _ = F
End

(* ===== Abort Compatibility for Reordering ===== *)

(* Failure class of a non-terminator opcode: what non-OK result types
   step_inst can produce (besides Error, which is structural).
   - NoFail: only OK or Error (pure ops, reads, writes)
   - CanRevert: can Abort with Revert_abort (ASSERT)
   - CanExHalt: can Abort with ExHalt_abort (ASSERT_UNREACHABLE, RETURNDATACOPY, INVALID)
   - AnyFail: can Halt or Abort with any type (INVOKE — from callee)
   Note: effects_independent INVOKE INVOKE = F, so AnyFail never pairs with itself. *)
Datatype:
  fail_class = NoFail | CanRevert | CanExHalt | AnyFail
End

Definition opcode_fail_class_def:
  opcode_fail_class ASSERT = CanRevert /\
  opcode_fail_class ASSERT_UNREACHABLE = CanExHalt /\
  opcode_fail_class RETURNDATACOPY = CanExHalt /\
  opcode_fail_class INVALID = CanExHalt /\
  opcode_fail_class INVOKE = AnyFail /\
  opcode_fail_class _ = NoFail
End

(* Two opcodes have compatible non-OK behavior: either at least one
   never fails, or both fail with the same class.
   Required for instruction reordering to preserve abort types. *)
Definition abort_compatible_def:
  abort_compatible op1 op2 <=>
    opcode_fail_class op1 = NoFail \/
    opcode_fail_class op2 = NoFail \/
    opcode_fail_class op1 = opcode_fail_class op2
End

(* ===== Address Spaces ===== *)

(* Matches vyper/evm/address_space.py *)
Datatype:
  addr_space =
    AddrSp_Memory | AddrSp_Storage | AddrSp_Transient |
    AddrSp_Calldata | AddrSp_Immutables | AddrSp_Data |
    AddrSp_Code | AddrSp_Returndata
End

(* Partial: only addr spaces with mutable state have effects.
 * Matches Python to_addr_space (which maps effect→addr_space for these 4). *)
Definition effect_of_addr_space_def:
  effect_of_addr_space AddrSp_Memory = SOME Eff_MEMORY /\
  effect_of_addr_space AddrSp_Storage = SOME Eff_STORAGE /\
  effect_of_addr_space AddrSp_Transient = SOME Eff_TRANSIENT /\
  effect_of_addr_space AddrSp_Immutables = SOME Eff_IMMUTABLES /\
  effect_of_addr_space _ = NONE
End

(* Word scale per address space: matches Python AddrSpace.word_scale.
   Storage/transient are word-addressed (1 slot per key),
   all others are byte-addressed (32 bytes per word). *)
Definition addr_space_word_scale_def:
  addr_space_word_scale AddrSp_Storage = 1n /\
  addr_space_word_scale AddrSp_Transient = 1n /\
  addr_space_word_scale _ = 32n
End
