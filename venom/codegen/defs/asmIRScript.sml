(*
 * Assembly IR Types
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Intermediate representation between Venom codegen and EVM bytecode.
 * Defines assembly instruction types and the stack operation plan type.
 *
 * TOP-LEVEL:
 *   asm_inst               — assembly instruction type
 *   stack_op               — stack plan operation type
 *   data_item, data_section — data segment types
 *   encode_num_bytes       — number → big-endian byte list
 *   venom_to_evm_name      — opcode → EVM name mapping
 *   data_segment_asm       — data segment → asm_inst list
 *   get_non_label_operands — filter out label operands
 *)

Theory asmIR
Ancestors
  stackModel venomEffects cfgTransform venomInst

(* =========================================================================
   Assembly Instructions
   Produced by plan executor, consumed by symbol resolution.
   ========================================================================= *)

Datatype:
  asm_inst =
  | AsmOp string                    (* EVM opcode: "ADD", "SWAP3", etc. *)
  | AsmPush (word8 list)            (* PUSH<n> with literal bytes *)
  | AsmPushLabel string             (* push label address (resolved later) *)
  | AsmPushOfst string num          (* push (label_address + offset) *)
  | AsmLabel string                 (* JUMPDEST marker *)
  | AsmDataHeader string            (* data section start *)
  | AsmDataItem (word8 list)        (* data section content *)
  | AsmDataLabel string             (* data section label reference *)
End

(* =========================================================================
   Stack Plan Operations
   Produced by plan generator, consumed by plan executor.
   ========================================================================= *)

Datatype:
  stack_op =
  | SOPush operand                  (* push literal/label onto stack *)
  | SOPop num                       (* pop n items from TOS *)
  | SOSwap num                      (* SWAP: 1-based distance (1..16) *)
  | SODup num                       (* DUP: 1-based distance (1..16) *)
  | SOPoke num operand              (* update stack model at dist, no EVM (phi) *)
  | SOSpill num                     (* spill TOS to memory offset *)
  | SORestore num                   (* restore from memory offset to TOS *)
  | SOEmit string                   (* EVM opcode name *)
  | SOInitialFmp                    (* deferred context-wide initial FMP *)
  | SOLabel string                  (* JUMPDEST label *)
  | SOPushLabel string              (* push label address *)
  | SOPushOfst string num           (* push (label + offset) *)
End

(* =========================================================================
   Byte Encoding Utility
   Encode a number as minimal big-endian byte list.
   Shared by plan executor (spill offsets) and symbol resolution (labels).
   ========================================================================= *)

Definition encode_num_bytes_def:
  encode_num_bytes (n:num) =
    if n = 0 then ([] : byte list)
    else SNOC (n2w n : byte) (encode_num_bytes (n DIV 256))
End

(* =========================================================================
   Venom Opcode → EVM Name Mapping
   For one-to-one instructions.
   ========================================================================= *)

Definition venom_to_evm_name_def:
  venom_to_evm_name ADD = SOME "ADD" ∧
  venom_to_evm_name SUB = SOME "SUB" ∧
  venom_to_evm_name MUL = SOME "MUL" ∧
  venom_to_evm_name Div = SOME "DIV" ∧
  venom_to_evm_name SDIV = SOME "SDIV" ∧
  venom_to_evm_name Mod = SOME "MOD" ∧
  venom_to_evm_name SMOD = SOME "SMOD" ∧
  venom_to_evm_name Exp = SOME "EXP" ∧
  venom_to_evm_name ADDMOD = SOME "ADDMOD" ∧
  venom_to_evm_name MULMOD = SOME "MULMOD" ∧
  venom_to_evm_name EQ = SOME "EQ" ∧
  venom_to_evm_name LT = SOME "LT" ∧
  venom_to_evm_name GT = SOME "GT" ∧
  venom_to_evm_name SLT = SOME "SLT" ∧
  venom_to_evm_name SGT = SOME "SGT" ∧
  venom_to_evm_name ISZERO = SOME "ISZERO" ∧
  venom_to_evm_name AND = SOME "AND" ∧
  venom_to_evm_name OR = SOME "OR" ∧
  venom_to_evm_name XOR = SOME "XOR" ∧
  venom_to_evm_name NOT = SOME "NOT" ∧
  venom_to_evm_name SHL = SOME "SHL" ∧
  venom_to_evm_name SHR = SOME "SHR" ∧
  venom_to_evm_name SAR = SOME "SAR" ∧
  venom_to_evm_name SIGNEXTEND = SOME "SIGNEXTEND" ∧
  venom_to_evm_name BYTE = SOME "BYTE" ∧
  venom_to_evm_name MLOAD = SOME "MLOAD" ∧
  venom_to_evm_name MSTORE = SOME "MSTORE" ∧
  venom_to_evm_name MSTORE8 = SOME "MSTORE8" ∧
  venom_to_evm_name MCOPY = SOME "MCOPY" ∧
  venom_to_evm_name MEMTOP = SOME "MSIZE" ∧
  venom_to_evm_name SLOAD = SOME "SLOAD" ∧
  venom_to_evm_name SSTORE = SOME "SSTORE" ∧
  venom_to_evm_name TLOAD = SOME "TLOAD" ∧
  venom_to_evm_name TSTORE = SOME "TSTORE" ∧
  venom_to_evm_name CALLER = SOME "CALLER" ∧
  venom_to_evm_name CALLVALUE = SOME "CALLVALUE" ∧
  venom_to_evm_name CALLDATALOAD = SOME "CALLDATALOAD" ∧
  venom_to_evm_name CALLDATASIZE = SOME "CALLDATASIZE" ∧
  venom_to_evm_name CALLDATACOPY = SOME "CALLDATACOPY" ∧
  venom_to_evm_name ADDRESS = SOME "ADDRESS" ∧
  venom_to_evm_name ORIGIN = SOME "ORIGIN" ∧
  venom_to_evm_name GASPRICE = SOME "GASPRICE" ∧
  venom_to_evm_name GAS = SOME "GAS" ∧
  venom_to_evm_name GASLIMIT = SOME "GASLIMIT" ∧
  venom_to_evm_name COINBASE = SOME "COINBASE" ∧
  venom_to_evm_name TIMESTAMP = SOME "TIMESTAMP" ∧
  venom_to_evm_name NUMBER = SOME "NUMBER" ∧
  venom_to_evm_name PREVRANDAO = SOME "PREVRANDAO" ∧
  venom_to_evm_name CHAINID = SOME "CHAINID" ∧
  venom_to_evm_name SELFBALANCE = SOME "SELFBALANCE" ∧
  venom_to_evm_name BALANCE = SOME "BALANCE" ∧
  venom_to_evm_name BLOCKHASH = SOME "BLOCKHASH" ∧
  venom_to_evm_name BASEFEE = SOME "BASEFEE" ∧
  venom_to_evm_name BLOBHASH = SOME "BLOBHASH" ∧
  venom_to_evm_name BLOBBASEFEE = SOME "BLOBBASEFEE" ∧
  venom_to_evm_name CODESIZE = SOME "CODESIZE" ∧
  venom_to_evm_name CODECOPY = SOME "CODECOPY" ∧
  venom_to_evm_name EXTCODESIZE = SOME "EXTCODESIZE" ∧
  venom_to_evm_name EXTCODEHASH = SOME "EXTCODEHASH" ∧
  venom_to_evm_name EXTCODECOPY = SOME "EXTCODECOPY" ∧
  venom_to_evm_name RETURNDATASIZE = SOME "RETURNDATASIZE" ∧
  venom_to_evm_name RETURNDATACOPY = SOME "RETURNDATACOPY" ∧
  venom_to_evm_name SHA3 = SOME "SHA3" ∧
  venom_to_evm_name CALL = SOME "CALL" ∧
  venom_to_evm_name STATICCALL = SOME "STATICCALL" ∧
  venom_to_evm_name DELEGATECALL = SOME "DELEGATECALL" ∧
  venom_to_evm_name CREATE = SOME "CREATE" ∧
  venom_to_evm_name CREATE2 = SOME "CREATE2" ∧
  venom_to_evm_name SELFDESTRUCT = SOME "SELFDESTRUCT" ∧
  venom_to_evm_name INVALID = SOME "INVALID" ∧
  venom_to_evm_name REVERT = SOME "REVERT" ∧
  venom_to_evm_name STOP = SOME "STOP" ∧
  (* Opcodes with special handling — not 1:1 *)
  venom_to_evm_name ILOAD = SOME "MLOAD" ∧
  venom_to_evm_name ISTORE = NONE ∧         (* needs SWAP1+MSTORE *)
  venom_to_evm_name RETURN = SOME "RETURN" ∧
  (* SSA/control flow opcodes — no direct EVM equivalent *)
  venom_to_evm_name PHI = NONE ∧
  venom_to_evm_name PARAM = NONE ∧
  venom_to_evm_name ASSIGN = NONE ∧
  venom_to_evm_name NOP = NONE ∧
  venom_to_evm_name JMP = NONE ∧
  venom_to_evm_name JNZ = NONE ∧
  venom_to_evm_name DJMP = NONE ∧
  (* Extended-core operations must be lowered before legacy codegen. *)
  venom_to_evm_name DALLOCA = NONE ∧
  venom_to_evm_name DRET = NONE ∧
  venom_to_evm_name GETFMP = NONE ∧
  venom_to_evm_name SETFMP = NONE ∧
  venom_to_evm_name RETFMP = NONE ∧
  venom_to_evm_name INITIAL_FMP = NONE ∧
  venom_to_evm_name BUMP = NONE ∧
  venom_to_evm_name INVOKE = NONE ∧
  venom_to_evm_name FMP_PARAM = NONE ∧
  venom_to_evm_name RETPC_PARAM = NONE ∧
  venom_to_evm_name RET = NONE ∧
  venom_to_evm_name LOG = NONE ∧             (* needs LOG{n} *)
  venom_to_evm_name ASSERT = NONE ∧
  venom_to_evm_name ASSERT_UNREACHABLE = NONE ∧
  venom_to_evm_name ALLOCA = NONE ∧
  venom_to_evm_name OFFSET = NONE ∧
  venom_to_evm_name SINK = NONE ∧
  venom_to_evm_name DLOAD = NONE ∧
  venom_to_evm_name DLOADBYTES = NONE
End

(* =========================================================================
   Instruction Operand Helpers
   ========================================================================= *)

Definition get_non_label_operands_def:
  get_non_label_operands inst =
    FILTER (λop. case op of Label _ => F | _ => T) inst.inst_operands
End

Definition get_label_operands_def:
  get_label_operands inst =
    FILTER (λop. case op of Label _ => T | _ => F) inst.inst_operands
End

Definition label_of_def:
  label_of (Label l) = l ∧
  label_of _ = ""
End

(* =========================================================================
   Data Segment Assembly
   data_item/data_section types are in venomInstTheory.
   ========================================================================= *)

(* Convert data segment to assembly instructions *)
Definition data_section_asm_def:
  data_section_asm ds =
    AsmDataHeader ds.ds_label ::
    MAP (λdi. case di of
      DataBytes bs => AsmDataItem bs
    | DataLabel l => AsmDataLabel l) ds.ds_items
End

Definition data_segment_asm_def:
  data_segment_asm segments =
    FLAT (MAP data_section_asm segments)
End
