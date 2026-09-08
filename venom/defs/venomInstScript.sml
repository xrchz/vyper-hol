(*
 * Venom Instructions
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * This theory defines the instruction set for Venom IR.
 *)

Theory venomInst
Ancestors
  venomState
  venomPolicyTypes
Libs
  listTheory

(* --------------------------------------------------------------------------
   Instruction Opcodes

   Venom opcodes closely mirror EVM but with some additions for
   SSA form (phi, param, assign) and internal function calls (invoke, ret).
   -------------------------------------------------------------------------- *)

Datatype:
  opcode =
    (* Arithmetic - note: Div/Mod to avoid HOL4 name clash *)
    | ADD | SUB | MUL | Div | SDIV | Mod | SMOD | Exp
    | ADDMOD | MULMOD
    (* Comparison *)
    | EQ | LT | GT | SLT | SGT | ISZERO
    (* Bitwise *)
    | AND | OR | XOR | NOT | SHL | SHR | SAR | SIGNEXTEND | BYTE
    (* Memory *)
    | MLOAD | MSTORE | MSTORE8 | MCOPY | MEMTOP
    (* Storage *)
    | SLOAD | SSTORE
    (* Transient storage *)
    | TLOAD | TSTORE
    (* Immutables (Vyper-specific) *)
    | ILOAD | ISTORE
    (* Control flow *)
    | JMP | JNZ | DJMP | RET | RETURN | REVERT | STOP | SINK
    (* SSA/IR-specific *)
    | PHI | PARAM | ASSIGN | NOP
    (* Allocation and frame-memory-pointer operations *)
    | ALLOCA | DALLOCA
    | DRET | GETFMP | SETFMP | RETFMP | INITIAL_FMP | BUMP
    (* Internal function calls and hidden physical parameters *)
    | INVOKE | FMP_PARAM | RETPC_PARAM
    (* Environment *)
    | CALLER | CALLVALUE | CALLDATALOAD | CALLDATASIZE | CALLDATACOPY
    | ADDRESS | ORIGIN | GASPRICE | GAS | GASLIMIT
    | COINBASE | TIMESTAMP | NUMBER | PREVRANDAO | CHAINID
    | SELFBALANCE | BALANCE | BLOCKHASH | BASEFEE
    | CODESIZE | CODECOPY | EXTCODESIZE | EXTCODEHASH | EXTCODECOPY
    | RETURNDATASIZE | RETURNDATACOPY
    | BLOBHASH | BLOBBASEFEE
    (* Hashing *)
    | SHA3
    (* External calls *)
    | CALL | STATICCALL | DELEGATECALL | CREATE | CREATE2
    (* Logging *)
    | LOG
    (* Other *)
    | SELFDESTRUCT | INVALID
    (* Assertions (Vyper-specific) *)
    | ASSERT | ASSERT_UNREACHABLE
    (* Data section access (Vyper-specific) *)
    | DLOAD | DLOADBYTES | OFFSET
End

(* --------------------------------------------------------------------------
   Instructions

   Each instruction has:
   - id: unique identifier (models object identity from Python)
   - opcode: the operation to perform
   - operands: list of input operands (rightmost = top of conceptual stack)
   - outputs: list of output variable names (SSA)

   Most instructions have 0 or 1 output. The invoke opcode can have multiple
   outputs for multi-return internal function calls.

   The inst_id is used to distinguish instructions that may have identical
   fields but are different objects. This is important for passes that
   track visited instructions or build instruction maps.
   -------------------------------------------------------------------------- *)

Datatype:
  instruction = <|
    inst_id : num;
    inst_opcode : opcode;
    inst_operands : operand list;
    inst_outputs : string list
  |>
End

(* Construct an instruction with a given ID *)
Definition mk_inst_def:
  mk_inst id op ops outs = <|
    inst_id := id;
    inst_opcode := op;
    inst_operands := ops;
    inst_outputs := outs
  |>
End

(* Helper: get single output (for instructions with exactly one output) *)
Definition inst_output_def:
  inst_output inst =
    case inst.inst_outputs of
      [out] => SOME out
    | _ => NONE
End

(* Helper: check if instruction has outputs *)
Definition has_outputs_def:
  has_outputs inst = ~NULL inst.inst_outputs
End

(* --------------------------------------------------------------------------
   Basic Block

   A basic block is a sequence of instructions with:
   - A label for control flow
   - Phi nodes at the start (if any)
   - Body instructions
   - A terminator at the end
   -------------------------------------------------------------------------- *)

Datatype:
  basic_block = <|
    bb_label : string;
    bb_instructions : instruction list
  |>
End

(* --------------------------------------------------------------------------
   Function

   An IR function contains its control-flow blocks together with independently
   owned identity, static-layout, and FMP-convention metadata.
   -------------------------------------------------------------------------- *)

Datatype:
  internal_call_abi = <|
    ica_has_memory_return_buffer : bool option;
    ica_user_return_count : num option
  |>
End

Datatype:
  fmp_signature = <|
    fms_has_fmp_param : bool;
    fms_publishes : bool
  |>
End

Datatype:
  ir_function = <|
    fn_name : string;
    fn_blocks : basic_block list;
    fn_call_abi : internal_call_abi;
    fn_noinline : bool;
    fn_forced_alloc_positions : (num,num) fmap;
    fn_eom : num option;
    fn_fmp_signature : fmp_signature option
  |>
End

Definition default_internal_call_abi_def:
  default_internal_call_abi = <|
    ica_has_memory_return_buffer := NONE;
    ica_user_return_count := NONE
  |>
End

Definition mk_raw_function_def:
  mk_raw_function name blocks = <|
    fn_name := name;
    fn_blocks := blocks;
    fn_call_abi := default_internal_call_abi;
    fn_noinline := F;
    fn_forced_alloc_positions := FEMPTY;
    fn_eom := NONE;
    fn_fmp_signature := NONE
  |>
End

(* --------------------------------------------------------------------------
   Context (whole program)

   Contains multiple functions, an optional entry point, and globally reserved
   static-layout intervals.

   NOTE: Python IRContext also has data_segment : list[DataSection] containing
   label references and raw bytes (for selector dispatch tables, deploy code,
   CBOR metadata). Passes that rename labels update data_segment too
   (base_pass.py _replace_all_labels). This is deferred until venom_to_bytecode
   is specified — data segment labels resolve to code offsets that depend on
   the bytecode layout. The lower_dload pass transforms DLOAD/DLOADBYTES
   into concrete memory operations using these offsets.
   -------------------------------------------------------------------------- *)

Datatype:
  venom_context = <|
    ctx_functions : ir_function list;
    ctx_entry : string option;
    ctx_global_reserved : (num # num) list
  |>
End

Definition mk_venom_context_def:
  mk_venom_context fns entry = <|
    ctx_functions := fns;
    ctx_entry := entry;
    ctx_global_reserved := []
  |>
End

(* Metadata ownership is deliberately split by the phase that owns each field. *)
Definition fn_identity_metadata_eq_def:
  fn_identity_metadata_eq f g <=>
    f.fn_name = g.fn_name /\
    f.fn_call_abi = g.fn_call_abi /\
    f.fn_noinline = g.fn_noinline
End

Definition fn_static_input_eq_def:
  fn_static_input_eq f g <=>
    f.fn_forced_alloc_positions = g.fn_forced_alloc_positions
End

Definition fn_static_layout_eq_def:
  fn_static_layout_eq f g <=> f.fn_eom = g.fn_eom
End

Definition fn_fmp_convention_eq_def:
  fn_fmp_convention_eq f g <=>
    f.fn_fmp_signature = g.fn_fmp_signature
End

Theorem mk_raw_function_metadata:
  !name blocks.
    (mk_raw_function name blocks).fn_call_abi = default_internal_call_abi /\
    (mk_raw_function name blocks).fn_noinline = F /\
    (mk_raw_function name blocks).fn_forced_alloc_positions = FEMPTY /\
    (mk_raw_function name blocks).fn_eom = NONE /\
    (mk_raw_function name blocks).fn_eom <> SOME 0 /\
    (mk_raw_function name blocks).fn_fmp_signature = NONE
Proof
  simp[mk_raw_function_def]
QED

Theorem fn_metadata_eq_refl:
  !f.
    fn_identity_metadata_eq f f /\
    fn_static_input_eq f f /\
    fn_static_layout_eq f f /\
    fn_fmp_convention_eq f f
Proof
  simp[fn_identity_metadata_eq_def, fn_static_input_eq_def,
       fn_static_layout_eq_def, fn_fmp_convention_eq_def]
QED

(* --------------------------------------------------------------------------
   Data segment types (shared between lowering and codegen)
   -------------------------------------------------------------------------- *)

Datatype:
  data_item = DataBytes (word8 list) | DataLabel string
End

Datatype:
  data_section = <|
    ds_label : string;
    ds_items : data_item list
  |>
End

(* --------------------------------------------------------------------------
   Operand helpers
   -------------------------------------------------------------------------- *)

(* Extract variable name from an operand, if it is a Var. *)
Definition operand_var_def:
  operand_var (Var v) = SOME v ∧
  operand_var _ = NONE
End

(* All variable names referenced by a list of operands. *)
Definition operand_vars_def:
  operand_vars [] = [] ∧
  operand_vars (op::ops) =
    case operand_var op of
      NONE => operand_vars ops
    | SOME v => v :: operand_vars ops
End

(* Variables used (read) by an instruction. *)
Definition inst_uses_def:
  inst_uses inst = operand_vars inst.inst_operands
End

(* Variables defined (written) by an instruction. *)
Definition inst_defs_def:
  inst_defs inst = inst.inst_outputs
End

(* Extract (label, var) pairs from PHI operands.
   PHI format: Label l1, Var v1, Label l2, Var v2, ... *)
Definition phi_pairs_def:
  phi_pairs [] = [] ∧
  phi_pairs [_] = [] ∧
  phi_pairs (Label l :: Var v :: rest) = (l, v) :: phi_pairs rest ∧
  phi_pairs (_ :: _ :: rest) = phi_pairs rest
End

(* --------------------------------------------------------------------------
   Instruction Classification
   -------------------------------------------------------------------------- *)

(* Terminators end a basic block *)
Definition is_terminator_def:
  is_terminator JMP = T /\
  is_terminator JNZ = T /\
  is_terminator DJMP = T /\
  is_terminator RET = T /\
  is_terminator RETURN = T /\
  is_terminator REVERT = T /\
  is_terminator STOP = T /\
  is_terminator SINK = T /\
  is_terminator SELFDESTRUCT = T /\
  is_terminator INVALID = T /\
  is_terminator DRET = T /\
  is_terminator RETFMP = T /\
  is_terminator DALLOCA = F /\
  is_terminator GETFMP = F /\
  is_terminator SETFMP = F /\
  is_terminator INITIAL_FMP = F /\
  is_terminator BUMP = F /\
  is_terminator FMP_PARAM = F /\
  is_terminator RETPC_PARAM = F /\
  is_terminator _ = F
End

(* Opcodes whose operands reference block labels (terminators + PHI).
   Used by subst_block_labels to restrict label substitution. *)
Definition is_block_label_opcode_def:
  is_block_label_opcode (opc : opcode) ⇔
    is_terminator opc ∨ opc = PHI
End

(* Pseudo-instructions: not real operations, just SSA bookkeeping.
 * Matches Python IRInstruction.is_pseudo (phi, param, source).
 * We omit "source" (test-only opcode not in our IR). *)
Definition is_pseudo_def:
  is_pseudo PHI = T /\
  is_pseudo PARAM = T /\
  is_pseudo FMP_PARAM = T /\
  is_pseudo RETPC_PARAM = T /\
  is_pseudo DALLOCA = F /\
  is_pseudo DRET = F /\
  is_pseudo GETFMP = F /\
  is_pseudo SETFMP = F /\
  is_pseudo RETFMP = F /\
  is_pseudo INITIAL_FMP = F /\
  is_pseudo BUMP = F /\
  is_pseudo _ = F
End

(* Volatile instructions must not be removed even if their outputs
   are unused — they have observable side effects or control flow.
   Matches Python VOLATILE_INSTRUCTIONS frozenset in basicblock.py. *)
Definition is_volatile_def:
  is_volatile PARAM = T /\
  is_volatile CALL = T /\
  is_volatile STATICCALL = T /\
  is_volatile DELEGATECALL = T /\
  is_volatile CREATE = T /\
  is_volatile CREATE2 = T /\
  is_volatile INVOKE = T /\
  is_volatile SSTORE = T /\
  is_volatile ISTORE = T /\
  is_volatile TSTORE = T /\
  is_volatile MSTORE = T /\
  is_volatile MSTORE8 = T /\
  is_volatile CALLDATACOPY = T /\
  is_volatile MCOPY = T /\
  is_volatile EXTCODECOPY = T /\
  is_volatile RETURNDATACOPY = T /\
  is_volatile CODECOPY = T /\
  is_volatile DLOADBYTES = T /\
  is_volatile RETURN = T /\
  is_volatile RET = T /\
  is_volatile SINK = T /\
  is_volatile JMP = T /\
  is_volatile JNZ = T /\
  is_volatile DJMP = T /\
  is_volatile LOG = T /\
  is_volatile SELFDESTRUCT = T /\
  is_volatile INVALID = T /\
  is_volatile REVERT = T /\
  is_volatile ASSERT = T /\
  is_volatile ASSERT_UNREACHABLE = T /\
  is_volatile STOP = T /\
  is_volatile DRET = T /\
  is_volatile RETFMP = T /\
  is_volatile FMP_PARAM = T /\
  is_volatile RETPC_PARAM = T /\
  is_volatile DALLOCA = F /\
  is_volatile GETFMP = F /\
  is_volatile SETFMP = F /\
  is_volatile INITIAL_FMP = F /\
  is_volatile BUMP = F /\
  is_volatile _ = F
End

(* Effect-free opcodes: only modify the output variable, nothing else.
   Includes pure arithmetic, env/state reads, SSA ops, and NOP. *)
Definition is_effect_free_op_def:
  (* Pure arithmetic / logic (exec_pure1/2/3) *)
  is_effect_free_op ADD = T /\
  is_effect_free_op SUB = T /\
  is_effect_free_op MUL = T /\
  is_effect_free_op Div = T /\
  is_effect_free_op SDIV = T /\
  is_effect_free_op Mod = T /\
  is_effect_free_op SMOD = T /\
  is_effect_free_op Exp = T /\
  is_effect_free_op ADDMOD = T /\
  is_effect_free_op MULMOD = T /\
  is_effect_free_op EQ = T /\
  is_effect_free_op LT = T /\
  is_effect_free_op GT = T /\
  is_effect_free_op SLT = T /\
  is_effect_free_op SGT = T /\
  is_effect_free_op ISZERO = T /\
  is_effect_free_op AND = T /\
  is_effect_free_op OR = T /\
  is_effect_free_op XOR = T /\
  is_effect_free_op NOT = T /\
  is_effect_free_op SHL = T /\
  is_effect_free_op SHR = T /\
  is_effect_free_op SAR = T /\
  is_effect_free_op SIGNEXTEND = T /\
  is_effect_free_op BYTE = T /\

  (* State reads (exec_read0/1) *)
  is_effect_free_op MLOAD = T /\
  is_effect_free_op SLOAD = T /\
  is_effect_free_op TLOAD = T /\
  is_effect_free_op ILOAD = T /\
  is_effect_free_op DLOAD = T /\
  is_effect_free_op MEMTOP = T /\
  is_effect_free_op SHA3 = T /\
  (* Environment reads (exec_read0/1) *)
  is_effect_free_op CALLER = T /\
  is_effect_free_op ADDRESS = T /\
  is_effect_free_op CALLVALUE = T /\
  is_effect_free_op GAS = T /\
  is_effect_free_op ORIGIN = T /\
  is_effect_free_op GASPRICE = T /\
  is_effect_free_op CHAINID = T /\
  is_effect_free_op COINBASE = T /\
  is_effect_free_op TIMESTAMP = T /\
  is_effect_free_op NUMBER = T /\
  is_effect_free_op PREVRANDAO = T /\
  is_effect_free_op GASLIMIT = T /\
  is_effect_free_op BASEFEE = T /\
  is_effect_free_op BLOBBASEFEE = T /\
  is_effect_free_op BLOCKHASH = T /\
  is_effect_free_op BLOBHASH = T /\
  is_effect_free_op BALANCE = T /\
  is_effect_free_op SELFBALANCE = T /\
  is_effect_free_op CALLDATASIZE = T /\
  is_effect_free_op CALLDATALOAD = T /\
  is_effect_free_op RETURNDATASIZE = T /\
  is_effect_free_op CODESIZE = T /\
  is_effect_free_op EXTCODESIZE = T /\
  is_effect_free_op EXTCODEHASH = T /\
  (* SSA bookkeeping *)
  is_effect_free_op ASSIGN = T /\
  is_effect_free_op PHI = T /\
  is_effect_free_op PARAM = T /\
  is_effect_free_op FMP_PARAM = T /\
  is_effect_free_op RETPC_PARAM = T /\
  is_effect_free_op OFFSET = T /\
  (* FMP value reads/arithmetic that do not mutate non-output state *)
  is_effect_free_op GETFMP = T /\
  is_effect_free_op INITIAL_FMP = T /\
  is_effect_free_op BUMP = T /\
  (* No-op (no outputs, no state change, no side effects) *)
  is_effect_free_op NOP = T /\
  (* Reviewed stateful FMP operations *)
  is_effect_free_op DALLOCA = F /\
  is_effect_free_op DRET = F /\
  is_effect_free_op SETFMP = F /\
  is_effect_free_op RETFMP = F /\
  (* Everything else *)
  is_effect_free_op _ = F
End

(* Memory-writing opcodes: modify vs_memory (and possibly output var) *)
Definition is_mem_write_op_def:
  is_mem_write_op MSTORE = T /\
  is_mem_write_op MSTORE8 = T /\
  is_mem_write_op MCOPY = T /\
  is_mem_write_op CALLDATACOPY = T /\
  is_mem_write_op RETURNDATACOPY = T /\
  is_mem_write_op CODECOPY = T /\
  is_mem_write_op EXTCODECOPY = T /\
  is_mem_write_op DLOADBYTES = T /\
  is_mem_write_op DRET = T /\
  is_mem_write_op DALLOCA = F /\
  is_mem_write_op GETFMP = F /\
  is_mem_write_op SETFMP = F /\
  is_mem_write_op RETFMP = F /\
  is_mem_write_op INITIAL_FMP = F /\
  is_mem_write_op BUMP = F /\
  is_mem_write_op FMP_PARAM = F /\
  is_mem_write_op RETPC_PARAM = F /\
  is_mem_write_op _ = F
End

(* Allocation opcodes: modify vs_allocas *)
Definition is_alloca_op_def:
  is_alloca_op ALLOCA = T /\
  is_alloca_op DALLOCA = F /\
  is_alloca_op DRET = F /\
  is_alloca_op GETFMP = F /\
  is_alloca_op SETFMP = F /\
  is_alloca_op RETFMP = F /\
  is_alloca_op INITIAL_FMP = F /\
  is_alloca_op BUMP = F /\
  is_alloca_op FMP_PARAM = F /\
  is_alloca_op RETPC_PARAM = F /\
  is_alloca_op _ = F
End

(* External call opcodes: modify multiple state fields *)
Definition is_ext_call_op_def:
  is_ext_call_op CALL = T /\
  is_ext_call_op STATICCALL = T /\
  is_ext_call_op DELEGATECALL = T /\
  is_ext_call_op CREATE = T /\
  is_ext_call_op CREATE2 = T /\
  is_ext_call_op DALLOCA = F /\
  is_ext_call_op DRET = F /\
  is_ext_call_op GETFMP = F /\
  is_ext_call_op SETFMP = F /\
  is_ext_call_op RETFMP = F /\
  is_ext_call_op INITIAL_FMP = F /\
  is_ext_call_op BUMP = F /\
  is_ext_call_op FMP_PARAM = F /\
  is_ext_call_op RETPC_PARAM = F /\
  is_ext_call_op _ = F
End

(* Raw FMP operations are eliminated by the FMP lowering boundary. *)
Definition is_raw_fmp_opcode_def:
  is_raw_fmp_opcode DALLOCA = T /\
  is_raw_fmp_opcode DRET = T /\
  is_raw_fmp_opcode GETFMP = T /\
  is_raw_fmp_opcode SETFMP = T /\
  is_raw_fmp_opcode RETFMP = T /\
  is_raw_fmp_opcode INITIAL_FMP = F /\
  is_raw_fmp_opcode BUMP = F /\
  is_raw_fmp_opcode FMP_PARAM = F /\
  is_raw_fmp_opcode RETPC_PARAM = F /\
  is_raw_fmp_opcode _ = F
End

(* Canonical classification for all parameter-like pseudo instructions. *)
Definition is_param_opcode_def:
  is_param_opcode PARAM = T /\
  is_param_opcode FMP_PARAM = T /\
  is_param_opcode RETPC_PARAM = T /\
  is_param_opcode _ = F
End

Theorem is_param_opcode_iff:
  is_param_opcode op <=>
    (op = PARAM \/ op = FMP_PARAM \/ op = RETPC_PARAM)
Proof
  Cases_on `op` >> simp[is_param_opcode_def]
QED

(* Compatibility classifier for the two hidden physical parameters only. *)
Definition is_fmp_param_opcode_def:
  is_fmp_param_opcode FMP_PARAM = T /\
  is_fmp_param_opcode RETPC_PARAM = T /\
  is_fmp_param_opcode DALLOCA = F /\
  is_fmp_param_opcode DRET = F /\
  is_fmp_param_opcode GETFMP = F /\
  is_fmp_param_opcode SETFMP = F /\
  is_fmp_param_opcode RETFMP = F /\
  is_fmp_param_opcode INITIAL_FMP = F /\
  is_fmp_param_opcode BUMP = F /\
  is_fmp_param_opcode _ = F
End

(* --------------------------------------------------------------------------
   Lookup Functions
   -------------------------------------------------------------------------- *)

(* Find a basic block by label *)
Definition lookup_block_def:
  lookup_block lbl bbs = FIND (\bb. bb.bb_label = lbl) bbs
End

(* Find a function by name *)
Definition lookup_function_def:
  lookup_function name fns = FIND (\f. f.fn_name = name) fns
End

Theorem lookup_function_mem:
  lookup_function name fns = SOME func ==>
  MEM name (MAP (\f. f.fn_name) fns)
Proof
  Induct_on `fns` >> rw[lookup_function_def, FIND_thm]
QED

Theorem lookup_function_not_mem:
  lookup_function name fns = NONE ==>
  ~MEM name (MAP (\f. f.fn_name) fns)
Proof
  Induct_on `fns` >> rw[lookup_function_def, FIND_thm]
QED

Theorem lookup_function_MEM:
  !name fns fn. lookup_function name fns = SOME fn ==> MEM fn fns
Proof
  Induct_on `fns` >> rw[lookup_function_def, FIND_thm] >>
  gvs[lookup_function_def] >> res_tac >> simp[]
QED

(* lookup_function commutes with MAP when f preserves fn_name *)
Theorem lookup_function_map:
  !name fns g.
    (!fn. (g fn).fn_name = fn.fn_name) ==>
    lookup_function name (MAP g fns) =
      OPTION_MAP g (lookup_function name fns)
Proof
  Induct_on `fns` >>
  rw[lookup_function_def, FIND_thm] >>
  gvs[lookup_function_def]
QED

(* Get instruction at index in a block *)
Definition get_instruction_def:
  get_instruction bb idx =
    if idx < LENGTH bb.bb_instructions then
      SOME (EL idx bb.bb_instructions)
    else NONE
End

(* Get the entry block of a function *)
Definition entry_block_def:
  entry_block fn =
    if NULL fn.fn_blocks then NONE
    else SOME (HD fn.fn_blocks)
End

(* Get successor labels of a terminator instruction *)
Definition get_successors_def:
  get_successors inst =
    if ~is_terminator inst.inst_opcode then [] else
    MAP THE (FILTER IS_SOME (MAP get_label inst.inst_operands))
End

(* The block labels of a function, in block order. *)
Definition fn_labels_def:
  fn_labels fn = MAP (λbb. bb.bb_label) fn.fn_blocks
End

(* Entry block label, if the function is non-empty. *)
Definition fn_entry_label_def:
  fn_entry_label fn =
    OPTION_MAP (λbb. bb.bb_label) (entry_block fn)
End

(* All variable names assigned anywhere in the function (deduplicated). *)
Definition fn_all_assignments_def:
  fn_all_assignments fn =
    nub (FLAT (MAP (λbb.
      FLAT (MAP inst_defs bb.bb_instructions))
      fn.fn_blocks))
End

(* Successor labels of a basic block: the unique labels targeted by its
 * terminator, reversed to match Vyper's iteration order.
 * Uses nub to match Python's OrderedSet cfg_out (deduplicates). *)
Definition bb_succs_def:
  bb_succs bb =
    case bb.bb_instructions of
      [] => []
    | insts => nub (REVERSE (get_successors (LAST insts)))
End

(* All instructions across all blocks, in block order. *)
Definition fn_insts_blocks_def:
  fn_insts_blocks [] = [] /\
  fn_insts_blocks (bb::bbs) =
    bb.bb_instructions ++ fn_insts_blocks bbs
End

Definition fn_insts_def:
  fn_insts fn = fn_insts_blocks fn.fn_blocks
End

Definition no_raw_fmp_ops_def:
  no_raw_fmp_ops fn <=>
    !inst. MEM inst (fn_insts fn) ==>
           ~is_raw_fmp_opcode inst.inst_opcode
End

(* The function names in a context. *)
Definition ctx_fn_names_def:
  ctx_fn_names ctx = MAP (\f. f.fn_name) ctx.ctx_functions
End
