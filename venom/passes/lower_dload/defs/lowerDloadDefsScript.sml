(*
 * Lower DLOAD Pass — Definitions
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 * Ports vyper/venom/passes/lower_dload.py to HOL4.
 *
 * Lowers dload and dloadbytes instructions to their EVM equivalents:
 *   dload ptr        -> alloca 32; add ptr code_end; codecopy dst add_out 32; mload dst
 *   dloadbytes dst src size -> add src code_end; codecopy dst code_ptr size
 *
 * Matches Python: emits ADD [ptr; Label "code_end"]. Labels resolve via
 * vs_labels (eval_operand handles Label operands). Correctness requires
 * code_layout_valid: vs_labels "code_end" = code/data boundary.
 *
 * No analysis needed - pure per-instruction expansion (1:N).
 * Framework: function_map_transform with FLAT o MAP.
 *
 * LEGACY SEMANTIC MODEL (used only by the existing simulation proof):
 *   lower_dload_inst      - arithmetic-ID per-instruction expansion
 *   lower_dload_block     - legacy block-level transform
 *   lower_dload_function  - legacy function-level transform
 *   lower_dload_context   - legacy context-level transform
 *
 * CONFIGURED EXECUTABLE API:
 *   lower_dload_configured_with_supply - unit transform plus final supply
 *   lower_dload_configured             - transformed unit projection
 *
 *   code_layout_valid     - precondition for legacy semantic correctness
 *
 * Helper:
 *   ld_alloca_var         - fresh variable name for alloca output
 *   ld_add_var            - fresh variable name for add output
 *
 * Source: vyper/venom/passes/lower_dload.py
 *)

Theory lowerDloadDefs
Ancestors
  passSimulationDefs venomExecSemantics venomInst irSupply
(* ===== Fresh Variable Names ===== *)

(* Fresh variable for alloca output.
   Naming scheme based on inst_id ensures uniqueness within a function. *)
Definition ld_alloca_var_def:
  ld_alloca_var (id:num) = STRCAT "ld_alloca_" (toString id)
End

(* Fresh variable for add output (ptr + code_end). *)
Definition ld_add_var_def:
  ld_add_var (id:num) = STRCAT "ld_add_" (toString id)
End

(* ===== Per-Instruction Expansion ===== *)

(*
 * Legacy/model-only expansion of a single instruction.  Its arithmetic IDs
 * support the existing simulation theorem, but this is not the configured O1
 * implementation and must not be used as evidence for configured freshness.
 *
 * dload [ptr] with output [out]:
 *   1. alloca [Lit 32w]                       -> [alloca_var]  (allocate temp memory)
 *   2. add [ptr; Label "code_end"]            -> [add_var]     (ptr + code_end)
 *   3. codecopy [Var alloca_var; Var add_var; Lit 32w]         (copy code -> memory)
 *   4. mload [Var alloca_var]                 -> [out]         (read from memory)
 *
 * dloadbytes [dst; src; size] (HOL4 semantic order: dst, src, size):
 *   1. add [src; Label "code_end"]            -> [add_var]     (src + code_end)
 *   2. codecopy [dst; Var add_var; size]                       (copy code -> memory)
 *
 * All other instructions pass through unchanged.
 *
 * Labels resolve via vs_labels (eval_operand handles Label operands).
 * Correctness requires code_layout_valid s.
 *)
Definition lower_dload_inst_def:
  lower_dload_inst inst =
    if inst.inst_opcode = DLOAD then
      case (inst.inst_operands, inst.inst_outputs) of
        ([ptr_op], [out]) =>
          let id = inst.inst_id in
          let alloca_v = ld_alloca_var id in
          let add_v = ld_add_var id in
          [<| inst_id := id; inst_opcode := ALLOCA;
              inst_operands := [Lit 32w]; inst_outputs := [alloca_v] |>;
           <| inst_id := id + 1; inst_opcode := ADD;
              inst_operands := [ptr_op; Label "code_end"];
              inst_outputs := [add_v] |>;
           <| inst_id := id + 2; inst_opcode := CODECOPY;
              inst_operands := [Var alloca_v; Var add_v; Lit 32w];
              inst_outputs := [] |>;
           <| inst_id := id + 3; inst_opcode := MLOAD;
              inst_operands := [Var alloca_v]; inst_outputs := [out] |>]
      | _ => [inst]
    else if inst.inst_opcode = DLOADBYTES then
      case inst.inst_operands of
        [dst_op; src_op; size_op] =>
          let id = inst.inst_id in
          let add_v = ld_add_var id in
          [<| inst_id := id; inst_opcode := ADD;
              inst_operands := [src_op; Label "code_end"];
              inst_outputs := [add_v] |>;
           <| inst_id := id + 1; inst_opcode := CODECOPY;
              inst_operands := [dst_op; Var add_v; size_op];
              inst_outputs := [] |>]
      | _ => [inst]
    else [inst]
End

(* ===== Block and Function Transform ===== *)

(* Transform a block by expanding all dload/dloadbytes instructions. *)
Definition lower_dload_block_def:
  lower_dload_block bb =
    bb with bb_instructions :=
      FLAT (MAP lower_dload_inst bb.bb_instructions)
End

(* Transform a function by expanding all blocks. *)
Definition lower_dload_function_def:
  lower_dload_function fn =
    function_map_transform lower_dload_block fn
End

(* Transform all functions in a context. *)
Definition lower_dload_context_def:
  lower_dload_context ctx =
    ctx with ctx_functions := MAP lower_dload_function ctx.ctx_functions
End

(* ===== Supply-aware configured transform ===== *)

(* Supply-threaded implementation.  The only configured entry points are the
   compilation-unit wrappers lower_dload_configured_with_supply and
   lower_dload_configured below: they initialize one supply from the whole unit
   and thread it across every function.  Future pipeline composition must call
   a configured unit wrapper once, never invoke this function-level API
   independently for each function.  The arithmetic-ID transform above remains
   only the model used by the existing legacy simulation proof. *)
Definition lower_dload_inst_supply_def:
  lower_dload_inst_supply s inst =
    if inst.inst_opcode = DLOAD then
      case (inst.inst_operands, inst.inst_outputs) of
        ([ptr_op], [out]) =>
          (case fresh_ir_var s of (alloca_v,s1) =>
           case fresh_ir_var s1 of (add_v,s2) =>
           case fresh_inst_id s2 of (alloca_id,s3) =>
           case fresh_inst_id s3 of (add_id,s4) =>
           case fresh_inst_id s4 of (copy_id,s5) =>
           case fresh_inst_id s5 of (load_id,s6) =>
             ([<| inst_id := alloca_id; inst_opcode := ALLOCA;
                  inst_operands := [Lit 32w]; inst_outputs := [alloca_v] |>;
               <| inst_id := add_id; inst_opcode := ADD;
                  inst_operands := [ptr_op; Label "code_end"];
                  inst_outputs := [add_v] |>;
               <| inst_id := copy_id; inst_opcode := CODECOPY;
                  inst_operands := [Var alloca_v; Var add_v; Lit 32w];
                  inst_outputs := [] |>;
               <| inst_id := load_id; inst_opcode := MLOAD;
                  inst_operands := [Var alloca_v]; inst_outputs := [out] |>],s6))
      | _ => ([inst],s)
    else if inst.inst_opcode = DLOADBYTES then
      case inst.inst_operands of
        [dst_op; src_op; size_op] =>
          (case fresh_ir_var s of (add_v,s1) =>
           case fresh_inst_id s1 of (add_id,s2) =>
           case fresh_inst_id s2 of (copy_id,s3) =>
             ([<| inst_id := add_id; inst_opcode := ADD;
                  inst_operands := [src_op; Label "code_end"];
                  inst_outputs := [add_v] |>;
               <| inst_id := copy_id; inst_opcode := CODECOPY;
                  inst_operands := [dst_op; Var add_v; size_op];
                  inst_outputs := [] |>],s3))
      | _ => ([inst],s)
    else ([inst],s)
End

Definition lower_dload_insts_supply_def:
  lower_dload_insts_supply s [] = ([],s) /\
  lower_dload_insts_supply s (inst::insts) =
    case lower_dload_inst_supply s inst of (out,s1) =>
    case lower_dload_insts_supply s1 insts of (outs,s2) =>
      (out ++ outs,s2)
End

Definition lower_dload_block_supply_def:
  lower_dload_block_supply s bb =
    case lower_dload_insts_supply s bb.bb_instructions of (insts,s1) =>
      (bb with bb_instructions := insts,s1)
End

Definition lower_dload_blocks_supply_def:
  lower_dload_blocks_supply s [] = ([],s) /\
  lower_dload_blocks_supply s (bb::bbs) =
    case lower_dload_block_supply s bb of (bb',s1) =>
    case lower_dload_blocks_supply s1 bbs of (bbs',s2) =>
      (bb'::bbs',s2)
End

Definition lower_dload_invalidates_layout_def:
  lower_dload_invalidates_layout fn <=>
    ?bb inst ptr out.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      inst.inst_opcode = DLOAD /\
      inst.inst_operands = [ptr] /\ inst.inst_outputs = [out]
End

Definition lower_dload_function_supply_def:
  lower_dload_function_supply s fn =
    case lower_dload_blocks_supply s fn.fn_blocks of (bbs,s1) =>
      (fn with <| fn_blocks := bbs;
                  fn_eom := if lower_dload_invalidates_layout fn
                            then NONE else fn.fn_eom |>,s1)
End

Definition lower_dload_functions_supply_def:
  lower_dload_functions_supply s [] = ([],s) /\
  lower_dload_functions_supply s (fn::fns) =
    case lower_dload_function_supply s fn of (fn',s1) =>
    case lower_dload_functions_supply s1 fns of (fns',s2) =>
      (fn'::fns',s2)
End

Definition lower_dload_context_supply_def:
  lower_dload_context_supply s ctx =
    case lower_dload_functions_supply s ctx.ctx_functions of (fns,s1) =>
      (ctx with ctx_functions := fns,s1)
End

Definition lower_dload_unit_supply_def:
  lower_dload_unit_supply s unit =
    case lower_dload_context_supply s unit.cu_context of (ctx,s1) =>
      (unit with cu_context := ctx,s1)
End

Definition lower_dload_configured_with_supply_def:
  lower_dload_configured_with_supply unit =
    lower_dload_unit_supply (init_ir_supply unit) unit
End

Definition lower_dload_configured_def:
  lower_dload_configured unit = FST (lower_dload_configured_with_supply unit)
End

(* ===== Code Layout Precondition ===== *)

(* Precondition for lower_dload correctness:
   1. vs_data_section is a suffix of vs_code
   2. vs_labels maps "code_end" to the boundary between bytecode and data

   Discharged by codegen: the assembler produces bytecode ++ data_section_bytes
   and sets code_end = LENGTH bytecode in the label map. *)
Definition code_layout_valid_def:
  code_layout_valid s <=>
    (?prefix. s.vs_code = prefix ++ s.vs_data_section) /\
    FLOOKUP s.vs_labels "code_end" =
      SOME (n2w (LENGTH s.vs_code - LENGTH s.vs_data_section)) /\
    LENGTH s.vs_code <= dimword(:256) DIV 2
End

(* ===== Variable Tracking ===== *)

(* Fresh variables introduced by expanding a single instruction.
   - DLOAD: two fresh intermediates (ld_alloca_var, ld_add_var)
   - DLOADBYTES: one fresh intermediate (ld_add_var)
   These variables do not exist in the original function. *)
Definition ld_fresh_vars_inst_def:
  ld_fresh_vars_inst inst =
    if inst.inst_opcode = DLOAD then
      {ld_alloca_var inst.inst_id; ld_add_var inst.inst_id}
    else if inst.inst_opcode = DLOADBYTES then
      {ld_add_var inst.inst_id}
    else {}
End

(* Fresh variables in a function (from DLOAD/DLOADBYTES expansion only). *)
Definition ld_fresh_vars_fn_def:
  ld_fresh_vars_fn fn =
    BIGUNION (set (MAP (\bb.
      BIGUNION (set (MAP ld_fresh_vars_inst bb.bb_instructions)))
      fn.fn_blocks))
End

(* Exempt variables: precisely the fresh intermediates introduced by lowering.
   Under the ld_no_original_alloca precondition, no original ALLOCA
   instructions exist, so the only differing variables are ld_alloca_var
   and ld_add_var from the DLOAD/DLOADBYTES expansion. *)
Definition ld_exempt_vars_fn_def:
  ld_exempt_vars_fn fn = ld_fresh_vars_fn fn
End

(* No original ALLOCA instructions in the function.
   This is a precondition only of the legacy arithmetic-ID simulation: DLOAD
   expansion inserts scratch ALLOCAs that shift vs_alloca_next, so an original
   ALLOCA could receive a different address.  It is not an O1 input invariant:
   raw frontend units admitted by the current pipeline boundary may contain
   ALLOCA.  Consequently the legacy correctness theorem below must not be cited
   as semantic correctness of the configured supply-aware O1 transform. *)
Definition ld_no_original_alloca_def:
  ld_no_original_alloca fn <=>
    !bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
      inst.inst_opcode <> ALLOCA
End

(* ===== Memory-Observing Opcode Exclusion ===== *)

(* Opcodes excluded from lower_dload functions.
   DLOAD expansion introduces ALLOCA+CODECOPY scratch that changes
   vs_memory layout.  We exclude all opcodes whose behavior depends on
   vs_memory, vs_allocas, or vs_returndata — fields that diverge.

   Memory readers: MLOAD, ILOAD, MEMTOP, SHA3, MCOPY, LOG
   External calls: CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2
   INVOKE: callee inherits vs_memory → different returns on divergent memory
   RETURNDATASIZE/RETURNDATACOPY: read vs_returndata (may differ)

   NOT excluded (safe):
   - MSTORE/CODECOPY/CALLDATACOPY/EXTCODECOPY: write-only to memory
   - RETURN/REVERT: terminal; ld_equiv omits vs_returndata
   - ALLOCA: output is exempt (in ld_exempt_vars_fn)
   - DLOAD/DLOADBYTES: transformation targets *)
Definition reads_memory_def:
  reads_memory op <=>
    op = MLOAD \/ op = ILOAD \/ op = MEMTOP \/ op = SHA3 \/ op = MCOPY \/
    op = LOG \/
    op = CALL \/ op = STATICCALL \/ op = DELEGATECALL \/
    op = CREATE \/ op = CREATE2 \/
    op = INVOKE \/
    op = RETURNDATASIZE \/ op = RETURNDATACOPY
End

Definition ld_no_mem_read_def:
  ld_no_mem_read fn <=>
    !bb inst.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
      ~reads_memory inst.inst_opcode
End

(* ===== DLOAD pointer safety ===== *)

(* The DLOAD lowering performs ptr + code_end in word arithmetic.
   This overflows when w2n ptr + LENGTH prefix >= dimword(:256).
   In Vyper, DLOAD operands are compile-time data section offsets (small).
   We require the ptr operand (for DLOAD) or src operand (for DLOADBYTES)
   evaluates to a value safe from overflow in any reachable state.

   Sufficient static condition: the relevant operand is a Lit whose value
   plus the code prefix length fits in a word. Since code_layout_valid
   gives LENGTH prefix <= dimword(:256) DIV 2, requiring the literal
   value < dimword(:256) DIV 2 ensures the sum < dimword(:256). *)
Definition ld_dload_safe_def:
  ld_dload_safe fn <=>
    !bb inst.
      MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
      (inst.inst_opcode = DLOAD ==>
        ?v. inst.inst_operands = [Lit v] /\
            w2n v < dimword(:256) DIV 2) /\
      (inst.inst_opcode = DLOADBYTES ==>
        ?dst_op v size_op.
          inst.inst_operands = [dst_op; Lit v; size_op] /\
          w2n v < dimword(:256) DIV 2)
End

(* ===== Lower-DLOAD Equivalence ===== *)

(* Tightest correct equivalence for lower_dload: everything in
   execution_equiv except vs_memory, vs_allocas, and vs_returndata.

   Why these are excluded:
   - vs_memory: DLOAD lowering uses ALLOCA+CODECOPY as scratch space,
     modifying memory beyond what the original DLOAD touches.
   - vs_allocas: ALLOCA introduces new alloca entries.
   - vs_returndata: RETURN/REVERT reads vs_memory to produce returndata;
     since memory can differ, returndata can too.

   All other fields are preserved:
   - Variables (excluding fresh ld_alloca_*/ld_add_* introduced by lowering)
   - Accounts, logs, transient, immutables (no instructions touch these)
   - Context fields (call_ctx, tx_ctx, block_ctx)
   - Data section, labels, code, params, prev_hashes (read-only) *)
Definition ld_equiv_def:
  ld_equiv vars s1 s2 <=>
    (!v. v NOTIN vars ==> lookup_var v s1 = lookup_var v s2) /\
    (* vs_memory OMITTED — DLOAD lowering uses scratch memory *)
    s1.vs_transient = s2.vs_transient /\
    s1.vs_halted = s2.vs_halted /\
    (* vs_returndata OMITTED — RETURN reads from divergent memory *)
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    s1.vs_fmp = s2.vs_fmp /\
    s1.vs_call_entry_fmp = s2.vs_call_entry_fmp /\
    s1.vs_initial_fmp = s2.vs_initial_fmp /\
    s1.vs_return_pc_token = s2.vs_return_pc_token
    (* vs_allocas OMITTED — ALLOCA introduces new entries *)
End
