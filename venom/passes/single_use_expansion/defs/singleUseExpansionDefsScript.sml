(*
 * Single Use Expansion Pass — Definitions
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * Ports vyper/venom/passes/single_use_expansion.py to HOL4.
 *
 * Transforms Venom IR to "single use" form:
 *   - Each variable is used at most once (by non-ASSIGN opcodes)
 *   - All operands to non-ASSIGN instructions must be variables
 *
 * For each instruction (except ASSIGN, OFFSET, PHI, PARAM):
 *   - For each operand that is a literal: insert ASSIGN before
 *   - For each operand that is a variable used more than once: insert ASSIGN
 *   - Skip: first operand of LOG (magic topic count)
 *
 * This is the inverse of AssignElimination.
 * Required by venom_to_assembly.py and helpful for DFT pass.
 *
 * Uses DFG analysis (use counts).
 *
 * TOP-LEVEL:
 *   sue_should_skip          — opcodes excluded from expansion
 *   sue_needs_assign         — check if operand needs ASSIGN wrapper
 *   sue_expand_inst          — per-instruction expansion
 *   sue_expand_block         — block-level transform
 *   sue_expand_function      — function-level transform
 *
 * Helper:
 *   sue_fresh_var            — fresh variable for inserted ASSIGNs
 *
 * Source: vyper/venom/passes/single_use_expansion.py
 *)

Theory singleUseExpansionDefs
Ancestors
  passSimulationDefs dfgDefs venomExecSemantics venomInst irSupply

(* ===== Opcodes to skip ===== *)

(* Python: if inst.opcode in ("assign", "offset", "phi", "param"): continue *)
Definition sue_should_skip_def:
  sue_should_skip opc <=>
    opc = ASSIGN \/ opc = OFFSET \/ opc = PHI \/ is_param_opcode opc
End

(* ===== Fresh Variable ===== *)

(* Fresh variable name based on instruction id and operand index. *)
Definition sue_fresh_var_def:
  sue_fresh_var (inst_id:num) (op_idx:num) =
    STRCAT "sue_" (STRCAT (toString inst_id)
                          (STRCAT "_" (toString op_idx)))
End

(* ===== Operand Needs Expansion ===== *)

(*
 * Check if an operand needs an ASSIGN wrapper.
 *
 * A variable operand needs wrapping if:
 *   - It appears more than once in the instruction's operands, OR
 *   - It has more than one use in the whole function (DFG use count > 1)
 *
 * A literal operand always needs wrapping (moved to a variable).
 * A label operand is never wrapped.
 *)
Definition sue_needs_assign_def:
  sue_needs_assign dfg (inst : instruction) (op_idx : num) =
    if op_idx >= LENGTH inst.inst_operands then F
    else
      let op = EL op_idx inst.inst_operands in
      (* Preserve parser-significant structural counts at operand 0. *)
      if (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) /\ op_idx = 0 then F
      else
        case op of
          Var v =>
            let uses = dfg_get_uses dfg v in
            let self_count = LENGTH (FILTER (\op'. op' = Var v)
                                            inst.inst_operands) in
            (* Multi-use: either used >1 times in this inst, or used elsewhere *)
            if LENGTH uses > 1 \/ self_count > 1 then T
            else F
        | Lit _ => T
        | Label _ => F
End

Theorem sue_needs_assign_DRET_head:
  inst.inst_opcode = DRET /\ inst.inst_operands <> [] ==>
  ~sue_needs_assign dfg inst 0
Proof
  Cases_on `inst.inst_operands` >>
  gvs[sue_needs_assign_def]
QED

(* ===== Per-Instruction Expansion ===== *)

(*
 * Expand a single instruction.
 * For each operand that needs expansion, insert an ASSIGN before it
 * and replace the operand with the ASSIGN's output variable.
 *
 * Returns: (prefix_assigns, modified_instruction)
 *)
(* Count remaining occurrences of op in a list *)
Definition sue_count_remaining_def:
  sue_count_remaining op [] = 0n /\
  sue_count_remaining op (x :: rest) =
    if x = op then 1 + sue_count_remaining op rest
    else sue_count_remaining op rest
End

(*
 * Expand operands. Uses 'remaining_ops' (the not-yet-processed tail)
 * to determine if this is the last occurrence of a multi-use var.
 * Python skips wrapping the last occurrence (since inst.operands
 * is mutated in-place, by the last occurrence self_count = 1).
 *)
Definition sue_expand_ops_def:
  sue_expand_ops dfg inst [] op_idx = ([], []) /\
  sue_expand_ops dfg inst (op :: rest) op_idx =
    let (more_assigns, more_ops) = sue_expand_ops dfg inst rest (op_idx + 1) in
    if ~sue_needs_assign dfg inst op_idx then
      (more_assigns, op :: more_ops)
    else
      (* Check if this is the last occurrence — Python skips wrapping it *)
      let remaining_same = sue_count_remaining op rest in
      case op of
        Var v =>
          let uses = dfg_get_uses dfg v in
          if LENGTH uses = 1 /\ remaining_same = 0 then
            (* Single global use AND last in this instruction → skip *)
            (more_assigns, op :: more_ops)
          else
            let vn = sue_fresh_var inst.inst_id op_idx in
            let assign_inst = <| inst_id := inst.inst_id * 1000 + op_idx;
                                 inst_opcode := ASSIGN;
                                 inst_operands := [op];
                                 inst_outputs := [vn] |> in
            (assign_inst :: more_assigns, Var vn :: more_ops)
      | _ =>
          let vn = sue_fresh_var inst.inst_id op_idx in
          let assign_inst = <| inst_id := inst.inst_id * 1000 + op_idx;
                               inst_opcode := ASSIGN;
                               inst_operands := [op];
                               inst_outputs := [vn] |> in
          (assign_inst :: more_assigns, Var vn :: more_ops)
End


Theorem sue_expand_ops_DRET_head:
  inst.inst_opcode = DRET /\ inst.inst_operands = op :: ops /\
  sue_expand_ops dfg inst (op :: ops) 0 = (assigns,new_ops) ==>
  ?more_ops. new_ops = op :: more_ops
Proof
  rw[sue_expand_ops_def] >>
  pairarg_tac >>
  gvs[sue_needs_assign_DRET_head]
QED
Definition sue_expand_inst_def:
  sue_expand_inst dfg inst =
    if sue_should_skip inst.inst_opcode then [inst]
    else
      let (assigns, new_ops) =
        sue_expand_ops dfg inst inst.inst_operands 0 in
      assigns ++ [inst with inst_operands := new_ops]
End

(* ===== Block and Function Transform ===== *)

Definition sue_expand_block_def:
  sue_expand_block dfg bb =
    bb with bb_instructions :=
      FLAT (MAP (sue_expand_inst dfg) bb.bb_instructions)
End

Definition sue_expand_function_def:
  sue_expand_function fn =
    let dfg = dfg_build_function fn in
    fn with fn_blocks :=
      MAP (sue_expand_block dfg) fn.fn_blocks
End

(* Fresh variable names introduced by the expansion *)
Definition sue_fresh_vars_fn_def:
  sue_fresh_vars_fn fn =
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst.
        MAPi (\idx op. sue_fresh_var inst.inst_id idx) inst.inst_operands)
        bb.bb_instructions))
      fn.fn_blocks))
End

(* sue_operands_wf: opcodes that ignore their operands must have no
   operands.  This includes NOP/STOP/SINK/INVALID and all exec_read0
   opcodes (CALLER, MEMTOP, etc.) whose step_inst_base ignores operands.
   Without this, SUE expansion could introduce assign errors for operands
   the original instruction never evaluates, breaking semantic equivalence.
   Trivially satisfied by the Vyper pipeline. *)
Definition sue_operands_wf_def:
  sue_operands_wf inst <=>
    (inst.inst_opcode = NOP \/ inst.inst_opcode = STOP \/
     inst.inst_opcode = SINK \/ inst.inst_opcode = INVALID \/
     inst.inst_opcode = CALLER \/ inst.inst_opcode = CALLVALUE \/
     inst.inst_opcode = CALLDATASIZE \/ inst.inst_opcode = ADDRESS \/
     inst.inst_opcode = ORIGIN \/ inst.inst_opcode = GASPRICE \/
     inst.inst_opcode = GAS \/ inst.inst_opcode = GASLIMIT \/
     inst.inst_opcode = COINBASE \/ inst.inst_opcode = TIMESTAMP \/
     inst.inst_opcode = NUMBER \/ inst.inst_opcode = PREVRANDAO \/
     inst.inst_opcode = CHAINID \/ inst.inst_opcode = SELFBALANCE \/
     inst.inst_opcode = BASEFEE \/ inst.inst_opcode = CODESIZE \/
     inst.inst_opcode = RETURNDATASIZE \/ inst.inst_opcode = BLOBBASEFEE \/
     inst.inst_opcode = MEMTOP ==>
     inst.inst_operands = [])
End

Definition sue_expand_context_def:
  sue_expand_context ctx =
    ctx with ctx_functions := MAP sue_expand_function ctx.ctx_functions
End


(* ===== Supply-aware configured transform ===== *)

(* The legacy arithmetic/name-based expansion above remains the semantic model.
   Configured callers use the traversal below, which threads one unit-wide
   supply through every operand, instruction, block, and function. *)
Definition sue_alloc_assign_supply_def:
  sue_alloc_assign_supply s op =
    case fresh_ir_var s of (vn,s1) =>
    case fresh_inst_id s1 of (id,s2) =>
      (<| inst_id := id; inst_opcode := ASSIGN;
          inst_operands := [op]; inst_outputs := [vn] |>, Var vn, s2)
End

Definition sue_expand_ops_supply_def:
  sue_expand_ops_supply dfg inst s [] op_idx = ([],[],s) /\
  sue_expand_ops_supply dfg inst s (op::rest) op_idx =
    case sue_expand_ops_supply dfg inst s rest (op_idx + 1) of
      (more_assigns,more_ops,s1) =>
      if ~sue_needs_assign dfg inst op_idx then
        (more_assigns,op::more_ops,s1)
      else
        let remaining_same = sue_count_remaining op rest in
        case op of
          Var v =>
            let uses = dfg_get_uses dfg v in
            if LENGTH uses = 1 /\ remaining_same = 0 then
              (more_assigns,op::more_ops,s1)
            else
              (case sue_alloc_assign_supply s1 op of (assign_inst,new_op,s2) =>
                 (assign_inst::more_assigns,new_op::more_ops,s2))
        | Label l => (more_assigns,op::more_ops,s1)
        | Lit w =>
            (case sue_alloc_assign_supply s1 op of (assign_inst,new_op,s2) =>
               (assign_inst::more_assigns,new_op::more_ops,s2))
End

Definition sue_expand_inst_supply_def:
  sue_expand_inst_supply dfg s inst =
    if sue_should_skip inst.inst_opcode then ([inst],s)
    else
      case sue_expand_ops_supply dfg inst s inst.inst_operands 0 of
        (assigns,new_ops,s1) =>
          (assigns ++ [inst with inst_operands := new_ops],s1)
End

Definition sue_expand_insts_supply_def:
  sue_expand_insts_supply dfg s [] = ([],s) /\
  sue_expand_insts_supply dfg s (inst::insts) =
    case sue_expand_inst_supply dfg s inst of (out,s1) =>
    case sue_expand_insts_supply dfg s1 insts of (outs,s2) =>
      (out ++ outs,s2)
End

Definition sue_expand_block_supply_def:
  sue_expand_block_supply dfg s bb =
    case sue_expand_insts_supply dfg s bb.bb_instructions of (insts,s1) =>
      (bb with bb_instructions := insts,s1)
End

Definition sue_expand_blocks_supply_def:
  sue_expand_blocks_supply dfg s [] = ([],s) /\
  sue_expand_blocks_supply dfg s (bb::bbs) =
    case sue_expand_block_supply dfg s bb of (bb',s1) =>
    case sue_expand_blocks_supply dfg s1 bbs of (bbs',s2) =>
      (bb'::bbs',s2)
End

Definition sue_expand_function_supply_def:
  sue_expand_function_supply s fn =
    let dfg = dfg_build_function fn in
    case sue_expand_blocks_supply dfg s fn.fn_blocks of (bbs,s1) =>
      (fn with fn_blocks := bbs,s1)
End

Definition sue_expand_functions_supply_def:
  sue_expand_functions_supply s [] = ([],s) /\
  sue_expand_functions_supply s (fn::fns) =
    case sue_expand_function_supply s fn of (fn',s1) =>
    case sue_expand_functions_supply s1 fns of (fns',s2) =>
      (fn'::fns',s2)
End

Definition sue_expand_context_supply_def:
  sue_expand_context_supply s ctx =
    case sue_expand_functions_supply s ctx.ctx_functions of (fns,s1) =>
      (ctx with ctx_functions := fns,s1)
End

Definition sue_unit_supply_def:
  sue_unit_supply s unit =
    case sue_expand_context_supply s unit.cu_context of (ctx,s1) =>
      (unit with cu_context := ctx,s1)
End

Definition sue_configured_with_supply_def:
  sue_configured_with_supply unit =
    sue_unit_supply (init_ir_supply unit) unit
End

Definition sue_configured_def:
  sue_configured unit = FST (sue_configured_with_supply unit)
End
