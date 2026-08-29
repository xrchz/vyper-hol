(*
 * Remove Unused Variables — Definitions
 *
 * Upstream: vyperlang/vyper@b7db6bb9f (sunset MSIZE, add MEMTOP, #4909)
 *
 * Ports vyper/venom/passes/remove_unused_variables.py to HOL4.
 *
 * Removes instructions that produce outputs never used, provided
 * the instruction is not volatile and not a terminator.
 *
 * Approach: liveness-based iterated removal.
 *   1. Run liveness analysis on current function
 *   2. NOP any removable instruction whose outputs are all dead
 *   3. Clear NOPs, repeat until fixpoint (OWHILE)
 *
 * The iteration is needed because standard liveness counts uses from
 * dead instructions — removing one dead instruction can make another's
 * output dead. Each iteration removes ≥1 instruction, so OWHILE
 * terminates (bounded by total instruction count).
 *
 * After MSIZE sunset (#4909): msize_fence machinery removed.
 * MEMTOP reads Eff_MEMORY, which conflicts with volatile memory-writers
 * via effects_independent. is_removable (which excludes is_volatile)
 * already prevents removing instructions that MEMTOP could observe.
 *
 * TOP-LEVEL:
 *   remove_unused_inst     — per-instruction transform (given live set)
 *   remove_unused_function — function-level transform (iterated)
 *)

Theory removeUnusedDefs
Libs
  pred_setLib
Ancestors
  analysisSimDefs livenessDefs passSharedDefs venomEffects cfgDefs While

(* ===== Per-instruction transform ===== *)

(* Stateful removable opcodes whose effects must be preserved even when all
   of their outputs are dead. *)
Definition remove_unused_must_preserve_op_def:
  remove_unused_must_preserve_op op <=>
    op = ALLOCA \/ op = DALLOCA \/ op = SETFMP
End

(* Transform given the set of live variables after this instruction.
   If the instruction is removable and none of its outputs are live,
   replace with NOP. *)
Definition remove_unused_inst_def:
  remove_unused_inst (live : string list) inst =
    if remove_unused_must_preserve_op inst.inst_opcode then inst
    else if ~is_removable inst then inst
    else if EVERY (\v. ~MEM v live) inst.inst_outputs
    then mk_nop_inst inst
    else inst
End

(* ===== Liveness query ===== *)

(* Query live-after for instruction at index idx.
   live_vars_at returns live_before, so:
   - for non-last instructions: live_after[idx] = live_before[idx+1]
   - for last instruction: live_after = block out_vars *)
Definition live_after_at_def:
  live_after_at lr lbl idx n_insts =
    if idx + 1 < n_insts then live_vars_at lr lbl (idx + 1)
    else live_vars_at lr lbl n_insts
End



(* ===== Function-level transform ===== *)

Definition remove_unused_block_def:
  remove_unused_block lr bb =
    let n = LENGTH bb.bb_instructions in
    bb with bb_instructions :=
      MAPi (\idx inst.
        remove_unused_inst (live_after_at lr bb.bb_label idx n) inst)
        bb.bb_instructions
End

(* Single pass: transform + clear NOPs *)
Definition remove_unused_single_pass_def:
  remove_unused_single_pass fn =
    let lr = liveness_analyze fn in
    clear_nops_function
      (function_map_transform
        (\bb. remove_unused_block lr bb)
        fn)
End

(* Iterate until fixpoint: matches Python's worklist behavior.
   Each iteration recomputes liveness (since removing instructions
   changes liveness results). OWHILE terminates because each changed
   iteration removes at least one instruction, strictly decreasing
   the total instruction count. *)
Definition remove_unused_iterate_def:
  remove_unused_iterate fn =
    OWHILE (\fn. remove_unused_single_pass fn <> fn)
           remove_unused_single_pass fn
End

Definition remove_unused_function_def:
  remove_unused_function fn =
    case remove_unused_iterate fn of
      SOME fn' => fn'
    | NONE => fn
End

(* All instruction outputs across all blocks of a function. *)
Definition fn_all_outputs_def:
  fn_all_outputs fn =
    set (FLAT (MAP (\bb.
      FLAT (MAP (\inst. inst.inst_outputs) bb.bb_instructions))
      fn.fn_blocks))
End

(* Variables eliminated by remove_unused: outputs of NOP'd instructions.
   These are dead (no live use) — their values don't affect any
   observable behavior. The correctness theorem excludes them from
   state equivalence. *)
Definition remove_unused_eliminated_vars_def:
  remove_unused_eliminated_vars fn =
    fn_all_outputs fn DIFF fn_all_outputs (remove_unused_function fn)
End

Definition remove_unused_context_def:
  remove_unused_context ctx =
    ctx with ctx_functions := MAP remove_unused_function ctx.ctx_functions
End

(* All eliminated vars across all functions in a context.
   Covers callee Halt/Abort propagation: a callee's eliminated vars
   may appear in the Halt state, so the top-level relation must
   forgive differences in ANY function's eliminated vars. *)
Definition remove_unused_all_eliminated_def:
  remove_unused_all_eliminated ctx =
    BIGUNION (IMAGE remove_unused_eliminated_vars (set ctx.ctx_functions))
End
