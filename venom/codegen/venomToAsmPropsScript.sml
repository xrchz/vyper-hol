(*
 * Venom IR → Assembly Correctness — Theorem Statements
 *
 * Simulation: for each Venom execution step, the generated asm
 * instructions (from stackPlanGen + planExec) preserve venom_asm_rel.
 *
 * Simulation lemmas use asm_steps (step-counted execution on the full
 * program) so PC is always meaningful and composes with run_asm.
 *
 * Preconditions: codegen_ready (SSA, SUE, normalized CFG, no bad opcodes).
 * Stated modulo gas.
 *
 * TOP-LEVEL:
 *   gen_inst_simulation     — per-instruction simulation (OK case)
 *   gen_block_simulation    — block-level simulation (all result cases)
 *   gen_fn_simulation       — function-level simulation
 *
 * STATUS: These are central open/cheated Venom→Asm simulation targets.
 * Several helper proof layers exist, but theorem statements/preconditions may
 * need stabilization before proof repair; see docs/compiler-proof-roadmap.md.
 *)

Theory venomToAsmProps
Ancestors
  codegenRel blockSimHelpers cleanOpsSim genBlockSim

(* ===== Per-Instruction Simulation ===== *)

(* Core simulation lemma: after Venom steps one instruction and asm
   executes the generated plan, venom_asm_rel is maintained.

   Covers continuation (OK) case only. Halting/aborting instructions
   are handled at the block level.

   venom_asm_rel is the LOOP INVARIANT — needed in both precondition
   and conclusion for chaining across instructions within a block. *)
Theorem gen_inst_simulation:
  ∀fuel ctx label_offsets offset_to_pc prog
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps'.
    codegen_ready_fn fn ∧
    venom_asm_rel label_offsets ps vs as ∧
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') ∧
    asm_block_at prog as.as_pc (execute_plan ops) ⇒
    ∀vs'. step_inst fuel ctx inst vs = OK vs' ∧
          step_mem_safe ps.ps_alloc vs vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmOK as' ∧
        venom_asm_rel label_offsets ps' vs' as'
Proof
  (* FALSE AS STATED. Missing preconditions vs gen_inst_ok_sim:
     1. inst_wf inst
        — dischargeable at block level from codegen_ready_fn + MEM bb/inst
     2. LENGTH (compute_operands inst) ≤ 16
        — pipeline obligation: EVM only has LOG0–LOG4 (tc ≤ 4 → 6 operands),
          INVOKE args bounded by callee arity. Add to codegen_ready_fn or
          a new evm_compatible predicate.
     3. Label resolution: ∀l. MEM (Label l) ... ⇒ IS_SOME (FLOOKUP lo l)
        — pipeline obligation from compute_label_offsets over full program.
     4. prefix_spill_wf lo (FRONT ops) ps
        — provable from generate_inst_plan output (needs new lemma).
     5. SSA freshness: output vars not in ps.ps_stack / ps.ps_spilled
        — dischargeable from ssa_form + plan_state invariant.
     6. Stack depth after emit_input_plan ≥ operand count
        — dischargeable from plan_state invariant.
     7. PHI soundness: stack-found phi var evaluates correctly
        — dischargeable from block entry invariant.
     Items 1,4,5,6,7 are dischargeable at block/fn level from their
     own invariants. Items 2,3 are pipeline obligations. *)
  cheat
QED

(* ===== Block-Level Simulation ===== *)

(* Running a basic block in Venom and executing the generated plan
   as asm steps produce related results.

   OK case: venom_asm_rel maintained (loop invariant for next block).
   Halt/Abort: venom_asm_terminal_rel (only observable effects matter).

   step_mem_safe is required for every Venom step during block
   execution (propagated from gen_inst_simulation). The quantified
   form below is stronger than necessary — it covers all possible
   step_inst calls, not just those reachable during this block.
   Refined at proof time to only reachable states. *)
Theorem gen_block_simulation:
  ∀fuel ctx label_offsets offset_to_pc prog
   liveness dfg cfg fn bb ps vs as block_ops ps'.
    codegen_ready_fn fn ∧
    venom_asm_rel label_offsets ps vs as ∧
    generate_block_plan liveness dfg cfg fn bb ps =
      SOME (block_ops, ps') ∧
    asm_block_at prog as.as_pc (execute_plan block_ops) ∧
    (* Spill safety: every Venom step preserves the spill region *)
    (∀inst vs1 vs2 fuel'.
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe ps.ps_alloc vs1 vs2) ⇒
    (* OK case: block continues to next block, invariant maintained *)
    (∀vs'. exec_block fuel ctx bb vs = OK vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmOK as' ∧
        venom_asm_rel label_offsets ps' vs' as') ∧
    (* Halt case: observable effects match *)
    (∀vs'. exec_block fuel ctx bb vs = Halt vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmHalt as' ∧
        venom_asm_terminal_rel vs' as') ∧
    (* Abort case *)
    (∀a vs'. exec_block fuel ctx bb vs = Abort a vs' ⇒
      ∃n as'.
        ((a = Revert_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmRevert as') ∨
         (a = ExHalt_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmFault as')) ∧
        venom_asm_terminal_rel vs' as')
Proof
  (* Missing preconditions from gen_inst_ok/halt/abort_sim:
     1. MEM bb fn.fn_blocks
        — dischargeable at fn level: generate_fn_plan iterates over fn.fn_blocks.
     2. LENGTH (compute_operands inst) ≤ 16  (per instruction)
        — pipeline obligation: evm_compatible (LOG tc ≤ 4, INVOKE arity bounded).
          Propagated from fn-level hypothesis.
     3. Label resolution: ∀l. MEM (Label l) ... ⇒ IS_SOME (FLOOKUP lo l)
        — pipeline obligation from compute_label_offsets.
     4. prefix_spill_wf as loop invariant
        — provable from generate_inst_plan output (needs new lemma);
          maintained across instructions by plan_state monotonicity.
     5. SSA freshness / output-disjointness
        — dischargeable from ssa_form + plan_state invariant across block.
     6. PHI soundness
        — dischargeable from block entry invariant.
     7. Stack depth after emit_input_plan
        — dischargeable from plan_state invariant.
     Item 1 is dischargeable at fn level. Items 2,3 propagate from
     fn-level hypotheses. Items 4–7 are block-internal invariants
     provable from generate_block_plan structure. *)
  cheat
QED

(* ===== Function-Level Simulation ===== *)

(* Full function simulation.
   Initial state: venom_asm_rel holds with fn_init_ps (params on stack).
   Terminal results: only observable effects (venom_asm_terminal_rel).

   fn_init_ps has PARAM operands in ps_stack matching the asm stack.
   The proof establishes the full venom_asm_rel invariant after the
   entry block's prepare_params_plan processes dead params.

   Spill safety: required for every Venom step during function
   execution. Uses fn_init_ps alloc (sa_spill_base = fn_eom).
   spill_mem_covered: initial memory covers spill high-water mark
   so MEMTOP agrees between Venom and asm from the start. *)
Theorem gen_fn_simulation:
  ∀fuel ctx label_offsets offset_to_pc prog fn fn_eom fn_ops
   ps_final vs as.
    codegen_ready_fn fn ∧
    generate_fn_plan fn fn_eom 0 = SOME (fn_ops, ps_final) ∧
    venom_asm_rel label_offsets (fn_init_ps fn fn_eom) vs as ∧
    asm_block_at prog as.as_pc (execute_plan fn_ops) ∧
    (* Spill safety *)
    (∀inst vs1 vs2 fuel'.
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe (fn_init_ps fn fn_eom).ps_alloc vs1 vs2) ∧
    (* MEMTOP: initial memory covers max spill offset *)
    spill_mem_covered ps_final.ps_alloc.sa_next_offset vs.vs_memory ⇒
    (* Halt case *)
    (∀vs'. run_blocks fuel ctx fn vs = Halt vs' ⇒
      ∃n as'.
        asm_steps label_offsets offset_to_pc prog n as = AsmHalt as' ∧
        venom_asm_terminal_rel vs' as') ∧
    (* Abort case *)
    (∀a vs'. run_blocks fuel ctx fn vs = Abort a vs' ⇒
      ∃n as'.
        ((a = Revert_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmRevert as') ∨
         (a = ExHalt_abort ∧
          asm_steps label_offsets offset_to_pc prog n as =
            AsmFault as')) ∧
        venom_asm_terminal_rel vs' as')
Proof
  cheat
QED
