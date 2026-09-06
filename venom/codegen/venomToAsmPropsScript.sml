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
  codegenRel contextCodegenRelProps fnPlanDecomp blockSimHelpers cleanOpsSim genBlockSim

(* ===== Per-Instruction Simulation ===== *)

(* Core simulation lemma: after Venom steps one instruction and asm
   executes the generated plan, venom_asm_rel is maintained.

   Covers continuation (OK) case only. Halting/aborting instructions
   are handled at the block level.

   venom_asm_rel is the LOOP INVARIANT — needed in both precondition
   and conclusion for chaining across instructions within a block. *)
Theorem gen_inst_simulation:
  ∀fuel ctx label_offsets offset_to_pc prog initial_fmp
   liveness dfg cfg fn inst next_liveness is_halting
   next_is_term bb_label ps vs as ops ps'.
    codegen_ready_fn fn ∧
    venom_asm_rel label_offsets ps vs as ∧
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') ∧
    asm_block_at prog as.as_pc (execute_plan initial_fmp ops) ⇒
    ∀vs'. step_inst fuel ctx inst vs = OK vs' ∧
          inst_memory_safe ps'.ps_alloc inst vs vs' ⇒
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
     7. Variable-input ownership: every variable in compute_operands is
        shallowly present on the plan stack or available in the spill map.
        This is independent of the post-input stack-length bound.
     8. PHI soundness: stack-found phi var evaluates correctly
        — dischargeable from block entry invariant.
     Items 1,4,5,6,7,8 are dischargeable at block/fn level from their
     own invariants. Items 2,3 are pipeline obligations. *)
  cheat
QED

(* ===== Block-Level Simulation ===== *)

(* Running a basic block in Venom and executing the generated plan
   as asm steps produce related results.

   OK case: venom_asm_rel maintained (loop invariant for next block).
   Halt/Abort: venom_asm_terminal_rel (only observable effects matter).

   inst_memory_safe is required for every Venom step during block
   execution (propagated from gen_inst_simulation). The quantified
   form below is stronger than necessary — it covers all possible
   step_inst calls, not just those reachable during this block.
   Refined at proof time to only reachable states. *)
Theorem gen_block_simulation:
  ∀fuel ctx label_offsets offset_to_pc prog initial_fmp
   liveness dfg cfg fn bb ps vs as block_ops ps'.
    codegen_ready_fn fn ∧
    venom_asm_rel label_offsets ps vs as ∧
    generate_block_plan liveness dfg cfg fn bb ps =
      SOME (block_ops, ps') ∧
    asm_block_at prog as.as_pc (execute_plan initial_fmp block_ops) ∧
    (* Spill safety: every Venom step preserves the spill region *)
    (∀inst vs1 vs2 fuel'.
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       inst_memory_safe ps.ps_alloc inst vs1 vs2) ⇒
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

(* Full function simulation for the region assigned by a successful context
   plan.  The ambient context relation masks every caller/callee spill region;
   the active function's local plan state starts at its assigned region base.
   The semantic proof gap is intentionally retained. *)
Theorem gen_fn_simulation:
  ∀fuel ctx cp i r fn label_offsets offset_to_pc prog
   vs as Inv.
    generate_context_plan ctx = SOME cp ∧
    i < LENGTH ctx.ctx_functions ∧
    EL i ctx.ctx_functions = fn ∧
    EL i cp.cp_regions = r ∧
    codegen_context_obligations Inv ctx cp ∧
    codegen_reachability_package Inv ctx vs ∧
    codegen_ready_fn fn ∧
    context_venom_asm_rel cp label_offsets
      (fn_init_ps fn r.sr_spill_base) vs as ∧
    asm_block_at prog as.as_pc
      (execute_plan cp.cp_initial_fmp r.sr_plan) ⇒
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
