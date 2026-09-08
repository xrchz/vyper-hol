(*
 * Dead Store Elimination — Proofs
 *
 * Precondition set (mathematically sound):
 *   - alloca_inv s:
 *       alloca regions are non-overlapping + alloca_next valid.
 *       Preserved by step_inst (proven: alloca_inv_step_inst).
 *       Needed by ma_may_alias_sound (allocas_non_overlapping s).
 *   - alloca_safe_access fn (alloca_roots fn) s:
 *       at state s, every memory access through a pointer-derived
 *       variable stays within its alloca region bounds.
 *       This ensures memloc_within_alloca for every access, which
 *       ma_may_alias_sound also requires.
 *       Vacuously true at initial state (FEMPTY allocas).
 *   - step_preserves_safety fn (alloca_roots fn):
 *       static property of the code — every non-terminator,
 *       non-ext-call step preserves alloca_safe_access +
 *       ptrs_in_alloca_bounds. This bridges from entry-state
 *       vacuity to per-reachable-state soundness.
 *       The counterexample (ADD ptr1 32w escaping Allocation 0)
 *       violates this: step_preserves_safety is F for cex_fn.
 *   - all_dead_stores: analysis output is correct (unchanged)
 *
 * Previous preconditions (alloca_inv + bp_ptrs_bounded + bp_ptr_sound)
 * were VACUOUSLY TRUE at entry (FEMPTY allocas/vars), allowing the
 * cross-allocation aliasing counterexample. bp_ptrs_bounded checks
 * memloc_within_alloca per-state, but none of the preconditions
 * established it at reachable states. step_preserves_safety is the
 * missing piece — it is a static code property (not per-state),
 * so it cannot be vacuously true.
 *
 * FALSE1: error asymmetry (cex2). FALSE2-5: aliasing (cex1).
 * why the old preconditions were insufficient.
 *
 * DLOAD fix: all_dead_stores now requires inst.inst_outputs = [].
 * This excludes DLOAD (which writes to memory AND produces an output
 * variable) from being classified as dead. NOP'ing DLOAD would
 * remove its output, breaking dse_equiv's variable agreement check.
 * Python doesn't check variable mappings (only EVM-observable effects),
 * but HOL4's dse_equiv checks !v. lookup_var v s1 = lookup_var v s2.
 *)

Theory deadStoreElimProofs
Ancestors
  deadStoreElimDefs passSimulationProps basePtrProps passSharedProps While
  venomMemProps venomMemProofs memAliasDefs passSharedField cfgAnalysisProps
  stateEquiv stateEquivProps venomState venomInst venomInstProps
  passSimulationDefs passSharedDefs execEquivParamDefs
  vfmTypes vfmState byte fcp memLocDefs
  dfIterateDefs finite_map basePtrDefs
  venomExecSemantics allocaRemapDefs pointerConfinedDefs
  venomEffects
Libs
  BasicProvers

(* ===== dse_equiv / dse_all_equiv properties ===== *)

Triviality dse_equiv_refl:
  !space s. dse_equiv space s s
Proof
  simp[dse_equiv_def]
QED

Triviality dse_equiv_trans:
  !space s1 s2 s3.
    dse_equiv space s1 s2 /\ dse_equiv space s2 s3 ==>
    dse_equiv space s1 s3
Proof
  simp[dse_equiv_def] >> metis_tac[]
QED

Triviality dse_equiv_implies_all:
  !space s1 s2. dse_equiv space s1 s2 ==> dse_all_equiv s1 s2
Proof
  simp[dse_equiv_def, dse_all_equiv_def]
QED

Triviality dse_all_equiv_refl:
  !s. dse_all_equiv s s
Proof
  simp[dse_all_equiv_def]
QED

Triviality dse_all_equiv_trans:
  !s1 s2 s3.
    dse_all_equiv s1 s2 /\ dse_all_equiv s2 s3 ==>
    dse_all_equiv s1 s3
Proof
  simp[dse_all_equiv_def] >> metis_tac[]
QED

(* ===== Bridge lemmas ===== *)

Triviality state_equiv_empty_implies_dse_equiv:
  !space s1 s2. state_equiv {} s1 s2 ==> dse_equiv space s1 s2
Proof
  simp[state_equiv_def, execution_equiv_def, dse_equiv_def,
       lookup_var_def] >>
  rpt strip_tac >>
  `FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v`
    by metis_tac[pred_setTheory.NOT_IN_EMPTY] >> gvs[]
QED

Triviality execution_equiv_empty_implies_dse_equiv:
  !space s1 s2. execution_equiv {} s1 s2 ==> dse_equiv space s1 s2
Proof
  simp[execution_equiv_def, dse_equiv_def, lookup_var_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

(* ===== lift_result composition lemmas ===== *)

Triviality lift_result_dse_equiv_trans:
  !space r1 r2 r3.
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2 /\
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r2 r3 ==>
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[dse_equiv_trans]
QED

Triviality lift_result_dse_all_equiv_trans:
  !r1 r2 r3.
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2 /\
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r2 r3 ==>
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[dse_all_equiv_trans]
QED

Triviality lift_result_dse_equiv_to_all:
  !space r1 r2.
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2 ==>
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def] >> metis_tac[dse_equiv_implies_all]
QED

(* Compose error-or-lift_result chains: if r1=Error, done.
   Otherwise lift_result R r1 r2, then r2 can't be Error either,
   so lift_result R r2 r3, and transitivity gives lift_result R r1 r3. *)
Triviality lift_result_or_error_trans:
  !R (r1:exec_result) r2 r3.
    ((?e. r1 = Error e) \/ lift_result R R R r1 r2) /\
    ((?e. r2 = Error e) \/ lift_result R R R r2 r3) /\
    (!s1 s2 s3. R s1 s2 /\ R s2 s3 ==> R s1 s3) ==>
    (?e. r1 = Error e) \/ lift_result R R R r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[]
QED

(* Bridge: error-or-lift_result with dse_equiv to dse_all_equiv *)
Triviality lift_result_or_error_equiv_to_all:
  !space (r1:exec_result) r2.
    ((?e. r1 = Error e) \/ lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2) ==>
    (?e. r1 = Error e) \/ lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2
Proof
  rpt strip_tac >> gvs[] >>
  disj2_tac >> irule lift_result_dse_equiv_to_all >> qexists `space` >> simp[]
QED

(* ===== clear_nops_function + dse_equiv bridge ===== *)

Triviality result_equiv_empty_implies_lift_result_dse_equiv:
  !space r1 r2.
    result_equiv {} r1 r2 ==>
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def, result_equiv_def] >>
  metis_tac[state_equiv_empty_implies_dse_equiv, execution_equiv_empty_implies_dse_equiv]
QED

Theorem clear_nops_function_dse_equiv:
  !space fuel ctx fn s.
    wf_function fn /\
    s.vs_inst_idx = 0 ==>
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (clear_nops_function fn) s)
Proof
  rpt strip_tac >> irule result_equiv_empty_implies_lift_result_dse_equiv >> irule clear_nops_function_correct >> simp[]
QED


(* ===== Single-pass correctness helpers ===== *)


(* H1: get_instruction in transformed block *)
Triviality get_instruction_block_map_transform:
  !f bb idx.
    get_instruction (block_map_transform f bb) idx =
    case get_instruction bb idx of NONE => NONE | SOME i => SOME (f i)
Proof
  simp[get_instruction_def, block_map_transform_def] >>
  rw[] >> simp[listTheory.EL_MAP]
QED

(* H2: block_map_transform preserves label *)
Triviality block_map_transform_label:
  !f bb. (block_map_transform f bb).bb_label = bb.bb_label
Proof
  simp[block_map_transform_def]
QED

(* H3: lookup_block in dse_single_pass *)
Triviality lookup_block_dse_single_pass:
  !lbl fn dead_ids space.
    lookup_block lbl (dse_single_pass dead_ids space fn).fn_blocks =
    OPTION_MAP (block_map_transform (dse_inst dead_ids space))
      (lookup_block lbl fn.fn_blocks)
Proof
  simp[dse_single_pass_def, function_map_transform_def] >>
  rpt gen_tac >> irule lookup_block_map >> simp[block_map_transform_label]
QED

(* H4: memory_def_opcode is not a terminator *)
Triviality memory_def_opcode_not_terminator:
  !space op. is_memory_def_opcode space op ==> ~is_terminator op
Proof
  Cases_on `space` >> simp[is_memory_def_opcode_def] >>
  strip_tac >> Cases_on `op` >>
  gvs[is_terminator_def] >> EVAL_TAC
QED

(* Add effect definitions to computeLib for EVAL capability *)
val _ = computeLib.add_funs
  [write_effects_def, read_effects_def, is_memory_def_opcode_def,
   empty_effects_def, all_effects_def, effects_in_space_def, is_terminator_def]

(* Space-to-effect mapping, matching the case expression in effects_in_space_def.
   Same incomplete pattern match: Immutables and Data get ARB (matching effects_in_space). *)
Definition space_effect_def:
  space_effect (space:addr_space) =
    case space of
      AddrSp_Memory => Eff_MEMORY
    | AddrSp_Storage => Eff_STORAGE
    | AddrSp_Transient => Eff_TRANSIENT
    | AddrSp_Calldata => Eff_MEMORY
    | AddrSp_Code => Eff_MEMORY
    | AddrSp_Returndata => Eff_MEMORY
End

Theorem effects_in_space_notin_write_effects:
  !space inst eff.
    effects_in_space space inst /\ eff <> space_effect space ==>
    eff NOTIN write_effects inst.inst_opcode
Proof
  Cases_on `space` >> simp[effects_in_space_def, space_effect_def] >>
  rpt strip_tac >> CCONTR_TAC >> gvs[pred_setTheory.SUBSET_DEF]
QED
(* Classification lemma: Memory space opcodes satisfying both
   is_memory_def_opcode and effects_in_space *)
Theorem is_memory_def_opcode_memory_effects_in_space:
  !inst.
    is_memory_def_opcode AddrSp_Memory inst.inst_opcode /\
    effects_in_space AddrSp_Memory inst ==>
    inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8 \/
    inst.inst_opcode = MCOPY \/ inst.inst_opcode = DLOAD \/
    inst.inst_opcode = DLOADBYTES \/ inst.inst_opcode = CODECOPY \/
    inst.inst_opcode = CALLDATACOPY
Proof
  gen_tac >> simp[Once effects_in_space_def, Once is_memory_def_opcode_def] >> Cases_on `inst.inst_opcode` >> EVAL_TAC
QED

(* Classification lemma: Storage space — SSTORE is the only opcode that
   is a memory-def opcode for Storage AND has all effects in Storage *)
Theorem effects_in_space_storage_is_sstore:
  !inst.
    is_memory_def_opcode AddrSp_Storage inst.inst_opcode /\
    effects_in_space AddrSp_Storage inst ==>
    inst.inst_opcode = SSTORE
Proof
  gen_tac >> simp[Once effects_in_space_def, Once is_memory_def_opcode_def] >> Cases_on `inst.inst_opcode` >> EVAL_TAC
QED

(* Classification lemma: Transient space — TSTORE is the only opcode that
   is a memory-def opcode for Transient AND has all effects in Transient *)
Theorem effects_in_space_transient_is_tstore:
  !inst.
    is_memory_def_opcode AddrSp_Transient inst.inst_opcode /\
    effects_in_space AddrSp_Transient inst ==>
    inst.inst_opcode = TSTORE
Proof
  gen_tac >> simp[Once effects_in_space_def, Once is_memory_def_opcode_def] >> Cases_on `inst.inst_opcode` >> EVAL_TAC
QED

Theorem sload_sstore_disjoint:
  !key1 key2 val s. key1 <> key2 ==> sload key2 (sstore key1 val s) = sload key2 s
Proof
  rpt strip_tac >> simp[sload_def, sstore_def, contract_storage_def, lookup_storage_def, update_storage_def, lookup_account_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem tload_tstore_disjoint:
  !key1 key2 val s. key1 <> key2 ==> tload key2 (tstore key1 val s) = tload key2 s
Proof
  rpt strip_tac >> simp[tload_def, tstore_def, contract_transient_def, lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

(* Memory-def opcodes are not ALLOCA operations.
   ALLOCA has empty write_effects, so no effect can be in write_effects ALLOCA,
   which makes is_memory_def_opcode false for ALLOCA. *)
Triviality is_memory_def_opcode_not_alloca_op:
  !space op. is_memory_def_opcode space op ==> ~is_alloca_op op
Proof
  Cases_on `space` >> Cases_on `op` >> EVAL_TAC
QED

(* effects_in_space with is_memory_def_opcode excludes INVOKE.
   INVOKE's write/read effects contain multiple effect types, so they can't
   be a subset of any singleton {space_eff}. EVAL-verified for all spaces. *)
Triviality effects_in_space_not_invoke:
  !space inst.
    is_memory_def_opcode space inst.inst_opcode /\
    effects_in_space space inst ==> inst.inst_opcode <> INVOKE
Proof
  gen_tac >>
  Cases_on `space` >>
  simp[Once effects_in_space_def, Once is_memory_def_opcode_def, space_effect_def] >>
  Cases_on `inst.inst_opcode` >> EVAL_TAC
QED

(* step_preserves_non_output_vars with empty outputs gives unconditional
   variable preservation. irule can match this directly. *)
Triviality step_preserves_all_vars_empty_outputs:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_outputs = [] ==>
    !v. lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  imp_res_tac step_preserves_non_output_vars >>
  gvs[]
QED

(* ===== Per-instruction dead store simulation ===== *)

(* Executing a memory-def opcode with empty outputs and effects confined
   to target space produces a state that is dse_equiv space-related
   to the original. This is the core per-instruction correctness lemma. *)
Theorem dse_dead_store_step_sim_ok:
  !dead_ids space fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_memory_def_opcode space inst.inst_opcode /\
    inst.inst_outputs = [] /\
    effects_in_space space inst ==>
    dse_equiv space s' s
Proof
  rpt strip_tac >>
  imp_res_tac memory_def_opcode_not_terminator >>
  imp_res_tac is_memory_def_opcode_not_alloca_op >>
  imp_res_tac effects_in_space_not_invoke >>
  imp_res_tac effects_in_space_notin_write_effects >>
  Cases_on `(space:addr_space)` >> gvs[is_memory_def_opcode_def, space_effect_def] >>
  simp[dse_equiv_def] >>
  rpt conj_tac >>
  TRY (gen_tac >> drule step_preserves_non_output_vars >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_halted >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_call_ctx >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_tx_ctx >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_block_ctx >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_code >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_data_section >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_labels >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_params >> simp[] >> NO_TAC) >>
  TRY (drule step_preserves_prev_hashes >> simp[] >> NO_TAC) >>
  TRY (drule step_inst_non_alloca_non_term_preserves_allocas >> simp[] >> NO_TAC) >>
  metis_tac[effect_distinct, write_effects_sound_transient, write_effects_sound_memory,
            write_effects_sound_accounts, write_effects_sound_returndata,
            write_effects_sound_log, write_effects_sound_immutables]
QED

(* H5: dse_inst preserves is_terminator *)
Triviality dse_inst_is_terminator:
  !dead_ids space inst.
    is_terminator (dse_inst dead_ids space inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rw[dse_inst_def] >>
  simp[mk_nop_inst_def, is_terminator_def] >>
  metis_tac[memory_def_opcode_not_terminator]
QED

(* H6: NOP semantics *)
Triviality step_inst_base_nop:
  !inst s. step_inst_base (mk_nop_inst inst) s = OK s
Proof
  simp[step_inst_base_def, mk_nop_inst_def]
QED

(* H7: step_inst for NOP (non-INVOKE) *)
Triviality step_inst_nop:
  !fuel ctx inst s. step_inst fuel ctx (mk_nop_inst inst) s = OK s
Proof
  rpt gen_tac >>
  `(mk_nop_inst inst).inst_opcode <> INVOKE` by simp[mk_nop_inst_def] >>
  simp[step_inst_non_invoke, step_inst_base_nop]
QED

(* H8: run_blocks never returns OK *)
Triviality run_blocks_never_ok:
  !fuel ctx fn s s'. run_blocks fuel ctx fn s <> OK s'
Proof
  Induct >- simp[Once run_blocks_def] >>
  simp[Once run_blocks_unfold] >>
  rpt gen_tac >> rpt (CASE_TAC >> fs[])
QED

(* ================================================================== *)
(* CORRECTNESS PROOF HELPERS                                          *)
(* ================================================================== *)


(* --- Entry label preservation --- *)

Triviality fmt_preserves_entry_label:
  !bt fn. (!bb. (bt bb).bb_label = bb.bb_label) ==>
    fn_entry_label (function_map_transform bt fn) = fn_entry_label fn
Proof
  rw[fn_entry_label_def, entry_block_def, function_map_transform_def] >>
  Cases_on `fn.fn_blocks` >> simp[]
QED

Triviality clear_nops_preserves_entry_label:
  !fn. fn_entry_label (clear_nops_function fn) = fn_entry_label fn
Proof
  rw[fn_entry_label_def, entry_block_def, clear_nops_function_def] >>
  Cases_on `fn.fn_blocks` >> simp[clear_nops_block_def]
QED

Triviality dse_single_pass_preserves_entry_label:
  !dead_ids space fn.
    fn_entry_label (dse_single_pass dead_ids space fn) = fn_entry_label fn
Proof
  rw[dse_single_pass_def] >> irule fmt_preserves_entry_label >>
  simp[block_map_transform_label]
QED

Triviality dse_iterate_preserves_entry_label:
  !analysis_fn space fn fn'.
    dse_iterate analysis_fn space fn = SOME fn' ==>
    fn_entry_label fn' = fn_entry_label fn
Proof
  rpt strip_tac >> gvs[dse_iterate_def] >>
  qpat_x_assum `OWHILE _ _ _ = _` mp_tac >>
  MAP_EVERY qid_spec_tac [`fn'`, `fn`] >>
  ho_match_mp_tac OWHILE_IND >> rw[] >>
  gvs[dse_single_pass_preserves_entry_label]
QED

Triviality dse_function_space_preserves_entry_label:
  !analysis_fn space fn.
    fn_entry_label (dse_function_space analysis_fn space fn) = fn_entry_label fn
Proof
  rw[dse_function_space_def] >>
  Cases_on `dse_iterate (analysis_fn space) space fn` >>
  simp[clear_nops_preserves_entry_label] >>
  imp_res_tac dse_iterate_preserves_entry_label
QED

(* When vs_allocas = FEMPTY, any mem_loc satisfies memloc_within_alloca:
   FLOOKUP FEMPTY aid = NONE for all aid, making the bound check vacuously T.
   This is the core reason bp_ptrs_bounded holds vacuously at initial state. *)
Triviality memloc_within_alloca_FEMPTY:
  !ml s. s.vs_allocas = FEMPTY ==> memloc_within_alloca ml s
Proof
  rw[memloc_within_alloca_def] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* bp_ptrs_bounded is vacuously true when vs_allocas = FEMPTY *)
Triviality bp_ptrs_bounded_empty_alloca:
  !bp fn s. s.vs_allocas = FEMPTY ==> bp_ptrs_bounded bp fn s
Proof
  rw[bp_ptrs_bounded_def] >> irule memloc_within_alloca_FEMPTY >> simp[]
QED

(* bp_ptr_sound is vacuously true when vs_vars = FEMPTY:
   IS_SOME (lookup_var v s) = IS_SOME (FLOOKUP FEMPTY v) = IS_SOME NONE = F *)
Triviality bp_ptr_sound_empty_vars:
  !bp s. s.vs_vars = FEMPTY ==> bp_ptr_sound bp s
Proof
  rw[bp_ptr_sound_def, lookup_var_def] >> simp[FLOOKUP_DEF]
QED

(* ================================================================== *)
(* COUNTEREXAMPLE: Vacuous preconditions                               *)
(*                                                                    *)
(* Root cause: bp_analyze assigns different Allocation IDs to adjacent *)
(* ALLOCAs and concludes they don't alias. But pointer arithmetic     *)
(* (ADD) from one allocation reaches into the adjacent one. The       *)
(* preconditions alloca_inv + bp_ptrs_bounded are vacuously true at   *)
(* entry state (FEMPTY allocas/vars), so they don't prevent this.     *)
(* ================================================================== *)


Triviality w2n_32_256:
  w2n (32w:256 word) = 32
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def, dimindex_256]
QED

Triviality w2n_100_256:
  w2n (100w:256 word) = 100
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def, dimindex_256]
QED

Triviality w2n_1_256:
  w2n (1w:256 word) = 1
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def, dimindex_256]
QED
(*
 * COUNTEREXAMPLE FUNCTION
 *
 *   Block A: ALLOCA 32 → ptr1 (id=0), ALLOCA 32 → ptr2 (id=1),
 *            ADD(ptr1, 32w) → ptr1_adj (id=2), JMP B (id=3)
 *   Block B: MSTORE [ptr1_adj, 42w] (id=4), MLOAD [ptr2] → result (id=5),
 *            STOP (id=6)
 *
 * bp_analyze: ptr1 → Allocation 0, ptr2 → Allocation 1,
 *             ptr1_adj → Allocation 0 offset 32.
 * may_overlap(Alloc 0 off 32, Alloc 1 off 0) = F (different allocations)
 * → MSTORE at id=4 classified as dead.
 *
 * At runtime (via run_function, starting at entry "A"):
 *   ptr1 = next_alloca_offset(s) = MAX 0 0 = 0
 *   ptr2 = MAX 32 0 = 32
 *   ptr1_adj = ptr1 + 32 = 0 + 32 = 32 = ptr2  ← ALIASED!
 *
 * Original: MSTORE writes 42w at ptr1_adj=32, MLOAD reads at ptr2=32 → 42w
 * Transformed: MSTORE NOP'd, MLOAD reads at ptr2=32 → 0w
 * 42w ≠ 0w → dse_equiv violated.
 *
 * NOTE: The NEW preconditions (alloca_safe_access + step_preserves_safety)
 * reject this counterexample: ADD(ptr1, 32w) produces ptr1_adj = 32 which
 * escapes Allocation 0 (size 32), violating step_preserves_safety.
 *)

Definition cex_fn_def:
  cex_fn = mk_raw_function "test"
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr1"] |>;
         <| inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr2"] |>;
         <| inst_id := 2; inst_opcode := ADD;
            inst_operands := [Var "ptr1"; Lit 32w]; inst_outputs := ["ptr1_adj"] |>;
         <| inst_id := 3; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 4; inst_opcode := MSTORE;
            inst_operands := [Var "ptr1_adj"; Lit 42w]; inst_outputs := [] |>;
         <| inst_id := 5; inst_opcode := MLOAD;
            inst_operands := [Var "ptr2"]; inst_outputs := ["result"] |>;
         <| inst_id := 6; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>]
End
Definition cex_analysis_fn_def:
  cex_analysis_fn (sp:addr_space) (fn':ir_function) =
    if sp = AddrSp_Memory /\ fn' = cex_fn then {4:num} else {}
End

(* Initial state: empty, run_function will set current_bb *)
Definition cex_state_def:
  cex_state = (init_venom_state "") with <|
    vs_transient := K (K 0w);
    vs_accounts := K ARB; vs_call_ctx := ARB;
    vs_tx_ctx := ARB; vs_block_ctx := ARB;
    vs_labels := FEMPTY |+ ("A", 0w:256 word) |+ ("B", 0w)
  |>
End

(* --- bp_analyze computes the expected base pointer map --- *)


Definition cex_bp_def:
  cex_bp = FEMPTY |+ ("ptr1_adj", [Ptr (Allocation 0) (SOME 32)])
                  |+ ("ptr2", [Ptr (Allocation 1) (SOME 0)])
                  |+ ("ptr1", [Ptr (Allocation 0) (SOME 0)])
End

Triviality cex_bp_analyze:
  bp_analyze (cfg_analyze cex_fn) cex_fn = cex_bp
Proof
  simp[bp_analyze_def, df_iterate_def] >>
  `(cfg_analyze cex_fn).cfg_dfs_pre = ["A"; "B"]` by EVAL_TAC >>
  simp[] >>
  `SND (bp_one_pass cex_fn ["A"; "B"] FEMPTY) = cex_bp`
    by (EVAL_TAC >> simp[FUPDATE_COMMUTES, cex_bp_def, w2n_32_256]) >>
  `SND (bp_one_pass cex_fn ["A"; "B"] cex_bp) = cex_bp`
    by (EVAL_TAC >> simp[FUPDATE_EQ, FUPDATE_COMMUTES, cex_bp_def,
                         w2n_32_256]) >>
  once_rewrite_tac[WHILE] >> simp[] >>
  `cex_bp <> FEMPTY` by simp[cex_bp_def] >>
  simp[] >>
  once_rewrite_tac[WHILE] >> simp[]
QED

(* --- all_dead_stores holds for the counterexample --- *)

Triviality cex_all_dead_stores:
  all_dead_stores {4} (cfg_analyze cex_fn) FEMPTY cex_bp AddrSp_Memory cex_fn
Proof
  simp[all_dead_stores_def] >>
  qexistsl [`EL 1 cex_fn.fn_blocks`, `0:num`] >>
  rpt (conj_tac >- (EVAL_TAC >> simp[w2n_32_256] >> NO_TAC)) >>
  CCONTR_TAC >>
  pop_assum (fn th => ASSUME_TAC (REWRITE_RULE[dse_mem_def_live_def] th)) >>
  pop_assum DISJ_CASES_TAC >- (
    pop_assum strip_assume_tac >>
    `LENGTH (EL 1 cex_fn.fn_blocks).bb_instructions = 3` by EVAL_TAC >>
    Cases_on `j` >- decide_tac >>
    Cases_on `n` >- (
      qpat_x_assum `dse_inst_reads_alias _ _ _ _ _` mp_tac >>
      EVAL_TAC) >>
    Cases_on `n'` >- (
      qpat_x_assum `dse_inst_reads_alias _ _ _ _ _` mp_tac >>
      EVAL_TAC) >>
    decide_tac) >>
  pop_assum strip_assume_tac >>
  qpat_x_assum `MEM _ (cfg_succs_of _ _)` mp_tac >>
  EVAL_TAC
QED
(* --- The full precondition holds (for all fn') --- *)
Triviality cex_precondition:
  !sp fn'. all_dead_stores (cex_analysis_fn sp fn')
             (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
             sp fn'
Proof
  rpt gen_tac >> simp[cex_analysis_fn_def] >>
  IF_CASES_TAC
  >- (gvs[cex_bp_analyze, cex_all_dead_stores])
  >- simp[all_dead_stores_def]
QED

(* --- dse_function_space transforms as expected --- *)

Triviality cex_single_pass:
  dse_single_pass {4} AddrSp_Memory cex_fn =
  mk_raw_function "test"
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr1"] |>;
         <| inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr2"] |>;
         <| inst_id := 2; inst_opcode := ADD;
            inst_operands := [Var "ptr1"; Lit 32w]; inst_outputs := ["ptr1_adj"] |>;
         <| inst_id := 3; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 4; inst_opcode := NOP;
            inst_operands := []; inst_outputs := [] |>;
         <| inst_id := 5; inst_opcode := MLOAD;
            inst_operands := [Var "ptr2"]; inst_outputs := ["result"] |>;
         <| inst_id := 6; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>]
Proof
  EVAL_TAC
QED

Triviality cex_analysis_fn_after_nop:
  cex_analysis_fn AddrSp_Memory (dse_single_pass {4} AddrSp_Memory cex_fn) = {}
Proof
  simp[cex_analysis_fn_def] >>
  rewrite_tac[cex_single_pass] >> EVAL_TAC
QED

Definition cex_fn_transformed_def:
  cex_fn_transformed = mk_raw_function "test"
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr1"] |>;
         <| inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr2"] |>;
         <| inst_id := 2; inst_opcode := ADD;
            inst_operands := [Var "ptr1"; Lit 32w]; inst_outputs := ["ptr1_adj"] |>;
         <| inst_id := 3; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 5; inst_opcode := MLOAD;
            inst_operands := [Var "ptr2"]; inst_outputs := ["result"] |>;
         <| inst_id := 6; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>]
End

Triviality cex_iterate:
  dse_iterate (cex_analysis_fn AddrSp_Memory) AddrSp_Memory cex_fn =
  SOME (dse_single_pass {4} AddrSp_Memory cex_fn)
Proof
  simp[dse_iterate_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[cex_analysis_fn_def] >>
  rewrite_tac[cex_single_pass] >> EVAL_TAC >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[cex_analysis_fn_def]
QED

Triviality cex_clear_nops:
  clear_nops_function (dse_single_pass {4} AddrSp_Memory cex_fn) =
  cex_fn_transformed
Proof
  rewrite_tac[cex_single_pass, cex_fn_transformed_def] >> EVAL_TAC
QED

Triviality cex_function_space:
  dse_function_space cex_analysis_fn AddrSp_Memory cex_fn = cex_fn_transformed
Proof
  simp[dse_function_space_def, cex_iterate, cex_clear_nops]
QED

Triviality OWHILE_FALSE:
  !G f s. ~G s ==> OWHILE G f s = SOME s
Proof
  rpt strip_tac >> once_rewrite_tac[OWHILE_THM] >> simp[]
QED

Triviality cex_iterate_identity:
  !sp. dse_iterate (cex_analysis_fn sp) sp cex_fn_transformed =
       SOME cex_fn_transformed
Proof
  gen_tac >> simp[dse_iterate_def] >>
  irule OWHILE_FALSE >> simp[cex_analysis_fn_def] >> EVAL_TAC
QED

Triviality cex_function_space_identity:
  !sp. dse_function_space cex_analysis_fn sp cex_fn_transformed =
    cex_fn_transformed
Proof
  simp[dse_function_space_def, cex_iterate_identity] >> EVAL_TAC
QED

(* dse_function composes three passes; only Memory changes cex_fn *)
Triviality cex_dse_function:
  dse_function cex_analysis_fn cex_fn = cex_fn_transformed
Proof
  simp[dse_function_def, cex_function_space, cex_function_space_identity]
QED

(* --- Execution divergence (run_function version) ---
   Both executions start at entry block A, execute identical ALLOCAs,
   then jump to block B. At block B:
   - Original: MSTORE writes 42w at ptr1_adj=32, then MLOAD reads at ptr2=32 → 42w
   - Transformed: NOP'd MSTORE, MLOAD reads at ptr2=32 from zero-init memory → 0w

   We prove: after block A, ptr1_adj = ptr2 = 32w (the pointers alias).
   This is the key runtime fact that bp_analyze misses. *)

(* After executing block A from entry state *)
Triviality cex_after_block_A:
  exec_block 0 ARB (EL 0 cex_fn.fn_blocks)
    (cex_state with <| vs_current_bb := "A"; vs_inst_idx := 0 |>) =
  OK (cex_state with <|
        vs_vars := FEMPTY |+ ("ptr1", 0w:256 word)
                          |+ ("ptr2", n2w (w2n (32w:256 word)))
                          |+ ("ptr1_adj", 0w + 32w);
        vs_prev_bb := SOME "A"; vs_current_bb := "B"; vs_inst_idx := 0;
        vs_allocas := FEMPTY |+ (0, (0, w2n (32w:256 word)))
                             |+ (1, (w2n (32w:256 word), w2n (32w:256 word)));
        vs_alloca_next := w2n (32w:256 word) + w2n (32w:256 word)
      |>)
Proof
  EVAL_TAC
QED

(* The key aliasing fact: ptr1_adj = ptr2 at runtime *)
Triviality cex_ptrs_alias:
  (0w:256 word) + 32w = n2w (w2n (32w:256 word))
Proof
  simp[w2n_32_256]
QED

(* 42w ≠ 0w at 256 bits *)
Triviality w42_neq_0:
  (42w:256 word) <> 0w
Proof
  simp[wordsTheory.dimword_def, dimindex_256]
QED

(* bp_ptrs_bounded FEMPTY is vacuously true (no alloca-based locations) *)
Triviality bp_ptrs_bounded_FEMPTY:
  !fn s. bp_ptrs_bounded FEMPTY fn s
Proof
  simp[bp_ptrs_bounded_def] >> rpt strip_tac >>
  Cases_on `ops.iao_ofst` >>
  gvs[bp_segment_from_ops_def, LET_THM, bp_ptr_from_op_def,
      bp_get_ptrs_def, FLOOKUP_DEF, ml_undefined_def]
QED
Definition cex_entry_state_def:
  cex_entry_state = cex_state with vs_current_bb := "A"
End

(* Concrete unconditional facts about cex_entry_state:
   These bypass conditional lemma resolution issues in the _FALSE proofs.
   All follow from cex_entry_state having vs_allocas = FEMPTY and vs_vars = FEMPTY.
   These are the VACUITY-theorem analogues of bp_ptr_sound_init / bp_ptrs_bounded_FEMPTY
   (which prove unconditional vacuity for FEMPTY bp). *)
Triviality cex_alloca_inv:
  alloca_inv cex_entry_state
Proof
  `cex_entry_state.vs_allocas = FEMPTY` by
    simp[cex_entry_state_def, cex_state_def, init_venom_state_def] >>
  drule alloca_inv_empty >> simp[]
QED

Triviality cex_bp_ptrs_bounded:
  bp_ptrs_bounded (bp_analyze (cfg_analyze cex_fn) cex_fn) cex_fn cex_entry_state
Proof
  `cex_entry_state.vs_allocas = FEMPTY` by
    simp[cex_entry_state_def, cex_state_def, init_venom_state_def] >>
  drule bp_ptrs_bounded_empty_alloca >> simp[]
QED

Triviality cex_bp_ptr_sound:
  bp_ptr_sound (bp_analyze (cfg_analyze cex_fn) cex_fn) cex_entry_state
Proof
  `cex_entry_state.vs_vars = FEMPTY` by
    simp[cex_entry_state_def, cex_state_def, init_venom_state_def] >>
  drule bp_ptr_sound_empty_vars >> simp[]
QED


(* ===== End-to-end negation: vacuous precondition theorems ===== *)
(*
 * The frozen statements use run_blocks with universally-quantified s.
 * We use cex_state with vs_current_bb := "A" (entry block) as the state.
 *)

(* Byte-level helpers for showing result divergence *)

Triviality get_byte_0w:
  !a be. get_byte a (0w:'a word) be = 0w
Proof
  simp[byteTheory.get_byte_def, wordsTheory.ZERO_SHIFT, wordsTheory.w2w_0]
QED

Triviality word_to_bytes_aux_0w:
  !n be. word_to_bytes_aux n (0w:'a word) be = REPLICATE n (0w:8 word)
Proof
  Induct_on `n` >>
  simp[byteTheory.word_to_bytes_aux_def, get_byte_0w,
       GSYM listTheory.SNOC_APPEND, rich_listTheory.SNOC_REPLICATE]
QED

Triviality word_of_bytes_zero:
  word_of_bytes T (0w:256 word) (REPLICATE 32 (0w:8 word)) = 0w
Proof
  `REPLICATE 32 (0w:8 word) = word_to_bytes (0w:256 word) T`
    by simp[byteTheory.word_to_bytes_def, dimindex_256, word_to_bytes_aux_0w] >>
  simp[vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED

Triviality w2n_0w_plus_32w:
  w2n (0w + 32w : 256 word) = 32
Proof
  simp[wordsTheory.WORD_ADD_0, w2n_32_256]
QED

Triviality w2n_n2w_w2n_32:
  w2n (n2w (w2n (32w : 256 word)) : 256 word) = 32
Proof
  simp[w2n_32_256, wordsTheory.w2n_n2w, wordsTheory.dimword_def, dimindex_256]
QED

Triviality dimindex_256_div_8:
  dimindex(:256) DIV 8 = 32
Proof
  simp[dimindex_256]
QED

(* List algebra helpers for mstore/mload roundtrip at offset 32 *)

Triviality drop_replicate_32:
  !x rest. DROP 32 (REPLICATE 32 (x:'a) ++ rest) = rest
Proof
  rpt gen_tac >>
  `LENGTH (REPLICATE 32 (x:'a)) = 32` by simp[] >>
  metis_tac[rich_listTheory.DROP_LENGTH_APPEND]
QED

Triviality wta_32_is_word_to_bytes:
  !w be. word_to_bytes_aux 32 (w:256 word) be = word_to_bytes w be
Proof
  simp[byteTheory.word_to_bytes_def, dimindex_256]
QED

Triviality take_word_to_bytes_32:
  !w be rest. TAKE 32 (word_to_bytes (w:256 word) be ++ rest) =
              word_to_bytes w be
Proof
  rpt gen_tac >>
  `LENGTH (word_to_bytes (w:256 word) be) = 32`
    by simp[byteTheory.LENGTH_word_to_bytes, dimindex_256] >>
  metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Triviality take_replicate_64_32:
  TAKE 32 (REPLICATE 64 (0w:8 word)) = REPLICATE 32 0w
Proof
  EVAL_TAC
QED

(* Abbreviation for the counterexample state *)

(* Shared: evaluate run_blocks, excluding stuck 256-bit word ops *)
val cex_eval_conv =
  computeLib.RESTR_EVAL_CONV [``word_of_bytes``, ``word_to_bytes_aux``];

(* Original: run_blocks produces Halt with result = 42w *)
Triviality cex_orig_is_halt:
  ?s. run_blocks 2 ARB cex_fn cex_entry_state = Halt s
Proof
  simp[cex_entry_state_def] >>
  CONV_TAC (DEPTH_CONV (fn t =>
    if can (match_term ``run_blocks n ctx fn st``) t
    then cex_eval_conv t else raise UNCHANGED)) >>
  simp[SF SFY_ss]
QED

Triviality cex_run_orig:
  FLOOKUP (let s = (case run_blocks 2 ARB cex_fn cex_entry_state
                     of Halt s => s | _ => ARB) in s.vs_vars)
    "result" = SOME (42w:256 word)
Proof
  simp[cex_entry_state_def] >>
  computeLib.RESTR_EVAL_TAC [``word_of_bytes``, ``word_to_bytes_aux``] >>
  simp[w2n_0w_plus_32w, w2n_n2w_w2n_32, dimindex_256_div_8,
       wta_32_is_word_to_bytes, take_replicate_64_32,
       drop_replicate_32, take_word_to_bytes_32,
       vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED

(* Transformed: run_blocks produces Halt with result = 0w *)
Triviality cex_trans_is_halt:
  ?s. run_blocks 2 ARB cex_fn_transformed cex_entry_state = Halt s
Proof
  simp[cex_entry_state_def] >>
  CONV_TAC (DEPTH_CONV (fn t =>
    if can (match_term ``run_blocks n ctx fn st``) t
    then cex_eval_conv t else raise UNCHANGED)) >>
  simp[SF SFY_ss]
QED

Triviality cex_run_trans:
  FLOOKUP (let s = (case run_blocks 2 ARB cex_fn_transformed cex_entry_state
                     of Halt s => s | _ => ARB) in s.vs_vars)
    "result" = SOME (0w:256 word)
Proof
  simp[cex_entry_state_def] >>
  computeLib.RESTR_EVAL_TAC [``word_of_bytes``] >>
  simp[w2n_n2w_w2n_32] >>
  once_rewrite_tac[GSYM $ EVAL ``REPLICATE 32 (0w:8 word)``] >>
  simp[word_of_bytes_zero]
QED

(* --- Shared counterexample tactic for both vacuity theorem negations --- *)
(* Both proofs follow the same pattern:
   1. Instantiate with cex_analysis_fn, cex_fn, cex_entry_state
   2. Simplify the transform (cex_function_space / cex_dse_function)
   3. Both calls produce Halt → extract "result" variable
   4. Original has 42w, transformed has 0w → contradiction *)


Triviality alloca_inv_empty_allocas:
  !s. s.vs_allocas = FEMPTY ==> alloca_inv s
Proof
  ACCEPT_TAC alloca_inv_empty
QED



(* ===== Per-block simulation for DSE ===== *)

(* R_dse_ok: extends dse_equiv with control-flow agreement.
   Required by block_sim_function which needs R_ok to relate control flow. *)
Definition R_dse_ok_def:
  R_dse_ok (space:addr_space) s1 s2 <=>
    dse_equiv space s1 s2 /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (s1.vs_halted <=> s2.vs_halted)
End

Triviality R_dse_ok_refl:
  !space s. R_dse_ok space s s
Proof
  simp[R_dse_ok_def, dse_equiv_refl]
QED

Triviality R_dse_ok_implies_dse_equiv:
  !space s1 s2. R_dse_ok space s1 s2 ==> dse_equiv space s1 s2
Proof
  simp[R_dse_ok_def]
QED

Triviality R_dse_ok_implies_cf:
  !space s1 s2. R_dse_ok space s1 s2 ==>
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    (s1.vs_halted <=> s2.vs_halted)
Proof
  simp[R_dse_ok_def]
QED

Triviality R_dse_ok_implies_R_term:
  !space s1 s2. R_dse_ok space s1 s2 ==> dse_equiv space s1 s2
Proof
  simp[R_dse_ok_def]
QED

Triviality R_dse_ok_trans:
  !space s1 s2 s3.
    R_dse_ok space s1 s2 /\ R_dse_ok space s2 s3 ==>
    R_dse_ok space s1 s3
Proof
  simp[R_dse_ok_def] >> metis_tac[dse_equiv_trans]
QED

(* Per-block simulation: executing original block on s1 and DSE-transformed
   block on s2 preserves R_dse_ok when s1,s2 start R_dse_ok-related at idx 0.
   This is the core obligation for block_sim_function.
   NOT PROVED: the frozen theorems are FALSE (see counterexamples below). *)

(* Corollary of block_sim_function: re-export with quantifiers matching
   dse_single_pass_correct's usage pattern (fuel,ctx,s at outer scope). *)
Triviality block_sim_function_lift:
  !R_ok R_term bt fn fuel ctx s.
    (!s. R_ok s s) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
      s1.vs_current_bb = s2.vs_current_bb /\
      s1.vs_inst_idx = s2.vs_inst_idx /\
      (s1.vs_halted <=> s2.vs_halted)) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !fuel ctx s1 s2.
        R_ok s1 s2 ==>
        (?e. run_block fuel ctx bb s1 = Error e) \/
        lift_result R_ok R_term R_term
          (run_block fuel ctx bb s1)
          (run_block fuel ctx (bt bb) s2)) /\
    s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result R_ok R_term R_term
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (function_map_transform bt fn) s)
Proof
  rpt strip_tac >> irule block_sim_function >> metis_tac[]
QED



(* ===== Positive theorem statements (with Error disjunct) ===== *)
(* The Error disjunct accounts for error asymmetry: a dead store instruction
   with an undefined operand errors in the original but the NOP'd version
   succeeds. See FALSE1 below for the
   counterexample that motivates this disjunct.

   Precondition chain (sound at every reachable state):
   alloca_inv s: allocas non-overlapping, preserved by step_inst.
   alloca_safe_access fn (alloca_roots fn) s:
     Memory accesses through pointer-derived vars stay within alloca bounds.
     Vacuously true at entry (FEMPTY allocas) — BUT paired with:
   step_preserves_safety fn (alloca_roots fn):
     Static code property — each non-terminator, non-ext-call step
     preserves alloca_safe_access + ptrs_in_alloca_bounds.
     NOT vacuous: it is a property of fn's instructions.
     The aliasing counterexample (ADD ptr1 32w escaping Allocation 0)
     violates this. Together with alloca_inv preservation, this induces
     alloca_inv + alloca_safe_access at every reachable state. *)
Theorem dse_function_space_correct:
  !analysis_fn space fuel ctx fn s.
    alloca_inv s /\
    alloca_safe_access fn (alloca_roots fn) s /\
    step_preserves_safety fn (alloca_roots fn) /\
    (!fn'. all_dead_stores (analysis_fn space fn')
             (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
             space fn') ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function_space analysis_fn space fn) s)
Proof
  cheat
QED

(* Full DSE (all three spaces) preserves dse_all_equiv,
   or original execution errors. *)
Theorem dse_function_correct:
  !analysis_fn fuel ctx fn s.
    alloca_inv s /\
    alloca_safe_access fn (alloca_roots fn) s /\
    step_preserves_safety fn (alloca_roots fn) /\
    (!space fn'.
      all_dead_stores (analysis_fn space fn')
        (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
        space fn') ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function analysis_fn fn) s)
Proof
  cheat
QED

(* ===== ERROR ASYMMETRY COUNTEREXAMPLE: Frozen theorems are FALSE ===== *)
(*
   Root cause: A dead store instruction with an undefined operand errors
   in the original (eval_operand returns NONE for Var not in vs_vars),
   but the NOP'd version succeeds (NOP returns OK s). lift_result R
   (Error e) (Halt s) = F, so the frozen lift_result conclusion fails.

   The all_dead_stores precondition is PURELY STATIC — it checks opcode,
   write location fixedness, effects, liveness — but does NOT require
   instruction operands to be defined at runtime. So all_dead_stores
   can hold even when the instruction's value operand is undefined.

   cex2_fn: Block A with MSTORE [Lit 100w; Var "undef"] (id=0), STOP (id=1)
   - bp_analyze = FEMPTY (no ALLOCAs)
   - bp_get_write_location = offset=SOME 100, size=SOME 32, alloca=NONE, volatile=F
   - ml_is_fixed = T, not volatile, outputs_unused, effects_in_space all hold
   - dse_mem_def_live = F (STOP doesn't read memory, no CFG successors)
   - alloca_roots cex2_fn = {} (no ALLOCA ops)
   - alloca_inv, alloca_safe_access, step_preserves_safety: all vacuously true

   Tightest fix: add Error disjunct to conclusion:
     (?e. run_blocks fuel ctx fn s = Error e) \/
     lift_result (dse_equiv space) ...
   OR: add runtime-definedness precondition for dead store operands.
*)

Definition cex2_fn_def:
  cex2_fn = mk_raw_function "cex2" [
    <| bb_label := "A"; bb_instructions := [
      <| inst_id := 0; inst_opcode := MSTORE;
         inst_operands := [Lit 100w; Var "undef"];
         inst_outputs := [] |>;
      <| inst_id := 1; inst_opcode := STOP;
         inst_operands := [];
         inst_outputs := [] |>
    ] |>
  ]
End

Definition cex2_analysis_fn_def:
  cex2_analysis_fn (sp:addr_space) (fn':ir_function) =
    if sp = AddrSp_Memory /\ fn' = cex2_fn then {0:num} else {}
End

Definition cex2_state_def:
  cex2_state = (init_venom_state "A") with <|
    vs_transient := K (K 0w);
    vs_accounts := K ARB; vs_call_ctx := ARB;
    vs_tx_ctx := ARB; vs_block_ctx := ARB;
    vs_labels := FEMPTY |+ ("A", 0w)
  |>
End

Triviality cex2_orig_errors:
  run_blocks 2 ARB cex2_fn cex2_state = Error "undefined operand"
Proof
  simp[Once run_blocks_def] >>
  simp[cex2_fn_def, mk_raw_function_def, cex2_state_def, lookup_block_def] >>
  simp[Once exec_block_def, get_instruction_def] >>
  simp[step_inst_non_invoke, step_inst_base_def] >>
  EVAL_TAC
QED

Definition cex2_fn_trans_def:
  cex2_fn_trans = mk_raw_function "cex2" [
    <| bb_label := "A"; bb_instructions := [
      <| inst_id := 0; inst_opcode := NOP;
         inst_operands := []; inst_outputs := [] |>;
      <| inst_id := 1; inst_opcode := STOP;
         inst_operands := []; inst_outputs := [] |>
    ] |>
  ]
End


Definition cex2_fn_clear_def:
  cex2_fn_clear = mk_raw_function "cex2" [
    <| bb_label := "A"; bb_instructions := [
      <| inst_id := 1; inst_opcode := STOP;
         inst_operands := []; inst_outputs := [] |>
    ] |>
  ]
End

Triviality cex2_trans_eq:
  dse_single_pass {0} AddrSp_Memory cex2_fn = cex2_fn_trans
Proof
  simp[dse_single_pass_def, function_map_transform_def,
       block_map_transform_def, listTheory.MAP,
       cex2_fn_def, cex2_fn_trans_def, mk_raw_function_def, dse_inst_def,
       mk_nop_inst_def, is_memory_def_opcode_def, is_terminator_def,
       write_effects_def, pred_setTheory.IN_INSERT,
       pred_setTheory.NOT_IN_EMPTY]
QED

Triviality cex2_trans_halts:
  run_blocks 2 ARB (dse_single_pass {0} AddrSp_Memory cex2_fn) cex2_state =
  Halt (cex2_state with <|vs_halted := T; vs_inst_idx := 1|>)
Proof
  simp[cex2_trans_eq] >>
  simp[Once run_blocks_def, cex2_fn_trans_def, mk_raw_function_def,
       cex2_state_def,
       lookup_block_def] >>
  EVAL_TAC
QED

Triviality cex2_alloca_roots_empty:
  alloca_roots cex2_fn = {}
Proof
  simp[alloca_roots_def, cex2_fn_def, mk_raw_function_def, fn_insts_def,
       fn_insts_blocks_def, inst_output_def, is_alloca_op_def,
       pred_setTheory.EXTENSION, PULL_EXISTS, listTheory.MEM,
       listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `inst.inst_opcode` >> gvs[]
QED

Triviality cex2_alloca_inv:
  alloca_inv cex2_state
Proof
  irule alloca_inv_empty_allocas >>
  simp[cex2_state_def, init_venom_state_def]
QED

Triviality cex2_bp_analyze:
  bp_analyze (cfg_analyze cex2_fn) cex2_fn = FEMPTY
Proof
  EVAL_TAC
QED

Triviality cex2_write_loc:
  bp_get_write_location FEMPTY (EL 0 (EL 0 cex2_fn.fn_blocks).bb_instructions) AddrSp_Memory =
  <| ml_offset := SOME (w2n (100w:256 word)); ml_size := SOME (w2n (32w:256 word));
     ml_alloca := NONE; ml_volatile := F |>
Proof
  CONV_TAC (LAND_CONV EVAL) >> simp[]
QED

(* ===== pointer_derived_vars with empty roots ===== *)
(* When no variables are roots for alloca tracking, no variables are
   pointer-derived either. This makes alloca_safe_access and
   ptrs_in_alloca_bounds with empty roots vacuously true. *)

Triviality operand_in_empty_F[local]:
  !x. (case x of Lit _ => F | Var v => MEM v [] | Label _ => F) = F
Proof
  Cases >> simp[]
QED

Triviality FLAT_MAP_K_nil[local]:
  !l. FLAT (MAP (\x:'a. []) l) = []
Proof
  Induct >> simp[]
QED

Triviality pointer_use_step_empty:
  !fn. pointer_use_step fn [] = []
Proof
  simp[pointer_use_step_def, operand_in_empty_F, FLAT_MAP_K_nil]
QED

Triviality pointer_use_step_step_empty:
  !fn. pointer_use_step_step fn [] = NONE
Proof
  simp[pointer_use_step_step_def, pointer_use_step_empty, LET_DEF]
QED

Triviality pointer_use_vars_empty:
  !fn. pointer_use_vars fn [] = []
Proof
  rpt gen_tac >> simp[pointer_use_vars_def] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[sumTheory.ISL, sumTheory.OUTL, pointer_use_step_step_empty] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >>
  simp[sumTheory.ISL]
QED

Triviality pointer_derived_vars_empty:
  !fn. pointer_derived_vars fn {} = {}
Proof
  simp[pointer_derived_vars_def, pointer_use_vars_empty,
       listTheory.SET_TO_LIST_EMPTY, listTheory.SET_TO_LIST_INV]
QED

Triviality alloca_safe_access_FEMPTY_allocas:
  !fn s. pointer_derived_vars fn {} = {} /\ s.vs_allocas = FEMPTY ==>
         alloca_safe_access fn {} s
Proof
  simp[alloca_safe_access_def, pointer_derived_vars_empty, LET_DEF,
       FLOOKUP_EMPTY, pred_setTheory.NOT_IN_EMPTY]
QED

Triviality ptrs_in_alloca_bounds_empty_roots:
  !fn s. pointer_derived_vars fn {} = {} ==>
         ptrs_in_alloca_bounds fn {} s
Proof
  simp[ptrs_in_alloca_bounds_def, pointer_derived_vars_empty,
       pred_setTheory.NOT_IN_EMPTY]
QED

(* Helper: ALLOCA instruction that executes successfully has inst_outputs = [out].
   exec_alloca returns Error unless outputs = [out], and step_inst_base ALLOCA
   either calls exec_alloca or returns Error. So OK v forces outputs = [out].
   Proof: gvs[step_inst_base_def, exec_alloca_def] with inst_opcode=ALLOCA in
   context lets the simplifier select the ALLOCA branch. Then exec_alloca_def
   constrains outputs. Pattern: cf. not_invoke_from_ok in allocaRemapProofs. *)
Triviality alloca_step_ok_has_output[local]:
  !inst s v.
    inst.inst_opcode = ALLOCA /\ step_inst_base inst s = OK v ==>
    ?out. inst.inst_outputs = [out]
Proof
  rpt gen_tac >> strip_tac >>
  CCONTR_TAC >> fs[] >>
  gvs[step_inst_base_def, exec_alloca_def] >>
  gvs[AllCaseEqs()] >>
  metis_tac[]
QED

(* Helper: instruction in a block that is in fn.fn_blocks is in fn_insts fn *)
Triviality fn_insts_blocks_MEM[local]:
  !bbs bb inst.
    MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> simp[fn_insts_blocks_def, listTheory.MEM_APPEND] >> metis_tac[]
QED

Triviality fn_insts_MEM[local]:
  !fn bb inst.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  rw[fn_insts_def] >> irule fn_insts_blocks_MEM >> metis_tac[]
QED

(* Helper: ALLOCA instruction that executes successfully (step_inst_base = OK v)
   and is in a function with alloca_roots fn = {} produces a contradiction.
   exec_alloca requires inst_outputs = [out], making out a member of alloca_roots. *)
Triviality alloca_step_ok_imp_roots_nonempty[local]:
  !fn inst bb s v.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = ALLOCA /\
    step_inst_base inst s = OK v ==>
    alloca_roots fn <> {}
Proof
  rpt strip_tac >>
  CCONTR_TAC >> fs[pred_setTheory.EXTENSION, pred_setTheory.NOT_IN_EMPTY] >>
  `?out. inst.inst_outputs = [out]` by metis_tac[alloca_step_ok_has_output] >>
  `inst_output inst = SOME out` by simp[inst_output_def] >>
  `MEM inst (fn_insts fn)` by metis_tac[fn_insts_MEM] >>
  first_x_assum (qspec_then `out` mp_tac) >>
  simp[alloca_roots_def] >> metis_tac[]
QED

(* When alloca_roots fn = {}, step_preserves_safety fn {} holds.
   An ALLOCA instruction that executes successfully has [out] outputs (from
   exec_alloca), making out a member of alloca_roots — contradiction. So
   ALLOCA is impossible under OK execution, and all clauses are vacuous. *)
(* Memory-nondecreasing: mstore/mstore8/write_memory_with_expansion
   extend memory (append 0s if needed), so LENGTH result >= LENGTH s.vs_memory.
   Proof: expand definition, case-split on whether expansion occurs,
   then arithmetic on LENGTH_APPEND/LENGTH_REPLICATE/LENGTH_TAKE_EQ/LENGTH_DROP. *)
(* When pointer_derived_vars is empty, alloca_safe_access is vacuously
   true (clause 2 quantifies over v IN pv which is empty).
   Clause 1 (off + asz <= LENGTH vs_memory) was removed from
   alloca_safe_access, so no LENGTH reasoning needed. *)
Triviality alloca_safe_access_empty_pv[local]:
  !fn roots s.
    pointer_derived_vars fn roots = {} ==>
    alloca_safe_access fn roots s
Proof
  simp[alloca_safe_access_def, LET_DEF, pred_setTheory.NOT_IN_EMPTY]
QED

(* cex2_fn only has MSTORE and STOP instructions — standalone helper to
   avoid expensive EVAL inside cex2_step_preserves_safety. *)
Triviality cex2_fn_only_mstore_and_stop[local]:
  !inst. MEM inst (fn_insts cex2_fn) ==> inst.inst_opcode = MSTORE \/ inst.inst_opcode = STOP
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[]
QED

(* cex2_fn has no ALLOCA instructions, so alloca_roots = {}.
   step_preserves_safety cex2_fn (alloca_roots fn):
   - Only non-term instruction is MSTORE (STOP is terminator)
   - MSTORE preserves allocas (not ALLOCA, not INVOKE)
   - ptrs_in_alloca_bounds vacuously true (empty pointer-derived vars)
   - alloca_safe_access vacuously true (empty pointer-derived vars,
     clause 2 quantifies over v IN pv = {}) *)
Triviality cex2_step_preserves_safety:
  step_preserves_safety cex2_fn (alloca_roots cex2_fn)
Proof
  simp[cex2_alloca_roots_empty, step_preserves_safety_def] >>
  rpt gen_tac >> strip_tac >>
  `inst.inst_opcode = MSTORE \/ inst.inst_opcode = STOP` by
    metis_tac[cex2_fn_only_mstore_and_stop, fn_insts_MEM] >>
  (* STOP is a terminator, contradicting the hypothesis *)
  `inst.inst_opcode <> STOP` by (
    CCONTR_TAC >> `is_terminator STOP` by EVAL_TAC >> gvs[]) >>
  `inst.inst_opcode = MSTORE` by gvs[] >>
  conj_tac
  >- (irule alloca_safe_access_empty_pv >>
      simp[pointer_derived_vars_empty]) >>
  simp[ptrs_in_alloca_bounds_def, pointer_derived_vars_empty,
       pred_setTheory.NOT_IN_EMPTY]
QED

(* cex2_fn has no successor blocks *)
Triviality cex2_no_succs[local]:
  cfg_succs_of (cfg_analyze cex2_fn) "A" = []
Proof
  EVAL_TAC
QED

(* Concrete instruction records from cex2_fn *)
Triviality cex2_mstore_inst[local]:
  EL 0 (EL 0 cex2_fn.fn_blocks).bb_instructions =
  <| inst_id := 0; inst_opcode := MSTORE;
     inst_operands := [Lit 100w; Var "undef"]; inst_outputs := [] |>
Proof
  EVAL_TAC
QED

Triviality cex2_stop_inst[local]:
  EL 1 (EL 0 cex2_fn.fn_blocks).bb_instructions =
  <| inst_id := 1; inst_opcode := STOP;
     inst_operands := []; inst_outputs := [] |>
Proof
  EVAL_TAC
QED

Triviality cex2_block_length[local]:
  LENGTH (EL 0 cex2_fn.fn_blocks).bb_instructions = 2
Proof
  EVAL_TAC
QED

Triviality cex2_stop_read_loc[local]:
  bp_get_read_location FEMPTY (EL 1 (EL 0 cex2_fn.fn_blocks).bb_instructions) AddrSp_Memory =
  <| ml_offset := SOME 0; ml_size := SOME 0; ml_alloca := NONE; ml_volatile := F |>
Proof
  simp[cex2_stop_inst] >> CONV_TAC (LAND_CONV EVAL) >> simp[]
QED

Triviality cex2_stop_write_loc[local]:
  bp_get_write_location FEMPTY (EL 1 (EL 0 cex2_fn.fn_blocks).bb_instructions) AddrSp_Memory =
  <| ml_offset := SOME 0; ml_size := SOME 0; ml_alloca := NONE; ml_volatile := F |>
Proof
  simp[cex2_stop_inst] >> CONV_TAC (LAND_CONV EVAL) >> simp[]
QED

(* The MSTORE at index 0 in cex2_fn is dead: no read before clobber.
   After inst_idx=0, the only instruction is STOP at index 1.
   STOP doesn't read memory (ml_empty never overlaps anything),
   and there are no k with 0 < k < 1 (clobber check vacuous).
   STOP has no CFG successors, so no cross-block reads either. *)
Triviality cex2_mstore_not_live[local]:
  ~dse_mem_def_live (cfg_analyze cex2_fn) FEMPTY FEMPTY
    (bp_get_write_location FEMPTY (EL 0 (EL 0 cex2_fn.fn_blocks).bb_instructions)
       AddrSp_Memory)
    AddrSp_Memory cex2_fn (EL 0 cex2_fn.fn_blocks) 0
Proof
  CCONTR_TAC >>
  pop_assum (fn th => ASSUME_TAC (REWRITE_RULE[dse_mem_def_live_def] th)) >>
  pop_assum DISJ_CASES_TAC >- (
    (* Case 1: in-block read. Only j=1 (STOP instruction). *)
    pop_assum strip_assume_tac >>
    `LENGTH (EL 0 cex2_fn.fn_blocks).bb_instructions = 2` by
      simp[cex2_block_length] >>
    Cases_on `j` >- decide_tac >>
    Cases_on `n` >- (
      qpat_x_assum `dse_inst_reads_alias _ _ _ _ _` mp_tac >>
      EVAL_TAC) >>
    decide_tac) >>
  (* Case 2: cross-block read. No CFG successors. *)
  pop_assum strip_assume_tac >>
  `(EL 0 cex2_fn.fn_blocks).bb_label = "A"` by EVAL_TAC >>
  qpat_x_assum `MEM _ (cfg_succs_of _ _)` mp_tac >>
  simp[cex2_no_succs]
QED

Triviality cex2_all_dead_stores:
  all_dead_stores {0} (cfg_analyze cex2_fn) FEMPTY
    (bp_analyze (cfg_analyze cex2_fn) cex2_fn) AddrSp_Memory cex2_fn
Proof
  simp[all_dead_stores_def] >>
  qexistsl [`EL 0 cex2_fn.fn_blocks`, `0:num`] >>
  simp[cex2_bp_analyze] >>
  rpt (conj_tac >- (EVAL_TAC >> simp[w2n_100_256, w2n_32_256] >> NO_TAC)) >>
  CCONTR_TAC >>
  pop_assum (fn th => ASSUME_TAC (REWRITE_RULE[dse_mem_def_live_def] th)) >>
  pop_assum DISJ_CASES_TAC >- (
    pop_assum strip_assume_tac >>
    `LENGTH (HD cex2_fn.fn_blocks).bb_instructions = 2` by EVAL_TAC >>
    Cases_on `j` >- decide_tac >>
    Cases_on `n` >- (
      qpat_x_assum `dse_inst_reads_alias _ _ _ _ _` mp_tac >>
      EVAL_TAC) >>
    decide_tac) >>
  pop_assum strip_assume_tac >>
  `(HD cex2_fn.fn_blocks).bb_label = "A"` by EVAL_TAC >>
  qpat_x_assum `MEM _ (cfg_succs_of _ _)` mp_tac >>
  EVAL_TAC
QED

Triviality cex2_precondition:
  alloca_inv cex2_state /\
  alloca_safe_access cex2_fn (alloca_roots cex2_fn) cex2_state /\
  step_preserves_safety cex2_fn (alloca_roots cex2_fn) /\
  (!space fn'.
     all_dead_stores (cex2_analysis_fn space fn')
       (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
       space fn')
Proof
  conj_tac >- simp[cex2_alloca_inv] >>
  conj_tac >- (
    simp[cex2_alloca_roots_empty, alloca_safe_access_FEMPTY_allocas,
         cex2_state_def, init_venom_state_def, pointer_derived_vars_empty]) >>
  conj_tac >- simp[cex2_step_preserves_safety] >>
  rpt gen_tac >> Cases_on `space = AddrSp_Memory /\ fn' = cex2_fn` >- (
    simp[cex2_analysis_fn_def, cex2_all_dead_stores]) >>
  simp[cex2_analysis_fn_def] >>
  simp[all_dead_stores_def, pred_setTheory.NOT_IN_EMPTY]
QED

Triviality cex2_clear_nops[local]:
  clear_nops_function cex2_fn_trans = cex2_fn_clear
Proof
  EVAL_TAC
QED

Triviality cex2_run_clear_halts[local]:
  run_blocks 2 ARB cex2_fn_clear cex2_state =
  Halt (cex2_state with <|vs_halted := T; vs_inst_idx := 0|>)
Proof
  simp[Once run_blocks_def, cex2_fn_clear_def, mk_raw_function_def,
       cex2_state_def,
       lookup_block_def] >>
  EVAL_TAC
QED

Triviality cex2_iterate_step[local]:
  dse_iterate (cex2_analysis_fn AddrSp_Memory) AddrSp_Memory cex2_fn =
  SOME cex2_fn_trans
Proof
  simp[dse_iterate_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[cex2_analysis_fn_def] >>
  rewrite_tac[cex2_trans_eq] >> EVAL_TAC >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[cex2_analysis_fn_def, cex2_fn_trans_def, mk_raw_function_def]
QED

(* Error asymmetry: dead store with undefined operand errors in original
   but NOP'd version halts cleanly. Preconditions (alloca_inv +
   alloca_safe_access + step_preserves_safety) are all vacuously true. *)
Theorem dse_function_space_correct_FALSE1:
  ~(!analysis_fn space fuel ctx fn s.
      alloca_inv s /\
      alloca_safe_access fn (alloca_roots fn) s /\
      step_preserves_safety fn (alloca_roots fn) /\
      (!space fn'.
        all_dead_stores (analysis_fn space fn')
          (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
          space fn') ==>
      lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (dse_function_space analysis_fn space fn) s))
Proof
  simp[] >>
  qexistsl [`cex2_analysis_fn`, `AddrSp_Memory`, `2`, `ARB`,
            `cex2_fn`, `cex2_state`] >>
  strip_assume_tac cex2_precondition >>
  strip_assume_tac cex2_orig_errors >>
  `dse_function_space cex2_analysis_fn AddrSp_Memory cex2_fn =
   cex2_fn_clear` by (
    simp[dse_function_space_def, cex2_iterate_step, cex2_clear_nops]) >>
  strip_assume_tac cex2_run_clear_halts >>
  simp[cex2_orig_errors, lift_result_def]
QED

(* ===== Aliasing counterexamples (cex1) ===== *)
(*
   bp_ptrs_bounded / bp_ptr_sound are vacuously true at entry (FEMPTY
   allocas/vars), allowing cross-allocation pointer arithmetic.
   step_preserves_safety is the missing precondition.
   *)

(* Aliasing: bp_ptrs_bounded vacuously true at entry, allowing
   cross-allocation pointer arithmetic (per-space). *)
Theorem dse_function_space_correct_FALSE2:
  ~(!analysis_fn space fuel ctx fn s.
      alloca_inv s /\
      bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
      (!fn'. all_dead_stores (analysis_fn space fn')
               (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
               space fn') ==>
      lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (dse_function_space analysis_fn space fn) s))
Proof
  simp[] >>
  qexistsl [`cex_analysis_fn`, `AddrSp_Memory`, `2`, `ARB`, `cex_fn`, `cex_entry_state`] >>
  `cex_entry_state.vs_allocas = FEMPTY`
    by (simp[cex_entry_state_def, cex_state_def, init_venom_state_def]) >>
  gvs[alloca_inv_empty_allocas, bp_ptrs_bounded_empty_alloca] >>
  simp[cex_precondition] >>
  simp[cex_function_space] >>
  strip_assume_tac cex_orig_is_halt >>
  strip_assume_tac cex_trans_is_halt >>
  simp[] >> fs[lift_result_def, dse_equiv_def] >>
  rpt strip_tac >>
  qexists `"result"` >> simp[lookup_var_def] >>
  mp_tac cex_run_orig >> mp_tac cex_run_trans >>
  qpat_x_assum `Halt s = _` (assume_tac o GSYM) >>
  qpat_x_assum `Halt s' = _` (assume_tac o GSYM) >>
  simp[w42_neq_0]
QED

(* Aliasing: no bp_ptrs_bounded precondition at all (per-space). *)
Theorem dse_function_space_correct_FALSE3:
  ~(!analysis_fn cfg aliases bp space fuel ctx fn s.
      (!fn'. all_dead_stores (analysis_fn space fn')
               (cfg_analyze fn') aliases (bp_analyze (cfg_analyze fn') fn')
               space fn') ==>
      lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (dse_function_space analysis_fn space fn) s))
Proof
  simp[] >>
  qexistsl [`cex_analysis_fn`, `FEMPTY`,
            `AddrSp_Memory`, `2`, `ARB`, `cex_fn`, `cex_entry_state`] >>
  conj_tac >- simp[cex_precondition] >>
  simp[cex_function_space] >>
  strip_assume_tac cex_orig_is_halt >>
  strip_assume_tac cex_trans_is_halt >>
  simp[] >> fs[lift_result_def, dse_equiv_def] >>
  rpt strip_tac >>
  qexists `"result"` >> simp[lookup_var_def] >>
  mp_tac cex_run_orig >> mp_tac cex_run_trans >>
  qpat_x_assum `Halt s = _` (assume_tac o GSYM) >>
  qpat_x_assum `Halt s' = _` (assume_tac o GSYM) >>
  simp[w42_neq_0]
QED

(* Aliasing: bp_ptrs_bounded + bp_ptr_sound vacuously true at entry
   (all-spaces). *)
Theorem dse_function_correct_FALSE4:
  ~(!analysis_fn fuel ctx fn s.
      alloca_inv s /\
      bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
      bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
      (!space fn'.
        all_dead_stores (analysis_fn space fn')
          (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
          space fn') ==>
      lift_result dse_all_equiv dse_all_equiv dse_all_equiv
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (dse_function analysis_fn fn) s))
Proof
  simp[] >>
  qexistsl [`cex_analysis_fn`, `2`, `ARB`, `cex_fn`, `cex_entry_state`] >>
  simp[cex_alloca_inv, cex_bp_ptr_sound, cex_bp_ptrs_bounded,
       cex_precondition, cex_dse_function] >>
  strip_assume_tac cex_orig_is_halt >>
  strip_assume_tac cex_trans_is_halt >>
  simp[] >> fs[lift_result_def, dse_all_equiv_def] >>
  rpt strip_tac >>
  qexists `"result"` >> simp[lookup_var_def] >>
  mp_tac cex_run_orig >> mp_tac cex_run_trans >>
  qpat_x_assum `Halt s = _` (assume_tac o GSYM) >>
  qpat_x_assum `Halt s' = _` (assume_tac o GSYM) >>
  simp[w42_neq_0]
QED

(* Aliasing: unconstrained bp, bp_ptr_sound + bp_ptrs_bounded not tied
   to bp_analyze (all-spaces). *)
Theorem dse_function_correct_FALSE5:
  ~(!analysis_fn aliases fuel ctx fn s bp.
      bp_ptr_sound bp s /\ bp_ptrs_bounded bp fn s /\
      (!space fn'.
        all_dead_stores (analysis_fn space fn')
          (cfg_analyze fn') aliases (bp_analyze (cfg_analyze fn') fn')
          space fn') ==>
      lift_result dse_all_equiv dse_all_equiv dse_all_equiv
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (dse_function analysis_fn fn) s))
Proof
  simp[] >>
  qexistsl [`cex_analysis_fn`, `FEMPTY`, `2`, `ARB`,
            `cex_fn`, `cex_entry_state`, `FEMPTY`] >>
  simp[bp_ptr_sound_init, bp_ptrs_bounded_FEMPTY, cex_precondition] >>
  simp[cex_dse_function] >>
  strip_assume_tac cex_orig_is_halt >>
  strip_assume_tac cex_trans_is_halt >>
  simp[] >> fs[lift_result_def, dse_all_equiv_def] >>
  rpt strip_tac >>
  qexists `"result"` >> simp[lookup_var_def] >>
  mp_tac cex_run_orig >> mp_tac cex_run_trans >>
  qpat_x_assum `Halt s = _` (assume_tac o GSYM) >>
  qpat_x_assum `Halt s' = _` (assume_tac o GSYM) >>
  simp[w42_neq_0]
QED


(* Helper: alloca_roots are finite *)
Triviality FINITE_alloca_roots[local]:
  !fn. FINITE (alloca_roots fn)
Proof
  rw[alloca_roots_def] >>
  irule pred_setTheory.SUBSET_FINITE >>
  qexists `set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` >>
  conj_tac >- simp[listTheory.FINITE_LIST_TO_SET] >>
  rw[pred_setTheory.SUBSET_DEF] >>
  gvs[inst_output_def, AllCaseEqs()] >>
  simp[listTheory.MEM_FLAT, listTheory.MEM_MAP, PULL_EXISTS] >>
  HINT_EXISTS_TAC >> simp[]
QED

Triviality pointer_use_step_step_append[local]:
  !fn input new_vars.
    pointer_use_step_step fn input = SOME new_vars ==>
    !v. MEM v input ==> MEM v new_vars
Proof
  rw[pointer_use_step_step_def] >>
  simp[listTheory.MEM_APPEND]
QED

Triviality MEM_pointer_use_vars[local]:
  !fn vars v. MEM v vars ==> MEM v (pointer_use_vars fn vars)
Proof
  rpt strip_tac >> simp[pointer_use_vars_def] >>
  qabbrev_tac `g = \w:string list + string list.
    case pointer_use_step_step fn (OUTL w) of
      NONE => INR (OUTL w) | SOME vs => INL vs` >>
  qspecl_then [`ISL`, `g`, `INL vars`]
    mp_tac (DB.fetch "While" "OWHILE_INV_IND"
      |> INST_TYPE [alpha |-> ``:string list + string list``]
      |> Q.INST [`P` |->
           `\s. case s of INL l => MEM v l | INR l => MEM v l`]
      |> SIMP_RULE (srw_ss()) []) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      rename [`ISL xx`] >> Cases_on `xx` >> gvs[Abbr`g`] >>
      Cases_on `pointer_use_step_step fn x` >> simp[] >>
      gvs[pointer_use_step_step_def, LET_DEF] >> rw[] >> simp[listTheory.MEM_APPEND]) >>
  disch_tac >>
  Cases_on `OWHILE ISL g (INL vars)` >> simp[] >>
  Cases_on `x` >> simp[] >> res_tac >> gvs[]
QED

Triviality alloca_roots_subset_pointer_derived_vars[local]:
  !fn x. x IN alloca_roots fn ==> x IN pointer_derived_vars fn (alloca_roots fn)
Proof
  rw[pointer_derived_vars_def] >>
  irule MEM_pointer_use_vars >>
  simp[listTheory.MEM_SET_TO_LIST, FINITE_alloca_roots]
QED

(* ===== Alloca safety: ALLOCA step breaks step_preserves_safety ===== *)

Triviality alloca_safe_access_init[local]:
  !fn roots. alloca_safe_access fn roots (init_venom_state "")
Proof
  rw[alloca_safe_access_def, init_venom_state_def]
QED

Triviality ptrs_in_alloca_bounds_init[local]:
  !fn roots. ptrs_in_alloca_bounds fn roots (init_venom_state "")
Proof
  rw[ptrs_in_alloca_bounds_def, init_venom_state_def, lookup_var_def]
QED

Triviality exec_alloca_init[local]:
  !inst alloc_size out.
    inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit alloc_size] /\
    inst.inst_outputs = [out] ==>
    ?v. step_inst_base inst (init_venom_state "") = OK v /\
        v.vs_allocas = FEMPTY |+ (inst.inst_id, (0, w2n alloc_size)) /\
        v.vs_alloca_next = w2n alloc_size /\
        v.vs_memory = [] /\
        lookup_var out v = SOME (n2w 0)
Proof
  rpt strip_tac >>
  qexists `(init_venom_state "") with <|
    vs_vars := FEMPTY |+ (out,0w);
    vs_allocas := FEMPTY |+ (inst.inst_id,(0,w2n alloc_size));
    vs_alloca_next := w2n alloc_size
  |>` >>
  ONCE_REWRITE_TAC[step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = ALLOCA`
    (fn th => PURE_REWRITE_TAC[th]) >>
  simp[exec_alloca_def] >>
  simp[init_venom_state_def, update_var_def, lookup_var_def] >>
  simp[FLOOKUP_UPDATE, venom_state_component_equality]
QED

(* alloca_step_breaks_safety was TRUE under the old alloca_safe_access
   (clause 1: off + asz <= LENGTH vs_memory fails post-ALLOCA because
   memory hasn't expanded yet). After removing clause 1, ALLOCA no
   longer necessarily breaks alloca_safe_access — clause 2 is about
   pointer-based access bounds, not memory size. ALLOCA still breaks
   ptrs_in_alloca_bounds for alloc_size = 0 (zero-size allocation means
   the pointer value 0w is NOT in any region), but that's a corner case.
   For alloc_size > 0, both alloca_safe_access and ptrs_in_alloca_bounds
   ARE preserved by ALLOCA.

   The key insight: step_preserves_safety's main value is blocking
   cross-allocation pointer arithmetic (like ADD ptr1 32w escaping
   Allocation 0). That's what the aliasing counterexample exploits. *)
