(*
 * Concretize Memory Locations — Correctness Statement
 *
 * Three components:
 * 1. Allocator soundness: non-overlapping for simultaneously-live allocas.
 * 2. Liveness + allocator: compute_alloc_map satisfies live_non_overlapping.
 * 3. Simulation: given well-formedness (venom_wf, inst_wf, ssa_form,
 *    distinct IDs), alloca mapping and invariants (all_allocas_mapped,
 *    overflow-safe, write-before-read, safe access, non-overlapping,
 *    sizes match), pointer safety (confined, affine ops, no OOB
 *    arithmetic, phi-preserve variables), preservation of invariants
 *    across eval_phis/exec_block/step_inst, excluded opcodes (no
 *    INVOKE/NOP/MEMTOP/LOG/MCOPY/EXTCODECOPY/DRET/ext_call),
 *    all_mem_via_pointer, mem_size_non_pv, mem_write_tail_non_pv,
 *    and concretize_rel on initial states, the transformed program
 *    preserves semantics under the liveness-aware concretize_rel.
 *)

Theory concretizeMemLocCorrectness
Ancestors
  concretizeMemLocDefs concretizeMemLocProofs
  passSimulationProps passSharedDefs passSharedProps
  allocaRemapDefs pointerConfinedDefs
  venomExecSemantics venomMemDefs venomInst

Theorem concretize_function_correct:
  !amap fn livesets init fuel ctx s1 s2.
    venom_wf ctx /\ fn_inst_wf fn /\ ssa_form fn /\
    fn_inst_ids_distinct fn /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    (!bb s s' n.
       MEM bb fn.fn_blocks /\ eval_phis s bb.bb_instructions = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) (s' with vs_inst_idx := n)) /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel ctx bb s s' init0 init1.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s ==>
       alloca_overflow_safe fn amap s') /\
    (!fuel0 ctx0 bb inst0 s s' init0 init1.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    live_non_overlapping livesets amap fn /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
                EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions)
      fn.fn_blocks /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (run_blocks fuel ctx fn s1)
        (run_blocks fuel ctx (concretize_function amap fn) s2)
Proof
  ACCEPT_TAC concretize_function_correct_proof
QED


Theorem MAP_EQ_MEM[local]:
  (!x. MEM x xs ==> f x = g x) ==> MAP f xs = MAP g xs
Proof
  Induct_on `xs` >> simp[] >> metis_tac[]
QED

Theorem concretize_inst_positions_adapter[local]:
  MEM inst (fn_insts fn) /\
  (!inst out. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_outputs = [out] ==>
     FLOOKUP amap out =
       OPTION_MAP n2w (FLOOKUP positions (Allocation inst.inst_id))) ==>
  concretize_inst_with_positions positions inst = concretize_inst amap inst
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (Cases_on `inst.inst_outputs`
      >- gvs[concretize_inst_with_positions_def, concretize_inst_def,
             is_alloca_op_def]
      >> Cases_on `t`
      >- (`FLOOKUP amap h =
             OPTION_MAP n2w
               (FLOOKUP positions (Allocation inst.inst_id))` by
            metis_tac[] >>
          Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >>
          gvs[concretize_inst_with_positions_def, concretize_inst_def,
              is_alloca_op_def])
      >> gvs[concretize_inst_with_positions_def, concretize_inst_def,
             is_alloca_op_def])
  >> Cases_on `inst.inst_opcode` >>
     gvs[concretize_inst_with_positions_def, concretize_inst_def,
         is_alloca_op_def]
QED

Theorem concretize_block_maps_adapter[local]:
  (!inst. MEM inst (fn_insts_blocks blocks) ==>
     concretize_inst_with_positions positions inst = concretize_inst amap inst) ==>
  MAP (block_map_transform (concretize_inst_with_positions positions)) blocks =
  MAP (block_map_transform (concretize_inst amap)) blocks
Proof
  Induct_on `blocks`
  >- simp[]
  >> simp[fn_insts_blocks_def,
          passSimulationDefsTheory.block_map_transform_def] >> rpt strip_tac >>
  `MAP (concretize_inst_with_positions positions) h.bb_instructions =
   MAP (concretize_inst amap) h.bb_instructions` by
    (irule MAP_EQ_MEM >> simp[]) >>
  simp[]
QED

Theorem concretize_function_positions_adapter:
  (!inst out. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_outputs = [out] ==>
     FLOOKUP amap out =
       OPTION_MAP n2w
         (FLOOKUP positions (Allocation inst.inst_id))) ==>
  concretize_function_with_positions positions fn =
  concretize_function amap fn
Proof
  strip_tac >>
  simp[concretize_function_with_positions_def, concretize_function_def,
       passSimulationDefsTheory.function_map_transform_def] >>
  `MAP (block_map_transform (concretize_inst_with_positions positions))
       fn.fn_blocks =
   MAP (block_map_transform (concretize_inst amap)) fn.fn_blocks` by
    (irule concretize_block_maps_adapter >>
     rpt strip_tac >>
     `MEM inst (fn_insts fn)` by simp[fn_insts_def] >>
     metis_tac[concretize_inst_positions_adapter]) >>
  simp[]
QED

Theorem concretize_function_with_positions_correct:
  !positions amap fn livesets init fuel ctx s1 s2.
    (!inst out. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_outputs = [out] ==>
       FLOOKUP amap out =
         OPTION_MAP n2w (FLOOKUP positions (Allocation inst.inst_id))) /\
    venom_wf ctx /\ fn_inst_wf fn /\ ssa_form fn /\
    fn_inst_ids_distinct fn /\
    all_allocas_mapped fn amap /\
    amap_from_allocas fn amap /\
    concretize_pointer_confined fn amap /\
    alloca_inv s1 /\
    alloca_overflow_safe fn amap s1 /\
    affine_pointer_ops fn (FDOM amap) /\
    pointer_arith_in_region fn (FDOM amap) /\
    phi_pv_all_var fn (FDOM amap) /\
    alloca_write_before_read fn (FDOM amap) livesets init s1 /\
    alloca_safe_access fn (FDOM amap) s1 /\
    (!bb s s' n.
       MEM bb fn.fn_blocks /\ eval_phis s bb.bb_instructions = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) (s' with vs_inst_idx := n)) /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel ctx bb s s' init0 init1.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel ctx bb s s'.
       MEM bb fn.fn_blocks /\ exec_block fuel ctx bb s = OK s' /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_overflow_safe fn amap s ==>
       alloca_overflow_safe fn amap s') /\
    (!fuel0 ctx0 bb inst0 s s' init0 init1.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_write_before_read fn (FDOM amap) livesets init0 s ==>
       alloca_write_before_read fn (FDOM amap) livesets init1 s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       alloca_safe_access fn (FDOM amap) s ==>
       alloca_safe_access fn (FDOM amap) s') /\
    (!fuel0 ctx0 bb inst0 s s'.
       MEM bb fn.fn_blocks /\ MEM inst0 bb.bb_instructions /\
       step_inst fuel0 ctx0 inst0 s = OK s' /\
       ~is_terminator inst0.inst_opcode /\
       concrete_allocas_non_overlapping amap fn s ==>
       concrete_allocas_non_overlapping amap fn s') /\
    all_mem_via_pointer fn (FDOM amap) /\
    mem_size_non_pv fn (FDOM amap) /\
    mem_write_tail_non_pv fn (FDOM amap) /\
    concrete_allocas_non_overlapping amap fn s1 /\
    alloca_sizes_match fn s1 /\
    live_non_overlapping livesets amap fn /\
    EVERY (\bb. EVERY (\i. i.inst_opcode <> INVOKE) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> NOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MEMTOP) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> LOG) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> MCOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> EXTCODECOPY) bb.bb_instructions /\
                EVERY (\i. i.inst_opcode <> DRET) bb.bb_instructions /\
                EVERY (\i. ~is_ext_call_op i.inst_opcode) bb.bb_instructions)
      fn.fn_blocks /\
    concretize_rel amap fn livesets init s1 s2 ==>
    ?init'.
      lift_result
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (concretize_rel amap fn livesets init')
        (run_blocks fuel ctx fn s1)
        (run_blocks fuel ctx (concretize_function_with_positions positions fn) s2)
Proof
  rpt strip_tac >>
  `concretize_function_with_positions positions fn = concretize_function amap fn` by
    (irule concretize_function_positions_adapter >> metis_tac[]) >>
  simp[] >>
  irule concretize_function_correct >>
  rpt conj_tac >> metis_tac[]
QED
(* ===== concretize_inst structural properties ===== *)

Triviality ci_preserves_id:
  !amap inst. (concretize_inst amap inst).inst_id = inst.inst_id
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >> simp[mk_nop_inst_def, mk_assign_inst_def]
QED

Triviality ci_terminator_identity:
  !amap inst. is_terminator inst.inst_opcode ==>
              concretize_inst amap inst = inst
Proof
  simp[concretize_inst_def] >> rpt strip_tac >>
  `~is_alloca_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> fs[is_alloca_op_def, is_terminator_def]) >>
  simp[]
QED

Triviality ci_non_term:
  !amap inst. ~is_terminator inst.inst_opcode ==>
              ~is_terminator (concretize_inst amap inst).inst_opcode
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >> gvs[mk_nop_inst_def, mk_assign_inst_def, is_terminator_def]
QED

Triviality ci_phi:
  !amap inst. inst.inst_opcode = PHI ==>
              (concretize_inst amap inst).inst_opcode = PHI
Proof
  simp[concretize_inst_def, is_alloca_op_def]
QED

Triviality ci_non_phi:
  !amap inst. inst.inst_opcode <> PHI ==>
              (concretize_inst amap inst).inst_opcode <> PHI
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >> gvs[mk_nop_inst_def, mk_assign_inst_def]
QED

Triviality ci_outputs:
  !amap inst. inst.inst_outputs = (concretize_inst amap inst).inst_outputs \/
              (concretize_inst amap inst).inst_outputs = []
Proof
  rw[concretize_inst_def] >>
  rpt CASE_TAC >> simp[mk_nop_inst_def, mk_assign_inst_def]
QED

(* ===== Obligations ===== *)

Theorem concretize_preserves_wf_function:
  !amap fn. wf_function fn ==> wf_function (concretize_function amap fn)
Proof
  rpt strip_tac >> simp[concretize_function_def] >>
  irule clear_nops_function_preserves_wf >>
  irule map_transform_preserves_wf >>
  simp[ci_preserves_id, ci_terminator_identity, ci_non_term, ci_phi, ci_non_phi]
QED

Theorem concretize_preserves_ssa_form:
  !amap fn. wf_function fn /\ ssa_form fn ==> ssa_form (concretize_function amap fn)
Proof
  rpt strip_tac >> simp[concretize_function_def] >>
  irule clear_nops_function_preserves_ssa >>
  irule map_transform_preserves_ssa >>
  simp[ci_preserves_id, ci_outputs] >>
  irule map_transform_preserves_wf >>
  simp[ci_preserves_id, ci_terminator_identity, ci_non_term, ci_phi, ci_non_phi]
QED
