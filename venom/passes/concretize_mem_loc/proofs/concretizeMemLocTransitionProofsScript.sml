(* Structural ownership-transition facts for checked concretization. *)

Theory concretizeMemLocTransitionProofs
Ancestors
  staticLayoutCompletionProofs staticLayoutAllocatorProofs
  staticLayoutWf concretizeMemLocDefs staticLayoutDefs
  passSimulationDefs passSharedDefs passSharedProps venomInst list

(* Disprove-first probe for the proposed certificate boundary. *)
Theorem concretize_layout_wf_malformed_output_probe:
  let fn = mk_raw_function "f"
    [<| bb_label := "entry";
        bb_instructions := [mk_inst 1 ALLOCA [Lit 1w] []] |>] in
  let layout = <| cl_positions := FEMPTY |+ (Allocation 1,0);
                  cl_eom := 1 |> in
    concretize_layout_wf [] fn layout /\
    fn_has_alloca
      (concretize_function_with_positions layout.cl_positions fn)
Proof
  EVAL_TAC >>
  simp[concretize_layout_wf_def, static_fn_positions_wf_def,
       static_position_wf_def, reserved_intervals_disjoint_def,
       global_reserved_end_def, allocation_eom_fold_def,
       allocation_end_def, concretize_function_with_positions_def,
       function_map_transform_def, block_map_transform_def,
       clear_nops_function_def, clear_nops_block_def,
       fn_has_alloca_def, fn_insts_def, fn_insts_blocks_def,
       concretize_inst_with_positions_def]
QED

Theorem concretize_inst_with_positions_not_alloca[local]:
  static_alloca_items fn = SOME items /\
  concretize_layout_wf reserved fn layout /\
  MEM inst (fn_insts fn) ==>
  (concretize_inst_with_positions layout.cl_positions inst).inst_opcode <>
    ALLOCA
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (`?size. inst.inst_operands = [Lit size] /\
              exact_static_alloca inst =
                SOME (Allocation inst.inst_id,w2n size)` by
        metis_tac[static_alloca_items_ALLOCA_exact] >>
      `?size pos.
         inst.inst_operands = [Lit size] /\
         FLOOKUP layout.cl_positions (Allocation inst.inst_id) = SOME pos` by
        (fs[concretize_layout_wf_def] >> metis_tac[]) >>
      gvs[exact_static_alloca_def, exact_static_alloca_size_def,
          AllCaseEqs(), concretize_inst_with_positions_def,
          mk_assign_inst_def])
  >> gvs[concretize_inst_with_positions_def]
QED

Theorem is_alloca_op_eq_alloca[local]:
  is_alloca_op op <=> op = ALLOCA
Proof
  Cases_on `op` >> simp[is_alloca_op_def]
QED

Theorem fn_insts_blocks_map_transform_mem[local]:
  MEM e (fn_insts_blocks (MAP (block_map_transform transform) blocks)) ==>
  ?inst. MEM inst (fn_insts_blocks blocks) /\ e = transform inst
Proof
  Induct_on `blocks`
  >- simp[fn_insts_blocks_def]
  >> rpt gen_tac
  >> simp[fn_insts_blocks_def, block_map_transform_def]
  >> strip_tac
  >- (gvs[MEM_MAP] >> qexists `y` >> simp[])
  >> first_x_assum drule >> strip_tac
  >> qexists `inst` >> simp[]
QED

Theorem transformed_blocks_have_no_alloca[local]:
  (!inst. MEM inst (fn_insts_blocks blocks) ==>
          (transform inst).inst_opcode <> ALLOCA) ==>
  ~EXISTS (\inst. is_alloca_op inst.inst_opcode)
    (fn_insts_blocks (MAP (block_map_transform transform) blocks))
Proof
  strip_tac >> strip_tac >>
  gvs[EXISTS_MEM, is_alloca_op_eq_alloca] >>
  drule fn_insts_blocks_map_transform_mem >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Theorem concretize_function_with_positions_removes_alloca:
  static_alloca_items fn = SOME items /\
  concretize_layout_wf reserved fn layout ==>
  ~fn_has_alloca
    (concretize_function_with_positions layout.cl_positions fn)
Proof
  strip_tac >>
  qabbrev_tac `mapped =
    function_map_transform
      (block_map_transform
        (concretize_inst_with_positions layout.cl_positions)) fn` >>
  `~EXISTS (\inst. is_alloca_op inst.inst_opcode)
      (fn_insts_blocks
        (MAP (block_map_transform
          (concretize_inst_with_positions layout.cl_positions))
          fn.fn_blocks))` by
    (irule transformed_blocks_have_no_alloca >>
     rpt strip_tac >>
     `(concretize_inst_with_positions layout.cl_positions inst).inst_opcode <>
       ALLOCA` by
       (irule concretize_inst_with_positions_not_alloca >>
        simp[fn_insts_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `~fn_has_alloca mapped` by
    simp[fn_has_alloca_def, Abbr `mapped`, function_map_transform_def,
         fn_insts_def] >>
  simp[concretize_function_with_positions_def, Abbr `mapped`] >>
  strip_tac >>
  gvs[fn_has_alloca_def, EXISTS_MEM] >>
  drule clear_nops_fn_insts_subset >>
  strip_tac >> metis_tac[]
QED

val _ = export_theory();
val _ = export_theory();
