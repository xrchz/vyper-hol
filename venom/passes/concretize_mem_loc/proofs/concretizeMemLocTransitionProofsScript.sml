(* Structural ownership-transition facts for checked concretization. *)

Theory concretizeMemLocTransitionProofs
Ancestors
  staticLayoutCompletionProofs staticLayoutAllocatorProofs
  staticLayoutFoldProofs staticLayoutWf concretizeMemLocDefs staticLayoutDefs
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

Theorem compute_function_layout_fuel_static_items[local]:
  compute_function_layout_fuel fuel reserved fn = SOME layout ==>
  ?items. static_alloca_items fn = SOME items
Proof
  simp[compute_function_layout_fuel_def] >>
  Cases_on `static_alloca_items fn` >> gvs[]
QED

Theorem compute_function_layout_eval_static_items[local]:
  compute_function_layout_eval reserved fn = SOME layout ==>
  ?items. static_alloca_items fn = SOME items
Proof
  simp[compute_function_layout_eval_def, complete_alloc_positions_def] >>
  Cases_on `static_alloca_items fn` >> gvs[]
QED

Theorem compute_function_layout_eval_wf[local]:
  compute_function_layout_eval reserved fn = SOME layout ==>
  concretize_layout_wf reserved fn layout
Proof
  strip_tac >>
  `?items. static_alloca_items fn = SOME items` by
    metis_tac[compute_function_layout_eval_static_items] >>
  qpat_x_assum `compute_function_layout_eval reserved fn = SOME layout` mp_tac >>
  simp[compute_function_layout_eval_def] >>
  Cases_on `complete_alloc_positions fn.fn_forced_alloc_positions
              reserved fn FEMPTY` >> gvs[] >>
  Cases_on `global_reserved_end reserved 0` >>
  gvs[mk_concretize_layout_def] >>
  Cases_on `allocation_eom_fold x (fn_insts fn) x'` >>
  gvs[mk_concretize_layout_def] >>
  strip_tac >> gvs[] >>
  drule complete_alloc_positions_success >> strip_tac >>
  simp[concretize_layout_wf_def] >>
  drule allocation_eom_fold_success >> strip_tac >>
  `x' < dimword (:256)` by
    (qspecl_then [`reserved`,`0`,`x'`] mp_tac
       global_reserved_end_lt_dimword >> simp[]) >>
  conj_tac
  >- (qspecl_then [`x`,`fn_insts fn`,`x'`,`x''`] mp_tac
        allocation_eom_fold_lt_dimword >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `?size. inst.inst_operands = [Lit size] /\
           exact_static_alloca inst =
             SOME (Allocation inst.inst_id,w2n size)` by
    metis_tac[static_alloca_items_ALLOCA_exact] >>
  qpat_x_assum `!inst alloc sz. _`
    (qspecl_then [`inst`,`Allocation inst.inst_id`,`w2n size'`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!inst. MEM inst (fn_insts fn) /\ _ ==> _`
    (qspec_then `inst` mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `allocation_end x inst = SOME alloc_end` mp_tac >>
  simp[allocation_end_def] >> strip_tac >>
  qpat_x_assum `!alloc pos. FLOOKUP x alloc = SOME pos ==> _`
    (qspecl_then [`Allocation inst.inst_id`,`pos`] mp_tac) >>
  simp[] >> strip_tac >>
  `w2n size' = sz` by
    metis_tac[static_alloca_items_exact_key_size_unique] >>
  gvs[] >> simp[static_position_wf_def]
QED

Theorem concretize_function_fuel_removes_alloca:
  concretize_function_fuel fuel reserved fn = SOME fn' ==>
  ~fn_has_alloca fn'
Proof
  simp[concretize_function_fuel_def] >>
  Cases_on `fn_has_static_layout fn`
  >- (rpt strip_tac >> gvs[]) >>
  Cases_on `compute_function_layout_fuel fuel reserved fn`
  >- gvs[] >>
  gvs[] >>
  drule compute_function_layout_fuel_static_items >> strip_tac >>
  `concretize_layout_wf reserved fn x` by
    metis_tac[compute_function_layout_fuel_wf] >>
  `~fn_has_alloca
      (concretize_function_with_positions x.cl_positions fn)` by
    (irule concretize_function_with_positions_removes_alloca >>
     metis_tac[]) >>
  rpt strip_tac >>
  gvs[apply_concretize_layout_def, fn_has_alloca_def, fn_insts_def,
      EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

Theorem concretize_function_eval_removes_alloca:
  concretize_function_eval reserved fn = SOME fn' ==>
  ~fn_has_alloca fn'
Proof
  simp[concretize_function_eval_def] >>
  Cases_on `fn_has_static_layout fn`
  >- (rpt strip_tac >> gvs[]) >>
  Cases_on `compute_function_layout_eval reserved fn`
  >- gvs[] >>
  gvs[] >>
  drule compute_function_layout_eval_static_items >> strip_tac >>
  `concretize_layout_wf reserved fn x` by
    metis_tac[compute_function_layout_eval_wf] >>
  `~fn_has_alloca
      (concretize_function_with_positions x.cl_positions fn)` by
    (irule concretize_function_with_positions_removes_alloca >>
     metis_tac[]) >>
  rpt strip_tac >>
  gvs[apply_concretize_layout_def, fn_has_alloca_def, fn_insts_def,
      EVERY_MEM, EXISTS_MEM] >> metis_tac[]
QED

val _ = export_theory();
