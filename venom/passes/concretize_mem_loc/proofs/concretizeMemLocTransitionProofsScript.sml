(* Structural ownership-transition facts for checked concretization. *)

Theory concretizeMemLocTransitionProofs
Ancestors
  staticLayoutCompletionProofs staticLayoutAllocatorProofs
  staticLayoutFoldProofs staticLayoutWf concretizeMemLocDefs staticLayoutDefs
  passSimulationDefs passSharedDefs passSharedProps venomInst list fcgDefs

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

Theorem collect_static_allocas_no_alloca[local]:
  (!inst. MEM inst insts ==> inst.inst_opcode <> ALLOCA) ==>
  collect_static_allocas insts = SOME []
Proof
  Induct_on `insts` >> simp[collect_static_allocas_def] >> metis_tac[]
QED

Theorem complete_alloc_positions_aux_no_alloca[local]:
  (!inst. MEM inst insts ==> inst.inst_opcode <> ALLOCA) ==>
  complete_alloc_positions_aux insts positions occupied = SOME positions
Proof
  Induct_on `insts` >> simp[complete_alloc_positions_aux_def] >> metis_tac[]
QED

Theorem allocation_eom_fold_no_alloca[local]:
  (!inst. MEM inst insts ==> inst.inst_opcode <> ALLOCA) ==>
  allocation_eom_fold positions insts acc = SOME acc
Proof
  Induct_on `insts` >> simp[allocation_eom_fold_def] >> metis_tac[]
QED

Theorem static_alloca_items_no_alloca[local]:
  ~fn_has_alloca fn ==> static_alloca_items fn = SOME []
Proof
  simp[fn_has_alloca_def, EXISTS_MEM, is_alloca_op_eq_alloca,
       static_alloca_items_def] >>
  metis_tac[collect_static_allocas_no_alloca]
QED

Theorem OPT_MMAP_success_LIST_REL[local]:
  OPT_MMAP f xs = SOME ys ==>
  LIST_REL (\x y. f x = SOME y) xs ys
Proof
  qid_spec_tac `ys` >> Induct_on `xs`
  >- simp[]
  >> rpt gen_tac
  >> Cases_on `f h` >> simp[]
  >> Cases_on `OPT_MMAP f xs` >> simp[]
  >> first_x_assum (qspec_then `x'` mp_tac) >> simp[] >> metis_tac[]
QED

Theorem LIST_REL_mono_imp[local]:
  LIST_REL r xs ys /\ (!x y. r x y ==> s x y) ==>
  LIST_REL s xs ys
Proof
  qid_spec_tac `ys` >> Induct_on `xs`
  >- simp[]
  >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

Theorem LIST_REL_right_EVERY[local]:
  LIST_REL r xs ys /\ (!x y. r x y ==> p y) ==>
  EVERY p ys
Proof
  qid_spec_tac `ys` >> Induct_on `xs`
  >- simp[]
  >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

Theorem LIST_REL_MEM_right[local]:
  LIST_REL r xs ys /\ MEM y ys ==>
  ?x. MEM x xs /\ r x y
Proof
  qid_spec_tac `ys` >> Induct_on `xs`
  >- simp[]
  >> Cases_on `ys` >> simp[] >> metis_tac[]
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

Theorem compute_function_layout_eval_wf:
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


Theorem compute_function_layout_eval_global_bound:
  compute_function_layout_eval reserved fn = SOME layout /\
  global_reserved_end reserved 0 = SOME global_end ==>
  global_end <= layout.cl_eom
Proof
  strip_tac >>
  `concretize_layout_wf reserved fn layout` by
    metis_tac[compute_function_layout_eval_wf] >>
  fs[concretize_layout_wf_def] >>
  gvs[] >>
  metis_tac[allocation_eom_fold_acc_bound]
QED

Theorem concretize_layout_wf_local_bound:
  concretize_layout_wf reserved fn layout /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
  ?size pos. inst.inst_operands = [Lit size] /\
    FLOOKUP layout.cl_positions (Allocation inst.inst_id) = SOME pos /\
    pos + w2n size <= layout.cl_eom
Proof
  simp[concretize_layout_wf_def] >> metis_tac[]
QED

Theorem compute_function_layout_eval_empty:
  ~fn_has_alloca fn /\
  fn.fn_forced_alloc_positions = FEMPTY /\
  reserved_intervals_wf reserved /\
  global_reserved_end reserved 0 = SOME global_end ==>
  ?layout. compute_function_layout_eval reserved fn = SOME layout /\
           layout.cl_eom = global_end
Proof
  rpt strip_tac >>
  `static_alloca_items fn = SOME []` by
    metis_tac[static_alloca_items_no_alloca] >>
  `!inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> ALLOCA` by
    (gvs[fn_has_alloca_def, EXISTS_MEM, is_alloca_op_eq_alloca] >>
     metis_tac[]) >>
  `complete_alloc_positions FEMPTY reserved fn FEMPTY = SOME FEMPTY` by
    (simp[complete_alloc_positions_def, forced_alloc_keys_valid_def,
          candidate_alloc_keys_valid_def, merge_forced_positions_def,
          checked_preserved_intervals_def,
          checked_preserved_intervals_aux_def] >>
     irule complete_alloc_positions_aux_no_alloca >> simp[]) >>
  `allocation_eom_fold FEMPTY (fn_insts fn) global_end = SOME global_end` by
    metis_tac[allocation_eom_fold_no_alloca] >>
  qexists `<| cl_positions := FEMPTY; cl_eom := global_end |>` >>
  simp[compute_function_layout_eval_def, mk_concretize_layout_def]
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
Theorem apply_concretize_layout_metadata_transition[local]:
  fn_identity_metadata_eq (apply_concretize_layout layout fn) fn /\
  fn_fmp_convention_eq (apply_concretize_layout layout fn) fn /\
  (apply_concretize_layout layout fn).fn_forced_alloc_positions = FEMPTY /\
  (apply_concretize_layout layout fn).fn_eom = SOME layout.cl_eom
Proof
  simp[apply_concretize_layout_def, concretize_function_with_positions_def,
       clear_nops_function_def, function_map_transform_def,
       fn_identity_metadata_eq_def, fn_fmp_convention_eq_def]
QED

Theorem concretize_function_fuel_metadata_transition:
  concretize_function_fuel fuel reserved fn = SOME fn' ==>
  fn_identity_metadata_eq fn' fn /\
  fn_fmp_convention_eq fn' fn /\
  fn'.fn_forced_alloc_positions = FEMPTY
Proof
  simp[concretize_function_fuel_def] >>
  Cases_on `fn_has_static_layout fn`
  >- (rpt strip_tac >> gvs[fn_identity_metadata_eq_def,
                            fn_fmp_convention_eq_def]) >>
  Cases_on `compute_function_layout_fuel fuel reserved fn`
  >- gvs[] >>
  rpt strip_tac >> gvs[apply_concretize_layout_metadata_transition]
QED

Theorem concretize_function_eval_metadata_transition:
  concretize_function_eval reserved fn = SOME fn' ==>
  fn_identity_metadata_eq fn' fn /\
  fn_fmp_convention_eq fn' fn /\
  fn'.fn_forced_alloc_positions = FEMPTY
Proof
  simp[concretize_function_eval_def] >>
  Cases_on `fn_has_static_layout fn`
  >- (rpt strip_tac >> gvs[fn_identity_metadata_eq_def,
                            fn_fmp_convention_eq_def]) >>
  Cases_on `compute_function_layout_eval reserved fn`
  >- gvs[] >>
  rpt strip_tac >> gvs[apply_concretize_layout_metadata_transition]
QED

Theorem concretize_function_fuel_sets_eom:
  concretize_function_fuel fuel reserved fn = SOME fn' ==>
  IS_SOME fn'.fn_eom
Proof
  simp[concretize_function_fuel_def] >>
  Cases_on `fn_has_static_layout fn`
  >- (rpt strip_tac >> gvs[fn_has_static_layout_def]) >>
  Cases_on `compute_function_layout_fuel fuel reserved fn`
  >- gvs[] >>
  rpt strip_tac >> gvs[apply_concretize_layout_metadata_transition]
QED

Theorem concretize_function_eval_sets_eom:
  concretize_function_eval reserved fn = SOME fn' ==>
  IS_SOME fn'.fn_eom
Proof
  simp[concretize_function_eval_def] >>
  Cases_on `fn_has_static_layout fn`
  >- (rpt strip_tac >> gvs[fn_has_static_layout_def]) >>
  Cases_on `compute_function_layout_eval reserved fn`
  >- gvs[] >>
  rpt strip_tac >> gvs[apply_concretize_layout_metadata_transition]
QED

Theorem concretize_function_layout_idempotent:
  fn.fn_eom = SOME eom /\ ~fn_has_alloca fn /\
  fn.fn_forced_alloc_positions = FEMPTY ==>
  concretize_function_fuel fuel reserved fn = SOME fn
Proof
  simp[concretize_function_fuel_def, fn_has_static_layout_def]
QED

Theorem concretize_function_rejects_stale_layout_input:
  fn.fn_eom = SOME eom /\
  (fn_has_alloca fn \/ fn.fn_forced_alloc_positions <> FEMPTY) ==>
  concretize_function_fuel fuel reserved fn = NONE
Proof
  simp[concretize_function_fuel_def, fn_has_static_layout_def] >>
  metis_tac[]
QED

Theorem concretize_function_eval_layout_idempotent:
  fn.fn_eom = SOME eom /\ ~fn_has_alloca fn /\
  fn.fn_forced_alloc_positions = FEMPTY ==>
  concretize_function_eval reserved fn = SOME fn
Proof
  simp[concretize_function_eval_def, fn_has_static_layout_def]
QED

Theorem concretize_function_eval_rejects_stale_layout_input:
  fn.fn_eom = SOME eom /\
  (fn_has_alloca fn \/ fn.fn_forced_alloc_positions <> FEMPTY) ==>
  concretize_function_eval reserved fn = NONE
Proof
  simp[concretize_function_eval_def, fn_has_static_layout_def] >>
  metis_tac[]
QED

Theorem concretize_function_fuel_success:
  concretize_function_fuel fuel reserved fn = SOME fn' ==>
  ~fn_has_alloca fn' /\
  fn'.fn_forced_alloc_positions = FEMPTY /\
  IS_SOME fn'.fn_eom /\
  fn_identity_metadata_eq fn' fn /\
  fn_fmp_convention_eq fn' fn
Proof
  metis_tac[concretize_function_fuel_removes_alloca,
            concretize_function_fuel_metadata_transition,
            concretize_function_fuel_sets_eom]
QED

Theorem concretize_function_eval_success:
  concretize_function_eval reserved fn = SOME fn' ==>
  ~fn_has_alloca fn' /\
  fn'.fn_forced_alloc_positions = FEMPTY /\
  IS_SOME fn'.fn_eom /\
  fn_identity_metadata_eq fn' fn /\
  fn_fmp_convention_eq fn' fn
Proof
  metis_tac[concretize_function_eval_removes_alloca,
            concretize_function_eval_metadata_transition,
            concretize_function_eval_sets_eom]
QED


Theorem concretize_function_eval_fresh_layout:
  fn.fn_eom = NONE /\
  concretize_function_eval reserved fn = SOME fn' ==>
  ?layout.
    compute_function_layout_eval reserved fn = SOME layout /\
    fn' = apply_concretize_layout layout fn /\
    concretize_layout_wf reserved fn layout /\
    (!global_end. global_reserved_end reserved 0 = SOME global_end ==>
      global_end <= layout.cl_eom) /\
    (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA ==>
      ?size pos. inst.inst_operands = [Lit size] /\
        FLOOKUP layout.cl_positions (Allocation inst.inst_id) = SOME pos /\
        pos + w2n size <= layout.cl_eom)
Proof
  rpt strip_tac >>
  qpat_x_assum `concretize_function_eval reserved fn = SOME fn'` mp_tac >>
  simp[concretize_function_eval_def, fn_has_static_layout_def] >>
  Cases_on `compute_function_layout_eval reserved fn` >> gvs[] >>
  strip_tac >>
  metis_tac[compute_function_layout_eval_wf,
            compute_function_layout_eval_global_bound,
            concretize_layout_wf_local_bound]
QED

Theorem concretize_context_eval_complete:
  concretize_context_eval ctx = SOME ctx' ==>
  ctx'.ctx_global_reserved = ctx.ctx_global_reserved /\
  LIST_REL
    (\fn fn'. ~fn_has_alloca fn' /\
      fn'.fn_forced_alloc_positions = FEMPTY /\
      IS_SOME fn'.fn_eom /\
      fn_identity_metadata_eq fn' fn /\
      fn_fmp_convention_eq fn' fn)
    ctx.ctx_functions ctx'.ctx_functions
Proof
  simp[concretize_context_eval_def] >>
  Cases_on `OPT_MMAP
    (concretize_function_eval ctx.ctx_global_reserved) ctx.ctx_functions` >>
  gvs[] >> strip_tac >> gvs[] >>
  drule OPT_MMAP_success_LIST_REL >> strip_tac >>
  drule LIST_REL_mono_imp >>
  disch_then irule >>
  rpt strip_tac >>
  metis_tac[concretize_function_eval_success]
QED

Theorem concretize_context_fuel_complete:
  concretize_context_fuel fuel ctx = SOME ctx' ==>
  ctx'.ctx_global_reserved = ctx.ctx_global_reserved /\
  LIST_REL
    (\fn fn'. ~fn_has_alloca fn' /\
      fn'.fn_forced_alloc_positions = FEMPTY /\
      IS_SOME fn'.fn_eom /\
      fn_identity_metadata_eq fn' fn /\
      fn_fmp_convention_eq fn' fn)
    ctx.ctx_functions ctx'.ctx_functions
Proof
  simp[concretize_context_fuel_def] >>
  Cases_on `OPT_MMAP
    (concretize_function_fuel fuel ctx.ctx_global_reserved)
    ctx.ctx_functions` >>
  gvs[] >> strip_tac >> gvs[] >>
  drule OPT_MMAP_success_LIST_REL >> strip_tac >>
  drule LIST_REL_mono_imp >>
  disch_then irule >>
  rpt strip_tac >>
  metis_tac[concretize_function_fuel_success]
QED

Theorem concretize_context_eval_wf:
  raw_static_inputs_wf ctx /\
  concretize_context_eval ctx = SOME ctx' ==>
  concretized_static_layouts_wf ctx'
Proof
  strip_tac >>
  drule concretize_context_eval_complete >> strip_tac >>
  fs[raw_static_inputs_wf_def, concretized_static_layouts_wf_def] >>
  rpt strip_tac >>
  `?fn0. MEM fn0 ctx.ctx_functions /\
          ~fn_has_alloca fn /\
          fn.fn_forced_alloc_positions = FEMPTY /\
          IS_SOME fn.fn_eom /\
          fn_identity_metadata_eq fn fn0 /\
          fn_fmp_convention_eq fn fn0` by
    (drule LIST_REL_MEM_right >> disch_then drule >> strip_tac >>
     qexists `x` >> gvs[]) >>
  simp[] >>
  fs[fn_has_alloca_def, EXISTS_MEM, is_alloca_op_eq_alloca] >>
  metis_tac[]
QED

Theorem concretize_context_fuel_wf:
  raw_static_inputs_wf ctx /\
  concretize_context_fuel fuel ctx = SOME ctx' ==>
  concretized_static_layouts_wf ctx'
Proof
  strip_tac >>
  drule concretize_context_fuel_complete >> strip_tac >>
  fs[raw_static_inputs_wf_def, concretized_static_layouts_wf_def] >>
  rpt strip_tac >>
  `?fn0. MEM fn0 ctx.ctx_functions /\
          ~fn_has_alloca fn /\
          fn.fn_forced_alloc_positions = FEMPTY /\
          IS_SOME fn.fn_eom /\
          fn_identity_metadata_eq fn fn0 /\
          fn_fmp_convention_eq fn fn0` by
    (drule LIST_REL_MEM_right >> disch_then drule >> strip_tac >>
     qexists `x` >> gvs[]) >>
  simp[] >>
  fs[fn_has_alloca_def, EXISTS_MEM, is_alloca_op_eq_alloca] >>
  metis_tac[]
QED
Theorem concretize_get_invoke_targets_append[local]:
  get_invoke_targets (xs ++ ys) =
  get_invoke_targets xs ++ get_invoke_targets ys
Proof
  Induct_on `xs`
  >- simp[get_invoke_targets_def]
  >> gen_tac >> Cases_on `h.inst_opcode = INVOKE`
  >- (Cases_on `h.inst_operands`
      >- simp[get_invoke_targets_def]
      >> Cases_on `h'` >> simp[get_invoke_targets_def])
  >> simp[get_invoke_targets_def]
QED

Theorem concretize_get_invoke_targets_cons[local]:
  get_invoke_targets (inst::insts) =
  get_invoke_targets [inst] ++ get_invoke_targets insts
Proof
  Cases_on `inst.inst_opcode = INVOKE`
  >- (Cases_on `inst.inst_operands`
      >- simp[get_invoke_targets_def]
      >> Cases_on `h` >> simp[get_invoke_targets_def])
  >> simp[get_invoke_targets_def]
QED

Theorem concretize_inst_with_positions_invoke_targets[local]:
  get_invoke_targets [concretize_inst_with_positions positions inst] =
  get_invoke_targets [inst]
Proof
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (Cases_on `inst.inst_outputs`
      >- simp[concretize_inst_with_positions_def, get_invoke_targets_def]
      >> Cases_on `t`
      >- (Cases_on `FLOOKUP positions (Allocation inst.inst_id)` >>
          simp[concretize_inst_with_positions_def, get_invoke_targets_def,
               mk_assign_inst_def, mk_nop_inst_def])
      >> simp[concretize_inst_with_positions_def, get_invoke_targets_def])
  >> simp[concretize_inst_with_positions_def]
QED

Theorem concretize_insts_with_positions_invoke_targets[local]:
  get_invoke_targets (MAP (concretize_inst_with_positions positions) insts) =
  get_invoke_targets insts
Proof
  Induct_on `insts`
  >- simp[get_invoke_targets_def]
  >> gen_tac >> Cases_on `h.inst_opcode = ALLOCA`
  >- (Cases_on `h.inst_outputs`
      >- simp[concretize_inst_with_positions_def, get_invoke_targets_def]
      >> Cases_on `t`
      >- (Cases_on `FLOOKUP positions (Allocation h.inst_id)` >>
          simp[concretize_inst_with_positions_def, get_invoke_targets_def,
               mk_assign_inst_def, mk_nop_inst_def])
      >> simp[concretize_inst_with_positions_def, get_invoke_targets_def])
  >> simp[concretize_inst_with_positions_def, get_invoke_targets_def]
QED

Theorem concretize_filter_nops_invoke_targets[local]:
  get_invoke_targets (FILTER (\inst. inst.inst_opcode <> NOP) insts) =
  get_invoke_targets insts
Proof
  Induct_on `insts`
  >- simp[get_invoke_targets_def]
  >> gen_tac >> Cases_on `h.inst_opcode = NOP`
  >- gvs[get_invoke_targets_def]
  >> simp[get_invoke_targets_def]
QED

Theorem concretize_mapped_blocks_invoke_targets[local]:
  get_invoke_targets
    (fn_insts_blocks
      (MAP (block_map_transform
        (concretize_inst_with_positions positions)) blocks)) =
  get_invoke_targets (fn_insts_blocks blocks)
Proof
  Induct_on `blocks`
  >- simp[fn_insts_blocks_def, get_invoke_targets_def]
  >> simp[fn_insts_blocks_def, block_map_transform_def,
          concretize_get_invoke_targets_append,
          concretize_insts_with_positions_invoke_targets]
QED

Theorem concretize_clear_nops_blocks_invoke_targets[local]:
  get_invoke_targets (fn_insts_blocks (MAP clear_nops_block blocks)) =
  get_invoke_targets (fn_insts_blocks blocks)
Proof
  Induct_on `blocks`
  >- simp[fn_insts_blocks_def, get_invoke_targets_def]
  >> simp[fn_insts_blocks_def, clear_nops_block_def,
          concretize_get_invoke_targets_append,
          concretize_filter_nops_invoke_targets]
QED

Theorem concretize_clear_nops_invoke_targets[local]:
  get_invoke_targets (fn_insts (clear_nops_function fn)) =
  get_invoke_targets (fn_insts fn)
Proof
  simp[clear_nops_function_def, fn_insts_def,
       concretize_clear_nops_blocks_invoke_targets]
QED

Theorem concretize_function_with_positions_invoke_targets[local]:
  MAP FST (fcg_scan_function
    (concretize_function_with_positions positions fn)) =
  MAP FST (fcg_scan_function fn)
Proof
  rewrite_tac[concretize_function_with_positions_def,
              fcg_scan_function_def] >>
  rewrite_tac[concretize_clear_nops_invoke_targets] >>
  simp[function_map_transform_def, fn_insts_def,
       concretize_mapped_blocks_invoke_targets]
QED

Theorem concretize_function_eval_invoke_targets:
  concretize_function_eval reserved fn = SOME fn' ==>
  MAP FST (fcg_scan_function fn') = MAP FST (fcg_scan_function fn)
Proof
  simp[concretize_function_eval_def, apply_concretize_layout_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  simp[fcg_scan_function_def, fn_insts_def] >>
  rewrite_tac[GSYM fn_insts_def, GSYM fcg_scan_function_def] >>
  simp[concretize_function_with_positions_invoke_targets]
QED

val _ = export_theory();
