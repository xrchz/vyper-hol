(*
 * Vyper-to-Venom Compilation (Top-Level Definition)
 *
 * Upstream: vyperlang/vyper@a7f7bf133 (split algebraic/affine passes)
 *
 * Wraps the compilation monad into a pure function:
 *   vyper_module -> venom_context option
 *
 * The compilation monad (compileEnv) builds up a compile_state
 * containing emitted blocks. This file defines:
 *   - initial_compile_state: starting state for the monad
 *   - extract_context: compile_state -> venom_context
 *   - run_lowering: run the monad, extract context
 *
 * TOP-LEVEL:
 *   run_lowering -- run compilation monad, produce venom_context
 *)

Theory vyperCompiler
Ancestors
  moduleLowering
  compileEnv
  venomInst
  venomCompilerTypes
  venomWf

(* ===== Compile State Initialization ===== *)

(* Initial compile state: all counters at 0, no blocks, entry block label. *)
Definition initial_compile_state_def:
  initial_compile_state (entry_label : string) : compile_state =
    <| cs_next_var := 0;
       cs_next_label := 0;
       cs_next_id := 0;
       cs_current_bb := entry_label;
       cs_current_insts := [];
       cs_blocks := [];
       cs_data_sections := []
    |>
End

(* ===== Context Extraction ===== *)

(* Extract a venom_context from the final compile state.
   Collects all finalized blocks plus the current (open) block
   into a single function. The entry function is the one whose
   entry block matches the initial current_bb. Finalized blocks are
   stored newest-first in the compile state. *)
Definition extract_context_def:
  extract_context (entry_label : string) (st : compile_state)
      : venom_context # data_section list =
    let current_bb = <| bb_label := st.cs_current_bb;
                        bb_instructions := st.cs_current_insts |> in
    let finalized = REVERSE st.cs_blocks in
    let all_blocks = finalized ++ [current_bb] in
    (mk_venom_context
       [mk_raw_function entry_label all_blocks]
       (SOME entry_label),
     REVERSE st.cs_data_sections)
End

(* Split at the first block carrying a certified internal-function entry label.
   The suffix retains the delimiter block. *)
Definition split_blocks_at_def:
  split_blocks_at (label : string) ([] : basic_block list) = NONE /\
  split_blocks_at label (bb :: rest) =
    if bb.bb_label = label then SOME ([], bb :: rest)
    else
      case split_blocks_at label rest of
        NONE => NONE
      | SOME (prefix, suffix) => SOME (bb :: prefix, suffix)
End

Theorem split_blocks_at_append_delimiter:
  ~MEM label (MAP (\b. b.bb_label) prefix) /\ bb.bb_label = label ==>
  split_blocks_at label (prefix ++ bb :: suffix) =
    SOME (prefix, bb :: suffix)
Proof
  Induct_on `prefix` >> simp[split_blocks_at_def]
QED

(* Raw internal functions receive only metadata certified by source lowering.
   Static-layout and FMP metadata deliberately retain mk_raw_function defaults. *)
Definition mk_internal_function_def:
  mk_internal_function name blocks has_ret_buf user_return_count =
    (mk_raw_function name blocks) with
      fn_call_abi :=
        <| ica_has_memory_return_buffer := SOME has_ret_buf;
           ica_user_return_count := SOME user_return_count |>
End

(* Partition the finalized block stream at ordered certified entry labels.
   The first component is the entry/external prefix; each remaining segment is
   packaged as one internal function. Missing or out-of-order labels fail. *)
Definition package_internal_blocks_def:
  package_internal_blocks
    ([] : (string # bool # num) list) (blocks : basic_block list) =
      SOME (blocks, []) /\
  package_internal_blocks ((name, has_ret_buf, rc) :: rest) blocks =
    case split_blocks_at name blocks of
      NONE => NONE
    | SOME (prefix, suffix) =>
        case package_internal_blocks rest suffix of
          NONE => NONE
        | SOME (fn_blocks, functions) =>
            SOME (prefix,
                  mk_internal_function name fn_blocks has_ret_buf rc :: functions)
End

Theorem mk_internal_function_metadata:
  !name blocks has_ret_buf rc.
    (mk_internal_function name blocks has_ret_buf rc).fn_name = name /\
    (mk_internal_function name blocks has_ret_buf rc).fn_blocks = blocks /\
    (mk_internal_function name blocks has_ret_buf rc).fn_call_abi =
      <| ica_has_memory_return_buffer := SOME has_ret_buf;
         ica_user_return_count := SOME rc |> /\
    ~(mk_internal_function name blocks has_ret_buf rc).fn_noinline /\
    (mk_internal_function name blocks has_ret_buf rc).fn_eom = NONE /\
    (mk_internal_function name blocks has_ret_buf rc).fn_fmp_signature = NONE
Proof
  simp[mk_internal_function_def, mk_raw_function_def]
QED


(* Project the certified packaging facts from compile_internal_fn_bodies inputs. *)
Definition internal_fn_descriptors_def:
  internal_fn_descriptors [] = [] /\
  internal_fn_descriptors
    ((name, cenv, params, has_ret_buf, is_nr, nkey, use_trans, is_view,
      is_ctor, imm_len, body, ret_type) :: rest) =
    (name, has_ret_buf, cenv.ce_returns_count) ::
      internal_fn_descriptors rest
End

Definition extract_context_with_internals_def:
  extract_context_with_internals entry_label internal_fns (st : compile_state) =
    let current_bb = <| bb_label := st.cs_current_bb;
                        bb_instructions := st.cs_current_insts |> in
    let all_blocks = REVERSE st.cs_blocks ++ [current_bb] in
    case package_internal_blocks (internal_fn_descriptors internal_fns) all_blocks of
      NONE => NONE
    | SOME (entry_blocks, functions) =>
        SOME
          (mk_venom_context
             (mk_raw_function entry_label entry_blocks :: functions)
             (SOME entry_label),
           REVERSE st.cs_data_sections)
End

(* A captured forced key is admissible only in the function that contains the
   corresponding ALLOCA instruction. *)
Definition forced_alloc_key_in_function_def:
  forced_alloc_key_in_function fn id <=>
    ?inst. MEM inst (fn_insts fn) /\
           inst.inst_id = id /\ inst.inst_opcode = ALLOCA
End

Definition forced_pairs_for_name_def:
  forced_pairs_for_name name metadata =
    MAP (\(_, id, pos). (id, pos))
      (FILTER (\(owner, _, _). owner = name) metadata)
End

Definition forced_metadata_ok_def:
  forced_metadata_ok functions metadata <=>
    ALL_DISTINCT (MAP (\fn. fn.fn_name) functions) /\
    ALL_DISTINCT (MAP (\(_, id, _). id) metadata) /\
    EVERY
      (\(owner, id, _).
         MEM owner (MAP (\fn. fn.fn_name) functions) /\
         EVERY
           (\fn. fn.fn_name = owner ==>
                 forced_alloc_key_in_function fn id)
           functions)
      metadata
End

(* Checked attachment rejects absent/duplicate owners and duplicate or
   non-ALLOCA keys before changing any function. *)
Definition attach_forced_metadata_def:
  attach_forced_metadata metadata functions =
    if forced_metadata_ok functions metadata then
      SOME
        (MAP
          (\fn. fn with fn_forced_alloc_positions :=
                    FUPDATE_LIST FEMPTY
                      (forced_pairs_for_name fn.fn_name metadata))
          functions)
    else NONE
End

Definition extract_context_with_forced_internals_def:
  extract_context_with_forced_internals entry_label internal_fns metadata
                                                (st : compile_state) =
    let current_bb = <| bb_label := st.cs_current_bb;
                        bb_instructions := st.cs_current_insts |> in
    let all_blocks = REVERSE st.cs_blocks ++ [current_bb] in
    case package_internal_blocks (internal_fn_descriptors internal_fns) all_blocks of
      NONE => NONE
    | SOME (entry_blocks, internal_functions) =>
        case attach_forced_metadata metadata
               (mk_raw_function entry_label entry_blocks :: internal_functions) of
          NONE => NONE

        | SOME functions =>
            SOME
              (mk_venom_context functions (SOME entry_label),
               REVERSE st.cs_data_sections)
End

Definition function_forced_metadata_ok_def:
  function_forced_metadata_ok fn <=>
    FEVERY (\(id, _). forced_alloc_key_in_function fn id)
      fn.fn_forced_alloc_positions
End

(* This check sits inside the `lowering_context_ok` guard on the main lowering
   path, so `computeLib` must be able to decide it or evaluation of the whole
   compiler stops at the `if`.  `finite_mapLib.add_finite_map_compset` supplies
   FLOOKUP/FUNION/FDOM/FUPDATE_LIST equations but no FEVERY equations at all --
   HOL keeps those in a separate compset (`FEVERY_cs`) reachable only through
   `fevery_EXPAND_CONV`, which EVAL never calls.  Register them persistently so
   every descendant theory inherits them, rather than patching each call site:
   the SML fixture libraries are not the only consumers, and EVAL_TAC in proofs
   resolves against the global compset that those libraries never touch.

   The chain terminates by peeling one FUPDATE per step:
     FEVERY P (f |+ (x,y))                       -> P (x,y) /\ FEVERY P (DRESTRICT f (COMPL {x}))
     FEVERY P (DRESTRICT (f |+ (k,v)) (COMPL s)) -> (~(k IN s) ==> P (k,v)) /\ ...
     FEVERY P (DRESTRICT FEMPTY (COMPL s))       -> FEVERY P FEMPTY -> T
   FUPDATE_LIST_THM is already in the compset, so maps built with FUPDATE_LIST
   reach that shape without needing FEVERY_FUPDATE_LIST (which is conditional on
   ALL_DISTINCT and so is not a plain compset rewrite). *)
val _ = computeLib.add_persistent_funs [
  "finite_map.FEVERY_FEMPTY",
  "finite_map.FEVERY_FUPDATE",
  "finite_map.DRESTRICT_FEMPTY",
  "finite_map.FEVERY_DRESTRICT_COMPL",
  "pred_set.IN_INSERT",
  "pred_set.NOT_IN_EMPTY"
]


Theorem forced_pairs_for_name_all_distinct:
  !metadata name.
    ALL_DISTINCT (MAP (\(_, id, _). id) metadata) ==>
    ALL_DISTINCT (MAP FST (forced_pairs_for_name name metadata))
Proof
  Induct_on `metadata` >- simp[forced_pairs_for_name_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[forced_pairs_for_name_def] >> strip_tac >>
  Cases_on `h0 = name`
  >- (gvs[] >> first_x_assum (qspec_then `h0` assume_tac) >>
      gvs[forced_pairs_for_name_def, listTheory.MEM_MAP,
          listTheory.MEM_FILTER, pairTheory.EXISTS_PROD]) >>
  gvs[] >> first_x_assum (qspec_then `name` assume_tac) >>
  gvs[forced_pairs_for_name_def]
QED
Theorem attach_forced_metadata_integrity:
  !metadata functions functions'.
    attach_forced_metadata metadata functions = SOME functions' ==>
    EVERY function_forced_metadata_ok functions'
Proof
  simp[attach_forced_metadata_def, forced_metadata_ok_def, AllCaseEqs()] >>
  rpt strip_tac >>
  simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  simp[function_forced_metadata_ok_def, forced_alloc_key_in_function_def,
       fn_insts_def] >>
  `ALL_DISTINCT
     (MAP FST (forced_pairs_for_name fn.fn_name metadata))` by
    metis_tac[forced_pairs_for_name_all_distinct] >>
  simp[finite_mapTheory.FEVERY_FUPDATE_LIST] >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  gvs[forced_pairs_for_name_def, listTheory.MEM_MAP,
      listTheory.MEM_FILTER, pairTheory.EXISTS_PROD] >>
  fs[listTheory.EVERY_MEM] >>
  res_tac >>
  gvs[forced_alloc_key_in_function_def, fn_insts_def] >>
  simp[finite_mapTheory.FEVERY_FEMPTY]
QED

Theorem function_forced_metadata_ok_lookup:
  !fn id pos.
    function_forced_metadata_ok fn /\
    FLOOKUP fn.fn_forced_alloc_positions id = SOME pos ==>
    forced_alloc_key_in_function fn id
Proof
  simp[function_forced_metadata_ok_def] >>
  rpt strip_tac >>
  drule finite_mapTheory.FEVERY_FLOOKUP >>
  disch_then drule >> simp[]
QED

Definition function_raw_metadata_defaults_def:
  function_raw_metadata_defaults fn <=>
    fn.fn_eom = NONE /\ fn.fn_fmp_signature = NONE
End

Theorem attach_forced_metadata_preserves_raw_defaults:
  !metadata functions functions'.
    EVERY function_raw_metadata_defaults functions /\
    attach_forced_metadata metadata functions = SOME functions' ==>
    EVERY function_raw_metadata_defaults functions'
Proof
  simp[attach_forced_metadata_def, AllCaseEqs(), listTheory.EVERY_MEM,
       function_raw_metadata_defaults_def] >>
  rpt strip_tac >>
  gvs[listTheory.MEM_MAP] >>
  first_x_assum drule >> simp[]
QED

Theorem package_internal_blocks_raw_defaults:
  !descriptors blocks entry_blocks functions.
    package_internal_blocks descriptors blocks = SOME (entry_blocks, functions) ==>
    EVERY function_raw_metadata_defaults functions
Proof
  Induct_on `descriptors` >- simp[package_internal_blocks_def] >>
  rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  gvs[package_internal_blocks_def, AllCaseEqs()] >>
  simp[function_raw_metadata_defaults_def, mk_internal_function_def,
       mk_raw_function_def] >>
  first_x_assum drule >> simp[]
QED

Theorem extract_context_with_forced_internals_metadata:
  !entry_label internal_fns metadata st ctx data.
    extract_context_with_forced_internals entry_label internal_fns metadata st =
      SOME (ctx, data) ==>
    EVERY function_forced_metadata_ok ctx.ctx_functions /\
    EVERY function_raw_metadata_defaults ctx.ctx_functions
Proof
  simp[extract_context_with_forced_internals_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[mk_venom_context_def]
  >- (drule attach_forced_metadata_integrity >> simp[])
  >>
  `EVERY function_raw_metadata_defaults
     (mk_raw_function entry_label entry_blocks :: internal_functions)` by
    (simp[function_raw_metadata_defaults_def, mk_raw_function_def] >>
     drule package_internal_blocks_raw_defaults >> simp[]) >>
  drule_all attach_forced_metadata_preserves_raw_defaults >> simp[]
QED
Definition invoke_target_ok_def:
  invoke_target_ok names inst <=>
    if inst.inst_opcode = INVOKE then
      case inst.inst_operands of
        Label label :: _ => MEM label names
      | _ => F
    else T
End

Theorem EVERY_fn_insts_blocks:
  !p blocks.
    EVERY p (fn_insts_blocks blocks) <=>
    EVERY (\bb. EVERY p bb.bb_instructions) blocks
Proof
  Induct_on `blocks` >>
  simp[fn_insts_blocks_def, listTheory.EVERY_APPEND]
QED

Definition wf_invoke_targets_check_def:
  wf_invoke_targets_check ctx <=>
    EVERY
      (\fn. EVERY
        (\bb. EVERY (invoke_target_ok (ctx_fn_names ctx)) bb.bb_instructions)
        fn.fn_blocks)
      ctx.ctx_functions
End

Definition forced_alloc_inputs_check_def:
  forced_alloc_inputs_check ctx <=>
    EVERY function_forced_metadata_ok ctx.ctx_functions
End

Definition lowering_context_ok_def:
  lowering_context_ok ctx <=>
    ALL_DISTINCT (ctx_fn_names ctx) /\
    wf_invoke_targets_check ctx /\
    ctx_inst_ids_distinct ctx /\
    forced_alloc_inputs_check ctx
End
(* ===== Policy Boundary ===== *)

Theorem wf_invoke_targets_check_eq:
  !ctx. wf_invoke_targets_check ctx <=> wf_invoke_targets ctx
Proof
  simp[wf_invoke_targets_check_def, GSYM EVERY_fn_insts_blocks,
       fn_insts_def, listTheory.EVERY_MEM,
       invoke_target_ok_def, wf_invoke_targets_def] >>
  gen_tac >> eq_tac
  >- (rpt strip_tac >>
      first_x_assum drule >> disch_then drule >> disch_then drule >>
      Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `h` >> gvs[])
  >> (rpt strip_tac >>
      first_x_assum (qspecl_then [`fn`, `e`] mp_tac) >>
      simp[] >> strip_tac >>
      Cases_on `e.inst_operands` >> gvs[])
QED

Theorem lowering_context_ok_integrity:
  !ctx. lowering_context_ok ctx ==>
        ctx_distinct_fn_names ctx /\ wf_invoke_targets ctx
Proof
  simp[lowering_context_ok_def, ctx_distinct_fn_names_def,
       wf_invoke_targets_check_eq]
QED

Theorem lowering_context_ok_static_integrity:
  !ctx. lowering_context_ok ctx ==>
        ctx_inst_ids_distinct ctx /\ forced_alloc_inputs_check ctx
Proof
  simp[lowering_context_ok_def]
QED

Definition internal_fn_matches_descriptor_def:
  internal_fn_matches_descriptor (name, has_ret_buf, rc) fn <=>
    fn.fn_name = name /\
    fn.fn_call_abi.ica_has_memory_return_buffer = SOME has_ret_buf /\
    fn.fn_call_abi.ica_user_return_count = SOME rc /\
    ~fn.fn_noinline /\ fn.fn_eom = NONE /\ fn.fn_fmp_signature = NONE
End

Theorem package_internal_blocks_metadata:
  !descriptors blocks entry_blocks functions.
    package_internal_blocks descriptors blocks = SOME (entry_blocks, functions) ==>
    LIST_REL internal_fn_matches_descriptor descriptors functions
Proof
  Induct_on `descriptors`
  >- simp[package_internal_blocks_def]
  >> rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  gvs[package_internal_blocks_def, AllCaseEqs()] >>
  simp[internal_fn_matches_descriptor_def, mk_internal_function_def,
       mk_raw_function_def] >>
  first_x_assum drule >> simp[]
QED

(* Raw source lowering implements the resolved O1 frontend contract.  Check the
   whole resolved shape rather than accepting a dispatch choice independently. *)
Definition lowering_policy_ok_def:
  lowering_policy_ok (rpolicy : resolved_compiler_policy) <=>
    target_capabilities_wf rpolicy.rpol_target /\
    rpolicy.rpol_target CapMcopy /\
    rpolicy.rpol_frontend_dispatch = Linear /\
    rpolicy.rpol_final_assembly = FAP_Optimize
End

(* ===== Pair-returning compatibility runners ===== *)

(* Legacy construction result.  New callers should use run_lowering, which
   keeps context and data atomic in a compilation_unit. *)
Definition run_lowering_pair_compat_def:
  run_lowering_pair_compat selectors external_fns internal_fns
               fallback_fn dispatch_strategy
               bucket_count fn_metadata_bytes
               dense_buckets
               (entry_info : num -> string # num # bool)
               (entry_label : string) =
    let st0 = initial_compile_state entry_label in
    let ((), st1) =
      compile_generate_runtime selectors external_fns internal_fns
        fallback_fn dispatch_strategy bucket_count fn_metadata_bytes
        dense_buckets entry_info st0
    in
    extract_context entry_label st1
End

(* Legacy deploy construction result. *)
Definition run_deploy_lowering_pair_compat_def:
  run_deploy_lowering_pair_compat has_constructor runtime_size immutables_len
                       constructor_args data_size
                       ctor_internal_fns
                       cenv body is_payable is_nonreentrant
                       nkey use_transient
                       (entry_label : string) =
    let st0 = initial_compile_state entry_label in
    let (forced_metadata, st1) =
      compile_generate_deploy has_constructor runtime_size immutables_len
        constructor_args data_size ctor_internal_fns
        cenv body is_payable is_nonreentrant nkey use_transient st0
    in
    extract_context entry_label st1
End

(* ===== Complete-unit raw lowering APIs ===== *)

Definition run_lowering_def:
  run_lowering selectors external_fns internal_fns fallback_fn
               (rpolicy : resolved_compiler_policy)
               bucket_count fn_metadata_bytes dense_buckets
               (entry_info : num -> string # num # bool)
               (entry_label : string) : compilation_unit option =
    if lowering_policy_ok rpolicy then
      let st0 = initial_compile_state entry_label in
      let ((), st1) =
        compile_generate_runtime selectors external_fns internal_fns
          fallback_fn rpolicy.rpol_frontend_dispatch
          bucket_count fn_metadata_bytes dense_buckets entry_info st0 in
      case extract_context_with_internals entry_label internal_fns st1 of
        NONE => NONE
      | SOME (ctx, data) =>
          if lowering_context_ok ctx then
            SOME <| cu_context := ctx; cu_data_segment := data |>
          else NONE
    else NONE
End


Definition install_immutable_reservation_def:
  install_immutable_reservation immutables_len ctx =
    ctx with ctx_global_reserved :=
      (if immutables_len = 0 then [] else [(0, immutables_len)])
End
(* Deploy lowering owns both the runtime size and runtime data installation. *)
Definition run_deploy_lowering_def:
  run_deploy_lowering has_constructor (rpolicy : resolved_compiler_policy)
                       (runtime_bytecode : byte list) immutables_len
                       constructor_args data_size ctor_internal_fns
                       cenv body is_payable is_nonreentrant
                       nkey use_transient
                       (entry_label : string) : compilation_unit option =
    if lowering_policy_ok rpolicy then
      let st0 = initial_compile_state entry_label in
      let (forced_metadata, st1) =
        compile_generate_deploy has_constructor (LENGTH runtime_bytecode)
          immutables_len constructor_args data_size ctor_internal_fns
          cenv body is_payable is_nonreentrant nkey use_transient st0 in
      case extract_context_with_forced_internals entry_label ctor_internal_fns
             forced_metadata st1 of
        NONE => NONE
      | SOME (ctx, data) =>
          let ctx' = install_immutable_reservation immutables_len ctx in
          if lowering_context_ok ctx' then
            SOME <| cu_context := ctx';
                    cu_data_segment :=
                      data ++
                      [<| ds_label := "runtime_begin";
                          ds_items := [DataBytes runtime_bytecode] |>] |>
          else NONE
    else NONE
End

Theorem run_deploy_lowering_global_reserved:
  run_deploy_lowering has_constructor rpolicy runtime_bytecode immutables_len
    constructor_args data_size ctor_internal_fns cenv stmts is_payable
    is_nonreentrant nkey use_transient entry_label = SOME u ==>
  u.cu_context.ctx_global_reserved =
    (if immutables_len = 0 then [] else [(0, immutables_len)])
Proof
  Cases_on `immutables_len = 0` >>
  simp[run_deploy_lowering_def, install_immutable_reservation_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem run_lowering_global_reserved:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info entry_label =
      SOME u ==>
  u.cu_context.ctx_global_reserved = []
Proof
  simp[run_lowering_def, extract_context_with_internals_def,
       mk_venom_context_def] >>
  pairarg_tac >> gvs[AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED


Theorem lookup_function_exists_for_name:
  !name functions.
    MEM name (MAP (\fn. fn.fn_name) functions) ==>
    ?fn. lookup_function name functions = SOME fn
Proof
  Induct_on `functions`
  >- simp[lookup_function_def, listTheory.FIND_thm]
  >> rpt strip_tac >> Cases_on `h.fn_name = name`
  >- (qexists `h` >> simp[lookup_function_def, listTheory.FIND_thm])
  >> gvs[] >> first_x_assum drule >> strip_tac >>
  qexists `fn` >> gvs[lookup_function_def, listTheory.FIND_thm]
QED

Theorem distinct_function_names_unique:
  !functions fn1 fn2 name.
    ALL_DISTINCT (MAP (\fn. fn.fn_name) functions) /\
    MEM fn1 functions /\ MEM fn2 functions /\
    fn1.fn_name = name /\ fn2.fn_name = name ==>
    fn1 = fn2
Proof
  Induct_on `functions`
  >- simp[]
  >> rpt strip_tac >>
  Cases_on `fn1 = h` >> Cases_on `fn2 = h` >>
  gvs[listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem lookup_function_result_name:
  !name functions fn.
    lookup_function name functions = SOME fn ==> fn.fn_name = name
Proof
  Induct_on `functions`
  >- simp[lookup_function_def, listTheory.FIND_thm]
  >> rpt strip_tac >> Cases_on `h.fn_name = name` >>
  gvs[lookup_function_def, listTheory.FIND_thm]
QED

Theorem invoke_target_resolves_uniquely:
  ctx_distinct_fn_names ctx /\ wf_invoke_targets ctx /\
  MEM caller ctx.ctx_functions /\ MEM inst (fn_insts caller) /\
  inst.inst_opcode = INVOKE ==>
  ?label rest callee.
    inst.inst_operands = Label label :: rest /\
    lookup_function label ctx.ctx_functions = SOME callee /\
    !fn. MEM fn ctx.ctx_functions /\ fn.fn_name = label ==> fn = callee
Proof
  rpt strip_tac >>
  qpat_x_assum `wf_invoke_targets ctx` mp_tac >>
  simp[wf_invoke_targets_def] >>
  disch_then (qspecl_then [`caller`, `inst`] mp_tac) >>
  simp[] >> strip_tac >>
  fs[ctx_fn_names_def] >>
  drule lookup_function_exists_for_name >> strip_tac >>
  qexists `fn` >> simp[] >>
  rpt strip_tac >>
  imp_res_tac lookup_function_MEM >>
  imp_res_tac lookup_function_result_name >>
  qspecl_then [`ctx.ctx_functions`, `fn'`, `fn`, `fn'.fn_name`] irule
    distinct_function_names_unique >>
  gvs[ctx_distinct_fn_names_def, ctx_fn_names_def] >>
  qexists `ctx` >> simp[]
QED

Theorem run_lowering_integrity:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info entry_label = SOME unit ==>
  ctx_distinct_fn_names unit.cu_context /\
  wf_invoke_targets unit.cu_context
Proof
  simp[run_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  metis_tac[lowering_context_ok_integrity]
QED

Theorem run_deploy_lowering_integrity:
  run_deploy_lowering has_constructor rpolicy runtime_bytecode immutables_len
    constructor_args data_size ctor_internal_fns cenv (ctor_stmts : stmt list) is_payable
    is_nonreentrant nkey use_transient entry_label = SOME unit ==>
  ctx_distinct_fn_names unit.cu_context /\
  wf_invoke_targets unit.cu_context
Proof
  simp[run_deploy_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  metis_tac[lowering_context_ok_integrity]
QED

Theorem run_lowering_static_integrity:
  run_lowering selectors external_fns internal_fns fallback_fn rpolicy
    bucket_count fn_metadata_bytes dense_buckets entry_info entry_label = SOME unit ==>
  ctx_inst_ids_distinct unit.cu_context /\
  forced_alloc_inputs_check unit.cu_context
Proof
  simp[run_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  metis_tac[lowering_context_ok_static_integrity]
QED

Theorem run_deploy_lowering_static_integrity:
  run_deploy_lowering has_constructor rpolicy runtime_bytecode immutables_len
    constructor_args data_size ctor_internal_fns cenv (ctor_stmts : stmt list) is_payable
    is_nonreentrant nkey use_transient entry_label = SOME unit ==>
  ctx_inst_ids_distinct unit.cu_context /\
  forced_alloc_inputs_check unit.cu_context
Proof
  simp[run_deploy_lowering_def] >> rpt strip_tac >>
  pairarg_tac >> gvs[AllCaseEqs()] >>
  metis_tac[lowering_context_ok_static_integrity]
QED
