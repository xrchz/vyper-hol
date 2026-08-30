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

(* ===== Policy Boundary ===== *)

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
    let ((), st1) =
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
      let (ctx, data) =
        run_lowering_pair_compat selectors external_fns internal_fns
          fallback_fn rpolicy.rpol_frontend_dispatch
          bucket_count fn_metadata_bytes dense_buckets entry_info entry_label
      in
        SOME <| cu_context := ctx; cu_data_segment := data |>
    else NONE
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
      let (ctx, data) =
        run_deploy_lowering_pair_compat has_constructor
          (LENGTH runtime_bytecode) immutables_len constructor_args data_size
          ctor_internal_fns cenv body is_payable is_nonreentrant
          nkey use_transient entry_label
      in
        SOME <| cu_context := ctx;
                cu_data_segment :=
                  data ++
                  [<| ds_label := "runtime_begin";
                      ds_items := [DataBytes runtime_bytecode] |>] |>
    else NONE
End
