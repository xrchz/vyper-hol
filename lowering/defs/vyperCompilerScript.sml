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

(* ===== Top-Level Compilation ===== *)

(* Run the compilation monad and extract a venom_context.
   This is the pure function composition:
     1. Initialize compile state
     2. Run compile_generate_runtime in the monad
     3. Extract the resulting context

   The arguments mirror compile_generate_runtime's parameters.
   A higher-level wrapper that extracts these from a vyper_module
   is left for future work (requires formalizing the module
   metadata extraction that Python does in VenomCompiler.__init__). *)
Definition run_lowering_def:
  run_lowering selectors external_fns internal_fns
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
    extract_context entry_label st1  (* returns (venom_context, data_section list) *)
End

(* Run the deploy compilation monad and extract a venom_context.
   Mirrors Python's generate_deploy_venom():
   - Constructor body (if present) with is_ctor_context=True
   - Internal fns reachable from constructor (is_ctor_context=True)
   - Deploy epilogue: codecopy runtime + return *)
Definition run_deploy_lowering_def:
  run_deploy_lowering has_constructor runtime_size immutables_len
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
