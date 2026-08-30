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

(* Small executable probes for the packaging boundary. *)
Theorem package_internal_blocks_two_probe:
  package_internal_blocks [("f", T, 2n); ("g", F, 0n)]
    [<| bb_label := "entry"; bb_instructions := [] |>;
     <| bb_label := "f"; bb_instructions := [] |>;
     <| bb_label := "f.more"; bb_instructions := [] |>;
     <| bb_label := "g"; bb_instructions := [] |>] =
  SOME
    ([<| bb_label := "entry"; bb_instructions := [] |>],
     [mk_internal_function "f"
        [<| bb_label := "f"; bb_instructions := [] |>;
         <| bb_label := "f.more"; bb_instructions := [] |>] T 2;
      mk_internal_function "g"
        [<| bb_label := "g"; bb_instructions := [] |>] F 0])
Proof
  EVAL_TAC
QED

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

Definition invoke_target_ok_def:
  invoke_target_ok names inst <=>
    if inst.inst_opcode = INVOKE then
      case inst.inst_operands of
        Label label :: _ => MEM label names
      | _ => F
    else T
End

Definition wf_invoke_targets_check_def:
  wf_invoke_targets_check ctx <=>
    EVERY
      (\fn. EVERY (invoke_target_ok (ctx_fn_names ctx)) (fn_insts fn))
      ctx.ctx_functions
End

Definition lowering_context_ok_def:
  lowering_context_ok ctx <=>
    ALL_DISTINCT (ctx_fn_names ctx) /\ wf_invoke_targets_check ctx
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
      let ((), st1) =
        compile_generate_deploy has_constructor (LENGTH runtime_bytecode)
          immutables_len constructor_args data_size ctor_internal_fns
          cenv body is_payable is_nonreentrant nkey use_transient st0 in
      case extract_context_with_internals entry_label ctor_internal_fns st1 of
        NONE => NONE
      | SOME (ctx, data) =>
          if lowering_context_ok ctx then
            SOME <| cu_context := ctx;
                    cu_data_segment :=
                      data ++
                      [<| ds_label := "runtime_begin";
                          ds_items := [DataBytes runtime_bytecode] |>] |>
          else NONE
    else NONE
End
