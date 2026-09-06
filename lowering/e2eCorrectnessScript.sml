(*
 * End-to-End Vyper-to-EVM Correctness
 *
 * TOP-LEVEL theorem: vyper_call_correct
 *   When EVM execution enters compiled Vyper bytecode (via CALL at
 *   any point in the call stack), the result corresponds to the
 *   Vyper source semantics (call_external).
 *
 * Internal proof structure (not visible in the top-level statement):
 *   1. vyper_to_venom_correct: call_external ~ run_context
 *   2. venom_pipeline_correct: run_context ~ run_context o pipeline
 *   3. codegen_correct: run_context ~ EVM run
 *
 * TOP-LEVEL:
 *   run_call                -- EVM execution of a single call frame
 *   call_state_rel          -- pre-call Vyper/EVM state correspondence
 *   vyper_call_correct      -- main correctness theorem
 *   compile_vyper_raw       -- full compilation chain (exploded args)
 *
 * Definitions (return_data_encodes, log_entry_corresponds,
 * state_effects_match, etc.) are in e2eDefsTheory.
 *
 * STATUS: E2E composition is scaffolding until lowering, the concrete Venom
 * pipeline instance, and codegen correctness are all closed with compatible
 * assumptions. See docs/compiler-proof-roadmap.md.
 *)

Theory e2eCorrectness
Ancestors
  e2eDefs
  vyperLoweringCorrect vfmExecution
  venomPipelineCorrect
  passSimulationDefs
  codegenCorrectness
  stateEquiv stateEquivProps
  venomExecSemantics
  vyperABI
  vyperInterpreter
  compileEnv compileVyper
  venomInst
  list

(* =====================================================================
   Call-Level Correctness (Main Theorem)
   ===================================================================== *)

(* ===== run_call: EVM execution of a single call frame ===== *)

(* Execute the current call frame until it completes.
   Keeps stepping while: execution hasn't aborted (ISL r) AND the
   context stack is at least as deep as when we started (our frame
   hasn't been popped yet).

   Returns SOME es' when the frame completes:
   - Normal case (depth > 1): our frame was popped by handle_exception,
     result incorporated into the caller's context. es' has the
     caller's context on top with returndata set, success flag pushed
     on stack, accounts updated or rolled back.
   - Outermost frame (depth = 1): handle_exception reraises, result
     is (INR exc_opt, es').
   - vfm_abort: hard abort, returns (INR exc_opt, es') with our
     frame still on the stack.
   Returns NONE only for non-termination (impossible with finite gas). *)
Definition run_call_def:
  run_call es =
    let depth = LENGTH es.contexts in
    OWHILE (λ(r, s). ISL r ∧ LENGTH s.contexts ≥ depth)
           (step o SND)
           (INL (), es)
End

(* ===== Pre-call state correspondence ===== *)

(* The EVM is starting a fresh call to compiled Vyper bytecode, and
   the runtime state corresponds to the Vyper abstract machine / tx.
   Covers: fresh call frame setup, account/storage correspondence,
   call parameters, block/chain context, type environment, and
   source deployment. *)
Definition call_state_rel_def:
  call_state_rel (program : toplevel list) bytecode am tx tenv
                 (ctxt : context) (rb : rollback_state)
                 (txp : transaction_parameters) ⇔
    (* Fresh call frame: bytecode loaded, pc=0, empty stack *)
    ctxt.msgParams.code = bytecode ∧
    ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode ∧
    ctxt.pc = 0 ∧
    ctxt.stack = [] ∧
    ctxt.logs = [] ∧
    ctxt.returnData = [] ∧
    ctxt.memory = [] ∧
    (* Accounts and transient storage match *)
    rb.accounts = am.accounts ∧
    rb.tStorage = am.tStorage ∧
    (* Call parameters match *)
    ctxt.msgParams.caller = tx.sender ∧
    ctxt.msgParams.callee = tx.target ∧
    ctxt.msgParams.value = tx.value ∧
    (* Block and chain context match *)
    txp.origin = tx.origin ∧
    txp.gasPrice = tx.gas_price ∧
    txp.baseFeePerGas = tx.base_fee ∧
    txp.blockNumber = tx.block_number ∧
    txp.blockTimeStamp = tx.time_stamp ∧
    txp.blockCoinBase = tx.coinbase ∧
    txp.blockGasLimit = tx.gas_limit ∧
    txp.chainId = tx.chain_id ∧
    txp.blobHashes = tx.blob_hashes ∧
    txp.baseFeePerBlobGas = tx.blob_base_fee ∧
    (* Type environment is derived from program *)
    tenv = type_env program ∧
    (* Source is deployed at target address *)
    (∃mods. ALOOKUP am.sources tx.target = SOME mods)
End

(* ===== Valid call ===== *)

(* The calldata encodes a valid call to an exported function of
   the Vyper program. Binds ret (return type) which is needed
   by the postcondition for ABI encoding of the return value. *)
Definition valid_vyper_call_def:
  valid_vyper_call am tx tenv calldata ret ⇔
    ∃mut nr args dflts body.
      lookup_exported_function
        (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
        tx.function_name = SOME (mut, nr, args, dflts, ret, body) ∧
      calldata_encodes tenv tx.function_name (MAP SND args) tx.args
        calldata
End

Definition compiled_event_info_def:
  compiled_event_info program =
    build_event_info (type_env program) program
      ((K NONE) : string -> (num # type list # bool list) option)
End

(* ===== Post-call result correspondence ===== *)

(* Relates the result of call_external to the EVM state after
   run_call completes. Takes both the starting state es and final
   state es_f, making preserved/changed fields explicit.

   Handles both outermost (r = INR exc_opt) and inner
   (r = INL (), frame popped) calls.

   Key uniformities across both cases:
   - Returndata: always in (FST (HD es_f.contexts)).returnData
     (callee's context for outermost; caller's after set_return_data
     for inner — handle_exception copies it before popping)
   - Accounts on success: es_f.rollback.accounts = am'.accounts
     (update_accounts modifies rollback; pop doesn't change it
     on success)
   - Accounts on revert: outermost leaves dirty accounts (caller
     handles rollback via r = INR (SOME Reverted)); inner has
     pop_and_incorporate_context restore pre-call rollback
   - Logs: callee's new EVM logs appended to the caller's pre-call
     logs. For outermost, pre-call logs are [] (callee's context
     started empty). For inner, they come from HD (TL es.contexts).
   - txParams: unchanged *)

(* Helper: the caller's logs before the call.
   Outermost (no caller): [].
   Inner: logs from the caller's context in the original state. *)
Definition caller_pre_logs_def:
  caller_pre_logs [] = ([] : event list) ∧
  caller_pre_logs (((ctxt : context), rb) :: _) = ctxt.logs
End

Definition call_result_matches_def:
  call_result_matches tenv event_info am tx ret r es es_f ⇔
    ∃ctxt_hd rb_hd accts tstor accs tdel md.
    (* es_f is es with contexts, rollback, msdomain updated.
       txParams preserved. Deeper contexts preserved. *)
    es_f = es with <|
      contexts := (ctxt_hd, rb_hd) :: TL (TL es.contexts);
      rollback := es.rollback with <|
        accounts := accts; tStorage := tstor;
        accesses := accs; toDelete := tdel
      |>;
      msdomain := md
    |> ∧
    case call_external am tx of
      (INL v, am') =>
        (* EVM indicates success *)
        (r = INR NONE ∨
         (r = INL () ∧
          ¬NULL ctxt_hd.stack ∧ HD ctxt_hd.stack = 1w)) ∧
        (* Returndata encodes the return value *)
        return_data_encodes tenv ret v es_f ∧
        (* Accounts and transient storage committed *)
        accts = am'.accounts ∧ tstor = am'.tStorage ∧
        (* Callee's new logs correspond to Vyper's logs *)
        (∃evm_logs.
           ctxt_hd.logs =
             caller_pre_logs (TL es.contexts) ++ evm_logs ∧
           logs_correspond event_info tenv tx.target
             am'.logs evm_logs)
    | (INR (AssertException _), _) =>
        (* Outermost: r signals revert, caller handles rollback.
           Inner: frame popped, caller sees 0w on stack,
           accounts rolled back by pop_and_incorporate_context. *)
        r = INR (SOME Reverted) ∨
        (r = INL () ∧
         ¬NULL ctxt_hd.stack ∧ HD ctxt_hd.stack = 0w ∧
         accts = am.accounts ∧ tstor = am.tStorage)
    | (INR (Error _), _) => T
    | (INR BreakException, _) => F
    | (INR ContinueException, _) => F
    | (INR (ReturnException _), _) => F
End

(* ===== Adapter Lemmas for vyper_call_correct ===== *)

(* Compilation + call_state_rel + valid_vyper_call together imply
   vyper_evm_correspondence.

   This bridges three gaps:
   1. compile_vyper → compile_vyper_raw (via compile_vyper_runtime_bytecode)
      with internally-computed selectors satisfying valid_function_call
   2. call_state_rel → initial_evm_rel (constructing Venom initial state
      from EVM context: accounts, storage, empty memory/logs/stack)
   3. Pipeline assumption: compile_vyper always uses a pipeline that
      satisfies ctx_pass_correct with observable_equiv

   Each gap is at the same level as the existing cheated Props theorems. *)
Theorem call_state_rel_initial_evm_rel[local]:
  !program bytecode am tx tenv ctxt rb rest es vs.
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel program bytecode am tx tenv ctxt rb es.txParams /\
    rb.accounts = vs.vs_accounts /\
    rb.tStorage = vs.vs_transient /\
    ctxt.returnData = vs.vs_returndata /\
    ctxt.logs = vs.vs_logs /\
    (!i. read_byte i vs.vs_memory = read_byte i ctxt.memory) /\
    ctxt.msgParams.data = vs.vs_call_ctx.cc_calldata
    ==>
    initial_evm_rel bytecode vs es
Proof
  rw[call_state_rel_def, initial_evm_rel_def] >> metis_tac[]
QED

Theorem valid_vyper_call_valid_function_call[local]:
  !am tx tenv selectors calldata args ret mut nr dflts body.
    lookup_exported_function
      (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
      tx.function_name = SOME (mut, nr, args, dflts, ret, body) /\
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args calldata /\
    (?sel fn_lbl htz.
       MEM (sel, fn_lbl, htz) selectors /\
       selector_matches sel tx.function_name
         (vyper_to_abi_types tenv (MAP SND args)))
    ==>
    valid_function_call tenv am tx selectors calldata args ret
Proof
  rw[valid_function_call_def] >> metis_tac[]
QED

Theorem compile_vyper_evm_correspondence[local]:
  !program pipeline dispatch_strategy deploy_bc runtime_bc
   am tx tenv ret ctxt rb rest es R_ok R_term.
    compile_vyper program pipeline dispatch_strategy
      = SOME (deploy_bc, runtime_bc) /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel program runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call am tx tenv ctxt.msgParams.data ret /\
    (!ctx vs. ctx_pass_correct pipeline R_ok R_term ctx vs) /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2)
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      vyper_evm_correspondence tenv (compiled_event_info program) ret am tx es
Proof
  cheat
QED

(* Bridge from vyper_evm_correspondence to run_call + call_result_matches.

   vyper_evm_correspondence is defined in terms of VFM's `run` which
   executes all frames to completion. call_result_matches uses `run_call`
   which stops when the current call frame completes.

   For outermost calls (LENGTH es.contexts = 1): run_call = run because
   step never empties the context stack (step_preserves_nonempty_contexts).
   For inner calls (LENGTH es.contexts > 1): run_call stops when
   handle_exception pops the callee frame; the postcondition includes
   the frame-popping effects (stack push, account rollback on revert).

   This encapsulates the EVM execution semantics reasoning about
   context stack management, handle_exception, and the OWHILE loop. *)
Theorem evm_correspondence_to_call_result[local]:
  !tenv event_info am tx ret es.
    vyper_evm_correspondence tenv event_info ret am tx es /\
    ~NULL es.contexts
    ==>
    ?r es_final.
      run_call es = SOME (r, es_final) /\
      call_result_matches tenv event_info am tx ret r es es_final
Proof
  cheat
QED

(* ===== Main Correctness Theorem ===== *)

(* Compiler correctness for a single external call.

   When EVM execution enters compiled Vyper bytecode (at any point
   in the call stack), the result corresponds to the Vyper source
   semantics (call_external am tx).

   Covers both outermost calls (rest = [], as in a transaction) and
   inner calls (rest ≠ [], as in a CALL from another contract).
   The pipeline and all Venom-internal details are hidden in the proof.

   Gas is existential: there exists a gas bound such that with enough
   gas, EVM execution produces the correct result. *)
Theorem vyper_call_correct:
  ∀program pipeline dispatch_strategy runtime_bc
   am tx tenv ret ctxt rb rest es R_ok R_term.
    (∃deploy_bc.
       compile_vyper program pipeline dispatch_strategy
         = SOME (deploy_bc, runtime_bc)) ∧
    es.contexts = (ctxt, rb) :: rest ∧
    call_state_rel program runtime_bc am tx tenv
      ctxt rb es.txParams ∧
    valid_vyper_call am tx tenv ctxt.msgParams.data ret ∧
    (!ctx vs. ctx_pass_correct pipeline R_ok R_term ctx vs) ∧
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) ∧
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2)
    ⇒
    ∃gas_needed.
      ctxt.msgParams.gasLimit ≥ gas_needed ⇒
      ∃r es_final.
        run_call es = SOME (r, es_final) ∧
        call_result_matches tenv (compiled_event_info program) am tx ret r es es_final
Proof
  rpt strip_tac
  (* Step 1: compile_vyper gives vyper_evm_correspondence with gas bound *)
  \\ drule_all compile_vyper_evm_correspondence
  \\ strip_tac
  \\ qexists `gas_needed`
  \\ strip_tac
  (* Step 2: Apply gas condition to get vyper_evm_correspondence *)
  \\ `vyper_evm_correspondence tenv (compiled_event_info program) ret am tx es` by
       metis_tac[]
  (* Step 3: Bridge to run_call + call_result_matches *)
  \\ drule evm_correspondence_to_call_result
  \\ simp[]
QED

(* ===================================================================== *)

(* ===== Full Compilation ===== *)

(* Full compilation: lowering + pass pipeline + codegen.
   Pipeline is a parameter -- instantiate for O2, O3, Os, etc. *)
Definition compile_vyper_raw_def:
  compile_vyper_raw selectors ext_fns int_fns fb_fn
                dispatch bucket_count fn_meta_bytes
                dense_buckets entry_info
                entry_label
                (pipeline : venom_context -> venom_context)
                fn_eom_map =
    let (ctx, data_seg) = run_lowering selectors ext_fns int_fns fb_fn
                            dispatch bucket_count fn_meta_bytes
                            dense_buckets entry_info entry_label in
    let ctx' = pipeline ctx in
    codegen ctx' fn_eom_map data_seg
End

(* ===== Component Theorems ===== *)

(* Pipeline preserves observable semantics.
   Given ctx_pass_correct with R_ok/R_term that each imply
   observable_equiv, every terminating execution of the original
   context has a fuel for the transformed context with
   observably equivalent results. *)
Theorem e2e_venom_pipeline:
  !(R_ok : venom_state -> venom_state -> bool) R_term ctx pipeline vs fuel.
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    ctx_pass_correct pipeline R_ok R_term ctx vs /\
    terminates (run_context fuel ctx vs)
    ==>
    ?fuel'. observable_result_equiv
              (run_context fuel ctx vs)
              (run_context fuel' (pipeline ctx) vs)
Proof
  simp[ctx_pass_correct_def, pass_correct_def] >>
  rpt strip_tac >>
  `?fuel'. terminates (run_context fuel' (pipeline ctx) vs)` by
    (gvs[] >> metis_tac[]) >>
  qexists_tac `fuel'` >>
  first_x_assum drule_all >> strip_tac >>
  `!r1 r2. lift_result R_ok R_term R_term r1 r2 ==>
           observable_result_equiv r1 r2` by
    (rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
     fs[lift_result_def, observable_result_equiv_def,
        observable_equiv_def, revert_equiv_def] >>
     metis_tac[]) >>
  metis_tac[]
QED

(* Codegen correctness: Venom execution corresponds to EVM execution.
   Wraps codegen_correct with initial_evm_rel. *)
Theorem e2e_venom_to_evm:
  !ctx fn_eom_map data_seg bytecode spill_hwm vs fuel.
    codegen_ready ctx /\
    ctx_wf ctx /\
    (!name efn. ctx.ctx_entry = SOME name /\
                lookup_function name ctx.ctx_functions = SOME efn ==>
                entry_fn_no_ret efn) /\
    codegen ctx fn_eom_map data_seg = SOME bytecode /\
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions /\
       step_inst fuel' ctx inst vs1 = OK vs2 ==>
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2)
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      (case run_context fuel ctx vs of
         Halt vs' =>
           ?es'. run es = SOME (INR NONE, es') /\
                 final_state_rel vs' es'
       | Abort Revert_abort vs' =>
           ?es'. run es = SOME (INR (SOME Reverted), es') /\
                 final_state_rel vs' es'
       | Abort ExHalt_abort vs' =>
           ?es' exc. run es = SOME (INR (SOME exc), es') /\
                     exc <> Reverted /\
                     final_state_rel vs' es'
       | OK _ => F
       | IntRet _ _ => F
       | Error _ => T)
Proof
  rpt strip_tac >>
  qsuff_tac `?gas_needed. !es.
    initial_ctx_rel ctx vs es /\
    (case es.contexts of
       [] => F
     | (ctxt,rb)::_ =>
       ctxt.msgParams.gasLimit >= gas_needed /\
       ctxt.msgParams.code = bytecode /\
       ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode) ==>
    (case run_context fuel ctx vs of
       OK _ => F
     | Halt vs' => ?es'. run es = SOME (INR NONE, es') /\ final_state_rel vs' es'
     | Abort Revert_abort vs' => ?es'. run es = SOME (INR (SOME Reverted), es') /\ final_state_rel vs' es'
     | Abort ExHalt_abort vs' => ?es' exc. run es = SOME (INR (SOME exc), es') /\ exc <> Reverted /\ final_state_rel vs' es'
     | IntRet _ _ => F
     | Error _ => T)`
  >- (strip_tac >> qexists `gas_needed` >> rpt strip_tac >>
      first_x_assum irule >>
      Cases_on `es.contexts` >> gvs[initial_evm_rel_def, initial_ctx_rel_def] >>
      PairCases_on `h` >> gvs[]) >>
  mp_tac (Q.SPECL [`fuel`, `ctx`, `fn_eom_map`, `data_seg`,
    `bytecode`, `spill_hwm`, `vs`] codegen_correct) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[]
QED

(* ===== Codegen Obligations ===== *)

(* Codegen success does not prove these source-context properties. They are
   explicit obligations supplied by lowering/pipeline correctness. *)
Definition codegen_context_obligations_def:
  codegen_context_obligations ctx spill_hwm ⇔
    codegen_ready ctx ∧
    ctx_wf ctx ∧
    (!name efn. ctx.ctx_entry = SOME name ∧
                lookup_function name ctx.ctx_functions = SOME efn ⇒
                entry_fn_no_ret efn) ∧
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx.ctx_functions ∧
       step_inst fuel' ctx inst vs1 = OK vs2 ⇒
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2)
End

Theorem compile_vyper_raw_well_formed:
  !selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    pipeline fn_eom_map bytecode spill_hwm.
  let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
  let ctx' = pipeline ctx in
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes
      dense_buckets entry_info entry_label
      pipeline fn_eom_map = SOME bytecode /\
    codegen_context_obligations ctx' spill_hwm
    ==>
    codegen_ready ctx' /\ ctx_wf ctx' /\
    (!name efn. ctx'.ctx_entry = SOME name /\
                lookup_function name ctx'.ctx_functions = SOME efn ==>
                entry_fn_no_ret efn) /\
    (!fn inst vs1 vs2 fuel'.
       MEM fn ctx'.ctx_functions /\
       step_inst fuel' ctx' inst vs1 = OK vs2 ==>
       step_mem_safe <| sa_fn_eom := 0;
                        sa_next_offset := spill_hwm;
                        sa_free_slots := [] |> vs1 vs2)
Proof
  rpt gen_tac
  \\ simp[pairTheory.UNCURRY, codegen_context_obligations_def]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ rw[]
QED

(* ===== Lowering State-to-Log Bridge ===== *)

(* Logs are part of source→Venom state_rel. This small bridge only adapts
   compileEnv's log relation to the e2e predicate shape. *)
Theorem external_call_state_rel_logs_correspond[local]:
  !tenv cenv cx am ss.
    cenv.ce_type_env = tenv /\
    external_call_state_rel cenv cx am ss ==>
    logs_correspond cenv.ce_event_info tenv cx.txn.target am.logs ss.vs_logs
Proof
  rw[external_call_state_rel_def, external_logs_rel_def, logs_correspond_def] >>
  irule LIST_REL_mono >>
  qexists_tac `log_entry_equiv cenv cx.txn.target` >>
  conj_tac >-
   (rpt gen_tac >>
    simp[log_entry_equiv_concrete_event, log_entry_corresponds_def]) >>
  simp[]
QED

(* Helper: expand let (x,y) = M in body  to  body[FST M/x, SND M/y] *)
fun expand_pair_let thm =
  thm |> SIMP_RULE bool_ss [LET_THM]
      |> CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV);

(* ===== Full E2E: Vyper to EVM ===== *)

(* Composes all three legs into a single theorem relating Vyper
   source semantics to EVM bytecode execution.
 *
 * Correspondence:
 *   Vyper success (INL v)       => EVM normal halt, returndata =
 *                                  ABI encoding of v, accounts,
 *                                  transient storage, and logs match
 *   Vyper revert (AssertExc)    => EVM REVERT, state_unchanged
 *   Vyper error                 => T (indicates source-level error;
 *                                  could be strengthened to F under
 *                                  well-formedness of am/tx)
 *   Break/Continue/Return       => F -- internal control flow,
 *                                  never escapes call_external
 *)

(* EVM REVERT preserves the call-boundary rollback state: committed accounts
   and transient storage in es.rollback are unchanged. Per-frame rollback
   snapshots are intentionally not compared here; CREATE/gas-accounting paths
   may update them internally without committing effects. *)
Theorem evm_revert_state_unchanged[local]:
  !es es'. run es = SOME (INR (SOME Reverted), es') /\
           ~NULL es.contexts
           ==>
           state_unchanged es es'
Proof
  cheat
QED

(* Main E2E theorem: Vyper source semantics ~ EVM execution.

   Gas: existential -- there exists a gas bound such that with enough
   gas, EVM execution always produces the correct result. Non-vacuous:
   the success case is always reachable. No OOG escape hatch needed.

   ctx_pass_correct is an assumption because the pipeline is
   parametric -- it holds for any pipeline assembled from
   semantics-preserving passes (e.g., the standard O2 pipeline).
   It is proved per-pipeline by composing individual pass proofs.
   The R_ok/R_term relations are the composed per-pass relations
   (via FOLDL rel_seq); the caller must show they imply
   observable_equiv (via foldl_rel_seq_preserves_observable).
   See e2e_vyper_to_evm_O2 for a concrete instance. *)
Theorem e2e_vyper_to_evm:
  !tenv event_info pipeline selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes dense_buckets entry_info
    entry_label fn_eom_map bytecode cenv spill_hwm
    (R_ok : venom_state -> venom_state -> bool) R_term
    am tx vs args ret.
  let (ctx, _) = run_lowering selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
    (* Compilation produces bytecode *)
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes
      dense_buckets entry_info entry_label
      pipeline fn_eom_map = SOME bytecode /\
    (* Source function exists, calldata valid, selector routes *)
    valid_function_call tenv am tx selectors
      vs.vs_call_ctx.cc_calldata args ret /\
    vs.vs_inst_idx = 0 /\
    cenv.ce_type_env = tenv /\
    event_info = cenv.ce_event_info /\
    codegen_context_obligations (pipeline ctx) spill_hwm /\
    (* Pipeline preserves observable semantics *)
    ctx_pass_correct pipeline R_ok R_term ctx vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2)
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      vyper_evm_correspondence tenv event_info ret am tx es
Proof
  rpt gen_tac
  \\ simp[pairTheory.UNCURRY]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ strip_tac
  \\ gvs[valid_function_call_def]
  (* Step 1: Apply lowering correctness *)
  \\ drule_all (expand_pair_let vyper_to_venom_correct)
  \\ disch_then (qspecl_then [`ext_fns`, `int_fns`, `fb_fn`,
       `dispatch`, `bucket_count`, `fn_meta_bytes`, `dense_buckets`,
       `entry_info`, `entry_label`, `cenv`] strip_assume_tac)
  (* Step 2: Use explicit codegen obligations *)
  \\ gvs[codegen_context_obligations_def]
  (* Abbreviate ctx for readability *)
  \\ qmatch_asmsub_abbrev_tac `ctx_pass_correct pipeline _ _ ctx vs`
  (* Extract codegen from compile_vyper_raw *)
  \\ `codegen (pipeline ctx) fn_eom_map
       (SND (run_lowering selectors ext_fns int_fns fb_fn dispatch bucket_count
              fn_meta_bytes dense_buckets entry_info entry_label))
     = SOME bytecode` by (
      gvs[compile_vyper_raw_def, pairTheory.UNCURRY, Abbr `ctx`] >>
      CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> gvs[])
  (* Step 3: Unfold correspondence, case split on Vyper result *)
  \\ simp[vyper_evm_correspondence_def]
  \\ Cases_on `call_external am tx`
  \\ rename1 `call_external am tx = (vyp_res, am')`
  \\ Cases_on `vyp_res` \\ gvs[external_call_result_rel_def]
  >- ((* INL: success case *)
   Cases_on `run_context fuel ctx vs`
   \\ gvs[external_call_result_rel_def]
   (* Now: Halt ss', with full source→Venom state relation. *)
   \\ `terminates (run_context fuel ctx vs)` by simp[terminates_def]
   \\ drule_all e2e_venom_pipeline \\ strip_tac
   \\ Cases_on `run_context fuel' (pipeline ctx) vs`
   \\ gvs[observable_result_equiv_def]
   (* Now: Halt ss2' with observable_equiv ss' ss2' *)
   \\ drule_all (SRULE [] e2e_venom_to_evm)
   \\ disch_then $ qspecl_then [`vs`, `fuel'`] strip_assume_tac
   \\ qexists `gas_needed` \\ rpt strip_tac
   \\ first_x_assum (qspec_then `es` mp_tac)
   \\ simp[pairTheory.UNCURRY]
   \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
   \\ gvs[] \\ strip_tac
   (* Now: run es = SOME (INR NONE, es'), final_state_rel ss2' es' *)
   \\ qexists `es'` \\ rpt conj_tac
   >- simp[]
   >- ((* return_data_encodes *)
     simp[return_data_encodes_def]
     \\ gvs[final_state_rel_def, observable_equiv_def]
     \\ Cases_on `es'.contexts` \\ gvs[]
     \\ PairCases_on `h` \\ gvs[]
     \\ qexists `abi_val` \\ simp[])
   \\ (* state_effects_match *)
   mp_tac (Q.SPECL [`cenv.ce_type_env`, `cenv`,
      `initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)`, `am'`, `v`]
      external_call_state_rel_logs_correspond)
   \\ simp[initial_evaluation_context_def] \\ strip_tac
   \\ simp[state_effects_match_def]
   \\ gvs[final_state_rel_def, observable_equiv_def, external_call_state_rel_def]
   \\ Cases_on `es'.contexts` \\ gvs[]
   \\ PairCases_on `h` \\ gvs[])
  (* INR: exception cases *)
  \\ rename1 `call_external am tx = (INR exc, am')`
  \\ Cases_on `exc` \\ gvs[external_call_result_rel_def]
  \\ TRY (Cases_on `run_context fuel ctx vs` >>
          gvs[external_call_result_rel_def] >> NO_TAC)
  (* AssertException => Revert *)
  \\ Cases_on `run_context fuel ctx vs`
  \\ gvs[external_call_result_rel_def]
  \\ Cases_on `a` \\ gvs[external_call_result_rel_def]
  \\ `terminates (run_context fuel ctx vs)` by simp[terminates_def]
  \\ drule_all e2e_venom_pipeline \\ strip_tac
  \\ Cases_on `run_context fuel' (pipeline ctx) vs`
  \\ gvs[observable_result_equiv_def]
  \\ drule_all (SRULE [] e2e_venom_to_evm)
  \\ disch_then $ qspecl_then [`vs`, `fuel'`] strip_assume_tac
  \\ qexists `gas_needed` \\ rpt strip_tac
  \\ first_x_assum (qspec_then `es` mp_tac)
  \\ simp[pairTheory.UNCURRY]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ gvs[] \\ strip_tac
  \\ qexists `es'` \\ conj_tac >- simp[]
  \\ irule evm_revert_state_unchanged \\ simp[]
QED

(* ===== Concrete Pipeline Instances ===== *)

(* The O2 pipeline preserves observable semantics.
   Combines individual O2 pass correctness theorems into
   a single ctx_pass_correct statement. Analysis functions
   (make_ssa, ircf, ricf, dse, amap, live_at) are parameters. *)
Theorem o2_pipeline_ctx_pass_correct[local]:
  !ircf_global ricf_global threshold
    make_ssa ircf ricf dse_analysis amap live_at ctx vs.
    ctx_pass_correct
      (venom_pipeline ircf_global ricf_global threshold
        (o2_fn_passes make_ssa ircf ricf dse_analysis amap live_at))
      observable_equiv observable_equiv ctx vs
Proof
  cheat
QED

Theorem e2e_vyper_to_evm_O2:
  !tenv event_info selectors ext_fns int_fns fb_fn
    dispatch bucket_count fn_meta_bytes dense_buckets entry_info
    entry_label
    ircf_global ricf_global threshold
    make_ssa ircf ricf dse_analysis amap live_at
    fn_eom_map bytecode cenv spill_hwm
    am tx vs args ret.
  let pipeline = venom_pipeline ircf_global ricf_global threshold
        (o2_fn_passes make_ssa ircf ricf dse_analysis amap live_at) in
    compile_vyper_raw selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes
      dense_buckets entry_info entry_label
      pipeline fn_eom_map = SOME bytecode /\
    valid_function_call tenv am tx selectors
      vs.vs_call_ctx.cc_calldata args ret /\
    vs.vs_inst_idx = 0 /\
    cenv.ce_type_env = tenv /\
    event_info = cenv.ce_event_info /\
    codegen_context_obligations (pipeline (FST (run_lowering selectors ext_fns int_fns fb_fn
      dispatch bucket_count fn_meta_bytes dense_buckets entry_info entry_label))) spill_hwm
    ==>
    ?gas_needed.
      !es. initial_evm_rel bytecode vs es /\
           ~NULL es.contexts /\
           (let (ctxt, rb) = HD es.contexts in
              ctxt.msgParams.gasLimit >= gas_needed)
      ==>
      vyper_evm_correspondence tenv event_info ret am tx es
Proof
  rpt gen_tac
  \\ simp[pairTheory.UNCURRY]
  \\ CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV)
  \\ strip_tac
  \\ qsuff_tac `?gas_needed. !es.
       initial_evm_rel bytecode vs es /\ ~NULL es.contexts /\
       (FST (HD es.contexts)).msgParams.gasLimit >= gas_needed ==>
       vyper_evm_correspondence tenv event_info ret am tx es`
  >- simp[]
  \\ drule (expand_pair_let e2e_vyper_to_evm |> SRULE [])
  \\ disch_then (qspecl_then [`cenv`, `spill_hwm`,
       `observable_equiv`, `observable_equiv`,
       `am`, `tx`, `vs`, `args`, `ret`] mp_tac)
  \\ simp[o2_pipeline_ctx_pass_correct]
QED

(* ===== Deploy Phase ===== *)

(* Deploy-phase correctness: the deploy bytecode, when executed on
   the EVM, correctly deploys the runtime bytecode.
   - Runs __init__ (if present)
   - CODECOPY's runtime bytecode to memory
   - RETURNs it
   The deployed code equals runtime_bc. *)
Theorem e2e_deploy_correctness:
  !tops pipeline dispatch_strategy deploy_bc runtime_bc.
    compile_vyper tops pipeline dispatch_strategy
      = SOME (deploy_bc, runtime_bc)
    ==>
    (* The deploy bytecode, when executed in creation context,
       runs __init__, then returns runtime_bc as deployed code. *)
    T (* TODO: state preconditions, EVM creation context relation *)
Proof
  simp[]
QED

(* ===== Two-Phase compile_vyper ===== *)

(* compile_vyper runtime phase produces the same bytecode as
   compile_vyper_raw with matching arguments. This connects
   the high-level two-phase API to the existing e2e correctness. *)
Theorem compile_vyper_runtime_bytecode:
  !tops pipeline dispatch_strategy deploy_bc runtime_bc.
    compile_vyper tops pipeline dispatch_strategy
      = SOME (deploy_bc, runtime_bc)
    ==>
    let tenv = type_env tops in
    let nkey_map = assign_nkeys tops 0 in
    let (ext_fns, int_fns, fb_fn, ctor_fn) = classify_functions tops in
    let selectors = build_selectors tenv ext_fns in
    let external_fns = MAP (package_external_fn tops F nkey_map) ext_fns in
    let runtime_int_fns = MAP (package_internal_fn tops F nkey_map F) int_fns in
    let fallback_fn = package_fallback_fn tops F nkey_map fb_fn in
      ?bucket_count fn_meta_bytes dense_buckets entry_info.
        compile_vyper_raw selectors external_fns runtime_int_fns fallback_fn
          dispatch_strategy bucket_count fn_meta_bytes
          dense_buckets entry_info "__entry" pipeline FEMPTY
          = SOME runtime_bc
Proof
  simp[compile_vyper_def, compile_vyper_raw_def, pairTheory.UNCURRY]
  \\ rpt strip_tac
  \\ rpt (pairarg_tac \\ gvs[])
  \\ gvs[AllCaseEqs()]
  \\ rpt (FIRST [pairarg_tac \\ gvs[AllCaseEqs()],
                CASE_TAC \\ gvs[AllCaseEqs()]])
  (* The hypothesis contains run_lowering with specific computed params.
     Extract them as witnesses for the existential. *)
  \\ qmatch_assum_abbrev_tac `codegen (pipeline (FST (run_lowering _ _ _ _ _ bc fmb db ei _))) _ _ = _`
  \\ MAP_EVERY qexists_tac [`bc`, `fmb`, `db`, `ei`]
  \\ gvs[]
QED
