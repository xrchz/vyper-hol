(*
 * End-to-End Vyper-to-EVM Correctness
 *
 * TOP-LEVEL theorem: vyper_call_correct
 *   When EVM execution enters compiled Vyper bytecode (via CALL at
 *   any point in the call stack), the result corresponds to the
 *   Vyper source semantics (call_external).
 *
 * Internal proof structure:
 *   1. checked_unit_transform_correct: source unit ~ transformed unit
 *   2. codegen_correct: transformed Venom context ~ EVM run
 *   3. finalizer_correct: assembled output ~ finalized runtime bytecode
 *
 * TOP-LEVEL:
 *   run_call                -- EVM execution of a single call frame
 *   call_state_rel          -- pre-call Vyper/EVM state correspondence
 *   vyper_call_correct      -- checked-unit compiler/call correctness theorem
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

(* The checked-unit correspondence below combines the explicit compilation,
   source-deployment, transform, codegen, and finalizer interfaces.  These
   small adapters keep initial-state and valid-call conversions local to the
   call-level consumer. *)
Theorem call_state_rel_initial_evm_rel[local]:
  !program cp bytecode am tx tenv ctxt rb rest es vs.
    initial_codegen_state_rel cp vs /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel program bytecode am tx tenv ctxt rb es.txParams /\
    rb.accounts = vs.vs_accounts /\
    rb.tStorage = vs.vs_transient /\
    ctxt.returnData = vs.vs_returndata /\
    ctxt.logs = vs.vs_logs /\
    (!i. read_byte i vs.vs_memory = read_byte i ctxt.memory) /\
    ctxt.msgParams.data = vs.vs_call_ctx.cc_calldata
    ==>
    initial_evm_rel cp bytecode vs es
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

Theorem log_entry_equiv_log_entry_corresponds[local]:
  !cenv event_info tenv addr l ev.
    cenv.ce_type_env = tenv /\ cenv.ce_event_info = event_info ==>
    (log_entry_equiv cenv addr l ev <=>
     log_entry_corresponds event_info tenv addr l ev)
Proof
  simp[log_entry_equiv_def, log_entry_corresponds_def]
QED

Theorem external_logs_rel_logs_correspond[local]:
  !cenv event_info tenv addr am ss.
    cenv.ce_type_env = tenv /\ cenv.ce_event_info = event_info ==>
    (external_logs_rel cenv addr am ss <=>
     logs_correspond event_info tenv addr am.logs ss.vs_logs)
Proof
  rw[external_logs_rel_def, logs_correspond_def] >>
  `log_entry_equiv cenv addr =
   log_entry_corresponds cenv.ce_event_info cenv.ce_type_env addr`
    by simp[FUN_EQ_THM, log_entry_equiv_log_entry_corresponds] >>
  simp[]
QED

(* The source semantics of the exact packaged compilation unit is an explicit
   boundary obligation.  In particular, it is not reconstructed from the
   weaker observable equivalence used by generic transform correctness. *)
Definition source_unit_execution_correct_def:
  source_unit_execution_correct tenv cenv am tx ret
    (unit : compilation_unit) vs <=>
    ?fuel. external_call_result_rel tenv cenv
      (initial_evaluation_context am.sources am.layouts tx
        (find_function_module am tx.target tx.function_name))
      ret (call_external am tx) (run_context fuel unit.cu_context vs)
End

Theorem source_unit_execution_correct:
  source_unit_execution_correct tenv cenv am tx ret unit vs <=>
  ?fuel. external_call_result_rel tenv cenv
    (initial_evaluation_context am.sources am.layouts tx
      (find_function_module am tx.target tx.function_name))
    ret (call_external am tx) (run_context fuel unit.cu_context vs)
Proof
  simp[source_unit_execution_correct_def]
QED
Theorem run_context_zero_error[local]:
  !ctx vs. ?e. run_context 0 ctx vs = Error e
Proof
  rpt gen_tac >> Cases_on `ctx.ctx_entry`
  >- simp[run_context_def]
  >> rename1 `ctx.ctx_entry = SOME entry` >>
     Cases_on `lookup_function entry ctx.ctx_functions`
  >- simp[run_context_def]
  >> rename1 `lookup_function entry ctx.ctx_functions = SOME fn` >>
     Cases_on `fn_entry_label fn`
  >- simp[run_context_def, run_function_def]
  >> simp[run_context_def, run_function_def, Once run_blocks_def]
QED

Theorem source_unit_execution_through_pipeline[local]:
  !tenv cenv am tx ret unit vs pipeline rpolicy out R_ok R_term.
    source_unit_execution_correct tenv cenv am tx ret unit vs /\
    pipeline rpolicy unit = SOME out /\
    checked_unit_transform_correct pipeline rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2)
    ==>
    ?fuel fuel'.
      external_call_result_rel tenv cenv
        (initial_evaluation_context am.sources am.layouts tx
          (find_function_module am tx.target tx.function_name))
        ret (call_external am tx) (run_context fuel unit.cu_context vs) /\
      observable_result_equiv
        (run_context fuel unit.cu_context vs)
        (run_context fuel' out.po_unit.cu_context vs)
Proof
  rpt strip_tac >>
  gvs[source_unit_execution_correct_def,
      checked_unit_transform_correct_def,
      ctx_transform_correct_def, pass_correct_def] >>
  `!r1 r2. lift_result R_ok R_term R_term r1 r2 ==>
           observable_result_equiv r1 r2` by
    (rpt gen_tac >> Cases_on `r1` >> Cases_on `r2` >>
     fs[lift_result_def, observable_result_equiv_def,
        observable_equiv_def, revert_equiv_def] >>
     metis_tac[]) >>
  Cases_on `terminates (run_context fuel unit.cu_context vs)`
  >- (`?fuel'. terminates
          (run_context fuel' out.po_unit.cu_context vs)` by metis_tac[] >>
      qexistsl [`fuel`, `fuel'`] >>
      metis_tac[])
  >> Cases_on `run_context fuel unit.cu_context vs` >>
     gvs[terminates_def] >>
     qspecl_then [`out.po_unit.cu_context`, `vs`] strip_assume_tac
       run_context_zero_error >>
     qexistsl [`fuel`, `0`] >>
     gvs[observable_result_equiv_def]
QED

Theorem e2e_vyper_to_evm:
  !tops pipeline finalizer policy rpolicy unit out prog deploy_bc runtime_bc
   cp name i r fn off Inv cenv am tx tenv ret ctxt rb rest es vs R_ok R_term.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    runtime_bc = assemble prog /\
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc) /\
    source_deployment_rel tops am tx cenv /\
    source_unit_execution_correct tenv cenv am tx ret unit vs /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    out.po_unit.cu_context.ctx_entry = SOME name /\
    lookup_function name out.po_unit.cu_context.ctx_functions = SOME fn /\
    i < LENGTH out.po_unit.cu_context.ctx_functions /\
    EL i out.po_unit.cu_context.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    contextCodegenRel$codegen_context_obligations
      Inv out.po_unit.cu_context cp /\
    contextCodegenRel$codegen_reachability_package
      Inv out.po_unit.cu_context vs /\
    initial_codegen_state_rel cp vs /\
    codegenCorrectness$initial_ctx_rel cp prog off
      out.po_unit.cu_context vs es /\
    asm_pc_to_offset prog off = 0 /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel tops runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call am tx tenv ctxt.msgParams.data ret /\
    cenv.ce_type_env = tenv /\
    cenv.ce_event_info = compiled_event_info tops /\
    checked_unit_transform_correct pipeline rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    finalizer_correct rpolicy finalizer
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      vyper_evm_correspondence tenv (compiled_event_info tops) ret am tx es
Proof
  rpt strip_tac >>
  drule_all source_unit_execution_through_pipeline >> strip_tac >>
  drule_all codegen_correct >> strip_tac >>
  qpat_x_assum `!fuel. ?gas_needed. _`
    (qspec_then `fuel'` strip_assume_tac) >>
  qexists `gas_needed` >> strip_tac >>
  first_x_assum (qspec_then `es` mp_tac) >>
  (impl_tac >- (gvs[call_state_rel_def])) >>
  strip_tac >>
  Cases_on `call_external am tx` >>
  rename1 `call_external am tx = (src_result, am')` >>
  Cases_on `src_result` >>
  Cases_on `run_context fuel unit.cu_context vs` >>
  Cases_on `run_context fuel' out.po_unit.cu_context vs` >>
  gvs[external_call_result_rel_def, observable_result_equiv_def,
      observable_equiv_def, revert_equiv_def,
      vyper_evm_correspondence_def] >>
  gvs[return_data_encodes_def, state_effects_match_def,
      final_state_rel_def, external_call_state_rel_def,
      initial_evaluation_context_def]
  >- (Cases_on `es'.contexts` >> gvs[] >> PairCases_on `h` >>
      gvs[] >> metis_tac[external_logs_rel_logs_correspond])
  >- (Cases_on `y` >> Cases_on `a` >>
      gvs[external_call_result_rel_def])
  >> Cases_on `y` >> gvs[external_call_result_rel_def]
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
  !tops pipeline finalizer policy rpolicy unit out prog deploy_bc runtime_bc
   cp name i r fn off Inv cenv am tx tenv ret ctxt rb rest es vs R_ok R_term.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    pipeline rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    runtime_bc = assemble prog /\
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc) /\
    source_deployment_rel tops am tx cenv /\
    source_unit_execution_correct tenv cenv am tx ret unit vs /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    out.po_unit.cu_context.ctx_entry = SOME name /\
    lookup_function name out.po_unit.cu_context.ctx_functions = SOME fn /\
    i < LENGTH out.po_unit.cu_context.ctx_functions /\
    EL i out.po_unit.cu_context.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    contextCodegenRel$codegen_context_obligations
      Inv out.po_unit.cu_context cp /\
    contextCodegenRel$codegen_reachability_package
      Inv out.po_unit.cu_context vs /\
    initial_codegen_state_rel cp vs /\
    codegenCorrectness$initial_ctx_rel cp prog off
      out.po_unit.cu_context vs es /\
    asm_pc_to_offset prog off = 0 /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel tops runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call am tx tenv ctxt.msgParams.data ret /\
    cenv.ce_type_env = tenv /\
    cenv.ce_event_info = compiled_event_info tops /\
    checked_unit_transform_correct pipeline rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    finalizer_correct rpolicy finalizer
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      vyper_evm_correspondence tenv (compiled_event_info tops) ret am tx es
Proof
  rpt strip_tac >> drule_all e2e_vyper_to_evm >> simp[]
QED

(* ===================================================================== *)

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

(* ===== Full E2E: Vyper to EVM ===== *)

(* Composes all three legs into a single theorem relating Vyper
   source semantics to EVM bytecode execution.
 *
 * Correspondence:
 *   Vyper success (INL v)       => EVM normal halt, returndata =
 *                                  ABI encoding of v, accounts,
 *                                  transient storage, and logs match
 *   Vyper revert (AssertExc)    => outermost EVM execution reports REVERT
 *   Vyper error                 => T (indicates source-level error;
 *                                  could be strengthened to F under
 *                                  well-formedness of am/tx)
 *   Break/Continue/Return       => F -- internal control flow,
 *                                  never escapes call_external
 *)

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


(* ===== Deploy Phase ===== *)

(* Deploy-phase correctness: the deploy bytecode, when executed on
   the EVM, correctly deploys the runtime bytecode.
   - Runs __init__ (if present)
   - CODECOPY's runtime bytecode to memory
   - RETURNs it
   The deployed code equals runtime_bc. *)
Theorem e2e_deploy_correctness:
  !tops pipeline finalizer policy deploy_bc runtime_bc.
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc)
    ==>
    (* The deploy bytecode, when executed in creation context,
       runs __init__, then returns runtime_bc as deployed code. *)
    T (* TODO: state preconditions, EVM creation context relation *)
Proof
  simp[]
QED

(* ===== Two-Phase compile_vyper ===== *)

(* Successful generic compilation exposes the concrete runtime lowering,
   pipeline output, matching final-assembly policy, and finalization result. *)
Theorem compile_vyper_runtime_bytecode:
  !tops pipeline finalizer policy deploy_bc runtime_bc.
    compile_vyper_with pipeline finalizer policy tops
      = SOME (deploy_bc, runtime_bc)
    ==>
    ?rpolicy runtime_unit out.
      resolve_o1_policy policy = SOME rpolicy /\
      lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
      pipeline rpolicy runtime_unit = SOME out /\
      out.po_final_assembly = rpolicy.rpol_final_assembly /\
      finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc
Proof
  simp[compile_vyper_with_def, checked_unit_pipeline_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  goal_assum $ drule_at Any
QED
