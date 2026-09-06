(*
 * End-to-End Definitions (Vyper-to-EVM Correspondence Predicates)
 *
 * Pure definitions used by the e2e correctness theorems.
 * No proof dependencies -- only definition-level ancestors.
 *
 * TOP-LEVEL:
 *   ctx_transform_correct -- semantic correctness for a context transform
 *   checked_unit_transform_correct -- successful atomic unit transform contract
 *   source_deployment_rel -- source target/module linkage
 *   finalizer_correct -- successful finalizer safety/preserve contract
 *   initial_codegen_state_rel -- context-plan initial FMP/token agreement
 *   return_data_encodes    -- Vyper return value ~ EVM returndata
 *   non_indexed_values     -- extract non-indexed event args
 *   non_indexed_types      -- extract non-indexed event arg types
 *   log_entry_corresponds  -- single Vyper log ~ EVM event
 *   logs_correspond        -- Vyper logs ~ EVM events (LIST_REL)
 *   state_effects_match    -- Vyper side effects ~ EVM post-state
 *   state_unchanged        -- rollback state unchanged (for reverts)
 *   vyper_evm_correspondence -- full Vyper-EVM case split
 *   initial_evm_rel        -- EVM state initialized with bytecode
 *   valid_function_call    -- source function callable with given args
 *)

Theory e2eDefs
Ancestors
  vfmExecution
  vyperABI
  vyperInterpreter
  compileEnv
  selectorDispatch
  codegenRel
  venomState
  passSimulationDefs
  assemblyFinalizer
  asmTargetSafety

(* ===== Generic Compiler Contracts ===== *)

(* A context transform is correct when executions from the same initial
   Venom state satisfy the generic pass-correctness contract. *)
Definition ctx_transform_correct_def:
  ctx_transform_correct R_ok R_term ctx ctx' s <=>
    pass_correct R_ok R_term R_term
      (\fuel. run_context fuel ctx s)
      (\fuel. run_context fuel ctx' s)
End

(* The pipeline boundary keeps each context and its associated data segment
   together in a compilation_unit.  Execution projects only the contexts. *)
Definition checked_unit_transform_correct_def:
  checked_unit_transform_correct
    (pipeline : resolved_compiler_policy -> compilation_unit ->
                pipeline_output option)
    rpolicy R_ok R_term (unit : compilation_unit) s <=>
    !out. pipeline rpolicy unit = SOME out ==>
      ctx_transform_correct R_ok R_term
        unit.cu_context out.po_unit.cu_context s
End

(* Every successful finalization is target-safe.  Preserve policy additionally
   requires exact identity of the assembly instruction list. *)
Definition finalizer_correct_def:
  finalizer_correct rpolicy (finalizer : assembly_finalizer) <=>
    !asm finalized_asm.
      finalizer rpolicy asm = SOME finalized_asm ==>
      assembly_target_safe rpolicy.rpol_target finalized_asm /\
      (rpolicy.rpol_final_assembly = FAP_Preserve ==>
       finalized_asm = asm)
End

(* The source target selects a module map, and the certified compile
   environment selects exactly the source top-level statements being run. *)
Definition source_deployment_rel_def:
  source_deployment_rel tops am tx cenv <=>
    ?mods. ALOOKUP am.sources tx.target = SOME mods /\
           ALOOKUP mods cenv.ce_module = SOME tops
End

(* Code generation starts from the FMP certified by the context plan, while
   the logical return continuation token is initially zero. *)
Definition initial_codegen_state_rel_def:
  initial_codegen_state_rel cp vs <=>
    vs.vs_fmp = n2w cp.cp_initial_fmp /\
    vs.vs_call_entry_fmp = n2w cp.cp_initial_fmp /\
    vs.vs_initial_fmp = n2w cp.cp_initial_fmp /\
    vs.vs_return_pc_token = 0w
End

(* ===== E2E Result Predicates ===== *)

(* EVM returndata equals ABI encoding of Vyper return value.
   Bridges Vyper values to EVM bytes via the ABI encoding scheme. *)
Definition return_data_encodes_def:
  return_data_encodes tenv ret_type v es' <=>
    ?abi_val ctxt rb rest.
      es'.contexts = (ctxt, rb) :: rest /\
      vyper_to_abi tenv ret_type v = SOME abi_val /\
      ctxt.returnData =
        enc (vyper_to_abi_type tenv ret_type) abi_val
End

(* ===== Log Correspondence ===== *)

(* Single log entry correspondence. Relates a Vyper log (nsid, values)
   to an EVM event, given:
   - event_info: maps event name to SOME (hash, arg_types, indexed_flags)
   - tenv: type environment for ABI encoding
   - addr: contract address (logger)

   EVM event structure:
   - ev.logger = contract address
   - ev.topics = event hash followed by indexed topics
   - ev.data = ABI-encode of non-indexed values as tuple

   Static indexed args are encoded as val_to_w256. Indexed bytes/string
   args are encoded as keccak256(raw bytes), matching compileEnv$logs_rel. *)
Definition log_entry_corresponds_def:
  log_entry_corresponds event_info tenv (addr : address)
    ((eid, vals) : log) (ev : event) <=>
    let event_name = nsid_to_string eid in
    case event_info event_name of
      NONE => F
    | SOME (event_hash, arg_types, indexed_flags) =>
        let idx_vals = indexed_values indexed_flags vals in
        let idx_bs = indexed_topic_flags indexed_flags (MAP is_bytestring_type arg_types) in
        let nidx_vals = log_non_indexed_values indexed_flags vals in
        let nidx_types = log_non_indexed_types indexed_flags arg_types in
          LENGTH indexed_flags = LENGTH vals /\
          LENGTH arg_types = LENGTH vals /\
          ev.logger = addr /\
          (?topic_tail.
             ev.topics = n2w event_hash :: topic_tail /\
             log_indexed_topics_equiv idx_bs idx_vals topic_tail) /\
          (?abi_vals.
             vyper_to_abi_list tenv nidx_types nidx_vals = SOME abi_vals /\
             ev.data = enc (Tuple (vyper_to_abi_types tenv nidx_types))
                           (ListV abi_vals))
End

(* Vyper logs correspond to EVM events (ordered, same-length).
   event_info maps event name -> SOME (hash, arg_types, indexed_flags)
   for declared events (from EventDecl with indexed flag). *)
Definition logs_correspond_def:
  logs_correspond event_info tenv (addr : address)
    (vyper_logs : log list) (evm_logs : event list) <=>
    LIST_REL (log_entry_corresponds event_info tenv addr)
      vyper_logs evm_logs
End

(* EVM post-state matches Vyper side effects:
   accounts, transient storage, and logs all correspond. *)
Definition state_effects_match_def:
  state_effects_match event_info (addr : address) tenv
    (am' : abstract_machine) es' <=>
    ?ctxt rb rest.
      es'.contexts = (ctxt, rb) :: rest /\
      es'.rollback.accounts = am'.accounts /\
      es'.rollback.tStorage = am'.tStorage /\
      logs_correspond event_info tenv addr am'.logs ctxt.logs
End

(* Rollback state unchanged at the call boundary: committed accounts and
   transient storage in the global rollback record are the same before and
   after execution. This avoids comparing per-frame snapshots, which EVM may
   update internally for gas accounting while still rolling back the call. *)
Definition state_unchanged_def:
  state_unchanged es es' <=>
    es'.rollback.accounts = es.rollback.accounts /\
    es'.rollback.tStorage = es.rollback.tStorage
End

(* Full Vyper-EVM correspondence for a single external call.
   Packages the case split on call_external result:
   - Success: EVM halts, returndata + state effects match
   - Assert/revert: EVM reverts, rollback state unchanged
   - Error: T (could be F under well-formedness)
   - Break/Continue/Return: F (never escape call_external) *)
Definition vyper_evm_correspondence_def:
  vyper_evm_correspondence tenv event_info ret am tx es <=>
    (case call_external am tx of
       (INL v, am') =>
         ?es'.
           run es = SOME (INR NONE, es') /\
           return_data_encodes tenv ret v es' /\
           state_effects_match event_info tx.target tenv am' es'
     | (INR (AssertException _), _) =>
         ?es'. run es = SOME (INR (SOME Reverted), es') /\
               state_unchanged es es'
     | (INR (Error _), _) => T
     | (INR BreakException, _) => F
     | (INR ContinueException, _) => F
     | (INR (ReturnException _), _) => F)
End

(* ===== EVM State Predicates ===== *)

(* EVM execution state corresponds to initial Venom state,
   with compiled bytecode loaded. Combines the initial state
   correspondence (shared environment, memory, empty stack)
   with the bytecode loading condition.
   Calldata: EVM msgParams.data = Venom cc_calldata (selector+ABI args). *)
Definition initial_evm_rel_def:
  initial_evm_rel bytecode vs es <=>
    ~NULL es.contexts /\
    let (ctxt, rb) = HD es.contexts in
      rb.accounts = vs.vs_accounts /\
      rb.tStorage = vs.vs_transient /\
      ctxt.returnData = vs.vs_returndata /\
      ctxt.logs = vs.vs_logs /\
      ctxt.stack = [] /\
      (!i. read_byte i vs.vs_memory = read_byte i ctxt.memory) /\
      ctxt.msgParams.data = vs.vs_call_ctx.cc_calldata /\
      ctxt.pc = 0 /\
      ctxt.msgParams.code = bytecode /\
      ctxt.msgParams.parsed = parse_code 0 FEMPTY bytecode
End

(* ===== Source Predicates ===== *)

(* Valid function call: source function exists in the abstract machine,
   calldata correctly ABI-encodes the arguments, and the selector
   table routes to the right function.

   Calldata is constrained via the tx (source args) and the EVM
   calldata bytes (in initial_evm_rel). The relation between
   tx.args and the ABI-encoded calldata is:
     calldata_encodes tenv name arg_types tx.args calldata_bytes

   No vs parameter needed -- calldata_encodes takes the byte list
   directly, and initial_evm_rel ensures EVM and Venom agree. *)
Definition valid_function_call_def:
  valid_function_call tenv am tx selectors calldata args ret <=>
    (?mut nr dflts body.
       lookup_exported_function
         (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
         tx.function_name = SOME (mut, nr, args, dflts, ret, body)) /\
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args
      calldata /\
    (?sel fn_lbl htz.
       MEM (sel, fn_lbl, htz) selectors /\
       selector_matches sel tx.function_name
         (vyper_to_abi_types tenv (MAP SND args)))
End
