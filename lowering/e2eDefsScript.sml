(*
 * End-to-End Definitions (Vyper-to-EVM Correspondence Predicates)
 *
 * Pure definitions used by the e2e correctness theorems.
 * No proof dependencies -- only definition-level ancestors.
 *
 * TOP-LEVEL:
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
  vyperEvent
  vyperInterpreter
  compileEnv
  selectorDispatch
  codegenRel
  venomState

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

(* Source execution now records the concrete EVM event directly. The metadata
   parameters remain temporarily for compatibility with the e2e API. *)
Definition log_entry_corresponds_def:
  log_entry_corresponds _ _ _ (source_event : log) (ev : event) <=>
    source_event = ev
End

(* Compatibility lemmas between the executable semantics encoder and the
   pre-existing relational log specification in compileEnv. *)
Theorem event_value_to_word_eq_val_to_w256:
  event_value_to_word v = val_to_w256 v
Proof
  Cases_on `v` >>
  simp[event_value_to_word_def, valueEncodingTheory.val_to_w256_def]
QED

Theorem encode_event_topic_eq_log_topic_equiv:
  encode_event_topic is_bytestring v = SOME topic <=>
  log_topic_equiv is_bytestring v topic
Proof
  Cases_on `is_bytestring` >> Cases_on `v` >>
  simp[encode_event_topic_def, log_topic_equiv_def,
       log_bytestring_topic_def, event_value_to_word_eq_val_to_w256,
       byteTheory.word_of_bytes_be_def] >>
  metis_tac[]
QED

Theorem encode_indexed_event_topics_characterization:
  encode_indexed_event_topics flags tys vals = SOME topics <=>
  LENGTH flags = LENGTH tys /\
  LENGTH flags = LENGTH vals /\
  log_indexed_topics_equiv
    (indexed_topic_flags flags (MAP is_bytestring_type tys))
    (indexed_values flags vals) topics
Proof
  `!ty. is_event_bytestring_type ty = is_bytestring_type ty` by
    (gen_tac >> Cases_on `ty` >> simp[is_event_bytestring_type_def,
                                      is_bytestring_type_def] >>
     Cases_on `b` >> simp[is_event_bytestring_type_def,
                          is_bytestring_type_def] >>
     Cases_on `b'` >> simp[is_event_bytestring_type_def,
                           is_bytestring_type_def]) >>
  qid_spec_tac `topics` >> qid_spec_tac `vals` >> qid_spec_tac `tys` >>
  Induct_on `flags`
  >- (Cases_on `tys` >> Cases_on `vals` >> Cases_on `topics` >>
      simp[encode_indexed_event_topics_def, indexed_topic_flags_def,
           indexed_values_def, log_indexed_topics_equiv_def])
  >> qx_gen_tac `flag` >> qx_gen_tac `tys` >>
  qx_gen_tac `vals` >> qx_gen_tac `topics` >>
  Cases_on `tys` >> Cases_on `vals` >> Cases_on `flag` >>
  Cases_on `topics` >>
  gvs[encode_indexed_event_topics_def, indexed_topic_flags_def,
      indexed_values_def, log_indexed_topics_equiv_def,
      is_event_bytestring_type_def, is_bytestring_type_def,
      encode_event_topic_eq_log_topic_equiv, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem non_indexed_event_args_characterization:
  non_indexed_event_args flags tys vals = SOME typed_vals <=>
  LENGTH flags = LENGTH tys /\
  LENGTH flags = LENGTH vals /\
  MAP FST typed_vals = log_non_indexed_types flags tys /\
  MAP SND typed_vals = log_non_indexed_values flags vals
Proof
  qid_spec_tac `typed_vals` >> qid_spec_tac `vals` >>
  qid_spec_tac `tys` >> Induct_on `flags`
  >- (Cases_on `tys` >> Cases_on `vals` >> Cases_on `typed_vals` >>
      simp[non_indexed_event_args_def, log_non_indexed_types_def,
           log_non_indexed_values_def])
  >> qx_gen_tac `flag` >> qx_gen_tac `tys` >>
  qx_gen_tac `vals` >> qx_gen_tac `typed_vals` >>
  Cases_on `tys` >> Cases_on `vals` >> Cases_on `flag` >>
  Cases_on `typed_vals` >>
  gvs[non_indexed_event_args_def, log_non_indexed_types_def,
      log_non_indexed_values_def, AllCaseEqs()] >>
  PairCases_on `h''` >> gvs[] >>
  simp[AC CONJ_ASSOC CONJ_COMM]
QED
Theorem non_indexed_event_args_exists:
  LENGTH flags = LENGTH tys /\
  LENGTH flags = LENGTH vals ==>
  ?typed_vals.
    non_indexed_event_args flags tys vals = SOME typed_vals /\
    MAP FST typed_vals = log_non_indexed_types flags tys /\
    MAP SND typed_vals = log_non_indexed_values flags vals
Proof
  qid_spec_tac `vals` >> qid_spec_tac `tys` >> Induct_on `flags`
  >- (Cases_on `tys` >> Cases_on `vals` >>
      simp[non_indexed_event_args_def, log_non_indexed_types_def,
           log_non_indexed_values_def])
  >> qx_gen_tac `flag` >> qx_gen_tac `tys` >> qx_gen_tac `vals` >>
  Cases_on `tys` >> Cases_on `vals` >> Cases_on `flag` >>
  gvs[non_indexed_event_args_def, log_non_indexed_types_def,
      log_non_indexed_values_def] >>
  strip_tac >> first_x_assum drule >> disch_then drule >> strip_tac >>
  qexists `(h,h')::typed_vals` >> simp[]
QED


(* OBSOLETE after source logs became concrete events. Preserved until the
   surrounding legacy compatibility package is removed deliberately.
Theorem log_entry_equiv_encode_vyper_event:
  log_entry_equiv cenv addr (eid, vals) ev <=>
  encode_vyper_event cenv.ce_event_info cenv.ce_type_env addr
    (nsid_to_string eid) vals = SOME ev
Proof
  Cases_on `cenv.ce_event_info (nsid_to_string eid)`
  >- simp[log_entry_equiv_def, encode_vyper_event_def]
  >> PairCases_on `x` >>
  simp[log_entry_equiv_def, encode_vyper_event_def,
       encode_vyper_event_metadata_def] >>
  eq_tac
  >- (strip_tac >>
      `encode_indexed_event_topics x2 x1 vals = SOME topic_tail` by
        (simp[encode_indexed_event_topics_characterization] >> metis_tac[]) >>
      `?typed_vals.
         non_indexed_event_args x2 x1 vals = SOME typed_vals /\
         MAP FST typed_vals = log_non_indexed_types x2 x1 /\
         MAP SND typed_vals = log_non_indexed_values x2 vals` by
        (irule non_indexed_event_args_exists >> metis_tac[]) >>
      Cases_on `ev` >> gvs[vfmTypesTheory.event_component_equality])
  >> Cases_on `encode_indexed_event_topics x2 x1 vals`
  >- simp[]
  >> Cases_on `non_indexed_event_args x2 x1 vals`
  >- simp[]
  >> Cases_on `vyper_to_abi_list cenv.ce_type_env (MAP FST x') (MAP SND x')`
  >- simp[]
  >> simp[] >> strip_tac >>
  gvs[encode_indexed_event_topics_characterization,
      non_indexed_event_args_characterization,
      vfmTypesTheory.event_component_equality] >>
  qexists `x` >> simp[]
QED

Theorem log_entry_corresponds_encode:
  log_entry_corresponds event_info tenv addr (eid, vals) ev <=>
  encode_vyper_event event_info tenv addr (nsid_to_string eid) vals = SOME ev
Proof
  simp[log_entry_corresponds_def]
QED
*)

Theorem log_entry_equiv_concrete_event:
  log_entry_equiv cenv addr source_event ev <=> source_event = ev
Proof
  simp[log_entry_equiv_def]
QED

Theorem log_entry_corresponds_concrete_event:
  log_entry_corresponds event_info tenv addr source_event ev <=>
  source_event = ev
Proof
  simp[log_entry_corresponds_def]
QED

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
