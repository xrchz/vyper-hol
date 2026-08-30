(*
 * Vyper-to-Venom Lowering Correctness (Top-Level)
 *
 * Upstream: vyperlang/vyper@a7f7bf133
 *
 * Connects Vyper big-step semantics (call_external) to Venom IR
 * execution (run_context) on the context produced by run_lowering_pair_compat.
 *
 * Three-layer decomposition:
 *   Layer 1 - Selector dispatch: calldata method_id routes to correct
 *     entry block (selectorDispatch, per compile_selector_dispatch)
 *   Layer 2 - Argument decoding: ABI-encoded calldata decoded to values
 *     matching tx.args (abiEncoderProps, valueEncodingProofs)
 *   Layer 3 - Function body: compiled Venom body preserves semantics
 *     (stmtLoweringProps, exprLoweringProps)
 *
 * TOP-LEVEL:
 *   external_call_result_rel -- cross-domain result relation
 *   vyper_to_venom_correct   -- lowering preserves execution semantics
 *
 * STATUS: Top-level lowering theorem is currently an open/cheated target.
 * Before major proof repair, check lowering definitions against the chosen
 * upstream compiler target; see docs/compiler-definition-parity.md.
 *)

Theory vyperLoweringCorrect
Ancestors
  vyperCompiler
  selectorDispatch
  moduleLoweringProps
  stmtLoweringProps
  exprLoweringProps
  valueEncodingProofs
  builtinProps
  contextProps
  arithmeticProps
  abiEncoderProps
  vyperInterpreter
  vyperContext
  venomExecSemantics
  venomState
  compileEnv

(* ===== Cross-Domain Result Relation ===== *)

(* Observable state produced by an external source call. Function-local scope
   state is gone at this boundary, so this is intentionally smaller than
   compileEnv$state_rel but still includes all externally visible effects. *)
Definition external_logs_rel_def:
  external_logs_rel cenv (addr : address) (am : abstract_machine) ss ⇔
    LIST_REL (log_entry_equiv cenv addr) am.logs ss.vs_logs
End

Definition external_call_state_rel_def:
  external_call_state_rel cenv cx (am : abstract_machine) ss ⇔
    ss.vs_accounts = am.accounts ∧
    ss.vs_transient = am.tStorage ∧
    external_logs_rel cenv cx.txn.target am ss ∧
    call_ctx_rel cx.txn ss.vs_call_ctx ss.vs_tx_ctx ss.vs_block_ctx
End

(* Relates Vyper external call results to Venom execution results.
   call_external returns (value + exception, abstract_machine).
   run_context returns exec_result.

   Parameterized by tenv (type environment), cenv/cx (the lowering
   state relation context), and ret_type (return type) for ABI encoding
   of the return value.

   Success case requires the external-call state relation, so logs,
   accounts, transient storage, call context, and returndata are all part
   of the lowering result relation instead of e2e-side patches. *)
Definition external_call_result_rel_def:
  (* Successful return *)
  (external_call_result_rel tenv cenv cx ret_type (INL v, am') (Halt ss') <=>
    cenv.ce_type_env = tenv /\
    external_call_state_rel cenv cx am' ss' /\
    (?abi_val.
      vyper_to_abi tenv ret_type v = SOME abi_val /\
      ss'.vs_returndata =
        enc (vyper_to_abi_type tenv ret_type) abi_val)) /\
  (* Assert/revert => Abort revert *)
  (external_call_result_rel tenv cenv cx ret_type (INR (AssertException _), am')
                             (Abort Revert_abort ss') <=> T) /\
  (* Vyper error => any Venom abort or error *)
  (external_call_result_rel tenv cenv cx ret_type (INR (Error _), am')
                             (Abort _ ss') <=> T) /\
  (external_call_result_rel tenv cenv cx ret_type (INR (Error _), am')
                             (Error _) <=> T) /\
  (* All other combinations are invalid *)
  (external_call_result_rel _ _ _ _ _ _ <=> F)
End

(* ===== Lowering Correctness ===== *)

(* For a well-formed external call to a compiled module:

   If calldata correctly encodes a call to function tx.function_name
   with arguments tx.args, then Venom execution on the lowered context
   produces a result corresponding to Vyper evaluation.

   ctx is bound to run_lowering_pair_compat on the given compilation inputs.
   The selector_matches predicate links sel_num to tx.function_name
   via keccak256 of the ABI signature. *)
Theorem vyper_to_venom_correct:
  !tenv selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    vs am tx sel fn_lbl htz cenv
    args dflts ret body mut nr.
  let (ctx, _) = run_lowering_pair_compat selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
    (* tx targets a known external function *)
    lookup_exported_function
      (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
      tx.function_name = SOME (mut, nr, args, dflts, ret, body) /\
    (* Calldata encodes the call *)
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args
      vs.vs_call_ctx.cc_calldata /\
    (* Selector table entry matches function *)
    MEM (sel, fn_lbl, htz) selectors /\
    selector_matches sel tx.function_name
      (vyper_to_abi_types tenv (MAP SND args)) /\
    (* Venom state is initial *)
    vs.vs_inst_idx = 0
    ==>
    ?fuel.
      external_call_result_rel tenv cenv
        (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name))
        ret (call_external am tx) (run_context fuel ctx vs)
Proof
  cheat
QED
