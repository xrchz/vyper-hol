(*
 * Rooted frame-memory-pointer signatures and post-lowering WF.
 *
 * This theory analyzes only current Venom syntax and current callee seals.
 *)

Theory fmpWfDefs
Ancestors
  callLayoutDefs
  staticLayoutWf

(* The finite universe used to bound rooted-provenance searches. *)
Definition fn_defined_values_def:
  fn_defined_values fn = FLAT (MAP inst_defs (fn_insts fn))
End

Definition fn_is_context_entry_def:
  fn_is_context_entry ctx fn <=> ctx.ctx_entry = SOME fn.fn_name
End

(* This is the non-recursive part of validating a seal against current syntax.
 * Rooted runner flow is deliberately added by fmp_signature_matches_fn below. *)
Definition fmp_signature_syntax_wf_def:
  fmp_signature_syntax_wf sig fn <=>
    canonical_param_prefix fn /\
    IS_SOME (fn_hidden_fmp_param fn) = sig.fms_has_fmp_param /\
    lowered_return_layout_wf sig fn
End

Definition call_abi_matches_fn_def:
  call_abi_matches_fn fn <=>
    canonical_param_prefix fn /\ fn_return_abi_matches fn
End

Definition fmp_seal_layout_matches_fn_def:
  fmp_seal_layout_matches_fn fn sig <=>
    fn.fn_fmp_signature = SOME sig /\
    fmp_signature_syntax_wf sig fn
End

(* A publishing invoke is trusted only after resolving its current callee and
 * validating that callee's current, sealed non-recursive layout. *)
Definition publishing_invoke_wf_def:
  publishing_invoke_wf ctx inst <=>
    ?callee_name args callee sig.
      inst.inst_operands = Label callee_name::args /\
      lookup_function callee_name ctx.ctx_functions = SOME callee /\
      fmp_seal_layout_matches_fn callee sig /\
      sig.fms_publishes /\
      invoke_input_arity_ok callee sig inst /\
      invoke_output_arity_ok callee sig inst
End

(* One producer step, parameterized by the already-rooted values available at
 * the smaller fuel.  Each accepted shape is intentionally exact. *)
Definition fmp_inst_roots_def:
  fmp_inst_roots ctx sig fn rooted v inst <=>
    (inst.inst_opcode = INITIAL_FMP /\
     fn_is_context_entry ctx fn /\
     inst.inst_operands = [] /\ inst.inst_outputs = [v]) \/
    (inst.inst_opcode = FMP_PARAM /\
     ~fn_is_context_entry ctx fn /\ sig.fms_has_fmp_param /\
     LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = [v]) \/
    (?src.
       inst.inst_opcode = ASSIGN /\
       inst.inst_operands = [Var src] /\ inst.inst_outputs = [v] /\
       rooted src) \/
    (inst.inst_opcode = PHI /\ inst.inst_outputs = [v] /\
     operand_vars inst.inst_operands <> [] /\
     2 * LENGTH (phi_pairs inst.inst_operands) =
       LENGTH inst.inst_operands /\
     EVERY rooted (operand_vars inst.inst_operands)) \/
    (?base size old new.
       inst.inst_opcode = BUMP /\
       inst.inst_operands = [Var base; size] /\
       inst.inst_outputs = [old; new] /\
       (v = old \/ v = new) /\ rooted base) \/
    ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
     LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = [v] /\
     EXISTS rooted (operand_vars inst.inst_operands)) \/
    (publishing_invoke_wf ctx inst /\
     inst.inst_outputs <> [] /\ v = LAST inst.inst_outputs)
End

Definition fmp_value_rooted_fuel_def:
  fmp_value_rooted_fuel ctx sig fn 0 v = F /\
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v =
    EXISTS
      (fmp_inst_roots ctx sig fn
        (fmp_value_rooted_fuel ctx sig fn fuel) v)
      (fn_insts fn)
End

Definition fmp_value_rooted_def:
  fmp_value_rooted ctx sig fn v =
    fmp_value_rooted_fuel ctx sig fn
      (SUC (LENGTH (fn_defined_values fn))) v
End

Definition fmp_bump_consumer_wf_def:
  fmp_bump_consumer_wf ctx sig fn inst <=>
    if inst.inst_opcode = BUMP then
      ?base size old new.
        inst.inst_operands = [Var base; size] /\
        inst.inst_outputs = [old; new] /\
        fmp_value_rooted ctx sig fn base
    else T
End

(* The hidden input is after all user inputs, never simply the last operand of
 * the whole instruction (whose first operand is the callee label). *)
Definition fmp_invoke_consumer_wf_def:
  fmp_invoke_consumer_wf ctx caller_sig fn inst <=>
    if inst.inst_opcode = INVOKE then
      ?callee_name args callee callee_sig.
        inst.inst_operands = Label callee_name::args /\
        lookup_function callee_name ctx.ctx_functions = SOME callee /\
        fmp_seal_layout_matches_fn callee callee_sig /\
        invoke_input_arity_ok callee callee_sig inst /\
        invoke_output_arity_ok callee callee_sig inst /\
        (callee_sig.fms_has_fmp_param ==>
          ?hidden.
            EL (LENGTH (fn_user_param_insts callee)) args = Var hidden /\
            fmp_value_rooted ctx caller_sig fn hidden)
    else T
End

Definition fmp_return_consumer_wf_def:
  fmp_return_consumer_wf ctx sig fn inst <=>
    if inst.inst_opcode = RET /\ sig.fms_publishes then
      ?n adopted.
        fn_expected_user_return_arity fn = SOME n /\
        lowered_return_inst_layout_wf T n inst /\
        operand_var (EL n inst.inst_operands) = SOME adopted /\
        fmp_value_rooted ctx sig fn adopted
    else T
End

Definition fmp_runner_inst_wf_def:
  fmp_runner_inst_wf ctx sig fn inst <=>
    fmp_bump_consumer_wf ctx sig fn inst /\
    fmp_invoke_consumer_wf ctx sig fn inst /\
    fmp_return_consumer_wf ctx sig fn inst
End

Definition fmp_runner_rooted_wf_def:
  fmp_runner_rooted_wf ctx sig fn <=>
    EVERY (fmp_runner_inst_wf ctx sig fn) (fn_insts fn)
End

(* A closed sanity check for the least-closure behavior: fuel does not turn an
 * unseeded cyclic alias into a root. *)
Definition fmp_cycle_probe_fn_def:
  fmp_cycle_probe_fn =
    mk_raw_function "cycle"
      [<| bb_label := "entry";
          bb_instructions := [mk_inst 1 ASSIGN [Var "x"] ["x"]] |>]
End

Theorem fmp_value_rooted_rejects_self_cycle:
  ~fmp_value_rooted
    (mk_venom_context [fmp_cycle_probe_fn] NONE)
    <| fms_has_fmp_param := F; fms_publishes := F |>
    fmp_cycle_probe_fn "x"
Proof
  EVAL_TAC >> simp[]
QED

val _ = export_theory();
