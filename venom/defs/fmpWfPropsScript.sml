(* Proof interface for rooted FMP analysis. *)

Theory fmpWfProps
Ancestors
  fmpWfDefs

Theorem fmp_return_abi_matches_no_returns:
  fn_return_insts fn = [] /\
  (fn.fn_call_abi.ica_has_memory_return_buffer = SOME T ==>
   fn_memory_return_buffer_param fn <> NONE) ==>
  fmp_return_abi_matches sig fn
Proof
  simp[fmp_return_abi_matches_def]
QED

Theorem fmp_lowered_return_layout_wf_no_returns:
  fn_return_insts fn = [] ==>
  fmp_lowered_return_layout_wf sig fn
Proof
  simp[fmp_lowered_return_layout_wf_def]
QED

Theorem call_abi_matches_fn_iff:
  call_abi_matches_fn fn <=>
  ?sig. fn.fn_fmp_signature = SOME sig /\
        canonical_param_prefix fn /\
        fmp_return_abi_matches sig fn
Proof
  simp[call_abi_matches_fn_def]
  >> Cases_on `fn.fn_fmp_signature` >> simp[]
QED

Theorem fmp_seal_layout_matches_fn_iff:
  fmp_seal_layout_matches_fn fn sig <=>
  fn.fn_fmp_signature = SOME sig /\
  canonical_param_prefix fn /\
  IS_SOME (fn_hidden_fmp_param fn) = sig.fms_has_fmp_param /\
  fmp_return_abi_matches sig fn /\
  fmp_lowered_return_layout_wf sig fn
Proof
  simp[fmp_seal_layout_matches_fn_def, fmp_signature_syntax_wf_def]
QED

Theorem invoke_layout_wf_invoke:
  invoke_layout_wf ctx inst /\ inst.inst_opcode = INVOKE ==>
  ?callee_name args callee sig.
    inst.inst_operands = Label callee_name::args /\
    lookup_function callee_name ctx.ctx_functions = SOME callee /\
    fmp_seal_layout_matches_fn callee sig /\
    invoke_input_arity_ok callee sig inst /\
    fmp_invoke_output_arity_ok callee sig inst
Proof
  simp[invoke_layout_wf_def]
QED

Theorem fmp_signature_matches_fn_some:
  fn.fn_fmp_signature = SOME sig ==>
  (fmp_signature_matches_fn ctx fn <=>
    fmp_signature_syntax_wf sig fn /\
    fmp_runner_rooted_wf ctx sig fn)
Proof
  simp[fmp_signature_matches_fn_def]
QED

Theorem fmp_lowered_context_wf_function:
  fmp_lowered_context_wf ctx /\ MEM fn ctx.ctx_functions ==>
  IS_SOME fn.fn_eom /\
  no_raw_fmp_ops fn /\
  call_abi_matches_fn fn /\
  fmp_signature_matches_fn ctx fn
Proof
  simp[fmp_lowered_context_wf_def]
QED

Theorem fmp_lowered_context_wf_invoke:
  fmp_lowered_context_wf ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
  invoke_layout_wf ctx inst
Proof
  simp[fmp_lowered_context_wf_def] >> metis_tac[]
QED


Theorem fmp_value_rooted_fuel_intro:
  MEM inst (fn_insts fn) /\
  fmp_inst_roots ctx sig fn (fmp_value_rooted_fuel ctx sig fn fuel) v inst ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  simp[fmp_value_rooted_fuel_def, listTheory.EXISTS_MEM] >> metis_tac[]
QED

Theorem fmp_value_rooted_fuel_initial:
  MEM inst (fn_insts fn) /\
  inst.inst_opcode = INITIAL_FMP /\
  fn_is_context_entry ctx fn /\
  inst.inst_operands = [] /\ inst.inst_outputs = [v] ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  strip_tac >> irule fmp_value_rooted_fuel_intro
  >> qexists `inst` >> simp[fmp_inst_roots_def]
QED

Theorem fmp_value_rooted_fuel_param:
  MEM inst (fn_insts fn) /\
  inst.inst_opcode = FMP_PARAM /\
  ~fn_is_context_entry ctx fn /\ sig.fms_has_fmp_param /\
  LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = [v] ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  strip_tac >> irule fmp_value_rooted_fuel_intro
  >> qexists `inst` >> simp[fmp_inst_roots_def]
QED

Theorem fmp_value_rooted_fuel_assign:
  MEM inst (fn_insts fn) /\
  inst.inst_opcode = ASSIGN /\
  inst.inst_operands = [Var src] /\ inst.inst_outputs = [v] /\
  fmp_value_rooted_fuel ctx sig fn fuel src ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  strip_tac >> irule fmp_value_rooted_fuel_intro
  >> qexists `inst` >> simp[fmp_inst_roots_def] >> metis_tac[]
QED

Theorem fmp_value_rooted_fuel_phi:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  inst.inst_outputs = [v] /\ operand_vars inst.inst_operands <> [] /\
  2 * LENGTH (phi_pairs inst.inst_operands) = LENGTH inst.inst_operands /\
  EVERY (fmp_value_rooted_fuel ctx sig fn fuel)
    (operand_vars inst.inst_operands) ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  strip_tac >> irule fmp_value_rooted_fuel_intro
  >> qexists `inst` >> simp[fmp_inst_roots_def] >> metis_tac[]
QED

Theorem fmp_value_rooted_fuel_phi_single:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI /\
  inst.inst_operands = [Label pred; Var src] /\ inst.inst_outputs = [v] /\
  fmp_value_rooted_fuel ctx sig fn fuel src ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  strip_tac >> irule fmp_value_rooted_fuel_phi
  >> qexists `inst`
  >> simp[venomInstTheory.operand_vars_def,
          venomInstTheory.operand_var_def,
          venomInstTheory.phi_pairs_def]
QED

Theorem fmp_value_rooted_fuel_bump:
  MEM inst (fn_insts fn) /\ inst.inst_opcode = BUMP /\
  inst.inst_operands = [Var (basev:string); (sizeop:operand)] /\
  inst.inst_outputs = [(oldv:string); (newv:string)] /\
  (v = oldv \/ v = newv) /\
  fmp_value_rooted_fuel ctx sig fn fuel basev ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  strip_tac >> irule fmp_value_rooted_fuel_intro
  >> qexists `inst` >> simp[fmp_inst_roots_def] >> metis_tac[]
QED

Theorem fmp_value_rooted_fuel_arith:
  MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = [v] /\
  EXISTS (fmp_value_rooted_fuel ctx sig fn fuel)
    (operand_vars inst.inst_operands) ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  strip_tac >> irule fmp_value_rooted_fuel_intro
  >> qexists `inst` >> simp[fmp_inst_roots_def] >> metis_tac[]
QED

Theorem fmp_value_rooted_fuel_publishing_invoke:
  MEM inst (fn_insts fn) /\ publishing_invoke_wf ctx inst /\
  inst.inst_outputs <> [] /\ v = LAST inst.inst_outputs ==>
  fmp_value_rooted_fuel ctx sig fn (SUC fuel) v
Proof
  strip_tac >> irule fmp_value_rooted_fuel_intro
  >> qexists `inst` >> simp[fmp_inst_roots_def] >> metis_tac[]
QED

Theorem fmp_runner_rooted_wf_bump:
  fmp_runner_rooted_wf ctx sig fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = BUMP ==>
  ?basev sizeop oldv newv.
    inst.inst_operands = [Var (basev:string); (sizeop:operand)] /\
    inst.inst_outputs = [(oldv:string); (newv:string)] /\
    fmp_value_rooted ctx sig fn basev
Proof
  simp[fmp_runner_rooted_wf_def, listTheory.EVERY_MEM,
       fmp_runner_inst_wf_def, fmp_bump_consumer_wf_def]
QED

Theorem fmp_runner_rooted_wf_invoke:
  fmp_runner_rooted_wf ctx caller_sig fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = INVOKE ==>
  ?callee_name args callee callee_sig.
    inst.inst_operands = Label callee_name::args /\
    lookup_function callee_name ctx.ctx_functions = SOME callee /\
    callee.fn_fmp_signature = SOME callee_sig /\
    fmp_signature_syntax_wf callee_sig callee /\
    invoke_input_arity_ok callee callee_sig inst /\
    fmp_invoke_output_arity_ok callee callee_sig inst /\
    (callee_sig.fms_has_fmp_param ==>
      ?hidden.
        EL (LENGTH (fn_user_param_insts callee)) args = Var hidden /\
        fmp_value_rooted ctx caller_sig fn hidden)
Proof
  simp[fmp_runner_rooted_wf_def, listTheory.EVERY_MEM,
       fmp_runner_inst_wf_def, fmp_invoke_consumer_wf_def,
       fmp_seal_layout_matches_fn_def] >> metis_tac[]
QED

Theorem fmp_runner_rooted_wf_publishing_return:
  fmp_runner_rooted_wf ctx sig fn /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = RET /\ sig.fms_publishes ==>
  ?n adopted.
    fmp_expected_user_return_arity sig fn = SOME n /\
    lowered_return_inst_layout_wf T n inst /\
    operand_var (EL n inst.inst_operands) = SOME adopted /\
    fmp_value_rooted ctx sig fn adopted
Proof
  simp[fmp_runner_rooted_wf_def, listTheory.EVERY_MEM,
       fmp_runner_inst_wf_def, fmp_return_consumer_wf_def]
QED

val _ = export_theory();
