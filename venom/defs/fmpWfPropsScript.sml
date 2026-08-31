(* Proof interface for rooted FMP analysis. *)

Theory fmpWfProps
Ancestors
  fmpWfDefs
Theorem call_abi_matches_fn_iff:
  call_abi_matches_fn fn <=>
  canonical_param_prefix fn /\ fn_return_abi_matches fn
Proof
  simp[call_abi_matches_fn_def]
QED

Theorem fmp_seal_layout_matches_fn_iff:
  fmp_seal_layout_matches_fn fn sig <=>
  fn.fn_fmp_signature = SOME sig /\
  canonical_param_prefix fn /\
  IS_SOME (fn_hidden_fmp_param fn) = sig.fms_has_fmp_param /\
  lowered_return_layout_wf sig fn
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
    invoke_output_arity_ok callee sig inst
Proof
  simp[invoke_layout_wf_def]
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
    invoke_output_arity_ok callee callee_sig inst /\
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
    fn_expected_user_return_arity fn = SOME n /\
    lowered_return_inst_layout_wf T n inst /\
    operand_var (EL n inst.inst_operands) = SOME adopted /\
    fmp_value_rooted ctx sig fn adopted
Proof
  simp[fmp_runner_rooted_wf_def, listTheory.EVERY_MEM,
       fmp_runner_inst_wf_def, fmp_return_consumer_wf_def]
QED

val _ = export_theory();
