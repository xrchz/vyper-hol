(* Proof interface for rooted FMP analysis. *)

Theory fmpWfProps
Ancestors
  fmpWfDefs

(* Closed probes for the signature-aware current-return boundary. *)
Definition fmp_arity_probe_publishing_sig_def:
  fmp_arity_probe_publishing_sig =
    <| fms_has_fmp_param := F; fms_publishes := T |>
End

Definition fmp_arity_probe_nonpublishing_sig_def:
  fmp_arity_probe_nonpublishing_sig =
    <| fms_has_fmp_param := F; fms_publishes := F |>
End

Definition fmp_arity_probe_publishing_fn_def:
  fmp_arity_probe_publishing_fn =
    mk_raw_function "arity_pub"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 0 RET [Var "user"; Var "adopted"; Var "rpc"] []] |>]
End

Definition fmp_arity_probe_nonpublishing_fn_def:
  fmp_arity_probe_nonpublishing_fn =
    mk_raw_function "arity_plain"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 0 RET [Var "user"; Var "rpc"] []] |>]
End

Definition fmp_arity_probe_mismatched_fn_def:
  fmp_arity_probe_mismatched_fn =
    fmp_arity_probe_publishing_fn with fn_call_abi :=
      (fmp_arity_probe_publishing_fn.fn_call_abi with
         ica_user_return_count := SOME 2)
End

Theorem fmp_current_return_arity_probe:
  fmp_current_return_user_arity fmp_arity_probe_publishing_sig
    (mk_inst 0 RET [Var "user"; Var "adopted"; Var "rpc"] []) = SOME 1 /\
  fmp_unique_return_arity fmp_arity_probe_publishing_sig
    fmp_arity_probe_publishing_fn = SOME 1 /\
  fmp_expected_user_return_arity fmp_arity_probe_publishing_sig
    fmp_arity_probe_publishing_fn = SOME 1 /\
  fmp_return_abi_matches fmp_arity_probe_publishing_sig
    fmp_arity_probe_publishing_fn /\
  fmp_current_return_user_arity fmp_arity_probe_nonpublishing_sig
    (mk_inst 0 RET [Var "user"; Var "rpc"] []) = SOME 1 /\
  fmp_unique_return_arity fmp_arity_probe_nonpublishing_sig
    fmp_arity_probe_nonpublishing_fn = SOME 1 /\
  fmp_expected_user_return_arity fmp_arity_probe_nonpublishing_sig
    fmp_arity_probe_nonpublishing_fn = SOME 1 /\
  fmp_return_abi_matches fmp_arity_probe_nonpublishing_sig
    fmp_arity_probe_nonpublishing_fn /\
  fmp_current_return_user_arity fmp_arity_probe_publishing_sig
    (mk_inst 0 RET [Var "rpc"] []) = NONE /\
  ~fmp_return_abi_matches fmp_arity_probe_publishing_sig
    fmp_arity_probe_mismatched_fn
Proof
  EVAL_TAC
QED

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

Theorem fmp_arity_probe_mismatched_rejected:
  ~fmp_return_abi_matches fmp_arity_probe_publishing_sig
    fmp_arity_probe_mismatched_fn
Proof
  EVAL_TAC
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

(* Compact executable fixtures spanning every rooted producer form. *)
Definition fmp_positive_callee_sig_def:
  fmp_positive_callee_sig =
    <| fms_has_fmp_param := T; fms_publishes := T |>
End

Definition fmp_positive_entry_sig_def:
  fmp_positive_entry_sig =
    <| fms_has_fmp_param := F; fms_publishes := F |>
End

Definition fmp_positive_callee_def:
  fmp_positive_callee =
    (mk_raw_function "callee"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 20 PARAM [Lit 0w] ["cu"];
             mk_inst 21 FMP_PARAM [Lit 1w] ["cfmp"];
             mk_inst 22 RETPC_PARAM [Lit 2w] ["crpc"];
             mk_inst 23 ADD [Var "cfmp"; Lit 1w] ["cadopt"];
             mk_inst 24 RET
               [Var "cu"; Var "cadopt"; Var "crpc"] []] |>]) with <|
      fn_eom := SOME 0;
      fn_fmp_signature := SOME fmp_positive_callee_sig
    |>
End

Definition fmp_positive_invoke_def:
  fmp_positive_invoke =
    mk_inst 8 INVOKE
      [Label "callee"; Lit 7w; Var "minus"] ["user_out"; "published"]
End

Definition fmp_positive_entry_def:
  fmp_positive_entry =
    (mk_raw_function "entry"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 0 RETPC_PARAM [Lit 0w] ["rpc"];
             mk_inst 1 INITIAL_FMP [] ["root"];
             mk_inst 2 ASSIGN [Var "root"] ["alias"];
             mk_inst 3 PHI [Label "entry"; Var "alias"] ["joined"];
             mk_inst 4 BUMP [Var "joined"; Lit 32w] ["old"; "new"];
             mk_inst 5 ADD [Var "new"; Lit 1w] ["plus"];
             mk_inst 6 SUB [Var "plus"; Lit 1w] ["minus"];
             fmp_positive_invoke;
             mk_inst 9 RET [Var "published"; Var "rpc"] []] |>]) with <|
      fn_eom := SOME 0;
      fn_fmp_signature := SOME fmp_positive_entry_sig
    |>
End

Definition fmp_positive_ctx_def:
  fmp_positive_ctx =
    mk_venom_context [fmp_positive_entry; fmp_positive_callee] (SOME "entry")
End

Theorem fmp_positive_root_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry (SUC fuel) "root"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_initial
  >> conj_tac >-
    (qexists `mk_inst 1 INITIAL_FMP [] ["root"]` >> EVAL_TAC)
  >> EVAL_TAC
QED

Theorem fmp_positive_alias_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry (SUC (SUC fuel)) "alias"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_assign
  >> qexistsl [`mk_inst 2 ASSIGN [Var "root"] ["alias"]`, `"root"`]
  >> simp[fmp_positive_root_fuel] >> EVAL_TAC
QED

Theorem fmp_positive_joined_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry (SUC (SUC (SUC fuel))) "joined"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_phi_single
  >> qexistsl [`mk_inst 3 PHI [Label "entry"; Var "alias"] ["joined"]`,
                `"entry"`, `"alias"`]
  >> simp[fmp_positive_alias_fuel] >> EVAL_TAC
QED

Theorem fmp_positive_new_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry (SUC (SUC (SUC (SUC fuel)))) "new"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_bump
  >> qexistsl [`"joined"`,
                `mk_inst 4 BUMP [Var "joined"; Lit 32w] ["old"; "new"]`,
                `"new"`, `"old"`, `Lit 32w`]
  >> simp[fmp_positive_joined_fuel] >> EVAL_TAC
QED

Theorem fmp_positive_plus_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry (SUC (SUC (SUC (SUC (SUC fuel))))) "plus"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_arith
  >> qexists `mk_inst 5 ADD [Var "new"; Lit 1w] ["plus"]`
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> conj_tac >-
    simp[venomInstTheory.mk_inst_def, venomInstTheory.operand_vars_def,
         venomInstTheory.operand_var_def, fmp_positive_new_fuel]
  >> conj_tac >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem fmp_positive_minus_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry (SUC (SUC (SUC (SUC (SUC (SUC fuel)))))) "minus"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_arith
  >> qexists `mk_inst 6 SUB [Var "plus"; Lit 1w] ["minus"]`
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> conj_tac >-
    simp[venomInstTheory.mk_inst_def, venomInstTheory.operand_vars_def,
         venomInstTheory.operand_var_def, fmp_positive_plus_fuel]
  >> conj_tac >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem fmp_positive_published_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry
      (SUC (SUC (SUC (SUC (SUC (SUC (SUC fuel))))))) "published"
Proof
  gen_tac
  >> `publishing_invoke_wf fmp_positive_ctx fmp_positive_invoke` by
       (simp[publishing_invoke_wf_def]
        >> qexistsl [`"callee"`, `[Lit 7w; Var "minus"]`,
                     `fmp_positive_callee`, `fmp_positive_callee_sig`]
        >> EVAL_TAC)
  >> irule fmp_value_rooted_fuel_publishing_invoke
  >> qexists `fmp_positive_invoke`
  >> simp[fmp_positive_invoke_def] >> EVAL_TAC
QED

Theorem fmp_positive_callee_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_callee_sig
    fmp_positive_callee (SUC fuel) "cfmp"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_param
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> qexists `mk_inst 21 FMP_PARAM [Lit 1w] ["cfmp"]` >> EVAL_TAC
QED

Theorem fmp_positive_callee_adopted_fuel:
  !fuel. fmp_value_rooted_fuel fmp_positive_ctx fmp_positive_callee_sig
    fmp_positive_callee (SUC (SUC fuel)) "cadopt"
Proof
  gen_tac >> irule fmp_value_rooted_fuel_arith
  >> qexists `mk_inst 23 ADD [Var "cfmp"; Lit 1w] ["cadopt"]`
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> conj_tac >-
    simp[venomInstTheory.mk_inst_def, venomInstTheory.operand_vars_def,
         venomInstTheory.operand_var_def, fmp_positive_callee_fuel]
  >> conj_tac >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem fmp_positive_defined_values_lengths:
  LENGTH (fn_defined_values fmp_positive_entry) = 10 /\
  LENGTH (fn_defined_values fmp_positive_callee) = 4
Proof
  EVAL_TAC
QED

Theorem fmp_positive_root_propagation_eval:
  fmp_value_rooted fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry "root" /\
  fmp_value_rooted fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry "alias" /\
  fmp_value_rooted fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry "joined" /\
  fmp_value_rooted fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry "new" /\
  fmp_value_rooted fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry "plus" /\
  fmp_value_rooted fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry "minus" /\
  fmp_value_rooted fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry "published" /\
  fmp_value_rooted fmp_positive_ctx fmp_positive_callee_sig
    fmp_positive_callee "cfmp"
Proof
  conj_tac >-
    (rewrite_tac[fmp_value_rooted_def,
                 cj 1 fmp_positive_defined_values_lengths]
     >> qspec_then `10` mp_tac fmp_positive_root_fuel >> simp[])
  >> conj_tac >-
    (rewrite_tac[fmp_value_rooted_def,
                 cj 1 fmp_positive_defined_values_lengths]
     >> qspec_then `9` mp_tac fmp_positive_alias_fuel >> simp[])
  >> conj_tac >-
    (rewrite_tac[fmp_value_rooted_def,
                 cj 1 fmp_positive_defined_values_lengths]
     >> qspec_then `8` mp_tac fmp_positive_joined_fuel >> simp[])
  >> conj_tac >-
    (rewrite_tac[fmp_value_rooted_def,
                 cj 1 fmp_positive_defined_values_lengths]
     >> qspec_then `7` mp_tac fmp_positive_new_fuel >> simp[])
  >> conj_tac >-
    (rewrite_tac[fmp_value_rooted_def,
                 cj 1 fmp_positive_defined_values_lengths]
     >> qspec_then `6` mp_tac fmp_positive_plus_fuel >> simp[])
  >> conj_tac >-
    (rewrite_tac[fmp_value_rooted_def,
                 cj 1 fmp_positive_defined_values_lengths]
     >> qspec_then `5` mp_tac fmp_positive_minus_fuel >> simp[])
  >> conj_tac >-
    (rewrite_tac[fmp_value_rooted_def,
                 cj 1 fmp_positive_defined_values_lengths]
     >> qspec_then `4` mp_tac fmp_positive_published_fuel >> simp[])
  >> rewrite_tac[fmp_value_rooted_def,
                 cj 2 fmp_positive_defined_values_lengths]
  >> qspec_then `4` mp_tac fmp_positive_callee_fuel >> simp[]
QED

Theorem fmp_positive_entry_syntax_wf:
  fmp_signature_syntax_wf fmp_positive_entry_sig fmp_positive_entry
Proof
  EVAL_TAC
QED

Theorem fmp_positive_callee_syntax_wf:
  fmp_signature_syntax_wf fmp_positive_callee_sig fmp_positive_callee
Proof
  EVAL_TAC
QED

Theorem fmp_positive_static_layout_wf:
  concretized_static_layouts_wf fmp_positive_ctx
Proof
  EVAL_TAC >> rpt strip_tac
  >> gvs[venomInstTheory.fn_insts_blocks_def]
QED

Theorem fmp_positive_entry_basics_wf:
  IS_SOME fmp_positive_entry.fn_eom /\
  no_raw_fmp_ops fmp_positive_entry /\
  call_abi_matches_fn fmp_positive_entry
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem fmp_positive_callee_basics_wf:
  IS_SOME fmp_positive_callee.fn_eom /\
  no_raw_fmp_ops fmp_positive_callee /\
  call_abi_matches_fn fmp_positive_callee
Proof
  EVAL_TAC >> rpt strip_tac >> gvs[venomInstTheory.is_raw_fmp_opcode_def]
QED
Theorem fmp_positive_function_basics_wf:
  !fn. MEM fn fmp_positive_ctx.ctx_functions ==>
    IS_SOME fn.fn_eom /\ no_raw_fmp_ops fn /\ call_abi_matches_fn fn
Proof
  simp[fmp_positive_ctx_def, venomInstTheory.mk_venom_context_def]
  >> metis_tac[fmp_positive_entry_basics_wf,
               fmp_positive_callee_basics_wf]
QED

Theorem fmp_positive_entry_bump_inst_wf:
  fmp_runner_inst_wf fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry
    (mk_inst 4 BUMP [Var "joined"; Lit 32w] ["old"; "new"])
Proof
  simp[fmp_runner_inst_wf_def, fmp_bump_consumer_wf_def,
       fmp_invoke_consumer_wf_def, fmp_return_consumer_wf_def,
       venomInstTheory.mk_inst_def, fmp_positive_root_propagation_eval]
QED

Theorem fmp_positive_entry_invoke_inst_wf:
  fmp_runner_inst_wf fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry fmp_positive_invoke
Proof
  simp[fmp_runner_inst_wf_def, fmp_bump_consumer_wf_def,
       fmp_invoke_consumer_wf_def, fmp_return_consumer_wf_def,
       fmp_positive_invoke_def, venomInstTheory.mk_inst_def]
  >> qexistsl [`fmp_positive_callee`, `fmp_positive_callee_sig`]
  >> conj_tac >- EVAL_TAC
  >> conj_tac >-
    simp[fmp_seal_layout_matches_fn_def, fmp_positive_callee_def,
         fmp_positive_callee_syntax_wf]
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> strip_tac
  >> qexists `"minus"`
  >> conj_tac >- EVAL_TAC
  >> simp[fmp_positive_root_propagation_eval]
QED

Theorem fmp_positive_entry_insts:
  fn_insts fmp_positive_entry =
    [mk_inst 0 RETPC_PARAM [Lit 0w] ["rpc"];
     mk_inst 1 INITIAL_FMP [] ["root"];
     mk_inst 2 ASSIGN [Var "root"] ["alias"];
     mk_inst 3 PHI [Label "entry"; Var "alias"] ["joined"];
     mk_inst 4 BUMP [Var "joined"; Lit 32w] ["old"; "new"];
     mk_inst 5 ADD [Var "new"; Lit 1w] ["plus"];
     mk_inst 6 SUB [Var "plus"; Lit 1w] ["minus"];
     fmp_positive_invoke;
     mk_inst 9 RET [Var "published"; Var "rpc"] []]
Proof
  EVAL_TAC
QED

Theorem fmp_positive_entry_runner_wf:
  fmp_runner_rooted_wf fmp_positive_ctx fmp_positive_entry_sig
    fmp_positive_entry
Proof
  rewrite_tac[fmp_runner_rooted_wf_def, fmp_positive_entry_insts]
  >> simp[fmp_positive_entry_bump_inst_wf,
          fmp_positive_entry_invoke_inst_wf,
          fmp_runner_inst_wf_def, fmp_bump_consumer_wf_def,
          fmp_invoke_consumer_wf_def, fmp_return_consumer_wf_def,
          fmp_positive_entry_sig_def, venomInstTheory.mk_inst_def]
QED

Theorem fmp_positive_callee_adopted_rooted:
  fmp_value_rooted fmp_positive_ctx fmp_positive_callee_sig
    fmp_positive_callee "cadopt"
Proof
  rewrite_tac[fmp_value_rooted_def,
              cj 2 fmp_positive_defined_values_lengths]
  >> qspec_then `3` mp_tac fmp_positive_callee_adopted_fuel
  >> simp[]
QED

Theorem fmp_positive_callee_return_inst_wf:
  fmp_runner_inst_wf fmp_positive_ctx fmp_positive_callee_sig
    fmp_positive_callee
    (mk_inst 24 RET [Var "cu"; Var "cadopt"; Var "crpc"] [])
Proof
  simp[fmp_runner_inst_wf_def, fmp_bump_consumer_wf_def,
       fmp_invoke_consumer_wf_def, fmp_return_consumer_wf_def,
       venomInstTheory.mk_inst_def]
  >> strip_tac
  >> qexistsl [`1`, `"cadopt"`]
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> conj_tac >- EVAL_TAC
  >> irule fmp_positive_callee_adopted_rooted
QED

Theorem fmp_positive_callee_insts:
  fn_insts fmp_positive_callee =
    [mk_inst 20 PARAM [Lit 0w] ["cu"];
     mk_inst 21 FMP_PARAM [Lit 1w] ["cfmp"];
     mk_inst 22 RETPC_PARAM [Lit 2w] ["crpc"];
     mk_inst 23 ADD [Var "cfmp"; Lit 1w] ["cadopt"];
     mk_inst 24 RET [Var "cu"; Var "cadopt"; Var "crpc"] []]
Proof
  EVAL_TAC
QED

Theorem fmp_positive_callee_runner_wf:
  fmp_runner_rooted_wf fmp_positive_ctx fmp_positive_callee_sig
    fmp_positive_callee
Proof
  rewrite_tac[fmp_runner_rooted_wf_def, fmp_positive_callee_insts]
  >> simp[fmp_positive_callee_return_inst_wf,
          fmp_runner_inst_wf_def, fmp_bump_consumer_wf_def,
          fmp_invoke_consumer_wf_def, fmp_return_consumer_wf_def,
          venomInstTheory.mk_inst_def]
QED

Theorem fmp_positive_invoke_layout_wf:
  invoke_layout_wf fmp_positive_ctx fmp_positive_invoke
Proof
  simp[invoke_layout_wf_def]
  >> strip_tac
  >> qexistsl [`"callee"`, `[Lit 7w; Var "minus"]`,
               `fmp_positive_callee`, `fmp_positive_callee_sig`]
  >> EVAL_TAC
QED

Theorem fmp_positive_ctx_functions:
  fmp_positive_ctx.ctx_functions =
    [fmp_positive_entry; fmp_positive_callee]
Proof
  EVAL_TAC
QED

Theorem fmp_positive_all_invoke_layouts_wf:
  !fn inst.
    MEM fn fmp_positive_ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
    invoke_layout_wf fmp_positive_ctx inst
Proof
  rpt strip_tac
  >> gvs[fmp_positive_ctx_functions]
  >> gvs[fmp_positive_entry_insts, fmp_positive_callee_insts]
  >> simp[fmp_positive_invoke_layout_wf, invoke_layout_wf_def,
          venomInstTheory.mk_inst_def]
QED

Theorem fmp_positive_signature_fields:
  fmp_positive_entry.fn_fmp_signature = SOME fmp_positive_entry_sig /\
  fmp_positive_callee.fn_fmp_signature = SOME fmp_positive_callee_sig
Proof
  EVAL_TAC
QED

Theorem fmp_positive_entry_signature_wf:
  fmp_signature_matches_fn fmp_positive_ctx fmp_positive_entry
Proof
  simp[fmp_signature_matches_fn_def,
       cj 1 fmp_positive_signature_fields,
       fmp_positive_entry_syntax_wf, fmp_positive_entry_runner_wf]
QED

Theorem fmp_positive_callee_signature_wf:
  fmp_signature_matches_fn fmp_positive_ctx fmp_positive_callee
Proof
  simp[fmp_signature_matches_fn_def,
       cj 2 fmp_positive_signature_fields,
       fmp_positive_callee_syntax_wf, fmp_positive_callee_runner_wf]
QED

Theorem fmp_positive_all_signatures_wf:
  !fn. MEM fn fmp_positive_ctx.ctx_functions ==>
    fmp_signature_matches_fn fmp_positive_ctx fn
Proof
  simp[fmp_positive_ctx_functions]
  >> metis_tac[fmp_positive_entry_signature_wf,
               fmp_positive_callee_signature_wf]
QED

Theorem fmp_positive_context_wf:
  fmp_lowered_context_wf fmp_positive_ctx
Proof
  simp[fmp_lowered_context_wf_def, fmp_positive_static_layout_wf,
       fmp_positive_function_basics_wf, fmp_positive_all_signatures_wf]
  >> MATCH_ACCEPT_TAC fmp_positive_all_invoke_layouts_wf
QED

Theorem fmp_positive_boundary_eval:
  fmp_signature_matches_fn fmp_positive_ctx fmp_positive_entry /\
  fmp_signature_matches_fn fmp_positive_ctx fmp_positive_callee /\
  invoke_layout_wf fmp_positive_ctx fmp_positive_invoke /\
  fmp_lowered_context_wf fmp_positive_ctx
Proof
  simp[fmp_positive_entry_signature_wf,
       fmp_positive_callee_signature_wf,
       fmp_positive_invoke_layout_wf, fmp_positive_context_wf]
QED

(* Closed negative fixtures: each changes one relevant root or seal condition. *)
Definition fmp_bad_nonentry_initial_fn_def:
  fmp_bad_nonentry_initial_fn =
    mk_raw_function "bad_nonentry_initial"
      [<| bb_label := "entry";
          bb_instructions := [mk_inst 40 INITIAL_FMP [] ["x"]] |>]
End

Definition fmp_bad_nonentry_initial_ctx_def:
  fmp_bad_nonentry_initial_ctx =
    mk_venom_context [fmp_bad_nonentry_initial_fn] NONE
End

Definition fmp_bad_entry_param_sig_def:
  fmp_bad_entry_param_sig =
    <| fms_has_fmp_param := T; fms_publishes := F |>
End

Definition fmp_bad_entry_param_fn_def:
  fmp_bad_entry_param_fn =
    (mk_raw_function "bad_entry_param"
      [<| bb_label := "entry";
          bb_instructions := [mk_inst 41 FMP_PARAM [Lit 0w] ["x"]] |>])
      with fn_fmp_signature := SOME fmp_bad_entry_param_sig
End

Definition fmp_bad_entry_param_ctx_def:
  fmp_bad_entry_param_ctx =
    mk_venom_context [fmp_bad_entry_param_fn] (SOME "bad_entry_param")
End

Theorem fmp_malformed_root_rejections_eval:
  ~fmp_value_rooted fmp_bad_nonentry_initial_ctx fmp_positive_entry_sig
     fmp_bad_nonentry_initial_fn "x" /\
  ~fmp_value_rooted fmp_bad_entry_param_ctx fmp_bad_entry_param_sig
     fmp_bad_entry_param_fn "x"
Proof
  EVAL_TAC >> simp[]
QED

Definition fmp_hidden_mismatch_sig_def:
  fmp_hidden_mismatch_sig =
    <| fms_has_fmp_param := F; fms_publishes := T |>
End

Definition fmp_hidden_mismatch_fn_def:
  fmp_hidden_mismatch_fn =
    fmp_positive_callee with
      fn_fmp_signature := SOME fmp_hidden_mismatch_sig
End

Definition fmp_positive_callee_explicit_abi_def:
  fmp_positive_callee_explicit_abi =
    fmp_positive_callee with fn_call_abi :=
      (fmp_positive_callee.fn_call_abi with
         ica_user_return_count := SOME 1)
End

Definition fmp_publish_mismatch_sig_def:
  fmp_publish_mismatch_sig =
    <| fms_has_fmp_param := T; fms_publishes := F |>
End

Definition fmp_publish_mismatch_fn_def:
  fmp_publish_mismatch_fn =
    fmp_positive_callee_explicit_abi with
      fn_fmp_signature := SOME fmp_publish_mismatch_sig
End

Definition fmp_absent_seal_fn_def:
  fmp_absent_seal_fn =
    fmp_positive_callee with fn_fmp_signature := NONE
End

Theorem fmp_malformed_seal_rejections_eval:
  ~fmp_seal_layout_matches_fn fmp_hidden_mismatch_fn
     fmp_hidden_mismatch_sig /\
  fmp_seal_layout_matches_fn fmp_positive_callee_explicit_abi
     fmp_positive_callee_sig /\
  ~fmp_seal_layout_matches_fn fmp_publish_mismatch_fn
     fmp_publish_mismatch_sig /\
  ~call_abi_matches_fn fmp_absent_seal_fn
Proof
  EVAL_TAC
QED


Definition fmp_dangling_invoke_def:
  fmp_dangling_invoke =
    mk_inst 50 INVOKE
      [Label "missing"; Lit 7w; Var "minus"] ["user_out"; "published"]
End

Definition fmp_short_input_invoke_def:
  fmp_short_input_invoke =
    mk_inst 51 INVOKE
      [Label "callee"; Var "minus"] ["user_out"; "published"]
End

Definition fmp_short_output_invoke_def:
  fmp_short_output_invoke =
    mk_inst 52 INVOKE
      [Label "callee"; Lit 7w; Var "minus"] ["user_out"]
End

Theorem fmp_positive_lookup_facts:
  lookup_function "callee" fmp_positive_ctx.ctx_functions =
    SOME fmp_positive_callee /\
  lookup_function "missing" fmp_positive_ctx.ctx_functions = NONE
Proof
  EVAL_TAC
QED

Theorem fmp_malformed_invoke_arity_facts:
  ~invoke_input_arity_ok fmp_positive_callee fmp_positive_callee_sig
     fmp_short_input_invoke /\
  ~fmp_invoke_output_arity_ok fmp_positive_callee fmp_positive_callee_sig
     fmp_short_output_invoke
Proof
  EVAL_TAC
QED

Theorem fmp_malformed_invoke_layout_rejections_eval:
  ~invoke_layout_wf fmp_positive_ctx fmp_dangling_invoke /\
  ~invoke_layout_wf fmp_positive_ctx fmp_short_input_invoke /\
  ~invoke_layout_wf fmp_positive_ctx fmp_short_output_invoke
Proof
  simp[invoke_layout_wf_def, fmp_dangling_invoke_def,
       fmp_short_input_invoke_def, fmp_short_output_invoke_def,
       venomInstTheory.mk_inst_def, fmp_positive_lookup_facts,
       fmp_seal_layout_matches_fn_def, fmp_positive_signature_fields,
       fmp_positive_callee_syntax_wf, fmp_malformed_invoke_arity_facts]
  >> EVAL_TAC
QED

Definition fmp_unrooted_hidden_invoke_def:
  fmp_unrooted_hidden_invoke =
    mk_inst 53 INVOKE
      [Label "callee"; Lit 7w; Var "ghost"] ["user_out"; "published"]
End

Definition fmp_unrooted_hidden_caller_def:
  fmp_unrooted_hidden_caller =
    (mk_raw_function "bad_hidden_caller"
      [<| bb_label := "entry";
          bb_instructions := [fmp_unrooted_hidden_invoke] |>]) with <|
      fn_eom := SOME 0;
      fn_fmp_signature := SOME fmp_positive_entry_sig
    |>
End

Definition fmp_unrooted_hidden_ctx_def:
  fmp_unrooted_hidden_ctx =
    mk_venom_context
      [fmp_unrooted_hidden_caller; fmp_positive_callee]
      (SOME "bad_hidden_caller")
End

Theorem fmp_unrooted_hidden_lookup:
  lookup_function "callee" fmp_unrooted_hidden_ctx.ctx_functions =
    SOME fmp_positive_callee
Proof
  EVAL_TAC
QED

Theorem fmp_unrooted_hidden_layout_wf:
  invoke_layout_wf fmp_unrooted_hidden_ctx fmp_unrooted_hidden_invoke
Proof
  simp[invoke_layout_wf_def, fmp_unrooted_hidden_invoke_def,
       venomInstTheory.mk_inst_def]
  >> qexistsl [`fmp_positive_callee`, `fmp_positive_callee_sig`]
  >> conj_tac >- simp[fmp_unrooted_hidden_lookup]
  >> conj_tac >-
    simp[fmp_seal_layout_matches_fn_def,
         cj 2 fmp_positive_signature_fields,
         fmp_positive_callee_syntax_wf]
  >> conj_tac >- EVAL_TAC
  >> EVAL_TAC
QED

Theorem fmp_unrooted_hidden_value_rejected:
  ~fmp_value_rooted fmp_unrooted_hidden_ctx fmp_positive_entry_sig
     fmp_unrooted_hidden_caller "ghost"
Proof
  EVAL_TAC >> simp[]
QED

Theorem fmp_unrooted_hidden_invoke_facts:
  fmp_unrooted_hidden_invoke.inst_opcode = INVOKE /\
  fmp_unrooted_hidden_invoke.inst_operands =
    [Label "callee"; Lit 7w; Var "ghost"] /\
  invoke_input_arity_ok fmp_positive_callee fmp_positive_callee_sig
    fmp_unrooted_hidden_invoke /\
  fmp_invoke_output_arity_ok fmp_positive_callee fmp_positive_callee_sig
    fmp_unrooted_hidden_invoke /\
  fmp_positive_callee_sig.fms_has_fmp_param /\
  EL (LENGTH (fn_user_param_insts fmp_positive_callee))
    [Lit 7w; Var "ghost"] = Var "ghost"
Proof
  EVAL_TAC
QED

Theorem fmp_unrooted_hidden_rejection_eval:
  invoke_layout_wf fmp_unrooted_hidden_ctx fmp_unrooted_hidden_invoke /\
  ~fmp_runner_inst_wf fmp_unrooted_hidden_ctx fmp_positive_entry_sig
     fmp_unrooted_hidden_caller fmp_unrooted_hidden_invoke
Proof
  simp[fmp_unrooted_hidden_layout_wf, fmp_runner_inst_wf_def,
       fmp_bump_consumer_wf_def, fmp_invoke_consumer_wf_def,
       fmp_return_consumer_wf_def, fmp_unrooted_hidden_invoke_facts,
       fmp_unrooted_hidden_lookup, fmp_seal_layout_matches_fn_def,
       cj 2 fmp_positive_signature_fields,
       fmp_positive_callee_syntax_wf, fmp_unrooted_hidden_value_rejected]
QED
Definition fmp_unrooted_adopted_fn_def:
  fmp_unrooted_adopted_fn =
    (mk_raw_function "bad_adopted"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 60 PARAM [Lit 0w] ["cu"];
             mk_inst 61 FMP_PARAM [Lit 1w] ["cfmp"];
             mk_inst 62 RETPC_PARAM [Lit 2w] ["crpc"];
             mk_inst 63 ADD [Var "cfmp"; Lit 1w] ["cadopt"];
             mk_inst 64 RET [Var "cu"; Var "ghost"; Var "crpc"] []] |>])
      with <| fn_eom := SOME 0;
              fn_fmp_signature := SOME fmp_positive_callee_sig |>
End

Definition fmp_unrooted_adopted_ctx_def:
  fmp_unrooted_adopted_ctx =
    mk_venom_context [fmp_unrooted_adopted_fn] NONE
End

Definition fmp_unrooted_adopted_ret_def:
  fmp_unrooted_adopted_ret =
    mk_inst 64 RET [Var "cu"; Var "ghost"; Var "crpc"] []
End

Theorem fmp_unrooted_adopted_rejection_eval:
  fmp_signature_syntax_wf fmp_positive_callee_sig
    fmp_unrooted_adopted_fn /\
  ~fmp_runner_inst_wf fmp_unrooted_adopted_ctx
     fmp_positive_callee_sig fmp_unrooted_adopted_fn
     fmp_unrooted_adopted_ret
Proof
  EVAL_TAC >> simp[venomInstTheory.operand_var_def]
QED

Definition fmp_misordered_return_fn_def:
  fmp_misordered_return_fn =
    (mk_raw_function "bad_return_order"
      [<| bb_label := "entry";
          bb_instructions :=
            [mk_inst 65 PARAM [Lit 0w] ["cu"];
             mk_inst 66 FMP_PARAM [Lit 1w] ["cfmp"];
             mk_inst 67 RETPC_PARAM [Lit 2w] ["crpc"];
             mk_inst 68 ADD [Var "cfmp"; Lit 1w] ["cadopt"];
             mk_inst 69 RET [Var "cu"; Var "crpc"; Var "cadopt"] []] |>])
      with <| fn_eom := SOME 0;
              fn_fmp_signature := SOME fmp_positive_callee_sig |>
End

Definition fmp_misordered_return_ctx_def:
  fmp_misordered_return_ctx =
    mk_venom_context [fmp_misordered_return_fn] NONE
End

Definition fmp_misordered_return_inst_def:
  fmp_misordered_return_inst =
    mk_inst 69 RET [Var "cu"; Var "crpc"; Var "cadopt"] []
End

Definition fmp_bad_abi_return_fn_def:
  fmp_bad_abi_return_fn =
    fmp_positive_callee with fn_call_abi :=
      (fmp_positive_callee.fn_call_abi with
         ica_user_return_count := SOME 2)
End

Theorem fmp_malformed_return_layout_rejections_eval:
  ~lowered_return_inst_layout_wf T 1
     (mk_inst 70 RET [Var "u"; Var "rpc"] []) /\
  ~lowered_return_inst_layout_wf T 1
     (mk_inst 71 RET [Var "u"; Var "a"; Var "x"; Var "rpc"] []) /\
  ~lowered_return_inst_layout_wf F 1
     (mk_inst 72 RET [Var "rpc"] []) /\
  lowered_return_inst_layout_wf T 1 fmp_misordered_return_inst /\
  ~fmp_runner_inst_wf fmp_misordered_return_ctx
     fmp_positive_callee_sig fmp_misordered_return_fn
     fmp_misordered_return_inst /\
  ~fmp_return_abi_matches fmp_positive_callee_sig fmp_bad_abi_return_fn
Proof
  EVAL_TAC >> simp[venomInstTheory.operand_var_def]
QED

Definition fmp_missing_eom_fn_def:
  fmp_missing_eom_fn =
    fmp_positive_entry with fn_eom := NONE
End

Definition fmp_missing_eom_ctx_def:
  fmp_missing_eom_ctx =
    mk_venom_context [fmp_missing_eom_fn] (SOME "entry")
End

Definition fmp_unconcretized_static_fn_def:
  fmp_unconcretized_static_fn =
    (mk_raw_function "bad_static"
      [<| bb_label := "entry";
          bb_instructions := [mk_inst 80 ALLOCA [Lit 32w] ["slot"]] |>])
      with <| fn_eom := SOME 0;
              fn_fmp_signature := SOME fmp_positive_entry_sig |>
End

Definition fmp_unconcretized_static_ctx_def:
  fmp_unconcretized_static_ctx =
    mk_venom_context [fmp_unconcretized_static_fn] (SOME "bad_static")
End

Theorem fmp_missing_eom_static_rejection:
  ~concretized_static_layouts_wf fmp_missing_eom_ctx
Proof
  simp[staticLayoutWfTheory.concretized_static_layouts_wf_def,
       fmp_missing_eom_ctx_def,
       venomInstTheory.mk_venom_context_def, fmp_missing_eom_fn_def]
QED

Theorem fmp_unconcretized_static_layout_rejection:
  ~concretized_static_layouts_wf fmp_unconcretized_static_ctx
Proof
  EVAL_TAC >> simp[venomInstTheory.fn_insts_blocks_def]
QED

Theorem fmp_eom_and_static_rejections_eval:
  ~concretized_static_layouts_wf fmp_missing_eom_ctx /\
  ~fmp_lowered_context_wf fmp_missing_eom_ctx /\
  ~concretized_static_layouts_wf fmp_unconcretized_static_ctx /\
  ~fmp_lowered_context_wf fmp_unconcretized_static_ctx
Proof
  simp[fmp_missing_eom_static_rejection,
       fmp_unconcretized_static_layout_rejection,
       fmp_lowered_context_wf_def]
QED
val _ = export_theory();
