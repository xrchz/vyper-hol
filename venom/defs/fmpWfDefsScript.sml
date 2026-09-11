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

(* Current lowered returns have a signature-dependent physical suffix: RETPC
 * alone for non-publishing functions, and adopted FMP followed by RETPC for
 * publishing functions.  This boundary is separate from raw return arity,
 * which intentionally does not know the FMP signature. *)
Definition fmp_current_return_user_arity_def:
  fmp_current_return_user_arity sig inst =
    if inst.inst_opcode <> RET then NONE
    else
      let overhead = if sig.fms_publishes then 2 else 1 in
      if overhead <= LENGTH inst.inst_operands then
        SOME (LENGTH inst.inst_operands - overhead)
      else NONE
End

Definition fmp_unique_return_arity_def:
  fmp_unique_return_arity sig fn =
    case fn_return_insts fn of
      [] => NONE
    | first::rest =>
        case fmp_current_return_user_arity sig first of
          NONE => NONE
        | SOME n =>
            if EVERY
                 (\inst. fmp_current_return_user_arity sig inst = SOME n)
                 rest
            then SOME n
            else NONE
End

Definition fmp_expected_user_return_arity_def:
  fmp_expected_user_return_arity sig fn =
    case fn.fn_call_abi.ica_user_return_count of
      SOME n => SOME n
    | NONE => fmp_unique_return_arity sig fn
End

Definition fmp_return_abi_matches_def:
  fmp_return_abi_matches sig fn <=>
    case fn_return_insts fn of
      [] =>
        (fn.fn_call_abi.ica_has_memory_return_buffer = SOME T ==>
         fn_memory_return_buffer_param fn <> NONE)
    | _ =>
        case fmp_unique_return_arity sig fn of
          NONE => F
        | SOME n =>
            (fn.fn_call_abi.ica_user_return_count = NONE \/
             fn.fn_call_abi.ica_user_return_count = SOME n) /\
            (fn.fn_call_abi.ica_has_memory_return_buffer = SOME T ==>
             fn_memory_return_buffer_param fn <> NONE)
End

Definition fmp_invoke_output_arity_ok_def:
  fmp_invoke_output_arity_ok callee sig inst <=>
    inst.inst_opcode = INVOKE /\
    (case inst.inst_operands of Label callee_name::args => T | _ => F) /\
    case fmp_expected_user_return_arity sig callee of
      NONE => F
    | SOME n =>
        LENGTH inst.inst_outputs =
          n + (if sig.fms_publishes then 1 else 0)
End

Definition fmp_lowered_return_layout_wf_def:
  fmp_lowered_return_layout_wf sig fn <=>
    case fn_return_insts fn of
      [] => T
    | returns =>
        case fmp_expected_user_return_arity sig fn of
          NONE => F
        | SOME n =>
            EVERY (lowered_return_inst_layout_wf sig.fms_publishes n) returns
End

(* This is the non-recursive part of validating a seal against current syntax.
 * Rooted runner flow is deliberately added by fmp_signature_matches_fn below. *)
Definition fmp_signature_syntax_wf_def:
  fmp_signature_syntax_wf sig fn <=>
    canonical_param_prefix fn /\
    IS_SOME (fn_hidden_fmp_param fn) = sig.fms_has_fmp_param /\
    fmp_return_abi_matches sig fn /\
    fmp_lowered_return_layout_wf sig fn
End

Definition call_abi_matches_fn_def:
  call_abi_matches_fn fn <=>
    case fn.fn_fmp_signature of
      NONE => F
    | SOME sig =>
        canonical_param_prefix fn /\ fmp_return_abi_matches sig fn
End

Definition fmp_seal_layout_matches_fn_def:
  fmp_seal_layout_matches_fn fn sig <=>
    fn.fn_fmp_signature = SOME sig /\
    fmp_signature_syntax_wf sig fn
End

Definition invoke_layout_wf_def:
  invoke_layout_wf ctx inst <=>
    inst.inst_opcode = INVOKE ==>
    ?callee_name args callee sig.
      inst.inst_operands = Label callee_name::args /\
      lookup_function callee_name ctx.ctx_functions = SOME callee /\
      fmp_seal_layout_matches_fn callee sig /\
      invoke_input_arity_ok callee sig inst /\
      fmp_invoke_output_arity_ok callee sig inst
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
      fmp_invoke_output_arity_ok callee sig inst
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
        fmp_invoke_output_arity_ok callee callee_sig inst /\
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
        fmp_expected_user_return_arity sig fn = SOME n /\
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

Definition fmp_signature_matches_fn_def:
  fmp_signature_matches_fn ctx fn <=>
    case fn.fn_fmp_signature of
      NONE => F
    | SOME sig =>
        fmp_signature_syntax_wf sig fn /\
        fmp_runner_rooted_wf ctx sig fn
End

Definition fmp_lowered_context_wf_def:
  fmp_lowered_context_wf ctx <=>
    concretized_static_layouts_wf ctx /\
    (!fn. MEM fn ctx.ctx_functions ==>
      IS_SOME fn.fn_eom /\
      no_raw_fmp_ops fn /\
      call_abi_matches_fn fn /\
      fmp_signature_matches_fn ctx fn) /\
    (!fn inst.
      MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) ==>
      invoke_layout_wf ctx inst)
End

(* ==========================================================================
   Executable views of finite FMP well-formedness checks.
   ========================================================================== *)

Theorem no_raw_fmp_ops_compute[compute]:
  no_raw_fmp_ops fn <=>
    EVERY (λinst. ~is_raw_fmp_opcode inst.inst_opcode) (fn_insts fn)
Proof
  simp[venomInstTheory.no_raw_fmp_ops_def, listTheory.EVERY_MEM]
QED

Theorem invoke_input_arity_ok_compute[compute]:
  invoke_input_arity_ok callee sig inst <=>
    inst.inst_opcode = INVOKE /\
    inst.inst_operands <> [] /\
    IS_SOME (get_label (HD inst.inst_operands)) /\
    LENGTH (TL inst.inst_operands) =
      LENGTH (fn_user_param_insts callee) +
        (if sig.fms_has_fmp_param then 1 else 0)
Proof
  Cases_on `inst.inst_operands` >>
  simp[callLayoutDefsTheory.invoke_input_arity_ok_def] >>
  Cases_on `h` >> simp[venomStateTheory.get_label_def]
QED

Theorem fmp_invoke_output_arity_ok_compute[compute]:
  fmp_invoke_output_arity_ok callee sig inst <=>
    inst.inst_opcode = INVOKE /\
    inst.inst_operands <> [] /\
    IS_SOME (get_label (HD inst.inst_operands)) /\
    case fmp_expected_user_return_arity sig callee of
      NONE => F
    | SOME n =>
        LENGTH inst.inst_outputs =
          n + (if sig.fms_publishes then 1 else 0)
Proof
  Cases_on `inst.inst_operands` >>
  simp[fmp_invoke_output_arity_ok_def] >>
  Cases_on `h` >> simp[venomStateTheory.get_label_def]
QED

Definition invoke_layout_wf_exec_def:
  invoke_layout_wf_exec ctx inst =
    if inst.inst_opcode <> INVOKE then T
    else if inst.inst_operands = [] then F
    else
      case get_label (HD inst.inst_operands) of
        NONE => F
      | SOME callee_name =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => F
          | SOME callee =>
              case callee.fn_fmp_signature of
                NONE => F
              | SOME sig =>
                  fmp_signature_syntax_wf sig callee /\
                  invoke_input_arity_ok callee sig inst /\
                  fmp_invoke_output_arity_ok callee sig inst
End

Theorem invoke_layout_wf_compute[compute]:
  invoke_layout_wf ctx inst <=> invoke_layout_wf_exec ctx inst
Proof
  Cases_on `inst.inst_opcode = INVOKE` >>
  simp[invoke_layout_wf_def, invoke_layout_wf_exec_def,
       fmp_seal_layout_matches_fn_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[venomStateTheory.get_label_def] >>
  Cases_on `lookup_function s ctx.ctx_functions` >> simp[] >>
  Cases_on `x.fn_fmp_signature` >> simp[]
QED

Definition publishing_invoke_wf_exec_def:
  publishing_invoke_wf_exec ctx inst =
    if inst.inst_opcode <> INVOKE then F
    else if inst.inst_operands = [] then F
    else
      case get_label (HD inst.inst_operands) of
        NONE => F
      | SOME callee_name =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => F
          | SOME callee =>
              case callee.fn_fmp_signature of
                NONE => F
              | SOME sig =>
                  fmp_signature_syntax_wf sig callee /\
                  sig.fms_publishes /\
                  invoke_input_arity_ok callee sig inst /\
                  fmp_invoke_output_arity_ok callee sig inst
End

Theorem publishing_invoke_wf_compute[compute]:
  publishing_invoke_wf ctx inst <=> publishing_invoke_wf_exec ctx inst
Proof
  Cases_on `inst.inst_opcode = INVOKE` >>
  simp[publishing_invoke_wf_def, publishing_invoke_wf_exec_def,
       fmp_seal_layout_matches_fn_def,
       callLayoutDefsTheory.invoke_input_arity_ok_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[venomStateTheory.get_label_def] >>
  Cases_on `lookup_function s ctx.ctx_functions` >> simp[] >>
  Cases_on `x.fn_fmp_signature` >> simp[]
QED

Definition fmp_inst_roots_exec_def:
  fmp_inst_roots_exec ctx sig fn rooted v inst =
    case inst.inst_opcode of
      INITIAL_FMP =>
        fn_is_context_entry ctx fn /\
        inst.inst_operands = [] /\ inst.inst_outputs = [v]
    | FMP_PARAM =>
        ~fn_is_context_entry ctx fn /\ sig.fms_has_fmp_param /\
        LENGTH inst.inst_operands = 1 /\ inst.inst_outputs = [v]
    | ASSIGN =>
        (case inst.inst_operands of
           [Var src] => inst.inst_outputs = [v] /\ rooted src
         | _ => F)
    | PHI =>
        inst.inst_outputs = [v] /\
        operand_vars inst.inst_operands <> [] /\
        2 * LENGTH (phi_pairs inst.inst_operands) =
          LENGTH inst.inst_operands /\
        EVERY rooted (operand_vars inst.inst_operands)
    | BUMP =>
        (case inst.inst_operands of
           [Var root_var; size_op] =>
             (case inst.inst_outputs of
                [old_var; new_var] =>
                  (v = old_var \/ v = new_var) /\ rooted root_var
              | _ => F)
         | _ => F)
    | ADD =>
        LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = [v] /\
        EXISTS rooted (operand_vars inst.inst_operands)
    | SUB =>
        LENGTH inst.inst_operands = 2 /\ inst.inst_outputs = [v] /\
        EXISTS rooted (operand_vars inst.inst_operands)
    | INVOKE =>
        publishing_invoke_wf ctx inst /\
        inst.inst_outputs <> [] /\ v = LAST inst.inst_outputs
    | _ => F
End

val fmp_inst_roots_opcode_tac =
  simp[fmp_inst_roots_def, fmp_inst_roots_exec_def,
       publishing_invoke_wf_compute, publishing_invoke_wf_exec_def];

Theorem fmp_inst_roots_compute[compute]:
  fmp_inst_roots ctx sig fn rooted v inst <=>
  fmp_inst_roots_exec ctx sig fn rooted v inst
Proof
  Cases_on `inst.inst_opcode` >|
    [(* 1-5 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 6-10 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 11-15 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 16-20 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 21-25 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 26-30 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 31-35 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 36-40 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 41-45 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 46-50 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 51-55 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 56-60 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 61-65 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 66-70 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 71-75 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 76-80 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 81-85 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 86-90 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 91-95 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     (* 96-100 *) fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac, fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac,
     fmp_inst_roots_opcode_tac] >> (* 101 *)
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Definition fmp_bump_consumer_wf_exec_def:
  fmp_bump_consumer_wf_exec ctx sig fn inst =
    if inst.inst_opcode <> BUMP then T
    else
      case inst.inst_operands of
        [Var root_var; size_op] =>
          (case inst.inst_outputs of
             [old_var; new_var] => fmp_value_rooted ctx sig fn root_var
           | _ => F)
      | _ => F
End

Theorem fmp_bump_consumer_wf_compute[compute]:
  fmp_bump_consumer_wf ctx sig fn inst <=>
  fmp_bump_consumer_wf_exec ctx sig fn inst
Proof
  Cases_on `inst.inst_opcode = BUMP` >>
  simp[fmp_bump_consumer_wf_def, fmp_bump_consumer_wf_exec_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `h` >> simp[] >>
  Cases_on `t'` >> simp[] >>
  Cases_on `inst.inst_outputs` >> simp[] >>
  Cases_on `t` >> simp[] >>
  Cases_on `t'` >> simp[]
QED

Definition fmp_invoke_consumer_wf_exec_def:
  fmp_invoke_consumer_wf_exec ctx caller_sig fn inst =
    if inst.inst_opcode <> INVOKE then T
    else if inst.inst_operands = [] then F
    else
      case get_label (HD inst.inst_operands) of
        NONE => F
      | SOME callee_name =>
          case lookup_function callee_name ctx.ctx_functions of
            NONE => F
          | SOME callee =>
              case callee.fn_fmp_signature of
                NONE => F
              | SOME callee_sig =>
                  fmp_signature_syntax_wf callee_sig callee /\
                  invoke_input_arity_ok callee callee_sig inst /\
                  fmp_invoke_output_arity_ok callee callee_sig inst /\
                  (if callee_sig.fms_has_fmp_param then
                     case operand_var
                       (EL (LENGTH (fn_user_param_insts callee))
                         (TL inst.inst_operands)) of
                       NONE => F
                     | SOME hidden =>
                         fmp_value_rooted ctx caller_sig fn hidden
                   else T)
End

Theorem fmp_invoke_consumer_wf_compute[compute]:
  fmp_invoke_consumer_wf ctx caller_sig fn inst <=>
  fmp_invoke_consumer_wf_exec ctx caller_sig fn inst
Proof
  Cases_on `inst.inst_opcode = INVOKE` >>
  simp[fmp_invoke_consumer_wf_def, fmp_invoke_consumer_wf_exec_def,
       fmp_seal_layout_matches_fn_def] >>
  Cases_on `inst.inst_operands` >> simp[] >>
  Cases_on `h` >> simp[venomStateTheory.get_label_def] >>
  Cases_on `lookup_function s ctx.ctx_functions` >> simp[] >>
  Cases_on `x.fn_fmp_signature` >> simp[] >>
  Cases_on `x'.fms_has_fmp_param` >> simp[] >>
  Cases_on `EL (LENGTH (fn_user_param_insts x)) t` >>
  simp[venomInstTheory.operand_var_def]
QED

Definition fmp_return_consumer_wf_exec_def:
  fmp_return_consumer_wf_exec ctx sig fn inst =
    if inst.inst_opcode <> RET \/ ~sig.fms_publishes then T
    else
      case fmp_expected_user_return_arity sig fn of
        NONE => F
      | SOME n =>
          lowered_return_inst_layout_wf T n inst /\
          case operand_var (EL n inst.inst_operands) of
            NONE => F
          | SOME adopted => fmp_value_rooted ctx sig fn adopted
End

Theorem fmp_return_consumer_wf_compute[compute]:
  fmp_return_consumer_wf ctx sig fn inst <=>
  fmp_return_consumer_wf_exec ctx sig fn inst
Proof
  Cases_on `inst.inst_opcode = RET` >>
  Cases_on `sig.fms_publishes` >>
  simp[fmp_return_consumer_wf_def, fmp_return_consumer_wf_exec_def] >>
  Cases_on `fmp_expected_user_return_arity sig fn` >> simp[] >>
  Cases_on `operand_var (EL x inst.inst_operands)` >> simp[]
QED

Theorem fmp_lowered_context_wf_compute[compute]:
  fmp_lowered_context_wf ctx <=>
    concretized_static_layouts_wf ctx /\
    EVERY
      (λfn. IS_SOME fn.fn_eom /\
            no_raw_fmp_ops fn /\
            call_abi_matches_fn fn /\
            fmp_signature_matches_fn ctx fn)
      ctx.ctx_functions /\
    EVERY (λfn. EVERY (invoke_layout_wf ctx) (fn_insts fn))
      ctx.ctx_functions
Proof
  simp[fmp_lowered_context_wf_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

val _ = export_theory();
