(* Temporary checked trace vehicle for the no-argument internal-call fixture. *)
Theory evalInternalCallTrace
Ancestors evalCompiler compileVyper concretizeMemLocDefs alist byte integer_word option
Libs finite_mapLib computeLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

Definition trace_rpolicy_def:
  trace_rpolicy =
    <| rpol_target := prague_capabilities;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>
End

val internal_call_runtime_lowering_partial =
  EVAL ``lower_vyper_runtime_unit internal_call_program trace_rpolicy``
val internal_call_runtime_lowering_simplified =
  SIMP_RULE (srw_ss())
    [finite_mapTheory.FEVERY_FEMPTY,
     venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
    internal_call_runtime_lowering_partial
val internal_call_runtime_lowering_eval =
  CONV_RULE (RAND_CONV computeLib.EVAL_CONV)
    internal_call_runtime_lowering_simplified

Definition internal_call_raw_unit_def:
  internal_call_raw_unit =
    ^(optionSyntax.dest_some
        (rhs (concl internal_call_runtime_lowering_eval)))
End

Theorem internal_call_runtime_lowering_exact:
  lower_vyper_runtime_unit internal_call_program trace_rpolicy =
    SOME internal_call_raw_unit
Proof
  pure_rewrite_tac[internal_call_raw_unit_def] >>
  ACCEPT_TAC internal_call_runtime_lowering_eval
QED

val internal_call_context_concretize_partial =
  EVAL
    ``concretize_context_eval
        (^(optionSyntax.dest_some
            (rhs (concl internal_call_runtime_lowering_eval)))).cu_context``
val internal_call_context_concretize_simplified =
  SIMP_RULE (srw_ss())
    [finite_mapTheory.FEVERY_FEMPTY,
     venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
    internal_call_context_concretize_partial
val internal_call_context_concretize_eval =
  CONV_RULE (RAND_CONV computeLib.EVAL_CONV)
    internal_call_context_concretize_simplified

Definition internal_call_trace_context_def:
  internal_call_trace_context =
    ^(optionSyntax.dest_some
        (rhs (concl internal_call_context_concretize_eval)))
End

Theorem internal_call_context_concretize_exact:
  concretize_context_eval internal_call_raw_unit.cu_context =
    SOME internal_call_trace_context
Proof
  pure_rewrite_tac[internal_call_raw_unit_def,
                   internal_call_trace_context_def] >>
  CONV_TAC (LHS_CONV (RAND_CONV computeLib.EVAL_CONV)) >>
  ACCEPT_TAC internal_call_context_concretize_eval
QED

Theorem internal_call_trace_context_provenance:
  ?raw_unit.
    lower_vyper_runtime_unit internal_call_program trace_rpolicy = SOME raw_unit /\
    concretize_context_eval raw_unit.cu_context = SOME internal_call_trace_context
Proof
  qexists `internal_call_raw_unit` >>
  simp[internal_call_runtime_lowering_exact,
       internal_call_context_concretize_exact]
QED


(* One-argument fixture: retain the exact lowered/concretized context and
   inspect only the already-localized second function. *)
val internal_call_arg_runtime_lowering_partial =
  EVAL ``lower_vyper_runtime_unit internal_call_arg_program trace_rpolicy``
val internal_call_arg_runtime_lowering_simplified =
  SIMP_RULE (srw_ss())
    [finite_mapTheory.FEVERY_FEMPTY,
     venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
    internal_call_arg_runtime_lowering_partial
val internal_call_arg_runtime_lowering_eval =
  CONV_RULE (RAND_CONV computeLib.EVAL_CONV)
    internal_call_arg_runtime_lowering_simplified

Definition internal_call_arg_raw_unit_def:
  internal_call_arg_raw_unit =
    ^(optionSyntax.dest_some
        (rhs (concl internal_call_arg_runtime_lowering_eval)))
End

val internal_call_arg_context_concretize_partial =
  EVAL
    ``concretize_context_eval
        (^(optionSyntax.dest_some
            (rhs (concl internal_call_arg_runtime_lowering_eval)))).cu_context``
val internal_call_arg_context_concretize_simplified =
  SIMP_RULE (srw_ss())
    [finite_mapTheory.FEVERY_FEMPTY,
     venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
    internal_call_arg_context_concretize_partial
val internal_call_arg_context_concretize_eval =
  CONV_RULE (RAND_CONV computeLib.EVAL_CONV)
    internal_call_arg_context_concretize_simplified

Definition internal_call_arg_trace_context_def:
  internal_call_arg_trace_context =
    ^(optionSyntax.dest_some
        (rhs (concl internal_call_arg_context_concretize_eval)))
End

Definition internal_call_arg_bar_def:
  internal_call_arg_bar = HD (TL internal_call_arg_trace_context.ctx_functions)
End

Theorem internal_call_arg_bar_not_canonical:
  ~canonical_param_prefix internal_call_arg_bar
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_bar_entry:
  fn_entry_label internal_call_arg_bar = SOME "bar"
Proof
  EVAL_TAC
QED

Theorem internal_call_arg_bar_fn_plan_none:
  generate_fn_plan_fuel 100000 internal_call_arg_bar 64 1 = NONE
Proof
  simp[stackPlanGenTheory.generate_fn_plan_fuel_def,
       internal_call_arg_bar_not_canonical]
QED

val _ = export_theory()
