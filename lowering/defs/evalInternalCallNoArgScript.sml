(* Focused exact evaluation for the no-argument internal-call fixture. *)
Theory evalInternalCallNoArg
Ancestors evalInternalCallTrace evalCompilerBytecodeDefs evalCompiler compileVyper concretizeMemLocDefs alist byte integer_word option
Libs evalCompilerBytecodeLib finite_mapLib computeLib wordsLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["bytecode"]

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset (computeLib.add_thms [fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset (computeLib.add_thms [i2w_pos])

Theorem fn_plan_fuel_success_stable[local]:
  (!fuel liveness dfg cfg fn worklist visited ps result extra.
    generate_fn_plan_aux_fuel fuel liveness dfg cfg fn worklist visited ps =
      SOME result ==>
    generate_fn_plan_aux_fuel (fuel + extra) liveness dfg cfg fn
      worklist visited ps = SOME result) /\
  (!fuel liveness dfg cfg fn ss sp succs visited ps result extra.
    generate_succs_plan_fuel fuel liveness dfg cfg fn ss sp succs visited ps =
      SOME result ==>
    generate_succs_plan_fuel (fuel + extra) liveness dfg cfg fn ss sp succs
      visited ps = SOME result)
Proof
  ho_match_mp_tac stackPlanGenTheory.generate_fn_plan_aux_fuel_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[Ntimes stackPlanGenTheory.generate_fn_plan_aux_fuel_def 2] >>
  rpt strip_tac >> BasicProvers.every_case_tac >> gvs[] >>
  simp[arithmeticTheory.ADD_CLAUSES,
       Once stackPlanGenTheory.generate_fn_plan_aux_fuel_def] >>
  metis_tac[]
QED

Theorem generate_fn_plan_aux_fuel_success_stable[local]:
  !fuel liveness dfg cfg fn worklist visited ps result extra.
    generate_fn_plan_aux_fuel fuel liveness dfg cfg fn worklist visited ps =
      SOME result ==>
    generate_fn_plan_aux_fuel (fuel + extra) liveness dfg cfg fn
      worklist visited ps = SOME result
Proof
  metis_tac[fn_plan_fuel_success_stable]
QED

val fn_plan_aux_fuel_tm = ``generate_fn_plan_aux_fuel``

fun rator_n_conv 0 conv = conv
  | rator_n_conv n conv = RATOR_CONV (rator_n_conv (n - 1) conv)

fun closed_fn_plan_aux_success_conv_with_fuels fuels tm =
  let
    val (head, args) = strip_comb tm
    val _ = if aconv head fn_plan_aux_fuel_tm andalso length args = 8
            then () else raise UNCHANGED
    val target_fuel = hd args
    val target_n = numSyntax.int_of_term target_fuel
    fun seek [] = raise Fail "no successful planner run within bounded fuel"
      | seek (n :: ns) =
          let
            val low_fuel = numSyntax.term_of_int n
            val low_tm = list_mk_comb (head, low_fuel :: tl args)
            val low_thm = computeLib.EVAL_CONV low_tm
            val low_rhs = rhs (concl low_thm)
          in
            if optionSyntax.is_some low_rhs then
              (n, low_fuel, low_thm, optionSyntax.dest_some low_rhs)
            else seek ns
          end
    val (n, low_fuel, low_thm, result) = seek fuels
    val _ = if n <= target_n then ()
            else raise Fail "successful probe fuel exceeds target fuel"
    val extra = numSyntax.term_of_int (target_n - n)
    val stable = SPECL (low_fuel :: tl args @ [result, extra])
      generate_fn_plan_aux_fuel_success_stable
    val lifted = MATCH_MP stable low_thm
    val normalized =
      CONV_RULE
        (LHS_CONV (rator_n_conv 7 (RAND_CONV computeLib.EVAL_CONV)))
        lifted
    val _ = if aconv (lhs (concl normalized)) tm then ()
            else raise Fail "lifted planner theorem does not match target"
  in
    normalized
  end

fun closed_compiler_eval_with_fuels fuels tm =
  let
    val partial = RESTR_EVAL_CONV [``generate_fn_plan_aux_fuel``] tm
    val partial_rhs = rhs (concl partial)
  in
    if optionSyntax.is_some partial_rhs orelse optionSyntax.is_none partial_rhs then
      partial
    else
      let
        val simplified =
          SIMP_RULE (srw_ss())
            [finite_mapTheory.FEVERY_FEMPTY,
             venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
            partial
        val staged =
          CONV_RULE
            (RAND_CONV (RESTR_EVAL_CONV [``generate_fn_plan_aux_fuel``]))
            simplified
        val planners =
          CONV_RULE
            (RAND_CONV
              (DEPTH_CONV (closed_fn_plan_aux_success_conv_with_fuels fuels)))
            staged
      in
        CONV_RULE (RAND_CONV computeLib.EVAL_CONV) planners
      end
  end

val internal_call_raw_unit_eval = EVAL ``internal_call_raw_unit``
val internal_call_runtime_pipeline_eval =
  closed_compiler_eval_with_fuels [100000]
    ``checked_unit_pipeline_fuel_for_testing 100000
        bytecode_unit_pipeline_for_testing
        bytecode_identity_finalizer_for_testing trace_rpolicy
        ^(rhs (concl internal_call_raw_unit_eval))``

Theorem internal_call_runtime_pipeline_exact:
  checked_unit_pipeline_fuel_for_testing 100000
    bytecode_unit_pipeline_for_testing
    bytecode_identity_finalizer_for_testing trace_rpolicy
    internal_call_raw_unit =
      ^(rhs (concl internal_call_runtime_pipeline_eval))
Proof
  rewrite_tac[internal_call_raw_unit_eval] >>
  ACCEPT_TAC internal_call_runtime_pipeline_eval
QED

val internal_call_runtime_pipeline_normalized =
  SIMP_RULE (srw_ss()) [] internal_call_runtime_pipeline_exact
val internal_call_runtime_bytes =
  optionSyntax.dest_some
    (rhs (concl internal_call_runtime_pipeline_normalized))

val internal_call_deploy_lowering_partial =
  EVAL ``lower_vyper_deploy_unit internal_call_program trace_rpolicy
          ^internal_call_runtime_bytes``
val internal_call_deploy_lowering_simplified =
  SIMP_RULE (srw_ss())
    [finite_mapTheory.FEVERY_FEMPTY,
     venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
    internal_call_deploy_lowering_partial
val internal_call_deploy_lowering_eval =
  CONV_RULE (RAND_CONV computeLib.EVAL_CONV)
    internal_call_deploy_lowering_simplified
val internal_call_deploy_lowering_normalized =
  SIMP_RULE (srw_ss()) [] internal_call_deploy_lowering_eval

Theorem internal_call_deploy_lowering_computed:
  lower_vyper_deploy_unit internal_call_program trace_rpolicy
    ^internal_call_runtime_bytes =
      ^(rhs (concl internal_call_deploy_lowering_normalized))
Proof
  ACCEPT_TAC internal_call_deploy_lowering_normalized
QED

val internal_call_deploy_unit =
  optionSyntax.dest_some
    (rhs (concl internal_call_deploy_lowering_normalized))

Theorem internal_call_deploy_lowering_exact:
  lower_vyper_deploy_unit internal_call_program trace_rpolicy
    ^internal_call_runtime_bytes = SOME ^internal_call_deploy_unit
Proof
  ACCEPT_TAC internal_call_deploy_lowering_normalized
QED

val internal_call_deploy_pipeline_eval =
  closed_compiler_eval_with_fuels [100000]
    ``checked_unit_pipeline_fuel_for_testing 100000
        bytecode_unit_pipeline_for_testing
        bytecode_identity_finalizer_for_testing trace_rpolicy
        ^internal_call_deploy_unit``

Theorem internal_call_deploy_pipeline_exact:
  checked_unit_pipeline_fuel_for_testing 100000
    bytecode_unit_pipeline_for_testing
    bytecode_identity_finalizer_for_testing trace_rpolicy
    ^internal_call_deploy_unit =
      ^(rhs (concl internal_call_deploy_pipeline_eval))
Proof
  ACCEPT_TAC internal_call_deploy_pipeline_eval
QED

val internal_call_deploy_pipeline_normalized =
  SIMP_RULE (srw_ss()) [] internal_call_deploy_pipeline_exact
val internal_call_deploy_bytes =
  optionSyntax.dest_some
    (rhs (concl internal_call_deploy_pipeline_normalized))

Theorem internal_call_deploy_policy_ok:
  lowering_policy_ok trace_rpolicy
Proof
  EVAL_TAC
QED

Theorem internal_call_deploy_classification:
  let (_, int_fns, _, ctor_fn) = classify_functions internal_call_program in
    ctor_fn = NONE /\ int_fns <> []
Proof
  EVAL_TAC
QED

Definition internal_call_deploy_forced_extraction_probe_def:
  internal_call_deploy_forced_extraction_probe runtime_bytecode =
    let sft = make_struct_fields_map internal_call_program in
    let sft_fn = get_struct_fields sft in
    let immutables_len = compute_immutables_len sft_fn internal_call_program in
    let nkey_map = assign_nkeys internal_call_program 0 in
    let use_trans = F in
    let (_, int_fns, _, ctor_fn) = classify_functions internal_call_program in
    let has_constructor = IS_SOME ctor_fn in
    let deploy_int_fns =
          MAP (set_internal_package_target trace_rpolicy.rpol_target o
               package_internal_fn internal_call_program use_trans nkey_map T
                 immutables_len) int_fns in
    let (ctor_cenv, ctor_args, ctor_payable, ctor_nr, ctor_nkey,
         ctor_trans, ctor_body, _) =
      set_constructor_package_target trace_rpolicy.rpol_target
        (case ctor_fn of
           SOME cf => package_constructor internal_call_program use_trans nkey_map cf
         | NONE => (ARB, ([] : (string # bool # bool # num # abi_dec_info) list),
                    F, F, 0n, F, ([] : stmt list), NoneT)) in
    let st0 = initial_compile_state "__deploy" in
    let (forced_metadata, st1) =
      compile_generate_deploy has_constructor (LENGTH runtime_bytecode)
        immutables_len ctor_args 0 deploy_int_fns ctor_cenv ctor_body
        ctor_payable ctor_nr ctor_nkey ctor_trans st0 in
    extract_context_with_forced_internals "__deploy" deploy_int_fns
      forced_metadata st1
End

val internal_call_deploy_forced_extraction_partial =
  EVAL ``internal_call_deploy_forced_extraction_probe
          ^internal_call_runtime_bytes``
val internal_call_deploy_forced_extraction_simplified =
  SIMP_RULE (srw_ss())
    [finite_mapTheory.FEVERY_FEMPTY,
     venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM]
    internal_call_deploy_forced_extraction_partial
val internal_call_deploy_forced_extraction_eval =
  CONV_RULE (RAND_CONV computeLib.EVAL_CONV)
    internal_call_deploy_forced_extraction_simplified
val internal_call_deploy_forced_extraction_normalized =
  SIMP_RULE (srw_ss()) [] internal_call_deploy_forced_extraction_eval

Theorem internal_call_deploy_forced_extraction_none:
  internal_call_deploy_forced_extraction_probe
    ^internal_call_runtime_bytes = NONE
Proof
  ACCEPT_TAC internal_call_deploy_forced_extraction_normalized
QED

Theorem resolve_internal_call_prague_policy[local]:
  resolve_o1_policy (o1_policy prague_capabilities) = SOME trace_rpolicy
Proof
  simp[venomPipelineDriverTheory.o1_policy_def,
       venomCompilerTypesTheory.resolve_o1_policy_def,
       trace_rpolicy_def,
       venomPolicyTypesTheory.target_capabilities_wf_def,
       venomPolicyTypesTheory.prague_capabilities_def]
QED

Theorem internal_call_no_arg_not_expected:
  compile_vyper_o1_fuel_for_testing 100000 internal_call_program <>
    SOME ^(evalCompilerBytecodeLib.read_hex_bytes "internal_call.hex")
Proof
  simp[compile_vyper_o1_fuel_for_testing_def,
       compileVyperTheory.compile_vyper_fuel_for_testing_def,
       resolve_internal_call_prague_policy,
       internal_call_runtime_lowering_exact,
       internal_call_runtime_pipeline_exact,
       internal_call_deploy_lowering_exact,
       internal_call_deploy_pipeline_exact] >>
  EVAL_TAC
QED
val _ = export_theory()
