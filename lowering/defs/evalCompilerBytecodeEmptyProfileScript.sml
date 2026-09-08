Theory evalCompilerBytecodeEmptyProfile
Ancestors evalCompilerBytecodeEmptySafetyPredicates
          evalCompilerBytecodeEmptyDeploySafetyPredicates
          evalCompilerBytecodeDefs
Libs finite_mapLib computeLib evalCompilerBytecodeLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t

val empty_profile_tm =
  ``formal_o1_ir_no_asm_opt 100000 ([] : toplevel list)``
val empty_profile_outer = computeLib.RESTR_EVAL_CONV
  [``lower_vyper_runtime_unit``,
   ``checked_unit_pipeline_fuel_for_testing``,
   ``lower_vyper_deploy_unit``] empty_profile_tm
val empty_profile_after_runtime_lowering =
  PURE_REWRITE_RULE
    [GSYM evalCompilerBytecodeTheory.empty_prague_rpolicy_def,
     evalCompilerBytecodeTheory.empty_runtime_lowering_exact]
    empty_profile_outer

val _ =
  if has_head ``checked_unit_pipeline_fuel_for_testing``
       (rhs (concl empty_profile_after_runtime_lowering))
  then () else raise Fail "empty profile did not reach checked runtime pipeline"

Theorem exact_empty_profile_after_runtime_lowering[local]:
  ^(concl empty_profile_after_runtime_lowering)
Proof
  ACCEPT_TAC empty_profile_after_runtime_lowering
QED

val runtime_driver =
  evalCompilerBytecodeEmptySafetyPredicatesTheory.exact_empty_runtime_driver_result
val runtime_driver_rhs = rhs (concl runtime_driver)
val _ =
  if head_is ``SOME`` runtime_driver_rhs andalso null (free_vars runtime_driver_rhs)
  then () else raise Fail "exact runtime driver RHS is not closed literal SOME"
val runtime_out_tm = optionSyntax.dest_some runtime_driver_rhs
val _ =
  if null (free_vars runtime_out_tm) then ()
  else raise Fail "exact runtime pipeline output is not closed"
val runtime_unit_projection = computeLib.EVAL_CONV ``(^runtime_out_tm).po_unit``
val runtime_unit_tm = rhs (concl runtime_unit_projection)
val _ =
  if null (free_vars runtime_unit_tm) then ()
  else raise Fail "projected exact runtime unit is not closed"

Theorem exact_empty_runtime_pipeline_output[local]:
  ^(concl runtime_driver)
Proof
  ACCEPT_TAC runtime_driver
QED

Theorem exact_empty_runtime_output_unit[local]:
  ^(concl runtime_unit_projection)
Proof
  ACCEPT_TAC runtime_unit_projection
QED

val runtime_codegen_tm =
  ``codegen_assembly_fuel 100000 empty_prague_rpolicy ^runtime_unit_tm``
val runtime_codegen_partial =
  computeLib.RESTR_EVAL_CONV [``generate_fn_plan_aux_fuel``]
    runtime_codegen_tm
fun is_runtime_planner_redex tm =
  let val (head, args) = strip_comb tm
  in same_const head ``generate_fn_plan_aux_fuel`` andalso length args = 8 end
  handle HOL_ERR _ => false
val runtime_planner_tms =
  find_terms is_runtime_planner_redex
    (rhs (concl runtime_codegen_partial))
val _ =
  if null runtime_planner_tms then
    raise Fail "runtime codegen exposed no planner redexes"
  else if List.all (fn tm => null (free_vars tm)) runtime_planner_tms then ()
  else raise Fail "runtime codegen exposed an open planner redex"
val runtime_planner_eqs =
  map
    (evalCompilerBytecodeLib.closed_fn_plan_aux_success_conv_with_fuels
       [16, 32, 64, 128, 256])
    runtime_planner_tms
val _ =
  if List.all
       (fn th =>
          optionSyntax.is_some (rhs (concl th)) andalso
          null (free_vars (rhs (concl th))))
       runtime_planner_eqs
  then () else raise Fail "lifted runtime planner result is not closed SOME"

Theorem exact_empty_runtime_planners_closed[local]:
  ^(list_mk_conj (map concl runtime_planner_eqs))
Proof
  ACCEPT_TAC (LIST_CONJ runtime_planner_eqs)
QED

val runtime_codegen_planned =
  PURE_REWRITE_RULE runtime_planner_eqs runtime_codegen_partial
val runtime_plan_eq =
  case runtime_planner_eqs of
    [th] => th
  | _ => raise Fail "expected exactly one runtime planner result"
val runtime_plan_tm = optionSyntax.dest_some (rhs (concl runtime_plan_eq))
val _ =
  if null (free_vars runtime_plan_tm) then ()
  else raise Fail "runtime codegen plan is not closed"

Theorem exact_empty_runtime_codegen_plan[local]:
  ^(concl runtime_plan_eq)
Proof
  ACCEPT_TAC runtime_plan_eq
QED

val runtime_context_plan_call =
  ``generate_context_plan_fuel 100000 (^runtime_unit_tm).cu_context``
val runtime_context_plan_partial =
  computeLib.RESTR_EVAL_CONV
    [``generate_fn_plan_aux_fuel``]
    runtime_context_plan_call
val runtime_context_plan_rewritten =
  PURE_REWRITE_RULE runtime_planner_eqs runtime_context_plan_partial
val runtime_context_plan_exact =
  CONV_RULE
    (RAND_CONV
      (SCONV
        [wordsTheory.dimword_def,
         stackPlanTypesTheory.stack_op_in_spill_region_def,
         stackPlanTypesTheory.spill_plan_in_region_def]))
    runtime_context_plan_rewritten
val runtime_context_plan_rhs = rhs (concl runtime_context_plan_exact)
val _ =
  if optionSyntax.is_some runtime_context_plan_rhs andalso
     null (free_vars runtime_context_plan_rhs)
  then () else raise Fail ("runtime context planner result is not closed SOME: " ^
                           term_to_string runtime_context_plan_rhs)
val runtime_context_plan_tm = optionSyntax.dest_some runtime_context_plan_rhs
val _ =
  if null (free_vars runtime_context_plan_tm) andalso
     type_of runtime_context_plan_tm = ``:context_plan``
  then () else raise Fail "runtime context plan payload is not closed context_plan"

Theorem exact_empty_runtime_context_plan[local]:
  generate_context_plan_fuel 100000 (^runtime_unit_tm).cu_context =
    SOME ^runtime_context_plan_tm
Proof
  ACCEPT_TAC runtime_context_plan_exact
QED


val _ = export_theory()
