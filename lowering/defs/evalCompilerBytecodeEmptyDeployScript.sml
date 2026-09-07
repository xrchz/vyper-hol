Theory evalCompilerBytecodeEmptyDeploy
Ancestors evalCompilerBytecodeEmptySafetyPredicates
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val empty_deploy_lowering_tm =
  ``lower_vyper_deploy_unit ([] : toplevel list)
      <| rpol_target := K T;
         rpol_frontend_dispatch := Linear;
         rpol_final_assembly := FAP_Optimize |>
      ([170w; 187w] : byte list)``
val exact_empty_deploy_lowering_raw = computeLib.EVAL_CONV empty_deploy_lowering_tm
val exact_empty_deploy_lowering =
  SIMP_RULE (srw_ss ()) [finite_mapTheory.FEVERY_FEMPTY]
    exact_empty_deploy_lowering_raw
val empty_deploy_lowering_rhs = rhs (concl exact_empty_deploy_lowering)
val _ =
  if head_is ``SOME`` empty_deploy_lowering_rhs then ()
  else raise Fail ("empty deploy lowering is not literal SOME: " ^
                   term_to_string empty_deploy_lowering_rhs)
val empty_deploy_unit_tm = optionSyntax.dest_some empty_deploy_lowering_rhs
val _ = assert_closed "exact empty deploy unit" empty_deploy_unit_tm

Definition empty_deploy_unit_def:
  empty_deploy_unit = ^empty_deploy_unit_tm
End

val exact_empty_deploy_lowering_named =
  PURE_REWRITE_RULE [GSYM empty_deploy_unit_def] exact_empty_deploy_lowering

val empty_deploy_named_rhs = rhs (concl exact_empty_deploy_lowering_named)
val _ =
  if head_is ``SOME`` empty_deploy_named_rhs andalso
     aconv (optionSyntax.dest_some empty_deploy_named_rhs) ``empty_deploy_unit`` andalso
     null (free_vars empty_deploy_named_rhs)
  then ()
  else raise Fail "named empty deploy lowering is not closed SOME empty_deploy_unit"

Theorem exact_empty_deploy_lowering_result:
  ^(concl exact_empty_deploy_lowering_named)
Proof
  ACCEPT_TAC exact_empty_deploy_lowering_named
QED

val _ = export_theory()
