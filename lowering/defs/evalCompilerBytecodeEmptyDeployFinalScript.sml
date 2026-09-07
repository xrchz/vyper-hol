Theory evalCompilerBytecodeEmptyDeployFinal
Ancestors evalCompilerBytecodeEmptyDeployPostFmpDFT
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_closed_head_arity c n t =
  find_term
    (fn u => head_arity c n u andalso null (free_vars u))
    t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val incoming =
  evalCompilerBytecodeEmptyDeployPostFmpDFTTheory.exact_empty_deploy_after_post_fmp_dft
val fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl incoming))
val fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    fold_tm
fun is_unit_case t =
  head_is ``option_CASE`` t andalso
  has_head ``execute_configured_fn_pass`` t
val unit_case_tm = find_term is_unit_case (rhs (concl fold_one))
val _ = assert_closed "CFGNormalization unit option case" unit_case_tm
val unit_case = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  unit_case_tm
val fold_exposed = PURE_REWRITE_RULE [unit_case] fold_one
val context_exposed = PURE_REWRITE_RULE [fold_exposed] incoming
val dispatcher_tm = find_closed_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl context_exposed))
val dispatcher_result = computeLib.EVAL_CONV dispatcher_tm
fun is_result_case t =
  head_is ``option_CASE`` t andalso
  can (find_term (fn u => aconv u dispatcher_tm)) t
val result_case_tm = find_term is_result_case (rhs (concl context_exposed))
val _ = assert_closed "CFGNormalization result option case" result_case_tm
val result_case_rewritten = REWRITE_CONV [dispatcher_result] result_case_tm
val result_case_reduced = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  (rhs (concl result_case_rewritten))
val result_case = TRANS result_case_rewritten result_case_reduced
val after_cfg_normalization = PURE_REWRITE_RULE [result_case] context_exposed

val tail_tm = rhs (concl after_cfg_normalization)
val _ = assert_closed "empty deploy configured-walk tail" tail_tm
val final_fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_cfg_normalization))
val (_, final_fold_args) = strip_comb final_fold_tm
val (final_passes, _) = listSyntax.dest_list (List.nth (final_fold_args, 2))
val _ =
  if null final_passes then ()
  else raise Fail "CFGNormalization did not expose the empty pass-list tail"
val final_fold_done =
  REWR_CONV (cj 1 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    final_fold_tm
val fold_result_tm = rhs (concl final_fold_done)
val _ =
  if head_is ``SOME`` fold_result_tm then ()
  else raise Fail "empty configured fold did not reduce to literal SOME"
val pair_tm = optionSyntax.dest_some fold_result_tm
val (final_unit_tm, final_supply_tm) = pairSyntax.dest_pair pair_tm
val _ = assert_closed "exact final deploy unit" final_unit_tm
val _ = assert_closed "exact final deploy supply" final_supply_tm

Definition empty_deploy_final_unit_def:
  empty_deploy_final_unit = ^final_unit_tm
End

Definition empty_deploy_final_supply_def:
  empty_deploy_final_supply = ^final_supply_tm
End

val final_fold_named =
  REWRITE_RULE [GSYM empty_deploy_final_unit_def,
                GSYM empty_deploy_final_supply_def]
    final_fold_done
val final_walk_concrete =
  PURE_REWRITE_RULE [final_fold_done] after_cfg_normalization
val final_walk_context =
  REWRITE_RULE [GSYM empty_deploy_final_unit_def,
                GSYM empty_deploy_final_supply_def]
    final_walk_concrete
val _ =
  if has_head ``run_configured_fn_pass_fold`` (rhs (concl final_walk_context))
  then raise Fail "final deploy walk still contains a configured fold"
  else ()
val _ =
  if has_head ``execute_configured_fn_pass`` (rhs (concl final_walk_context))
  then raise Fail "final deploy walk still contains a dispatcher"
  else ()

Theorem exact_empty_deploy_after_cfg_normalization:
  ^(concl after_cfg_normalization)
Proof
  ACCEPT_TAC after_cfg_normalization
QED

Theorem exact_empty_deploy_configured_walk:
  ^(concl final_walk_context)
Proof
  ACCEPT_TAC final_walk_context
QED

val _ = export_theory()
