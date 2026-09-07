Theory evalCompilerBytecodeFinalPasses
Ancestors evalCompilerBytecodeAfterSecondSimplifyCfg
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head_arity c n t =
  if head_arity c n t then t
  else (find_term (head_arity c n) t
        handle HOL_ERR _ => raise Fail
          ("missing head/arity " ^ term_to_string c))
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm ^
    " ; free vars: " ^
    String.concatWith ", " (map term_to_string (free_vars tm)))
fun assert_passes label expected_next th =
  let
    val fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
      (rhs (concl th))
    val _ = assert_closed (label ^ " residual fold") fold_tm
    val (_, args) = strip_comb fold_tm
    val (passes, _) = listSyntax.dest_list (List.nth (args, 2))
  in
    case expected_next of
      SOME expected =>
        if not (null passes) andalso aconv (hd passes) expected then ()
        else raise Fail (label ^ " has unexpected next pass")
    | NONE =>
        if null passes then ()
        else raise Fail (label ^ " did not reach the empty pass list")
  end
fun advance_one label expected_next context =
  let
    val fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
      (rhs (concl context))
    val _ = assert_closed (label ^ " incoming fold") fold_tm
    val fold_one =
      REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
        fold_tm
    fun is_unit_case t =
      head_is ``option_CASE`` t andalso
      has_head ``execute_configured_fn_pass`` t
    val unit_case_tm = find_term is_unit_case (rhs (concl fold_one))
    val _ = assert_closed (label ^ " unit option case") unit_case_tm
    val unit_case = computeLib.RESTR_EVAL_CONV
      [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
      unit_case_tm
    val fold_exposed = PURE_REWRITE_RULE [unit_case] fold_one
    val context_exposed = PURE_REWRITE_RULE [fold_exposed] context
    val dispatcher_tm = find_head_arity ``execute_configured_fn_pass`` 5
      (rhs (concl context_exposed))
    val _ = assert_closed (label ^ " dispatcher") dispatcher_tm
    val dispatcher_result = computeLib.EVAL_CONV dispatcher_tm
    fun is_result_case t =
      head_is ``option_CASE`` t andalso
      can (find_term (fn u => aconv u dispatcher_tm)) t
    val result_case_tm = find_term is_result_case
      (rhs (concl context_exposed))
    val _ = assert_closed (label ^ " result option case") result_case_tm
    val result_case_rewritten =
      REWRITE_CONV [dispatcher_result] result_case_tm
    val result_case_reduced = computeLib.RESTR_EVAL_CONV
      [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
      (rhs (concl result_case_rewritten))
    val result_case = TRANS result_case_rewritten result_case_reduced
    val context' = PURE_REWRITE_RULE [result_case] context_exposed
    val _ =
      if aconv (lhs (concl context')) (lhs (concl context)) then ()
      else raise Fail (label ^ " changed the outer LHS")
    val _ =
      if can (find_term (head_arity ``execute_configured_fn_pass`` 5))
           (rhs (concl context')) then
        raise Fail (label ^ " left a residual applied dispatcher")
      else ()
    val _ = assert_passes label expected_next context'
  in
    context'
  end

val after_second_simplify_cfg =
  evalCompilerBytecodeAfterSecondSimplifyCfgTheory.exact_empty_runtime_after_second_simplify_cfg

val after_single_use_expansion = advance_one "SingleUseExpansion"
  (SOME ``CFP_Simple VP_DFT``) after_second_simplify_cfg

Theorem exact_empty_runtime_after_single_use_expansion:
  ^(concl after_single_use_expansion)
Proof
  ACCEPT_TAC after_single_use_expansion
QED

val after_dft = advance_one "DFT"
  (SOME ``CFP_Simple VP_CFGNormalization``) after_single_use_expansion

Theorem exact_empty_runtime_after_dft:
  ^(concl after_dft)
Proof
  ACCEPT_TAC after_dft
QED

val after_cfg_normalization = advance_one "CFGNormalization"
  NONE after_dft
val final_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_cfg_normalization))
val _ = assert_closed "final configured fold" final_fold_tm
val final_fold_done =
  REWR_CONV (cj 1 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    final_fold_tm
val _ =
  if head_is ``SOME`` (rhs (concl final_fold_done)) then ()
  else raise Fail "empty configured fold did not reduce to literal SOME"
val final_walk_context =
  PURE_REWRITE_RULE [final_fold_done] after_cfg_normalization
val _ =
  if has_head ``run_configured_fn_pass_fold`` (rhs (concl final_walk_context)) then
    raise Fail "final walk still contains a configured fold"
  else ()
val _ =
  if has_head ``execute_configured_fn_pass`` (rhs (concl final_walk_context)) then
    raise Fail "final walk still contains a dispatcher"
  else ()

Theorem exact_empty_runtime_after_cfg_normalization:
  ^(concl after_cfg_normalization)
Proof
  ACCEPT_TAC after_cfg_normalization
QED

Theorem exact_empty_runtime_configured_walk:
  ^(concl final_walk_context)
Proof
  ACCEPT_TAC final_walk_context
QED

val _ = export_theory()
