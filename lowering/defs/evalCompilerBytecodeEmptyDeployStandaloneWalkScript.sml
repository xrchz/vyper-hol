Theory evalCompilerBytecodeEmptyDeployStandaloneWalk
Ancestors evalCompilerBytecodeEmptyDeployFinal
Libs computeLib

open HolKernel Parse boolLib bossLib

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun head_arity c n t =
  head_is c t andalso length (snd (strip_comb t)) = n
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_closed_head_arity c n t =
  if head_arity c n t andalso null (free_vars t) then t
  else find_term (fn u => head_arity c n u andalso null (free_vars u)) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)

val first_boundary =
  evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.exact_empty_deploy_callee_first_first_fold
val first_fold_tm = find_closed_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl first_boundary))

fun pass_head fold_tm =
  let
    val (_, args) = strip_comb fold_tm
    val (passes, _) = listSyntax.dest_list (List.nth (args, 2))
  in
    if null passes then NONE else SOME (hd passes)
  end

fun assert_pass label expected fold_tm =
  case pass_head fold_tm of
    SOME actual =>
      if aconv actual expected then ()
      else raise Fail (label ^ " has wrong pass head: " ^ term_to_string actual)
  | NONE => raise Fail (label ^ " unexpectedly has an empty pass list")

fun is_dispatch_case t =
  head_is ``option_CASE`` t andalso has_head ``execute_configured_fn_pass`` t

(* Produce a context-independent equation from one closed configured fold to
   its closed successor fold.  The dispatcher theorem is required to match
   the dispatcher exposed by this exact fold, so a stale driver-context fact
   cannot silently rewrite nothing. *)
fun closed_fold_step label expected next_expected dispatcher_result fold_tm =
  let
    val _ = assert_closed (label ^ " input fold") fold_tm
    val _ = assert_pass (label ^ " input fold") expected fold_tm
    val fold_one =
      REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
        fold_tm
    val unit_case_tm = find_term is_dispatch_case (rhs (concl fold_one))
    val _ = assert_closed (label ^ " current-function option owner") unit_case_tm
    val unit_case = computeLib.RESTR_EVAL_CONV
      [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
      unit_case_tm
    val fold_exposed = PURE_REWRITE_RULE [unit_case] fold_one
    val dispatcher_tm = find_closed_head_arity ``execute_configured_fn_pass`` 5
      (rhs (concl fold_exposed))
    val (_, dispatcher_args) = strip_comb dispatcher_tm
    val actual = List.nth (dispatcher_args, 1)
    val _ =
      if aconv actual expected then ()
      else raise Fail (label ^ " exposed the wrong dispatcher: " ^
        term_to_string actual)
    val _ =
      if aconv (lhs (concl dispatcher_result)) dispatcher_tm then ()
      else raise Fail (label ^ " dispatcher theorem does not match the closed fold")
    fun owns_dispatch t =
      head_is ``option_CASE`` t andalso
      can (find_term (fn u => aconv u dispatcher_tm)) t
    val result_case_tm = find_term owns_dispatch (rhs (concl fold_exposed))
    val _ = assert_closed (label ^ " dispatcher result owner") result_case_tm
    val result_case_rewritten =
      REWRITE_CONV [dispatcher_result] result_case_tm
    val result_case_reduced = computeLib.RESTR_EVAL_CONV
      [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
      (rhs (concl result_case_rewritten))
    val result_case = TRANS result_case_rewritten result_case_reduced
    val fold_after_result = PURE_REWRITE_RULE [result_case] fold_exposed
    val tail_reduced = computeLib.RESTR_EVAL_CONV
      [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
      (rhs (concl fold_after_result))
    val step = TRANS fold_after_result tail_reduced
    val successor = rhs (concl step)
    val _ =
      if head_arity ``run_configured_fn_pass_fold`` 7 successor then ()
      else raise Fail (label ^ " did not reduce directly to a successor fold")
    val _ = assert_closed (label ^ " successor fold") successor
    val _ = assert_pass (label ^ " successor fold") next_expected successor
    val _ =
      if aconv (lhs (concl step)) fold_tm then ()
      else raise Fail (label ^ " changed its input fold")
  in
    step
  end

val _ = assert_pass "standalone initial fold" ``CFP_Simple VP_MakeSSA`` first_fold_tm

(* The first MakeSSA result was local to GraphBoundary, so reconstruct only
   that already-small dispatcher equation from the exact closed call. *)
val first_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    first_fold_tm
val first_unit_case_tm = find_term is_dispatch_case (rhs (concl first_fold_one))
val first_unit_case = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  first_unit_case_tm
val first_fold_exposed = PURE_REWRITE_RULE [first_unit_case] first_fold_one
val first_dispatch_tm = find_closed_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl first_fold_exposed))
val first_dispatch_one =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_make_ssa
    first_dispatch_tm
val first_make_ssa_tm = find_closed_head_arity ``make_ssa_current_fn`` 2
  (rhs (concl first_dispatch_one))
val exact_first_make_ssa = computeLib.EVAL_CONV first_make_ssa_tm
val exact_first_dispatch =
  CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss ()) [exact_first_make_ssa]))
    first_dispatch_one
val _ =
  if head_is ``SOME`` (rhs (concl exact_first_dispatch)) then ()
  else raise Fail "standalone first MakeSSA dispatcher is not SOME"

val step_make_ssa = closed_fold_step "standalone MakeSSA"
  ``CFP_Simple VP_MakeSSA`` ``CFP_Simple VP_LowerDload``
  exact_first_dispatch first_fold_tm
val lower_fold_tm = rhs (concl step_make_ssa)

val step_lower = closed_fold_step "standalone LowerDload"
  ``CFP_Simple VP_LowerDload`` ``CFP_Simple VP_ConcretizeMemLoc``
  evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.exact_empty_deploy_lower_dload_dispatch
  lower_fold_tm
val concretize_fold_tm = rhs (concl step_lower)

val step_concretize = closed_fold_step "standalone ConcretizeMemLoc"
  ``CFP_Simple VP_ConcretizeMemLoc`` ``CFP_Simple VP_FmpLowering``
  evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.exact_empty_deploy_concretize_dispatch
  concretize_fold_tm
val fmp_fold_tm = rhs (concl step_concretize)

val step_fmp = closed_fold_step "standalone FmpLowering"
  ``CFP_Simple VP_FmpLowering`` ``CFP_Simple VP_MakeSSA``
  evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.exact_empty_deploy_fmp_dispatch
  fmp_fold_tm
val second_make_ssa_fold_tm = rhs (concl step_fmp)

val step_second_make_ssa = closed_fold_step "standalone second MakeSSA"
  ``CFP_Simple VP_MakeSSA`` ``CFP_Simple VP_SimplifyCFG``
  evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.exact_empty_deploy_second_make_ssa_dispatch
  second_make_ssa_fold_tm
val simplify_cfg_fold_tm = rhs (concl step_second_make_ssa)

val exact_simplify_cfg_dispatch_literal =
  PURE_REWRITE_RULE
    [evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.empty_deploy_post_fmp_simplify_cfg_operand_def]
    evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgResultTheory.exact_empty_deploy_post_fmp_simplify_cfg_dispatch

val step_simplify_cfg = closed_fold_step "standalone SimplifyCFG"
  ``CFP_Simple VP_SimplifyCFG`` ``CFP_Simple VP_SingleUseExpansion``
  exact_simplify_cfg_dispatch_literal simplify_cfg_fold_tm
val single_use_fold_tm = rhs (concl step_simplify_cfg)

val first_to_single_use =
  step_make_ssa
  |> (fn th => TRANS th step_lower)
  |> (fn th => TRANS th step_concretize)
  |> (fn th => TRANS th step_fmp)
  |> (fn th => TRANS th step_second_make_ssa)
  |> (fn th => TRANS th step_simplify_cfg)
val _ =
  if aconv (lhs (concl first_to_single_use)) first_fold_tm andalso
     aconv (rhs (concl first_to_single_use)) single_use_fold_tm andalso
     null (free_vars (concl first_to_single_use))
  then () else raise Fail "standalone midpoint fold chain is malformed"

Theorem exact_empty_deploy_standalone_first_fold_to_single_use:
  ^(concl first_to_single_use)
Proof
  ACCEPT_TAC first_to_single_use
QED

val _ = export_theory()
