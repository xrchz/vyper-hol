Theory evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgIter
Ancestors evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgRound
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t

val round_fixpoint_guard_th = computeLib.EVAL_CONV
  ``empty_deploy_post_fmp_simplify_cfg_round1_fn.fn_blocks =
    empty_deploy_post_fmp_simplify_cfg_operand.fn_blocks``

Theorem exact_empty_deploy_post_fmp_round_fixpoint_guard:
  ^(concl round_fixpoint_guard_th)
Proof
  ACCEPT_TAC round_fixpoint_guard_th
QED

val iter_suc_clause =
  Q.SPECL [`0`, `empty_deploy_post_fmp_simplify_cfg_operand`]
    (cj 2 simplifyCfgDefsTheory.simplify_cfg_iter_with_labels_def)
val exact_iter_th = SIMP_RULE (srw_ss ())
  [evalCompilerBytecodeEmptyDeployPostFmpSimplifyCfgRoundTheory.exact_empty_deploy_post_fmp_simplify_cfg_round_with_labels,
   round_fixpoint_guard_th,
   cj 1 simplifyCfgDefsTheory.simplify_cfg_iter_with_labels_def]
  iter_suc_clause
val _ =
  if has_head ``simplify_cfg_iter_with_labels`` (rhs (concl exact_iter_th))
  then raise Fail "post-FMP deploy one-step iterator left a recursive iterator"
  else ()

Theorem exact_empty_deploy_post_fmp_simplify_cfg_iter_with_labels:
  ^(concl exact_iter_th)
Proof
  ACCEPT_TAC exact_iter_th
QED

val fn_unfold = REWR_CONV
  simplifyCfgDefsTheory.simplify_cfg_fn_with_labels_def
  ``simplify_cfg_fn_with_labels empty_deploy_post_fmp_simplify_cfg_operand``
val exact_fn_th = SIMP_RULE (srw_ss ())
  [evalCompilerBytecodeEmptyDeployGraphBoundaryTheory.exact_empty_deploy_post_fmp_simplify_cfg_block_count,
   exact_iter_th] fn_unfold
val _ =
  if has_head ``simplify_cfg_iter_with_labels`` (rhs (concl exact_fn_th)) orelse
     has_head ``simplify_cfg_fn_with_labels`` (rhs (concl exact_fn_th))
  then raise Fail "post-FMP deploy SimplifyCFG wrapper left a recursive head"
  else ()

Theorem exact_empty_deploy_post_fmp_simplify_cfg_fn_with_labels:
  ^(concl exact_fn_th)
Proof
  ACCEPT_TAC exact_fn_th
QED

val _ = export_theory()
