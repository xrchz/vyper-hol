Theory evalCompilerBytecodeEmptyDeployPreWalk1
Ancestors evalCompilerBytecodeEmptyDeploy
Libs computeLib finite_mapLib

open HolKernel Parse boolLib bossLib

val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY])
val () = computeLib.upd_compset
  (computeLib.add_thms [integer_wordTheory.i2w_pos])

fun head_is c t = same_const (fst (strip_comb t)) c handle HOL_ERR _ => false
fun has_head c t = head_is c t orelse can (find_term (head_is c)) t
fun find_head c t = if head_is c t then t else find_term (head_is c) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm)
fun rew_rec def tm =
  FIRST_CONV [REWR_CONV (cj 1 def), REWR_CONV (cj 2 def)] tm

val empty_deploy_rpolicy_tm =
  ``<| rpol_target := K T;
       rpol_frontend_dispatch := Linear;
       rpol_final_assembly := FAP_Optimize |>``
val empty_deploy_driver_tm =
  ``run_venom_pipeline (K T) (K T) (K T) ^empty_deploy_rpolicy_tm
      o1_pipeline_spec empty_deploy_unit``
val empty_deploy_driver_one =
  REWR_CONV venomPipelineDriverTheory.run_venom_pipeline_def
    empty_deploy_driver_tm
fun eval_true label tm =
  let
    val raw = computeLib.EVAL_CONV tm
    val th = SIMP_RULE (srw_ss ())
      [finite_mapTheory.FEVERY_FEMPTY,
       venomInstTheory.fn_insts_blocks_def, DISJ_IMP_THM] raw
    val c = concl th
    val proved = aconv c tm orelse aconv c ``T`` orelse
      (boolSyntax.is_eq c andalso aconv (rhs c) ``T``)
    val _ = if proved then ()
            else raise Fail (label ^ " did not evaluate to true: " ^
                             term_to_string c)
  in th end
val empty_deploy_spec_wf = eval_true "empty deploy pipeline-spec guard"
  ``pipeline_spec_wf ^empty_deploy_rpolicy_tm o1_pipeline_spec``

val empty_deploy_raw_static_wf = eval_true "empty deploy raw-static guard"
  ``raw_static_inputs_wf empty_deploy_unit.cu_context``

val _ = export_theory()
