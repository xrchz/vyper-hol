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


Theorem deploy_unit_wf_intro[local]:
  ctx_wf unit.cu_context /\
  wf_invoke_targets unit.cu_context /\
  ctx_inst_ids_distinct unit.cu_context /\
  (!fn. MEM fn unit.cu_context.ctx_functions ==>
        wf_function fn /\ fn_inst_wf fn) /\
  unit_labels_wf unit ==>
  unit_wf unit
Proof
  rw[venomCompilerWfTheory.unit_wf_def,
     venomWfTheory.venom_wf_def]
QED

Theorem deploy_bb_well_formed_snoc[local]:
  is_terminator term.inst_opcode /\
  EVERY (\i. ~is_terminator i.inst_opcode) prefix /\
  EVERY (\i. i.inst_opcode <> PHI) (prefix ++ [term]) ==>
  bb_well_formed
    <| bb_label := lbl; bb_instructions := prefix ++ [term] |>
Proof
  rw[venomWfTheory.bb_well_formed_def] >>
  rpt strip_tac >> simp[]
  >- (Cases_on `i < LENGTH prefix`
      >- gvs[listTheory.EVERY_EL, listTheory.EL_APPEND_EQN]
      >> `i = LENGTH prefix` by decide_tac
      >> simp[listTheory.EL_APPEND_EQN])
  >> Cases_on `j < LENGTH prefix`
  >- gvs[listTheory.EVERY_EL, listTheory.EL_APPEND_EQN]
  >> `j = LENGTH prefix` by decide_tac
  >> gvs[listTheory.EL_APPEND_EQN]
QED

Theorem deploy_fn_inst_wf_from_blocks[local]:
  (!bb. MEM bb fn.fn_blocks ==>
        EVERY inst_wf bb.bb_instructions) ==>
  fn_inst_wf fn
Proof
  rw[venomWfTheory.fn_inst_wf_def] >>
  first_x_assum drule >>
  simp[listTheory.EVERY_MEM]
QED

fun eval_closed label tm =
  let
    val _ = assert_closed label tm
  in
    computeLib.EVAL_CONV tm
  end

val deploy_functions_th = eval_closed "deploy function projection"
  ``empty_deploy_unit.cu_context.ctx_functions``
val deploy_functions = fst (listSyntax.dest_list (rhs (concl deploy_functions_th)))
val _ = if length deploy_functions = 1 then ()
        else raise Fail "deploy context does not have exactly one function"
val deploy_fn_tm = hd deploy_functions
val deploy_blocks_th = eval_closed "deploy block projection"
  ``(^deploy_fn_tm).fn_blocks``
val deploy_blocks = fst (listSyntax.dest_list (rhs (concl deploy_blocks_th)))
val _ = if length deploy_blocks = 1 then ()
        else raise Fail "deploy function does not have exactly one block"
val deploy_bb_tm = hd deploy_blocks
val deploy_insts_th = eval_closed "deploy instruction projection"
  ``(^deploy_bb_tm).bb_instructions``
val deploy_insts = fst (listSyntax.dest_list (rhs (concl deploy_insts_th)))
val _ = if length deploy_insts = 4 then ()
        else raise Fail "deploy block does not have exactly four instructions"
val deploy_succs_th = eval_closed "deploy block successors"
  ``bb_succs ^deploy_bb_tm``
val deploy_data_segment_th = eval_closed "deploy data segment projection"
  ``empty_deploy_unit.cu_data_segment``

Theorem deploy_functions_shape[local]:
  ^(concl deploy_functions_th)
Proof
  ACCEPT_TAC deploy_functions_th
QED

Theorem deploy_blocks_shape[local]:
  ^(concl deploy_blocks_th)
Proof
  ACCEPT_TAC deploy_blocks_th
QED

Theorem deploy_instructions_shape[local]:
  ^(concl deploy_insts_th)
Proof
  ACCEPT_TAC deploy_insts_th
QED

Theorem deploy_succs_shape[local]:
  ^(concl deploy_succs_th)
Proof
  ACCEPT_TAC deploy_succs_th
QED

Theorem deploy_data_segment_shape[local]:
  ^(concl deploy_data_segment_th)
Proof
  ACCEPT_TAC deploy_data_segment_th
QED

Theorem deploy_bb_snoc_shape[local]:
  ^deploy_bb_tm =
    <| bb_label := (^deploy_bb_tm).bb_label;
       bb_instructions := FRONT ((^deploy_bb_tm).bb_instructions) ++
                          [LAST ((^deploy_bb_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED

Theorem deploy_bb_well_formed[local]:
  bb_well_formed ^deploy_bb_tm
Proof
  once_rewrite_tac[deploy_bb_snoc_shape] >>
  irule deploy_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem deploy_bb_instructions_wf[local]:
  EVERY inst_wf (^deploy_bb_tm).bb_instructions
Proof
  simp[venomWfTheory.inst_wf_def]
QED

Theorem deploy_function_well_formed[local]:
  wf_function ^deploy_fn_tm
Proof
  simp[venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def,
       venomWfTheory.fn_succs_closed_def,
       venomWfTheory.fn_inst_ids_distinct_def,
       venomInstTheory.fn_labels_def,
       deploy_bb_well_formed,
       deploy_succs_shape] >>
  rpt strip_tac >> gvs[deploy_bb_well_formed, deploy_succs_shape]
QED

Theorem deploy_function_instructions_wf[local]:
  fn_inst_wf ^deploy_fn_tm
Proof
  simp[venomWfTheory.fn_inst_wf_def,
       deploy_blocks_shape] >>
  rpt strip_tac >> gvs[venomWfTheory.inst_wf_def]
QED

Theorem deploy_context_functions_wf[local]:
  !fn. MEM fn empty_deploy_unit.cu_context.ctx_functions ==>
        wf_function fn /\ fn_inst_wf fn
Proof
  simp[deploy_functions_shape,
       deploy_function_well_formed,
       deploy_function_instructions_wf]
QED

Theorem deploy_context_wf[local]:
  ctx_wf empty_deploy_unit.cu_context
Proof
  simp[venomWfTheory.ctx_wf_def,
       venomWfTheory.ctx_distinct_fn_names_def,
       venomWfTheory.ctx_has_entry_def,
       venomInstTheory.ctx_fn_names_def,
       empty_deploy_unit_def,
       deploy_functions_shape]
QED

Theorem deploy_invoke_targets_wf[local]:
  wf_invoke_targets empty_deploy_unit.cu_context
Proof
  rw[venomWfTheory.wf_invoke_targets_def] >> rpt strip_tac >>
  gvs[deploy_functions_shape,
      venomInstTheory.fn_insts_def,
      venomInstTheory.fn_insts_blocks_def,
      deploy_blocks_shape,
      deploy_instructions_shape]
QED

Theorem deploy_context_inst_ids_distinct[local]:
  ctx_inst_ids_distinct empty_deploy_unit.cu_context
Proof
  simp[venomWfTheory.ctx_inst_ids_distinct_def,
       deploy_functions_shape,
       deploy_blocks_shape,
       deploy_instructions_shape]
QED

Theorem deploy_unit_labels_wf[local]:
  unit_labels_wf empty_deploy_unit
Proof
  simp[venomCompilerWfTheory.unit_labels_wf_def,
       venomCompilerWfTheory.unit_label_namespace_def,
       venomCompilerWfTheory.unit_data_labels_consistent_def,
       venomCompilerWfTheory.unit_data_label_refs_def,
       venomCompilerWfTheory.data_section_label_refs_def,
       venomCompilerWfTheory.data_item_label_refs_def,
       venomInstTheory.fn_labels_def,
       empty_deploy_unit_def,
       deploy_functions_shape,
       deploy_blocks_shape,
       deploy_data_segment_shape]
QED

Theorem empty_deploy_unit_wf[local]:
  unit_wf empty_deploy_unit
Proof
  irule deploy_unit_wf_intro >>
  simp[deploy_context_wf,
       deploy_invoke_targets_wf,
       deploy_context_inst_ids_distinct,
       deploy_context_functions_wf,
       deploy_unit_labels_wf]
QED

val empty_deploy_driver_after_guards =
  SIMP_RULE (srw_ss ())
    [empty_deploy_spec_wf, empty_deploy_unit_wf,
     empty_deploy_raw_static_wf]
    empty_deploy_driver_one
val empty_deploy_pre_runner_tm = find_head ``run_pipeline_stages``
  (rhs (concl empty_deploy_driver_after_guards))
val _ = assert_closed "empty deploy pre-walk runner" empty_deploy_pre_runner_tm
val (_, empty_deploy_pre_args) = strip_comb empty_deploy_pre_runner_tm
val _ =
  if length empty_deploy_pre_args = 4 then ()
  else raise Fail "empty deploy pre-walk runner has unexpected arity"
val empty_deploy_initial_supply_tm = List.nth (empty_deploy_pre_args, 3)
val empty_deploy_initial_supply =
  computeLib.EVAL_CONV empty_deploy_initial_supply_tm
val empty_deploy_pre_runner_shape =
  SIMP_CONV (srw_ss ())
    [venomPassScheduleTheory.o1_pipeline_spec_exact,
     empty_deploy_initial_supply]
    empty_deploy_pre_runner_tm
val empty_deploy_normalized_pre_tm = rhs (concl empty_deploy_pre_runner_shape)
val _ = assert_closed "normalized empty deploy pre-walk runner"
  empty_deploy_normalized_pre_tm
val empty_deploy_pre_one =
  rew_rec venomPipelineRunnerTheory.run_pipeline_stages_def
    empty_deploy_normalized_pre_tm
val empty_deploy_first_stage_tm = find_head ``run_pipeline_stage``
  (rhs (concl empty_deploy_pre_one))
val _ = assert_closed "empty deploy first pre-walk stage"
  empty_deploy_first_stage_tm
val (_, empty_deploy_first_stage_args) = strip_comb empty_deploy_first_stage_tm
val _ =
  if length empty_deploy_first_stage_args = 4 andalso
     aconv (List.nth (empty_deploy_first_stage_args, 1))
       ``PS_MapFunctions (CFP_Simple VP_SimplifyCFG)``
  then ()
  else raise Fail "empty deploy first pre-walk stage is not SimplifyCFG"

val empty_deploy_driver_normalized =
  CONV_RULE
    (RAND_CONV
      (ONCE_DEPTH_CONV (REWR_CONV empty_deploy_pre_runner_shape)))
    empty_deploy_driver_after_guards
val exact_empty_deploy_driver_to_first_stage =
  CONV_RULE
    (RAND_CONV (ONCE_DEPTH_CONV (REWR_CONV empty_deploy_pre_one)))
    empty_deploy_driver_normalized
val _ =
  if aconv (lhs (concl exact_empty_deploy_driver_to_first_stage))
       empty_deploy_driver_tm
  then ()
  else raise Fail "first-stage exposure changed the empty deploy driver LHS"
val exact_empty_deploy_first_stage_rhs =
  rhs (concl exact_empty_deploy_driver_to_first_stage)
val exposed_empty_deploy_first_stage_tm = find_head ``run_pipeline_stage``
  exact_empty_deploy_first_stage_rhs
val _ = assert_closed "exposed empty deploy SimplifyCFG stage"
  exposed_empty_deploy_first_stage_tm
val _ =
  if aconv exposed_empty_deploy_first_stage_tm empty_deploy_first_stage_tm
  then ()
  else raise Fail "driver context does not contain the exact first stage"

Theorem exact_empty_deploy_driver_first_stage_context:
  ^(concl exact_empty_deploy_driver_to_first_stage)
Proof
  ACCEPT_TAC exact_empty_deploy_driver_to_first_stage
QED

Theorem exact_empty_deploy_complete_pre_walk_one_context:
  ^(concl empty_deploy_pre_one)
Proof
  ACCEPT_TAC empty_deploy_pre_one
QED

val _ = export_theory()
