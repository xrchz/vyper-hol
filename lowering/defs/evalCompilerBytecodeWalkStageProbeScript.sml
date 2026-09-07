Theory evalCompilerBytecodeWalkStageProbe
Ancestors evalCompilerBytecodeAfterMakeSSA
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
  if head_arity c n t then t else find_term (head_arity c n) t
fun assert_closed label tm =
  if null (free_vars tm) then ()
  else raise Fail (label ^ " is not closed: " ^ term_to_string tm ^
    " ; free vars: " ^
    String.concatWith ", " (map term_to_string (free_vars tm)))

val after_make_ssa =
  evalCompilerBytecodeAfterMakeSSATheory.exact_empty_runtime_after_make_ssa_to_lower_dload
val lower_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_make_ssa))
val _ = assert_closed "LowerDload residual fold" lower_fold_tm
val lower_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    lower_fold_tm
fun is_dispatch_case t =
  head_is ``option_CASE`` t andalso has_head ``execute_configured_fn_pass`` t
val lower_unit_case_tm =
  find_term is_dispatch_case (rhs (concl lower_fold_one))
val _ = assert_closed "LowerDload unit option case" lower_unit_case_tm
val lower_unit_case = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  lower_unit_case_tm
val lower_fold_exposed = PURE_REWRITE_RULE [lower_unit_case] lower_fold_one
val lower_context_exposed = PURE_REWRITE_RULE [lower_fold_exposed] after_make_ssa
val lower_dispatch_tm = find_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl lower_context_exposed))
val _ = assert_closed "LowerDload dispatcher" lower_dispatch_tm
val (_, lower_dispatch_args) = strip_comb lower_dispatch_tm
val _ =
  if aconv (List.nth (lower_dispatch_args, 1))
       ``CFP_Simple VP_LowerDload``
  then () else raise Fail "first residual dispatcher is not LowerDload"
val exact_lower_dispatch = computeLib.EVAL_CONV lower_dispatch_tm

Theorem exact_empty_runtime_lower_dload_dispatch:
  ^(concl exact_lower_dispatch)
Proof
  ACCEPT_TAC exact_lower_dispatch
QED

fun is_exact_dispatch_case dispatch_tm t =
  head_is ``option_CASE`` t andalso
  can (find_term (fn u => aconv u dispatch_tm)) t
val lower_dispatch_case_tm =
  find_term (is_exact_dispatch_case lower_dispatch_tm)
    (rhs (concl lower_context_exposed))
val _ = assert_closed "LowerDload result option case" lower_dispatch_case_tm
val lower_dispatch_case_rewritten =
  REWRITE_CONV [exact_lower_dispatch] lower_dispatch_case_tm
val lower_dispatch_case_reduced = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  (rhs (concl lower_dispatch_case_rewritten))
val lower_dispatch_case =
  TRANS lower_dispatch_case_rewritten lower_dispatch_case_reduced
val after_lower_dload =
  PURE_REWRITE_RULE [lower_dispatch_case] lower_context_exposed
val concretize_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_lower_dload))
val _ = assert_closed "ConcretizeMemLoc residual fold" concretize_fold_tm
val (_, concretize_fold_args) = strip_comb concretize_fold_tm
val (concretize_passes, _) =
  listSyntax.dest_list (List.nth (concretize_fold_args, 2))
val _ =
  if not (null concretize_passes) andalso
     aconv (hd concretize_passes) ``CFP_Simple VP_ConcretizeMemLoc``
  then () else raise Fail "post-LowerDload fold is not headed by ConcretizeMemLoc"

Theorem exact_empty_runtime_after_lower_dload:
  ^(concl after_lower_dload)
Proof
  ACCEPT_TAC after_lower_dload
QED

fun normalize_residual_context label context =
  let
    val fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
      (rhs (concl context))
  in
    if null (free_vars fold_tm) then context
    else
      let
        fun is_closed_enclosing_case t =
          head_is ``option_CASE`` t andalso null (free_vars t) andalso
          can (find_term (fn u => aconv u fold_tm)) t
        val candidates = find_terms is_closed_enclosing_case (rhs (concl context))
        val _ = if null candidates then
                  raise Fail (label ^ " has no closed enclosing option case")
                else ()
        fun smaller (t, best) =
          if term_size t < term_size best then t else best
        val enclosing_case_tm =
          foldl smaller (hd candidates) (tl candidates)
        val enclosing_case = computeLib.RESTR_EVAL_CONV
          [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
          enclosing_case_tm
        val next = PURE_REWRITE_RULE [enclosing_case] context
        val next_fold = find_head_arity ``run_configured_fn_pass_fold`` 7
          (rhs (concl next))
      in
        if null (free_vars next_fold) then next
        else raise Fail (label ^ " enclosing option-case reduction did not close residual fold: " ^
          term_to_string next_fold)
      end
  end

fun advance_pass expected label context =
  let
    val fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
      (rhs (concl context))
    val _ = assert_closed (label ^ " residual fold") fold_tm
    val (_, fold_args) = strip_comb fold_tm
    val (passes, _) = listSyntax.dest_list (List.nth (fold_args, 2))
    val _ =
      if not (null passes) andalso aconv (hd passes) expected then ()
      else raise Fail (label ^ " residual fold has the wrong head pass")
    val fold_one =
      REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
        fold_tm
    val unit_case_tm = find_term is_dispatch_case (rhs (concl fold_one))
    val _ = assert_closed (label ^ " unit option case") unit_case_tm
    val unit_case = computeLib.RESTR_EVAL_CONV
      [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
      unit_case_tm
    val fold_exposed = PURE_REWRITE_RULE [unit_case] fold_one
    val context_exposed = PURE_REWRITE_RULE [fold_exposed] context
    val dispatch_tm = find_head_arity ``execute_configured_fn_pass`` 5
      (rhs (concl context_exposed))
    val _ = assert_closed (label ^ " dispatcher") dispatch_tm
    val (_, dispatch_args) = strip_comb dispatch_tm
    val _ =
      if aconv (List.nth (dispatch_args, 1)) expected then ()
      else raise Fail (label ^ " dispatcher has the wrong pass")
    val exact_dispatch = computeLib.EVAL_CONV dispatch_tm
    val context_rewritten =
      PURE_REWRITE_RULE [exact_dispatch] context_exposed
    val after = CONV_RULE
      (RAND_CONV (computeLib.RESTR_EVAL_CONV
        [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]))
      context_rewritten
  in
    (exact_dispatch, context_exposed, after)
  end

val (exact_concretize_dispatch, concretize_context_exposed,
     after_concretize) =
  advance_pass ``CFP_Simple VP_ConcretizeMemLoc`` "ConcretizeMemLoc"
    after_lower_dload

Theorem exact_empty_runtime_concretize_mem_loc_dispatch:
  ^(concl exact_concretize_dispatch)
Proof
  ACCEPT_TAC exact_concretize_dispatch
QED

Theorem exact_empty_runtime_after_concretize_mem_loc:
  ^(concl after_concretize)
Proof
  ACCEPT_TAC after_concretize
QED

val fmp_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_concretize))
val _ = assert_closed "FmpLowering residual fold" fmp_fold_tm
val fmp_fold_one =
  REWR_CONV (cj 2 venomFnScheduleRunnerTheory.run_configured_fn_pass_fold_def)
    fmp_fold_tm
val fmp_unit_case_tm = find_term is_dispatch_case (rhs (concl fmp_fold_one))
val _ = assert_closed "FmpLowering unit option case" fmp_unit_case_tm
val fmp_unit_case = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  fmp_unit_case_tm
val fmp_fold_exposed = PURE_REWRITE_RULE [fmp_unit_case] fmp_fold_one
val fmp_context_exposed =
  PURE_REWRITE_RULE [fmp_fold_exposed] after_concretize
val fmp_dispatch_tm = find_head_arity ``execute_configured_fn_pass`` 5
  (rhs (concl fmp_context_exposed))
val _ = assert_closed "FmpLowering dispatcher" fmp_dispatch_tm
val (_, fmp_dispatch_args) = strip_comb fmp_dispatch_tm
val _ =
  if length fmp_dispatch_args = 5 andalso
     aconv (List.nth (fmp_dispatch_args, 1))
       ``CFP_Simple VP_FmpLowering``
  then () else raise Fail "FmpLowering dispatcher argument shape mismatch"
val fmp_policy_tm = List.nth (fmp_dispatch_args, 0)
val fmp_unit_tm = List.nth (fmp_dispatch_args, 2)
val fmp_supply_tm = List.nth (fmp_dispatch_args, 3)
val fmp_function_tm = List.nth (fmp_dispatch_args, 4)
val fmp_dispatch_unfold =
  REWR_CONV venomPassDispatcherTheory.execute_configured_fn_pass_fmp
    fmp_dispatch_tm
val fmp_lower_tm = find_head_arity ``fmp_lower_function`` 3
  (rhs (concl fmp_dispatch_unfold))
val (_, fmp_lower_args) = strip_comb fmp_lower_tm
val fmp_context_tm = List.nth (fmp_lower_args, 0)
val _ = assert_closed "FmpLowering policy" fmp_policy_tm
val _ = assert_closed "FmpLowering unit" fmp_unit_tm
val _ = assert_closed "FmpLowering context" fmp_context_tm
val _ = assert_closed "FmpLowering supply" fmp_supply_tm
val _ = assert_closed "FmpLowering function" fmp_function_tm

val fmp_analysis_tm = list_mk_comb
  (``analyze_fmp_context``, [fmp_context_tm])
val exact_fmp_analysis_raw = computeLib.EVAL_CONV fmp_analysis_tm
val fmp_analysis_rhs = rhs (concl exact_fmp_analysis_raw)
val (_, fmp_analysis_result_args) = strip_comb fmp_analysis_rhs
val _ =
  if head_is ``SOME`` fmp_analysis_rhs andalso
     length fmp_analysis_result_args = 1
  then () else raise Fail "empty-runtime FMP analysis did not return SOME"
val fmp_infos_tm = hd fmp_analysis_result_args
val _ = assert_closed "empty-runtime FMP analysis information" fmp_infos_tm

Definition empty_runtime_fmp_infos_def:
  empty_runtime_fmp_infos = ^fmp_infos_tm
End

val exact_fmp_analysis =
  REWRITE_RULE [GSYM empty_runtime_fmp_infos_def] exact_fmp_analysis_raw

Theorem exact_empty_runtime_fmp_analysis:
  ^(concl exact_fmp_analysis)
Proof
  ACCEPT_TAC exact_fmp_analysis
QED

Theorem exact_empty_runtime_fmp_info_valid:
  fmp_info_valid ^fmp_context_tm empty_runtime_fmp_infos
Proof
  irule fmpAnalysisPropsTheory.analyze_fmp_context_valid >>
  ACCEPT_TAC exact_empty_runtime_fmp_analysis
QED

val fmp_lower_input_tm = list_mk_comb
  (``fmp_lower_input``, [fmp_infos_tm, fmp_context_tm, fmp_function_tm])
val exact_fmp_lower_input_raw = computeLib.EVAL_CONV fmp_lower_input_tm
val exact_fmp_lower_input =
  REWRITE_RULE [GSYM empty_runtime_fmp_infos_def] exact_fmp_lower_input_raw

Theorem exact_empty_runtime_fmp_lower_input:
  ^(concl exact_fmp_lower_input)
Proof
  ACCEPT_TAC exact_fmp_lower_input
QED

val fmp_lookup_tm =
  ``FLOOKUP ^fmp_infos_tm (^fmp_function_tm).fn_name``
val exact_fmp_lookup_raw = computeLib.EVAL_CONV fmp_lookup_tm
val exact_fmp_lookup =
  REWRITE_RULE [GSYM empty_runtime_fmp_infos_def] exact_fmp_lookup_raw

Theorem exact_empty_runtime_fmp_bottom_lookup:
  ^(concl exact_fmp_lookup)
Proof
  ACCEPT_TAC exact_fmp_lookup
QED


Theorem empty_runtime_bb_well_formed_snoc[local]:
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

Theorem empty_runtime_fn_inst_wf_from_blocks[local]:
  (!bb. MEM bb fn.fn_blocks ==>
        EVERY inst_wf bb.bb_instructions) ==>
  fn_inst_wf fn
Proof
  rw[venomWfTheory.fn_inst_wf_def] >>
  first_x_assum drule >>
  simp[listTheory.EVERY_MEM]
QED

fun eval_fmp_closed label tm =
  let
    val _ = assert_closed label tm
  in
    computeLib.EVAL_CONV tm
  end

val fmp_blocks_th = eval_fmp_closed "FMP function block projection"
  ``(^fmp_function_tm).fn_blocks``
val fmp_blocks = fst (listSyntax.dest_list (rhs (concl fmp_blocks_th)))
val _ = if length fmp_blocks = 1 then ()
        else raise Fail ("FMP function block count: " ^
          Int.toString (length fmp_blocks))
val fmp_bb0_tm = hd fmp_blocks
fun fmp_block_instructions label bb =
  let
    val th = eval_fmp_closed label ``(^bb).bb_instructions``
    val insts = fst (listSyntax.dest_list (rhs (concl th)))
  in
    (th, insts)
  end

val (fmp_bb0_insts_th, fmp_bb0_insts) =
  fmp_block_instructions "FMP block 0 instruction projection" fmp_bb0_tm
val _ = if length fmp_bb0_insts = 4 then ()
        else raise Fail "FMP block 0 does not have exactly four instructions"

val fmp_bb0_succs_th = eval_fmp_closed "FMP block 0 successors"
  ``bb_succs ^fmp_bb0_tm``

Theorem empty_runtime_fmp_blocks_shape[local]:
  ^(concl fmp_blocks_th)
Proof
  ACCEPT_TAC fmp_blocks_th
QED

Theorem empty_runtime_fmp_bb0_instructions_shape[local]:
  ^(concl fmp_bb0_insts_th)
Proof
  ACCEPT_TAC fmp_bb0_insts_th
QED

Theorem empty_runtime_fmp_bb0_succs_shape[local]:
  ^(concl fmp_bb0_succs_th)
Proof
  ACCEPT_TAC fmp_bb0_succs_th
QED
Theorem empty_runtime_fmp_bb0_snoc_shape[local]:
  ^fmp_bb0_tm =
    <| bb_label := (^fmp_bb0_tm).bb_label;
       bb_instructions := FRONT ((^fmp_bb0_tm).bb_instructions) ++
                          [LAST ((^fmp_bb0_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED

Theorem empty_runtime_fmp_bb0_well_formed[local]:
  bb_well_formed ^fmp_bb0_tm
Proof
  once_rewrite_tac[empty_runtime_fmp_bb0_snoc_shape] >>
  irule empty_runtime_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem empty_runtime_fmp_bb0_instructions_wf[local]:
  EVERY inst_wf (^fmp_bb0_tm).bb_instructions
Proof
  EVAL_TAC >> simp[]
QED

Theorem exact_empty_runtime_fmp_function_not_well_formed:
  ~wf_function ^fmp_function_tm
Proof
  simp[venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def,
       venomWfTheory.fn_succs_closed_def,
       venomWfTheory.fn_inst_ids_distinct_def,
       venomInstTheory.fn_labels_def,
       empty_runtime_fmp_blocks_shape,
       empty_runtime_fmp_bb0_well_formed,
       empty_runtime_fmp_bb0_succs_shape] >>
  qexists `"@fallback_0"` >> simp[]
QED


Theorem exact_empty_runtime_fmp_reclaims_rejected:
  analyze_fmp_reclaims empty_runtime_fmp_infos
    ^fmp_context_tm ^fmp_function_tm = NONE
Proof
  simp[fmpReclaimDefsTheory.analyze_fmp_reclaims_def,
       exact_empty_runtime_fmp_function_not_well_formed]
QED

Theorem exact_empty_runtime_fmp_with_info_rejected:
  fmp_lower_function_with_info empty_runtime_fmp_infos
    ^fmp_context_tm ^fmp_supply_tm ^fmp_function_tm = NONE
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_with_info_def,
       exact_empty_runtime_fmp_info_valid,
       exact_empty_runtime_fmp_lower_input,
       exact_empty_runtime_fmp_bottom_lookup,
       exact_empty_runtime_fmp_reclaims_rejected]
QED


val exact_fmp_lower_rejected =
  REWR_CONV fmpLowerDefsTheory.fmp_lower_function_def fmp_lower_tm
  |> CONV_RULE (RAND_CONV (REWRITE_CONV
       [exact_fmp_analysis, exact_empty_runtime_fmp_with_info_rejected]))

Theorem exact_empty_runtime_fmp_lower_rejected:
  ^(concl exact_fmp_lower_rejected)
Proof
  ACCEPT_TAC exact_fmp_lower_rejected
QED

val exact_fmp_dispatch_rejected =
  fmp_dispatch_unfold
  |> CONV_RULE (RAND_CONV (REWRITE_CONV [exact_fmp_lower_rejected]))

Theorem exact_empty_runtime_fmp_dispatch_rejected:
  ^(concl exact_fmp_dispatch_rejected)
Proof
  ACCEPT_TAC exact_fmp_dispatch_rejected
QED

val fmp_dispatch_case_tm =
  find_term (is_exact_dispatch_case fmp_dispatch_tm)
    (rhs (concl fmp_context_exposed))
val _ = assert_closed "FmpLowering result option case" fmp_dispatch_case_tm
val fmp_dispatch_case_rewritten =
  REWRITE_CONV [exact_fmp_dispatch_rejected] fmp_dispatch_case_tm
val fmp_dispatch_case_reduced = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  (rhs (concl fmp_dispatch_case_rewritten))
val fmp_dispatch_case_rejected =
  TRANS fmp_dispatch_case_rewritten fmp_dispatch_case_reduced
val after_fmp_rejected =
  PURE_REWRITE_RULE [fmp_dispatch_case_rejected] fmp_context_exposed
val after_fmp_rejected_closed =
  CONV_RULE
    (RAND_CONV (computeLib.RESTR_EVAL_CONV
      [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]))
    after_fmp_rejected


val first_make_ssa_dispatch_tm =
  lhs (concl evalCompilerBytecodeMakeSSAResultTheory.exact_empty_runtime_first_make_ssa_result)
val (_, first_make_ssa_dispatch_args) = strip_comb first_make_ssa_dispatch_tm
val pre_make_ssa_function_tm = List.nth (first_make_ssa_dispatch_args, 4)
val (_, concretize_dispatch_args_for_provenance) =
  strip_comb (lhs (concl exact_concretize_dispatch))
val post_lower_dload_function_tm =
  List.nth (concretize_dispatch_args_for_provenance, 4)

fun eval_cfg_projection label fn_tm =
  let
    val _ = assert_closed (label ^ " function") fn_tm
    fun normalize th =
      CONV_RULE (RAND_CONV (SIMP_CONV (srw_ss ()) [])) th
    val labels = normalize (computeLib.EVAL_CONV
      ``MAP bb_label (^fn_tm).fn_blocks``)
    val succs = normalize (computeLib.EVAL_CONV
      ``MAP bb_succs (^fn_tm).fn_blocks``)
    val closed = normalize (computeLib.EVAL_CONV ``fn_succs_closed ^fn_tm``)
  in
    (labels, succs, closed)
  end


fun first_unit_function label unit_tm =
  let
    val functions_th = computeLib.EVAL_CONV
      ``(^unit_tm).cu_context.ctx_functions``
    val (functions, _) = listSyntax.dest_list (rhs (concl functions_th))
  in
    if length functions = 1 then hd functions
    else raise Fail (label ^ " does not contain exactly one function")
  end

val raw_pre_walk_call_tm =
  lhs (concl evalCompilerBytecodeSimplifyCfgResultTheory.exact_empty_runtime_pre_walk_result)
val (_, raw_pre_walk_call_args) = strip_comb raw_pre_walk_call_tm
val raw_runtime_unit_tm = List.nth (raw_pre_walk_call_args, 2)
val raw_runtime_function_tm =
  first_unit_function "raw runtime unit" raw_runtime_unit_tm
val pre_walk_function_tm = first_unit_function "pre-walk unit"
  ``empty_runtime_pre_walk_unit``
val selected_walk_function_tm = first_unit_function "selected walk unit"
  ``empty_runtime_walk_unit``

val (raw_runtime_labels, raw_runtime_succs, raw_runtime_closed) =
  eval_cfg_projection "raw runtime" raw_runtime_function_tm
val (pre_walk_labels, pre_walk_succs, pre_walk_closed) =
  eval_cfg_projection "post-pre-walk" pre_walk_function_tm
val (selected_walk_labels, selected_walk_succs, selected_walk_closed) =
  eval_cfg_projection "selected walk" selected_walk_function_tm
val raw_runtime_blocks = fst (listSyntax.dest_list
  (rhs (concl (computeLib.EVAL_CONV ``(^raw_runtime_function_tm).fn_blocks``))))
val pre_walk_blocks = fst (listSyntax.dest_list
  (rhs (concl (computeLib.EVAL_CONV ``(^pre_walk_function_tm).fn_blocks``))))
val selected_walk_blocks = fst (listSyntax.dest_list
  (rhs (concl (computeLib.EVAL_CONV ``(^selected_walk_function_tm).fn_blocks``))))
val _ =
  if map length [raw_runtime_blocks, pre_walk_blocks, selected_walk_blocks] = [3,1,1]
  then ()
  else raise Fail "expected CFG block-count transition 3 -> 1 -> 1"
val (pre_make_ssa_labels, pre_make_ssa_succs, pre_make_ssa_closed) =
  eval_cfg_projection "pre-MakeSSA" pre_make_ssa_function_tm
val (post_make_ssa_labels, post_make_ssa_succs, post_make_ssa_closed) =
  eval_cfg_projection "post-MakeSSA" (List.nth (lower_dispatch_args, 4))
val (post_lower_dload_labels, post_lower_dload_succs, post_lower_dload_closed) =
  eval_cfg_projection "post-LowerDload" post_lower_dload_function_tm
val (post_concretize_labels, post_concretize_succs, post_concretize_closed) =
  eval_cfg_projection "post-ConcretizeMemLoc" fmp_function_tm

val first_simplify_cfg_input_tm = ``first_simplify_cfg_operand``
val first_simplify_cfg_output_tm = ``first_simplify_cfg_round1_fn``
val (first_simplify_input_labels, first_simplify_input_succs,
     first_simplify_input_closed) =
  eval_cfg_projection "first SimplifyCFG input" first_simplify_cfg_input_tm
val (first_simplify_output_labels, first_simplify_output_succs,
     first_simplify_output_closed) =
  eval_cfg_projection "first SimplifyCFG output" first_simplify_cfg_output_tm
val first_simplify_input_blocks = fst (listSyntax.dest_list
  (rhs (concl (computeLib.EVAL_CONV
    ``first_simplify_cfg_operand.fn_blocks``))))
val first_simplify_output_blocks = fst (listSyntax.dest_list
  (rhs (concl (computeLib.EVAL_CONV
    ``first_simplify_cfg_round1_fn.fn_blocks``))))
val _ =
  if map length [first_simplify_input_blocks, first_simplify_output_blocks] = [3,1]
  then ()
  else raise Fail "first SimplifyCFG does not exhibit the 3 -> 1 block loss"

Theorem exact_empty_runtime_first_simplify_cfg_provenance:
  ^(concl first_simplify_input_labels) /\
  ^(concl first_simplify_input_succs) /\
  ^(concl first_simplify_output_labels) /\
  ^(concl first_simplify_output_succs)
Proof
  ACCEPT_TAC (LIST_CONJ
    [first_simplify_input_labels, first_simplify_input_succs,
     first_simplify_output_labels, first_simplify_output_succs])
QED
Theorem exact_empty_runtime_walk_selection_cfg_provenance:
  ^(concl raw_runtime_labels) /\
  ^(concl raw_runtime_succs) /\
  ^(concl pre_walk_labels) /\
  ^(concl pre_walk_succs) /\
  ^(concl selected_walk_labels) /\
  ^(concl selected_walk_succs)
Proof
  ACCEPT_TAC (LIST_CONJ
    [raw_runtime_labels, raw_runtime_succs,
     pre_walk_labels, pre_walk_succs,
     selected_walk_labels, selected_walk_succs])
QED

Theorem exact_empty_runtime_pre_make_ssa_cfg_projection:
  ^(concl pre_make_ssa_labels) /\
  ^(concl pre_make_ssa_succs) /\
  ^(concl pre_make_ssa_closed)
Proof
  ACCEPT_TAC (LIST_CONJ [pre_make_ssa_labels, pre_make_ssa_succs,
                         pre_make_ssa_closed])
QED

Theorem exact_empty_runtime_post_make_ssa_cfg_projection:
  ^(concl post_make_ssa_labels) /\
  ^(concl post_make_ssa_succs) /\
  ^(concl post_make_ssa_closed)
Proof
  ACCEPT_TAC (LIST_CONJ [post_make_ssa_labels, post_make_ssa_succs,
                         post_make_ssa_closed])
QED

Theorem exact_empty_runtime_post_lower_dload_cfg_projection:
  ^(concl post_lower_dload_labels) /\
  ^(concl post_lower_dload_succs) /\
  ^(concl post_lower_dload_closed)
Proof
  ACCEPT_TAC (LIST_CONJ [post_lower_dload_labels, post_lower_dload_succs,
                         post_lower_dload_closed])
QED

Theorem exact_empty_runtime_post_concretize_cfg_projection:
  ^(concl post_concretize_labels) /\
  ^(concl post_concretize_succs) /\
  ^(concl post_concretize_closed)
Proof
  ACCEPT_TAC (LIST_CONJ [post_concretize_labels, post_concretize_succs,
                         post_concretize_closed])
QED
Theorem exact_empty_runtime_after_fmp_lowering_rejected:
  ^(concl after_fmp_rejected_closed)
Proof
  ACCEPT_TAC after_fmp_rejected_closed
QED
val _ = export_theory()
