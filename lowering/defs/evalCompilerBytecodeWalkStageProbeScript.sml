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
  let val _ = assert_closed label tm
  in computeLib.EVAL_CONV tm end

val fmp_blocks_th = eval_fmp_closed "FMP function block projection"
  ``(^fmp_function_tm).fn_blocks``
val (fmp_blocks, _) = listSyntax.dest_list (rhs (concl fmp_blocks_th))
val _ = if length fmp_blocks = 3 then ()
        else raise Fail ("FMP function block count: " ^
          Int.toString (length fmp_blocks))
val fmp_bb0_tm = List.nth (fmp_blocks, 0)
val fmp_bb1_tm = List.nth (fmp_blocks, 1)
val fmp_bb2_tm = List.nth (fmp_blocks, 2)

fun block_shape bb =
  let
    val insts_th = eval_fmp_closed "FMP block instructions"
      ``(^bb).bb_instructions``
    val insts = fst (listSyntax.dest_list (rhs (concl insts_th)))
    val succs_th = eval_fmp_closed "FMP block successors" ``bb_succs ^bb``
  in (insts_th, insts, succs_th) end
val (fmp_bb0_insts_th, fmp_bb0_insts, fmp_bb0_succs_th) =
  block_shape fmp_bb0_tm
val (fmp_bb1_insts_th, fmp_bb1_insts, fmp_bb1_succs_th) =
  block_shape fmp_bb1_tm
val (fmp_bb2_insts_th, fmp_bb2_insts, fmp_bb2_succs_th) =
  block_shape fmp_bb2_tm
val _ =
  if List.all (fn xs => not (null xs))
       [fmp_bb0_insts, fmp_bb1_insts, fmp_bb2_insts]
  then () else raise Fail "FMP function contains an empty block"
Theorem empty_runtime_fmp_bb0_snoc_shape[local]:
  ^fmp_bb0_tm =
    <| bb_label := (^fmp_bb0_tm).bb_label;
       bb_instructions := FRONT ((^fmp_bb0_tm).bb_instructions) ++
                          [LAST ((^fmp_bb0_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED
Theorem empty_runtime_fmp_bb1_snoc_shape[local]:
  ^fmp_bb1_tm =
    <| bb_label := (^fmp_bb1_tm).bb_label;
       bb_instructions := FRONT ((^fmp_bb1_tm).bb_instructions) ++
                          [LAST ((^fmp_bb1_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED
Theorem empty_runtime_fmp_bb2_snoc_shape[local]:
  ^fmp_bb2_tm =
    <| bb_label := (^fmp_bb2_tm).bb_label;
       bb_instructions := FRONT ((^fmp_bb2_tm).bb_instructions) ++
                          [LAST ((^fmp_bb2_tm).bb_instructions)] |>
Proof
  EVAL_TAC
QED

Theorem empty_runtime_fmp_bb0_well_formed[local]:
  bb_well_formed ^fmp_bb0_tm
Proof
  once_rewrite_tac[empty_runtime_fmp_bb0_snoc_shape] >>
  irule empty_runtime_bb_well_formed_snoc >> EVAL_TAC
QED
Theorem empty_runtime_fmp_bb1_well_formed[local]:
  bb_well_formed ^fmp_bb1_tm
Proof
  once_rewrite_tac[empty_runtime_fmp_bb1_snoc_shape] >>
  irule empty_runtime_bb_well_formed_snoc >> EVAL_TAC
QED
Theorem empty_runtime_fmp_bb2_well_formed[local]:
  bb_well_formed ^fmp_bb2_tm
Proof
  once_rewrite_tac[empty_runtime_fmp_bb2_snoc_shape] >>
  irule empty_runtime_bb_well_formed_snoc >> EVAL_TAC
QED

Theorem empty_runtime_fmp_bb0_instructions_wf[local]:
  EVERY inst_wf (^fmp_bb0_tm).bb_instructions
Proof
  EVAL_TAC >> simp[]
QED
Theorem empty_runtime_fmp_bb1_instructions_wf[local]:
  EVERY inst_wf (^fmp_bb1_tm).bb_instructions
Proof
  simp[venomWfTheory.inst_wf_def]
QED
Theorem empty_runtime_fmp_bb2_instructions_wf[local]:
  EVERY inst_wf (^fmp_bb2_tm).bb_instructions
Proof
  EVAL_TAC >> simp[]
QED

Theorem exact_empty_runtime_fmp_function_well_formed:
  wf_function ^fmp_function_tm
Proof
  simp[venomWfTheory.wf_function_def,
       venomWfTheory.fn_has_entry_def,
       venomWfTheory.fn_succs_closed_def,
       venomWfTheory.fn_inst_ids_distinct_def,
       venomInstTheory.fn_labels_def,
       empty_runtime_fmp_bb0_well_formed,
       empty_runtime_fmp_bb1_well_formed,
       empty_runtime_fmp_bb2_well_formed,
       fmp_bb0_succs_th, fmp_bb1_succs_th, fmp_bb2_succs_th] >>
  conj_tac
  >- (rpt strip_tac >>
      gvs[empty_runtime_fmp_bb0_well_formed,
          empty_runtime_fmp_bb1_well_formed,
          empty_runtime_fmp_bb2_well_formed])
  >> rpt strip_tac >>
  gvs[fmp_bb0_succs_th, fmp_bb1_succs_th, fmp_bb2_succs_th]
QED

Theorem exact_empty_runtime_fmp_function_inst_wf:
  fn_inst_wf ^fmp_function_tm
Proof
  irule empty_runtime_fn_inst_wf_from_blocks >>
  rpt strip_tac >>
  gvs[fmp_blocks_th,
      empty_runtime_fmp_bb0_instructions_wf,
      empty_runtime_fmp_bb1_instructions_wf,
      empty_runtime_fmp_bb2_instructions_wf]
QED

val fmp_reclaim_states_tm =
  ``fmp_reclaim_states ^fmp_function_tm``
val exact_fmp_reclaim_states_raw =
  eval_fmp_closed "empty-runtime FMP reclaim states" fmp_reclaim_states_tm
val fmp_reclaim_states_rhs = rhs (concl exact_fmp_reclaim_states_raw)
val (_, fmp_reclaim_states_result_args) = strip_comb fmp_reclaim_states_rhs
val _ =
  if head_is ``SOME`` fmp_reclaim_states_rhs andalso
     length fmp_reclaim_states_result_args = 1
  then () else raise Fail "empty-runtime FMP reclaim states did not return SOME"
val fmp_states_tm = hd fmp_reclaim_states_result_args
val _ = assert_closed "empty-runtime FMP reclaim-state payload" fmp_states_tm

Definition empty_runtime_fmp_states_def:
  empty_runtime_fmp_states = ^fmp_states_tm
End

val exact_fmp_reclaim_states =
  REWRITE_RULE [GSYM empty_runtime_fmp_states_def]
    exact_fmp_reclaim_states_raw

Theorem exact_empty_runtime_fmp_reclaim_states:
  ^(concl exact_fmp_reclaim_states)
Proof
  ACCEPT_TAC exact_fmp_reclaim_states
QED

val fmp_candidate_tm = list_mk_comb
  (``fmp_candidate_plan``,
   [fmp_infos_tm, fmp_context_tm, fmp_function_tm, fmp_states_tm])
val exact_fmp_candidate_raw =
  eval_fmp_closed "empty-runtime FMP candidate plan" fmp_candidate_tm
val exact_fmp_candidate =
  REWRITE_RULE [GSYM empty_runtime_fmp_infos_def,
                GSYM empty_runtime_fmp_states_def]
    exact_fmp_candidate_raw

Theorem exact_empty_runtime_fmp_candidate_empty:
  ^(concl exact_fmp_candidate)
Proof
  ACCEPT_TAC exact_fmp_candidate
QED

Theorem exact_empty_runtime_fmp_reclaim_result:
  analyze_fmp_reclaims empty_runtime_fmp_infos ^fmp_context_tm
    ^fmp_function_tm = SOME FEMPTY
Proof
  irule fmpReclaimPropsTheory.analyze_fmp_reclaims_ready >>
  simp[exact_empty_runtime_fmp_info_valid,
       exact_empty_runtime_fmp_function_well_formed,
       exact_empty_runtime_fmp_function_inst_wf,
       exact_empty_runtime_fmp_reclaim_states,
       exact_empty_runtime_fmp_candidate_empty,
       fmpReclaimDefsTheory.fmp_reclaim_plan_ok_def] >>
  EVAL_TAC
QED

Theorem exact_empty_runtime_fmp_reclaim_input:
  fmp_reclaim_input ^fmp_function_tm FEMPTY
Proof
  simp[fmpLowerDefsTheory.fmp_reclaim_input_def]
QED


val fmp_checked_seal_tm = list_mk_comb
  (``fmp_checked_seal``,
   [fmp_context_tm, fmp_function_tm, ``fmp_info_bottom``,
    ``(^fmp_function_tm).fn_blocks``])
val exact_fmp_checked_seal_raw =
  eval_fmp_closed "empty-runtime FMP checked seal" fmp_checked_seal_tm
val fmp_checked_seal_rhs = rhs (concl exact_fmp_checked_seal_raw)
val (_, fmp_checked_seal_result_args) = strip_comb fmp_checked_seal_rhs
val _ =
  if head_is ``SOME`` fmp_checked_seal_rhs andalso
     length fmp_checked_seal_result_args = 1
  then () else raise Fail "empty-runtime FMP checked seal did not return SOME"
val fmp_sealed_function_tm = hd fmp_checked_seal_result_args
val _ = assert_closed "empty-runtime sealed FMP function" fmp_sealed_function_tm

Definition empty_runtime_fmp_sealed_function_def:
  empty_runtime_fmp_sealed_function = ^fmp_sealed_function_tm
End

val exact_fmp_checked_seal =
  exact_fmp_checked_seal_raw
  |> SIMP_RULE (srw_ss ()) [fmpAnalysisDefsTheory.fmp_info_bottom_def]
  |> REWRITE_RULE [GSYM empty_runtime_fmp_sealed_function_def]

Theorem exact_empty_runtime_fmp_checked_seal:
  ^(concl exact_fmp_checked_seal)
Proof
  ACCEPT_TAC exact_fmp_checked_seal
QED

Theorem exact_empty_runtime_fmp_with_info:
  fmp_lower_function_with_info empty_runtime_fmp_infos ^fmp_context_tm
    ^fmp_supply_tm ^fmp_function_tm =
  SOME (empty_runtime_fmp_sealed_function,^fmp_supply_tm)
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_with_info_def,
       exact_empty_runtime_fmp_info_valid,
       exact_empty_runtime_fmp_lower_input,
       exact_empty_runtime_fmp_bottom_lookup,
       exact_empty_runtime_fmp_reclaim_result,
       exact_empty_runtime_fmp_reclaim_input,
       exact_empty_runtime_fmp_checked_seal,
       fmpAnalysisDefsTheory.fmp_info_bottom_def]
QED

val exact_fmp_with_info_normalized =
  SIMP_RULE (srw_ss ()) [] exact_empty_runtime_fmp_with_info

Theorem exact_empty_runtime_fmp_lower:
  fmp_lower_function ^fmp_context_tm ^fmp_supply_tm ^fmp_function_tm =
  SOME (empty_runtime_fmp_sealed_function,^fmp_supply_tm)
Proof
  simp[fmpLowerDefsTheory.fmp_lower_function_def,
       exact_empty_runtime_fmp_analysis,
       exact_fmp_with_info_normalized]
QED

val exact_fmp_dispatch =
  fmp_dispatch_unfold
  |> CONV_RULE (RAND_CONV (REWRITE_CONV [exact_empty_runtime_fmp_lower]))
  |> CONV_RULE (RAND_CONV (computeLib.RESTR_EVAL_CONV
       [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]))
val _ =
  if head_is ``SOME`` (rhs (concl exact_fmp_dispatch)) then ()
  else raise Fail ("corrected FMP dispatcher did not return SOME: " ^
    term_to_string (rhs (concl exact_fmp_dispatch)))

Theorem exact_empty_runtime_fmp_dispatch:
  ^(concl exact_fmp_dispatch)
Proof
  ACCEPT_TAC exact_fmp_dispatch
QED

val fmp_dispatch_case_tm =
  find_term (is_exact_dispatch_case fmp_dispatch_tm)
    (rhs (concl fmp_context_exposed))
val _ = assert_closed "FmpLowering result option case" fmp_dispatch_case_tm
val fmp_dispatch_case_rewritten =
  REWRITE_CONV [exact_fmp_dispatch] fmp_dispatch_case_tm
val fmp_dispatch_case_reduced = computeLib.RESTR_EVAL_CONV
  [``execute_configured_fn_pass``, ``run_configured_fn_pass_fold``]
  (rhs (concl fmp_dispatch_case_rewritten))
val fmp_dispatch_case =
  TRANS fmp_dispatch_case_rewritten fmp_dispatch_case_reduced
val after_fmp = PURE_REWRITE_RULE [fmp_dispatch_case] fmp_context_exposed
val after_fmp_closed = normalize_residual_context "post-FMP" after_fmp
val next_fold_tm = find_head_arity ``run_configured_fn_pass_fold`` 7
  (rhs (concl after_fmp_closed))
val _ = assert_closed "post-FMP residual fold" next_fold_tm
val (_, next_fold_args) = strip_comb next_fold_tm
val (next_passes, _) = listSyntax.dest_list (List.nth (next_fold_args, 2))
val _ =
  if not (null next_passes) andalso
     aconv (hd next_passes) ``CFP_Simple VP_MakeSSA``
  then () else raise Fail "post-FMP residual fold is not headed by MakeSSA"

Theorem exact_empty_runtime_after_fmp_lowering:
  ^(concl after_fmp_closed)
Proof
  ACCEPT_TAC after_fmp_closed
QED

val _ = export_theory();
