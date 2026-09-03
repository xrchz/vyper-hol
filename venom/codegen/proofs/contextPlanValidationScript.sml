(*
 * Focused executable checks for the checked context spill planner.
 *)

Theory contextPlanValidation
Ancestors
  contextPlanProps spillBaseValidation stackPlanGen
Libs
  BasicProvers
Theorem context_plan_dimindex_256[local,simp]:
  dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED


Definition context_plan_empty_zero_ctx_def:
  context_plan_empty_zero_ctx =
    <|ctx_functions := []; ctx_entry := NONE; ctx_global_reserved := []|>
End

Definition context_plan_empty_global_ctx_def:
  context_plan_empty_global_ctx =
    <|ctx_functions := []; ctx_entry := NONE;
      ctx_global_reserved := [(64,32)]|>
End

Theorem context_plan_empty_eval:
  generate_context_plan context_plan_empty_zero_ctx =
    SOME <|cp_regions := []; cp_max_static_eom := 0;
           cp_peak_spill_end := 0; cp_initial_fmp := 0|> /\
  generate_context_plan context_plan_empty_global_ctx =
    SOME <|cp_regions := []; cp_max_static_eom := 96;
           cp_peak_spill_end := 0; cp_initial_fmp := 96|>
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Definition context_plan_missing_ctx_def:
  context_plan_missing_ctx =
    <|ctx_functions := [spill_base_empty_fn]; ctx_entry := NONE;
      ctx_global_reserved := []|>
End

Definition context_plan_zero_size_ctx_def:
  context_plan_zero_size_ctx =
    <|ctx_functions := []; ctx_entry := NONE;
      ctx_global_reserved := [(64,0)]|>
End

Definition context_plan_overlap_ctx_def:
  context_plan_overlap_ctx =
    <|ctx_functions := []; ctx_entry := NONE;
      ctx_global_reserved := [(64,32); (80,32)]|>
End

Definition context_plan_reserved_overflow_ctx_def:
  context_plan_reserved_overflow_ctx =
    <|ctx_functions := []; ctx_entry := NONE;
      ctx_global_reserved := [(dimword (:256) - 1,1)]|>
End

Definition context_plan_fmp_overflow_ctx_def:
  context_plan_fmp_overflow_ctx =
    <|ctx_functions := []; ctx_entry := NONE;
      ctx_global_reserved := [(dimword (:256) - 31,1)]|>
End

Theorem context_plan_failure_eval:
  generate_context_plan context_plan_missing_ctx = NONE /\
  generate_context_plan context_plan_zero_size_ctx = NONE /\
  generate_context_plan context_plan_overlap_ctx = NONE /\
  generate_context_plan context_plan_reserved_overflow_ctx = NONE /\
  generate_context_plan context_plan_fmp_overflow_ctx = NONE
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Definition context_plan_first_fn_def:
  context_plan_first_fn =
    spill_base_spilling_fn with <|fn_name := "first"; fn_eom := SOME 64|>
End

Definition context_plan_second_fn_def:
  context_plan_second_fn =
    spill_base_spilling_fn with <|fn_name := "second"; fn_eom := SOME 96|>
End

Definition context_plan_two_fn_ctx_def:
  context_plan_two_fn_ctx =
    <|ctx_functions := [context_plan_first_fn; context_plan_second_fn];
      ctx_entry := SOME "first"; ctx_global_reserved := [(128,32)]|>
End

Theorem context_plan_fn_canonical_eval[local,simp]:
  canonical_param_prefix context_plan_first_fn /\
  canonical_param_prefix context_plan_second_fn
Proof
  EVAL_TAC
QED

Theorem context_plan_first_live_eval[local]:
  liveness_analyze context_plan_first_fn = spill_base_spilling_live
Proof
  EVAL_TAC
QED

Theorem context_plan_first_dfg_eval[local]:
  dfg_build_function context_plan_first_fn = spill_base_spilling_dfg
Proof
  EVAL_TAC
QED

Theorem context_plan_first_cfg_eval[local]:
  cfg_analyze context_plan_first_fn = spill_base_spilling_cfg
Proof
  EVAL_TAC
QED

Theorem context_plan_first_control_eval[local]:
  fn_entry_label context_plan_first_fn = SOME "entry" /\
  lookup_block "entry" context_plan_first_fn.fn_blocks =
    SOME spill_base_entry_bb /\
  cfg_succs_of spill_base_spilling_cfg "entry" = []
Proof
  EVAL_TAC
QED

Theorem context_plan_first_producer_eval[local]:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_first_fn spill_base_producer
    ["p17"; "p16"; "p15"; "p14"; "p13"; "p12"; "p11"; "p10";
     "p9"; "p8"; "p7"; "p6"; "p5"; "p4"; "p3"; "p2"; "p1"; "p0"]
    T F "entry" (init_plan_state 160) =
  SOME (spill_base_producer_ops 160, spill_base_after_producer 160)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem context_plan_first_consumer_eval[local]:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_first_fn spill_base_consumer
    [] T T "entry" (spill_base_after_producer 160) =
  SOME (spill_base_consumer_ops, spill_base_after_consumer 160)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem context_plan_first_stop_eval[local]:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_first_fn spill_base_stop
    [] T F "entry" (spill_base_after_consumer 160) =
  SOME ([SOEmit "STOP"], spill_base_after_consumer 160)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem context_plan_first_block_control[local]:
  HD context_plan_first_fn.fn_blocks = spill_base_entry_bb /\
  spill_base_entry_bb.bb_label = "entry" /\
  spill_base_entry_bb.bb_instructions =
    [spill_base_producer; spill_base_consumer; spill_base_stop] /\
  prepare_params_plan spill_base_spilling_live context_plan_first_fn
    (init_plan_state 160) = ([], init_plan_state 160) /\
  cfg_preds_of spill_base_spilling_cfg "entry" = [] /\
  non_param_insts spill_base_entry_bb =
    [spill_base_producer; spill_base_consumer; spill_base_stop] /\
  bb_is_halting spill_base_entry_bb /\
  get_params spill_base_entry_bb.bb_instructions = [] /\
  live_vars_at spill_base_spilling_live "entry" 1 =
    ["p17"; "p16"; "p15"; "p14"; "p13"; "p12"; "p11"; "p10";
     "p9"; "p8"; "p7"; "p6"; "p5"; "p4"; "p3"; "p2"; "p1"; "p0"] /\
  live_vars_at spill_base_spilling_live "entry" 2 = [] /\
  live_vars_at spill_base_spilling_live "entry" 3 = [] /\
  ~is_terminator spill_base_consumer.inst_opcode /\
  is_terminator spill_base_stop.inst_opcode
Proof
  EVAL_TAC >>
  simp[livenessDefsTheory.live_vars_at_def, dfAnalyzeDefsTheory.df_at_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem context_plan_first_block_eval[local]:
  generate_block_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_first_fn spill_base_entry_bb
    (init_plan_state 160) =
  SOME (spill_base_block_ops 160, spill_base_after_consumer 160)
Proof
  simp[generate_block_plan_def, context_plan_first_block_control,
       context_plan_first_producer_eval, context_plan_first_consumer_eval,
       context_plan_first_stop_eval, spill_base_block_ops_def]
QED

Theorem context_plan_first_aux_eval[local]:
  generate_fn_plan_aux spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_first_fn ["entry"] []
    (init_plan_state 160) =
  SOME (spill_base_block_ops 160, ["entry"], spill_base_after_consumer 160)
Proof
  simp[generate_fn_plan_aux_def, context_plan_first_control_eval,
       context_plan_first_block_eval]
QED

Theorem context_plan_first_fn_plan_eval:
  generate_fn_plan context_plan_first_fn 160 0 =
  SOME (spill_base_block_ops 160, spill_base_after_consumer 160)
Proof
  simp[generate_fn_plan_def, context_plan_first_live_eval,
       context_plan_first_dfg_eval, context_plan_first_cfg_eval,
       context_plan_first_control_eval, context_plan_first_aux_eval,
       spillBaseValidationTheory.init_plan_state_counter_zero]
QED

Theorem context_plan_first_region_eval[local]:
  spill_plan_in_region 160 736 (spill_base_block_ops 160)
Proof
  EVAL_TAC
QED

Theorem context_plan_second_live_eval[local]:
  liveness_analyze context_plan_second_fn = spill_base_spilling_live
Proof
  EVAL_TAC
QED

Theorem context_plan_second_dfg_eval[local]:
  dfg_build_function context_plan_second_fn = spill_base_spilling_dfg
Proof
  EVAL_TAC
QED

Theorem context_plan_second_cfg_eval[local]:
  cfg_analyze context_plan_second_fn = spill_base_spilling_cfg
Proof
  EVAL_TAC
QED

Theorem context_plan_second_control_eval[local]:
  fn_entry_label context_plan_second_fn = SOME "entry" /\
  lookup_block "entry" context_plan_second_fn.fn_blocks =
    SOME spill_base_entry_bb /\
  cfg_succs_of spill_base_spilling_cfg "entry" = []
Proof
  EVAL_TAC
QED

Theorem context_plan_second_producer_eval[local]:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_second_fn spill_base_producer
    ["p17"; "p16"; "p15"; "p14"; "p13"; "p12"; "p11"; "p10";
     "p9"; "p8"; "p7"; "p6"; "p5"; "p4"; "p3"; "p2"; "p1"; "p0"]
    T F "entry" (init_plan_state 736) =
  SOME (spill_base_producer_ops 736, spill_base_after_producer 736)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem context_plan_second_consumer_eval[local]:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_second_fn spill_base_consumer
    [] T T "entry" (spill_base_after_producer 736) =
  SOME (spill_base_consumer_ops, spill_base_after_consumer 736)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem context_plan_second_stop_eval[local]:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_second_fn spill_base_stop
    [] T F "entry" (spill_base_after_consumer 736) =
  SOME ([SOEmit "STOP"], spill_base_after_consumer 736)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem context_plan_second_block_control[local]:
  HD context_plan_second_fn.fn_blocks = spill_base_entry_bb /\
  spill_base_entry_bb.bb_label = "entry" /\
  spill_base_entry_bb.bb_instructions =
    [spill_base_producer; spill_base_consumer; spill_base_stop] /\
  prepare_params_plan spill_base_spilling_live context_plan_second_fn
    (init_plan_state 736) = ([], init_plan_state 736) /\
  cfg_preds_of spill_base_spilling_cfg "entry" = [] /\
  non_param_insts spill_base_entry_bb =
    [spill_base_producer; spill_base_consumer; spill_base_stop] /\
  bb_is_halting spill_base_entry_bb /\
  get_params spill_base_entry_bb.bb_instructions = [] /\
  live_vars_at spill_base_spilling_live "entry" 1 =
    ["p17"; "p16"; "p15"; "p14"; "p13"; "p12"; "p11"; "p10";
     "p9"; "p8"; "p7"; "p6"; "p5"; "p4"; "p3"; "p2"; "p1"; "p0"] /\
  live_vars_at spill_base_spilling_live "entry" 2 = [] /\
  live_vars_at spill_base_spilling_live "entry" 3 = [] /\
  ~is_terminator spill_base_consumer.inst_opcode /\
  is_terminator spill_base_stop.inst_opcode
Proof
  EVAL_TAC >>
  simp[livenessDefsTheory.live_vars_at_def, dfAnalyzeDefsTheory.df_at_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem context_plan_second_block_eval[local]:
  generate_block_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_second_fn spill_base_entry_bb
    (init_plan_state 736) =
  SOME (spill_base_block_ops 736, spill_base_after_consumer 736)
Proof
  simp[generate_block_plan_def, context_plan_second_block_control,
       context_plan_second_producer_eval, context_plan_second_consumer_eval,
       context_plan_second_stop_eval, spill_base_block_ops_def]
QED

Theorem context_plan_second_aux_eval[local]:
  generate_fn_plan_aux spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg context_plan_second_fn ["entry"] []
    (init_plan_state 736) =
  SOME (spill_base_block_ops 736, ["entry"], spill_base_after_consumer 736)
Proof
  simp[generate_fn_plan_aux_def, context_plan_second_control_eval,
       context_plan_second_block_eval]
QED

Theorem context_plan_second_fn_plan_eval:
  generate_fn_plan context_plan_second_fn 736 0 =
  SOME (spill_base_block_ops 736, spill_base_after_consumer 736)
Proof
  simp[generate_fn_plan_def, context_plan_second_live_eval,
       context_plan_second_dfg_eval, context_plan_second_cfg_eval,
       context_plan_second_control_eval, context_plan_second_aux_eval,
       spillBaseValidationTheory.init_plan_state_counter_zero]
QED

Theorem context_plan_second_region_eval[local]:
  spill_plan_in_region 736 1312 (spill_base_block_ops 736)
Proof
  EVAL_TAC
QED

Theorem context_plan_two_fn_eval:
  case generate_context_plan context_plan_two_fn_ctx of
    NONE => F
  | SOME cp =>
      LENGTH cp.cp_regions = 2 /\
      MAP (\r. r.sr_fn_name) cp.cp_regions = ["first"; "second"] /\
      (EL 0 cp.cp_regions).sr_spill_base = 160 /\
      (EL 0 cp.cp_regions).sr_spill_end = 736 /\
      (EL 1 cp.cp_regions).sr_spill_base = 736 /\
      (EL 1 cp.cp_regions).sr_spill_end = 1312 /\
      (EL 0 cp.cp_regions).sr_spill_end <=
        (EL 1 cp.cp_regions).sr_spill_base /\
      cp.cp_peak_spill_end = 1312 /\
      cp.cp_initial_fmp = 1312
Proof
  simp[context_plan_two_fn_ctx_def, generate_context_plan_def,
       generate_context_plan_with_def, max_live_eom_def, collect_fn_eoms_def,
       generate_context_regions_def, finish_context_plan_def,
       staticLayoutDefsTheory.reserved_intervals_wf_def,
       staticLayoutDefsTheory.reserved_intervals_disjoint_def,
       staticLayoutDefsTheory.reserved_interval_wf_def,
       staticLayoutDefsTheory.global_reserved_end_def,
       context_plan_first_fn_def, context_plan_second_fn_def] >>
  rewrite_tac[GSYM context_plan_first_fn_def, GSYM context_plan_second_fn_def] >>
  simp[context_plan_first_fn_plan_eval, context_plan_second_fn_plan_eval,
       context_plan_first_region_eval, context_plan_second_region_eval,
       generate_context_regions_def, finish_context_plan_def,
       spill_base_after_consumer_def, venomLayoutTheory.ceil32_def,
       wordsTheory.dimword_def]
QED

val _ = export_theory();
