Theory spillBaseValidation
Ancestors
  stackPlanGen
Libs
  BasicProvers

Definition spill_base_empty_fn_def:
  spill_base_empty_fn = mk_raw_function "spill_base_empty" []
End

Definition spill_base_outputs_def:
  spill_base_outputs =
    ["p0"; "p1"; "p2"; "p3"; "p4"; "p5"; "p6"; "p7";
     "p8"; "p9"; "p10"; "p11"; "p12"; "p13"; "p14";
     "p15"; "p16"; "p17"]
End

Definition spill_base_inputs_def:
  spill_base_inputs =
    [Var "p17"; Var "p16"; Var "p15"; Var "p14"; Var "p13";
     Var "p12"; Var "p11"; Var "p10"; Var "p9"; Var "p8";
     Var "p7"; Var "p6"; Var "p5"; Var "p4"; Var "p3";
     Var "p2"; Var "p1"; Var "p0"]
End

Definition spill_base_producer_def:
  spill_base_producer = mk_inst 0 ADD [] spill_base_outputs
End

Definition spill_base_consumer_def:
  spill_base_consumer = mk_inst 1 ADD spill_base_inputs []
End

Definition spill_base_stop_def:
  spill_base_stop = mk_inst 2 STOP [] []
End

Definition spill_base_entry_bb_def:
  spill_base_entry_bb =
    <| bb_label := "entry";
       bb_instructions :=
         [spill_base_producer; spill_base_consumer; spill_base_stop] |>
End

Definition spill_base_spilling_fn_def:
  spill_base_spilling_fn =
    mk_raw_function "spill_base_spilling" [spill_base_entry_bb]
End

Theorem spill_base_empty_plan_eval:
  generate_fn_plan spill_base_empty_fn 96 7 = NONE /\
  generate_fn_plan_fuel 20 spill_base_empty_fn 96 7 = NONE
Proof
  EVAL_TAC
QED

Definition spill_base_spilling_live_def:
  spill_base_spilling_live =
    <| ds_inst :=
         FUNION
           (FEMPTY |+ (("entry", 3), [])
                   |+ (("entry", 2), [])
                   |+ (("entry", 1),
                       ["p17"; "p16"; "p15"; "p14"; "p13"; "p12";
                        "p11"; "p10"; "p9"; "p8"; "p7"; "p6"; "p5";
                        "p4"; "p3"; "p2"; "p1"; "p0"])
                   |+ (("entry", 0), [])) FEMPTY;
       ds_boundary := FEMPTY |+ ("entry", []) |>
End

Theorem spill_base_spilling_live_eval:
  liveness_analyze spill_base_spilling_fn = spill_base_spilling_live
Proof
  EVAL_TAC
QED

Theorem spill_base_spilling_live_fuel_eval:
  liveness_analyze_fuel 100 spill_base_spilling_fn = spill_base_spilling_live
Proof
  EVAL_TAC
QED

Definition spill_base_spilling_dfg_def:
  spill_base_spilling_dfg =
    <| dfg_uses :=
         FEMPTY |+ ("p17", [spill_base_consumer])
                |+ ("p16", [spill_base_consumer])
                |+ ("p15", [spill_base_consumer])
                |+ ("p14", [spill_base_consumer])
                |+ ("p13", [spill_base_consumer])
                |+ ("p12", [spill_base_consumer])
                |+ ("p11", [spill_base_consumer])
                |+ ("p10", [spill_base_consumer])
                |+ ("p9", [spill_base_consumer])
                |+ ("p8", [spill_base_consumer])
                |+ ("p7", [spill_base_consumer])
                |+ ("p6", [spill_base_consumer])
                |+ ("p5", [spill_base_consumer])
                |+ ("p4", [spill_base_consumer])
                |+ ("p3", [spill_base_consumer])
                |+ ("p2", [spill_base_consumer])
                |+ ("p1", [spill_base_consumer])
                |+ ("p0", [spill_base_consumer]);
       dfg_defs :=
         FEMPTY |+ ("p0", spill_base_producer)
                |+ ("p1", spill_base_producer)
                |+ ("p2", spill_base_producer)
                |+ ("p3", spill_base_producer)
                |+ ("p4", spill_base_producer)
                |+ ("p5", spill_base_producer)
                |+ ("p6", spill_base_producer)
                |+ ("p7", spill_base_producer)
                |+ ("p8", spill_base_producer)
                |+ ("p9", spill_base_producer)
                |+ ("p10", spill_base_producer)
                |+ ("p11", spill_base_producer)
                |+ ("p12", spill_base_producer)
                |+ ("p13", spill_base_producer)
                |+ ("p14", spill_base_producer)
                |+ ("p15", spill_base_producer)
                |+ ("p16", spill_base_producer)
                |+ ("p17", spill_base_producer);
       dfg_ids :=
         FEMPTY |+ (2, spill_base_stop)
                |+ (1, spill_base_consumer)
                |+ (0, spill_base_producer) |>
End

Theorem spill_base_spilling_dfg_eval:
  dfg_build_function spill_base_spilling_fn = spill_base_spilling_dfg
Proof
  EVAL_TAC
QED

Definition spill_base_spilling_cfg_def:
  spill_base_spilling_cfg =
    <| cfg_succs := FEMPTY |+ ("entry", []) |+ ("entry", []);
       cfg_preds := FEMPTY |+ ("entry", []);
       cfg_reachable := FEMPTY |+ ("entry", T);
       cfg_dfs_post := ["entry"];
       cfg_dfs_pre := ["entry"] |>
End

Theorem spill_base_spilling_cfg_eval:
  cfg_analyze spill_base_spilling_fn = spill_base_spilling_cfg
Proof
  EVAL_TAC
QED

Theorem spill_base_spilling_entry_succ_eval:
  entry_block spill_base_spilling_fn = SOME spill_base_entry_bb /\
  cfg_succs_of spill_base_spilling_cfg "entry" = []
Proof
  EVAL_TAC
QED

Definition spill_base_after_producer_def:
  spill_base_after_producer b =
    <| ps_stack :=
         [Var "p17"; Var "p1"; Var "p2"; Var "p3"; Var "p4";
          Var "p5"; Var "p6"; Var "p7"; Var "p8"; Var "p9";
          Var "p10"; Var "p11"; Var "p12"; Var "p13"; Var "p14";
          Var "p15"; Var "p16"; Var "p0"];
       ps_spilled := FEMPTY;
       ps_alloc :=
         <| sa_free_slots :=
              [b; b + 32; b + 64; b + 96; b + 128; b + 160;
               b + 192; b + 224; b + 256; b + 288; b + 320;
               b + 352; b + 384; b + 416; b + 448; b + 480;
               b + 512; b + 544];
            sa_next_offset := b + 576;
            sa_spill_base := b |>;
       ps_label_counter := 0 |>
End

Definition spill_base_producer_ops_def:
  spill_base_producer_ops b =
    [SOEmit "ADD";
     SOSpill b; SOSpill (b + 32); SOSpill (b + 64); SOSpill (b + 96);
     SOSpill (b + 128); SOSpill (b + 160); SOSpill (b + 192);
     SOSpill (b + 224); SOSpill (b + 256); SOSpill (b + 288);
     SOSpill (b + 320); SOSpill (b + 352); SOSpill (b + 384);
     SOSpill (b + 416); SOSpill (b + 448); SOSpill (b + 480);
     SOSpill (b + 512); SOSpill (b + 544);
     SORestore b; SORestore (b + 512); SORestore (b + 480);
     SORestore (b + 448); SORestore (b + 416); SORestore (b + 384);
     SORestore (b + 352); SORestore (b + 320); SORestore (b + 288);
     SORestore (b + 256); SORestore (b + 224); SORestore (b + 192);
     SORestore (b + 160); SORestore (b + 128); SORestore (b + 96);
     SORestore (b + 64); SORestore (b + 32); SORestore (b + 544)]
End

Theorem spill_base_producer_160_eval:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn spill_base_producer
    ["p17"; "p16"; "p15"; "p14"; "p13"; "p12"; "p11"; "p10";
     "p9"; "p8"; "p7"; "p6"; "p5"; "p4"; "p3"; "p2"; "p1"; "p0"]
    T F "entry" (init_plan_state 160) =
  SOME (spill_base_producer_ops 160, spill_base_after_producer 160)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED


Theorem spill_base_producer_224_eval:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn spill_base_producer
    ["p17"; "p16"; "p15"; "p14"; "p13"; "p12"; "p11"; "p10";
     "p9"; "p8"; "p7"; "p6"; "p5"; "p4"; "p3"; "p2"; "p1"; "p0"]
    T F "entry" (init_plan_state 224) =
  SOME (spill_base_producer_ops 224, spill_base_after_producer 224)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Definition spill_base_after_consumer_def:
  spill_base_after_consumer b =
    <| ps_stack := [];
       ps_spilled := FEMPTY;
       ps_alloc :=
         <| sa_free_slots :=
              [b; b + 32; b + 64; b + 96; b + 128; b + 160;
               b + 192; b + 224; b + 256; b + 288; b + 320;
               b + 352; b + 384; b + 416; b + 448; b + 480;
               b + 512; b + 544];
            sa_next_offset := b + 576;
            sa_spill_base := b |>;
       ps_label_counter := 0 |>
End

Definition spill_base_consumer_ops_def:
  spill_base_consumer_ops =
    [SOSwap 1; SOSwap 16; SOSwap 2; SOSwap 15; SOSwap 3; SOSwap 14;
     SOSwap 4; SOSwap 13; SOSwap 5; SOSwap 12; SOSwap 6; SOSwap 11;
     SOSwap 7; SOSwap 10; SOSwap 8; SOSwap 9; SOSwap 8; SOSwap 7;
     SOSwap 6; SOSwap 5; SOSwap 4; SOSwap 3; SOSwap 2; SOEmit "ADD"]
End

Theorem spill_base_consumer_160_eval:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn spill_base_consumer
    [] T T "entry" (spill_base_after_producer 160) =
  SOME (spill_base_consumer_ops, spill_base_after_consumer 160)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem spill_base_consumer_224_eval:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn spill_base_consumer
    [] T T "entry" (spill_base_after_producer 224) =
  SOME (spill_base_consumer_ops, spill_base_after_consumer 224)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem spill_base_stop_160_eval:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn spill_base_stop
    [] T F "entry" (spill_base_after_consumer 160) =
  SOME ([SOEmit "STOP"], spill_base_after_consumer 160)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Theorem spill_base_stop_224_eval:
  generate_inst_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn spill_base_stop
    [] T F "entry" (spill_base_after_consumer 224) =
  SOME ([SOEmit "STOP"], spill_base_after_consumer 224)
Proof
  EVAL_TAC >> simp[listTheory.SET_TO_LIST_EMPTY]
QED

Definition spill_base_block_ops_def:
  spill_base_block_ops b =
    SOLabel "entry" ::
      (spill_base_producer_ops b ++ spill_base_consumer_ops ++
       [SOEmit "STOP"])
End

Theorem spill_base_block_control_eval:
  HD spill_base_spilling_fn.fn_blocks = spill_base_entry_bb /\
  spill_base_entry_bb.bb_label = "entry" /\
  spill_base_entry_bb.bb_instructions =
    [spill_base_producer; spill_base_consumer; spill_base_stop] /\
  prepare_params_plan spill_base_spilling_live spill_base_spilling_fn
    (init_plan_state 160) = ([], init_plan_state 160) /\
  prepare_params_plan spill_base_spilling_live spill_base_spilling_fn
    (init_plan_state 224) = ([], init_plan_state 224) /\
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

Theorem spill_base_block_160_eval:
  generate_block_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn spill_base_entry_bb
    (init_plan_state 160) =
  SOME (spill_base_block_ops 160, spill_base_after_consumer 160)
Proof
  simp[generate_block_plan_def, spill_base_block_control_eval,
       spill_base_producer_160_eval, spill_base_consumer_160_eval,
       spill_base_stop_160_eval, spill_base_block_ops_def]
QED

Theorem spill_base_block_224_eval:
  generate_block_plan spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn spill_base_entry_bb
    (init_plan_state 224) =
  SOME (spill_base_block_ops 224, spill_base_after_consumer 224)
Proof
  simp[generate_block_plan_def, spill_base_block_control_eval,
       spill_base_producer_224_eval, spill_base_consumer_224_eval,
       spill_base_stop_224_eval, spill_base_block_ops_def]
QED


Theorem spill_base_block_160_observables:
  MEM (SOSpill 160) (spill_base_block_ops 160) /\
  (spill_base_after_consumer 160).ps_alloc.sa_spill_base = 160 /\
  160 < (spill_base_after_consumer 160).ps_alloc.sa_next_offset
Proof
  EVAL_TAC
QED

Theorem spill_base_block_224_observables:
  MEM (SOSpill 224) (spill_base_block_ops 224) /\
  (spill_base_after_consumer 224).ps_alloc.sa_spill_base = 224 /\
  224 < (spill_base_after_consumer 224).ps_alloc.sa_next_offset
Proof
  EVAL_TAC
QED


Theorem spill_base_planner_control_eval:
  fn_entry_label spill_base_spilling_fn = SOME "entry" /\
  lookup_block "entry" spill_base_spilling_fn.fn_blocks =
    SOME spill_base_entry_bb
Proof
  EVAL_TAC
QED

Theorem spill_base_fn_aux_160_eval:
  generate_fn_plan_aux spill_base_spilling_live spill_base_spilling_dfg
    spill_base_spilling_cfg spill_base_spilling_fn ["entry"] []
    (init_plan_state 160) =
  SOME (spill_base_block_ops 160, ["entry"], spill_base_after_consumer 160)
Proof
  simp[generate_fn_plan_aux_def, spill_base_planner_control_eval,
       spill_base_block_160_eval, spill_base_spilling_entry_succ_eval]
QED

Theorem spill_base_fn_aux_fuel_224_eval:
  !fuel.
  generate_fn_plan_aux_fuel (SUC (SUC fuel)) spill_base_spilling_live
    spill_base_spilling_dfg spill_base_spilling_cfg spill_base_spilling_fn
    ["entry"] [] (init_plan_state 224) =
  SOME (spill_base_block_ops 224, ["entry"], spill_base_after_consumer 224)
Proof
  gen_tac >>
  simp[generate_fn_plan_aux_fuel_def, spill_base_planner_control_eval,
       spill_base_block_224_eval, spill_base_spilling_entry_succ_eval]
QED


Theorem spill_base_fn_aux_fuel_100_224_eval:
  generate_fn_plan_aux_fuel 100 spill_base_spilling_live
    spill_base_spilling_dfg spill_base_spilling_cfg spill_base_spilling_fn
    ["entry"] [] (init_plan_state 224) =
  SOME (spill_base_block_ops 224, ["entry"], spill_base_after_consumer 224)
Proof
  mp_tac (Q.SPEC `98` spill_base_fn_aux_fuel_224_eval) >> simp[]
QED

Theorem init_plan_state_counter_zero:
  (init_plan_state b with ps_label_counter := 0) = init_plan_state b
Proof
  simp[stackPlanTypesTheory.init_plan_state_def]
QED

Theorem spill_base_spilling_canonical_eval[simp]:
  canonical_param_prefix spill_base_spilling_fn
Proof
  EVAL_TAC
QED

Theorem spill_base_spilling_plan_exact:
  generate_fn_plan spill_base_spilling_fn 160 0 =
  SOME (spill_base_block_ops 160, spill_base_after_consumer 160)
Proof
  simp[generate_fn_plan_def, spill_base_spilling_live_eval,
       spill_base_spilling_dfg_eval, spill_base_spilling_cfg_eval,
       spill_base_planner_control_eval, spill_base_fn_aux_160_eval,
       init_plan_state_counter_zero]
QED

Theorem spill_base_spilling_plan_fuel_exact:
  generate_fn_plan_fuel 100 spill_base_spilling_fn 224 0 =
  SOME (spill_base_block_ops 224, spill_base_after_consumer 224)
Proof
  simp[generate_fn_plan_fuel_def, spill_base_spilling_live_fuel_eval,
       spill_base_spilling_dfg_eval, spill_base_spilling_cfg_eval,
       spill_base_planner_control_eval, spill_base_fn_aux_fuel_100_224_eval,
       init_plan_state_counter_zero]
QED

Theorem spill_base_spilling_plan_eval:
  case generate_fn_plan spill_base_spilling_fn 160 0 of
    NONE => F
  | SOME (ops, ps) =>
      EXISTS (\op. case op of SOSpill off => 160 <= off | _ => F) ops /\
      ps.ps_alloc.sa_spill_base = 160 /\
      160 < ps.ps_alloc.sa_next_offset
Proof
  simp[spill_base_spilling_plan_exact, spill_base_block_ops_def,
       spill_base_producer_ops_def, spill_base_after_consumer_def]
QED

Theorem spill_base_spilling_plan_fuel_eval:
  case generate_fn_plan_fuel 100 spill_base_spilling_fn 224 0 of
    NONE => F
  | SOME (ops, ps) =>
      EXISTS (\op. case op of SOSpill off => 224 <= off | _ => F) ops /\
      ps.ps_alloc.sa_spill_base = 224 /\
      224 < ps.ps_alloc.sa_next_offset
Proof
  simp[spill_base_spilling_plan_fuel_exact, spill_base_block_ops_def,
       spill_base_producer_ops_def, spill_base_after_consumer_def]
QED
