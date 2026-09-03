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
  generate_fn_plan spill_base_empty_fn 96 7 =
    SOME ([], (init_plan_state 96) with ps_label_counter := 7) /\
  generate_fn_plan_fuel 20 spill_base_empty_fn 96 7 =
    SOME ([], (init_plan_state 96) with ps_label_counter := 7)
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
