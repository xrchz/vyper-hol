(* Focused executable probes for the conservative FMP reclaim abstraction. *)

Theory fmpReclaimProps
Ancestors
  fmpReclaimDefs
  fmpAnalysisProps

Definition reclaim_straight_fn_def[local]:
  reclaim_straight_fn = mk_raw_function "straight"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 MLOAD [Var "p"] ["x"];
           mk_inst 2 STOP [] []] |>]
End

Definition reclaim_join_fn_def[local]:
  reclaim_join_fn = mk_raw_function "join_veto"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 JNZ [Lit 1w; Label "left"; Label "right"] []] |>;
     <| bb_label := "left";
        bb_instructions :=
          [mk_inst 1 DALLOCA [Lit 32w] ["left_mark"];
           mk_inst 2 JMP [Label "join"] []] |>;
     <| bb_label := "right";
        bb_instructions := [mk_inst 3 JMP [Label "join"] []] |>;
     <| bb_label := "join";
        bb_instructions := [mk_inst 4 STOP [] []] |>]
End

Definition reclaim_divergent_join_fn_def[local]:
  reclaim_divergent_join_fn = mk_raw_function "divergent_join_veto"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["old"];
           mk_inst 1 JNZ [Lit 1w; Label "left"; Label "right"] []] |>;
     <| bb_label := "left";
        bb_instructions :=
          [mk_inst 2 DALLOCA [Lit 32w] ["left"];
           mk_inst 3 JMP [Label "join"] []] |>;
     <| bb_label := "right";
        bb_instructions :=
          [mk_inst 4 DALLOCA [Lit 32w] ["right"];
           mk_inst 5 JMP [Label "join"] []] |>;
     <| bb_label := "join";
        bb_instructions := [mk_inst 6 STOP [] []] |>]
End

Definition reclaim_pin_fn_def[local]:
  reclaim_pin_fn = mk_raw_function "pin_veto"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 ASSIGN [Var "p"] ["q"];
           mk_inst 2 MSTORE [Lit 0w; Var "q"] [];
           mk_inst 3 STOP [] []] |>]
End

Definition reclaim_capture_fn_def[local]:
  reclaim_capture_fn = mk_raw_function "capture_veto"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 GETFMP [] ["captured"];
           mk_inst 1 MSTORE [Lit 0w; Var "captured"] [];
           mk_inst 2 DALLOCA [Lit 32w] ["p"];
           mk_inst 3 STOP [] []] |>]
End

Definition reclaim_loop_fn_def[local]:
  reclaim_loop_fn = mk_raw_function "loop"
    [<| bb_label := "entry";
        bb_instructions := [mk_inst 0 JMP [Label "entry"] []] |>]
End

Definition reclaim_ctx_def[local]:
  reclaim_ctx fn = mk_venom_context [fn] (SOME fn.fn_name)
End

Definition reclaim_infos_def[local]:
  reclaim_infos fn = THE (analyze_fmp_context (reclaim_ctx fn))
End
Definition reclaim_straight_states_def[local]:
  reclaim_straight_states = THE (fmp_reclaim_states reclaim_straight_fn)
End


Theorem fmp_common_top_probe:
  fmp_common_top ["young"; "old"] ["young"; "old"] =
    ["young"; "old"] /\
  fmp_common_top ["left"; "old"] ["right"; "old"] = []
Proof
  EVAL_TAC
QED

Theorem reclaim_lt3_cases[local]:
  !(k:num). k < 3 <=> k = 0 \/ k = 1 \/ k = 2
Proof
  Induct >> simp[]
QED

Theorem reclaim_straight_fn_wf[local]:
  wf_function reclaim_straight_fn /\ fn_inst_wf reclaim_straight_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[reclaim_lt3_cases, listTheory.REV_DEF, venomInstTheory.is_terminator_def,
      venomWfTheory.inst_wf_def]
QED

Theorem reclaim_straight_infos_valid[local]:
  fmp_info_valid (reclaim_ctx reclaim_straight_fn)
    (reclaim_infos reclaim_straight_fn)
Proof
  irule analyze_fmp_context_valid >> EVAL_TAC
QED

Theorem reclaim_straight_captures[local]:
  FLAT (MAP fmp_getfmp_outputs (fn_insts reclaim_straight_fn)) = []
Proof
  EVAL_TAC
QED

Theorem reclaim_straight_states_eq[local]:
  fmp_reclaim_states reclaim_straight_fn = SOME reclaim_straight_states
Proof
  EVAL_TAC
QED

Theorem reclaim_straight_state_at_exit[local]:
  df_at NONE reclaim_straight_states "entry" 3 =
    SOME <| frs_stack := ["p"]; frs_captures := [];
            frs_can_reclaim := T |>
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_straight_target_ok[local]:
  fmp_restore_target_ok (reclaim_infos reclaim_straight_fn)
    (reclaim_ctx reclaim_straight_fn) reclaim_straight_fn
    (liveness_analyze reclaim_straight_fn) [] ("entry",3) "p"
Proof
  simp[fmp_restore_target_ok_def, reclaim_straight_infos_valid] >>
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_straight_plan_ok[local]:
  fmp_reclaim_plan_ok (reclaim_infos reclaim_straight_fn)
    (reclaim_ctx reclaim_straight_fn) reclaim_straight_fn
    (FEMPTY |+ (("entry",3),"p"))
Proof
  simp[fmp_reclaim_plan_ok_def, fmp_reclaim_entry_ok_def,
       finite_mapTheory.FLOOKUP_UPDATE, reclaim_straight_captures,
       reclaim_straight_target_ok]
QED

Theorem reclaim_straight_blocks[local]:
  reclaim_straight_fn.fn_blocks =
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 MLOAD [Var "p"] ["x"];
           mk_inst 2 STOP [] []] |>]
Proof
  EVAL_TAC
QED

Theorem reclaim_straight_block_candidate[local]:
  fmp_block_restore (reclaim_infos reclaim_straight_fn)
    (reclaim_ctx reclaim_straight_fn) reclaim_straight_fn
    (liveness_analyze reclaim_straight_fn) (cfg_analyze reclaim_straight_fn)
    reclaim_straight_states
    <| bb_label := "entry";
       bb_instructions :=
         [mk_inst 0 DALLOCA [Lit 32w] ["p"];
          mk_inst 1 MLOAD [Var "p"] ["x"];
          mk_inst 2 STOP [] []] |> = SOME (("entry",3),"p")
Proof
  simp[fmp_block_restore_def, reclaim_straight_state_at_exit,
       fmp_stack_reclaimable_def, reclaim_straight_target_ok,
       fmp_oldest_def] >> EVAL_TAC
QED

Theorem reclaim_straight_candidate[local]:
  fmp_candidate_plan (reclaim_infos reclaim_straight_fn)
    (reclaim_ctx reclaim_straight_fn) reclaim_straight_fn
    reclaim_straight_states = FEMPTY |+ (("entry",3),"p")
Proof
  simp[fmp_candidate_plan_def, reclaim_straight_blocks,
       fmp_collect_candidates_def, reclaim_straight_block_candidate,
       fmp_plan_of_list_def]
QED
Theorem fmp_reclaim_straight_line_eval:
  analyze_fmp_reclaims (reclaim_infos reclaim_straight_fn)
      (reclaim_ctx reclaim_straight_fn) reclaim_straight_fn =
    SOME (FEMPTY |+ (("entry",3),"p"))
Proof
  simp[analyze_fmp_reclaims_def, reclaim_straight_infos_valid,
       reclaim_straight_fn_wf, reclaim_straight_states_eq,
       reclaim_straight_candidate, reclaim_straight_plan_ok] >>
  EVAL_TAC
QED


Theorem analyze_fmp_reclaims_ready:
  fmp_info_valid ctx infos /\ MEM fn ctx.ctx_functions /\
  wf_function fn /\ fn_inst_wf fn /\ fn.fn_fmp_signature = NONE /\
  fmp_reclaim_states fn = SOME states /\
  fmp_candidate_plan infos ctx fn states = plan /\
  fmp_reclaim_plan_ok infos ctx fn plan ==>
  analyze_fmp_reclaims infos ctx fn = SOME plan
Proof
  simp[analyze_fmp_reclaims_def] >> metis_tac[]
QED


Theorem reclaim_lt2_cases[local]:
  !(k:num). k < 2 <=> k = 0 \/ k = 1
Proof
  Induct >> simp[]
QED

Theorem reclaim_lt4_cases[local]:
  !(k:num). k < 4 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3
Proof
  Induct >> simp[]
QED

Theorem reclaim_join_wf[local]:
  wf_function reclaim_join_fn /\ fn_inst_wf reclaim_join_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[reclaim_lt2_cases, reclaim_lt4_cases, listTheory.REV_DEF,
      venomStateTheory.get_label_def, venomInstTheory.is_terminator_def,
      venomWfTheory.inst_wf_def]
QED

Theorem reclaim_join_infos_valid[local]:
  fmp_info_valid (reclaim_ctx reclaim_join_fn) (reclaim_infos reclaim_join_fn)
Proof
  irule analyze_fmp_context_valid >> EVAL_TAC
QED

Definition reclaim_join_states_def[local]:
  reclaim_join_states = THE (fmp_reclaim_states reclaim_join_fn)
End

Theorem reclaim_join_states_eq[local]:
  fmp_reclaim_states reclaim_join_fn = SOME reclaim_join_states
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_join_candidate_empty[local]:
  fmp_candidate_plan (reclaim_infos reclaim_join_fn)
    (reclaim_ctx reclaim_join_fn) reclaim_join_fn reclaim_join_states = FEMPTY
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE,
       fmp_plan_of_list_def]
QED

Theorem fmp_reclaim_join_veto_eval:
  analyze_fmp_reclaims (reclaim_infos reclaim_join_fn)
    (reclaim_ctx reclaim_join_fn) reclaim_join_fn = SOME FEMPTY
Proof
  irule analyze_fmp_reclaims_ready >>
  simp[reclaim_join_infos_valid, reclaim_join_wf, reclaim_join_states_eq,
       reclaim_join_candidate_empty, fmp_reclaim_plan_ok_def] >>
  EVAL_TAC
QED


Theorem reclaim_divergent_join_wf[local]:
  wf_function reclaim_divergent_join_fn /\
  fn_inst_wf reclaim_divergent_join_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[reclaim_lt2_cases, reclaim_lt4_cases, listTheory.REV_DEF,
      venomStateTheory.get_label_def, venomInstTheory.is_terminator_def,
      venomWfTheory.inst_wf_def]
QED

Theorem reclaim_divergent_join_infos_valid[local]:
  fmp_info_valid (reclaim_ctx reclaim_divergent_join_fn)
    (reclaim_infos reclaim_divergent_join_fn)
Proof
  irule analyze_fmp_context_valid >> EVAL_TAC
QED

Definition reclaim_divergent_join_states_def[local]:
  reclaim_divergent_join_states =
    THE (fmp_reclaim_states reclaim_divergent_join_fn)
End

Theorem reclaim_divergent_join_states_eq[local]:
  fmp_reclaim_states reclaim_divergent_join_fn =
    SOME reclaim_divergent_join_states
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_reclaim_divergent_join_state_eval:
  df_at NONE reclaim_divergent_join_states "join" 0 =
    SOME <| frs_stack := []; frs_captures := [];
            frs_can_reclaim := T |>
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_divergent_join_candidate_empty[local]:
  fmp_candidate_plan (reclaim_infos reclaim_divergent_join_fn)
    (reclaim_ctx reclaim_divergent_join_fn) reclaim_divergent_join_fn
    reclaim_divergent_join_states = FEMPTY
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE,
       fmp_plan_of_list_def]
QED

Theorem fmp_reclaim_divergent_join_veto_eval:
  analyze_fmp_reclaims (reclaim_infos reclaim_divergent_join_fn)
    (reclaim_ctx reclaim_divergent_join_fn) reclaim_divergent_join_fn =
    SOME FEMPTY
Proof
  irule analyze_fmp_reclaims_ready >>
  simp[reclaim_divergent_join_infos_valid, reclaim_divergent_join_wf,
       reclaim_divergent_join_states_eq,
       reclaim_divergent_join_candidate_empty, fmp_reclaim_plan_ok_def] >>
  EVAL_TAC
QED

Definition reclaim_pin_states_def[local]:
  reclaim_pin_states = THE (fmp_reclaim_states reclaim_pin_fn)
End

Theorem reclaim_pin_wf[local]:
  wf_function reclaim_pin_fn /\ fn_inst_wf reclaim_pin_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[reclaim_lt4_cases, listTheory.REV_DEF,
      venomInstTheory.is_terminator_def, venomWfTheory.inst_wf_def]
QED

Theorem reclaim_pin_infos_valid[local]:
  fmp_info_valid (reclaim_ctx reclaim_pin_fn) (reclaim_infos reclaim_pin_fn)
Proof
  irule analyze_fmp_context_valid >> EVAL_TAC
QED

Theorem reclaim_pin_states_eq[local]:
  fmp_reclaim_states reclaim_pin_fn = SOME reclaim_pin_states
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_pin_state_at_exit[local]:
  df_at NONE reclaim_pin_states "entry" 4 =
    SOME <|frs_stack := ["p"]; frs_captures := []; frs_can_reclaim := T|>
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_pin_target_veto[local]:
  ~fmp_restore_target_ok (reclaim_infos reclaim_pin_fn)
    (reclaim_ctx reclaim_pin_fn) reclaim_pin_fn
    (liveness_analyze reclaim_pin_fn) [] ("entry",4) "p"
Proof
  simp[fmp_restore_target_ok_def, reclaim_pin_infos_valid] >>
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_pin_blocks[local]:
  reclaim_pin_fn.fn_blocks =
    [<|bb_label := "entry";
       bb_instructions :=
         [mk_inst 0 DALLOCA [Lit 32w] ["p"];
          mk_inst 1 ASSIGN [Var "p"] ["q"];
          mk_inst 2 MSTORE [Lit 0w; Var "q"] [];
          mk_inst 3 STOP [] []]|>]
Proof
  EVAL_TAC
QED

Theorem reclaim_pin_block_none[local]:
  fmp_block_restore (reclaim_infos reclaim_pin_fn)
    (reclaim_ctx reclaim_pin_fn) reclaim_pin_fn
    (liveness_analyze reclaim_pin_fn) (cfg_analyze reclaim_pin_fn)
    reclaim_pin_states
    <|bb_label := "entry";
      bb_instructions :=
        [mk_inst 0 DALLOCA [Lit 32w] ["p"];
         mk_inst 1 ASSIGN [Var "p"] ["q"];
         mk_inst 2 MSTORE [Lit 0w; Var "q"] [];
         mk_inst 3 STOP [] []]|> = NONE
Proof
  simp[reclaim_pin_blocks, fmp_block_restore_def, reclaim_pin_state_at_exit,
       fmp_stack_reclaimable_def, reclaim_pin_target_veto] >> EVAL_TAC
QED

Theorem reclaim_pin_candidate_empty[local]:
  fmp_candidate_plan (reclaim_infos reclaim_pin_fn)
    (reclaim_ctx reclaim_pin_fn) reclaim_pin_fn reclaim_pin_states = FEMPTY
Proof
  simp[fmp_candidate_plan_def, reclaim_pin_blocks,
       fmp_collect_candidates_def, reclaim_pin_block_none,
       fmp_plan_of_list_def]
QED

Theorem fmp_reclaim_pin_veto_eval:
  analyze_fmp_reclaims (reclaim_infos reclaim_pin_fn)
    (reclaim_ctx reclaim_pin_fn) reclaim_pin_fn = SOME FEMPTY /\
  fmp_target_pinned reclaim_pin_fn "p"
Proof
  conj_tac
  >- (irule analyze_fmp_reclaims_ready >>
      simp[reclaim_pin_infos_valid, reclaim_pin_wf, reclaim_pin_states_eq,
           reclaim_pin_candidate_empty, fmp_reclaim_plan_ok_def] >> EVAL_TAC)
  >> EVAL_TAC >> simp[]
QED

Definition reclaim_capture_states_def[local]:
  reclaim_capture_states = THE (fmp_reclaim_states reclaim_capture_fn)
End

Theorem reclaim_capture_wf[local]:
  wf_function reclaim_capture_fn /\ fn_inst_wf reclaim_capture_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[reclaim_lt4_cases, listTheory.REV_DEF,
      venomInstTheory.is_terminator_def, venomWfTheory.inst_wf_def]
QED

Theorem reclaim_capture_infos_valid[local]:
  fmp_info_valid (reclaim_ctx reclaim_capture_fn)
    (reclaim_infos reclaim_capture_fn)
Proof
  irule analyze_fmp_context_valid >> EVAL_TAC
QED

Theorem reclaim_capture_states_eq[local]:
  fmp_reclaim_states reclaim_capture_fn = SOME reclaim_capture_states
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_capture_state_at_exit[local]:
  df_at NONE reclaim_capture_states "entry" 4 =
    SOME <|frs_stack := ["p"]; frs_captures := ["captured"];
           frs_can_reclaim := T|>
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_capture_target_veto[local]:
  ~fmp_restore_target_ok (reclaim_infos reclaim_capture_fn)
    (reclaim_ctx reclaim_capture_fn) reclaim_capture_fn
    (liveness_analyze reclaim_capture_fn) ["captured"] ("entry",4) "p"
Proof
  simp[fmp_restore_target_ok_def, reclaim_capture_infos_valid] >>
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_capture_blocks[local]:
  reclaim_capture_fn.fn_blocks =
    [<|bb_label := "entry";
       bb_instructions :=
         [mk_inst 0 GETFMP [] ["captured"];
          mk_inst 1 MSTORE [Lit 0w; Var "captured"] [];
          mk_inst 2 DALLOCA [Lit 32w] ["p"];
          mk_inst 3 STOP [] []]|>]
Proof
  EVAL_TAC
QED

Theorem reclaim_capture_block_none[local]:
  fmp_block_restore (reclaim_infos reclaim_capture_fn)
    (reclaim_ctx reclaim_capture_fn) reclaim_capture_fn
    (liveness_analyze reclaim_capture_fn) (cfg_analyze reclaim_capture_fn)
    reclaim_capture_states
    <|bb_label := "entry";
      bb_instructions :=
        [mk_inst 0 GETFMP [] ["captured"];
         mk_inst 1 MSTORE [Lit 0w; Var "captured"] [];
         mk_inst 2 DALLOCA [Lit 32w] ["p"];
         mk_inst 3 STOP [] []]|> = NONE
Proof
  simp[fmp_block_restore_def, reclaim_capture_state_at_exit,
       fmp_stack_reclaimable_def, reclaim_capture_target_veto] >> EVAL_TAC
QED

Theorem reclaim_capture_candidate_empty[local]:
  fmp_candidate_plan (reclaim_infos reclaim_capture_fn)
    (reclaim_ctx reclaim_capture_fn) reclaim_capture_fn
    reclaim_capture_states = FEMPTY
Proof
  simp[fmp_candidate_plan_def, reclaim_capture_blocks,
       fmp_collect_candidates_def, reclaim_capture_block_none,
       fmp_plan_of_list_def]
QED

Theorem fmp_reclaim_capture_escape_veto_eval:
  analyze_fmp_reclaims (reclaim_infos reclaim_capture_fn)
    (reclaim_ctx reclaim_capture_fn) reclaim_capture_fn = SOME FEMPTY /\
  fmp_capture_escaped reclaim_capture_fn "captured"
Proof
  conj_tac
  >- (irule analyze_fmp_reclaims_ready >>
      simp[reclaim_capture_infos_valid, reclaim_capture_wf,
           reclaim_capture_states_eq, reclaim_capture_candidate_empty,
           fmp_reclaim_plan_ok_def] >> EVAL_TAC)
  >> EVAL_TAC >> simp[]
QED

Theorem fmp_reclaim_live_and_nondominating_veto_eval:
  MEM "p" (live_vars_at (liveness_analyze reclaim_straight_fn) "entry" 1) /\
  ~fmp_restore_target_ok (reclaim_infos reclaim_straight_fn)
    (reclaim_ctx reclaim_straight_fn) reclaim_straight_fn
    (liveness_analyze reclaim_straight_fn) [] ("entry",1) "p" /\
  ~fmp_restore_target_ok (reclaim_infos reclaim_straight_fn)
    (reclaim_ctx reclaim_straight_fn) reclaim_straight_fn
    (liveness_analyze reclaim_straight_fn) [] ("entry",0) "p"
Proof
  simp[fmp_restore_target_ok_def, reclaim_straight_infos_valid] >>
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_reclaim_current_input_rejection_eval:
  analyze_fmp_reclaims FEMPTY (reclaim_ctx reclaim_straight_fn)
    reclaim_straight_fn = NONE /\
  analyze_fmp_reclaims (reclaim_infos reclaim_straight_fn)
    (reclaim_ctx reclaim_straight_fn) reclaim_pin_fn = NONE
Proof
  simp[analyze_fmp_reclaims_def, reclaim_straight_infos_valid] >>
  EVAL_TAC >> simp[fmpAnalysisDefsTheory.fmp_info_valid_def]
QED
Definition reclaim_younger_live_fn_def[local]:
  reclaim_younger_live_fn = mk_raw_function "younger_live"
    [<|bb_label := "entry";
       bb_instructions :=
         [mk_inst 0 DALLOCA [Lit 32w] ["old"];
          mk_inst 1 DALLOCA [Lit 32w] ["young"];
          mk_inst 2 MLOAD [Var "young"] ["x"];
          mk_inst 3 STOP [] []]|>]
End

Theorem reclaim_younger_infos_valid[local]:
  fmp_info_valid (reclaim_ctx reclaim_younger_live_fn)
    (reclaim_infos reclaim_younger_live_fn)
Proof
  irule analyze_fmp_context_valid >> EVAL_TAC
QED

Theorem reclaim_younger_target_live[local]:
  MEM "young"
    (live_vars_at (liveness_analyze reclaim_younger_live_fn) "entry" 2) /\
  ~fmp_restore_target_ok (reclaim_infos reclaim_younger_live_fn)
    (reclaim_ctx reclaim_younger_live_fn) reclaim_younger_live_fn
    (liveness_analyze reclaim_younger_live_fn) [] ("entry",2) "young"
Proof
  simp[fmp_restore_target_ok_def, reclaim_younger_infos_valid] >>
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_reclaim_younger_live_mark_veto_eval:
  ~fmp_stack_reclaimable (reclaim_infos reclaim_younger_live_fn)
    (reclaim_ctx reclaim_younger_live_fn) reclaim_younger_live_fn
    (liveness_analyze reclaim_younger_live_fn) [] ("entry",2)
    ["young"; "old"]
Proof
  simp[fmp_stack_reclaimable_def, reclaim_younger_target_live]
QED

Definition reclaim_loop_states_def[local]:
  reclaim_loop_states = THE (fmp_reclaim_states reclaim_loop_fn)
End

Theorem reclaim_loop_wf[local]:
  wf_function reclaim_loop_fn /\ fn_inst_wf reclaim_loop_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[reclaim_lt2_cases, listTheory.REV_DEF, venomStateTheory.get_label_def,
      venomInstTheory.is_terminator_def, venomWfTheory.inst_wf_def]
QED

Theorem reclaim_loop_infos_valid[local]:
  fmp_info_valid (reclaim_ctx reclaim_loop_fn) (reclaim_infos reclaim_loop_fn)
Proof
  irule analyze_fmp_context_valid >> EVAL_TAC
QED

Theorem reclaim_loop_states_eq[local]:
  fmp_reclaim_states reclaim_loop_fn = SOME reclaim_loop_states
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem reclaim_loop_candidate_empty[local]:
  fmp_candidate_plan (reclaim_infos reclaim_loop_fn)
    (reclaim_ctx reclaim_loop_fn) reclaim_loop_fn reclaim_loop_states = FEMPTY
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE,
       fmp_plan_of_list_def]
QED

Theorem fmp_reclaim_loop_totality_eval:
  analyze_fmp_reclaims (reclaim_infos reclaim_loop_fn)
    (reclaim_ctx reclaim_loop_fn) reclaim_loop_fn = SOME FEMPTY
Proof
  irule analyze_fmp_reclaims_ready >>
  simp[reclaim_loop_infos_valid, reclaim_loop_wf, reclaim_loop_states_eq,
       reclaim_loop_candidate_empty, fmp_reclaim_plan_ok_def] >>
  EVAL_TAC
QED


Theorem analyze_fmp_reclaims_checked:
  analyze_fmp_reclaims infos ctx fn = SOME plan ==>
  fmp_info_valid ctx infos /\
  MEM fn ctx.ctx_functions /\
  fmp_reclaim_plan_ok infos ctx fn plan
Proof
  simp[analyze_fmp_reclaims_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_reclaim_plan_ok_lookup:
  fmp_reclaim_plan_ok infos ctx fn plan /\
  FLOOKUP plan point = SOME target ==>
  fmp_reclaim_entry_ok infos ctx fn point target
Proof
  simp[fmp_reclaim_plan_ok_def] >> metis_tac[]
QED

Theorem analyze_fmp_reclaims_target_checked:
  analyze_fmp_reclaims infos ctx fn = SOME plan /\
  FLOOKUP plan point = SOME target ==>
  ?bb def_lbl def_i dalloca.
    lookup_block (FST point) fn.fn_blocks = SOME bb /\
    SND point <= LENGTH bb.bb_instructions /\
    fmp_find_dalloca target fn.fn_blocks =
      SOME (def_lbl,def_i,dalloca) /\
    dalloca.inst_opcode = DALLOCA /\
    dalloca.inst_outputs = [target] /\
    fmp_definition_dominates fn def_lbl def_i point /\
    EVERY
      (\v. ~MEM v
        (live_vars_at (liveness_analyze fn) (FST point) (SND point)))
      (fmp_derived_vars fn target) /\
    ~fmp_target_pinned fn target /\
    EVERY
      (\cap. ~fmp_capture_veto fn (liveness_analyze fn) point cap)
      (FLAT (MAP fmp_getfmp_outputs (fn_insts fn)))
Proof
  rpt strip_tac >>
  drule analyze_fmp_reclaims_checked >> strip_tac >>
  drule fmp_reclaim_plan_ok_lookup >>
  disch_then drule >>
  simp[fmp_reclaim_entry_ok_def, fmp_restore_target_ok_def,
       fmp_point_well_located_def] >>
  metis_tac[]
QED

Theorem analyze_fmp_reclaims_deterministic:
  analyze_fmp_reclaims infos ctx fn = SOME p1 /\
  analyze_fmp_reclaims infos ctx fn = SOME p2 ==>
  p1 = p2
Proof
  rpt strip_tac >> gvs[]
QED

val _ = export_theory();
