(* Focused executable validation for conservative FMP reclaim analysis. *)

Theory fmpReclaimProps
Ancestors
  fmpReclaimDefs

Definition fmp_test_fn_def[local]:
  fmp_test_fn = mk_raw_function "f"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 MLOAD [Var "p"] ["x"];
           mk_inst 2 STOP [] []] |>]
End

Definition fmp_nested_fn_def[local]:
  fmp_nested_fn = mk_raw_function "f"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 DALLOCA [Lit 64w] ["q"];
           mk_inst 2 STOP [] []] |>]
End

Definition fmp_pin_fn_def[local]:
  fmp_pin_fn = mk_raw_function "f"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 ASSIGN [Var "p"] ["q"];
           mk_inst 2 STOP [] []] |>]
End

Definition fmp_capture_fn_def[local]:
  fmp_capture_fn = mk_raw_function "f"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 MSTORE [Lit 0w; Var "p"] [];
           mk_inst 2 STOP [] []] |>]
End

Definition fmp_escape_fn_def[local]:
  fmp_escape_fn = mk_raw_function "f"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 32w] ["p"];
           mk_inst 1 RET [Var "p"] []] |>]
End

Definition fmp_join_fn_def[local]:
  fmp_join_fn = mk_raw_function "f"
    [<| bb_label := "entry";
        bb_instructions :=
          [mk_inst 0 JNZ [Lit 1w; Label "left"; Label "right"] []] |>;
     <| bb_label := "left";
        bb_instructions :=
          [mk_inst 1 DALLOCA [Lit 32w] ["p"];
           mk_inst 2 JMP [Label "join"] []] |>;
     <| bb_label := "right";
        bb_instructions := [mk_inst 3 JMP [Label "join"] []] |>;
     <| bb_label := "join";
        bb_instructions := [mk_inst 4 STOP [] []] |>]
End

Definition fmp_ctx_def[local]:
  fmp_ctx fn = mk_venom_context [fn] (SOME fn.fn_name)
End
Theorem analyze_fmp_reclaims_preconditions:
  !ctx name infos fn.
    analyze_fmp_context ctx = SOME infos ==>
    lookup_function name ctx.ctx_functions = SOME fn ==>
    fn.fn_fmp_signature = NONE ==>
    wf_function fn ==>
    fn_inst_wf fn ==>
    analyze_fmp_reclaims ctx name =
      case fmp_mark_analyze fn of
        NONE => NONE
      | SOME marks =>
          let live = liveness_analyze fn in
          let cfg = cfg_analyze fn in
          let restores =
            fmp_collect_restores ctx fn live marks cfg fn.fn_blocks in
          SOME <| frp_function := fn.fn_name;
                  frp_restores := restores |>
Proof
  rpt strip_tac >>
  Cases_on `fmp_mark_analyze fn` >>
  simp[analyze_fmp_reclaims_def]
QED


Theorem fmp_lt3_cases[local]:
  !(k:num). k < 3 <=> k = 0 \/ k = 1 \/ k = 2
Proof
  Induct >> simp[]
QED

Theorem fmp_test_fn_wf[local]:
  wf_function fmp_test_fn /\ fn_inst_wf fmp_test_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[fmp_lt3_cases, listTheory.REV_DEF,
      venomInstTheory.is_terminator_def, venomWfTheory.inst_wf_def]
QED

Theorem fmp_lt2_cases[local]:
  !(k:num). k < 2 <=> k = 0 \/ k = 1
Proof
  Induct >> simp[]
QED

Theorem fmp_lt4_cases[local]:
  !(k:num). k < 4 <=> k = 0 \/ k = 1 \/ k = 2 \/ k = 3
Proof
  Induct >> simp[]
QED

Theorem fmp_nested_fn_wf[local]:
  wf_function fmp_nested_fn /\ fn_inst_wf fmp_nested_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[fmp_lt3_cases, listTheory.REV_DEF,
      venomInstTheory.is_terminator_def, venomWfTheory.inst_wf_def]
QED

Theorem fmp_pin_fn_wf[local]:
  wf_function fmp_pin_fn /\ fn_inst_wf fmp_pin_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[fmp_lt3_cases, listTheory.REV_DEF,
      venomInstTheory.is_terminator_def, venomWfTheory.inst_wf_def]
QED

Theorem fmp_capture_fn_wf[local]:
  wf_function fmp_capture_fn /\ fn_inst_wf fmp_capture_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[fmp_lt3_cases, listTheory.REV_DEF,
      venomInstTheory.is_terminator_def, venomWfTheory.inst_wf_def]
QED

Theorem fmp_escape_fn_wf[local]:
  wf_function fmp_escape_fn /\ fn_inst_wf fmp_escape_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[fmp_lt2_cases, listTheory.REV_DEF, venomStateTheory.get_label_def,
      venomInstTheory.is_terminator_def, venomWfTheory.inst_wf_def]
QED

Theorem fmp_join_fn_wf[local]:
  wf_function fmp_join_fn /\ fn_inst_wf fmp_join_fn
Proof
  EVAL_TAC >> rw[] >>
  gvs[fmp_lt2_cases, fmp_lt4_cases, listTheory.REV_DEF,
      venomStateTheory.get_label_def, venomInstTheory.is_terminator_def,
      venomWfTheory.inst_wf_def]
QED

Theorem fmp_test_analyze_reduction[local]:
  analyze_fmp_reclaims (fmp_ctx fmp_test_fn) "f" =
    case fmp_mark_analyze fmp_test_fn of
      NONE => NONE
    | SOME marks =>
        let live = liveness_analyze fmp_test_fn in
        let cfg = cfg_analyze fmp_test_fn in
        let restores =
          fmp_collect_restores (fmp_ctx fmp_test_fn) fmp_test_fn
            live marks cfg fmp_test_fn.fn_blocks in
        SOME <| frp_function := fmp_test_fn.fn_name;
                frp_restores := restores |>
Proof
  irule analyze_fmp_reclaims_preconditions >>
  simp[fmp_test_fn_wf] >> EVAL_TAC >> simp[]
QED


Theorem fmp_nested_analyze_reduction[local]:
  analyze_fmp_reclaims (fmp_ctx fmp_nested_fn) "f" =
    case fmp_mark_analyze fmp_nested_fn of
      NONE => NONE
    | SOME marks =>
        let live = liveness_analyze fmp_nested_fn in
        let cfg = cfg_analyze fmp_nested_fn in
        let restores = fmp_collect_restores (fmp_ctx fmp_nested_fn)
          fmp_nested_fn live marks cfg fmp_nested_fn.fn_blocks in
        SOME <|frp_function := fmp_nested_fn.fn_name; frp_restores := restores|>
Proof
  irule analyze_fmp_reclaims_preconditions >>
  simp[fmp_nested_fn_wf] >> EVAL_TAC >> simp[]
QED

Theorem fmp_join_analyze_reduction[local]:
  analyze_fmp_reclaims (fmp_ctx fmp_join_fn) "f" =
    case fmp_mark_analyze fmp_join_fn of
      NONE => NONE
    | SOME marks =>
        let live = liveness_analyze fmp_join_fn in
        let cfg = cfg_analyze fmp_join_fn in
        let restores = fmp_collect_restores (fmp_ctx fmp_join_fn)
          fmp_join_fn live marks cfg fmp_join_fn.fn_blocks in
        SOME <|frp_function := fmp_join_fn.fn_name; frp_restores := restores|>
Proof
  irule analyze_fmp_reclaims_preconditions >>
  simp[fmp_join_fn_wf] >> EVAL_TAC >> simp[]
QED

Theorem fmp_pin_analyze_reduction[local]:
  analyze_fmp_reclaims (fmp_ctx fmp_pin_fn) "f" =
    case fmp_mark_analyze fmp_pin_fn of
      NONE => NONE
    | SOME marks =>
        let live = liveness_analyze fmp_pin_fn in
        let cfg = cfg_analyze fmp_pin_fn in
        let restores = fmp_collect_restores (fmp_ctx fmp_pin_fn)
          fmp_pin_fn live marks cfg fmp_pin_fn.fn_blocks in
        SOME <|frp_function := fmp_pin_fn.fn_name; frp_restores := restores|>
Proof
  irule analyze_fmp_reclaims_preconditions >>
  simp[fmp_pin_fn_wf] >> EVAL_TAC >> simp[]
QED

Theorem fmp_capture_analyze_reduction[local]:
  analyze_fmp_reclaims (fmp_ctx fmp_capture_fn) "f" =
    case fmp_mark_analyze fmp_capture_fn of
      NONE => NONE
    | SOME marks =>
        let live = liveness_analyze fmp_capture_fn in
        let cfg = cfg_analyze fmp_capture_fn in
        let restores = fmp_collect_restores (fmp_ctx fmp_capture_fn)
          fmp_capture_fn live marks cfg fmp_capture_fn.fn_blocks in
        SOME <|frp_function := fmp_capture_fn.fn_name; frp_restores := restores|>
Proof
  irule analyze_fmp_reclaims_preconditions >>
  simp[fmp_capture_fn_wf] >> EVAL_TAC >> simp[]
QED

Theorem fmp_escape_analyze_reduction[local]:
  analyze_fmp_reclaims (fmp_ctx fmp_escape_fn) "f" =
    case fmp_mark_analyze fmp_escape_fn of
      NONE => NONE
    | SOME marks =>
        let live = liveness_analyze fmp_escape_fn in
        let cfg = cfg_analyze fmp_escape_fn in
        let restores = fmp_collect_restores (fmp_ctx fmp_escape_fn)
          fmp_escape_fn live marks cfg fmp_escape_fn.fn_blocks in
        SOME <|frp_function := fmp_escape_fn.fn_name; frp_restores := restores|>
Proof
  irule analyze_fmp_reclaims_preconditions >>
  simp[fmp_escape_fn_wf] >> EVAL_TAC >> simp[]
QED
Theorem fmp_reclaim_straight_line_eval:
  analyze_fmp_reclaims (fmp_ctx fmp_test_fn) "f" =
    SOME <| frp_function := "f";
            frp_restores :=
              [(<|fp_block := "entry"; fp_index := 3|>, "p")] |>
Proof
  rewrite_tac[fmp_test_analyze_reduction] >> EVAL_TAC >>
  simp[fmp_take_reclaimable_def, fmp_restore_target_ok_def] >> EVAL_TAC >> simp[]
QED

Theorem fmp_reclaim_nested_lifo_eval:
  analyze_fmp_reclaims (fmp_ctx fmp_nested_fn) "f" =
    SOME <| frp_function := "f";
            frp_restores :=
              [(<|fp_block := "entry"; fp_index := 3|>, "q");
               (<|fp_block := "entry"; fp_index := 3|>, "p")] |>
Proof
  rewrite_tac[fmp_nested_analyze_reduction] >> EVAL_TAC >>
  simp[fmp_take_reclaimable_def, fmp_restore_target_ok_def] >> EVAL_TAC >> simp[]
QED

Theorem fmp_reclaim_join_veto_eval:
  analyze_fmp_reclaims (fmp_ctx fmp_join_fn) "f" =
    SOME <| frp_function := "f"; frp_restores := [] |>
Proof
  rewrite_tac[fmp_join_analyze_reduction] >> EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE,
       fmp_take_reclaimable_def, fmp_restore_target_ok_def] >> EVAL_TAC >> simp[]
QED

Theorem fmp_reclaim_pin_capture_escape_eval:
  analyze_fmp_reclaims (fmp_ctx fmp_pin_fn) "f" =
    SOME <|frp_function := "f"; frp_restores := []|> /\
  analyze_fmp_reclaims (fmp_ctx fmp_capture_fn) "f" =
    SOME <|frp_function := "f"; frp_restores := []|> /\
  analyze_fmp_reclaims (fmp_ctx fmp_escape_fn) "f" =
    SOME <|frp_function := "f"; frp_restores := []|> /\
  fmp_target_pinned fmp_pin_fn "p" /\
  fmp_target_captured fmp_capture_fn "p" /\
  fmp_target_escapes fmp_escape_fn "p"
Proof
  rewrite_tac[fmp_pin_analyze_reduction, fmp_capture_analyze_reduction,
              fmp_escape_analyze_reduction] >> EVAL_TAC >>
  simp[fmp_take_reclaimable_def, fmp_restore_target_ok_def] >> EVAL_TAC >> simp[]
QED

Theorem fmp_reclaim_live_and_nondominating_veto_eval:
  let live = liveness_analyze fmp_test_fn in
  let early = <|fp_block := "entry"; fp_index := 1|> in
  let before = <|fp_block := "entry"; fp_index := 0|> in
  ~fmp_restore_target_ok (fmp_ctx fmp_test_fn) fmp_test_fn live early "p" /\
  ~fmp_restore_target_ok (fmp_ctx fmp_test_fn) fmp_test_fn live before "p"
Proof
  EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE,
       fmp_restore_target_ok_def] >> EVAL_TAC >> simp[]
QED

Theorem fmp_reclaim_unknown_malformed_deterministic_eval:
  analyze_fmp_reclaims (fmp_ctx fmp_test_fn) "missing" = NONE /\
  analyze_fmp_reclaims
    (mk_venom_context [fmp_test_fn; fmp_test_fn] (SOME "f")) "f" = NONE /\
  analyze_fmp_reclaims (fmp_ctx fmp_test_fn) "f" =
    analyze_fmp_reclaims (fmp_ctx fmp_test_fn) "f" /\
  analyze_fmp_reclaims (fmp_ctx fmp_test_fn) "f" <>
    analyze_fmp_reclaims (fmp_ctx fmp_pin_fn) "f"
Proof
  rewrite_tac[fmp_test_analyze_reduction, fmp_pin_analyze_reduction] >> EVAL_TAC >>
  simp[finite_mapTheory.FLOOKUP_FUNION, finite_mapTheory.FLOOKUP_UPDATE,
       fmp_take_reclaimable_def, fmp_restore_target_ok_def] >> EVAL_TAC >> simp[]
QED

val _ = export_theory();
