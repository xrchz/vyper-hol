(*
 * Executable mapped-stage and frozen callee-first pipeline runners.
 *
 * Persistent runner state is exactly the current compilation unit and one
 * threaded IR supply.  In particular, analysis discard is an explicit
 * boundary but there is no persistent analysis cache to clear.
 *)

Theory venomPipelineRunner
Ancestors
  venomFnScheduleRunner

Definition run_named_fn_schedules_def:
  run_named_fn_schedules runner rpolicy passes [] unit supply =
    SOME (unit,supply) /\
  run_named_fn_schedules runner rpolicy passes (name::names) unit supply =
    case run_configured_fn_passes runner rpolicy passes name unit supply of
      NONE => NONE
    | SOME (unit1,supply1) =>
        run_named_fn_schedules runner rpolicy passes names unit1 supply1
End

Definition run_mapped_functions_def:
  run_mapped_functions rpolicy pass unit supply =
    run_named_fn_schedules execute_configured_fn_pass rpolicy [pass]
      (ctx_fn_names unit.cu_context) unit supply
End

Definition run_pipeline_stage_def:
  run_pipeline_stage rpolicy (PS_MapFunctions pass) unit supply =
    run_mapped_functions rpolicy pass unit supply /\
  run_pipeline_stage rpolicy PS_DiscardAnalyses unit supply =
    SOME (unit,supply)
End

Definition run_pipeline_stages_def:
  run_pipeline_stages rpolicy [] unit supply = SOME (unit,supply) /\
  run_pipeline_stages rpolicy (stage::stages) unit supply =
    case run_pipeline_stage rpolicy stage unit supply of
      NONE => NONE
    | SOME (unit1,supply1) =>
        run_pipeline_stages rpolicy stages unit1 supply1
End

Definition run_callee_first_def:
  run_callee_first rpolicy passes frozen_names unit supply =
    run_named_fn_schedules execute_configured_fn_pass rpolicy passes
      frozen_names unit supply
End

(* Closed structural probes for order, state threading, and failure. *)
Definition task040_three_unit_def:
  task040_three_unit = <|
    cu_context := mk_venom_context
      [mk_raw_function "first" [];
       mk_raw_function "second" [];
       mk_raw_function "third" []] (SOME "third");
    cu_data_segment := []
  |>
End

Definition task040_callee_unit_def:
  task040_callee_unit = <|
    cu_context := mk_venom_context
      [mk_raw_function "callee1" [];
       mk_raw_function "callee2" [];
       mk_raw_function "caller" []] (SOME "caller");
    cu_data_segment := []
  |>
End

Definition task040_trace_runner_def:
  task040_trace_runner rpolicy pass unit supply fn =
    let digit =
      if fn.fn_name = "first" \/ fn.fn_name = "callee1" then 1
      else if fn.fn_name = "second" \/ fn.fn_name = "callee2" then 2
      else 3
    in
      SOME <| fpo_function := fn; fpo_label_map := [];
              fpo_supply := supply with irs_next_var :=
                10 * supply.irs_next_var + digit |>
End

Definition task040_fail_second_runner_def:
  task040_fail_second_runner rpolicy pass unit supply fn =
    if fn.fn_name = "second" \/ fn.fn_name = "callee2" then NONE
    else task040_trace_runner rpolicy pass unit supply fn
End

Theorem task040_mapped_order_eval:
  run_named_fn_schedules task040_trace_runner task039_policy
    [CFP_Simple VP_SimplifyCFG]
    (ctx_fn_names task040_three_unit.cu_context) task040_three_unit
    (init_ir_supply task040_three_unit) =
  SOME (task040_three_unit,
        (init_ir_supply task040_three_unit) with irs_next_var := 123)
Proof
  EVAL_TAC
QED

Theorem task040_multi_callee_order_eval:
  run_named_fn_schedules task040_trace_runner task039_policy
    [CFP_Simple VP_SimplifyCFG] ["callee1"; "callee2"; "caller"]
    task040_callee_unit (init_ir_supply task040_callee_unit) =
  SOME (task040_callee_unit,
        (init_ir_supply task040_callee_unit) with irs_next_var := 123)
Proof
  EVAL_TAC
QED

Theorem task040_mapped_failure_eval:
  run_named_fn_schedules task040_fail_second_runner task039_policy
    [CFP_Simple VP_SimplifyCFG]
    (ctx_fn_names task040_three_unit.cu_context) task040_three_unit
    (init_ir_supply task040_three_unit) = NONE
Proof
  EVAL_TAC
QED

Theorem task040_callee_failure_eval:
  run_named_fn_schedules task040_fail_second_runner task039_policy
    [CFP_Simple VP_SimplifyCFG] ["callee1"; "callee2"; "caller"]
    task040_callee_unit (init_ir_supply task040_callee_unit) = NONE
Proof
  EVAL_TAC
QED

Theorem task040_discard_identity_eval:
  run_pipeline_stage task039_policy PS_DiscardAnalyses task040_three_unit
    (init_ir_supply task040_three_unit) =
  SOME (task040_three_unit,init_ir_supply task040_three_unit)
Proof
  EVAL_TAC
QED

Theorem task040_later_stage_failure_eval:
  run_pipeline_stages task039_policy
    [PS_DiscardAnalyses; PS_MapFunctions (CFP_Simple VP_FmpLowering)]
    task040_three_unit (init_ir_supply task040_three_unit) = NONE
Proof
  EVAL_TAC
QED

Theorem task040_canonical_mapped_smoke_eval:
  run_mapped_functions task039_policy (CFP_Simple VP_SimplifyCFG)
    task040_three_unit (init_ir_supply task040_three_unit) =
  SOME (task040_three_unit,init_ir_supply task040_three_unit)
Proof
  EVAL_TAC
QED

Definition task040_concretized_unit_def:
  task040_concretized_unit =
    task040_three_unit with cu_context :=
      task040_three_unit.cu_context with ctx_functions :=
        MAP (\fn. fn with fn_eom := SOME 0)
          task040_three_unit.cu_context.ctx_functions
End

Theorem task040_next_stage_observes_replacement_eval:
  run_pipeline_stages task039_policy
    [PS_MapFunctions (CFP_Simple VP_ConcretizeMemLoc);
     PS_MapFunctions (CFP_Simple VP_SimplifyCFG)]
    task040_three_unit (init_ir_supply task040_three_unit) =
  SOME (task040_concretized_unit,init_ir_supply task040_three_unit)
Proof
  EVAL_TAC
QED

Theorem task040_canonical_callee_first_smoke_eval:
  run_callee_first task039_policy [] ["callee1"; "callee2"; "caller"]
    task040_callee_unit (init_ir_supply task040_callee_unit) =
  SOME (task040_callee_unit,init_ir_supply task040_callee_unit)
Proof
  EVAL_TAC
QED

val _ = export_theory ();
