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

val _ = export_theory ();
