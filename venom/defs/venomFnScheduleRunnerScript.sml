(*
 * Atomic configured per-function schedule runner.
 *)

Theory venomFnScheduleRunner
Ancestors
  venomPassDispatcher unitLabelMap venomCompilerWf irSupply

Definition lookup_unique_function_def:
  lookup_unique_function name fns =
    case FILTER (\fn. fn.fn_name = name) fns of
      [fn] => SOME fn
    | _ => NONE
End

Definition replace_unique_function_def:
  replace_unique_function name replacement fns =
    if replacement.fn_name <> name then NONE
    else
      case FILTER (\fn. fn.fn_name = name) fns of
        [_] => SOME (MAP (\fn. if fn.fn_name = name then replacement else fn) fns)
      | _ => NONE
End

Definition list_subset_def:
  list_subset xs ys <=> EVERY (\x. MEM x ys) xs
End

Definition ir_supply_covers_fn_def:
  ir_supply_covers_fn s fn <=>
    list_subset (fn_ir_inst_ids fn) s.irs_used_inst_ids /\
    EVERY (\id. id < s.irs_next_inst) (fn_ir_inst_ids fn) /\
    list_subset (fn_ir_vars fn) s.irs_used_vars /\
    list_subset (fn_ir_labels fn) s.irs_used_labels
End

Definition ir_supply_covers_unit_def:
  ir_supply_covers_unit s unit <=>
    list_subset (unit_ir_inst_ids unit) s.irs_used_inst_ids /\
    EVERY (\id. id < s.irs_next_inst) (unit_ir_inst_ids unit) /\
    list_subset (unit_ir_vars unit) s.irs_used_vars /\
    list_subset (unit_ir_labels unit) s.irs_used_labels
End

Definition ir_supply_extends_def:
  ir_supply_extends old new <=>
    old.irs_next_inst <= new.irs_next_inst /\
    old.irs_next_var <= new.irs_next_var /\
    old.irs_next_label <= new.irs_next_label /\
    list_subset old.irs_used_inst_ids new.irs_used_inst_ids /\
    list_subset old.irs_used_vars new.irs_used_vars /\
    list_subset old.irs_used_labels new.irs_used_labels
End

Definition fn_invoke_targets_def:
  fn_invoke_targets fn = MAP FST (fcg_scan_function fn)
End

Definition unit_invoke_targets_def:
  unit_invoke_targets unit =
    FLAT (MAP fn_invoke_targets unit.cu_context.ctx_functions)
End

Definition unit_with_current_fn_def:
  unit_with_current_fn unit fn =
    case replace_unique_function fn.fn_name fn
           unit.cu_context.ctx_functions of
      NONE => NONE
    | SOME fns =>
        SOME (unit with cu_context :=
          unit.cu_context with ctx_functions := fns)
End

Definition run_configured_fn_pass_fold_def:
  run_configured_fn_pass_fold runner rpolicy [] unit s current_fn label_map =
    SOME (current_fn,label_map,s) /\
  run_configured_fn_pass_fold runner rpolicy (pass::passes) unit s current_fn label_map =
    case unit_with_current_fn unit current_fn of
      NONE => NONE
    | SOME observed =>
        case runner rpolicy pass observed s current_fn of
          NONE => NONE
        | SOME out =>
            if out.fpo_function.fn_name = current_fn.fn_name /\
               fn_pass_effects_hold (fn_pass_tag pass) current_fn out /\
               introduces_no_invoke_edges current_fn out.fpo_function /\
               ir_supply_extends s out.fpo_supply /\
               ir_supply_covers_fn out.fpo_supply out.fpo_function /\
               ir_supply_covers_unit out.fpo_supply observed
            then run_configured_fn_pass_fold runner rpolicy passes unit
                   out.fpo_supply out.fpo_function
                   (label_map ++ out.fpo_label_map)
            else NONE
End

Definition run_configured_fn_passes_def:
  run_configured_fn_passes runner rpolicy passes name unit supply =
    if ~ir_supply_covers_unit supply unit then NONE
    else
      case lookup_unique_function name unit.cu_context.ctx_functions of
        NONE => NONE
      | SOME fn =>
          case run_configured_fn_pass_fold runner rpolicy passes unit supply fn [] of
            NONE => NONE
          | SOME (fn',label_map,s') =>
              case replace_unique_function name fn'
                     unit.cu_context.ctx_functions of
                NONE => NONE
              | SOME fns =>
                  let candidate =
                    unit with cu_context :=
                      unit.cu_context with ctx_functions := fns
                  in
                    case apply_unit_label_map label_map candidate of
                      NONE => NONE
                    | SOME unit' =>
                        if unit_labels_wf unit' /\
                           list_subset (unit_invoke_targets unit')
                             (unit_invoke_targets unit) /\
                           ir_supply_covers_unit s' unit' /\
                           unit_global_inst_ids_distinct unit'
                        then SOME (unit',s')
                        else NONE
End

Definition run_fn_schedule_def:
  run_fn_schedule rpolicy passes name unit =
    run_configured_fn_passes execute_configured_fn_pass rpolicy passes name
      unit (init_ir_supply unit)
End

val _ = export_theory ();
