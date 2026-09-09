(*
 * Stack Plan Types and Spill Management
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * Types for the plan generator state and spill slot allocation.
 *
 * TOP-LEVEL:
 *   spill_alloc, plan_state — state types
 *   alloc_spill_slot, free_spill_slot, init_spill_alloc — slot management
 *   init_plan_state, fresh_label — state initialization
 *   operand_to_string, is_var_operand, is_label_operand — operand helpers
 *)

Theory stackPlanTypes
Ancestors
  asmIR venomLayout
(* =========================================================================
   Spill Allocator State (global within a function)
   ========================================================================= *)

Datatype:
  spill_alloc = <|
    sa_free_slots : num list;
    sa_next_offset : num;
    sa_spill_base : num
  |>
End

(* =========================================================================
   Plan Generator State
   ========================================================================= *)

Datatype:
  plan_state = <|
    ps_stack : operand list;
    ps_spilled : (operand, num) fmap;
    ps_alloc : spill_alloc;
    ps_label_counter : num
  |>
End


(* =========================================================================
   Context Spill Planning
   ========================================================================= *)

Datatype:
  spill_region = <|
    sr_fn_name : string;
    sr_spill_base : num;
    sr_spill_end : num;
    sr_plan : stack_op list
  |>
End

Datatype:
  context_plan = <|
    cp_regions : spill_region list;
    cp_max_static_eom : num;
    cp_peak_spill_end : num;
    cp_initial_fmp : num
  |>
End

Datatype:
  context_plan_acc = <|
    cpa_regions : spill_region list;
    cpa_label_counter : num;
    cpa_next_spill_base : num;
    cpa_peak_spill_end : num
  |>
End

Definition ordered_spill_regions_def:
  (ordered_spill_regions [] = T) /\
  (ordered_spill_regions (r::rs) =
    (r.sr_spill_base <= r.sr_spill_end /\
     EVERY (\r'. r.sr_spill_end <= r'.sr_spill_base) rs /\
     ordered_spill_regions rs))
End

Definition context_plan_layout_wf_def:
  context_plan_layout_wf cp <=>
    EVERY
      (\r. cp.cp_max_static_eom <= r.sr_spill_base /\
           r.sr_spill_base <= r.sr_spill_end)
      cp.cp_regions /\
    ordered_spill_regions cp.cp_regions /\
    EVERY
      (\r. r.sr_spill_base < r.sr_spill_end ==>
           r.sr_spill_end <= cp.cp_peak_spill_end)
      cp.cp_regions /\
    cp.cp_initial_fmp =
      ceil32 (MAX cp.cp_max_static_eom cp.cp_peak_spill_end) /\
    cp.cp_max_static_eom <= cp.cp_initial_fmp /\
    cp.cp_peak_spill_end <= cp.cp_initial_fmp /\
    cp.cp_initial_fmp MOD 32 = 0
End

Definition region_spill_access_def:
  region_spill_access r off <=>
    MEM (SOSpill off) r.sr_plan \/ MEM (SORestore off) r.sr_plan
End

Definition stack_op_in_spill_region_def:
  stack_op_in_spill_region base spill_end op =
    case op of
      SOSpill off => base <= off /\ off + 32 <= spill_end
    | SORestore off => base <= off /\ off + 32 <= spill_end
    | SOInitialFmp => T
    | _ => T
End

Definition spill_plan_in_region_def:
  spill_plan_in_region base spill_end ops <=>
    EVERY (stack_op_in_spill_region base spill_end) ops
End
(* =========================================================================
   Spill Slot Management
   ========================================================================= *)

Definition alloc_spill_slot_def:
  alloc_spill_slot alloc =
    case alloc.sa_free_slots of
      [] => (alloc.sa_next_offset,
             alloc with sa_next_offset := alloc.sa_next_offset + 32)
    | slots =>
        (LAST slots,
         alloc with sa_free_slots := FRONT slots)
End

Definition free_spill_slot_def:
  free_spill_slot off alloc =
    alloc with sa_free_slots := SNOC off alloc.sa_free_slots
End

Definition init_spill_alloc_def:
  init_spill_alloc spill_base = <|
    sa_free_slots := [];
    sa_next_offset := spill_base;
    sa_spill_base := spill_base
  |>
End

Definition init_plan_state_def:
  init_plan_state spill_base = <|
    ps_stack := [];
    ps_spilled := FEMPTY;
    ps_alloc := init_spill_alloc spill_base;
    ps_label_counter := 0
  |>
End

Definition fresh_label_def:
  fresh_label prefix ps =
    let n = ps.ps_label_counter + 1 in
    (prefix ++ "_" ++ num_to_dec_string n,
     ps with ps_label_counter := n)
End

(* =========================================================================
   Operand Helpers
   ========================================================================= *)

Definition operand_to_string_def:
  operand_to_string (Var s) = s ∧
  operand_to_string (Lit _) = "" ∧
  operand_to_string (Label _) = ""
End

Definition is_var_operand_def:
  is_var_operand (Var _) = T ∧
  is_var_operand (Lit _) = F ∧
  is_var_operand (Label _) = F
End

Definition is_label_operand_def:
  is_label_operand (Label _) = T ∧
  is_label_operand (Var _) = F ∧
  is_label_operand (Lit _) = F
End
