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
  asmIR

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
