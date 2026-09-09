(*
 * Checked static-layout vocabulary.
 *
 * This foundational theory is deliberately independent of venomWfTheory and
 * of the legacy liveness allocator.
 *)

Theory staticLayoutDefs
Ancestors
  memLocDefs

Datatype:
  concretize_layout = <|
    cl_positions : (allocation, num) fmap;
    cl_eom : num
  |>
End

(* A reserved interval denotes the nonempty half-open range [pos,pos+size).
   Its exclusive endpoint must itself be a representable 256-bit address. *)
Definition reserved_interval_wf_def:
  reserved_interval_wf (pos, size) <=>
    0 < size /\ pos + size < dimword (:256)
End

Definition reserved_intervals_disjoint_def:
  reserved_intervals_disjoint ((pos1 : num), size1) (pos2, size2) <=>
    pos1 + size1 <= pos2 \/ pos2 + size2 <= pos1
End

Definition reserved_intervals_wf_def:
  reserved_intervals_wf [] = T /\
  reserved_intervals_wf (r::rs) =
    (reserved_interval_wf r /\
     EVERY (reserved_intervals_disjoint r) rs /\
     reserved_intervals_wf rs)
End

(* Extract the exclusive end of exactly one statically placed ALLOCA. *)
Definition allocation_end_def:
  allocation_end positions inst =
    case (inst.inst_operands,
          FLOOKUP positions (Allocation inst.inst_id)) of
      ([Lit sz], SOME pos) => SOME (pos + w2n sz)
    | _ => NONE
End

(* Check and accumulate the maximum exclusive end of global reservations. *)
Definition global_reserved_end_def:
  global_reserved_end [] eom = SOME eom /\
  global_reserved_end ((pos,size)::rs) eom =
    let alloc_end = pos + size in
      if reserved_interval_wf (pos,size)
      then global_reserved_end rs (MAX eom alloc_end)
      else NONE
End

(* Check every ALLOCA and accumulate its maximum exclusive end. *)
Definition allocation_eom_fold_def:
  allocation_eom_fold positions [] eom = SOME eom /\
  allocation_eom_fold positions (inst::insts) eom =
    if inst.inst_opcode = ALLOCA then
      case allocation_end positions inst of
        NONE => NONE
      | SOME alloc_end =>
          if alloc_end < dimword (:256)
          then allocation_eom_fold positions insts (MAX eom alloc_end)
          else NONE
    else allocation_eom_fold positions insts eom
End

Definition mk_concretize_layout_def:
  mk_concretize_layout reserved positions fn =
    case global_reserved_end reserved 0 of
      NONE => NONE
    | SOME global_eom =>
        case allocation_eom_fold positions (fn_insts fn) global_eom of
          NONE => NONE
        | SOME eom => SOME <| cl_positions := positions; cl_eom := eom |>
End

val _ = export_theory();
