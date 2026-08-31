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

val _ = export_theory();
