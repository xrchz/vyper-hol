(*
 * Structural parser for dynamic-return (DRET) operand envelopes.
 *)

Theory dretShapeDefs
Ancestors
  venomInst

Definition parse_dret_shape_def:
  parse_dret_shape inst =
    case inst.inst_operands of
      Lit k :: rest =>
        let dyn_count = w2n k in
        let n = LENGTH inst.inst_operands in
        if 0 < dyn_count /\ 2 + 2 * dyn_count <= n then
          SOME (n - 2 - 2 * dyn_count, dyn_count)
        else NONE
    | _ => NONE
End

Theorem parse_dret_shape_length:
  parse_dret_shape inst = SOME (ordinary,dynamic) ==>
  0 < dynamic /\
  LENGTH inst.inst_operands = 2 + ordinary + 2 * dynamic
Proof
  Cases_on `inst.inst_operands` >>
  gvs[parse_dret_shape_def] >>
  Cases_on `h` >>
  gvs[parse_dret_shape_def] >>
  decide_tac
QED
