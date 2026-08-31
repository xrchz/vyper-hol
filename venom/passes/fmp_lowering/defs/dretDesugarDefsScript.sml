(*
 * Target-checked DRET desugaring definitions.
 *)

Theory dretDesugarDefs
Ancestors
  dretShapeDefs irSupply

Definition dret_desugar_input_def:
  dret_desugar_input fn <=>
    fn.fn_fmp_signature = NONE /\
    (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = DRET ==>
            IS_SOME (parse_dret_shape inst))
End

Definition no_dret_def:
  no_dret fn <=>
    !inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> DRET
End

Definition map_functions_supply_def:
  map_functions_supply f s [] = SOME ([],s) /\
  map_functions_supply f s (fn::fns) =
    case f s fn of
      NONE => NONE
    | SOME (fn',s') =>
        case map_functions_supply f s' fns of
          NONE => NONE
        | SOME (fns',s'') => SOME (fn'::fns',s'')
End

Definition map_ctx_functions_supply_def:
  map_ctx_functions_supply f s ctx =
    case map_functions_supply f s ctx.ctx_functions of
      NONE => NONE
    | SOME (fns,s') => SOME (ctx with ctx_functions := fns,s')
End

(* Split a parser-accepted raw DRET envelope.  The count literal itself is
   omitted; the final operand is the original return-PC operand. *)
Definition split_dret_operands_def:
  split_dret_operands inst =
    case parse_dret_shape inst of
      NONE => NONE
    | SOME (ordinary,dynamic) =>
        let rest = TL inst.inst_operands in
          SOME (TAKE ordinary rest,
                TAKE (2 * dynamic) (DROP ordinary rest),
                EL (LENGTH rest - 1) rest)
End

(* Expand an exact source/size-pair list from left to right.  The result is
   (emitted instructions, destination operands, final cursor, final supply). *)
Definition expand_dret_pairs_def:
  expand_dret_pairs s cursor [] = SOME ([],[],cursor,s) /\
  expand_dret_pairs s cursor (src::size::pairs) =
    (case fresh_ir_var s of (plus31_v,s1) =>
     case fresh_ir_var s1 of (aligned_v,s2) =>
     case fresh_ir_var s2 of (next_v,s3) =>
     case fresh_inst_id s3 of (copy_id,s4) =>
     case fresh_inst_id s4 of (plus31_id,s5) =>
     case fresh_inst_id s5 of (align_id,s6) =>
     case fresh_inst_id s6 of (next_id,s7) =>
     case expand_dret_pairs s7 (Var next_v) pairs of
       NONE => NONE
     | SOME (tail,dsts,final_cursor,s8) =>
         SOME
           (mk_inst copy_id MCOPY [cursor;src;size] [] ::
            mk_inst plus31_id ADD [size; Lit 31w] [plus31_v] ::
            mk_inst align_id AND
              [Var plus31_v;
               Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
              [aligned_v] ::
            mk_inst next_id ADD [cursor; Var aligned_v] [next_v] :: tail,
            cursor::dsts, final_cursor, s8)) /\
  expand_dret_pairs s cursor _ = NONE
End

Definition replace_dret_inst_def:
  replace_dret_inst s entry_cursor inst =
    if inst.inst_opcode <> DRET then NONE else
    case split_dret_operands inst of
      NONE => NONE
    | SOME (ordinary,pairs,return_pc) =>
        case expand_dret_pairs s entry_cursor pairs of
          NONE => NONE
        | SOME (body,dsts,final_cursor,s1) =>
            (case fresh_inst_id s1 of (setfmp_id,s2) =>
             case fresh_inst_id s2 of (retfmp_id,s3) =>
               SOME
                 (body ++
                  [mk_inst setfmp_id SETFMP [final_cursor] [];
                   mk_inst retfmp_id RETFMP
                     (ordinary ++ dsts ++ [return_pc]) []],
                  s3))
End

val _ = export_theory();
