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

val _ = export_theory();
