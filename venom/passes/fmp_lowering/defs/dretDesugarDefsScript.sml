(*
 * Target-checked DRET desugaring definitions.
 *)

Theory dretDesugarDefs
Ancestors
  dretShapeDefs irSupply

Definition dret_value_operand_def:
  dret_value_operand op <=>
    (?w. op = Lit w) \/ (?v. op = Var v)
End

Definition dret_desugar_input_def:
  dret_desugar_input fn <=>
    fn.fn_fmp_signature = NONE /\
    (!inst. MEM inst (fn_insts fn) /\ inst.inst_opcode = DRET ==>
            IS_SOME (parse_dret_shape inst) /\
            EVERY dret_value_operand inst.inst_operands)
End

Definition no_dret_def:
  no_dret fn <=>
    !inst. MEM inst (fn_insts fn) ==> inst.inst_opcode <> DRET
End

(* Executable views for the pass guards. *)
Theorem dret_value_operand_compute[compute]:
  dret_value_operand op <=>
    case op of
      Lit w => T
    | Var v => T
    | Label lbl => F
Proof
  Cases_on `op` >> simp[dret_value_operand_def]
QED

Theorem dret_desugar_input_compute[compute]:
  dret_desugar_input fn <=>
    fn.fn_fmp_signature = NONE /\
    EVERY
      (λinst. inst.inst_opcode = DRET ==>
              IS_SOME (parse_dret_shape inst) /\
              EVERY dret_value_operand inst.inst_operands)
      (fn_insts fn)
Proof
  simp[dret_desugar_input_def, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem no_dret_compute[compute]:
  no_dret fn <=>
    EVERY (λinst. inst.inst_opcode <> DRET) (fn_insts fn)
Proof
  simp[no_dret_def, listTheory.EVERY_MEM]
QED

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
Datatype:
  dret_pair_expansion =
    DretPairExpansion (instruction list) (operand list) operand ir_supply
End

Definition expand_dret_pairs_def:
  expand_dret_pairs s cursor [] =
    SOME (DretPairExpansion [] [] cursor s) /\
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
     | SOME (DretPairExpansion tail dsts final_cursor s8) =>
         SOME (DretPairExpansion
           (mk_inst copy_id MCOPY [cursor;src;size] [] ::
            mk_inst plus31_id ADD [size; Lit 31w] [plus31_v] ::
            mk_inst align_id AND
              [Var plus31_v;
               Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
              [aligned_v] ::
            mk_inst next_id ADD [cursor; Var aligned_v] [next_v] :: tail)
           (cursor::dsts) final_cursor s8)) /\
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
        | SOME (DretPairExpansion body dsts final_cursor s1) =>
            (case fresh_inst_id s1 of (setfmp_id,s2) =>
             case fresh_inst_id s2 of (retfmp_id,s3) =>
               SOME
                 (body ++
                  [mk_inst setfmp_id SETFMP [final_cursor] [];
                   mk_inst retfmp_id RETFMP
                     (ordinary ++ dsts ++ [return_pc]) []],
                  s3))
End

Definition dret_desugar_insts_def:
  dret_desugar_insts s entry_cursor [] = SOME ([],s) /\
  dret_desugar_insts s entry_cursor (inst::insts) =
    if inst.inst_opcode = DRET then
      case replace_dret_inst s entry_cursor inst of
        NONE => NONE
      | SOME (replacement,s1) =>
          case dret_desugar_insts s1 entry_cursor insts of
            NONE => NONE
          | SOME (tail,s2) => SOME (replacement ++ tail,s2)
    else
      case dret_desugar_insts s entry_cursor insts of
        NONE => NONE
      | SOME (tail,s1) => SOME (inst::tail,s1)
End

Definition dret_desugar_blocks_def:
  dret_desugar_blocks s entry_cursor [] = SOME ([],s) /\
  dret_desugar_blocks s entry_cursor (bb::bbs) =
    case dret_desugar_insts s entry_cursor bb.bb_instructions of
      NONE => NONE
    | SOME (insts,s1) =>
        case dret_desugar_blocks s1 entry_cursor bbs of
          NONE => NONE
        | SOME (tail,s2) =>
            SOME ((bb with bb_instructions := insts)::tail,s2)
End

Definition dret_desugar_function_def:
  dret_desugar_function target s fn =
    if no_dret fn then SOME (fn,s)
    else if ~(dret_desugar_input fn /\ target CapMcopy) then NONE
    else
      case fn.fn_blocks of
        [] => NONE
      | first::rest =>
          (case fresh_ir_var s of (entry_v,s1) =>
           case fresh_inst_id s1 of (getfmp_id,s2) =>
           case dret_desugar_blocks s2 (Var entry_v) (first::rest) of
             NONE => NONE
           | SOME (blocks,s3) =>
               case blocks of
                 [] => NONE
               | first'::rest' =>
                   SOME
                     (fn with fn_blocks :=
                       (first' with bb_instructions :=
                         mk_inst getfmp_id GETFMP [] [entry_v] ::
                         first'.bb_instructions)::rest',
                      s3))
End

Definition dret_desugar_context_def:
  dret_desugar_context target s ctx =
    map_ctx_functions_supply (dret_desugar_function target) s ctx
End

Definition dret_desugar_configured_with_supply_def:
  dret_desugar_configured_with_supply target unit =
    case dret_desugar_context target (init_ir_supply unit) unit.cu_context of
      NONE => NONE
    | SOME (ctx,s) => SOME (unit with cu_context := ctx,s)
End

Definition dret_desugar_configured_def:
  dret_desugar_configured target unit =
    OPTION_MAP FST (dret_desugar_configured_with_supply target unit)
End

val _ = export_theory();
