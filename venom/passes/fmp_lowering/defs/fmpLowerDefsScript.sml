(*
 * Checked frame-memory-pointer lowering.
 *)

Theory fmpLowerDefs
Ancestors
  dretDesugarDefs fmpReclaimDefs irSupply

(* A checked decomposition of the physical entry prefix before FMP lowering.
   User PARAM instructions are retained in source order; an existing hidden FMP
   parameter is rejected, and the optional RETPC parameter is separated from
   the ordinary body. *)
Datatype:
  fmp_entry_layout =
    FmpEntryLayout (instruction list) (instruction option) (instruction list)
End

Definition split_fmp_entry_from_def:
  split_fmp_entry_from k users [] =
    SOME (FmpEntryLayout (REVERSE users) NONE []) /\
  split_fmp_entry_from k users (inst::insts) =
    if inst.inst_opcode = PARAM then
      if param_inst_at k inst then
        split_fmp_entry_from (SUC k) (inst::users) insts
      else NONE
    else if inst.inst_opcode = FMP_PARAM then NONE
    else if inst.inst_opcode = RETPC_PARAM then
      if param_inst_at k inst /\ no_param_insts insts then
        SOME (FmpEntryLayout (REVERSE users) (SOME inst) insts)
      else NONE
    else if no_param_insts (inst::insts) then
      SOME (FmpEntryLayout (REVERSE users) NONE (inst::insts))
    else NONE
End

Definition split_fmp_entry_def:
  split_fmp_entry fn =
    case fn.fn_blocks of
      [] => NONE
    | entry::_ => split_fmp_entry_from 0 [] entry.bb_instructions
End

Definition set_param_index_def:
  set_param_index k inst = inst with inst_operands := [Lit (n2w k)]
End

(* Resolve an INVOKE against both the current context and the freshly computed
   information map.  The returned argument list excludes the leading label. *)
Definition fmp_resolve_invoke_def:
  fmp_resolve_invoke infos ctx inst =
    if inst.inst_opcode <> INVOKE then NONE
    else
      case inst.inst_operands of
        Label name::args =>
          (case lookup_function name ctx.ctx_functions of
             NONE => NONE
           | SOME callee =>
               case FLOOKUP infos name of
                 NONE => NONE
               | SOME info => SOME (callee,info,args))
      | _ => NONE
End

(* Exact envelopes consumed by the lowering engine.  In particular DRET and
   malformed raw operations cannot fall through as ordinary instructions. *)
Definition fmp_lower_inst_shape_def:
  fmp_lower_inst_shape infos ctx inst <=>
    case inst.inst_opcode of
      DALLOCA => LENGTH inst.inst_operands = 1 /\
                 LENGTH inst.inst_outputs = 1
    | DRET => F
    | GETFMP => inst.inst_operands = [] /\
                LENGTH inst.inst_outputs = 1
    | SETFMP => LENGTH inst.inst_operands = 1 /\
                inst.inst_outputs = []
    | RETFMP => inst.inst_operands <> [] /\ inst.inst_outputs = []
    | INVOKE => IS_SOME (fmp_resolve_invoke infos ctx inst)
    | op => ~is_raw_fmp_opcode op
End

Definition fmp_lower_insts_shape_def:
  fmp_lower_insts_shape infos ctx insts <=>
    EVERY (fmp_lower_inst_shape infos ctx) insts
End

Definition fmp_lower_blocks_shape_def:
  fmp_lower_blocks_shape infos ctx bbs <=>
    EVERY (\bb. fmp_lower_insts_shape infos ctx bb.bb_instructions) bbs
End

(* The internal lowering boundary is independently checked: the function must
   be the current context member, unsealed, covered by current information,
   canonically parameterized without an existing FMP parameter, and every
   instruction must have a supported exact envelope. *)
Definition fmp_lower_input_def:
  fmp_lower_input infos ctx fn <=>
    lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
    fn.fn_fmp_signature = NONE /\
    FLOOKUP infos fn.fn_name <> NONE /\
    canonical_param_prefix fn /\
    fn_hidden_fmp_param fn = NONE /\
    IS_SOME (split_fmp_entry fn) /\
    fmp_lower_blocks_shape infos ctx fn.fn_blocks
End

(* Select restores at one exact endpoint while preserving plan order.  The
   second component is threaded through all blocks and must be empty at the
   outer boundary, so an unlocated analysis result cannot be ignored. *)
Definition fmp_select_point_restores_def:
  fmp_select_point_restores p [] = ([],[]) /\
  fmp_select_point_restores p ((q,base)::rest) =
    let (here,later) = fmp_select_point_restores p rest in
      if q = p then (base::here,later)
      else (here,(q,base)::later)
End

Definition fmp_reclaim_input_def:
  fmp_reclaim_input fn plan <=>
    plan.frp_function = fn.fn_name /\
    EVERY (\pb. fmp_point_well_located fn (FST pb)) plan.frp_restores
End

(* Lower one checked instruction.  Single-instruction rewrites retain the
   source ID; a DALLOCA expansion obtains every temporary and instruction ID
   from the unit supply. *)
Definition fmp_lower_inst_def:
  fmp_lower_inst infos ctx runner s inst =
    if ~fmp_lower_inst_shape infos ctx inst then NONE
    else
      case inst.inst_opcode of
        DALLOCA =>
          (case inst.inst_operands of
             [size_op] =>
               (case inst.inst_outputs of
                  [old] =>
                    (case fresh_ir_var s of (plus31,s1) =>
                     case fresh_ir_var s1 of (aligned,s2) =>
                     case fresh_inst_id s2 of (add_id,s3) =>
                     case fresh_inst_id s3 of (and_id,s4) =>
                     case fresh_inst_id s4 of (bump_id,s5) =>
                       SOME
                         ([mk_inst add_id ADD [size_op; Lit 31w] [plus31];
                           mk_inst and_id AND
                             [Var plus31;
                              Lit 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0w]
                             [aligned];
                           mk_inst bump_id BUMP
                             [Var runner; Var aligned] [old;runner]],
                          s5))
                | _ => NONE)
           | _ => NONE)
      | DRET => NONE
      | GETFMP =>
          (case inst.inst_outputs of
             [out] => SOME ([inst with <| inst_opcode := ASSIGN;
                                        inst_operands := [Var runner] |>],s)
           | _ => NONE)
      | SETFMP =>
          (case inst.inst_operands of
             [value] => SOME ([inst with <| inst_opcode := ASSIGN;
                                          inst_outputs := [runner] |>],s)
           | _ => NONE)
      | RETFMP =>
          if NULL inst.inst_operands then NONE
          else SOME
            ([inst with <| inst_opcode := RET;
                         inst_operands :=
                           FRONT inst.inst_operands ++
                           [Var runner; LAST inst.inst_operands] |>],s)
      | INVOKE =>
          (case fmp_resolve_invoke infos ctx inst of
             NONE => NONE
           | SOME (callee,info,args) =>
               SOME
                 ([inst with <|
                     inst_operands :=
                       Label callee.fn_name ::
                       (args ++ if info.fi_needs_fmp then [Var runner] else []);
                     inst_outputs :=
                       inst.inst_outputs ++
                       if info.fi_publishes_fmp then [runner] else [] |>],s))
      | op =>
          if is_raw_fmp_opcode op then NONE else SOME ([inst],s)
End

Definition fmp_lower_insts_def:
  fmp_lower_insts infos ctx runner s [] = SOME ([],s) /\
  fmp_lower_insts infos ctx runner s (inst::insts) =
    case fmp_lower_inst infos ctx runner s inst of
      NONE => NONE
    | SOME (head,s1) =>
        case fmp_lower_insts infos ctx runner s1 insts of
          NONE => NONE
        | SOME (tail,s2) => SOME (head ++ tail,s2)
End

Definition fmp_emit_restores_def:
  fmp_emit_restores runner s [] = ([],s) /\
  fmp_emit_restores runner s (base::bases) =
    case fresh_inst_id s of (id,s1) =>
    case fmp_emit_restores runner s1 bases of (tail,s2) =>
      (mk_inst id ASSIGN [Var base] [runner]::tail,s2)
End

Datatype:
  fmp_blocks_result =
    FmpBlocksResult (basic_block list) ((fmp_point # string) list) ir_supply
End

(* Reclaim points refer to original instruction indices.  Each block selects
   its exact original endpoint before rewriting; leftovers are returned for the
   outer checked boundary to reject. *)
Definition fmp_lower_blocks_def:
  fmp_lower_blocks infos ctx runner s restores [] =
    SOME (FmpBlocksResult [] restores s) /\
  fmp_lower_blocks infos ctx runner s restores (bb::bbs) =
    case fmp_lower_insts infos ctx runner s bb.bb_instructions of
      NONE => NONE
    | SOME (insts,s1) =>
        let p = <| fp_block := bb.bb_label;
                   fp_index := LENGTH bb.bb_instructions |> in
        let (bases,later) = fmp_select_point_restores p restores in
        case fmp_emit_restores runner s1 bases of (restore_insts,s2) =>
        case fmp_lower_blocks infos ctx runner s2 later bbs of
          NONE => NONE
        | SOME (FmpBlocksResult tail leftover s3) =>
            SOME (FmpBlocksResult
              ((bb with bb_instructions := insts ++ restore_insts)::tail)
              leftover s3)
End

val _ = export_theory();
