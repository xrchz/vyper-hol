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

val _ = export_theory();
