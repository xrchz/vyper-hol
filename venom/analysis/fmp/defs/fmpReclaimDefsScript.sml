(*
 * Conservative executable FMP reclaim analysis.
 *
 * This is an intentional syntactic abstraction of the pinned Python pass, not
 * an exact-parity claim.  It only emits a restore at a terminal instruction
 * boundary after a stable bounded forward analysis.  Every emitted entry is
 * rechecked against analyses recomputed from the supplied current function.
 *)

Theory fmpReclaimDefs
Ancestors
  fmpAnalysisDefs
  livenessDefs
  cfgDefs
  dominatorDefs
  arithmetic
  finite_map

Type fmp_point = ``:string # num``

Datatype:
  fmp_reclaim_state = <|
    frs_stack : string list;
    frs_captures : string list;
    frs_can_reclaim : bool
  |>
End

Type fmp_reclaim_plan = ``:(fmp_point,string) fmap``

Definition fmp_empty_reclaim_state_def:
  fmp_empty_reclaim_state = <|
    frs_stack := [];
    frs_captures := [];
    frs_can_reclaim := T
  |>
End

(* Stacks are newest-first, hence their common top is their common prefix. *)
Definition fmp_common_top_def:
  fmp_common_top [] ys = [] /\
  fmp_common_top xs [] = [] /\
  fmp_common_top (x::xs) (y::ys) =
    if x = y then x::fmp_common_top xs ys else []
End

Definition fmp_reclaim_join_def:
  fmp_reclaim_join x y = <|
    frs_stack := fmp_common_top x.frs_stack y.frs_stack;
    frs_captures := list_union x.frs_captures y.frs_captures;
    frs_can_reclaim := (x.frs_can_reclaim /\ y.frs_can_reclaim)
  |>
End

Definition fmp_reclaim_option_join_def:
  fmp_reclaim_option_join NONE y = y /\
  fmp_reclaim_option_join x NONE = x /\
  fmp_reclaim_option_join (SOME x) (SOME y) =
    SOME (fmp_reclaim_join x y)
End

Definition fmp_single_output_def:
  fmp_single_output (inst:instruction) =
    case inst.inst_outputs of [v] => SOME v | _ => NONE
End

Definition fmp_getfmp_outputs_def:
  fmp_getfmp_outputs (inst:instruction) =
    if inst.inst_opcode = GETFMP then inst.inst_outputs else []
End

Definition fmp_transfer_def:
  fmp_transfer (inst:instruction) NONE = NONE /\
  fmp_transfer (inst:instruction) (SOME (st:fmp_reclaim_state)) =
    let captures = list_union (fmp_getfmp_outputs inst) st.frs_captures in
    let can_reclaim =
      (st.frs_can_reclaim /\
       inst.inst_opcode <> SETFMP /\ inst.inst_opcode <> RETFMP /\
       inst.inst_opcode <> DRET) in
    if inst.inst_opcode = DALLOCA then
      if LENGTH inst.inst_outputs = 1 then
        SOME <| frs_stack := HD inst.inst_outputs::st.frs_stack;
                frs_captures := captures;
                frs_can_reclaim := can_reclaim |>
      else SOME <| frs_stack := st.frs_stack;
                   frs_captures := captures;
                   frs_can_reclaim := F |>
    else SOME <| frs_stack := st.frs_stack;
                 frs_captures := captures;
                 frs_can_reclaim := can_reclaim |>
End

Definition fmp_edge_transfer_def:
  fmp_edge_transfer src dst st = st
End

Definition fmp_reclaim_fuel_def:
  fmp_reclaim_fuel fn =
    (LENGTH fn.fn_blocks + 1) * (LENGTH (fn_insts fn) + 1)
End

Definition fmp_reclaim_analyze_fuel_def:
  fmp_reclaim_analyze_fuel fuel fn =
    case entry_block fn of
      NONE => NONE
    | SOME entry =>
        SOME (df_analyze_fuel fuel Forward NONE fmp_reclaim_option_join
          (K fmp_transfer) (K fmp_edge_transfer) fn.fn_blocks
          (SOME (entry.bb_label,SOME fmp_empty_reclaim_state)) fn)
End

(* A second round with one extra unit of fuel is the executable stability
 * check.  Cycles are therefore total and uncertainty rejects conservatively. *)
Definition fmp_reclaim_states_def:
  fmp_reclaim_states fn =
    case fmp_reclaim_analyze_fuel (fmp_reclaim_fuel fn) fn of
      NONE => NONE
    | SOME states =>
        (case fmp_reclaim_analyze_fuel (fmp_reclaim_fuel fn + 1) fn of
           SOME states' => if states' = states then SOME states else NONE
         | NONE => NONE)
End

Definition fmp_point_well_located_def:
  fmp_point_well_located fn (p:fmp_point) <=>
    ?bb. lookup_block (FST p) fn.fn_blocks = SOME bb /\
         SND p <= LENGTH bb.bb_instructions
End

Definition fmp_find_dalloca_at_aux_def:
  fmp_find_dalloca_at_aux (base:string) (lbl:string) [] (n:num) = NONE /\
  fmp_find_dalloca_at_aux (base:string) (lbl:string)
      ((inst:instruction)::rest) (n:num) =
    if inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [base] then
      SOME (lbl,n,inst)
    else fmp_find_dalloca_at_aux base lbl rest (n + 1)
End

Definition fmp_find_dalloca_def:
  fmp_find_dalloca base [] = NONE /\
  fmp_find_dalloca base (bb::bbs) =
    case fmp_find_dalloca_at_aux base bb.bb_label bb.bb_instructions 0 of
      NONE => fmp_find_dalloca base bbs
    | SOME found => SOME found
End

Definition fmp_definition_dominates_def:
  fmp_definition_dominates fn def_lbl def_i (p:fmp_point) <=>
    (def_lbl = FST p /\ def_i < SND p) \/
    (def_lbl <> FST p /\
     dominates (dom_analyze (cfg_analyze fn) fn) def_lbl (FST p))
End

Definition fmp_transparent_opcode_def:
  fmp_transparent_opcode op <=>
    op = ASSIGN \/ op = ADD \/ op = SUB \/ op = PHI
End

Definition fmp_inst_uses_any_def:
  fmp_inst_uses_any vars inst <=>
    EXISTS (\v. MEM v (inst_uses inst)) vars
End

Definition fmp_derived_step_def:
  fmp_derived_step [] vars = vars /\
  fmp_derived_step (inst::rest) vars =
    let vars' =
      if fmp_transparent_opcode inst.inst_opcode /\
         fmp_inst_uses_any vars inst
      then list_union inst.inst_outputs vars
      else vars in
    fmp_derived_step rest vars'
End

Definition fmp_derived_vars_def:
  fmp_derived_vars fn base =
    FUNPOW (fmp_derived_step (fn_insts fn)) (LENGTH (fn_insts fn)) [base]
End

Definition fmp_operand_at_is_def:
  fmp_operand_at_is base n ops <=>
    n < LENGTH ops /\ EL n ops = Var base
End

Definition fmp_direct_memory_use_def:
  fmp_direct_memory_use inst base <=>
    (inst.inst_opcode = MLOAD /\
       fmp_operand_at_is base 0 inst.inst_operands) \/
    ((inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8) /\
       fmp_operand_at_is base 0 inst.inst_operands) \/
    (inst.inst_opcode = MCOPY /\
       (fmp_operand_at_is base 0 inst.inst_operands \/
        fmp_operand_at_is base 1 inst.inst_operands)) \/
    (inst.inst_opcode = SHA3 /\
       fmp_operand_at_is base 0 inst.inst_operands)
End

Definition fmp_inst_has_unsafe_derived_use_def:
  fmp_inst_has_unsafe_derived_use vars inst <=>
    ?v. MEM v vars /\ MEM v (inst_uses inst) /\
        ~fmp_direct_memory_use inst v /\
        ~fmp_transparent_opcode inst.inst_opcode
End

Definition fmp_target_pinned_def:
  fmp_target_pinned fn base <=>
    EXISTS (fmp_inst_has_unsafe_derived_use (fmp_derived_vars fn base))
      (fn_insts fn)
End

Definition fmp_capture_escaped_def:
  fmp_capture_escaped fn cap <=>
    EXISTS (\inst. MEM cap (inst_uses inst)) (fn_insts fn)
End

Definition fmp_capture_veto_def:
  fmp_capture_veto fn live (p:fmp_point) cap <=>
    MEM cap (live_vars_at live (FST p) (SND p)) \/
    fmp_capture_escaped fn cap
End

Definition fmp_restore_target_ok_def:
  fmp_restore_target_ok infos ctx fn live captures (p:fmp_point) base <=>
    fmp_info_valid ctx infos /\ MEM fn ctx.ctx_functions /\
    fmp_point_well_located fn p /\
    ?def_lbl def_i dalloca.
      fmp_find_dalloca base fn.fn_blocks = SOME (def_lbl,def_i,dalloca) /\
      dalloca.inst_opcode = DALLOCA /\ dalloca.inst_outputs = [base] /\
      fmp_definition_dominates fn def_lbl def_i p /\
      EVERY (\v. ~MEM v (live_vars_at live (FST p) (SND p)))
        (fmp_derived_vars fn base) /\
      ~fmp_target_pinned fn base /\
      EVERY (\cap. ~fmp_capture_veto fn live p cap) captures
End

Definition fmp_stack_reclaimable_def:
  fmp_stack_reclaimable infos ctx fn live captures p stack <=>
    stack <> [] /\ EVERY (fmp_restore_target_ok infos ctx fn live captures p) stack
End

Definition fmp_oldest_def:
  fmp_oldest (x::xs) = LAST (x::xs)
End

Definition fmp_block_restore_def:
  fmp_block_restore infos ctx fn live cfg states bb =
    let p = (bb.bb_label,LENGTH bb.bb_instructions) in
    if cfg_succs_of cfg bb.bb_label <> [] then NONE
    else
      case df_at NONE states bb.bb_label (LENGTH bb.bb_instructions) of
        NONE => NONE
      | SOME st =>
          if st.frs_can_reclaim /\
             fmp_stack_reclaimable infos ctx fn live st.frs_captures p st.frs_stack
          then SOME (p,fmp_oldest st.frs_stack)
          else NONE
End

Definition fmp_collect_candidates_def:
  fmp_collect_candidates infos ctx fn live cfg states [] = [] /\
  fmp_collect_candidates infos ctx fn live cfg states (bb::bbs) =
    case fmp_block_restore infos ctx fn live cfg states bb of
      NONE => fmp_collect_candidates infos ctx fn live cfg states bbs
    | SOME entry => entry::fmp_collect_candidates infos ctx fn live cfg states bbs
End

Definition fmp_plan_of_list_def:
  fmp_plan_of_list [] = FEMPTY /\
  fmp_plan_of_list ((p,base)::rest) = fmp_plan_of_list rest |+ (p,base)
End

Definition fmp_reclaim_entry_ok_def:
  fmp_reclaim_entry_ok infos ctx fn (p:fmp_point) base <=>
    fmp_restore_target_ok infos ctx fn (liveness_analyze fn)
      (FLAT (MAP fmp_getfmp_outputs (fn_insts fn))) p base
End

Definition fmp_reclaim_plan_ok_def:
  fmp_reclaim_plan_ok infos ctx fn (plan:fmp_reclaim_plan) <=>
    !p base. FLOOKUP plan p = SOME base ==>
      fmp_reclaim_entry_ok infos ctx fn p base
End

Definition fmp_candidate_plan_def:
  fmp_candidate_plan infos ctx fn states =
    let live = liveness_analyze fn in
    let cfg = cfg_analyze fn in
    fmp_plan_of_list
      (fmp_collect_candidates infos ctx fn live cfg states fn.fn_blocks)
End

Definition analyze_fmp_reclaims_def:
  analyze_fmp_reclaims (infos:fmp_info_map) (ctx:venom_context)
      (fn:ir_function) : fmp_reclaim_plan option =
    if ~fmp_info_valid ctx infos \/ ~MEM fn ctx.ctx_functions \/
       ~wf_function fn \/ ~fn_inst_wf fn \/ fn.fn_fmp_signature <> NONE
    then NONE
    else
      case fmp_reclaim_states fn of
        NONE => NONE
      | SOME states =>
          let plan = fmp_candidate_plan infos ctx fn states in
          if fmp_reclaim_plan_ok infos ctx fn plan then SOME plan else NONE
End

val _ = export_theory();
