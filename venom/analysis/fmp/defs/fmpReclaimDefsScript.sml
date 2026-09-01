(*
 * Conservative syntactic FMP reclaim analysis.
 *
 * Pinned-upstream comparison boundary: the reclaim logic in the pinned
 * Vyper Venom FMP-lowering pass (vyper/venom/passes/*; see VYPER_PIN) uses
 * Python analysis/provenance objects which are not represented by the HOL
 * instruction record.  This theory therefore exposes an intentional
 * abstraction, not an exact-parity claim, and accepts no cached external
 * liveness, DFG, or reclaim map.
 *
 * Syntactic use classification frozen for this abstraction:
 *   - a well-shaped DALLOCA with exactly one output creates a LIFO mark;
 *   - an exact base variable used only in an explicitly recognized memory
 *     address position is a direct admissible use;
 *   - PHI, ASSIGN, arithmetic/derived-pointer, or any otherwise unclassified
 *     use pins the mark;
 *   - storing the base as a value or passing it to call-like code captures it;
 *   - returning, invoking, or otherwise publishing the base escapes it.
 * Unknown or overlapping cases take the strongest conservative veto.
 *)

Theory fmpReclaimDefs
Ancestors
  fmpAnalysisDefs
  livenessDefs
  cfgDefs
  arithmetic
  finite_map

Datatype:
  fmp_point = <| fp_block : string; fp_index : num |>
End

Datatype:
  fmp_mark = <|
    fm_point : fmp_point;
    fm_inst_id : num;
    fm_base : string
  |>
End

Datatype:
  fmp_reclaim_state = <|
    frs_marks : fmp_mark list;
    frs_vetoed : string list
  |>
End

Datatype:
  fmp_reclaim_plan = <|
    frp_function : string;
    frp_restores : (fmp_point # string) list
  |>
End

Definition fmp_empty_state_def:
  fmp_empty_state = <| frs_marks := []; frs_vetoed := [] |>
End

Definition fmp_common_prefix_def:
  fmp_common_prefix [] ys = [] /\
  fmp_common_prefix xs [] = [] /\
  fmp_common_prefix (x::xs) (y::ys) =
    if x = y then x::fmp_common_prefix xs ys else []
End

Definition fmp_state_join_def:
  fmp_state_join NONE y = y /\
  fmp_state_join x NONE = x /\
  fmp_state_join (SOME x) (SOME y) = SOME <|
    frs_marks := fmp_common_prefix x.frs_marks y.frs_marks;
    frs_vetoed := list_union x.frs_vetoed y.frs_vetoed
  |>
End

Definition fmp_find_inst_index_def:
  fmp_find_inst_index id [] (n:num) = NONE /\
  fmp_find_inst_index id (inst::rest) n =
    if inst.inst_id = id then SOME n
    else fmp_find_inst_index id rest (n + 1)
End

Definition fmp_find_inst_point_def:
  fmp_find_inst_point id [] = NONE /\
  fmp_find_inst_point id (bb::bbs) =
    case fmp_find_inst_index id bb.bb_instructions 0 of
      SOME n => SOME <| fp_block := bb.bb_label; fp_index := n |>
    | NONE => fmp_find_inst_point id bbs
End

Definition fmp_dalloca_mark_def:
  fmp_dalloca_mark bbs inst =
    if inst.inst_opcode = DALLOCA then
      case inst.inst_outputs of
        [v] =>
          (case fmp_find_inst_point inst.inst_id bbs of
             NONE => NONE
           | SOME p => SOME <| fm_point := p;
                              fm_inst_id := inst.inst_id;
                              fm_base := v |>)
      | _ => NONE
    else NONE
End

Definition fmp_operand_at_is_def:
  fmp_operand_at_is base n ops <=>
    n < LENGTH ops /\ EL n ops = Var base
End

Definition fmp_direct_base_use_def:
  fmp_direct_base_use inst base <=>
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

Definition fmp_call_like_opcode_def:
  fmp_call_like_opcode op <=>
    op = CALL \/ op = STATICCALL \/ op = DELEGATECALL \/
    op = CREATE \/ op = CREATE2 \/ op = INVOKE
End

Definition fmp_escape_opcode_def:
  fmp_escape_opcode op <=>
    op = RET \/ op = RETFMP \/ op = DRET \/ op = RETURN \/
    op = REVERT \/ op = INVOKE
End

Definition fmp_inst_captures_def:
  fmp_inst_captures inst base <=>
    MEM base (inst_uses inst) /\
    (fmp_call_like_opcode inst.inst_opcode \/
     ((inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8) /\
      fmp_operand_at_is base 1 inst.inst_operands))
End

Definition fmp_inst_escapes_def:
  fmp_inst_escapes inst base <=>
    MEM base (inst_uses inst) /\ fmp_escape_opcode inst.inst_opcode
End

Definition fmp_inst_pins_def:
  fmp_inst_pins inst base <=>
    MEM base (inst_uses inst) /\
    ~fmp_direct_base_use inst base /\
    ~fmp_inst_captures inst base /\
    ~fmp_inst_escapes inst base
End

Definition fmp_target_pinned_def:
  fmp_target_pinned fn base <=>
    EXISTS (\inst. fmp_inst_pins inst base) (fn_insts fn)
End

Definition fmp_target_captured_def:
  fmp_target_captured fn base <=>
    EXISTS (\inst. fmp_inst_captures inst base) (fn_insts fn)
End

Definition fmp_target_escapes_def:
  fmp_target_escapes fn base <=>
    EXISTS (\inst. fmp_inst_escapes inst base) (fn_insts fn)
End

Definition fmp_veto_marks_def:
  fmp_veto_marks inst [] vetoed = vetoed /\
  fmp_veto_marks inst (m::ms) vetoed =
    fmp_veto_marks inst ms
      (if MEM m.fm_base (inst_uses inst) /\
          ~fmp_direct_base_use inst m.fm_base
       then set_insert m.fm_base vetoed else vetoed)
End

Definition fmp_mark_transfer_def:
  fmp_mark_transfer bbs inst NONE = NONE /\
  fmp_mark_transfer bbs inst (SOME st) =
    let vetoed = fmp_veto_marks inst st.frs_marks st.frs_vetoed in
    case fmp_dalloca_mark bbs inst of
      NONE => SOME (st with frs_vetoed := vetoed)
    | SOME mark => SOME <| frs_marks := st.frs_marks ++ [mark];
                          frs_vetoed := vetoed |>
End

Definition fmp_mark_edge_transfer_def:
  fmp_mark_edge_transfer bbs src dst st = st
End

Definition fmp_mark_fuel_def:
  fmp_mark_fuel fn =
    (LENGTH fn.fn_blocks + 1) * (LENGTH (fn_insts fn) + 1)
End

Definition fmp_mark_analyze_fuel_def:
  fmp_mark_analyze_fuel fuel fn =
    case entry_block fn of
      NONE => NONE
    | SOME entry =>
        SOME (df_analyze_fuel fuel Forward NONE fmp_state_join
          fmp_mark_transfer fmp_mark_edge_transfer fn.fn_blocks
          (SOME (entry.bb_label, SOME fmp_empty_state)) fn)
End

Definition fmp_mark_analyze_def:
  fmp_mark_analyze fn =
    case fmp_mark_analyze_fuel (fmp_mark_fuel fn) fn of
      NONE => NONE
    | SOME st =>
        (case fmp_mark_analyze_fuel (fmp_mark_fuel fn + 1) fn of
           SOME st' => if st' = st then SOME st else NONE
         | NONE => NONE)
End

Definition fmp_point_well_located_def:
  fmp_point_well_located fn p <=>
    ?bb. lookup_block p.fp_block fn.fn_blocks = SOME bb /\
         p.fp_index <= LENGTH bb.bb_instructions
End

Definition fmp_mark_matches_base_def:
  fmp_mark_matches_base fn mark base <=>
    mark.fm_base = base /\
    ?bb inst.
      lookup_block mark.fm_point.fp_block fn.fn_blocks = SOME bb /\
      mark.fm_point.fp_index < LENGTH bb.bb_instructions /\
      EL mark.fm_point.fp_index bb.bb_instructions = inst /\
      inst.inst_id = mark.fm_inst_id /\
      inst.inst_opcode = DALLOCA /\ inst.inst_outputs = [base]
End

(* This deliberately conservative executable dominance relation accepts only
 * same-block, forward instruction order.  Cross-block candidates discovered
 * by the stack analysis are filtered out rather than justified by logical
 * path quantification. *)
Definition fmp_mark_dominates_point_def:
  fmp_mark_dominates_point mark p <=>
    mark.fm_point.fp_block = p.fp_block /\
    mark.fm_point.fp_index < p.fp_index
End

Definition fmp_find_base_mark_def:
  fmp_find_base_mark base [] = NONE /\
  fmp_find_base_mark base (bb::bbs) =
    case FIND (\inst. inst.inst_opcode = DALLOCA /\
                       inst.inst_outputs = [base]) bb.bb_instructions of
      NONE => fmp_find_base_mark base bbs
    | SOME inst => fmp_dalloca_mark (bb::bbs) inst
End

Definition fmp_restore_target_ok_def:
  fmp_restore_target_ok ctx fn live p base <=>
    lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
    fmp_point_well_located fn p /\
    ?mark.
      fmp_find_base_mark base fn.fn_blocks = SOME mark /\
      fmp_mark_matches_base fn mark base /\
      fmp_mark_dominates_point mark p /\
      ~MEM base (live_vars_at live p.fp_block p.fp_index) /\
      ~fmp_target_pinned fn base /\
      ~fmp_target_captured fn base /\
      ~fmp_target_escapes fn base
End

Definition fmp_take_reclaimable_def:
  fmp_take_reclaimable ctx fn live p vetoed [] = [] /\
  fmp_take_reclaimable ctx fn live p vetoed (m::ms) =
    if MEM m.fm_base vetoed then []
    else if fmp_restore_target_ok ctx fn live p m.fm_base then
      (p,m.fm_base)::fmp_take_reclaimable ctx fn live p vetoed ms
    else []
End

Definition fmp_exit_reclaim_allowed_def:
  fmp_exit_reclaim_allowed cfg lbl <=>
    case cfg_succs_of cfg lbl of
      [] => T
    | [succ] => cfg_preds_of cfg succ = [lbl]
    | _ => F
End

Definition fmp_collect_block_restores_def:
  fmp_collect_block_restores ctx fn live marks cfg bb =
    let p = <| fp_block := bb.bb_label;
               fp_index := LENGTH bb.bb_instructions |> in
    if ~fmp_exit_reclaim_allowed cfg bb.bb_label then []
    else
      case df_at NONE marks bb.bb_label (LENGTH bb.bb_instructions) of
        NONE => []
      | SOME st =>
          fmp_take_reclaimable ctx fn live p st.frs_vetoed
            (REVERSE st.frs_marks)
End

Definition fmp_collect_restores_def:
  fmp_collect_restores ctx fn live marks cfg [] = [] /\
  fmp_collect_restores ctx fn live marks cfg (bb::bbs) =
    fmp_collect_block_restores ctx fn live marks cfg bb ++
    fmp_collect_restores ctx fn live marks cfg bbs
End

Definition analyze_fmp_reclaims_def:
  analyze_fmp_reclaims (ctx:venom_context) (name:string) :
      fmp_reclaim_plan option =
    case analyze_fmp_context ctx of
      NONE => NONE
    | SOME infos =>
        case lookup_function name ctx.ctx_functions of
          NONE => NONE
        | SOME fn =>
            if fn.fn_fmp_signature <> NONE \/
               ~wf_function fn \/ ~fn_inst_wf fn then NONE
            else
              case fmp_mark_analyze fn of
                NONE => NONE
              | SOME marks =>
                  let live = liveness_analyze fn in
                  let cfg = cfg_analyze fn in
                  let restores =
                    fmp_collect_restores ctx fn live marks cfg fn.fn_blocks in
                  SOME <| frp_function := fn.fn_name;
                          frp_restores := restores |>
End

Definition fmp_reclaim_plan_valid_def:
  fmp_reclaim_plan_valid ctx name plan <=>
    plan.frp_function = name /\
    ?fn live.
      lookup_function name ctx.ctx_functions = SOME fn /\
      live = liveness_analyze fn /\
      !p base. MEM (p,base) plan.frp_restores ==>
        fmp_restore_target_ok ctx fn live p base
End

val _ = export_theory();
