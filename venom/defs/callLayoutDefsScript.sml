(*
 * Canonical physical call-parameter layout.
 *
 * This theory is deliberately below venomWf and static-layout theories.
 *)

Theory callLayoutDefs
Ancestors
  venomInst

Definition fn_entry_insts_def:
  fn_entry_insts fn =
    case entry_block fn of
      NONE => []
    | SOME bb => bb.bb_instructions
End

Definition fn_hidden_fmp_param_def:
  fn_hidden_fmp_param fn =
    FIND (\inst. inst.inst_opcode = FMP_PARAM) (fn_entry_insts fn)
End

Definition fn_retpc_param_def:
  fn_retpc_param fn =
    FIND (\inst. inst.inst_opcode = RETPC_PARAM) (fn_entry_insts fn)
End

Definition fn_user_param_insts_def:
  fn_user_param_insts fn =
    FILTER (\inst. inst.inst_opcode = PARAM) (fn_entry_insts fn)
End

(* The literal operand is the physical position in the complete parameter
 * prefix.  Every physical parameter also defines exactly one SSA value. *)
Definition param_inst_at_def:
  param_inst_at k inst <=>
    is_param_opcode inst.inst_opcode /\
    inst.inst_operands = [Lit (n2w k)] /\
    LENGTH inst.inst_outputs = 1
End

Definition erase_param_index_def:
  erase_param_index inst =
    if is_param_opcode inst.inst_opcode then
      inst with inst_operands := []
    else inst
End
Definition param_insts_from_def:
  param_insts_from k [] = T /\
  param_insts_from k (inst::insts) =
    (param_inst_at k inst /\ param_insts_from (SUC k) insts)
End

Definition no_param_insts_def:
  no_param_insts insts <=>
    EVERY (\inst. ~is_param_opcode inst.inst_opcode) insts
End

Definition canonical_after_fmp_def:
  canonical_after_fmp k [] = T /\
  canonical_after_fmp k (inst::insts) =
    if inst.inst_opcode = RETPC_PARAM then
      param_inst_at k inst /\ no_param_insts insts
    else
      no_param_insts (inst::insts)
End

Definition canonical_entry_params_from_def:
  canonical_entry_params_from k [] = T /\
  canonical_entry_params_from k (inst::insts) =
    if inst.inst_opcode = PARAM then
      param_inst_at k inst /\
      canonical_entry_params_from (SUC k) insts
    else if inst.inst_opcode = FMP_PARAM then
      param_inst_at k inst /\ canonical_after_fmp (SUC k) insts
    else if inst.inst_opcode = RETPC_PARAM then
      param_inst_at k inst /\ no_param_insts insts
    else
      no_param_insts (inst::insts)
End

Definition canonical_param_prefix_def:
  canonical_param_prefix fn <=>
    case fn.fn_blocks of
      [] => F
    | entry::rest =>
        canonical_entry_params_from 0 entry.bb_instructions /\
        EVERY (\bb. no_param_insts bb.bb_instructions) rest
End
val _ = export_theory();
