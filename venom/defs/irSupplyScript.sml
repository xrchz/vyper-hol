(*
 * Unit-wide fresh-name and instruction-ID supply.
 *)

Theory irSupply
Ancestors
  venomCompilerWf
Libs
  listTheory

(* Collectors are deliberately list-valued: duplicates are harmless and the
   resulting definitions remain directly executable. *)
Definition operand_ir_labels_def:
  operand_ir_labels [] = [] /\
  operand_ir_labels (Label l :: ops) = l :: operand_ir_labels ops /\
  operand_ir_labels (_ :: ops) = operand_ir_labels ops
End

Definition inst_ir_vars_def:
  inst_ir_vars inst = inst.inst_outputs ++ inst_uses inst
End

Definition inst_ir_labels_def:
  inst_ir_labels inst = operand_ir_labels inst.inst_operands
End

Definition block_ir_inst_ids_def:
  block_ir_inst_ids bb = MAP (\inst. inst.inst_id) bb.bb_instructions
End

Definition block_ir_vars_def:
  block_ir_vars bb = FLAT (MAP inst_ir_vars bb.bb_instructions)
End

Definition block_ir_labels_def:
  block_ir_labels bb = bb.bb_label :: FLAT (MAP inst_ir_labels bb.bb_instructions)
End

Definition fn_ir_inst_ids_def:
  fn_ir_inst_ids fn = FLAT (MAP block_ir_inst_ids fn.fn_blocks)
End

Definition fn_ir_vars_def:
  fn_ir_vars fn = FLAT (MAP block_ir_vars fn.fn_blocks)
End

Definition fn_ir_labels_def:
  fn_ir_labels fn = fn.fn_name :: FLAT (MAP block_ir_labels fn.fn_blocks)
End

Definition data_item_ir_labels_def:
  data_item_ir_labels (DataLabel l) = [l] /\
  data_item_ir_labels (DataBytes bytes) = []
End

Definition data_section_ir_labels_def:
  data_section_ir_labels section =
    section.ds_label :: FLAT (MAP data_item_ir_labels section.ds_items)
End

Definition unit_ir_inst_ids_def:
  unit_ir_inst_ids unit =
    FLAT (MAP fn_ir_inst_ids unit.cu_context.ctx_functions)
End

Definition unit_ir_vars_def:
  unit_ir_vars unit =
    FLAT (MAP fn_ir_vars unit.cu_context.ctx_functions)
End

Definition unit_ir_labels_def:
  unit_ir_labels unit =
    (case unit.cu_context.ctx_entry of NONE => [] | SOME l => [l]) ++
    FLAT (MAP fn_ir_labels unit.cu_context.ctx_functions) ++
    FLAT (MAP data_section_ir_labels unit.cu_data_segment)
End

Theorem MEM_operand_ir_labels:
  MEM l (operand_ir_labels ops) <=> MEM (Label l) ops
Proof
  Induct_on `ops` >> simp[operand_ir_labels_def] >>
  Cases_on `h` >> simp[operand_ir_labels_def]
QED

Theorem MEM_unit_ir_inst_ids:
  MEM id (unit_ir_inst_ids unit) <=>
  ?fn bb inst.
    MEM fn unit.cu_context.ctx_functions /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    id = inst.inst_id
Proof
  simp[unit_ir_inst_ids_def, fn_ir_inst_ids_def, block_ir_inst_ids_def,
       MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem MEM_unit_ir_vars:
  MEM v (unit_ir_vars unit) <=>
  ?fn bb inst.
    MEM fn unit.cu_context.ctx_functions /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    (MEM v inst.inst_outputs \/ MEM v (inst_uses inst))
Proof
  simp[unit_ir_vars_def, fn_ir_vars_def, block_ir_vars_def,
       inst_ir_vars_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_entry:
  unit.cu_context.ctx_entry = SOME l ==>
  MEM l (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def]
QED

Theorem unit_ir_labels_function:
  MEM fn unit.cu_context.ctx_functions ==>
  MEM fn.fn_name (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, fn_ir_labels_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_block:
  MEM fn unit.cu_context.ctx_functions /\ MEM bb fn.fn_blocks ==>
  MEM bb.bb_label (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, fn_ir_labels_def, block_ir_labels_def,
       MEM_FLAT, MEM_MAP, PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_operand:
  MEM fn unit.cu_context.ctx_functions /\
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM (Label l) inst.inst_operands ==>
  MEM l (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, fn_ir_labels_def, block_ir_labels_def,
       inst_ir_labels_def, MEM_operand_ir_labels, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_section:
  MEM section unit.cu_data_segment ==>
  MEM section.ds_label (unit_ir_labels unit)
Proof
  simp[unit_ir_labels_def, data_section_ir_labels_def, MEM_FLAT, MEM_MAP,
       PULL_EXISTS] >> metis_tac[]
QED

Theorem unit_ir_labels_data_item:
  MEM section unit.cu_data_segment /\ MEM (DataLabel l) section.ds_items ==>
  MEM l (unit_ir_labels unit)
Proof
  strip_tac >>
  simp[unit_ir_labels_def, data_section_ir_labels_def,
       data_item_ir_labels_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  disj2_tac >> qexists `section` >> simp[] >>
  disj2_tac >> qexists `DataLabel l` >> simp[data_item_ir_labels_def]
QED

val _ = export_theory ();
