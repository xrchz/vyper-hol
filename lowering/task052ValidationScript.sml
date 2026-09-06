(* Focused shape and projection validation for TASK 052 relations. *)

Theory task052Validation
Ancestors
  e2eDefs
Libs
  BasicProvers

Theorem checked_unit_transform_correct_exists:
  checked_unit_transform_correct pipeline rpolicy R_ok R_term unit s ==>
  ?out. pipeline rpolicy unit = SOME out
Proof
  simp[checked_unit_transform_correct_def] >> metis_tac[]
QED

Theorem checked_unit_transform_correct_success:
  checked_unit_transform_correct pipeline rpolicy R_ok R_term unit s /\
  pipeline rpolicy unit = SOME out ==>
  ctx_transform_correct R_ok R_term
    unit.cu_context out.po_unit.cu_context s
Proof
  rw[checked_unit_transform_correct_def] >> gvs[]
QED

Theorem source_deployment_rel_target:
  source_deployment_rel tops am tx cenv ==>
  ?mods. ALOOKUP am.sources tx.target = SOME mods /\
         ALOOKUP mods cenv.ce_module = SOME tops
Proof
  simp[source_deployment_rel_def]
QED

Theorem finalizer_correct_target_safe:
  finalizer_correct rpolicy finalizer /\
  finalizer rpolicy asm = SOME asm' ==>
  assembly_target_safe rpolicy.rpol_target asm'
Proof
  rw[finalizer_correct_def] >> first_x_assum drule >> simp[]
QED

Theorem finalizer_correct_preserve_identity:
  finalizer_correct rpolicy finalizer /\
  rpolicy.rpol_final_assembly = FAP_Preserve /\
  finalizer rpolicy asm = SOME asm' ==>
  asm' = asm
Proof
  rw[finalizer_correct_def] >> first_x_assum drule >> simp[]
QED

Theorem initial_codegen_state_rel_fmp:
  initial_codegen_state_rel cp vs ==>
  vs.vs_fmp = n2w cp.cp_initial_fmp
Proof
  simp[initial_codegen_state_rel_def]
QED

Theorem initial_codegen_state_rel_call_entry_fmp:
  initial_codegen_state_rel cp vs ==>
  vs.vs_call_entry_fmp = n2w cp.cp_initial_fmp
Proof
  simp[initial_codegen_state_rel_def]
QED

Theorem initial_codegen_state_rel_initial_fmp:
  initial_codegen_state_rel cp vs ==>
  vs.vs_initial_fmp = n2w cp.cp_initial_fmp
Proof
  simp[initial_codegen_state_rel_def]
QED

Theorem initial_codegen_state_rel_return_pc_token:
  initial_codegen_state_rel cp vs ==>
  vs.vs_return_pc_token = 0w
Proof
  simp[initial_codegen_state_rel_def]
QED

Theorem initial_evm_rel_initial_codegen_state:
  initial_evm_rel cp bytecode vs es ==>
  initial_codegen_state_rel cp vs
Proof
  simp[initial_evm_rel_def]
QED

Theorem initial_evm_rel_fmp:
  initial_evm_rel cp bytecode vs es ==>
  vs.vs_fmp = n2w cp.cp_initial_fmp
Proof
  simp[initial_evm_rel_def, initial_codegen_state_rel_def]
QED

Theorem initial_evm_rel_call_entry_fmp:
  initial_evm_rel cp bytecode vs es ==>
  vs.vs_call_entry_fmp = n2w cp.cp_initial_fmp
Proof
  simp[initial_evm_rel_def, initial_codegen_state_rel_def]
QED

Theorem initial_evm_rel_initial_fmp:
  initial_evm_rel cp bytecode vs es ==>
  vs.vs_initial_fmp = n2w cp.cp_initial_fmp
Proof
  simp[initial_evm_rel_def, initial_codegen_state_rel_def]
QED

Theorem initial_evm_rel_return_pc_token:
  initial_evm_rel cp bytecode vs es ==>
  vs.vs_return_pc_token = 0w
Proof
  simp[initial_evm_rel_def, initial_codegen_state_rel_def]
QED

val _ = export_theory ();
