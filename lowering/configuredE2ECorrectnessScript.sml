(*
 * Configured end-to-end correctness interfaces.
 *
 * This theory keeps the generic compiler and semantic obligations explicit,
 * while exposing the two successful phases of compile_vyper_with and the
 * Prague O1 specialization of the generic end-to-end theorem.
 *)

Theory configuredE2ECorrectness
Ancestors
  e2eCorrectness

(* A successful generic compilation records all intermediate values from both
   the runtime and deployment phases. *)
Theorem compile_vyper_with_success_phases:
  compile_vyper_with pipeline finalizer policy tops =
    SOME (deploy_bc,runtime_bc) ==>
  ?rpolicy runtime_unit runtime_out deploy_unit deploy_out.
    resolve_o1_policy policy = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
    pipeline rpolicy runtime_unit = SOME runtime_out /\
    runtime_out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy runtime_out.po_unit = SOME runtime_bc /\
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME deploy_unit /\
    pipeline rpolicy deploy_unit = SOME deploy_out /\
    deploy_out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy deploy_out.po_unit = SOME deploy_bc
Proof
  simp[compileVyperTheory.compile_vyper_with_def,
       compileVyperTheory.checked_unit_pipeline_def] >>
  rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  goal_assum $ drule_at Any
QED

(* Phase-local conditional results compose for the exact bytecode pair returned
   by compile_vyper_with. *)
Theorem compile_vyper_with_deploy_runtime_compose:
  compile_vyper_with pipeline finalizer policy tops =
    SOME (deploy_bc,runtime_bc) /\
  (!rpolicy runtime_unit runtime_out.
     resolve_o1_policy policy = SOME rpolicy /\
     lower_vyper_runtime_unit tops rpolicy = SOME runtime_unit /\
     pipeline rpolicy runtime_unit = SOME runtime_out /\
     runtime_out.po_final_assembly = rpolicy.rpol_final_assembly /\
     finalize_codegen finalizer rpolicy runtime_out.po_unit = SOME runtime_bc
     ==> runtime_ok runtime_bc) /\
  (!rpolicy deploy_unit deploy_out.
     resolve_o1_policy policy = SOME rpolicy /\
     lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME deploy_unit /\
     pipeline rpolicy deploy_unit = SOME deploy_out /\
     deploy_out.po_final_assembly = rpolicy.rpol_final_assembly /\
     finalize_codegen finalizer rpolicy deploy_out.po_unit = SOME deploy_bc
     ==> deploy_ok deploy_bc runtime_bc)
  ==> runtime_ok runtime_bc /\ deploy_ok deploy_bc runtime_bc
Proof
  strip_tac >>
  drule compile_vyper_with_success_phases >>
  strip_tac >>
  conj_tac
  >- (first_x_assum irule >> simp[])
  >> first_x_assum irule >> simp[]
QED
