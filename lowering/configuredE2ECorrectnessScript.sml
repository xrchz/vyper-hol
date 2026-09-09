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

(* Prague O1 is obtained solely by instantiating the generic end-to-end
   correctness theorem; all semantic obligations remain explicit. *)
Theorem e2e_vyper_to_evm_O1:
  !tops finalizer rpolicy unit out prog deploy_bc runtime_bc
   cp name i r fn off Inv cenv am tx tenv ret ctxt rb rest es vs R_ok R_term.
    resolve_o1_policy (o1_policy prague_capabilities) = SOME rpolicy /\
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    (\rpolicy unit.
       run_venom_pipeline (K T) (K T) (K T)
         rpolicy o1_pipeline_spec unit) rpolicy unit = SOME out /\
    out.po_final_assembly = rpolicy.rpol_final_assembly /\
    finalize_codegen finalizer rpolicy out.po_unit = SOME runtime_bc /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    runtime_bc = assemble prog /\
    compile_vyper_with
      (\rpolicy unit.
         run_venom_pipeline (K T) (K T) (K T)
           rpolicy o1_pipeline_spec unit)
      finalizer (o1_policy prague_capabilities) tops =
        SOME (deploy_bc, runtime_bc) /\
    source_deployment_rel tops am tx cenv /\
    source_unit_execution_correct tenv cenv am tx ret unit vs /\
    generate_context_plan out.po_unit.cu_context = SOME cp /\
    out.po_unit.cu_context.ctx_entry = SOME name /\
    lookup_function name out.po_unit.cu_context.ctx_functions = SOME fn /\
    i < LENGTH out.po_unit.cu_context.ctx_functions /\
    EL i out.po_unit.cu_context.ctx_functions = fn /\
    EL i cp.cp_regions = r /\
    ops_contain_at off
      (execute_plan cp.cp_initial_fmp (context_plan_ops cp))
      (execute_plan cp.cp_initial_fmp r.sr_plan) /\
    contextCodegenRel$codegen_context_obligations
      Inv out.po_unit.cu_context cp /\
    contextCodegenRel$codegen_reachability_package
      Inv out.po_unit.cu_context vs /\
    initial_codegen_state_rel cp vs /\
    codegenCorrectness$initial_ctx_rel cp prog off
      out.po_unit.cu_context vs es /\
    asm_pc_to_offset prog off = 0 /\
    es.contexts = (ctxt, rb) :: rest /\
    call_state_rel tops runtime_bc am tx tenv ctxt rb es.txParams /\
    valid_vyper_call am tx tenv ctxt.msgParams.data ret /\
    cenv.ce_type_env = tenv /\
    cenv.ce_event_info = compiled_event_info tops /\
    checked_unit_transform_correct
      (\rpolicy unit.
         run_venom_pipeline (K T) (K T) (K T)
           rpolicy o1_pipeline_spec unit)
      rpolicy R_ok R_term unit vs /\
    (!s1 s2. R_ok s1 s2 ==> observable_equiv s1 s2) /\
    (!s1 s2. R_term s1 s2 ==> observable_equiv s1 s2) /\
    finalizer_correct rpolicy finalizer
    ==>
    ?gas_needed.
      ctxt.msgParams.gasLimit >= gas_needed ==>
      vyper_evm_correspondence tenv (compiled_event_info tops) ret am tx es
Proof
  rpt strip_tac >>
  drule_all e2eCorrectnessTheory.e2e_vyper_to_evm >>
  simp[]
QED
