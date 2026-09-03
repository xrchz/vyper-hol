(* Focused logical and executable checks for TASK 047. *)

Theory contextCodegenRelValidation
Ancestors
  contextCodegenRelProps contextCodegenRel contextPlanValidation fcgDefs codegenRel
Libs
  BasicProvers

Theorem context_rel_dimindex_8[local,simp]:
  dimindex (:8) = 8
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Definition context_rel_caller_region_def:
  context_rel_caller_region =
    <|sr_fn_name := "caller"; sr_spill_base := 0; sr_spill_end := 1;
      sr_plan := []|>
End

Definition context_rel_callee_region_def:
  context_rel_callee_region =
    <|sr_fn_name := "callee"; sr_spill_base := 1; sr_spill_end := 2;
      sr_plan := []|>
End

Definition context_rel_two_fn_cp_def:
  context_rel_two_fn_cp =
    <|cp_regions := [context_rel_caller_region; context_rel_callee_region];
      cp_max_static_eom := 0; cp_peak_spill_end := 2;
      cp_initial_fmp := 32|>
End

Definition context_rel_source_mem_def:
  context_rel_source_mem = ([0w; 0w] : byte list)
End

Definition context_rel_assembly_mem_def:
  context_rel_assembly_mem = ([1w; 2w] : byte list)
End

Theorem context_rel_two_function_union_eval:
  context_spill_byte context_rel_two_fn_cp 0 /\
  context_spill_byte context_rel_two_fn_cp 1 /\
  ~context_spill_byte context_rel_two_fn_cp 2
Proof
  conj_tac >-
    (simp[context_spill_byte_def, context_rel_two_fn_cp_def] >>
     qexists `context_rel_caller_region` >>
     simp[context_rel_caller_region_def]) >>
  conj_tac >-
    (simp[context_spill_byte_def, context_rel_two_fn_cp_def] >>
     qexists `context_rel_callee_region` >>
     simp[context_rel_callee_region_def]) >>
  strip_tac >> drule context_spill_byte_cases >>
  simp[context_rel_two_fn_cp_def] >> strip_tac >>
  CCONTR_TAC >>
  gvs[context_rel_caller_region_def, context_rel_callee_region_def]
QED

(* Both caller and callee bytes may differ even while the callee region is the
   selected local region: the ambient relation masks their union. *)
Theorem context_rel_caller_live_while_callee_active:
  MEM context_rel_callee_region context_rel_two_fn_cp.cp_regions /\
  context_memory_rel context_rel_two_fn_cp
    context_rel_source_mem context_rel_assembly_mem /\
  read_byte 0 context_rel_source_mem <>
    read_byte 0 context_rel_assembly_mem /\
  read_byte 1 context_rel_source_mem <>
    read_byte 1 context_rel_assembly_mem
Proof
  conj_tac >-
    simp[context_rel_two_fn_cp_def] >>
  conj_tac >-
    (rw[context_memory_rel_def] >>
     Cases_on `i < 2` >-
       (`i = 0 \/ i = 1` by decide_tac >>
        gvs[context_rel_two_function_union_eval]) >>
     simp[read_byte_def, context_rel_source_mem_def,
          context_rel_assembly_mem_def]) >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem context_rel_agrees_immediately_outside_union:
  read_byte 2 context_rel_source_mem =
    read_byte 2 context_rel_assembly_mem
Proof
  EVAL_TAC
QED

(* A callee-local relation does not mask the suspended caller's byte. *)
Theorem context_relation_not_callee_local_relation:
  context_memory_rel context_rel_two_fn_cp
    context_rel_source_mem context_rel_assembly_mem /\
  ~memory_rel
    <|sa_spill_base := context_rel_callee_region.sr_spill_base;
      sa_next_offset := context_rel_callee_region.sr_spill_end;
      sa_free_slots := []|>
    context_rel_source_mem context_rel_assembly_mem
Proof
  conj_tac >-
    metis_tac[context_rel_caller_live_while_callee_active] >>
  strip_tac >>
  fs[memory_rel_def] >>
  first_x_assum (qspec_then `0` mp_tac) >>
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem codegen_reachability_false_invariant:
  !ctx initial_vs.
    ~codegen_reachability_package
      (\ctx fn inst vs. F) ctx initial_vs
Proof
  simp[codegen_reachability_package_def]
QED

Definition context_rel_invoke_b_def:
  context_rel_invoke_b = mk_inst 0 INVOKE [Label "b"; Lit 0w] []
End

Definition context_rel_invoke_a_def:
  context_rel_invoke_a = mk_inst 1 INVOKE [Label "a"; Lit 0w] []
End

Definition context_rel_stop_def:
  context_rel_stop = mk_inst 2 STOP [] []
End

Definition context_rel_a_calls_b_def:
  context_rel_a_calls_b = mk_raw_function "a"
    [<|bb_label := "entry";
       bb_instructions := [context_rel_invoke_b; context_rel_stop]|>]
End

Definition context_rel_b_leaf_def:
  context_rel_b_leaf = mk_raw_function "b"
    [<|bb_label := "entry"; bb_instructions := [context_rel_stop]|>]
End

Definition context_rel_acyclic_ctx_def:
  context_rel_acyclic_ctx =
    mk_venom_context [context_rel_a_calls_b; context_rel_b_leaf] (SOME "a")
End

Definition context_rel_a_calls_a_def:
  context_rel_a_calls_a = mk_raw_function "a"
    [<|bb_label := "entry";
       bb_instructions := [context_rel_invoke_a; context_rel_stop]|>]
End

Definition context_rel_recursive_ctx_def:
  context_rel_recursive_ctx =
    mk_venom_context [context_rel_a_calls_a] (SOME "a")
End

Theorem reachable_call_graph_acyclic_examples:
  reachable_call_graph_acyclic context_rel_acyclic_ctx /\
  ~reachable_call_graph_acyclic context_rel_recursive_ctx
Proof
  EVAL_TAC
QED

val _ = export_theory();
