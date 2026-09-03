(* Boundary lemmas for context-wide code-generation memory relations. *)

Theory contextCodegenRelProps
Ancestors
  contextCodegenRel planSpillBounds codegenRel

Theorem context_spill_byte_of_region:
  MEM r cp.cp_regions /\
  r.sr_spill_base <= i /\ i < r.sr_spill_end ==>
  context_spill_byte cp i
Proof
  simp[context_spill_byte_def] >> metis_tac[]
QED

Theorem context_spill_byte_cases:
  context_spill_byte cp i ==>
  ?r. MEM r cp.cp_regions /\
      r.sr_spill_base <= i /\ i < r.sr_spill_end
Proof
  simp[context_spill_byte_def]
QED

Theorem generated_local_spill_byte_in_context:
  generate_context_plan ctx = SOME cp /\
  MEM r cp.cp_regions /\
  region_spill_access r off /\
  off <= i /\ i < off + 32 ==>
  context_spill_byte cp i
Proof
  rpt strip_tac >>
  `r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end` by
    (drule generate_context_plan_access_bounded >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  simp[context_spill_byte_def] >>
  qexists `r` >> simp[] >> decide_tac
QED

Theorem context_spill_step_safe_local:
  MEM r cp.cp_regions /\ context_spill_step_safe cp vs vs' ==>
  step_mem_safe
    <|sa_spill_base := r.sr_spill_base;
      sa_next_offset := r.sr_spill_end;
      sa_free_slots := slots|> vs vs'
Proof
  rw[context_spill_step_safe_def, step_mem_safe_def] >>
  first_x_assum irule >>
  simp[context_spill_byte_def] >>
  qexists `r` >> simp[]
QED

Theorem local_memory_rel_context:
  MEM r cp.cp_regions /\
  memory_rel
    <|sa_spill_base := r.sr_spill_base;
      sa_next_offset := r.sr_spill_end;
      sa_free_slots := slots|> vm am ==>
  context_memory_rel cp vm am
Proof
  rw[memory_rel_def, context_memory_rel_def] >>
  first_x_assum irule >>
  CCONTR_TAC >> gvs[] >>
  qpat_x_assum `~context_spill_byte cp i` mp_tac >>
  simp[context_spill_byte_def] >>
  qexists `r` >> simp[]
QED

(* The ambient relation has no active-function parameter, so changing from
   any planned caller region to any planned callee region preserves it. *)
Theorem context_memory_rel_active_function_change:
  MEM caller_region cp.cp_regions /\
  MEM callee_region cp.cp_regions /\
  context_memory_rel cp vm am ==>
  context_memory_rel cp vm am
Proof
  simp[]
QED

val _ = export_theory();
