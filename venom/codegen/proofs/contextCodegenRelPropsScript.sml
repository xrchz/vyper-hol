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

Theorem generated_spill_access_context_boundary:
  generate_context_plan ctx = SOME cp /\
  MEM r cp.cp_regions /\
  region_spill_access r off /\
  off <= i /\ i < off + 32 ==>
  (r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end) /\
  context_spill_byte cp i
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac
  >- (drule generate_context_plan_access_bounded >>
      simp[listTheory.EVERY_MEM] >> metis_tac[])
  >> metis_tac[generated_local_spill_byte_in_context]
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


(* A nonempty direct footprint can only come from an opcode whose source
   semantics performs byte-memory writes.  INVOKE is deliberately absent:
   it is an aggregate nested execution covered by the context invariant. *)
Theorem source_memory_write_ranges_opcode_coverage:
  source_memory_write_ranges inst vs <> [] ==>
  inst.inst_opcode = MSTORE \/ inst.inst_opcode = MSTORE8 \/
  inst.inst_opcode = ISTORE \/ inst.inst_opcode = MCOPY \/
  inst.inst_opcode = CALLDATACOPY \/
  inst.inst_opcode = RETURNDATACOPY \/
  inst.inst_opcode = DLOADBYTES \/ inst.inst_opcode = CODECOPY \/
  inst.inst_opcode = EXTCODECOPY \/ inst.inst_opcode = CALL \/
  inst.inst_opcode = STATICCALL \/ inst.inst_opcode = DELEGATECALL \/
  inst.inst_opcode = DRET
Proof
  Cases_on `inst.inst_opcode` >>
  simp[source_memory_write_ranges_def]
QED

Theorem source_memory_write_ranges_INVOKE[simp]:
  source_memory_write_ranges (inst with inst_opcode := INVOKE) vs = []
Proof
  simp[source_memory_write_ranges_def]
QED

Theorem INVOKE_not_pre_codegen_opcode:
  ~is_pre_codegen_opcode INVOKE
Proof
  simp[stackPlanGenTheory.is_pre_codegen_opcode_def,
       stackPlanGenTheory.is_unlowered_internal_call_opcode_def,
       stackPlanGenTheory.is_unlowered_fmp_opcode_def,
       venomInstTheory.is_raw_fmp_opcode_def]
QED

Theorem source_memory_writes_disjoint_range_excludes_spill:
  source_memory_writes_disjoint alloc inst vs /\
  MEM (off,len) (source_memory_write_ranges inst vs) /\
  alloc.sa_spill_base <= i /\ i < alloc.sa_next_offset ==>
  ~(off <= i /\ i < off + len)
Proof
  rw[source_memory_writes_disjoint_def, listTheory.EVERY_MEM] >>
  first_x_assum drule >> disch_tac >> gvs[] >> decide_tac
QED
(* Generic preservation boundary for the live spill relation.  Writer-specific
   proofs need only show that operand meanings and each live 32-byte spill
   window are unchanged; they need not unfold plan_spill_rel. *)
Theorem plan_spill_rel_preserved:
  plan_spill_rel lo vs spilled am /\
  (!op. op IN FDOM spilled ==>
        operand_val vs' lo op = operand_val vs lo op) /\
  (!op off. FLOOKUP spilled op = SOME off ==>
     word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off am')) =
     word_of_bytes T (0w:bytes32) (TAKE 32 (DROP off am))) ==>
  plan_spill_rel lo vs' spilled am'
Proof
  rw[plan_spill_rel_def] >>
  qpat_x_assum `!op off. FLOOKUP spilled op = SOME off ==> _`
    (qspecl_then [`op`,`off`] mp_tac) >>
  simp[] >> strip_tac >>
  `op IN FDOM spilled` by fs[finite_mapTheory.FLOOKUP_DEF] >>
  qpat_assum `!op. op IN FDOM spilled ==> _`
    (qspec_then `op` assume_tac) >>
  metis_tac[]
QED
(* Generic bytewise transfer for memory_rel.  A matched source/assembly write
   may change bytes in its range; all other bytes are inherited from the old
   relation.  Concrete writer lemmas discharge these three small premises. *)
Theorem memory_rel_preserved_matched_write:
  memory_rel alloc vm am /\
  (!i. ~(off <= i /\ i < off + len) ==>
       read_byte i vm' = read_byte i vm) /\
  (!i. ~(off <= i /\ i < off + len) ==>
       read_byte i am' = read_byte i am) /\
  (!i. off <= i /\ i < off + len ==>
       read_byte i vm' = read_byte i am') ==>
  memory_rel alloc vm' am'
Proof
  rw[memory_rel_def] >>
  Cases_on `off <= i /\ i < off + len`
  >- metis_tac[]
  >> metis_tac[]
QED

Theorem context_source_memory_writes_disjoint_local:
  MEM r cp.cp_regions /\
  context_source_memory_writes_disjoint cp inst vs ==>
  source_memory_writes_disjoint
    <|sa_spill_base := r.sr_spill_base;
      sa_next_offset := r.sr_spill_end;
      sa_free_slots := slots|> inst vs
Proof
  rw[context_source_memory_writes_disjoint_def,
     source_memory_writes_disjoint_def, listTheory.EVERY_MEM] >>
  first_x_assum drule >>
  PairCases_on `e` >> simp[] >> metis_tac[]
QED

val _ = export_theory();
