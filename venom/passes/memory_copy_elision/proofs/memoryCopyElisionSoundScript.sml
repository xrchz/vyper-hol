(*
 * Memory Copy Elision — Soundness Predicate and Per-Instruction Proofs
 *
 * Defines the soundness predicate for copy fact lattice values and
 * proves that copy_elision_inst satisfies analysis_inst_simulates.
 *
 * The soundness predicate cf_sound says: for each entry in the copy
 * fact lattice, the destination memory region contains bytes that match
 * what you'd read from the source region (for the recorded size).
 * Under this invariant, NOP'ing a redundant copy or forwarding through
 * an intermediate buffer preserves state equivalence.
 *
 * TOP-LEVEL EXPORTS:
 *   cf_sound_opt_def — soundness predicate
 *   cf_sound_opt_fempty — FEMPTY is trivially sound
 *   cf_sound_opt_state_equiv — soundness preserved by state_equiv {}
 *   cei_simulates_inv — analysis_inst_simulates for copy_elision_inst
 *   copy_fact_transfer_sound_thm — transfer_sound for copy_fact_transfer
 *)

Theory memoryCopyElisionSound
Ancestors
  memoryCopyElisionDefs analysisSimDefs analysisSimProps
  passSimulationDefs passSimulationProps passSharedDefs passSharedProps
  venomWf venomInst venomInstProps venomState venomExecSemantics
  venomEffects venomMemDefs venomMemProps venomMemProofs
  stateEquiv stateEquivProps execEquivParamDefs execEquivParamProps
  dfgAnalysisProps dfgDefs dfAnalyzeDefs
  basePtrDefs memLocDefs memAliasDefs memAliasProofs
  finite_map list pred_set
Libs
  pairLib fcpLib

(* ===== Soundness predicate ===== *)

(* Select the source data region based on copy opcode.
   MCOPY reads from memory; other copy opcodes read from their
   respective address spaces (calldata, data section, code, returndata). *)
Definition cf_source_data_def:
  cf_source_data MCOPY s = s.vs_memory /\
  cf_source_data CALLDATACOPY s = s.vs_call_ctx.cc_calldata /\
  cf_source_data DLOADBYTES s = s.vs_data_section /\
  cf_source_data CODECOPY s = s.vs_code /\
  cf_source_data RETURNDATACOPY s = s.vs_returndata /\
  cf_source_data _ s = []  (* non-copy opcodes: empty, vacuously safe *)
End

(* A copy fact entry is sound when the destination memory region
   already contains the bytes that would be read from the source.
   This is the runtime invariant that justifies eliding redundant copies
   and forwarding through intermediate buffers.

   Concretely, for a lattice entry (ml, cf) where:
   - ml is a destination MemoryLocation (with known offset and size)
   - cf.cf_source is the source operand
   - cf.cf_size is the size operand
   - cf.cf_opcode determines the source address space
   The entry is sound when:
   - eval_operand cf.cf_source s = SOME src_val
   - ml.ml_offset = SOME dst_off, ml.ml_size = SOME sz_num
   - The bytes at dst_off[0..sz_num-1] in memory equal the bytes
     at src_val[0..sz_num-1] in the source data for cf.cf_opcode

   The source data is selected by cf_source_data:
   - MCOPY: s.vs_memory
   - CALLDATACOPY: s.vs_call_ctx.cc_calldata
   - DLOADBYTES: s.vs_data_section
   - CODECOPY: s.vs_code
   - RETURNDATACOPY: s.vs_returndata
*)
Definition cf_entry_sound_def:
  cf_entry_sound (bp : bp_result) (dfg : dfg_analysis) (ml : mem_loc)
                 (cf : copy_fact) (s : venom_state) <=>
    (* Use memloc_runtime_region to resolve alloca-relative offsets
       to absolute addresses.  For ml_alloca = NONE this gives
       (ml_offset, ml_size); for ml_alloca = SOME alloc it gives
       (alloca_base + ml_offset, ml_size).  NONE when either
       component is unknown or alloca not yet executed → vacuously T. *)
    case memloc_runtime_region ml s of
      SOME (dst_off, sz_num) =>
        (* The source operand evaluates *)
        ?src_val.
          eval_operand (normalize_operand dfg [] cf.cf_source) s = SOME src_val /\
          let mem = s.vs_memory in
          let src_data = cf_source_data cf.cf_opcode s in
          (* Destination is within memory (no expansion needed) *)
          dst_off + sz_num <= LENGTH mem /\
          (* RETURNDATACOPY aborts on out-of-bounds access (EIP-211),
             so the forwarded step must also be in-bounds to succeed.
             Other copy opcodes (MCOPY, CALLDATACOPY, etc.) pad with
             zeros so they always succeed regardless of source bounds. *)
          (cf.cf_opcode = RETURNDATACOPY ==>
           w2n src_val + sz_num <= LENGTH src_data) /\
          (* The destination region already has the right bytes
             from the source address space.  Source data is padded
             with zeros to handle out-of-bounds reads matching the
             EVM semantics for CALLDATACOPY/CODECOPY/DLOADBYTES/MCOPY. *)
          TAKE sz_num (DROP dst_off mem) =
          TAKE sz_num (DROP (w2n src_val) src_data ++ REPLICATE sz_num 0w)
    | NONE => T
End

(* For ml_alloca = NONE, memloc_runtime_region reduces to (ml_offset, ml_size).
   This lets existing proofs (which all handle alloca=NONE) use the old form. *)
Triviality cf_entry_sound_none_alloca[local]:
  !bp dfg ml cf s.
    ml.ml_alloca = NONE ==>
    (cf_entry_sound bp dfg ml cf s <=>
     case (ml.ml_offset, ml.ml_size) of
       (SOME dst_off, SOME sz_num) =>
         ?src_val.
           eval_operand (normalize_operand dfg [] cf.cf_source) s = SOME src_val /\
           let mem = s.vs_memory in
           let src_data = cf_source_data cf.cf_opcode s in
           dst_off + sz_num <= LENGTH mem /\
           (cf.cf_opcode = RETURNDATACOPY ==>
            w2n src_val + sz_num <= LENGTH src_data) /\
           TAKE sz_num (DROP dst_off mem) =
           TAKE sz_num (DROP (w2n src_val) src_data ++ REPLICATE sz_num 0w)
     | (SOME _, NONE) => T
     | (NONE, SOME _) => T
     | (NONE, NONE) => T)
Proof
  rw[cf_entry_sound_def, memloc_runtime_region_def] >>
  Cases_on `ml.ml_offset` >> Cases_on `ml.ml_size` >> simp[]
QED

(* Raw lattice soundness: all entries are sound *)
Definition cf_sound_def:
  cf_sound bp dfg (cfl : copy_fact_lattice_raw) s <=>
    !ml cf. FLOOKUP cfl ml = SOME cf ==>
            cf_entry_sound bp dfg ml cf s
End

(* Key well-formedness: ml_size is determined by cf_size.
   This holds by construction (keys = ce_memloc_from_ops bp dest cf_size)
   and is preserved by DRESTRICT (which never modifies entries).
   Separate from cf_sound because it's state-independent and not preserved
   by cf_entry_sound_equiv (operand_equiv doesn't preserve syntactic form). *)
Definition cf_key_size_ok_def:
  cf_key_size_ok bp ml cf <=>
    ml.ml_size = (ce_memloc_from_ops bp cf.cf_source cf.cf_size).ml_size
End

Definition cf_keys_ok_def:
  cf_keys_ok bp (cfl : copy_fact_lattice_raw) <=>
    !ml entry. FLOOKUP cfl ml = SOME entry ==>
            cf_key_size_ok bp ml entry /\ ml_is_fixed ml /\
            (entry.cf_opcode = MCOPY ==>
             ml_is_fixed (ce_memloc_from_ops bp entry.cf_source entry.cf_size))
End

(* cf_keys_ok is preserved by DRESTRICT *)
Triviality cf_keys_ok_drestrict[local]:
  !bp cfl S. cf_keys_ok bp cfl ==> cf_keys_ok bp (DRESTRICT cfl S)
Proof
  rw[cf_keys_ok_def] >> rpt strip_tac >> fs[FLOOKUP_DRESTRICT] >> res_tac
QED

(* cf_keys_ok holds for FEMPTY *)
Triviality cf_keys_ok_fempty[local]:
  !bp. cf_keys_ok bp FEMPTY
Proof
  simp[cf_keys_ok_def]
QED

(* cf_keys_ok preserved by FUPDATE when new entry has matching size
   and the key is fixed *)
Triviality cf_keys_ok_fupdate[local]:
  !bp cfl ml cf.
    cf_keys_ok bp cfl /\ cf_key_size_ok bp ml cf /\ ml_is_fixed ml /\
    (cf.cf_opcode = MCOPY ==>
     ml_is_fixed (ce_memloc_from_ops bp cf.cf_source cf.cf_size)) ==>
    cf_keys_ok bp (cfl |+ (ml, cf))
Proof
  rw[cf_keys_ok_def, cf_key_size_ok_def] >> rpt strip_tac >>
  fs[FLOOKUP_UPDATE] >> BasicProvers.every_case_tac >> gvs[] >>
  res_tac
QED

(* Option-wrapped soundness *)
Definition cf_sound_opt_def:
  cf_sound_opt bp dfg (cfl_opt : copy_fact_lattice) s <=>
    case cfl_opt of NONE => T | SOME cfl => cf_sound bp dfg cfl s
End

(* Option-wrapped key well-formedness *)
Definition cf_keys_ok_opt_def:
  cf_keys_ok_opt bp (cfl_opt : copy_fact_lattice) <=>
    case cfl_opt of NONE => T | SOME cfl => cf_keys_ok bp cfl
End

(* Unwrap cf_keys_ok_opt to cf_keys_ok on unwrap_copy_facts *)
Triviality cf_keys_ok_opt_unwrap[local]:
  !bp v. cf_keys_ok_opt bp v ==> cf_keys_ok bp (unwrap_copy_facts v)
Proof
  Cases_on `v` >> simp[cf_keys_ok_opt_def, unwrap_copy_facts_def, cf_keys_ok_fempty]
QED

(* Alloca-bounded entries: every alloca-backed key in the copy map has
   its access within the alloca bounds.  Needed for different-alloca
   disjointness via allocas_non_overlapping.  State-dependent because
   alloca sizes come from vs_allocas. *)
Definition cf_alloca_ok_def:
  cf_alloca_ok bp (cfl : copy_fact_lattice_raw) s <=>
    !ml cf. FLOOKUP cfl ml = SOME cf ==>
            memloc_within_alloca ml s /\
            (cf.cf_opcode = MCOPY ==>
             memloc_within_alloca (ce_memloc_from_ops bp cf.cf_source cf.cf_size) s)
End

Definition cf_alloca_ok_opt_def:
  cf_alloca_ok_opt bp (cfl_opt : copy_fact_lattice) s <=>
    case cfl_opt of NONE => T | SOME cfl => cf_alloca_ok bp cfl s
End

Triviality cf_alloca_ok_fempty[local]:
  !bp s. cf_alloca_ok bp FEMPTY s
Proof
  simp[cf_alloca_ok_def]
QED

(* Unwrap cf_alloca_ok_opt to cf_alloca_ok on unwrap_copy_facts *)
Triviality cf_alloca_ok_opt_unwrap[local]:
  !bp v s. cf_alloca_ok_opt bp v s ==> cf_alloca_ok bp (unwrap_copy_facts v) s
Proof
  Cases_on `v` >>
  simp[cf_alloca_ok_opt_def, unwrap_copy_facts_def, cf_alloca_ok_fempty]
QED

Triviality cf_alloca_ok_drestrict[local]:
  !bp cfl S s. cf_alloca_ok bp cfl s ==> cf_alloca_ok bp (DRESTRICT cfl S) s
Proof
  rw[cf_alloca_ok_def, FLOOKUP_DRESTRICT] >> rpt strip_tac >> res_tac
QED

Triviality cf_alloca_ok_fupdate[local]:
  !bp cfl ml cf s.
    cf_alloca_ok bp cfl s /\
    memloc_within_alloca ml s /\
    (cf.cf_opcode = MCOPY ==>
     memloc_within_alloca (ce_memloc_from_ops bp cf.cf_source cf.cf_size) s) ==>
    cf_alloca_ok bp (cfl |+ (ml, cf)) s
Proof
  rw[cf_alloca_ok_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac
QED

Triviality cf_alloca_ok_opt_fempty[local]:
  !bp s. cf_alloca_ok_opt bp (SOME FEMPTY) s
Proof
  simp[cf_alloca_ok_opt_def, cf_alloca_ok_fempty]
QED

(* cf_alloca_ok depends only on vs_allocas — preserved by memory writes *)
(* memloc_within_alloca depends only on vs_allocas *)
Triviality memloc_within_alloca_allocas_eq[local]:
  !ml s s'. s'.vs_allocas = s.vs_allocas ==>
    (memloc_within_alloca ml s' <=> memloc_within_alloca ml s)
Proof
  rw[memloc_within_alloca_def]
QED

Triviality cf_alloca_ok_allocas_eq[local]:
  !bp cfl s s'. s'.vs_allocas = s.vs_allocas ==>
    (cf_alloca_ok bp cfl s' <=> cf_alloca_ok bp cfl s)
Proof
  rw[cf_alloca_ok_def] >>
  eq_tac >> rpt strip_tac >> res_tac >>
  metis_tac[memloc_within_alloca_allocas_eq]
QED

(* Combined: cf_alloca_ok preserved through DRESTRICT when allocas unchanged *)
Triviality cf_alloca_ok_drestrict_step[local]:
  !bp cfl S s s'.
    cf_alloca_ok bp cfl s /\ s'.vs_allocas = s.vs_allocas ==>
    cf_alloca_ok bp (DRESTRICT cfl S) s'
Proof
  rpt strip_tac >>
  irule (iffLR cf_alloca_ok_allocas_eq) >> qexists `s` >> simp[] >>
  irule cf_alloca_ok_drestrict >> simp[]
QED

(* _opt versions for DRESTRICT of unwrap_copy_facts *)
Triviality cf_alloca_ok_opt_drestrict_step[local]:
  !bp v S s s'.
    cf_alloca_ok_opt bp v s /\ s'.vs_allocas = s.vs_allocas ==>
    cf_alloca_ok_opt bp (SOME (DRESTRICT (unwrap_copy_facts v) S)) s'
Proof
  Cases_on `v` >>
  simp[cf_alloca_ok_opt_def, unwrap_copy_facts_def,
       DRESTRICT_FEMPTY, cf_alloca_ok_fempty] >>
  metis_tac[cf_alloca_ok_drestrict_step]
QED

(* cf_alloca_ok preserved through FUPDATE when allocas unchanged *)
Triviality cf_alloca_ok_fupdate_step[local]:
  !bp cfl ml cf s s'.
    cf_alloca_ok bp cfl s /\ s'.vs_allocas = s.vs_allocas /\
    memloc_within_alloca ml s /\
    (cf.cf_opcode = MCOPY ==>
     memloc_within_alloca (ce_memloc_from_ops bp cf.cf_source cf.cf_size) s) ==>
    cf_alloca_ok bp (cfl |+ (ml, cf)) s'
Proof
  rpt strip_tac >>
  irule (iffLR cf_alloca_ok_allocas_eq) >> qexists `s` >> simp[] >>
  irule cf_alloca_ok_fupdate >> simp[]
QED

(* _opt version: invalidate + FUPDATE in one step *)
Triviality cf_alloca_ok_opt_invalidate_fupdate_step[local]:
  !bp aliases v ml cf s s'.
    cf_alloca_ok_opt bp v s /\ s'.vs_allocas = s.vs_allocas /\
    memloc_within_alloca ml s /\
    (cf.cf_opcode = MCOPY ==>
     memloc_within_alloca (ce_memloc_from_ops bp cf.cf_source cf.cf_size) s) ==>
    cf_alloca_ok_opt bp
      (SOME (copy_fact_invalidate aliases bp (unwrap_copy_facts v) ml
             |+ (ml, cf))) s'
Proof
  rpt strip_tac >>
  simp[cf_alloca_ok_opt_def] >>
  irule cf_alloca_ok_fupdate_step >> qexists `s` >> simp[] >>
  simp[copy_fact_invalidate_def] >>
  IF_CASES_TAC >> simp[cf_alloca_ok_fempty] >>
  irule cf_alloca_ok_drestrict_step >> qexists `s` >> simp[] >>
  Cases_on `v` >>
  gvs[cf_alloca_ok_opt_def, unwrap_copy_facts_def, cf_alloca_ok_fempty]
QED

Triviality cf_keys_ok_opt_drestrict[local]:
  !bp v S.
    cf_keys_ok_opt bp v ==>
    cf_keys_ok_opt bp (SOME (DRESTRICT (unwrap_copy_facts v) S))
Proof
  Cases_on `v` >>
  simp[cf_keys_ok_opt_def, unwrap_copy_facts_def,
       DRESTRICT_FEMPTY, cf_keys_ok_fempty] >>
  metis_tac[cf_keys_ok_drestrict]
QED

(* Alloca addresses fit in a word.  Trivially holds for real EVM execution
   since alloca bases are memory offsets (< 2^256).  Needed to ensure
   w2n (n2w addr) = addr for alloca-backed addresses. *)
Definition allocas_in_word_def:
  allocas_in_word s <=>
    !aid base sz. FLOOKUP s.vs_allocas aid = SOME (base, sz) ==>
      base + sz < dimword(:256)
End

(* allocas_in_word depends only on vs_allocas *)
Triviality allocas_in_word_allocas_eq[local]:
  !s s'. s'.vs_allocas = s.vs_allocas ==>
    (allocas_in_word s' <=> allocas_in_word s)
Proof
  rw[allocas_in_word_def]
QED

(* allocas_in_word + alloca-backed memloc → addr + sz < dimword.
   For ml_alloca = NONE, addr comes from w2n (Lit n) which is < dimword
   automatically — handle that case separately at use sites. *)
Triviality runtime_region_in_word[local]:
  !ml s addr sz.
    allocas_in_word s /\
    IS_SOME ml.ml_alloca /\
    memloc_within_alloca ml s /\
    memloc_runtime_region ml s = SOME (addr, sz) ==>
    addr + sz < dimword(:256)
Proof
  rw[allocas_in_word_def, memloc_within_alloca_def,
     memloc_runtime_region_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  first_x_assum (qspecl_then [`n`, `FST x`, `SND x`] mp_tac) >> gvs[]
QED

(* Combined helper: copy fact entry addr fits in a word.
   Derives memloc_within_alloca from cf_alloca_ok_opt + FLOOKUP, then
   proves addr < dimword via alloca (runtime_region_in_word) or Lit (w2n_lt).
   Replaces the LENGTH s.vs_memory < dimword requirement in cei_step_sim. *)
Triviality cf_entry_addr_lt_dimword[local]:
  !bp v op sz s addr sz_num cf.
    cf_alloca_ok_opt bp v s /\ allocas_in_word s /\
    FLOOKUP (unwrap_copy_facts v) (ce_memloc_from_ops bp op sz) = SOME cf /\
    memloc_runtime_region (ce_memloc_from_ops bp op sz) s = SOME (addr, sz_num) /\
    (!l. op <> Label l) ==>
    addr < dimword(:256)
Proof
  rpt strip_tac >>
  (* derive memloc_within_alloca from cf_alloca_ok *)
  `memloc_within_alloca (ce_memloc_from_ops bp op sz) s` by (
    `cf_alloca_ok bp (unwrap_copy_facts v) s` by
      (irule cf_alloca_ok_opt_unwrap >> simp[]) >>
    gvs[cf_alloca_ok_def] >> res_tac) >>
  (* case split on alloca backing *)
  Cases_on `IS_SOME (ce_memloc_from_ops bp op sz).ml_alloca`
  >- (
    mp_tac (Q.SPECL [`ce_memloc_from_ops bp op sz`, `s`, `addr`, `sz_num`]
              runtime_region_in_word) >> simp[] >> decide_tac)
  >>
  gvs[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM] >>
  Cases_on `op` >> gvs[ml_undefined_def, memloc_runtime_region_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  mp_tac (INST_TYPE [``:'a`` |-> ``:256``] wordsTheory.w2n_lt) >>
  disch_then (qspec_then `c` mp_tac) >> simp[]
QED

(* BP analysis at fixpoint: ASSIGN propagates pointer sets.
   At fixpoint, bp_handle_inst for ASSIGN sets bp_get_ptrs accordingly:
   - ASSIGN [Var src] → bp_get_ptrs bp out = bp_get_ptrs bp src
   - ASSIGN [Lit/Label/other] → bp_get_ptrs bp out = [] (unchanged from init)
   This ensures normalize_operand preserves bp_ptr_from_op. *)
Definition bp_assigns_stable_def:
  bp_assigns_stable bp dfg <=>
    !v inst. FLOOKUP dfg.dfg_defs v = SOME inst /\
             inst.inst_opcode = ASSIGN ==>
             (case inst.inst_operands of
                [Var w] => bp_get_ptrs bp v = bp_get_ptrs bp w
              | _ => bp_get_ptrs bp v = [])
End

(* Under bp_assigns_stable, normalize_operand preserves bp_ptr_from_op.
   Proof by induction on normalize_operand's recursion. *)
Theorem bp_ptr_from_op_normalize:
  !dfg visited op.
    bp_assigns_stable bp dfg ==>
    bp_ptr_from_op bp (normalize_operand dfg visited op) =
    bp_ptr_from_op bp op
Proof
  ho_match_mp_tac normalize_operand_ind >> rpt strip_tac >>
  simp[Once normalize_operand_def] >>
  (* Only the Var case remains after simp *)
  rename1 `MEM v visited` >>
  IF_CASES_TAC >> simp[] >>
  BasicProvers.FULL_CASE_TAC >> simp[] >>
  rename1 `FLOOKUP dfg.dfg_defs v = SOME inst` >>
  IF_CASES_TAC >> simp[] >>
  BasicProvers.FULL_CASE_TAC >> simp[] >>
  BasicProvers.FULL_CASE_TAC >> simp[] >>
  rename1 `inst.inst_operands = [src_op]` >>
  (* IH gives: bp_ptr_from_op bp (normalize dfg (v::visited) src_op) =
               bp_ptr_from_op bp src_op *)
  `bp_ptr_from_op bp (normalize_operand dfg (v::visited) src_op) =
   bp_ptr_from_op bp src_op` by (first_x_assum irule >> simp[]) >>
  simp[] >>
  (* bp_assigns_stable gives pointer relationship for v *)
  gvs[bp_assigns_stable_def] >>
  first_x_assum (qspecl_then [`v`, `inst`] mp_tac) >> simp[] >>
  Cases_on `src_op` >> gvs[bp_ptr_from_op_def]
QED

(* Main consequence: memloc_within_alloca transfers through normalize.
   Case analysis: Lit/Label → trivially T (NONE alloca or ml_undefined).
   Var v → Var w: same bp_ptr_from_op → same alloca/offset → same bound.
   Var v → Lit n: bp_get_ptrs bp v = [] → bp_ptr_from_op = NONE →
     ml_offset = NONE → trivially T. *)
Theorem memloc_within_alloca_normalize:
  !bp dfg op sz s.
    bp_assigns_stable bp dfg /\
    memloc_within_alloca (ce_memloc_from_ops bp op sz) s ==>
    memloc_within_alloca (ce_memloc_from_ops bp (normalize_operand dfg [] op) sz) s
Proof
  rpt strip_tac >>
  `bp_ptr_from_op bp (normalize_operand dfg [] op) =
   bp_ptr_from_op bp op` by (irule bp_ptr_from_op_normalize >> simp[]) >>
  Cases_on `normalize_operand dfg [] op`
  >- ((* Lit → ml_alloca = NONE → trivially T *)
      simp[ce_memloc_from_ops_def, bp_segment_from_ops_def,
           memloc_within_alloca_def] >>
      BasicProvers.every_case_tac >> simp[])
  >> ((* Var/Label: same bp_ptr_from_op as op *)
      Cases_on `op` >>
      gvs[ce_memloc_from_ops_def, bp_segment_from_ops_def,
          memloc_within_alloca_def, bp_ptr_from_op_def,
          ml_undefined_def])
QED

(* For a fixed offset op (non-Label), ml_size depends only on the sz operand.
   This means cf_key_size_ok + FLOOKUP chain implies matching ml_size
   for any (non-Label) offset paired with either sz. *)
Theorem ce_memloc_ml_size_only_sz:
  !bp op sz.
    (!l. op <> Label l) ==>
    (ce_memloc_from_ops bp op sz).ml_size =
    (case sz of Lit n => SOME (w2n n) | _ => NONE)
Proof
  rpt strip_tac >>
  Cases_on `op` >>
  gvs[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* memloc_within_alloca depends on ml_offset, ml_size, ml_alloca.
   For a fixed offset op, if ml_size matches between two sz values,
   memloc_within_alloca is equivalent. *)
Triviality memloc_within_alloca_change_sz[local]:
  !bp op sz1 sz2 s.
    (ce_memloc_from_ops bp op sz1).ml_size =
    (ce_memloc_from_ops bp op sz2).ml_size ==>
    (memloc_within_alloca (ce_memloc_from_ops bp op sz1) s <=>
     memloc_within_alloca (ce_memloc_from_ops bp op sz2) s)
Proof
  rpt strip_tac >>
  simp[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
       memloc_within_alloca_def] >>
  Cases_on `op` >> simp[] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Label offsets produce ml_undefined, which is trivially within alloca *)
Triviality memloc_within_alloca_label[local]:
  !bp l sz s. memloc_within_alloca (ce_memloc_from_ops bp (Label l) sz) s
Proof
  simp[ce_memloc_from_ops_def, bp_segment_from_ops_def,
       ml_undefined_def, memloc_within_alloca_def]
QED

(* bp_ptrs_bounded gives memloc_within_alloca for MCOPY read locations *)
Triviality bp_ptrs_bounded_mcopy_read_loc[local]:
  !bp fn s bb inst dst src sz.
    bp_ptrs_bounded bp fn s /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = MCOPY /\
    inst.inst_operands = [dst; src; sz] ==>
    memloc_within_alloca (ce_memloc_from_ops bp src sz) s
Proof
  rw[bp_ptrs_bounded_def, ce_memloc_from_ops_def] >>
  qabbrev_tac `ops = <|iao_ofst := src; iao_size := SOME sz;
                        iao_max_size := SOME sz|>` >>
  Cases_on `IS_SOME (bp_segment_from_ops bp ops).ml_alloca`
  >- (first_x_assum (qspecl_then [`bb`,`inst`,`ops`] mp_tac) >>
      simp[Abbr `ops`, mem_read_ops_def])
  >> gvs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE, Abbr `ops`,
         memloc_within_alloca_def, bp_segment_from_ops_def, LET_THM] >>
     Cases_on `src` >> simp[] >>
     BasicProvers.every_case_tac >> gvs[]
QED

(* Combined extraction: get all per-entry facts from cf_keys_ok + cf_alloca_ok
   in one go, avoiding competing ∀ml cf. FLOOKUP ... patterns. *)
Triviality cf_entry_facts_from_flookup[local]:
  !bp cfl ml cf s.
    cf_keys_ok bp cfl /\ cf_alloca_ok bp cfl s /\
    FLOOKUP cfl ml = SOME cf ==>
    cf_key_size_ok bp ml cf /\
    ml_is_fixed ml /\
    memloc_within_alloca ml s /\
    (cf.cf_opcode = MCOPY ==>
     ml_is_fixed (ce_memloc_from_ops bp cf.cf_source cf.cf_size) /\
     memloc_within_alloca (ce_memloc_from_ops bp cf.cf_source cf.cf_size) s)
Proof
  rw[cf_keys_ok_def, cf_alloca_ok_def] >> res_tac
QED

(* FEMPTY is trivially sound *)
Theorem cf_sound_opt_fempty:
  !bp dfg s. cf_sound_opt bp dfg (SOME FEMPTY) s
Proof
  simp[cf_sound_opt_def, cf_sound_def]
QED

(* NONE (top) is trivially sound *)
Theorem cf_sound_opt_none:
  !bp dfg s. cf_sound_opt bp dfg NONE s
Proof
  simp[cf_sound_opt_def]
QED

(* Soundness preserved by state_equiv {} (identical states) *)
Theorem cf_sound_opt_state_equiv:
  !bp dfg v s1 s2.
    state_equiv {} s1 s2 /\ cf_sound_opt bp dfg v s1 ==>
    cf_sound_opt bp dfg v s2
Proof
  rpt strip_tac >>
  `s1.vs_memory = s2.vs_memory` by fs[state_equiv_def, execution_equiv_def] >>
  `s1.vs_allocas = s2.vs_allocas` by fs[state_equiv_def, execution_equiv_def] >>
  `!op. eval_operand op s1 = eval_operand op s2` by
    (gen_tac >> irule eval_operand_equiv >> qexists_tac `{}` >> simp[]) >>
  `!opc. cf_source_data opc s1 = cf_source_data opc s2` by
    (Cases >> simp[cf_source_data_def] >>
     fs[state_equiv_def, execution_equiv_def]) >>
  `!ml. memloc_runtime_region ml s1 = memloc_runtime_region ml s2` by
    (gen_tac >> simp[memloc_runtime_region_def] >>
     BasicProvers.every_case_tac >> gvs[]) >>
  Cases_on `v` >> fs[cf_sound_opt_def, cf_sound_def] >>
  rpt strip_tac >> res_tac >>
  fs[cf_entry_sound_def]
QED

(* Entry soundness transfers via operand_equiv: if the source operands
   are equivalent under the DFG, the entry sound predicate transfers.
   This is used in join soundness (both join_right and join_left) and
   transfer soundness proofs. *)
Theorem cf_entry_sound_equiv:
  !bp dfg ml cf1 cf2 s.
    cf_entry_sound bp dfg ml cf2 s /\
    cf1.cf_opcode = cf2.cf_opcode /\
    operand_equiv dfg cf1.cf_source cf2.cf_source ==>
    cf_entry_sound bp dfg ml cf1 s
Proof
  rpt strip_tac >>
  fs[cf_entry_sound_def, operand_equiv_def]
QED

(* ===== analysis_inst_simulates for copy_elision_inst ===== *)

(* Copy opcodes are not terminators or INVOKE *)
Triviality copy_opcode_not_term[local]:
  !op. is_copy_opcode op ==> ~is_terminator op
Proof
  Cases >> simp[is_copy_opcode_def, is_terminator_def]
QED

Triviality copy_opcode_not_invoke[local]:
  !op. is_copy_opcode op ==> op <> INVOKE
Proof
  Cases >> simp[is_copy_opcode_def]
QED

Triviality copy_opcode_not_phi[local]:
  !op. is_copy_opcode op ==> op <> PHI
Proof
  Cases >> simp[is_copy_opcode_def]
QED

Triviality copy_opcode_cases[local]:
  !op.
    is_copy_opcode op ==>
    op = MCOPY \/ op = CALLDATACOPY \/ op = CODECOPY \/
    op = DLOADBYTES \/ op = RETURNDATACOPY
Proof
  Cases >> simp[is_copy_opcode_def]
QED

(* mcopy is identity when destination bytes already equal source bytes *)
Theorem mcopy_identity[local]:
  !dst src sz s.
    dst + sz <= LENGTH s.vs_memory /\
    src + sz <= LENGTH s.vs_memory /\
    TAKE sz (DROP dst s.vs_memory) = TAKE sz (DROP src s.vs_memory) ==>
    mcopy dst src sz s = s
Proof
  rw[mcopy_def] >>
  `LENGTH (TAKE sz (DROP src s.vs_memory)) = sz` by simp[LENGTH_TAKE, LENGTH_DROP] >>
  `TAKE sz (DROP src s.vs_memory ++ REPLICATE sz 0w) = TAKE sz (DROP src s.vs_memory)` by
    simp[TAKE_APPEND1] >>
  simp[] >>
  match_mp_tac write_memory_with_expansion_identity >> simp[]
QED

(* run_insts of singleton = step_inst *)
Theorem run_insts_singleton[local]:
  !fuel ctx inst s. run_insts fuel ctx [inst] s = step_inst fuel ctx inst s
Proof
  rw[run_insts_def] >> CASE_TAC
QED

(* inst_transform_structural for copy_elision_inst *)
Theorem cei_structural[local]:
  !bp dfg.
    inst_transform_structural (\v inst. [copy_elision_inst bp dfg v inst])
Proof
  rpt gen_tac >>
  simp[inst_transform_structural_def] >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[copy_elision_inst_def, LET_THM] >>
  TRY (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >> NO_TAC) >>
  TRY (fs[] >> NO_TAC) >>
  TRY (
    qexists `inst` >> simp[] >>
    Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >> NO_TAC) >>
  TRY (
    qexists `inst` >> simp[] >>
    Cases_on `inst.inst_opcode` >> gvs[] >> NO_TAC) >>
  rpt (IF_CASES_TAC >> fs[mk_nop_inst_def, is_terminator_def]) >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  TRY CASE_TAC >> fs[mk_nop_inst_def, is_terminator_def] >>
  imp_res_tac copy_opcode_not_term >> imp_res_tac copy_opcode_not_invoke >>
  imp_res_tac copy_opcode_not_phi >>
  fs[]
QED

(* Common tactic: when transformed instruction = original,
   both sides of lift_result are the same execution result. *)
val unchanged_tac =
  simp[step_inst_non_invoke, step_inst_base_def] >>
  irule lift_result_refl >>
  simp[state_equiv_refl, execution_equiv_refl];

(* ml_is_fixed on ce_memloc implies offset operand is not Label *)
Triviality ce_memloc_fixed_not_label[local]:
  !bp op sz.
    ml_is_fixed (ce_memloc_from_ops bp op sz) ==> !l. op <> Label l
Proof
  rw[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
     ml_is_fixed_def, ml_undefined_def] >>
  Cases_on `op` >> gvs[]
QED

(* ml_is_fixed on ce_memloc implies size operand is Lit *)
Triviality ce_memloc_fixed_sz_lit[local]:
  !bp op sz.
    ml_is_fixed (ce_memloc_from_ops bp op sz) ==> ?n. sz = Lit n
Proof
  rw[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
     ml_is_fixed_def, ml_undefined_def] >>
  Cases_on `op` >> Cases_on `sz` >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* When sz = Lit n and op is non-Label, ml_size = SOME (w2n n) *)
Triviality ce_memloc_lit_size[local]:
  !bp op (n:bytes32).
    (!l. op <> Label l) ==>
    (ce_memloc_from_ops bp op (Lit n)).ml_size = SOME (w2n n)
Proof
  rw[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM] >>
  Cases_on `op` >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Wrapper for bp_segment_from_ops_runtime_region_proof that works
   directly with ce_memloc_from_ops. *)
Triviality ce_memloc_runtime_region[local]:
  !bp dst_op sz s.
    bp_ptr_sound bp s /\
    ml_is_fixed (ce_memloc_from_ops bp dst_op sz) /\
    IS_SOME (eval_operand dst_op s) ==>
    ?addr.
      eval_operand dst_op s = SOME (n2w addr) /\
      memloc_runtime_region (ce_memloc_from_ops bp dst_op sz) s =
        SOME (addr, THE (ce_memloc_from_ops bp dst_op sz).ml_size)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bp`,
    `<| iao_ofst := dst_op; iao_size := SOME sz; iao_max_size := SOME sz |>`,
    `ce_memloc_from_ops bp dst_op sz`, `s`]
    (DB.fetch "memAliasProofs" "bp_segment_from_ops_runtime_region_proof")) >>
  simp[ce_memloc_from_ops_def]
QED

(* Like ce_memloc_runtime_region but expressed via w2n of the eval result.
   Requires allocas_in_word + memloc_within_alloca so that the existential
   addr from bp_segment_from_ops fits in a word (addr < dimword).
   This avoids callers needing to reason about n2w/w2n round-tripping. *)
Triviality ce_memloc_runtime_w2n[local]:
  !bp op sz s v.
    bp_ptr_sound bp s /\
    allocas_in_word s /\
    ml_is_fixed (ce_memloc_from_ops bp op sz) /\
    memloc_within_alloca (ce_memloc_from_ops bp op sz) s /\
    eval_operand op s = SOME v ==>
    memloc_runtime_region (ce_memloc_from_ops bp op sz) s =
      SOME (w2n v, THE (ce_memloc_from_ops bp op sz).ml_size)
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bp`, `op`, `sz`, `s`] ce_memloc_runtime_region) >>
  simp[] >>
  strip_tac >>
  gvs[] >>
  Cases_on `(ce_memloc_from_ops bp op sz).ml_alloca`
  >- suspend "none_case"
  >> suspend "some_case"
QED

Resume ce_memloc_runtime_w2n[none_case]:
  gvs[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM] >>
  Cases_on `op` >> gvs[ml_is_fixed_def, ml_undefined_def] >>
  gvs[memloc_runtime_region_def] >>
  BasicProvers.every_case_tac >> gvs[] >>
  mp_tac (INST_TYPE [``:'a`` |-> ``:256``] wordsTheory.w2n_lt) >>
  disch_then (qspec_then `c` mp_tac) >> simp[]
QED

Resume ce_memloc_runtime_w2n[some_case]:
  mp_tac (Q.SPECL [`ce_memloc_from_ops bp op sz`, `s`]
             runtime_region_in_word) >>
  simp[]
QED

Finalise ce_memloc_runtime_w2n

(* Helper: operand_equiv + dfg_assigns_sound → normalized eval equals raw eval.
   cf_entry_sound uses normalize(op1), execution uses op2; this connects them. *)
Triviality operand_equiv_norm_eval[local]:
  !dfg op1 op2 s.
    operand_equiv dfg op1 op2 /\ dfg_assigns_sound dfg s ==>
    eval_operand (normalize_operand dfg [] op1) s = eval_operand op2 s
Proof
  rw[operand_equiv_def] >>
  metis_tac[normalize_operand_eval]
QED

(* Helper: cf_sound_opt + FLOOKUP → cf_entry_sound *)
Triviality cf_sound_opt_entry[local]:
  !bp dfg v ml cf s.
    cf_sound_opt bp dfg v s /\ FLOOKUP (unwrap_copy_facts v) ml = SOME cf ==>
    cf_entry_sound bp dfg ml cf s
Proof
  Cases_on `v` >> gvs[cf_sound_opt_def, unwrap_copy_facts_def, cf_sound_def]
QED

(* Helper: step_inst for copy opcodes with SOME operands produces
   write_memory_with_expansion with padded bytes from cf_source_data.
   Only RETURNDATACOPY needs the source bound (aborts on OOB per EIP-211);
   all other copy opcodes pad with zeros unconditionally. *)
Triviality step_copy_opcode_ok[local]:
  !fuel ctx inst opc dst_op src_op sz_op dst_val src_val sz_val s.
    is_copy_opcode opc /\
    inst.inst_outputs = [] /\
    eval_operand dst_op s = SOME dst_val /\
    eval_operand src_op s = SOME src_val /\
    eval_operand sz_op s = SOME sz_val /\
    (opc = RETURNDATACOPY ==>
     w2n src_val + w2n sz_val <= LENGTH (cf_source_data opc s)) ==>
    step_inst fuel ctx
      (inst with <| inst_opcode := opc;
                    inst_operands := [dst_op; src_op; sz_op] |>) s =
    OK (write_memory_with_expansion (w2n dst_val)
          (TAKE (w2n sz_val) (DROP (w2n src_val) (cf_source_data opc s) ++
                              REPLICATE (w2n sz_val) 0w)) s)
Proof
  rpt strip_tac >>
  drule copy_opcode_cases >> strip_tac >> gvs[]
  >- gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
         mcopy_def, LET_THM]
  >- gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
         LET_THM]
  >- gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
         LET_THM]
  >- gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
         LET_THM] >>
  gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
      LET_THM] >>
  (* RETURNDATACOPY: in-bounds, so TAKE without padding = TAKE with padding *)
  `TAKE (w2n sz_val) (DROP (w2n src_val) s.vs_returndata ++ REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n src_val) s.vs_returndata)` by
    (irule TAKE_APPEND1 >> simp[LENGTH_DROP]) >>
  simp[]
QED

(* Reverse of step_copy_opcode_ok: from step_inst = OK s', derive s' = wmwe.
   Does NOT require bounds precondition (mcopy/codecopy/dloadbytes pad).
   Takes operands as parameters to avoid EL-style conclusion issues. *)
Triviality step_is_copy_eq_wmwe[local]:
  !fuel ctx inst s s' dst src sz.
    is_copy_opcode inst.inst_opcode /\
    inst.inst_operands = [dst; src; sz] /\
    step_inst fuel ctx inst s = OK s' ==>
    ?dst_val src_val sz_val.
      eval_operand dst s = SOME dst_val /\
      eval_operand src s = SOME src_val /\
      eval_operand sz s = SOME sz_val /\
      s' = write_memory_with_expansion (w2n dst_val)
             (TAKE (w2n sz_val)
                (DROP (w2n src_val) (cf_source_data inst.inst_opcode s) ++
                 REPLICATE (w2n sz_val) 0w)) s
Proof
  rpt strip_tac >>
  drule copy_opcode_cases >> strip_tac >> gvs[]
  >- (gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
          mcopy_def, LET_THM] >>
      BasicProvers.every_case_tac >> gvs[])
  >- (gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
          LET_THM] >>
      BasicProvers.every_case_tac >> gvs[])
  >- (gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
          LET_THM] >>
      BasicProvers.every_case_tac >> gvs[])
  >- (gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
          LET_THM] >>
      BasicProvers.every_case_tac >> gvs[]) >>
  gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
      LET_THM] >>
  BasicProvers.every_case_tac >> gvs[] >>
  `TAKE (w2n x) (DROP (w2n x') s.vs_returndata ++ REPLICATE (w2n x) 0w) =
   TAKE (w2n x) (DROP (w2n x') s.vs_returndata)` by
    (irule TAKE_APPEND1 >> simp[LENGTH_DROP]) >>
  simp[]
QED

(* RETURNDATACOPY bound: if step_inst = OK for a copy opcode that is
   RETURNDATACOPY, then the source was in bounds. *)
Triviality step_copy_rdc_bound[local]:
  !fuel ctx inst s s' dst src sz dst_val src_val sz_val.
    inst.inst_opcode = RETURNDATACOPY /\
    inst.inst_operands = [dst; src; sz] /\
    eval_operand src s = SOME src_val /\
    eval_operand sz s = SOME sz_val /\
    step_inst fuel ctx inst s = OK s' ==>
    w2n src_val + w2n sz_val <= LENGTH (cf_source_data RETURNDATACOPY s)
Proof
  rpt strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_def, cf_source_data_def,
      LET_THM] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Per-instruction simulation: copy_elision_inst preserves semantics.
   Cases:
   1. Non-MCOPY: identity transform, trivially simulated.
   2. MCOPY, NOP: dest already has source bytes → mcopy identity.
   3. MCOPY, forwarding: forwarded source has same bytes → same result.
   4. MCOPY, unchanged: identity, trivially simulated.
*)
Theorem cei_step_sim[local]:
  !bp dfg fuel (ctx:venom_context) v inst s.
    cf_sound_opt bp dfg v s /\ cf_keys_ok_opt bp v /\ inst_wf inst /\
    dfg_assigns_sound dfg s /\ bp_ptr_sound bp s /\
    cf_alloca_ok_opt bp v s /\ allocas_in_word s ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx [copy_elision_inst bp dfg v inst] s)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = MCOPY`
  >- (
    (* MCOPY case — requires memory-level reasoning *)
    (* decompose inst_wf to get 3 operands *)
    gvs[inst_wf_def, LENGTH_EQ_NUM_compute, PULL_EXISTS] >>
    rename1 `inst.inst_operands = [dst_op; src_op; sz_op]` >>
    (* simplify original step_inst for MCOPY *)
    simp[step_inst_non_invoke, step_inst_base_def] >>
    (* case split on operand evaluation *)
    Cases_on `eval_operand dst_op s` >> simp[] >>
    Cases_on `eval_operand src_op s` >> simp[] >>
    Cases_on `eval_operand sz_op s` >> simp[] >>
    rename1 `eval_operand dst_op s = SOME dst_val` >>
    rename1 `eval_operand src_op s = SOME src_val` >>
    rename1 `eval_operand sz_op s = SOME sz_val` >>
    (* All operands SOME. Goal: lift_result ... (OK (mcopy ...))
       (run_insts ... [copy_elision_inst ...] s) *)
    (* simplify copy_elision_inst for MCOPY with 3 operands *)
    simp[copy_elision_inst_def, LET_THM, run_insts_singleton] >>
    (* Case split on FLOOKUP write_loc *)
    qabbrev_tac `write_loc = ce_memloc_from_ops bp dst_op sz_op` >>
    qabbrev_tac `read_loc = ce_memloc_from_ops bp src_op sz_op` >>
    Cases_on `FLOOKUP (unwrap_copy_facts v) write_loc` >> simp[]
    >- (
      (* FLOOKUP write_loc = NONE *)
      Cases_on `FLOOKUP (unwrap_copy_facts v) read_loc` >> simp[]
      >- unchanged_tac (* NONE/NONE *)
      >>
      IF_CASES_TAC >> simp[]
      >- suspend "fwd1" (* forward_1: NONE/SOME with is_copy_opcode *)
      >> unchanged_tac)
    >>
    (* FLOOKUP write_loc = SOME cf *)
    rename1 `FLOOKUP _ write_loc = SOME cf` >>
    IF_CASES_TAC
    >- (
      (* NOP case: redundant copy *)
      gvs[] >>
      `step_inst fuel ctx (mk_nop_inst inst) s = OK s` by
        (irule step_nop_identity >> simp[mk_nop_inst_def]) >>
      simp[lift_result_def, state_equiv_refl] >>
      suspend "nop")
    >>
    gvs[] >>
    Cases_on `FLOOKUP (unwrap_copy_facts v) read_loc` >> simp[]
    >- unchanged_tac (* SOME/NONE *)
    >>
    IF_CASES_TAC >> simp[]
    >- suspend "fwd2" (* forward_2: SOME/SOME with is_copy_opcode *)
    >> unchanged_tac)
  >>
  (* Non-MCOPY: copy_elision_inst returns inst unchanged *)
  `copy_elision_inst bp dfg v inst = inst` by (
    simp[copy_elision_inst_def] >>
    Cases_on `inst.inst_opcode = INVOKE` >> simp[]) >>
  simp[run_insts_singleton] >>
  DISJ2_TAC >> unchanged_tac
QED

Resume cei_step_sim[nop]:
  (* Goal: state_equiv {} (mcopy (w2n dst_val) (w2n src_val) (w2n sz_val) s) s
     Strategy: cf_entry_sound says dest already has source bytes → mcopy identity *)
  (* 1. ml_is_fixed write_loc *)
  `cf_keys_ok bp (unwrap_copy_facts v)` by
    (irule cf_keys_ok_opt_unwrap >> simp[]) >>
  `ml_is_fixed write_loc` by (gvs[cf_keys_ok_def] >> res_tac) >>
  (* 2. Unabbreviate write_loc *)
  qpat_x_assum `Abbrev (write_loc = _)`
    (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  (* 3. sz_op = Lit n *)
  drule_all ce_memloc_fixed_sz_lit >> strip_tac >> gvs[] >>
  (* 4. Runtime region *)
  drule ce_memloc_runtime_region >>
  disch_then drule >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!l. dst_op <> Label l` by
    (CCONTR_TAC >> gvs[] >> drule_all ce_memloc_fixed_not_label >> simp[]) >>
  `(ce_memloc_from_ops bp dst_op (Lit n)).ml_size = SOME (w2n n)` by
    (irule ce_memloc_lit_size >> simp[]) >>
  (* 5. cf_entry_sound *)
  drule_all cf_sound_opt_entry >> strip_tac >>
  (* Unfold cf_entry_sound with known runtime region *)
  pop_assum mp_tac >>
  simp[cf_entry_sound_def, cf_source_data_def] >>
  strip_tac >>
  (* 6. addr < dimword via alloca reasoning *)
  `addr < dimword(:256)` by (
    drule_all cf_entry_addr_lt_dimword >> simp[]) >>
  (* 7. Connect normalized source to src_op via operand_equiv *)
  `eval_operand (normalize_operand dfg [] cf.cf_source) s =
   eval_operand src_op s` by
    (irule operand_equiv_norm_eval >> simp[]) >>
  gvs[] >>
  (* gvs resolved dst_val = n2w addr and simplified w2n (n2w addr) = addr *)
  (* 8. sz_val = n *)
  `sz_val = n` by gvs[eval_operand_def] >>
  gvs[] >>
  (* 8. mcopy identity: dest already has source bytes.
     bytes_eq: TAKE sz (DROP dst mem) = TAKE sz (DROP src mem ++ REPLICATE sz 0w)
     mcopy_def: mcopy dst src sz s = wmwe dst (TAKE sz (DROP src mem ++ REPLICATE sz 0w)) s
     So mcopy writes bytes_eq_RHS to dst, but dst already has those bytes -> identity *)
  `mcopy addr (w2n src_val) (w2n n) s = s` by (
    simp[mcopy_def] >>
    irule write_memory_with_expansion_identity >> simp[LENGTH_TAKE_EQ]) >>
  simp[state_equiv_refl]
QED

Resume cei_step_sim[fwd1]:
  (* Goal: lift_result ... (OK (mcopy dst src sz s))
           (step_inst ... (inst with <|opcode:=x.cf_opcode; ops:=[dst_op; norm x.cf_source; sz_op]|>) s)
     Strategy: cf_entry_sound for read_loc says bytes at src in memory =
     bytes at x.cf_source in source_data. Both sides write same bytes to dst. *)
  (* 1. ml_is_fixed read_loc → sz_op = Lit n *)
  `cf_keys_ok bp (unwrap_copy_facts v)` by
    (irule cf_keys_ok_opt_unwrap >> simp[]) >>
  `ml_is_fixed read_loc` by (gvs[cf_keys_ok_def] >> res_tac) >>
  qpat_x_assum `Abbrev (read_loc = _)`
    (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all ce_memloc_fixed_sz_lit >> strip_tac >> gvs[] >>
  (* 2. Runtime region for read_loc → eval src_op = SOME (n2w addr) *)
  `!l. src_op <> Label l` by
    (CCONTR_TAC >> gvs[] >> drule_all ce_memloc_fixed_not_label >> simp[]) >>
  drule ce_memloc_runtime_region >>
  disch_then (qspec_then `src_op` mp_tac) >>
  disch_then (qspec_then `Lit n` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `(ce_memloc_from_ops bp src_op (Lit n)).ml_size = SOME (w2n n)` by
    (irule ce_memloc_lit_size >> simp[]) >>
  (* 3. cf_entry_sound for read_loc → bytes equality + source eval *)
  drule_all cf_sound_opt_entry >> strip_tac >>
  pop_assum mp_tac >>
  simp[cf_entry_sound_def] >> strip_tac >>
  (* Now have from cf_entry_sound (padded):
     - addr + w2n n ≤ LENGTH memory
     - (x.cf_opcode = RETURNDATACOPY ⇒ source bound)
     - TAKE (w2n n) (DROP addr mem) =
       TAKE (w2n n) (DROP (w2n src_val') source_data ++ REPLICATE (w2n n) 0w) *)
  `addr < dimword(:256)` by (
    drule_all cf_entry_addr_lt_dimword >> simp[]) >>
  gvs[] >>
  `sz_val = n` by gvs[eval_operand_def] >> gvs[] >>
  (* 4. Evaluate forwarded step using step_copy_opcode_ok *)
  `step_inst fuel ctx
     (inst with <| inst_opcode := x.cf_opcode;
                   inst_operands := [dst_op; normalize_operand dfg [] x.cf_source; Lit n] |>) s =
   OK (write_memory_with_expansion (w2n dst_val)
         (TAKE (w2n n) (DROP (w2n src_val') (cf_source_data x.cf_opcode s) ++
                         REPLICATE (w2n n) 0w)) s)` by
    (irule step_copy_opcode_ok >> simp[]) >>
  (* 5. Show original mcopy bytes = forwarded bytes. *)
  `TAKE (w2n n) (DROP addr s.vs_memory ++ REPLICATE (w2n n) 0w) =
   TAKE (w2n n) (DROP (w2n src_val') (cf_source_data x.cf_opcode s) ++
                  REPLICATE (w2n n) 0w)` by (
    `TAKE (w2n n) (DROP addr s.vs_memory ++ REPLICATE (w2n n) 0w) =
     TAKE (w2n n) (DROP addr s.vs_memory)` by
      (irule TAKE_APPEND1 >> simp[LENGTH_DROP]) >>
    simp[]) >>
  simp[lift_result_def, mcopy_def, state_equiv_refl]
QED

Resume cei_step_sim[fwd2]:
  (* Same structure as fwd1 *)
  `cf_keys_ok bp (unwrap_copy_facts v)` by
    (irule cf_keys_ok_opt_unwrap >> simp[]) >>
  `ml_is_fixed read_loc` by (gvs[cf_keys_ok_def] >> res_tac) >>
  qpat_x_assum `Abbrev (read_loc = _)`
    (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all ce_memloc_fixed_sz_lit >> strip_tac >> gvs[] >>
  `!l. src_op <> Label l` by
    (CCONTR_TAC >> gvs[] >> drule_all ce_memloc_fixed_not_label >> simp[]) >>
  drule ce_memloc_runtime_region >>
  disch_then (qspec_then `src_op` mp_tac) >>
  disch_then (qspec_then `Lit n` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `(ce_memloc_from_ops bp src_op (Lit n)).ml_size = SOME (w2n n)` by
    (irule ce_memloc_lit_size >> simp[]) >>
  drule_all cf_sound_opt_entry >> strip_tac >>
  pop_assum mp_tac >>
  simp[cf_entry_sound_def] >> strip_tac >>
  `addr < dimword(:256)` by (
    drule_all cf_entry_addr_lt_dimword >> simp[]) >>
  gvs[] >>
  `sz_val = n` by gvs[eval_operand_def] >> gvs[] >>
  `step_inst fuel ctx
     (inst with <| inst_opcode := x.cf_opcode;
                   inst_operands := [dst_op; normalize_operand dfg [] x.cf_source; Lit n] |>) s =
   OK (write_memory_with_expansion (w2n dst_val)
         (TAKE (w2n n) (DROP (w2n src_val') (cf_source_data x.cf_opcode s) ++
                         REPLICATE (w2n n) 0w)) s)` by
    (irule step_copy_opcode_ok >> simp[]) >>
  `TAKE (w2n n) (DROP addr s.vs_memory ++ REPLICATE (w2n n) 0w) =
   TAKE (w2n n) (DROP (w2n src_val') (cf_source_data x.cf_opcode s) ++
                  REPLICATE (w2n n) 0w)` by (
    `TAKE (w2n n) (DROP addr s.vs_memory ++ REPLICATE (w2n n) 0w) =
     TAKE (w2n n) (DROP addr s.vs_memory)` by
      (irule TAKE_APPEND1 >> simp[LENGTH_DROP]) >>
    simp[]) >>
  simp[lift_result_def, mcopy_def, state_equiv_refl]
QED

Finalise cei_step_sim;

(* inst_idx independence *)
Triviality ptr_matches_var_inst_idx[local,simp]:
  ptr_matches_var p v (s with vs_inst_idx := n) = ptr_matches_var p v s
Proof
  Cases_on `p` >> rename1 `Ptr a off` >>
  Cases_on `off` >> Cases_on `a` >>
  simp[ptr_matches_var_def, lookup_var_def]
QED

Triviality bp_ptr_sound_inst_idx[local,simp]:
  bp_ptr_sound bp (s with vs_inst_idx := n) = bp_ptr_sound bp s
Proof
  simp[bp_ptr_sound_def, lookup_var_def]
QED

Triviality dfg_assigns_sound_inst_idx[local,simp]:
  dfg_assigns_sound dfg (s with vs_inst_idx := n) = dfg_assigns_sound dfg s
Proof
  simp[dfgCorrectnessProofTheory.dfg_assigns_sound_def,
       lookup_var_def, instIdxIndepTheory.eval_op_inst_idx]
QED

Triviality allocas_non_overlapping_inst_idx[local,simp]:
  allocas_non_overlapping (s with vs_inst_idx := n) = allocas_non_overlapping s
Proof
  simp[allocas_non_overlapping_def]
QED

Triviality allocas_in_word_inst_idx[local,simp]:
  allocas_in_word (s with vs_inst_idx := n) = allocas_in_word s
Proof
  simp[allocas_in_word_def]
QED

Triviality bp_ptrs_bounded_inst_idx[local,simp]:
  bp_ptrs_bounded bp fn (s with vs_inst_idx := n) = bp_ptrs_bounded bp fn s
Proof
  simp[bp_ptrs_bounded_def, memloc_within_alloca_def]
QED

(* Per-instruction simulation for inv3: dfg_assigns_sound, bp_ptr_sound,
   allocas_in_word are inst_idx-independent, so stripping vs_inst_idx := 0
   is safe. cf_alloca_ok_opt + allocas_in_word replace the old
   LENGTH s.vs_memory < dimword(:256) requirement. *)
Theorem cei_simulates_inv:
  !bp dfg fuel (ctx:venom_context) v inst s.
    cf_sound_opt bp dfg v s /\ cf_keys_ok_opt bp v /\
    cf_alloca_ok_opt bp v s /\ inst_wf inst /\
    dfg_assigns_sound dfg (s with vs_inst_idx := 0) /\
    bp_ptr_sound bp (s with vs_inst_idx := 0) /\
    allocas_in_word (s with vs_inst_idx := 0) ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result (state_equiv {}) (execution_equiv {}) (execution_equiv {})
      (step_inst fuel ctx inst s)
      (run_insts fuel ctx [copy_elision_inst bp dfg v inst] s)
Proof
  rpt strip_tac >> irule cei_step_sim >> gvs[]
QED

(* ===== transfer_sound for copy_fact_transfer ===== *)

(* Terminators that return OK preserve memory, call_ctx, data_section, code, returndata.
   JMP/JNZ/DJMP go through jump_to which only modifies control flow.
   STOP/REVERT return non-OK (Halt/Revert), so don't appear here. *)
Triviality terminator_opcode_cases[local]:
  !op.
    is_terminator op ==>
    op = JMP \/ op = JNZ \/ op = DJMP \/ op = RET \/
    op = RETURN \/ op = REVERT \/ op = STOP \/ op = SINK \/
    op = SELFDESTRUCT \/ op = INVALID \/ op = DRET \/ op = RETFMP
Proof
  Cases >> simp[is_terminator_def]
QED

val terminator_tuple_tac =
  fs[venomExecSemanticsTheory.step_inst_base_def, jump_to_def,
     halt_state_def, revert_state_def, set_returndata_def, LET_THM] >>
  rpt (BasicProvers.PURE_FULL_CASE_TAC >>
       fs[jump_to_def, halt_state_def, revert_state_def,
          set_returndata_def]) >>
  gvs[];

Triviality step_inst_base_terminator_ok_field_tuple[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\
    is_terminator inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    (s'.vs_memory, s'.vs_allocas, s'.vs_call_ctx,
     s'.vs_data_section, s'.vs_code, s'.vs_returndata) =
    (s.vs_memory, s.vs_allocas, s.vs_call_ctx,
     s.vs_data_section, s.vs_code, s.vs_returndata)
Proof
  rpt strip_tac >>
  drule terminator_opcode_cases >> strip_tac
  >- terminator_tuple_tac (* JMP *)
  >- terminator_tuple_tac (* JNZ *)
  >- terminator_tuple_tac (* DJMP *)
  >- terminator_tuple_tac (* RET *)
  >- terminator_tuple_tac (* RETURN *)
  >- terminator_tuple_tac (* REVERT *)
  >- terminator_tuple_tac (* STOP *)
  >- terminator_tuple_tac (* SINK *)
  >- terminator_tuple_tac (* SELFDESTRUCT *)
  >- terminator_tuple_tac (* INVALID *)
  >- fs[write_effects_def] (* DRET excluded by no-memory premise *)
  >- terminator_tuple_tac (* RETFMP *)
QED

Triviality step_terminator_preserves_fields[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_terminator inst.inst_opcode /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
    s'.vs_memory = s.vs_memory /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_code = s.vs_code /\
    s'.vs_returndata = s.vs_returndata
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by (
    Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  `step_inst_base inst s = OK s'` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  drule_all step_inst_base_terminator_ok_field_tuple >>
  simp[]
QED

(* cf_sound is preserved by DRESTRICT (subset of entries) *)
Triviality cf_sound_drestrict[local]:
  !bp dfg cfl s keys.
    cf_sound bp dfg cfl s ==>
    cf_sound bp dfg (DRESTRICT cfl keys) s
Proof
  rw[cf_sound_def] >> rpt strip_tac >> fs[FLOOKUP_DRESTRICT]
QED

(* cf_entry_sound preserved when memory, allocas, source eval unchanged *)
Triviality cf_entry_sound_preserved[local]:
  !bp dfg ml cf s s'.
    cf_entry_sound bp dfg ml cf s /\
    s'.vs_memory = s.vs_memory /\
    s'.vs_allocas = s.vs_allocas /\
    cf_source_data cf.cf_opcode s' = cf_source_data cf.cf_opcode s /\
    eval_operand (normalize_operand dfg [] cf.cf_source) s' =
    eval_operand (normalize_operand dfg [] cf.cf_source) s ==>
    cf_entry_sound bp dfg ml cf s'
Proof
  rw[cf_entry_sound_def, memloc_runtime_region_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* cf_sound preserved when memory unchanged and non-killed var evals preserved *)
Triviality cf_sound_prune_preserved[local]:
  !bp dfg killed cfl s s'.
    cf_sound bp dfg cfl s /\
    s'.vs_memory = s.vs_memory /\
    s'.vs_allocas = s.vs_allocas /\
    s'.vs_labels = s.vs_labels /\
    (!opc. cf_source_data opc s' = cf_source_data opc s) /\
    (!v. v NOTIN killed ==> lookup_var v s' = lookup_var v s) ==>
    cf_sound bp dfg (copy_fact_prune_vars dfg killed cfl) s'
Proof
  rw[cf_sound_def, copy_fact_prune_vars_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[] >>
  `~operand_var_killed killed (normalize_operand dfg [] cf.cf_source)` by (
    CCONTR_TAC >> gvs[] >>
    `ml IN {ml | ?cf. FLOOKUP cfl ml = SOME cf /\
            operand_var_killed killed (normalize_operand dfg [] cf.cf_source)}` by (
      simp[] >> qexists_tac `cf` >> simp[]) >>
    fs[IN_DIFF]) >>
  first_x_assum drule >> strip_tac >>
  irule cf_entry_sound_preserved >> qexists_tac `s` >>
  simp[] >>
  (* eval_operand unchanged: source is not Var v with v IN killed *)
  Cases_on `normalize_operand dfg [] cf.cf_source` >>
  gvs[operand_var_killed_def, eval_operand_def]
QED

(* After executing an instruction, the transfer function correctly
   updates the copy fact lattice to maintain soundness. *)

(* Memory preserved by non-terminator, non-alloca, non-ext-call, non-memory ops.
   INVOKE is excluded because write_effects INVOKE = all_effects includes Eff_MEMORY. *)
Triviality invoke_has_mem_effect[local]:
  Eff_MEMORY IN write_effects INVOKE
Proof
  EVAL_TAC
QED

Triviality not_invoke_if_no_mem_effect[local]:
  Eff_MEMORY NOTIN write_effects inst.inst_opcode ==>
  inst.inst_opcode <> INVOKE
Proof
  CCONTR_TAC >> gvs[invoke_has_mem_effect]
QED

(* Variables not in inst_defs (= inst_outputs) preserved by any instruction *)
Triviality step_preserves_unkilled_vars[local]:
  !fuel ctx inst s s' v.
    step_inst fuel ctx inst s = OK s' /\
    ~MEM v (inst_defs inst) ==>
    lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >> gvs[inst_defs_def] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[venomExecPropsTheory.step_terminator_preserves_vars]
  >> (drule_all step_preserves_non_output_vars >> strip_tac)
QED

(* Eff_RETURNDATA NOTIN write_effects when Eff_MEMORY NOTIN and not ext_call *)
Triviality eff_returndata_from_memory[local]:
  !opc. ~is_ext_call_op opc /\ Eff_MEMORY NOTIN write_effects opc ==>
        Eff_RETURNDATA NOTIN write_effects opc
Proof
  Cases >> simp[is_ext_call_op_def, write_effects_def] >> EVAL_TAC
QED

(* cf_source_data is preserved by any OK step whose opcode has no memory effect,
   and is not an ext-call or alloca. *)
Triviality step_preserves_cf_source_data[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode ==>
    !opc. cf_source_data opc s' = cf_source_data opc s
Proof
  rpt strip_tac >>
  imp_res_tac not_invoke_if_no_mem_effect >>
  Cases_on `is_terminator inst.inst_opcode`
  >- ((* Terminator: use combined preservation lemma *)
      drule_all step_terminator_preserves_fields >> strip_tac >>
      Cases_on `opc` >> simp[cf_source_data_def] >> gvs[])
  >> (* Non-terminator: step_inst_preserves_all gives all fields *)
  `Eff_RETURNDATA NOTIN write_effects inst.inst_opcode` by
    (irule eff_returndata_from_memory >> simp[]) >>
  drule_all step_inst_preserves_all >> strip_tac >>
  Cases_on `opc` >> simp[cf_source_data_def]
QED



(* Case 4 helper: instruction has no memory/alloca/ext-call effect.
   Memory preserved + non-output variables preserved → pruned lattice sound. *)
Triviality cft_case4[local]:
  !bp dfg ctx fuel run_ctx v inst s s'.
    ctx.ce_bp = bp /\ ctx.ce_dfg = dfg /\
    cf_sound_opt bp dfg v s /\
    step_inst fuel run_ctx inst s = OK s' /\
    ~is_copy_opcode inst.inst_opcode /\
    inst.inst_opcode <> MSTORE /\
    Eff_MEMORY NOTIN write_effects inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    cf_sound_opt bp dfg
      (SOME (copy_fact_prune_vars ctx.ce_dfg (set (inst_defs inst))
               (unwrap_copy_facts v))) s'
Proof
  rpt strip_tac >>
  simp[cf_sound_opt_def] >>
  Cases_on `v` >> fs[cf_sound_opt_def, unwrap_copy_facts_def]
  >- simp[copy_fact_prune_vars_def, DRESTRICT_FEMPTY, cf_sound_def]
  >>
  irule cf_sound_prune_preserved >> qexists_tac `s` >> fs[] >>
  (* Memory preservation: terminators don't touch memory either *)
  `s'.vs_memory = s.vs_memory` by (
    Cases_on `is_terminator inst.inst_opcode`
    >- metis_tac[step_terminator_preserves_fields]
    >> metis_tac[step_inst_no_memory_write_preserves_memory,
                 not_invoke_if_no_mem_effect]) >>
  `inst.inst_opcode <> INVOKE` by metis_tac[not_invoke_if_no_mem_effect] >>
  `s'.vs_allocas = s.vs_allocas` by metis_tac[step_inst_non_alloca_preserves_allocas] >>
  `s'.vs_labels = s.vs_labels` by (
    Cases_on `is_terminator inst.inst_opcode`
    >- (imp_res_tac venomExecPropsTheory.step_inst_preserves_labels_always >>
        gvs[])
    >> metis_tac[venomInstPropsTheory.step_preserves_labels]) >>
  `!opc. cf_source_data opc s' = cf_source_data opc s` by
    (irule step_preserves_cf_source_data >> metis_tac[]) >>
  simp[] >>
  rpt strip_tac >>
  irule step_preserves_unkilled_vars >> metis_tac[]
QED

(* ===== Memory write / disjoint read helpers ===== *)

(* word_to_bytes of a bytes32 has length 32 *)
Theorem word_to_bytes32_length[local,simp]:
  !v:bytes32. LENGTH (word_to_bytes v T) = 32
Proof
  simp[byteTheory.LENGTH_word_to_bytes]
QED

(* Reading a disjoint region after write_memory_with_expansion is unchanged.
   Key property: if [off, off+n) doesn't overlap [d, d+len) and is within
   the original memory, then TAKE n (DROP off mem') = TAKE n (DROP off mem). *)
(* Padded read as GENLIST of mem_byte_at *)
Triviality take_drop_pad_as_genlist[local]:
  !mem:(word8 list) off n.
    TAKE n (DROP off mem ++ REPLICATE n 0w) =
    GENLIST (\i. mem_byte_at mem (off + i)) n
Proof
  rpt gen_tac >>
  simp[LIST_EQ_REWRITE, LENGTH_TAKE_EQ, LENGTH_GENLIST,
       EL_TAKE, EL_GENLIST, EL_APPEND_EQN, EL_DROP,
       LENGTH_DROP, LENGTH_APPEND,
       rich_listTheory.LENGTH_REPLICATE,
       rich_listTheory.EL_REPLICATE,
       allocaRemapDefsTheory.mem_byte_at_def] >>
  rpt strip_tac >>
  `(x < LENGTH mem - off) = (off + x < LENGTH mem)` by simp[] >>
  simp[]
QED

(* Padded variant: no off + n ≤ LENGTH mem requirement.
   Works because wmwe expansion uses 0w, matching REPLICATE 0w. *)
Triviality wmwe_disjoint_read_padded[local]:
  !off n d (bytes:word8 list) s.
    regions_disjoint (off, n) (d, LENGTH bytes) ==>
    TAKE n (DROP off (write_memory_with_expansion d bytes s).vs_memory ++
            REPLICATE n 0w) =
    TAKE n (DROP off s.vs_memory ++ REPLICATE n 0w)
Proof
  rpt strip_tac >>
  Cases_on `off + n <= LENGTH s.vs_memory`
  >- (
    (* Case 1: In-bounds. Strip padding via TAKE_APPEND1, use wmwe_disjoint_read. *)
    `n <= LENGTH (DROP off s.vs_memory)` by simp[LENGTH_DROP] >>
    `LENGTH s.vs_memory <= LENGTH (write_memory_with_expansion d bytes s).vs_memory` by
      (irule write_memory_with_expansion_nondecreasing) >>
    `n <= LENGTH (DROP off (write_memory_with_expansion d bytes s).vs_memory)` by
      simp[LENGTH_DROP] >>
    simp[TAKE_APPEND1] >>
    irule write_memory_with_expansion_regions_disjoint_read >> simp[])
  >>
  (* Case 2: OOB. Element-wise. *)
  suspend "oob"
QED

Resume wmwe_disjoint_read_padded[oob]:
  simp[take_drop_pad_as_genlist] >>
  simp[LIST_EQ_REWRITE, LENGTH_GENLIST, EL_GENLIST] >>
  rpt strip_tac >>
  irule copyFwdEquivTheory.wmwe_byte_at_outside >>
  gvs[regions_disjoint_def]
QED

Finalise wmwe_disjoint_read_padded

(* List helper: reading back the middle segment of a spliced list *)
Triviality take_drop_splice[local]:
  !m (Y:'a list) X Z. m <= LENGTH X ==>
    TAKE (LENGTH Y) (DROP m (TAKE m X ++ Y ++ Z)) = Y
Proof
  rpt strip_tac >>
  `TAKE m X ++ Y ++ Z = TAKE m X ++ (Y ++ Z)` by simp[] >>
  pop_assum SUBST1_TAC >>
  `DROP m (TAKE m X ++ (Y ++ Z)) = DROP m (TAKE m X) ++ (Y ++ Z)` by
    (irule DROP_APPEND1 >> simp[LENGTH_TAKE]) >>
  pop_assum SUBST1_TAC >>
  simp[rich_listTheory.DROP_TAKE_EQ_NIL, rich_listTheory.TAKE_LENGTH_APPEND]
QED

(* write_memory_with_expansion only changes vs_memory. *)
Triviality memloc_runtime_region_wmwe[local,simp]:
  !ml off bytes s.
    memloc_runtime_region ml (write_memory_with_expansion off bytes s) =
    memloc_runtime_region ml s
Proof
  rw[memloc_runtime_region_def, write_memory_with_expansion_def, LET_THM]
QED

(* ml_is_fixed forces sz = Lit n, and THE ml_size = w2n of evaluated sz *)
Triviality ml_is_fixed_eval_size[local]:
  !bp dst sz s sz_val.
    ml_is_fixed (ce_memloc_from_ops bp dst sz) /\
    eval_operand sz s = SOME sz_val ==>
    THE (ce_memloc_from_ops bp dst sz).ml_size = w2n sz_val
Proof
  rpt strip_tac >>
  Cases_on `sz` >>
  gvs[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
      ml_is_fixed_def, ml_undefined_def, eval_operand_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality cf_source_data_wmwe[local]:
  !opc off bytes s. opc <> MCOPY ==>
    cf_source_data opc (write_memory_with_expansion off bytes s) =
    cf_source_data opc s
Proof
  Cases >> simp[cf_source_data_def, write_memory_with_expansion_def, LET_THM]
QED

(* cf_entry_sound preserved across state transition s → s' when:
   - eval_operand for source unchanged
   - allocas unchanged
   - memory didn't shrink
   - dest region bytes preserved
   - source data slice preserved (handles MCOPY where source = memory)
   - source data didn't shrink *)
Triviality cf_entry_sound_transfer[local]:
  !bp dfg ml cf s s'.
    cf_entry_sound bp dfg ml cf s /\
    eval_operand (normalize_operand dfg [] cf.cf_source) s' =
    eval_operand (normalize_operand dfg [] cf.cf_source) s /\
    LENGTH s'.vs_memory >= LENGTH s.vs_memory /\
    s'.vs_allocas = s.vs_allocas /\
    (case memloc_runtime_region ml s of
       SOME (dst_off, sz_num) =>
         !src_val. eval_operand (normalize_operand dfg [] cf.cf_source) s = SOME src_val ==>
           TAKE sz_num (DROP dst_off s'.vs_memory) =
           TAKE sz_num (DROP dst_off s.vs_memory) /\
           (cf.cf_opcode = RETURNDATACOPY ==>
            w2n src_val + sz_num <= LENGTH (cf_source_data cf.cf_opcode s')) /\
           TAKE sz_num (DROP (w2n src_val) (cf_source_data cf.cf_opcode s') ++
                        REPLICATE sz_num 0w) =
           TAKE sz_num (DROP (w2n src_val) (cf_source_data cf.cf_opcode s) ++
                        REPLICATE sz_num 0w)
     | NONE => T) ==>
    cf_entry_sound bp dfg ml cf s'
Proof
  rw[cf_entry_sound_def, memloc_runtime_region_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* step_inst for MSTORE gives mstore *)
Triviality step_mstore_eq[local]:
  !fuel ctx inst s s'.
    inst.inst_opcode = MSTORE /\
    step_inst fuel ctx inst s = OK s' ==>
    ?addr val_op.
      inst.inst_operands = [addr; val_op] /\
      ?a v. eval_operand addr s = SOME a /\
            eval_operand val_op s = SOME v /\
            s' = mstore (w2n a) v s
Proof
  rpt strip_tac >>
  gvs[Once step_inst_def] >>
  gvs[step_inst_base_def, exec_write2_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* Memory doesn't shrink after mstore *)
(* ===== MSTORE transfer case ===== *)

(* For MSTORE with literal destination operand Lit n:
   bp_get_write_location returns ml_offset = SOME (w2n n), ml_size = SOME 32,
   ml_alloca = NONE, matching the runtime write destination exactly. *)
Triviality bp_write_loc_mstore_lit[local]:
  !bp inst n val_op.
    inst.inst_opcode = MSTORE /\
    inst.inst_operands = [Lit n; val_op] ==>
    bp_get_write_location bp inst AddrSp_Memory =
    <| ml_offset := SOME (w2n n); ml_size := SOME 32;
       ml_alloca := NONE; ml_volatile := F |>
Proof
  rw[bp_get_write_location_def, mem_write_ops_def, bp_segment_from_ops_def,
     LET_THM, is_alloca_op_def, is_raw_fmp_opcode_def,
     venomEffectsTheory.write_effects_def] >>
  simp[wordsTheory.dimword_def]
QED

(* Helper: ¬may_overlap with known offsets/sizes/alloca → arithmetic disjointness *)
Triviality not_overlap_disjoint[local]:
  !loc1 loc2 o1 s1 o2 s2.
    ~may_overlap loc1 loc2 /\
    loc1.ml_offset = SOME o1 /\ loc1.ml_size = SOME s1 /\
    loc2.ml_offset = SOME o2 /\ loc2.ml_size = SOME s2 /\
    loc1.ml_alloca = loc2.ml_alloca ==>
    (s1 = 0 \/ s2 = 0 \/ o1 + s1 <= o2 \/ o2 + s2 <= o1)
Proof
  rw[may_overlap_def] >> BasicProvers.every_case_tac >> gvs[LET_THM]
QED



(* ce_memloc_from_ops: size field depends only on sz, not on the offset operand.
   Label produces ml_undefined with ml_size=NONE, so excluded. *)
Triviality ce_memloc_size_same[local]:
  !bp op1 op2 (sz:operand).
    (!l. op1 <> Label l) /\ (!l. op2 <> Label l) ==>
    (ce_memloc_from_ops bp op1 sz).ml_size = (ce_memloc_from_ops bp op2 sz).ml_size
Proof
  rw[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM] >>
  Cases_on `op1` >> Cases_on `op2` >> gvs[] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* cf_key_size_ok when both key and value use same size and non-Label offsets *)
Triviality cf_key_size_ok_same_sz[local]:
  !bp dst src opc sz.
    (!l. dst <> Label l) /\ (!l. src <> Label l) ==>
    cf_key_size_ok bp (ce_memloc_from_ops bp dst sz)
      <| cf_opcode := opc; cf_source := src; cf_size := sz |>
Proof
  rw[cf_key_size_ok_def] >> irule ce_memloc_size_same >> simp[]
QED

(* --- Simp rules: mstore only changes vs_memory --- *)

Triviality memloc_runtime_region_mstore[local,simp]:
  !ml addr_w v' s.
    memloc_runtime_region ml (mstore addr_w v' s) =
    memloc_runtime_region ml s
Proof
  rw[memloc_runtime_region_def, mstore_def, LET_THM]
QED

Triviality eval_operand_mstore[local,simp]:
  !op addr_w v' s.
    eval_operand op (mstore addr_w v' s) = eval_operand op s
Proof
  Cases >> rw[eval_operand_def, lookup_var_def, mstore_def, LET_THM]
QED

Triviality cf_source_data_mstore[local,simp]:
  !opc addr_w v' s.
    opc <> MCOPY ==>
    cf_source_data opc (mstore addr_w v' s) = cf_source_data opc s
Proof
  Cases >> rw[cf_source_data_def, mstore_def, LET_THM]
QED

(* General per-entry soundness preservation after write_memory_with_expansion.
   Takes regions_disjoint as input — caller derives it from
   may_overlap (Lit case) or ma_may_alias_sound_proof (Var case).
   For MCOPY entries, source region disjointness also required.
   Generalises to any write (MSTORE, MCOPY, CALLDATACOPY, etc). *)
Triviality cf_entry_sound_wmwe[local]:
  !bp dfg write_off (bytes:word8 list) s ml cf.
    cf_entry_sound bp dfg ml cf s /\
    (case memloc_runtime_region ml s of
       SOME (addr_ml, sz_ml) =>
         regions_disjoint (addr_ml, sz_ml) (write_off, LENGTH bytes) /\
         (cf.cf_opcode = MCOPY ==>
          !src_val.
            eval_operand (normalize_operand dfg [] cf.cf_source) s =
              SOME src_val ==>
            regions_disjoint (w2n src_val, sz_ml) (write_off, LENGTH bytes))
     | NONE => T) ==>
    cf_entry_sound bp dfg ml cf (write_memory_with_expansion write_off bytes s)
Proof
  rpt strip_tac >>
  simp[cf_entry_sound_def] >>
  fs[cf_entry_sound_def] >>
  Cases_on `memloc_runtime_region ml s` >> gvs[] >>
  PairCases_on `x` >> gvs[LET_THM] >>
  rename1 `SOME (addr_ml, sz_ml)` >>
  mp_tac (Q.SPECL [`write_off`, `bytes`, `s`] write_memory_with_expansion_nondecreasing) >>
  strip_tac >>
  rpt conj_tac
  >- suspend "mem_len"
  >- suspend "src_len"
  >> suspend "bytes_eq"
QED

Resume cf_entry_sound_wmwe[mem_len]:
  simp[]
QED

Resume cf_entry_sound_wmwe[src_len]:
  strip_tac >>
  Cases_on `cf.cf_opcode = MCOPY`
  >- gvs[cf_source_data_def]
  >> simp[cf_source_data_wmwe]
QED

Resume cf_entry_sound_wmwe[bytes_eq]:
  (* Chain: LHS = TAKE(DROP dst new_mem) = TAKE(DROP dst old_mem) [wmwe_disjoint_read]
                = TAKE(DROP src old_src_data ++ REPLICATE 0w)     [assumption]
                = TAKE(DROP src new_src_data ++ REPLICATE 0w)     [src unchanged or padded_read] *)
  `TAKE sz_ml (DROP addr_ml
     (write_memory_with_expansion write_off bytes s).vs_memory) =
   TAKE sz_ml (DROP addr_ml s.vs_memory)` by (
    irule write_memory_with_expansion_regions_disjoint_read >> simp[]) >>
  simp[] >>
  Cases_on `cf.cf_opcode = MCOPY`
  >- (gvs[cf_source_data_def] >>
      CONV_TAC SYM_CONV >> irule wmwe_disjoint_read_padded >> simp[])
  >> simp[cf_source_data_wmwe]
QED

Finalise cf_entry_sound_wmwe;

(* cft_mstore_entry: specialisation for mstore (32-byte write) *)
Triviality cft_mstore_entry[local]:
  !bp dfg addr_w v' s ml cf.
    cf_entry_sound bp dfg ml cf s /\
    (case memloc_runtime_region ml s of
       SOME (addr_ml, sz_ml) =>
         regions_disjoint (addr_ml, sz_ml) (addr_w, 32) /\
         (cf.cf_opcode = MCOPY ==>
          !src_val.
            eval_operand (normalize_operand dfg [] cf.cf_source) s =
              SOME src_val ==>
            regions_disjoint (w2n src_val, sz_ml) (addr_w, 32))
     | NONE => T) ==>
    cf_entry_sound bp dfg ml cf (mstore addr_w v' s)
Proof
  rpt strip_tac >> simp[mstore_eq_write_mem] >>
  irule cf_entry_sound_wmwe >> simp[word_to_bytes32_length]
QED


(* For non-Lit operands, ce_memloc_from_ops always produces a mem_loc
   that may_overlap any alloca=NONE fixed-size write location, because
   the result has either ml_offset=NONE or ml_alloca=SOME. *)
Triviality ce_memloc_var_overlaps[local]:
  !bp v sz wloc.
    wloc.ml_alloca = NONE /\ IS_SOME wloc.ml_offset /\
    wloc.ml_size <> SOME 0 /\
    (ce_memloc_from_ops bp (Var v) sz).ml_size <> SOME 0 ==>
    may_overlap (ce_memloc_from_ops bp (Var v) sz) wloc
Proof
  rw[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
     may_overlap_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

Triviality ce_memloc_label_overlaps[local]:
  !bp l sz wloc.
    wloc.ml_alloca = NONE /\ IS_SOME wloc.ml_offset /\
    wloc.ml_size <> SOME 0 ==>
    may_overlap (ce_memloc_from_ops bp (Label l) sz) wloc
Proof
  simp[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
       may_overlap_def, ml_undefined_def]
QED

(* Lit-case MCOPY source: ¬may_overlap (src_ml) (wl_lit) →
   regions_disjoint (w2n src_val, sz) (w2n n, 32).
   For Var/Label sources, ¬may_overlap contradicts ce_memloc_var/label_overlaps. *)
Triviality mcopy_src_not_overlap_disjoint_lit[local]:
  !bp dfg ml cf s (n:bytes32).
    cf_entry_sound bp dfg ml cf s /\
    cf.cf_opcode = MCOPY /\
    ~may_overlap (ce_memloc_from_ops bp cf.cf_source cf.cf_size)
      <| ml_offset := SOME (w2n n); ml_size := SOME 32;
         ml_alloca := NONE; ml_volatile := F |> /\
    (ce_memloc_from_ops bp cf.cf_source cf.cf_size).ml_size = ml.ml_size ==>
    case memloc_runtime_region ml s of
      SOME (addr_ml, sz_ml) =>
        !src_val.
          eval_operand (normalize_operand dfg [] cf.cf_source) s = SOME src_val ==>
          regions_disjoint (w2n src_val, sz_ml) (w2n n, 32)
    | NONE => T
Proof
  rpt strip_tac >>
  Cases_on `memloc_runtime_region ml s` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  rpt strip_tac >>
  rename1 `memloc_runtime_region ml s = SOME (addr_ml, sz_ml)` >>
  (* sz_ml comes from ml.ml_size via memloc_runtime_region *)
  `sz_ml = THE ml.ml_size` by (
    fs[memloc_runtime_region_def] >>
    BasicProvers.every_case_tac >> gvs[]) >>
  (* MCOPY source must be Lit (Var/Label contradict ¬may_overlap) *)
  Cases_on `cf.cf_source`
  >- ((* Lit k: src_val = k, get arithmetic from may_overlap *)
      gvs[normalize_operand_def, eval_operand_def,
          ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
          may_overlap_def, regions_disjoint_def] >>
      BasicProvers.every_case_tac >> gvs[])
  >- ((* Var: contradicts ¬may_overlap, or sz_ml=0 trivial *)
      Cases_on `ml.ml_size = SOME 0`
      >- (gvs[] >> fs[memloc_runtime_region_def] >>
          BasicProvers.every_case_tac >> gvs[regions_disjoint_def])
      >> `may_overlap (ce_memloc_from_ops bp (Var s') cf.cf_size)
           <|ml_offset := SOME (w2n n); ml_size := SOME 32;
             ml_alloca := NONE; ml_volatile := F|>` suffices_by gvs[] >>
      irule ce_memloc_var_overlaps >> gvs[])
  >> (* Label: contradicts ¬may_overlap *)
  `may_overlap (ce_memloc_from_ops bp (Label s') cf.cf_size)
    <|ml_offset := SOME (w2n n); ml_size := SOME 32;
      ml_alloca := NONE; ml_volatile := F|>` suffices_by gvs[] >>
  irule ce_memloc_label_overlaps >> simp[]
QED

(* MSTORE Lit case: surviving entries after alias-based invalidation. *)
Triviality cft_mstore_lit[local]:
  !bp dfg ctx fuel run_ctx v inst s (n:bytes32) val_op val_v.
    wf_alias_sets ctx.ce_aliases /\
    cf_sound_opt bp dfg v s /\
    cf_keys_ok_opt bp v /\
    inst.inst_opcode = MSTORE /\
    inst.inst_operands = [Lit n; val_op] /\
    eval_operand val_op s = SOME val_v ==>
    cf_sound_opt bp dfg
      (SOME (copy_fact_invalidate ctx.ce_aliases bp
               (unwrap_copy_facts v)
               (bp_get_write_location bp inst AddrSp_Memory)))
      (mstore (w2n n) val_v s)
Proof
  rpt strip_tac >>
  (* Unfold to get DRESTRICT form *)
  simp[copy_fact_invalidate_def, cf_sound_opt_def,
       bp_get_write_location_def, mem_write_ops_def, LET_THM,
       write_effects_def, is_alloca_op_def, is_raw_fmp_opcode_def,
       bp_segment_from_ops_def, ml_is_fixed_def] >>
  simp[cf_sound_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  Cases_on `v` >> gvs[cf_sound_opt_def, cf_sound_def, unwrap_copy_facts_def] >>
  first_x_assum drule >> strip_tac >>
  gvs[memAliasProofsTheory.ma_may_alias_iff] >>
  `32 MOD dimword(:256) = 32` by simp[wordsTheory.dimword_def] >> gvs[] >>
  qabbrev_tac `wl_lit = <| ml_offset := SOME (w2n n); ml_size := SOME 32;
    ml_alloca := NONE; ml_volatile := F |>` >>
  (* Apply general per-entry lemma *)
  irule cft_mstore_entry >> simp[] >>
  (* Case on memloc_runtime_region for disjointness *)
  Cases_on `memloc_runtime_region ml s` >> simp[] >>
  rename1 `SOME p` >> PairCases_on `p` >> simp[] >>
  conj_tac
  >- ((* Dest disjointness from ¬may_overlap *)
      simp[regions_disjoint_def] >>
      fs[memloc_runtime_region_def] >>
      BasicProvers.every_case_tac >> gvs[] >>
      fs[Abbr `wl_lit`, may_overlap_def, LET_THM] >> gvs[])
  >>
  (* MCOPY source disjointness *)
  rpt strip_tac >>
  `cf_key_size_ok bp ml cf` by (
    fs[cf_keys_ok_opt_def, cf_keys_ok_def] >> res_tac) >>
  mp_tac mcopy_src_not_overlap_disjoint_lit >>
  disch_then (qspecl_then [`bp`,`dfg`,`ml`,`cf`,`s`,`n`] mp_tac) >>
  simp[Abbr `wl_lit`] >> fs[cf_key_size_ok_def]
QED


Triviality ce_memloc_var_ml_size[local,simp]:
  THE (ce_memloc_from_ops bp (Var v) (Lit 32w)).ml_size = 32
Proof
  simp[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
       bp_ptr_from_op_def] >>
  BasicProvers.every_case_tac >> simp[Once wordsTheory.dimword_def]
QED

(* For Var write location: ml_is_fixed → IS_SOME ml_alloca *)
Triviality ce_memloc_var_has_alloca[local]:
  ml_is_fixed (ce_memloc_from_ops bp (Var v) sz) ==>
  IS_SOME (ce_memloc_from_ops bp (Var v) sz).ml_alloca
Proof
  simp[ml_is_fixed_def, ce_memloc_from_ops_def, bp_segment_from_ops_def,
       bp_ptr_from_op_def, LET_THM] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* For Var write location with runtime region: addr < dimword *)
Triviality ce_memloc_var_addr_in_word[local]:
  !bp v sz s addr.
    ml_is_fixed (ce_memloc_from_ops bp (Var v) sz) /\
    memloc_runtime_region (ce_memloc_from_ops bp (Var v) sz) s =
      SOME (addr, THE (ce_memloc_from_ops bp (Var v) sz).ml_size) /\
    allocas_in_word s /\
    memloc_within_alloca (ce_memloc_from_ops bp (Var v) sz) s ==>
    addr < dimword(:256)
Proof
  rpt strip_tac >>
  `addr + THE (ce_memloc_from_ops bp (Var v) sz).ml_size < dimword(:256)`
    suffices_by simp[] >>
  irule runtime_region_in_word >>
  qexistsl [`ce_memloc_from_ops bp (Var v) sz`, `s`] >> simp[] >>
  irule ce_memloc_var_has_alloca >> metis_tac[]
QED

(* memloc_runtime_region SOME → ml_size = SOME sz *)
Triviality memloc_runtime_size[local]:
  !ml s addr sz.
    memloc_runtime_region ml s = SOME (addr, sz) ==> ml.ml_size = SOME sz
Proof
  rw[memloc_runtime_region_def] >>
  BasicProvers.every_case_tac >> gvs[]
QED

(* MCOPY source disjointness from non-aliasing.
   Given a copy fact entry for an MCOPY: the source memloc doesn't alias
   a write location wl → the source runtime region (w2n src_val, sz_ml)
   is disjoint from wl's runtime region. Bridges normalize_operand eval
   to memloc_runtime_region via dfg_assigns_sound. *)
Triviality mcopy_source_disjoint[local]:
  !bp dfg aliases ml cf s wl addr_ml sz_ml addr_w sz_w.
    cf.cf_opcode = MCOPY /\
    wf_alias_sets aliases /\
    cf_entry_sound bp dfg ml cf s /\
    cf_key_size_ok bp ml cf /\
    ml_is_fixed (ce_memloc_from_ops bp cf.cf_source cf.cf_size) /\
    memloc_within_alloca (ce_memloc_from_ops bp cf.cf_source cf.cf_size) s /\
    dfg_assigns_sound dfg s /\
    bp_ptr_sound bp s /\
    allocas_in_word s /\
    allocas_non_overlapping s /\
    memloc_within_alloca wl s /\
    memloc_runtime_region ml s = SOME (addr_ml, sz_ml) /\
    memloc_runtime_region wl s = SOME (addr_w, sz_w) /\
    ~ma_may_alias aliases (ce_memloc_from_ops bp cf.cf_source cf.cf_size) wl ==>
    !src_val.
      eval_operand (normalize_operand dfg [] cf.cf_source) s = SOME src_val ==>
      regions_disjoint (w2n src_val, sz_ml) (addr_w, sz_w)
Proof
  rpt strip_tac >>
  (* normalize → raw eval *)
  mp_tac normalize_operand_eval >>
  disch_then (qspecl_then [`dfg`, `[]`, `cf.cf_source`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  (* source memloc runtime region = (w2n src_val, sz_ml) *)
  mp_tac (Q.SPECL [`bp`, `cf.cf_source`, `cf.cf_size`, `s`, `src_val`]
            ce_memloc_runtime_w2n) >>
  simp[] >> strip_tac >>
  mp_tac memloc_runtime_size >>
  disch_then (qspecl_then [`ml`, `s`, `addr_ml`, `sz_ml`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[cf_key_size_ok_def] >>
  qpat_x_assum `SOME _ = _.ml_size` (SUBST_ALL_TAC o GSYM) >>
  gvs[] >>
  drule_all ma_may_alias_sound_proof >> simp[]
QED

(* General: surviving entries in copy_fact_invalidate remain sound after
   any write_memory_with_expansion at wl's runtime address.
   Generalises cft_mstore_var to arbitrary write sizes. *)
Triviality cft_invalidate_sound_wmwe[local]:
  !bp dfg aliases v wl addr_w sz_w (data:word8 list) s.
    wf_alias_sets aliases /\
    cf_sound_opt bp dfg v s /\
    cf_keys_ok_opt bp v /\
    cf_alloca_ok bp (unwrap_copy_facts v) s /\
    dfg_assigns_sound dfg s /\
    allocas_non_overlapping s /\
    allocas_in_word s /\
    bp_ptr_sound bp s /\
    memloc_within_alloca wl s /\
    memloc_runtime_region wl s = SOME (addr_w, sz_w) /\
    LENGTH data = sz_w ==>
    cf_sound_opt bp dfg
      (SOME (DRESTRICT (unwrap_copy_facts v)
         {k | ~ma_may_alias aliases k wl /\
              (case FLOOKUP (unwrap_copy_facts v) k of
                 NONE => T
               | SOME cf => cf.cf_opcode = MCOPY ==>
                   ~ma_may_alias aliases
                     (ce_memloc_from_ops bp cf.cf_source cf.cf_size) wl)}))
      (write_memory_with_expansion addr_w data s)
Proof
  rpt strip_tac >>
  simp[cf_sound_opt_def, cf_sound_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >>
  Cases_on `v` >> gvs[cf_sound_opt_def, cf_sound_def, unwrap_copy_facts_def] >>
  first_x_assum drule >> strip_tac >>
  irule cf_entry_sound_wmwe >> simp[] >>
  Cases_on `memloc_runtime_region ml s` >> simp[] >>
  rename1 `SOME p` >> PairCases_on `p` >> simp[] >>
  rename1 `memloc_runtime_region ml s = SOME (addr_ml, sz_ml)` >>
  `memloc_within_alloca ml s` by (fs[cf_alloca_ok_def] >> res_tac) >>
  conj_tac
  >- (irule ma_may_alias_sound_proof >>
      qexistsl [`ml`, `wl`, `s`, `aliases`] >> simp[])
  >> strip_tac >>
  mp_tac mcopy_source_disjoint >>
  disch_then (qspecl_then [`bp`,`dfg`,`aliases`,`ml`,`cf`,`s`,`wl`,
                            `addr_ml`,`sz_ml`,`addr_w`,`LENGTH data`] mp_tac) >>
  simp[] >> (impl_tac >- (
    gvs[cf_keys_ok_opt_def, cf_keys_ok_def] >>
    first_x_assum drule >> strip_tac >> simp[] >>
    gvs[cf_alloca_ok_def] >> res_tac)) >>
  simp[]
QED

(* MSTORE Var case: surviving entries sound after mstore at Var addr.
   Thin wrapper around cft_invalidate_sound_wmwe for 32-byte writes. *)
Triviality cft_mstore_var[local]:
  !bp dfg aliases v addr_w val_v wl s.
    wf_alias_sets aliases /\
    cf_sound_opt bp dfg v s /\
    cf_keys_ok_opt bp v /\
    cf_alloca_ok bp (unwrap_copy_facts v) s /\
    dfg_assigns_sound dfg s /\
    allocas_non_overlapping s /\
    allocas_in_word s /\
    bp_ptr_sound bp s /\
    memloc_within_alloca wl s /\
    memloc_runtime_region wl s = SOME (addr_w, 32) ==>
    cf_sound_opt bp dfg
      (SOME (DRESTRICT (unwrap_copy_facts v)
         {k | ~ma_may_alias aliases k wl /\
              (case FLOOKUP (unwrap_copy_facts v) k of
                 NONE => T
               | SOME cf => cf.cf_opcode = MCOPY ==>
                   ~ma_may_alias aliases
                     (ce_memloc_from_ops bp cf.cf_source cf.cf_size) wl)}))
      (mstore addr_w val_v s)
Proof
  rpt strip_tac >> simp[mstore_eq_write_mem] >>
  irule cft_invalidate_sound_wmwe >> simp[word_to_bytes32_length]
QED

Triviality cft_mstore[local]:
  !bp dfg ctx fuel run_ctx v inst s s'.
    ctx.ce_bp = bp /\ ctx.ce_dfg = dfg /\
    wf_alias_sets ctx.ce_aliases /\
    cf_sound_opt bp dfg v s /\
    cf_keys_ok_opt bp v /\
    cf_alloca_ok bp (unwrap_copy_facts v) s /\
    dfg_assigns_sound dfg s /\
    allocas_non_overlapping s /\
    allocas_in_word s /\
    bp_ptr_sound bp s /\
    memloc_within_alloca (bp_get_write_location bp inst AddrSp_Memory) s /\
    step_inst fuel run_ctx inst s = OK s' /\
    inst.inst_opcode = MSTORE ==>
    cf_sound_opt bp dfg
      (SOME (copy_fact_invalidate ctx.ce_aliases ctx.ce_bp
               (unwrap_copy_facts v)
               (bp_get_write_location ctx.ce_bp inst AddrSp_Memory))) s'
Proof
  rpt strip_tac >> gvs[] >>
  drule_all step_mstore_eq >> strip_tac >> gvs[] >>
  rename1 `inst.inst_operands = [addr_op; val_op]` >>
  rename1 `eval_operand addr_op s = SOME a` >>
  rename1 `eval_operand val_op s = SOME val_v` >>
  Cases_on `addr_op`
  >- ((* Lit n *)
      gvs[eval_operand_def] >>
      irule cft_mstore_lit >> metis_tac[])
  >- suspend "var_case"
  >> (* Label: ml_undefined → unfixed → FEMPTY *)
  simp[bp_get_write_location_def, mem_write_ops_def, LET_THM,
       write_effects_def, is_alloca_op_def,
       bp_segment_from_ops_def, ml_undefined_def, ml_is_fixed_def,
       copy_fact_invalidate_def] >>
  Cases_on `v` >> gvs[cf_sound_opt_def, cf_sound_def, unwrap_copy_facts_def]
QED

Resume cft_mstore[var_case]:
  simp[bp_get_write_location_def, mem_write_ops_def, LET_THM,
       write_effects_def, is_alloca_op_def, is_raw_fmp_opcode_def,
       copy_fact_invalidate_def] >>
  IF_CASES_TAC
  >- simp[cf_sound_opt_def, cf_sound_def] >>
  fs[] >>
  (* fold bp_segment_from_ops → ce_memloc_from_ops in goal+asms *)
  once_rewrite_tac [GSYM ce_memloc_from_ops_def] >>
  (* get runtime region *)
  mp_tac (Q.SPECL [`ctx.ce_bp`, `Var s'`, `Lit 32w`, `s`]
    ce_memloc_runtime_region) >>
  (impl_tac >- simp[ce_memloc_from_ops_def]) >>
  strip_tac >>
  (* addr < dimword via ce_memloc_var_addr_in_word *)
  `addr < dimword (:256)` by (
    mp_tac (Q.SPECL [`ctx.ce_bp`, `s'`, `Lit 32w`, `s`, `addr`]
      ce_memloc_var_addr_in_word) >>
    simp[ce_memloc_from_ops_def] >>
    qpat_x_assum `memloc_within_alloca _ s` mp_tac >>
    simp[bp_get_write_location_def, mem_write_ops_def, LET_THM,
         write_effects_def, is_alloca_op_def, is_raw_fmp_opcode_def,
         ce_memloc_from_ops_def]) >>
  gvs[] >>
  irule cft_mstore_var >> simp[] >>
  qpat_x_assum `memloc_within_alloca _ s` mp_tac >>
  simp[ce_memloc_from_ops_def,
       bp_get_write_location_def, mem_write_ops_def, LET_THM,
       write_effects_def, is_alloca_op_def, is_raw_fmp_opcode_def]
QED

Finalise cft_mstore

(* cf_keys_ok preserved by copy_fact_invalidate *)
Triviality cf_keys_ok_invalidate[local]:
  !bp aliases cfl wl.
    cf_keys_ok bp cfl ==>
    cf_keys_ok bp (copy_fact_invalidate aliases bp cfl wl)
Proof
  rw[copy_fact_invalidate_def]
  >- simp[cf_keys_ok_fempty]
  >> irule cf_keys_ok_drestrict >> simp[]
QED

(* For is_copy opcodes with 3 operands, bp_get_write_location = ce_memloc_from_ops *)
Triviality is_copy_write_loc_eq[local]:
  !bp inst dst src sz.
    is_copy_opcode inst.inst_opcode /\
    inst.inst_operands = [dst; src; sz] ==>
    bp_get_write_location bp inst AddrSp_Memory =
    ce_memloc_from_ops bp dst sz
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_copy_opcode_def, bp_get_write_location_def,
      ce_memloc_from_ops_def, write_effects_def, mem_write_ops_def,
      is_alloca_op_def, is_raw_fmp_opcode_def]
QED

(* bp_ptrs_bounded gives memloc_within_alloca for write locations.
   For non-INVOKE, non-DLOAD memory writers, bp_get_write_location =
   bp_segment_from_ops (mem_write_ops inst). bp_ptrs_bounded covers
   the IS_SOME ml_alloca case; NONE alloca is vacuously within_alloca. *)
Triviality bp_ptrs_bounded_write_loc[local]:
  !bp fn s bb inst.
    bp_ptrs_bounded bp fn s /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode <> DLOAD /\ inst.inst_opcode <> INVOKE /\
    ~is_raw_fmp_opcode inst.inst_opcode /\
    Eff_MEMORY IN write_effects inst.inst_opcode ==>
    memloc_within_alloca (bp_get_write_location bp inst AddrSp_Memory) s
Proof
  rw[bp_ptrs_bounded_def, bp_get_write_location_def] >>
  Cases_on `mem_write_ops inst`
  >- simp[ml_undefined_def, memloc_within_alloca_def]
  >> simp[] >>
     Cases_on `IS_SOME (bp_segment_from_ops bp x).ml_alloca`
     >- (first_x_assum irule >> metis_tac[])
     >> gvs[quantHeuristicsTheory.IS_SOME_EQ_NOT_NONE,
            memloc_within_alloca_def] >>
        Cases_on `(bp_segment_from_ops bp x).ml_offset` >> simp[] >>
        Cases_on `(bp_segment_from_ops bp x).ml_size` >> simp[]
QED

Theorem copy_fact_transfer_sound_thm:
  !bp dfg ctx fn.
    ctx.ce_bp = bp /\ ctx.ce_dfg = dfg /\
    wf_alias_sets ctx.ce_aliases /\
    bp_assigns_stable bp dfg ==>
    transfer_sound_block_inv
      (\v s. cf_sound_opt bp dfg v s /\ cf_keys_ok_opt bp v /\
             cf_alloca_ok_opt bp v s)
      (\s. dfg_assigns_sound dfg s /\ bp_ptr_sound bp s /\
           allocas_non_overlapping s /\
           allocas_in_word s /\ bp_ptrs_bounded bp fn s)
      copy_fact_transfer ctx fn
Proof
  rpt strip_tac >> gvs[] >>
  rewrite_tac[transfer_sound_block_inv_def] >>
  simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  simp[copy_fact_transfer_def, LET_THM] >>
  IF_CASES_TAC
  >- suspend "is_copy"
  >> IF_CASES_TAC
  >- suspend "mstore"
  >> IF_CASES_TAC
  >- suspend "volatile"
  >> suspend "no_mem_effect"
QED

(* --- Case: volatile/alloca/ext-call → FEMPTY --- *)
Resume copy_fact_transfer_sound_thm[volatile]:
  simp[cf_sound_opt_def, cf_sound_def, cf_keys_ok_opt_def,
       cf_keys_ok_fempty, cf_alloca_ok_opt_def, cf_alloca_ok_fempty]
QED

(* --- Case: no memory effect → copy_fact_prune_vars --- *)
Resume copy_fact_transfer_sound_thm[no_mem_effect]:
  `Eff_MEMORY NOTIN write_effects inst.inst_opcode` by gvs[] >>
  `~is_alloca_op inst.inst_opcode` by gvs[] >>
  `~is_ext_call_op inst.inst_opcode` by gvs[] >>
  `inst.inst_opcode <> INVOKE` by metis_tac[not_invoke_if_no_mem_effect] >>
  `s'.vs_allocas = s.vs_allocas` by
    (irule step_inst_non_alloca_preserves_allocas >> metis_tac[]) >>
  (* cf_sound_opt: from cft_case4 *)
  conj_asm1_tac
  >- (irule cft_case4 >> metis_tac[])
  >> conj_tac
  >- (* cf_keys_ok: prune is DRESTRICT *)
     (simp[cf_keys_ok_opt_def, copy_fact_prune_vars_def] >>
      Cases_on `v` >> gvs[cf_keys_ok_opt_def, unwrap_copy_facts_def]
      >- simp[DRESTRICT_FEMPTY, cf_keys_ok_fempty]
      >> irule cf_keys_ok_drestrict >> simp[])
  >> (* cf_alloca_ok: prune is DRESTRICT, allocas preserved *)
     simp[cf_alloca_ok_opt_def, copy_fact_prune_vars_def] >>
     Cases_on `v` >> gvs[cf_alloca_ok_opt_def, unwrap_copy_facts_def]
     >- simp[DRESTRICT_FEMPTY, cf_alloca_ok_fempty]
     >> irule (iffLR cf_alloca_ok_allocas_eq) >> qexists `s` >> simp[] >>
        irule cf_alloca_ok_drestrict >> simp[]
QED

(* --- Case: MSTORE → copy_fact_invalidate --- *)
(* Derive inst_idx-free forms, then apply cft_mstore + cf_keys_ok_invalidate +
   cf_alloca_ok_drestrict + allocas_eq. *)
Resume copy_fact_transfer_sound_thm[mstore]:
  rpt conj_tac
  >- suspend "mst_sound"
  >- suspend "mst_keys"
  >> suspend "mst_alloca"
QED

Resume copy_fact_transfer_sound_thm[mst_sound]:
  `bp_ptr_sound ctx.ce_bp s` by gvs[] >>
  `allocas_non_overlapping s` by gvs[] >>
  `allocas_in_word s` by gvs[] >>
  `bp_ptrs_bounded ctx.ce_bp fn s` by gvs[] >>
  `memloc_within_alloca
     (bp_get_write_location ctx.ce_bp inst AddrSp_Memory) s` by (
    mp_tac bp_ptrs_bounded_write_loc >>
    disch_then (qspecl_then [`ctx.ce_bp`,`fn`,`s`,`bb`,`inst`] mp_tac) >>
    gvs[write_effects_def, opcode2num_thm, is_raw_fmp_opcode_def]) >>
  irule cft_mstore >> simp[] >>
  qexistsl [`fuel`, `run_ctx`, `s`] >>
  Cases_on `v` >>
  gvs[cf_alloca_ok_opt_def, unwrap_copy_facts_def, cf_alloca_ok_fempty]
QED

Resume copy_fact_transfer_sound_thm[mst_keys]:
  simp[cf_keys_ok_opt_def] >>
  irule cf_keys_ok_invalidate >>
  Cases_on `v` >> gvs[cf_keys_ok_opt_def, unwrap_copy_facts_def, cf_keys_ok_fempty]
QED

Resume copy_fact_transfer_sound_thm[mst_alloca]:
  `s'.vs_allocas = s.vs_allocas` by (
    mp_tac step_inst_non_alloca_preserves_allocas >>
    disch_then (qspecl_then [`fuel`,`run_ctx`,`inst`,`s`,`s'`] mp_tac) >>
    gvs[is_alloca_op_def, opcode2num_thm]) >>
  simp[cf_alloca_ok_opt_def, copy_fact_invalidate_def] >>
  IF_CASES_TAC >> simp[cf_alloca_ok_fempty] >>
  irule cf_alloca_ok_drestrict_step >> qexists `s` >>
  Cases_on `v` >> gvs[cf_alloca_ok_opt_def, unwrap_copy_facts_def,
                       cf_alloca_ok_fempty]
QED

(* --- Case: is_copy_opcode --- *)
Resume copy_fact_transfer_sound_thm[is_copy]:
  (* Derive inst_idx-free forms *)
  `bp_ptr_sound ctx.ce_bp s` by gvs[] >>
  `allocas_non_overlapping s` by gvs[] >>
  `allocas_in_word s` by gvs[] >>
  `bp_ptrs_bounded ctx.ce_bp fn s` by gvs[] >>
  (* Case split on operand shape *)
  Cases_on `inst.inst_operands`
  >- simp[cf_sound_opt_def, cf_sound_def, cf_keys_ok_opt_def,
          cf_keys_ok_fempty, cf_alloca_ok_opt_def, cf_alloca_ok_fempty] >>
  Cases_on `t`
  >- simp[cf_sound_opt_def, cf_sound_def, cf_keys_ok_opt_def,
          cf_keys_ok_fempty, cf_alloca_ok_opt_def, cf_alloca_ok_fempty] >>
  Cases_on `t'`
  >- simp[cf_sound_opt_def, cf_sound_def, cf_keys_ok_opt_def,
          cf_keys_ok_fempty, cf_alloca_ok_opt_def, cf_alloca_ok_fempty] >>
  Cases_on `t`
  >- (rename1 `inst.inst_operands = [dst; src; sz]` >>
      simp[] >> pairarg_tac >> gvs[] >>
      (* Shared setup for all is_copy subcases *)
      qabbrev_tac `write_loc = ce_memloc_from_ops ctx.ce_bp dst sz` >>
      drule_all step_is_copy_eq_wmwe >> strip_tac >>
      rename1 `eval_operand dst s = SOME dst_val` >>
      rename1 `eval_operand src s = SOME src_val` >>
      rename1 `eval_operand sz s = SOME sz_val` >>
      qpat_x_assum `s' = _` SUBST_ALL_TAC >>
      `memloc_within_alloca write_loc s` by (
        `bp_get_write_location ctx.ce_bp inst AddrSp_Memory = write_loc` by
          (simp[Abbr `write_loc`] >> irule is_copy_write_loc_eq >> simp[]) >>
        mp_tac bp_ptrs_bounded_write_loc >>
        disch_then (qspecl_then [`ctx.ce_bp`,`fn`,`s`,`bb`,`inst`] mp_tac) >>
        (impl_tac >- (
          simp[] >> Cases_on `inst.inst_opcode` >>
          gvs[is_copy_opcode_def, opcode2num_thm, write_effects_def,
              is_raw_fmp_opcode_def])) >>
        simp[]) >>
      mp_tac (Q.SPECL [`ctx.ce_bp`, `dst`, `sz`, `s`, `dst_val`]
                ce_memloc_runtime_w2n) >>
      simp[Abbr `write_loc`] >> strip_tac >>
      qabbrev_tac `write_loc = ce_memloc_from_ops ctx.ce_bp dst sz` >>
      (* Case: redundant MCOPY? *)
      IF_CASES_TAC
      >- suspend "redundant"
      >> (* Non-redundant: has FUPDATE or just invalidation *)
      IF_CASES_TAC
      >- suspend "fupdate"
      >> suspend "no_fupdate")
  >> (* 4+ operands → FEMPTY *)
  simp[cf_sound_opt_def, cf_sound_def, cf_keys_ok_opt_def,
       cf_keys_ok_fempty, cf_alloca_ok_opt_def, cf_alloca_ok_fempty]
QED

Resume copy_fact_transfer_sound_thm[redundant]:
  (* Shared setup already derived: write_loc, dst_val, src_val, sz_val,
     memloc_within_alloca, runtime_region. *)
  gvs[] >> (* inst.inst_opcode = MCOPY from redundancy *)
  Cases_on `FLOOKUP (unwrap_copy_facts v) write_loc` >> gvs[] >>
  rename1 `FLOOKUP (unwrap_copy_facts v) write_loc = SOME cf` >>
  (* Derive ml_is_fixed from cf_keys_ok *)
  `ml_is_fixed write_loc` by (
    Cases_on `v` >>
    gvs[cf_keys_ok_opt_def, unwrap_copy_facts_def, cf_keys_ok_def] >>
    res_tac) >>
  qabbrev_tac `sz_num = THE write_loc.ml_size` >>
  (* Get cf_entry_sound for the existing entry *)
  `cf_entry_sound ctx.ce_bp ctx.ce_dfg write_loc cf s` by
    metis_tac[cf_sound_opt_entry] >>
  (* From operand_equiv: eval(normalize cf.cf_source) = eval src = SOME src_val *)
  `eval_operand (normalize_operand ctx.ce_dfg [] cf.cf_source) s = SOME src_val` by (
    mp_tac (Q.SPECL [`ctx.ce_dfg`, `cf.cf_source`, `src`, `s`]
              operand_equiv_norm_eval) >> simp[]) >>
  (* Unfold cf_entry_sound: since runtime_region = SOME, get byte equality *)
  gvs[cf_entry_sound_def, cf_source_data_def] >>
  (* sz_val = n2w sz_num: ml_is_fixed forces sz = Lit *)
  `w2n sz_val = sz_num` by (
    simp[Abbr `sz_num`, Abbr `write_loc`] >>
    Cases_on `sz` >>
    gvs[ce_memloc_from_ops_def, bp_segment_from_ops_def, LET_THM,
        ml_is_fixed_def, ml_undefined_def, eval_operand_def] >>
    BasicProvers.every_case_tac >> gvs[]) >>
  gvs[] >>
  (* Show the wmwe is identity: data = existing dest bytes *)
  `write_memory_with_expansion (w2n dst_val)
     (TAKE (w2n sz_val)
        (DROP (w2n src_val) s.vs_memory ++ REPLICATE (w2n sz_val) 0w))
     s = s` by (
    irule write_memory_with_expansion_identity >>
    simp[LENGTH_TAKE_EQ, rich_listTheory.LENGTH_REPLICATE]) >>
  gvs[] >>
  (* v = SOME cfl (since FLOOKUP found something) *)
  Cases_on `v` >>
  gvs[cf_sound_opt_def, cf_keys_ok_opt_def, cf_alloca_ok_opt_def,
      unwrap_copy_facts_def]
QED

Resume copy_fact_transfer_sound_thm[fupdate]:
  (* Shared setup already derived: write_loc, dst_val, src_val, sz_val,
     memloc_within_alloca, runtime_region. *)
  rpt conj_tac
  >- suspend "fu_sound"
  >- suspend "fu_keys"
  >> suspend "fu_alloca"
QED

Resume copy_fact_transfer_sound_thm[no_fupdate]:
  rpt conj_tac
  >- suspend "nf_sound"
  >- suspend "nf_keys"
  >> suspend "nf_alloca"
QED

Resume copy_fact_transfer_sound_thm[nf_sound]:
  Cases_on `ml_is_fixed write_loc`
  >- ((* ml_is_fixed: invalidation preserves soundness *)
      simp[copy_fact_invalidate_def, LET_THM] >>
      irule cft_invalidate_sound_wmwe >> simp[] >>
      conj_tac
      >- (mp_tac (Q.SPECL [`ctx.ce_bp`, `dst`, `sz`, `s`, `sz_val`]
                    ml_is_fixed_eval_size) >>
          simp[Abbr `write_loc`]) >>
      Cases_on `v` >>
      gvs[cf_alloca_ok_opt_def, unwrap_copy_facts_def, cf_alloca_ok_fempty])
  >> (* ¬ml_is_fixed: copy_fact_invalidate = FEMPTY *)
  simp[copy_fact_invalidate_def, cf_sound_opt_def, cf_sound_def]
QED

Resume copy_fact_transfer_sound_thm[nf_keys]:
  simp[cf_keys_ok_opt_def] >>
  irule cf_keys_ok_invalidate >>
  Cases_on `v` >>
  gvs[cf_keys_ok_opt_def, unwrap_copy_facts_def, cf_keys_ok_fempty]
QED

Resume copy_fact_transfer_sound_thm[nf_alloca]:
  (* wmwe_vs_allocas[simp] handles allocas preservation automatically *)
  simp[cf_alloca_ok_opt_def, copy_fact_invalidate_def] >>
  IF_CASES_TAC >> simp[cf_alloca_ok_fempty] >>
  irule cf_alloca_ok_drestrict_step >> qexists `s` >>
  Cases_on `v` >>
  gvs[cf_alloca_ok_opt_def, unwrap_copy_facts_def, cf_alloca_ok_fempty]
QED

Resume copy_fact_transfer_sound_thm[fu_keys]:
  simp[cf_keys_ok_opt_def] >>
  irule cf_keys_ok_fupdate >> simp[] >>
  conj_tac
  >- (irule cf_keys_ok_invalidate >>
      Cases_on `v` >>
      gvs[cf_keys_ok_opt_def, unwrap_copy_facts_def, cf_keys_ok_fempty])
  >> simp[Abbr `write_loc`] >>
  irule cf_key_size_ok_same_sz >> gvs[] >>
  metis_tac[ce_memloc_fixed_not_label]
QED

Resume copy_fact_transfer_sound_thm[fu_alloca]:
  irule cf_alloca_ok_opt_invalidate_fupdate_step >> qexists `s` >> simp[] >>
  strip_tac >>
  qpat_x_assum `copy_fact_resolve _ _ _ _ _ _ = _` mp_tac >>
  simp[copy_fact_resolve_def] >>
  IF_CASES_TAC
  >- ((* inst.inst_opcode = MCOPY *)
      CASE_TAC
      >- ((* FLOOKUP = NONE: final_src = src *)
          strip_tac >> gvs[] >>
          irule bp_ptrs_bounded_mcopy_read_loc >> metis_tac[])
      >> ((* FLOOKUP = SOME: forwarding *)
          simp[LET_THM] >> strip_tac >> gvs[] >>
          suspend "fwd_alloca"))
  >- ((* inst.inst_opcode ≠ MCOPY *)
      strip_tac >> gvs[])
QED

Resume copy_fact_transfer_sound_thm[fwd_alloca]:
  (* Extract cf_keys_ok and cf_alloca_ok from opt wrappers *)
  rename1 `FLOOKUP _ _ = SOME src_cf` >>
  `cf_keys_ok ctx.ce_bp (unwrap_copy_facts v)` by
    (irule cf_keys_ok_opt_unwrap >> simp[]) >>
  `cf_alloca_ok ctx.ce_bp (unwrap_copy_facts v) s` by
    (Cases_on `v` >>
     gvs[cf_alloca_ok_opt_def, unwrap_copy_facts_def, cf_alloca_ok_fempty]) >>
  (* Extract all per-entry facts in one shot *)
  drule_all cf_entry_facts_from_flookup >> strip_tac >>
  gvs[] >>  (* src_cf.cf_opcode = MCOPY → discharge implication *)
  (* memloc_within_alloca (ce_memloc bp src_cf.cf_source src_cf.cf_size) s *)
  (* normalize preserves memloc_within_alloca *)
  `memloc_within_alloca
     (ce_memloc_from_ops ctx.ce_bp
        (normalize_operand ctx.ce_dfg [] src_cf.cf_source)
        src_cf.cf_size) s` by
    (irule memloc_within_alloca_normalize >> simp[]) >>
  (* change_sz from src_cf.cf_size to sz *)
  irule (iffRL memloc_within_alloca_change_sz) >>
  qexists `src_cf.cf_size` >> simp[] >>
  (* Need: (ce_memloc bp (norm src_cf.cf_source) sz).ml_size =
           (ce_memloc bp (norm src_cf.cf_source) src_cf.cf_size).ml_size *)
  (* Both use same non-Label op, so ml_size depends only on sz operand *)
  `!l. src_cf.cf_source <> Label l` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`, `src_cf.cf_source`, `src_cf.cf_size`]
               ce_memloc_fixed_not_label) >> simp[]) >>
  simp[ce_memloc_ml_size_only_sz] >>
  (* Now need: case sz = case src_cf.cf_size (both produce same ml_size) *)
  (* From cf_key_size_ok: (ce_memloc bp src sz).ml_size =
                           (ce_memloc bp src_cf.cf_source src_cf.cf_size).ml_size *)
  `!l. src <> Label l` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`, `src`, `sz`]
               ce_memloc_fixed_not_label) >> simp[]) >>
  gvs[cf_key_size_ok_def, ce_memloc_ml_size_only_sz]
QED

(* LENGTH of the TAKE/DROP/REPLICATE bytes used in MCOPY *)
Triviality mcopy_bytes_length[local]:
  !src sz mem. LENGTH (TAKE sz (DROP src mem ++ REPLICATE sz 0w)) = sz
Proof
  simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP,
       rich_listTheory.LENGTH_REPLICATE]
QED

Resume copy_fact_transfer_sound_thm[fu_sound]:
  (* Abbreviate for readability *)
  qabbrev_tac `s' = write_memory_with_expansion (w2n dst_val)
    (TAKE (w2n sz_val)
       (DROP (w2n src_val) (cf_source_data inst.inst_opcode s) ++
        REPLICATE (w2n sz_val) 0w)) s` >>
  qabbrev_tac `bytes = TAKE (w2n sz_val)
    (DROP (w2n src_val) (cf_source_data inst.inst_opcode s) ++
     REPLICATE (w2n sz_val) 0w)` >>
  (* Get MAP-level soundness of inval via cft_invalidate_sound_wmwe *)
  `cf_alloca_ok ctx.ce_bp (unwrap_copy_facts v) s` by
    (irule cf_alloca_ok_opt_unwrap >> simp[]) >>
  `memloc_runtime_region write_loc s = SOME (w2n dst_val, THE write_loc.ml_size)`
    by simp[] >>
  suspend "inval_sound"
QED

Resume copy_fact_transfer_sound_thm[inval_sound]:
  qspecl_then [`ctx.ce_bp`, `ctx.ce_dfg`, `ctx.ce_aliases`, `v`,
               `write_loc`, `w2n dst_val`, `w2n sz_val`,
               `bytes`, `s`] mp_tac cft_invalidate_sound_wmwe >>
  (impl_tac >- suspend "discharge_cft") >>
  strip_tac >>
  suspend "use_cft"
QED

Resume copy_fact_transfer_sound_thm[discharge_cft]:
  simp[Abbr `bytes`, mcopy_bytes_length, Abbr `write_loc`] >>
  gvs[] >> metis_tac[ml_is_fixed_eval_size, cf_alloca_ok_opt_unwrap]
QED

Resume copy_fact_transfer_sound_thm[use_cft]:
  (* Unfold cf_sound_opt on goal (FUPDATE). *)
  simp[cf_sound_opt_def, cf_sound_def, FLOOKUP_UPDATE,
       copy_fact_invalidate_def, Abbr `s'`, Abbr `bytes`] >>
  rpt strip_tac >> Cases_on `write_loc = ml` >> gvs[]
  >- suspend "new_entry"
  >> ((* ml ≠ write_loc: surviving — inval soundness closes it *)
      qpat_x_assum `cf_sound_opt _ _ (SOME (DRESTRICT _ _)) _` mp_tac >>
      simp[cf_sound_opt_def, cf_sound_def])
QED

Resume copy_fact_transfer_sound_thm[new_entry]:
  (* Goal: cf_entry_sound ... ml new_cf (wmwe dst_val bytes s)
     where new_cf = <|cf_opcode := final_op; cf_source := final_src; cf_size := sz|>
     Unfold cf_entry_sound, use wmwe-simp lemmas for runtime_region and eval *)
  simp[cf_entry_sound_def] >>
  (* memloc_runtime_region ml (wmwe ...) = memloc_runtime_region ml s = SOME (...) *)
  (* After simp, goal should be ∃src_val. eval ... = SOME src_val ∧ bounds ∧ byte_eq *)
  (* Case split on copy_fact_resolve to determine final_op/final_src *)
  qpat_x_assum `copy_fact_resolve _ _ _ _ _ _ = _` mp_tac >>
  simp[copy_fact_resolve_def, LET_THM] >>
  Cases_on `inst.inst_opcode = MCOPY` >> simp[]
  >- ((* MCOPY: further split on FLOOKUP *)
      Cases_on `FLOOKUP (unwrap_copy_facts v) (ce_memloc_from_ops ctx.ce_bp src sz)`
      >> simp[]
      >- ((* FLOOKUP = NONE: case 2 — MCOPY no forwarding *)
          strip_tac >> gvs[] >>
          suspend "case_mcopy_nofwd")
      >> ((* FLOOKUP = SOME: case 3 — MCOPY with forwarding *)
          rename1 `FLOOKUP _ _ = SOME src_cf` >>
          strip_tac >> gvs[] >>
          suspend "case_mcopy_fwd"))
  >> ((* non-MCOPY: case 1 *)
      strip_tac >> gvs[] >>
      suspend "case_non_mcopy")
QED

Resume copy_fact_transfer_sound_thm[case_non_mcopy]:
  suspend "non_mcopy_body"
QED

Resume copy_fact_transfer_sound_thm[non_mcopy_body]:
  qexists `src_val` >>
  `eval_operand (normalize_operand ctx.ce_dfg [] final_src) s = SOME src_val` by
    metis_tac[normalize_operand_eval] >>
  `THE ml.ml_size = w2n sz_val` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`, `dst`, `sz`, `s`, `sz_val`]
              ml_is_fixed_eval_size) >>
     simp[Abbr `ml`]) >>
  simp[] >>
  rpt conj_tac
  >- suspend "nm_memlen"
  >- suspend "nm_rdc"
  >> suspend "nm_bytes"
QED

Resume copy_fact_transfer_sound_thm[nm_memlen]:
  `LENGTH (TAKE (w2n sz_val) (DROP (w2n src_val)
      (cf_source_data inst.inst_opcode s) ++ REPLICATE (w2n sz_val) 0w)) =
   w2n sz_val` by simp[LENGTH_TAKE_EQ, rich_listTheory.LENGTH_REPLICATE] >>
  metis_tac[copyFwdEquivTheory.wmwe_length, arithmeticTheory.GREATER_EQ]
QED

Resume copy_fact_transfer_sound_thm[nm_rdc]:
  strip_tac >> simp[cf_source_data_wmwe] >>
  drule_all step_copy_rdc_bound >> simp[]
QED

Resume copy_fact_transfer_sound_thm[nm_bytes]:
  qabbrev_tac `bytes = TAKE (w2n sz_val) (DROP (w2n src_val)
     (cf_source_data inst.inst_opcode s) ++ REPLICATE (w2n sz_val) 0w)` >>
  `LENGTH bytes = w2n sz_val` by
    simp[Abbr `bytes`, LENGTH_TAKE_EQ, rich_listTheory.LENGTH_REPLICATE] >>
  metis_tac[write_memory_with_expansion_read_self, cf_source_data_wmwe]
QED

Resume copy_fact_transfer_sound_thm[case_mcopy_nofwd]:
  suspend "nofwd_body"
QED

Resume copy_fact_transfer_sound_thm[nofwd_body]:
  qexists `src_val` >>
  `eval_operand (normalize_operand ctx.ce_dfg [] final_src) s = SOME src_val` by
    metis_tac[normalize_operand_eval] >>
  `THE ml.ml_size = w2n sz_val` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`, `dst`, `sz`, `s`, `sz_val`]
              ml_is_fixed_eval_size) >>
     simp[Abbr `ml`]) >>
  simp[] >>
  (* MCOPY ≠ RETURNDATACOPY so rdc_bound simplified away, only 2 conjuncts *)
  conj_tac
  >- suspend "nofwd_memlen"
  >> suspend "nofwd_bytes"
QED

Resume copy_fact_transfer_sound_thm[nofwd_memlen]:
  `LENGTH (TAKE (w2n sz_val) (DROP (w2n src_val)
      (cf_source_data MCOPY s) ++ REPLICATE (w2n sz_val) 0w)) =
   w2n sz_val` by simp[LENGTH_TAKE_EQ, rich_listTheory.LENGTH_REPLICATE] >>
  metis_tac[copyFwdEquivTheory.wmwe_length, arithmeticTheory.GREATER_EQ]
QED

Resume copy_fact_transfer_sound_thm[nofwd_bytes]:
  (* cf_source_data MCOPY s = s.vs_memory *)
  simp[cf_source_data_def] >>
  qabbrev_tac `bytes = TAKE (w2n sz_val) (DROP (w2n src_val) s.vs_memory ++
     REPLICATE (w2n sz_val) 0w)` >>
  `LENGTH bytes = w2n sz_val` by
    simp[Abbr `bytes`, LENGTH_TAKE_EQ, rich_listTheory.LENGTH_REPLICATE] >>
  (* LHS = bytes by write_memory_with_expansion_read_self *)
  `TAKE (w2n sz_val) (DROP (w2n dst_val)
     (write_memory_with_expansion (w2n dst_val) bytes s).vs_memory) = bytes` by
    metis_tac[write_memory_with_expansion_read_self] >>
  (* RHS: need source disjoint from dest to show old bytes = new bytes *)
  `memloc_within_alloca (ce_memloc_from_ops ctx.ce_bp final_src sz) s` by
    metis_tac[bp_ptrs_bounded_mcopy_read_loc] >>
  `THE (ce_memloc_from_ops ctx.ce_bp final_src sz).ml_size = w2n sz_val` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`, `final_src`, `sz`, `s`, `sz_val`]
              ml_is_fixed_eval_size) >> simp[]) >>
  `memloc_runtime_region (ce_memloc_from_ops ctx.ce_bp final_src sz) s =
     SOME (w2n src_val, w2n sz_val)` by
    (drule_all ce_memloc_runtime_w2n >> simp[]) >>
  `regions_disjoint (w2n dst_val, w2n sz_val) (w2n src_val, w2n sz_val)` by
    metis_tac[ma_may_alias_sound_proof] >>
  (* RHS = bytes by wmwe_disjoint_read_padded *)
  `TAKE (w2n sz_val) (DROP (w2n src_val)
     (write_memory_with_expansion (w2n dst_val) bytes s).vs_memory ++
     REPLICATE (w2n sz_val) 0w) =
   TAKE (w2n sz_val) (DROP (w2n src_val) s.vs_memory ++
     REPLICATE (w2n sz_val) 0w)` by
    (irule wmwe_disjoint_read_padded >>
     gvs[regions_disjoint_def]) >>
  simp[Abbr `bytes`]
QED

Resume copy_fact_transfer_sound_thm[case_mcopy_fwd]:
  suspend "fwd_body"
QED

Resume copy_fact_transfer_sound_thm[fwd_body]:
  (* Extract old entry's cf_entry_sound at source location *)
  `cf_keys_ok ctx.ce_bp (unwrap_copy_facts v)` by
    metis_tac[cf_keys_ok_opt_unwrap] >>
  `ml_is_fixed (ce_memloc_from_ops ctx.ce_bp src sz) /\
   memloc_within_alloca (ce_memloc_from_ops ctx.ce_bp src sz) s` by
    metis_tac[cf_entry_facts_from_flookup] >>
  `THE (ce_memloc_from_ops ctx.ce_bp src sz).ml_size = w2n sz_val` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`, `src`, `sz`, `s`, `sz_val`]
              ml_is_fixed_eval_size) >> simp[]) >>
  `memloc_runtime_region (ce_memloc_from_ops ctx.ce_bp src sz) s =
     SOME (w2n src_val, w2n sz_val)` by
    (drule_all ce_memloc_runtime_w2n >> simp[]) >>
  `cf_entry_sound ctx.ce_bp ctx.ce_dfg (ce_memloc_from_ops ctx.ce_bp src sz)
     src_cf s` by
    metis_tac[cf_sound_opt_entry] >>
  (* Unpack old entry's cf_entry_sound *)
  pop_assum mp_tac >> simp[cf_entry_sound_def] >>
  strip_tac >> rename1 `eval_operand _ s = SOME old_src_val` >>
  (* Witness: eval chain normalize → normalize → ... gives old_src_val *)
  qexists `old_src_val` >>
  `eval_operand (normalize_operand ctx.ce_dfg []
     (normalize_operand ctx.ce_dfg [] src_cf.cf_source)) s =
     SOME old_src_val` by
    metis_tac[normalize_operand_eval] >>
  `THE ml.ml_size = w2n sz_val` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`, `dst`, `sz`, `s`, `sz_val`]
              ml_is_fixed_eval_size) >>
     simp[Abbr `ml`]) >>
  simp[] >>
  (* 3 conjuncts (or 2 if rdc simplified): memlen, [rdc,] bytes *)
  rpt conj_tac
  >- suspend "fwd_memlen"
  >- suspend "fwd_rest"
  >> suspend "fwd_rest2"
QED

Resume copy_fact_transfer_sound_thm[fwd_memlen]:
  `LENGTH (TAKE (w2n sz_val) (DROP (w2n src_val)
      (cf_source_data MCOPY s) ++ REPLICATE (w2n sz_val) 0w)) =
   w2n sz_val` by simp[LENGTH_TAKE_EQ, rich_listTheory.LENGTH_REPLICATE] >>
  metis_tac[copyFwdEquivTheory.wmwe_length, arithmeticTheory.GREATER_EQ]
QED

Resume copy_fact_transfer_sound_thm[fwd_rest]:
  strip_tac >> simp[cf_source_data_wmwe] >>
  gvs[]
QED

Resume copy_fact_transfer_sound_thm[fwd_rest2]:
  suspend "fwd_bytes_setup"
QED

(* Abbreviate bytes, establish write_memory_with_expansion_read_self, reduce to old entry *)
Resume copy_fact_transfer_sound_thm[fwd_bytes_setup]:
  qabbrev_tac `bytes = TAKE (w2n sz_val) (DROP (w2n src_val)
     (cf_source_data MCOPY s) ++ REPLICATE (w2n sz_val) 0w)` >>
  `LENGTH bytes = w2n sz_val` by
    simp[Abbr `bytes`, LENGTH_TAKE_EQ, rich_listTheory.LENGTH_REPLICATE] >>
  (* LHS = bytes by write_memory_with_expansion_read_self *)
  `TAKE (w2n sz_val) (DROP (w2n dst_val)
     (write_memory_with_expansion (w2n dst_val) bytes s).vs_memory) = bytes` by
    metis_tac[write_memory_with_expansion_read_self] >>
  (* bytes = TAKE sz (DROP src s.mem) since padding unnecessary *)
  `bytes = TAKE (w2n sz_val) (DROP (w2n src_val) s.vs_memory)` by
    (simp[Abbr `bytes`, cf_source_data_def, TAKE_APPEND1]) >>
  (* Case split on src_cf.cf_opcode = MCOPY *)
  Cases_on `src_cf.cf_opcode = MCOPY`
  >- suspend "fwd_bytes_mcopy"
  >> suspend "fwd_bytes_nonmcopy"
QED

(* Non-MCOPY: cf_source_data unchanged through wmwe *)
Resume copy_fact_transfer_sound_thm[fwd_bytes_nonmcopy]:
  simp[cf_source_data_wmwe]
QED

(* MCOPY: need wmwe_disjoint_read_padded for source region *)
Resume copy_fact_transfer_sound_thm[fwd_bytes_mcopy]:
  gvs[] >>
  `ml_is_fixed (ce_memloc_from_ops ctx.ce_bp
     (normalize_operand ctx.ce_dfg [] src_cf.cf_source) sz)` by gvs[] >>
  `¬ma_may_alias ctx.ce_aliases ml (ce_memloc_from_ops ctx.ce_bp
     (normalize_operand ctx.ce_dfg [] src_cf.cf_source) sz)` by gvs[] >>
  (* Establish eval for single-normalize (needed by ce_memloc_runtime_w2n) *)
  `eval_operand (normalize_operand ctx.ce_dfg [] src_cf.cf_source) s =
     SOME old_src_val` by
    metis_tac[normalize_operand_eval] >>
  (* memloc_within_alloca for source: cf_alloca_ok gives it for
     (src_cf.cf_source, src_cf.cf_size), then change_sz swaps size,
     then normalize handles the normalize_operand *)
  (* Get source within_alloca from cf_entry_facts_from_flookup *)
  `memloc_within_alloca (ce_memloc_from_ops ctx.ce_bp
     src_cf.cf_source src_cf.cf_size) s` by
    (drule_all cf_entry_facts_from_flookup >> simp[]) >>
  suspend "fwd_disjoint"
QED

Resume copy_fact_transfer_sound_thm[fwd_disjoint]:
  suspend "fwd_size_eq"
QED

Resume copy_fact_transfer_sound_thm[fwd_size_eq]:
  (* Goal: padded read from old_src in memory unchanged through wmwe at dst.
     Reason: alias analysis proves source region (old_src, sz) disjoint from
     dest region (dst, sz), so write doesn't affect any byte in read range. *)
  (* Reuse disjointness chain from fwd_disjoint block assumptions:
     Need memloc_within_alloca for (normalize src_cf.cf_source, sz).
     Have within_alloca for (src_cf.cf_source, src_cf.cf_size).
     Chain: change_sz → normalize. *)
  (* Re-derive ml_is_fixed for src_cf source location + cf_key_size_ok *)
  `ml_is_fixed (ce_memloc_from_ops ctx.ce_bp src_cf.cf_source src_cf.cf_size) /\
   cf_key_size_ok ctx.ce_bp (ce_memloc_from_ops ctx.ce_bp src sz) src_cf` by
    (qpat_assum `cf_keys_ok _ _` mp_tac >>
     rewrite_tac[cf_keys_ok_def] >>
     disch_then (qspecl_then [`ce_memloc_from_ops ctx.ce_bp src sz`,
                              `src_cf`] mp_tac) >>
     simp[]) >>
  (* Non-Label exclusion *)
  `!l. src_cf.cf_source <> Label l` by
    metis_tac[ce_memloc_fixed_not_label] >>
  `!l. src <> Label l` by
    metis_tac[ce_memloc_fixed_not_label] >>
  (* Size equality + change_sz *)
  `memloc_within_alloca
     (ce_memloc_from_ops ctx.ce_bp src_cf.cf_source sz) s` by
    (irule (iffRL memloc_within_alloca_change_sz) >>
     qexists `src_cf.cf_size` >> simp[] >>
     simp[ce_memloc_ml_size_only_sz] >>
     gvs[cf_key_size_ok_def, ce_memloc_ml_size_only_sz]) >>
  (* normalize preserves memloc_within_alloca *)
  `memloc_within_alloca
     (ce_memloc_from_ops ctx.ce_bp
        (normalize_operand ctx.ce_dfg [] src_cf.cf_source) sz) s` by
    (irule memloc_within_alloca_normalize >> simp[]) >>
  (* THE ml_size = w2n sz_val *)
  `THE (ce_memloc_from_ops ctx.ce_bp
     (normalize_operand ctx.ce_dfg [] src_cf.cf_source) sz).ml_size =
     w2n sz_val` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`,
       `normalize_operand ctx.ce_dfg [] src_cf.cf_source`,
       `sz`, `s`, `sz_val`] ml_is_fixed_eval_size) >> simp[]) >>
  (* runtime_region for source *)
  `memloc_runtime_region (ce_memloc_from_ops ctx.ce_bp
     (normalize_operand ctx.ce_dfg [] src_cf.cf_source) sz) s =
     SOME (w2n old_src_val, w2n sz_val)` by
    (mp_tac (Q.SPECL [`ctx.ce_bp`,
       `normalize_operand ctx.ce_dfg [] src_cf.cf_source`,
       `sz`, `s`, `old_src_val`] ce_memloc_runtime_w2n) >>
     simp[]) >>
  (* regions_disjoint *)
  `regions_disjoint (w2n dst_val, w2n sz_val)
     (w2n old_src_val, w2n sz_val)` by
    metis_tac[ma_may_alias_sound_proof] >>
  (* cf_source_data MCOPY = vs_memory, then wmwe_disjoint_read_padded *)
  simp[cf_source_data_def] >>
  CONV_TAC SYM_CONV >> irule wmwe_disjoint_read_padded >>
  gvs[regions_disjoint_def]
QED

Finalise copy_fact_transfer_sound_thm
