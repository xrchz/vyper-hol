(*
 * Base Pointer Analysis — Proofs
 *
 * TOP-LEVEL:
 *   bp_handle_inst_other_var_proof       — transfer function frame property
 *   bp_handle_inst_no_output_unchanged_proof — no-output identity
 *   bp_ptr_sound_init_proof               — FEMPTY is trivially sound
 *   bp_handle_inst_sound_proof            — transfer preserves bp_ptr_sound
 *   bp_process_block_sound_proof          — block-level soundness
 *   bp_ptr_from_op_sound_proof            — singleton pointer ⇒ exact address
 *   bp_segment_from_ops_sound_proof       — alloca-backed mem_loc soundness
 *)

Theory basePtrProofs
Ancestors
  basePtrDefs venomExecSemantics venomWf memLocDefs venomInstProofs
  venomInstProofs1 venomExecProofs venomMemProps finite_map list pred_set venomInst

(* Transfer function only modifies the output variable's pointer set. *)
Theorem bp_handle_inst_other_var_proof:
  ∀result inst c r v.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst ≠ SOME v ⇒
    bp_get_ptrs r v = bp_get_ptrs result v
Proof
  rw[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> gvs[LET_THM] >>
  rename1 `SOME out` >>
  Cases_on `inst.inst_opcode` >> gvs[LET_THM, bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE]
QED

(* No-output instructions don't modify the pointer map at all. *)
Theorem bp_handle_inst_no_output_unchanged_proof:
  ∀result inst c r.
    bp_handle_inst result inst = (c, r) ∧
    inst_output inst = NONE ⇒
    r = result
Proof
  rw[bp_handle_inst_def] >>
  Cases_on `inst_output inst` >> gvs[]
QED

(* Initialization: analysis starts from FEMPTY, which is trivially sound. *)
Theorem bp_ptr_sound_init_proof:
  ∀s. bp_ptr_sound FEMPTY s
Proof
  rw[bp_ptr_sound_def, bp_get_ptrs_def, FLOOKUP_DEF]
QED

(* ===================================================================
   Local helpers for soundness proofs
   =================================================================== *)

(* inst_wf + inst_output = SOME out ⇒ inst_outputs = [out] *)
Theorem inst_wf_outputs_some[local]:
  ∀inst out. inst_wf inst ∧ inst_output inst = SOME out ⇒
    inst.inst_outputs = [out]
Proof
  rw[venomInstTheory.inst_output_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

(* is_terminator + inst_wf ⇒ inst_outputs = [] *)
Theorem terminator_no_outputs[local]:
  ∀inst. inst_wf inst ∧ is_terminator inst.inst_opcode ⇒
    inst.inst_outputs = []
Proof
  ACCEPT_TAC venomExecProofsTheory.terminator_no_outputs
QED

(* FOLDL update_var preserves lookup for vars not in output list *)
Theorem foldl_update_var_preserves_lookup[local]:
  ∀kvs s v. ¬MEM v (MAP FST kvs) ⇒
    lookup_var v (FOLDL (λs' (k,v). update_var k v s') s kvs) = lookup_var v s
Proof
  Induct >> simp[pairTheory.FORALL_PROD] >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`update_var p_1 p_2 s`, `v`] mp_tac) >>
  simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
       FLOOKUP_UPDATE]
QED

(* bind_outputs preserves lookup for non-output vars *)
Theorem bind_outputs_preserves_lookup[local]:
  ∀outs vals s s' v.
    bind_outputs outs vals s = SOME s' ∧ ¬MEM v outs ⇒
    lookup_var v s' = lookup_var v s
Proof
  rw[venomExecSemanticsTheory.bind_outputs_def, AllCaseEqs()] >> gvs[] >>
  `MAP FST (ZIP (outs, vals)) = outs` by
    (irule (cj 1 MAP_ZIP) >> gvs[]) >>
  metis_tac[foldl_update_var_preserves_lookup]
QED

(* FOLDL update_var preserves vs_allocas *)
Theorem foldl_update_var_allocas[local]:
  ∀kvs base. (FOLDL (λs' (k,v). update_var k v s') base kvs).vs_allocas =
             base.vs_allocas
Proof
  Induct >> rw[pairTheory.FORALL_PROD] >>
  Cases_on `h` >> rw[venomStateTheory.update_var_def]
QED

(* Non-ALLOCA, non-INVOKE step_inst preserves vs_allocas. *)
Theorem step_inst_allocas[local]:
  ∀fuel ctx inst (s : venom_state) s'.
    step_inst fuel ctx inst s = OK s' ∧
    inst.inst_opcode ≠ ALLOCA ∧
    inst.inst_opcode ≠ INVOKE ⇒
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  `step_inst_base inst s = OK s'` by
    metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
  qspecl_then [`inst`, `s`, `s'`] mp_tac step_inst_base_preserves_allocas >>
  impl_tac >- gvs[] >>
  simp[]
QED

(* step_inst preserves FLOOKUP of alloca ids that aren't the current inst_id.
   Non-ALLOCA: full vs_allocas preservation. ALLOCA: only inst_id changes. *)
Theorem step_inst_alloca_flookup:
  ∀fuel ctx inst (s : venom_state) s' aid.
    step_inst fuel ctx inst s = OK s' ∧
    (inst.inst_opcode = ALLOCA ⇒ aid ≠ inst.inst_id) ⇒
    FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    gvs[Once venomExecSemanticsTheory.step_inst_def, AllCaseEqs()] >>
    qpat_x_assum `bind_outputs _ _ _ = _` mp_tac >>
    simp[venomExecSemanticsTheory.bind_outputs_def, AllCaseEqs()] >>
    strip_tac >> Cases_on `ret.iret_adopt_fmp` >>
    gvs[foldl_update_var_allocas,
      venomExecSemanticsTheory.adopt_return_fmp_def,
      venomExecSemanticsTheory.merge_callee_state_def]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (
    `step_inst_base inst s = OK s'` by
      metis_tac[venomExecSemanticsTheory.step_inst_non_invoke] >>
    gvs[venomExecSemanticsTheory.step_inst_base_def] >>
    gvs[AllCaseEqs(), venomExecSemanticsTheory.exec_alloca_def,
        venomStateTheory.update_var_def, FLOOKUP_UPDATE])
  >>
    `inst.inst_opcode <> INVOKE` by simp[] >>
    drule_all step_inst_allocas >> strip_tac >> ASM_REWRITE_TAC[]
QED

(* For non-output vars, lookup_var is preserved across step_inst = OK.
   Covers all opcodes: terminators (JMP/JNZ/DJMP), INVOKE, and rest. *)
Theorem step_inst_preserves_lookup:
  ∀fuel ctx inst (s : venom_state) s' v.
    step_inst fuel ctx inst s = OK s' ∧
    ¬MEM v inst.inst_outputs ⇒
    lookup_var v s' = lookup_var v s
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* INVOKE: merge_callee_state takes caller vs_vars,
       bind_outputs only writes inst_outputs *)
    gvs[Once venomExecSemanticsTheory.step_inst_def, AllCaseEqs()] >>
    drule bind_outputs_preserves_lookup >>
    disch_then (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
    Cases_on `ret.iret_adopt_fmp` >>
    simp[venomStateTheory.lookup_var_def,
         venomExecSemanticsTheory.adopt_return_fmp_def,
         venomExecSemanticsTheory.merge_callee_state_def]
  ) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `step_inst_base inst s = OK s'` by
      fs[venomExecSemanticsTheory.step_inst_non_invoke] >>
    fs[venomExecSemanticsTheory.step_inst_base_def] >>
    gvs[venomInstTheory.is_terminator_def, AllCaseEqs()] >>
    TRY (pairarg_tac >> gvs[] >>
         drule pack_dret_dynamic_preserves_non_memory >>
         simp[venomStateTheory.lookup_var_def]) >>
    gvs[venomStateTheory.jump_to_def, venomStateTheory.lookup_var_def]
  )
  >- (
    drule_all step_preserves_non_output_vars >> metis_tac[]
  )
QED

(* ptr_matches_var is preserved when allocas and lookup_var are unchanged *)
Theorem ptr_matches_var_preserved:
  ∀p v v' s s'.
    ptr_matches_var p v s ∧
    lookup_var v' s' = lookup_var v s ∧
    (∀aid off. p = Ptr (Allocation aid) off ⇒
       FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) ⇒
    ptr_matches_var p v' s'
Proof
  Cases_on `p` >> rename1 `Ptr alloc off_opt` >>
  Cases_on `alloc` >> Cases_on `off_opt` >>
  rw[ptr_matches_var_def] >> metis_tac[]
QED

(* ptr_matches_var on Allocation gives FLOOKUP ≠ NONE *)
Theorem ptr_matches_var_alloca_exists:
  ∀aid off v s.
    ptr_matches_var (Ptr (Allocation aid) off) v s ⇒
    FLOOKUP s.vs_allocas aid ≠ NONE
Proof
  Cases_on `off` >> rw[ptr_matches_var_def] >> strip_tac >> gvs[]
QED

(* Frame lemma: bp_ptr_sound witness + preservation for unchanged variables. *)
Theorem bp_ptr_sound_frame[local]:
  ∀bp bp' v s s'.
    bp_ptr_sound bp s ∧
    IS_SOME (lookup_var v s') ∧
    bp_get_ptrs bp' v ≠ [] ∧
    bp_get_ptrs bp' v = bp_get_ptrs bp v ∧
    lookup_var v s' = lookup_var v s ∧
    (∀aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) ⇒
    ∃p. MEM p (bp_get_ptrs bp' v) ∧ ptr_matches_var p v s'
Proof
  rpt strip_tac >>
  `bp_get_ptrs bp v ≠ [] ∧ IS_SOME (lookup_var v s)` by gvs[] >>
  `∃p. MEM p (bp_get_ptrs bp v) ∧ ptr_matches_var p v s` by
    (fs[bp_ptr_sound_def]) >>
  qexists_tac `p` >> gvs[] >>
  irule ptr_matches_var_preserved >> qexistsl_tac [`s`, `v`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum irule >> metis_tac[]
QED

(* resolve_phi produces a Var operand that is among phi_pairs *)
Theorem resolve_phi_in_phi_pairs[local]:
  ∀prev ops val_op.
    phi_well_formed ops ∧
    resolve_phi prev ops = SOME val_op ⇒
    ∃v. val_op = Var v ∧ MEM v (MAP SND (phi_pairs ops))
Proof
  gen_tac >>
  ho_match_mp_tac venomWfTheory.phi_well_formed_ind >>
  rw[venomWfTheory.phi_well_formed_def,
     venomExecSemanticsTheory.resolve_phi_def,
     venomInstTheory.phi_pairs_def] >>
  gvs[] >>
  TRY (Cases_on `v3` >>
       gvs[venomInstTheory.phi_pairs_def] >> metis_tac[] >> NO_TAC) >>
  metis_tac[]
QED

(* offset_by preserves the allocation component *)
Theorem offset_by_alloc[local]:
  ∀p delta. ∃alloc off'. offset_by p delta = Ptr alloc off'
Proof
  Cases_on `p` >> Cases_on `o'` >> Cases_on `delta` >>
  rw[offset_by_def]
QED

Theorem sub_offset_by_alloc[local]:
  ∀p delta. ∃alloc off'. sub_offset_by p delta = Ptr alloc off'
Proof
  Cases_on `p` >> Cases_on `o'` >> Cases_on `delta` >>
  rw[sub_offset_by_def] >> BasicProvers.EVERY_CASE_TAC >> rw[]
QED

(* offset_by preserves the allocation ID *)
Theorem offset_by_same_alloc[local]:
  ∀alloc off delta. ∃off'. offset_by (Ptr alloc off) delta = Ptr alloc off'
Proof
  Cases_on `off` >> Cases_on `delta` >> rw[offset_by_def]
QED

Theorem sub_offset_by_same_alloc[local]:
  ∀alloc off delta. ∃off'. sub_offset_by (Ptr alloc off) delta = Ptr alloc off'
Proof
  Cases_on `off` >> Cases_on `delta` >> rw[sub_offset_by_def] >>
  BasicProvers.EVERY_CASE_TAC >> rw[]
QED

(* Any word can be expressed as n2w (base + delta) for some delta.
   Core fact for NONE-offset ptr_matches_var. *)
Theorem word_as_base_offset[local]:
  ∀(w : 256 word) b. ∃delta. w = n2w (b + delta)
Proof
  rpt gen_tac >>
  qexists_tac `w2n (w - n2w b)` >>
  simp[GSYM wordsTheory.word_add_n2w, wordsTheory.n2w_w2n,
       wordsTheory.WORD_SUB_ADD2]
QED

(* Key: if ptr_matches_var p v s, then offset_by p produces a pointer
   that matches any variable whose value is (value of v) + (some word) *)
Theorem offset_by_ptr_matches[local]:
  ∀alloc off v s delta out s'.
    ptr_matches_var (Ptr (Allocation alloc) off) v s ∧
    FLOOKUP s'.vs_allocas alloc = FLOOKUP s.vs_allocas alloc ∧
    lookup_var out s' = SOME (THE (lookup_var v s) + n2w delta) ⇒
    ptr_matches_var (offset_by (Ptr (Allocation alloc) off) (SOME delta)) out s'
Proof
  Cases_on `off` >> rw[offset_by_def, ptr_matches_var_def] >> gvs[] >>
  simp[wordsTheory.word_add_n2w] >> metis_tac[]
QED

Theorem offset_by_none_ptr_matches[local]:
  ∀alloc off v s out s'.
    ptr_matches_var (Ptr (Allocation alloc) off) v s ∧
    FLOOKUP s'.vs_allocas alloc = FLOOKUP s.vs_allocas alloc ∧
    IS_SOME (lookup_var out s') ⇒
    ptr_matches_var (offset_by (Ptr (Allocation alloc) off) NONE) out s'
Proof
  Cases_on `off` >> rw[offset_by_def, ptr_matches_var_def] >>
  gvs[] >>
  Cases_on `lookup_var out s'` >> gvs[] >>
  rename1 `SOME w` >>
  metis_tac[word_as_base_offset]
QED

Theorem sub_offset_by_ptr_matches[local]:
  ∀alloc off v s delta out s'.
    ptr_matches_var (Ptr (Allocation alloc) off) v s ∧
    FLOOKUP s'.vs_allocas alloc = FLOOKUP s.vs_allocas alloc ∧
    lookup_var out s' = SOME (THE (lookup_var v s) - n2w delta) ⇒
    ptr_matches_var (sub_offset_by (Ptr (Allocation alloc) off) (SOME delta)) out s'
Proof
  Cases_on `off` >> rw[sub_offset_by_def, ptr_matches_var_def] >>
  gvs[] >> BasicProvers.EVERY_CASE_TAC >> rw[ptr_matches_var_def] >>
  gvs[] >>
  TRY (metis_tac[word_as_base_offset]) >>
  simp[GSYM wordsTheory.n2w_sub]
QED

(* Given a sound bp, a tracked source variable with FLOOKUP bp src = SOME ptrs,
   and a pointer-transform f, there exists a matching pointer in MAP f ptrs. *)
Theorem bp_ptr_sound_map_witness[local]:
  ∀bp s src f ptrs out s'.
    bp_ptr_sound bp s ∧
    FLOOKUP bp src = SOME ptrs ∧ ptrs ≠ [] ∧
    IS_SOME (lookup_var src s) ∧
    (∀p. MEM p ptrs ∧ ptr_matches_var p src s ⇒
         ptr_matches_var (f p) out s') ⇒
    ∃q. MEM q (MAP f ptrs) ∧ ptr_matches_var q out s'
Proof
  rpt strip_tac >>
  `bp_get_ptrs bp src ≠ []` by simp[bp_get_ptrs_def] >>
  `∃p. MEM p (bp_get_ptrs bp src) ∧ ptr_matches_var p src s` by
    (fs[bp_ptr_sound_def]) >>
  `MEM p ptrs` by gvs[bp_get_ptrs_def] >>
  qexists_tac `f p` >> conj_tac
  >- (simp[MEM_MAP] >> metis_tac[])
  >- (first_x_assum irule >> simp[])
QED

(* ===================================================================
   Soundness of transfer function.

   Alloca condition weakened: only requires preservation for aids already
   in vs_allocas. This supports INVOKE (callee can ADD alloca entries).
   =================================================================== *)

Theorem bp_handle_inst_sound_proof:
  ∀bp inst c bp' fuel ctx s s'.
    bp_ptr_sound bp s ∧
    bp_handle_inst bp inst = (c, bp') ∧
    step_inst fuel ctx inst s = OK s' ∧
    inst_wf inst ∧
    (∀out. inst_output inst = SOME out ⇒ bp_get_ptrs bp out = []) ∧
    (inst_output inst = NONE ⇒ inst.inst_outputs = []) ∧
    (∀v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) ∧
    (∀v. inst.inst_opcode = PHI ∧
         MEM v (MAP SND (phi_pairs inst.inst_operands)) ∧
         IS_SOME (lookup_var v s) ⇒
         bp_get_ptrs bp v ≠ []) ⇒
    bp_ptr_sound bp' s'
Proof
  rpt strip_tac >>
  rw[bp_ptr_sound_def] >> rpt strip_tac >>
  Cases_on `inst_output inst`
  >- (
    (* NONE: bp' = bp unchanged. inst.inst_outputs = [] by precondition. *)
    imp_res_tac bp_handle_inst_no_output_unchanged_proof >> gvs[] >>
    `inst.inst_outputs = []` by metis_tac[] >>
    irule bp_ptr_sound_frame >> simp[] >>
    qexistsl_tac [`bp`, `s`] >> simp[] >>
    (conj_tac >- metis_tac[]) >>
    irule step_inst_preserves_lookup >>
    qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[]
  ) >>
  rename1 `SOME out` >>
  Cases_on `v = out`
  >- (
    (* v = out: new ptrs match the opcode semantics *)
    gvs[] >>
    qpat_x_assum `bp_handle_inst _ _ = _`
      (strip_assume_tac o REWRITE_RULE [bp_handle_inst_def, LET_THM]) >>
    gvs[] >>
    imp_res_tac inst_wf_outputs_some >> gvs[] >>
    Cases_on `inst.inst_opcode` >> gvs[LET_THM, bp_get_ptrs_def, FLOOKUP_UPDATE]
    >~ [`ALLOCA`] >- suspend "alloca"
    >~ [`ADD`] >- suspend "add"
    >~ [`SUB`] >- suspend "sub"
    (* PHI case: auto-solved - bp_handle_inst PHI = (F, result), so bp_get_ptrs bp out = [] makes goal vacuous *)
    >~ [`ASSIGN`] >- suspend "assign"
  )
  >- (
    (* v ≠ out: ptrs unchanged, lookup_var preserved *)
    `bp_get_ptrs bp' v = bp_get_ptrs bp v` by (
      irule bp_handle_inst_other_var_proof >>
      qexistsl_tac [`c`, `inst`] >> simp[]) >>
    irule bp_ptr_sound_frame >> simp[] >>
    qexistsl_tac [`bp`, `s`] >> simp[] >>
    (conj_tac >- metis_tac[]) >>
    irule step_inst_preserves_lookup >>
    qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[] >>
    gvs[venomInstTheory.inst_output_def] >>
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[]
  )
QED

Resume bp_handle_inst_sound_proof[alloca]:
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_alloca_def,
      venomWfTheory.inst_wf_def] >>
  gvs[venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> gvs[] >>
  TRY (Cases_on `x` >> gvs[]) >>
  simp[ptr_from_alloca_def, ptr_matches_var_def, FLOOKUP_UPDATE,
       venomStateTheory.lookup_var_def]
QED

Resume bp_handle_inst_sound_proof[add]:
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_pure2_def, AllCaseEqs(),
      venomWfTheory.inst_wf_def,
      venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
      FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[FLOOKUP_UPDATE] >>
  irule bp_ptr_sound_map_witness >> simp[] >>
  qexistsl_tac [`bp`, `s`] >>
  first_assum (irule_at Any) >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def] >>
  rpt strip_tac >>
  TRY (gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
       >> NO_TAC) >>
  (`∃aid off'. p = Ptr (Allocation aid) off'` by
    (Cases_on `p` >> Cases_on `a` >> metis_tac[])) >> gvs[] >>
  TRY (irule offset_by_ptr_matches) >>
  TRY (irule offset_by_none_ptr_matches) >>
  simp[venomStateTheory.lookup_var_def, FLOOKUP_UPDATE,
       wordsTheory.n2w_w2n] >>
  (* Remaining: ∃s_old v. arith ∧ allocas_eq ∧ ptr_matches_var ... v s_old
     Witness s_old := s; find v from ptr_matches_var assumption *)
  qexists_tac `s` >> first_assum (irule_at (Pos last)) >>
  gvs[venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
      wordsTheory.WORD_ADD_COMM]
QED

Resume bp_handle_inst_sound_proof[sub]:
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_def,
      venomExecSemanticsTheory.exec_pure2_def, AllCaseEqs(),
      venomWfTheory.inst_wf_def,
      venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def,
      FLOOKUP_UPDATE] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[FLOOKUP_UPDATE] >>
  irule bp_ptr_sound_map_witness >> simp[] >>
  qexistsl_tac [`bp`, `s`] >>
  first_assum (irule_at Any) >>
  simp[venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def] >>
  rpt strip_tac >>
  TRY (gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
       >> NO_TAC) >>
  (`∃aid off'. p = Ptr (Allocation aid) off'` by
    (Cases_on `p` >> Cases_on `a` >> metis_tac[])) >> gvs[] >>
  TRY (irule sub_offset_by_ptr_matches) >>
  TRY (irule offset_by_none_ptr_matches) >>
  simp[venomStateTheory.lookup_var_def, FLOOKUP_UPDATE,
       wordsTheory.n2w_w2n] >>
  qexists_tac `s` >> first_assum (irule_at (Pos last)) >>
  gvs[venomStateTheory.lookup_var_def, venomStateTheory.eval_operand_def]
QED

Resume bp_handle_inst_sound_proof[assign]:
  fs[GSYM bp_get_ptrs_def] >>
  gvs[venomExecSemanticsTheory.step_inst_non_invoke,
      venomExecSemanticsTheory.step_inst_base_def, AllCaseEqs(),
      venomWfTheory.inst_wf_def,
      venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, FLOOKUP_UPDATE,
      venomStateTheory.eval_operand_def] >>
  (* Case split op1: only Var src case has non-empty ptrs *)
  Cases_on `op1` >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE] >>
  rename1 `Var src` >>
  gvs[venomStateTheory.eval_operand_def, GSYM bp_get_ptrs_def] >>
  (* bp_ptr_sound gives a matching pointer for src *)
  `∃p. MEM p (bp_get_ptrs bp src) ∧ ptr_matches_var p src s` by
    (fs[bp_ptr_sound_def] >> first_x_assum irule >>
     simp[venomStateTheory.lookup_var_def]) >>
  qexists_tac `p` >> simp[] >>
  irule ptr_matches_var_preserved >>
  qexistsl_tac [`s`, `src`] >>
  simp[venomStateTheory.lookup_var_def, FLOOKUP_UPDATE]
QED

Finalise bp_handle_inst_sound_proof

(* DOMSUB helpers for fixpoint proof *)
Theorem bp_ptr_sound_domsub[local]:
  !bp v s. bp_ptr_sound bp s ==> bp_ptr_sound (bp \\ v) s
Proof
  rw[bp_ptr_sound_def] >>
  rename1 `bp_get_ptrs (bp \\ v) w` >>
  `w <> v` by (CCONTR_TAC >> gvs[bp_get_ptrs_def, FLOOKUP_DEF, fmap_domsub]) >>
  `bp_get_ptrs (bp \\ v) w = bp_get_ptrs bp w` by
    simp[bp_get_ptrs_def, DOMSUB_FLOOKUP_NEQ] >>
  gvs[]
QED

Theorem bp_get_ptrs_domsub_self[local]:
  !bp v. bp_get_ptrs (bp \\ v) v = []
Proof
  rw[bp_get_ptrs_def, FLOOKUP_DEF, DOMSUB_FAPPLY_NEQ, fmap_domsub]
QED

Theorem bp_get_ptrs_domsub_neq[local]:
  !bp v w. v <> w ==> bp_get_ptrs (bp \\ v) w = bp_get_ptrs bp w
Proof
  rw[bp_get_ptrs_def, DOMSUB_FLOOKUP_NEQ]
QED

(* phi_pairs vars are a subset of operand_vars *)
Theorem phi_pairs_subset_operand_vars[local]:
  !ops x. MEM x (MAP SND (phi_pairs ops)) ==> MEM x (operand_vars ops)
Proof
  Induct_on `ops` using venomInstTheory.phi_pairs_ind >>
  rpt strip_tac >>
  gvs[venomInstTheory.phi_pairs_def,
      venomInstTheory.operand_vars_def,
      venomInstTheory.operand_var_def] >>
  Cases_on `operand_var v1` >> gvs[]
QED

(* General frame lemma: bp_ptr_sound preserved by step_inst.
   For the output variable, caller provides either:
   (a) bp_get_ptrs bp out = [] — vacuously true, or
   (b) a direct proof that ptr_matches_var holds for the new value.
   This separates frame reasoning from per-opcode reasoning. *)
Theorem bp_ptr_sound_preserved_by_step:
  !bp inst fuel ctx s s'.
    bp_ptr_sound bp s /\
    step_inst fuel ctx inst s = OK s' /\
    inst_wf inst /\
    (inst_output inst = NONE ==> inst.inst_outputs = []) /\
    (!out. inst_output inst = SOME out ==>
       bp_get_ptrs bp out = [] \/
       (IS_SOME (lookup_var out s') ==>
        ?p. MEM p (bp_get_ptrs bp out) /\ ptr_matches_var p out s')) /\
    (!v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ==>
       FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) ==>
    bp_ptr_sound bp s'
Proof
  rpt strip_tac >>
  simp[bp_ptr_sound_def] >>
  rpt strip_tac >>
  Cases_on `inst_output inst = SOME v`
  >- suspend "output"
  >> suspend "frame"
QED

Resume bp_ptr_sound_preserved_by_step[output]:
  gvs[] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  strip_tac >> metis_tac[]
QED

Resume bp_ptr_sound_preserved_by_step[frame]:
  (* v is not the output → lookup_var v preserved *)
  `lookup_var v s' = lookup_var v s` by (
    irule step_inst_preserves_lookup >>
    qexistsl_tac [`ctx`, `fuel`, `inst`] >> simp[] >>
    Cases_on `inst_output inst` >> gvs[venomInstTheory.inst_output_def] >>
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  (* bp_ptr_sound bp s gives a matching pointer for v *)
  `?p. MEM p (bp_get_ptrs bp v) /\ ptr_matches_var p v s` by
    gvs[bp_ptr_sound_def] >>
  qexists `p` >> simp[] >>
  MATCH_MP_TAC ptr_matches_var_preserved >>
  qexists `v` >> simp[] >> metis_tac[]
QED

Finalise bp_ptr_sound_preserved_by_step

(* ===================================================================
   Block-level soundness.

   Hypotheses ensure per-step allocas preservation:
   - bb_well_formed bb (terminator is last; no post-terminator gap)
   - ALLOCA inst_ids are pairwise distinct
   - ALLOCA inst_ids don't collide with initial bp pointers
   - INVOKE preserves pre-existing alloca entries
   =================================================================== *)

(* offset_by / sub_offset_by preserve the allocation of a ptr *)
Theorem offset_by_alloc_id[local]:
  (∀p d a off. offset_by p d = Ptr a off ⇒
    ∃off'. p = Ptr a off') ∧
  (∀p d a off. sub_offset_by p d = Ptr a off ⇒
    ∃off'. p = Ptr a off')
Proof
  conj_tac >> (
    Cases_on `p` >> Cases_on `o'` >> Cases_on `d` >>
    simp[offset_by_def, sub_offset_by_def] >> rw[])
QED

(* All alloc_ids in bp_handle_inst output trace to input bp or ALLOCA *)
Theorem bp_handle_inst_alloc_ids[local]:
  ∀bp inst c r v aid off.
    bp_handle_inst bp inst = (c, r) ∧
    MEM (Ptr (Allocation aid) off) (bp_get_ptrs r v) ⇒
    (∃w off'. MEM (Ptr (Allocation aid) off') (bp_get_ptrs bp w)) ∨
    (inst.inst_opcode = ALLOCA ∧ aid = inst.inst_id)
Proof
  rpt strip_tac >>
  reverse (Cases_on `inst_output inst = SOME v`)
  >- (
    `bp_get_ptrs r v = bp_get_ptrs bp v` by
      (irule bp_handle_inst_other_var_proof >> metis_tac[]) >>
    disj1_tac >> metis_tac[]) >>
  (* v = out, the output variable. Case split on opcode. *)
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (
    (* ALLOCA: aid = inst.inst_id *)
    disj2_tac >>
    fs[bp_handle_inst_def, venomInstTheory.inst_output_def] >>
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, ptr_from_alloca_def]) >>
  disj1_tac >>
  (* Non-ALLOCA: all ptrs in r trace back to bp.
     Strategy: unfold bp_handle_inst pair to extract r,
     then case-split on opcode *)
  fs[bp_handle_inst_def, venomInstTheory.inst_output_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  rename1 `inst.inst_outputs = [out]` >>
  (* Case split on opcode. Most give r = bp or bp|+(out,[]). *)
  Cases_on `inst.inst_opcode` >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, ptr_from_alloca_def,
      MEM_MAP, MEM_nub, MEM_FLAT] >>
  fs[GSYM bp_get_ptrs_def] >>
  (* Close simple cases: r = bp, ptrs unchanged *)
  TRY (qexists_tac `out` >> qexists_tac `off` >>
       first_assum ACCEPT_TAC) >>
  (* ADD, SUB, ASSIGN, PHI: operand case splits *)
  BasicProvers.every_case_tac >>
  gvs[bp_get_ptrs_def, FLOOKUP_UPDATE, MEM_MAP,
      MEM_nub, MEM_FLAT] >>
  fs[GSYM bp_get_ptrs_def] >>
  TRY (imp_res_tac (CONJUNCT1 offset_by_alloc_id) >> metis_tac[]) >>
  TRY (imp_res_tac (CONJUNCT2 offset_by_alloc_id) >> metis_tac[]) >>
  TRY (imp_res_tac (GSYM (CONJUNCT1 offset_by_alloc_id)) >> metis_tac[]) >>
  imp_res_tac (GSYM (CONJUNCT2 offset_by_alloc_id)) >> metis_tac[]
QED

(* Wrapper: applies bp_handle_inst_sound_proof with per-instruction conditions.
   Caller provides output freshness, alloca preservation, and PHI directly. *)
Theorem bp_handle_inst_sound_in_block[local]:
  ∀bp inst c r fuel ctx s s'.
    bp_ptr_sound bp s ∧
    bp_handle_inst bp inst = (c, r) ∧
    step_inst fuel ctx inst s = OK s' ∧
    inst_wf inst ∧
    (∀out. MEM out inst.inst_outputs ⇒ bp_get_ptrs bp out = []) ∧
    (inst_output inst = NONE ⇒ inst.inst_outputs = []) ∧
    (∀v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       FLOOKUP s'.vs_allocas aid = FLOOKUP s.vs_allocas aid) ∧
    (∀v. inst.inst_opcode = PHI ∧
       MEM v (MAP SND (phi_pairs inst.inst_operands)) ∧
       IS_SOME (lookup_var v s) ⇒
       bp_get_ptrs bp v ≠ []) ⇒
    bp_ptr_sound r s'
Proof
  rpt strip_tac >>
  irule bp_handle_inst_sound_proof >>
  qexistsl_tac [`bp`, `c`, `ctx`, `fuel`, `inst`, `s`] >>
  ASM_REWRITE_TAC[] >> rpt conj_tac >> rpt strip_tac >>
  TRY (first_x_assum irule >>
       imp_res_tac inst_wf_outputs_some >> gvs[] >> NO_TAC) >>
  metis_tac[]
QED

(* Generalized block-level lemma: from arbitrary index to end.
   Supports INVOKE via explicit alloca preservation precondition. *)
Theorem bp_process_block_sound_gen[local]:
  ∀n fuel ctx bb s' bp0 s0 c0 bp'.
    n + s0.vs_inst_idx = LENGTH bb.bb_instructions ∧
    bb_well_formed bb ∧
    bp_ptr_sound bp0 s0 ∧
    bp_process_block bp0 (DROP s0.vs_inst_idx bb.bb_instructions) = (c0, bp') ∧
    exec_block fuel ctx bb s0 = OK s' ∧
    s0.vs_inst_idx ≤ LENGTH bb.bb_instructions ∧
    ALL_DISTINCT (FLAT (MAP (λi. i.inst_outputs)
      (DROP s0.vs_inst_idx bb.bb_instructions))) ∧
    (∀inst out. MEM inst (DROP s0.vs_inst_idx bb.bb_instructions) ∧
       MEM out inst.inst_outputs ⇒ bp_get_ptrs bp0 out = []) ∧
    (∀inst. MEM inst (DROP s0.vs_inst_idx bb.bb_instructions) ∧
       inst_output inst = NONE ⇒ inst.inst_outputs = []) ∧
    (∀inst. MEM inst (DROP s0.vs_inst_idx bb.bb_instructions) ⇒
       inst_wf inst) ∧
    (∀inst v aid off. MEM inst (DROP s0.vs_inst_idx bb.bb_instructions) ∧
       inst.inst_opcode = ALLOCA ∧
       MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp0 v) ⇒
       aid ≠ inst.inst_id) ∧
    ALL_DISTINCT (MAP (λi. i.inst_id)
      (FILTER (λi. i.inst_opcode = ALLOCA)
        (DROP s0.vs_inst_idx bb.bb_instructions))) ∧
    (∀inst v. MEM inst (DROP s0.vs_inst_idx bb.bb_instructions) ∧
       inst.inst_opcode = PHI ∧
       MEM v (MAP SND (phi_pairs inst.inst_operands)) ∧
       IS_SOME (lookup_var v s0) ⇒
       bp_get_ptrs bp0 v ≠ []) ⇒
    bp_ptr_sound bp' s'
Proof
  Induct_on `n`
  >- (
    (* Base: n = 0, idx = LENGTH ⇒ DROP = [] ⇒ exec_block errors *)
    rpt strip_tac >>
    `s0.vs_inst_idx = LENGTH bb.bb_instructions` by decide_tac >>
    fs[DROP_LENGTH_TOO_LONG, bp_process_block_def,
       Once exec_block_def, venomInstTheory.get_instruction_def])
  >- (
  rpt strip_tac >>
  `s0.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
  (* Decompose DROP = hd :: tl *)
  qabbrev_tac `inst = EL s0.vs_inst_idx bb.bb_instructions` >>
  `DROP s0.vs_inst_idx bb.bb_instructions =
     inst :: DROP (s0.vs_inst_idx + 1) bb.bb_instructions` by (
    simp[Abbr `inst`] >> irule rich_listTheory.DROP_EL_CONS >> simp[]) >>
  (* Decompose bp_process_block *)
  `∃c1 r1. bp_handle_inst bp0 inst = (c1, r1)` by metis_tac[pairTheory.PAIR] >>
  `∃c2. bp_process_block r1 (DROP (s0.vs_inst_idx + 1) bb.bb_instructions) = (c2, bp')` by (
    qpat_x_assum `bp_process_block bp0 _ = _` mp_tac >>
    ASM_REWRITE_TAC[] >> simp[bp_process_block_def] >>
    pairarg_tac >> fs[] >> pairarg_tac >> fs[] >> strip_tac >> gvs[] >>
    metis_tac[]) >>
  `c0 = (c1 ∨ c2)` by (
    qpat_x_assum `bp_process_block bp0 _ = _` mp_tac >>
    ASM_REWRITE_TAC[] >> simp[bp_process_block_def] >>
    pairarg_tac >> fs[] >> pairarg_tac >> fs[]) >>
  (* Establish MEM inst and inst_wf cheaply *)
  `inst = EL s0.vs_inst_idx bb.bb_instructions` by
    fs[Abbr `inst`] >>
  `MEM inst (DROP s0.vs_inst_idx bb.bb_instructions)` by (
    ASM_REWRITE_TAC[MEM]) >>
  `inst_wf inst` by metis_tac[] >>
  qpat_x_assum `DROP _ _ = _ :: _` kall_tac >>
  (* Pop IH and inst_eq to protect from simp, unfold exec_block *)
  qpat_x_assum `inst = _` (fn inst_eq =>
    qpat_x_assum `∀fuel ctx bb s' bp0 s0 c0 bp'. _` (fn ih =>
      qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
      PURE_ONCE_REWRITE_TAC [exec_block_def] >>
      PURE_REWRITE_TAC [venomInstTheory.get_instruction_def] >>
      PURE_ONCE_REWRITE_TAC [GSYM inst_eq] >>
      simp[] >> strip_tac >>
      assume_tac ih >> assume_tac inst_eq)) >>
  (* Case split on step_inst result *)
  qpat_x_assum `(case step_inst _ _ _ _ of _ => _) = OK _` mp_tac >>
  Cases_on `step_inst fuel ctx inst s0`
  >- (
    (* OK case *)
    rename1 `step_inst _ _ inst s0 = OK s1` >>
    REWRITE_TAC[venomExecSemanticsTheory.exec_result_case_def] >>
    strip_tac >>
    Cases_on `is_terminator inst.inst_opcode`
    >- suspend "terminator"
    >- suspend "non_terminator")
  (* Non-OK cases: case_def gives Halt/Abort/IntRet/Error = OK → F *)
  >> SIMP_TAC bool_ss [venomExecSemanticsTheory.exec_result_case_def,
                        GSYM venomExecSemanticsTheory.exec_result_distinct])
QED

(* INVOKE preserves caller's vs_allocas: merge_callee_state keeps caller's,
   bind_outputs only does update_var which doesn't touch vs_allocas. *)
Theorem step_inst_invoke_preserves_allocas[local]:
  ∀fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' ∧
    inst.inst_opcode = INVOKE ⇒
    s'.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  gvs[Once venomExecSemanticsTheory.step_inst_def, AllCaseEqs()] >>
  gvs[venomExecSemanticsTheory.bind_outputs_def, AllCaseEqs()] >>
  Cases_on `ret.iret_adopt_fmp` >>
  gvs[foldl_update_var_allocas,
      venomExecSemanticsTheory.adopt_return_fmp_def,
      venomExecSemanticsTheory.merge_callee_state_def]
QED

(* Helper: derive per-instruction alloca FLOOKUP preservation.
   INVOKE: full vs_allocas preserved (merge_callee_state keeps caller's).
   ALLOCA: only inst_id entry changes.
   Other: full vs_allocas preserved. *)
Theorem step_alloca_from_block[local]:
  ∀fuel ctx inst s0 s1 bp insts.
    step_inst fuel ctx inst s0 = OK s1 ∧
    MEM inst insts ∧
    (∀i v aid off. MEM i insts ∧ i.inst_opcode = ALLOCA ∧
       MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       aid ≠ i.inst_id) ⇒
    ∀v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       FLOOKUP s1.vs_allocas aid = FLOOKUP s0.vs_allocas aid
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (drule_all step_inst_invoke_preserves_allocas >> simp[])
  >- (
    `inst.inst_opcode = ALLOCA ⇒ aid ≠ inst.inst_id` by metis_tac[] >>
    metis_tac[step_inst_alloca_flookup])
QED

Theorem is_terminator_not_alloca_invoke[local]:
  ∀opc. is_terminator opc ⇒ opc ≠ ALLOCA ∧ opc ≠ INVOKE
Proof
  Cases >> simp[venomInstTheory.is_terminator_def]
QED

Resume bp_process_block_sound_gen[terminator]:
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `(if is_terminator _ then _ else _) = OK _` mp_tac >>
  ASM_REWRITE_TAC[] >>
  Cases_on `s1.vs_halted` >> simp[] >> strip_tac >>
  `s0.vs_inst_idx + 1 = LENGTH bb.bb_instructions` by (
    `s0.vs_inst_idx = PRE (LENGTH bb.bb_instructions)` by (
      qpat_assum `bb_well_formed _`
        (strip_assume_tac o REWRITE_RULE[bb_well_formed_def]) >>
      first_x_assum irule >>
      gvs[markerTheory.Abbrev_def]) >>
    pop_assum mp_tac >>
    qpat_assum `_ < LENGTH _` mp_tac >> DECIDE_TAC) >>
  imp_res_tac (REWRITE_RULE [] rich_listTheory.DROP_LENGTH_NIL_rwt) >>
  qpat_x_assum `bp_process_block r1 _ = _` mp_tac >>
  ASM_REWRITE_TAC[] >> simp[bp_process_block_def] >>
  strip_tac >>
  (* Establish allocas preservation BEFORE VAR_EQ_TAC eliminates s1 *)
  `s1.vs_allocas = s0.vs_allocas` by
    metis_tac[step_inst_allocas, is_terminator_not_alloca_invoke] >>
  BasicProvers.VAR_EQ_TAC >>
  irule bp_handle_inst_sound_in_block >>
  qexistsl_tac [`bp0`, `c1`, `ctx`, `fuel`, `inst`, `s0`] >>
  gvs[markerTheory.Abbrev_def] >>
  rpt conj_tac
  >- ((* PHI *) metis_tac[])
  >- ((* output freshness *) metis_tac[])
QED

(* After bp_handle_inst, output ptrs for other instructions stay empty. *)
Theorem bp_handle_inst_output_ptrs_tail[local]:
  ∀bp0 inst c r insts i out.
    bp_handle_inst bp0 inst = (c, r) ∧
    ALL_DISTINCT (FLAT (MAP (λi. i.inst_outputs) (inst :: insts))) ∧
    MEM i insts ∧ MEM out i.inst_outputs ∧
    (∀j out. MEM j (inst :: insts) ∧ MEM out j.inst_outputs ⇒
       bp_get_ptrs bp0 out = []) ⇒
    bp_get_ptrs r out = []
Proof
  rpt strip_tac >>
  (* out ∉ inst.inst_outputs from ALL_DISTINCT FLAT *)
  `¬MEM out inst.inst_outputs` by (
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    simp[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
    metis_tac[]) >>
  `inst_output inst ≠ SOME out` by (
    strip_tac >>
    gvs[venomInstTheory.inst_output_def] >>
    Cases_on `inst.inst_outputs` >> gvs[] >>
    Cases_on `t` >> gvs[]) >>
  `bp_get_ptrs r out = bp_get_ptrs bp0 out` by
    metis_tac[bp_handle_inst_other_var_proof] >>
  ASM_REWRITE_TAC[] >>
  first_x_assum irule >> simp[MEM] >> metis_tac[]
QED

Theorem bp_ptr_sound_inst_idx[local]:
  ∀bp s n. bp_ptr_sound bp (s with vs_inst_idx := n) ⇔ bp_ptr_sound bp s
Proof
  rw[bp_ptr_sound_def, venomStateTheory.lookup_var_def] >>
  `∀p v. ptr_matches_var p v (s with vs_inst_idx := n) ⇔
         ptr_matches_var p v s` by (
    rpt gen_tac >> Cases_on `p` >> Cases_on `a` >> Cases_on `o'` >>
    simp[ptr_matches_var_def, venomStateTheory.lookup_var_def]) >>
  ASM_REWRITE_TAC[]
QED

(* ALLOCA freshness: after bp_handle_inst, remaining ALLOCAs still don't
   collide with tracked pointer aids in r. *)
Theorem bp_handle_inst_alloca_freshness_tail[local]:
  ∀bp0 inst c r insts inst' v aid off.
    bp_handle_inst bp0 inst = (c, r) ∧
    (∀i v aid off. MEM i (inst :: insts) ∧ i.inst_opcode = ALLOCA ∧
       MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp0 v) ⇒
       aid ≠ i.inst_id) ∧
    ALL_DISTINCT (MAP (λi. i.inst_id)
      (FILTER (λi. i.inst_opcode = ALLOCA) (inst :: insts))) ∧
    MEM inst' insts ∧ inst'.inst_opcode = ALLOCA ∧
    MEM (Ptr (Allocation aid) off) (bp_get_ptrs r v) ⇒
    aid ≠ inst'.inst_id
Proof
  rpt strip_tac >>
  (* Use bp_handle_inst_alloc_ids to trace aid back *)
  drule_all bp_handle_inst_alloc_ids >>
  strip_tac >>
  pop_assum strip_assume_tac
  >- (
    (* Case (a): aid comes from bp_get_ptrs bp0 w for some w *)
    qpat_assum `!i v' aid' off'. MEM i (inst :: insts) /\ _ ==> aid' <> _`
      (qspecl_then [`inst'`, `w`, `aid`, `off'`] mp_tac) >>
    (impl_tac >- ASM_REWRITE_TAC[MEM]) >>
    strip_tac >> first_assum ACCEPT_TAC)
  >- (
    (* Case (b): aid = inst.inst_id, inst.opcode = ALLOCA *)
    gvs[] >>
    qpat_x_assum `ALL_DISTINCT _` mp_tac >>
    SIMP_TAC bool_ss [FILTER, MAP, ALL_DISTINCT] >>
    strip_tac >>
    CCONTR_TAC >> gvs[] >>
    qpat_x_assum `¬MEM _ _` mp_tac >>
    REWRITE_TAC[] >>
    SIMP_TAC bool_ss [MEM_MAP, MEM_FILTER] >>
    qexists_tac `inst'` >> ASM_REWRITE_TAC[])
QED

(* After step_inst PHI, for any phi pair variable v:
   PHI is now a no-op in both step_inst and bp_handle_inst,
   so s1 = s0 and r = bp0. The hypothesis directly gives bp_get_ptrs bp0 v ≠ []. *)
Theorem bp_handle_inst_phi_transfer[local]:
  ∀bp0 inst c r fuel ctx s0 s1 inst' insts v.
    bp_handle_inst bp0 inst = (c, r) ∧
    inst_wf inst ∧
    ¬is_terminator inst.inst_opcode ∧
    step_inst fuel ctx inst s0 = OK s1 ∧
    inst.inst_opcode = PHI ∧
    MEM inst' insts ∧ inst'.inst_opcode = PHI ∧
    MEM v (MAP SND (phi_pairs inst'.inst_operands)) ∧
    IS_SOME (lookup_var v s1) ∧
    (∀i w. MEM i (inst :: insts) ∧ i.inst_opcode = PHI ∧
       MEM w (MAP SND (phi_pairs i.inst_operands)) ∧
       IS_SOME (lookup_var w s0) ⇒
       bp_get_ptrs bp0 w ≠ []) ⇒
    bp_get_ptrs r v ≠ []
Proof
  rpt strip_tac >>
  `r = bp0` by (
    qpat_x_assum `bp_handle_inst bp0 inst = (c,r)` mp_tac >>
    simp[bp_handle_inst_def, LET_THM] >>
    Cases_on `inst_output inst` >> gvs[] >>
    Cases_on `inst.inst_opcode` >> gvs[]) >>
  `s1 = s0` by (
    qpat_x_assum `step_inst fuel ctx inst s0 = OK s1` mp_tac >>
    simp[venomExecSemanticsTheory.step_inst_non_invoke,
         venomExecSemanticsTheory.step_inst_base_def]) >>
  gvs[] >>
  first_x_assum (qspecl_then [`inst'`, `v`] mp_tac) >>
  simp[MEM]
QED

Resume bp_process_block_sound_gen[non_terminator]:
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_x_assum `(if _ then _ else _) = OK _` mp_tac >>
  ASM_REWRITE_TAC[] >> strip_tac >>
  (* Alloca preservation for this step *)
  `∀v aid off. MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp0 v) ⇒
     FLOOKUP s1.vs_allocas aid = FLOOKUP s0.vs_allocas aid` by (
    rpt strip_tac >>
    Cases_on `inst.inst_opcode = INVOKE`
    >- (drule_all step_inst_invoke_preserves_allocas >> simp[])
    >- (
      `inst.inst_opcode = ALLOCA ⇒ aid ≠ inst.inst_id` by metis_tac[] >>
      metis_tac[step_inst_alloca_flookup])) >>
  `bp_ptr_sound r1 s1` by (
    irule bp_handle_inst_sound_in_block >>
    qexistsl_tac [`bp0`, `c1`, `ctx`, `fuel`, `inst`, `s0`] >>
    gvs[markerTheory.Abbrev_def] >> rpt conj_tac >> metis_tac[]) >>
  (* Unwrap Abbrev without VAR_EQ_TAC (which hangs with this assumption set) *)
  qpat_x_assum `Abbrev (inst = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  (* DROP decomposition *)
  `DROP s0.vs_inst_idx bb.bb_instructions =
   inst :: DROP (s0.vs_inst_idx + 1) bb.bb_instructions` by (
    `DROP s0.vs_inst_idx bb.bb_instructions =
     EL s0.vs_inst_idx bb.bb_instructions ::
     DROP (s0.vs_inst_idx + 1) bb.bb_instructions` suffices_by
      ASM_REWRITE_TAC[] >>
    irule rich_listTheory.DROP_EL_CONS >> DECIDE_TAC) >>
  (* Apply IH *)
  qpat_x_assum `!fuel ctx bb s' bp0 s0 c0 bp'. _` (
    qspecl_then [`fuel`, `ctx`, `bb`, `s'`, `r1`,
      `s1 with vs_inst_idx := SUC s0.vs_inst_idx`,
      `c2`, `bp'`] mp_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [arithmeticTheory.ADD1]) >>
  SIMP_TAC pure_ss [venomStateTheory.venom_state_accfupds, combinTheory.K_THM, arithmeticTheory.ADD1] >>
  impl_tac
  >- (
    conj_tac >- DECIDE_TAC >>           (* 1 *)
    conj_tac >- (first_assum ACCEPT_TAC) >> (* 2 *)
    conj_tac >- ASM_REWRITE_TAC[bp_ptr_sound_inst_idx] >> (* 3 *)
    conj_tac >- (first_assum ACCEPT_TAC) >> (* 4 *)
    conj_tac >- (first_assum ACCEPT_TAC) >> (* 5 *)
    conj_tac >- DECIDE_TAC >>           (* 6 *)
    conj_tac >- (                        (* 7 *)
      qpat_x_assum `ALL_DISTINCT (FLAT (MAP _ (DROP s0.vs_inst_idx _)))` mp_tac >>
      qpat_x_assum `DROP _ _ = _ :: _`
        (fn eq => PURE_REWRITE_TAC [eq]) >>
      REWRITE_TAC[MAP, FLAT, ALL_DISTINCT_APPEND] >> metis_tac[]) >>
    conj_tac >- (                        (* 8 *)
      rpt strip_tac >>
      mp_tac bp_handle_inst_output_ptrs_tail >>
      DISCH_THEN (qspecl_then [`bp0`, `inst`, `c1`, `r1`,
        `DROP (s0.vs_inst_idx + 1) bb.bb_instructions`,
        `inst'`, `out`] mp_tac) >>
      (impl_tac >- (
        rpt conj_tac >| [
          first_assum ACCEPT_TAC,
          qpat_assum `ALL_DISTINCT (FLAT (MAP _ (DROP s0.vs_inst_idx _)))` mp_tac >>
          qpat_assum `DROP _ _ = _ :: _`
            (fn eq => PURE_ONCE_REWRITE_TAC [eq]) >>
          DISCH_TAC >> first_assum ACCEPT_TAC,
          first_assum ACCEPT_TAC, first_assum ACCEPT_TAC,
          metis_tac[MEM]
        ])) >>
      DISCH_TAC >> first_assum ACCEPT_TAC) >>
    conj_tac >- (                        (* 9: inst_output NONE → [] *)
      rpt strip_tac >>
      qpat_assum `!inst'. MEM inst' (DROP _ _) /\ inst_output _ = NONE ==> _`
        (qspec_then `inst'` mp_tac) >>
      (impl_tac >- (
        qpat_x_assum `DROP _ _ = _ :: _`
          (fn eq => PURE_REWRITE_TAC [eq]) >>
        REWRITE_TAC[MEM] >> ASM_REWRITE_TAC[])) >>
      strip_tac >> ASM_REWRITE_TAC[]) >>
    conj_tac >- (                        (* 10: inst_wf *)
      rpt strip_tac >>
      qpat_assum `!i. MEM i (DROP s0.vs_inst_idx _) ==> _`
        (qspec_then `inst'` mp_tac) >>
      (impl_tac >- (
        qpat_x_assum `DROP _ _ = _ :: _`
          (fn eq => PURE_REWRITE_TAC [eq]) >>
        REWRITE_TAC[MEM] >> ASM_REWRITE_TAC[])) >>
      strip_tac >> ASM_REWRITE_TAC[]) >>
    conj_tac >- (                        (* 11: alloca freshness *)
      rpt gen_tac >> strip_tac >>
      qpat_assum `DROP _ _ = _ :: _`
        (fn eq => RULE_ASSUM_TAC (PURE_ONCE_REWRITE_RULE [eq])) >>
      mp_tac (Q.SPECL [`bp0`, `inst`, `c1`, `r1`,
        `DROP (s0.vs_inst_idx + 1) bb.bb_instructions`,
        `inst'`, `v`, `aid`, `off`]
        bp_handle_inst_alloca_freshness_tail) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      DISCH_TAC >> first_assum ACCEPT_TAC) >>
    conj_tac >- (                        (* 12: ALL_DISTINCT alloca *)
      qpat_x_assum `ALL_DISTINCT (MAP _ (FILTER _ (DROP s0.vs_inst_idx _)))` mp_tac >>
      qpat_x_assum `DROP _ _ = _ :: _`
        (fn eq => PURE_REWRITE_TAC [eq]) >>
      SIMP_TAC bool_ss [FILTER] >>
      Cases_on `inst.inst_opcode = ALLOCA` >>
      ASM_REWRITE_TAC[MAP, ALL_DISTINCT]
      >- (DISCH_TAC >> pop_assum (ACCEPT_TAC o CONJUNCT2))
      >> (DISCH_TAC >> first_assum ACCEPT_TAC)) >>
    (* 13 - phi transfer *)
      rpt strip_tac >>
      rename1 `MEM inst2 (DROP _ _)` >>
      rename1 `MEM v2 (MAP SND _)` >>
      Cases_on `inst.inst_opcode = PHI`
      >- (
        qpat_x_assum `IS_SOME (lookup_var v2 _)` (fn th =>
          assume_tac (SIMP_RULE (srw_ss())
            [venomStateTheory.lookup_var_def] th)) >>
        mp_tac bp_handle_inst_phi_transfer >>
        DISCH_THEN (qspecl_then [`bp0`, `inst`, `c1`, `r1`, `fuel`, `ctx`,
          `s0`, `s1`, `inst2`,
          `DROP (s0.vs_inst_idx + 1) bb.bb_instructions`,
          `v2`] mp_tac) >>
        qpat_assum `DROP _ _ = _ :: _`
          (fn eq => PURE_REWRITE_TAC [GSYM eq]) >>
        PURE_REWRITE_TAC [venomStateTheory.lookup_var_def] >>
        (impl_tac >- (
          rpt conj_tac >>
          TRY (first_assum ACCEPT_TAC) >>
          rpt strip_tac >>
          qpat_assum `!_ _. MEM _ (DROP s0.vs_inst_idx _) /\ _ ==> _`
            (qspecl_then [`i`, `w`] mp_tac) >>
          PURE_REWRITE_TAC [venomStateTheory.lookup_var_def] >>
          ASM_REWRITE_TAC[] >>
          DISCH_TAC >> first_assum ACCEPT_TAC)) >>
        strip_tac)
      >> (
        `∃j. j < LENGTH bb.bb_instructions ∧
             inst2 = EL j bb.bb_instructions ∧
             s0.vs_inst_idx < j` by (
          qpat_x_assum `MEM inst2 (DROP _ _)` mp_tac >>
          REWRITE_TAC[MEM_DROP] >> strip_tac >>
          qexists_tac `m + (s0.vs_inst_idx + 1)` >>
          ASM_REWRITE_TAC[] >> DECIDE_TAC) >>
        qpat_assum `bb_well_formed bb` mp_tac >>
        REWRITE_TAC[venomWfTheory.bb_well_formed_def] >>
        strip_tac >>
        first_x_assum (qspecl_then [`s0.vs_inst_idx`, `j`] mp_tac) >>
        qpat_assum `inst = _` (fn eq =>
          PURE_ONCE_REWRITE_TAC[GSYM eq]) >>
        qpat_x_assum `inst2 = _` (fn eq =>
          PURE_ONCE_REWRITE_TAC[GSYM eq]) >>
        ASM_REWRITE_TAC[])) >>
  strip_tac
QED

Finalise bp_process_block_sound_gen;

(* Block-level: processing a block preserves soundness through exec_block. *)
Theorem bp_process_block_sound_proof:
  ∀bp bb c bp' fuel ctx s s'.
    bp_ptr_sound bp s ∧
    bp_process_block bp bb.bb_instructions = (c, bp') ∧
    exec_block fuel ctx bb s = OK s' ∧
    s.vs_inst_idx = 0 ∧
    bb_well_formed bb ∧
    (∀inst. MEM inst bb.bb_instructions ⇒ inst_wf inst) ∧
    ALL_DISTINCT (FLAT (MAP (λi. i.inst_outputs) bb.bb_instructions)) ∧
    (∀inst out. MEM inst bb.bb_instructions ∧
               inst_output inst = SOME out ⇒
               bp_get_ptrs bp out = []) ∧
    (∀inst. MEM inst bb.bb_instructions ∧
           inst_output inst = NONE ⇒ inst.inst_outputs = []) ∧
    ctx_inst_ids_distinct ctx ∧
    (∀inst v aid off. MEM inst bb.bb_instructions ∧
       inst.inst_opcode = ALLOCA ∧
       MEM (Ptr (Allocation aid) off) (bp_get_ptrs bp v) ⇒
       aid ≠ inst.inst_id) ∧
    ALL_DISTINCT (MAP (λi. i.inst_id)
      (FILTER (λi. i.inst_opcode = ALLOCA) bb.bb_instructions)) ∧
    (∀inst v. MEM inst bb.bb_instructions ∧
       inst.inst_opcode = PHI ∧
       MEM v (MAP SND (phi_pairs inst.inst_operands)) ∧
       IS_SOME (lookup_var v s) ⇒
       bp_get_ptrs bp v ≠ []) ⇒
    bp_ptr_sound bp' s'
Proof
  rpt strip_tac >>
  irule bp_process_block_sound_gen >>
  qexistsl_tac [`bb`, `bp`, `c`, `ctx`, `fuel`,
                 `LENGTH bb.bb_instructions`, `s`] >>
  simp[DROP_0] >>
  rpt conj_tac >> rpt strip_tac >>
  TRY (res_tac >> fs[] >> NO_TAC) >>
  (* Bridge inst_output → MEM: use SOME case + NONE case *)
  Cases_on `inst_output inst`
  >- (`inst.inst_outputs = []` by res_tac >> gvs[])
  >- (`inst_wf inst` by res_tac >>
      imp_res_tac inst_wf_outputs_some >> gvs[] >> res_tac)
QED

(* Singleton pointer ⇒ exact runtime address. *)
Theorem bp_ptr_from_op_sound_proof:
  ∀bp v aid off s.
    bp_ptr_sound bp s ∧
    bp_ptr_from_op bp (Var v) = SOME (Ptr (Allocation aid) (SOME off)) ∧
    IS_SOME (eval_operand (Var v) s) ⇒
    ∃base sz.
      FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
      eval_operand (Var v) s = SOME (n2w (base + off))
Proof
  rpt strip_tac >>
  gvs[venomStateTheory.eval_operand_def, bp_ptr_from_op_def] >>
  Cases_on `bp_get_ptrs bp v` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  fs[bp_ptr_sound_def] >>
  first_x_assum (qspec_then `v` mp_tac) >> rw[] >>
  gvs[ptr_matches_var_def]
QED

(* Alloca-backed mem_loc correctly describes runtime address. *)
Theorem bp_segment_from_ops_sound_proof:
  ∀bp ops ml aid off s.
    bp_ptr_sound bp s ∧
    bp_segment_from_ops bp ops = ml ∧
    ml_is_fixed ml ∧
    ml.ml_alloca = SOME (Allocation aid) ∧
    ml.ml_offset = SOME off ∧
    IS_SOME (eval_operand ops.iao_ofst s) ⇒
    ∃base sz.
      FLOOKUP s.vs_allocas aid = SOME (base, sz) ∧
      eval_operand ops.iao_ofst s = SOME (n2w (base + off))
Proof
  rpt strip_tac >>
  Cases_on `ops.iao_ofst` >>
  gvs[bp_segment_from_ops_def, LET_THM, ml_is_fixed_def, ml_undefined_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[] >>
  irule bp_ptr_from_op_sound_proof >>
  metis_tac[]
QED


(* FDOM of bp_handle_inst: only adds the output variable *)
Theorem bp_handle_inst_fdom:
  !bp inst c bp'.
    bp_handle_inst bp inst = (c, bp') ==>
    FDOM bp' SUBSET FDOM bp UNION set (inst_defs inst)
Proof
  rw[bp_handle_inst_def, inst_defs_def, inst_output_def] >>
  gvs[AllCaseEqs(), FDOM_FUPDATE, SUBSET_DEF] >>
  metis_tac[]
QED

(* FDOM of bp_process_block *)
Theorem bp_process_block_fdom:
  !bp insts c bp'.
    bp_process_block bp insts = (c, bp') ==>
    FDOM bp' SUBSET
      FDOM bp UNION BIGUNION (set (MAP (set o inst_defs) insts))
Proof
  Induct_on `insts`
  >- (simp[bp_process_block_def] >> simp[SUBSET_DEF]) >>
  rpt strip_tac >>
  fs[bp_process_block_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  drule bp_handle_inst_fdom >>
  first_x_assum drule >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem phi_pairs_mem_operand_vars:
  !ops x. MEM x (MAP SND (phi_pairs ops)) ==> MEM x (operand_vars ops)
Proof
  ho_match_mp_tac phi_pairs_ind >> rpt strip_tac >>
  gvs[phi_pairs_def, operand_vars_def, operand_var_def] >>
  Cases_on `v1` >> gvs[operand_vars_def, operand_var_def]
QED

(* For tracking opcodes, when output var is NOT in FDOM bp (fresh), the
   output ptrs depend only on non-output input ptrs. *)
Theorem bp_handle_inst_tracking_output_ptrs:
  !bp1 bp2 inst c1 bp1' c2 bp2' out.
    bp_handle_inst bp1 inst = (c1, bp1') /\
    bp_handle_inst bp2 inst = (c2, bp2') /\
    inst_output inst = SOME out /\
    inst_wf inst /\
    out NOTIN FDOM bp1 /\ out NOTIN FDOM bp2 /\
    (inst.inst_opcode = ALLOCA \/ inst.inst_opcode = ADD \/
     inst.inst_opcode = SUB \/ inst.inst_opcode = ASSIGN) /\
    (!v. v <> out ==> bp_get_ptrs bp1 v = bp_get_ptrs bp2 v) /\
    EVERY (\v. v <> out) (inst_uses inst) ==>
    bp_get_ptrs bp1' out = bp_get_ptrs bp2' out
Proof
  rpt strip_tac >>
  `inst.inst_outputs = [out]` by (drule_all inst_wf_outputs_some >> simp[]) >>
  (* Key: bp_get_ptrs bp_i out = [] since out ∉ FDOM bp_i *)
  `bp_get_ptrs bp1 out = []` by simp[bp_get_ptrs_def, FLOOKUP_DEF] >>
  `bp_get_ptrs bp2 out = []` by simp[bp_get_ptrs_def, FLOOKUP_DEF] >>
  (* Rewrite operand bp_get_ptrs to use bp2 everywhere.
     inst_uses gives all operand vars; EVERY says they're ≠ out. *)
  `!v. MEM v (inst_uses inst) ==> bp_get_ptrs bp1 v = bp_get_ptrs bp2 v` by
    metis_tac[EVERY_MEM] >>
  (* Now expand bp_handle_inst and case-split on opcode *)
  qpat_x_assum `bp_handle_inst bp1 _ = _` mp_tac >>
  qpat_x_assum `bp_handle_inst bp2 _ = _` mp_tac >>
  rewrite_tac[bp_handle_inst_def, inst_output_def] >>
  asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >> BETA_TAC >>
  Cases_on `inst.inst_opcode` >> gvs[] >>
  rpt strip_tac >> gvs[] >>
  (* ALLOCA: result independent of bp *)
  TRY (gvs[bp_get_ptrs_def, FLOOKUP_UPDATE] >> NO_TAC) >>
  (* ADD/SUB/ASSIGN: use operand bp_get_ptrs agreement *)
  TRY (
    BasicProvers.EVERY_CASE_TAC >> gvs[bp_get_ptrs_def, FLOOKUP_UPDATE] >>
    gvs[inst_uses_def, operand_vars_def, operand_var_def] >> NO_TAC) >>
  (* All other cases (PHI, etc.) now excluded by hypothesis *)
  gvs[]
QED

(* For non-tracking opcodes with output, bp_handle_inst doesn't modify bp. *)
Theorem bp_handle_inst_passthrough_output:
  !bp inst c bp' out.
    bp_handle_inst bp inst = (c, bp') /\
    inst_output inst = SOME out /\
    inst_wf inst /\
    inst.inst_opcode <> ALLOCA /\ inst.inst_opcode <> ADD /\
    inst.inst_opcode <> SUB /\ inst.inst_opcode <> ASSIGN ==>
    bp' = bp
Proof
  rpt strip_tac >>
  drule_all inst_wf_outputs_some >> strip_tac >>
  qpat_x_assum `bp_handle_inst _ _ = _` mp_tac >>
  once_rewrite_tac[bp_handle_inst_def] >>
  asm_rewrite_tac[] >>
  simp_tac std_ss [LET_THM] >> BETA_TAC >>
  Cases_on `inst.inst_opcode` >> gvs[]
QED
