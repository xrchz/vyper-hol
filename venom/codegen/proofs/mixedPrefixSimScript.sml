(*
 * Mixed Prefix Simulation: prefix ops (including SOSpill/SORestore)
 * preserve full venom_asm_rel.
 *
 * Generalizes simple_prefix_venom_asm_rel to handle SOSpill and SORestore
 * in addition to simple stack ops.
 *
 * Key results:
 *   single_mixed_op_sim        — single prefix op preserves venom_asm_rel
 *   mixed_prefix_venom_asm_rel — op list preserves venom_asm_rel
 *)

Theory mixedPrefixSim
Ancestors
  strongPrefixSim spillSim planWf
  codegenRel stackOpSim stackOpAsmSim prefixExec
  asmSem stackPlanTypes planExec stackModel
  blockSimHelpers instSimHelpers asmToBytecodeProofs
  list rich_list
Libs BasicProvers

(* =========================================================================
   Plan state transformation for ALL prefix ops
   ========================================================================= *)

(* Reverse lookup: find the operand stored at a given spill offset via Hilbert choice *)
Definition spill_lookup_def:
  spill_lookup off spilled = @op. FLOOKUP spilled op = SOME off
End

Definition apply_prefix_op_def:
  apply_prefix_op initial_fmp lo (SOSpill off) ps =
    ps with <| ps_stack := stack_pop 1 ps.ps_stack;
               ps_spilled := ps.ps_spilled |+
                 (stack_peek 0 ps.ps_stack, off);
               ps_alloc := ps.ps_alloc with
                 sa_next_offset := MAX ps.ps_alloc.sa_next_offset (off + 32)
             |> /\
  apply_prefix_op initial_fmp lo (SORestore off) ps =
    (let op = spill_lookup off ps.ps_spilled in
     ps with <| ps_stack := stack_push op ps.ps_stack;
                ps_spilled := ps.ps_spilled \\ op |>) /\
  apply_prefix_op initial_fmp lo SOInitialFmp ps =
    ps with ps_stack := stack_push (Lit (n2w initial_fmp)) ps.ps_stack /\
  apply_prefix_op initial_fmp lo (SOPush op) ps = apply_simple_op lo (SOPush op) ps /\
  apply_prefix_op initial_fmp lo (SOPop n) ps = apply_simple_op lo (SOPop n) ps /\
  apply_prefix_op initial_fmp lo (SOSwap n) ps = apply_simple_op lo (SOSwap n) ps /\
  apply_prefix_op initial_fmp lo (SODup n) ps = apply_simple_op lo (SODup n) ps /\
  apply_prefix_op initial_fmp lo (SOPoke n op) ps = apply_simple_op lo (SOPoke n op) ps /\
  apply_prefix_op initial_fmp lo (SOEmit name) ps = apply_simple_op lo (SOEmit name) ps /\
  apply_prefix_op initial_fmp lo (SOLabel lbl) ps = apply_simple_op lo (SOLabel lbl) ps /\
  apply_prefix_op initial_fmp lo (SOPushLabel lbl) ps = apply_simple_op lo (SOPushLabel lbl) ps /\
  apply_prefix_op initial_fmp lo (SOPushOfst lbl off) ps =
    apply_simple_op lo (SOPushOfst lbl off) ps
End

Definition apply_prefix_ops_def:
  apply_prefix_ops initial_fmp lo [] ps = ps /\
  apply_prefix_ops initial_fmp lo (op::rest) ps =
    apply_prefix_ops initial_fmp lo rest (apply_prefix_op initial_fmp lo op ps)
End

(* =========================================================================
   Well-formedness predicate for spill/restore ops
   ========================================================================= *)

(* Additional well-formedness conditions for spill/restore ops *)
Definition spill_op_wf_def:
  spill_op_wf ps (SOSpill off) =
    (off < dimword(:256) /\
     ps.ps_alloc.sa_spill_base <= off /\
     (!op2 off2. FLOOKUP ps.ps_spilled op2 = SOME off2 ==>
                 off2 + 32 <= off \/ off + 32 <= off2)) /\
  spill_op_wf ps (SORestore off) =
    (off < dimword(:256) /\
     (?op. FLOOKUP ps.ps_spilled op = SOME off)) /\
  spill_op_wf ps (SOPush op) = T /\
  spill_op_wf ps (SOPop n) = T /\
  spill_op_wf ps (SOSwap n) = T /\
  spill_op_wf ps (SODup n) = T /\
  spill_op_wf ps (SOPoke n op) = T /\
  spill_op_wf ps (SOEmit name) = T /\
  spill_op_wf ps SOInitialFmp = T /\
  spill_op_wf ps (SOLabel lbl) = T /\
  spill_op_wf ps (SOPushLabel lbl) = T /\
  spill_op_wf ps (SOPushOfst lbl off) = T
End

(* Threaded well-formedness: each op is ok given the plan state at that point *)
Definition prefix_spill_wf_def:
  prefix_spill_wf initial_fmp lo [] ps = T /\
  prefix_spill_wf initial_fmp lo (op::rest) ps =
    (spill_op_wf ps op /\
     prefix_spill_wf initial_fmp lo rest
       (apply_prefix_op initial_fmp lo op ps))
End

(* is_prefix_op (from prefixSimTheory): T for all constructors except SOEmit *)

(* =========================================================================
   Hilbert choice helper for SORestore
   ========================================================================= *)

Theorem spill_lookup_flookup[local]:
  !off ps.
    (?op. FLOOKUP ps.ps_spilled op = SOME off) ==>
    FLOOKUP ps.ps_spilled (spill_lookup off ps.ps_spilled) = SOME off
Proof
  rpt strip_tac >>
  simp[spill_lookup_def] >>
  SELECT_ELIM_TAC >>
  metis_tac[]
QED

(* =========================================================================
   LENGTH helper: apply_prefix_op preserves stack_op_wf length invariant
   ========================================================================= *)

Theorem apply_prefix_op_length[local]:
  !initial_fmp lo op ps.
    is_prefix_op op ==>
    LENGTH (apply_prefix_op initial_fmp lo op ps).ps_stack =
      SND (stack_op_wf lo op (LENGTH ps.ps_stack))
Proof
  rpt strip_tac >>
  Cases_on `op` >>
  gvs[prefixSimTheory.is_prefix_op_def, apply_prefix_op_def,
      is_simple_stack_op_def, apply_simple_op_def, stack_op_wf_def,
      stack_pop_def, stack_push_def, stack_swap_def,
      LENGTH_TAKE_EQ, LENGTH_LUPDATE] >>
  TRY (Cases_on `o'` >>
       gvs[is_simple_stack_op_def, apply_simple_op_def, stack_op_wf_def,
           stack_push_def])
QED

(* =========================================================================
   Unified single-op simulation
   ========================================================================= *)

val simple_prefix_tac =
  simp[apply_prefix_op_def] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  match_mp_tac simple_op_venom_asm_rel >>
  simp[is_simple_stack_op_def];

val zero_op_tac =
  simp[apply_prefix_op_def, apply_simple_op_def,
       exec_stack_op_def, asm_steps_def];

Theorem single_mixed_op_sim:
  !initial_fmp op lo o2pc prog ps vs st.
    is_prefix_op op /\
    FST (stack_op_wf lo op (LENGTH ps.ps_stack)) /\
    spill_op_wf ps op /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (exec_stack_op initial_fmp op) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (exec_stack_op initial_fmp op)) st = AsmOK st' /\
          venom_asm_rel lo (apply_prefix_op initial_fmp lo op ps) vs st' /\
          st'.as_pc = st.as_pc + LENGTH (exec_stack_op initial_fmp op)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `op` >> gvs[prefixSimTheory.is_prefix_op_def]
  (* Order: SOPush SOPop SOSwap SODup SOPoke SOSpill SORestore
            SOLabel SOPushLabel SOPushOfst *)
  >- (Cases_on `o'` >>
      PURE_REWRITE_TAC[apply_prefix_op_def]
      (* Lit: delegate to simple_op_venom_asm_rel *)
      >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
          match_mp_tac simple_op_venom_asm_rel >>
          simp[is_simple_stack_op_def])
      (* Var: zero asm instructions, plan-state-only change *)
      >- (simp[exec_stack_op_def, Once asm_steps_def, asm_block_at_nil,
               apply_simple_op_def, stack_push_def] >>
          fs[venom_asm_rel_def, plan_stack_rel_def])
      (* Label: delegate to simple_op_venom_asm_rel *)
      >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
          match_mp_tac simple_op_venom_asm_rel >>
          simp[is_simple_stack_op_def]))  (* SOPush *)
  >- simple_prefix_tac  (* SOPop *)
  >- simple_prefix_tac  (* SOSwap *)
  >- simple_prefix_tac  (* SODup *)
  >- zero_op_tac        (* SOPoke *)
  >- (gvs[spill_op_wf_def, stack_op_wf_def, exec_stack_op_def,
          apply_prefix_op_def] >>
      match_mp_tac spill_op_venom_asm_rel >> rpt conj_tac >> fs[])  (* SOSpill *)
  >- (gvs[spill_op_wf_def, exec_stack_op_def, apply_prefix_op_def] >>
      SUBGOAL_THEN
        ``FLOOKUP ps.ps_spilled (spill_lookup n ps.ps_spilled) = SOME n``
        ASSUME_TAC
      >- (irule spill_lookup_flookup >> metis_tac[]) >>
      qspecl_then [`lo`, `o2pc`, `prog`, `n`,
                   `spill_lookup n ps.ps_spilled`, `ps`, `vs`, `st`]
        mp_tac restore_op_venom_asm_rel >>
      simp[])  (* SORestore *)
  >- (gvs[stack_op_wf_def, exec_stack_op_def, apply_prefix_op_def,
          stack_push_def] >>
      match_mp_tac initial_fmp_push_venom_asm_rel >> simp[])  (* SOInitialFmp *)
  >- simple_prefix_tac  (* SOLabel *)
  >- simple_prefix_tac  (* SOPushLabel *)
  (* SOPushOfst — like SOPushLabel but with offset delta *)
  >- (gvs[stack_op_wf_def, exec_stack_op_def] >>
      `?off. FLOOKUP lo s = SOME off` by
        (Cases_on `FLOOKUP lo s` >> gvs[]) >>
      drule_all simple_op_push_ofst >>
      simp[apply_prefix_op_def, apply_simple_op_def])
QED

(* =========================================================================
   Mixed prefix simulation (inductive)
   ========================================================================= *)

Theorem mixed_prefix_venom_asm_rel:
  !ops initial_fmp lo o2pc prog ps vs st.
    prefix_wf lo (LENGTH ps.ps_stack) ops /\
    prefix_spill_wf initial_fmp lo ops ps /\
    EVERY is_prefix_op ops /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo (apply_prefix_ops initial_fmp lo ops ps) vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  Induct_on `ops`
  >- (rpt strip_tac >>
      simp[Once asm_steps_def, execute_plan_def, apply_prefix_ops_def])
  >> rpt gen_tac >> strip_tac >>
  rename1 `op :: ops` >>
  fs[EVERY_DEF, apply_prefix_ops_def, execute_plan_def,
     prefix_spill_wf_def] >>
  (* Decompose prefix_wf for cons *)
  fs[Once prefix_wf_cons] >>
  pairarg_tac >> gvs[] >>
  (* Decompose asm_block_at for append *)
  qpat_x_assum `asm_block_at _ _ (exec_stack_op initial_fmp op ++ _)` mp_tac >>
  REWRITE_TAC[asm_block_at_append] >> strip_tac >>
  (* Apply single-op lemma *)
  mp_tac single_mixed_op_sim >>
  disch_then (qspecl_then [`initial_fmp`, `op`, `lo`, `o2pc`, `prog`, `ps`, `vs`, `st`]
    mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  (* Apply IH: need LENGTH (apply_prefix_op ...).ps_stack = n' *)
  first_x_assum (qspecl_then [`initial_fmp`, `lo`, `o2pc`, `prog`,
    `apply_prefix_op initial_fmp lo op ps`, `vs`, `st'`] mp_tac) >>
  (impl_tac >- (
    qpat_assum `is_prefix_op _`
      (fn th => REWRITE_TAC[MATCH_MP apply_prefix_op_length th]) >>
    fs[])) >>
  strip_tac >>
  (* Compose asm_steps *)
  qexists_tac `st''` >> simp[] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  match_mp_tac (GEN_ALL asm_steps_compose_ok) >>
  qexists_tac `st'` >> fs[]
QED
