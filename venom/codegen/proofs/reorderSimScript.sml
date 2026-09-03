(*
 * Reorder Plan Simulation
 *
 * Key results:
 *   reorder_plan_eq_plan_steps — FOLDL bridge to plan_steps
 *   plan_stack_rel_poke/poke_swap — moved to instSimHelpers
 *   reorder_single_op_at_tos — single-operand reorder puts op at TOS
 *)

Theory reorderSim
Ancestors
  foldlSim doSwapSim spillSim instSimHelpers strongPrefixSim
  stackOpSim mixedPrefixSim planAlign
  stackPlanGen stackPlanOps stackPlanTypes stackModel
  codegenRel asmSem planExec planWf
  indexedLists list rich_list finite_map arithmetic


(* Value-sensitive equality for planner stacks.  Reorder may replace an
   operand by an operand_equiv alias without changing its runtime value. *)
Definition plan_stack_sem_eq_def:
  plan_stack_sem_eq lo vs (s1 : operand list) s2 <=>
    LENGTH s1 = LENGTH s2 /\
    !i. i < LENGTH s1 ==>
      operand_val vs lo (EL i s1) = operand_val vs lo (EL i s2)
End

Theorem plan_stack_sem_eq_refl[simp]:
  !lo vs s. plan_stack_sem_eq lo vs s s
Proof
  simp[plan_stack_sem_eq_def]
QED

Theorem plan_stack_sem_eq_trans:
  !lo vs s1 s2 s3.
    plan_stack_sem_eq lo vs s1 s2 /\
    plan_stack_sem_eq lo vs s2 s3 ==>
    plan_stack_sem_eq lo vs s1 s3
Proof
  simp[plan_stack_sem_eq_def] >> metis_tac[]
QED

Theorem plan_stack_sem_eq_map_values:
  !lo vs s1 s2.
    plan_stack_sem_eq lo vs s1 s2 ==>
    MAP (operand_val vs lo) s1 = MAP (operand_val vs lo) s2
Proof
  rw[plan_stack_sem_eq_def, LIST_EQ_REWRITE] >>
  `x < LENGTH s1` by decide_tac >>
  simp[EL_MAP] >>
  qpat_assum `!i. _` (qspec_then `x` mp_tac) >> simp[]
QED

Theorem plan_stack_sem_eq_lastn:
  !lo vs s1 s2 n.
    plan_stack_sem_eq lo vs s1 s2 ==>
    MAP (operand_val vs lo) (LASTN n s1) =
    MAP (operand_val vs lo) (LASTN n s2)
Proof
  rpt strip_tac >> drule plan_stack_sem_eq_map_values >>
  simp[rich_listTheory.LASTN_def, MAP_REVERSE, MAP_TAKE]
QED

Theorem plan_stack_sem_eq_last:
  !lo vs s1 s2.
    plan_stack_sem_eq lo vs s1 s2 /\ s1 <> [] ==>
    operand_val vs lo (LAST s1) = operand_val vs lo (LAST s2)
Proof
  rpt strip_tac >>
  `s2 <> []` by (strip_tac >> gvs[plan_stack_sem_eq_def]) >>
  drule plan_stack_sem_eq_lastn >>
  disch_then (qspec_then `1` mp_tac) >>
  simp[rich_listTheory.LASTN_1]
QED

Theorem plan_stack_sem_eq_poke:
  !lo vs s1 s2 d op1 op2.
    plan_stack_sem_eq lo vs s1 s2 /\
    operand_val vs lo op1 = operand_val vs lo op2 ==>
    plan_stack_sem_eq lo vs
      (stack_poke d op1 s1) (stack_poke d op2 s2)
Proof
  rw[plan_stack_sem_eq_def, stack_poke_def] >>
  simp[listTheory.LUPDATE_SEM] >>
  rpt strip_tac >>
  Cases_on `i = LENGTH s1 - 1 - d` >> simp[]
QED

(* =========================================================================
   Bridge: reorder_plan = plan_steps (reorder_one ...)
   ========================================================================= *)

Theorem reorder_foldl_body_eq[local]:
  !dfg target_ops.
    foldl_body (\(idx,op) ps. reorder_one dfg target_ops idx op ps) =
    (\(ops, ps) (idx, op).
      let (step_ops, ps') = reorder_one dfg target_ops idx op ps in
      (ops ++ step_ops, ps'))
Proof
  rpt gen_tac >>
  simp[FUN_EQ_THM, foldl_body_def, pairTheory.FORALL_PROD]
QED

Theorem reorder_plan_eq_plan_steps:
  !dfg target_ops ps.
    reorder_plan dfg target_ops ps =
    plan_steps (\(idx,op) ps. reorder_one dfg target_ops idx op ps)
      (MAPi (\i op. (i, op)) target_ops) ps
Proof
  rpt gen_tac >>
  REWRITE_TAC[reorder_plan_def] >>
  REWRITE_TAC[GSYM reorder_foldl_body_eq] >>
  REWRITE_TAC[GSYM plan_steps_eq_foldl]
QED

(* plan_stack_rel_poke and plan_stack_rel_poke_swap moved to instSimHelpers *)

(* =========================================================================
   Stack Model Helpers
   ========================================================================= *)

(* stack_find returns element satisfying predicate *)
Theorem stack_find_el[local]:
  !p xs d. stack_find p xs = SOME d ==> p (EL d xs)
Proof
  Induct_on `xs` >> simp[stack_find_def] >>
  rpt gen_tac >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `stack_find p xs` >> simp[] >>
  strip_tac >> gvs[] >>
  simp[EL_CONS]
QED

(* stack_get_depth gives EL relationship *)
Theorem stack_get_depth_el[local]:
  !op stk d.
    stack_get_depth op stk = SOME d ==>
    EL (LENGTH stk - 1 - d) stk = op
Proof
  rpt gen_tac >> simp[stack_get_depth_def] >> strip_tac >>
  imp_res_tac stack_find_bound >>
  imp_res_tac stack_find_el >> fs[] >>
  (* Have: EL d (REVERSE stk) = op, d < LENGTH (REVERSE stk) *)
  (* EL_REVERSE: n < LENGTH l ==> EL n (REVERSE l) = EL (PRE (LENGTH l - n)) l *)
  mp_tac (SPECL [``d:num``, ``stk:'a list``] EL_REVERSE) >>
  fs[LENGTH_REVERSE] >>
  strip_tac >>
  (* Now have: EL (PRE (LENGTH stk - d)) stk = EL d (REVERSE stk) = op *)
  `PRE (LENGTH (stk:'a list) - d) = LENGTH stk - 1 - d`
    suffices_by (disch_then (fn th => fs[th])) >>
  decide_tac
QED

(* stack_get_depth implies non-empty and bounded *)
Theorem stack_get_depth_bound[local]:
  !op stk d. stack_get_depth op stk = SOME d ==>
    d < LENGTH stk /\ stk <> []
Proof
  rpt strip_tac
  >- (fs[stack_get_depth_def] >> imp_res_tac stack_find_bound >> fs[])
  >- (Cases_on `stk` >> fs[stack_get_depth_def, stack_find_def])
QED

(* stack_get_depth = SOME 0 means LAST stk = op *)
Theorem stack_get_depth_zero_last[local]:
  !op stk. stack_get_depth op stk = SOME 0 ==>
    stk <> [] /\ LAST stk = op
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac stack_get_depth_bound >> simp[] >>
  imp_res_tac stack_get_depth_el >> gvs[] >>
  simp[LAST_EL] >>
  imp_res_tac (DECIDE ``0:num < n ==> PRE n = n - 1``) >>
  ASM_REWRITE_TAC[]
QED

(* stack_poke preserves non-empty (general) *)
Theorem stack_poke_nonempty[local]:
  !d op stk. stk <> [] ==> stack_poke d op stk <> []
Proof
  rpt gen_tac >> strip_tac >>
  REWRITE_TAC[GSYM LENGTH_NIL] >>
  simp[stack_poke_def, LENGTH_LUPDATE] >>
  Cases_on `stk` >> fs[]
QED

(* stack_poke at 0 sets LAST *)
Theorem stack_poke_zero_last[local]:
  !op stk. stk <> [] ==> LAST (stack_poke 0 op stk) = op
Proof
  rpt strip_tac >> simp[stack_poke_def] >>
  `LENGTH stk >= 1` suffices_by
    (strip_tac >> simp[LAST_EL, LENGTH_LUPDATE, EL_LUPDATE]) >>
  Cases_on `stk` >> fs[]
QED

(* stack_swap preserves LAST position *)
Theorem stack_swap_last[local]:
  !d stk.
    d < LENGTH stk /\ stk <> [] ==>
    LAST (stack_swap d stk) =
    EL (LENGTH stk - 1 - d) stk
Proof
  rpt strip_tac >>
  simp[stack_swap_def, LET_THM,
       LAST_EL, LENGTH_LUPDATE, EL_LUPDATE] >>
  IF_CASES_TAC
  >- (
    (* PRE (LENGTH stk) = LENGTH stk - (d+1), so d = 0 *)
    imp_res_tac (DECIDE ``(d:num) < n /\ PRE n = n - (d + 1) ==> d = 0``) >>
    gvs[]
  ) >>
  simp[]
QED

(* stack_swap preserves non-empty *)
Theorem stack_swap_nonempty[local]:
  !d stk. stk <> [] ==> stack_swap d stk <> []
Proof
  rpt gen_tac >> strip_tac >>
  REWRITE_TAC[GSYM LENGTH_NIL] >>
  simp[stack_swap_def, LET_THM, LENGTH_LUPDATE] >>
  Cases_on `stk` >> fs[]
QED

(* do_swap deep: ps_stack is a specific expression *)
Theorem do_swap_deep_stack[local]:
  !dist ps. ~(dist = 0) /\ ~(dist <= 16) /\
    dist < LENGTH ps.ps_stack ==>
    (SND (do_swap dist ps)).ps_stack =
    TAKE (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack ++
    MAP (\idx. EL idx (top_n (dist + 1) ps.ps_stack))
      ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0])
Proof
  rpt strip_tac >>
  simp[do_swap_def, LET_THM] >>
  pairarg_tac >> simp[]
QED

(* do_swap dist puts element at depth dist at TOS (LAST) *)
Theorem do_swap_last[local]:
  !dist ps op.
    stack_get_depth op ps.ps_stack = SOME dist /\ dist <> 0 /\
    dist < LENGTH ps.ps_stack ==>
    LAST (SND (do_swap dist ps)).ps_stack = op /\
    (SND (do_swap dist ps)).ps_stack <> []
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac stack_get_depth_el >>
  `ps.ps_stack <> []` by (Cases_on `ps.ps_stack` >> fs[]) >>
  Cases_on `dist <= 16`
  >- simp[do_swap_def, stack_swap_last, stack_swap_nonempty]
  >>
  qspecl_then [`dist`, `ps`] mp_tac do_swap_deep_stack >>
  simp[] >> strip_tac >>
  simp[top_n_def, GSYM rich_listTheory.LASTN_def,
       rich_listTheory.LASTN_DROP] >>
  once_rewrite_tac[GSYM (cj 1 EL)] >>
  simp[EL_DROP] >>
  `LENGTH ps.ps_stack - 1 - dist =
   LENGTH ps.ps_stack - (dist + 1)` by simp[] >>
  fs[]
QED

(* =========================================================================
   Single-operand reorder puts operand at TOS

   When reorder_plan is called with [op], final_dist = 0, so every
   code path (depth 0 no-op, shallow swap, equiv poke, restore from
   spill) ends with op at LAST ps'.ps_stack.
   ========================================================================= *)

Theorem reorder_single_op_at_tos:
  !dfg op ps rops ps'.
    ((?d. stack_get_depth op ps.ps_stack = SOME d) \/
     (stack_get_depth op ps.ps_stack = NONE /\
      IS_SOME (FLOOKUP ps.ps_spilled op))) /\
    reorder_plan dfg [op] ps = (rops, ps') ==>
    ps'.ps_stack <> [] /\ LAST ps'.ps_stack = op
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  simp[reorder_plan_def, MAPi_def, MAPi_ACC_def, LET_THM] >>
  Cases_on `reorder_one dfg [op] 0 op ps` >>
  simp[] >> strip_tac >> gvs[]
  >- (
    (* Case 1: op on stack at depth d *)
    rename1 `stack_get_depth op ps.ps_stack = SOME d0` >>
    qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
    simp[reorder_one_def, LET_THM] >>
    imp_res_tac stack_get_depth_bound >>
    Cases_on `d0 > 16`
    >- suspend "deep"
    >> (* d <= 16 *)
    `~(d0 > 16)` by simp[] >> simp[] >>
    Cases_on `d0 = 0`
    >- (
      simp[] >> strip_tac >> gvs[] >>
      imp_res_tac stack_get_depth_zero_last >> simp[])
    >> imp_res_tac (DECIDE ``(d:num) < (n:num) /\ d <> 0 ==> 0 < n``) >>
    simp[] >>
    Cases_on `operand_equiv dfg op (stack_peek 0 ps.ps_stack)`
    >- (
      simp[] >> strip_tac >> gvs[] >>
      conj_tac
      >- (irule stack_poke_nonempty >>
          irule stack_poke_nonempty >> simp[])
      >> (irule stack_poke_zero_last >>
          irule stack_poke_nonempty >> simp[]))
    >> simp[do_swap_def] >> strip_tac >> gvs[] >>
    conj_tac
    >- (irule stack_swap_nonempty >> simp[])
    >> (imp_res_tac stack_get_depth_el >> simp[stack_swap_last]))
  >> (* Case 2: op not on stack, but spilled *)
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  rename1 `IS_SOME (FLOOKUP ps.ps_spilled op)` >>
  simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- fs[]
  >> rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  simp[do_restore_def, stack_push_def, stack_get_depth_def,
       REVERSE_SNOC, stack_find_def] >>
  strip_tac >> gvs[] >>
  simp[LAST_SNOC, SNOC_APPEND]
QED

Resume reorder_single_op_at_tos[deep]:
  simp[] >> pairarg_tac >> simp[] >>
  rename1 `reduce_depth_plan _ _ _ _ = (reduce_ops, ps2)` >>
  qspecl_then [`LENGTH ps.ps_stack`, `[op]`, `op`, `ps`, `d0`]
    mp_tac (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)
              (REWRITE_RULE [LET_THM] reduce_depth_plan_dist_ge)) >>
  (impl_tac >- simp[]) >> simp[] >> strip_tac >>
  Cases_on `d'` >- fs[] >>
  rename1 `stack_get_depth op ps2.ps_stack = SOME (SUC n)` >>
  qpat_assum `stack_get_depth _ _ = SOME (SUC _)`
    (strip_assume_tac o MATCH_MP stack_get_depth_bound) >>
  simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek 0 ps2.ps_stack)`
  >- (
    strip_tac >> gvs[] >> conj_tac
    >- (irule stack_poke_nonempty >>
        irule stack_poke_nonempty >> simp[])
    >> (irule stack_poke_zero_last >>
        irule stack_poke_nonempty >> simp[]))
  >> pairarg_tac >> simp[] >>
  simp[do_swap_def] >> strip_tac >> gvs[] >>
  qspecl_then [`SUC n`, `ps2`, `op`] mp_tac do_swap_last >>
  simp[]
QED

Finalise reorder_single_op_at_tos;

(* =========================================================================
   After executing the reorder ops for a single operand, the operand's
   value sits at the top of the asm stack.

   This differs from reorder_single_op_at_tos which describes the
   FORMAL plan output ps' (which includes bookkeeping pokes).  Here we
   describe the ACTUAL state after apply_prefix_ops, using plan_stack_rel
   and operand_equiv soundness to bridge the poke case.
   ========================================================================= *)

Theorem reorder_single_op_val_on_tos:
  !dfg op ps rops ps' lo vs as_stk.
    reorder_plan dfg [op] ps = (rops, ps') /\
    (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 16) /\
    plan_stack_rel lo vs
      (apply_prefix_ops initial_fmp lo rops ps).ps_stack as_stk /\
    as_stk <> [] /\
    (!at. operand_equiv dfg op at ==>
          operand_val vs lo op = operand_val vs lo at) ==>
    operand_val vs lo op = SOME (HD as_stk)
Proof
  rpt gen_tac >> strip_tac >>
  (* Unfold reorder_plan for [op] *)
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  simp[reorder_plan_def, MAPi_def, MAPi_ACC_def, LET_THM] >>
  Cases_on `reorder_one dfg [op] 0 op ps` >>
  simp[] >> strip_tac >> gvs[] >>
  (* Unfold reorder_one with final_dist = 0 *)
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  rename1 `stack_get_depth op ps.ps_stack = SOME d0` >>
  imp_res_tac (DECIDE ``(d:num) <= 16 ==> ~(d > 16)``) >>
  imp_res_tac stack_get_depth_bound >>
  simp[] >>
  (* All cases: extract plan_stack_rel_hd at the end *)
  (* Helper: given LAST stk = x, plan_stack_rel lo vs stk as_stk, stk <> [],
     we get operand_val vs lo x = SOME (HD as_stk) *)
  Cases_on `d0 = 0`
  >- (
    (* depth 0: already at TOS, no ops *)
    simp[] >> strip_tac >> gvs[] >>
    fs[apply_prefix_ops_def] >>
    imp_res_tac stack_get_depth_zero_last >>
    qspecl_then [`lo`,`vs`,`ps.ps_stack`,`as_stk`] mp_tac plan_stack_rel_hd >>
    ASM_REWRITE_TAC[] >> strip_tac >> gvs[]
  ) >>
  imp_res_tac (DECIDE ``(d:num) < (n:num) /\ d <> 0 ==> 0 < n``) >>
  simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek 0 ps.ps_stack)`
  >- (
    (* operand_equiv: poke only, no asm ops *)
    simp[] >> strip_tac >> gvs[] >>
    fs[apply_prefix_ops_def] >>
    (* operand_equiv soundness gives operand_val op = operand_val at_target *)
    first_x_assum (qspec_then `stack_peek 0 ps.ps_stack` mp_tac) >>
    simp[] >> strip_tac >>
    (* Now: operand_val op = operand_val (stack_peek 0 stk) *)
    (* stack_peek 0 stk = LAST stk, and plan_stack_rel_hd gives the result *)
    qspecl_then [`lo`,`vs`,`ps.ps_stack`,`as_stk`] mp_tac plan_stack_rel_hd >>
    ASM_REWRITE_TAC[] >> strip_tac >>
    (* Rewrite stack_peek 0 to LAST *)
    `stack_peek 0 ps.ps_stack = LAST ps.ps_stack` by (
      simp[stack_peek_def, LAST_EL] >>
      Cases_on `ps.ps_stack` >> fs[]) >>
    gvs[]
  ) >>
  (* no operand_equiv: do_swap d0, do_swap 0 *)
  simp[do_swap_def] >>
  strip_tac >> gvs[] >>
  fs[apply_prefix_ops_def, apply_prefix_op_def,
     apply_simple_op_def] >>
  (* After SOSwap d0: stack_swap d0 ps.ps_stack *)
  `LAST (stack_swap d0 ps.ps_stack) = op` by (
    imp_res_tac stack_get_depth_el >>
    simp[stack_swap_last]) >>
  qspecl_then [`lo`,`vs`,`stack_swap d0 ps.ps_stack`,`as_stk`]
    mp_tac plan_stack_rel_hd >>
  simp[stack_swap_nonempty] >> ASM_REWRITE_TAC[] >> strip_tac >> gvs[]
QED

(* =========================================================================
   Alignment: apply_prefix_ops of reduce_depth_plan ops = bookkeeping
   ========================================================================= *)

(* do_spill_at: ops applied to same state give same ps_stack *)
(* SOSwap/SOSpill/SORestore: stack+spilled independence (single op) *)
Theorem apply_ssr_indep[local]:
  !op lo ps1 ps2.
    ((?d. op = SOSwap d) \/ (?off. op = SOSpill off) \/
     (?off. op = SORestore off)) /\
    ps1.ps_stack = ps2.ps_stack /\
    ps1.ps_spilled = ps2.ps_spilled ==>
    (apply_prefix_op initial_fmp lo op ps1).ps_stack =
      (apply_prefix_op initial_fmp lo op ps2).ps_stack /\
    (apply_prefix_op initial_fmp lo op ps1).ps_spilled =
      (apply_prefix_op initial_fmp lo op ps2).ps_spilled
Proof
  rpt gen_tac >> strip_tac >>
  gvs[apply_prefix_op_def, apply_simple_op_def, LET_THM,
      spill_lookup_def]
QED

(* SOSwap/SOSpill/SORestore: stack+spilled independence (op list) *)
Theorem apply_ssr_ops_indep[local]:
  !ops lo ps1 ps2.
    EVERY (\op. (?d. op = SOSwap d) \/ (?off. op = SOSpill off) \/
                (?off. op = SORestore off)) ops /\
    ps1.ps_stack = ps2.ps_stack /\
    ps1.ps_spilled = ps2.ps_spilled ==>
    (apply_prefix_ops initial_fmp lo ops ps1).ps_stack =
      (apply_prefix_ops initial_fmp lo ops ps2).ps_stack /\
    (apply_prefix_ops initial_fmp lo ops ps1).ps_spilled =
      (apply_prefix_ops initial_fmp lo ops ps2).ps_spilled
Proof
  Induct >> simp[apply_prefix_ops_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum match_mp_tac >>
  metis_tac[apply_ssr_indep]
QED


(* Durable direct-state invariant used by deep reorder operations. *)
Theorem do_restore_structural_wf:
  !op ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
    spill_alloc_layout_wf (SND (do_restore op ps)).ps_alloc
                          (SND (do_restore op ps)).ps_spilled /\
    ALL_DISTINCT (SND (do_restore op ps)).ps_stack /\
    DISJOINT (set (SND (do_restore op ps)).ps_stack)
             (FDOM (SND (do_restore op ps)).ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- simp[do_restore_def]
  >> rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `spill_alloc_layout_wf (free_spill_slot off ps.ps_alloc)
     (ps.ps_spilled \\ op)` by
    metis_tac[spill_alloc_layout_wf_after_free] >>
  `op IN FDOM ps.ps_spilled` by fs[flookup_thm] >>
  `~MEM op ps.ps_stack` by (
    fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  fs[do_restore_def, stack_push_def] >>
  conj_tac >- simp[ALL_DISTINCT_SNOC] >>
  fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
     finite_mapTheory.FDOM_DOMSUB] >>
  gen_tac >> Cases_on `x = op` >> simp[] >> metis_tac[]
QED

Theorem do_spill_tos_structural_wf[local]:
  !ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    ps.ps_stack <> [] ==>
    spill_alloc_layout_wf (SND (do_spill_tos ps)).ps_alloc
                          (SND (do_spill_tos ps)).ps_spilled /\
    ALL_DISTINCT (SND (do_spill_tos ps)).ps_stack /\
    DISJOINT (set (SND (do_spill_tos ps)).ps_stack)
             (FDOM (SND (do_spill_tos ps)).ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  simp[do_spill_tos_def, LET_THM] >> pairarg_tac >> simp[] >>
  rename1 `alloc_spill_slot ps.ps_alloc = (off, al')` >>
  `spill_alloc_layout_wf al'
     (ps.ps_spilled |+ (stack_peek 0 ps.ps_stack, off))` by
    metis_tac[spill_alloc_layout_wf_after_alloc] >>
  simp[stack_pop_def, stack_peek_def] >>
  conj_tac
  >- simp[ALL_DISTINCT_TAKE] >>
  conj_tac
  >- (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
      metis_tac[MEM_TAKE]) >>
  `TAKE (LENGTH ps.ps_stack - 1) ps.ps_stack = FRONT ps.ps_stack` by
    simp[rich_listTheory.FRONT_BY_TAKE] >>
  `EL (LENGTH ps.ps_stack - 1) ps.ps_stack = LAST ps.ps_stack` by
    simp[LAST_EL, PRE_SUB1] >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `TAKE _ _ = FRONT _` SUBST1_TAC >>
  irule MEM_FRONT_NOT_LAST >> simp[]
QED

Theorem do_spill_at_structural_wf:
  !d ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    d < LENGTH ps.ps_stack ==>
    spill_alloc_layout_wf (SND (do_spill_at d ps)).ps_alloc
                          (SND (do_spill_at d ps)).ps_spilled /\
    ALL_DISTINCT (SND (do_spill_at d ps)).ps_stack /\
    DISJOINT (set (SND (do_spill_at d ps)).ps_stack)
             (FDOM (SND (do_spill_at d ps)).ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  `ps.ps_stack <> []` by (strip_tac >> gvs[]) >>
  Cases_on `d = 0`
  >- (simp[do_spill_at_def] >> irule do_spill_tos_structural_wf >> simp[]) >>
  simp[do_spill_at_def, LET_THM] >> pairarg_tac >> simp[] >>
  qspecl_then [`ps with ps_stack := stack_swap d ps.ps_stack`]
    mp_tac do_spill_tos_structural_wf >>
  simp[] >> disch_then irule >>
  `ALL_DISTINCT (stack_swap d ps.ps_stack) /\
   set (stack_swap d ps.ps_stack) = set ps.ps_stack` by
    (irule stack_swap_permutation >> simp[]) >>
  simp[] >>
  fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
  irule stack_swap_nonempty >> simp[]
QED

Theorem reduce_depth_plan_structural_wf:
  !fuel target_ops target_op ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
    spill_alloc_layout_wf
      (SND (reduce_depth_plan fuel target_ops target_op ps)).ps_alloc
      (SND (reduce_depth_plan fuel target_ops target_op ps)).ps_spilled /\
    ALL_DISTINCT
      (SND (reduce_depth_plan fuel target_ops target_op ps)).ps_stack /\
    DISJOINT
      (set (SND (reduce_depth_plan fuel target_ops target_op ps)).ps_stack)
      (FDOM (SND (reduce_depth_plan fuel target_ops target_op ps)).ps_spilled)
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_depth target_op ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x` >> simp[] >>
  pairarg_tac >> simp[] >>
  imp_res_tac stack_get_depth_bound >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  imp_res_tac select_spill_candidate_bound >>
  `spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
   ALL_DISTINCT ps'.ps_stack /\
   DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)` by (
    qspecl_then [`x'`, `ps`] mp_tac do_spill_at_structural_wf >> simp[]) >>
  first_x_assum (qspecl_then [`target_ops`, `target_op`, `ps'`] mp_tac) >>
  simp[] >> strip_tac >> pairarg_tac >> gvs[]
QED

(* do_spill_at: apply_prefix_ops aligns with do_spill_at on stack+spilled *)
Theorem do_spill_at_align[local]:
  !d ps lo.
    (apply_prefix_ops initial_fmp lo (FST (do_spill_at d ps)) ps).ps_stack =
      (SND (do_spill_at d ps)).ps_stack /\
    (apply_prefix_ops initial_fmp lo (FST (do_spill_at d ps)) ps).ps_spilled =
      (SND (do_spill_at d ps)).ps_spilled
Proof
  rpt gen_tac >>
  simp[do_spill_at_def, LET_THM] >>
  Cases_on `d = 0`
  >- (
    simp[do_spill_tos_def, LET_THM] >>
    Cases_on `alloc_spill_slot ps.ps_alloc` >>
    simp[apply_prefix_ops_def, apply_prefix_op_def])
  >>
  simp[do_spill_tos_def, LET_THM] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >>
  simp[apply_prefix_ops_def, apply_prefix_op_def, apply_simple_op_def]
QED

(* do_spill_at produces only SOSwap/SOSpill ops *)
Theorem do_spill_at_only_swap_spill[local]:
  !d ps.
    EVERY (\op. (?d. op = SOSwap d) \/ (?off. op = SOSpill off))
      (FST (do_spill_at d ps))
Proof
  rpt gen_tac >>
  simp[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `d = 0`
  >- (Cases_on `alloc_spill_slot ps.ps_alloc` >> simp[]) >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> simp[]
QED

(* reduce_depth_plan produces only SOSwap/SOSpill ops *)
Theorem reduce_depth_plan_only_swap_spill[local]:
  !fuel target_ops target_op ps.
    EVERY (\op. (?d. op = SOSwap d) \/ (?off. op = SOSpill off))
      (FST (reduce_depth_plan fuel target_ops target_op ps))
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >>
  Cases_on `stack_get_depth target_op ps.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x` >> simp[] >>
  Cases_on `do_spill_at x' ps` >>
  rename1 `do_spill_at _ ps = (spill_ops, ps1)` >> simp[] >>
  Cases_on `reduce_depth_plan fuel target_ops target_op ps1` >>
  rename1 `reduce_depth_plan _ _ _ _ = (rest_ops, ps2)` >>
  simp[EVERY_APPEND] >> conj_tac
  >- (`spill_ops = FST (do_spill_at x' ps)` by simp[] >>
      metis_tac[do_spill_at_only_swap_spill])
  >> first_x_assum (qspecl_then [`target_ops`, `target_op`, `ps1`] mp_tac) >>
  simp[]
QED

(* reduce_depth_plan: stack+spilled alignment by induction on fuel *)
Theorem reduce_depth_plan_align[local]:
  !fuel target_ops target_op ps lo.
    let (ops, ps') = reduce_depth_plan fuel target_ops target_op ps in
    (apply_prefix_ops initial_fmp lo ops ps).ps_stack = ps'.ps_stack /\
    (apply_prefix_ops initial_fmp lo ops ps).ps_spilled = ps'.ps_spilled
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM, apply_prefix_ops_def]
  >>
  rpt gen_tac >>
  Cases_on `stack_get_depth target_op ps.ps_stack`
  >- simp[apply_prefix_ops_def] >>
  rename1 `stack_get_depth _ _ = SOME dist` >>
  simp[] >> IF_CASES_TAC >- simp[apply_prefix_ops_def] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops dist`
  >- simp[apply_prefix_ops_def] >>
  rename1 `select_spill_candidate _ _ _ = SOME cand` >>
  simp[] >>
  Cases_on `do_spill_at cand ps` >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  simp[] >>
  Cases_on `reduce_depth_plan fuel target_ops target_op ps1` >>
  rename1 `reduce_depth_plan _ _ _ _ = (rest_ops, ps2)` >>
  simp[] >>
  simp[apply_prefix_ops_append] >>
  (* IH for ps1 *)
  first_x_assum (qspecl_then
    [`target_ops`, `target_op`, `ps1`, `lo`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  suspend "step"
QED

Resume reduce_depth_plan_align[step]:
  (* do_spill_at_align gives stack+spilled equality *)
  `(apply_prefix_ops initial_fmp lo spill_ops ps).ps_stack = ps1.ps_stack /\
   (apply_prefix_ops initial_fmp lo spill_ops ps).ps_spilled = ps1.ps_spilled` by (
    qspecl_then [`cand`, `ps`, `lo`] mp_tac do_spill_at_align >>
    gvs[]) >>
  (* rest_ops are SOSwap/SOSpill, weaken to include SORestore *)
  `EVERY (\op. (?d. op = SOSwap d) \/ (?off. op = SOSpill off) \/
               (?off. op = SORestore off)) rest_ops` by (
    `EVERY (\op. (?d. op = SOSwap d) \/ (?off. op = SOSpill off))
       rest_ops` by (
      qspecl_then [`fuel`, `target_ops`, `target_op`, `ps1`]
        mp_tac reduce_depth_plan_only_swap_spill >>
      gvs[]) >>
    pop_assum mp_tac >> match_mp_tac EVERY_MONOTONIC >>
    simp[] >> metis_tac[]) >>
  (* apply_ssr_ops_indep + IH *)
  qspecl_then [`rest_ops`, `lo`,
    `apply_prefix_ops initial_fmp lo spill_ops ps`, `ps1`]
    mp_tac apply_ssr_ops_indep >>
  simp[]
QED

Finalise reduce_depth_plan_align;

(* =========================================================================
   Extended: operand value at TOS for any depth (including d > 16)
   ========================================================================= *)

Theorem reorder_single_op_val_on_tos_deep:
  !dfg op ps rops ps' lo vs as_stk.
    reorder_plan dfg [op] ps = (rops, ps') /\
    (?d. stack_get_depth op ps.ps_stack = SOME d) /\
    plan_stack_rel lo vs
      (apply_prefix_ops initial_fmp lo rops ps).ps_stack as_stk /\
    as_stk <> [] /\
    (!at. operand_equiv dfg op at ==>
          operand_val vs lo op = operand_val vs lo at) /\
    (* Spill conditions for deep swap (dist > 16) *)
    (!d' ps2.
       d' > 16 /\ d' < LENGTH ps2.ps_stack /\
       (ps2 = SND (reduce_depth_plan (LENGTH ps.ps_stack)
                     [op] op ps)) ==>
       ALL_DISTINCT (top_n (d' + 1) ps2.ps_stack) /\
       DISJOINT (set (top_n (d' + 1) ps2.ps_stack))
                (FDOM ps2.ps_spilled) /\
       spill_alloc_wf ps2.ps_alloc ps2.ps_spilled /\
       ps2.ps_alloc.sa_next_offset + 32 * (d' + 1) < dimword(:256))
    ==>
    operand_val vs lo op = SOME (HD as_stk)
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `stack_get_depth op ps.ps_stack = SOME d0` >>
  Cases_on `d0 <= 16`
  >- (
    (* d <= 16: delegate to existing theorem *)
    qspecl_then [`dfg`, `op`, `ps`, `rops`, `ps'`, `lo`, `vs`, `as_stk`]
      mp_tac reorder_single_op_val_on_tos >>
    simp[] >> disch_then irule >>
    Q.EXISTS_TAC `d0` >> simp[])
  >> (* d > 16 *)
  (* Unfold reorder_plan for [op] *)
  qpat_x_assum `reorder_plan _ _ _ = _` mp_tac >>
  simp[reorder_plan_def, MAPi_def, MAPi_ACC_def, LET_THM] >>
  Cases_on `reorder_one dfg [op] 0 op ps` >>
  simp[] >> strip_tac >> gvs[] >>
  (* Unfold reorder_one with d > 16 *)
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  imp_res_tac stack_get_depth_bound >>
  (* reduce_depth_plan *)
  pairarg_tac >> simp[] >>
  rename1 `reduce_depth_plan _ _ _ _ = (reduce_ops, ps2)` >>
  (* Stack+spilled alignment: apply_prefix_ops reduce_ops ps = ps2 *)
  `(apply_prefix_ops initial_fmp lo reduce_ops ps).ps_stack = ps2.ps_stack /\
   (apply_prefix_ops initial_fmp lo reduce_ops ps).ps_spilled = ps2.ps_spilled` by (
    qspecl_then [`LENGTH ps.ps_stack`, `[op]`, `op`, `ps`, `lo`]
      mp_tac reduce_depth_plan_align >>
    simp[LET_THM]) >>
  (* reduce_ops are only SOSwap/SOSpill *)
  `EVERY (\op'. (?d. op' = SOSwap d) \/ (?off. op' = SOSpill off))
     reduce_ops` by (
    `reduce_ops = FST (reduce_depth_plan (LENGTH ps.ps_stack)
       [op] op ps)` by simp[] >>
    metis_tac[reduce_depth_plan_only_swap_spill]) >>
  (* Case: stack_get_depth op ps2.ps_stack *)
  Cases_on `stack_get_depth op ps2.ps_stack`
  >- (
    (* NONE contradicts reduce_depth_plan_dist_ge *)
    simp[] >> strip_tac >> gvs[] >>
    qspecl_then [`LENGTH ps.ps_stack`, `[op]`, `op`, `ps`, `d0`]
      mp_tac (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)
                (REWRITE_RULE [LET_THM] reduce_depth_plan_dist_ge)) >>
    (impl_tac >- simp[]) >> simp[] >> metis_tac[optionTheory.NOT_NONE_SOME])
  >>
  rename1 `stack_get_depth op ps2.ps_stack = SOME dist'` >>
  qpat_assum `stack_get_depth _ _ = SOME dist'`
    (strip_assume_tac o MATCH_MP stack_get_depth_bound) >>
  (* final_dist = 0 for single-op *)
  simp[] >>
  (* Case: dist' = 0 *)
  Cases_on `dist' = 0`
  >- (
    simp[] >> strip_tac >> fs[] >>
    simp[apply_prefix_ops_append, apply_prefix_ops_nil] >>
    imp_res_tac stack_get_depth_zero_last >>
    qspecl_then [`lo`,`vs`,`ps2.ps_stack`,`as_stk`]
      mp_tac plan_stack_rel_hd >>
    (impl_tac >- fs[]) >>
    simp[])
  >>
  imp_res_tac (DECIDE ``(d:num) < (n:num) /\ d <> 0 ==> 0 < n``) >>
  simp[] >>
  (* Case: operand_equiv (poke case) *)
  Cases_on `operand_equiv dfg op (stack_peek 0 ps2.ps_stack)`
  >- (simp[] >> strip_tac >> fs[] >>
    simp[apply_prefix_ops_append, apply_prefix_ops_nil] >>
    suspend "poke")
  >>
  (* Swap case *)
  pairarg_tac >> simp[] >>
  simp[do_swap_def] >> strip_tac >> fs[] >>
  simp[apply_prefix_ops_append, apply_prefix_ops_nil] >>
  Cases_on `dist' <= 16`
  >- (simp[apply_prefix_ops_def, apply_prefix_op_def, apply_simple_op_def] >>
    suspend "swap_le16")
  >>
  suspend "deep_swap"
QED

Resume reorder_single_op_val_on_tos_deep[poke]:
  (* plan_stack_rel_hd: LAST ps2.ps_stack maps to HD as_stk *)
  qspecl_then [`lo`,`vs`,`ps2.ps_stack`,`as_stk`]
    mp_tac plan_stack_rel_hd >>
  (impl_tac >- simp[]) >>
  (* operand_equiv: op has same val as stack_peek 0 = LAST *)
  first_x_assum (qspec_then `stack_peek 0 ps2.ps_stack` mp_tac) >>
  simp[] >>
  (* stack_peek 0 stk = LAST stk when stk <> [] *)
  rewrite_tac[stack_peek_def, GSYM PRE_SUB1] >>
  simp[GSYM LAST_EL]
QED

Resume reorder_single_op_val_on_tos_deep[swap_le16]:
  (* swap1_ops = [SOSwap dist'] since dist' <= 16, dist' <> 0 *)
  `swap1_ops = [SOSwap dist']` by (
    qpat_x_assum `do_swap _ _ = _` mp_tac >>
    simp[do_swap_def]) >>
  (* Rewrite plan_stack_rel to use stack_swap *)
  `(apply_prefix_ops initial_fmp lo q ps).ps_stack =
   stack_swap dist' ps2.ps_stack` by (
    qpat_x_assum `_ = q` (SUBST_ALL_TAC o SYM) >>
    simp[apply_prefix_ops_append, apply_prefix_ops_def,
         apply_prefix_op_def, apply_simple_op_def]) >>
  (* Rewrite plan_stack_rel assumption *)
  `plan_stack_rel lo vs (stack_swap dist' ps2.ps_stack) as_stk` by
    fs[] >>
  imp_res_tac stack_get_depth_el >>
  qspecl_then [`lo`,`vs`,
    `stack_swap dist' ps2.ps_stack`,`as_stk`]
    mp_tac plan_stack_rel_hd >>
  (impl_tac >- simp[stack_swap_nonempty]) >>
  simp[stack_swap_last]
QED

(* FOLDL spill produces only SOSpill ops *)
Theorem foldl_spill_only_sospill[local]:
  !items ops0 offs0 al0 ops1 offs1 al1.
    EVERY (\op'. ?off. op' = SOSpill off) ops0 /\
    FOLDL (\(ops,offs,al) item.
      (\(off,al'). (ops ++ [SOSpill off], SNOC off offs, al'))
        (alloc_spill_slot al))
      (ops0, offs0, al0) items = (ops1, offs1, al1) ==>
    EVERY (\op'. ?off. op' = SOSpill off) ops1
Proof
  Induct >> simp[] >>
  rpt gen_tac >> pairarg_tac >> simp[] >>
  strip_tac >> first_x_assum match_mp_tac >>
  Q.EXISTS_TAC `ops0 ++ [SOSpill off]` >>
  qexistsl [`SNOC off offs0`, `al'`, `offs1`, `al1`] >>
  simp[EVERY_APPEND]
QED

(* do_swap ops are always SOSwap/SOSpill/SORestore *)
Theorem do_swap_ops_ssr[local]:
  !dist ps.
    EVERY (\op'. (?d. op' = SOSwap d) \/ (?off. op' = SOSpill off) \/
                 (?off. op' = SORestore off)) (FST (do_swap dist ps))
Proof
  rpt gen_tac >>
  rewrite_tac[do_swap_def, LET_THM] >>
  IF_CASES_TAC >- simp[] >>
  IF_CASES_TAC >- simp[] >>
  BETA_TAC >> pairarg_tac >> gvs[EVERY_APPEND, EVERY_MAP] >>
  irule EVERY_MONOTONIC >>
  Q.EXISTS_TAC `\op'. ?off. op' = SOSpill off` >>
  conj_tac >- simp[] >>
  qspecl_then [`top_n (dist + 1) ps.ps_stack`,
    `[] : stack_op list`, `[] : num list`, `ps.ps_alloc`,
    `spill_ops`, `offsets`, `alloc'`]
    mp_tac foldl_spill_only_sospill >> simp[]
QED

(* do_swap deep: apply_prefix_ops gives same stack as direct computation *)

Resume reorder_single_op_val_on_tos_deep[deep_swap]:
  (* swap1_ops are SOSwap/SOSpill/SORestore *)
  `EVERY (\op'. (?d. op' = SOSwap d) \/ (?off. op' = SOSpill off) \/
                (?off. op' = SORestore off)) swap1_ops` by (
    `swap1_ops = FST (do_swap dist' ps2)` by gvs[] >>
    metis_tac[do_swap_ops_ssr]) >>
  (* apply_ssr_ops_indep bridges reduce_ops gap *)
  `(apply_prefix_ops initial_fmp lo swap1_ops
      (apply_prefix_ops initial_fmp lo reduce_ops ps)).ps_stack =
   (apply_prefix_ops initial_fmp lo swap1_ops ps2).ps_stack` by (
    qspecl_then [`swap1_ops`, `lo`,
      `apply_prefix_ops initial_fmp lo reduce_ops ps`, `ps2`]
      mp_tac apply_ssr_ops_indep >>
    simp[]) >>
  (* do_swap_apply_stack_align *)
  `(apply_prefix_ops initial_fmp lo swap1_ops ps2).ps_stack =
   (SND (do_swap dist' ps2)).ps_stack` by (
    `swap1_ops = FST (do_swap dist' ps2)` by simp[] >>
    pop_assum SUBST_ALL_TAC >>
    match_mp_tac do_swap_apply_stack_align >> simp[] >>
    first_x_assum (qspec_then `dist'` mp_tac) >> simp[]) >>
  (* do_swap_last *)
  `LAST (SND (do_swap dist' ps2)).ps_stack = op /\
   (SND (do_swap dist' ps2)).ps_stack <> []` by (
    irule do_swap_last >> simp[]) >>
  (* rewrite plan_stack_rel to use do_swap result stack *)
  `q = reduce_ops ++ swap1_ops` by gvs[] >>
  pop_assum (fn eq =>
    qpat_x_assum `plan_stack_rel _ _ _ _`
      (mp_tac o REWRITE_RULE [eq, apply_prefix_ops_append])) >>
  (* Rewrite using the stack equality chain *)
  qpat_x_assum `(apply_prefix_ops initial_fmp lo swap1_ops
    (apply_prefix_ops initial_fmp lo reduce_ops ps)).ps_stack = _` (SUBST1_TAC) >>
  qpat_x_assum `(apply_prefix_ops initial_fmp lo swap1_ops ps2).ps_stack = _`
    (SUBST1_TAC) >>
  strip_tac >>
  (* plan_stack_rel on (SND (do_swap dist' ps2)).ps_stack *)
  qspecl_then [`lo`, `vs`,
    `(SND (do_swap dist' ps2)).ps_stack`, `as_stk`]
    mp_tac plan_stack_rel_hd >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  simp[]
QED

Finalise reorder_single_op_val_on_tos_deep
