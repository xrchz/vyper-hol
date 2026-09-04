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
  foldlSim doSwapSim spillSim instSimHelpers strongPrefixSim planSpillBounds dfgDefs
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

Theorem plan_stack_rel_sem_eq:
  plan_stack_rel lo vs s1 astk /\
  plan_stack_sem_eq lo vs s1 s2 ==>
  plan_stack_rel lo vs s2 astk
Proof
  rw[plan_stack_rel_def, plan_stack_sem_eq_def] >>
  qpat_assum `!j. j < LENGTH s1 ==>
    operand_val vs lo (EL j s1) = operand_val vs lo (EL j s2)`
    (qspec_then `PRE (LENGTH s2 - i)` mp_tac) >>
  (impl_tac >- decide_tac) >>
  strip_tac >>
  qpat_assum `!j. j < LENGTH s1 ==>
    operand_val vs lo (EL j (REVERSE s1)) = SOME (EL j astk)`
    (qspec_then `i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  strip_tac >>
  gvs[EL_REVERSE]
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


(* Input preparation and reorder may temporarily duplicate pending operands
   anywhere in the stack.  Each logical pending occurrence licenses one extra
   stack occurrence in addition to at most one canonical retained copy.  An
   operand still owned by the spill map has no canonical stack allowance.
   [fixed] records target positions already established by reorder_plan. *)
Definition plan_state_residual_wf_def:
  plan_state_residual_wf base pending fixed (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    fixed <= LENGTH pending /\
    (!i. i < fixed ==>
       stack_peek (LENGTH pending - 1 - i) ps.ps_stack = EL i pending) /\
    (!op. LIST_ELEM_COUNT op ps.ps_stack <=
          SUC (LIST_ELEM_COUNT op pending)) /\
    (!op. op IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending)
End

(* Fixed-zero residual resources without the pending-length obligation.  This
   is stable across each input-emission step; length is supplied only when the
   complete pending list is known. *)
Definition residual_budget_wf_def:
  residual_budget_wf base pending (ps : plan_state) <=>
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    (!op. LIST_ELEM_COUNT op ps.ps_stack <=
          SUC (LIST_ELEM_COUNT op pending)) /\
    (!op. op IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending)
End

Definition pending_inventory_wf_def:
  pending_inventory_wf pending (ps : plan_state) <=>
    !op. LIST_ELEM_COUNT op pending <=
      LIST_ELEM_COUNT op ps.ps_stack +
      (if op IN FDOM ps.ps_spilled then 1 else 0)
End

Theorem all_distinct_elem_count_le_one[local]:
  !(xs : 'a list) x.
    ALL_DISTINCT xs ==> LIST_ELEM_COUNT x xs <= 1
Proof
  Induct >> simp[LIST_ELEM_COUNT_THM] >> rpt strip_tac >>
  Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
  >- (`~(LIST_ELEM_COUNT h xs > 0)` by
        metis_tac[LIST_ELEM_COUNT_MEM] >> decide_tac)
  >> first_x_assum (qspec_then `x` mp_tac) >> simp[]
QED

Theorem elem_count_cons_mono[local]:
  !(h : 'a) x xs.
    LIST_ELEM_COUNT x xs <= LIST_ELEM_COUNT x (h::xs)
Proof
  rpt gen_tac >> Cases_on `h = x` >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem elem_count_le_one_all_distinct[local]:
  !(xs : 'a list).
    (!x. LIST_ELEM_COUNT x xs <= 1) ==> ALL_DISTINCT xs
Proof
  Induct
  >- simp[]
  >- (gen_tac >> disch_tac >> simp[] >> conj_tac
      >- (`LIST_ELEM_COUNT h xs = 0` by
            (Cases_on `FILTER (\x. x = h) xs`
             >- simp[LIST_ELEM_COUNT_DEF]
             >> qpat_assum `!x. LIST_ELEM_COUNT x (h::xs) <= 1`
                  (qspec_then `h` assume_tac) >>
                fs[LIST_ELEM_COUNT_DEF] >>
                qpat_x_assum `SUC (LENGTH (FILTER (\x. x = h) xs)) <= 1`
                  mp_tac >> ASM_REWRITE_TAC[] >> simp[]) >>
          fs[GSYM LIST_ELEM_COUNT_MEM])
      >> first_x_assum irule >> gen_tac >>
         qpat_assum `!x. LIST_ELEM_COUNT x (h::xs) <= 1`
           (qspec_then `x` assume_tac) >>
         qspecl_then [`h`, `x`, `xs`] assume_tac elem_count_cons_mono >>
         decide_tac)
QED

Theorem residual_budget_wf_canonical:
  !base pending ps.
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
    residual_budget_wf base pending ps
Proof
  rpt gen_tac >> strip_tac >>
  simp[residual_budget_wf_def] >> conj_tac
  >- (gen_tac >> drule all_distinct_elem_count_le_one >>
      disch_then (qspec_then `op` assume_tac) >> decide_tac)
  >> rpt strip_tac >>
     `~MEM op ps.ps_stack` by
       (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
        metis_tac[]) >>
     fs[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem residual_budget_wf_to_residual:
  !base pending ps.
    residual_budget_wf base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack ==>
    plan_state_residual_wf base pending 0 ps
Proof
  simp[residual_budget_wf_def, plan_state_residual_wf_def]
QED

Theorem plan_state_residual_wf_canonical:
  !base pending ps.
    plan_slots_bounded base ps /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    LENGTH pending <= LENGTH ps.ps_stack ==>
    plan_state_residual_wf base pending 0 ps
Proof
  rpt gen_tac >> strip_tac >>
  simp[plan_state_residual_wf_def] >> conj_tac
  >- (gen_tac >>
      drule all_distinct_elem_count_le_one >>
      disch_then (qspec_then `op` assume_tac) >> decide_tac)
  >> rpt strip_tac >>
     `~MEM op ps.ps_stack` by
       (fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
        metis_tac[]) >>
     fs[GSYM LIST_ELEM_COUNT_MEM]
QED

Theorem plan_state_residual_wf_fix_next:
  !base pending fixed ps.
    plan_state_residual_wf base pending fixed ps /\
    fixed < LENGTH pending /\
    stack_peek (LENGTH pending - 1 - fixed) ps.ps_stack =
      EL fixed pending ==>
    plan_state_residual_wf base pending (SUC fixed) ps
Proof
  simp[plan_state_residual_wf_def] >> rpt strip_tac >>
  Cases_on `i = fixed` >> gvs[] >>
  first_x_assum irule >> decide_tac
QED


Theorem elem_count_append[local]:
  !x (xs : 'a list) ys.
    LIST_ELEM_COUNT x (xs ++ ys) =
    LIST_ELEM_COUNT x xs + LIST_ELEM_COUNT x ys
Proof
  gen_tac >> Induct >> simp[LIST_ELEM_COUNT_THM]
QED

Theorem elem_count_take_el_lt[local]:
  !(xs : operand list) n.
    n < LENGTH xs ==>
    LIST_ELEM_COUNT (EL n xs) (TAKE n xs) <
      LIST_ELEM_COUNT (EL n xs) xs
Proof
  rpt strip_tac >> drule TAKE_DROP_SUC >>
  disch_then (fn th => mp_tac
    (AP_TERM ``LIST_ELEM_COUNT (EL n xs) : operand list -> num`` th)) >>
  simp[elem_count_append, LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem fixed_window_segment[local]:
  !(pending : operand list) fixed stack.
    LENGTH pending <= LENGTH stack /\ fixed <= LENGTH pending /\
    (!i. i < fixed ==>
      stack_peek (LENGTH pending - 1 - i) stack = EL i pending) ==>
    TAKE fixed (DROP (LENGTH stack - LENGTH pending) stack) =
      TAKE fixed pending
Proof
  rpt gen_tac >> strip_tac >> irule LIST_EQ >>
  simp[LENGTH_TAKE, LENGTH_DROP] >> rpt strip_tac >>
  first_x_assum (qspec_then `x` mp_tac) >>
  simp[stack_peek_def, EL_TAKE, EL_DROP] >>
  AP_TERM_TAC >> decide_tac
QED


Theorem fixed_window_count_bound[local]:
  !(pending : operand list) fixed stack op.
    LENGTH pending <= LENGTH stack /\ fixed <= LENGTH pending /\
    (!i. i < fixed ==>
      stack_peek (LENGTH pending - 1 - i) stack = EL i pending) /\
    stack_get_unfixed_depth op (LENGTH pending - 1 - fixed)
      (LENGTH pending) stack = NONE ==>
    LIST_ELEM_COUNT op stack <= LIST_ELEM_COUNT op (TAKE fixed pending)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stack_get_unfixed_depth _ _ _ _ = NONE` mp_tac >>
  simp[stack_get_unfixed_depth_NONE] >> strip_tac >>
  qabbrev_tac `off = LENGTH stack - LENGTH pending` >>
  `TAKE fixed (DROP off stack) = TAKE fixed pending` by
    (unabbrev_all_tac >> irule fixed_window_segment >> simp[]) >>
  `stack = TAKE off stack ++ TAKE fixed (DROP off stack) ++
           DROP (off + fixed) stack` by
    (`TAKE fixed (DROP off stack) ++ DROP (off + fixed) stack =
       DROP off stack` by
       MATCH_ACCEPT_TAC
         (ONCE_REWRITE_RULE [Q.SPECL [`fixed`, `off`] ADD_COMM]
            (REWRITE_RULE [DROP_DROP_T]
              (Q.SPECL [`fixed`, `DROP off stack`] TAKE_DROP))) >>
     once_rewrite_tac[GSYM APPEND_ASSOC] >>
     qpat_assum
       `TAKE fixed (DROP off stack) ++ DROP (off + fixed) stack =
          DROP off stack`
       (fn th => once_rewrite_tac[th]) >>
     MATCH_ACCEPT_TAC (SYM (Q.SPECL [`off`, `stack`] TAKE_DROP))) >>
  `~MEM op (TAKE off stack)` by
    (simp[MEM_EL] >> rpt strip_tac >>
     first_x_assum (qspec_then `LENGTH stack - 1 - n` mp_tac) >>
     simp[stack_peek_def] >>
     `n < LENGTH stack` by
       (qpat_assum `stack = _`
          (fn th => mp_tac (AP_TERM ``LENGTH : operand list -> num`` th)) >>
        simp[] >> decide_tac) >>
     `LENGTH stack - 1 - (LENGTH stack - 1 - n) = n` by decide_tac >>
     `off <= LENGTH stack` by (unabbrev_all_tac >> decide_tac) >>
     `n < off` by fs[LENGTH_TAKE] >>
     `LENGTH pending <= LENGTH stack - 1 - n` by
       (unabbrev_all_tac >> decide_tac) >>
     simp[EL_TAKE] >> decide_tac) >>
  `~MEM op (DROP (off + fixed) stack)` by
    (simp[MEM_EL] >> rpt strip_tac >>
     first_x_assum
       (qspec_then `LENGTH stack - 1 - (off + fixed + n)` mp_tac) >>
     simp[stack_peek_def, EL_DROP] >>
     `LENGTH stack - 1 - (LENGTH stack - 1 - (off + fixed + n)) =
        off + fixed + n` by decide_tac >>
     `LENGTH stack - 1 - (off + fixed + n) <=
        LENGTH pending - 1 - fixed` by
       (unabbrev_all_tac >> decide_tac) >>
     simp[] >> unabbrev_all_tac >> decide_tac) >>
  `LIST_ELEM_COUNT op (TAKE off stack) = 0 /\
   LIST_ELEM_COUNT op (DROP (off + fixed) stack) = 0` by
    fs[GSYM LIST_ELEM_COUNT_MEM] >>
  qpat_x_assum `stack = _`
    (fn th => mp_tac
      (AP_TERM ``LIST_ELEM_COUNT op : operand list -> num`` th)) >>
  simp[elem_count_append] >> decide_tac
QED

Theorem pending_inventory_wf_next_available:
  !base pending fixed ps.
    pending_inventory_wf pending ps /\
    plan_state_residual_wf base pending fixed ps /\
    fixed < LENGTH pending ==>
      (?d. stack_get_unfixed_depth (EL fixed pending)
             (LENGTH pending - 1 - fixed) (LENGTH pending)
             ps.ps_stack = SOME d) \/
      (stack_get_unfixed_depth (EL fixed pending)
         (LENGTH pending - 1 - fixed) (LENGTH pending)
         ps.ps_stack = NONE /\
       IS_SOME (FLOOKUP ps.ps_spilled (EL fixed pending)))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth (EL fixed pending)
    (LENGTH pending - 1 - fixed) (LENGTH pending) ps.ps_stack` >>
  simp[FLOOKUP_DEF] >>
  Cases_on `EL fixed pending IN FDOM ps.ps_spilled` >> simp[] >>
  fs[pending_inventory_wf_def] >>
  qpat_assum `!op. _`
    (qspec_then `EL fixed pending` assume_tac) >>
  fs[plan_state_residual_wf_def] >>
  `LIST_ELEM_COUNT (EL fixed pending) ps.ps_stack <=
     LIST_ELEM_COUNT (EL fixed pending) (TAKE fixed pending)` by
    (irule fixed_window_count_bound >> simp[]) >>
  qpat_assum `EL fixed pending NOTIN FDOM ps.ps_spilled`
    (fn th => fs[th]) >>
  `LIST_ELEM_COUNT (EL fixed pending) pending <=
     LIST_ELEM_COUNT (EL fixed pending) ps.ps_stack` by
    first_assum ACCEPT_TAC >>
  drule_then assume_tac elem_count_take_el_lt >> decide_tac
QED

Theorem residual_budget_does_not_imply_pending_inventory[local]:
  let ps = (init_plan_state 0) with
             ps_stack := [Var "core_a"; Var "core_b"] in
    plan_state_residual_wf 0 [Var "need_x"; Var "need_y"] 0 ps /\
    2 <= LENGTH ps.ps_stack /\
    ~pending_inventory_wf [Var "need_x"; Var "need_y"] ps /\
    stack_get_unfixed_depth (Var "need_x") 1 2 ps.ps_stack = NONE /\
    ~IS_SOME (FLOOKUP ps.ps_spilled (Var "need_x"))
Proof
  EVAL_TAC >> conj_tac
  >- (simp[] >> gen_tac >> Cases_on `op` >> simp[LIST_ELEM_COUNT_THM] >>
      rpt IF_CASES_TAC >> gvs[]) 
  >> strip_tac >>
     first_x_assum (qspec_then `Var "need_x"` mp_tac) >> EVAL_TAC
QED
Theorem residual_budget_wf_extend_pending[local]:
  !base pending op ps.
    residual_budget_wf base pending ps ==>
    residual_budget_wf base (pending ++ [op]) ps
Proof
  simp[residual_budget_wf_def, elem_count_append] >>
  rpt strip_tac
  >- (qpat_assum `!x. LIST_ELEM_COUNT x ps.ps_stack <= SUC _`
        (qspec_then `op'` mp_tac) >> decide_tac)
  >> qpat_assum `!x. x IN FDOM ps.ps_spilled ==> _`
       (qspec_then `op'` (drule_then assume_tac)) >> decide_tac
QED

Theorem elem_count_snoc[local]:
  !x y (xs : 'a list).
    LIST_ELEM_COUNT x (SNOC y xs) =
    LIST_ELEM_COUNT x xs + LIST_ELEM_COUNT x [y]
Proof
  gen_tac >> gen_tac >> Induct >> simp[LIST_ELEM_COUNT_THM] >>
  rpt gen_tac >> Cases_on `h = x` >> gvs[LIST_ELEM_COUNT_THM]
QED

Theorem residual_budget_wf_push[local]:
  !base pending op ps.
    residual_budget_wf base pending ps ==>
    residual_budget_wf base (pending ++ [op])
      (ps with ps_stack := stack_push op ps.ps_stack)
Proof
  simp[residual_budget_wf_def, stack_push_def, elem_count_append,
       elem_count_snoc] >>
  rpt strip_tac
  >- (qpat_assum `!x. LIST_ELEM_COUNT x ps.ps_stack <= SUC _`
        (qspec_then `op'` mp_tac) >> decide_tac)
  >> qpat_assum `!x. x IN FDOM ps.ps_spilled ==> _`
       (qspec_then `op'` (drule_then assume_tac)) >> decide_tac
QED
Theorem residual_budget_wf_restore[local]:
  !base pending op ps ops ps'.
    residual_budget_wf base pending ps /\
    do_restore op ps = (ops, ps') ==>
    residual_budget_wf base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `residual_budget_wf spill_base pending ps` >>
  fs[residual_budget_wf_def] >>
  `plan_slots_bounded spill_base ps'` by
    imp_res_tac do_restore_slots_bounded >>
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- gvs[do_restore_def]
  >> rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
     gvs[do_restore_def, residual_budget_wf_def, stack_push_def,
         elem_count_snoc] >>
     conj_tac
     >- metis_tac[spill_alloc_layout_wf_after_free]
     >> conj_tac
     >- (gen_tac >> Cases_on `op' = op` >> gvs[LIST_ELEM_COUNT_THM]
         >- (`op IN FDOM ps.ps_spilled` by fs[flookup_thm] >>
             qpat_assum `!x. x IN FDOM ps.ps_spilled ==>
               LIST_ELEM_COUNT x ps.ps_stack <= LIST_ELEM_COUNT x pending`
               (qspec_then `op` (drule_then assume_tac)) >>
             decide_tac)
         >> qpat_assum `!x. LIST_ELEM_COUNT x ps.ps_stack <= SUC _`
              (qspec_then `op'` assume_tac) >> decide_tac)
     >> rpt strip_tac >>
        qpat_assum `!x. x IN FDOM ps.ps_spilled ==> _`
          (qspec_then `op'` (drule_then assume_tac)) >>
        gvs[LIST_ELEM_COUNT_THM]
QED

Theorem residual_budget_wf_do_swap[local]:
  !base pending dist ps ops ps'.
    residual_budget_wf base pending ps /\
    dist < LENGTH ps.ps_stack /\
    do_swap dist ps = (ops, ps') ==>
    residual_budget_wf base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  fs[residual_budget_wf_def] >>
  imp_res_tac do_swap_slots_bounded >>
  imp_res_tac do_swap_multiplicity_layout >>
  gvs[residual_budget_wf_def]
QED

Theorem stack_pop_one_elem_count[local]:
  !x (xs : 'a list).
    xs <> [] ==>
    LIST_ELEM_COUNT x (stack_pop 1 xs) +
    LIST_ELEM_COUNT x [stack_peek 0 xs] = LIST_ELEM_COUNT x xs
Proof
  rpt strip_tac >>
  `?ys y. xs = SNOC y ys` by metis_tac[rich_listTheory.SNOC_CASES] >>
  gvs[stack_pop_def, stack_peek_def, elem_count_snoc,
      rich_listTheory.TAKE_SNOC, EL_LENGTH_SNOC]
QED

Theorem do_spill_at_multiplicity_layout[local]:
  !d ps ops ps'.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    do_spill_at d ps = (ops, ps') ==>
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
    (!x. LIST_ELEM_COUNT x ps'.ps_stack +
         LIST_ELEM_COUNT x [stack_peek d ps.ps_stack] =
         LIST_ELEM_COUNT x ps.ps_stack) /\
    (?off. ps'.ps_spilled =
           ps.ps_spilled |+ (stack_peek d ps.ps_stack, off))
Proof
  rpt gen_tac >> strip_tac >>
  `ps.ps_stack <> []` by (strip_tac >> gvs[]) >>
  Cases_on `d = 0`
  >- (gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
      Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >>
      rpt conj_tac
      >- metis_tac[spill_alloc_layout_wf_after_alloc]
      >- (gen_tac >>
          qspecl_then [`x`, `ps.ps_stack`] mp_tac
            stack_pop_one_elem_count >> simp[] >> decide_tac)
      >> metis_tac[])
  >> `stack_peek 0 (stack_swap d ps.ps_stack) =
      stack_peek d ps.ps_stack` by
       (simp[stack_peek_def, stack_swap_def, LET_THM, EL_LUPDATE] >>
        IF_CASES_TAC >> gvs[] >> decide_tac) >>
     `!x. LIST_ELEM_COUNT x (stack_swap d ps.ps_stack) =
          LIST_ELEM_COUNT x ps.ps_stack` by
       (gen_tac >>
        qspecl_then [`d`, `ps`, `x`] mp_tac do_swap_multiplicity >>
        simp[do_swap_def]) >>
     gvs[do_spill_at_def, do_spill_tos_def, LET_THM] >>
     Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[] >>
     rpt conj_tac
     >- metis_tac[spill_alloc_layout_wf_after_alloc]
     >- (gen_tac >>
         `stack_swap d ps.ps_stack <> []` by
           (strip_tac >> gvs[stack_swap_def]) >>
         qspecl_then [`x`, `stack_swap d ps.ps_stack`] assume_tac
           stack_pop_one_elem_count >>
         qpat_assum `!x. LIST_ELEM_COUNT x (stack_swap d ps.ps_stack) = _`
           (qspec_then `x` assume_tac) >>
         gvs[] >> decide_tac)
     >> metis_tac[]
QED

Theorem residual_budget_wf_do_spill_at[local]:
  !base pending d ps ops ps'.
    residual_budget_wf base pending ps /\
    d < LENGTH ps.ps_stack /\ d <= 16 /\
    ~MEM (stack_peek d ps.ps_stack) pending /\
    do_spill_at d ps = (ops, ps') ==>
    residual_budget_wf base pending ps'
Proof
  rpt gen_tac >> strip_tac >>
  fs[residual_budget_wf_def] >>
  imp_res_tac do_spill_at_slots_bounded >>
  imp_res_tac do_spill_at_multiplicity_layout >>
  gvs[residual_budget_wf_def] >> conj_tac
  >- (gen_tac >>
      qpat_assum `!op. LIST_ELEM_COUNT op ps.ps_stack <= _`
        (qspec_then `op` assume_tac) >>
      qpat_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
        (qspec_then `op` assume_tac) >> decide_tac)
  >> rpt strip_tac >>
     Cases_on `op = stack_peek d ps.ps_stack`
     >- (gvs[GSYM LIST_ELEM_COUNT_MEM, LIST_ELEM_COUNT_THM] >>
         qpat_assum `!op. LIST_ELEM_COUNT op ps.ps_stack <= _`
           (qspec_then `stack_peek d ps.ps_stack` assume_tac) >>
         qpat_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
           (qspec_then `stack_peek d ps.ps_stack` assume_tac) >>
         `LIST_ELEM_COUNT (stack_peek d ps.ps_stack) pending = 0` by
           decide_tac >>
         `LIST_ELEM_COUNT (stack_peek d ps.ps_stack) ps.ps_stack <= 1` by
           decide_tac >>
         qpat_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
           (qspec_then `stack_peek d ps.ps_stack` assume_tac) >>
         fs[LIST_ELEM_COUNT_THM] >> decide_tac)
     >> `op IN FDOM ps.ps_spilled` by
          gvs[finite_mapTheory.FDOM_FUPDATE] >>
        `LIST_ELEM_COUNT op ps.ps_stack <= LIST_ELEM_COUNT op pending` by
          (qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
             (qspec_then `op` (drule_then ACCEPT_TAC))) >>
        `LIST_ELEM_COUNT op ps'.ps_stack <=
         LIST_ELEM_COUNT op ps.ps_stack` by
          (qpat_assum `!x. LIST_ELEM_COUNT x ps'.ps_stack + _ = _`
             (qspec_then `op` assume_tac) >> decide_tac) >>
        decide_tac
QED
Theorem residual_budget_wf_stack_poke_exchange[local]:
  !base pending ps d1 d2.
    residual_budget_wf base pending ps /\
    d1 < LENGTH ps.ps_stack /\ d2 < LENGTH ps.ps_stack ==>
    residual_budget_wf base pending
      (ps with ps_stack :=
        stack_poke d2 (stack_peek d1 ps.ps_stack)
          (stack_poke d1 (stack_peek d2 ps.ps_stack) ps.ps_stack))
Proof
  simp[residual_budget_wf_def] >> rpt strip_tac
  >- (qpat_assum `!op. LIST_ELEM_COUNT op ps.ps_stack <= _`
        (qspec_then `op` mp_tac) >>
      simp[stack_poke_exchange_multiplicity])
  >> qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
       (qspec_then `op` (drule_then mp_tac)) >>
     simp[stack_poke_exchange_multiplicity]
QED

Theorem select_spill_candidate_not_pending[local]:
  !stk pending target_dist target_len cand.
    select_spill_candidate stk pending target_dist target_len = SOME cand ==>
    ~MEM (stack_peek cand stk) pending
Proof
  rpt strip_tac >>
  fs[select_spill_candidate_def, LET_THM] >>
  imp_res_tac FIND_SOME_MEM >> gvs[]
QED

Theorem reorder_restore_residual_budget_wf[local]:
  !base pending op f ps.
    residual_budget_wf base pending ps /\
    LENGTH pending <= LENGTH ps.ps_stack ==>
    let (_,ps') =
      case stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack of
        SOME _ => ([] : stack_op list, ps)
      | NONE =>
          (case FLOOKUP ps.ps_spilled op of
             SOME _ => do_restore op ps
           | NONE => ([], ps))
    in residual_budget_wf base pending ps' /\
       LENGTH pending <= LENGTH ps'.ps_stack
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `stack_get_unfixed_depth op f (LENGTH pending) ps.ps_stack` >>
  simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  Cases_on `do_restore op ps` >> gvs[] >>
  conj_tac
  >- (qspecl_then [`base'`, `pending`, `op`, `ps`, `q`, `r`] mp_tac
        residual_budget_wf_restore >> simp[])
  >> qspecl_then [`op`, `ps`] mp_tac do_restore_length >> simp[]
QED

Theorem reduce_depth_plan_residual_budget_wf[local]:
  !fuel base pending target_op f ps ops ps'.
    residual_budget_wf base pending ps /\
    reduce_depth_plan fuel pending target_op f (LENGTH pending) ps =
      (ops, ps') ==>
    residual_budget_wf base pending ps'
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target_op f (LENGTH pending)
              ps.ps_stack` >> gvs[] >>
  Cases_on `f + 1 < LENGTH pending` >> gvs[] >>
  Cases_on `x <= 16` >> gvs[] >>
  Cases_on `select_spill_candidate ps.ps_stack pending x
              (LENGTH pending)` >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  `1 <= LENGTH ps.ps_stack` by
    (drule stack_get_unfixed_depth_bound >> simp[]) >>
  `cand <= 16 /\ cand < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  `~MEM (stack_peek cand ps.ps_stack) pending` by
    metis_tac[select_spill_candidate_not_pending] >>
  `residual_budget_wf base' pending ps1` by
    metis_tac[residual_budget_wf_do_spill_at] >>
  Cases_on `reduce_depth_plan fuel pending target_op f (LENGTH pending) ps1` >>
  gvs[] >>
  first_x_assum
    (qspecl_then [`base'`, `pending`, `target_op`, `f`, `ps1`,
                  `q`, `ps'`] mp_tac) >>
  simp[]
QED


Theorem residual_budget_wf_dup[local]:
  !base pending op dist ps ops ps'.
    residual_budget_wf base pending ps /\
    stack_get_depth op ps.ps_stack = SOME dist /\
    do_dup dist ps = (ops, ps') ==>
    residual_budget_wf base (pending ++ [op]) ps'
Proof
  rpt gen_tac >> strip_tac >>
  rename1 `residual_budget_wf spill_base pending ps` >>
  `dist < LENGTH ps.ps_stack /\ stack_peek dist ps.ps_stack = op` by
    metis_tac[stack_get_depth_props] >>
  fs[residual_budget_wf_def] >>
  `plan_slots_bounded spill_base ps'` by
    imp_res_tac do_dup_slots_bounded >>
  imp_res_tac do_dup_multiplicity_layout >>
  gvs[residual_budget_wf_def, elem_count_append] >>
  conj_tac
  >- (gen_tac >> Cases_on `op = stack_peek dist ps.ps_stack`
      >- (gvs[LIST_ELEM_COUNT_THM] >>
          qpat_assum `!x. LIST_ELEM_COUNT x ps.ps_stack <= SUC _`
            (qspec_then `stack_peek dist ps.ps_stack` mp_tac) >>
          decide_tac)
      >> simp[LIST_ELEM_COUNT_THM] >>
         qpat_assum `!x. LIST_ELEM_COUNT x ps.ps_stack <= SUC _`
           (qspec_then `op` mp_tac) >> decide_tac)
  >> rpt strip_tac >> Cases_on `op = stack_peek dist ps.ps_stack`
     >- (gvs[LIST_ELEM_COUNT_THM] >>
         qpat_assum `!x. x IN FDOM ps.ps_spilled ==>
           LIST_ELEM_COUNT x ps.ps_stack <= LIST_ELEM_COUNT x pending`
           (qspec_then `stack_peek dist ps.ps_stack`
             (drule_then assume_tac)) >> decide_tac)
     >> simp[LIST_ELEM_COUNT_THM] >>
        qpat_assum `!x. x IN FDOM ps.ps_spilled ==>
          LIST_ELEM_COUNT x ps.ps_stack <= LIST_ELEM_COUNT x pending`
          (qspec_then `op` (drule_then assume_tac)) >> decide_tac
QED
Theorem emit_one_input_residual_budget_wf:
  !base pending opc nl op ps ops ps'.
    residual_budget_wf base pending ps /\
    emit_one_input opc nl op ps = (ops, ps') ==>
    residual_budget_wf base (pending ++ [op]) ps'
Proof
  rpt gen_tac >> strip_tac >> Cases_on `op`
  >- (gvs[emit_one_input_def, is_var_operand_def, LET_THM] >>
      irule residual_budget_wf_push >> first_assum ACCEPT_TAC)
  >- (rename1 `Var v` >>
      Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (gvs[emit_one_input_def, is_var_operand_def, LET_THM] >>
          Cases_on `MEM v nl`
          >- (gvs[] >>
              Cases_on `stack_get_depth (Var v) ps.ps_stack`
              >- (gvs[] >> irule residual_budget_wf_extend_pending >>
                  first_assum ACCEPT_TAC)
              >> rename1 `stack_get_depth _ _ = SOME dist` >>
                 Cases_on `do_dup dist ps` >> gvs[] >>
                 imp_res_tac residual_budget_wf_dup)
          >> gvs[] >> irule residual_budget_wf_extend_pending >>
             first_assum ACCEPT_TAC)
      >> Cases_on `do_restore (Var v) ps` >>
         rename1 `do_restore (Var v) ps = (restore_ops, ps1)` >>
         `residual_budget_wf base' pending ps1` by
           imp_res_tac residual_budget_wf_restore >>
         gvs[emit_one_input_def, is_var_operand_def, LET_THM] >>
         Cases_on `MEM v nl`
         >- (gvs[] >> Cases_on `stack_get_depth (Var v) ps1.ps_stack`
             >- (gvs[] >> irule residual_budget_wf_extend_pending >>
                 first_assum ACCEPT_TAC)
             >> rename1 `stack_get_depth _ _ = SOME dist` >>
                Cases_on `do_dup dist ps1` >> gvs[] >>
                imp_res_tac residual_budget_wf_dup)
         >> gvs[] >> irule residual_budget_wf_extend_pending >>
            first_assum ACCEPT_TAC)
  >> gvs[emit_one_input_def, is_var_operand_def, LET_THM] >>
     Cases_on `opc = INVOKE` >> gvs[] >>
     irule residual_budget_wf_push >> first_assum ACCEPT_TAC
QED


Theorem do_dup_spilled_unchanged[local]:
  !(ps : plan_state) dist.
    (SND (do_dup dist ps)).ps_spilled = ps.ps_spilled
Proof
  gen_tac >> gen_tac >> Cases_on `dist <= 15` >>
  simp[do_dup_def, LET_THM] >> rpt (pairarg_tac >> gvs[])
QED

Theorem do_dup_inventory_count[local]:
  !(ps : plan_state) dist x.
    dist < LENGTH ps.ps_stack ==>
    LIST_ELEM_COUNT x (SND (do_dup dist ps)).ps_stack +
      (if x IN FDOM (SND (do_dup dist ps)).ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) +
      (if x = stack_peek dist ps.ps_stack then 1 else 0)
Proof
  rpt strip_tac >> drule_then assume_tac do_dup_stack_exact >>
  simp[do_dup_spilled_unchanged, elem_count_append, LIST_ELEM_COUNT_THM] >>
  Cases_on `x = stack_peek dist ps.ps_stack` >>
  simp[LIST_ELEM_COUNT_DEF]
QED

Theorem do_restore_inventory_count[local]:
  !(ps : plan_state) op off x.
    FLOOKUP ps.ps_spilled op = SOME off ==>
    LIST_ELEM_COUNT x (SND (do_restore op ps)).ps_stack +
      (if x IN FDOM (SND (do_restore op ps)).ps_spilled then 1 else 0) =
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac >>
  simp[do_restore_def, stack_push_def, elem_count_snoc,
       LIST_ELEM_COUNT_THM] >>
  Cases_on `x = op` >> gvs[flookup_thm, LIST_ELEM_COUNT_DEF]
QED

Theorem stack_get_depth_push_inventory[local]:
  !op stk. stack_get_depth op (stack_push op stk) = SOME 0
Proof
  rw[stack_get_depth_def, stack_push_def, REVERSE_SNOC, stack_find_def]
QED

Theorem stack_get_depth_restore_inventory[local]:
  !(ps : plan_state) op off.
    FLOOKUP ps.ps_spilled op = SOME off ==>
    stack_get_depth op (SND (do_restore op ps)).ps_stack = SOME 0
Proof
  simp[do_restore_def, stack_get_depth_push_inventory]
QED

Theorem emit_one_input_inventory_mono_aux[local]:
  !opc nl op (ps : plan_state) x.
    LIST_ELEM_COUNT x ps.ps_stack +
      (if x IN FDOM ps.ps_spilled then 1 else 0) <=
    LIST_ELEM_COUNT x (SND (emit_one_input opc nl op ps)).ps_stack +
      (if x IN FDOM (SND (emit_one_input opc nl op ps)).ps_spilled
       then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `op`
  >- simp[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def,
           elem_count_snoc, LIST_ELEM_COUNT_THM]
  >- (rename1 `Var v` >> Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (simp[emit_one_input_def, is_var_operand_def, LET_THM] >>
          Cases_on `MEM v nl` >> simp[]
          >- (Cases_on `stack_get_depth (Var v) ps.ps_stack` >> simp[] >>
              rename1 `stack_get_depth _ _ = SOME dist` >>
              `dist < LENGTH ps.ps_stack /\
               stack_peek dist ps.ps_stack = Var v` by
                metis_tac[stack_get_depth_props] >>
              qspecl_then [`ps`, `dist`, `x`] (drule_then assume_tac)
                do_dup_inventory_count >>
              qpat_assum
                `!y. LIST_ELEM_COUNT y (SND (do_dup dist ps)).ps_stack + _ = _`
                (qspec_then `x` assume_tac) >>
              CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
              simp[] >> decide_tac)
          >> simp[])
      >> rename1 `FLOOKUP ps.ps_spilled (Var v) = SOME off` >>
         Cases_on `do_restore (Var v) ps` >>
         rename1 `do_restore (Var v) ps = (restore_ops, psr)` >>
         qspecl_then [`ps`, `Var v`, `off`] mp_tac
           stack_get_depth_restore_inventory >> simp[] >> strip_tac >>
         `0 < LENGTH psr.ps_stack /\ stack_peek 0 psr.ps_stack = Var v` by
           metis_tac[stack_get_depth_props] >>
         qspecl_then [`ps`, `Var v`, `off`, `x`] mp_tac
           do_restore_inventory_count >> simp[] >> strip_tac >>
         Cases_on `MEM v nl`
         >- (qspecl_then [`psr`, `0`, `x`] (drule_then assume_tac)
               do_dup_inventory_count >>
             qpat_assum
               `!y. LIST_ELEM_COUNT y (SND (do_dup 0 psr)).ps_stack + _ = _`
               (qspec_then `x` assume_tac) >>
             Cases_on `do_dup 0 psr` >>
             gvs[emit_one_input_def, is_var_operand_def, LET_THM] >>
             decide_tac)
         >> simp[emit_one_input_def, is_var_operand_def, LET_THM])
  >> Cases_on `opc = INVOKE` >>
     gvs[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def,
         elem_count_snoc, LIST_ELEM_COUNT_THM] >> decide_tac
QED

Theorem stack_peek_eq_EL_REVERSE_inventory[local]:
  !stk d. d < LENGTH stk ==>
    stack_peek d stk = EL d (REVERSE stk)
Proof
  rpt strip_tac >> simp[stack_peek_def, EL_REVERSE] >>
  `PRE (LENGTH stk - d) = LENGTH stk - 1 - d` by decide_tac >> simp[]
QED

Theorem stack_get_depth_exists_inventory[local]:
  !op stk. MEM op stk ==> ?d. stack_get_depth op stk = SOME d
Proof
  rpt strip_tac >> Cases_on `stack_get_depth op stk` >> simp[] >>
  fs[stack_get_depth_NONE, MEM_EL] >>
  `LENGTH stk - 1 - n < LENGTH stk` by decide_tac >>
  `stack_peek (LENGTH stk - 1 - n) stk = op` by
    (`LENGTH stk - 1 - (LENGTH stk - 1 - n) = n` by decide_tac >>
     SIMP_TAC std_ss [stack_peek_def] >>
     qpat_assum `LENGTH stk - 1 - (LENGTH stk - 1 - n) = n`
       (fn th => rewrite_tac[th]) >>
     qpat_assum `op = EL n stk` (ACCEPT_TAC o SYM)) >>
  metis_tac[]
QED

Theorem elem_count_mem_pos_inventory[local]:
  !op stk. MEM op stk ==> 1 <= LIST_ELEM_COUNT op stk
Proof
  rpt strip_tac >> drule (iffRL LIST_ELEM_COUNT_MEM) >> decide_tac
QED

Theorem covered_operand_inventory[local]:
  !op (ps : plan_state).
    (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) ==>
    1 <= LIST_ELEM_COUNT op ps.ps_stack +
         (if op IN FDOM ps.ps_spilled then 1 else 0)
Proof
  rpt strip_tac
  >- (drule elem_count_mem_pos_inventory >> decide_tac)
  >> simp[]
QED
Theorem emit_one_input_inventory_inc[local]:
  !opc nl op (ps : plan_state).
    (~is_var_operand op \/
     ?v. op = Var v /\ MEM v nl /\
         (MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled)) ==>
    LIST_ELEM_COUNT op ps.ps_stack +
      (if op IN FDOM ps.ps_spilled then 1 else 0) + 1 <=
    LIST_ELEM_COUNT op (SND (emit_one_input opc nl op ps)).ps_stack +
      (if op IN FDOM (SND (emit_one_input opc nl op ps)).ps_spilled
       then 1 else 0)
Proof
  rpt gen_tac >> Cases_on `op`
  >- simp[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def,
           elem_count_snoc, LIST_ELEM_COUNT_THM]
  >- (rename1 `Var v` >> simp[is_var_operand_def] >> disch_then assume_tac >>
      Cases_on `FLOOKUP ps.ps_spilled (Var v)`
      >- (`MEM (Var v) ps.ps_stack` by
            metis_tac[flookup_thm] >>
          drule stack_get_depth_exists_inventory >> strip_tac >>
          rename1 `stack_get_depth (Var v) ps.ps_stack = SOME dist` >>
          `dist < LENGTH ps.ps_stack /\
           stack_peek dist ps.ps_stack = Var v` by
            metis_tac[stack_get_depth_props] >>
          qspecl_then [`ps`, `dist`, `Var v`] (drule_then assume_tac)
            do_dup_inventory_count >>
          qpat_assum
            `!z. LIST_ELEM_COUNT (Var z) (SND (do_dup dist ps)).ps_stack + _ = _`
            (qspec_then `v` assume_tac) >>
          Cases_on `do_dup dist ps` >>
          gvs[emit_one_input_def, is_var_operand_def, LET_THM] >> decide_tac)
      >> rename1 `FLOOKUP ps.ps_spilled (Var v) = SOME off` >>
         Cases_on `do_restore (Var v) ps` >>
         rename1 `do_restore (Var v) ps = (restore_ops, psr)` >>
         qspecl_then [`ps`, `Var v`, `off`] mp_tac
           stack_get_depth_restore_inventory >> simp[] >> strip_tac >>
         `0 < LENGTH psr.ps_stack /\ stack_peek 0 psr.ps_stack = Var v` by
           metis_tac[stack_get_depth_props] >>
         qspecl_then [`ps`, `Var v`, `off`, `Var v`] mp_tac
           do_restore_inventory_count >> simp[] >> strip_tac >>
         qspecl_then [`psr`, `0`, `Var v`] (drule_then assume_tac)
           do_dup_inventory_count >>
         qpat_assum
           `!z. LIST_ELEM_COUNT (Var z) (SND (do_dup 0 psr)).ps_stack + _ = _`
           (qspec_then `v` assume_tac) >>
         Cases_on `do_dup 0 psr` >>
         gvs[emit_one_input_def, is_var_operand_def, LET_THM] >> decide_tac)
  >> Cases_on `opc = INVOKE` >>
     gvs[emit_one_input_def, is_var_operand_def, LET_THM, stack_push_def,
         elem_count_snoc, LIST_ELEM_COUNT_THM] >> decide_tac
QED
Theorem inventory_available_chain[local]:
  !(a : num) b c. 1 <= a /\ a <= b /\ b <= c ==> 1 <= c
Proof
  rpt strip_tac >> decide_tac
QED

Theorem inventory_increment_chain[local]:
  !(a : num) b c. a + 1 <= b /\ b <= c ==> 1 <= c
Proof
  rpt strip_tac >> decide_tac
QED

Theorem inventory_double_from_available[local]:
  !(a : num) b c. 1 <= a /\ a + 1 <= b /\ b <= c ==> 2 <= c
Proof
  rpt strip_tac >> decide_tac
QED

Theorem inventory_double_increment[local]:
  !(a : num) b c. a + 1 <= b /\ b + 1 <= c ==> 2 <= c
Proof
  rpt strip_tac >> decide_tac
QED

Theorem inventory_double_offset_chain[local]:
  !(a : num) b c. a + 2 <= b /\ b <= c ==> 2 <= c
Proof
  rpt strip_tac >> decide_tac
QED

Theorem inventory_offset_le_transport[local]:
  !(a : num) x i k b.
    a = x + i /\ x + (i + k) <= b ==>
    a + k <= b
Proof
  rpt strip_tac >> decide_tac
QED

Theorem emit_input_plan_two_pending_inventory:
  !opc h h' nl ps iops ps1.
    (!op. MEM op [h;h'] /\ is_var_operand op ==>
          MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled) /\
    emit_input_plan opc [h;h'] nl ps = (iops,ps1) ==>
    pending_inventory_wf [h;h'] ps1
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `emit_input_plan _ _ _ _ = _` mp_tac >>
  simp[emit_input_plan_two] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[pending_inventory_wf_def] >> gen_tac >>
  `LIST_ELEM_COUNT op ps.ps_stack +
     (if op IN FDOM ps.ps_spilled then 1 else 0) <=
   LIST_ELEM_COUNT op ps1'.ps_stack +
     (if op IN FDOM ps1'.ps_spilled then 1 else 0)` by
    (qspecl_then [`opc`, `operand_vars [h'] ++ nl`, `h`, `ps`, `op`] mp_tac
       emit_one_input_inventory_mono_aux >> simp[]) >>
  `LIST_ELEM_COUNT op ps1'.ps_stack +
     (if op IN FDOM ps1'.ps_spilled then 1 else 0) <=
   LIST_ELEM_COUNT op ps1.ps_stack +
     (if op IN FDOM ps1.ps_spilled then 1 else 0)` by
    (qspecl_then [`opc`, `nl`, `h'`, `ps1'`, `op`] mp_tac
       emit_one_input_inventory_mono_aux >> simp[]) >>
  `is_var_operand h ==>
   1 <= LIST_ELEM_COUNT h ps.ps_stack +
        (if h IN FDOM ps.ps_spilled then 1 else 0)` by
    (strip_tac >> irule covered_operand_inventory >>
     qpat_assum `!x. _` (qspec_then `h` mp_tac) >> simp[]) >>
  `is_var_operand h' ==>
   1 <= LIST_ELEM_COUNT h' ps.ps_stack +
        (if h' IN FDOM ps.ps_spilled then 1 else 0)` by
    (strip_tac >> irule covered_operand_inventory >>
     qpat_assum `!x. _` (qspec_then `h'` mp_tac) >> simp[]) >>
  `(~is_var_operand h \/ h = h') ==>
   LIST_ELEM_COUNT h ps.ps_stack +
     (if h IN FDOM ps.ps_spilled then 1 else 0) + 1 <=
   LIST_ELEM_COUNT h ps1'.ps_stack +
     (if h IN FDOM ps1'.ps_spilled then 1 else 0)` by
    (strip_tac >>
     qspecl_then [`opc`, `operand_vars [h'] ++ nl`, `h`, `ps`] mp_tac
       emit_one_input_inventory_inc >> simp[] >>
     Cases_on `h` >>
     gvs[is_var_operand_def, operand_vars_def, operand_var_def]) >>
  `~is_var_operand h' ==>
   LIST_ELEM_COUNT h' ps1'.ps_stack +
     (if h' IN FDOM ps1'.ps_spilled then 1 else 0) + 1 <=
   LIST_ELEM_COUNT h' ps1.ps_stack +
     (if h' IN FDOM ps1.ps_spilled then 1 else 0)` by
    (strip_tac >>
     qspecl_then [`opc`, `nl`, `h'`, `ps1'`] mp_tac
       emit_one_input_inventory_inc >> simp[]) >>
  qabbrev_tac `A = LIST_ELEM_COUNT op ps.ps_stack +
    (if op IN FDOM ps.ps_spilled then 1 else 0)` >>
  qabbrev_tac `B = LIST_ELEM_COUNT op ps1'.ps_stack +
    (if op IN FDOM ps1'.ps_spilled then 1 else 0)` >>
  qabbrev_tac `C = LIST_ELEM_COUNT op ps1.ps_stack +
    (if op IN FDOM ps1.ps_spilled then 1 else 0)` >>
  Cases_on `op = h` >> Cases_on `op = h'` >>
  gvs[LIST_ELEM_COUNT_THM] >>
  Cases_on `is_var_operand h` >> Cases_on `is_var_operand h'` >>
  gvs[]
  >- (`A + 1 <= B` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `A`]) >>
      irule inventory_double_from_available >>
      goal_assum $ drule_at Any >> simp[])
  >- (`A + 1 <= B` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `A`]) >>
      irule inventory_double_from_available >>
      goal_assum $ drule_at Any >> simp[])
  >- (`A + 1 <= B` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `A`]) >>
      `B + 1 <= C` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `B`]) >>
      decide_tac)
  >- (`A + 1 <= B` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `A`]) >>
      `B + 1 <= C` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `B`]) >>
      decide_tac)
  >- (`A + 1 <= B` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `A`]) >>
      decide_tac)
  >- (`A + 1 <= B` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `A`]) >>
      decide_tac)
  >- (`B + 1 <= C` by
        (irule inventory_offset_le_transport >>
         goal_assum $ drule_at Any >>
         simp[Abbr `B`]) >>
      decide_tac)
  >> `B + 1 <= C` by
       (irule inventory_offset_le_transport >>
        goal_assum $ drule_at Any >>
        simp[Abbr `B`]) >>
     decide_tac
QED


Theorem elem_count_from_append[local]:
  !(full : 'a list) prefix suffix.
    full = prefix ++ suffix ==>
    !x. LIST_ELEM_COUNT x full =
        LIST_ELEM_COUNT x prefix + LIST_ELEM_COUNT x suffix
Proof
  rpt strip_tac >> gvs[elem_count_append]
QED
Theorem fixed_suffix_decompose[local]:
  !(stack : 'a list) pending.
    LENGTH pending <= LENGTH stack /\
    (!i. i < LENGTH pending ==>
       stack_peek (LENGTH pending - 1 - i) stack = EL i pending) ==>
    stack = stack_pop (LENGTH pending) stack ++ pending
Proof
  rpt gen_tac >> strip_tac >>
  `DROP (LENGTH stack - LENGTH pending) stack = pending` by
    (irule LIST_EQ >> simp[LENGTH_DROP] >> rpt strip_tac >>
     first_x_assum (qspec_then `x` mp_tac) >>
     simp[stack_peek_def, EL_DROP] >> decide_tac) >>
  simp[stack_pop_def] >>
  metis_tac[TAKE_DROP]
QED

Theorem plan_state_residual_wf_pop:
  !base pending ps.
    plan_state_residual_wf base pending (LENGTH pending) ps ==>
    plan_slots_bounded base
      (ps with ps_stack := stack_pop (LENGTH pending) ps.ps_stack) /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT (stack_pop (LENGTH pending) ps.ps_stack) /\
    DISJOINT (set (stack_pop (LENGTH pending) ps.ps_stack))
             (FDOM ps.ps_spilled)
Proof
  rpt gen_tac >> simp[plan_state_residual_wf_def] >> strip_tac >>
  `ps.ps_stack = stack_pop (LENGTH pending) ps.ps_stack ++ pending` by
    (irule fixed_suffix_decompose >> simp[]) >>
  drule elem_count_from_append >> disch_then assume_tac >>
  conj_tac
  >- (irule elem_count_le_one_all_distinct >> gen_tac >>
      qpat_assum
        `!op. LIST_ELEM_COUNT op ps.ps_stack <=
              SUC (LIST_ELEM_COUNT op pending)`
        (qspec_then `x` assume_tac) >>
      qpat_assum
        `!x. LIST_ELEM_COUNT x ps.ps_stack = _`
        (qspec_then `x` assume_tac) >>
      decide_tac)
  >> fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >>
     gen_tac >>
     Cases_on `x IN FDOM ps.ps_spilled` >> simp[] >>
     qpat_assum `!op. op IN FDOM ps.ps_spilled ==> _`
       (qspec_then `x` (drule_then assume_tac)) >>
     simp[GSYM LIST_ELEM_COUNT_MEM] >> decide_tac
QED

(* Concrete probes for multiplicity budgets and fixed-suffix elimination. *)
Theorem plan_state_residual_wf_duplicate_probe:
  let ps = (init_plan_state 0) with
             ps_stack := [Var "core_x"; Var "core_y";
                          Var "pending"; Var "pending"] in
    plan_state_residual_wf 0 [Var "pending"; Var "pending"] 2 ps
Proof
  EVAL_TAC >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `i = 0 \/ i = 1` by decide_tac >> gvs[])
  >> gen_tac >>
     Cases_on `Var "core_x" = op` >> gvs[] >>
     Cases_on `Var "core_y" = op` >> gvs[] >>
     Cases_on `Var "pending" = op` >> gvs[]
QED

Theorem plan_state_residual_wf_distinct_probe:
  let ps = (init_plan_state 0) with
             ps_stack := [Var "core_x"; Var "core_y";
                          Var "left"; Var "right"] in
    plan_state_residual_wf 0 [Var "left"; Var "right"] 2 ps
Proof
  EVAL_TAC >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `i = 0 \/ i = 1` by decide_tac >> gvs[])
  >> gen_tac >>
     Cases_on `Var "core_x" = op` >> gvs[] >>
     Cases_on `Var "core_y" = op` >> gvs[] >>
     Cases_on `Var "left" = op` >> gvs[] >>
     Cases_on `Var "right" = op` >> gvs[]
QED

Theorem plan_state_residual_wf_rejects_core_duplicate:
  let ps = (init_plan_state 0) with
             ps_stack := [Var "core"; Var "core";
                          Var "pending"; Var "pending"] in
    ~plan_state_residual_wf 0 [Var "pending"; Var "pending"] 2 ps
Proof
  EVAL_TAC >> strip_tac >>
  qpat_x_assum `!op. LENGTH _ <= _`
    (qspec_then `Var "core"` mp_tac) >> simp[]
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

(* Exchanging two in-range stack depths preserves the structural list facts. *)
Theorem stack_poke_exchange_structural_wf[local]:
  !stk d1 d2.
    ALL_DISTINCT stk /\ d1 < LENGTH stk /\ d2 < LENGTH stk ==>
    ALL_DISTINCT
      (stack_poke d2 (stack_peek d1 stk)
        (stack_poke d1 (stack_peek d2 stk) stk)) /\
    set (stack_poke d2 (stack_peek d1 stk)
          (stack_poke d1 (stack_peek d2 stk) stk)) = set stk
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `i1 = LENGTH stk - 1 - d1` >>
  qabbrev_tac `i2 = LENGTH stk - 1 - d2` >>
  `i1 < LENGTH stk /\ i2 < LENGTH stk` by
    simp[Abbr `i1`, Abbr `i2`] >>
  `stack_peek d1 stk = EL i1 stk /\
   stack_peek d2 stk = EL i2 stk` by
    simp[stack_peek_def, Abbr `i1`, Abbr `i2`] >>
  conj_tac
  >- (rw[EL_ALL_DISTINCT_EL_EQ, stack_poke_def, EL_LUPDATE] >>
      rpt (IF_CASES_TAC >> simp[]) >>
      metis_tac[ALL_DISTINCT_EL_IMP])
  >> rw[pred_setTheory.EXTENSION, MEM_EL] >>
  simp[stack_poke_def, EL_LUPDATE] >>
  metis_tac[]
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
    stack_peek dist ps.ps_stack = op /\ dist <> 0 /\
    dist < LENGTH ps.ps_stack ==>
    LAST (SND (do_swap dist ps)).ps_stack = op /\
    (SND (do_swap dist ps)).ps_stack <> []
Proof
  rpt gen_tac >> strip_tac >>
  `EL (LENGTH ps.ps_stack - (dist + 1)) ps.ps_stack = op` by
    fs[stack_peek_def] >>
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

(* A generated swap places the old TOS value at its requested depth. *)
Theorem do_swap_peek_dist[local]:
  !dist ps.
    dist < LENGTH ps.ps_stack ==>
    stack_peek dist (SND (do_swap dist ps)).ps_stack =
      stack_peek 0 ps.ps_stack
Proof
  rpt strip_tac >>
  Cases_on `dist = 0`
  >- simp[do_swap_def] >>
  Cases_on `dist <= 16`
  >- simp[do_swap_def, stack_peek_def, stack_swap_def, LET_THM,
          EL_LUPDATE] >>
  qspecl_then [`dist`, `ps`] mp_tac do_swap_deep_stack >>
  simp[] >> strip_tac >>
  simp[stack_peek_def, top_n_def, LENGTH_TAKE, EL_APPEND_EQN,
       GSYM rich_listTheory.LASTN_def, rich_listTheory.LASTN_DROP] >>
  once_rewrite_tac[GSYM (cj 1 EL)] >>
  simp[EL_DROP]
QED

(* Updating one in-range depth leaves every other in-range depth unchanged. *)
Theorem stack_poke_peek_other[local]:
  !stk d k op.
    d < LENGTH stk /\ k < LENGTH stk /\ k <> d ==>
    stack_peek k (stack_poke d op stk) = stack_peek k stk
Proof
  rpt strip_tac >>
  simp[stack_peek_def, stack_poke_def, LENGTH_LUPDATE, EL_LUPDATE] >>
  `LENGTH stk - 1 - k <> LENGTH stk - 1 - d` by decide_tac >>
  simp[]
QED

(* A shallow generated swap changes only TOS and its requested depth. *)
Theorem do_swap_peek_other[local]:
  !dist k ps.
    dist <= 16 /\ dist < LENGTH ps.ps_stack /\ k < LENGTH ps.ps_stack /\
    k <> 0 /\ k <> dist ==>
    stack_peek k (SND (do_swap dist ps)).ps_stack = stack_peek k ps.ps_stack
Proof
  rpt strip_tac >>
  Cases_on `dist = 0` >- simp[do_swap_def] >>
  simp[do_swap_def, stack_peek_def, stack_swap_def, LET_THM,
       LENGTH_LUPDATE, EL_LUPDATE] >>
  `LENGTH ps.ps_stack - 1 - k <> PRE (LENGTH ps.ps_stack)` by decide_tac >>
  `LENGTH ps.ps_stack - 1 - k <>
   LENGTH ps.ps_stack - (dist + 1)` by decide_tac >>
  simp[]
QED

(* A deep generated swap also leaves every non-TOS shallower depth unchanged. *)
Theorem do_swap_peek_shallower[local]:
  !dist k ps.
    k < dist /\ dist < LENGTH ps.ps_stack /\ k <> 0 ==>
    stack_peek k (SND (do_swap dist ps)).ps_stack = stack_peek k ps.ps_stack
Proof
  rpt strip_tac >>
  Cases_on `dist <= 16`
  >- (irule do_swap_peek_other >> simp[]) >>
  qspecl_then [`dist`, `ps`] mp_tac do_swap_deep_stack >>
  simp[] >> strip_tac >>
  simp[stack_peek_def, top_n_def, LENGTH_TAKE, EL_APPEND_EQN,
       GSYM rich_listTheory.LASTN_def, rich_listTheory.LASTN_DROP] >>
  `dist - (k + 1) < dist - 1` by decide_tac >>
  simp[EL_MAP, EL_GENLIST, EL_DROP] >>
  AP_TERM_TAC >> decide_tac
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
    simp[reorder_one_def, LET_THM, stack_get_unfixed_depth_empty_window] >>
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
  simp[reorder_one_def, LET_THM, stack_get_unfixed_depth_empty_window] >>
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
  rename1 `reduce_depth_plan _ _ _ _ _ _ = (reduce_ops, ps2)` >>
  qspecl_then [`LENGTH ps.ps_stack`, `[op]`, `op`, `0`, `1`, `ps`, `d0`]
    mp_tac (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)
              (REWRITE_RULE [LET_THM] reduce_depth_plan_dist_ge)) >>
  (impl_tac >- simp[stack_get_unfixed_depth_empty_window]) >>
  simp[stack_get_unfixed_depth_empty_window] >> strip_tac >>
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
  imp_res_tac stack_get_depth_el >>
  qspecl_then [`SUC n`, `ps2`, `op`] mp_tac do_swap_last >>
  simp[stack_peek_def]
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
  simp[reorder_one_def, LET_THM, stack_get_unfixed_depth_empty_window] >>
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
  !fuel target_ops target_op f target_len ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
    spill_alloc_layout_wf
      (SND (reduce_depth_plan fuel target_ops target_op f target_len ps)).ps_alloc
      (SND (reduce_depth_plan fuel target_ops target_op f target_len ps)).ps_spilled /\
    ALL_DISTINCT
      (SND (reduce_depth_plan fuel target_ops target_op f target_len ps)).ps_stack /\
    DISJOINT
      (set (SND (reduce_depth_plan fuel target_ops target_op f target_len ps)).ps_stack)
      (FDOM (SND (reduce_depth_plan fuel target_ops target_op f target_len ps)).ps_spilled)
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >>
  simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >>
  simp[] >> pairarg_tac >> simp[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  imp_res_tac select_spill_candidate_bound >>
  `spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
   ALL_DISTINCT ps'.ps_stack /\
   DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled)` by (
    qspecl_then [`x'`, `ps`] mp_tac do_spill_at_structural_wf >> simp[]) >>
  first_x_assum
    (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`, `ps'`] mp_tac) >>
  simp[] >> strip_tac >> pairarg_tac >>
  Cases_on `x <= 16` >> gvs[]
QED


Theorem reorder_restore_structural_wf[local]:
  !op f target_len ps.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
    spill_alloc_layout_wf
      (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
              SOME _ => ([] : stack_op list, ps)
            | NONE =>
                (case FLOOKUP ps.ps_spilled op of
                   SOME _ => do_restore op ps
                 | NONE => ([], ps)))).ps_alloc
      (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
              SOME _ => ([] : stack_op list, ps)
            | NONE =>
                (case FLOOKUP ps.ps_spilled op of
                   SOME _ => do_restore op ps
                 | NONE => ([], ps)))).ps_spilled /\
    ALL_DISTINCT
      (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
              SOME _ => ([] : stack_op list, ps)
            | NONE =>
                (case FLOOKUP ps.ps_spilled op of
                   SOME _ => do_restore op ps
                 | NONE => ([], ps)))).ps_stack /\
    DISJOINT
      (set (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
                   SOME _ => ([] : stack_op list, ps)
                 | NONE =>
                     (case FLOOKUP ps.ps_spilled op of
                        SOME _ => do_restore op ps
                      | NONE => ([], ps)))).ps_stack)
      (FDOM (SND (case stack_get_unfixed_depth op f target_len ps.ps_stack of
                    SOME _ => ([] : stack_op list, ps)
                  | NONE =>
                      (case FLOOKUP ps.ps_spilled op of
                         SOME _ => do_restore op ps
                       | NONE => ([], ps)))).ps_spilled)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `stack_get_unfixed_depth op f target_len ps.ps_stack` >> simp[] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  metis_tac[do_restore_structural_wf]
QED

Theorem do_spill_at_stack_length[local]:
  !d ps.
    d < LENGTH ps.ps_stack ==>
    LENGTH (SND (do_spill_at d ps)).ps_stack = LENGTH ps.ps_stack - 1
Proof
  rpt gen_tac >> strip_tac >>
  simp[do_spill_at_def, do_spill_tos_def, LET_THM] >>
  Cases_on `d = 0` >> simp[stack_pop_def] >>
  Cases_on `alloc_spill_slot ps.ps_alloc` >> gvs[stack_pop_def]
QED

Theorem reduce_depth_plan_length_floor:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') ==>
    MIN 17 (LENGTH ps.ps_stack) <= LENGTH ps'.ps_stack
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >>
  simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >>
  simp[] >> pairarg_tac >> simp[] >>
  rename1 `do_spill_at x' ps = (spill_ops, ps1)` >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  drule stack_get_unfixed_depth_bound >> strip_tac >>
  `1 <= LENGTH ps.ps_stack` by decide_tac >>
  `x' < LENGTH ps.ps_stack` by
    metis_tac[select_spill_candidate_bound] >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack - 1` by (
    qspecl_then [`x'`, `ps`] mp_tac do_spill_at_stack_length >>
    simp[] >> gvs[]) >>
  first_x_assum
    (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`, `ps1`,
                  `rest_ops`, `ps'`] mp_tac) >>
  simp[] >> Cases_on `x <= 16` >> gvs[] >> decide_tac
QED

Theorem reorder_one_residual_budget_wf:
  !dfg pending idx op ps ops ps' base.
    residual_budget_wf base pending ps /\
    idx < LENGTH pending /\
    LENGTH pending <= LENGTH ps.ps_stack /\
    LENGTH pending <= 16 /\
    reorder_one dfg pending idx op ps = (ops, ps') ==>
    residual_budget_wf base pending ps' /\
    LENGTH pending <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf base' pending ps1 /\
   LENGTH pending <= LENGTH ps1.ps_stack` by
    (qspecl_then [`base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps`]
       mp_tac reorder_restore_residual_budget_wf >> simp[] >> gvs[]) >>
  gvs[] >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `residual_budget_wf base' pending ps2` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `base'`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `ps1`, `reduce_ops`, `ps2`]
       mp_tac reduce_depth_plan_residual_budget_wf >> simp[]) >>
  `LENGTH pending <= LENGTH ps2.ps_stack` by
    (Cases_on `x > 16` >> gvs[] >>
     qspecl_then [`LENGTH ps1.ps_stack`, `pending`, `op`,
       `LENGTH pending - (idx + 1)`, `LENGTH pending`, `ps1`,
       `reduce_ops`, `ps2`] mp_tac reduce_depth_plan_length_floor >>
     simp[] >> decide_tac) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH pending - (idx + 1)) (LENGTH pending) ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  qpat_x_assum `stack_peek dist' ps2.ps_stack = op`
    (fn th => SUBST_ALL_TAC (SYM th)) >>
  `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = LENGTH pending - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `LENGTH pending - (idx + 1) < LENGTH ps2.ps_stack` >> gvs[] >>
  Cases_on `operand_equiv dfg (stack_peek dist' ps2.ps_stack)
    (stack_peek (LENGTH pending - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> gvs[] >> conj_tac
      >- (irule residual_budget_wf_stack_poke_exchange >> simp[])
      >> simp[stack_poke_def]) >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops, ps3)` >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap (LENGTH pending - (idx + 1)) ps3 =
           (swap2_ops, ps4)` >>
  `residual_budget_wf base' pending ps3` by
    metis_tac[residual_budget_wf_do_swap] >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by
    (qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >> simp[]) >>
  `residual_budget_wf base' pending ps4` by
    (qspecl_then [`base'`, `pending`,
       `LENGTH pending - (idx + 1)`, `ps3`, `swap2_ops`, `ps4`]
       mp_tac residual_budget_wf_do_swap >> simp[]) >>
  `LENGTH ps4.ps_stack = LENGTH ps3.ps_stack` by
    (qspecl_then [`LENGTH pending - (idx + 1)`, `ps3`]
       mp_tac do_swap_length >> simp[]) >>
  strip_tac >> gvs[]
QED

Theorem reorder_one_structural_wf:
  !dfg target_ops idx op ps ops ps'.
    LENGTH target_ops <= 17 /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\
    reorder_one dfg target_ops idx op ps = (ops, ps') /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) ==>
    spill_alloc_layout_wf ps'.ps_alloc ps'.ps_spilled /\
    ALL_DISTINCT ps'.ps_stack /\
    DISJOINT (set ps'.ps_stack) (FDOM ps'.ps_spilled) /\
    LENGTH target_ops <= LENGTH ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled /\
   ALL_DISTINCT ps1.ps_stack /\
   DISJOINT (set ps1.ps_stack) (FDOM ps1.ps_spilled)` by (
    qspecl_then [`op`, `num_ops - (idx + 1)`, `num_ops`, `ps`]
      mp_tac reorder_restore_structural_wf >>
    simp[] >> gvs[]) >>
  `LENGTH target_ops <= LENGTH ps1.ps_stack` by (
    Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops
      ps.ps_stack` >> gvs[]
    >- (Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >>
        qspecl_then [`op`, `ps`] mp_tac do_restore_length >> simp[])) >>
  Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops
    ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  pairarg_tac >> simp[] >>
  `spill_alloc_layout_wf ps2.ps_alloc ps2.ps_spilled /\
   ALL_DISTINCT ps2.ps_stack /\
   DISJOINT (set ps2.ps_stack) (FDOM ps2.ps_spilled)` by (
    Cases_on `x > 16`
    >- (qspecl_then [`LENGTH ps1.ps_stack`, `target_ops`, `op`,
          `num_ops - (idx + 1)`, `num_ops`, `ps1`]
          mp_tac reduce_depth_plan_structural_wf >>
        simp[] >> gvs[])
    >> gvs[]) >>
  `LENGTH target_ops <= LENGTH ps2.ps_stack` by (
    Cases_on `x > 16`
    >- (qspecl_then [`LENGTH ps1.ps_stack`, `target_ops`, `op`,
          `num_ops - (idx + 1)`, `num_ops`, `ps1`]
          mp_tac reduce_depth_plan_length_floor >>
        simp[] >> strip_tac >> gvs[] >> decide_tac)
    >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op (num_ops - (idx + 1)) num_ops
    ps2.ps_stack` >> simp[]
  >- (strip_tac >> gvs[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `num_ops - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  Cases_on `dist' = num_ops - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[]) >>
  Cases_on `operand_equiv dfg op
              (stack_peek (num_ops - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (`ALL_DISTINCT
         (stack_poke (num_ops - (idx + 1)) (stack_peek dist' ps2.ps_stack)
           (stack_poke dist'
             (stack_peek (num_ops - (idx + 1)) ps2.ps_stack) ps2.ps_stack)) /\
       set
         (stack_poke (num_ops - (idx + 1)) (stack_peek dist' ps2.ps_stack)
           (stack_poke dist'
             (stack_peek (num_ops - (idx + 1)) ps2.ps_stack) ps2.ps_stack)) =
       set ps2.ps_stack` by (
        irule stack_poke_exchange_structural_wf >> simp[]) >>
      strip_tac >> gvs[] >>
      rpt conj_tac >> simp[stack_poke_def] >>
      fs[pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >>
  `spill_alloc_layout_wf ps3.ps_alloc ps3.ps_spilled /\
   ALL_DISTINCT ps3.ps_stack /\
   DISJOINT (set ps3.ps_stack) (FDOM ps3.ps_spilled)` by (
    qspecl_then [`dist'`, `ps2`] mp_tac
      doSwapSimTheory.do_swap_structural_layout_wf >> simp[] >> gvs[]) >>
  `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by (
    qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >> simp[] >> gvs[]) >>
  `spill_alloc_layout_wf ps4.ps_alloc ps4.ps_spilled /\
   ALL_DISTINCT ps4.ps_stack /\
   DISJOINT (set ps4.ps_stack) (FDOM ps4.ps_spilled)` by (
    qspecl_then [`num_ops - (idx + 1)`, `ps3`] mp_tac
      doSwapSimTheory.do_swap_structural_layout_wf >> simp[] >> gvs[]) >>
  `LENGTH ps4.ps_stack = LENGTH ps3.ps_stack` by (
    qspecl_then [`num_ops - (idx + 1)`, `ps3`] mp_tac do_swap_length >>
    simp[] >> gvs[]) >>
  strip_tac >> gvs[]
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
  !fuel target_ops target_op f target_len ps.
    EVERY (\op. (?d. op = SOSwap d) \/ (?off. op = SOSpill off))
      (FST (reduce_depth_plan fuel target_ops target_op f target_len ps))
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM] >>
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack` >>
  simp[] >> IF_CASES_TAC >> simp[] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops x target_len` >>
  simp[] >>
  Cases_on `do_spill_at x' ps` >>
  rename1 `do_spill_at _ ps = (spill_ops, ps1)` >> simp[] >>
  Cases_on `reduce_depth_plan fuel target_ops target_op f target_len ps1` >>
  rename1 `reduce_depth_plan _ _ _ _ _ _ = (rest_ops, ps2)` >>
  Cases_on `x <= 16`
  >- simp[] >>
  simp[EVERY_APPEND] >> conj_tac
  >- (`spill_ops = FST (do_spill_at x' ps)` by simp[] >>
      metis_tac[do_spill_at_only_swap_spill]) >>
  first_x_assum
    (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`, `ps1`] mp_tac) >>
  simp[]
QED

Theorem reduce_depth_plan_align[local]:
  !fuel target_ops target_op f target_len ps lo.
    let (ops, ps') =
      reduce_depth_plan fuel target_ops target_op f target_len ps in
    (apply_prefix_ops initial_fmp lo ops ps).ps_stack = ps'.ps_stack /\
    (apply_prefix_ops initial_fmp lo ops ps).ps_spilled = ps'.ps_spilled
Proof
  Induct >> simp[reduce_depth_plan_def, LET_THM, apply_prefix_ops_def] >>
  rpt gen_tac >>
  Cases_on `stack_get_unfixed_depth target_op f target_len ps.ps_stack`
  >- simp[apply_prefix_ops_def] >>
  rename1 `stack_get_unfixed_depth _ _ _ _ = SOME dist` >>
  simp[] >> IF_CASES_TAC >- simp[apply_prefix_ops_def] >>
  Cases_on `select_spill_candidate ps.ps_stack target_ops dist target_len`
  >- simp[apply_prefix_ops_def] >>
  rename1 `select_spill_candidate _ _ _ _ = SOME cand` >>
  simp[] >>
  Cases_on `do_spill_at cand ps` >>
  rename1 `do_spill_at cand ps = (spill_ops, ps1)` >>
  simp[] >>
  Cases_on `reduce_depth_plan fuel target_ops target_op f target_len ps1` >>
  rename1 `reduce_depth_plan _ _ _ _ _ _ = (rest_ops, ps2)` >>
  simp[] >> simp[apply_prefix_ops_append] >>
  first_x_assum (qspecl_then
    [`target_ops`, `target_op`, `f`, `target_len`, `ps1`, `lo`] mp_tac) >>
  simp[LET_THM] >> strip_tac >>
  Cases_on `dist <= 16`
  >- simp[apply_prefix_ops_def] >>
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
      qspecl_then [`fuel`, `target_ops`, `target_op`, `f`, `target_len`, `ps1`]
        mp_tac reduce_depth_plan_only_swap_spill >>
      gvs[]) >>
    pop_assum mp_tac >> match_mp_tac EVERY_MONOTONIC >>
    simp[] >> metis_tac[]) >>
  (* apply_ssr_ops_indep + IH *)
  qspecl_then [`rest_ops`, `lo`,
    `apply_prefix_ops initial_fmp lo spill_ops ps`, `ps1`]
    mp_tac apply_ssr_ops_indep >>
  simp[apply_prefix_ops_append]
QED

Finalise reduce_depth_plan_align;


(* Prefix interpretation depends only on the planner stack and spill map. *)
Theorem apply_prefix_ops_ext_stack_spilled[local]:
  !ops lo ps1 ps2.
    ps1.ps_stack = ps2.ps_stack /\
    ps1.ps_spilled = ps2.ps_spilled ==>
    (apply_prefix_ops initial_fmp lo ops ps1).ps_stack =
      (apply_prefix_ops initial_fmp lo ops ps2).ps_stack /\
    (apply_prefix_ops initial_fmp lo ops ps1).ps_spilled =
      (apply_prefix_ops initial_fmp lo ops ps2).ps_spilled
Proof
  Induct >> simp[apply_prefix_ops_def] >>
  rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  Cases_on `h` >>
  simp[apply_prefix_op_def, apply_simple_op_def,
       stack_push_def, stack_pop_def, stack_swap_def,
       stack_peek_def, stack_poke_def, spill_lookup_def] >>
  TRY (Cases_on `o'` >> simp[apply_simple_op_def, stack_push_def])
QED

(* Executing the emitted operations of one reorder step agrees with the
   formal planner output up to runtime operand values.  Alias-only pokes are
   the sole non-syntactic branch. *)
Theorem stack_poke_peek[local]:
  !d stk. d < LENGTH stk ==> stack_poke d (stack_peek d stk) stk = stk
Proof
  rpt strip_tac >>
  simp[stack_poke_def, stack_peek_def, listTheory.LUPDATE_SAME]
QED

Theorem reorder_one_sem_align:
  !dfg target_ops idx op ps ops ps' lo vs.
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    ALL_DISTINCT ps.ps_stack /\
    DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
    idx < LENGTH target_ops /\
    MEM op target_ops /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\
    LENGTH target_ops <= 16 /\
    reorder_one dfg target_ops idx op ps = (ops, ps') /\
    (!op1 at. operand_equiv dfg op1 at ==>
              operand_val vs lo op1 = operand_val vs lo at) ==>
    plan_stack_sem_eq lo vs
      (apply_prefix_ops initial_fmp lo ops ps).ps_stack ps'.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM] >>
  pairarg_tac >> simp[] >>
  rename1 `(case stack_get_unfixed_depth op
    (LENGTH target_ops - (idx + 1)) (LENGTH target_ops) ps.ps_stack of _ => _) =
    (restore_ops,ps1)` >>
  `(apply_prefix_ops initial_fmp lo restore_ops ps).ps_stack = ps1.ps_stack /\
   (apply_prefix_ops initial_fmp lo restore_ops ps).ps_spilled = ps1.ps_spilled` by (
    qpat_x_assum `(case stack_get_unfixed_depth op _ _ ps.ps_stack of _ => _) = _`
      mp_tac >>
    Cases_on `stack_get_unfixed_depth op
      (LENGTH target_ops - (idx + 1)) (LENGTH target_ops) ps.ps_stack` >>
    simp[apply_prefix_ops_def] >>
    Cases_on `FLOOKUP ps.ps_spilled op` >> simp[apply_prefix_ops_def] >>
    strip_tac >> drule do_restore_ss_align >>
    disch_then (qspecl_then [`initial_fmp`, `lo`] mp_tac) >>
    (impl_tac >- metis_tac[spill_alloc_layout_wf_spilled_separated]) >>
    simp[]) >>
  `spill_alloc_layout_wf ps1.ps_alloc ps1.ps_spilled /\
   ALL_DISTINCT ps1.ps_stack /\
   DISJOINT (set ps1.ps_stack) (FDOM ps1.ps_spilled)` by (
    qspecl_then [`op`, `LENGTH target_ops - (idx + 1)`,
      `LENGTH target_ops`, `ps`] mp_tac reorder_restore_structural_wf >>
    simp[] >> gvs[]) >>
  Cases_on `stack_get_unfixed_depth op
    (LENGTH target_ops - (idx + 1)) (LENGTH target_ops) ps1.ps_stack` >> simp[]
  >- (strip_tac >> gvs[apply_prefix_ops_append] >> simp[]) >>
  pairarg_tac >> simp[] >>
  rename1 `(if x > 16 then _ else _) = (reduce_ops,ps2)` >>
  `(apply_prefix_ops initial_fmp lo reduce_ops ps1).ps_stack = ps2.ps_stack /\
   (apply_prefix_ops initial_fmp lo reduce_ops ps1).ps_spilled = ps2.ps_spilled` by (
    Cases_on `x > 16` >> gvs[apply_prefix_ops_def] >>
    qspecl_then [`LENGTH ps1.ps_stack`, `target_ops`, `op`,
      `LENGTH target_ops - (idx + 1)`, `LENGTH target_ops`, `ps1`, `lo`]
      mp_tac reduce_depth_plan_align >> simp[LET_THM]) >>
  `spill_alloc_layout_wf ps2.ps_alloc ps2.ps_spilled /\
   ALL_DISTINCT ps2.ps_stack /\
   DISJOINT (set ps2.ps_stack) (FDOM ps2.ps_spilled)` by (
    Cases_on `x > 16` >> gvs[] >>
    qspecl_then [`LENGTH ps1.ps_stack`, `target_ops`, `op`,
      `LENGTH target_ops - (idx + 1)`, `LENGTH target_ops`, `ps1`]
      mp_tac reduce_depth_plan_structural_wf >> simp[]) >>
  `(apply_prefix_ops initial_fmp lo (restore_ops ++ reduce_ops) ps).ps_stack =
     ps2.ps_stack` by (
    simp[apply_prefix_ops_append] >>
    `((apply_prefix_ops initial_fmp lo reduce_ops
        (apply_prefix_ops initial_fmp lo restore_ops ps)).ps_stack =
       (apply_prefix_ops initial_fmp lo reduce_ops ps1).ps_stack)` by (
      irule (cj 1 apply_prefix_ops_ext_stack_spilled) >> simp[]) >>
    simp[]) >>
  `LENGTH target_ops <= LENGTH ps1.ps_stack` by (
    qpat_x_assum `(case stack_get_unfixed_depth op _ _ ps.ps_stack of _ => _) = _`
      mp_tac >>
    Cases_on `stack_get_unfixed_depth op
      (LENGTH target_ops - (idx + 1)) (LENGTH target_ops) ps.ps_stack` >> simp[]
    >- (Cases_on `FLOOKUP ps.ps_spilled op` >> simp[]
        >- (strip_tac >> gvs[]) >>
        strip_tac >> qspecl_then [`op`, `ps`] mp_tac do_restore_length >>
        simp[] >> strip_tac >> gvs[] >> decide_tac) >>
    strip_tac >> gvs[]) >>
  `LENGTH target_ops <= LENGTH ps2.ps_stack` by (
    Cases_on `x > 16` >> gvs[] >>
    qspecl_then [`LENGTH ps1.ps_stack`, `target_ops`, `op`,
      `LENGTH target_ops - (idx + 1)`, `LENGTH target_ops`, `ps1`,
      `reduce_ops`, `ps2`] mp_tac reduce_depth_plan_length_floor >>
    simp[] >> decide_tac) >>
  `?dist'. stack_get_unfixed_depth op
      (LENGTH target_ops - (idx + 1)) (LENGTH target_ops) ps2.ps_stack =
      SOME dist'` by (
    Cases_on `x > 16` >> gvs[] >>
    qspecl_then [`LENGTH ps1.ps_stack`, `target_ops`, `op`,
      `LENGTH target_ops - (idx + 1)`, `LENGTH target_ops`, `ps1`, `x`]
      mp_tac (REWRITE_RULE [LET_THM] reduce_depth_plan_dist_ge) >>
    simp[] >> metis_tac[]) >>
  rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
  `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `LENGTH target_ops - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
  simp[] >>
  Cases_on `dist' = LENGTH target_ops - (idx + 1)` >> simp[]
  >- (strip_tac >> gvs[apply_prefix_ops_append] >> simp[]) >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH target_ops - (idx + 1)) ps2.ps_stack)` >> simp[]
  >- (strip_tac >> fs[apply_prefix_ops_append] >>
      `stack_poke dist' op ps2.ps_stack = ps2.ps_stack` by
        metis_tac[stack_poke_peek] >>
      `plan_stack_sem_eq lo vs ps2.ps_stack
         (stack_poke dist'
            (stack_peek (LENGTH target_ops - (idx + 1)) ps2.ps_stack)
            ps2.ps_stack)` by (
        qspecl_then [`lo`, `vs`, `ps2.ps_stack`, `ps2.ps_stack`,
          `dist'`, `op`,
          `stack_peek (LENGTH target_ops - (idx + 1)) ps2.ps_stack`]
          mp_tac plan_stack_sem_eq_poke >>
        (impl_tac >- (simp[] >> first_x_assum irule >> simp[])) >>
        simp[stack_poke_peek]) >>
      qspecl_then [`lo`, `vs`, `ps2.ps_stack`,
        `stack_poke dist'
          (stack_peek (LENGTH target_ops - (idx + 1)) ps2.ps_stack)
          ps2.ps_stack`,
        `LENGTH target_ops - (idx + 1)`,
        `stack_peek (LENGTH target_ops - (idx + 1)) ps2.ps_stack`, `op`]
        mp_tac plan_stack_sem_eq_poke >>
      simp[stack_poke_peek] >> strip_tac >>
      gvs[] >> simp[apply_prefix_ops_append]) >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap dist' ps2 = (swap1_ops,ps3)` >>
  pairarg_tac >> simp[] >>
  rename1 `do_swap (LENGTH target_ops - (idx + 1)) ps3 =
           (swap2_ops,ps4)` >>
  strip_tac >> gvs[] >>
  `spill_alloc_layout_wf ps3.ps_alloc ps3.ps_spilled /\
   ALL_DISTINCT ps3.ps_stack /\
   DISJOINT (set ps3.ps_stack) (FDOM ps3.ps_spilled)` by (
    qspecl_then [`dist'`, `ps2`] mp_tac do_swap_structural_layout_wf >>
    simp[]) >>
  `(apply_prefix_ops initial_fmp lo swap1_ops ps2).ps_stack = ps3.ps_stack /\
   (apply_prefix_ops initial_fmp lo swap1_ops ps2).ps_spilled = ps3.ps_spilled` by (
    qspecl_then [`dist'`, `ps2`, `lo`] mp_tac
      do_swap_apply_relevant_align_layout >>
    simp[LET_THM]) >>
  `(apply_prefix_ops initial_fmp lo swap2_ops ps3).ps_stack = ps'.ps_stack /\
   (apply_prefix_ops initial_fmp lo swap2_ops ps3).ps_spilled = ps'.ps_spilled` by (
    qspecl_then [`LENGTH target_ops - (idx + 1)`, `ps3`, `lo`] mp_tac
      do_swap_apply_relevant_align_layout >>
    simp[LET_THM] >>
    `LENGTH ps3.ps_stack = LENGTH ps2.ps_stack` by (
      qspecl_then [`dist'`, `ps2`] mp_tac do_swap_length >> simp[]) >>
    simp[]) >>
  `(apply_prefix_ops initial_fmp lo (restore_ops ++ reduce_ops) ps).ps_spilled =
     ps2.ps_spilled` by (
    simp[apply_prefix_ops_append] >>
    `(apply_prefix_ops initial_fmp lo reduce_ops
        (apply_prefix_ops initial_fmp lo restore_ops ps)).ps_spilled =
      (apply_prefix_ops initial_fmp lo reduce_ops ps1).ps_spilled` by (
      irule (cj 2 apply_prefix_ops_ext_stack_spilled) >> simp[]) >>
    simp[]) >>
  `let pre = apply_prefix_ops initial_fmp lo
               (restore_ops ++ reduce_ops) ps;
       via1 = apply_prefix_ops initial_fmp lo swap1_ops pre
   in via1.ps_stack = ps3.ps_stack /\
      via1.ps_spilled = ps3.ps_spilled` by (
    simp[LET_THM] >>
    qspecl_then [`swap1_ops`, `lo`,
      `apply_prefix_ops initial_fmp lo (restore_ops ++ reduce_ops) ps`, `ps2`]
      mp_tac apply_prefix_ops_ext_stack_spilled >> simp[]) >>
  `let pre = apply_prefix_ops initial_fmp lo
               (restore_ops ++ reduce_ops) ps;
       via1 = apply_prefix_ops initial_fmp lo swap1_ops pre;
       via2 = apply_prefix_ops initial_fmp lo swap2_ops via1
   in via2.ps_stack = ps'.ps_stack` by (
    gvs[LET_THM] >>
    qspecl_then [`swap2_ops`, `lo`,
      `apply_prefix_ops initial_fmp lo swap1_ops
        (apply_prefix_ops initial_fmp lo
          (restore_ops ++ reduce_ops) ps)`, `ps3`]
      mp_tac apply_prefix_ops_ext_stack_spilled >> simp[]) >>
  gvs[LET_THM] >>

  qpat_x_assum
    `(apply_prefix_ops initial_fmp lo swap2_ops
       (apply_prefix_ops initial_fmp lo swap1_ops
         (apply_prefix_ops initial_fmp lo
           (restore_ops ++ reduce_ops) ps))).ps_stack = ps'.ps_stack`
    mp_tac >>
  simp[apply_prefix_ops_append]
QED


Theorem reorder_place_phase_places[local]:
  !dfg op dist final_dist ps.
    dist < LENGTH ps.ps_stack /\
    stack_peek dist ps.ps_stack = op /\
    final_dist < LENGTH ps.ps_stack ==>
    let (_,ps') =
      if dist = final_dist then ([] : stack_op list,ps)
      else
        let at_target = stack_peek final_dist ps.ps_stack in
        if operand_equiv dfg op at_target then
          ([],ps with ps_stack :=
             stack_poke final_dist op
               (stack_poke dist at_target ps.ps_stack))
        else
          let (s1,ps1) = do_swap dist ps in
          let (s2,ps2) = do_swap final_dist ps1 in
          (s1 ++ s2,ps2)
    in stack_peek final_dist ps'.ps_stack = op
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `dist = final_dist`
  >- gvs[] >>
  Cases_on `operand_equiv dfg op (stack_peek final_dist ps.ps_stack)` >> simp[]
  >- simp[stack_peek_def, stack_poke_def, EL_LUPDATE] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `stack_peek 0 ps1.ps_stack = op` by (
    Cases_on `dist = 0`
    >- (gvs[do_swap_def] >>
        imp_res_tac stack_get_depth_el >>
        simp[stack_peek_def]) >>
    qspecl_then [`dist`, `ps`, `op`] mp_tac do_swap_last >>
    (impl_tac >- simp[]) >> strip_tac >>
    `ps1.ps_stack <> []` by gvs[] >>
    `stack_peek 0 ps1.ps_stack = LAST ps1.ps_stack` by (
      Cases_on `ps1.ps_stack` >> gvs[stack_peek_def, LAST_EL]) >>
    gvs[]) >>
  qspecl_then [`dist`, `ps`] mp_tac do_swap_length >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by gvs[] >>
  qspecl_then [`final_dist`, `ps1`] mp_tac do_swap_peek_dist >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `(\(s1,ps1). _) (do_swap dist ps) = (_,ps')` mp_tac >>
  asm_rewrite_tac[] >>
  Cases_on `do_swap final_dist ps1` >> simp[] >> strip_tac >> gvs[]
QED

(* Once all swaps are shallow, placement preserves any distinct fixed depth. *)
Theorem reorder_place_phase_preserves[local]:
  !dfg op dist final_dist k ps.
    dist < LENGTH ps.ps_stack /\
    stack_peek dist ps.ps_stack = op /\
    dist <= 16 /\ final_dist <= 16 /\
    final_dist < LENGTH ps.ps_stack /\ k < LENGTH ps.ps_stack /\
    k <> 0 /\ k <> dist /\ k <> final_dist ==>
    let (_,ps') =
      if dist = final_dist then ([] : stack_op list,ps)
      else
        let at_target = stack_peek final_dist ps.ps_stack in
        if operand_equiv dfg op at_target then
          ([],ps with ps_stack :=
             stack_poke final_dist op
               (stack_poke dist at_target ps.ps_stack))
        else
          let (s1,ps1) = do_swap dist ps in
          let (s2,ps2) = do_swap final_dist ps1 in
          (s1 ++ s2,ps2)
    in stack_peek k ps'.ps_stack = stack_peek k ps.ps_stack
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `dist = final_dist` >> simp[] >>
  Cases_on `operand_equiv dfg op (stack_peek final_dist ps.ps_stack)` >> simp[]
  >- (`stack_peek k
         (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack) =
       stack_peek k ps.ps_stack` by
        (irule stack_poke_peek_other >> simp[]) >>
      `stack_peek k
         (stack_poke final_dist op
           (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)) =
       stack_peek k
         (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)` by
        (irule stack_poke_peek_other >> simp[stack_poke_def]) >>
      metis_tac[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  qspecl_then [`dist`, `k`, `ps`] mp_tac do_swap_peek_other >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`dist`, `ps`] mp_tac do_swap_length >>
  (impl_tac >- simp[]) >> strip_tac >>
  qspecl_then [`final_dist`, `k`, `ps1`] mp_tac do_swap_peek_other >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qpat_x_assum `(\(s1,ps1). _) (do_swap dist ps) = (_,ps')` mp_tac >>
  asm_rewrite_tac[] >>
  Cases_on `do_swap final_dist ps1` >> simp[] >> strip_tac >> gvs[]
QED

(* Placement preserves an already-fixed target depth.  A deep source swap is
   safe because every fixed depth is shallower than any unprotected deep
   source; the final swap is always within the <=16 target window. *)
Theorem reorder_place_phase_preserves_fixed[local]:
  !dfg op dist final_dist k target_len ps.
    dist < LENGTH ps.ps_stack /\
    stack_peek dist ps.ps_stack = op /\
    final_dist < k /\ k < target_len /\ target_len <= 16 /\
    ~(final_dist < dist /\ dist < target_len) /\
    final_dist < LENGTH ps.ps_stack /\ k < LENGTH ps.ps_stack ==>
    let (_,ps') =
      if dist = final_dist then ([] : stack_op list,ps)
      else
        let at_target = stack_peek final_dist ps.ps_stack in
        if operand_equiv dfg op at_target then
          ([],ps with ps_stack :=
             stack_poke final_dist op
               (stack_poke dist at_target ps.ps_stack))
        else
          let (s1,ps1) = do_swap dist ps in
          let (s2,ps2) = do_swap final_dist ps1 in
          (s1 ++ s2,ps2)
    in stack_peek k ps'.ps_stack = stack_peek k ps.ps_stack
Proof
  rpt strip_tac >> simp[LET_THM] >>
  Cases_on `dist = final_dist` >> simp[] >>
  `k <> 0 /\ k <> dist /\ k <> final_dist` by decide_tac >>
  Cases_on `operand_equiv dfg op (stack_peek final_dist ps.ps_stack)` >> simp[]
  >- (`stack_peek k
         (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack) =
       stack_peek k ps.ps_stack` by
        (irule stack_poke_peek_other >> simp[]) >>
      `stack_peek k
         (stack_poke final_dist op
           (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)) =
       stack_peek k
         (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)` by
        (irule stack_poke_peek_other >> simp[stack_poke_def]) >>
      metis_tac[]) >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  `stack_peek k ps1.ps_stack = stack_peek k ps.ps_stack` by
    (Cases_on `dist <= 16`
     >- (qspecl_then [`dist`, `k`, `ps`] mp_tac do_swap_peek_other >> simp[])
     >> qspecl_then [`dist`, `k`, `ps`] mp_tac do_swap_peek_shallower >>
        simp[] >> decide_tac) >>
  `LENGTH ps1.ps_stack = LENGTH ps.ps_stack` by
    (qspecl_then [`dist`, `ps`] mp_tac do_swap_length >> simp[]) >>
  qspecl_then [`final_dist`, `k`, `ps1`] mp_tac do_swap_peek_other >>
  (impl_tac >- gvs[]) >> strip_tac >>
  qpat_x_assum `(\(s1,ps1). _) (do_swap dist ps) = (_,ps')` mp_tac >>
  asm_rewrite_tac[] >>
  Cases_on `do_swap final_dist ps1` >> simp[] >> strip_tac >> gvs[]
QED
(* A successful reorder step places its requested operand at its indexed
   target depth in the formal planner stack. *)

(* State-only normalization of the already-available reorder path.  Consumers
   need not unfold the nested option and pair control flow of reorder_one. *)
Theorem reorder_one_existing_state[local]:
  !dfg target_ops idx op ps ops ps' d.
    idx < LENGTH target_ops /\ idx <> 0 /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\
    stack_get_unfixed_depth op (LENGTH target_ops - 1 - idx)
      (LENGTH target_ops) ps.ps_stack = SOME d /\
    reduce_depth_plan (LENGTH ps.ps_stack) target_ops op
      (LENGTH target_ops - 1 - idx) (LENGTH target_ops) ps = ([],ps) /\
    reorder_one dfg target_ops idx op ps = (ops,ps') ==>
    ps' = SND
      (if d = LENGTH target_ops - 1 - idx then ([] : stack_op list,ps)
       else
         let at_target = stack_peek (LENGTH target_ops - 1 - idx) ps.ps_stack in
         if operand_equiv dfg op at_target then
           ([],ps with ps_stack :=
             stack_poke (LENGTH target_ops - 1 - idx) op
               (stack_poke d at_target ps.ps_stack))
         else
           let (s1,ps1) = do_swap d ps in
           let (s2,ps2) = do_swap (LENGTH target_ops - 1 - idx) ps1 in
           (s1 ++ s2,ps2))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH target_ops - (idx + 1) = LENGTH target_ops - 1 - idx` by
    decide_tac >>
  `LENGTH target_ops - 1 - idx < LENGTH ps.ps_stack` by decide_tac >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[reorder_one_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >> BETA_TAC >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  Cases_on `d > 16` >> asm_rewrite_tac[] >>
  pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[optionTheory.option_case_def] >> BETA_TAC >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  asm_rewrite_tac[] >>
  Cases_on `d = LENGTH target_ops - 1 - idx` >> asm_rewrite_tac[] >>
  pure_rewrite_tac[listTheory.APPEND] >>
  disch_then (fn th =>
    mp_tac (AP_TERM ``SND : stack_op list # plan_state -> plan_state`` th)) >>
  pure_rewrite_tac[pairTheory.SND] >>
  disch_tac >> sym_tac >> first_assum ACCEPT_TAC
QED


Theorem reorder_one_preserves_fixed:
  !dfg target_ops idx op ps ops ps' i d.
    idx < LENGTH target_ops /\ i < idx /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\ LENGTH target_ops <= 16 /\
    stack_get_unfixed_depth op (LENGTH target_ops - 1 - idx)
      (LENGTH target_ops) ps.ps_stack = SOME d /\
    reorder_one dfg target_ops idx op ps = (ops,ps') ==>
    stack_peek (LENGTH target_ops - 1 - i) ps'.ps_stack =
    stack_peek (LENGTH target_ops - 1 - i) ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >>
  `idx <> 0` by decide_tac >>
  `LENGTH target_ops - 1 - idx < LENGTH target_ops - 1 - i /\
   LENGTH target_ops - 1 - i < LENGTH target_ops /\
   LENGTH target_ops - 1 - idx < LENGTH ps.ps_stack /\
   LENGTH target_ops - 1 - i < LENGTH ps.ps_stack` by decide_tac >>
  `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = op /\
   ~(LENGTH target_ops - 1 - idx < d /\ d < LENGTH target_ops)` by
    metis_tac[stack_get_unfixed_depth_props] >>
  `reduce_depth_plan (LENGTH ps.ps_stack) target_ops op
      (LENGTH target_ops - 1 - idx) (LENGTH target_ops) ps = ([],ps)` by
    (Cases_on `LENGTH ps.ps_stack` >> simp[reduce_depth_plan_def] >> decide_tac) >>
  `ps' = SND
      (if d = LENGTH target_ops - 1 - idx then ([] : stack_op list,ps)
       else
         let at_target = stack_peek (LENGTH target_ops - 1 - idx) ps.ps_stack in
         if operand_equiv dfg op at_target then
           ([],ps with ps_stack :=
             stack_poke (LENGTH target_ops - 1 - idx) op
               (stack_poke d at_target ps.ps_stack))
         else
           let (s1,ps1) = do_swap d ps in
           let (s2,ps2) = do_swap (LENGTH target_ops - 1 - idx) ps1 in
           (s1 ++ s2,ps2))` by
    metis_tac[reorder_one_existing_state] >>
  qspecl_then [`dfg`, `op`, `d`, `LENGTH target_ops - 1 - idx`,
    `LENGTH target_ops - 1 - i`, `LENGTH target_ops`, `ps`]
    mp_tac reorder_place_phase_preserves_fixed >>
  simp[LET_THM] >>
  pairarg_tac >> simp[]
QED

Theorem reorder_one_places:
  !dfg target_ops idx op ps ops ps'.
    idx < LENGTH target_ops /\
    MEM op target_ops /\
    LENGTH target_ops <= LENGTH ps.ps_stack /\
    LENGTH target_ops <= 16 /\
    ((?d. stack_get_unfixed_depth op (LENGTH target_ops - 1 - idx)
            (LENGTH target_ops) ps.ps_stack = SOME d) \/
     (stack_get_unfixed_depth op (LENGTH target_ops - 1 - idx)
        (LENGTH target_ops) ps.ps_stack = NONE /\
      IS_SOME (FLOOKUP ps.ps_spilled op))) /\
    reorder_one dfg target_ops idx op ps = (ops,ps') ==>
    stack_peek (LENGTH target_ops - 1 - idx) ps'.ps_stack = op
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH target_ops - 1 - idx = LENGTH target_ops - (idx + 1)` by
    decide_tac >>
  gvs[] >>
  qpat_x_assum `reorder_one _ _ _ _ _ = _` mp_tac >>
  simp[reorder_one_def, LET_THM]
  >- (rename1 `stack_get_unfixed_depth op _ _ ps.ps_stack = SOME d` >>
      `d < LENGTH ps.ps_stack /\ stack_peek d ps.ps_stack = op` by
        metis_tac[stack_get_unfixed_depth_props] >>
      Cases_on `d > 16` >> simp[]
      >- (pairarg_tac >> simp[] >>
          rename1 `reduce_depth_plan (LENGTH ps.ps_stack) target_ops op
            (LENGTH target_ops - (idx + 1)) (LENGTH target_ops) ps =
            (reduce_ops,ps2)` >>
          `?dist'. stack_get_unfixed_depth op
              (LENGTH target_ops - (idx + 1)) (LENGTH target_ops)
              ps2.ps_stack = SOME dist'` by (
            qspecl_then [`LENGTH ps.ps_stack`, `target_ops`, `op`,
              `LENGTH target_ops - (idx + 1)`, `LENGTH target_ops`, `ps`, `d`]
              mp_tac (REWRITE_RULE [LET_THM] reduce_depth_plan_dist_ge) >>
            simp[] >> metis_tac[]) >>
          rename1 `stack_get_unfixed_depth op _ _ ps2.ps_stack = SOME dist'` >>
          `LENGTH target_ops <= LENGTH ps2.ps_stack` by (
            qspecl_then [`LENGTH ps.ps_stack`, `target_ops`, `op`,
              `LENGTH target_ops - (idx + 1)`, `LENGTH target_ops`, `ps`,
              `reduce_ops`, `ps2`]
              mp_tac reduce_depth_plan_length_floor >> simp[] >> decide_tac) >>
          `dist' < LENGTH ps2.ps_stack /\ stack_peek dist' ps2.ps_stack = op` by
            metis_tac[stack_get_unfixed_depth_props] >>
          `LENGTH target_ops - (idx + 1) < LENGTH ps2.ps_stack` by decide_tac >>
          strip_tac >>
          qspecl_then [`dfg`, `op`, `dist'`,
            `LENGTH target_ops - (idx + 1)`, `ps2`]
            mp_tac reorder_place_phase_places >> simp[] >> strip_tac >>
          Cases_on `dist' = LENGTH target_ops - (idx + 1)` >> gvs[] >>
          Cases_on `operand_equiv dfg (stack_peek d ps.ps_stack)
            (stack_peek (LENGTH target_ops - (idx + 1)) ps2.ps_stack)` >> gvs[] >>
          Cases_on `do_swap dist' ps2` >> gvs[] >>
          rename1 `do_swap dist' ps2 = (swap1_ops,ps3)` >>
          Cases_on `do_swap (LENGTH target_ops - (idx + 1)) ps3` >> gvs[]) >>
      strip_tac >>
      qspecl_then [`dfg`, `op`, `d`,
        `LENGTH target_ops - (idx + 1)`, `ps`]
        mp_tac reorder_place_phase_places >>
      simp[] >>
      `LENGTH target_ops - (idx + 1) < LENGTH ps.ps_stack` by decide_tac >>
      simp[]) >>
  Cases_on `FLOOKUP ps.ps_spilled op`
  >- fs[] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  simp[do_restore_def, stack_push_def] >>
  qabbrev_tac
    `psr = ps with <|ps_stack := SNOC op ps.ps_stack;
                     ps_spilled := ps.ps_spilled \\ op;
                     ps_alloc := free_spill_slot off ps.ps_alloc|>` >>
  `stack_get_depth op psr.ps_stack = SOME 0` by
    simp[Abbr `psr`, stack_get_depth_def, REVERSE_SNOC, stack_find_def] >>
  `stack_get_unfixed_depth op (LENGTH target_ops - (idx + 1))
     (LENGTH target_ops) psr.ps_stack = SOME 0` by
    metis_tac[stack_get_unfixed_depth_zero] >>
  `LENGTH target_ops - (idx + 1) < LENGTH psr.ps_stack` by
    (simp[Abbr `psr`] >> decide_tac) >>
  `stack_peek 0 psr.ps_stack = op` by
    simp[Abbr `psr`, stack_peek_def, EL_LENGTH_SNOC] >>
  strip_tac >>
  `SNOC op ps.ps_stack = psr.ps_stack` by simp[Abbr `psr`] >>
  qpat_x_assum `(case stack_get_unfixed_depth _ _ _ (SNOC _ _) of
                    NONE => _ | SOME _ => _) = (ops,ps')` mp_tac >>
  simp[] >> strip_tac >>
  qspecl_then [`dfg`, `op`, `0`, `LENGTH target_ops - (idx + 1)`, `psr`]
    mp_tac reorder_place_phase_places >> simp[] >> strip_tac >>
  Cases_on `LENGTH target_ops <= idx + 1` >> gs[] >>
  Cases_on `operand_equiv dfg op
    (stack_peek (LENGTH target_ops - (idx + 1)) psr.ps_stack)` >>
  gs[] >>
  Cases_on `do_swap 0 psr` >> gs[] >>
  rename1 `do_swap 0 psr = (swap1_ops,ps1)` >>
  Cases_on `do_swap (LENGTH target_ops - (idx + 1)) ps1` >> gs[]
QED

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
                     [op] op 0 1 ps)) ==>
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
  simp[reorder_one_def, LET_THM, stack_get_unfixed_depth_empty_window] >>
  imp_res_tac stack_get_depth_bound >>
  (* reduce_depth_plan *)
  pairarg_tac >> simp[] >>
  rename1 `reduce_depth_plan _ _ _ _ _ _ = (reduce_ops, ps2)` >>
  (* Stack+spilled alignment: apply_prefix_ops reduce_ops ps = ps2 *)
  `(apply_prefix_ops initial_fmp lo reduce_ops ps).ps_stack = ps2.ps_stack /\
   (apply_prefix_ops initial_fmp lo reduce_ops ps).ps_spilled = ps2.ps_spilled` by (
    qspecl_then [`LENGTH ps.ps_stack`, `[op]`, `op`, `0`, `1`, `ps`, `lo`]
      mp_tac reduce_depth_plan_align >>
    simp[LET_THM]) >>
  (* reduce_ops are only SOSwap/SOSpill *)
  `EVERY (\op'. (?d. op' = SOSwap d) \/ (?off. op' = SOSpill off))
     reduce_ops` by (
    `reduce_ops = FST (reduce_depth_plan (LENGTH ps.ps_stack)
       [op] op 0 1 ps)` by simp[] >>
    metis_tac[reduce_depth_plan_only_swap_spill]) >>
  (* Case: stack_get_depth op ps2.ps_stack *)
  Cases_on `stack_get_depth op ps2.ps_stack`
  >- (
    (* NONE contradicts reduce_depth_plan_dist_ge *)
    simp[] >> strip_tac >> gvs[] >>
    qspecl_then [`LENGTH ps.ps_stack`, `[op]`, `op`, `0`, `1`, `ps`, `d0`]
      mp_tac (CONV_RULE (DEPTH_CONV pairLib.GEN_BETA_CONV)
                (REWRITE_RULE [LET_THM] reduce_depth_plan_dist_ge)) >>
    (impl_tac >- simp[stack_get_unfixed_depth_empty_window]) >>
    simp[stack_get_unfixed_depth_empty_window])
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
  imp_res_tac stack_get_depth_el >>
  (* do_swap_last *)
  `LAST (SND (do_swap dist' ps2)).ps_stack = op /\
   (SND (do_swap dist' ps2)).ps_stack <> []` by (
    irule do_swap_last >> simp[stack_peek_def]) >>
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


(* Checked post-repair trace: suffix-aware input emission creates a second x,
   and multiplicity-aware reorder preserves both requested occurrences. *)
Theorem probe_bump_duplicate_after_emit_repair_succeeds:
  let ps0 = (init_plan_state 0) with
              ps_stack := [Var "x"; Var "y"] in
  let (input_ops,ps1) = emit_input_plan BUMP [Var "x"; Var "x"] [] ps0 in
  let (reorder_ops,ps2) = reorder_plan dfg_empty [Var "x"; Var "x"] ps1 in
  let aps = apply_prefix_ops initial_fmp FEMPTY
              (input_ops ++ reorder_ops) ps0 in
  let vs0 = (init_venom_state "entry") with
              vs_vars := FEMPTY |+ ("x",1w) |+ ("y",2w) in
    LENGTH (FILTER (\op. op = Var "x") ps1.ps_stack) = 2 /\
    stack_peek 1 ps2.ps_stack = Var "x" /\
    stack_peek 0 ps2.ps_stack = Var "x" /\
    stack_peek 1 aps.ps_stack = Var "x" /\
    stack_peek 0 aps.ps_stack = Var "x" /\
    operand_val vs0 FEMPTY (stack_peek 1 ps2.ps_stack) = SOME 1w /\
    operand_val vs0 FEMPTY (stack_peek 0 ps2.ps_stack) = SOME 1w /\
    operand_val vs0 FEMPTY (stack_peek 1 aps.ps_stack) = SOME 1w /\
    operand_val vs0 FEMPTY (stack_peek 0 aps.ps_stack) = SOME 1w
Proof
  EVAL_TAC
QED

Theorem probe_dfg_empty_alias_sound:
  !vs lo op at.
    operand_equiv dfg_empty op at ==>
    operand_val vs lo op = operand_val vs lo at
Proof
  rpt strip_tac >>
  Cases_on `op` >> Cases_on `at` >>
  gvs[operand_equiv_def, normalize_operand_def, dfg_empty_def]
QED
