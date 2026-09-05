(*
 * Spill/restore offset bounds for generated stack plans.
 *
 * This theory tracks both live and reusable spill slots, so historical
 * operations can be bounded without exposing allocator internals to context
 * planning proofs.
 *)

Theory planSpillBounds
Ancestors
  allocMono stackPlanGen stackPlanOps stackPlanTypes stackModel asmIR
  contextCodegenRel finite_map list rich_list arithmetic pair
Libs
  BasicProvers pairLib

Definition alloc_slots_bounded_def:
  alloc_slots_bounded base (al : spill_alloc) <=>
    al.sa_spill_base = base /\
    base <= al.sa_next_offset /\
    EVERY (\off. base <= off /\ off + 32 <= al.sa_next_offset)
          al.sa_free_slots
End

Definition plan_slots_bounded_def:
  plan_slots_bounded base (ps : plan_state) <=>
    alloc_slots_bounded base ps.ps_alloc /\
    (!op off. FLOOKUP ps.ps_spilled op = SOME off ==>
       base <= off /\ off + 32 <= ps.ps_alloc.sa_next_offset)
End

Definition ops_spill_bounded_def:
  ops_spill_bounded base spill_end (ops : stack_op list) <=>
    !off. MEM (SOSpill off) ops \/ MEM (SORestore off) ops ==>
      base <= off /\ off + 32 <= spill_end
End

Theorem ops_spill_bounded_nil[simp]:
  !base spill_end. ops_spill_bounded base spill_end []
Proof
  simp[ops_spill_bounded_def]
QED

Theorem ops_spill_bounded_append:
  !base spill_end xs ys.
    ops_spill_bounded base spill_end (xs ++ ys) <=>
    ops_spill_bounded base spill_end xs /\
    ops_spill_bounded base spill_end ys
Proof
  simp[ops_spill_bounded_def] >> metis_tac[]
QED

Theorem ops_spill_bounded_weaken:
  !base e1 e2 ops.
    ops_spill_bounded base e1 ops /\ e1 <= e2 ==>
    ops_spill_bounded base e2 ops
Proof
  simp[ops_spill_bounded_def] >> metis_tac[LESS_EQ_TRANS]
QED

Theorem ops_spill_bounded_context_spill_byte:
  !base spill_end ops r cp off i.
    ops_spill_bounded base spill_end ops /\
    MEM r cp.cp_regions /\ r.sr_spill_base = base /\
    spill_end <= r.sr_spill_end /\
    (MEM (SOSpill off) ops \/ MEM (SORestore off) ops) /\
    off <= i /\ i < off + 32 ==>
    context_spill_byte cp i
Proof
  rpt strip_tac >>
  qpat_x_assum `ops_spill_bounded _ _ _` mp_tac >>
  rewrite_tac[ops_spill_bounded_def] >>
  disch_then (qspec_then `off` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  simp[context_spill_byte_def] >>
  qexists `r` >> simp[] >> decide_tac
QED

Theorem every_front_last[local]:
  !(P : 'a -> bool) l.
    l <> [] /\ EVERY P l ==>
    EVERY P (FRONT l) /\ P (LAST l)
Proof
  gen_tac >> Induct >> simp[] >> Cases_on `l` >> simp[]
QED

Theorem alloc_spill_slot_bounded:
  !base al off al'.
    alloc_slots_bounded base al /\
    alloc_spill_slot al = (off, al') ==>
    alloc_slots_bounded base al' /\
    base <= off /\ off + 32 <= al'.sa_next_offset
Proof
  rpt gen_tac >> strip_tac >>
  fs[alloc_slots_bounded_def, alloc_spill_slot_def] >>
  Cases_on `al.sa_free_slots` >> gvs[] >>
  rpt BasicProvers.VAR_EQ_TAC >>
  simp[alloc_slots_bounded_def] >>
  qspecl_then [`\off. al.sa_spill_base <= off /\
                     off + 32 <= al.sa_next_offset`, `h::t`]
    mp_tac every_front_last >> simp[]
QED


Theorem free_spill_slot_bounded:
  !base al off.
    alloc_slots_bounded base al /\
    base <= off /\ off + 32 <= al.sa_next_offset ==>
    alloc_slots_bounded base (free_spill_slot off al)
Proof
  simp[alloc_slots_bounded_def, free_spill_slot_def, EVERY_SNOC]
QED

Theorem init_plan_state_slots_bounded:
  !base ctr.
    plan_slots_bounded base
      ((init_plan_state base) with ps_label_counter := ctr)
Proof
  simp[plan_slots_bounded_def, alloc_slots_bounded_def,
       init_plan_state_def, init_spill_alloc_def]
QED

Theorem do_spill_tos_slots_bounded:
  !base ps ops ps'.
    plan_slots_bounded base ps /\
    do_spill_tos ps = (ops, ps') ==>
    plan_slots_bounded base ps' /\
    ops_spill_bounded base ps'.ps_alloc.sa_next_offset ops
Proof
  rpt gen_tac >> simp[do_spill_tos_def] >> pairarg_tac >> gvs[] >>
  rpt strip_tac >> gvs[plan_slots_bounded_def] >>
  drule_all alloc_spill_slot_bounded >> strip_tac >>
  imp_res_tac alloc_spill_slot_next_offset >>
  simp[ops_spill_bounded_def, FLOOKUP_UPDATE] >>
  rpt conj_tac >> rpt gen_tac >> every_case_tac >> gvs[] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem do_restore_slots_bounded:
  !base op ps ops ps'.
    plan_slots_bounded base ps /\
    do_restore op ps = (ops, ps') ==>
    plan_slots_bounded base ps' /\
    ops_spill_bounded base ps'.ps_alloc.sa_next_offset ops
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> gvs[] >> rpt strip_tac
  >- (rpt BasicProvers.VAR_EQ_TAC >>
      simp[ops_spill_bounded_def])
  >> gvs[plan_slots_bounded_def] >>
  qpat_assum `!op off. FLOOKUP _ op = SOME off ==> _`
    (qspecl_then [`op`, `x`] mp_tac) >> simp[] >> strip_tac >>
  drule_all free_spill_slot_bounded >>
  simp[ops_spill_bounded_def, DOMSUB_FLOOKUP_THM, free_spill_slot_def] >>
  metis_tac[]
QED


Theorem plan_slots_bounded_stack_update[simp]:
  !base ps stk.
    plan_slots_bounded base (ps with ps_stack := stk) <=>
    plan_slots_bounded base ps
Proof
  simp[plan_slots_bounded_def]
QED

Theorem do_spill_at_slots_bounded:
  !base dist ps ops ps'.
    plan_slots_bounded base ps /\
    do_spill_at dist ps = (ops, ps') ==>
    plan_slots_bounded base ps' /\
    ops_spill_bounded base ps'.ps_alloc.sa_next_offset ops
Proof
  rpt gen_tac >> simp[do_spill_at_def] >> IF_CASES_TAC >> gvs[]
  >- metis_tac[do_spill_tos_slots_bounded]
  >> (pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
      `plan_slots_bounded base' (ps with ps_stack := stack_swap dist ps.ps_stack)` by
        simp[] >>
      imp_res_tac do_spill_tos_slots_bounded >>
      conj_tac >- first_assum ACCEPT_TAC >>
      simp[ops_spill_bounded_def] >>
      qpat_assum `ops_spill_bounded base' _ spill_ops`
        (ACCEPT_TAC o REWRITE_RULE [ops_spill_bounded_def]))
QED

Theorem foldl_free_slots_bounded:
  !offs base al.
    alloc_slots_bounded base al /\
    EVERY (\off. base <= off /\ off + 32 <= al.sa_next_offset) offs ==>
    alloc_slots_bounded base
      (FOLDL (\al off. free_spill_slot off al) al offs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  simp[free_spill_slot_next_offset] >>
  metis_tac[free_spill_slot_bounded]
QED

Theorem foldl_alloc_slots_bounded:
  !items ops offs al base.
    alloc_slots_bounded base al /\
    ops_spill_bounded base al.sa_next_offset ops /\
    EVERY (\off. base <= off /\ off + 32 <= al.sa_next_offset) offs ==>
    let res = FOLDL (\(ops, offs, al) item.
          (ops ++ [SOSpill (FST (alloc_spill_slot al))],
           SNOC (FST (alloc_spill_slot al)) offs,
           SND (alloc_spill_slot al)))
        (ops, offs, al) items in
      alloc_slots_bounded base (SND (SND res)) /\
      ops_spill_bounded base (SND (SND res)).sa_next_offset (FST res) /\
      EVERY (\off. base <= off /\
                    off + 32 <= (SND (SND res)).sa_next_offset)
            (FST (SND res)) /\
      al.sa_next_offset <= (SND (SND res)).sa_next_offset
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `alloc_spill_slot al` >> simp[] >>
  drule_all alloc_spill_slot_bounded >> strip_tac >>
  `al.sa_next_offset <= r.sa_next_offset` by
    metis_tac[alloc_spill_slot_next_offset] >>
  qpat_x_assum `!ops offs al base. _`
    (qspecl_then [`ops ++ [SOSpill q]`, `SNOC q offs`, `r`, `base'`]
      mp_tac) >>
  impl_tac
  >- (`ops_spill_bounded base' r.sa_next_offset ops` by
        (qspecl_then [`base'`, `al.sa_next_offset`, `r.sa_next_offset`, `ops`]
           mp_tac ops_spill_bounded_weaken >> simp[]) >>
      `EVERY (\off. base' <= off /\ off + 32 <= r.sa_next_offset) offs` by
        (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> decide_tac) >>
      simp[ops_spill_bounded_append, ops_spill_bounded_def, EVERY_SNOC]) >>
  strip_tac >> gvs[] >> decide_tac
QED

Theorem ops_spill_bounded_map_spill:
  !base spill_end offsets.
    EVERY (\off. base <= off /\ off + 32 <= spill_end) offsets ==>
    ops_spill_bounded base spill_end (MAP SOSpill offsets)
Proof
  simp[ops_spill_bounded_def, EVERY_MEM, MEM_MAP] >> metis_tac[]
QED

Theorem ops_spill_bounded_map_restore:
  !base spill_end offsets idxs.
    EVERY (\off. base <= off /\ off + 32 <= spill_end) offsets /\
    EVERY (\i. i < LENGTH offsets) idxs ==>
    ops_spill_bounded base spill_end
      (MAP (\i. SORestore (EL i offsets)) idxs)
Proof
  simp[ops_spill_bounded_def, EVERY_MEM, MEM_MAP] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  `MEM (EL i offsets) offsets` by simp[EL_MEM] >> metis_tac[]
QED

Theorem foldl_alloc_offsets_length:
  !items ops offs al.
    LENGTH (FST (SND (FOLDL (\(ops, offs, al) item.
      (ops ++ [SOSpill (FST (alloc_spill_slot al))],
       SNOC (FST (alloc_spill_slot al)) offs,
       SND (alloc_spill_slot al)))
      (ops, offs, al) items))) = LENGTH offs + LENGTH items
Proof
  Induct >> simp[]
QED

Theorem stack_find_index_bound[local]:
  !p l d. stack_find p l = SOME d ==> d < LENGTH l
Proof
  Induct_on `l` >> simp[stack_find_def] >> rpt strip_tac >>
  Cases_on `p h` >> fs[] >>
  Cases_on `stack_find p l` >> fs[] >> res_tac >> simp[]
QED

Theorem stack_get_depth_lt_length[local]:
  !op stk d. stack_get_depth op stk = SOME d ==> d < LENGTH stk
Proof
  rpt strip_tac >> fs[stack_get_depth_def] >>
  imp_res_tac stack_find_index_bound >> fs[]
QED

Theorem do_swap_slots_bounded:
  !base dist ps ops ps'.
    plan_slots_bounded base ps /\
    dist < LENGTH ps.ps_stack /\
    do_swap dist ps = (ops, ps') ==>
    plan_slots_bounded base ps' /\
    ops_spill_bounded base ps'.ps_alloc.sa_next_offset ops
Proof
  rpt gen_tac >> simp[do_swap_def] >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> gvs[] >> simp[ops_spill_bounded_def])
  >> IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> gvs[] >>
      simp[plan_slots_bounded_def, ops_spill_bounded_def])
  >> CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >>
  qabbrev_tac `res = FOLDL
    (\(ops,offs,al) item.
       (ops ++ [SOSpill (FST (alloc_spill_slot al))],
        SNOC (FST (alloc_spill_slot al)) offs,
        SND (alloc_spill_slot al)))
    ([],[],ps.ps_alloc) (top_n (dist + 1) ps.ps_stack)` >>
  PairCases_on `res` >> gvs[] >>
  qspecl_then [`top_n (dist + 1) ps.ps_stack`, `[]`, `[]`,
               `ps.ps_alloc`, `base'`] mp_tac foldl_alloc_slots_bounded >>
  simp[] >>
  (impl_tac >- gvs[plan_slots_bounded_def]) >>
  strip_tac >>
  `LENGTH res1 = dist + 1` by
    (qspecl_then [`top_n (dist + 1) ps.ps_stack`, `[]`, `[]`,
                  `ps.ps_alloc`] mp_tac foldl_alloc_offsets_length >>
     simp[] >>
     simp[top_n_def, LENGTH_TAKE] >> decide_tac) >>
  qabbrev_tac `final_al =
    FOLDL (\al off. free_spill_slot off al) res2 res1` >>
  `final_al.sa_next_offset = res2.sa_next_offset` by
    simp[Abbr `final_al`, foldl_free_next_offset] >>
  `alloc_slots_bounded base' final_al` by
    (simp[Abbr `final_al`] >> irule foldl_free_slots_bounded >> simp[]) >>
  `plan_slots_bounded base' (ps with ps_alloc := final_al)` by
    (simp[plan_slots_bounded_def] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `plan_slots_bounded base' ps` mp_tac >>
     simp[plan_slots_bounded_def] >> strip_tac >>
     first_x_assum drule >> strip_tac >> decide_tac) >>
  `EVERY (\i. i < LENGTH res1)
     (REVERSE ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0]))` by
    (simp[EVERY_REVERSE, EVERY_APPEND, EVERY_GENLIST] >> decide_tac) >>
  `ops_spill_bounded base' res2.sa_next_offset
     (MAP (\i. SORestore (EL i res1))
       (REVERSE ([dist] ++ GENLIST (\i. i + 1) (dist - 1) ++ [0])))` by
    (irule ops_spill_bounded_map_restore >> simp[]) >>
  gvs[Abbr `final_al`, ops_spill_bounded_append] >>
  qpat_x_assum `ops_spill_bounded _ _
    (MAP _ (REVERSE (_ ++ [0])))` mp_tac >>
  simp[REVERSE_APPEND, MAP_APPEND, ops_spill_bounded_append,
       ops_spill_bounded_def] >> metis_tac[]
QED
Theorem do_swap_plan_slots_bounded:
  !base dist ps ops ps'.
    plan_slots_bounded base ps /\
    do_swap dist ps = (ops, ps') ==>
    plan_slots_bounded base ps'
Proof
  rpt gen_tac >> simp[do_swap_def] >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> gvs[]) >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> gvs[]) >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >> strip_tac >>
  qabbrev_tac `res = FOLDL
    (\(ops,offs,al) item.
       (ops ++ [SOSpill (FST (alloc_spill_slot al))],
        SNOC (FST (alloc_spill_slot al)) offs,
        SND (alloc_spill_slot al)))
    ([],[],ps.ps_alloc) (top_n (dist + 1) ps.ps_stack)` >>
  PairCases_on `res` >> gvs[] >>
  qspecl_then [`top_n (dist + 1) ps.ps_stack`, `[]`, `[]`,
               `ps.ps_alloc`, `base'`] mp_tac foldl_alloc_slots_bounded >>
  simp[] >> (impl_tac >- gvs[plan_slots_bounded_def]) >> strip_tac >>
  qabbrev_tac `final_al =
    FOLDL (\al off. free_spill_slot off al) res2 res1` >>
  `alloc_slots_bounded base' final_al` by
    (simp[Abbr `final_al`] >> irule foldl_free_slots_bounded >> simp[]) >>
  simp[plan_slots_bounded_def, Abbr `final_al`] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `plan_slots_bounded base' ps` mp_tac >>
  simp[plan_slots_bounded_def, foldl_free_next_offset] >> strip_tac >>
  first_x_assum drule >> strip_tac >> decide_tac
QED


Theorem do_dup_slots_bounded:
  !base dist ps ops ps'.
    plan_slots_bounded base ps /\
    dist < LENGTH ps.ps_stack /\
    do_dup dist ps = (ops, ps') ==>
    plan_slots_bounded base ps' /\
    ops_spill_bounded base ps'.ps_alloc.sa_next_offset ops
Proof
  rpt gen_tac >> simp[do_dup_def] >>
  IF_CASES_TAC >> gvs[]
  >- (rpt strip_tac >> gvs[] >>
      simp[plan_slots_bounded_def, ops_spill_bounded_def])
  >> CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >>
  qabbrev_tac `res = FOLDL
    (\(ops,offs,al) item.
       (ops ++ [SOSpill (FST (alloc_spill_slot al))],
        SNOC (FST (alloc_spill_slot al)) offs,
        SND (alloc_spill_slot al)))
    ([],[],ps.ps_alloc) (top_n (dist + 1) ps.ps_stack)` >>
  PairCases_on `res` >> gvs[] >>
  qspecl_then [`top_n (dist + 1) ps.ps_stack`, `[]`, `[]`,
               `ps.ps_alloc`, `base'`] mp_tac foldl_alloc_slots_bounded >>
  simp[] >>
  (impl_tac >- gvs[plan_slots_bounded_def]) >>
  strip_tac >>
  `LENGTH res1 = dist + 1` by
    (qspecl_then [`top_n (dist + 1) ps.ps_stack`, `[]`, `[]`,
                  `ps.ps_alloc`] mp_tac foldl_alloc_offsets_length >>
     simp[] >>
     simp[top_n_def, LENGTH_TAKE] >> decide_tac) >>
  qabbrev_tac `final_al =
    FOLDL (\al off. free_spill_slot off al) res2 res1` >>
  `final_al.sa_next_offset = res2.sa_next_offset` by
    simp[Abbr `final_al`, foldl_free_next_offset] >>
  `alloc_slots_bounded base' final_al` by
    (simp[Abbr `final_al`] >> irule foldl_free_slots_bounded >> simp[]) >>
  `plan_slots_bounded base' (ps with ps_alloc := final_al)` by
    (simp[plan_slots_bounded_def] >>
     rpt gen_tac >> strip_tac >>
     qpat_x_assum `plan_slots_bounded base' ps` mp_tac >>
     simp[plan_slots_bounded_def] >> strip_tac >>
     first_x_assum drule >> strip_tac >> decide_tac) >>
  `EVERY (\i. i < LENGTH res1)
     (REVERSE (GENLIST I (dist + 1) ++ [0]))` by
    (simp[EVERY_REVERSE, EVERY_APPEND, EVERY_GENLIST]) >>
  `ops_spill_bounded base' res2.sa_next_offset
     (MAP (\i. SORestore (EL i res1))
       (REVERSE (GENLIST I (dist + 1) ++ [0])))` by
    (irule ops_spill_bounded_map_restore >> simp[]) >>
  gvs[Abbr `final_al`, ops_spill_bounded_append] >>
  qpat_x_assum `ops_spill_bounded _ _
    (MAP _ (REVERSE (_ ++ [0])))` mp_tac >>
  simp[REVERSE_APPEND, MAP_APPEND, ops_spill_bounded_append,
       ops_spill_bounded_def] >> metis_tac[]
QED

Theorem reduce_depth_plan_slots_bounded:
  !fuel target_ops target_op f target_len base ps ops ps'.
    plan_slots_bounded base ps /\
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') ==>
    plan_slots_bounded base ps' /\
    ops_spill_bounded base ps'.ps_alloc.sa_next_offset ops
Proof
  Induct >> rpt gen_tac
  >- (simp[reduce_depth_plan_def] >> rpt strip_tac >>
      gvs[ops_spill_bounded_def])
  >> simp[reduce_depth_plan_def] >>
  every_case_tac >> gvs[] >> rpt strip_tac >> gnvs[]
  >- (Cases_on `do_spill_at x' ps` >>
      Cases_on `reduce_depth_plan fuel target_ops target_op f target_len r` >>
      gvs[] >>
      imp_res_tac do_spill_at_slots_bounded >>
      qpat_x_assum `!target_ops target_op f target_len base ps ops ps'. _`
        (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`,
          `base'`, `r`, `q'`, `ps'`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      imp_res_tac reduce_depth_plan_next_offset >>
      gvs[ops_spill_bounded_append] >>
      metis_tac[ops_spill_bounded_weaken])
  >> (Cases_on `do_spill_at x' ps` >>
      Cases_on `reduce_depth_plan fuel target_ops target_op f target_len r` >>
      gvs[] >>
      imp_res_tac do_spill_at_slots_bounded >>
      qpat_x_assum `!target_ops target_op f target_len base ps ops ps'. _`
        (qspecl_then [`target_ops`, `target_op`, `f`, `target_len`,
          `base'`, `r`, `q'`, `ps'`] mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      imp_res_tac reduce_depth_plan_next_offset >>
      gvs[ops_spill_bounded_append] >>
      metis_tac[ops_spill_bounded_weaken])
QED

Theorem foldl_plan_ops_bounded:
  !f items init_ops ps base.
    plan_slots_bounded base ps /\
    ops_spill_bounded base ps.ps_alloc.sa_next_offset init_ops /\
    (!item ps step_ops ps'.
       plan_slots_bounded base ps /\ f item ps = (step_ops, ps') ==>
       plan_slots_bounded base ps' /\
       ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset /\
       ops_spill_bounded base ps'.ps_alloc.sa_next_offset step_ops) ==>
    let res = FOLDL (\(acc,ps) item.
      let (step_ops,ps') = f item ps in (acc ++ step_ops,ps'))
      (init_ops,ps) items in
    plan_slots_bounded base (SND res) /\
    ps.ps_alloc.sa_next_offset <= (SND res).ps_alloc.sa_next_offset /\
    ops_spill_bounded base (SND res).ps_alloc.sa_next_offset (FST res)
Proof
  gen_tac >> Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  Cases_on `f h ps` >> simp[] >>
  qpat_assum `!item ps step_ops ps'. _`
    (qspecl_then [`h`, `ps`, `q`, `r`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_x_assum `!init_ops ps base. _`
    (qspecl_then [`init_ops ++ q`, `r`, `base'`] mp_tac) >>
  impl_tac
  >- (simp[ops_spill_bounded_append] >> conj_tac
      >- (fs[ops_spill_bounded_def] >> rpt strip_tac >>
          `base' <= off /\ off + 32 <= ps.ps_alloc.sa_next_offset` by
            (qpat_assum `!off. MEM (SOSpill off) init_ops \/ _ ==> _`
               (qspec_then `off` mp_tac) >> simp[]) >>
          decide_tac)
      >> first_assum ACCEPT_TAC) >>
  strip_tac >> gvs[] >> decide_tac
QED

Theorem spill_plan_in_region_iff_ops_spill_bounded:
  !base spill_end ops.
    spill_plan_in_region base spill_end ops <=>
    ops_spill_bounded base spill_end ops
Proof
  rpt gen_tac >>
  pure_rewrite_tac [spill_plan_in_region_def, EVERY_MEM,
                    ops_spill_bounded_def] >>
  eq_tac
  >- (strip_tac >> gen_tac >> disch_tac >>
      qpat_x_assum `MEM (SOSpill off) ops \/ MEM (SORestore off) ops`
        (DISJ_CASES_THEN assume_tac) >>
      first_x_assum drule >>
      simp[stack_op_in_spill_region_def]) >>
  rpt strip_tac >> Cases_on `e` >>
  gvs[stack_op_in_spill_region_def]
QED

Theorem spill_plan_in_region_region_access:
  !r. spill_plan_in_region r.sr_spill_base r.sr_spill_end r.sr_plan ==>
      !off. region_spill_access r off ==>
        r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end
Proof
  simp[spill_plan_in_region_iff_ops_spill_bounded,
       ops_spill_bounded_def, region_spill_access_def]
QED

Theorem generate_context_regions_access_bounded:
  !gen fns acc acc'.
    generate_context_regions gen fns acc = SOME acc' /\
    EVERY
      (\r. !off. region_spill_access r off ==>
           r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end)
      acc.cpa_regions ==>
    EVERY
      (\r. !off. region_spill_access r off ==>
           r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end)
      acc'.cpa_regions
Proof
  gen_tac >> Induct
  >- simp[generate_context_regions_def] >>
  rpt gen_tac >>
  simp[generate_context_regions_def] >>
  Cases_on `gen h acc.cpa_next_spill_base acc.cpa_label_counter` >>
  gvs[] >> PairCases_on `x` >>
  gvs[AllCaseEqs(), EVERY_SNOC] >>
  rpt strip_tac >>
  first_x_assum drule >>
  disch_then irule >>
  simp[EVERY_SNOC] >>
  fs[spill_plan_in_region_iff_ops_spill_bounded,
     ops_spill_bounded_def, region_spill_access_def] >>
  first_assum ACCEPT_TAC
QED

Theorem generate_context_plan_with_access_bounded:
  !gen ctx cp.
    generate_context_plan_with gen ctx = SOME cp ==>
    EVERY
      (\r. !off. region_spill_access r off ==>
           r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end)
      cp.cp_regions
Proof
  rpt gen_tac >>
  simp[generate_context_plan_with_def] >>
  Cases_on `max_live_eom ctx` >> gvs[] >>
  Cases_on `generate_context_regions gen ctx.ctx_functions
    <|cpa_regions := []; cpa_label_counter := 0;
      cpa_next_spill_base := x; cpa_peak_spill_end := 0|>` >>
  gvs[finish_context_plan_def] >>
  rpt strip_tac >>
  drule generate_context_regions_access_bounded >>
  gvs[]
QED

Theorem generate_context_plan_access_bounded:
  !ctx cp.
    generate_context_plan ctx = SOME cp ==>
    EVERY
      (\r. !off. region_spill_access r off ==>
           r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end)
      cp.cp_regions
Proof
  simp[generate_context_plan_def] >>
  metis_tac[generate_context_plan_with_access_bounded]
QED

Theorem generate_context_plan_fuel_access_bounded:
  !fuel ctx cp.
    generate_context_plan_fuel fuel ctx = SOME cp ==>
    EVERY
      (\r. !off. region_spill_access r off ==>
           r.sr_spill_base <= off /\ off + 32 <= r.sr_spill_end)
      cp.cp_regions
Proof
  simp[generate_context_plan_fuel_def] >>
  metis_tac[generate_context_plan_with_access_bounded]
QED



val _ = export_theory();
