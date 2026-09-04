(*
 * Alloc Monotonicity Toolkit
 *
 * Every plan_state-threading function in the codegen preserves
 * sa_spill_base and is monotone on sa_next_offset. This file proves
 * these properties bottom-up from alloc_spill_slot/free_spill_slot
 * through generate_block_plan.
 *
 * Key export: generate_block_plan_alloc_mono
 *)

Theory allocMono
Ancestors
  stackPlanGen stackPlanTypes stackPlanOps stackModel planExec
  asmIR list rich_list arithmetic pair
Libs
  BasicProvers pairLib

(* ========== Base: alloc_spill_slot and free_spill_slot ========== *)

Theorem alloc_spill_slot_spill_base:
  !a off a'.
    alloc_spill_slot a = (off, a') ==>
    a'.sa_spill_base = a.sa_spill_base
Proof
  rpt gen_tac >> simp[alloc_spill_slot_def] >>
  Cases_on `a.sa_free_slots` >> simp[] >> strip_tac >> gvs[]
QED

Theorem alloc_spill_slot_next_offset:
  !a off a'.
    alloc_spill_slot a = (off, a') ==>
    a.sa_next_offset <= a'.sa_next_offset
Proof
  rpt gen_tac >> simp[alloc_spill_slot_def] >>
  Cases_on `a.sa_free_slots` >> simp[] >> strip_tac >> gvs[]
QED

Theorem free_spill_slot_spill_base:
  !off a. (free_spill_slot off a).sa_spill_base = a.sa_spill_base
Proof
  simp[free_spill_slot_def]
QED

Theorem free_spill_slot_next_offset:
  !off a. (free_spill_slot off a).sa_next_offset = a.sa_next_offset
Proof
  simp[free_spill_slot_def]
QED

(* ========== FOLDL helpers for alloc_spill_slot and free_spill_slot ========== *)

(* State with FST/SND form to match what simp produces *)
Theorem foldl_alloc_spill_base:
  !items ops offs al.
    (SND (SND (FOLDL (\(ops, offs, al) item.
       (ops ++ [SOSpill (FST (alloc_spill_slot al))],
        SNOC (FST (alloc_spill_slot al)) offs,
        SND (alloc_spill_slot al)))
     (ops, offs, al) items))).sa_spill_base = al.sa_spill_base
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `alloc_spill_slot al` >>
  rename1 `alloc_spill_slot al = (off1, al1)` >>
  drule alloc_spill_slot_spill_base >> strip_tac >> simp[] >>
  first_x_assum (qspecl_then [`ops ++ [SOSpill off1]`,
    `SNOC off1 offs`, `al1`] mp_tac) >> simp[]
QED

Theorem foldl_alloc_next_offset:
  !items acc.
    (SND (SND acc)).sa_next_offset <=
    (SND (SND (FOLDL (\(ops, offs, al) item.
       (ops ++ [SOSpill (FST (alloc_spill_slot al))],
        SNOC (FST (alloc_spill_slot al)) offs,
        SND (alloc_spill_slot al)))
     acc items))).sa_next_offset
Proof
  Induct >> simp[] >> rpt gen_tac >>
  Cases_on `acc` >> Cases_on `r` >>
  rename1 `(ops0, offs0, al0)` >> simp[] >>
  Cases_on `alloc_spill_slot al0` >>
  rename1 `alloc_spill_slot al0 = (off1, al1)` >>
  simp[] >>
  `al0.sa_next_offset <= al1.sa_next_offset`
    by metis_tac[alloc_spill_slot_next_offset] >>
  first_x_assum (qspec_then
    `(ops0 ++ [SOSpill off1], SNOC off1 offs0, al1)` mp_tac) >>
  simp[] >> decide_tac
QED

Theorem foldl_free_spill_base:
  !offs al.
    (FOLDL (\al off. free_spill_slot off al) al offs).sa_spill_base =
    al.sa_spill_base
Proof
  Induct >> simp[free_spill_slot_spill_base]
QED

Theorem foldl_free_next_offset:
  !offs al.
    (FOLDL (\al off. free_spill_slot off al) al offs).sa_next_offset =
    al.sa_next_offset
Proof
  Induct >> simp[free_spill_slot_next_offset]
QED

(* ========== Composition: sequential plan_state threading ========== *)

(* We prove properties directly for each function rather than defining
   a predicate, since each function has different signature. *)

(* ========== do_spill_tos ========== *)

Theorem do_spill_tos_spill_base:
  !ps ops ps'.
    do_spill_tos ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[do_spill_tos_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[alloc_spill_slot_spill_base]
QED

Theorem do_spill_tos_next_offset:
  !ps ops ps'.
    do_spill_tos ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[do_spill_tos_def] >>
  pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[alloc_spill_slot_next_offset]
QED

(* ========== do_spill_at ========== *)

Theorem do_spill_at_spill_base:
  !dist ps ops ps'.
    do_spill_at dist ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[do_spill_at_def] >>
  IF_CASES_TAC >> gvs[]
  >- metis_tac[do_spill_tos_spill_base]
  >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  drule do_spill_tos_spill_base >> simp[]
QED

Theorem do_spill_at_next_offset:
  !dist ps ops ps'.
    do_spill_at dist ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[do_spill_at_def] >>
  IF_CASES_TAC >> gvs[]
  >- metis_tac[do_spill_tos_next_offset]
  >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  drule do_spill_tos_next_offset >> simp[]
QED

(* ========== do_restore ========== *)

Theorem do_restore_spill_base:
  !op ps ops ps'.
    do_restore op ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[free_spill_slot_spill_base]
QED

Theorem do_restore_next_offset:
  !op ps ops ps'.
    do_restore op ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >> simp[] >>
  strip_tac >> gvs[free_spill_slot_next_offset]
QED

(* ========== do_swap ========== *)

(* do_swap/do_dup deep case: FOLDL alloc + FOLDL free pattern.
   We use Cases_on on the FOLDL triple result. *)
Theorem do_swap_spill_base:
  !dist ps ops ps'.
    do_swap dist ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[do_swap_def] >>
  IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> gvs[])
  >> (* deep case: introduce FOLDL result *)
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >> gvs[] >>
  simp[foldl_free_spill_base, foldl_alloc_spill_base]
QED

Theorem do_swap_next_offset:
  !dist ps ops ps'.
    do_swap dist ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[do_swap_def] >>
  IF_CASES_TAC >> gvs[] >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> gvs[])
  >> CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >> gvs[] >>
  simp[foldl_free_next_offset] >>
  qspecl_then [`top_n (dist + 1) ps.ps_stack`,
               `([],[],ps.ps_alloc)`]
    mp_tac foldl_alloc_next_offset >> simp[]
QED

(* ========== do_dup ========== *)

Theorem do_dup_spill_base:
  !dist ps ops ps'.
    do_dup dist ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[do_dup_def] >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> gvs[])
  >> CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >> gvs[] >>
  simp[foldl_free_spill_base, foldl_alloc_spill_base]
QED

Theorem do_dup_next_offset:
  !dist ps ops ps'.
    do_dup dist ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[do_dup_def] >>
  IF_CASES_TAC >> gvs[]
  >- (strip_tac >> gvs[])
  >> CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >> gvs[] >>
  simp[foldl_free_next_offset] >>
  qspecl_then [`top_n (dist + 1) ps.ps_stack`,
               `([],[],ps.ps_alloc)`]
    mp_tac foldl_alloc_next_offset >> simp[]
QED

(* ========== reduce_depth_plan ========== *)

Theorem reduce_depth_plan_spill_base:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  Induct >> rpt gen_tac
  >- (simp[reduce_depth_plan_def] >> strip_tac >> gvs[])
  >> simp[reduce_depth_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[]
  >- (pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      drule do_spill_at_spill_base >> strip_tac >>
      res_tac >> simp[])
QED

Theorem reduce_depth_plan_next_offset:
  !fuel target_ops target_op f target_len ps ops ps'.
    reduce_depth_plan fuel target_ops target_op f target_len ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  Induct >> rpt gen_tac
  >- (simp[reduce_depth_plan_def] >> strip_tac >> gvs[])
  >> simp[reduce_depth_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[]
  >- (pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
      drule do_spill_at_next_offset >> strip_tac >>
      res_tac >> decide_tac)
QED

(* ========== reorder_one ========== *)

(* reorder_one only modifies ps_alloc through do_restore, reduce_depth_plan,
   and do_swap. Use every_case_tac but first PURE_REWRITE to avoid unfolding
   sub-function definitions which cause goal explosion. *)

Theorem reorder_one_spill_base:
  !dfg target_ops target_idx op ps ops ps'.
    reorder_one dfg target_ops target_idx op ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >>
  rewrite_tac[reorder_one_def] >>
  BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum`_ = (_,ps')`mp_tac >>
  BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[AllCaseEqs()] >>
    drule do_restore_spill_base >> strip_tac >> gvs[]) >>
  BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum`_ = (_,ps')`mp_tac >>
  BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[AllCaseEqs()] >>
    drule reduce_depth_plan_spill_base >> strip_tac >> gvs[] >>
    drule do_restore_spill_base >> strip_tac >> gvs[]) >>
  BasicProvers.LET_ELIM_TAC >>
  gvs[AllCaseEqs()] >>
  TRY(drule do_restore_spill_base >> strip_tac >> gvs[]) >>
  TRY(drule reduce_depth_plan_spill_base >> strip_tac >> gvs[]) >>
  imp_res_tac do_swap_spill_base >> gvs[] >>
  gvs[Abbr`ps'`]
QED

Theorem reorder_one_next_offset:
  !dfg target_ops target_idx op ps ops ps'.
    reorder_one dfg target_ops target_idx op ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >>
  rewrite_tac[reorder_one_def] >>
  BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum`_ = (_,ps')`mp_tac >>
  BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[AllCaseEqs()] >>
    drule do_restore_next_offset >> strip_tac >> gvs[]) >>
  BasicProvers.LET_ELIM_TAC >>
  qpat_x_assum`_ = (_,ps')`mp_tac >>
  BasicProvers.TOP_CASE_TAC >- (
    strip_tac >> gvs[AllCaseEqs()] >>
    drule reduce_depth_plan_next_offset >> strip_tac >> gvs[] >>
    drule do_restore_next_offset >> strip_tac >> gvs[]) >>
  BasicProvers.LET_ELIM_TAC >>
  gvs[AllCaseEqs()] >>
  TRY(drule do_restore_next_offset >> strip_tac >> gvs[]) >>
  TRY(drule reduce_depth_plan_next_offset >> strip_tac >> gvs[]) >>
  imp_res_tac do_swap_next_offset >> gvs[] >>
  gvs[Abbr`ps'`]
QED

(* ========== FOLDL invariants for plan_state threading ========== *)

(* Single-accumulator FOLDL: sa_spill_base preserved when each step preserves it *)
Theorem foldl_spill_base_direct[local]:
  !f items ps.
    (!ps' item. (f ps' item).ps_alloc.sa_spill_base = ps'.ps_alloc.sa_spill_base) ==>
    (FOLDL f ps items).ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  gen_tac >> Induct >> simp[FOLDL]
QED

(* Single-accumulator FOLDL: sa_next_offset preserved (equality) *)
Theorem foldl_next_offset_eq_direct[local]:
  !f items ps.
    (!ps' item. (f ps' item).ps_alloc.sa_next_offset =
                ps'.ps_alloc.sa_next_offset) ==>
    (FOLDL f ps items).ps_alloc.sa_next_offset = ps.ps_alloc.sa_next_offset
Proof
  gen_tac >> Induct >> simp[FOLDL]
QED

(* Specialized: SND of pair-accumulator FOLDL preserves sa_spill_base *)
Theorem foldl_snd_spill_base_invariant[local]:
  !f items init.
    (!x item. (SND (f x item)).ps_alloc.sa_spill_base =
              (SND x).ps_alloc.sa_spill_base) ==>
    (SND (FOLDL f init items)).ps_alloc.sa_spill_base =
    (SND init).ps_alloc.sa_spill_base
Proof
  gen_tac >> Induct >> simp[FOLDL]
QED

(* Specialized: SND of pair-accumulator FOLDL is monotone on sa_next_offset *)
Theorem foldl_snd_next_offset_invariant[local]:
  !f items init.
    (!x item. (SND x).ps_alloc.sa_next_offset <=
              (SND (f x item)).ps_alloc.sa_next_offset) ==>
    (SND init).ps_alloc.sa_next_offset <=
    (SND (FOLDL f init items)).ps_alloc.sa_next_offset
Proof
  gen_tac >> Induct >> simp[FOLDL] >>
  rpt gen_tac >> strip_tac >>
  irule LESS_EQ_TRANS >>
  qexists_tac `(SND (f init h)).ps_alloc.sa_next_offset` >>
  simp[]
QED

(* ========== FOLDL projection for ops-accumulating step functions ==========
   Many codegen functions are FOLDL of the form:
     FOLDL (\(ops,ps) item. let (step_ops,ps') = f item ps in (ops++step_ops, ps'))
   The plan_state (ps) is threaded; the ops just accumulate.

   Key insight: foldl_snd_projection shows SND of this FOLDL equals a simpler
   single-accumulator FOLDL, eliminating all pair-lambda issues from proofs. *)

Theorem foldl_snd_projection[local]:
  !f items init_ops init_ps.
    SND (FOLDL (\(acc,ps) item.
      let (ops,ps') = f item ps in (acc ++ ops, ps'))
      (init_ops, init_ps) items)
    = FOLDL (\ps item. SND (f item ps)) init_ps items
Proof
  gen_tac >> Induct >> rpt gen_tac >> simp[FOLDL] >>
  Cases_on `f h init_ps` >>
  simp[LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  first_x_assum (qspecl_then [`init_ops ++ q`, `r`] mp_tac) >>
  simp[LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[]
QED

Theorem foldl_simple_spill_base[local]:
  !f items init_ps.
    (!item ps. (SND (f item ps)).ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base) ==>
    (FOLDL (\ps item. SND (f item ps)) init_ps items).ps_alloc.sa_spill_base =
    init_ps.ps_alloc.sa_spill_base
Proof
  gen_tac >> Induct >> simp[FOLDL]
QED

Theorem foldl_simple_next_offset[local]:
  !f items init_ps.
    (!item ps. ps.ps_alloc.sa_next_offset <=
               (SND (f item ps)).ps_alloc.sa_next_offset) ==>
    init_ps.ps_alloc.sa_next_offset <=
    (FOLDL (\ps item. SND (f item ps)) init_ps items).ps_alloc.sa_next_offset
Proof
  gen_tac >> Induct >> simp[FOLDL] >>
  rpt strip_tac >>
  `init_ps.ps_alloc.sa_next_offset <=
   (SND (f h init_ps)).ps_alloc.sa_next_offset` by simp[] >>
  `(SND (f h init_ps)).ps_alloc.sa_next_offset <=
   (FOLDL (\ps item. SND (f item ps)) (SND (f h init_ps)) items)
    .ps_alloc.sa_next_offset` by metis_tac[] >>
  decide_tac
QED

(* ========== reorder_plan (FOLDL of reorder_one) ========== *)

(* Pair-item version of foldl_snd_projection:
   SND of pair-accum FOLDL with pair-items = simple FOLDL on SND *)
Theorem foldl_pair_item_snd_projection[local]:
  !g items init_ops init_ps.
    SND (FOLDL (\(acc,ps) (a,b).
      let (ops,ps') = g a b ps in (acc ++ ops, ps'))
      (init_ops, init_ps) items)
    = FOLDL (\ps (a,b). SND (g a b ps)) init_ps items
Proof
  gen_tac >> Induct >> rpt gen_tac >> simp[FOLDL] >>
  Cases_on `h` >> simp[FOLDL] >>
  Cases_on `g q r init_ps` >>
  simp[LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  first_x_assum (qspecl_then [`init_ops ++ q'`, `r'`] mp_tac) >>
  simp[LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[]
QED

(* Pair-item simple FOLDL preserves fn_eom *)
Theorem foldl_pair_simple_spill_base[local]:
  !g items init_ps.
    (!a b ps. (SND (g a b ps)).ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base) ==>
    (FOLDL (\ps (a,b). SND (g a b ps)) init_ps items).ps_alloc.sa_spill_base =
    init_ps.ps_alloc.sa_spill_base
Proof
  gen_tac >> Induct >> simp[FOLDL] >>
  Cases >> simp[FOLDL]
QED

(* Pair-item simple FOLDL: next_offset monotone *)
Theorem foldl_pair_simple_next_offset[local]:
  !g items init_ps.
    (!a b ps. ps.ps_alloc.sa_next_offset <=
              (SND (g a b ps)).ps_alloc.sa_next_offset) ==>
    init_ps.ps_alloc.sa_next_offset <=
    (FOLDL (\ps (a,b). SND (g a b ps)) init_ps items).ps_alloc.sa_next_offset
Proof
  gen_tac >> Induct >> simp[FOLDL] >>
  Cases >> simp[FOLDL] >> rpt strip_tac >>
  irule LESS_EQ_TRANS >>
  qexists_tac `(SND (g q r init_ps)).ps_alloc.sa_next_offset` >>
  simp[]
QED

Theorem reorder_plan_spill_base:
  !dfg target_ops ps ops ps'.
    reorder_plan dfg target_ops ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> PURE_REWRITE_TAC[reorder_plan_def] >> strip_tac >>
  `ps' = SND (ops, ps')` by simp[] >> pop_assum SUBST1_TAC >>
  qpat_x_assum `FOLDL _ _ _ = _` (SUBST1_TAC o GSYM) >>
  PURE_REWRITE_TAC[foldl_pair_item_snd_projection] >>
  match_mp_tac foldl_pair_simple_spill_base >> rpt gen_tac >>
  Cases_on `reorder_one dfg target_ops a b ps` >> simp[] >>
  metis_tac[reorder_one_spill_base]
QED

Theorem reorder_plan_next_offset:
  !dfg target_ops ps ops ps'.
    reorder_plan dfg target_ops ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> PURE_REWRITE_TAC[reorder_plan_def] >> strip_tac >>
  `ps' = SND (ops, ps')` by simp[] >> pop_assum SUBST1_TAC >>
  qpat_x_assum `FOLDL _ _ _ = _` (SUBST1_TAC o GSYM) >>
  PURE_REWRITE_TAC[foldl_pair_item_snd_projection] >>
  match_mp_tac foldl_pair_simple_next_offset >> rpt gen_tac >>
  Cases_on `reorder_one dfg target_ops a b ps` >> simp[] >>
  metis_tac[reorder_one_next_offset]
QED

(* ========== SND-form simp rules for fn_eom ========== *)
(* Convert conditional f args = (ops,ps') ==> ps'.field = ps.field
   to unconditional (SND (f args)).field = ps.field — usable as simp rules *)
fun mk_snd_spill_base th =
  let val th1 = SPEC_ALL th
      val (ant, con) = dest_imp (concl th1)
      val (f_app, pair_tm) = dest_eq ant
      val ps' = #2 (pairSyntax.dest_pair pair_tm)
      val snd_app = pairSyntax.mk_snd f_app
      val new_goal = gen_all (subst [ps' |-> snd_app] con)
  in
    prove(new_goal,
      rpt gen_tac >>
      Cases_on [ANTIQUOTE f_app] >> gvs[] >>
      imp_res_tac th)
  end;

val snd_spill_base_rules = map mk_snd_spill_base [
  do_restore_spill_base, do_dup_spill_base, do_swap_spill_base,
  do_spill_tos_spill_base, do_spill_at_spill_base,
  reduce_depth_plan_spill_base, reorder_one_spill_base];

(* Reuse mk_snd_spill_base for next_offset — same SND substitution pattern *)
val snd_next_offset_rules = map mk_snd_spill_base [
  do_restore_next_offset, do_dup_next_offset, do_swap_next_offset,
  do_spill_tos_next_offset, do_spill_at_next_offset,
  reduce_depth_plan_next_offset, reorder_one_next_offset];

(* ========== emit_one_input ========== *)

Theorem emit_one_input_spill_base:
  !opc next_liveness op ps ops ps'.
    emit_one_input opc next_liveness op ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  Cases_on `op` >> rpt gen_tac >>
  simp[emit_one_input_def, is_var_operand_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp snd_spill_base_rules >>
  every_case_tac >> gvs[] >>
  simp snd_spill_base_rules >>
  strip_tac >> gvs[] >>
  simp snd_spill_base_rules >>
  TRY (imp_res_tac do_restore_spill_base >> gvs[])
QED

Theorem emit_one_input_next_offset:
  !opc next_liveness op ps ops ps'.
    emit_one_input opc next_liveness op ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  Cases_on `op` >> rpt gen_tac >>
  simp[emit_one_input_def, is_var_operand_def, LET_THM] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  every_case_tac >> gvs[] >>
  strip_tac >> gvs[] >>
  TRY (imp_res_tac do_restore_next_offset >> imp_res_tac do_dup_next_offset >>
       decide_tac) >>
  TRY (imp_res_tac do_restore_next_offset >> decide_tac) >>
  TRY (imp_res_tac do_dup_next_offset >> decide_tac) >>
  (* SND-form goals: use unconditional SND-form rules + transitivity *)
  simp snd_next_offset_rules >>
  irule LESS_EQ_TRANS >>
  qexists_tac `(SND (do_restore (Var s) ps)).ps_alloc.sa_next_offset` >>
  simp snd_next_offset_rules
QED

(* ========== emit_input_plan (structural traversal of emit_one_input) ========== *)

Theorem emit_input_plan_spill_base:
  !opc operands next_liveness ps ops ps'.
    emit_input_plan opc operands next_liveness ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  gen_tac >> Induct
  >- simp[emit_input_plan_def] >>
  rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ next_liveness) h ps` >>
  Cases_on `emit_input_plan opc operands next_liveness r` >>
  gvs[emit_input_plan_def] >>
  metis_tac[emit_one_input_spill_base]
QED

Theorem emit_input_plan_next_offset:
  !opc operands next_liveness ps ops ps'.
    emit_input_plan opc operands next_liveness ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  gen_tac >> Induct
  >- simp[emit_input_plan_def] >>
  rpt gen_tac >>
  Cases_on `emit_one_input opc (operand_vars operands ++ next_liveness) h ps` >>
  Cases_on `emit_input_plan opc operands next_liveness r` >>
  gvs[emit_input_plan_def] >>
  imp_res_tac emit_one_input_next_offset >>
  first_x_assum drule >> rpt strip_tac >> gvs[] >> decide_tac
QED

(* ========== popmany_individual (FOLDL with do_swap) ========== *)
(* Per-step obligation for popmany FOLDL: fn_eom preserved, next_offset monotone.
   Uses foldl_snd_{fn_eom,next_offset}_invariant directly on the simp-expanded def,
   avoiding syntactic mismatch between let-form and pair-lambda form. *)

Theorem popmany_individual_spill_base:
  !to_pop ps ops ps'.
    popmany_individual to_pop ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[popmany_individual_def] >> strip_tac >>
  `ps' = SND (ops, ps')` by simp[] >> pop_assum SUBST1_TAC >>
  `ps = SND ([]:stack_op list, ps)` by simp[] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  qpat_x_assum `_ = _` (SUBST1_TAC o GSYM) >>
  match_mp_tac foldl_snd_spill_base_invariant >> rpt gen_tac >>
  Cases_on `x` >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  Cases_on `stack_get_depth item r.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `do_swap x r` >> simp[] >>
  imp_res_tac do_swap_spill_base
QED

Theorem popmany_individual_next_offset:
  !to_pop ps ops ps'.
    popmany_individual to_pop ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[popmany_individual_def] >> strip_tac >>
  `ps' = SND (ops, ps')` by simp[] >> pop_assum SUBST1_TAC >>
  `ps = SND ([]:stack_op list, ps)` by simp[] >>
  pop_assum (fn th => PURE_ONCE_REWRITE_TAC[th]) >>
  qpat_x_assum `_ = _` (SUBST1_TAC o GSYM) >>
  match_mp_tac foldl_snd_next_offset_invariant >> rpt gen_tac >>
  Cases_on `x` >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  Cases_on `stack_get_depth item r.ps_stack` >> simp[] >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `do_swap x r` >> simp[] >>
  imp_res_tac do_swap_next_offset >> simp[]
QED

(* ========== popmany_plan ========== *)

Theorem popmany_plan_spill_base:
  !to_pop ps ops ps'.
    popmany_plan to_pop ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  Cases >> simp[popmany_plan_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (IF_CASES_TAC >> simp[]
      >- (pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
          metis_tac[do_swap_spill_base])
      >> metis_tac[popmany_individual_spill_base])
  >> metis_tac[popmany_individual_spill_base]
QED

Theorem popmany_plan_next_offset:
  !to_pop ps ops ps'.
    popmany_plan to_pop ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  Cases >> simp[popmany_plan_def] >>
  rpt gen_tac >> IF_CASES_TAC >> simp[]
  >- (IF_CASES_TAC >> simp[]
      >- (pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
          metis_tac[do_swap_next_offset])
      >> metis_tac[popmany_individual_next_offset])
  >> metis_tac[popmany_individual_next_offset]
QED

(* ========== optimistic_swap_plan ========== *)

Theorem optimistic_swap_plan_spill_base:
  !dfg inst next_liveness next_is_term ps ops ps'.
    optimistic_swap_plan dfg inst next_liveness next_is_term ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[do_swap_spill_base]
QED

Theorem optimistic_swap_plan_next_offset:
  !dfg inst next_liveness next_is_term ps ops ps'.
    optimistic_swap_plan dfg inst next_liveness next_is_term ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[optimistic_swap_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[do_swap_next_offset]
QED

(* ========== release_dead_spills ========== *)

Theorem release_dead_spills_spill_base:
  !next_liveness ps.
    (release_dead_spills next_liveness ps).ps_alloc.sa_spill_base =
    ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[release_dead_spills_def] >>
  match_mp_tac foldl_spill_base_direct >> rpt gen_tac >>
  Cases_on `item` >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[free_spill_slot_spill_base]
QED

Theorem release_dead_spills_next_offset:
  !next_liveness ps.
    (release_dead_spills next_liveness ps).ps_alloc.sa_next_offset =
    ps.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[release_dead_spills_def] >>
  match_mp_tac foldl_next_offset_eq_direct >> rpt gen_tac >>
  Cases_on `item` >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  simp[free_spill_slot_next_offset]
QED

(* ========== fresh_label ========== *)

Theorem fresh_label_spill_base:
  !prefix ps lbl ps'.
    fresh_label prefix ps = (lbl, ps') ==>
    ps'.ps_alloc = ps.ps_alloc
Proof
  simp[fresh_label_def] >> rpt strip_tac >> gvs[]
QED

(* ========== generate_emit_ops ========== *)

(* generate_emit_ops preserves entire ps_alloc: all branches either
   return ps unchanged or go through fresh_label which only touches ps_next_label. *)
Theorem generate_emit_ops_alloc:
  !inst ltc ps ops ps'.
    generate_emit_ops inst ltc ps = (ops, ps') ==>
    ps'.ps_alloc = ps.ps_alloc
Proof
  rpt gen_tac >> simp[generate_emit_ops_def] >>
  Cases_on `venom_to_evm_name inst.inst_opcode` >> simp[] >>
  strip_tac >> gvs[] >>
  (* NONE branch: nested if-then-else chain *)
  Cases_on `inst.inst_opcode = JNZ` >> gvs[]
  >- (every_case_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = JMP` >> gvs[]
  >- (every_case_tac >> gvs[]) >>
  Cases_on `inst.inst_opcode = DJMP` >> gvs[] >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[]
  >- (Cases_on `HD inst.inst_operands` >> gvs[] >>
      pairarg_tac >> gvs[] >> drule fresh_label_spill_base >> simp[]) >>
  Cases_on `inst.inst_opcode = RET` >> gvs[] >>
  Cases_on `inst.inst_opcode = ASSERT` >> gvs[] >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE` >> gvs[]
  >- (pairarg_tac >> gvs[] >> drule fresh_label_spill_base >> simp[]) >>
  Cases_on `inst.inst_opcode = LOG` >> gvs[] >>
  Cases_on `inst.inst_opcode = ISTORE` >> gvs[] >>
  Cases_on `inst.inst_opcode = INITIAL_FMP` >> gvs[] >>
  Cases_on `inst.inst_opcode = BUMP` >> gvs[]
QED

Theorem generate_emit_ops_spill_base:
  !inst ltc ps ops ps'.
    generate_emit_ops inst ltc ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  metis_tac[generate_emit_ops_alloc]
QED

Theorem generate_emit_ops_next_offset:
  !inst ltc ps ops ps'.
    generate_emit_ops inst ltc ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> strip_tac >> drule generate_emit_ops_alloc >> simp[]
QED

(* ========== generate_phi_plan ========== *)

Theorem generate_phi_plan_spill_base:
  !inst next_liveness ps ops ps'.
    generate_phi_plan inst next_liveness ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[generate_phi_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  Cases_on `do_dup x ps` >> gvs[] >>
  metis_tac[do_dup_spill_base]
QED

Theorem generate_phi_plan_next_offset:
  !inst next_liveness ps ops ps'.
    generate_phi_plan inst next_liveness ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[generate_phi_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  Cases_on `do_dup x ps` >> gvs[] >>
  metis_tac[do_dup_next_offset]
QED

(* ========== generate_offset_plan ========== *)

Theorem generate_offset_plan_spill_base:
  !inst ps ops ps'.
    generate_offset_plan inst ps = (ops, ps') ==>
    ps'.ps_alloc = ps.ps_alloc
Proof
  rpt gen_tac >> simp[generate_offset_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[]
QED

(* ========== generate_regular_inst_plan ========== *)

(* Helper: the FOLDL that pushes outputs only modifies ps_stack, not ps_alloc *)
Theorem foldl_push_outputs_alloc[local]:
  !outs ps0.
    (FOLDL (\ps' out. ps' with ps_stack := stack_push (Var out) ps'.ps_stack)
       ps0 outs).ps_alloc = ps0.ps_alloc
Proof
  Induct >> simp[]
QED

Theorem generate_regular_inst_plan_spill_base:
  !liveness dfg cfg fn inst nl ih nit bbl ps ops ps'.
    generate_regular_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
      (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[generate_regular_inst_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst ltc` >>
  qpat_x_assum `Abbrev _` kall_tac >>
  drule emit_input_plan_spill_base >> strip_tac >>
  (* JMP reorder *)
  `ps2.ps_alloc.sa_spill_base = ps1.ps_alloc.sa_spill_base` by
    (qpat_x_assum `(if _ then _ else _) = (join_ops,ps2)` mp_tac >>
     simp[AllCaseEqs()] >> metis_tac[reorder_plan_spill_base]) >>
  `ps3 = ps2` by
    (qpat_x_assum `(if _ then _ else _) = (operands',ps3)` mp_tac >>
     rpt IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* operands reorder *)
  `ps4.ps_alloc.sa_spill_base = ps2.ps_alloc.sa_spill_base` by
    metis_tac[reorder_plan_spill_base] >>
  (* emit ops *)
  drule generate_emit_ops_spill_base >> strip_tac >>
  (* popmany *)
  `ps8.ps_alloc.sa_spill_base = ps7.ps_alloc.sa_spill_base` by
    (qpat_x_assum `(if _ then _ else _) = (pop_ops,ps8)` mp_tac >>
     IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[] >>
     metis_tac[popmany_plan_spill_base]) >>
  (* optimistic swap *)
  `ps9.ps_alloc.sa_spill_base = ps8.ps_alloc.sa_spill_base` by
    (qpat_x_assum `(if _ then _ else _) = (opt_ops,ps9)` mp_tac >>
     IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[] >>
     metis_tac[optimistic_swap_plan_spill_base]) >>
  rpt (qpat_x_assum `(if _ then _ else _) = _` kall_tac) >>
  rpt (qpat_x_assum `reorder_plan _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `generate_emit_ops _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_input_plan _ _ _ _ = _` kall_tac) >>
  IF_CASES_TAC >> strip_tac >> gvs[] >>
  fs[release_dead_spills_spill_base, foldl_push_outputs_alloc]
QED

Theorem generate_regular_inst_plan_next_offset:
  !liveness dfg cfg fn inst nl ih nit bbl ps ops ps'.
    generate_regular_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
      (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[generate_regular_inst_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst ltc` >>
  qpat_x_assum `Abbrev _` kall_tac >>
  drule emit_input_plan_next_offset >> strip_tac >>
  (* JMP reorder *)
  `ps1.ps_alloc.sa_next_offset <= ps2.ps_alloc.sa_next_offset` by
    (qpat_x_assum `(if _ then _ else _) = (join_ops,ps2)` mp_tac >>
     simp[AllCaseEqs()] >> strip_tac >> gvs[] >>
     metis_tac[reorder_plan_next_offset]) >>
  `ps3 = ps2` by
    (qpat_x_assum `(if _ then _ else _) = (operands',ps3)` mp_tac >>
     rpt IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[]) >>
  rpt BasicProvers.VAR_EQ_TAC >>
  (* operands reorder *)
  `ps2.ps_alloc.sa_next_offset <= ps4.ps_alloc.sa_next_offset` by
    metis_tac[reorder_plan_next_offset] >>
  (* emit ops *)
  drule generate_emit_ops_next_offset >> strip_tac >>
  (* popmany *)
  `ps7.ps_alloc.sa_next_offset <= ps8.ps_alloc.sa_next_offset` by
    (qpat_x_assum `(if _ then _ else _) = (pop_ops,ps8)` mp_tac >>
     IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[] >>
     metis_tac[popmany_plan_next_offset]) >>
  (* optimistic swap *)
  `ps8.ps_alloc.sa_next_offset <= ps9.ps_alloc.sa_next_offset` by
    (qpat_x_assum `(if _ then _ else _) = (opt_ops,ps9)` mp_tac >>
     IF_CASES_TAC >> gvs[] >> strip_tac >> gvs[] >>
     metis_tac[optimistic_swap_plan_next_offset]) >>
  rpt (qpat_x_assum `(if _ then _ else _) = _` kall_tac) >>
  rpt (qpat_x_assum `reorder_plan _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `generate_emit_ops _ _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_input_plan _ _ _ _ = _` kall_tac) >>
  IF_CASES_TAC >> strip_tac >> gvs[] >>
  fs[release_dead_spills_next_offset, foldl_push_outputs_alloc] >>
  decide_tac
QED

(* ========== generate_inst_plan ========== *)

Theorem generate_inst_plan_spill_base:
  !liveness dfg cfg fn inst nl ih nit bbl ps ops ps'.
    generate_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
      SOME (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[generate_inst_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[generate_phi_plan_spill_base,
            generate_offset_plan_spill_base,
            generate_regular_inst_plan_spill_base]
QED

Theorem generate_inst_plan_next_offset:
  !liveness dfg cfg fn inst nl ih nit bbl ps ops ps'.
    generate_inst_plan liveness dfg cfg fn inst nl ih nit bbl ps =
      SOME (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[generate_inst_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  TRY (metis_tac[generate_phi_plan_next_offset]) >>
  TRY (drule generate_offset_plan_spill_base >> simp[]) >>
  metis_tac[generate_regular_inst_plan_next_offset]
QED

(* ========== prepare_params_plan ========== *)

Theorem prepare_params_plan_spill_base:
  !liveness fn ps ops ps'.
    prepare_params_plan liveness fn ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[prepare_params_plan_def] >>
  IF_CASES_TAC >> gvs[] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >> gvs[] >>
  (* popmany preserves fn_eom *)
  qmatch_goalsub_abbrev_tac `SND (popmany_plan fl fps)` >>
  `(SND (popmany_plan fl fps)).ps_alloc.sa_spill_base =
   fps.ps_alloc.sa_spill_base` by
    (Cases_on `popmany_plan fl fps` >> simp[] >>
     metis_tac[popmany_plan_spill_base]) >>
  `fps.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base` by
    (simp[Abbr `fps`] >> match_mp_tac foldl_spill_base_direct >> simp[]) >>
  (* optimistic_swap_plan preserves fn_eom *)
  qmatch_goalsub_abbrev_tac `SND osp_res` >>
  `(SND osp_res).ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base` by
    (Cases_on `osp_res` >> simp[] >>
     qpat_x_assum `Abbrev (osp_res = _)` (assume_tac o
       REWRITE_RULE [markerTheory.Abbrev_def]) >> gvs[] >>
     metis_tac[optimistic_swap_plan_spill_base])
QED

Theorem prepare_params_plan_next_offset:
  !liveness fn ps ops ps'.
    prepare_params_plan liveness fn ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[prepare_params_plan_def] >>
  IF_CASES_TAC >> gvs[] >>
  CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
  strip_tac >> gvs[] >>
  qmatch_goalsub_abbrev_tac `SND (popmany_plan fl fps)` >>
  `fps.ps_alloc.sa_next_offset <= (SND (popmany_plan fl fps)).ps_alloc.sa_next_offset` by
    (Cases_on `popmany_plan fl fps` >> simp[] >>
     `fps.ps_alloc.sa_next_offset = ps.ps_alloc.sa_next_offset` by
       (simp[Abbr `fps`] >> match_mp_tac foldl_next_offset_eq_direct >> simp[]) >>
     metis_tac[popmany_plan_next_offset]) >>
  qmatch_goalsub_abbrev_tac `SND osp_res` >>
  `(SND (popmany_plan fl fps)).ps_alloc.sa_next_offset <=
   (SND osp_res).ps_alloc.sa_next_offset` by
    (Cases_on `osp_res` >> simp[] >>
     qpat_x_assum `Abbrev (osp_res = _)` (assume_tac o
       REWRITE_RULE [markerTheory.Abbrev_def]) >> gvs[] >>
     metis_tac[optimistic_swap_plan_next_offset]) >>
  `fps.ps_alloc.sa_next_offset = ps.ps_alloc.sa_next_offset` by
    (simp[Abbr `fps`] >> match_mp_tac foldl_next_offset_eq_direct >> simp[]) >>
  decide_tac
QED

(* ========== clean_stack_plan ========== *)

Theorem clean_stack_plan_spill_base:
  !liveness cfg fn bb ps ops ps'.
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  rpt gen_tac >> simp[clean_stack_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[popmany_plan_spill_base]
QED

Theorem clean_stack_plan_next_offset:
  !liveness cfg fn bb ps ops ps'.
    clean_stack_plan liveness cfg fn bb ps = (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >> simp[clean_stack_plan_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  metis_tac[popmany_plan_next_offset]
QED

(* ========== generate_block_plan (FOLDL of generate_inst_plan) ========== *)

(* Generic option-FOLDL: FOLDL f NONE stays NONE. *)
Theorem foldl_none_stays_none[local]:
  !(f : 'a option -> 'b -> 'a option) items.
    (!item. f NONE item = NONE) ==>
    FOLDL f NONE items = NONE
Proof
  gen_tac >> Induct >> simp[FOLDL]
QED

(* Generic option-FOLDL invariant: works for ANY step function f.
   If P holds for x0, is preserved by each step, and f NONE = NONE,
   then P holds for the final result. *)
Theorem option_foldl_generic_invariant[local]:
  !(f : 'a option -> 'b -> 'a option)
   (P : 'a -> bool) items x0 res.
    P x0 ==>
    (!acc item y. P acc ==> f (SOME acc) item = SOME y ==> P y) ==>
    (!item. f NONE item = NONE) ==>
    FOLDL f (SOME x0) items = SOME res ==>
    P res
Proof
  ntac 2 gen_tac >> Induct >> simp[FOLDL] >>
  rpt gen_tac >> ntac 3 strip_tac >>
  Cases_on `f (SOME x0) h`
  >- (imp_res_tac foldl_none_stays_none >> simp[]) >>
  rename1 `SOME v` >> strip_tac >>
  qpat_assum `!acc item y. _` (qspecl_then [`x0`, `h`, `v`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `!x0 res. _ ==> _ ==> _ ==> FOLDL _ _ _ = _ ==> _`
    (qspecl_then [`v`, `res`] mp_tac) >>
  metis_tac[]
QED

(* ML function: specialize option_foldl_generic_invariant for a given
   predicate on pair-accumulator (stack_op list # plan_state).
   Result: drule-ready theorem with FOLDL equation as first antecedent. *)
fun mk_block_foldl_inv pred_term =
  option_foldl_generic_invariant
  |> Q.ISPECL [`f : (stack_op list # plan_state) option ->
                    (num # instruction) ->
                    (stack_op list # plan_state) option`,
               pred_term]
  |> SIMP_RULE (srw_ss()) [pairTheory.UNCURRY]
  |> Q.SPECL [`items`, `(ops0, ps_init)`, `(ops_final, ps_final)`]
  |> SIMP_RULE (srw_ss()) []
  |> Q.GEN `ps_final` |> Q.GEN `ops_final`
  |> Q.GEN `items` |> Q.GEN `ps_init` |> Q.GEN `ops0`
  |> Q.GEN `f` |> Q.GEN `ps0`
  |> REWRITE_RULE [AND_IMP_INTRO]
  |> ONCE_REWRITE_RULE [CONJ_COMM]
  |> REWRITE_RULE [GSYM AND_IMP_INTRO];

val block_foldl_spill_base = mk_block_foldl_inv
  `\(ops1 : stack_op list, ps1 : plan_state).
     ps1.ps_alloc.sa_spill_base = ps0.ps_alloc.sa_spill_base`;

val block_foldl_next_offset = mk_block_foldl_inv
  `\(ops1 : stack_op list, ps1 : plan_state).
     ps0.ps_alloc.sa_next_offset <= ps1.ps_alloc.sa_next_offset`;

(* Shared tactic for generate_block_plan_spill_base / _next_offset:
   unfold, decompose pipeline, apply FOLDL invariant via drule. *)
fun gen_block_plan_tac foldl_thm inst_thm extra_tac =
  rpt gen_tac >> simp[generate_block_plan_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  TRY (imp_res_tac prepare_params_plan_spill_base) >>
  TRY (imp_res_tac prepare_params_plan_next_offset) >>
  TRY (imp_res_tac clean_stack_plan_spill_base) >>
  TRY (imp_res_tac clean_stack_plan_next_offset) >>
  gvs[] >>
  drule foldl_thm >>
  simp[] >> disch_then irule >> rpt conj_tac >>
  rpt gen_tac >> simp[UNCURRY] >> rpt strip_tac >>
  every_case_tac >> gvs[] >>
  imp_res_tac inst_thm >> gvs[] >> extra_tac;

Theorem generate_block_plan_spill_base:
  !liveness dfg cfg fn bb ps ops ps'.
    generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base
Proof
  gen_block_plan_tac block_foldl_spill_base generate_inst_plan_spill_base all_tac
QED

Theorem generate_block_plan_next_offset:
  !liveness dfg cfg fn bb ps ops ps'.
    generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') ==>
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  gen_block_plan_tac block_foldl_next_offset generate_inst_plan_next_offset
    (TRY decide_tac)
QED

(* Combined for convenience *)
Theorem generate_block_plan_alloc_mono:
  !liveness dfg cfg fn bb ps ops ps'.
    generate_block_plan liveness dfg cfg fn bb ps = SOME (ops, ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset
Proof
  metis_tac[generate_block_plan_spill_base, generate_block_plan_next_offset]
QED

(* ========== DFS-level alloc monotonicity (mutual induction) ========== *)

(* generate_fn_plan_aux and generate_succs_plan both preserve sa_spill_base
   and are monotone on sa_next_offset. Proved by the DFS mutual induction
   principle, using generate_block_plan_alloc_mono as the base case. *)

Theorem fn_plan_aux_alloc_mono:
  (!liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset) /\
  (!liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset)
Proof
  ho_match_mp_tac generate_fn_plan_aux_ind >> rpt conj_tac
  (* base: worklist = [] *)
  >- (rpt gen_tac >> rpt strip_tac >>
      gvs[Once generate_fn_plan_aux_def])
  (* step: worklist = lbl :: rest *)
  >- (
    rpt gen_tac >> strip_tac >>
    rpt gen_tac >> strip_tac >>
    qpat_x_assum `generate_fn_plan_aux _ _ _ _ (_ :: _) _ _ = _` mp_tac >>
    simp[Once generate_fn_plan_aux_def] >>
    IF_CASES_TAC >> gvs[] >>
    TRY (first_x_assum irule >> simp[] >> NO_TAC) >>
    Cases_on `lookup_block lbl fn.fn_blocks` >> gvs[] >>
    TRY (first_x_assum irule >> simp[] >> NO_TAC) >>
    rename1 `_ = SOME bb_h` >>
    every_case_tac >> gvs[] >>
    strip_tac >> gvs[] >>
    imp_res_tac generate_block_plan_alloc_mono >>
    gvs[] >> decide_tac
  )
  (* base: succs = [] *)
  >- (rpt gen_tac >> rpt strip_tac >>
      gvs[Once generate_fn_plan_aux_def])
  (* step: succs = succ :: rest_succs *)
  >- (
    rpt gen_tac >> strip_tac >>
    simp[Once generate_fn_plan_aux_def] >>
    every_case_tac >> gvs[] >>
    strip_tac >> gvs[] >> decide_tac
  )
QED


(* Public boundary for function-plan allocation from an assigned spill base. *)
Theorem generate_fn_plan_alloc_mono:
  !fn spill_base lbl_ctr ops ps_final.
    generate_fn_plan fn spill_base lbl_ctr = SOME (ops, ps_final) ==>
    ps_final.ps_alloc.sa_spill_base = spill_base /\
    spill_base <= ps_final.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >>
  Cases_on `fn_entry_label fn`
  >- (simp[generate_fn_plan_def, init_plan_state_def, init_spill_alloc_def] >>
      rpt strip_tac >> gvs[])
  >> simp[generate_fn_plan_def] >>
  every_case_tac >> gvs[] >>
  strip_tac >> gvs[] >>
  imp_res_tac (cj 1 fn_plan_aux_alloc_mono) >>
  gvs[init_plan_state_def, init_spill_alloc_def]
QED


Theorem fn_plan_aux_fuel_alloc_mono:
  (!fuel liveness dfg cfg fn worklist visited ps ops visited' ps'.
    generate_fn_plan_aux_fuel fuel liveness dfg cfg fn worklist visited ps =
      SOME (ops, visited', ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset) /\
  (!fuel liveness dfg cfg fn ss sp succs visited ps ops visited' ps'.
    generate_succs_plan_fuel fuel liveness dfg cfg fn ss sp succs visited ps =
      SOME (ops, visited', ps') ==>
    ps'.ps_alloc.sa_spill_base = ps.ps_alloc.sa_spill_base /\
    ps.ps_alloc.sa_next_offset <= ps'.ps_alloc.sa_next_offset)
Proof
  ho_match_mp_tac generate_fn_plan_aux_fuel_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[Once generate_fn_plan_aux_fuel_def] >>
  every_case_tac >> gvs[] >> rpt strip_tac >>
  imp_res_tac generate_block_plan_alloc_mono >> gvs[] >> decide_tac
QED

Theorem generate_fn_plan_fuel_alloc_mono:
  !fuel fn spill_base lbl_ctr ops ps_final.
    generate_fn_plan_fuel fuel fn spill_base lbl_ctr = SOME (ops, ps_final) ==>
    ps_final.ps_alloc.sa_spill_base = spill_base /\
    spill_base <= ps_final.ps_alloc.sa_next_offset
Proof
  rpt gen_tac >>
  Cases_on `fn_entry_label fn`
  >- (simp[generate_fn_plan_fuel_def, init_plan_state_def,
           init_spill_alloc_def] >> rpt strip_tac >> gvs[])
  >> simp[generate_fn_plan_fuel_def] >>
  every_case_tac >> gvs[] >> strip_tac >> gvs[] >>
  imp_res_tac (cj 1 fn_plan_aux_fuel_alloc_mono) >>
  gvs[init_plan_state_def, init_spill_alloc_def]
QED

val _ = export_theory();
