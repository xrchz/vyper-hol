(*
 * Context planner: complete function-EOM collection and static bounds.
 *)

Theory contextPlanEomProofs
Ancestors
  stackPlanGen staticLayoutFoldProofs

Theorem collect_fn_eoms_NONE:
  collect_fn_eoms fns = NONE <=>
  ?fn. MEM fn fns /\ fn.fn_eom = NONE
Proof
  Induct_on `fns`
  >- simp[collect_fn_eoms_def]
  >> rpt gen_tac >>
     Cases_on `h.fn_eom` >>
     Cases_on `collect_fn_eoms fns` >>
     gvs[collect_fn_eoms_def] >>
     metis_tac[]
QED

Theorem collect_fn_eoms_SOME:
  collect_fn_eoms fns = SOME eoms ==>
  LIST_REL (\fn eom. fn.fn_eom = SOME eom) fns eoms
Proof
  qid_spec_tac `eoms` >> Induct_on `fns`
  >- simp[collect_fn_eoms_def]
  >> rpt gen_tac >>
     Cases_on `h.fn_eom` >>
     Cases_on `collect_fn_eoms fns` >>
     gvs[collect_fn_eoms_def] >>
     strip_tac >> gvs[]
QED

Theorem max_live_eom_missing:
  (?fn. MEM fn ctx.ctx_functions /\ fn.fn_eom = NONE) ==>
  max_live_eom ctx = NONE
Proof
  strip_tac >>
  `collect_fn_eoms ctx.ctx_functions = NONE` by
    metis_tac[collect_fn_eoms_NONE] >>
  Cases_on `reserved_intervals_wf ctx.ctx_global_reserved`
  >- (Cases_on `global_reserved_end ctx.ctx_global_reserved 0` >>
      simp[max_live_eom_def])
  >> simp[max_live_eom_def]
QED

val _ = export_theory();
