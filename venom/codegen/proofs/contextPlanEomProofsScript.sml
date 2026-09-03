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


Theorem foldl_max_seed[local]:
  !xs seed. seed <= FOLDL MAX seed xs
Proof
  Induct
  >- simp[]
  >> rpt gen_tac >> pure_rewrite_tac[listTheory.FOLDL] >>
     irule arithmeticTheory.LESS_EQ_TRANS >>
     qexists `MAX seed h` >>
     conj_tac
     >- simp[arithmeticTheory.MAX_DEF]
     >> first_x_assum irule
QED

Theorem foldl_max_mem[local]:
  !x xs seed. MEM x xs ==> x <= FOLDL MAX seed xs
Proof
  gen_tac >> Induct
  >- simp[]
  >> rpt gen_tac >> simp[] >> strip_tac
  >- (gvs[] >> irule arithmeticTheory.LESS_EQ_TRANS >>
      qexists `MAX seed h` >> conj_tac
      >- simp[arithmeticTheory.MAX_DEF]
      >> irule foldl_max_seed)
  >> first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem list_rel_mem_left[local]:
  !R xs ys x.
    LIST_REL R xs ys /\ MEM x xs ==>
    ?y. MEM y ys /\ R x y
Proof
  gen_tac >> Induct
  >- simp[]
  >> Cases_on `ys` >> simp[] >> metis_tac[]
QED

Theorem max_live_eom_bound:
  max_live_eom ctx = SOME max_eom /\
  MEM fn ctx.ctx_functions /\ fn.fn_eom = SOME eom ==>
  eom <= max_eom
Proof
  rpt strip_tac >>
  Cases_on `reserved_intervals_wf ctx.ctx_global_reserved` >>
  gvs[max_live_eom_def] >>
  Cases_on `global_reserved_end ctx.ctx_global_reserved 0` >>
  gvs[max_live_eom_def] >>
  Cases_on `collect_fn_eoms ctx.ctx_functions` >>
  gvs[max_live_eom_def] >>
  drule collect_fn_eoms_SOME >> strip_tac >>
  drule_all list_rel_mem_left >> strip_tac >>
  gvs[] >> metis_tac[foldl_max_mem]
QED

Theorem max_live_eom_global_bound:
  max_live_eom ctx = SOME max_eom /\
  MEM ((pos : num),(sz : num)) ctx.ctx_global_reserved ==>
  pos + sz <= max_eom
Proof
  rpt strip_tac >>
  Cases_on `reserved_intervals_wf ctx.ctx_global_reserved` >>
  gvs[max_live_eom_def] >>
  Cases_on `global_reserved_end ctx.ctx_global_reserved 0` >>
  gvs[max_live_eom_def] >>
  Cases_on `collect_fn_eoms ctx.ctx_functions` >>
  gvs[max_live_eom_def] >>
  drule global_reserved_end_success >> strip_tac >>
  metis_tac[foldl_max_seed, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem max_live_eom_malformed:
  ~reserved_intervals_wf ctx.ctx_global_reserved ==>
  max_live_eom ctx = NONE
Proof
  simp[max_live_eom_def]
QED
val _ = export_theory();
