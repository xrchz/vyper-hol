(* Structural properties for fresh FMP analysis. *)

Theory fmpAnalysisProps
Ancestors
  fmpAnalysisDefs
  fmpWfProps
  fmpWfDefs
  callLayoutDefs
  venomWf
  venomInst
(* ------------------------------------------------------------------------- *)
(* Generic seed and synchronous-step boundaries. *)

Theorem fmp_info_join_fields[simp]:
  (fmp_info_join x y).fi_needs_fmp =
    (x.fi_needs_fmp \/ y.fi_needs_fmp) /\
  (fmp_info_join x y).fi_publishes_fmp =
    (x.fi_publishes_fmp \/ y.fi_publishes_fmp)
Proof
  Cases_on `x` >> Cases_on `y` >> simp[fmp_info_join_def]
QED

Theorem fmp_join_target_info_fields_mono:
  !targets acc out.
    fmp_join_target_info infos targets acc = SOME out ==>
    (acc.fi_needs_fmp ==> out.fi_needs_fmp) /\
    (acc.fi_publishes_fmp ==> out.fi_publishes_fmp)
Proof
  Induct >> simp[fmp_join_target_info_def]
  >> rpt gen_tac
  >> Cases_on `FLOOKUP infos h` >> simp[]
  >> strip_tac
  >> first_x_assum
       (qspecl_then [`fmp_info_join acc x`, `out`] mp_tac)
  >> simp[]
QED

Theorem fmp_seed_function_own_lookup:
  fmp_seed_function ctx fn acc = SOME acc' ==>
  ?info. FLOOKUP acc' fn.fn_name = SOME info
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> Cases_on `fn.fn_fmp_signature` >> gvs[]
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_seed_function_preserves_lookup:
  fmp_seed_function ctx fn acc = SOME acc' /\
  FLOOKUP acc name = SOME info ==>
  FLOOKUP acc' name = SOME info
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> Cases_on `fn.fn_fmp_signature` >> gvs[]
  >> Cases_on `fn.fn_name = name` >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_seed_functions_preserves_lookup:
  !fns acc out name info.
    fmp_seed_functions ctx fns acc = SOME out /\
    FLOOKUP acc name = SOME info ==>
    FLOOKUP out name = SOME info
Proof
  Induct >> rw[fmp_seed_functions_def]
  >> Cases_on `fmp_seed_function ctx h acc` >> gvs[]
  >> first_x_assum irule
  >> metis_tac[fmp_seed_function_preserves_lookup]
QED

Theorem fmp_seed_functions_coverage:
  !fns acc out fn.
    fmp_seed_functions ctx fns acc = SOME out /\ MEM fn fns ==>
    ?info. FLOOKUP out fn.fn_name = SOME info
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> metis_tac[fmp_seed_function_own_lookup,
               fmp_seed_functions_preserves_lookup]
QED

Theorem seed_fmp_context_coverage:
  seed_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions ==>
  ?info. FLOOKUP infos fn.fn_name = SOME info
Proof
  simp[seed_fmp_context_def]
  >> metis_tac[fmp_seed_functions_coverage]
QED
Theorem fmp_seed_function_targets:
  fmp_seed_function ctx fn acc = SOME acc' ==>
  ?targets. fmp_function_targets ctx fn = SOME targets
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
QED

Theorem fmp_seed_functions_targets:
  !fns acc out fn.
    fmp_seed_functions ctx fns acc = SOME out /\ MEM fn fns ==>
    ?targets. fmp_function_targets ctx fn = SOME targets
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> metis_tac[fmp_seed_function_targets]
QED

Theorem seed_fmp_context_targets:
  seed_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions ==>
  ?targets. fmp_function_targets ctx fn = SOME targets
Proof
  simp[seed_fmp_context_def]
  >> metis_tac[fmp_seed_functions_targets]
QED

Theorem fmp_seed_function_sealed_lookup:
  fmp_seed_function ctx fn acc = SOME acc' /\
  fn.fn_fmp_signature = SOME sig ==>
  fmp_signature_matches_fn ctx fn /\
  FLOOKUP acc' fn.fn_name = SOME (fmp_info_of_signature sig)
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_seed_functions_sealed_lookup:
  !fns acc out fn sig.
    fmp_seed_functions ctx fns acc = SOME out /\ MEM fn fns /\
    fn.fn_fmp_signature = SOME sig ==>
    fmp_signature_matches_fn ctx fn /\
    FLOOKUP out fn.fn_name = SOME (fmp_info_of_signature sig)
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> metis_tac[fmp_seed_function_sealed_lookup,
               fmp_seed_functions_preserves_lookup]
QED
Theorem seed_fmp_context_sealed_lookup:
  seed_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = SOME sig ==>
  fmp_signature_matches_fn ctx fn /\
  FLOOKUP infos fn.fn_name = SOME (fmp_info_of_signature sig)
Proof
  simp[seed_fmp_context_def]
  >> metis_tac[fmp_seed_functions_sealed_lookup]
QED


Theorem fmp_seed_functions_existing_name_not_mem:
  !fns acc out name info.
    fmp_seed_functions ctx fns acc = SOME out /\
    FLOOKUP acc name = SOME info ==>
    !fn. MEM fn fns ==> fn.fn_name <> name
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> strip_tac
  >> gen_tac >> strip_tac
  >> Cases_on `fn = h`
  >- (strip_tac >> gvs[fmp_seed_function_def])
  >> gvs[]
  >> `FLOOKUP x name = SOME info` by
       metis_tac[fmp_seed_function_preserves_lookup]
  >> first_x_assum (qspecl_then [`x`, `out`, `name`, `info`] mp_tac)
  >> simp[]
QED
Theorem fmp_seed_functions_distinct:
  !fns acc out.
    fmp_seed_functions ctx fns acc = SOME out ==>
    ALL_DISTINCT (MAP (\fn. fn.fn_name) fns)
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> strip_tac
  >> conj_tac
  >- (drule fmp_seed_function_own_lookup
      >> strip_tac
      >> qspecl_then [`fns`, `x`, `out`, `h.fn_name`, `info`] mp_tac
           fmp_seed_functions_existing_name_not_mem
      >> simp[listTheory.MEM_MAP]
      >> metis_tac[])
  >> first_x_assum (qspecl_then [`x`, `out`] mp_tac) >> simp[]
QED

Theorem seed_fmp_context_distinct:
  seed_fmp_context ctx = SOME infos ==> ctx_distinct_fn_names ctx
Proof
  simp[seed_fmp_context_def, ctx_distinct_fn_names_def, ctx_fn_names_def]
  >> metis_tac[fmp_seed_functions_distinct]
QED

Theorem fmp_step_functions_preserves_other_lookup:
  !fns fresh out name info.
    EVERY (\fn. fn.fn_name <> name) fns /\
    FLOOKUP fresh name = SOME info /\
    fmp_step_functions ctx old fns fresh = SOME out ==>
    FLOOKUP out name = SOME info
Proof
  Induct >> simp[fmp_step_functions_def]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_step_function ctx old h` >> gvs[]
  >> first_x_assum
       (qspecl_then [`fresh |+ (h.fn_name,x)`, `out`, `name`, `info`] mp_tac)
  >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_step_functions_lookup:
  !fns fresh out fn.
    ALL_DISTINCT (MAP (\f. f.fn_name) fns) /\ MEM fn fns /\
    fmp_step_functions ctx old fns fresh = SOME out ==>
    ?info.
      fmp_step_function ctx old fn = SOME info /\
      FLOOKUP out fn.fn_name = SOME info
Proof
  Induct >> simp[fmp_step_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_step_function ctx old h` >> simp[]
  >> strip_tac
  >- (qexists `x` >> simp[]
      >> qspecl_then
           [`fns`, `fresh |+ (h.fn_name,x)`, `out`, `h.fn_name`, `x`]
           mp_tac fmp_step_functions_preserves_other_lookup
      >> simp[finite_mapTheory.FLOOKUP_UPDATE, listTheory.EVERY_MEM]
      >> disch_then irule
      >> simp[listTheory.EVERY_MEM]
      >> metis_tac[listTheory.MEM_MAP])
  >> first_x_assum
       (qspecl_then [`fresh |+ (h.fn_name,x)`, `out`, `fn`] mp_tac)
  >> simp[]
QED

Theorem fmp_context_step_lookup:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fmp_context_step ctx old = SOME out ==>
  ?info.
    fmp_step_function ctx old fn = SOME info /\
    FLOOKUP out fn.fn_name = SOME info
Proof
  simp[fmp_context_step_def, ctx_distinct_fn_names_def, ctx_fn_names_def]
  >> metis_tac[fmp_step_functions_lookup]
QED

Theorem fmp_context_step_coverage:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fmp_context_step ctx old = SOME out ==>
  ?info. FLOOKUP out fn.fn_name = SOME info
Proof
  metis_tac[fmp_context_step_lookup]
QED

Theorem fmp_context_step_sealed_lookup:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = SOME sig /\
  fmp_context_step ctx old = SOME out ==>
  FLOOKUP out fn.fn_name = FLOOKUP old fn.fn_name
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_lookup
  >> strip_tac
  >> Cases_on `FLOOKUP old fn.fn_name`
  >> gvs[fmp_step_function_def]
QED

Theorem fmp_context_step_unsealed_lookup:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out ==>
  ?old_info targets info.
    FLOOKUP old fn.fn_name = SOME old_info /\
    fmp_function_targets ctx fn = SOME targets /\
    fmp_join_target_info old targets
      (fmp_info_join old_info (fmp_direct_info fn)) = SOME info /\
    FLOOKUP out fn.fn_name = SOME info
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_lookup
  >> simp[fmp_step_function_def]
  >> Cases_on `FLOOKUP old fn.fn_name` >> simp[]
  >> Cases_on `fmp_function_targets ctx fn` >> simp[]
  >> metis_tac[]
QED
Theorem fmp_context_step_unsealed_old_fields_mono:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out /\
  FLOOKUP old fn.fn_name = SOME old_info /\
  FLOOKUP out fn.fn_name = SOME info ==>
  (old_info.fi_needs_fmp ==> info.fi_needs_fmp) /\
  (old_info.fi_publishes_fmp ==> info.fi_publishes_fmp)
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_unsealed_lookup
  >> strip_tac
  >> gvs[]
  >> drule fmp_join_target_info_fields_mono
  >> simp[]
QED

Theorem fmp_context_step_unsealed_direct_fields:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out /\
  FLOOKUP out fn.fn_name = SOME info ==>
  ((fmp_direct_info fn).fi_needs_fmp ==> info.fi_needs_fmp) /\
  ((fmp_direct_info fn).fi_publishes_fmp ==> info.fi_publishes_fmp)
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_unsealed_lookup
  >> strip_tac
  >> gvs[]
  >> drule fmp_join_target_info_fields_mono
  >> simp[]
QED


(* ------------------------------------------------------------------------- *)
(* Bounded-round invariants and the public analysis contract. *)

Theorem fmp_option_step_none_funpow[simp]:
  !n. FUNPOW (fmp_option_step ctx) n NONE = NONE
Proof
  Induct >> simp[arithmeticTheory.FUNPOW, fmp_option_step_def]
QED

Theorem analyze_fmp_context_seeded:
  analyze_fmp_context ctx = SOME infos ==>
  ?seed. seed_fmp_context ctx = SOME seed
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
QED

Theorem analyze_fmp_context_distinct:
  analyze_fmp_context ctx = SOME infos ==>
  ctx_distinct_fn_names ctx
Proof
  metis_tac[analyze_fmp_context_seeded, seed_fmp_context_distinct]
QED

Theorem fmp_option_rounds_coverage:
  !n old out.
    ctx_distinct_fn_names ctx /\
    (!fn. MEM fn ctx.ctx_functions ==>
      ?info. FLOOKUP old fn.fn_name = SOME info) /\
    FUNPOW (fmp_option_step ctx) n (SOME old) = SOME out ==>
    !fn. MEM fn ctx.ctx_functions ==>
      ?info. FLOOKUP out fn.fn_name = SOME info
Proof
  Induct
  >- simp[arithmeticTheory.FUNPOW]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_context_step ctx old`
  >> gvs[arithmeticTheory.FUNPOW, fmp_option_step_def]
  >> first_x_assum (qspecl_then [`x`, `out`] mp_tac)
  >> metis_tac[fmp_context_step_coverage]
QED

Theorem fmp_option_rounds_sealed_lookup:
  !n old out.
    ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
    fn.fn_fmp_signature = SOME sig /\
    FUNPOW (fmp_option_step ctx) n (SOME old) = SOME out ==>
    FLOOKUP out fn.fn_name = FLOOKUP old fn.fn_name
Proof
  Induct
  >- simp[arithmeticTheory.FUNPOW]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_context_step ctx old`
  >> gvs[arithmeticTheory.FUNPOW, fmp_option_step_def]
  >> first_x_assum (qspecl_then [`x`, `out`] mp_tac)
  >> metis_tac[fmp_context_step_sealed_lookup]
QED

Theorem analyze_fmp_context_coverage:
  analyze_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions ==>
  ?info. FLOOKUP infos fn.fn_name = SOME info
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
  >> metis_tac[seed_fmp_context_distinct, seed_fmp_context_coverage,
               fmp_option_rounds_coverage]
QED

Theorem analyze_fmp_context_sealed_lookup:
  analyze_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = SOME sig ==>
  fmp_signature_matches_fn ctx fn /\
  FLOOKUP infos fn.fn_name = SOME (fmp_info_of_signature sig)
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
  >> metis_tac[seed_fmp_context_distinct, seed_fmp_context_sealed_lookup,
               fmp_option_rounds_sealed_lookup]
QED

Theorem fmp_option_rounds_unsealed_old_fields_mono:
  !n old out old_info info.
    ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
    fn.fn_fmp_signature = NONE /\
    FLOOKUP old fn.fn_name = SOME old_info /\
    FUNPOW (fmp_option_step ctx) n (SOME old) = SOME out /\
    FLOOKUP out fn.fn_name = SOME info ==>
    (old_info.fi_needs_fmp ==> info.fi_needs_fmp) /\
    (old_info.fi_publishes_fmp ==> info.fi_publishes_fmp)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[arithmeticTheory.FUNPOW])
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_context_step ctx old`
  >> gvs[arithmeticTheory.FUNPOW, fmp_option_step_def]
  >> metis_tac[fmp_context_step_coverage,
               fmp_context_step_unsealed_old_fields_mono]
QED

Theorem fmp_seed_function_unsealed_lookup:
  fmp_seed_function ctx fn acc = SOME acc' /\
  fn.fn_fmp_signature = NONE ==>
  FLOOKUP acc' fn.fn_name = SOME (fmp_direct_info fn)
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem fmp_seed_functions_unsealed_lookup:
  !fns acc out fn.
    fmp_seed_functions ctx fns acc = SOME out /\ MEM fn fns /\
    fn.fn_fmp_signature = NONE ==>
    FLOOKUP out fn.fn_name = SOME (fmp_direct_info fn)
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h acc` >> simp[]
  >> metis_tac[fmp_seed_function_unsealed_lookup,
               fmp_seed_functions_preserves_lookup]
QED

Theorem seed_fmp_context_unsealed_lookup:
  seed_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE ==>
  FLOOKUP infos fn.fn_name = SOME (fmp_direct_info fn)
Proof
  simp[seed_fmp_context_def]
  >> metis_tac[fmp_seed_functions_unsealed_lookup]
QED

Theorem analyze_fmp_context_unsealed_direct_fields:
  analyze_fmp_context ctx = SOME infos /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  FLOOKUP infos fn.fn_name = SOME info ==>
  ((fmp_direct_info fn).fi_needs_fmp ==> info.fi_needs_fmp) /\
  ((fmp_direct_info fn).fi_publishes_fmp ==> info.fi_publishes_fmp)
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
  >> metis_tac[seed_fmp_context_distinct,
               seed_fmp_context_unsealed_lookup,
               fmp_option_rounds_unsealed_old_fields_mono]
QED

Theorem fmp_join_target_info_needs_iff:
  !targets acc out.
    fmp_join_target_info infos targets acc = SOME out ==>
    (out.fi_needs_fmp <=>
       acc.fi_needs_fmp \/
       ?name info. MEM name targets /\
         FLOOKUP infos name = SOME info /\ info.fi_needs_fmp)
Proof
  Induct >> simp[fmp_join_target_info_def]
  >> rpt gen_tac
  >> Cases_on `FLOOKUP infos h` >> simp[]
  >> strip_tac
  >> first_x_assum
       (qspecl_then [`fmp_info_join acc x`, `out`] mp_tac)
  >> simp[]
  >> disch_then (fn th => rewrite_tac[th])
  >> eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem fmp_join_target_info_publishes_iff:
  !targets acc out.
    fmp_join_target_info infos targets acc = SOME out ==>
    (out.fi_publishes_fmp <=>
       acc.fi_publishes_fmp \/
       ?name info. MEM name targets /\
         FLOOKUP infos name = SOME info /\ info.fi_publishes_fmp)
Proof
  Induct >> simp[fmp_join_target_info_def]
  >> rpt gen_tac
  >> Cases_on `FLOOKUP infos h` >> simp[]
  >> strip_tac
  >> first_x_assum
       (qspecl_then [`fmp_info_join acc x`, `out`] mp_tac)
  >> simp[]
  >> disch_then (fn th => rewrite_tac[th])
  >> eq_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

Definition fmp_unsealed_calls_def:
  fmp_unsealed_calls ctx caller callee <=>
    MEM caller ctx.ctx_functions /\
    caller.fn_fmp_signature = NONE /\
    MEM callee ctx.ctx_functions /\
    ?targets. fmp_function_targets ctx caller = SOME targets /\
              MEM callee.fn_name targets
End

Definition fmp_needs_source_def:
  fmp_needs_source fn <=>
    case fn.fn_fmp_signature of
      SOME sig => (fmp_info_of_signature sig).fi_needs_fmp
    | NONE => (fmp_direct_info fn).fi_needs_fmp
End

Definition fmp_publishes_source_def:
  fmp_publishes_source fn <=>
    case fn.fn_fmp_signature of
      SOME sig => (fmp_info_of_signature sig).fi_publishes_fmp
    | NONE => (fmp_direct_info fn).fi_publishes_fmp
End

Theorem fmp_resolve_targets_lookup:
  !targets name.
    fmp_resolve_targets ctx targets /\ MEM name targets ==>
    ?fn. lookup_function name ctx.ctx_functions = SOME fn
Proof
  Induct >> simp[fmp_resolve_targets_def]
  >> rpt gen_tac >> strip_tac
  >> gvs[]
  >> Cases_on `lookup_function h ctx.ctx_functions` >> gvs[]
  >> metis_tac[]
QED

Theorem fmp_function_targets_lookup:
  fmp_function_targets ctx caller = SOME targets /\ MEM name targets ==>
  ?callee. lookup_function name ctx.ctx_functions = SOME callee
Proof
  rw[fmp_function_targets_def]
  >> Cases_on `fmp_collect_invokes (fn_insts caller)` >> gvs[]
  >> metis_tac[fmp_resolve_targets_lookup]
QED

Theorem seed_fmp_context_needs_source:
  seed_fmp_context ctx = SOME seed /\ MEM fn ctx.ctx_functions /\
  FLOOKUP seed fn.fn_name = SOME info ==>
  (info.fi_needs_fmp <=> fmp_needs_source fn)
Proof
  Cases_on `fn.fn_fmp_signature`
  >- (simp[fmp_needs_source_def] >> strip_tac
      >> drule_all seed_fmp_context_unsealed_lookup >> gvs[])
  >> simp[fmp_needs_source_def] >> strip_tac
  >> drule_all seed_fmp_context_sealed_lookup >> gvs[]
QED

Theorem seed_fmp_context_publishes_source:
  seed_fmp_context ctx = SOME seed /\ MEM fn ctx.ctx_functions /\
  FLOOKUP seed fn.fn_name = SOME info ==>
  (info.fi_publishes_fmp <=> fmp_publishes_source fn)
Proof
  Cases_on `fn.fn_fmp_signature`
  >- (simp[fmp_publishes_source_def] >> strip_tac
      >> drule_all seed_fmp_context_unsealed_lookup >> gvs[])
  >> simp[fmp_publishes_source_def] >> strip_tac
  >> drule_all seed_fmp_context_sealed_lookup >> gvs[]
QED

Theorem lookup_function_name:
  !name fns fn.
    lookup_function name fns = SOME fn ==> fn.fn_name = name
Proof
  Induct_on `fns` >> rw[lookup_function_def, listTheory.FIND_thm]
  >> gvs[lookup_function_def]
QED

Theorem fmp_target_name_callee:
  fmp_function_targets ctx caller = SOME targets /\ MEM name targets ==>
  ?callee. MEM callee ctx.ctx_functions /\ callee.fn_name = name
Proof
  strip_tac
  >> drule_all fmp_function_targets_lookup
  >> strip_tac
  >> qexists `callee`
  >> metis_tac[lookup_function_MEM, lookup_function_name]
QED

Theorem fmp_target_needs_exists:
  MEM caller ctx.ctx_functions /\ caller.fn_fmp_signature = NONE /\
  fmp_function_targets ctx caller = SOME targets ==>
  ((?name info. MEM name targets /\ FLOOKUP old name = SOME info /\
                 info.fi_needs_fmp) <=>
   ?callee info. fmp_unsealed_calls ctx caller callee /\
     FLOOKUP old callee.fn_name = SOME info /\ info.fi_needs_fmp)
Proof
  strip_tac >> eq_tac
  >- (strip_tac
      >> drule_all fmp_target_name_callee >> strip_tac
      >> qexistsl [`callee`, `info`]
      >> simp[fmp_unsealed_calls_def] >> metis_tac[])
  >> strip_tac >> gvs[fmp_unsealed_calls_def]
  >> qexistsl [`callee.fn_name`, `info`] >> metis_tac[]
QED

Theorem fmp_target_publishes_exists:
  MEM caller ctx.ctx_functions /\ caller.fn_fmp_signature = NONE /\
  fmp_function_targets ctx caller = SOME targets ==>
  ((?name info. MEM name targets /\ FLOOKUP old name = SOME info /\
                 info.fi_publishes_fmp) <=>
   ?callee info. fmp_unsealed_calls ctx caller callee /\
     FLOOKUP old callee.fn_name = SOME info /\ info.fi_publishes_fmp)
Proof
  strip_tac >> eq_tac
  >- (strip_tac
      >> drule_all fmp_target_name_callee >> strip_tac
      >> qexistsl [`callee`, `info`]
      >> simp[fmp_unsealed_calls_def] >> metis_tac[])
  >> strip_tac >> gvs[fmp_unsealed_calls_def]
  >> qexistsl [`callee.fn_name`, `info`] >> metis_tac[]
QED

Theorem fmp_context_step_unsealed_needs_iff:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out /\
  FLOOKUP old fn.fn_name = SOME old_info /\
  FLOOKUP out fn.fn_name = SOME info ==>
  (info.fi_needs_fmp <=>
    old_info.fi_needs_fmp \/ (fmp_direct_info fn).fi_needs_fmp \/
    ?callee callee_info. fmp_unsealed_calls ctx fn callee /\
      FLOOKUP old callee.fn_name = SOME callee_info /\
      callee_info.fi_needs_fmp)
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_unsealed_lookup
  >> strip_tac >> gvs[]
  >> drule fmp_join_target_info_needs_iff >> simp[]
  >> disch_then (fn th => once_rewrite_tac[th])
  >> drule_all fmp_target_needs_exists
  >> strip_tac
  >> first_x_assum (qspec_then `old` mp_tac)
  >> strip_tac >> metis_tac[]
QED

Theorem fmp_context_step_unsealed_publishes_iff:
  ctx_distinct_fn_names ctx /\ MEM fn ctx.ctx_functions /\
  fn.fn_fmp_signature = NONE /\
  fmp_context_step ctx old = SOME out /\
  FLOOKUP old fn.fn_name = SOME old_info /\
  FLOOKUP out fn.fn_name = SOME info ==>
  (info.fi_publishes_fmp <=>
    old_info.fi_publishes_fmp \/ (fmp_direct_info fn).fi_publishes_fmp \/
    ?callee callee_info. fmp_unsealed_calls ctx fn callee /\
      FLOOKUP old callee.fn_name = SOME callee_info /\
      callee_info.fi_publishes_fmp)
Proof
  rpt strip_tac
  >> drule_all fmp_context_step_unsealed_lookup
  >> strip_tac >> gvs[]
  >> drule fmp_join_target_info_publishes_iff >> simp[]
  >> disch_then (fn th => once_rewrite_tac[th])
  >> drule_all fmp_target_publishes_exists
  >> strip_tac
  >> first_x_assum (qspec_then `old` mp_tac)
  >> strip_tac >> metis_tac[]
QED

Definition fmp_reaches_in_def:
  (fmp_reaches_in ctx 0 caller source <=> caller = source) /\
  (fmp_reaches_in ctx (SUC n) caller source <=>
     caller = source \/
     ?callee. fmp_unsealed_calls ctx caller callee /\
              fmp_reaches_in ctx n callee source)
End

Theorem fmp_reaches_in_mono:
  !n caller source.
    fmp_reaches_in ctx n caller source ==>
    fmp_reaches_in ctx (SUC n) caller source
Proof
  Induct
  >- simp[fmp_reaches_in_def]
  >> rpt gen_tac
  >> pure_rewrite_tac[fmp_reaches_in_def]
  >> strip_tac
  >- simp[]
  >> disj2_tac
  >> qexists `callee`
  >> simp[]
  >> first_x_assum (qspecl_then [`callee`, `source`] mp_tac)
  >> simp[fmp_reaches_in_def]
QED

Theorem fmp_reaches_in_carrier:
  !n caller source.
    MEM caller ctx.ctx_functions /\ fmp_reaches_in ctx n caller source ==>
    MEM source ctx.ctx_functions
Proof
  Induct >> simp[fmp_reaches_in_def, fmp_unsealed_calls_def]
  >> metis_tac[]
QED


Theorem fmp_reaches_in_sealed:
  !n fn source sig.
    fn.fn_fmp_signature = SOME sig /\
    fmp_reaches_in ctx n fn source ==>
    fn = source
Proof
  Induct
  >- simp[fmp_reaches_in_def]
  >> rpt gen_tac >> strip_tac
  >> gvs[fmp_reaches_in_def, fmp_unsealed_calls_def]
QED

Theorem fmp_reaches_in_refl:
  !n fn. fmp_reaches_in ctx n fn fn
Proof
  Cases >> simp[fmp_reaches_in_def]
QED


Theorem fmp_callee_needs_round_exists:
  (!callee. MEM callee ctx.ctx_functions ==>
     ?ci. FLOOKUP old callee.fn_name = SOME ci) /\
  (!callee ci. MEM callee ctx.ctx_functions /\
     FLOOKUP old callee.fn_name = SOME ci ==>
     (ci.fi_needs_fmp <=>
       ?source. MEM source ctx.ctx_functions /\
         fmp_reaches_in ctx n callee source /\ fmp_needs_source source)) ==>
  ((?callee ci. fmp_unsealed_calls ctx caller callee /\
       FLOOKUP old callee.fn_name = SOME ci /\ ci.fi_needs_fmp) <=>
   ?callee source. fmp_unsealed_calls ctx caller callee /\
     MEM source ctx.ctx_functions /\
     fmp_reaches_in ctx n callee source /\ fmp_needs_source source)
Proof
  strip_tac
  >> qpat_x_assum `!callee. MEM callee ctx.ctx_functions ==> _`
       (mk_asm "coverage")
  >> qpat_x_assum
       `!callee ci. MEM callee ctx.ctx_functions /\
          FLOOKUP old callee.fn_name = SOME ci ==> _`
       (mk_asm "semantics")
  >> eq_tac
  >- (strip_tac
      >> `MEM callee ctx.ctx_functions` by
           metis_tac[fmp_unsealed_calls_def]
      >> asm "semantics" (qspecl_then [`callee`, `ci`] mp_tac)
      >> simp[] >> metis_tac[])
  >> strip_tac
  >> `MEM callee ctx.ctx_functions` by
       metis_tac[fmp_unsealed_calls_def]
  >> asm "coverage" (qspec_then `callee` mp_tac)
  >> simp[] >> strip_tac
  >> asm "semantics" (qspecl_then [`callee`, `ci`] mp_tac)
  >> simp[] >> strip_tac
  >> qexistsl [`callee`, `ci`]
  >> metis_tac[]
QED
Theorem fmp_option_rounds_needs_iff:
  !n seed out fn info.
    seed_fmp_context ctx = SOME seed /\
    FUNPOW (fmp_option_step ctx) n (SOME seed) = SOME out /\
    MEM fn ctx.ctx_functions /\
    FLOOKUP out fn.fn_name = SOME info ==>
    (info.fi_needs_fmp <=>
      ?source. MEM source ctx.ctx_functions /\
        fmp_reaches_in ctx n fn source /\ fmp_needs_source source)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac
      >> gvs[arithmeticTheory.FUNPOW, fmp_reaches_in_def]
      >> drule_all seed_fmp_context_needs_source
      >> metis_tac[])
  >> rpt gen_tac >> strip_tac
  >> `ctx_distinct_fn_names ctx` by
       metis_tac[seed_fmp_context_distinct]
  >> qpat_x_assum `FUNPOW _ (SUC n) _ = _` mp_tac
  >> rewrite_tac[arithmeticTheory.FUNPOW_SUC]
  >> Cases_on `FUNPOW (fmp_option_step ctx) n (SOME seed)`
  >> simp[fmp_option_step_def]
  >> strip_tac
  >> `!f. MEM f ctx.ctx_functions ==>
        ?i. FLOOKUP x f.fn_name = SOME i` by
       metis_tac[seed_fmp_context_coverage,
                 fmp_option_rounds_coverage]
  >> qpat_assum `!f. MEM f ctx.ctx_functions ==> _`
       (qspec_then `fn` mp_tac)
  >> (impl_tac >- simp[])
  >> strip_tac
  >> `!callee ci. MEM callee ctx.ctx_functions /\
        FLOOKUP x callee.fn_name = SOME ci ==>
        (ci.fi_needs_fmp <=>
          ?source. MEM source ctx.ctx_functions /\
            fmp_reaches_in ctx n callee source /\
            fmp_needs_source source)` by
       (rpt strip_tac
        >> first_assum
             (qspecl_then [`seed`, `x`, `callee`, `ci`] mp_tac)
        >> simp[])
  >> Cases_on `fn.fn_fmp_signature`
  >- (drule_all fmp_context_step_unsealed_needs_iff
      >> strip_tac
      >> `((?callee ci. fmp_unsealed_calls ctx fn callee /\
               FLOOKUP x callee.fn_name = SOME ci /\ ci.fi_needs_fmp) <=>
            ?callee source. fmp_unsealed_calls ctx fn callee /\
              MEM source ctx.ctx_functions /\
              fmp_reaches_in ctx n callee source /\
              fmp_needs_source source)` by
           (irule fmp_callee_needs_round_exists >> simp[])
      >> pop_assum $ mk_asm "callee_bridge"
      >> `(i.fi_needs_fmp <=>
            ?source. MEM source ctx.ctx_functions /\
              fmp_reaches_in ctx n fn source /\
              fmp_needs_source source)` by
           (first_assum
              (qspecl_then [`seed`, `x`, `fn`, `i`] mp_tac)
            >> simp[])
      >> eq_tac
      >- (strip_tac
          >> qpat_assum `info.fi_needs_fmp <=> _`
               (fn th => drule (iffLR th))
          >> strip_tac
          >- (qpat_assum `i.fi_needs_fmp <=> _`
                (fn th => drule (iffLR th))
              >> strip_tac
              >> qexists `source` >> simp[]
              >> metis_tac[fmp_reaches_in_mono])
          >- (qexists `fn`
              >> simp[fmp_reaches_in_refl, fmp_needs_source_def])
          >> `?callee source. fmp_unsealed_calls ctx fn callee /\
                MEM source ctx.ctx_functions /\
                fmp_reaches_in ctx n callee source /\
                fmp_needs_source source` by
               (asm "callee_bridge" (fn th => irule (iffLR th))
                >> qexistsl [`callee`, `callee_info`] >> simp[])
          >> rename1 `fmp_reaches_in ctx n path_callee source`
          >> qexists `source` >> simp[]
          >> pure_rewrite_tac[fmp_reaches_in_def]
          >> disj2_tac >> qexists `path_callee` >> simp[])
      >> strip_tac
      >> qpat_assum `info.fi_needs_fmp <=> _`
           (fn th => irule (iffRL th))
      >> qpat_x_assum `fmp_reaches_in ctx (SUC n) fn source` mp_tac
      >> simp[fmp_reaches_in_def]
      >> strip_tac
      >- (disj2_tac >> disj1_tac
          >> gvs[fmp_needs_source_def])
      >> disj2_tac >> disj2_tac
      >> asm "callee_bridge" (fn th => irule (iffRL th))
      >> qexistsl [`callee`, `source`] >> simp[])
  >> `FLOOKUP out fn.fn_name = FLOOKUP x fn.fn_name` by
       metis_tac[fmp_context_step_sealed_lookup]
  >> first_x_assum
       (qspecl_then [`seed`, `x`, `fn`, `i`] mp_tac)
  >> gvs[]
  >> metis_tac[fmp_reaches_in_sealed, fmp_reaches_in_refl,
               fmp_reaches_in_def, fmp_unsealed_calls_def]
QED

Theorem fmp_callee_publishes_round_exists:
  (!callee. MEM callee ctx.ctx_functions ==>
     ?ci. FLOOKUP old callee.fn_name = SOME ci) /\
  (!callee ci. MEM callee ctx.ctx_functions /\
     FLOOKUP old callee.fn_name = SOME ci ==>
     (ci.fi_publishes_fmp <=>
       ?source. MEM source ctx.ctx_functions /\
         fmp_reaches_in ctx n callee source /\ fmp_publishes_source source)) ==>
  ((?callee ci. fmp_unsealed_calls ctx caller callee /\
       FLOOKUP old callee.fn_name = SOME ci /\ ci.fi_publishes_fmp) <=>
   ?callee source. fmp_unsealed_calls ctx caller callee /\
     MEM source ctx.ctx_functions /\
     fmp_reaches_in ctx n callee source /\ fmp_publishes_source source)
Proof
  strip_tac
  >> qpat_x_assum `!callee. MEM callee ctx.ctx_functions ==> _`
       (mk_asm "coverage")
  >> qpat_x_assum
       `!callee ci. MEM callee ctx.ctx_functions /\
          FLOOKUP old callee.fn_name = SOME ci ==> _`
       (mk_asm "semantics")
  >> eq_tac
  >- (strip_tac
      >> `MEM callee ctx.ctx_functions` by
           metis_tac[fmp_unsealed_calls_def]
      >> asm "semantics" (qspecl_then [`callee`, `ci`] mp_tac)
      >> simp[] >> metis_tac[])
  >> strip_tac
  >> `MEM callee ctx.ctx_functions` by
       metis_tac[fmp_unsealed_calls_def]
  >> asm "coverage" (qspec_then `callee` mp_tac)
  >> simp[] >> strip_tac
  >> asm "semantics" (qspecl_then [`callee`, `ci`] mp_tac)
  >> simp[] >> strip_tac
  >> qexistsl [`callee`, `ci`]
  >> metis_tac[]
QED

Theorem fmp_option_rounds_publishes_iff:
  !n seed out fn info.
    seed_fmp_context ctx = SOME seed /\
    FUNPOW (fmp_option_step ctx) n (SOME seed) = SOME out /\
    MEM fn ctx.ctx_functions /\
    FLOOKUP out fn.fn_name = SOME info ==>
    (info.fi_publishes_fmp <=>
      ?source. MEM source ctx.ctx_functions /\
        fmp_reaches_in ctx n fn source /\ fmp_publishes_source source)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac
      >> gvs[arithmeticTheory.FUNPOW, fmp_reaches_in_def]
      >> drule_all seed_fmp_context_publishes_source
      >> metis_tac[])
  >> rpt gen_tac >> strip_tac
  >> `ctx_distinct_fn_names ctx` by
       metis_tac[seed_fmp_context_distinct]
  >> qpat_x_assum `FUNPOW _ (SUC n) _ = _` mp_tac
  >> rewrite_tac[arithmeticTheory.FUNPOW_SUC]
  >> Cases_on `FUNPOW (fmp_option_step ctx) n (SOME seed)`
  >> simp[fmp_option_step_def]
  >> strip_tac
  >> `!f. MEM f ctx.ctx_functions ==>
        ?i. FLOOKUP x f.fn_name = SOME i` by
       metis_tac[seed_fmp_context_coverage,
                 fmp_option_rounds_coverage]
  >> qpat_assum `!f. MEM f ctx.ctx_functions ==> _`
       (qspec_then `fn` mp_tac)
  >> (impl_tac >- simp[])
  >> strip_tac
  >> `!callee ci. MEM callee ctx.ctx_functions /\
        FLOOKUP x callee.fn_name = SOME ci ==>
        (ci.fi_publishes_fmp <=>
          ?source. MEM source ctx.ctx_functions /\
            fmp_reaches_in ctx n callee source /\
            fmp_publishes_source source)` by
       (rpt strip_tac
        >> first_assum
             (qspecl_then [`seed`, `x`, `callee`, `ci`] mp_tac)
        >> simp[])
  >> Cases_on `fn.fn_fmp_signature`
  >- (drule_all fmp_context_step_unsealed_publishes_iff
      >> strip_tac
      >> `((?callee ci. fmp_unsealed_calls ctx fn callee /\
               FLOOKUP x callee.fn_name = SOME ci /\ ci.fi_publishes_fmp) <=>
            ?callee source. fmp_unsealed_calls ctx fn callee /\
              MEM source ctx.ctx_functions /\
              fmp_reaches_in ctx n callee source /\
              fmp_publishes_source source)` by
           (irule fmp_callee_publishes_round_exists >> simp[])
      >> pop_assum $ mk_asm "callee_bridge"
      >> `(i.fi_publishes_fmp <=>
            ?source. MEM source ctx.ctx_functions /\
              fmp_reaches_in ctx n fn source /\
              fmp_publishes_source source)` by
           (first_assum
              (qspecl_then [`seed`, `x`, `fn`, `i`] mp_tac)
            >> simp[])
      >> eq_tac
      >- (strip_tac
          >> qpat_assum `info.fi_publishes_fmp <=> _`
               (fn th => drule (iffLR th))
          >> strip_tac
          >- (qpat_assum `i.fi_publishes_fmp <=> _`
                (fn th => drule (iffLR th))
              >> strip_tac
              >> qexists `source` >> simp[]
              >> metis_tac[fmp_reaches_in_mono])
          >- (qexists `fn`
              >> simp[fmp_reaches_in_refl, fmp_publishes_source_def])
          >> `?callee source. fmp_unsealed_calls ctx fn callee /\
                MEM source ctx.ctx_functions /\
                fmp_reaches_in ctx n callee source /\
                fmp_publishes_source source` by
               (asm "callee_bridge" (fn th => irule (iffLR th))
                >> qexistsl [`callee`, `callee_info`] >> simp[])
          >> rename1 `fmp_reaches_in ctx n path_callee source`
          >> qexists `source` >> simp[]
          >> pure_rewrite_tac[fmp_reaches_in_def]
          >> disj2_tac >> qexists `path_callee` >> simp[])
      >> strip_tac
      >> qpat_assum `info.fi_publishes_fmp <=> _`
           (fn th => irule (iffRL th))
      >> qpat_x_assum `fmp_reaches_in ctx (SUC n) fn source` mp_tac
      >> simp[fmp_reaches_in_def]
      >> strip_tac
      >- (disj2_tac >> disj1_tac
          >> gvs[fmp_publishes_source_def])
      >> disj2_tac >> disj2_tac
      >> asm "callee_bridge" (fn th => irule (iffRL th))
      >> qexistsl [`callee`, `source`] >> simp[])
  >> `FLOOKUP out fn.fn_name = FLOOKUP x fn.fn_name` by
       metis_tac[fmp_context_step_sealed_lookup]
  >> first_x_assum
       (qspecl_then [`seed`, `x`, `fn`, `i`] mp_tac)
  >> gvs[]
  >> metis_tac[fmp_reaches_in_sealed, fmp_reaches_in_refl,
               fmp_reaches_in_def, fmp_unsealed_calls_def]
QED

Theorem fmp_reaches_in_NRC:
  !n caller source.
    fmp_reaches_in ctx n caller source <=>
    ?k. k <= n /\ NRC (fmp_unsealed_calls ctx) k caller source
Proof
  Induct
  >- simp[fmp_reaches_in_def, arithmeticTheory.NRC]
  >> rpt gen_tac
  >> simp[fmp_reaches_in_def, arithmeticTheory.NRC]
  >> eq_tac >> strip_tac
  >- (qexists `0` >> simp[])
  >- (qexists `SUC k` >> simp[arithmeticTheory.NRC]
      >> qexists `callee` >> simp[])
  >> Cases_on `k` >> gvs[arithmeticTheory.NRC]
  >> metis_tac[]
QED

Theorem LRC_suffix_from_mem[local]:
  !ls x y e.
    list$LRC R ls x y /\ MEM e ls ==>
    ?qs. list$LRC R qs e y /\ LENGTH qs <= LENGTH ls /\
         !v. MEM v qs ==> MEM v ls
Proof
  Induct >> simp[listTheory.LRC_def]
  >> rpt gen_tac >> strip_tac
  >> gvs[]
  >- (qexists `e::ls` >> simp[listTheory.LRC_def]
      >> qexists `z` >> simp[])
  >> first_x_assum (qspecl_then [`z`, `y`, `e`] mp_tac)
  >> simp[] >> strip_tac
  >> qexists `qs` >> simp[]
  >> metis_tac[]
QED

Theorem LRC_simple[local]:
  !ls x y.
    list$LRC R ls x y ==>
    ?qs. list$LRC R qs x y /\ ALL_DISTINCT qs /\
         LENGTH qs <= LENGTH ls /\
         !v. MEM v qs ==> MEM v ls
Proof
  measureInduct_on `LENGTH ls`
  >> rpt gen_tac >> strip_tac
  >> Cases_on `ls`
  >- (qexists `[]` >> gvs[listTheory.LRC_def])
  >> gvs[listTheory.LRC_def]
  >> Cases_on `MEM h t`
  >- (drule_all LRC_suffix_from_mem
      >> strip_tac
      >> first_assum (qspec_then `qs` mp_tac)
      >> (impl_tac >- decide_tac)
      >> disch_then (qspecl_then [`h`, `y`] mp_tac)
      >> (impl_tac >- simp[])
      >> strip_tac
      >> qexists `qs'` >> simp[]
      >> metis_tac[])
  >> first_assum (qspec_then `t` mp_tac)
  >> (impl_tac >- simp[])
  >> disch_then (qspecl_then [`z`, `y`] mp_tac)
  >> (impl_tac >- simp[])
  >> strip_tac
  >> qexists `h::qs` >> simp[listTheory.LRC_def]
  >> conj_tac
  >- (qexists `z` >> simp[])
  >> conj_tac >- metis_tac[]
  >> metis_tac[]
QED

Theorem fmp_LRC_carrier[local]:
  !ls caller source.
    list$LRC (fmp_unsealed_calls ctx) ls caller source /\
    MEM caller ctx.ctx_functions ==>
    !v. MEM v ls ==> MEM v ctx.ctx_functions
Proof
  Induct >> simp[listTheory.LRC_def, fmp_unsealed_calls_def]
  >> metis_tac[]
QED

Theorem ALL_DISTINCT_MEM_LENGTH_LE[local]:
  ALL_DISTINCT xs /\ (!x. MEM x xs ==> MEM x ys) ==>
  LENGTH xs <= LENGTH ys
Proof
  strip_tac
  >> `set xs SUBSET set ys` by simp[pred_setTheory.SUBSET_DEF]
  >> `CARD (set xs) <= CARD (set ys)` by
       (irule pred_setTheory.CARD_SUBSET >> simp[])
  >> `CARD (set xs) = LENGTH xs` by
       metis_tac[listTheory.ALL_DISTINCT_CARD_LIST_TO_SET]
  >> `CARD (set ys) <= LENGTH ys` by
       simp[listTheory.CARD_LIST_TO_SET]
  >> decide_tac
QED

Theorem fmp_reaches_in_saturates:
  MEM caller ctx.ctx_functions /\
  fmp_reaches_in ctx (SUC (LENGTH ctx.ctx_functions)) caller source ==>
  fmp_reaches_in ctx (LENGTH ctx.ctx_functions) caller source
Proof
  strip_tac
  >> qpat_x_assum
       `fmp_reaches_in ctx (SUC (LENGTH ctx.ctx_functions)) caller source`
       mp_tac
  >> rewrite_tac[fmp_reaches_in_NRC]
  >> strip_tac
  >> qpat_x_assum `NRC _ k caller source` mp_tac
  >> rewrite_tac[listTheory.NRC_LRC]
  >> strip_tac
  >> drule LRC_simple >> strip_tac
  >> `!v. MEM v ls ==> MEM v ctx.ctx_functions` by
       metis_tac[fmp_LRC_carrier]
  >> `!v. MEM v qs ==> MEM v ctx.ctx_functions` by
       metis_tac[]
  >> `LENGTH qs <= LENGTH ctx.ctx_functions` by
       metis_tac[ALL_DISTINCT_MEM_LENGTH_LE]
  >> rewrite_tac[fmp_reaches_in_NRC]
  >> qexists `LENGTH qs` >> simp[]
  >> rewrite_tac[listTheory.NRC_LRC]
  >> qexists `qs` >> simp[]
QED

Theorem fmp_seed_function_FDOM[local]:
  fmp_seed_function ctx fn infos = SOME out ==>
  FDOM out = fn.fn_name INSERT FDOM infos
Proof
  rw[fmp_seed_function_def]
  >> Cases_on `fmp_function_targets ctx fn` >> gvs[]
  >> Cases_on `fn.fn_fmp_signature` >> gvs[finite_mapTheory.FDOM_FUPDATE]
QED

Theorem fmp_seed_functions_FDOM[local]:
  !fns infos out.
    fmp_seed_functions ctx fns infos = SOME out ==>
    FDOM out = set (MAP (\fn. fn.fn_name) fns) UNION FDOM infos
Proof
  Induct >> simp[fmp_seed_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_seed_function ctx h infos` >> simp[]
  >> strip_tac
  >> first_x_assum (qspecl_then [`x`, `out`] mp_tac)
  >> simp[] >> strip_tac
  >> drule fmp_seed_function_FDOM
  >> simp[pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem seed_fmp_context_FDOM[local]:
  seed_fmp_context ctx = SOME infos ==>
  FDOM infos = set (MAP (\fn. fn.fn_name) ctx.ctx_functions)
Proof
  simp[seed_fmp_context_def]
  >> strip_tac
  >> drule fmp_seed_functions_FDOM
  >> simp[]
QED

Theorem fmp_step_functions_FDOM[local]:
  !fns fresh out.
    fmp_step_functions ctx old fns fresh = SOME out ==>
    FDOM out = set (MAP (\fn. fn.fn_name) fns) UNION FDOM fresh
Proof
  Induct >> simp[fmp_step_functions_def]
  >> rpt gen_tac
  >> Cases_on `fmp_step_function ctx old h` >> simp[]
  >> strip_tac
  >> first_x_assum
       (qspecl_then [`fresh |+ (h.fn_name,x)`, `out`] mp_tac)
  >> simp[finite_mapTheory.FDOM_FUPDATE, pred_setTheory.EXTENSION]
  >> metis_tac[]
QED

Theorem fmp_context_step_FDOM[local]:
  fmp_context_step ctx old = SOME out ==>
  FDOM out = set (MAP (\fn. fn.fn_name) ctx.ctx_functions)
Proof
  simp[fmp_context_step_def]
  >> strip_tac
  >> drule fmp_step_functions_FDOM
  >> simp[]
QED

Theorem fmp_option_rounds_FDOM[local]:
  !n old out.
    FDOM old = set (MAP (\fn. fn.fn_name) ctx.ctx_functions) /\
    FUNPOW (fmp_option_step ctx) n (SOME old) = SOME out ==>
    FDOM out = set (MAP (\fn. fn.fn_name) ctx.ctx_functions)
Proof
  Induct
  >- simp[arithmeticTheory.FUNPOW]
  >> rpt gen_tac >> strip_tac
  >> Cases_on `fmp_context_step ctx old`
  >> gvs[arithmeticTheory.FUNPOW, fmp_option_step_def]
  >> metis_tac[fmp_context_step_FDOM]
QED

Theorem analyze_fmp_context_FDOM[local]:
  analyze_fmp_context ctx = SOME infos ==>
  FDOM infos = set (MAP (\fn. fn.fn_name) ctx.ctx_functions)
Proof
  rw[analyze_fmp_context_def]
  >> Cases_on `seed_fmp_context ctx` >> gvs[]
  >> metis_tac[seed_fmp_context_FDOM, fmp_option_rounds_FDOM]
QED

Theorem fmp_info_eq_fields[local]:
  x.fi_needs_fmp = y.fi_needs_fmp /\
  x.fi_publishes_fmp = y.fi_publishes_fmp ==>
  x = y
Proof
  Cases_on `x` >> Cases_on `y` >> simp[]
QED

Theorem fmp_join_target_info_total[local]:
  !targets acc.
    (!name. MEM name targets ==> ?info. FLOOKUP infos name = SOME info) ==>
    ?out. fmp_join_target_info infos targets acc = SOME out
Proof
  Induct >> simp[fmp_join_target_info_def]
  >> rpt gen_tac >> strip_tac
  >> pop_assum $ mk_asm "coverage"
  >> asm "coverage" (qspec_then `h` mp_tac) >> simp[] >> strip_tac
  >> simp[]
  >> first_x_assum irule
  >> rpt strip_tac
  >> asm "coverage" (qspec_then `name` mp_tac) >> simp[]
QED

Theorem fmp_step_function_total[local]:
  MEM fn ctx.ctx_functions /\
  (!f. MEM f ctx.ctx_functions ==> ?info. FLOOKUP old f.fn_name = SOME info) /\
  (!f. MEM f ctx.ctx_functions ==> ?targets. fmp_function_targets ctx f = SOME targets) ==>
  ?info. fmp_step_function ctx old fn = SOME info
Proof
  strip_tac
  >> qpat_x_assum `!f. MEM f ctx.ctx_functions ==>
                         ?info. FLOOKUP old f.fn_name = SOME info`
       (mk_asm "infos")
  >> qpat_x_assum `!f. MEM f ctx.ctx_functions ==>
                         ?targets. fmp_function_targets ctx f = SOME targets`
       (mk_asm "targets")
  >> asm "infos" (qspec_then `fn` mp_tac) >> simp[] >> strip_tac
  >> asm "targets" (qspec_then `fn` mp_tac) >> simp[] >> strip_tac
  >> simp[fmp_step_function_def]
  >> Cases_on `fn.fn_fmp_signature` >> simp[]
  >> irule fmp_join_target_info_total
  >> rpt strip_tac
  >> drule_all fmp_target_name_callee >> strip_tac
  >> asm "infos" (qspec_then `callee` mp_tac) >> simp[]
QED

Theorem fmp_step_functions_total[local]:
  (!f. MEM f ctx.ctx_functions ==>
       ?info. FLOOKUP old f.fn_name = SOME info) /\
  (!f. MEM f ctx.ctx_functions ==>
       ?targets. fmp_function_targets ctx f = SOME targets) /\
  (!f. MEM f fs ==> MEM f ctx.ctx_functions) ==>
  !acc. ?out. fmp_step_functions ctx old fs acc = SOME out
Proof
  Induct_on `fs`
  >- simp[fmp_step_functions_def]
  >> rpt strip_tac
  >> simp[fmp_step_functions_def]
  >> `?info. fmp_step_function ctx old h = SOME info` by
       (irule fmp_step_function_total >> simp[] >> metis_tac[])
  >> simp[]
  >> first_x_assum irule
  >> metis_tac[]
QED

Theorem fmp_context_step_total[local]:
  (!f. MEM f ctx.ctx_functions ==> ?info. FLOOKUP old f.fn_name = SOME info) /\
  (!f. MEM f ctx.ctx_functions ==> ?targets. fmp_function_targets ctx f = SOME targets) ==>
  ?out. fmp_context_step ctx old = SOME out
Proof
  simp[fmp_context_step_def]
  >> strip_tac
  >> irule fmp_step_functions_total
  >> simp[]
QED

Theorem fmp_final_round_fixed[local]:
  seed_fmp_context ctx = SOME seed /\
  FUNPOW (fmp_option_step ctx) (LENGTH ctx.ctx_functions) (SOME seed) =
    SOME infos ==>
  fmp_context_step ctx infos = SOME infos
Proof
  strip_tac
  >> `ctx_distinct_fn_names ctx` by
       metis_tac[seed_fmp_context_distinct]
  >> `!fn. MEM fn ctx.ctx_functions ==>
        ?info. FLOOKUP infos fn.fn_name = SOME info` by
       metis_tac[seed_fmp_context_coverage, fmp_option_rounds_coverage]
  >> `!fn. MEM fn ctx.ctx_functions ==>
        ?targets. fmp_function_targets ctx fn = SOME targets` by
       metis_tac[seed_fmp_context_targets]
  >> `?next. fmp_context_step ctx infos = SOME next` by
       metis_tac[fmp_context_step_total]
  >> `FUNPOW (fmp_option_step ctx) (SUC (LENGTH ctx.ctx_functions))
        (SOME seed) = SOME next` by
       simp[arithmeticTheory.FUNPOW_SUC, fmp_option_step_def]
  >> `FDOM infos = set (MAP (\fn. fn.fn_name) ctx.ctx_functions)` by
       metis_tac[seed_fmp_context_FDOM, fmp_option_rounds_FDOM]
  >> `FDOM next = set (MAP (\fn. fn.fn_name) ctx.ctx_functions)` by
       metis_tac[fmp_context_step_FDOM]
  >> `next = infos` by
       (rewrite_tac[finite_mapTheory.FLOOKUP_EXT]
        >> simp[FUN_EQ_THM]
        >> gen_tac
        >> Cases_on `x IN FDOM infos`
        >- (`?fn. MEM fn ctx.ctx_functions /\ fn.fn_name = x` by
              (qpat_x_assum `FDOM infos = _`
                 (fn th => fs[th, listTheory.MEM_MAP])
               >> qexists `fn` >> simp[])
            >> qpat_assum
                 `!f. MEM f ctx.ctx_functions ==>
                      ?i. FLOOKUP infos f.fn_name = SOME i`
                 (qspec_then `fn` mp_tac)
            >> (impl_tac >- simp[])
            >> strip_tac
            >> `?next_info. FLOOKUP next fn.fn_name = SOME next_info` by
                 metis_tac[fmp_context_step_coverage]
            >> gvs[]
            >> irule fmp_info_eq_fields
            >> conj_tac
            >- (qspecl_then
                  [`LENGTH ctx.ctx_functions`, `seed`, `infos`, `fn`, `info`]
                  mp_tac fmp_option_rounds_needs_iff
                >> (impl_tac >- simp[]) >> strip_tac
                >> qspecl_then
                     [`SUC (LENGTH ctx.ctx_functions)`, `seed`, `next`,
                      `fn`, `next_info`]
                     mp_tac fmp_option_rounds_needs_iff
                >> (impl_tac >- simp[]) >> strip_tac
                >> metis_tac[fmp_reaches_in_mono,
                             fmp_reaches_in_saturates])
            >> qspecl_then
                 [`LENGTH ctx.ctx_functions`, `seed`, `infos`, `fn`, `info`]
                 mp_tac fmp_option_rounds_publishes_iff
            >> (impl_tac >- simp[]) >> strip_tac
            >> qspecl_then
                 [`SUC (LENGTH ctx.ctx_functions)`, `seed`, `next`,
                  `fn`, `next_info`]
                 mp_tac fmp_option_rounds_publishes_iff
            >> (impl_tac >- simp[]) >> strip_tac
            >> metis_tac[fmp_reaches_in_mono,
                         fmp_reaches_in_saturates])
        >> gvs[finite_mapTheory.FLOOKUP_DEF])
  >> gvs[]
QED


Theorem fmp_reaches_in_final_unsealed[local]:
  MEM caller ctx.ctx_functions /\ caller.fn_fmp_signature = NONE ==>
  (fmp_reaches_in ctx (LENGTH ctx.ctx_functions) caller source <=>
   caller = source \/
   ?callee. fmp_unsealed_calls ctx caller callee /\
            fmp_reaches_in ctx (LENGTH ctx.ctx_functions) callee source)
Proof
  strip_tac
  >> Cases_on `ctx.ctx_functions`
  >- gvs[]
  >> eq_tac
  >- (strip_tac
      >> qpat_x_assum
           `fmp_reaches_in ctx (LENGTH (h::t)) caller source` mp_tac
      >> pure_once_rewrite_tac[listTheory.LENGTH]
      >> CONV_TAC (LAND_CONV (SCONV [fmp_reaches_in_def]))
      >> metis_tac[fmp_reaches_in_mono])
  >> strip_tac
  >- simp[fmp_reaches_in_refl]
  >> `fmp_reaches_in ctx (SUC (LENGTH ctx.ctx_functions)) caller source` by
       (pure_once_rewrite_tac[fmp_reaches_in_def]
        >> disj2_tac >> qexists `callee`
        >> conj_tac >- (first_assum ACCEPT_TAC)
        >> qpat_assum `ctx.ctx_functions = h::t`
             (fn th => rewrite_tac[th])
        >> first_assum ACCEPT_TAC)
  >> metis_tac[fmp_reaches_in_saturates]
QED


Theorem fmp_final_needs_join_iff[local]:
  seed_fmp_context ctx = SOME seed /\
  FUNPOW (fmp_option_step ctx) (LENGTH ctx.ctx_functions) (SOME seed) =
    SOME infos /\
  MEM fn ctx.ctx_functions /\ fn.fn_fmp_signature = NONE /\
  fmp_function_targets ctx fn = SOME targets /\
  FLOOKUP infos fn.fn_name = SOME info ==>
  (info.fi_needs_fmp <=>
   (fmp_direct_info fn).fi_needs_fmp \/
   ?name callee_info. MEM name targets /\
     FLOOKUP infos name = SOME callee_info /\ callee_info.fi_needs_fmp)
Proof
  strip_tac
  >> `!callee. MEM callee ctx.ctx_functions ==>
        ?ci. FLOOKUP infos callee.fn_name = SOME ci` by
       metis_tac[seed_fmp_context_distinct, seed_fmp_context_coverage,
                 fmp_option_rounds_coverage]
  >> `!callee ci. MEM callee ctx.ctx_functions /\
        FLOOKUP infos callee.fn_name = SOME ci ==>
        (ci.fi_needs_fmp <=>
         ?source. MEM source ctx.ctx_functions /\
           fmp_reaches_in ctx (LENGTH ctx.ctx_functions) callee source /\
           fmp_needs_source source)` by
       metis_tac[fmp_option_rounds_needs_iff]
  >> `((?name callee_info. MEM name targets /\
          FLOOKUP infos name = SOME callee_info /\ callee_info.fi_needs_fmp) <=>
       ?callee callee_info. fmp_unsealed_calls ctx fn callee /\
         FLOOKUP infos callee.fn_name = SOME callee_info /\
         callee_info.fi_needs_fmp)` by
       (irule fmp_target_needs_exists >> simp[])
  >> `((?callee callee_info. fmp_unsealed_calls ctx fn callee /\
          FLOOKUP infos callee.fn_name = SOME callee_info /\
          callee_info.fi_needs_fmp) <=>
       ?callee source. fmp_unsealed_calls ctx fn callee /\
         MEM source ctx.ctx_functions /\
         fmp_reaches_in ctx (LENGTH ctx.ctx_functions) callee source /\
         fmp_needs_source source)` by
       (irule fmp_callee_needs_round_exists >> simp[])
  >> `info.fi_needs_fmp <=>
       ?source. MEM source ctx.ctx_functions /\
         fmp_reaches_in ctx (LENGTH ctx.ctx_functions) fn source /\
         fmp_needs_source source` by
       metis_tac[fmp_option_rounds_needs_iff]
  >> `!source.
       (fmp_reaches_in ctx (LENGTH ctx.ctx_functions) fn source <=>
        fn = source \/
        ?callee. fmp_unsealed_calls ctx fn callee /\
          fmp_reaches_in ctx (LENGTH ctx.ctx_functions) callee source)` by
       metis_tac[fmp_reaches_in_final_unsealed]
  >> gvs[fmp_needs_source_def]
  >> eq_tac
  >- (strip_tac
      >- (disj1_tac >> gvs[])
      >> disj2_tac
      >> qexistsl [`callee`, `source`] >> simp[])
  >> strip_tac
  >- (qexists `fn` >> simp[])
  >> qexists `source` >> simp[]
  >> disj2_tac >> qexists `callee` >> simp[]
QED

Theorem fmp_final_publishes_join_iff[local]:
  seed_fmp_context ctx = SOME seed /\
  FUNPOW (fmp_option_step ctx) (LENGTH ctx.ctx_functions) (SOME seed) =
    SOME infos /\
  MEM fn ctx.ctx_functions /\ fn.fn_fmp_signature = NONE /\
  fmp_function_targets ctx fn = SOME targets /\
  FLOOKUP infos fn.fn_name = SOME info ==>
  (info.fi_publishes_fmp <=>
   (fmp_direct_info fn).fi_publishes_fmp \/
   ?name callee_info. MEM name targets /\
     FLOOKUP infos name = SOME callee_info /\ callee_info.fi_publishes_fmp)
Proof
  strip_tac
  >> `!callee. MEM callee ctx.ctx_functions ==>
        ?ci. FLOOKUP infos callee.fn_name = SOME ci` by
       metis_tac[seed_fmp_context_distinct, seed_fmp_context_coverage,
                 fmp_option_rounds_coverage]
  >> `!callee ci. MEM callee ctx.ctx_functions /\
        FLOOKUP infos callee.fn_name = SOME ci ==>
        (ci.fi_publishes_fmp <=>
         ?source. MEM source ctx.ctx_functions /\
           fmp_reaches_in ctx (LENGTH ctx.ctx_functions) callee source /\
           fmp_publishes_source source)` by
       metis_tac[fmp_option_rounds_publishes_iff]
  >> `((?name callee_info. MEM name targets /\
          FLOOKUP infos name = SOME callee_info /\
          callee_info.fi_publishes_fmp) <=>
       ?callee callee_info. fmp_unsealed_calls ctx fn callee /\
         FLOOKUP infos callee.fn_name = SOME callee_info /\
         callee_info.fi_publishes_fmp)` by
       (irule fmp_target_publishes_exists >> simp[])
  >> `((?callee callee_info. fmp_unsealed_calls ctx fn callee /\
          FLOOKUP infos callee.fn_name = SOME callee_info /\
          callee_info.fi_publishes_fmp) <=>
       ?callee source. fmp_unsealed_calls ctx fn callee /\
         MEM source ctx.ctx_functions /\
         fmp_reaches_in ctx (LENGTH ctx.ctx_functions) callee source /\
         fmp_publishes_source source)` by
       (irule fmp_callee_publishes_round_exists >> simp[])
  >> `info.fi_publishes_fmp <=>
       ?source. MEM source ctx.ctx_functions /\
         fmp_reaches_in ctx (LENGTH ctx.ctx_functions) fn source /\
         fmp_publishes_source source` by
       metis_tac[fmp_option_rounds_publishes_iff]
  >> `!source.
       (fmp_reaches_in ctx (LENGTH ctx.ctx_functions) fn source <=>
        fn = source \/
        ?callee. fmp_unsealed_calls ctx fn callee /\
          fmp_reaches_in ctx (LENGTH ctx.ctx_functions) callee source)` by
       metis_tac[fmp_reaches_in_final_unsealed]
  >> gvs[fmp_publishes_source_def]
  >> eq_tac
  >- (strip_tac
      >- (disj1_tac >> gvs[])
      >> disj2_tac
      >> qexistsl [`callee`, `source`] >> simp[])
  >> strip_tac
  >- (qexists `fn` >> simp[])
  >> qexists `source` >> simp[]
  >> disj2_tac >> qexists `callee` >> simp[]
QED
Theorem analyze_fmp_context_unsealed_join[local]:
  analyze_fmp_context ctx = SOME infos /\
  MEM fn ctx.ctx_functions /\ fn.fn_fmp_signature = NONE ==>
  ?targets info.
    fmp_function_targets ctx fn = SOME targets /\
    FLOOKUP infos fn.fn_name = SOME info /\
    fmp_join_target_info infos targets (fmp_direct_info fn) = SOME info
Proof
  strip_tac
  >> `?seed. seed_fmp_context ctx = SOME seed /\
        FUNPOW (fmp_option_step ctx) (LENGTH ctx.ctx_functions) (SOME seed) =
          SOME infos` by
       (qpat_x_assum `analyze_fmp_context ctx = SOME infos` mp_tac
        >> rw[analyze_fmp_context_def]
        >> Cases_on `seed_fmp_context ctx` >> gvs[])
  >> `?targets. fmp_function_targets ctx fn = SOME targets` by
       metis_tac[seed_fmp_context_targets]
  >> `?info. FLOOKUP infos fn.fn_name = SOME info` by
       metis_tac[analyze_fmp_context_coverage]
  >> `?out. fmp_join_target_info infos targets (fmp_direct_info fn) =
             SOME out` by
       (irule fmp_join_target_info_total
        >> rpt strip_tac
        >> drule_all fmp_target_name_callee >> strip_tac
        >> metis_tac[analyze_fmp_context_coverage])
  >> qexistsl [`targets`, `info`]
  >> simp[]
  >> `out = info` by
       (irule fmp_info_eq_fields
        >> conj_tac
        >- (qspecl_then [`targets`, `fmp_direct_info fn`, `out`]
              mp_tac fmp_join_target_info_needs_iff
            >> (impl_tac >- simp[]) >> strip_tac
            >> drule_all fmp_final_needs_join_iff
            >> metis_tac[])
        >> qspecl_then [`targets`, `fmp_direct_info fn`, `out`]
             mp_tac fmp_join_target_info_publishes_iff
        >> (impl_tac >- simp[]) >> strip_tac
        >> drule_all fmp_final_publishes_join_iff
        >> metis_tac[])
  >> gvs[]
QED

Theorem analyze_fmp_context_valid:
  analyze_fmp_context ctx = SOME infos ==>
  fmp_info_valid ctx infos
Proof
  strip_tac
  >> simp[fmp_info_valid_def]
  >> conj_tac
  >- metis_tac[analyze_fmp_context_distinct]
  >> conj_tac
  >- metis_tac[analyze_fmp_context_coverage]
  >> conj_tac
  >- metis_tac[analyze_fmp_context_sealed_lookup]
  >> metis_tac[analyze_fmp_context_unsealed_join]
QED
val _ = export_theory();
