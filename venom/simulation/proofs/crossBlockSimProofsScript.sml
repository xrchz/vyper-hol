(*
 * Cross-Block Simulation — Proofs
 *
 * TOP-LEVEL:
 *   resolves_to_mono_proof             — monotonicity of resolves_to
 *   resolving_block_sim_function_proof — the main lifting theorem
 *)

Theory crossBlockSimProofs
Ancestors
  crossBlockSimDefs passSimulationDefs passSimulationProofs
  execEquivParamDefs execEquivParamProofs execEquivParamBase
  stateEquiv stateEquivProps execEquivProps venomExecProps
  venomExecSemantics venomExecProofs venomInst
  arithmetic relation pair list

(* ===== resolves_to_mono ===== *)

Theorem resolves_to_mono_proof:
  !R_ok R_term bbs1 bbs2 n m r1 r2.
    n <= m /\
    resolves_to R_ok R_term bbs1 bbs2 n r1 r2 ==>
    resolves_to R_ok R_term bbs1 bbs2 m r1 r2
Proof
  Induct_on `n` >> rw[]
  >- (Cases_on `m` >> fs[resolves_to_def])
  >>
  Cases_on `m` >> fs[] >>
  fs[resolves_to_def]
QED

(* ===== INVOKE at fuel 0 always returns Error ===== *)

Triviality step_inst_invoke_fuel_0:
  !ctx inst s. inst.inst_opcode = INVOKE ==>
    ?e. step_inst 0 ctx inst s = Error e
Proof
  rw[step_inst_def, run_blocks_def] >>
  BasicProvers.EVERY_CASE_TAC
QED

(* ===== General fuel monotonicity for run_blocks ===== *)
(* This is a GENERAL property of the execution model: once run_blocks
   terminates at some fuel, additional fuel gives the same result.
   Proved by strong induction on fuel, with a sub-lemma for exec_block.
   Key insight: all INVOKEs that execute during a terminating run also
   terminate (otherwise they'd produce Error, and the outer fn would too),
   so by IH they are fuel-independent. *)

Triviality step_inst_fuel_mono:
  !f ctx inst st k.
    (!e. step_inst f ctx inst st <> Error e) ==>
    (!ctx' fn' s'. terminates (run_blocks f ctx' fn' s') ==>
       !k'. run_blocks (f + k') ctx' fn' s' = run_blocks f ctx' fn' s') ==>
    step_inst (f + k) ctx inst st = step_inst f ctx inst st
Proof
  rw[] >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    `step_inst f ctx inst st =
       case decode_invoke inst of
         NONE => Error "invoke: bad operand format"
       | SOME (callee_name, arg_ops) =>
           case lookup_function callee_name ctx.ctx_functions of
             NONE => Error "invoke: function not found"
           | SOME callee_fn =>
               case eval_operands arg_ops st of
                 NONE => Error "invoke: undefined argument"
               | SOME args =>
                   case setup_callee callee_fn args st of
                     NONE => Error "invoke: empty function"
                   | SOME callee_s =>
                       case run_blocks f ctx callee_fn callee_s of
                         OK v => Error "invoke: callee did not return"
                       | Halt s'' => Halt s''
                       | Abort a s'' => Abort a s''
                       | IntRet ret callee_s' =>
                           (case bind_outputs inst.inst_outputs ret.iret_values
                                   (adopt_return_fmp ret
                                      (merge_callee_state st callee_s')) of
                             NONE => Error "invoke: return arity mismatch"
                           | SOME s'' => OK s'')
                       | Error e => Error e`
      by simp[Once step_inst_def] >>
    Cases_on `decode_invoke inst`
    >- gvs[]
    >- (
      Cases_on `x` >>
      rename1 `decode_invoke inst = SOME (cn, ao)` >>
      Cases_on `lookup_function cn ctx.ctx_functions`
      >- gvs[]
      >- (
        rename1 `_ = SOME cfn` >>
        Cases_on `eval_operands ao st`
        >- gvs[]
        >- (
          rename1 `_ = SOME args` >>
          Cases_on `setup_callee cfn args st`
          >- gvs[]
          >- (
            rename1 `_ = SOME cs` >>
            `terminates (run_blocks f ctx cfn cs)` by
              (Cases_on `run_blocks f ctx cfn cs` >>
               gvs[terminates_def]) >>
            `run_blocks (f + k) ctx cfn cs = run_blocks f ctx cfn cs` by
              (first_x_assum irule >> simp[]) >>
            rw[step_inst_def]
          )
        )
      )
    )
  )
  >- metis_tac[step_inst_non_invoke]
QED

Triviality exec_block_fuel_mono_lem:
  !n (ctx:venom_context) (bb:basic_block) (st:venom_state) f.
    n = LENGTH bb.bb_instructions - st.vs_inst_idx ==>
    (!e. exec_block f ctx bb st <> Error e) ==>
    (!ctx' fn' s'. terminates (run_blocks f ctx' fn' s') ==>
       !k. run_blocks (f + k) ctx' fn' s' = run_blocks f ctx' fn' s') ==>
    !k. exec_block (f + k) ctx bb st = exec_block f ctx bb st
Proof
  completeInduct_on `n` >> rw[] >>
  simp[Once exec_block_def] >>
  `exec_block f ctx bb st =
   case get_instruction bb st.vs_inst_idx of
     NONE => Error "block not terminated"
   | SOME inst =>
     case step_inst f ctx inst st of
       OK st' => if is_terminator inst.inst_opcode then
                   if st'.vs_halted then Halt st' else OK st'
                 else exec_block f ctx bb (st' with vs_inst_idx := SUC st.vs_inst_idx)
     | Halt st' => Halt st'
     | Abort a st' => Abort a st'
     | IntRet vals st' => IntRet vals st'
     | Error e => Error e` by simp[Once exec_block_def] >>
  Cases_on `get_instruction bb st.vs_inst_idx`
  >- gvs[]
  >- (
    rename1 `_ = SOME inst` >>
    gvs[] >>
    `!e. step_inst f ctx inst st <> Error e` by
      (spose_not_then strip_assume_tac >> gvs[]) >>
    `step_inst (f + k) ctx inst st = step_inst f ctx inst st` by
      (irule step_inst_fuel_mono >> simp[]) >>
    gvs[] >>
    Cases_on `step_inst f ctx inst st` >> gvs[]
    >- (
      rename1 `_ = OK st'` >>
      IF_CASES_TAC >> gvs[] >>
      `st'.vs_inst_idx = st.vs_inst_idx`
        by metis_tac[step_inst_preserves_inst_idx] >>
      `st.vs_inst_idx < LENGTH bb.bb_instructions`
        by (fs[get_instruction_def] >>
            Cases_on `st.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[]) >>
      first_x_assum irule >> simp[]
    )
  )
QED

Triviality run_block_fuel_mono_lem:
  !f ctx bb s.
    (!e. run_block f ctx bb s <> Error e) ==>
    (!ctx' fn' s'. terminates (run_blocks f ctx' fn' s') ==>
       !k. run_blocks (f + k) ctx' fn' s' = run_blocks f ctx' fn' s') ==>
    !k. run_block (f + k) ctx bb s = run_block f ctx bb s
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[eval_phis_ok_or_error_defs] >>
  qsuff_tac
    `!e. exec_block f ctx bb (v with vs_inst_idx := phi_prefix_length bb.bb_instructions) <> Error e`
  >- (strip_tac >> irule (REWRITE_RULE[GSYM AND_IMP_INTRO] exec_block_fuel_mono_lem) >> simp[]) >>
  rpt strip_tac >>
  first_assum (qspecl_then [`e`] assume_tac) >>
  fs[run_block_def]
QED

Triviality run_block_not_error_if_terminates[local]:
  !n ctx fn bb s.
    terminates (run_blocks (SUC n) ctx fn s) ==>
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
    !e. run_block n ctx bb s <> Error e
Proof
  rpt strip_tac >>
  CCONTR_TAC >>
  qpat_x_assum `terminates _` mp_tac >>
  simp[Once run_blocks_unfold, terminates_def]
QED

Triviality run_blocks_fuel_mono_IH[local]:
  !n ctx' fn' s' k.
    (!m. m < SUC n ==>
       !ctx fn s. terminates (run_blocks m ctx fn s) ==>
       !k. run_blocks (m + k) ctx fn s = run_blocks m ctx fn s) ==>
    terminates (run_blocks n ctx' fn' s') ==>
    run_blocks (n + k) ctx' fn' s' = run_blocks n ctx' fn' s'
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`n`] mp_tac) >> simp[] >> metis_tac[]
QED

Triviality terminates_run_blocks_from_run_block_OK[local]:
  !n ctx fn s bb v.
    terminates (run_blocks (SUC n) ctx fn s) /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block n ctx bb s = OK v /\ ~v.vs_halted ==>
    terminates (run_blocks n ctx fn v)
Proof
  rpt strip_tac >>
  qpat_x_assum `terminates _` mp_tac >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  simp[terminates_def]
QED

Theorem run_blocks_fuel_mono:
  !fuel ctx fn s.
    terminates (run_blocks fuel ctx fn s) ==>
    !k. run_blocks (fuel + k) ctx fn s = run_blocks fuel ctx fn s
Proof
  Induct_on `fuel` >> rpt strip_tac
  >- (
    `run_blocks 0 ctx fn s = Error "out of fuel"` by EVAL_TAC >>
    fs[terminates_def])
  >>
  rename1 `SUC n` >>
  `SUC n + k = SUC (n + k)` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
  >> rename1 `SOME bb` >>
  `!e. run_block n ctx bb s <> Error e`
    by metis_tac[run_block_not_error_if_terminates] >>
  `run_block (n + k) ctx bb s = run_block n ctx bb s`
    by (irule run_block_fuel_mono_lem >> conj_tac
        >- simp[]
        >>
        rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[]) >>
  Cases_on `run_block n ctx bb s` >> gvs[] >>
  rename1 `OK v` >>
  Cases_on `v.vs_halted` >> gvs[] >>
  `terminates (run_blocks n ctx fn v)`
    by metis_tac[terminates_run_blocks_from_run_block_OK] >>
  first_x_assum (qspecl_then [`ctx`,`fn`,`v`] mp_tac) >> simp[]
QED

(* Boundary lemma: run_blocks_fuel_mono in the universal form needed by
   run_block_fuel_mono_lem and fuel_mono_eq. Avoids metis_tac timeout. *)
Triviality run_blocks_fuel_mono_univ:
  !fuel.
    (!ctx fn s. terminates (run_blocks fuel ctx fn s) ==>
       !k. run_blocks (fuel + k) ctx fn s = run_blocks fuel ctx fn s)
Proof
  gen_tac >> rpt strip_tac >> irule run_blocks_fuel_mono >> simp[]
QED

Triviality exec_block_fuel_mono:
  !f ctx bb s.
    (!e. exec_block f ctx bb s <> Error e) ==>
    !k. exec_block (f + k) ctx bb s = exec_block f ctx bb s
Proof
  rpt strip_tac >>
  irule (REWRITE_RULE [GSYM AND_IMP_INTRO] exec_block_fuel_mono_lem) >>
  simp[run_blocks_fuel_mono_univ]
QED

(* ===== resolves_to helpers ===== *)

(* Both sides non-continuable: resolves_to collapses to lift_result *)
Triviality resolves_to_terminal_collapses:
  !n R_ok R_term bbs1 bbs2 r1 r2.
    resolves_to R_ok R_term bbs1 bbs2 n r1 r2 /\
    (!v. r1 = OK v ==> v.vs_halted) /\
    (!v. r2 = OK v ==> v.vs_halted) ==>
    lift_result R_ok R_term R_term r1 r2
Proof
  Induct_on `n` >> rw[resolves_to_def]
QED

(* When r1 is not OK-non-halted AND terminates, lift_result r1 (Error e) = F *)
Triviality lift_result_term_error_F:
  !R_ok R_term r1 e.
    terminates r1 /\
    (!v. r1 = OK v ==> v.vs_halted) ==>
    ~lift_result R_ok R_term R_term r1 (Error e)
Proof
  Cases_on `r1` >> simp[lift_result_def, terminates_def]
QED

(* Symmetric *)
Triviality lift_result_error_term_F:
  !R_ok R_term e r2.
    terminates r2 /\
    (!v. r2 = OK v ==> v.vs_halted) ==>
    ~lift_result R_ok R_term R_term (Error e) r2
Proof
  Cases_on `r2` >> simp[lift_result_def, terminates_def]
QED

(* ===== inst_idx_0_lemma ===== *)

Triviality inst_idx_0_lemma:
  !v:venom_state. v.vs_inst_idx = 0 ==> (v with vs_inst_idx := 0 = v)
Proof
  rw[venomStateTheory.venom_state_component_equality]
QED

Triviality run_block_OK_inst_idx_0[local]:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] mp_tac eval_phis_ok_or_error_defs >> strip_tac >>
  fs[run_block_def] >> drule exec_block_OK_inst_idx_0 >> simp[]
QED

Triviality run_block_ok_sets_prev_bb[local]:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_prev_bb <> NONE
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] mp_tac eval_phis_ok_or_error_defs >>
  strip_tac >- (fs[run_block_def] >> metis_tac[exec_block_ok_sets_prev_bb]) >>
  fs[run_block_def]
QED

(* ===== run_blocks one-step helpers ===== *)

Triviality run_blocks_ok_block_at:
  !ctx fn bb s v fuel.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block fuel ctx bb s = OK v /\ ~v.vs_halted ==>
    run_blocks (SUC fuel) ctx fn s = run_blocks fuel ctx fn v
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[]
QED

(* At any fuel: non-OK block result propagates to run_blocks *)
Triviality run_blocks_at_non_ok_block:
  !f ctx fn bb s r.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block f ctx bb s = r /\ (!v. r <> OK v) ==>
    run_blocks (SUC f) ctx fn s = r
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[] >>
  Cases_on `r` >> gvs[]
QED

(* At any fuel: OK-halted block result becomes Halt *)
Triviality run_blocks_at_ok_halted_block:
  !f ctx fn bb s v.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block f ctx bb s = OK v /\ v.vs_halted ==>
    run_blocks (SUC f) ctx fn s = Halt v
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >> simp[]
QED


(* ===== resolve_right_fn: right-side resolution ===== *)
(* If resolves_to n r1 (OK v2) where r1 is "fn-terminal" (terminates,
   and OK only if halted), and v2 is non-halted, then fn' from v2
   terminates with lift_result matching the fn-level view of r1.
   Handles both r1 <> OK v and r1 = OK v_halted. *)

Triviality resolve_right_fn:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn_blocks.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted))
  ==>
    !n bbs1 r1 v2.
      resolves_to R_ok R_term bbs1 fn_blocks n r1 (OK v2) /\
      ~v2.vs_halted /\ v2.vs_inst_idx = 0 /\
      terminates r1 /\
      (!v. r1 = OK v ==> v.vs_halted)
    ==>
      !fn' ctx.
        fn'.fn_blocks = fn_blocks
      ==>
        ?fuel. terminates (run_blocks fuel ctx fn' v2) /\
          ((!v. r1 <> OK v) ==>
            lift_result R_ok R_term R_term r1 (run_blocks fuel ctx fn' v2)) /\
          (!v. r1 = OK v ==>
            lift_result R_ok R_term R_term (Halt v) (run_blocks fuel ctx fn' v2))
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `n` >> rpt strip_tac
  >- (gvs[resolves_to_def] >>
      Cases_on `r1` >> gvs[lift_result_def] >>
      res_tac >> gvs[])
  >> gvs[Once resolves_to_def]
  >- (Cases_on `r1` >> gvs[lift_result_def] >>
      res_tac >> gvs[])
  >> rename1 `lookup_block v2.vs_current_bb fn'.fn_blocks = SOME bb`
  >> qpat_x_assum `!fuel ctx. resolves_to _ _ _ _ _ _ (run_block _ _ _ _)`
       (qspecl_then [`0`, `ctx`] strip_assume_tac)
  >> Cases_on `run_block 0 ctx bb v2` >> gvs[]
  (* OK v *)
  >- (
    rename1 `run_block 0 ctx bb v2 = OK v` >>
    `!k. run_block k ctx bb v2 = OK v` by (
      `!e. run_block 0 ctx bb v2 <> Error e` by simp[] >>
      `!k. run_block (0 + k) ctx bb v2 = run_block 0 ctx bb v2`
        by (irule run_block_fuel_mono_lem >> simp[run_blocks_fuel_mono_univ]) >>
      fs[]) >>
    Cases_on `v.vs_halted`
    >- (
      qpat_x_assum `resolves_to _ _ _ _ _ _ (OK _)`
        (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                              resolves_to_terminal_collapses)) >>
      simp[] >> strip_tac >>
      qexists_tac `SUC 0` >>
      `run_blocks (SUC 0) ctx fn' v2 = Halt v`
        by (irule run_blocks_at_ok_halted_block >> simp[]) >>
      simp[terminates_def] >>
      Cases_on `r1` >> gvs[lift_result_def, terminates_def] >> res_tac)
    >- (
      `v.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      qpat_x_assum `!bbs1 r1 v2. resolves_to _ _ _ _ _ _ (OK _) /\ _ ==> _`
        (qspecl_then [`bbs1`, `r1`, `v`] mp_tac) >>
      simp[] >> strip_tac >>
      pop_assum (qspecl_then [`fn'`, `ctx`] mp_tac) >> simp[] >>
      strip_tac >>
      rename1 `terminates (run_blocks fuel2 ctx fn' v)` >>
      qexists_tac `SUC fuel2` >>
      `run_blocks (SUC fuel2) ctx fn' v2 = run_blocks fuel2 ctx fn' v`
        by (irule run_blocks_ok_block_at >> simp[]) >>
      simp[]))
  (* Halt/Abort/IntRet: terminal block, resolves_to collapses *)
  >> (
    qpat_x_assum `resolves_to _ _ _ _ _ _ _`
      (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            resolves_to_terminal_collapses)) >>
    simp[terminates_def] >> strip_tac >>
    TRY (
      `!e. run_block 0 ctx bb v2 <> Error e` by simp[] >>
      `!k. run_block (0 + k) ctx bb v2 = run_block 0 ctx bb v2`
        by (irule run_block_fuel_mono_lem >> simp[run_blocks_fuel_mono_univ]) >>
      fs[] >>
      qexists_tac `SUC 0` >>
      `run_blocks (SUC 0) ctx fn' v2 = run_block 0 ctx bb v2`
        by (irule run_blocks_at_non_ok_block >> simp[]) >>
      simp[terminates_def]) >>
    Cases_on `r1` >> gvs[lift_result_def, terminates_def])
QED

(* ===== Symmetry: lift_result flip ===== *)

Triviality lift_result_flip:
  !R_ok R_term r1 r2.
    lift_result R_ok R_term R_term r1 r2 <=>
    lift_result (\a b. R_ok b a) (\a b. R_term b a) (\a b. R_term b a) r2 r1
Proof
  Cases_on `r1` >> Cases_on `r2` >> simp[lift_result_def] >> metis_tac[]
QED

(* ===== resolve_left_fn: generalized left resolution ===== *)
(* Symmetric to resolve_right_fn for the left side. *)

Triviality resolve_left_fn:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn_blocks.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted))
  ==>
    !n bbs2 r2 v1.
      resolves_to R_ok R_term fn_blocks bbs2 n (OK v1) r2 /\
      ~v1.vs_halted /\ v1.vs_inst_idx = 0 /\
      terminates r2 /\
      (!v. r2 = OK v ==> v.vs_halted)
    ==>
      !fn ctx.
        fn.fn_blocks = fn_blocks
      ==>
        ?fuel. terminates (run_blocks fuel ctx fn v1) /\
          ((!v. r2 <> OK v) ==>
            lift_result R_ok R_term R_term (run_blocks fuel ctx fn v1) r2) /\
          (!v. r2 = OK v ==>
            lift_result R_ok R_term R_term (run_blocks fuel ctx fn v1) (Halt v))
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `n`
  >- (rpt strip_tac >> gvs[resolves_to_def] >>
      Cases_on `r2` >> gvs[lift_result_def] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[Once resolves_to_def] >>
  TRY (Cases_on `r2` >> gvs[lift_result_def] >> metis_tac[] >> NO_TAC) >>
  rename1 `lookup_block v1.vs_current_bb fn.fn_blocks = SOME bb` >>
      `v1 with vs_inst_idx := 0 = v1` by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      qpat_x_assum `!fuel ctx. resolves_to _ _ _ _ _ (run_block _ _ _ _) _`
        (qspecl_then [`0`, `ctx`] strip_assume_tac) >>
      `!e. run_block 0 ctx bb v1 <> Error e` by (
        spose_not_then strip_assume_tac >> gvs[] >>
        drule resolves_to_terminal_collapses >> simp[] >> strip_tac >>
        Cases_on `r2` >> gvs[lift_result_def, terminates_def]) >>
      `!k. run_block (0 + k) ctx bb v1 = run_block 0 ctx bb v1` by
        (irule run_block_fuel_mono_lem >> simp[run_blocks_fuel_mono_univ]) >>
      fs[] >>
      Cases_on `run_block 0 ctx bb v1` >> gvs[] >>
      TRY (rename1 `_ = OK v1'` >>
        Cases_on `v1'.vs_halted` >> gvs[] >>
        TRY (drule resolves_to_terminal_collapses >> simp[] >> strip_tac >>
          qexists_tac `SUC 0` >>
          `run_blocks (SUC 0) ctx fn v1 = Halt v1'`
            by (irule run_blocks_at_ok_halted_block >> simp[]) >>
          simp[terminates_def] >>
          Cases_on `r2` >> gvs[lift_result_def] >> metis_tac[] >> NO_TAC) >>
        `v1'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
        qpat_x_assum `!bbs2 r2 v1. _ ==> _`
          (qspecl_then [`bbs2`, `r2`, `v1'`] mp_tac) >>
        simp[] >> strip_tac >>
        pop_assum (qspecl_then [`fn`, `ctx`] mp_tac) >> simp[] >>
        strip_tac >>
        rename1 `terminates (run_blocks fuel2 ctx fn v1')` >>
        qexists_tac `SUC fuel2` >>
        `run_blocks (SUC fuel2) ctx fn v1 = run_blocks fuel2 ctx fn v1'`
          by (irule run_blocks_ok_block_at >> simp[]) >>
        simp[] >> NO_TAC) >>
      drule resolves_to_terminal_collapses >> simp[terminates_def] >> strip_tac >>
      qexists_tac `SUC 0` >>
      `run_blocks (SUC 0) ctx fn v1 = run_block 0 ctx bb v1`
        by (irule run_blocks_at_non_ok_block >> simp[]) >>
      simp[terminates_def] >>
      Cases_on `r2` >> gvs[lift_result_def, terminates_def]
QED

(* ===== resolve_left_fn_error: resolution to Error ==> fn never terminates ===== *)

Triviality resolve_left_fn_error:
  !n R_ok R_term fn bbs2 e v1.
    resolves_to R_ok R_term fn.fn_blocks bbs2 n (OK v1) (Error e) /\
    ~v1.vs_halted /\ v1.vs_inst_idx = 0 ==>
    !ctx fuel. ~terminates (run_blocks fuel ctx fn v1)
Proof
  Induct_on `n`
  >- rw[resolves_to_def, lift_result_def]
  >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  `?bb. lookup_block v1.vs_current_bb fn.fn_blocks = SOME bb /\
        !fuel ctx. resolves_to R_ok R_term fn.fn_blocks bbs2 n
          (run_block fuel ctx bb v1) (Error e)` by (
    qpat_x_assum `resolves_to _ _ _ _ (SUC _) _ _` mp_tac >>
    simp[Once resolves_to_def, lift_result_def] >>
    simp[]) >>
  Cases_on `fuel`
  >- simp[Once run_blocks_def, terminates_def]
  >> rename1 `SUC fuel'` >>
  first_x_assum (qspecl_then [`fuel'`, `ctx`] assume_tac) >>
  Cases_on `run_block fuel' ctx bb v1` >> gvs[]
  >- (
    (* OK v' - continuation case *)
    rename1 `run_block fuel' ctx bb v1 = OK v'` >>
    Cases_on `v'.vs_halted`
    >- (
      `run_blocks (SUC fuel') ctx fn v1 = Halt v'`
        by (irule run_blocks_at_ok_halted_block >> simp[]) >>
      drule resolves_to_terminal_collapses >> simp[terminates_def] >>
      gvs[lift_result_def])
    >- (
      `v'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      `run_blocks (SUC fuel') ctx fn v1 = run_blocks fuel' ctx fn v'`
        by (irule run_blocks_ok_block_at >> simp[]) >>
      simp[] >>
      PRED_ASSUM is_forall (fn ih =>
        mp_tac (Q.SPECL [`R_ok`,`R_term`,`fn`,`bbs2`,`e`,`v'`] ih)) >>
      simp[] >> strip_tac >>
      first_x_assum (qspecl_then [`fuel'`] mp_tac) >> simp[]))
  >- (
    (* Halt - contradiction via resolves_to_terminal_collapses *)
    `run_blocks (SUC fuel') ctx fn v1 = run_block_entry fuel' ctx bb v1`
      by (irule run_blocks_at_non_ok_block >> simp[]) >>
    simp[terminates_def] >>
    drule resolves_to_terminal_collapses >> simp[lift_result_def])
  >- (
    (* Abort - contradiction *)
    `run_blocks (SUC fuel') ctx fn v1 = run_block_entry fuel' ctx bb v1`
      by (irule run_blocks_at_non_ok_block >> simp[]) >>
    simp[terminates_def] >>
    drule resolves_to_terminal_collapses >> simp[lift_result_def])
  >- (
    (* IntRet - contradiction *)
    `run_blocks (SUC fuel') ctx fn v1 = run_block_entry fuel' ctx bb v1`
      by (irule run_blocks_at_non_ok_block >> simp[]) >>
    simp[terminates_def] >>
    drule resolves_to_terminal_collapses >> simp[lift_result_def])
  >>
    (* Error - terminates = F directly *)
    `run_blocks (SUC fuel') ctx fn v1 = run_block_entry fuel' ctx bb v1`
      by (irule run_blocks_at_non_ok_block >> simp[]) >>
    simp[terminates_def]
QED

(* ===== fuel_alignment: align fuels via fuel mono + same-code ===== *)

Triviality fuel_alignment:
  !R_ok R_term fn ctx s1 s2 f1 f2.
    R_ok s1 s2 /\
    terminates (run_blocks f1 ctx fn s1) /\
    terminates (run_blocks f2 ctx fn s2) /\
    (!fuel k ctx s. terminates (run_blocks fuel ctx fn s) ==>
       run_blocks (fuel + k) ctx fn s = run_blocks fuel ctx fn s) /\
    (!fuel ctx s1 s2. R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_blocks fuel ctx fn s1)
                                (run_blocks fuel ctx fn s2))
  ==>
    lift_result R_ok R_term R_term (run_blocks f1 ctx fn s1)
                             (run_blocks f2 ctx fn s2)
Proof
  rpt strip_tac >>
  qpat_x_assum `!fuel ctx s1 s2. R_ok s1 s2 ==> _`
    (qspecl_then [`f1 + f2`, `ctx`, `s1`, `s2`] mp_tac) >>
  simp[] >> strip_tac >>
  `run_blocks (f1 + f2) ctx fn s1 = run_blocks f1 ctx fn s1` by
    (qpat_x_assum `!fuel k ctx s. terminates _ ==> _`
       (qspecl_then [`f1`, `f2`, `ctx`, `s1`] mp_tac) >> simp[]) >>
  `run_blocks (f1 + f2) ctx fn s2 = run_blocks f2 ctx fn s2` by
    (qpat_x_assum `!fuel k ctx s. terminates _ ==> _`
       (qspecl_then [`f2`, `f1`, `ctx`, `s2`] mp_tac) >>
     `f2 + f1 = f1 + f2` by simp[] >> gvs[]) >>
  gvs[]
QED

(* ===== fwd_terminal_block: terminal block result => fn' terminates ===== *)
(* When run_block on the original side gives a terminal result (non-OK or
   OK-halted), and block sim gives resolving_block_sim on the mid/transformed
   block results, show fn' terminates with matching lift_result. *)

(* lift_result_resolves_to: composing lift_result on the left with resolves_to.
   If r1 ~ r2 (via lift_result) and resolves_to n r2 r3, then resolves_to n r1 r3.
   The key case: when r2 = OK v2 continues (left-continues disjunct), r1 = OK v1
   also continues with the same block (same current_bb from R_ok). *)

Triviality lift_result_resolves_to:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bbs1 bbs2.
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==>
       (s1.vs_halted <=> s2.vs_halted) /\
       s1.vs_current_bb = s2.vs_current_bb /\
       s1.vs_inst_idx = s2.vs_inst_idx) /\
    (!s1 s2. R_ok s1 s2 ==>
       R_ok (s1 with vs_inst_idx := 0) (s2 with vs_inst_idx := 0)) /\
    (!fuel ctx bb s1 s2. MEM bb bbs1 /\ R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx bb s2))
  ==>
    !n r1 r2 r3.
      lift_result R_ok R_term R_term r1 r2 /\
      resolves_to R_ok R_term bbs1 bbs2 n r2 r3 ==>
      resolves_to R_ok R_term bbs1 bbs2 n r1 r3
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `n` >> rpt strip_tac
  >- ( (* n=0: lift_result composition *)
    gvs[resolves_to_def] >>
    irule lift_result_trans_proof >>
    rpt conj_tac >> TRY (FIRST_ASSUM ACCEPT_TAC) >>
    qexists_tac `r2` >> simp[])
  >>
  qpat_x_assum `resolves_to _ _ _ _ (SUC _) _ _` mp_tac >>
  simp[Once resolves_to_def] >> strip_tac >> gvs[] >|
  [(* d1: lift_result r2 r3 *)
   simp[Once resolves_to_def] >> disj1_tac >>
   Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
   gvs[lift_result_def] >> metis_tac[],
   (* d2: left continues from r1 ~ OK v *)
   Cases_on `r1` >> gvs[lift_result_def] >>
   rename1 `R_ok v' v` >>
   `v'.vs_current_bb = v.vs_current_bb /\
    ~v'.vs_halted /\ v'.vs_inst_idx = v.vs_inst_idx` by metis_tac[] >>
   simp[Once resolves_to_def] >> disj2_tac >> disj1_tac >>
   `MEM bb bbs1` by metis_tac[lookup_block_MEM] >>
   rpt gen_tac >>
   `lift_result R_ok R_term R_term
      (run_block fuel ctx' bb v')
      (run_block fuel ctx' bb v)` by
     (first_x_assum irule >> metis_tac[]) >>
   metis_tac[],
   (* d3: right continues — r1 doesn't change *)
   simp[Once resolves_to_def] >> disj2_tac >> disj2_tac >>
   rpt gen_tac >> metis_tac[]]
QED


(* ===== fuel_mono_eq: equal results when both terminate ===== *)

Triviality fuel_mono_eq:
  !fn f1 f2 ctx s.
    terminates (run_blocks f1 ctx fn s) /\
    terminates (run_blocks f2 ctx fn s) /\
    (!fuel k ctx s. terminates (run_blocks fuel ctx fn s) ==>
       run_blocks (fuel + k) ctx fn s = run_blocks fuel ctx fn s) ==>
    run_blocks f1 ctx fn s = run_blocks f2 ctx fn s
Proof
  rpt strip_tac >>
  `f1 <= f2 \/ f2 <= f1` by simp[] >> gvs[] >|
  [`f2 = f1 + (f2 - f1)` by simp[] >> metis_tac[],
   `f1 = f2 + (f1 - f2)` by simp[] >> metis_tac[]]
QED

(* ===== resolve_left_lift: resolves_to left-OK + right-terminal ===== *)
(* When resolves_to has left = OK v (non-halted), right = fn-terminal,
   and run_blocks at fuel f terminates from v, then lift_result holds
   at fuel f directly. Combines resolve_left_fn + fuel_mono_eq. *)

Triviality resolve_left_lift:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) n bbs2 r2 v fn ctx f.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    resolves_to R_ok R_term fn.fn_blocks bbs2 n (OK v) r2 /\
    ~v.vs_halted /\ v.vs_inst_idx = 0 /\
    terminates r2 /\ (!v'. r2 = OK v' ==> v'.vs_halted) /\
    terminates (run_blocks f ctx fn v)
  ==>
    lift_result R_ok R_term R_term (run_blocks f ctx fn v)
      (case r2 of OK v' => Halt v' | other => other)
Proof
  rpt strip_tac >>
  qspecl_then [`R_ok`, `R_term`, `fn.fn_blocks`] mp_tac resolve_left_fn >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`n`, `bbs2`, `r2`, `v`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`fn`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `terminates (run_blocks fuel_l ctx fn v)` >>
  `run_blocks fuel_l ctx fn v = run_blocks f ctx fn v` by
    (irule fuel_mono_eq >> simp[run_blocks_fuel_mono_univ]) >>
  Cases_on `r2` >> gvs[]
QED

(* ===== Helper: left-terminal + right-block → fn' terminates ===== *)
(* When the left block result is fn-terminal (terminates, OK only if halted),
   and we have resolves_to between it and the right block result,
   show fn' from s2 terminates with lift_result. *)

Triviality left_terminal_right_fn:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   fn' bbs1 nn' r1 bb' s2 f ctx.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    resolves_to R_ok R_term bbs1 fn'.fn_blocks nn' r1
      (run_block f ctx bb' s2) /\
    terminates r1 /\ (!v. r1 = OK v ==> v.vs_halted) /\
    lookup_block s2.vs_current_bb fn'.fn_blocks = SOME bb' /\
    s2.vs_inst_idx = 0
  ==>
    ?fuel'. terminates (run_blocks fuel' ctx fn' s2) /\
      ((!v. r1 <> OK v) ==>
        lift_result R_ok R_term R_term r1 (run_blocks fuel' ctx fn' s2)) /\
      (!v. r1 = OK v ==>
        lift_result R_ok R_term R_term (Halt v) (run_blocks fuel' ctx fn' s2))
Proof
  rpt strip_tac >>
  Cases_on `run_block f ctx bb' s2`
  (* OK v2 *)
  >- (
    rename1 `run_block f ctx bb' s2 = OK v2` >>
    Cases_on `v2.vs_halted`
    >- (
      (* OK halted *)
      `!v'. OK v2 = OK v' ==> v'.vs_halted` by fs[] >>
      `lift_result R_ok R_term R_term r1 (OK v2)` by
        metis_tac[resolves_to_terminal_collapses] >>
      qexists_tac `SUC f` >>
      `run_blocks (SUC f) ctx fn' s2 = Halt v2` by
        (irule run_blocks_at_ok_halted_block >> simp[]) >>
      simp[terminates_def] >>
      Cases_on `r1` >> fs[lift_result_def, terminates_def])
    >- (
      (* OK non-halted *)
      `v2.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      qspecl_then [`R_ok`, `R_term`, `fn'.fn_blocks`] mp_tac
        resolve_right_fn >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`nn'`, `bbs1`, `r1`, `v2`] mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`fn'`, `ctx`] mp_tac) >>
      simp[] >> strip_tac >>
      rename1 `terminates (run_blocks fuel2 ctx fn' v2)` >>
      qexists_tac `SUC (MAX f fuel2)` >>
      `!k. run_block (f + k) ctx bb' s2 = run_block f ctx bb' s2` by
        (irule run_block_fuel_mono_lem >> simp[run_blocks_fuel_mono_univ]) >>
      `run_block (MAX f fuel2) ctx bb' s2 = OK v2` by
        (pop_assum (qspec_then `MAX f fuel2 - f` mp_tac) >>
         simp[arithmeticTheory.MAX_DEF]) >>
      `run_blocks (SUC (MAX f fuel2)) ctx fn' s2 =
       run_blocks (MAX f fuel2) ctx fn' v2` by
        (irule run_blocks_ok_block_at >> simp[]) >>
      `run_blocks (MAX f fuel2) ctx fn' v2 =
       run_blocks fuel2 ctx fn' v2` by
        (`MAX f fuel2 = fuel2 + (MAX f fuel2 - fuel2)` by
           simp[arithmeticTheory.MAX_DEF] >>
         first_x_assum (fn th =>
           mp_tac (MATCH_MP run_blocks_fuel_mono th)) >>
         simp[] >> disch_then (qspecl_then [`MAX f fuel2 - fuel2`] mp_tac) >>
         simp[]) >>
      rpt strip_tac >> fs[terminates_def]))
  (* Halt/Abort/IntRet/Error: terminal block, resolves_to collapses *)
  >> (
    qpat_x_assum `resolves_to _ _ _ _ _ _ _`
      (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                            resolves_to_terminal_collapses)) >>
    simp[terminates_def] >> strip_tac >>
    TRY (
      qexists_tac `SUC f` >>
      `run_blocks (SUC f) ctx fn' s2 = run_block f ctx bb' s2` by
        (irule run_blocks_at_non_ok_block >> simp[]) >>
      simp[terminates_def]) >>
    Cases_on `r1` >> fs[lift_result_def, terminates_def])
QED


(* ===== fwd_left_block_terminal: non-OK left block → fn' terminates ===== *)
(* When the left block gives a non-OK result (Halt/Abort/IntRet/Error),
   run_blocks returns that result. Combined with left_terminal_right_fn
   this gives fn' termination + lift_result. Error case is contradiction. *)

Triviality fwd_left_block_terminal:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   fn fn' bbs1 nn' r1 bb bb' s1 s2 f ctx.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s2.vs_current_bb fn'.fn_blocks = SOME bb' /\
    run_block f ctx bb s1 = r1 /\ terminates r1 /\ (!v. r1 <> OK v) /\
    resolves_to R_ok R_term bbs1 fn'.fn_blocks nn' r1
      (run_block f ctx bb' s2) /\
    s1.vs_inst_idx = 0 /\
    s2.vs_inst_idx = 0 /\
    terminates (run_blocks (SUC f) ctx fn s1)
  ==>
    ?fuel'. terminates (run_blocks fuel' ctx fn' s2) /\
      lift_result R_ok R_term R_term (run_blocks (SUC f) ctx fn s1)
        (run_blocks fuel' ctx fn' s2)
Proof
  rpt strip_tac >>
  `run_blocks (SUC f) ctx fn s1 = r1` by
    (irule run_blocks_at_non_ok_block >> simp[] >> metis_tac[]) >>
  `!v. r1 = OK v ==> v.vs_halted` by (rpt strip_tac >> gvs[]) >>
  qspecl_then [`R_ok`, `R_term`, `fn'`, `bbs1`, `nn'`,
    `r1`, `bb'`, `s2`, `f`, `ctx`] mp_tac left_terminal_right_fn >>
  impl_tac >- fs[terminates_def] >>
  strip_tac >>
  qexists_tac `fuel'` >> fs[terminates_def]
QED

(* ===== fwd_term_one_step: single function step ===== *)
(* Given resolves_to nn' between block results at fuel f, and
   terminates (run_blocks (SUC f) ctx fn s1), show fn' terminates.
   Covers: OK/halted (left terminal), OK/non-halted (fuel IH),
   non-OK (fwd_left_block_terminal), Error (contradiction). *)

Triviality fwd_term_one_step:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   fn fn' bb bb' nn' s1 s2 f ctx.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    lookup_block s1.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block s2.vs_current_bb fn'.fn_blocks = SOME bb' /\
    MEM bb fn.fn_blocks /\
    resolves_to R_ok R_term fn.fn_blocks fn'.fn_blocks nn'
      (run_block f ctx bb s1) (run_block f ctx bb' s2) /\
    s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    terminates (run_blocks (SUC f) ctx fn s1) /\
    (* fuel IH: at lower fuel, with any resolves_to level *)
    (!nn2 v v'.
       resolves_to R_ok R_term fn.fn_blocks fn'.fn_blocks nn2 (OK v) (OK v') /\
       v.vs_inst_idx = 0 /\ ~v.vs_halted /\
       v'.vs_inst_idx = 0 /\ ~v'.vs_halted /\
       terminates (run_blocks f ctx fn v) ==>
       ?fuel2. terminates (run_blocks fuel2 ctx fn' v') /\
         lift_result R_ok R_term R_term (run_blocks f ctx fn v)
           (run_blocks fuel2 ctx fn' v'))
  ==>
    ?fuel'. terminates (run_blocks fuel' ctx fn' s2) /\
      lift_result R_ok R_term R_term (run_blocks (SUC f) ctx fn s1)
        (run_blocks fuel' ctx fn' s2)
Proof
  rpt strip_tac >>
  Cases_on `run_block f ctx bb s1`
  >- (
    (* OK v *)
    rename1 `_ = OK v` >>
    Cases_on `v.vs_halted`
    >- (
      (* OK-halted: fn = Halt v. Left is fn-terminal. *)
      `run_blocks (SUC f) ctx fn s1 = Halt v` by
        (irule run_blocks_at_ok_halted_block >> simp[]) >>
      `!v'. OK v = OK v' ==> v'.vs_halted` by fs[] >>
      qspecl_then [`R_ok`, `R_term`, `fn'`, `fn.fn_blocks`, `nn'`,
        `OK v`, `bb'`, `s2`, `f`, `ctx`] mp_tac left_terminal_right_fn >>
      impl_tac >- fs[terminates_def] >>
      strip_tac >>
      qexists_tac `fuel'` >> simp[terminates_def] >>
      rpt strip_tac >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[]
    )
    >- (
      (* OK non-halted: fn continues, use fuel IH *)
      `run_blocks (SUC f) ctx fn s1 = run_blocks f ctx fn v` by
        (irule run_blocks_ok_block_at >> simp[]) >>
      `v.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      `terminates (run_blocks f ctx fn v)` by fs[terminates_def] >>
      Cases_on `run_block f ctx bb' s2`
      >- (
        (* Right OK v' *)
        rename1 `_ = OK v'` >>
        Cases_on `v'.vs_halted`
        >- (
          (* Right OK v' halted: fn' = Halt v', resolve_left_lift for lift_result *)
          `run_blocks (SUC f) ctx fn' s2 = Halt v'` by
            (irule run_blocks_at_ok_halted_block >> simp[]) >>
          qexists_tac `SUC f` >> simp[terminates_def] >>
          qspecl_then [`R_ok`, `R_term`, `nn'`, `fn'.fn_blocks`,
            `OK v'`, `v`, `fn`, `ctx`, `f`] mp_tac resolve_left_lift >>
          impl_tac >- simp[terminates_def] >>
          simp[]
        )
        >- (
          `v'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
          first_x_assum (qspecl_then [`nn'`, `v`, `v'`] mp_tac) >>
          simp[] >>
          strip_tac >>
          rename1 `terminates (run_blocks fuel2 ctx fn' v')` >>
          qexists_tac `SUC (MAX f fuel2)` >>
          `!k. run_block (f + k) ctx bb' s2 =
           run_block f ctx bb' s2` by (
            irule run_block_fuel_mono_lem >> simp[run_blocks_fuel_mono_univ]) >>
          `run_block (MAX f fuel2) ctx bb' s2 = OK v'` by
            (pop_assum (qspec_then `MAX f fuel2 - f` mp_tac) >>
             simp[arithmeticTheory.MAX_DEF]) >>
          `run_blocks (SUC (MAX f fuel2)) ctx fn' s2 =
           run_blocks (MAX f fuel2) ctx fn' v'` by
            (irule run_blocks_ok_block_at >> simp[]) >>
          `run_blocks (MAX f fuel2) ctx fn' v' =
           run_blocks fuel2 ctx fn' v'` by
            (`MAX f fuel2 = fuel2 + (MAX f fuel2 - fuel2)` by
               simp[arithmeticTheory.MAX_DEF] >>
             first_x_assum (fn th =>
               mp_tac (MATCH_MP run_blocks_fuel_mono th)) >>
             simp[] >> disch_then (qspecl_then [`MAX f fuel2 - fuel2`] mp_tac) >>
             simp[]) >>
          rpt strip_tac >> fs[terminates_def]
        )
      )
      (* Right Halt/Abort/IntRet: fn' = block result, use resolve_left_lift *)
      >- (
        `run_blocks (SUC f) ctx fn' s2 = run_block f ctx bb' s2` by
          (irule run_blocks_at_non_ok_block >> simp[]) >>
        qexists_tac `SUC f` >> simp[terminates_def] >>
        qspecl_then [`R_ok`, `R_term`, `nn'`, `fn'.fn_blocks`,
          `run_block f ctx bb' s2`, `v`, `fn`, `ctx`, `f`]
          mp_tac resolve_left_lift >>
        impl_tac >- simp[terminates_def] >>
        simp[])
      >- (
        `run_blocks (SUC f) ctx fn' s2 = run_block f ctx bb' s2` by
          (irule run_blocks_at_non_ok_block >> simp[]) >>
        qexists_tac `SUC f` >> simp[terminates_def] >>
        qspecl_then [`R_ok`, `R_term`, `nn'`, `fn'.fn_blocks`,
          `run_block f ctx bb' s2`, `v`, `fn`, `ctx`, `f`]
          mp_tac resolve_left_lift >>
        impl_tac >- simp[terminates_def] >>
        simp[])
      >- (
        `run_blocks (SUC f) ctx fn' s2 = run_block f ctx bb' s2` by
          (irule run_blocks_at_non_ok_block >> simp[]) >>
        qexists_tac `SUC f` >> simp[terminates_def] >>
        qspecl_then [`R_ok`, `R_term`, `nn'`, `fn'.fn_blocks`,
          `run_block f ctx bb' s2`, `v`, `fn`, `ctx`, `f`]
          mp_tac resolve_left_lift >>
        impl_tac >- simp[terminates_def] >>
        simp[])
      (* Right Error: contradiction via resolve_left_fn_error *)
      >- (
        rename1 `_ = Error e` >>
        `~terminates (run_blocks f ctx fn v)` by (
          qspecl_then [`nn'`, `R_ok`, `R_term`, `fn`, `fn'.fn_blocks`, `e`, `v`]
            mp_tac resolve_left_fn_error >>
          impl_tac >- simp[] >>
          disch_then (qspecl_then [`ctx`, `f`] mp_tac) >> simp[]) >>
        fs[terminates_def])
    )
  )
  (* Halt/Abort/IntRet: use fwd_left_block_terminal *)
  >> (TRY (
    qspecl_then [`R_ok`, `R_term`, `fn`, `fn'`, `fn.fn_blocks`, `nn'`,
      `run_block f ctx bb s1`, `bb`, `bb'`, `s1`, `s2`, `f`, `ctx`]
      mp_tac fwd_left_block_terminal >>
    impl_tac >- simp[terminates_def] >>
    strip_tac >> qexists_tac `fuel'` >> fs[terminates_def] >> NO_TAC) >>
  (* Error: contradiction with terminates *)
  `run_blocks (SUC f) ctx fn s1 = run_block f ctx bb s1` by
    (irule run_blocks_at_non_ok_block >> simp[]) >>
  fs[terminates_def])
QED

(* ===== D2 helper: left terminal wrapper ===== *)
(* When left block result is terminal (non-OK, or OK-halted), wraps
   resolve_right_fn into a clean lift_result conclusion. *)

Triviality fwd_left_terminal:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn1 fn2 bb s1 s2 nn f ctx.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    lookup_block s1.vs_current_bb fn1.fn_blocks = SOME bb /\
    s1.vs_inst_idx = 0 /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    resolves_to R_ok R_term fn1.fn_blocks fn2.fn_blocks nn
      (run_block f ctx bb s1) (OK s2) /\
    terminates (run_block f ctx bb s1) /\
    (!v. run_block f ctx bb s1 = OK v ==> v.vs_halted)
  ==>
    ?fuel'. terminates (run_blocks fuel' ctx fn2 s2) /\
      lift_result R_ok R_term R_term (run_blocks (SUC f) ctx fn1 s1)
        (run_blocks fuel' ctx fn2 s2)
Proof
  rpt strip_tac >>
  qspecl_then [`R_ok`, `R_term`, `fn2.fn_blocks`] mp_tac
    resolve_right_fn >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`nn`, `fn1.fn_blocks`,
    `run_block f ctx bb s1`, `s2`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (qspecl_then [`fn2`, `ctx`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `fuel` >> simp[] >>
  Cases_on `run_block f ctx bb s1`
  >- (
    rename1 `_ = OK v'` >>
    `v'.vs_halted` by metis_tac[] >>
    `run_blocks (SUC f) ctx fn1 s1 = Halt v'` by
      (irule run_blocks_at_ok_halted_block >> simp[]) >>
    simp[] >> metis_tac[]
  )
  (* Halt/Abort/IntRet: fn1 = block result, then metis_tac *)
  >> (TRY (
    `run_blocks (SUC f) ctx fn1 s1 = run_block f ctx bb s1` by
      (irule run_blocks_at_non_ok_block >> simp[]) >>
    simp[] >> metis_tac[] >> NO_TAC))
QED

(* ===== D2 helper: left resolves one step =====  *)
(* SUC nn case, disjunct 2: left-side OK state takes one block step.
   resolves_to nn (run_block f ctx bb s1) (OK s2).
   Use fuel IH (at f < SUC f) to handle OK-non-halted;
   fwd_left_terminal handles all terminal cases. *)

Triviality gen_term_lift_left_step:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn1 fn2 bb s1 s2 f nn ctx.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    lookup_block s1.vs_current_bb fn1.fn_blocks = SOME bb /\
    MEM bb fn1.fn_blocks /\
    s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    resolves_to R_ok R_term fn1.fn_blocks fn2.fn_blocks nn
      (run_block f ctx bb s1) (OK s2) /\
    terminates (run_blocks (SUC f) ctx fn1 s1) /\
    (* fuel IH: at fuel f, any nn *)
    (!nn2 v v'.
       resolves_to R_ok R_term fn1.fn_blocks fn2.fn_blocks nn2 (OK v) (OK v') /\
       v.vs_inst_idx = 0 /\ ~v.vs_halted /\
       v'.vs_inst_idx = 0 /\ ~v'.vs_halted /\
       terminates (run_blocks f ctx fn1 v) ==>
       ?fuel2. terminates (run_blocks fuel2 ctx fn2 v') /\
         lift_result R_ok R_term R_term (run_blocks f ctx fn1 v)
           (run_blocks fuel2 ctx fn2 v'))
  ==>
    ?fuel'. terminates (run_blocks fuel' ctx fn2 s2) /\
      lift_result R_ok R_term R_term (run_blocks (SUC f) ctx fn1 s1)
        (run_blocks fuel' ctx fn2 s2)
Proof
  rpt strip_tac >>
  Cases_on `run_block f ctx bb s1`
  >- (
    (* OK v' *)
    rename1 `_ = OK v'` >>
    Cases_on `v'.vs_halted`
    >- (irule fwd_left_terminal >> simp[terminates_def] >> metis_tac[])
    >- (
      (* OK non-halted: fuel IH at f *)
      `run_blocks (SUC f) ctx fn1 s1 = run_blocks f ctx fn1 v'` by
        (irule run_blocks_ok_block_at >> simp[]) >>
      `terminates (run_blocks f ctx fn1 v')` by fs[terminates_def] >>
      `v'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      qpat_x_assum `!nn2 v v'. resolves_to _ _ _ _ nn2 (OK v) (OK v') /\ _ ==> _`
        (qspecl_then [`nn`, `v'`, `s2`] mp_tac) >> simp[]
    )
  )
  (* Halt/Abort/IntRet/Error *)
  >> (TRY (irule fwd_left_terminal >> simp[terminates_def] >>
           metis_tac[] >> NO_TAC) >>
  `run_blocks (SUC f) ctx fn1 s1 = run_block f ctx bb s1` by
    (irule run_blocks_at_non_ok_block >> simp[]) >>
  fs[terminates_def])
QED

(* ===== D3 helper: right terminal wrapper ===== *)
(* When right block result is terminal (non-OK, or OK-halted),
   wraps resolve_left_lift + fuel independence into a clean conclusion.
   Mirror of fwd_left_terminal. *)

Triviality fwd_right_terminal:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn1 fn2 bb s1 s2 nn fuel ctx.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    lookup_block s2.vs_current_bb fn2.fn_blocks = SOME bb /\
    s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    (!fuel' ctx'. resolves_to R_ok R_term fn1.fn_blocks fn2.fn_blocks nn
      (OK s1) (run_block fuel' ctx' bb (s2 with vs_inst_idx := 0))) /\
    terminates (run_blocks fuel ctx fn1 s1) /\
    terminates (run_block 0 ctx bb s2) /\
    (!v. run_block 0 ctx bb s2 = OK v ==> v.vs_halted)
  ==>
    ?fuel'. terminates (run_blocks fuel' ctx fn2 s2) /\
      lift_result R_ok R_term R_term (run_blocks fuel ctx fn1 s1)
        (run_blocks fuel' ctx fn2 s2)
Proof
  rpt strip_tac >>
  `s2 with vs_inst_idx := 0 = s2` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  (* Block is fuel-independent: no Error at fuel 0 *)
  `!e. run_block 0 ctx bb s2 <> Error e` by (
    spose_not_then strip_assume_tac >> fs[] >>
    first_assum (qspecl_then [`0`, `ctx`] assume_tac) >>
    qspecl_then [`nn`, `R_ok`, `R_term`, `fn1`, `fn2.fn_blocks`,
      `e`, `s1`] mp_tac resolve_left_fn_error >>
    simp[] >> metis_tac[]) >>
  `!k. run_block (0 + k) ctx bb s2 = run_block 0 ctx bb s2` by
    (irule run_block_fuel_mono_lem >> simp[run_blocks_fuel_mono_univ]) >>
  fs[] >>
  first_assum (qspecl_then [`0`, `ctx`] assume_tac) >>
  qexists_tac `SUC 0` >>
  Cases_on `run_block 0 ctx bb s2`
  >- (
    rename1 `_ = OK v'` >>
    `v'.vs_halted` by metis_tac[] >>
    `run_blocks (SUC 0) ctx fn2 s2 = Halt v'` by
      (irule run_blocks_at_ok_halted_block >> simp[]) >>
    simp[terminates_def] >>
    qspecl_then [`R_ok`, `R_term`, `nn`, `fn2.fn_blocks`,
      `OK v'`, `s1`, `fn1`, `ctx`, `fuel`] mp_tac resolve_left_lift >>
    impl_tac >- simp[terminates_def] >-
    simp[]
  )
  (* Halt/Abort/IntRet/Error *)
  >> (TRY (
    `run_blocks (SUC 0) ctx fn2 s2 = run_block 0 ctx bb s2` by
      (irule run_blocks_at_non_ok_block >> simp[]) >>
    simp[terminates_def] >>
    qspecl_then [`R_ok`, `R_term`, `nn`, `fn2.fn_blocks`,
      `run_block 0 ctx bb s2`, `s1`, `fn1`, `ctx`, `fuel`]
      mp_tac resolve_left_lift >>
    impl_tac >- simp[terminates_def] >-
    simp[] >> NO_TAC) >>
  fs[terminates_def])
QED

(* ===== D3 helper: right resolves one step ===== *)
(* SUC nn case, disjunct 3: right-side OK state takes one resolution block step.
   resolves_to nn (OK s1) (run_block fuel ctx bb s2).
   OK-non-halted uses nn IH; terminal uses fwd_right_terminal. *)

Triviality gen_term_lift_right_step:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn1 fn2 bb s1 s2 fuel nn ctx.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted)) /\
    lookup_block s2.vs_current_bb fn2.fn_blocks = SOME bb /\
    s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
    s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
    (!fuel' ctx'. resolves_to R_ok R_term fn1.fn_blocks fn2.fn_blocks nn
      (OK s1) (run_block fuel' ctx' bb (s2 with vs_inst_idx := 0))) /\
    terminates (run_blocks fuel ctx fn1 s1) /\
    (* nn IH: at same fuel, lower nn *)
    (!v v'.
       resolves_to R_ok R_term fn1.fn_blocks fn2.fn_blocks nn (OK v) (OK v') /\
       v.vs_inst_idx = 0 /\ ~v.vs_halted /\
       v'.vs_inst_idx = 0 /\ ~v'.vs_halted /\
       terminates (run_blocks fuel ctx fn1 v) ==>
       ?fuel2. terminates (run_blocks fuel2 ctx fn2 v') /\
         lift_result R_ok R_term R_term (run_blocks fuel ctx fn1 v)
           (run_blocks fuel2 ctx fn2 v'))
  ==>
    ?fuel'. terminates (run_blocks fuel' ctx fn2 s2) /\
      lift_result R_ok R_term R_term (run_blocks fuel ctx fn1 s1)
        (run_blocks fuel' ctx fn2 s2)
Proof
  rpt strip_tac >>
  `s2 with vs_inst_idx := 0 = s2` by simp[] >>
  pop_assum SUBST_ALL_TAC >>
  (* Establish fuel independence *)
  `!e. run_block 0 ctx bb s2 <> Error e` by (
    spose_not_then strip_assume_tac >> fs[] >>
    first_assum (qspecl_then [`0`, `ctx`] assume_tac) >>
    qspecl_then [`nn`, `R_ok`, `R_term`, `fn1`, `fn2.fn_blocks`,
      `e`, `s1`] mp_tac resolve_left_fn_error >>
    simp[] >> metis_tac[]) >>
  `!k. run_block (0 + k) ctx bb s2 = run_block 0 ctx bb s2` by
    (irule run_block_fuel_mono_lem >> simp[run_blocks_fuel_mono_univ]) >>
  fs[] >>
  Cases_on `run_block 0 ctx bb s2`
  >- (
    rename1 `_ = OK v'` >>
    Cases_on `v'.vs_halted`
    >- (
      irule fwd_right_terminal >>
      simp[terminates_def, inst_idx_0_lemma] >> metis_tac[]
    )
    >- (
      (* OK non-halted: nn IH *)
      `v'.vs_inst_idx = 0` by metis_tac[run_block_OK_inst_idx_0] >>
      qpat_x_assum `!v v'. resolves_to _ _ _ _ _ (OK v) (OK v') /\ _ ==> _`
        (qspecl_then [`s1`, `v'`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >>
      strip_tac >>
      rename1 `terminates (run_blocks fuel2 ctx fn2 v')` >>
      qexists_tac `SUC fuel2` >>
      `run_blocks (SUC fuel2) ctx fn2 s2 =
       run_blocks fuel2 ctx fn2 v'` by
        (irule run_blocks_ok_block_at >> simp[]) >>
      fs[terminates_def]
    )
  )
  (* Halt/Abort/IntRet/Error *)
  >> (TRY (irule fwd_right_terminal >>
           simp[terminates_def, inst_idx_0_lemma] >>
           metis_tac[] >> NO_TAC))
QED

(* ===== Generalized termination lifting ===== *)
(* Given resolves_to nn (OK s1) (OK s2) and fn1 terminates at s1,
   show fn2 terminates at s2 with lift_result.
   Generalized: no function_map_transform dependency. The caller provides
   a "block correspondence" that for any block lookup in fn1 with R_ok-related
   states, yields a corresponding fn2 block with resolving_block_sim. *)

Theorem gen_term_lift:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn1 fn2.
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
       s1.vs_current_bb = s2.vs_current_bb /\
       s1.vs_inst_idx = s2.vs_inst_idx) /\
    (!s1 s2. R_ok s1 s2 ==>
       R_ok (s1 with vs_inst_idx := 0) (s2 with vs_inst_idx := 0)) /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (* Block correspondence *)
    (!lbl bb fuel ctx s1 s2.
       lookup_block lbl fn1.fn_blocks = SOME bb /\
       MEM bb fn1.fn_blocks /\
       R_ok s1 s2 /\
       s1.vs_current_bb = lbl /\ s2.vs_current_bb = lbl /\
       s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
       ~s1.vs_halted /\ ~s2.vs_halted ==>
       ?bb2. lookup_block lbl fn2.fn_blocks = SOME bb2 /\
         resolving_block_sim R_ok R_term fn1.fn_blocks fn2.fn_blocks
           (run_block fuel ctx bb s1) (run_block fuel ctx bb2 s2))
  ==>
    !fuel nn ctx s1 s2.
      resolves_to R_ok R_term fn1.fn_blocks fn2.fn_blocks nn (OK s1) (OK s2) /\
      s1.vs_inst_idx = 0 /\ ~s1.vs_halted /\
      s2.vs_inst_idx = 0 /\ ~s2.vs_halted /\
      terminates (run_blocks fuel ctx fn1 s1) ==>
      ?fuel'. terminates (run_blocks fuel' ctx fn2 s2) /\
        lift_result R_ok R_term R_term
          (run_blocks fuel ctx fn1 s1)
          (run_blocks fuel' ctx fn2 s2)
Proof
  rpt gen_tac >> strip_tac >>
  (* Main induction: completeInduct on fuel, then Induct on nn *)
  completeInduct_on `fuel` >> Induct_on `nn`
  >- (
    (* === nn = 0: resolves_to 0 = lift_result = R_ok s1 s2 === *)
    rpt strip_tac >>
    (* Decompose resolves_to 0 via mp_tac to avoid rewriting block correspondence *)
    qpat_x_assum `resolves_to _ _ _ _ 0 _ _` mp_tac >>
    simp[resolves_to_def, lift_result_def] >> strip_tac >>
    (* Now we have R_ok s1 s2 without damaging block correspondence *)
    `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
    `s2.vs_inst_idx = 0` by metis_tac[] >>
    Cases_on `fuel`
    >- (qpat_x_assum `terminates _` mp_tac >>
        simp[Once run_blocks_def, terminates_def])
    >>
    rename1 `SUC f` >>
    Cases_on `lookup_block s1.vs_current_bb fn1.fn_blocks`
    >- (qpat_x_assum `terminates _` mp_tac >>
        simp[Once run_blocks_def, terminates_def])
    >>
    rename1 `_ = SOME bb` >>
    `MEM bb fn1.fn_blocks` by metis_tac[lookup_block_MEM] >>
    (* Use block correspondence to get fn2 block and resolving_block_sim *)
    `?bb2. lookup_block s1.vs_current_bb fn2.fn_blocks = SOME bb2 /\
       resolving_block_sim R_ok R_term fn1.fn_blocks fn2.fn_blocks
         (run_block f ctx bb s1) (run_block f ctx bb2 s2)` by
      (first_x_assum (qspecl_then
         [`s1.vs_current_bb`, `bb`, `f`, `ctx`, `s1`, `s2`] mp_tac) >>
       simp[]) >>
    (* Extract resolves_to from resolving_block_sim *)
    fs[resolving_block_sim_def] >>
    rename1 `resolves_to _ _ _ _ nn' _ _` >>
    (* Apply fwd_term_one_step via forward proof *)
    `lookup_block s2.vs_current_bb fn2.fn_blocks = SOME bb2` by
      metis_tac[] >>
    qspecl_then [`R_ok`, `R_term`, `fn1`, `fn2`, `bb`, `bb2`, `nn'`,
      `s1`, `s2`, `f`, `ctx`] mp_tac fwd_term_one_step >>
    impl_tac >- (
      simp[] >> rpt strip_tac >>
      first_x_assum (qspec_then `f` mp_tac) >> simp[] >>
      disch_then (qspecl_then [`nn2`, `ctx`, `v`, `v'`] mp_tac) >> simp[]) >>
    strip_tac >> qexists_tac `fuel'` >> simp[]
  )
  >- (
    (* === SUC nn === *)
    rpt strip_tac >>
    qpat_x_assum `resolves_to _ _ _ _ (SUC _) _ _` mp_tac >>
    PURE_ONCE_REWRITE_TAC[resolves_to_def] >> strip_tac
    >- (
      (* D1: lift_result => reduce to nn case via resolves_to_mono *)
      `resolves_to R_ok R_term fn1.fn_blocks fn2.fn_blocks nn
         (OK s1) (OK s2)` by (
        qspecl_then [`R_ok`, `R_term`, `fn1.fn_blocks`, `fn2.fn_blocks`,
          `0`, `nn`] mp_tac resolves_to_mono_proof >>
        simp[resolves_to_def, lift_result_def]) >>
      first_assum (qspecl_then [`ctx`, `s1`, `s2`] mp_tac) >> simp[]
    )
    >- (
      (* D2: left-resolves. OK s1 = OK v => s1 = v.
         lookup_block s1.vs_current_bb fn1.fn_blocks = SOME bb.
         !fuel ctx. resolves_to nn (run_block fuel ctx bb s1) (OK s2).
         Use gen_term_lift_left_step with fuel IH at f. *)
      qpat_x_assum `OK _ = OK _` (SUBST_ALL_TAC o SYM o
        SIMP_RULE std_ss [exec_result_11]) >>
      `s1 with vs_inst_idx := 0 = s1` by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      `MEM bb fn1.fn_blocks` by metis_tac[lookup_block_MEM] >>
      Cases_on `fuel`
      >- (qpat_x_assum `terminates _` mp_tac >>
          simp[Once run_blocks_def, terminates_def])
      >- (
        rename1 `SUC f` >>
        (* Instantiate resolution at f, ctx *)
        qpat_x_assum `!fuel' ctx'. resolves_to _ _ _ _ _ _ _`
          (qspecl_then [`f`, `ctx`] assume_tac) >>
        qspecl_then [`R_ok`, `R_term`, `fn1`, `fn2`, `bb`, `s1`, `s2`,
          `f`, `nn`, `ctx`] mp_tac gen_term_lift_left_step >>
        impl_tac >- (
          simp[] >> rpt strip_tac >>
          first_x_assum (qspec_then `f` mp_tac) >> simp[] >>
          disch_then (qspecl_then [`nn2`, `ctx`, `v`, `v'`] mp_tac) >> simp[]
        ) >>
        strip_tac >> qexists_tac `fuel'` >> simp[]
      )
    )
    >- (
      (* D3: right-resolves. OK s2 = OK v => s2 = v.
         lookup_block s2.vs_current_bb fn2.fn_blocks = SOME bb.
         !fuel ctx. resolves_to nn (OK s1) (run_block fuel ctx bb s2).
         Use gen_term_lift_right_step with nn IH. *)
      qpat_x_assum `OK _ = OK _` (SUBST_ALL_TAC o SYM o
        SIMP_RULE std_ss [exec_result_11]) >>
      `s2 with vs_inst_idx := 0 = s2` by simp[] >>
      pop_assum SUBST_ALL_TAC >>
      qspecl_then [`R_ok`, `R_term`, `fn1`, `fn2`, `bb`, `s1`, `s2`,
        `fuel`, `nn`, `ctx`] mp_tac gen_term_lift_right_step >>
      impl_tac >- (
        simp[] >> rpt strip_tac >>
        first_assum (qspecl_then [`ctx`, `v`, `v'`] mp_tac) >> simp[]
      ) >>
      strip_tac >> qexists_tac `fuel'` >> simp[]
    )
  )
QED

(* ===== resolves_to_flip: swap left/right in resolves_to ===== *)

Triviality resolves_to_flip:
  !R_ok R_term bbs1 bbs2 n r1 r2.
    resolves_to R_ok R_term bbs1 bbs2 n r1 r2 ==>
    resolves_to (\a b. R_ok b a) (\a b. R_term b a) bbs2 bbs1 n r2 r1
Proof
  Induct_on `n`
  >- (rw[resolves_to_def] >>
      Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def])
  >- (
    rpt strip_tac >>
    qpat_x_assum `resolves_to _ _ _ _ (SUC _) _ _` mp_tac >>
    PURE_ONCE_REWRITE_TAC[resolves_to_def] >> strip_tac
    >- (simp[resolves_to_def] >>
        Cases_on `r1` >> Cases_on `r2` >> fs[lift_result_def])
    >- (simp[resolves_to_def] >> disj2_tac >> disj2_tac >> metis_tac[])
    >- (simp[resolves_to_def] >> disj1_tac >> disj2_tac >> metis_tac[])
  )
QED


(* ===== Forward lift: fn terminates → fn' terminates + lift_result ===== *)

Triviality fwd_lift:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn bt.
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s.
       MEM bb fn.fn_blocks /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
       resolving_block_sim R_ok R_term fn.fn_blocks fn'.fn_blocks
         (run_block fuel ctx bb s) (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ ~s.vs_halted /\
      terminates (run_blocks fuel ctx fn s) ==>
      ?fuel'. terminates (run_blocks fuel' ctx fn' s) /\
        lift_result R_ok R_term R_term
          (run_blocks fuel ctx fn s)
          (run_blocks fuel' ctx fn' s)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields) >> simp[]) >>
  `!s1 s2. R_ok s1 s2 ==>
     R_ok (s1 with vs_inst_idx := 0) (s2 with vs_inst_idx := 0)` by
    (rpt strip_tac >> irule vsr_inst_idx_R_ok >> metis_tac[]) >>
  `!s. R_ok s s` by (rpt strip_tac >> irule vsr_R_ok_refl >> metis_tac[]) >>
  `!fuel ctx bb s1 s2. MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                              (run_block fuel ctx bb s2)` by (
    rpt strip_tac >>
    irule run_block_preserves_R_helper >> metis_tac[]
  ) >>
  (* Establish block correspondence as standalone fact *)
  `!lbl bb fuel ctx s1 s2.
     lookup_block lbl fn.fn_blocks = SOME bb /\ MEM bb fn.fn_blocks /\
     R_ok s1 s2 /\ s1.vs_current_bb = lbl /\ s2.vs_current_bb = lbl /\
     s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
     ~s1.vs_halted /\ ~s2.vs_halted ==>
     ?bb2. lookup_block lbl (function_map_transform bt fn).fn_blocks = SOME bb2 /\
       resolving_block_sim R_ok R_term fn.fn_blocks
         (function_map_transform bt fn).fn_blocks
         (run_block fuel ctx bb s1) (run_block fuel ctx bb2 s2)` by (
    rpt strip_tac >>
    qexists_tac `bt bb` >>
    conj_tac
    >- simp[function_map_transform_def, lookup_block_map_proof]
    >- (
      `lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
         (run_block fuel ctx bb s2)` by (
        qpat_x_assum `!f c b a b'. MEM _ _ /\ R_ok _ _ ==> lift_result _ _ _ _ _`
          (irule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
        simp[]
      ) >>
      qpat_x_assum `!b f c s. MEM _ _ /\ _ ==> resolving_block_sim _ _ _ _ _ _`
        (qspecl_then [`bb`, `fuel`, `ctx`, `s2`] mp_tac) >>
      simp[] >> strip_tac >>
      fs[resolving_block_sim_def] >>
      qexists_tac `n` >>
      irule (REWRITE_RULE [GSYM AND_IMP_INTRO] lift_result_resolves_to) >>
      metis_tac[]
    )
  ) >>
  (* Apply gen_term_lift *)
  qspecl_then [`R_ok`, `R_term`, `fn`, `function_map_transform bt fn`]
    mp_tac gen_term_lift >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`fuel`, `0`, `ctx`, `s`, `s`] mp_tac) >>
  simp[resolves_to_def, lift_result_def]
QED

(* ===== Backward lift: fn' terminates → fn terminates + lift_result ===== *)

Triviality bwd_lift:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn bt.
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s.
       MEM bb fn.fn_blocks /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
       resolving_block_sim R_ok R_term fn.fn_blocks fn'.fn_blocks
         (run_block fuel ctx bb s) (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\ ~s.vs_halted /\
      terminates (run_blocks fuel ctx fn' s) ==>
      ?fuel'. terminates (run_blocks fuel' ctx fn s) /\
        lift_result R_ok R_term R_term
          (run_blocks fuel' ctx fn s)
          (run_blocks fuel ctx fn' s)
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  (* Derive properties from valid_state_rel *)
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[]) >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields) >> simp[]) >>
  `!s1 s2. R_ok s1 s2 ==>
     R_ok (s1 with vs_inst_idx := 0) (s2 with vs_inst_idx := 0)` by
    (rpt strip_tac >> irule vsr_inst_idx_R_ok >> metis_tac[]) >>
  `!s. R_ok s s` by (rpt strip_tac >> irule vsr_R_ok_refl >> metis_tac[]) >>
  `!fuel ctx bb s1 s2. MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                              (run_block fuel ctx bb s2)` by (
    rpt strip_tac >>
    irule run_block_preserves_R_helper >> metis_tac[]
  ) >>
  (* Establish backward block correspondence as standalone fact *)
  `!lbl bb2 fuel ctx s1 s2.
     lookup_block lbl (function_map_transform bt fn).fn_blocks = SOME bb2 /\
     MEM bb2 (function_map_transform bt fn).fn_blocks /\
     R_ok s2 s1 /\ s1.vs_current_bb = lbl /\ s2.vs_current_bb = lbl /\
     s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
     ~s1.vs_halted /\ ~s2.vs_halted ==>
     ?bb_orig. lookup_block lbl fn.fn_blocks = SOME bb_orig /\
       resolving_block_sim (\a b. R_ok b a) (\a b. R_term b a)
         (function_map_transform bt fn).fn_blocks fn.fn_blocks
         (run_block fuel ctx bb2 s1) (run_block fuel ctx bb_orig s2)` by (
    rpt strip_tac >>
    (* Extract original block from fn' lookup *)
    `?bb. lookup_block lbl fn.fn_blocks = SOME bb /\ bt bb = bb2` by (
      qpat_x_assum `lookup_block _ (function_map_transform _ _).fn_blocks = _` mp_tac >>
      simp[function_map_transform_def, lookup_block_map_proof] >>
      Cases_on `lookup_block lbl fn.fn_blocks` >> simp[]
    ) >>
    qexists_tac `bb` >> simp[] >>
    `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
    (* Triangle: lift_result R_ok R_term R_term (bb s2) (bb s1) *)
    `lift_result R_ok R_term R_term (run_block fuel ctx bb s2)
       (run_block fuel ctx bb s1)` by (
      qpat_x_assum `!f c b a b'. MEM _ _ /\ R_ok _ _ ==> lift_result _ _ _ _ _`
        (irule o REWRITE_RULE [GSYM AND_IMP_INTRO]) >>
      simp[]
    ) >>
    (* Block sim at s1: resolving_block_sim (bb s1) ((bt bb) s1) *)
    qpat_x_assum `!b f c s. MEM _ _ /\ _ ==> resolving_block_sim _ _ _ _ _ _`
      (qspecl_then [`bb`, `fuel`, `ctx`, `s1`] mp_tac) >>
    simp[] >> strip_tac >>
    (* Compose: resolves_to (bb s2) ((bt bb) s1) *)
    fs[resolving_block_sim_def] >>
    `resolves_to R_ok R_term fn.fn_blocks
       (function_map_transform bt fn).fn_blocks n
       (run_block fuel ctx bb s2) (run_block fuel ctx (bt bb) s1)` by (
      irule (REWRITE_RULE [GSYM AND_IMP_INTRO] lift_result_resolves_to) >>
      metis_tac[]
    ) >>
    (* Flip *)
    `resolves_to (\a b. R_ok b a) (\a b. R_term b a)
       (function_map_transform bt fn).fn_blocks fn.fn_blocks n
       (run_block fuel ctx (bt bb) s1) (run_block fuel ctx bb s2)` by
      metis_tac[resolves_to_flip] >>
    metis_tac[]
  ) >>
  (* Apply gen_term_lift with flipped relations: fn' -> fn *)
  qspecl_then [`\a b. R_ok b a`, `\a b. R_term b a`,
               `function_map_transform bt fn`, `fn`]
    mp_tac gen_term_lift >>
  BETA_TAC >>
  simp[] >>
  impl_tac >- metis_tac[] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`fuel`, `0`, `ctx`, `s`, `s`] mp_tac) >>
  simp[resolves_to_def, lift_result_def] >> strip_tac >>
  qexists_tac `fuel'` >> simp[] >>
  qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
  Cases_on `run_blocks fuel' ctx fn s` >>
  Cases_on `run_blocks fuel ctx (function_map_transform bt fn) s` >>
  simp[lift_result_def]
QED

(* ===== Main theorem ===== *)

Theorem resolving_block_sim_function_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn bt.
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s.
       MEM bb fn.fn_blocks /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
       resolving_block_sim R_ok R_term fn.fn_blocks fn'.fn_blocks
         (run_block fuel ctx bb s)
         (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!fuel k ctx s.
       terminates (run_blocks fuel ctx fn s) ==>
       run_blocks (fuel + k) ctx fn s = run_blocks fuel ctx fn s) /\
    (!fuel k ctx s.
       terminates (run_blocks fuel ctx fn' s) ==>
       run_blocks (fuel + k) ctx fn' s = run_blocks fuel ctx fn' s)
  ==>
    !ctx s. s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ((?fuel. terminates (run_blocks fuel ctx fn s)) <=>
     (?fuel'. terminates (run_blocks fuel' ctx fn' s))) /\
    (!fuel fuel'.
       terminates (run_blocks fuel ctx fn s) /\
       terminates (run_blocks fuel' ctx fn' s) ==>
       lift_result R_ok R_term R_term
         (run_blocks fuel ctx fn s)
         (run_blocks fuel' ctx fn' s))
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  (* Apply fwd_lift *)
  `!fuel ctx s. s.vs_inst_idx = 0 /\ ~s.vs_halted /\
     terminates (run_blocks fuel ctx fn s) ==>
     ?fuel'. terminates (run_blocks fuel' ctx
                (function_map_transform bt fn) s) /\
       lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
         (run_blocks fuel' ctx (function_map_transform bt fn) s)` by (
    mp_tac
      (SIMP_RULE (srw_ss()) [LET_THM] (Q.SPECL [`R_ok`, `R_term`, `fn`, `bt`] fwd_lift)) >>
    impl_tac >- (rpt conj_tac >> rpt (first_x_assum ACCEPT_TAC)) >>
    simp[]
  ) >>
  (* Apply bwd_lift *)
  `!fuel ctx s. s.vs_inst_idx = 0 /\ ~s.vs_halted /\
     terminates (run_blocks fuel ctx (function_map_transform bt fn) s) ==>
     ?fuel'. terminates (run_blocks fuel' ctx fn s) /\
       lift_result R_ok R_term R_term (run_blocks fuel' ctx fn s)
         (run_blocks fuel ctx (function_map_transform bt fn) s)` by (
    mp_tac
      (SIMP_RULE (srw_ss()) [LET_THM] (Q.SPECL [`R_ok`, `R_term`, `fn`, `bt`] bwd_lift)) >>
    impl_tac >- (rpt conj_tac >> rpt (first_x_assum ACCEPT_TAC)) >>
    simp[]
  ) >>
  conj_tac
  (* Termination equivalence *)
  >- (eq_tac >> strip_tac >> res_tac >> metis_tac[]) >>
  (* lift_result at arbitrary fuels *)
  rpt strip_tac >>
  `?fuel_f. terminates (run_blocks fuel_f ctx
              (function_map_transform bt fn) s) /\
     lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
       (run_blocks fuel_f ctx (function_map_transform bt fn) s)` by (
    qpat_x_assum `!fuel ctx s.
      s.vs_inst_idx = 0 /\ ~s.vs_halted /\
      terminates (run_blocks fuel ctx fn s) ==> _`
      (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
    simp[]
  ) >>
  `run_blocks fuel' ctx (function_map_transform bt fn) s =
   run_blocks fuel_f ctx (function_map_transform bt fn) s` by (
    irule fuel_mono_eq >> simp[] >> metis_tac[]
  ) >>
  metis_tac[]
QED

(* Version with weaker per-block sim: only requires non-halted states.
   Strictly stronger conclusion-wise (same conclusion, weaker precondition).
   Used by RTA and other passes where per-block sim fails for halted states. *)
Theorem resolving_block_sim_function_v2:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) fn bt.
    let fn' = function_map_transform bt fn in
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!bb fuel ctx s.
       MEM bb fn.fn_blocks /\ s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
       resolving_block_sim R_ok R_term fn.fn_blocks fn'.fn_blocks
         (run_block fuel ctx bb s)
         (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!fuel k ctx s.
       terminates (run_blocks fuel ctx fn s) ==>
       run_blocks (fuel + k) ctx fn s = run_blocks fuel ctx fn s) /\
    (!fuel k ctx s.
       terminates (run_blocks fuel ctx fn' s) ==>
       run_blocks (fuel + k) ctx fn' s = run_blocks fuel ctx fn' s)
  ==>
    !ctx s. s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
    ((?fuel. terminates (run_blocks fuel ctx fn s)) <=>
     (?fuel'. terminates (run_blocks fuel' ctx fn' s))) /\
    (!fuel fuel'.
       terminates (run_blocks fuel ctx fn s) /\
       terminates (run_blocks fuel' ctx fn' s) ==>
       lift_result R_ok R_term R_term
         (run_blocks fuel ctx fn s)
         (run_blocks fuel' ctx fn' s))
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  `!fuel ctx s. s.vs_inst_idx = 0 /\ ~s.vs_halted /\
     terminates (run_blocks fuel ctx fn s) ==>
     ?fuel'. terminates (run_blocks fuel' ctx
                (function_map_transform bt fn) s) /\
       lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
         (run_blocks fuel' ctx (function_map_transform bt fn) s)` by (
    mp_tac
      (SIMP_RULE (srw_ss()) [LET_THM] (Q.SPECL [`R_ok`, `R_term`, `fn`, `bt`] fwd_lift)) >>
    impl_tac >- (rpt conj_tac >> rpt (first_x_assum ACCEPT_TAC)) >>
    simp[]
  ) >>
  `!fuel ctx s. s.vs_inst_idx = 0 /\ ~s.vs_halted /\
     terminates (run_blocks fuel ctx (function_map_transform bt fn) s) ==>
     ?fuel'. terminates (run_blocks fuel' ctx fn s) /\
       lift_result R_ok R_term R_term (run_blocks fuel' ctx fn s)
         (run_blocks fuel ctx (function_map_transform bt fn) s)` by (
    mp_tac
      (SIMP_RULE (srw_ss()) [LET_THM] (Q.SPECL [`R_ok`, `R_term`, `fn`, `bt`] bwd_lift)) >>
    impl_tac >- (rpt conj_tac >> rpt (first_x_assum ACCEPT_TAC)) >>
    simp[]
  ) >>
  conj_tac
  >- (eq_tac >> strip_tac >> res_tac >> metis_tac[]) >>
  rpt strip_tac >>
  `?fuel_f. terminates (run_blocks fuel_f ctx
              (function_map_transform bt fn) s) /\
     lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
       (run_blocks fuel_f ctx (function_map_transform bt fn) s)` by (
    qpat_x_assum `!fuel ctx s.
      s.vs_inst_idx = 0 /\ ~s.vs_halted /\
      terminates (run_blocks fuel ctx fn s) ==> _`
      (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
    simp[]
  ) >>
  `run_blocks fuel' ctx (function_map_transform bt fn) s =
   run_blocks fuel_f ctx (function_map_transform bt fn) s` by (
    irule fuel_mono_eq >> simp[] >> metis_tac[]
  ) >>
  metis_tac[]
QED
