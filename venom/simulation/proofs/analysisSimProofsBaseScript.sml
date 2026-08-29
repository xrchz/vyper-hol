(*
 * Analysis-Driven Simulation — Proofs
 *
 * TOP-LEVEL:
 *   analysis_inst_sim_block_sim_proof       — inst sim ⟹ block sim (at idx=0)
 *   df_analysis_pass_correct_sound_proof    — with soundness threading
 *   df_analysis_pass_correct_widen_sound_proof — widening variant
 *   df_analysis_pass_correct_prepend_proof  — prepend-aware variant
 *   analysis_function_transform_compare_proof — compare two transforms
 *   analysis_inst_simulates_from_1_proof    — 1:1 as special case of 1:N
 *
 * Helper:
 *   analysis_block_sim, block_sim_function_by_lookup, foldl_sound,
 *   run_insts_singleton, abt_label, abt_widen_label,
 *   step_inst_idx_indep, run_insts_idx_indep, run_insts_preserves_idx
 *)

Theory analysisSimProofsBase
Ancestors
  analysisSimDefs execEquivParamDefs dfAnalyzeProofs dfAnalyzeDefs
  dfAnalyzeWidenProofs dfAnalyzeWidenDefs
  passSimulationDefs passSimulationProofs execEquivParamProofs
  execEquivParamBase stateEquiv venomExecSemantics venomInst instIdxIndep
  venomState list finite_map pred_set
Libs
  execEquivParamLib

open execEquivParamLib

fun analysis_lift_result_case_tac () = gvs[lift_result_def]

(* ===== Helpers ===== *)

Theorem venom_state_idx_self_update:
  !st : venom_state. st with vs_inst_idx := st.vs_inst_idx = st
Proof
  Cases >> simp[venom_state_fn_updates]
QED

Theorem run_insts_singleton:
  !fuel ctx (x:instruction) s.
    run_insts fuel ctx [x] s = step_inst fuel ctx x s
Proof
  rw[run_insts_def] >> CASE_TAC >> simp[run_insts_def]
QED

Triviality run_insts_append:
  !xs ys fuel ctx s.
    run_insts fuel ctx (xs ++ ys) s =
    case run_insts fuel ctx xs s of
      OK s' => run_insts fuel ctx ys s'
    | Halt s' => Halt s'
    | Abort a s' => Abort a s'
    | IntRet v s' => IntRet v s'
    | Error e => Error e
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[run_insts_def]
QED

(* PHI is an error in step_inst_base (PHIs are evaluated by eval_phis at block entry) *)
Triviality step_inst_base_phi_error[local]:
  !inst s. inst.inst_opcode = PHI ==> step_inst_base inst s = Error "phi outside prefix"
Proof
  rpt strip_tac >> simp[step_inst_base_def]
QED

Triviality step_inst_phi_error[local]:
  !fuel ctx inst s. inst.inst_opcode = PHI ==> step_inst fuel ctx inst s = Error "phi outside prefix"
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by simp[] >>
  drule step_inst_non_invoke >>
  simp[step_inst_base_phi_error]
QED

(* R_ok preservation for run_insts (simpler than exec_block — no terminator handling) *)
Theorem run_insts_preserves_R:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) instrs.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!inst x. MEM inst instrs /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s1 s2. R_ok s1 s2 ==>
      lift_result R_ok R_term R_term (run_insts fuel ctx instrs s1)
                               (run_insts fuel ctx instrs s2)
Proof
  ntac 2 gen_tac >> Induct >>
  rw[run_insts_def, lift_result_def] >>
  `lift_result R_ok R_term R_term (step_inst fuel ctx h s1)
     (step_inst fuel ctx h s2)` by
    (irule step_inst_preserves_R_proof >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx h s1` >>
  Cases_on `step_inst fuel ctx h s2` >>
  gvs[lift_result_def, run_insts_def] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

(* Lift per-group simulation through run_insts on concatenated instruction lists.
   Given per-group sim and R_ok preservation for the left groups,
   derive sim for the whole FLAT. *)
Triviality run_insts_compare_step:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   g1 (g1s' : instruction list list) g2 (g2s' : instruction list list).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    LENGTH g1s' = LENGTH g2s' /\
    (!fuel ctx s.
       (?e. run_insts fuel ctx g1 s = Error e) \/
       lift_result R_ok R_term R_term
         (run_insts fuel ctx g1 s) (run_insts fuel ctx g2 s)) /\
    (!i fuel ctx s.
       i < LENGTH g1s' ==>
       (?e. run_insts fuel ctx (EL i g1s') s = Error e) \/
       lift_result R_ok R_term R_term
         (run_insts fuel ctx (EL i g1s') s)
         (run_insts fuel ctx (EL i g2s') s)) /\
    (!inst x. MEM inst (FLAT (g1 :: g1s')) /\ MEM (Var x) inst.inst_operands
       ==> !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!fuel ctx s.
       (?e. run_insts fuel ctx (FLAT g1s') s = Error e) \/
       lift_result R_ok R_term R_term
         (run_insts fuel ctx (FLAT g1s') s)
         (run_insts fuel ctx (FLAT g2s') s))
  ==>
    !fuel ctx s.
      (?e. run_insts fuel ctx (g1 ++ FLAT g1s') s = Error e) \/
      lift_result R_ok R_term R_term
        (run_insts fuel ctx (g1 ++ FLAT g1s') s)
        (run_insts fuel ctx (g2 ++ FLAT g2s') s)
Proof
  rpt strip_tac >> simp[run_insts_append] >>
  `(?e. run_insts fuel ctx g1 s = Error e) \/
   lift_result R_ok R_term R_term (run_insts fuel ctx g1 s)
     (run_insts fuel ctx g2 s)` by metis_tac[]
  >>
  Cases_on `run_insts fuel ctx g1 s` >>
  Cases_on `run_insts fuel ctx g2 s` >>
  gvs[lift_result_def]
  >>
  rename1 `R_ok v1 v2` >>
  `lift_result R_ok R_term R_term (run_insts fuel ctx (FLAT g1s') v1)
     (run_insts fuel ctx (FLAT g1s') v2)` by (
    irule run_insts_preserves_R >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >>
    qpat_assum `!inst x. (_ \/ _) /\ _ ==> _`
      (qspecl_then [`inst`, `x`] mp_tac) >>
    simp[])
  >>
  `(?e. run_insts fuel ctx (FLAT g1s') v2 = Error e) \/
   lift_result R_ok R_term R_term (run_insts fuel ctx (FLAT g1s') v2)
     (run_insts fuel ctx (FLAT g2s') v2)` by metis_tac[]
  >>
  Cases_on `run_insts fuel ctx (FLAT g1s') v1` >>
  Cases_on `run_insts fuel ctx (FLAT g1s') v2` >>
  gvs[lift_result_def] >>
  Cases_on `run_insts fuel ctx (FLAT g2s') v2` >>
  gvs[lift_result_def] >>
  metis_tac[]
QED

Theorem run_insts_compare:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (g1s : instruction list list)
   (g2s : instruction list list).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    LENGTH g1s = LENGTH g2s /\
    (!i fuel ctx s.
       i < LENGTH g1s ==>
       (?e. run_insts fuel ctx (EL i g1s) s = Error e) \/
       lift_result R_ok R_term R_term
         (run_insts fuel ctx (EL i g1s) s)
         (run_insts fuel ctx (EL i g2s) s)) /\
    (!inst x. MEM inst (FLAT g1s) /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      (?e. run_insts fuel ctx (FLAT g1s) s = Error e) \/
      lift_result R_ok R_term R_term
        (run_insts fuel ctx (FLAT g1s) s)
        (run_insts fuel ctx (FLAT g2s) s)
Proof
  ntac 2 gen_tac >> Induct
  >- (rpt strip_tac >> gvs[run_insts_def, lift_result_def] >>
      metis_tac[vsr_R_ok_refl])
  >> strip_tac >> Cases_on `g2s` >> fs[]
  >> rpt strip_tac
  >> simp[run_insts_append]
  >> `(?e. run_insts fuel ctx h s = Error e) \/
     lift_result R_ok R_term R_term (run_insts fuel ctx h s)
       (run_insts fuel ctx h' s)` by (
    first_x_assum (qspecl_then [`0`, `fuel`, `ctx`, `s`] mp_tac) >> simp[])
  >>
  Cases_on `run_insts fuel ctx h s` >>
  Cases_on `run_insts fuel ctx h' s` >|
  [analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac (),
   analysis_lift_result_case_tac (), analysis_lift_result_case_tac ()]
  >>
  rename1 `R_ok v1 v2` >>
  `lift_result R_ok R_term R_term (run_insts fuel ctx (FLAT g1s) v1)
     (run_insts fuel ctx (FLAT g1s) v2)` by (
    irule run_insts_preserves_R >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac)
  >>
  `!i fuel' ctx' s''. i < LENGTH t ==>
     (?e. run_insts fuel' ctx' (EL i g1s) s'' = Error e) \/
     lift_result R_ok R_term R_term (run_insts fuel' ctx' (EL i g1s) s'')
       (run_insts fuel' ctx' (EL i t) s'')` by (
    rpt strip_tac >>
    first_x_assum (qspecl_then [`SUC i`, `fuel'`, `ctx'`, `s''`] mp_tac) >>
    simp[])
  >>
  `(?e. run_insts fuel ctx (FLAT g1s) v2 = Error e) \/
   lift_result R_ok R_term R_term (run_insts fuel ctx (FLAT g1s) v2)
     (run_insts fuel ctx (FLAT t) v2)` by (
    qpat_x_assum `!g2s. _` (qspec_then `t` mp_tac) >>
    impl_tac >> TRY (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[]) >>
    metis_tac[])
  >>
  Cases_on `run_insts fuel ctx (FLAT g1s) v1` >>
  Cases_on `run_insts fuel ctx (FLAT g1s) v2` >>
  gvs[lift_result_def] >>
  Cases_on `run_insts fuel ctx (FLAT t) v2` >>
  gvs[lift_result_def] >>
  metis_tac[]
QED

Theorem abt_label:
  !bottom result (f:'a -> instruction -> instruction list) bb.
    (analysis_block_transform bottom result f bb).bb_label = bb.bb_label
Proof
  simp[analysis_block_transform_def]
QED

Triviality abt_widen_label:
  !bottom result (f:'a -> instruction -> instruction list) bb.
    (analysis_block_transform_widen bottom result f bb).bb_label = bb.bb_label
Proof
  simp[analysis_block_transform_widen_def]
QED

(* step_inst for non-term non-INVOKE is idx-independent (bridges to instIdxIndep) *)
Theorem step_inst_idx_indep:
  !fuel ctx inst s n.
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    step_inst fuel ctx inst (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (step_inst fuel ctx inst s)
Proof
  rw[step_inst_non_invoke, step_inst_inst_idx_indep]
QED

(* run_insts on non-term non-INVOKE instructions is idx-independent *)
Theorem run_insts_idx_indep:
  !fuel ctx insts s n.
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    run_insts fuel ctx insts (s with vs_inst_idx := n) =
    exec_result_map (\s'. s' with vs_inst_idx := n)
      (run_insts fuel ctx insts s)
Proof
  Induct_on `insts` >> simp[run_insts_def, exec_result_map_def] >>
  rpt gen_tac >> strip_tac >>
  simp[run_insts_def, step_inst_idx_indep] >>
  Cases_on `step_inst fuel ctx h s` >>
  simp[exec_result_map_def, run_insts_def] >>
  `v.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `n`] mp_tac) >>
  simp[] >>
  strip_tac >> simp[exec_result_map_def]
QED

(* run_insts preserves vs_inst_idx on OK results *)
Theorem run_insts_preserves_idx:
  !fuel ctx insts s s'.
    run_insts fuel ctx insts s = OK s' /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts ==>
    s'.vs_inst_idx = s.vs_inst_idx
Proof
  Induct_on `insts` >> simp[run_insts_def] >>
  rpt gen_tac >> strip_tac >>
  fs[run_insts_def] >>
  BasicProvers.FULL_CASE_TAC >> fs[] >>
  `v.vs_inst_idx = s.vs_inst_idx` by metis_tac[step_inst_preserves_inst_idx] >>
  metis_tac[]
QED

(* ===== 1:1 as special case ===== *)

Theorem analysis_inst_simulates_from_1_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (g : 'a -> instruction -> instruction).
    analysis_inst_simulates_1 R_ok R_term sound g ==>
    analysis_inst_simulates R_ok R_term sound (\v inst. [g v inst])
Proof
  rw[analysis_inst_simulates_def, analysis_inst_simulates_1_def,
     inst_transform_structural_def, inst_transform_structural_1_def,
     run_insts_singleton]
QED

(* EL into FLAT at offset = LENGTH(FLAT(TAKE i ...)) indexes into EL i *)
(* Decompose MAPi g xs at index i *)
Triviality MAPi_decompose:
  !i (g : num -> 'a -> 'b list) xs.
    i < LENGTH xs ==>
    FLAT (MAPi g xs) =
      FLAT (TAKE i (MAPi g xs)) ++ g i (EL i xs) ++
      FLAT (DROP (SUC i) (MAPi g xs))
Proof
  rpt strip_tac >>
  `i < LENGTH (MAPi g xs)` by simp[indexedListsTheory.LENGTH_MAPi] >>
  `TAKE i (MAPi g xs) ++ [EL i (MAPi g xs)] ++ DROP (SUC i) (MAPi g xs) =
   MAPi g xs` by metis_tac[rich_listTheory.TAKE_DROP_SUC] >>
  `EL i (MAPi g xs) = g i (EL i xs)` by
    simp[indexedListsTheory.EL_MAPi] >>
  `FLAT (MAPi g xs) =
   FLAT (TAKE i (MAPi g xs) ++ [g i (EL i xs)] ++ DROP (SUC i) (MAPi g xs))` by
    metis_tac[] >>
  fs[FLAT_APPEND, FLAT]
QED

(* EL into FLAT at offset = LENGTH(FLAT(TAKE i ...)) indexes into EL i *)
Theorem EL_FLAT_MAPi:
  !i (g : num -> 'a -> 'b list) xs k.
    i < LENGTH xs /\ k < LENGTH (g i (EL i xs)) ==>
    EL (LENGTH (FLAT (TAKE i (MAPi g xs))) + k)
       (FLAT (MAPi g xs)) = EL k (g i (EL i xs))
Proof
  rpt strip_tac >>
  `FLAT (MAPi g xs) =
     FLAT (TAKE i (MAPi g xs)) ++ g i (EL i xs) ++
     FLAT (DROP (SUC i) (MAPi g xs))` by metis_tac[MAPi_decompose] >>
  pop_assum SUBST1_TAC >>
  simp[EL_APPEND_EQN]
QED

(* The FLAT offset + prefix length stays within bounds *)
Theorem FLAT_MAPi_offset_bound:
  !i (g : num -> 'a -> 'b list) xs.
    i < LENGTH xs ==>
    LENGTH (FLAT (TAKE i (MAPi g xs))) + LENGTH (g i (EL i xs))
      <= LENGTH (FLAT (MAPi g xs))
Proof
  rpt strip_tac >>
  `FLAT (MAPi g xs) =
     FLAT (TAKE i (MAPi g xs)) ++ g i (EL i xs) ++
     FLAT (DROP (SUC i) (MAPi g xs))` by metis_tac[MAPi_decompose] >>
  pop_assum SUBST1_TAC >>
  simp[]
QED

(* TAKE (SUC i) advances the FLAT offset by LENGTH (g i (EL i xs)) *)
Theorem FLAT_MAPi_offset_SUC:
  !i (g : num -> 'a -> 'b list) xs.
    i < LENGTH xs ==>
    LENGTH (FLAT (TAKE (SUC i) (MAPi g xs))) =
    LENGTH (FLAT (TAKE i (MAPi g xs))) + LENGTH (g i (EL i xs))
Proof
  rpt strip_tac >>
  `SUC i <= LENGTH (MAPi g xs)` by simp[indexedListsTheory.LENGTH_MAPi] >>
  `TAKE (SUC i) (MAPi g xs) = SNOC (EL i (MAPi g xs)) (TAKE i (MAPi g xs))` by
    simp[rich_listTheory.TAKE_SUC_BY_TAKE] >>
  `EL i (MAPi g xs) = g i (EL i xs)` by
    simp[indexedListsTheory.EL_MAPi] >>
  gvs[SNOC_APPEND, FLAT_APPEND, FLAT]
QED

(* When run_insts succeeds on a non-term non-INVOKE prefix, exec_block
   skips past those instructions and continues from the resulting state. *)
Theorem exec_block_skip_prefix:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix s = OK s'
  ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  Induct >> rw[run_insts_def] >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by simp[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    simp[step_inst_idx_indep] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_inst_preserves_inst_idx] >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  gvs[] >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `s1`, `SUC j`, `s'`]
    mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >>
  impl_tac
  >- (rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
      simp[arithmeticTheory.ADD_CLAUSES])
  >> simp[]
QED

(* R_term tolerates vs_inst_idx changes *)
Triviality R_term_idx_change:
  !R_ok R_term s n.
    valid_state_rel R_ok R_term ==> R_term (s with vs_inst_idx := n) s
Proof
  rpt strip_tac >>
  `R_term s s` by metis_tac[vsr_R_term_refl] >>
  vsr_reconstruct_R_term_tac `s` `s`
QED

Triviality R_term_idx_change2:
  !R_ok R_term s n.
    valid_state_rel R_ok R_term ==> R_term s (s with vs_inst_idx := n)
Proof
  rpt strip_tac >>
  `R_term s s` by metis_tac[vsr_R_term_refl] >>
  vsr_reconstruct_R_term_tac `s` `s`
QED

(* R_ok tolerates vs_inst_idx changes when both sides change to the same value *)
Theorem R_ok_idx_change:
  !R_ok R_term s1 s2 n.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 ==>
    R_ok (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  rpt strip_tac >>
  vsr_reconstruct_R_ok_tac `s1` `s2`
QED

(* R_term tolerates vs_inst_idx changes on both sides *)
Theorem R_term_idx_change_both:
  !R_ok R_term s1 s2 n.
    valid_state_rel R_ok R_term /\ R_term s1 s2 ==>
    R_term (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  rpt strip_tac >>
  vsr_reconstruct_R_term_tac `s1` `s2`
QED

(* lift_result preserved by exec_result_map when g preserves R_ok/R_term *)
Triviality lift_result_exec_result_map:
  !R_ok R_term g r1 r2.
    lift_result R_ok R_term R_term r1 r2 /\
    (!s1 s2. R_ok s1 s2 ==> R_ok (g s1) (g s2)) /\
    (!s1 s2. R_term s1 s2 ==> R_term (g s1) (g s2))
  ==> lift_result R_ok R_term R_term (exec_result_map g r1) (exec_result_map g r2)
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def, exec_result_map_def]
QED

(* Block-level exec_block_preserves_R: same block, R_ok states.
   The operand condition is carried as a premise (not assumed globally). *)
Theorem exec_block_preserves_R_block:
  !R_ok R_term.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) ==>
    !fuel ctx bb s1 s2.
      (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
         !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
      R_ok s1 s2 ==>
      lift_result R_ok R_term R_term (exec_block fuel ctx bb s1)
                               (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  pop_assum mp_tac >>
  pop_assum mp_tac >>
  MAP_EVERY qid_spec_tac [`s2`, `s1`, `bb`, `ctx`, `fuel`] >>
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn s. T` >> rw[] >>
  simp[Once exec_block_def] >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  `s1.vs_inst_idx = s2.vs_inst_idx` by
    (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
  gvs[] >>
  Cases_on `get_instruction bb s2.vs_inst_idx` >> gvs[lift_result_def] >>
  rename1 `get_instruction bb _ = SOME inst` >>
  `MEM inst bb.bb_instructions` by
    (gvs[get_instruction_def] >> irule listTheory.EL_MEM >> simp[]) >>
  `lift_result R_ok R_term R_term (step_inst fuel ctx inst s1)
     (step_inst fuel ctx inst s2)` by
    (irule step_inst_preserves_R_proof >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst fuel ctx inst s1` >>
  Cases_on `step_inst fuel ctx inst s2` >>
  gvs[lift_result_def] >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[lift_result_def]
  >- (`v.vs_halted <=> v'.vs_halted` by
        (imp_res_tac vsr_R_ok_fields >> gvs[]) >>
      Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
      metis_tac[vsr_R_ok_R_term])
  >>
  first_x_assum irule >> conj_tac >- fs[] >>
  irule R_ok_idx_change >> fs[] >> metis_tac[]
QED

(* Halt-wrapping preserves lift_result when valid_state_rel holds.
   Avoids 5x5 case explosion in terminator proofs. *)
Triviality lift_result_halt_wrap:
  !R_ok R_term r1 r2.
    valid_state_rel R_ok R_term ==>
    lift_result R_ok R_term R_term r1 r2 ==>
    lift_result R_ok R_term R_term
      (case r1 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case r2 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  Cases_on `r1` >> Cases_on `r2` >> gvs[lift_result_def] >>
  imp_res_tac vsr_R_ok_fields >> gvs[] >>
  Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
  metis_tac[vsr_R_ok_R_term]
QED

(* For a terminator instruction, exec_block's one-step result is
   lift_result-compatible between states differing only in vs_inst_idx.
   Proof: case split on terminator opcodes; jump_to erases idx to 0,
   halt_state preserves idx but routes to Halt (R_term), others are
   Error/IntRet/Abort (R_term or trivial). *)
Theorem terminator_exec_block_step_lift:
  !R_ok R_term. valid_state_rel R_ok R_term ==>
  !fuel ctx inst s j.
    is_terminator inst.inst_opcode ==>
    lift_result R_ok R_term R_term
      (case step_inst fuel ctx inst s of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case step_inst fuel ctx inst (s with vs_inst_idx := j) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  simp[step_inst_non_invoke] >>
  (* Fact A: normalizing idx to 0, both sides equal *)
  `exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst (s with vs_inst_idx := j)) =
   exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst s)` by
    simp[terminator_step_inst_base_idx_norm0] >>
  (* Case split on one side; norm0 constrains the other *)
  Cases_on `step_inst_base inst s` >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := j)` >>
  gvs[exec_result_map_def, venom_state_component_equality, lift_result_def]
  >- (
    (* OK-OK: both idx=0 by terminator_OK_inst_idx_0 *)
    `v.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
    `v'.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
    `v' = v` by gvs[venom_state_component_equality] >>
    gvs[] >> irule lift_result_refl_proof >>
    metis_tac[vsr_R_ok_refl, vsr_R_term_refl]
  ) >>
  (* Non-OK cases: v' = v with idx updated → R_term *)
  (`v' = v with vs_inst_idx := v'.vs_inst_idx` by
     gvs[venom_state_component_equality] >>
   pop_assum SUBST1_TAC >>
   metis_tac[R_term_idx_change2])
QED

(* Reverse direction: lift_result from (s with idx:=j) to s *)
Theorem terminator_exec_block_step_lift_rev:
  !R_ok R_term. valid_state_rel R_ok R_term ==>
  !fuel ctx inst s j.
    is_terminator inst.inst_opcode ==>
    lift_result R_ok R_term R_term
      (case step_inst fuel ctx inst (s with vs_inst_idx := j) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case step_inst fuel ctx inst s of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def]) >>
  simp[step_inst_non_invoke] >>
  `exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst (s with vs_inst_idx := j)) =
   exec_result_map (\s'. s' with vs_inst_idx := 0)
     (step_inst_base inst s)` by
    simp[terminator_step_inst_base_idx_norm0] >>
  Cases_on `step_inst_base inst (s with vs_inst_idx := j)` >>
  Cases_on `step_inst_base inst s` >>
  gvs[exec_result_map_def, venom_state_component_equality, lift_result_def]
  >- (
    `v.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
    `v'.vs_inst_idx = 0` by metis_tac[terminator_OK_inst_idx_0] >>
    `v = v'` by gvs[venom_state_component_equality] >>
    gvs[] >> irule lift_result_refl_proof >>
    metis_tac[vsr_R_ok_refl, vsr_R_term_refl]
  ) >>
  (`v = v' with vs_inst_idx := v.vs_inst_idx` by
     gvs[venom_state_component_equality] >>
   pop_assum SUBST1_TAC >>
   metis_tac[R_term_idx_change])
QED

(* INVOKE step_inst is idx-independent: setup_callee sets idx=0,
   merge_callee_state preserves caller structure.
   step_inst INVOKE on (s with idx := j) = exec_result_map (with idx := j) (step_inst INVOKE s) *)
Triviality foldl_update_var_idx:
  !pairs s0 j.
    FOLDL (\s' (out,val). s' with vs_vars := s'.vs_vars |+ (out,val))
      (s0 with vs_inst_idx := j) pairs =
    (FOLDL (\s' (out,val). s' with vs_vars := s'.vs_vars |+ (out,val))
       s0 pairs) with vs_inst_idx := j
Proof
  Induct >- simp[venom_state_component_equality] >>
  simp[pairTheory.FORALL_PROD] >> rpt gen_tac >>
  first_x_assum (qspecl_then
    [`s0 with vs_vars := s0.vs_vars |+ (p_1, p_2)`, `j`] mp_tac) >>
  simp[venom_state_component_equality]
QED

Triviality merge_callee_state_idx:
  !caller callee j.
    merge_callee_state (caller with vs_inst_idx := j) callee =
    (merge_callee_state caller callee) with vs_inst_idx := j
Proof
  simp[merge_callee_state_def, venom_state_component_equality]
QED


Triviality adopt_return_fmp_idx:
  !ir s j.
    adopt_return_fmp ir (s with vs_inst_idx := j) =
    (adopt_return_fmp ir s) with vs_inst_idx := j
Proof
  rpt gen_tac >>
  Cases_on `ir.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, venom_state_component_equality]
QED
Triviality bind_outputs_idx:
  !outs vals s j.
    bind_outputs outs vals (s with vs_inst_idx := j) =
    OPTION_MAP (\s'. s' with vs_inst_idx := j) (bind_outputs outs vals s)
Proof
  simp[bind_outputs_def, update_var_def] >> rw[] >>
  simp[foldl_update_var_idx]
QED

(* For INVOKE, only the OK case shifts idx; Halt/Abort/Error are identical *)
Theorem invoke_step_inst_idx_OK_only:
  !fuel ctx inst s j.
    inst.inst_opcode = INVOKE ==>
    step_inst fuel ctx inst (s with vs_inst_idx := j) =
    case step_inst fuel ctx inst s of
      OK s'' => OK (s'' with vs_inst_idx := j)
    | x => x
Proof
  rpt strip_tac >>
  simp[step_inst_def, eval_ops_inst_idx, setup_callee_def,
       merge_callee_state_idx, adopt_return_fmp_idx, bind_outputs_idx,
       venom_state_component_equality] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[decode_invoke_def]
QED

(* Bridge: lift_result between two INVOKE instructions at base state
   implies lift_result at shifted idx (both sides shifted by same amount). *)
Triviality invoke_lift_result_idx_bridge:
  !R_ok R_term fuel ctx inst1 inst2 s n.
    valid_state_rel R_ok R_term /\
    inst1.inst_opcode = INVOKE /\ inst2.inst_opcode = INVOKE /\
    lift_result R_ok R_term R_term
      (step_inst fuel ctx inst1 s)
      (step_inst fuel ctx inst2 s)
  ==>
    lift_result R_ok R_term R_term
      (step_inst fuel ctx inst1 (s with vs_inst_idx := n))
      (step_inst fuel ctx inst2 (s with vs_inst_idx := n))
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst1 (s with vs_inst_idx := n) =
    case step_inst fuel ctx inst1 s of
      OK s'' => OK (s'' with vs_inst_idx := n)
    | x => x` by simp[invoke_step_inst_idx_OK_only] >>
  `step_inst fuel ctx inst2 (s with vs_inst_idx := n) =
    case step_inst fuel ctx inst2 s of
      OK s'' => OK (s'' with vs_inst_idx := n)
    | x => x` by simp[invoke_step_inst_idx_OK_only] >>
  ntac 2 (pop_assum SUBST1_TAC) >>
  Cases_on `step_inst fuel ctx inst1 s` >>
  Cases_on `step_inst fuel ctx inst2 s` >>
  gvs[lift_result_def] >>
  metis_tac[R_ok_idx_change]
QED

(* For two DIFFERENT INVOKE instructions with simulation between them,
   relates exec_block continuations on both sides with different idx offsets.
   Generalizes invoke_exec_block_step_lift to different instructions. *)
Triviality invoke_exec_block_step_lift_sim:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
  valid_state_rel R_ok R_term ==>
  !fuel ctx inst1 inst2 s i j bb bb'.
    inst1.inst_opcode = INVOKE /\ inst2.inst_opcode = INVOKE /\
    lift_result R_ok R_term R_term
      (step_inst fuel ctx inst1 s) (step_inst fuel ctx inst2 s) /\
    (!v1 v2. step_inst fuel ctx inst1 s = OK v1 /\
             step_inst fuel ctx inst2 s = OK v2 /\ R_ok v1 v2 ==>
       lift_result R_ok R_term R_term
         (exec_block fuel ctx bb (v1 with vs_inst_idx := SUC i))
         (exec_block fuel ctx bb' (v2 with vs_inst_idx := SUC j)))
  ==>
    lift_result R_ok R_term R_term
      (case step_inst fuel ctx inst1 s of
         OK s'' => exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case step_inst fuel ctx inst2 (s with vs_inst_idx := j) of
         OK s'' => exec_block fuel ctx bb' (s'' with vs_inst_idx := SUC j)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst2 (s with vs_inst_idx := j) =
    case step_inst fuel ctx inst2 s of
      OK s'' => OK (s'' with vs_inst_idx := j)
    | x => x` by simp[invoke_step_inst_idx_OK_only] >>
  pop_assum SUBST1_TAC >>
  Cases_on `step_inst fuel ctx inst1 s` >>
  Cases_on `step_inst fuel ctx inst2 s` >>
  gvs[lift_result_def] >>
  first_x_assum irule >> gvs[]
QED

(* Executing the same instruction suffix at different block offsets
   gives lift_result-related results. Used for prepend correctness:
   after prepending k instructions, the original suffix at offset k
   simulates the same suffix at offset 0 in the smaller block. *)
Theorem exec_block_index_shift:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
    valid_state_rel R_ok R_term ==>
  !n fuel ctx bb1 bb2 s k.
    n = LENGTH bb2.bb_instructions - s.vs_inst_idx /\
    s.vs_inst_idx <= LENGTH bb2.bb_instructions /\
    k + LENGTH bb2.bb_instructions = LENGTH bb1.bb_instructions /\
    (!i. s.vs_inst_idx <= i /\ i < LENGTH bb2.bb_instructions ==>
       EL (k + i) bb1.bb_instructions = EL i bb2.bb_instructions)
  ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb2 s)
      (exec_block fuel ctx bb1 (s with vs_inst_idx := s.vs_inst_idx + k))
Proof
  rpt gen_tac \\ strip_tac
  \\ completeInduct_on `n` \\ rpt gen_tac \\ strip_tac
  \\ qabbrev_tac `i = s.vs_inst_idx`
  \\ Cases_on `i >= LENGTH bb2.bb_instructions`
  >- (
    `i = LENGTH bb2.bb_instructions` by fs[Abbr `i`]
    \\ ONCE_REWRITE_TAC [exec_block_def]
    \\ simp[get_instruction_def, lift_result_def])
  \\ `i < LENGTH bb2.bb_instructions` by fs[]
  \\ `EL (i + k) bb1.bb_instructions = EL i bb2.bb_instructions` by (
    first_x_assum (qspec_then `i` mp_tac) \\ simp[Abbr `i`])
  \\ `i + k < LENGTH bb1.bb_instructions` by fs[]
  \\ CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def]))
  \\ CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def]))
  \\ simp[get_instruction_def]
  \\ qabbrev_tac `inst = EL i bb2.bb_instructions`
  \\ Cases_on `is_terminator inst.inst_opcode`
  >- (asm_simp_tac bool_ss []
      \\ irule terminator_exec_block_step_lift \\ simp[])
  \\ asm_simp_tac bool_ss []
  \\ Cases_on `inst.inst_opcode = INVOKE`
  >- (
    simp[invoke_step_inst_idx_OK_only]
    \\ Cases_on `step_inst fuel ctx inst s` \\ simp[lift_result_def]
    >- (
      rename1 `OK v`
      \\ imp_res_tac step_inst_preserves_inst_idx
      \\ `LENGTH bb2.bb_instructions - SUC i < n` by simp[Abbr `i`]
      \\ qpat_x_assum `!m. m < _ ==> _` (qspec_then
           `LENGTH bb2.bb_instructions - SUC i` mp_tac)
      \\ asm_simp_tac bool_ss []
      \\ disch_then (qspecl_then [
           `fuel`, `ctx`, `bb1`, `bb2`,
           `v with vs_inst_idx := SUC i`, `k`] mp_tac)
      \\ simp[Abbr `i`, arithmeticTheory.ADD_CLAUSES])
    \\ metis_tac[vsr_R_term_refl])
  \\ simp[step_inst_idx_indep, exec_result_map_def]
  \\ Cases_on `step_inst fuel ctx inst s`
  \\ simp[lift_result_def, exec_result_map_def]
  >- (
    rename1 `OK v`
    \\ imp_res_tac step_inst_preserves_inst_idx
    \\ `LENGTH bb2.bb_instructions - SUC i < n` by simp[Abbr `i`]
    \\ qpat_x_assum `!m. m < _ ==> _` (qspec_then
         `LENGTH bb2.bb_instructions - SUC i` mp_tac)
    \\ asm_simp_tac bool_ss []
    \\ disch_then (qspecl_then [
         `fuel`, `ctx`, `bb1`, `bb2`,
         `v with vs_inst_idx := SUC i`, `k`] mp_tac)
    \\ simp[Abbr `i`, arithmeticTheory.ADD_CLAUSES])
  \\ metis_tac[R_term_idx_change2]
QED

(* Combined: skip-prefix + index-shift + R_ok-bridge.
   Shows exec_block on a block with instructions = prefix ++ rest
   is related to exec_block on just rest, when the prefix is
   run_insts-equivalent and preserves R_ok. *)
Theorem exec_block_with_prefix:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   fuel ctx bb_long bb_short prefix s.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    bb_long.bb_instructions = prefix ++ bb_short.bb_instructions /\
    bb_long.bb_label = bb_short.bb_label /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (?s'. run_insts fuel ctx prefix s = OK s' /\ R_ok s s') /\
    s.vs_inst_idx = 0 /\
    (!inst x. MEM inst bb_short.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !sa sb. R_ok sa sb ==> lookup_var x sa = lookup_var x sb)
  ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb_short s)
      (exec_block fuel ctx bb_long s)
Proof
  rpt strip_tac
  \\ rename1 `run_insts _ _ prefix s = OK s'`
  (* s' preserves idx *)
  \\ `s'.vs_inst_idx = 0` by (
       `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
          prefix` by fs[] >>
       metis_tac[run_insts_preserves_idx])
  (* 3b: R_ok bridge on bb_short *)
  \\ `lift_result R_ok R_term R_term (exec_block fuel ctx bb_short s)
                               (exec_block fuel ctx bb_short s')` by (
       irule exec_block_preserves_R_block >>
       rpt conj_tac >> first_assum ACCEPT_TAC)
  (* 3c: skip prefix equation *)
  \\ `s with vs_inst_idx := 0 = s` by
       simp[venom_state_component_equality]
  \\ `exec_block fuel ctx bb_long s =
      exec_block fuel ctx bb_long
        (s' with vs_inst_idx := LENGTH prefix)` by (
       pop_assum (fn eq =>
         CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [SYM eq]))) >>
       irule (REWRITE_RULE [arithmeticTheory.ADD_CLAUSES]
         (Q.SPECL [`prefix`, `fuel`, `ctx`, `bb_long`, `s`, `0`, `s'`]
           exec_block_skip_prefix)) >>
       rpt conj_tac >>
       TRY (first_assum ACCEPT_TAC) >>
       TRY (simp[LENGTH_APPEND]) >>
       rpt strip_tac >> simp[rich_listTheory.EL_APPEND1])
  (* 3d: index shift *)
  \\ `lift_result R_ok R_term R_term
        (exec_block fuel ctx bb_short s')
        (exec_block fuel ctx bb_long
          (s' with vs_inst_idx := LENGTH prefix))` by (
       mp_tac exec_block_index_shift >>
       disch_then (qspecl_then [`R_ok`, `R_term`] mp_tac) >>
       impl_tac >- first_assum ACCEPT_TAC >>
       disch_then (qspecl_then [
         `LENGTH bb_short.bb_instructions`,
         `fuel`, `ctx`, `bb_long`, `bb_short`,
         `s'`, `LENGTH prefix`] mp_tac) >>
       simp[] >>
       impl_tac
       >- (rpt conj_tac >>
           TRY (simp[LENGTH_APPEND]) >>
           rpt strip_tac >>
           simp[rich_listTheory.EL_APPEND2])
       >> simp[])
  (* Chain: bb_short s ~ bb_short s' ~ bb_long (s' + len) = bb_long s *)
  \\ `lift_result R_ok R_term R_term
        (exec_block fuel ctx bb_short s')
        (exec_block fuel ctx bb_long s)` by (
       qpat_x_assum `exec_block _ _ bb_long s = _` (SUBST1_TAC) >>
       first_assum ACCEPT_TAC)
  \\ irule lift_result_trans_proof
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ conj_tac >- first_assum ACCEPT_TAC
  \\ qexists_tac `exec_block fuel ctx bb_short s'`
  \\ conj_tac >> first_assum ACCEPT_TAC
QED

(* step_inst at idx=0: if step_inst ... s = OK v and inst is non-terminator,
   then step_inst ... (s with idx := 0) = OK (v with idx := 0).
   Unifies INVOKE (invoke_step_inst_idx_OK_only) and non-term non-INVOKE
   (step_inst_idx_indep) cases. *)
Triviality step_inst_at_0:
  !fuel ctx inst s v.
    ~is_terminator inst.inst_opcode /\
    step_inst fuel ctx inst s = OK v ==>
    step_inst fuel ctx inst (s with vs_inst_idx := 0) =
      OK (v with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    `step_inst fuel ctx inst (s with vs_inst_idx := 0) =
     case step_inst fuel ctx inst s of
       OK s'' => OK (s'' with vs_inst_idx := 0)
     | x => x` by simp[invoke_step_inst_idx_OK_only] >>
    fs[]
  )
  >- (
    `step_inst fuel ctx inst (s with vs_inst_idx := 0) =
     exec_result_map (\s'. s' with vs_inst_idx := 0)
       (step_inst fuel ctx inst s)` by
      simp[step_inst_idx_indep] >>
    fs[exec_result_map_def]
  )
QED

(* Combined: transfer_sound + step_inst_at_0.
   Given soundness at (s with idx := 0), derives soundness at (v with idx := 0)
   after a successful non-terminator step. *)
Triviality transfer_sound_at_0:
  !sound transfer ctx fuel run_ctx inst s v val.
    transfer_sound sound transfer ctx /\
    ~is_terminator inst.inst_opcode /\
    step_inst fuel run_ctx inst s = OK v /\
    sound val (s with vs_inst_idx := 0) ==>
    sound (transfer ctx inst val) (v with vs_inst_idx := 0)
Proof
  rpt strip_tac >>
  `step_inst fuel run_ctx inst (s with vs_inst_idx := 0) =
   OK (v with vs_inst_idx := 0)` by
    (irule step_inst_at_0 >> fs[]) >>
  fs[transfer_sound_def] >>
  first_x_assum irule >>
  qexistsl_tac [`fuel`, `run_ctx`, `s with vs_inst_idx := 0`] >> fs[]
QED

(* INVOKE step lift with error disjunct in the continuation.
   When the IH gives Error \/ lift_result, this composes with the
   INVOKE step mechanics. *)
Triviality invoke_exec_block_step_lift_err:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
  valid_state_rel R_ok R_term ==>
  !fuel ctx inst s i j bb bb'.
    inst.inst_opcode = INVOKE /\
    (!v'. step_inst fuel ctx inst s = OK v' ==>
       (?e. exec_block fuel ctx bb (v' with vs_inst_idx := SUC i) = Error e) \/
       lift_result R_ok R_term R_term
         (exec_block fuel ctx bb (v' with vs_inst_idx := SUC i))
         (exec_block fuel ctx bb'
            (v' with vs_inst_idx := SUC j)))
  ==>
    (?e. (case step_inst fuel ctx inst s of
            OK s'' => exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
          | Halt s' => Halt s'
          | Abort a s' => Abort a s'
          | IntRet rv ss => IntRet rv ss
          | Error e => Error e) = Error e) \/
    lift_result R_ok R_term R_term
      (case step_inst fuel ctx inst s of
         OK s'' => exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case step_inst fuel ctx inst (s with vs_inst_idx := j) of
         OK s'' => exec_block fuel ctx bb' (s'' with vs_inst_idx := SUC j)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst (s with vs_inst_idx := j) =
    case step_inst fuel ctx inst s of
      OK s'' => OK (s'' with vs_inst_idx := j)
    | x => x` by simp[invoke_step_inst_idx_OK_only] >>
  Cases_on `step_inst fuel ctx inst s` >> fs[lift_result_def] >>
  metis_tac[vsr_R_ok_refl, vsr_R_term_refl]
QED

(* For two DIFFERENT INVOKE instructions with error disjunct.
   Combines invoke_exec_block_step_lift_sim with error escape. *)
Triviality invoke_exec_block_step_lift_sim_err:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool).
  valid_state_rel R_ok R_term ==>
  !fuel ctx inst1 inst2 s i j bb bb'.
    inst1.inst_opcode = INVOKE /\ inst2.inst_opcode = INVOKE /\
    lift_result R_ok R_term R_term
      (step_inst fuel ctx inst1 s) (step_inst fuel ctx inst2 s) /\
    (!v1 v2. step_inst fuel ctx inst1 s = OK v1 /\
             step_inst fuel ctx inst2 s = OK v2 /\ R_ok v1 v2 ==>
       (?e. exec_block fuel ctx bb (v1 with vs_inst_idx := SUC i) = Error e) \/
       lift_result R_ok R_term R_term
         (exec_block fuel ctx bb (v1 with vs_inst_idx := SUC i))
         (exec_block fuel ctx bb' (v2 with vs_inst_idx := SUC j)))
  ==>
    (?e. (case step_inst fuel ctx inst1 s of
            OK s'' => exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
          | Halt s' => Halt s'
          | Abort a s' => Abort a s'
          | IntRet rv ss => IntRet rv ss
          | Error e => Error e) = Error e) \/
    lift_result R_ok R_term R_term
      (case step_inst fuel ctx inst1 s of
         OK s'' => exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (case step_inst fuel ctx inst2 (s with vs_inst_idx := j) of
         OK s'' => exec_block fuel ctx bb' (s'' with vs_inst_idx := SUC j)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
Proof
  rpt strip_tac >>
  `step_inst fuel ctx inst2 (s with vs_inst_idx := j) =
    case step_inst fuel ctx inst2 s of
      OK s'' => OK (s'' with vs_inst_idx := j)
    | x => x` by simp[invoke_step_inst_idx_OK_only] >>
  pop_assum SUBST1_TAC >>
  Cases_on `step_inst fuel ctx inst1 s` >>
  Cases_on `step_inst fuel ctx inst2 s` >>
  gvs[lift_result_def] >>
  first_x_assum irule >> gvs[]
QED

(* When run_insts fails (non-OK), exec_block on the same instructions
   produces a lift_result-compatible result (R_term allows idx difference). *)
Theorem exec_block_prefix_fail_lift:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) prefix.
  valid_state_rel R_ok R_term ==>
  !fuel ctx bb s j.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    ~(?s'. run_insts fuel ctx prefix s = OK s')
  ==>
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb (s with vs_inst_idx := j))
      (run_insts fuel ctx prefix s)
Proof
  gen_tac >> gen_tac >> Induct >- rw[run_insts_def] >>
  rpt strip_tac >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by fs[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    (fs[] >> simp[step_inst_idx_indep]) >>
  fs[run_insts_def] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def]
  >- (
    (* OK: recurse *)
    `v.vs_inst_idx = s.vs_inst_idx` by
      (fs[] >> metis_tac[step_inst_preserves_inst_idx]) >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `v`, `SUC j`] mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES] >>
    impl_tac
    >- (fs[] >> rw[] >> first_x_assum (qspec_then `SUC k` mp_tac) >>
        simp[arithmeticTheory.ADD_CLAUSES])
    >> simp[]
  )
  >> simp[lift_result_def] >> metis_tac[R_term_idx_change]
QED

(* Reversed direction: run_insts first, exec_block second.
   Same induction as exec_block_prefix_fail_lift but swapped order. *)
Theorem run_insts_lift_exec_block:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) prefix.
  valid_state_rel R_ok R_term ==>
  !fuel ctx bb s j.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    ~(?s'. run_insts fuel ctx prefix s = OK s')
  ==>
    lift_result R_ok R_term R_term
      (run_insts fuel ctx prefix s)
      (exec_block fuel ctx bb (s with vs_inst_idx := j))
Proof
  gen_tac >> gen_tac >> Induct >- rw[run_insts_def] >>
  rpt strip_tac >>
  rename1 `h :: prefix` >>
  `j < LENGTH bb.bb_instructions` by fs[] >>
  `EL j bb.bb_instructions = h` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst fuel ctx h (s with vs_inst_idx := j) =
   exec_result_map (\s'. s' with vs_inst_idx := j)
     (step_inst fuel ctx h s)` by
    (fs[] >> simp[step_inst_idx_indep]) >>
  fs[run_insts_def] >>
  ONCE_REWRITE_TAC[exec_block_def] >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[exec_result_map_def]
  >- (
    (* OK: recurse *)
    `v.vs_inst_idx = s.vs_inst_idx` by
      (fs[] >> metis_tac[step_inst_preserves_inst_idx]) >>
    first_x_assum (qspecl_then [`fuel`, `ctx`, `bb`, `v`, `SUC j`] mp_tac) >>
    simp[arithmeticTheory.ADD_CLAUSES] >>
    impl_tac
    >- (fs[] >> rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >>
        simp[arithmeticTheory.ADD_CLAUSES])
    >> simp[]
  )
  >> simp[lift_result_def] >> metis_tac[R_term_idx_change2]
QED

(* ===== Block-level simulation (idx=0 precondition) ===== *)

(* step_inst Error is idx-independent: if step_inst errors at idx=0,
   it errors at any idx. *)
Triviality step_inst_error_idx_indep:
  !fuel ctx inst s e.
    step_inst fuel ctx inst (s with vs_inst_idx := 0) = Error e ==>
    !n. step_inst fuel ctx inst (s with vs_inst_idx := n) = Error e
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE` >> fs[step_inst_non_invoke]
  >- (
    fs[step_inst_def, eval_ops_inst_idx, setup_callee_def] >>
    rpt BasicProvers.FULL_CASE_TAC >> fs[] >>
    gvs[bind_outputs_def]
  ) >>
  (* non-INVOKE: step_inst = step_inst_base *)
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    (* norm0(base(s with idx:=k)) = norm0(base(s)) for all k.
       Substituting base(s with idx:=0) = Error e and simplifying,
       norm0(base(s with idx:=n)) = Error e.
       Cases on base(s with idx:=n): must be Error. *)
    `exec_result_map (\s'. s' with vs_inst_idx := 0)
       (step_inst_base inst (s with vs_inst_idx := n)) = Error e` by (
      qspecl_then [`inst`, `s`, `n`] mp_tac
        terminator_step_inst_base_idx_norm0 >>
      qspecl_then [`inst`, `s`, `0`] mp_tac
        terminator_step_inst_base_idx_norm0 >>
      simp[exec_result_map_def]) >>
    Cases_on `step_inst_base inst (s with vs_inst_idx := n)` >>
    gvs[exec_result_map_def]
  ) >>
  (* Non-terminator non-INVOKE: full idx-indep *)
  qspecl_then [`inst`, `s`, `0`]
    mp_tac step_inst_inst_idx_indep >> simp[] >>
  Cases_on `step_inst_base inst s` >> simp[exec_result_map_def] >>
  disch_tac >>
  qspecl_then [`inst`, `s`, `n`]
    mp_tac step_inst_inst_idx_indep >> simp[exec_result_map_def]
QED

(* Corollary: error at idx=0 implies error at original idx *)
Theorem step_inst_error_idx_recover:
  !fuel ctx inst st e.
    step_inst fuel ctx inst (st with vs_inst_idx := 0) = Error e ==>
    step_inst fuel ctx inst st = Error e
Proof
  rpt strip_tac >>
  `!n. step_inst fuel ctx inst (st with vs_inst_idx := n) = Error e`
    by metis_tac[step_inst_error_idx_indep] >>
  pop_assum (qspec_then `st.vs_inst_idx` mp_tac) >>
  Cases_on `st` >> simp[venom_state_fn_updates]
QED

(* Reusable tactic for exec_block_preserves_R_block goals *)
val rbpr_tac =
  irule exec_block_preserves_R_block >> rpt conj_tac
  >- (rpt strip_tac >> res_tac)
  >- fs[]
  >- fs[]
  >- (irule R_ok_idx_change >> fs[] >> metis_tac[])
  >- fs[];

(* Continuation lemma: after step_inst OK/OK with R_ok v1 v2,
   bridge IH(v2) + R_block(bb, v1→v2) to get simulation for
   exec_block bb v1 vs exec_block transformed v2. *)
Theorem block_sim_continuation:
  !R_ok R_term bb tbb fuel ctx v1 v2 i j g.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    R_ok v1 v2 /\
    (!inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    ((?e. exec_block fuel ctx bb (v2 with vs_inst_idx := SUC i) = Error e) \/
     lift_result R_ok R_term R_term
       (exec_block fuel ctx bb (v2 with vs_inst_idx := SUC i))
       (exec_block fuel ctx tbb (v2 with vs_inst_idx := j)))
  ==>
    (?e. exec_block fuel ctx bb (v1 with vs_inst_idx := SUC i) = Error e) \/
    lift_result R_ok R_term R_term
      (exec_block fuel ctx bb (v1 with vs_inst_idx := SUC i))
      (exec_block fuel ctx tbb (v2 with vs_inst_idx := j))
Proof
  rpt strip_tac >>
  `lift_result R_ok R_term R_term
     (exec_block fuel ctx bb (v1 with vs_inst_idx := SUC i))
     (exec_block fuel ctx bb (v2 with vs_inst_idx := SUC i))` by (
    irule exec_block_preserves_R_block >> rpt conj_tac
    >- (rpt strip_tac >> res_tac)
    >- fs[]
    >- fs[]
    >- metis_tac[R_ok_idx_change]
    >- fs[]
  ) >>
  gvs[]
  >- (
    (* IH Error: R_block forces v1 to error too *)
    Cases_on `exec_block fuel ctx bb (v1 with vs_inst_idx := SUC i)` >>
    gvs[lift_result_def]
  )
  >- (
    (* IH lift_result: compose via transitivity *)
    DISJ2_TAC >>
    irule lift_result_trans_proof >>
    conj_tac >- fs[] >> conj_tac >- fs[] >> conj_tac >- fs[] >>
    qexists_tac `exec_block fuel ctx bb (v2 with vs_inst_idx := SUC i)` >>
    fs[]
  )
QED

(* Block-level simulation with execution-threaded soundness.
   Threads soundness through execution using transfer_sound
   and idx-independence of step_inst.

   Key insight: at instruction i, the exec_block state has vs_inst_idx = i,
   but soundness holds at the "natural" state with vs_inst_idx = 0
   (step_inst preserves idx, exec_block adjusts it). Using
   step_inst_idx_indep, we factor out the idx shift and apply the
   simulation at the natural state where soundness holds. *)

(* Specialization of exec_block_skip_prefix for a single instruction.
   Proved in clean context to avoid simp/fs loops in rich assumption contexts. *)
Triviality exec_block_skip_one[local]:
  !fuel ctx bb s j inst s'.
    j < LENGTH bb.bb_instructions /\
    EL j bb.bb_instructions = inst /\
    ~is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    step_inst fuel ctx inst s = OK s'
  ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := SUC j)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`[inst]`, `fuel`, `ctx`, `bb`, `s`, `j`, `s'`]
    mp_tac exec_block_skip_prefix >>
  impl_tac >- fs[run_insts_singleton] >>
  simp[arithmeticTheory.ADD1]
QED

(* Core block simulation theorem.
   Uses per-block transfer_sound_wf (restricted to well-formed instructions) for
   maximum generality. analysis_block_sim (below) wraps this with the
   stronger but more common transfer_sound hypothesis. *)
(* Generalized version of analysis_block_sim_wf: works for arbitrary
   vs_inst_idx <= LENGTH, not just vs_inst_idx = 0. Needed because
   analysis_run_block_sim must apply block sim at phi_prefix_length
   (not 0) for the parallel PHI semantics. *)
Theorem analysis_block_sim_from_wf:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!fuel ctx' v inst s s'.
       MEM inst bb.bb_instructions /\
       inst_wf inst /\ sound v s /\
       step_inst fuel ctx' inst s = OK s' ==>
       sound (transfer run_ctx inst v) s') /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s.
      s.vs_inst_idx <= LENGTH bb.bb_instructions /\
      sound (df_at bottom result bb.bb_label s.vs_inst_idx)
            (s with vs_inst_idx := 0) ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb)
           (s with vs_inst_idx :=
              LENGTH (FLAT (TAKE s.vs_inst_idx
                (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)))))
Proof
  rpt strip_tac >>
  simp[analysis_block_transform_def] >>
  qabbrev_tac `g = \idx inst. f (df_at bottom result bb.bb_label idx) inst` >>
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx)
           (s with vs_inst_idx := 0) ==>
     (?e. exec_block fuel ctx bb s = Error e) \/
     lift_result R_ok R_term R_term (exec_block fuel ctx bb s)
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s with vs_inst_idx :=
             LENGTH (FLAT (TAKE s.vs_inst_idx (MAPi g bb.bb_instructions)))))`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions - s.vs_inst_idx`, `fuel`, `ctx`, `s`] mp_tac) >>
      simp[]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    (* Base: i >= LENGTH, both Error *)
    `i = LENGTH bb.bb_instructions` by fs[] >>
    DISJ1_TAC >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  (* Inductive step: i < LENGTH *)
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qabbrev_tac `v = df_at bottom result bb.bb_label i` >>
  `inst_wf (EL i bb.bb_instructions)` by metis_tac[EVERY_EL] >>
  (* AIS facts: save simulation clause as ML val, put structural as assumptions *)
  qpat_x_assum `analysis_inst_simulates _ _ _ _`
    (fn ais =>
      let val ais' = REWRITE_RULE [analysis_inst_simulates_def] ais
          val (sim, structural) = CONJ_PAIR ais'
      in
        ASSUME_TAC sim >> ASSUME_TAC structural
      end) >>
  (* inst_transform_structural f kept as biconditional; clauses extracted per-case *)
  (* EL into FLAT for transformed block *)
  sg `!k. k < LENGTH (g i (EL i bb.bb_instructions)) ==>
       EL (LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) + k)
          (FLAT (MAPi g bb.bb_instructions)) =
       EL k (g i (EL i bb.bb_instructions))`
  >- (rpt strip_tac >> irule EL_FLAT_MAPi >> simp[]) >>
  sg `LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
      LENGTH (g i (EL i bb.bb_instructions)) <=
      LENGTH (FLAT (MAPi g bb.bb_instructions))`
  >- (irule FLAT_MAPi_offset_bound >> simp[]) >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  qabbrev_tac `j = LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions)))` >>
  `g i inst = f v inst` by simp[Abbr `g`, Abbr `v`, Abbr `inst`] >>
  (* Establish exec_block unrolling as a fact, then SUBST1_TAC *)
  sg `exec_block fuel ctx bb s' =
      case step_inst fuel ctx inst s' of
        OK s'' =>
          if is_terminator inst.inst_opcode then
            if s''.vs_halted then Halt s'' else OK s''
          else exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
      | Halt s'' => Halt s''
      | Abort a s'' => Abort a s''
      | IntRet rv ss => IntRet rv ss
      | Error e => Error e`
  >- (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `i`]
  ) >>
  pop_assum SUBST1_TAC >>
  (* AIS at idx=0: Error \/ lift_result *)
  `sound v (s' with vs_inst_idx := 0)` by fs[Abbr `v`] >>
  (* Use the sim clause directly (keep for non-term case) *)
  first_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`,
                              `s' with vs_inst_idx := 0`] mp_tac) >>
  impl_tac >- fs[] >>
  strip_tac
  >- (
    (* AIS Error: step_inst at idx=0 errors, bridge to s' via idx_indep *)
    DISJ1_TAC >>
    `s' with vs_inst_idx := i = s'` by
      simp[Abbr `i`, venom_state_component_equality] >>
    `step_inst fuel ctx inst s' = Error e` by metis_tac[step_inst_error_idx_indep] >>
    simp[]
  ) >>
  (* AIS lift_result from here on *)
  (* === Terminator case === *)
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `?inst'. f v inst = [inst'] /\ is_terminator inst'.inst_opcode` by (
      qhdtm_x_assum `inst_transform_structural`
        (fn th => metis_tac [CONJUNCT1 (REWRITE_RULE [inst_transform_structural_def] th)]) >> simp[]) >>
    `g i inst = [inst']` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst'` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`, Abbr `j`]) >>
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst (s' with vs_inst_idx := 0))
       (step_inst fuel ctx inst' (s' with vs_inst_idx := 0))` by
      fs[run_insts_singleton] >>
    DISJ2_TAC >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def] >>
    irule lift_result_trans_proof >>
    conj_tac >- fs[] >> conj_tac >- fs[] >> conj_tac >- fs[] >>
    qexists_tac `case step_inst fuel ctx inst' (s' with vs_inst_idx := 0) of
       OK s'' => if s''.vs_halted then Halt s'' else OK s''
     | Halt s' => Halt s' | Abort a s' => Abort a s'
     | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
    conj_tac
    >- (
      irule lift_result_trans_proof >>
      conj_tac >- fs[] >> conj_tac >- fs[] >> conj_tac >- fs[] >>
      qexists_tac `case step_inst fuel ctx inst (s' with vs_inst_idx := 0) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s' | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
      conj_tac
      >- (irule terminator_exec_block_step_lift >> simp[])
      >- (irule lift_result_halt_wrap >> simp[])
    )
    >- (
      `(s' with vs_inst_idx := 0) with vs_inst_idx := j =
       s' with vs_inst_idx := j` by simp[] >>
      pop_assum (SUBST1_TAC o SYM) >>
      irule terminator_exec_block_step_lift >> simp[]
    )
  ) >>
  (* === INVOKE case === *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* Get inst' from structural *)
    `?inst'. f v inst = [inst'] /\ inst'.inst_opcode = INVOKE` by (
      qhdtm_x_assum `inst_transform_structural`
        (fn th => metis_tac [CONJUNCT1 (CONJUNCT2 (REWRITE_RULE [inst_transform_structural_def] th))]) >> simp[]) >>
    `g i inst = [inst']` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst'` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
    (* lift_result between step_inst inst and inst' at idx=0 *)
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst (s' with vs_inst_idx := 0))
       (step_inst fuel ctx inst' (s' with vs_inst_idx := 0))` by
      fs[run_insts_singleton] >>
    (* Bridge lift_result from idx=0 to s' (idx=i) *)
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst s')
       (step_inst fuel ctx inst' s')` by (
      `s' = (s' with vs_inst_idx := 0) with vs_inst_idx := i` by
        simp[Abbr `i`, venom_state_component_equality] >>
      pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
      irule invoke_lift_result_idx_bridge >> fs[]
    ) >>
    (* Unroll RHS exec_block at j *)
    `exec_block fuel ctx
       (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
       (s' with vs_inst_idx := j) =
     (case step_inst fuel ctx inst' (s' with vs_inst_idx := j) of
        OK s'' => exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s'' with vs_inst_idx :=
             SUC (LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions)))))
      | Halt s'' => Halt s''
      | Abort a s'' => Abort a s''
      | IntRet rv ss => IntRet rv ss
      | Error e => Error e)` by (
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      simp[get_instruction_def, is_terminator_def]
    ) >>
    pop_assum SUBST1_TAC >>
    simp[] >>
    (* Case split on step_inst *)
    `step_inst fuel ctx inst' (s' with vs_inst_idx := j) =
     case step_inst fuel ctx inst' s' of
       OK s'' => OK (s'' with vs_inst_idx := j)
     | x => x` by simp[invoke_step_inst_idx_OK_only] >>
    Cases_on `step_inst fuel ctx inst s'` >>
    Cases_on `step_inst fuel ctx inst' s'` >>
    gvs[lift_result_def]
    >- (
    (* INVOKE OK/OK case *)
    `step_inst fuel ctx inst (s' with vs_inst_idx := 0) =
     OK (v' with vs_inst_idx := 0)` by
      (irule step_inst_at_0 >> fs[]) >>
    `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
    `sound (transfer run_ctx inst v) (v' with vs_inst_idx := 0)` by (
      first_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`,
          `s' with vs_inst_idx := 0`, `v' with vs_inst_idx := 0`] mp_tac) >>
      simp[]) >>
    `transfer run_ctx inst v = df_at bottom result bb.bb_label (SUC i)` by (
      `SUC i <= LENGTH bb.bb_instructions` by fs[] >>
      qpat_x_assum `!idx. SUC idx <= _ ==> _` (qspec_then `i` mp_tac) >>
      simp[Abbr `inst`, Abbr `v`]) >>
    `sound (df_at bottom result bb.bb_label (SUC i)) (v' with vs_inst_idx := 0)` by
      metis_tac[] >>
    (* Soundness transfer to v'' *)
    `R_ok (v' with vs_inst_idx := 0) (v'' with vs_inst_idx := 0)` by
      metis_tac[R_ok_idx_change] >>
    `sound (df_at bottom result bb.bb_label (SUC i))
           (v'' with vs_inst_idx := 0)` by metis_tac[] >>
    (* Apply block_sim_continuation: v' ~ v'' via R_ok,
       then IH at SUC i for v'' gives Error \/ lift_result *)
    irule block_sim_continuation >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (* IH for v'' at SUC i *)
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) = SUC j` by (
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
       LENGTH (g i (EL i bb.bb_instructions))`
        by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
      simp[Abbr `j`, Abbr `inst`]) >>
    qpat_x_assum `!m. m < _ ==> !fuel' ctx' s'. _`
      (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
    impl_tac >- decide_tac >>
    disch_then (qspecl_then [`fuel`, `ctx`,
      `v'' with vs_inst_idx := SUC i`] mp_tac) >>
    SIMP_TAC (srw_ss()) [] >>
    impl_tac >- (rpt conj_tac >> TRY decide_tac >> first_assum ACCEPT_TAC) >>
    metis_tac[]
    )
  ) >>
  (* === PHI case === *)
  Cases_on `inst.inst_opcode = PHI`
  >- (
    (* PHI gives Error in step_inst_base, so exec_block errors out.
       The conclusion (?e. exec_block ... = Error e) \/ ... is satisfied
       by the first disjunct. *)
    DISJ1_TAC >> simp[step_inst_phi_error]
  ) >>
  (* === Non-term non-INVOKE non-PHI case === *)
  `EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
    (f v inst)` by (
    qhdtm_x_assum `inst_transform_structural`
      (fn th => mp_tac (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (REWRITE_RULE [inst_transform_structural_def] th))))) >>
    fs[EVERY_MEM] >> metis_tac[]) >>
  (* Derive simulation at s' via idx-independence detour through idx=0 *)
  `lift_result R_ok R_term R_term (step_inst fuel ctx inst s')
    (run_insts fuel ctx (f v inst) s')` by (
    qabbrev_tac `s_nat = s' with vs_inst_idx := 0` >>
    `sound v s_nat` by simp[Abbr `v`, Abbr `s_nat`] >>
    `lift_result R_ok R_term R_term (step_inst fuel ctx inst s_nat)
      (run_insts fuel ctx (f v inst) s_nat)` by (
      first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`, `s_nat`] mp_tac) >>
      simp[]) >>
    `s' = s_nat with vs_inst_idx := i` by
      simp[Abbr `s_nat`, Abbr `i`, venom_state_component_equality] >>
    `step_inst fuel ctx inst s' =
     exec_result_map (\s''. s'' with vs_inst_idx := i)
       (step_inst fuel ctx inst s_nat)` by (
      qpat_assum `s' = _` (fn th =>
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[step_inst_idx_indep]) >>
    `run_insts fuel ctx (f v inst) s' =
     exec_result_map (\s''. s'' with vs_inst_idx := i)
       (run_insts fuel ctx (f v inst) s_nat)` by (
      qpat_x_assum `s' = _` (fn th =>
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[run_insts_idx_indep]) >>
    ntac 2 (pop_assum SUBST1_TAC) >>
    irule lift_result_exec_result_map >>
    simp[] >> metis_tac[R_ok_idx_change, R_term_idx_change_both]) >>
  (* Case split on step_inst. After simp[], Error solved, 4 goals remain:
     OK, Halt, Abort, IntRet (in constructor order). *)
  Cases_on `step_inst fuel ctx inst s'` >> simp[]
  (* After simp: Error case solved, 4 goals remain: OK, Halt, Abort, IntRet *)
  (* Halt/Abort/IntRet dispatched first, then OK case *)
  >- (
    (* === OK case === *)
    rename1 `step_inst _ _ _ _ = OK st1` >>
    `st1.vs_inst_idx = s'.vs_inst_idx` by
      metis_tac[step_inst_preserves_inst_idx] >>
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
     j + LENGTH (g i inst)` by (
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
       LENGTH (g i (EL i bb.bb_instructions))`
        by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
      simp[Abbr `j`, Abbr `inst`]) >>
    (* Case split on run_insts *)
    Cases_on `run_insts fuel ctx (f v inst) s'`
    >- (
      (* run_insts OK: skip prefix, establish soundness, apply IH *)
      rename1 `run_insts _ _ _ _ = OK st2` >>
      `st2.vs_inst_idx = s'.vs_inst_idx` by
        metis_tac[run_insts_preserves_idx] >>
      `R_ok st1 st2` by (
        qpat_x_assum `lift_result _ _ _ (OK _) (OK _)` mp_tac >>
        simp[lift_result_def]) >>
      (* Skip past the f v inst prefix in the transformed block *)
      `exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
         (s' with vs_inst_idx := j) =
       exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
         (st2 with vs_inst_idx := j + LENGTH (g i inst))` by (
        qspecl_then [`f v inst`, `fuel`, `ctx`,
          `bb with bb_instructions := FLAT (MAPi g bb.bb_instructions)`,
          `s'`, `j`, `st2`] mp_tac exec_block_skip_prefix >>
        impl_tac >- fs[] >>
        simp[]) >>
      `j + LENGTH (g i inst) = j + LENGTH (f v inst)` by simp[] >>
      pop_assum (fn th => FULL_SIMP_TAC (srw_ss()) [th]) >>
      (* Establish soundness at SUC i for st1 *)
      `sound (df_at bottom result bb.bb_label (SUC i))
             (st1 with vs_inst_idx := 0)` by (
        `df_at bottom result bb.bb_label (SUC i) =
         transfer run_ctx (EL i bb.bb_instructions)
           (df_at bottom result bb.bb_label i)` by
          (qpat_x_assum `!idx. SUC idx <= _ ==> _`
            (qspec_then `i` mp_tac) >> simp[]) >>
        pop_assum SUBST1_TAC >>
        `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
        `step_inst fuel ctx inst (s' with vs_inst_idx := 0) =
         OK (st1 with vs_inst_idx := 0)` by
          (irule step_inst_at_0 >> fs[]) >>
        first_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`,
          `s' with vs_inst_idx := 0`, `st1 with vs_inst_idx := 0`] mp_tac) >>
        simp[Abbr `v`, Abbr `inst`]) >>
      (* Transfer soundness from st1 to st2 via R_ok *)
      `R_ok (st1 with vs_inst_idx := 0) (st2 with vs_inst_idx := 0)` by (
        match_mp_tac (Q.SPECL [`R_ok`, `R_term`] R_ok_idx_change) >>
        simp[]) >>
      `sound (df_at bottom result bb.bb_label (SUC i))
             (st2 with vs_inst_idx := 0)` by (
        qpat_assum `!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> _`
          (qspecl_then [`df_at bottom result bb.bb_label (SUC i)`,
             `st1 with vs_inst_idx := 0`,
             `st2 with vs_inst_idx := 0`] mp_tac) >>
        simp[]) >>
      (* Apply block_sim_continuation + IH *)
      irule block_sim_continuation >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       j + LENGTH (g i inst)` by (
        `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
         LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
         LENGTH (g i (EL i bb.bb_instructions))`
          by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
        simp[Abbr `j`, Abbr `inst`]) >>
      qpat_x_assum `!m. m < _ ==> !fuel' ctx' s'. _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then (qspecl_then [`fuel`, `ctx`,
        `st2 with vs_inst_idx := SUC i`] mp_tac) >>
      SIMP_TAC (srw_ss()) [] >>
      impl_tac >- (rpt conj_tac >> TRY decide_tac >> first_assum ACCEPT_TAC) >>
      simp[]
    )
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
  )
  (* === Halt/Abort/IntRet step_inst cases === *)
  (* step_inst is non-OK, so run_insts can't be OK either.
     Chain: step_inst result ~ run_insts result ~ exec_block on transformed. *)
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
QED

Theorem analysis_block_sim_wf:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (* transfer_sound_wf restricted to block instructions *)
    (!fuel ctx' v inst s s'.
       MEM inst bb.bb_instructions /\
       inst_wf inst /\ sound v s /\
       step_inst fuel ctx' inst s = OK s' ==>
       sound (transfer run_ctx inst v) s') /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  simp[analysis_block_transform_def] >>
  qabbrev_tac `g = \idx inst. f (df_at bottom result bb.bb_label idx) inst` >>
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions /\
     sound (df_at bottom result bb.bb_label s.vs_inst_idx)
           (s with vs_inst_idx := 0) ==>
     (?e. exec_block fuel ctx bb s = Error e) \/
     lift_result R_ok R_term R_term (exec_block fuel ctx bb s)
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s with vs_inst_idx :=
             LENGTH (FLAT (TAKE s.vs_inst_idx (MAPi g bb.bb_instructions)))))`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      `s with vs_inst_idx := 0 = s` by fs[venom_state_component_equality] >>
      simp[TAKE_0]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    (* Base: i >= LENGTH, both Error *)
    `i = LENGTH bb.bb_instructions` by fs[] >>
    DISJ1_TAC >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  (* Inductive step: i < LENGTH *)
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qabbrev_tac `v = df_at bottom result bb.bb_label i` >>
  `inst_wf (EL i bb.bb_instructions)` by metis_tac[EVERY_EL] >>
  (* AIS facts: save simulation clause as ML val, put structural as assumptions *)
  qpat_x_assum `analysis_inst_simulates _ _ _ _`
    (fn ais =>
      let val ais' = REWRITE_RULE [analysis_inst_simulates_def] ais
          val (sim, structural) = CONJ_PAIR ais'
      in
        ASSUME_TAC sim >> ASSUME_TAC structural
      end) >>
  (* inst_transform_structural f kept as biconditional; clauses extracted per-case *)
  (* EL into FLAT for transformed block *)
  sg `!k. k < LENGTH (g i (EL i bb.bb_instructions)) ==>
       EL (LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) + k)
          (FLAT (MAPi g bb.bb_instructions)) =
       EL k (g i (EL i bb.bb_instructions))`
  >- (rpt strip_tac >> irule EL_FLAT_MAPi >> simp[]) >>
  sg `LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
      LENGTH (g i (EL i bb.bb_instructions)) <=
      LENGTH (FLAT (MAPi g bb.bb_instructions))`
  >- (irule FLAT_MAPi_offset_bound >> simp[]) >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  qabbrev_tac `j = LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions)))` >>
  `g i inst = f v inst` by simp[Abbr `g`, Abbr `v`, Abbr `inst`] >>
  (* Establish exec_block unrolling as a fact, then SUBST1_TAC *)
  sg `exec_block fuel ctx bb s' =
      case step_inst fuel ctx inst s' of
        OK s'' =>
          if is_terminator inst.inst_opcode then
            if s''.vs_halted then Halt s'' else OK s''
          else exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
      | Halt s'' => Halt s''
      | Abort a s'' => Abort a s''
      | IntRet rv ss => IntRet rv ss
      | Error e => Error e`
  >- (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `i`]
  ) >>
  pop_assum SUBST1_TAC >>
  (* AIS at idx=0: Error \/ lift_result *)
  `sound v (s' with vs_inst_idx := 0)` by fs[Abbr `v`] >>
  (* Use the sim clause directly (keep for non-term case) *)
  first_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`,
                              `s' with vs_inst_idx := 0`] mp_tac) >>
  impl_tac >- fs[] >>
  strip_tac
  >- (
    (* AIS Error: step_inst at idx=0 errors, bridge to s' via idx_indep *)
    DISJ1_TAC >>
    `s' with vs_inst_idx := i = s'` by
      simp[Abbr `i`, venom_state_component_equality] >>
    `step_inst fuel ctx inst s' = Error e` by metis_tac[step_inst_error_idx_indep] >>
    simp[]
  ) >>
  (* AIS lift_result from here on *)
  (* === Terminator case === *)
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `?inst'. f v inst = [inst'] /\ is_terminator inst'.inst_opcode` by (
      qhdtm_x_assum `inst_transform_structural`
        (fn th => metis_tac [CONJUNCT1 (REWRITE_RULE [inst_transform_structural_def] th)]) >> simp[]) >>
    `g i inst = [inst']` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst'` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`, Abbr `j`]) >>
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst (s' with vs_inst_idx := 0))
       (step_inst fuel ctx inst' (s' with vs_inst_idx := 0))` by
      fs[run_insts_singleton] >>
    DISJ2_TAC >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def] >>
    irule lift_result_trans_proof >>
    conj_tac >- fs[] >> conj_tac >- fs[] >> conj_tac >- fs[] >>
    qexists_tac `case step_inst fuel ctx inst' (s' with vs_inst_idx := 0) of
       OK s'' => if s''.vs_halted then Halt s'' else OK s''
     | Halt s' => Halt s' | Abort a s' => Abort a s'
     | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
    conj_tac
    >- (
      irule lift_result_trans_proof >>
      conj_tac >- fs[] >> conj_tac >- fs[] >> conj_tac >- fs[] >>
      qexists_tac `case step_inst fuel ctx inst (s' with vs_inst_idx := 0) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s' | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
      conj_tac
      >- (irule terminator_exec_block_step_lift >> simp[])
      >- (irule lift_result_halt_wrap >> simp[])
    )
    >- (
      `(s' with vs_inst_idx := 0) with vs_inst_idx := j =
       s' with vs_inst_idx := j` by simp[] >>
      pop_assum (SUBST1_TAC o SYM) >>
      irule terminator_exec_block_step_lift >> simp[]
    )
  ) >>
  (* === INVOKE case === *)
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    (* Get inst' from structural *)
    `?inst'. f v inst = [inst'] /\ inst'.inst_opcode = INVOKE` by (
      qhdtm_x_assum `inst_transform_structural`
        (fn th => metis_tac [CONJUNCT1 (CONJUNCT2 (REWRITE_RULE [inst_transform_structural_def] th))]) >> simp[]) >>
    `g i inst = [inst']` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst'` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
    (* lift_result between step_inst inst and inst' at idx=0 *)
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst (s' with vs_inst_idx := 0))
       (step_inst fuel ctx inst' (s' with vs_inst_idx := 0))` by
      fs[run_insts_singleton] >>
    (* Bridge lift_result from idx=0 to s' (idx=i) *)
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst s')
       (step_inst fuel ctx inst' s')` by (
      `s' = (s' with vs_inst_idx := 0) with vs_inst_idx := i` by
        simp[Abbr `i`, venom_state_component_equality] >>
      pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
      irule invoke_lift_result_idx_bridge >> fs[]
    ) >>
    (* Unroll RHS exec_block at j *)
    `exec_block fuel ctx
       (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
       (s' with vs_inst_idx := j) =
     (case step_inst fuel ctx inst' (s' with vs_inst_idx := j) of
        OK s'' => exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s'' with vs_inst_idx :=
             SUC (LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions)))))
      | Halt s'' => Halt s''
      | Abort a s'' => Abort a s''
      | IntRet rv ss => IntRet rv ss
      | Error e => Error e)` by (
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      simp[get_instruction_def, is_terminator_def]
    ) >>
    pop_assum SUBST1_TAC >>
    simp[] >>
    (* Case split on step_inst *)
    `step_inst fuel ctx inst' (s' with vs_inst_idx := j) =
     case step_inst fuel ctx inst' s' of
       OK s'' => OK (s'' with vs_inst_idx := j)
     | x => x` by simp[invoke_step_inst_idx_OK_only] >>
    Cases_on `step_inst fuel ctx inst s'` >>
    Cases_on `step_inst fuel ctx inst' s'` >>
    gvs[lift_result_def]
    >- (
    (* INVOKE OK/OK case *)
    `step_inst fuel ctx inst (s' with vs_inst_idx := 0) =
     OK (v' with vs_inst_idx := 0)` by
      (irule step_inst_at_0 >> fs[]) >>
    `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
    `sound (transfer run_ctx inst v) (v' with vs_inst_idx := 0)` by (
      first_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`,
          `s' with vs_inst_idx := 0`, `v' with vs_inst_idx := 0`] mp_tac) >>
      simp[]) >>
    `transfer run_ctx inst v = df_at bottom result bb.bb_label (SUC i)` by (
      `SUC i <= LENGTH bb.bb_instructions` by fs[] >>
      qpat_x_assum `!idx. SUC idx <= _ ==> _` (qspec_then `i` mp_tac) >>
      simp[Abbr `inst`, Abbr `v`]) >>
    `sound (df_at bottom result bb.bb_label (SUC i)) (v' with vs_inst_idx := 0)` by
      metis_tac[] >>
    (* Soundness transfer to v'' *)
    `R_ok (v' with vs_inst_idx := 0) (v'' with vs_inst_idx := 0)` by
      metis_tac[R_ok_idx_change] >>
    `sound (df_at bottom result bb.bb_label (SUC i))
           (v'' with vs_inst_idx := 0)` by metis_tac[] >>
    (* Apply block_sim_continuation: v' ~ v'' via R_ok,
       then IH at SUC i for v'' gives Error \/ lift_result *)
    irule block_sim_continuation >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    (* IH for v'' at SUC i *)
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) = SUC j` by (
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
       LENGTH (g i (EL i bb.bb_instructions))`
        by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
      simp[Abbr `j`, Abbr `inst`]) >>
    qpat_x_assum `!m. m < _ ==> !fuel' ctx' s'. _`
      (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
    impl_tac >- decide_tac >>
    disch_then (qspecl_then [`fuel`, `ctx`,
      `v'' with vs_inst_idx := SUC i`] mp_tac) >>
    SIMP_TAC (srw_ss()) [] >>
    impl_tac >- (rpt conj_tac >> TRY decide_tac >> first_assum ACCEPT_TAC) >>
    metis_tac[]
    )
  ) >>
  (* === PHI case === *)
  Cases_on `inst.inst_opcode = PHI`
  >- (
    (* PHI gives Error in step_inst_base, so exec_block errors out.
       The conclusion (?e. exec_block ... = Error e) \/ ... is satisfied
       by the first disjunct. *)
    DISJ1_TAC >> simp[step_inst_phi_error]
  ) >>
  (* === Non-term non-INVOKE non-PHI case === *)
  `EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
    (f v inst)` by (
    qhdtm_x_assum `inst_transform_structural`
      (fn th => mp_tac (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (REWRITE_RULE [inst_transform_structural_def] th))))) >>
    fs[EVERY_MEM] >> metis_tac[]) >>
  (* Derive simulation at s' via idx-independence detour through idx=0 *)
  `lift_result R_ok R_term R_term (step_inst fuel ctx inst s')
    (run_insts fuel ctx (f v inst) s')` by (
    qabbrev_tac `s_nat = s' with vs_inst_idx := 0` >>
    `sound v s_nat` by simp[Abbr `v`, Abbr `s_nat`] >>
    `lift_result R_ok R_term R_term (step_inst fuel ctx inst s_nat)
      (run_insts fuel ctx (f v inst) s_nat)` by (
      first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`, `s_nat`] mp_tac) >>
      simp[]) >>
    `s' = s_nat with vs_inst_idx := i` by
      simp[Abbr `s_nat`, Abbr `i`, venom_state_component_equality] >>
    `step_inst fuel ctx inst s' =
     exec_result_map (\s''. s'' with vs_inst_idx := i)
       (step_inst fuel ctx inst s_nat)` by (
      qpat_assum `s' = _` (fn th =>
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[step_inst_idx_indep]) >>
    `run_insts fuel ctx (f v inst) s' =
     exec_result_map (\s''. s'' with vs_inst_idx := i)
       (run_insts fuel ctx (f v inst) s_nat)` by (
      qpat_x_assum `s' = _` (fn th =>
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[run_insts_idx_indep]) >>
    ntac 2 (pop_assum SUBST1_TAC) >>
    irule lift_result_exec_result_map >>
    simp[] >> metis_tac[R_ok_idx_change, R_term_idx_change_both]) >>
  (* Case split on step_inst. After simp[], Error solved, 4 goals remain:
     OK, Halt, Abort, IntRet (in constructor order). *)
  Cases_on `step_inst fuel ctx inst s'` >> simp[]
  (* After simp: Error case solved, 4 goals remain: OK, Halt, Abort, IntRet *)
  (* Halt/Abort/IntRet dispatched first, then OK case *)
  >- (
    (* === OK case === *)
    rename1 `step_inst _ _ _ _ = OK st1` >>
    `st1.vs_inst_idx = s'.vs_inst_idx` by
      metis_tac[step_inst_preserves_inst_idx] >>
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
     j + LENGTH (g i inst)` by (
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
       LENGTH (g i (EL i bb.bb_instructions))`
        by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
      simp[Abbr `j`, Abbr `inst`]) >>
    (* Case split on run_insts *)
    Cases_on `run_insts fuel ctx (f v inst) s'`
    >- (
      (* run_insts OK: skip prefix, establish soundness, apply IH *)
      rename1 `run_insts _ _ _ _ = OK st2` >>
      `st2.vs_inst_idx = s'.vs_inst_idx` by
        metis_tac[run_insts_preserves_idx] >>
      `R_ok st1 st2` by (
        qpat_x_assum `lift_result _ _ _ (OK _) (OK _)` mp_tac >>
        simp[lift_result_def]) >>
      (* Skip past the f v inst prefix in the transformed block *)
      `exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
         (s' with vs_inst_idx := j) =
       exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
         (st2 with vs_inst_idx := j + LENGTH (g i inst))` by (
        qspecl_then [`f v inst`, `fuel`, `ctx`,
          `bb with bb_instructions := FLAT (MAPi g bb.bb_instructions)`,
          `s'`, `j`, `st2`] mp_tac exec_block_skip_prefix >>
        impl_tac >- fs[] >>
        simp[]) >>
      `j + LENGTH (g i inst) = j + LENGTH (f v inst)` by simp[] >>
      pop_assum (fn th => FULL_SIMP_TAC (srw_ss()) [th]) >>
      (* Establish soundness at SUC i for st1 *)
      `sound (df_at bottom result bb.bb_label (SUC i))
             (st1 with vs_inst_idx := 0)` by (
        `df_at bottom result bb.bb_label (SUC i) =
         transfer run_ctx (EL i bb.bb_instructions)
           (df_at bottom result bb.bb_label i)` by
          (qpat_x_assum `!idx. SUC idx <= _ ==> _`
            (qspec_then `i` mp_tac) >> simp[]) >>
        pop_assum SUBST1_TAC >>
        `MEM inst bb.bb_instructions` by metis_tac[EL_MEM] >>
        `step_inst fuel ctx inst (s' with vs_inst_idx := 0) =
         OK (st1 with vs_inst_idx := 0)` by
          (irule step_inst_at_0 >> fs[]) >>
        first_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`,
          `s' with vs_inst_idx := 0`, `st1 with vs_inst_idx := 0`] mp_tac) >>
        simp[Abbr `v`, Abbr `inst`]) >>
      (* Transfer soundness from st1 to st2 via R_ok *)
      `R_ok (st1 with vs_inst_idx := 0) (st2 with vs_inst_idx := 0)` by (
        match_mp_tac (Q.SPECL [`R_ok`, `R_term`] R_ok_idx_change) >>
        simp[]) >>
      `sound (df_at bottom result bb.bb_label (SUC i))
             (st2 with vs_inst_idx := 0)` by (
        qpat_assum `!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> _`
          (qspecl_then [`df_at bottom result bb.bb_label (SUC i)`,
             `st1 with vs_inst_idx := 0`,
             `st2 with vs_inst_idx := 0`] mp_tac) >>
        simp[]) >>
      (* Apply block_sim_continuation + IH *)
      irule block_sim_continuation >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       j + LENGTH (g i inst)` by (
        `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
         LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
         LENGTH (g i (EL i bb.bb_instructions))`
          by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
        simp[Abbr `j`, Abbr `inst`]) >>
      qpat_x_assum `!m. m < _ ==> !fuel' ctx' s'. _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then (qspecl_then [`fuel`, `ctx`,
        `st2 with vs_inst_idx := SUC i`] mp_tac) >>
      SIMP_TAC (srw_ss()) [] >>
      impl_tac >- (rpt conj_tac >> TRY decide_tac >> first_assum ACCEPT_TAC) >>
      simp[]
    )
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
  )
  (* === Halt/Abort/IntRet step_inst cases === *)
  (* step_inst is non-OK, so run_insts can't be OK either.
     Chain: step_inst result ~ run_insts result ~ exec_block on transformed. *)
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
QED

(* Generalized wrapper: transfer_sound => analysis_block_sim_from_wf.
   Same as analysis_block_sim but works at arbitrary vs_inst_idx <= LENGTH. *)
Theorem analysis_block_sim_from:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    transfer_sound sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s.
      s.vs_inst_idx <= LENGTH bb.bb_instructions /\
      sound (df_at bottom result bb.bb_label s.vs_inst_idx)
            (s with vs_inst_idx := 0) ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb)
           (s with vs_inst_idx :=
              LENGTH (FLAT (TAKE s.vs_inst_idx
                (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)))))
Proof
  rpt strip_tac >>
  mp_tac analysis_block_sim_from_wf >>
  disch_then (qspecl_then [`R_ok`, `R_term`, `sound`, `f`, `bb`, `bottom`,
    `result`, `transfer`, `run_ctx`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >>
    fs[transfer_sound_def] >> res_tac) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  simp[]
QED

(* Backward-compatible wrapper: transfer_sound => transfer_sound_wf *)
Theorem analysis_block_sim:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    transfer_sound sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  mp_tac analysis_block_sim_wf >>
  disch_then (qspecl_then [`R_ok`, `R_term`, `sound`, `f`, `bb`, `bottom`,
    `result`, `transfer`, `run_ctx`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >>
    fs[transfer_sound_def] >> res_tac) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  simp[]
QED

(* Variant of analysis_block_sim_wf with a state_inv threaded alongside sound.
   Per-inst sim gets both sound v s AND state_inv s.
   Uses transfer_sound_wf (not transfer_sound) and requires inst_wf in
   the state_inv preservation hypothesis. *)
Theorem analysis_block_sim_inv:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (* Per-inst sim with both sound AND state_inv *)
    (!fuel ctx v inst s.
       sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result R_ok R_term R_term (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    inst_transform_structural f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    transfer_sound_wf sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    (* state_inv preserved through well-formed step_inst from this block *)
    (!fuel ctx inst s s'.
       MEM inst bb.bb_instructions /\
       inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (* state_inv preserved through R_ok *)
    (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s /\
      state_inv s ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac
  \\ qabbrev_tac `sound' = \(v:'a) s. sound v s /\
       state_inv (s with vs_inst_idx := 0)`
  \\ qspecl_then [`R_ok`, `R_term`, `sound'`, `f`, `bb`, `bottom`,
       `result`, `transfer`, `run_ctx`] mp_tac analysis_block_sim_wf
  \\ impl_tac
  >- (
    rpt conj_tac \\ TRY (first_assum ACCEPT_TAC)
    (* analysis_inst_simulates for sound' *)
    >- (simp[analysis_inst_simulates_def, Abbr `sound'`]
        \\ rpt strip_tac \\ res_tac)
    (* transfer_sound_wf for sound' *)
    >- (rpt strip_tac \\ gvs[Abbr `sound'`] \\ conj_tac
        >- (fs[transfer_sound_wf_def] \\ res_tac)
        \\ res_tac)
    (* sound' preserved by R_ok *)
    \\ rpt strip_tac \\ gvs[Abbr `sound'`] \\ conj_tac >- res_tac
    \\ qspecl_then [`R_ok`, `R_term`, `s1`, `s2`, `0`]
         mp_tac R_ok_idx_change \\ simp[]
    \\ disch_tac \\ res_tac)
  (* Apply result to our goal *)
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac)
  \\ simp[Abbr `sound'`]
  \\ disch_then irule
  \\ `s with vs_inst_idx := 0 = s` by
       (Cases_on `s` \\ gvs[venom_state_fn_updates])
  \\ gvs[]
QED

(* Generalized variant of analysis_block_sim_inv: works at arbitrary
   vs_inst_idx <= LENGTH rather than idx=0. Wraps analysis_block_sim_from_wf
   with sound' = sound v s /\ state_inv(s with vs_inst_idx := 0).
   Same preconditions as analysis_block_sim_inv. *)
Theorem analysis_block_sim_inv_from:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!fuel ctx v inst s.
       sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result R_ok R_term R_term (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    inst_transform_structural f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    transfer_sound_wf sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    (!fuel ctx inst s s'.
       MEM inst bb.bb_instructions /\
       inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx <= LENGTH bb.bb_instructions /\
      sound (df_at bottom result bb.bb_label s.vs_inst_idx)
            (s with vs_inst_idx := 0) /\
      state_inv (s with vs_inst_idx := 0) ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb)
           (s with vs_inst_idx :=
              LENGTH (FLAT (TAKE s.vs_inst_idx
                (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)))))
Proof
  rpt strip_tac >>
  qabbrev_tac `sound' = \(v:'a) s. sound v s /\
       state_inv (s with vs_inst_idx := 0)` >>
  qspecl_then [`R_ok`, `R_term`, `sound'`, `f`, `bb`, `bottom`,
       `result`, `transfer`, `run_ctx`] mp_tac analysis_block_sim_from_wf >>
  impl_tac
  >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (simp[analysis_inst_simulates_def, Abbr `sound'`]
        >> rpt strip_tac >> res_tac)
    >- (rpt strip_tac >> gvs[Abbr `sound'`] >> conj_tac
        >- (fs[transfer_sound_wf_def] >> res_tac)
        >> res_tac)
    >> rpt strip_tac >> gvs[Abbr `sound'`] >> conj_tac >- res_tac
    >> qspecl_then [`R_ok`, `R_term`, `s1`, `s2`, `0`]
         mp_tac R_ok_idx_change >> simp[]
    >> disch_tac >> res_tac) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  simp[Abbr `sound'`]
QED


(* Variant of analysis_block_sim_inv with block-restricted transfer soundness.
   The transfer_sound hypothesis only needs to hold for instructions that are
   in the block's bb_instructions (and from a block in fn.fn_blocks).
   Essential for passes where soundness depends on SSA/DFG properties
   that only hold for block-local instructions. *)
Theorem analysis_block_sim_inv_block:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb fn
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (* Per-inst sim with both sound AND state_inv *)
    (!fuel ctx v inst s.
       sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result R_ok R_term R_term (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    inst_transform_structural f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    MEM bb fn.fn_blocks /\
    transfer_sound_block_inv sound state_inv transfer run_ctx fn /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    (* state_inv preserved through well-formed step_inst from this block *)
    (!fuel ctx inst s s'.
       MEM inst bb.bb_instructions /\
       inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (* state_inv preserved through R_ok *)
    (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 /\
      sound (df_at bottom result bb.bb_label 0) s /\
      state_inv s ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac
  \\ qabbrev_tac `sound' = \(v:'a) s. sound v s /\
       state_inv (s with vs_inst_idx := 0)`
  \\ qspecl_then [`R_ok`, `R_term`, `sound'`, `f`, `bb`, `bottom`,
       `result`, `transfer`, `run_ctx`] mp_tac analysis_block_sim_wf
  \\ impl_tac
  >- (
    rpt conj_tac \\ TRY (first_assum ACCEPT_TAC)
    (* analysis_inst_simulates for sound' *)
    >- (simp[analysis_inst_simulates_def, Abbr `sound'`]
        \\ rpt strip_tac \\ res_tac)
    (* block-restricted transfer_sound for sound' *)
    >- (rpt strip_tac \\ gvs[Abbr `sound'`] \\ conj_tac
        >- (fs[transfer_sound_block_inv_def] \\ res_tac)
        \\ res_tac)
    (* sound' preserved by R_ok *)
    \\ rpt strip_tac \\ gvs[Abbr `sound'`] \\ conj_tac >- res_tac
    \\ qspecl_then [`R_ok`, `R_term`, `s1`, `s2`, `0`]
         mp_tac R_ok_idx_change \\ simp[]
    \\ disch_tac \\ res_tac)
  (* Apply result to our goal *)
  \\ disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac)
  \\ simp[Abbr `sound'`]
  \\ disch_then irule
  \\ `s with vs_inst_idx := 0 = s` by
       (Cases_on `s` \\ gvs[venom_state_fn_updates])
  \\ gvs[]
QED


(* Generalized variant of analysis_block_sim_inv_block: works at arbitrary
   vs_inst_idx <= LENGTH rather than idx=0. Wraps analysis_block_sim_from_wf
   with sound' = sound v s /\ state_inv(s with vs_inst_idx := 0).
   Same preconditions as analysis_block_sim_inv_block. *)
Theorem analysis_block_sim_inv_block_from:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb fn
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!fuel ctx v inst s.
       sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result R_ok R_term R_term (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    inst_transform_structural f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    MEM bb fn.fn_blocks /\
    transfer_sound_block_inv sound state_inv transfer run_ctx fn /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    (!fuel ctx inst s s'.
       MEM inst bb.bb_instructions /\
       inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx <= LENGTH bb.bb_instructions /\
      sound (df_at bottom result bb.bb_label s.vs_inst_idx)
            (s with vs_inst_idx := 0) /\
      state_inv (s with vs_inst_idx := 0) ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb)
           (s with vs_inst_idx :=
              LENGTH (FLAT (TAKE s.vs_inst_idx
                (MAPi (\idx inst. f (df_at bottom result bb.bb_label idx) inst)
                  bb.bb_instructions)))))
Proof
  rpt strip_tac >>
  qabbrev_tac `sound' = \(v:'a) s. sound v s /\
       state_inv (s with vs_inst_idx := 0)` >>
  qspecl_then [`R_ok`, `R_term`, `sound'`, `f`, `bb`, `bottom`,
       `result`, `transfer`, `run_ctx`] mp_tac analysis_block_sim_from_wf >>
  impl_tac
  >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
    >- (simp[analysis_inst_simulates_def, Abbr `sound'`]
        >> rpt strip_tac >> res_tac)
    >- (rpt strip_tac >> gvs[Abbr `sound'`] >> conj_tac
        >- (fs[transfer_sound_block_inv_def] >> res_tac)
        >> res_tac)
    >> rpt strip_tac >> gvs[Abbr `sound'`] >> conj_tac >- res_tac
    >> qspecl_then [`R_ok`, `R_term`, `s1`, `s2`, `0`]
         mp_tac R_ok_idx_change >> simp[]
    >> disch_tac >> res_tac) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >>
  simp[Abbr `sound'`]
QED

(* Variant of analysis_block_sim with universal soundness instead of
   transfer_sound + chain. Drops R_ok-monotonicity of sound and
   sound(df_at 0, s) precondition since universal soundness subsumes both. *)
Theorem analysis_block_sim_univ:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state).
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!i s. i < LENGTH bb.bb_instructions ==>
           sound (df_at bottom result bb.bb_label i) s)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  simp[analysis_block_transform_def] >>
  qabbrev_tac `g = \idx inst. f (df_at bottom result bb.bb_label idx) inst` >>
  `!n fuel ctx s.
     n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
     s.vs_inst_idx <= LENGTH bb.bb_instructions ==>
     (?e. exec_block fuel ctx bb s = Error e) \/
     lift_result R_ok R_term R_term (exec_block fuel ctx bb s)
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s with vs_inst_idx :=
             LENGTH (FLAT (TAKE s.vs_inst_idx (MAPi g bb.bb_instructions)))))`
    suffices_by (
      disch_then (qspecl_then
        [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `s`] mp_tac) >>
      `s with vs_inst_idx := 0 = s` by fs[venom_state_component_equality] >>
      simp[TAKE_0]) >>
  completeInduct_on `n` >> rpt strip_tac >>
  qabbrev_tac `i = s'.vs_inst_idx` >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    `i = LENGTH bb.bb_instructions` by fs[] >>
    DISJ1_TAC >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def]
  ) >>
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qabbrev_tac `v = df_at bottom result bb.bb_label i` >>
  `inst_wf (EL i bb.bb_instructions)` by metis_tac[EVERY_EL] >>
  qpat_x_assum `analysis_inst_simulates _ _ _ _`
    (fn ais =>
      let val ais' = REWRITE_RULE [analysis_inst_simulates_def] ais
          val (sim, structural) = CONJ_PAIR ais'
      in
        ASSUME_TAC sim >> ASSUME_TAC structural
      end) >>
  (* inst_transform_structural f kept as biconditional; clauses extracted per-case *)
  sg `!k. k < LENGTH (g i (EL i bb.bb_instructions)) ==>
       EL (LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) + k)
          (FLAT (MAPi g bb.bb_instructions)) =
       EL k (g i (EL i bb.bb_instructions))`
  >- (rpt strip_tac >> irule EL_FLAT_MAPi >> simp[]) >>
  sg `LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
      LENGTH (g i (EL i bb.bb_instructions)) <=
      LENGTH (FLAT (MAPi g bb.bb_instructions))`
  >- (irule FLAT_MAPi_offset_bound >> simp[]) >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  qabbrev_tac `j = LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions)))` >>
  `g i inst = f v inst` by simp[Abbr `g`, Abbr `v`, Abbr `inst`] >>
  sg `exec_block fuel ctx bb s' =
      case step_inst fuel ctx inst s' of
        OK s'' =>
          if is_terminator inst.inst_opcode then
            if s''.vs_halted then Halt s'' else OK s''
          else exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
      | Halt s'' => Halt s''
      | Abort a s'' => Abort a s''
      | IntRet rv ss => IntRet rv ss
      | Error e => Error e`
  >- (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `i`]
  ) >>
  pop_assum SUBST1_TAC >>
  `sound v (s' with vs_inst_idx := 0)` by fs[Abbr `v`] >>
  first_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`,
                              `s' with vs_inst_idx := 0`] mp_tac) >>
  impl_tac >- fs[] >>
  strip_tac
  >- (
    DISJ1_TAC >>
    `s' with vs_inst_idx := i = s'` by
      simp[Abbr `i`, venom_state_component_equality] >>
    `step_inst fuel ctx inst s' = Error e` by metis_tac[step_inst_error_idx_indep] >>
    simp[]
  ) >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `?inst'. f v inst = [inst'] /\ is_terminator inst'.inst_opcode` by (
      qhdtm_x_assum `inst_transform_structural`
        (fn th => metis_tac [CONJUNCT1 (REWRITE_RULE [inst_transform_structural_def] th)]) >> simp[]) >>
    `g i inst = [inst']` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst'` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `inst`, Abbr `j`]) >>
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst (s' with vs_inst_idx := 0))
       (step_inst fuel ctx inst' (s' with vs_inst_idx := 0))` by
      fs[run_insts_singleton] >>
    DISJ2_TAC >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def] >>
    irule lift_result_trans_proof >>
    conj_tac >- fs[] >> conj_tac >- fs[] >> conj_tac >- fs[] >>
    qexists_tac `case step_inst fuel ctx inst' (s' with vs_inst_idx := 0) of
       OK s'' => if s''.vs_halted then Halt s'' else OK s''
     | Halt s' => Halt s' | Abort a s' => Abort a s'
     | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
    conj_tac
    >- (
      irule lift_result_trans_proof >>
      conj_tac >- fs[] >> conj_tac >- fs[] >> conj_tac >- fs[] >>
      qexists_tac `case step_inst fuel ctx inst (s' with vs_inst_idx := 0) of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s' | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss | Error e => Error e` >>
      conj_tac
      >- (irule terminator_exec_block_step_lift >> simp[])
      >- (irule lift_result_halt_wrap >> simp[])
    )
    >- (
      `(s' with vs_inst_idx := 0) with vs_inst_idx := j =
       s' with vs_inst_idx := j` by simp[] >>
      pop_assum (SUBST1_TAC o SYM) >>
      irule terminator_exec_block_step_lift >> simp[]
    )
  ) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    `?inst'. f v inst = [inst'] /\ inst'.inst_opcode = INVOKE` by (
      qhdtm_x_assum `inst_transform_structural`
        (fn th => metis_tac [CONJUNCT1 (CONJUNCT2 (REWRITE_RULE [inst_transform_structural_def] th))]) >> simp[]) >>
    `g i inst = [inst']` by fs[] >>
    `j < LENGTH (FLAT (MAPi g bb.bb_instructions))` by fs[] >>
    `EL j (FLAT (MAPi g bb.bb_instructions)) = inst'` by
      (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst (s' with vs_inst_idx := 0))
       (step_inst fuel ctx inst' (s' with vs_inst_idx := 0))` by
      fs[run_insts_singleton] >>
    `lift_result R_ok R_term R_term
       (step_inst fuel ctx inst s')
       (step_inst fuel ctx inst' s')` by (
      `s' = (s' with vs_inst_idx := 0) with vs_inst_idx := i` by
        simp[Abbr `i`, venom_state_component_equality] >>
      pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
      irule invoke_lift_result_idx_bridge >> fs[]
    ) >>
    `exec_block fuel ctx
       (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
       (s' with vs_inst_idx := j) =
     (case step_inst fuel ctx inst' (s' with vs_inst_idx := j) of
        OK s'' => exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s'' with vs_inst_idx :=
             SUC (LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions)))))
      | Halt s'' => Halt s''
      | Abort a s'' => Abort a s''
      | IntRet rv ss => IntRet rv ss
      | Error e => Error e)` by (
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      simp[get_instruction_def, is_terminator_def]
    ) >>
    pop_assum SUBST1_TAC >>
    simp[] >>
    `step_inst fuel ctx inst' (s' with vs_inst_idx := j) =
     case step_inst fuel ctx inst' s' of
       OK s'' => OK (s'' with vs_inst_idx := j)
     | x => x` by simp[invoke_step_inst_idx_OK_only] >>
    Cases_on `step_inst fuel ctx inst s'` >>
    Cases_on `step_inst fuel ctx inst' s'` >>
    gvs[lift_result_def]
    >- (
    (* INVOKE OK/OK case — no soundness needed, IH has no soundness precond *)
    `R_ok (v' with vs_inst_idx := 0) (v'' with vs_inst_idx := 0)` by
      metis_tac[R_ok_idx_change] >>
    irule block_sim_continuation >>
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) = SUC j` by (
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
       LENGTH (g i (EL i bb.bb_instructions))`
        by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
      simp[Abbr `j`, Abbr `inst`]) >>
    qpat_x_assum `!m. m < _ ==> !fuel' ctx' s'. _`
      (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
    impl_tac >- decide_tac >>
    disch_then (qspecl_then [`fuel`, `ctx`,
      `v'' with vs_inst_idx := SUC i`] mp_tac) >>
    SIMP_TAC (srw_ss()) [] >>
    impl_tac >- (rpt conj_tac >> TRY decide_tac) >>
    metis_tac[]
    )
  ) >>
  (* === PHI case === *)
  Cases_on `inst.inst_opcode = PHI`
  >- (
    (* PHI gives Error in step_inst_base, so exec_block errors out.
       The conclusion (?e. exec_block ... = Error e) \/ ... is satisfied
       by the first disjunct. *)
    DISJ1_TAC >> simp[step_inst_phi_error]
  ) >>
  (* === Non-term non-INVOKE non-PHI case === *)
  `EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
    (f v inst)` by (
    qhdtm_x_assum `inst_transform_structural`
      (fn th => mp_tac (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (REWRITE_RULE [inst_transform_structural_def] th))))) >>
    fs[EVERY_MEM] >> metis_tac[]) >>
  `lift_result R_ok R_term R_term (step_inst fuel ctx inst s')
    (run_insts fuel ctx (f v inst) s')` by (
    qabbrev_tac `s_nat = s' with vs_inst_idx := 0` >>
    `sound v s_nat` by simp[Abbr `v`, Abbr `s_nat`] >>
    `lift_result R_ok R_term R_term (step_inst fuel ctx inst s_nat)
      (run_insts fuel ctx (f v inst) s_nat)` by (
      first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `inst`, `s_nat`] mp_tac) >>
      simp[]) >>
    `s' = s_nat with vs_inst_idx := i` by
      simp[Abbr `s_nat`, Abbr `i`, venom_state_component_equality] >>
    `step_inst fuel ctx inst s' =
     exec_result_map (\s''. s'' with vs_inst_idx := i)
       (step_inst fuel ctx inst s_nat)` by (
      qpat_assum `s' = _` (fn th =>
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[step_inst_idx_indep]) >>
    `run_insts fuel ctx (f v inst) s' =
     exec_result_map (\s''. s'' with vs_inst_idx := i)
       (run_insts fuel ctx (f v inst) s_nat)` by (
      qpat_x_assum `s' = _` (fn th =>
        CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
      simp[run_insts_idx_indep]) >>
    ntac 2 (pop_assum SUBST1_TAC) >>
    irule lift_result_exec_result_map >>
    simp[] >> metis_tac[R_ok_idx_change, R_term_idx_change_both]) >>
  Cases_on `step_inst fuel ctx inst s'` >> simp[]
  >- (
    rename1 `step_inst _ _ _ _ = OK st1` >>
    `st1.vs_inst_idx = s'.vs_inst_idx` by
      metis_tac[step_inst_preserves_inst_idx] >>
    `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
     j + LENGTH (g i inst)` by (
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
       LENGTH (g i (EL i bb.bb_instructions))`
        by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
      simp[Abbr `j`, Abbr `inst`]) >>
    Cases_on `run_insts fuel ctx (f v inst) s'`
    >- (
      rename1 `run_insts _ _ _ _ = OK st2` >>
      `st2.vs_inst_idx = s'.vs_inst_idx` by
        metis_tac[run_insts_preserves_idx] >>
      `R_ok st1 st2` by (
        qpat_x_assum `lift_result _ _ _ (OK _) (OK _)` mp_tac >>
        simp[lift_result_def]) >>
      `exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
         (s' with vs_inst_idx := j) =
       exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
         (st2 with vs_inst_idx := j + LENGTH (g i inst))` by (
        qspecl_then [`f v inst`, `fuel`, `ctx`,
          `bb with bb_instructions := FLAT (MAPi g bb.bb_instructions)`,
          `s'`, `j`, `st2`] mp_tac exec_block_skip_prefix >>
        impl_tac >- fs[] >>
        simp[]) >>
      `j + LENGTH (g i inst) = j + LENGTH (f v inst)` by simp[] >>
      pop_assum (fn th => FULL_SIMP_TAC (srw_ss()) [th]) >>
      (* No soundness needed — IH has no soundness precondition *)
      irule block_sim_continuation >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
       j + LENGTH (g i inst)` by (
        `LENGTH (FLAT (TAKE (SUC i) (MAPi g bb.bb_instructions))) =
         LENGTH (FLAT (TAKE i (MAPi g bb.bb_instructions))) +
         LENGTH (g i (EL i bb.bb_instructions))`
          by (irule FLAT_MAPi_offset_SUC >> simp[]) >>
        simp[Abbr `j`, Abbr `inst`]) >>
      qpat_x_assum `!m. m < _ ==> !fuel' ctx' s'. _`
        (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
      impl_tac >- decide_tac >>
      disch_then (qspecl_then [`fuel`, `ctx`,
        `st2 with vs_inst_idx := SUC i`] mp_tac) >>
      SIMP_TAC (srw_ss()) [] >>
      impl_tac >- (rpt conj_tac >> TRY decide_tac) >>
      simp[]
    )
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
    >- (gvs[lift_result_def])
  )
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
  >- (
    `~(?s0. run_insts fuel ctx (f v inst) s' = OK s0)` by
      (Cases_on `run_insts fuel ctx (f v inst) s'` >> gvs[lift_result_def]) >>
    `lift_result R_ok R_term R_term (run_insts fuel ctx (f v inst) s')
       (exec_block fuel ctx
          (bb with bb_instructions := FLAT (MAPi g bb.bb_instructions))
          (s' with vs_inst_idx := j))` by (
      irule run_insts_lift_exec_block >> fs[]) >>
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_insts fuel ctx (f v inst) s'` >> gvs[])
QED

(* Specialization: universal soundness + fn_inst_wf.
   vs_inst_idx = 0: required because FLAT expansion changes block length;
   false at arbitrary idx (see counterexampleScript.sml). *)
Theorem analysis_inst_sim_block_sim_proof:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (bottom : 'a) (result : 'a df_state)
   (f : 'a -> instruction -> instruction list) bb.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    (!i s. i < LENGTH bb.bb_instructions ==>
           sound (df_at bottom result bb.bb_label i) s)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. exec_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
          (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  qspecl_then [`R_ok`, `R_term`, `sound`, `f`, `bb`, `bottom`, `result`]
    mp_tac analysis_block_sim_univ >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[EVERY_MEM] >> rpt strip_tac >>
      fs[venomWfTheory.fn_inst_wf_def] >> res_tac) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `s`] mp_tac) >> simp[]
QED


(* ===== With soundness threading ===== *)

(* FOLDL preserves a predicate when bottom satisfies it and join preserves it *)
Theorem foldl_sound:
  !l (bottom:'a) join (sound : 'a -> 'b -> bool).
    (!s. sound bottom s) /\
    (!a b s. sound a s ==> sound (join a b) s) ==>
    !s. sound (FOLDL join bottom l) s
Proof
  Induct >> rw[] >> metis_tac[]
QED

Theorem lift_result_error_left:
  !R_ok R_term r e. lift_result R_ok R_term R_term r (Error e) ==> ?e'. r = Error e'
Proof
  Cases_on `r` >> simp[lift_result_def]
QED

(* Like block_sim_function_proof, but block sim only required for
   lookup_block-returned blocks (avoids shadowed block issue).
   Uses run_block (eval_phis + exec_block) instead of exec_block,
   so the per-block sim hypothesis doesn't need s.vs_inst_idx = 0. *)
Triviality run_block_OK_inst_idx_0[local]:
  !fuel ctx bb s v. run_block fuel ctx bb s = OK v ==> v.vs_inst_idx = 0
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] mp_tac eval_phis_ok_or_error_defs >>
  strip_tac >> fs[run_block_def] >> drule venomExecProofsTheory.exec_block_OK_inst_idx_0 >> simp[]
QED

Triviality block_sim_function_by_lookup_ind_step:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn fuel.
    valid_state_rel R_ok R_term /\
    (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
    (!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
       s1.vs_current_bb = s2.vs_current_bb /\
       s1.vs_inst_idx = s2.vs_inst_idx) /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!fuel ctx bb s1 s2.
       MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
       lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                                (run_block fuel ctx bb s2)) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      !fuel ctx s.
        (?e. run_block fuel ctx bb s = Error e) \/
        lift_result R_ok R_term R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_blocks fuel ctx fn s1 = Error e) \/
       lift_result R_ok R_term R_term (run_blocks fuel ctx fn s1)
         (run_blocks fuel ctx (function_map_transform bt fn) s2))
  ==>
    !ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_blocks (SUC fuel) ctx fn s1 = Error e) \/
       lift_result R_ok R_term R_term (run_blocks (SUC fuel) ctx fn s1)
         (run_blocks (SUC fuel) ctx (function_map_transform bt fn) s2)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  `s1.vs_current_bb = s2.vs_current_bb` by metis_tac[] >>
  `s2.vs_inst_idx = 0` by metis_tac[] >>
  ONCE_REWRITE_TAC[run_blocks_unfold] >>
  simp[function_map_transform_def, lookup_block_map_proof] >>
  Cases_on `lookup_block s2.vs_current_bb fn.fn_blocks`
  >- gvs[lift_result_def]
  >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecProofsTheory.lookup_block_MEM] >>
  (* Same-code R_ok preservation *)
  `lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx bb s2)` by metis_tac[] >>
  (* Per-block sim: bb s2 ~ bt bb s2 (with error disjunct) *)
  `(?e. run_block fuel ctx bb s2 = Error e) \/
   lift_result R_ok R_term R_term (run_block fuel ctx bb s2)
     (run_block fuel ctx (bt bb) s2)` by (
    qpat_assum `!lbl bb. lookup_block _ _ = SOME _ ==> _`
      (qspecl_then [`s2.vs_current_bb`, `bb`] mp_tac) >> simp[]) >>
  Cases_on `?e. run_block fuel ctx bb s2 = Error e`
  >- (
    fs[] >> imp_res_tac lift_result_error_left >> gvs[]
  )
  >>
  `lift_result R_ok R_term R_term (run_block fuel ctx bb s2)
                            (run_block fuel ctx (bt bb) s2)` by metis_tac[] >>
  (* Triangle via transitivity *)
  `lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                            (run_block fuel ctx (bt bb) s2)` by (
    irule lift_result_trans_proof >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qexists_tac `run_block fuel ctx bb s2` >>
    conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `run_block fuel ctx bb s1` >>
  Cases_on `run_block fuel ctx (bt bb) s2` >>
  gvs[lift_result_def]
  >>
  (* Only OK-OK case survives *)
  rename1 `R_ok v1 v2` >>
  Cases_on `v1.vs_halted`
  >- (
    (* v1 halted *)
    `v2.vs_halted` by metis_tac[] >> simp[lift_result_def] >>
    metis_tac[]
  ) >>
  (* v1 not halted *)
  `~v2.vs_halted` by metis_tac[] >> simp[lift_result_def] >>
  gvs[function_map_transform_def] >>
  `v1.vs_inst_idx = 0 /\ v2.vs_inst_idx = 0` by
    metis_tac[run_block_OK_inst_idx_0] >>
  qpat_assum `!ctx' s1' s2'. R_ok s1' s2' /\ _ ==> _`
    (qspecl_then [`ctx`, `v1`, `v2`] mp_tac) >>
  simp[]
QED

Theorem block_sim_function_by_lookup:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool) bt fn.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!bb. (bt bb).bb_label = bb.bb_label) /\
    (!lbl bb. lookup_block lbl fn.fn_blocks = SOME bb ==>
      !fuel ctx s.
        (?e. run_block fuel ctx bb s = Error e) \/
        lift_result R_ok R_term R_term (run_block fuel ctx bb s)
                                 (run_block fuel ctx (bt bb) s)) /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2)
  ==>
    !fuel ctx s.
      s.vs_inst_idx = 0 ==>
      (?e. run_blocks fuel ctx fn s = Error e) \/
      lift_result R_ok R_term R_term (run_blocks fuel ctx fn s)
                 (run_blocks fuel ctx (function_map_transform bt fn) s)
Proof
  rpt gen_tac >> strip_tac >>
  `!s1 s2. R_ok s1 s2 ==> R_term s1 s2` by
    (rpt strip_tac >> irule vsr_R_ok_R_term >> metis_tac[])
  >>
  `!s1 s2. R_ok s1 s2 ==> (s1.vs_halted <=> s2.vs_halted) /\
     s1.vs_current_bb = s2.vs_current_bb /\
     s1.vs_inst_idx = s2.vs_inst_idx` by
    (rpt strip_tac >> imp_res_tac
      (REWRITE_RULE [GSYM AND_IMP_INTRO] vsr_R_ok_fields))
  >>
  `!fuel ctx bb s1 s2.
     MEM bb fn.fn_blocks /\ R_ok s1 s2 ==>
     lift_result R_ok R_term R_term (run_block fuel ctx bb s1)
                              (run_block fuel ctx bb s2)` by
    (match_mp_tac run_block_preserves_R_helper >>
     rpt conj_tac >> first_assum ACCEPT_TAC)
  >>
  qsuff_tac
    `!fuel ctx s1 s2. R_ok s1 s2 /\ s1.vs_inst_idx = 0 ==>
       (?e. run_blocks fuel ctx fn s1 = Error e) \/
       lift_result R_ok R_term R_term (run_blocks fuel ctx fn s1)
         (run_blocks fuel ctx (function_map_transform bt fn) s2)`
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`fuel`, `ctx`, `s`, `s`] mp_tac) >>
      impl_tac >- (conj_tac >- (irule vsr_R_ok_refl >> metis_tac[]) >> simp[]) >>
      simp[])
  >>
  Induct_on `fuel`
  >- (rw[] >> simp[run_blocks_def, function_map_transform_def, lift_result_def])
  >>
  rpt strip_tac >>
  irule (SIMP_RULE (srw_ss()) [] block_sim_function_by_lookup_ind_step) >>
  rpt (first_assum (fn th => EXISTS_TAC (rand (concl th)) >> ACCEPT_TAC th)
       ORELSE conj_tac ORELSE first_assum ACCEPT_TAC)
QED

(* ===== eval_phis / run_block bridge lemmas for parallel PHI semantics ===== *)

(* inst_transform_structural preserves the PHI prefix exactly:
   PHIs map to themselves, and non-PHIs map to non-PHIs only.
   Combined with bb_well_formed (PHIs form a prefix), this means
   eval_phis on the transformed block agrees with the original. *)

Theorem phi_prefix_length_head_not_phi:
  !h l. h.inst_opcode <> PHI /\ (!i j. i < j /\ j < LENGTH (h::l) /\
    (EL j (h::l)).inst_opcode = PHI ==> (EL i (h::l)).inst_opcode = PHI) ==>
    phi_prefix_length l = 0
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `l` >- simp[phi_prefix_length_def] >>
  Cases_on `h'.inst_opcode = PHI` >- (
    first_x_assum (qspecl_then [`0`, `SUC 0`] mp_tac) >> simp[]) >>
  simp[phi_prefix_length_def]
QED

Triviality phi_prefix_shift_cond1[local]:
  !f h l.
    (!idx inst. idx < LENGTH (h::l) /\ EL idx (h::l) = inst /\ inst.inst_opcode = PHI ==>
       f idx inst = [inst]) ==>
  !idx inst. idx < LENGTH l /\ EL idx l = inst /\ inst.inst_opcode = PHI ==>
    f (SUC idx) inst = [inst]
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`SUC idx`, `inst`] mp_tac) >> simp[EL_restricted]
QED

Triviality phi_prefix_shift_cond2[local]:
  !f h l.
    (!idx inst. idx < LENGTH (h::l) /\ EL idx (h::l) = inst /\ inst.inst_opcode <> PHI ==>
       EVERY (\i. i.inst_opcode <> PHI) (f idx inst)) ==>
  !idx inst. idx < LENGTH l /\ EL idx l = inst /\ inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (f (SUC idx) inst)
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`SUC idx`, `inst`] mp_tac) >> simp[EL_restricted]
QED

Theorem phi_prefix_shift_cond3:
  !h l.
    (!i j. i < j /\ j < LENGTH (h::l) /\ (EL j (h::l)).inst_opcode = PHI ==>
       (EL i (h::l)).inst_opcode = PHI) ==>
  !i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
    (EL i l).inst_opcode = PHI
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[EL_restricted]
QED

Theorem phi_prefix_length_flat_mapi:
  !f l.
    (!idx inst. idx < LENGTH l /\ EL idx l = inst /\ inst.inst_opcode = PHI ==>
       f idx inst = [inst]) /\
    (!idx inst. idx < LENGTH l /\ EL idx l = inst /\ inst.inst_opcode <> PHI ==>
       EVERY (\i. i.inst_opcode <> PHI) (f idx inst)) /\
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
       (EL i l).inst_opcode = PHI) ==>
    phi_prefix_length (FLAT (MAPi f l)) = phi_prefix_length l
Proof
  Induct_on `l` >- simp[phi_prefix_length_def] >>
  rpt gen_tac >> strip_tac >>
  simp[indexedListsTheory.MAPi_def, phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    `f 0 h = [h]` by (first_x_assum (qspecl_then [`0`, `h`] mp_tac) >> simp[]) >>
    simp[phi_prefix_length_def] >>
    qpat_x_assum `!f. _ ==> phi_prefix_length (FLAT (MAPi f l)) = phi_prefix_length l`
      ho_match_mp_tac >>
    simp[combinTheory.o_DEF] >>
    match_mp_tac phi_prefix_shift_cond3 >>
    qexists `h` >>
    rpt gen_tac >> strip_tac >>
    first_x_assum irule >> simp[] >>
    qexists `j` >> simp[] >>
    `LENGTH (h::l) = SUC (LENGTH l)` by simp[] >>
    decide_tac) >>
  `phi_prefix_length l = 0` by metis_tac[phi_prefix_length_head_not_phi] >>
  `EVERY (\i. i.inst_opcode <> PHI) (f 0 h)` by (
    first_x_assum (qspecl_then [`0`, `h`] mp_tac) >> simp[]) >>
  Cases_on `f 0 h`
  >- (
    qpat_x_assum `phi_prefix_length l = 0` (fn th => simp[GSYM th]) >>
    qpat_x_assum `EVERY (\i. i.inst_opcode <> PHI) ([] :instruction list)` kall_tac >>
    qpat_x_assum `!f. _ ==> phi_prefix_length (FLAT (MAPi f l)) = phi_prefix_length l`
      ho_match_mp_tac >>
    simp[combinTheory.o_DEF] >>
    match_mp_tac phi_prefix_shift_cond3 >>
    qexists `h` >>
    rpt gen_tac >> strip_tac >>
    first_x_assum irule >> simp[] >>
    qexists `j` >> simp[] >>
    `LENGTH (h::l) = SUC (LENGTH l)` by simp[] >>
    decide_tac) >>
  gvs[EVERY_DEF, APPEND, phi_prefix_length_def]
QED

Theorem phi_prefix_length_zero_eval_phis_ok:
  !l s. phi_prefix_length l = 0 ==> eval_phis s l = OK s
Proof
  Cases_on `l` >- simp[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem eval_phis_flat_mapi:
  !f s l.
    (!idx inst. idx < LENGTH l /\ EL idx l = inst /\ inst.inst_opcode = PHI ==>
       f idx inst = [inst]) /\
    (!idx inst. idx < LENGTH l /\ EL idx l = inst /\ inst.inst_opcode <> PHI ==>
       EVERY (\i. i.inst_opcode <> PHI) (f idx inst)) /\
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
       (EL i l).inst_opcode = PHI) ==>
    eval_phis s (FLAT (MAPi f l)) = eval_phis s l
Proof
  Induct_on `l` >- simp[eval_phis_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    (* PHI case: f 0 h = [h], so FLAT(MAPi f (h::l)) = h :: FLAT(MAPi (f o SUC) l).
       eval_phis s (h :: rest) reads eval_one_phi s h identically on both sides,
       then recurses into rest. Prove inner equality via IH with shifted conditions. *)
    `f 0 h = [h]` by (first_x_assum (qspecl_then [`0`, `h`] mp_tac) >> simp[]) >>
    `eval_phis s (FLAT (MAPi (f o SUC) l)) = eval_phis s l` by (
      qpat_x_assum `!f s. _ ==> eval_phis s (FLAT (MAPi f l)) = eval_phis s l`
        ho_match_mp_tac >>
      simp[combinTheory.o_DEF] >>
      match_mp_tac phi_prefix_shift_cond3 >> qexists `h` >>
      rpt gen_tac >> strip_tac >>
      first_x_assum irule >> simp[] >>
      qexists `j` >> simp[] >>
      `LENGTH (h::l) = SUC (LENGTH l)` by simp[] >> decide_tac) >>
    simp[indexedListsTheory.MAPi_def, eval_phis_def])
  >- (
    (* Non-PHI case: h is not PHI, so eval_phis s (h::l) = OK s.
       phi_prefix_length (h::l) = 0, and by phi_prefix_length_flat_mapi,
       phi_prefix_length (FLAT (MAPi f (h::l))) = 0, so eval_phis on LHS = OK s too. *)
    `phi_prefix_length (FLAT (MAPi f (h::l))) = 0` by (
      irule EQ_TRANS >>
      qexists_tac `phi_prefix_length (h::l)` >> conj_tac
      >- (irule (Q.SPECL [`f`, `h::l`] phi_prefix_length_flat_mapi) >>
          rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC)
      >- simp[phi_prefix_length_def]) >>
    simp[phi_prefix_length_zero_eval_phis_ok, eval_phis_def])
QED

(* PHI prefix of a list is all PHIs *)
Theorem phi_prefix_all_phi:
  !l. EVERY (\i. i.inst_opcode = PHI) (TAKE (phi_prefix_length l) l)
Proof
  Induct >> rw[phi_prefix_length_def]
QED

(* PHI prefix instructions are not terminators and not INVOKE *)
Theorem phi_prefix_no_terminator:
  !l. EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE)
         (TAKE (phi_prefix_length l) l)
Proof
  Induct >> rw[phi_prefix_length_def] >>
  Cases_on `h.inst_opcode` >> rw[is_terminator_def, opcode_EQ_opcode]
QED

(* run_insts over PHI-only instructions gives Error:
   step_inst PHI returns Error "phi outside prefix" *)
Theorem run_insts_phi_error:
  !fuel ctx insts s.
    EVERY (\i. i.inst_opcode = PHI) insts /\ insts <> [] ==>
    ?e. run_insts fuel ctx insts s = Error e
Proof
  Cases_on `insts` >-
    simp[] >>
  rpt strip_tac >>
  `h.inst_opcode = PHI` by fs[] >>
  simp[step_inst_phi_error] >>
  ONCE_REWRITE_TAC[run_insts_def] >>
  simp[step_inst_phi_error]
QED

(* Extract conditions from inst_transform_structural for use in
   eval_phis_flat_mapi and phi_prefix_length_flat_mapi. These avoid
   the namespace collision that occurs when f is free in the proof context
   and we try fs[inst_transform_structural_def] or metis_tac. *)
Theorem inst_transform_phi:
  !f v inst.
    inst_transform_structural f /\ inst.inst_opcode = PHI ==>
    f v inst = [inst]
Proof
  rpt gen_tac >> strip_tac >>
  fs[inst_transform_structural_def]
QED

Theorem is_terminator_not_phi:
  !op. is_terminator op ==> op <> PHI
Proof
  Cases_on `op` >> rw[is_terminator_def]
QED

Theorem is_terminator_not_INVOKE:
  !op. is_terminator op ==> op <> INVOKE
Proof
  Cases_on `op` >> rw[is_terminator_def]
QED

Theorem inst_transform_non_phi_weak:
  !f v inst.
    inst_transform_structural f /\ inst.inst_opcode <> PHI ==>
    EVERY (\i. i.inst_opcode <> PHI) (f v inst)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `?inst'. f v inst = [inst'] /\ is_terminator inst'.inst_opcode` by
      fs[inst_transform_structural_def] >>
    simp[EVERY_DEF] >> metis_tac[is_terminator_not_phi])
  >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (
    `?inst'. f v inst = [inst'] /\ inst'.inst_opcode = INVOKE` by
      fs[inst_transform_structural_def] >>
    simp[EVERY_DEF] >> Cases_on `inst'.inst_opcode` >> rw[opcode_EQ_opcode])
  >>
  (* OTHER CASE: ¬is_terminator ∧ ≠INVOKE ∧ ≠PHI *)
  fs[inst_transform_structural_def] >>
  qpat_x_assum `!v inst. _ ==> EVERY _ _` (qspecl_then [`v`, `inst`] mp_tac) >>
  simp[EVERY_CONJ]

QED

(* Weakened 4th conjunct: the old form before ≠PHI was added.
   For non-terminator, non-INVOKE inputs, outputs are non-terminator, non-INVOKE.
   Proved by case-splitting on PHI; in the PHI case, output is [inst] which
   satisfies the weaker EVERY. *)
Theorem inst_transform_non_term_non_invoke:
  !f v inst.
    inst_transform_structural f /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE ==>
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) (f v inst)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `is_terminator inst.inst_opcode` >> gvs[] >>
  Cases_on `inst.inst_opcode = INVOKE` >> gvs[] >>
  Cases_on `inst.inst_opcode = PHI`
  >- (
    `f v inst = [inst]` by fs[inst_transform_structural_def] >>
    simp[EVERY_DEF] >>
    metis_tac[is_terminator_not_phi, is_terminator_not_INVOKE])
  >>
  (* 4th conjunct: ~is_terminator /\ <>INVOKE /\ <>PHI *)
  fs[inst_transform_structural_def] >>
  qpat_x_assum `!v inst. ~is_terminator _ /\ _ <> INVOKE /\ _ <> PHI ==> EVERY _ _`
    (qspecl_then [`v`, `inst`] mp_tac) >>
  simp[] >>
  DISCH_THEN (fn th => mp_tac th >> match_mp_tac EVERY_MONOTONIC) >>
  simp[]
QED

(* Shared tactic for all analysis_run_block_sim variants.
   Pattern: derive eval_phis agreement, derive phi_prefix_length agreement,
   case-split on eval_phis, apply analysis_block_sim* at idx=0,
   bridge from idx=0 to idx=phi_prefix_length via exec_block_skip_prefix. *)

(* LENGTH of FLAT(TAKE ppl (MAPi f l)) = ppl when PHI instructions
   map to singletons and non-PHIs don't produce PHIs.
   This connects the FLAT-based indexing of the transformed block
   to the phi_prefix_length of the original block. *)
Theorem length_flat_take_phi_prefix:
  !f l.
    (!idx inst. idx < LENGTH l /\ EL idx l = inst /\ inst.inst_opcode = PHI ==>
       f idx inst = [inst]) /\
    (!i j. i < j /\ j < LENGTH l /\ (EL j l).inst_opcode = PHI ==>
       (EL i l).inst_opcode = PHI) ==>
    LENGTH (FLAT (TAKE (phi_prefix_length l) (MAPi f l))) = phi_prefix_length l
Proof
  Induct_on `l` >- simp[phi_prefix_length_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (
    (* h is PHI: f 0 h = [h], so first element of MAPi is [h] *)
    `f 0 h = [h]` by (
      first_x_assum (qspecl_then [`0`, `h`] mp_tac) >> simp[]) >>
    simp[phi_prefix_length_def, indexedListsTheory.MAPi_def,
         combinTheory.o_DEF] >>
    (* Goal is now the IH conclusion for (f o SUC).
       Use the IH (oldest assumption) via match_mp_tac *)
    last_x_assum match_mp_tac >> conj_tac
    >- (
      rpt gen_tac >> strip_tac >>
      first_x_assum (qspecl_then [`SUC idx`, `inst`] mp_tac) >> simp[])
    >- (
      rpt gen_tac >> strip_tac >>
      first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]))
  >- (
    `phi_prefix_length l = 0` by metis_tac[phi_prefix_length_head_not_phi] >>
    simp[phi_prefix_length_def, indexedListsTheory.MAPi_def])
QED

(* Bridge from analysis_block_sim (exec_block level, vs_inst_idx=0)
   to run_block level. This is the key lemma for the parallel PHI
   semantics: because inst_transform_structural preserves PHIs exactly,
   eval_phis agrees on original and transformed blocks, and phi_prefix_length
   is preserved, so we can wrap exec_block-level sim in run_block.

   The soundness hypothesis is on the post-eval_phis state with vs_inst_idx := 0,
   because eval_phis modifies vs_vars (PHI outputs) and the abstract sound
   predicate may depend on variable values. Callers must discharge this by
   showing their analysis correctly models post-PHI states. *)
Theorem analysis_run_block_sim:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    analysis_inst_simulates R_ok R_term sound f /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    transfer_sound sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx))
  ==>
    !fuel ctx s s_phi.
      eval_phis s bb.bb_instructions = OK s_phi /\
      sound (df_at bottom result bb.bb_label
               (phi_prefix_length bb.bb_instructions))
            (s_phi with vs_inst_idx := 0) ==>
      (?e. run_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `bt = analysis_block_transform bottom result f bb` >>
  qabbrev_tac `g = \idx inst. f (df_at bottom result bb.bb_label idx) inst` >>
  `bt.bb_instructions = FLAT (MAPi g bb.bb_instructions)` by
    simp[Abbr `bt`, Abbr `g`, analysis_block_transform_def] >>
  `bt.bb_label = bb.bb_label` by
    simp[Abbr `bt`, Abbr `g`, analysis_block_transform_def] >>
  (* extract inst_transform_structural f from analysis_inst_simulates *)
  `inst_transform_structural f` by metis_tac[analysis_inst_simulates_def] >>
  (* eval_phis agrees on both blocks *)
  `eval_phis s bt.bb_instructions = OK s_phi` by (
    qpat_assum `bt.bb_instructions = _` (fn th => once_rewrite_tac [th]) >>
    qpat_assum `eval_phis s bb.bb_instructions = OK s_phi`
      (fn th => once_rewrite_tac [GSYM th]) >>
    match_mp_tac (GEN_ALL eval_phis_flat_mapi) >>
    simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >> drule inst_transform_non_phi_weak >> simp[])
    >- (rpt strip_tac >>
        imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  (* phi_prefix_length also agrees *)
  `phi_prefix_length bt.bb_instructions = phi_prefix_length bb.bb_instructions` by (
    qpat_assum `bt.bb_instructions = _` (fn th => once_rewrite_tac [th]) >>
    match_mp_tac (GEN_ALL phi_prefix_length_flat_mapi) >>
    simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >> drule inst_transform_non_phi_weak >> simp[])
    >- (rpt strip_tac >>
        imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  (* Unfold run_block *)
  ONCE_REWRITE_TAC[run_block_def] >>
  (* Resolve eval_phis case splits using known OK results *)
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  Cases_on `eval_phis s bt.bb_instructions` >> gvs[] >>
  (* Apply analysis_block_sim_from directly at phi_prefix_length *)
  mp_tac analysis_block_sim_from >>
  disch_then (qspecl_then [`R_ok`,`R_term`,`sound`,`f`,`bb`,`bottom`,
    `result`,`transfer`,`run_ctx`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> fs[transfer_sound_def] >> res_tac) >>
  disch_then (qspecl_then [`fuel`,`ctx`,
    `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`] mp_tac) >>
  impl_tac >- (
    simp[venomExecProofsTheory.phi_prefix_length_le]) >>
  simp[analysis_block_transform_def, Abbr `bt`] >>
  `LENGTH (FLAT (TAKE (phi_prefix_length bb.bb_instructions)
    (MAPi g bb.bb_instructions))) = phi_prefix_length bb.bb_instructions` by
    (irule length_flat_take_phi_prefix >> simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >>
        imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  simp[]
QED

(* Variant of analysis_run_block_sim with state_inv (mirrors analysis_block_sim_inv).
   Like analysis_run_block_sim, the soundness and state_inv hypotheses are on
   the post-eval_phis state at vs_inst_idx = 0. *)
Theorem analysis_run_block_sim_inv:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!fuel ctx v inst s.
       sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result R_ok R_term R_term (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    inst_transform_structural f /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    transfer_sound_wf sound transfer run_ctx /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    (!fuel ctx inst s s'.
       MEM inst bb.bb_instructions /\
       inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s s_phi.
      eval_phis s bb.bb_instructions = OK s_phi /\
      sound (df_at bottom result bb.bb_label
               (phi_prefix_length bb.bb_instructions))
            (s_phi with vs_inst_idx := 0) /\
      state_inv (s_phi with vs_inst_idx := 0) ==>
      (?e. run_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `bt = analysis_block_transform bottom result f bb` >>
  qabbrev_tac `g = \idx inst. f (df_at bottom result bb.bb_label idx) inst` >>
  `bt.bb_instructions = FLAT (MAPi g bb.bb_instructions)` by
    simp[Abbr `bt`, Abbr `g`, analysis_block_transform_def] >>
  `bt.bb_label = bb.bb_label` by
    simp[Abbr `bt`, Abbr `g`, analysis_block_transform_def] >>
  (* eval_phis agrees on both blocks *)
  `eval_phis s bt.bb_instructions = OK s_phi` by (
    qpat_assum `bt.bb_instructions = _` (fn th => once_rewrite_tac [th]) >>
    qpat_assum `eval_phis s bb.bb_instructions = OK s_phi`
      (fn th => once_rewrite_tac [GSYM th]) >>
    match_mp_tac (GEN_ALL eval_phis_flat_mapi) >>
    simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >> drule inst_transform_non_phi_weak >> simp[])
    >- (rpt strip_tac >> imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  (* phi_prefix_length also agrees *)
  `phi_prefix_length bt.bb_instructions = phi_prefix_length bb.bb_instructions` by (
    qpat_assum `bt.bb_instructions = _` (fn th => once_rewrite_tac [th]) >>
    match_mp_tac (GEN_ALL phi_prefix_length_flat_mapi) >>
    simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >> drule inst_transform_non_phi_weak >> simp[])
    >- (rpt strip_tac >> imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  (* Unfold run_block *)
  ONCE_REWRITE_TAC[run_block_def] >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  Cases_on `eval_phis s bt.bb_instructions` >> gvs[] >>
  (* Apply analysis_block_sim_inv_from directly at phi_prefix_length *)
  mp_tac analysis_block_sim_inv_from >>
  disch_then (qspecl_then [`R_ok`,`R_term`,`sound`,`state_inv`,`f`,`bb`,`bottom`,
    `result`,`transfer`,`run_ctx`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac) >>
  disch_then (qspecl_then [`fuel`,`ctx`,
    `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`] mp_tac) >>
  impl_tac >- (
    simp[venomExecProofsTheory.phi_prefix_length_le]) >>
  simp[analysis_block_transform_def, Abbr `bt`] >>
  `LENGTH (FLAT (TAKE (phi_prefix_length bb.bb_instructions)
    (MAPi g bb.bb_instructions))) = phi_prefix_length bb.bb_instructions` by
    (irule length_flat_take_phi_prefix >> simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >>
        imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  simp[]
QED

(* Variant of analysis_run_block_sim with block-restricted transfer soundness
   (mirrors analysis_block_sim_inv_block).
   Like analysis_run_block_sim_inv, the soundness and state_inv hypotheses
   are on the post-eval_phis state at vs_inst_idx = 0. *)
Theorem analysis_run_block_sim_inv_block:
  !(R_ok : venom_state -> venom_state -> bool)
   (R_term : venom_state -> venom_state -> bool)
   (sound : 'a -> venom_state -> bool)
   (state_inv : venom_state -> bool)
   (f : 'a -> instruction -> instruction list) bb fn
   (bottom : 'a) (result : 'a df_state) transfer run_ctx.
    valid_state_rel R_ok R_term /\
    (!s1 s2 s3. R_ok s1 s2 /\ R_ok s2 s3 ==> R_ok s1 s3) /\
    (!s1 s2 s3. R_term s1 s2 /\ R_term s2 s3 ==> R_term s1 s3) /\
    (!fuel ctx v inst s.
       sound v s /\ state_inv (s with vs_inst_idx := 0) /\ inst_wf inst ==>
       (?e. step_inst fuel ctx inst s = Error e) \/
       lift_result R_ok R_term R_term (step_inst fuel ctx inst s)
         (run_insts fuel ctx (f v inst) s)) /\
    inst_transform_structural f /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    (!inst x.
       MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
       !s1 s2. R_ok s1 s2 ==> lookup_var x s1 = lookup_var x s2) /\
    MEM bb fn.fn_blocks /\
    transfer_sound_block_inv sound state_inv transfer run_ctx fn /\
    (!v s1 s2. R_ok s1 s2 /\ sound v s1 ==> sound v s2) /\
    (!idx. SUC idx <= LENGTH bb.bb_instructions ==>
       df_at bottom result bb.bb_label (SUC idx) =
       transfer run_ctx (EL idx bb.bb_instructions)
         (df_at bottom result bb.bb_label idx)) /\
    (!fuel ctx inst s s'.
       MEM inst bb.bb_instructions /\
       inst_wf inst /\
       state_inv (s with vs_inst_idx := 0) /\
       step_inst fuel ctx inst s = OK s' ==>
       state_inv (s' with vs_inst_idx := 0)) /\
    (!s1 s2. R_ok s1 s2 /\ state_inv s1 ==> state_inv s2)
  ==>
    !fuel ctx s s_phi.
      eval_phis s bb.bb_instructions = OK s_phi /\
      sound (df_at bottom result bb.bb_label
               (phi_prefix_length bb.bb_instructions))
            (s_phi with vs_inst_idx := 0) /\
      state_inv (s_phi with vs_inst_idx := 0) ==>
      (?e. run_block fuel ctx bb s = Error e) \/
      lift_result R_ok R_term R_term
        (run_block fuel ctx bb s)
        (run_block fuel ctx (analysis_block_transform bottom result f bb) s)
Proof
  rpt strip_tac >>
  qabbrev_tac `bt = analysis_block_transform bottom result f bb` >>
  qabbrev_tac `g = \idx inst. f (df_at bottom result bb.bb_label idx) inst` >>
  `bt.bb_instructions = FLAT (MAPi g bb.bb_instructions)` by
    simp[Abbr `bt`, Abbr `g`, analysis_block_transform_def] >>
  `bt.bb_label = bb.bb_label` by
    simp[Abbr `bt`, Abbr `g`, analysis_block_transform_def] >>
  (* eval_phis agrees on both blocks *)
  `eval_phis s bt.bb_instructions = OK s_phi` by (
    qpat_assum `bt.bb_instructions = _` (fn th => once_rewrite_tac [th]) >>
    qpat_assum `eval_phis s bb.bb_instructions = OK s_phi`
      (fn th => once_rewrite_tac [GSYM th]) >>
    match_mp_tac (GEN_ALL eval_phis_flat_mapi) >>
    simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >> drule inst_transform_non_phi_weak >> simp[])
    >- (rpt strip_tac >> imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  (* phi_prefix_length also agrees *)
  `phi_prefix_length bt.bb_instructions = phi_prefix_length bb.bb_instructions` by (
    qpat_assum `bt.bb_instructions = _` (fn th => once_rewrite_tac [th]) >>
    match_mp_tac (GEN_ALL phi_prefix_length_flat_mapi) >>
    simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >> drule inst_transform_non_phi_weak >> simp[])
    >- (rpt strip_tac >> imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  (* Unfold run_block *)
  ONCE_REWRITE_TAC[run_block_def] >>
  Cases_on `eval_phis s bb.bb_instructions` >> gvs[] >>
  Cases_on `eval_phis s bt.bb_instructions` >> gvs[] >>
  (* Apply analysis_block_sim_inv_block_from directly at phi_prefix_length *)
  mp_tac analysis_block_sim_inv_block_from >>
  disch_then (qspecl_then [`R_ok`,`R_term`,`sound`,`state_inv`,`f`,`bb`,`fn`,
    `bottom`,`result`,`transfer`,`run_ctx`] mp_tac) >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
    rpt strip_tac >> res_tac) >>
  disch_then (qspecl_then [`fuel`,`ctx`,
    `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`] mp_tac) >>
  impl_tac >- (
    simp[venomExecProofsTheory.phi_prefix_length_le]) >>
  simp[analysis_block_transform_def, Abbr `bt`] >>
  `LENGTH (FLAT (TAKE (phi_prefix_length bb.bb_instructions)
    (MAPi g bb.bb_instructions))) = phi_prefix_length bb.bb_instructions` by
    (irule length_flat_take_phi_prefix >> simp[Abbr `g`] >> rpt conj_tac
    >- (rpt strip_tac >> drule inst_transform_phi >> simp[])
    >- (rpt strip_tac >>
        imp_res_tac venomWfTheory.bb_well_formed_def >> fs[] >> res_tac)) >>
  simp[]
QED
