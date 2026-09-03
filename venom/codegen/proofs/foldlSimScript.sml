(*
 * Plan composition and FOLDL simulation infrastructure
 *
 * Provides:
 * 1. plan_seq_sim — compose two plan segments preserving venom_asm_rel
 * 2. plan_steps / plan_steps_sim — recursive plan step simulation
 * 3. foldl_body / plan_steps_eq_foldl — bridge to FOLDL-based definitions
 *)

Theory foldlSim
Ancestors
  codegenRel asmSem planExec stackPlanTypes stackModel
  blockSimHelpers stackOpSim
  list rich_list arithmetic
Libs markerLib

(* ===================================================================
   Two-segment composition
   =================================================================== *)

Theorem plan_seq_sim:
  !lo o2pc prog vs ps1 ps2 ps3 ops1 ops2 st.
    venom_asm_rel lo ps1 vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp (ops1 ++ ops2)) /\
    (!st1.
      venom_asm_rel lo ps1 vs st1 /\
      asm_block_at prog st1.as_pc (execute_plan initial_fmp ops1) ==>
      ?st2.
        asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops1)) st1 = AsmOK st2 /\
        venom_asm_rel lo ps2 vs st2 /\
        st2.as_pc = st1.as_pc + LENGTH (execute_plan initial_fmp ops1)) /\
    (!st2.
      venom_asm_rel lo ps2 vs st2 /\
      asm_block_at prog st2.as_pc (execute_plan initial_fmp ops2) ==>
      ?st3.
        asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops2)) st2 = AsmOK st3 /\
        venom_asm_rel lo ps3 vs st3 /\
        st3.as_pc = st2.as_pc + LENGTH (execute_plan initial_fmp ops2)) ==>
    ?st3.
      asm_steps lo o2pc prog
        (LENGTH (execute_plan initial_fmp (ops1 ++ ops2))) st = AsmOK st3 /\
      venom_asm_rel lo ps3 vs st3 /\
      st3.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp (ops1 ++ ops2))
Proof
  rpt gen_tac >> strip_tac >>
  `asm_block_at prog st.as_pc (execute_plan initial_fmp ops1) /\
   asm_block_at prog (st.as_pc + LENGTH (execute_plan initial_fmp ops1))
     (execute_plan initial_fmp ops2)` by
    fs[execute_plan_append, asm_block_at_append] >>
  `?st2. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops1)) st = AsmOK st2 /\
         venom_asm_rel lo ps2 vs st2 /\
         st2.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops1)` by
    (first_x_assum (qspec_then `st` mp_tac) >> simp[]) >>
  `asm_block_at prog st2.as_pc (execute_plan initial_fmp ops2)` by
    ASM_REWRITE_TAC[] >>
  `?st3. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops2)) st2 = AsmOK st3 /\
         venom_asm_rel lo ps3 vs st3 /\
         st3.as_pc = st2.as_pc + LENGTH (execute_plan initial_fmp ops2)` by
    (first_x_assum (qspec_then `st2` mp_tac) >> simp[]) >>
  qexists_tac `st3` >>
  simp[execute_plan_append, LENGTH_APPEND] >>
  irule asm_steps_compose_ok >>
  qexistsl_tac [`st2`] >>
  ASM_REWRITE_TAC[]
QED

(* ===================================================================
   Per-step simulation property
   =================================================================== *)

Definition step_sim_ok_def:
  step_sim_ok initial_fmp f lo o2pc prog vs =
    !item ps ops ps1 st.
      f item ps = (ops, ps1) /\
      venom_asm_rel lo ps vs st /\
      asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
      ?st1.
        asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st1 /\
        venom_asm_rel lo ps1 vs st1 /\
        st1.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
End

(* ===================================================================
   Recursive plan step computation and FOLDL bridge
   =================================================================== *)

Definition plan_steps_def:
  plan_steps (f : 'a -> plan_state -> stack_op list # plan_state)
    [] ps = ([] : stack_op list, ps) /\
  plan_steps f (item::rest) ps =
    let (step_ops, ps1) = f item ps in
    let (rest_ops, ps_final) = plan_steps f rest ps1 in
    (step_ops ++ rest_ops, ps_final)
End

(* Named FOLDL body — avoids let/lambda mismatch in proofs *)
Definition foldl_body_def:
  foldl_body (f : 'a -> plan_state -> stack_op list # plan_state)
    (ops_acc : stack_op list, ps_cur) item =
    let (step_ops, ps_next) = f item ps_cur in
    (ops_acc ++ step_ops, ps_next)
End

(* SND is invariant under accumulator *)
Theorem foldl_plan_snd[local]:
  !(items : 'a list)
    (f : 'a -> plan_state -> stack_op list # plan_state) acc ps.
    SND (FOLDL (foldl_body f) (acc, ps) items) =
    SND (plan_steps f items ps)
Proof
  Induct_on `items`
  THENL [
    simp[plan_steps_def, foldl_body_def],
    rpt gen_tac >>
    PURE_ONCE_REWRITE_TAC[plan_steps_def] >>
    PURE_ONCE_REWRITE_TAC[FOLDL] >>
    simp[foldl_body_def] >>
    Cases_on `f h ps` >>
    rename1 `f h ps = (step_ops, ps1)` >>
    simp[] >>
    Cases_on `plan_steps f items ps1` >>
    simp[]
  ]
QED

(* FST accumulates correctly *)
Theorem foldl_plan_fst[local]:
  !(items : 'a list)
    (f : 'a -> plan_state -> stack_op list # plan_state) acc ps.
    FST (FOLDL (foldl_body f) (acc, ps) items) =
    acc ++ FST (plan_steps f items ps)
Proof
  Induct_on `items`
  THENL [
    simp[plan_steps_def, foldl_body_def],
    rpt gen_tac >>
    PURE_ONCE_REWRITE_TAC[plan_steps_def] >>
    PURE_ONCE_REWRITE_TAC[FOLDL] >>
    simp[foldl_body_def] >>
    Cases_on `f h ps` >>
    rename1 `f h ps = (step_ops, ps1)` >>
    simp[] >>
    Cases_on `plan_steps f items ps1` >>
    rename1 `plan_steps f items ps1 = (rest_ops, ps_final)` >>
    simp[GSYM APPEND_ASSOC]
  ]
QED

(* Bridge: plan_steps = FOLDL with foldl_body *)
Theorem plan_steps_eq_foldl:
  !(items : 'a list)
    (f : 'a -> plan_state -> stack_op list # plan_state) ps.
    plan_steps f items ps =
    FOLDL (foldl_body f) ([] : stack_op list, ps) items
Proof
  rpt gen_tac >>
  `FST (FOLDL (foldl_body f) ([],ps) items) =
   [] ++ FST (plan_steps f items ps)` by
    REWRITE_TAC[foldl_plan_fst] >>
  `SND (FOLDL (foldl_body f) ([],ps) items) =
   SND (plan_steps f items ps)` by
    REWRITE_TAC[foldl_plan_snd] >>
  Cases_on `plan_steps f items ps` >>
  Cases_on `FOLDL (foldl_body f) ([],ps) items` >>
  fs[]
QED

(* ===================================================================
   Invariant-based simulation (generalizes plan_steps_sim)
   =================================================================== *)

Definition step_sim_ok_inv_def:
  step_sim_ok_inv initial_fmp P f lo o2pc prog vs =
    !item ps ops ps1 st.
      P ps /\
      f item ps = (ops, ps1) /\
      venom_asm_rel lo ps vs st /\
      asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
      ?st1.
        asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st1 /\
        venom_asm_rel lo ps1 vs st1 /\
        st1.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
        P ps1
End

Theorem step_sim_ok_from_inv:
  !P f lo o2pc prog vs.
    step_sim_ok_inv initial_fmp (K T) f lo o2pc prog vs ==>
    step_sim_ok initial_fmp f lo o2pc prog vs
Proof
  simp[step_sim_ok_def, step_sim_ok_inv_def]
QED

Theorem plan_steps_sim_inv:
  !(items : 'a list) f lo o2pc prog vs ps all_ops ps_final st P.
    step_sim_ok_inv initial_fmp P f lo o2pc prog vs /\
    P ps /\
    plan_steps f items ps = (all_ops, ps_final) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp all_ops) ==>
    ?st_final.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp all_ops)) st =
        AsmOK st_final /\
      venom_asm_rel lo ps_final vs st_final /\
      st_final.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp all_ops) /\
      P ps_final
Proof
  Induct >>
  rpt gen_tac >> strip_tac
  >- (gvs[plan_steps_def] >>
      qexists_tac `st` >> simp[execute_plan_def, asm_steps_def])
  >>
  qpat_x_assum `plan_steps _ _ _ = _` mp_tac >>
  simp[Once plan_steps_def, LET_THM] >>
  Cases_on `f h ps` >>
  rename1 `f h ps = (step_ops, ps1)` >>
  simp[] >>
  Cases_on `plan_steps f items ps1` >>
  rename1 `plan_steps f items ps1 = (rest_ops, ps_rest)` >>
  simp[] >> strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  qpat_x_assum `asm_block_at _ _ (execute_plan initial_fmp _)` mp_tac >>
  simp[execute_plan_append, asm_block_at_append] >>
  strip_tac >>
  SUBGOAL_THEN
    ``?st1. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp step_ops)) st =
              AsmOK st1 /\
            venom_asm_rel lo ps1 vs st1 /\
            st1.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp step_ops) /\
            P ps1``
    STRIP_ASSUME_TAC
  THENL [
    qpat_x_assum `step_sim_ok_inv _ _ _ _ _ _ _` mp_tac >>
    simp[step_sim_ok_inv_def] >>
    disch_then (qspecl_then [`h`, `ps`, `step_ops`, `ps1`, `st`]
      mp_tac) >> simp[],
    ALL_TAC
  ] >>
  SUBGOAL_THEN
    ``?st2. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp rest_ops)) st1 =
              AsmOK st2 /\
            venom_asm_rel lo ps_final vs st2 /\
            st2.as_pc = st1.as_pc + LENGTH (execute_plan initial_fmp rest_ops) /\
            P ps_final``
    STRIP_ASSUME_TAC
  THENL [
    first_x_assum (qspecl_then
      [`f`, `lo`, `o2pc`, `prog`, `vs`, `ps1`,
       `rest_ops`, `ps_final`, `st1`, `P`] mp_tac) >>
    simp[step_sim_ok_inv_def],
    ALL_TAC
  ] >>
  qexists_tac `st2` >> rpt conj_tac
  >- metis_tac[asm_steps_compose_ok, ADD_COMM]
  >- ASM_REWRITE_TAC[]
  >- simp[]
  >- ASM_REWRITE_TAC[]
QED

(* plan_steps_sim is the special case with trivial invariant *)
Theorem plan_steps_sim:
  !(items : 'a list) f lo o2pc prog vs ps all_ops ps_final st.
    step_sim_ok initial_fmp f lo o2pc prog vs /\
    plan_steps f items ps = (all_ops, ps_final) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp all_ops) ==>
    ?st_final.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp all_ops)) st =
        AsmOK st_final /\
      venom_asm_rel lo ps_final vs st_final /\
      st_final.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp all_ops)
Proof
  rpt strip_tac >>
  qspecl_then [`items`, `f`, `lo`, `o2pc`, `prog`, `vs`, `ps`,
    `all_ops`, `ps_final`, `st`, `K T`]
    mp_tac plan_steps_sim_inv >>
  simp[step_sim_ok_inv_def] >>
  disch_then match_mp_tac >>
  fs[step_sim_ok_def]
QED

