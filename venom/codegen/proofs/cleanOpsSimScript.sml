(*
 * clean_stack_plan simulation
 *)

Theory cleanOpsSim
Ancestors
  planAlign doSwapSim strongPrefixSim blockSimHelpers
  codegenRel asmSem planExec planWf foldlSim
  stackPlanGen stackPlanTypes stackModel stackPlanOps
  prefixExec stackOpSim
  list rich_list arithmetic

Theorem contiguous_top_stack_bound[local]:
  !to_pop (stk : operand list).
    to_pop <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v stk) to_pop) /\
    is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v stk) to_pop)) ==>
    LENGTH to_pop < LENGTH stk
Proof
  rpt strip_tac >>
  fs[is_contiguous_top_def, LET_THM] >>
  qabbrev_tac `depths = MAP THE (MAP (\v. stack_get_depth v stk) to_pop)` >>
  `LENGTH depths = LENGTH to_pop` by simp[Abbr `depths`] >>
  `LENGTH to_pop >= 1` by
    (CCONTR_TAC >> `LENGTH to_pop = 0` by decide_tac >>
     `to_pop = []` by metis_tac[LENGTH_NIL] >>
     gvs[]) >>
  (* MEM (LENGTH to_pop) depths via QSORT preservation *)
  `MEM (LENGTH to_pop) (GENLIST SUC (LENGTH to_pop))` by
    (simp[MEM_GENLIST] >> qexists_tac `LENGTH to_pop - 1` >> simp[]) >>
  `MEM (LENGTH to_pop) depths` by
    metis_tac[sortingTheory.QSORT_MEM] >>
  (* Get index i where EL i depths = LENGTH to_pop *)
  fs[MEM_EL] >>
  rename1 `nn < LENGTH depths` >>
  `EL nn depths = THE (EL nn (MAP (\v. stack_get_depth v stk) to_pop))` by
    simp[Abbr `depths`, EL_MAP] >>
  `IS_SOME (EL nn (MAP (\v. stack_get_depth v stk) to_pop))` by
    (fs[EVERY_EL] >> first_x_assum irule >> decide_tac) >>
  Cases_on `EL nn (MAP (\v. stack_get_depth v stk) to_pop)` >> fs[] >>
  `stack_get_depth (EL nn to_pop) stk = SOME (LENGTH to_pop)` by
    (qpat_x_assum `EL nn (MAP _ _) = SOME _` mp_tac >> simp[EL_MAP]) >>
  fs[stack_get_depth_def] >>
  imp_res_tac stack_find_bound >>
  fs[]
QED

(* FOLDL body in popmany_individual *)
Definition pop_foldl_body_def:
  pop_foldl_body (ops, ps) v =
    case stack_get_depth v ps.ps_stack of
      NONE => (ops, ps)
    | SOME dist =>
        let (swap_ops, ps1) =
          if dist = 0 then ([] : stack_op list, ps)
          else do_swap dist ps in
        (ops ++ swap_ops ++ [SOPop 1],
         ps1 with ps_stack := stack_pop 1 ps1.ps_stack)
End

Theorem popmany_individual_eq_foldl[local]:
  !to_pop ps.
    popmany_individual to_pop ps =
    FOLDL pop_foldl_body ([], ps)
      (QSORT (\a b.
        case (stack_get_depth a ps.ps_stack,
              stack_get_depth b ps.ps_stack) of
          (SOME da, SOME db) => da <= db
        | _ => T) to_pop)
Proof
  rpt gen_tac >>
  PURE_REWRITE_TAC[popmany_individual_def] >>
  PURE_REWRITE_TAC[LET_THM] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  (* Show the two FOLDL bodies are extensionally equal *)
  SUBGOAL_THEN ``(\(ops,ps) v.
    case stack_get_depth v ps.ps_stack of
      NONE => (ops,ps)
    | SOME dist =>
        (\(swap_ops,ps').
          (ops ++ swap_ops ++ [SOPop 1],
           ps' with ps_stack := stack_pop 1 ps'.ps_stack))
          (if dist = 0 then ([],ps) else do_swap dist ps)) =
    pop_foldl_body``
    (fn th => REWRITE_TAC[th])
  >- (
    simp[FUN_EQ_THM, pairTheory.FORALL_PROD, pop_foldl_body_def] >>
    rpt gen_tac >>
    Cases_on `stack_get_depth v p_2.ps_stack` >> simp[] >>
    Cases_on `x = 0` >> simp[] >>
    Cases_on `do_swap x p_2` >> simp[]
  )
QED

(* do_swap preserves ps_stack length when dist < LENGTH stack *)
Theorem do_swap_length[local]:
  !dist ps ops ps1.
    dist < LENGTH ps.ps_stack /\
    do_swap dist ps = (ops, ps1) ==>
    LENGTH ps1.ps_stack = LENGTH ps.ps_stack
Proof
  rpt strip_tac >>
  qpat_x_assum `do_swap _ _ = _` mp_tac >>
  simp[do_swap_def] >>
  Cases_on `dist = 0` >- simp[] >>
  Cases_on `dist <= 16`
  >- (simp[] >> strip_tac >> gvs[stack_swap_length])
  >- (
    simp[LET_THM] >>
    CONV_TAC (DEPTH_CONV PairRules.PBETA_CONV) >>
    strip_tac >> gvs[] >>
    simp[LENGTH_APPEND, LENGTH_MAP, LENGTH_REVERSE] >>
    qabbrev_tac `chunk = dist + 1` >>
    `chunk <= LENGTH ps.ps_stack` by simp[Abbr `chunk`] >>
    simp[LENGTH_TAKE_EQ] >>
    `LENGTH ([chunk - 1] ++ GENLIST (\i. i + 1) (chunk - 2) ++ [0n]) =
     chunk` by simp[Abbr `chunk`, LENGTH_GENLIST] >>
    simp[]
  )
QED

(* ===================================================================
   pop_one_step: the per-element function for popmany_individual.
   Enables reuse of foldlSim machinery (plan_steps_sim).
   =================================================================== *)

Definition pop_one_step_def:
  pop_one_step v ps =
    case stack_get_depth v ps.ps_stack of
      NONE => ([] : stack_op list, ps)
    | SOME dist =>
        let (swap_ops, ps1) =
          if dist = 0 then ([] : stack_op list, ps)
          else do_swap dist ps in
        (swap_ops ++ [SOPop 1],
         ps1 with ps_stack := stack_pop 1 ps1.ps_stack)
End

Theorem pop_foldl_body_eq_foldl_body[local]:
  pop_foldl_body = foldl_body pop_one_step
Proof
  simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
  rpt gen_tac >>
  simp[pop_foldl_body_def, foldl_body_def, pop_one_step_def] >>
  Cases_on `stack_get_depth x p_2.ps_stack` >> simp[] >>
  Cases_on `x' = 0` >> simp[] >>
  Cases_on `do_swap x' p_2` >> simp[]
QED

Theorem pop_one_step_length[local]:
  !v ps ops ps1.
    pop_one_step v ps = (ops, ps1) ==>
    LENGTH ps1.ps_stack <= LENGTH ps.ps_stack
Proof
  rpt gen_tac >>
  simp[pop_one_step_def] >>
  Cases_on `stack_get_depth v ps.ps_stack`
  THENL [
    simp[] >> strip_tac >> gvs[],
    rename1 `SOME dist` >>
    SUBGOAL_THEN ``dist < LENGTH ps.ps_stack`` STRIP_ASSUME_TAC
    THENL [
      fs[stack_get_depth_def] >> imp_res_tac stack_find_bound >>
      fs[LENGTH_REVERSE],
      ALL_TAC
    ] >>
    Cases_on `dist = 0`
    THENL [
      simp[] >> strip_tac >> gvs[stack_pop_def] >>
      simp[LENGTH_DROP],
      Cases_on `do_swap dist ps` >>
      rename1 `do_swap dist ps = (sw_ops, ps2)` >>
      simp[] >> strip_tac >> gvs[stack_pop_def] >>
      imp_res_tac do_swap_length >>
      simp[LENGTH_DROP]
    ]
  ]
QED

Theorem pop_one_step_sim[local]:
  !v ps ops ps1 lo o2pc prog vs st.
    pop_one_step v ps = (ops, ps1) /\
    (case stack_get_depth v ps.ps_stack of
       NONE => T | SOME d => d <= 16) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st1.
      asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st = AsmOK st1 /\
      venom_asm_rel lo ps1 vs st1 /\
      st1.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `pop_one_step _ _ = _` mp_tac >>
  simp[pop_one_step_def] >>
  Cases_on `stack_get_depth v ps.ps_stack`
  >- (
    (* NONE case *)
    simp[] >> strip_tac >> gvs[] >>
    qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]
  ) >>
  rename1 `SOME dist` >>
  Cases_on `dist = 0`
  >- (
    (* dist = 0: just pop *)
    simp[LET_THM] >> strip_tac >> gvs[] >>
    suspend "dist0"
  ) >>
  (* dist > 0, dist <= 16: swap then pop *)
  Cases_on `do_swap dist ps` >>
  rename1 `do_swap dist ps = (swap_ops, ps2)` >>
  simp[LET_THM] >> strip_tac >> gvs[] >>
  suspend "distN"
QED

Resume pop_one_step_sim[dist0]:
  (* Goal: stack_get_depth = SOME 0, venom_asm_rel, asm_block_at *)
  SUBGOAL_THEN ``0 < LENGTH ps.ps_stack`` STRIP_ASSUME_TAC
  THENL [
    fs[stack_get_depth_def] >> imp_res_tac stack_find_bound >> fs[],
    ALL_TAC
  ] >>
  qspecl_then [`initial_fmp`, `lo`, `o2pc`, `prog`, `SOPop 1`, `ps`, `vs`, `st`]
    mp_tac simple_op_venom_asm_rel >>
  (impl_tac
  THENL [
    conj_tac THENL [EVAL_TAC, ALL_TAC] >>
    conj_tac THENL [simp[stack_op_wf_def] >> decide_tac, ALL_TAC] >>
    conj_tac THENL [first_assum ACCEPT_TAC, ALL_TAC] >>
    fs[execute_plan_def, exec_stack_op_def],
    ALL_TAC
  ]) >>
  strip_tac >>
  rename1 `asm_steps _ _ _ _ st = AsmOK st2` >>
  qexists_tac `st2` >>
  fs[execute_plan_def, exec_stack_op_def, apply_simple_op_def, stack_pop_def]
QED

Resume pop_one_step_sim[distN]:
  (* Manual composition: do_swap then SOPop 1 *)
  SUBGOAL_THEN ``dist < LENGTH ps.ps_stack`` STRIP_ASSUME_TAC
  THENL [
    fs[stack_get_depth_def] >> imp_res_tac stack_find_bound >> fs[],
    ALL_TAC
  ] >>
  qpat_x_assum `asm_block_at _ _ _` mp_tac >>
  PURE_REWRITE_TAC[execute_plan_append, asm_block_at_append] >> strip_tac >>
  (* do_swap (dist <= 16 eliminates spill precondition) *)
  SUBGOAL_THEN ``~(dist > (16:num))`` STRIP_ASSUME_TAC
  THENL [decide_tac, ALL_TAC] >>
  qspecl_then [`dist`, `ps`, `swap_ops`, `ps2`, `lo`, `o2pc`, `prog`,
               `vs`, `st`] mp_tac do_swap_venom_asm_rel_small >>
  (impl_tac THENL [simp[], ALL_TAC]) >> strip_tac >>
  rename1 `asm_steps _ _ _ _ st = AsmOK st2` >>
  (* SOPop 1 *)
  qspecl_then [`initial_fmp`, `lo`, `o2pc`, `prog`, `SOPop 1`, `ps2`, `vs`, `st2`]
    mp_tac simple_op_venom_asm_rel >>
  (impl_tac THENL [
    conj_tac THENL [EVAL_TAC, ALL_TAC] >>
    conj_tac THENL [
      simp[stack_op_wf_def] >> imp_res_tac do_swap_length >> decide_tac,
      ALL_TAC] >>
    conj_tac THENL [first_assum ACCEPT_TAC, ALL_TAC] >>
    fs[execute_plan_def, exec_stack_op_def],
    ALL_TAC]) >> strip_tac >>
  rename1 `asm_steps _ _ _ _ st2 = AsmOK st3` >>
  qexists_tac `st3` >>
  conj_tac THENL [
    fs[execute_plan_append, execute_plan_def, LENGTH_APPEND] >>
    match_mp_tac (GEN_ALL asm_steps_compose_ok) >>
    qexists_tac `st2` >> fs[],
    ALL_TAC
  ] >>
  fs[apply_simple_op_def, stack_pop_def, execute_plan_append,
     execute_plan_def, LENGTH_APPEND]
QED

Finalise pop_one_step_sim;

(* step_sim_ok_inv with stack length invariant.
   Invariant: LENGTH ps.ps_stack <= 17 ensures all depths <= 16. *)
Theorem pop_one_step_sim_ok_inv[local]:
  !lo o2pc prog vs.
    step_sim_ok_inv initial_fmp (\ps. LENGTH ps.ps_stack <= 17)
      pop_one_step lo o2pc prog vs
Proof
  simp[step_sim_ok_inv_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `pop_one_step item ps = (ops, ps1)` >>
  (* Establish depth <= 16 from LENGTH invariant *)
  SUBGOAL_THEN
    ``case stack_get_depth item ps.ps_stack of
        NONE => T | SOME d => d <= 16``
    STRIP_ASSUME_TAC
  THENL [
    Cases_on `stack_get_depth item ps.ps_stack` >> simp[] >>
    fs[stack_get_depth_def] >>
    imp_res_tac stack_find_bound >> fs[LENGTH_REVERSE] >> decide_tac,
    ALL_TAC
  ] >>
  (* Apply pop_one_step_sim *)
  qspecl_then [`item`, `ps`, `ops`, `ps1`, `lo`, `o2pc`, `prog`, `vs`, `st`]
    mp_tac pop_one_step_sim >>
  (impl_tac THENL [ASM_REWRITE_TAC[], ALL_TAC]) >>
  strip_tac >>
  qexists_tac `st1` >> ASM_REWRITE_TAC[] >>
  (* Invariant preserved via pop_one_step_length *)
  imp_res_tac pop_one_step_length >> decide_tac
QED

(* FOLDL simulation via plan_steps_sim_inv.
   Uses mp_tac + impl_tac to avoid itlist2 bug with SUBGOAL_THEN on
   polymorphic plan_steps (type variable mismatch in THENL branches). *)
val pop_foldl_sim = save_thm("pop_foldl_sim", prove(
  ``!sorted lo o2pc prog ps vs st ops_acc ps2.
    venom_asm_rel lo ps vs st /\
    LENGTH ps.ps_stack <= 17 /\
    FOLDL pop_foldl_body ([], ps) sorted = (ops_acc, ps2) /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops_acc) ==>
    ?st1. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops_acc)) st =
            AsmOK st1 /\
          venom_asm_rel lo ps2 vs st1 /\
          st1.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops_acc)``,
  rpt strip_tac >>
  mp_tac (INST_TYPE [alpha |-> ``:operand``] plan_steps_sim_inv) >>
  disch_then (qspecl_then [`sorted`, `pop_one_step`,
    `lo`, `o2pc`, `prog`, `vs`,
    `ps`, `ops_acc`, `ps2`, `st`,
    `\p:plan_state. LENGTH p.ps_stack <= 17`] mp_tac) >>
  impl_tac
  THENL [
    REWRITE_TAC[plan_steps_eq_foldl, GSYM pop_foldl_body_eq_foldl_body] >>
    BETA_TAC >> ASM_REWRITE_TAC[pop_one_step_sim_ok_inv],
    strip_tac >> qexists_tac `st_final` >> ASM_REWRITE_TAC[]
  ]
));

(* Main theorem: popmany_individual preserves venom_asm_rel *)
Theorem popmany_individual_sim:
  !to_pop ps clean_ops ps2 lo o2pc prog vs as.
    popmany_individual to_pop ps = (clean_ops, ps2) /\
    LENGTH ps.ps_stack <= 17 /\
    venom_asm_rel lo ps vs as /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp clean_ops) ==>
    ?n as'.
      asm_steps lo o2pc prog n as = AsmOK as' /\
      venom_asm_rel lo ps2 vs as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp clean_ops)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `popmany_individual _ _ = _` mp_tac >>
  PURE_REWRITE_TAC[popmany_individual_eq_foldl] >>
  strip_tac >>
  drule_all pop_foldl_sim >>
  metis_tac[]
QED

Theorem popmany_plan_top_two_sim:
  !drop_a drop_b a b stk ps ops ps' lo o2pc prog vs st.
    ps.ps_stack = stk ++ [a; b] /\
    a <> b /\
    popmany_plan
      (if drop_a then a :: if drop_b then [b] else []
       else if drop_b then [b] else []) ps = (ops,ps') /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?n st'.
      asm_steps lo o2pc prog n st = AsmOK st' /\
      venom_asm_rel lo ps' vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt gen_tac >> strip_tac >>
  qexists_tac `LENGTH (execute_plan initial_fmp ops)` >>
  Cases_on `drop_a` >> Cases_on `drop_b` >>
  gvs[popmany_plan_def, popmany_individual_def, is_contiguous_top_def,
      stack_get_depth_def, stack_find_def, do_swap_def, LET_THM,
      REVERSE_APPEND, stack_pop_def, TAKE_APPEND1, TAKE_APPEND2,
      sortingTheory.QSORT_DEF,
      sortingTheory.PARTITION_DEF, sortingTheory.PART_DEF] >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  TRY (rename1 `asm_block_at _ _ (execute_plan _ [])` >>
       qexists_tac `st` >>
       gvs[asm_steps_def, execute_plan_def] >> NO_TAC) >>
  TRY (rename1 `asm_block_at _ _ (execute_plan _ [SOPop 1])` >>
       qspecl_then [`[SOPop 1]`, `initial_fmp`, `lo`, `o2pc`, `prog`,
                    `ps`, `vs`, `st`] mp_tac simple_prefix_venom_asm_rel >>
       (impl_tac >-
         gvs[prefix_wf_def, stack_op_wf_def, is_simple_stack_op_def]) >>
       strip_tac >> qexists_tac `st'` >>
       gvs[apply_simple_ops_def, apply_simple_op_def, stack_pop_def,
           TAKE_APPEND1, TAKE_APPEND2] >> NO_TAC) >>
  TRY (rename1 `asm_block_at _ _ (execute_plan _ [SOSwap 1; SOPop 1])` >>
       qspecl_then [`[SOSwap 1; SOPop 1]`, `initial_fmp`, `lo`, `o2pc`, `prog`,
                    `ps`, `vs`, `st`] mp_tac simple_prefix_venom_asm_rel >>
       (impl_tac >-
         gvs[prefix_wf_def, stack_op_wf_def, is_simple_stack_op_def]) >>
       strip_tac >> qexists_tac `st'` >>
       gvs[apply_simple_ops_def, apply_simple_op_def, stack_swap_def,
           stack_pop_def, TAKE_APPEND1, TAKE_APPEND2] >> NO_TAC) >>
  rename1 `asm_block_at _ _ (execute_plan _ [SOPop 1; SOPop 1])` >>
  qspecl_then [`[SOPop 1; SOPop 1]`, `initial_fmp`, `lo`, `o2pc`, `prog`,
               `ps`, `vs`, `st`] mp_tac simple_prefix_venom_asm_rel >>
  (impl_tac >-
    gvs[prefix_wf_def, stack_op_wf_def, is_simple_stack_op_def]) >>
  strip_tac >> qexists_tac `st'` >>
  gvs[apply_simple_ops_def, apply_simple_op_def, stack_pop_def,
      TAKE_APPEND1, TAKE_APPEND2]
QED
Theorem clean_ops_sim:
  !label_offsets offset_to_pc prog liveness cfg fn bb ps ps2 clean_ops vs as.
    venom_asm_rel label_offsets ps vs as /\
    LENGTH ps.ps_stack <= 17 /\
    clean_stack_plan liveness cfg fn bb ps = (clean_ops, ps2) /\
    asm_block_at prog as.as_pc (execute_plan initial_fmp clean_ops) ==>
    ?n as'.
      asm_steps label_offsets offset_to_pc prog n as = AsmOK as' /\
      venom_asm_rel label_offsets ps2 vs as' /\
      as'.as_pc = as.as_pc + LENGTH (execute_plan initial_fmp clean_ops)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `clean_stack_plan _ _ _ _ _ = _` mp_tac >>
  simp[clean_stack_plan_def, LET_THM] >>
  Cases_on `cfg_preds_of cfg bb.bb_label`
  >- (
    simp[] >> strip_tac >> gvs[] >>
    qexistsl_tac [`0`, `as`] >>
    simp[asm_steps_def, execute_plan_def]
  ) >>
  Cases_on `t`
  >- (
    rename1 `cfg_preds_of _ _ = [pred_lbl]` >>
    simp[] >>
    Cases_on `LENGTH (cfg_succs_of cfg pred_lbl) <= 1`
    >- (
      simp[] >> strip_tac >> gvs[] >>
      qexistsl_tac [`0`, `as`] >>
      simp[asm_steps_def, execute_plan_def]
    ) >>
    simp[] >>
    Cases_on `lookup_block pred_lbl fn.fn_blocks`
    >- (
      simp[] >> strip_tac >> gvs[] >>
      qexistsl_tac [`0`, `as`] >>
      simp[asm_steps_def, execute_plan_def]
    ) >>
    rename1 `lookup_block _ _ = SOME pred_bb` >>
    simp[] >>
    qabbrev_tac `inputs = input_vars_from pred_lbl
      bb.bb_instructions (live_vars_at liveness bb.bb_label 0)` >>
    qabbrev_tac `layout = live_vars_at liveness pred_lbl
      (LENGTH pred_bb.bb_instructions)` >>
    qabbrev_tac `to_pop = FILTER (\v. ~MEM v inputs) layout` >>
    strip_tac >>
    Cases_on `MAP Var to_pop = ([] : operand list)`
    >- (
      `clean_ops = [] /\ ps2 = ps` by
        (qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
         simp[popmany_plan_def]) >>
      gvs[] >>
      qexistsl_tac [`0`, `as`] >>
      simp[asm_steps_def, execute_plan_def]
    ) >>
    qabbrev_tac `depths_opt =
      MAP (\v. stack_get_depth v ps.ps_stack) (MAP Var to_pop)` >>
    Cases_on `EVERY IS_SOME depths_opt /\
              is_contiguous_top (MAP THE depths_opt)`
    >- (
      (* Contiguous case *)
      `LENGTH (MAP Var to_pop) < LENGTH ps.ps_stack` by (
        irule contiguous_top_stack_bound >>
        ASM_REWRITE_TAC[] >>
        simp[Abbr `depths_opt`]
      ) >>
      `LENGTH (MAP Var to_pop) <= 16` by (
        fs[Abbr `depths_opt`, is_contiguous_top_def, LET_THM]
      ) >>
      suspend "contiguous"
    )
    >- suspend "noncontig"
  ) >>
  (* Multiple predecessors *)
  simp[] >> strip_tac >> gvs[] >>
  qexistsl_tac [`0`, `as`] >>
  simp[asm_steps_def, execute_plan_def]
QED

Resume clean_ops_sim[contiguous]:
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
  qexistsl_tac [`LENGTH (execute_plan initial_fmp clean_ops)`] >>
  irule popmany_plan_contiguous_sim >>
  conj_tac >- ASM_REWRITE_TAC[] >>
  qexistsl_tac [`ps`, `MAP Var to_pop`] >>
  ASM_REWRITE_TAC[] >>
  simp[Abbr `depths_opt`]
QED

(* Helper: popmany_plan falls back to popmany_individual when not contiguous *)
Theorem popmany_plan_noncontig[local]:
  !ops ps ops2 ps2.
    ops <> [] /\
    ~(EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) ops) /\
      is_contiguous_top (MAP THE (MAP (\v. stack_get_depth v ps.ps_stack) ops))) /\
    popmany_plan ops ps = (ops2, ps2) ==>
    popmany_individual ops ps = (ops2, ps2)
Proof
  Cases_on `ops`
  >- (rpt strip_tac >> fs[])
  >- (
    rpt strip_tac >>
    qpat_x_assum `popmany_plan _ _ = _` mp_tac >>
    PURE_REWRITE_TAC[popmany_plan_def, LET_THM] >> BETA_TAC >>
    IF_CASES_TAC
    >- (
      IF_CASES_TAC
      >- (qpat_x_assum `~_` mp_tac >> ASM_REWRITE_TAC[])
      >- simp[]
    )
    >- simp[]
  )
QED

Resume clean_ops_sim[noncontig]:
  qpat_x_assum `Abbrev (depths_opt = _)` (STRIP_ASSUME_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  qpat_x_assum `depths_opt = _` SUBST_ALL_TAC >>
  SUBGOAL_THEN ``popmany_individual (MAP Var to_pop) ps = (clean_ops:(stack_op list), ps2)``
    STRIP_ASSUME_TAC
  THENL [
    match_mp_tac popmany_plan_noncontig >>
    ASM_REWRITE_TAC[],
    drule_all popmany_individual_sim >>
    metis_tac[ADD_COMM]
  ]
QED

Finalise clean_ops_sim;

