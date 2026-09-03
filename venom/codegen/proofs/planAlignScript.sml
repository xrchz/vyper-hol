(*
 * Plan Alignment Lemmas
 *
 * Proves that codegen sub-functions (do_swap, do_dup, popmany_plan, etc.)
 * produce ops whose apply_prefix_ops matches the computed plan state.
 *
 * This is the bridge between mixed_prefix_venom_asm_rel (which uses
 * apply_prefix_ops) and the actual plan state from the codegen.
 *)

Theory planAlign
Ancestors
  stackPlanOps stackPlanTypes stackModel stackPlanGen
  mixedPrefixSim strongPrefixSim prefixExec
  planExec
  list rich_list finite_map
Libs
  BasicProvers

(* =========================================================================
   do_swap alignment (dist <= 16)
   ========================================================================= *)

Theorem do_swap_align:
  !dist ps ops ps'.
    do_swap dist ps = (ops, ps') /\ dist <= 16 ==>
    !lo. apply_prefix_ops initial_fmp lo ops ps = ps'
Proof
  rpt strip_tac >>
  fs[do_swap_def] >>
  Cases_on `dist = 0`
  >- gvs[apply_prefix_ops_def]
  >- (gvs[apply_prefix_ops_def, apply_prefix_op_def,
          apply_simple_op_def])
QED

(* =========================================================================
   do_dup alignment (dist <= 15)
   ========================================================================= *)

Theorem do_dup_align:
  !dist ps ops ps'.
    do_dup dist ps = (ops, ps') /\ dist <= 15 ==>
    !lo. apply_prefix_ops initial_fmp lo ops ps = ps'
Proof
  rpt strip_tac >>
  fs[do_dup_def] >>
  gvs[apply_prefix_ops_def, apply_prefix_op_def,
      apply_simple_op_def, stack_dup_def, stack_push_def,
      stack_peek_def]
QED

(* =========================================================================
   SOPop alignment
   ========================================================================= *)

Theorem sopop_align:
  !n ps lo.
    apply_prefix_ops initial_fmp lo [SOPop n] ps =
      ps with ps_stack := TAKE (LENGTH ps.ps_stack - n) ps.ps_stack
Proof
  simp[apply_prefix_ops_def, apply_prefix_op_def, apply_simple_op_def]
QED

(* =========================================================================
   Composition: apply_prefix_ops on appended op lists
   ========================================================================= *)

Theorem apply_prefix_ops_append:
  !ops1 ops2 lo ps.
    apply_prefix_ops initial_fmp lo (ops1 ++ ops2) ps =
    apply_prefix_ops initial_fmp lo ops2 (apply_prefix_ops initial_fmp lo ops1 ps)
Proof
  Induct_on `ops1` >>
  simp[apply_prefix_ops_def]
QED

Theorem apply_prefix_ops_nil:
  !lo ps. apply_prefix_ops initial_fmp lo [] ps = ps
Proof
  simp[apply_prefix_ops_def]
QED

(* =========================================================================
   popmany_plan contiguous alignment (dist <= 16)
   When all items to pop are contiguous at top and dist <= 16,
   the generated ops (swap + pop) align with plan state.
   ========================================================================= *)

Theorem popmany_plan_contiguous_align:
  !to_pop ps ops ps'.
    popmany_plan to_pop ps = (ops, ps') /\
    to_pop <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) to_pop) /\
    is_contiguous_top (MAP THE
      (MAP (\v. stack_get_depth v ps.ps_stack) to_pop)) /\
    LENGTH to_pop <= 16 ==>
    !lo. apply_prefix_ops initial_fmp lo ops ps = ps'
Proof
  rpt strip_tac >>
  (* to_pop <> [] so unfold the non-empty clause *)
  Cases_on `to_pop` >- fs[] >>
  fs[popmany_plan_def, LET_THM] >>
  (* EVERY IS_SOME simplifies the if *)
  gvs[] >>
  (* is_contiguous_top simplifies the inner if *)
  Cases_on `do_swap (LENGTH (h::t)) ps` >>
  rename1 `do_swap _ _ = (swap_ops, ps2)` >>
  gvs[] >>
  `apply_prefix_ops initial_fmp lo swap_ops ps = ps2` by
    metis_tac[do_swap_align] >>
  simp[apply_prefix_ops_append, sopop_align, stack_pop_def]
QED

(* =========================================================================
   Bridge: apply_prefix_ops = apply_simple_ops for simple ops
   ========================================================================= *)

Theorem apply_prefix_op_simple:
  !lo op ps.
    is_simple_stack_op op ==>
    apply_prefix_op initial_fmp lo op ps = apply_simple_op lo op ps
Proof
  rpt strip_tac >>
  Cases_on `op` >> fs[is_simple_stack_op_def, apply_prefix_op_def] >>
  Cases_on `o'` >> fs[is_simple_stack_op_def, apply_prefix_op_def]
QED

Theorem apply_prefix_ops_eq_simple:
  !ops lo ps.
    EVERY is_simple_stack_op ops ==>
    apply_prefix_ops initial_fmp lo ops ps = apply_simple_ops lo ops ps
Proof
  Induct_on `ops` >>
  simp[apply_prefix_ops_def, apply_simple_ops_def] >>
  rpt strip_tac >>
  fs[EVERY_DEF] >>
  `apply_prefix_op initial_fmp lo h ps = apply_simple_op lo h ps` by
    metis_tac[apply_prefix_op_simple] >>
  ASM_REWRITE_TAC[]
QED

(* =========================================================================
   do_swap produces simple ops
   ========================================================================= *)

Theorem do_swap_simple:
  !dist ps ops ps'.
    do_swap dist ps = (ops, ps') /\ dist <= 16 ==>
    EVERY is_simple_stack_op ops
Proof
  rpt strip_tac >>
  fs[do_swap_def] >>
  Cases_on `dist = 0` >> gvs[is_simple_stack_op_def]
QED

(* =========================================================================
   popmany_plan contiguous produces simple ops
   ========================================================================= *)

Theorem popmany_plan_contiguous_simple:
  !to_pop ps ops ps'.
    popmany_plan to_pop ps = (ops, ps') /\
    to_pop <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) to_pop) /\
    is_contiguous_top (MAP THE
      (MAP (\v. stack_get_depth v ps.ps_stack) to_pop)) /\
    LENGTH to_pop <= 16 ==>
    EVERY is_simple_stack_op ops
Proof
  rpt strip_tac >>
  Cases_on `to_pop` >- fs[] >>
  fs[popmany_plan_def, LET_THM] >> gvs[] >>
  Cases_on `do_swap (LENGTH (h::t)) ps` >>
  rename1 `do_swap _ _ = (swap_ops, ps2)` >> gvs[] >>
  simp[EVERY_APPEND, is_simple_stack_op_def] >>
  irule do_swap_simple >> metis_tac[]
QED

(* =========================================================================
   popmany_plan contiguous prefix_wf
   ========================================================================= *)

Theorem popmany_plan_contiguous_prefix_wf:
  !to_pop ps ops ps' lo.
    popmany_plan to_pop ps = (ops, ps') /\
    to_pop <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) to_pop) /\
    is_contiguous_top (MAP THE
      (MAP (\v. stack_get_depth v ps.ps_stack) to_pop)) /\
    LENGTH to_pop <= 16 /\
    LENGTH to_pop < LENGTH ps.ps_stack ==>
    prefix_wf lo (LENGTH ps.ps_stack) ops
Proof
  rpt strip_tac >>
  Cases_on `to_pop` >- fs[] >>
  fs[popmany_plan_def, LET_THM] >> gvs[] >>
  Cases_on `do_swap (LENGTH (h::t)) ps` >>
  rename1 `do_swap _ _ = (swap_ops, ps2)` >> gvs[] >>
  (* do_swap dist: either [] or [SOSwap dist] *)
  fs[do_swap_def] >>
  Cases_on `SUC (LENGTH t) = 0` >- fs[] >>
  gvs[] >>
  (* ops = [SOSwap (SUC (LENGTH t)); SOPop (SUC (LENGTH t))] *)
  simp[prefix_wf_def, stack_op_wf_def]
QED

(* =========================================================================
   Combined popmany_plan contiguous simulation lemma
   ========================================================================= *)

(* Packages alignment + simple + prefix_wf into a single usable lemma *)
Theorem popmany_plan_contiguous_sim:
  !to_pop ps ops ps' lo o2pc prog vs st.
    popmany_plan to_pop ps = (ops, ps') /\
    to_pop <> [] /\
    EVERY IS_SOME (MAP (\v. stack_get_depth v ps.ps_stack) to_pop) /\
    is_contiguous_top (MAP THE
      (MAP (\v. stack_get_depth v ps.ps_stack) to_pop)) /\
    LENGTH to_pop <= 16 /\
    LENGTH to_pop < LENGTH ps.ps_stack /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
            AsmOK st' /\
          venom_asm_rel lo ps' vs st' /\
          st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops)
Proof
  rpt strip_tac >>
  (* Use simple_prefix_venom_asm_rel *)
  qspecl_then [`ops`, `initial_fmp`, `lo`, `o2pc`, `prog`, `ps`, `vs`, `st`]
    mp_tac simple_prefix_venom_asm_rel >>
  (impl_tac >- (
    rpt conj_tac
    >- metis_tac[popmany_plan_contiguous_simple]
    >- metis_tac[popmany_plan_contiguous_prefix_wf]
    >> ASM_REWRITE_TAC[]
  )) >>
  strip_tac >>
  qexists_tac `st'` >> ASM_REWRITE_TAC[] >>
  (* Bridge: apply_simple_ops = apply_prefix_ops for simple ops *)
  `EVERY is_simple_stack_op ops` by
    metis_tac[popmany_plan_contiguous_simple] >>
  `apply_simple_ops lo ops ps = apply_prefix_ops initial_fmp lo ops ps` by
    metis_tac[apply_prefix_ops_eq_simple] >>
  `apply_prefix_ops initial_fmp lo ops ps = ps'` by
    metis_tac[popmany_plan_contiguous_align] >>
  gvs[]
QED

(* =========================================================================
   Spill map injectivity: Hilbert choice resolves uniquely
   ========================================================================= *)

(* When the spill map has non-overlapping offsets (from spill_alloc_wf),
   the Hilbert choice @op. FLOOKUP spilled op = SOME off is uniquely
   determined. *)
Theorem spill_hilbert_unique:
  !spilled (op:operand) (off:num).
    FLOOKUP spilled op = SOME off /\
    (!op1 off1 op2 off2.
       FLOOKUP spilled op1 = SOME off1 /\
       FLOOKUP spilled op2 = SOME off2 /\
       op1 <> op2 ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1) ==>
    (@op'. FLOOKUP spilled op' = SOME off) = op
Proof
  rpt strip_tac >>
  SELECT_ELIM_TAC >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  spose_not_then assume_tac >>
  first_x_assum (qspecl_then [`x`, `off`, `op`, `off`] mp_tac) >>
  simp[]
QED

(* =========================================================================
   do_restore alignment on ps_stack and ps_spilled
   ========================================================================= *)

(* do_restore aligns with apply_prefix_ops on stack and spilled fields,
   given that the spill map has non-overlapping offsets. *)
Theorem do_restore_ss_align:
  !op ps ops ps'.
    do_restore op ps = (ops, ps') /\
    (!op1 off1 op2 off2.
       FLOOKUP ps.ps_spilled op1 = SOME off1 /\
       FLOOKUP ps.ps_spilled op2 = SOME off2 /\
       op1 <> op2 ==>
       off1 + 32 <= off2 \/ off2 + 32 <= off1) ==>
    !lo. (apply_prefix_ops initial_fmp lo ops ps).ps_stack = ps'.ps_stack /\
         (apply_prefix_ops initial_fmp lo ops ps).ps_spilled = ps'.ps_spilled
Proof
  rpt strip_tac >>
  fs[do_restore_def] >>
  Cases_on `FLOOKUP ps.ps_spilled op` >>
  gvs[apply_prefix_ops_def, apply_prefix_op_def, LET_THM,
      stack_push_def] >>
  rename1 `FLOOKUP ps.ps_spilled op = SOME off` >>
  `spill_lookup off ps.ps_spilled = op` by
    (simp[spill_lookup_def] >> metis_tac[spill_hilbert_unique]) >>
  simp[DOMSUB_FLOOKUP_THM]
QED

(* =========================================================================
   stack_get_depth bounds
   ========================================================================= *)

Theorem stack_find_bound:
  !p l d. stack_find p l = SOME d ==> d < LENGTH l
Proof
  Induct_on `l` >> simp[stack_find_def] >> rpt strip_tac >>
  Cases_on `p h` >> fs[] >>
  Cases_on `stack_find p l` >> fs[] >> res_tac >> simp[]
QED

Theorem stack_get_depth_bound:
  !op stk d. stack_get_depth op stk = SOME d ==> d < LENGTH stk
Proof
  rpt strip_tac >> fs[stack_get_depth_def] >>
  imp_res_tac stack_find_bound >> fs[]
QED

(* =========================================================================
   emit_one_input alignment on ps_stack and ps_spilled
   ========================================================================= *)

(* When the spill map is injective and stack sufficiently small,
   emit_one_input's ops align with the returned plan state
   on ps_stack and ps_spilled. *)
Theorem emit_one_input_ss_align:
  !opc next_liveness op ps ops ps'.
    emit_one_input opc next_liveness op ps = (ops, ps') /\
    (!op1 off1 op2 off2.
       FLOOKUP ps.ps_spilled op1 = SOME off1 /\
       FLOOKUP ps.ps_spilled op2 = SOME off2 /\
       op1 <> op2 ==> off1 + 32 <= off2 \/ off2 + 32 <= off1) /\
    LENGTH ps.ps_stack <= 15 /\
    ~(?l. op = Label l /\ opc = INVOKE) ==>
    !lo. (apply_prefix_ops initial_fmp lo ops ps).ps_stack = ps'.ps_stack /\
         (apply_prefix_ops initial_fmp lo ops ps).ps_spilled = ps'.ps_spilled
Proof
  rpt gen_tac >> strip_tac >> gen_tac >>
  qpat_x_assum `emit_one_input _ _ _ _ = _` mp_tac >>
  simp[emit_one_input_def, LET_THM] >>
  (* Case split: is restore needed? *)
  Cases_on `is_var_operand op /\ IS_SOME (FLOOKUP ps.ps_spilled op)`
  >- (
    (* Restore case *)
    simp[] >>
    Cases_on `do_restore op ps` >>
    rename1 `do_restore op ps = (restore_ops, ps1)` >>
    simp[] >>
    (* do_restore alignment *)
    `(apply_prefix_ops initial_fmp lo restore_ops ps).ps_stack = ps1.ps_stack /\
     (apply_prefix_ops initial_fmp lo restore_ops ps).ps_spilled = ps1.ps_spilled` by
      (irule do_restore_ss_align >> metis_tac[]) >>
    (* ps1 stack length bound *)
    `LENGTH ps1.ps_stack <= 16` by (
      fs[do_restore_def] >> Cases_on `FLOOKUP ps.ps_spilled op` >>
      gvs[stack_push_def, LENGTH_SNOC, LET_THM]) >>
    (* Now case split on op *)
    Cases_on `op` >> fs[is_var_operand_def]
    >- (
      (* Var v *)
      Cases_on `MEM s next_liveness` >> simp[]
      >- (
        Cases_on `stack_get_depth (Var s) ps1.ps_stack` >> simp[]
        >- (strip_tac >> gvs[])
        >> (
          rename1 `stack_get_depth _ _ = SOME dist` >>
          Cases_on `do_dup dist ps1` >>
          rename1 `do_dup dist ps1 = (dup_ops, ps2)` >>
          simp[] >> strip_tac >> gvs[] >>
          simp[apply_prefix_ops_append] >>
          `dist <= 15` by (
            imp_res_tac stack_get_depth_bound >> simp[]) >>
          (* do_dup with dist <= 15 produces [SODup (dist+1)] *)
          `dup_ops = [SODup (dist + 1)]` by (
            fs[do_dup_def]) >>
          gvs[] >>
          (* Abbreviate intermediate state after restore *)
          qmatch_goalsub_abbrev_tac `apply_prefix_ops initial_fmp lo _ ps_mid` >>
          (* Unfold SODup on ps_mid *)
          simp[apply_prefix_ops_def, apply_prefix_op_def,
               apply_simple_op_def] >>
          (* ps_mid.ps_stack = ps1.ps_stack by do_restore_ss_align *)
          `ps_mid.ps_stack = ps1.ps_stack` by simp[Abbr `ps_mid`] >>
          (* Unfold do_dup to see what ps' is *)
          gvs[do_dup_def, stack_dup_def, stack_peek_def]
        )
      )
      >> (strip_tac >> gvs[])
    )
  )
  >> suspend "no_restore"
QED

Resume emit_one_input_ss_align[no_restore]:
  simp[] >>
  Cases_on `op` >> fs[is_var_operand_def]
  >- ( (* Lit *)
    strip_tac >> gvs[apply_prefix_ops_def,
      apply_prefix_op_def, apply_simple_op_def, stack_push_def]
  )
  >- ( (* Var *)
    Cases_on `MEM s next_liveness` >> simp[]
    >- (
      Cases_on `stack_get_depth (Var s) ps.ps_stack` >> simp[]
      >- simp[apply_prefix_ops_def]
      >- (
        rename1 `stack_get_depth _ _ = SOME dist` >>
        Cases_on `do_dup dist ps` >>
        rename1 `do_dup dist ps = (dup_ops, ps2)` >>
        simp[] >> strip_tac >> gvs[] >>
        `dist <= 15` by (
          imp_res_tac stack_get_depth_bound >> simp[]) >>
        metis_tac[do_dup_align]
      )
    )
    >- simp[apply_prefix_ops_def]
  )
  >- ( (* Label *)
    Cases_on `opc = INVOKE`
    >- (gvs[])
    >> (simp[] >> strip_tac >> gvs[apply_prefix_ops_def,
        apply_prefix_op_def, apply_simple_op_def, stack_push_def])
  )
QED

Finalise emit_one_input_ss_align
