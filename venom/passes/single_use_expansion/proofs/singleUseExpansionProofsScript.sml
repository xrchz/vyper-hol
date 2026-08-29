(*
 * Single Use Expansion Pass — Proofs
 *
 * TOP-LEVEL (exported API):
 *   sue_expand_function_correct_proof — expansion preserves semantics
 *   sue_establishes_single_use_form   — expansion establishes single-use form
 *)

Theory singleUseExpansionProofs
Ancestors
  singleUseExpansionDefs dretShapeDefs passSharedDefs passSharedProps
  passSimulationDefs passSimulationProofs
  stateEquiv stateEquivProps execEquivParamProofs analysisSimProofsBase
  venomWf venomInstProps dfgAnalysisProps
  venomExecSemantics venomExecProofs venomState venomInst
  analysisSimDefs finite_map pred_set list
  indexedLists instIdxIndep
Libs
  pairLib

(* ===== Helper: sue_expand_function is a function_map_transform ===== *)

Theorem sue_expand_function_is_fmt[local]:
  sue_expand_function fn =
  function_map_transform (sue_expand_block (dfg_build_function fn)) fn
Proof
  simp[sue_expand_function_def, function_map_transform_def]
QED

Theorem sue_expand_block_label[local]:
  !dfg bb. (sue_expand_block dfg bb).bb_label = bb.bb_label
Proof
  simp[sue_expand_block_def]
QED

(* ===== Helper: lookup/eval after update_var ===== *)

Theorem lookup_var_update_diff[local]:
  x <> y ==> lookup_var x (update_var y v s) = lookup_var x s
Proof
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem eval_operand_update_diff[local]:
  (!x. op = Var x ==> x <> v) ==>
  eval_operand op (update_var v w s) = eval_operand op s
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_update_diff, update_var_def]
QED

(* ===== Helper: run_insts append ===== *)

Theorem run_insts_append[local]:
  !prefix rest fuel ctx s.
    run_insts fuel ctx (prefix ++ rest) s =
    case run_insts fuel ctx prefix s of
      OK s' => run_insts fuel ctx rest s'
    | Halt v => Halt v
    | Abort a v => Abort a v
    | IntRet v1 v2 => IntRet v1 v2
    | Error e => Error e
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> rw[]
QED

(* ===== sue_expand_ops structural properties ===== *)

(* The assigns produced by sue_expand_ops are all ASSIGN opcode *)
Theorem sue_expand_ops_assigns_are_assign[local]:
  !dfg inst ops idx assigns new_ops.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) ==>
    EVERY (\a. a.inst_opcode = ASSIGN) assigns
Proof
  Induct_on `ops` >> rw[sue_expand_ops_def] >>
  pairarg_tac >> gvs[] >>
  reverse (Cases_on `sue_needs_assign dfg inst idx`) >> gvs[]
  >- (res_tac >> gvs[]) >>
  Cases_on `h` >> gvs[] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  (* Var case: case split on skip condition *)
  Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
            sue_count_remaining (Var s) ops = 0` >> gvs[] >>
  res_tac
QED

(* The new_ops have the same length as the original ops *)
Theorem sue_expand_ops_length[local]:
  !dfg inst ops idx assigns new_ops.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) ==>
    LENGTH new_ops = LENGTH ops
Proof
  Induct_on `ops` >> rw[sue_expand_ops_def] >>
  pairarg_tac >> gvs[] >>
  reverse (Cases_on `sue_needs_assign dfg inst idx`) >> gvs[]
  >- (res_tac >> gvs[]) >>
  Cases_on `h` >> gvs[] >>
  TRY (res_tac >> gvs[] >> NO_TAC) >>
  Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
            sue_count_remaining (Var s) ops = 0` >> gvs[] >>
  res_tac
QED

(* The modified instruction preserves opcode, outputs, id *)
Theorem sue_expand_inst_preserves_opcode[local]:
  !dfg inst.
    ~sue_should_skip inst.inst_opcode ==>
    ?assigns new_ops.
      sue_expand_inst dfg inst = assigns ++ [inst with inst_operands := new_ops] /\
      EVERY (\a. a.inst_opcode = ASSIGN) assigns /\
      LENGTH new_ops = LENGTH inst.inst_operands
Proof
  rw[sue_expand_inst_def] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac sue_expand_ops_assigns_are_assign >>
  imp_res_tac sue_expand_ops_length >> gvs[] >>
  metis_tac[]
QED

(* Skipped instructions are unchanged *)
Theorem sue_expand_inst_skip[local]:
  !dfg inst.
    sue_should_skip inst.inst_opcode ==>
    sue_expand_inst dfg inst = [inst]
Proof
  rw[sue_expand_inst_def]
QED

(* ===== Effect-free simulation helpers ===== *)

(* Running effect-free instructions whose outputs are all in fresh
   preserves state_equiv fresh. Uses step_effect_free_state_equiv. *)
Theorem run_effect_free_state_equiv[local]:
  !insts fuel ctx st st' fresh.
    EVERY (\a. is_effect_free_op a.inst_opcode) insts /\
    EVERY (\a. !out. MEM out a.inst_outputs ==> out IN fresh) insts /\
    run_insts fuel ctx insts st = OK st' ==>
    state_equiv fresh st st'
Proof
  Induct >> rw[run_insts_def]
  >- metis_tac[stateEquivPropsTheory.state_equiv_refl] >>
  Cases_on `step_inst fuel ctx h st` >> gvs[] >>
  `state_equiv (set h.inst_outputs) st v`
    by metis_tac[venomInstPropsTheory.step_effect_free_state_equiv] >>
  `set h.inst_outputs SUBSET fresh`
    by (rw[SUBSET_DEF] >> metis_tac[]) >>
  `state_equiv fresh st v`
    by metis_tac[stateEquivPropsTheory.state_equiv_subset] >>
  `state_equiv fresh v st'` by (
    last_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `st'`, `fresh`] mp_tac) >>
    gvs[]) >>
  metis_tac[stateEquivPropsTheory.state_equiv_trans]
QED

(* ASSIGN is effect-free *)
Theorem assign_is_effect_free[local]:
  is_effect_free_op ASSIGN
Proof
  EVAL_TAC
QED

(* ASSIGN assigns produce effect-free instructions *)
Theorem sue_assigns_are_effect_free[local]:
  !assigns.
    EVERY (\a. a.inst_opcode = ASSIGN) assigns ==>
    EVERY (\a. is_effect_free_op a.inst_opcode) assigns
Proof
  Induct >> rw[] >> EVAL_TAC >> gvs[]
QED

(* ===== run_insts_preserves_lookup ===== *)

(* Effect-free instructions that don't output to v preserve lookup_var v *)
Theorem run_insts_preserves_lookup[local]:
  !insts fuel ctx v st st'.
    run_insts fuel ctx insts st = OK st' /\
    EVERY (\i. ~MEM v i.inst_outputs) insts /\
    EVERY (\i. is_effect_free_op i.inst_opcode) insts ==>
    lookup_var v st' = lookup_var v st
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h st` >> gvs[] >>
  `state_equiv (set h.inst_outputs) st v'`
    by metis_tac[venomInstPropsTheory.step_effect_free_state_equiv] >>
  `v NOTIN set h.inst_outputs` by (gvs[EVERY_MEM] >> metis_tac[]) >>
  `lookup_var v v' = lookup_var v st` by (
    fs[stateEquivTheory.state_equiv_def,
       stateEquivTheory.execution_equiv_def] >>
    first_x_assum (qspec_then `v` mp_tac) >> gvs[]) >>
  first_x_assum (qspecl_then [`fuel`, `ctx`, `v`, `v'`, `st'`] mp_tac) >>
  gvs[]
QED

(* ===== sue_expand_ops outputs ===== *)

(* Assigns produced by sue_expand_ops output to sue_fresh_var at indices in [idx, idx+LENGTH ops) *)
Theorem sue_expand_ops_outputs[local]:
  !dfg inst ops idx assigns new_ops.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) ==>
    EVERY (\a. ?k. idx <= k /\ k < idx + LENGTH ops /\
                   a.inst_outputs = [sue_fresh_var inst.inst_id k])
      assigns
Proof
  Induct_on `ops` >> rw[sue_expand_ops_def] >>
  pairarg_tac >> gvs[] >>
  reverse (Cases_on `sue_needs_assign dfg inst idx`) >> gvs[]
  >- (res_tac >> gvs[EVERY_MEM] >> rw[] >> res_tac >>
      qexists_tac `k` >> gvs[]) >>
  Cases_on `h` >> gvs[]
  >- ((* Lit case *)
      res_tac >> gvs[EVERY_MEM] >> rw[] >> gvs[]
      >- (qexists_tac `idx` >> gvs[])
      >> (res_tac >> qexists_tac `k` >> gvs[]))
  >- ((* Var case *)
      Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
                sue_count_remaining (Var s) ops = 0` >> gvs[]
      >- (res_tac >> gvs[EVERY_MEM] >> rw[] >> res_tac >>
          qexists_tac `k` >> gvs[])
      >> (res_tac >> gvs[EVERY_MEM] >> rw[] >> gvs[]
          >- (qexists_tac `idx` >> gvs[])
          >> (res_tac >> qexists_tac `k` >> gvs[])))
  >- ((* Label case — dead code since sue_needs_assign returns F for Label *)
      res_tac >> gvs[] >> conj_tac
      >- (qexists_tac `idx` >> gvs[])
      >> (gvs[EVERY_MEM] >> rw[] >> res_tac >> qexists_tac `k` >> gvs[]))
QED

(* ===== sue_fresh_var injectivity ===== *)

Theorem sue_fresh_var_inj[local]:
  sue_fresh_var id i = sue_fresh_var id j ==> i = j
Proof
  simp[sue_fresh_var_def]
QED

(* ===== sue_expand_ops_eval — operand equivalence after running assigns ===== *)

(* No original variable appears in assign outputs *)
Theorem sue_expand_ops_no_orig_in_outputs[local]:
  !ops dfg inst idx assigns new_ops v.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    (!j. idx <= j /\ j < idx + LENGTH ops ==>
         v <> sue_fresh_var inst.inst_id j) ==>
    EVERY (\a. ~MEM v a.inst_outputs) assigns
Proof
  rpt strip_tac >>
  imp_res_tac sue_expand_ops_outputs >>
  gvs[EVERY_MEM] >> rw[] >> strip_tac >>
  res_tac >> gvs[MEM]
QED

(* Fresh var at j < idx not in outputs of assigns starting at idx *)
Theorem sue_expand_ops_earlier_fresh_not_in_outputs[local]:
  !ops dfg inst idx assigns new_ops j.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    j < idx ==>
    EVERY (\a. ~MEM (sue_fresh_var inst.inst_id j) a.inst_outputs) assigns
Proof
  rpt strip_tac >>
  imp_res_tac sue_expand_ops_outputs >>
  gvs[EVERY_MEM] >> rw[] >> strip_tac >>
  res_tac >> gvs[MEM] >>
  `j = k` by metis_tac[sue_fresh_var_inj] >> gvs[]
QED

(* Helper: eval_operand on non-fresh var preserved through update_var on fresh *)
Theorem eval_operand_update_fresh[local]:
  !op st id idx w.
    (!x. op = Var x ==> x <> sue_fresh_var id idx) ==>
    eval_operand op (update_var (sue_fresh_var id idx) w st) =
    eval_operand op st
Proof
  Cases >> rw[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Helper: lookup_var on non-fresh var preserved through assigns from sue_expand_ops *)
Theorem sue_assigns_preserve_orig_lookup[local]:
  !ops dfg inst idx assigns new_ops fuel ctx st st' v.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    run_insts fuel ctx assigns st = OK st' /\
    (!j. idx <= j /\ j < idx + LENGTH ops ==>
         v <> sue_fresh_var inst.inst_id j) ==>
    lookup_var v st' = lookup_var v st
Proof
  rpt strip_tac >>
  `EVERY (\a. ~MEM v a.inst_outputs) assigns` by
    metis_tac[sue_expand_ops_no_orig_in_outputs] >>
  `EVERY (\a. is_effect_free_op a.inst_opcode) assigns` by
    (imp_res_tac sue_expand_ops_assigns_are_assign >>
     metis_tac[sue_assigns_are_effect_free]) >>
  metis_tac[run_insts_preserves_lookup]
QED

(* General: effect-free run_insts preserves vs_labels *)
Theorem run_insts_effect_free_preserves_labels[local]:
  !insts fuel ctx st st'.
    run_insts fuel ctx insts st = OK st' /\
    EVERY (\i. is_effect_free_op i.inst_opcode) insts ==>
    st'.vs_labels = st.vs_labels
Proof
  Induct >> rw[run_insts_def] >>
  Cases_on `step_inst fuel ctx h st` >> gvs[] >>
  `state_equiv (set h.inst_outputs) st v`
    by metis_tac[venomInstPropsTheory.step_effect_free_state_equiv] >>
  `v.vs_labels = st.vs_labels` by
    fs[stateEquivTheory.state_equiv_def,
       stateEquivTheory.execution_equiv_def] >>
  metis_tac[]
QED

(* General: sue assigns preserve eval_operand for any operand
   whose Var (if any) is not a sue_fresh_var in the assign range *)
Theorem sue_assigns_preserve_eval_operand[local]:
  !ops dfg inst idx assigns new_ops fuel ctx st st' op.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    run_insts fuel ctx assigns st = OK st' /\
    (!x. op = Var x ==>
         !j. idx <= j /\ j < idx + LENGTH ops ==>
             x <> sue_fresh_var inst.inst_id j) ==>
    eval_operand op st' = eval_operand op st
Proof
  rpt strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def]
  >- ((* Var case: use sue_assigns_preserve_orig_lookup *)
      irule sue_assigns_preserve_orig_lookup >>
      metis_tac[])
  >- ((* Label case: use labels preservation *)
      imp_res_tac sue_expand_ops_assigns_are_assign >>
      `EVERY (\i. is_effect_free_op i.inst_opcode) assigns`
        by metis_tac[sue_assigns_are_effect_free] >>
      drule_all run_insts_effect_free_preserves_labels >> simp[])
QED

(* Freshness decomposition helpers — extract needed forms from
   the bounded freshness precondition on (h::ops) *)
Theorem fresh_cons_tail[local]:
  (!v j. MEM (Var v) (h::ops) /\ lo <= j /\ j < lo + SUC (LENGTH ops) ==>
         v <> f j)
  ==>
  (!v j. MEM (Var v) ops /\ (lo + 1) <= j /\ j < (lo + 1) + LENGTH ops ==>
         v <> f j)
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`v`,`j`] mp_tac) >> simp[]
QED

Theorem fresh_cons_head[local]:
  (!v j. MEM (Var v) (h::ops) /\ lo <= j /\ j < lo + SUC (LENGTH ops) ==>
         v <> f j)
  ==>
  (!v. h = Var v ==> !j. lo <= j /\ j < lo + SUC (LENGTH ops) ==>
       v <> f j)
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`v`,`j`] mp_tac) >> simp[]
QED

Theorem fresh_cons_elem[local]:
  (!v j. MEM (Var v) (h::ops) /\ lo <= j /\ j < lo + SUC (LENGTH ops) ==>
         v <> f j)
  ==>
  (!v. MEM (Var v) ops ==> v <> f lo)
Proof
  rpt strip_tac >>
  first_x_assum (qspecl_then [`v`,`lo`] mp_tac) >> simp[]
QED

(* Core: per-element operand equivalence after running assign prefix *)
Theorem sue_expand_ops_eval[local]:
  !ops dfg inst idx assigns new_ops fuel ctx st st'.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    run_insts fuel ctx assigns st = OK st' /\
    (!v j. MEM (Var v) ops /\ idx <= j /\ j < idx + LENGTH ops ==>
           v <> sue_fresh_var inst.inst_id j)
  ==>
    !i. i < LENGTH ops ==>
        eval_operand (EL i new_ops) st' = eval_operand (EL i ops) st
Proof
  Induct_on `ops` >> rpt gen_tac >> strip_tac
  (* Base: LENGTH [] = 0, so i < 0 is vacuously true *)
  >- gvs[sue_expand_ops_def] >>
  (* Step: extract freshness-derived forms BEFORE gvs mangles them *)
  qpat_x_assum `!v j. MEM (Var v) (h::ops) /\ _ ==> _`
    (fn th => let
      val th' = CONV_RULE (DEPTH_CONV
        (REWR_CONV (CONJUNCT2 listTheory.LENGTH))) th
    in
      assume_tac (MATCH_MP fresh_cons_tail th') >>
      assume_tac (MATCH_MP fresh_cons_head th') >>
      assume_tac (MATCH_MP fresh_cons_elem th')
    end) >>
  gvs[sue_expand_ops_def] >> pairarg_tac >> gvs[] >>
  reverse (Cases_on `sue_needs_assign dfg inst idx`) >> gvs[]
  >- (
    (* Not expanded: assigns = more_assigns, new_ops = h::more_ops *)
    Cases_on `i` >> gvs[]
    >- (
      (* Position 0: passthrough — eval_operand h preserved through assigns *)
      qspecl_then [`ops`, `dfg`, `inst`, `idx + 1`, `assigns`, `more_ops`,
                   `fuel`, `ctx`, `st`, `st'`, `h`]
        mp_tac sue_assigns_preserve_eval_operand >>
      impl_tac >- (
        simp[] >> rpt strip_tac >>
        first_x_assum match_mp_tac >> simp[]
      ) >> simp[]
    )
    >- (
      (* Position SUC n: use IH with tail freshness *)
      first_x_assum (qspecl_then [`dfg`, `inst`, `idx + 1`,
        `assigns`, `more_ops`, `fuel`, `ctx`, `st`, `st'`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspec_then `n` mp_tac) >> simp[]
    )
  )
  >>
  Cases_on `h` >> gvs[]
  (* Lit expanded case *)
  >- (
    gvs[run_insts_def, step_inst_def, step_inst_base_def, eval_operand_def] >>
    Cases_on `i` >> gvs[eval_operand_def]
    >- (
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      imp_res_tac sue_expand_ops_assigns_are_assign >>
      imp_res_tac sue_assigns_are_effect_free >>
      `EVERY (\a. ~MEM (sue_fresh_var inst.inst_id idx) a.inst_outputs)
        more_assigns` by (
        qspecl_then [`ops`, `dfg`, `inst`, `idx + 1`, `more_assigns`,
                     `more_ops`, `idx`]
          mp_tac sue_expand_ops_earlier_fresh_not_in_outputs >>
        simp[]) >>
      drule_all run_insts_preserves_lookup >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
    )
    >- (
      strip_tac >>
      first_x_assum (qspecl_then [`dfg`, `inst`, `idx + 1`,
        `more_assigns`, `more_ops`, `fuel`, `ctx`,
        `update_var (sue_fresh_var inst.inst_id idx) c st`, `st'`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
      `eval_operand (EL n ops)
        (update_var (sue_fresh_var inst.inst_id idx) c st) =
       eval_operand (EL n ops) st` suffices_by gvs[] >>
      irule eval_operand_update_fresh >> rw[] >>
      `MEM (Var x) ops` by metis_tac[MEM_EL] >>
      CCONTR_TAC >> gvs[]
    )
  )
  (* Var expanded case *)
  >- (
    Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
              sue_count_remaining (Var s) ops = 0`
    >- (
      (* Single use passthrough *)
      gvs[] >> Cases_on `i` >> gvs[]
      >- (
        qspecl_then [`ops`, `dfg`, `inst`, `idx + 1`, `assigns`, `more_ops`,
                     `fuel`, `ctx`, `st`, `st'`, `Var s`]
          mp_tac sue_assigns_preserve_eval_operand >>
        simp[eval_operand_def] >>
        (impl_tac >- (
          rpt strip_tac >>
          first_x_assum match_mp_tac >> simp[]
        )) >> simp[]
      )
      >- (
        first_x_assum (qspecl_then [`dfg`, `inst`, `idx + 1`,
          `assigns`, `more_ops`, `fuel`, `ctx`, `st`, `st'`] mp_tac) >>
        (impl_tac >- simp[]) >>
        disch_then (qspec_then `n` mp_tac) >> simp[]
      )
    )
    >- (
      (* Multi-use: expanded with ASSIGN [Var s] prefix *)
      gvs[run_insts_def, step_inst_def, step_inst_base_def, eval_operand_def] >>
      BasicProvers.FULL_CASE_TAC >> gvs[] >>
      Cases_on `i` >> gvs[eval_operand_def]
      >- (
        simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
        imp_res_tac sue_expand_ops_assigns_are_assign >>
        imp_res_tac sue_assigns_are_effect_free >>
        `EVERY (\a. ~MEM (sue_fresh_var inst.inst_id idx) a.inst_outputs)
          more_assigns` by (
          qspecl_then [`ops`, `dfg`, `inst`, `idx + 1`, `more_assigns`,
                       `more_ops`, `idx`]
            mp_tac sue_expand_ops_earlier_fresh_not_in_outputs >>
          simp[]) >>
        drule_all run_insts_preserves_lookup >>
        simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
      )
      >- (
        strip_tac >>
        first_x_assum (qspecl_then [`dfg`, `inst`, `idx + 1`,
          `more_assigns`, `more_ops`, `fuel`, `ctx`,
          `update_var (sue_fresh_var inst.inst_id idx) x st`, `st'`] mp_tac) >>
        (impl_tac >- simp[]) >>
        disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
        `eval_operand (EL n ops)
          (update_var (sue_fresh_var inst.inst_id idx) x st) =
         eval_operand (EL n ops) st` suffices_by gvs[] >>
        irule eval_operand_update_fresh >> rw[] >>
        `MEM (Var x') ops` by metis_tac[MEM_EL] >>
        CCONTR_TAC >> gvs[]
      )
    )
  )
  (* Label expanded case: ASSIGN [Label s] — structurally same as Lit *)
  >- (
    gvs[run_insts_def, step_inst_def, step_inst_base_def, eval_operand_def] >>
    BasicProvers.FULL_CASE_TAC >> gvs[] >>
    Cases_on `i` >> gvs[eval_operand_def]
    >- (
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      imp_res_tac sue_expand_ops_assigns_are_assign >>
      imp_res_tac sue_assigns_are_effect_free >>
      `EVERY (\a. ~MEM (sue_fresh_var inst.inst_id idx) a.inst_outputs)
        more_assigns` by (
        qspecl_then [`ops`, `dfg`, `inst`, `idx + 1`, `more_assigns`,
                     `more_ops`, `idx`]
          mp_tac sue_expand_ops_earlier_fresh_not_in_outputs >>
        simp[]) >>
      drule_all run_insts_preserves_lookup >>
      simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      imp_res_tac run_insts_effect_free_preserves_labels >> gvs[]
    )
    >- (
      strip_tac >>
      first_x_assum (qspecl_then [`dfg`, `inst`, `idx + 1`,
        `more_assigns`, `more_ops`, `fuel`, `ctx`,
        `update_var (sue_fresh_var inst.inst_id idx) x st`, `st'`] mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
      `eval_operand (EL n ops)
        (update_var (sue_fresh_var inst.inst_id idx) x st) =
       eval_operand (EL n ops) st` suffices_by gvs[] >>
      irule eval_operand_update_fresh >> rw[] >>
      `MEM (Var x') ops` by metis_tac[MEM_EL] >>
      CCONTR_TAC >> gvs[]
    )
  )
QED

(* ===== Fresh variable membership ===== *)

(* sue_fresh_var for any instruction/operand in fn is in sue_fresh_vars_fn *)
Theorem sue_fresh_var_in_fresh_set[local]:
  !fn bb inst idx.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    idx < LENGTH inst.inst_operands ==>
    sue_fresh_var inst.inst_id idx IN sue_fresh_vars_fn fn
Proof
  rw[sue_fresh_vars_fn_def] >>
  simp[MEM_FLAT, MEM_MAP, MEM_MAPi, PULL_EXISTS] >>
  metis_tac[]
QED

(* Assign outputs from sue_expand_ops are in sue_fresh_vars_fn *)
Theorem sue_expand_assigns_in_fresh[local]:
  !fn bb inst dfg assigns new_ops.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    sue_expand_ops dfg inst inst.inst_operands 0 = (assigns, new_ops) ==>
    EVERY (\a. !out. MEM out a.inst_outputs ==> out IN sue_fresh_vars_fn fn)
      assigns
Proof
  rpt strip_tac >>
  imp_res_tac sue_expand_ops_outputs >>
  gvs[EVERY_MEM] >> rw[] >>
  res_tac >> gvs[MEM] >>
  irule sue_fresh_var_in_fresh_set >> simp[] >>
  metis_tac[]
QED

(* ===== Structural properties of sue_expand_ops: labels and LOG HD ===== *)

(* When sue_needs_assign is F, the operand passes through unchanged.
   Stated with offset arithmetic: ops is the suffix at position idx. *)
Theorem sue_expand_ops_passthrough[local]:
  !ops dfg inst idx assigns new_ops.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) ==>
    !j. j < LENGTH ops /\ ~sue_needs_assign dfg inst (j + idx) ==>
    EL j new_ops = EL j ops
Proof
  Induct_on `ops` >> rw[sue_expand_ops_def] >>
  pairarg_tac >> gvs[] >>
  reverse (Cases_on `sue_needs_assign dfg inst idx`) >> gvs[]
  >- (
    (* Not expanded: passthrough *)
    Cases_on `j` >> gvs[] >>
    first_x_assum drule >>
    disch_then (qspec_then `n` mp_tac) >>
    full_simp_tac (srw_ss() ++ ARITH_ss) [arithmeticTheory.ADD1]
  )
  >- (
    (* Expanded: j=0 is contradiction *)
    Cases_on `j` >> gvs[] >>
    (* j = SUC n: all expanded branches produce _ :: more_ops,
       so EL (SUC n) new_ops = EL n more_ops. Apply IH. *)
    `(idx + 1) + n = idx + SUC n` by simp[] >>
    `~sue_needs_assign dfg inst ((idx + 1) + n)` by metis_tac[] >>
    Cases_on `h` >> gvs[] >>
    TRY (
      first_x_assum drule >>
      disch_then (qspec_then `n` mp_tac) >> gvs[] >> NO_TAC
    ) >>
    Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
              sue_count_remaining (Var s) ops = 0` >> gvs[] >>
    first_x_assum drule >>
    disch_then (qspec_then `n` mp_tac) >> gvs[]
  )
QED


(* DRET's leading dynamic-count literal is parser syntax and passes through. *)
Theorem sue_expand_ops_dret_parse_preserved[local]:
  inst.inst_opcode = DRET /\
  sue_expand_ops dfg inst inst.inst_operands 0 = (assigns,new_ops) ==>
  parse_dret_shape (inst with inst_operands := new_ops) =
  parse_dret_shape inst
Proof
  rpt strip_tac >>
  imp_res_tac sue_expand_ops_length >>
  Cases_on `inst.inst_operands` >-
    gvs[dretShapeDefsTheory.parse_dret_shape_def, sue_expand_ops_def] >>
  `?more_ops. new_ops = h :: more_ops` by
    metis_tac[sue_expand_ops_DRET_head] >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def]
QED
(* Labels are never expanded: sue_needs_assign returns F for Label operands *)
Theorem sue_expand_ops_label_preserved[local]:
  !dfg inst assigns new_ops.
    sue_expand_ops dfg inst inst.inst_operands 0 = (assigns, new_ops) ==>
    !i. i < LENGTH inst.inst_operands ==>
        !lbl. EL i inst.inst_operands = Label lbl ==> EL i new_ops = Label lbl
Proof
  rpt strip_tac >>
  `EL i new_ops = EL i inst.inst_operands` suffices_by gvs[] >>
  `i < LENGTH inst.inst_operands /\ ~sue_needs_assign dfg inst (i + 0)` by
    (gvs[] >> simp[sue_needs_assign_def]) >>
  metis_tac[sue_expand_ops_passthrough]
QED

(* LOG's first operand is never expanded: sue_needs_assign returns F at index 0 for LOG *)
Theorem sue_expand_ops_log_hd_preserved[local]:
  !dfg inst assigns new_ops.
    inst.inst_opcode = LOG /\
    inst.inst_operands <> [] /\
    sue_expand_ops dfg inst inst.inst_operands 0 = (assigns, new_ops) ==>
    HD new_ops = HD inst.inst_operands
Proof
  rpt strip_tac >>
  `0 < LENGTH inst.inst_operands` by (Cases_on `inst.inst_operands` >> gvs[]) >>
  `0 < LENGTH inst.inst_operands /\ ~sue_needs_assign dfg inst (0 + 0)` by
    (gvs[] >> simp[sue_needs_assign_def]) >>
  `EL 0 new_ops = EL 0 inst.inst_operands` by
    metis_tac[sue_expand_ops_passthrough] >>
  imp_res_tac sue_expand_ops_length >>
  Cases_on `inst.inst_operands` >> gvs[]
QED

(* eval_operand of original operands preserved through assigns *)

(* ===== Per-instruction simulation ===== *)

(* Per-instruction sim: expanding an instruction preserves semantics.
   The key chain:
   1. run_insts assigns st = OK st' ==> state_equiv fresh st st'
   2. eval_operand (EL i new_ops) st' = eval_operand (EL i ops) st (sue_expand_ops_eval)
   3. eval_operand (EL i ops) st' = eval_operand (EL i ops) st (assigns preserve orig)
   4. From 2+3: per-element agreement in st'
   5. step_inst_operands_equiv: step_inst (inst with new_ops) st' = step_inst inst st'
   6. step_inst_preserves_R_proof: lift_result ... (step_inst inst st) (step_inst inst st')
   7. Combine *)
(* ASSIGN instructions only produce OK or Error *)
Theorem step_inst_assign_ok_or_error[local]:
  !fuel ctx inst st.
    inst.inst_opcode = ASSIGN ==>
    (?st'. step_inst fuel ctx inst st = OK st') \/
    (?e. step_inst fuel ctx inst st = Error e)
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_def] >>
  qpat_x_assum `inst.inst_opcode = ASSIGN`
    (fn th => assume_tac th >> PURE_REWRITE_TAC[th]) >>
  simp[is_terminator_def] >>
  ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  qpat_x_assum `inst.inst_opcode = ASSIGN`
    (fn th => PURE_REWRITE_TAC[th]) >> simp[] >>
  Cases_on `inst.inst_operands` >> gvs[] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `t'` >> gvs[] >>
  Cases_on `eval_operand h st` >> gvs[]
QED

(* run_insts on ASSIGN-only list produces OK or Error *)
Theorem run_insts_assigns_ok_or_error[local]:
  !insts fuel ctx st.
    EVERY (\a. a.inst_opcode = ASSIGN) insts ==>
    (?st'. run_insts fuel ctx insts st = OK st') \/
    (?e. run_insts fuel ctx insts st = Error e)
Proof
  Induct >> rw[run_insts_def] >>
  `(?st'. step_inst fuel ctx h st = OK st') \/
   (?e. step_inst fuel ctx h st = Error e)` by
    metis_tac[step_inst_assign_ok_or_error] >>
  gvs[]
QED

(* Helper: if an assign in the expansion prefix errors, the original
   instruction also errors. *)
(* Helper: ASSIGN errors iff eval_operand is NONE *)
Theorem assign_error_eval_none[local]:
  !fuel ctx op out id st.
    (?e. step_inst fuel ctx
           <| inst_opcode := ASSIGN; inst_operands := [op];
              inst_outputs := [out]; inst_id := id |> st = Error e) <=>
    eval_operand op st = NONE
Proof
  rw[step_inst_non_invoke, step_inst_base_def, is_alloca_op_def] >>
  Cases_on `eval_operand op st` >> simp[]
QED

(* Helper: if eval_operands returns NONE, some position has eval NONE *)
Theorem eval_operands_none_exists[local]:
  !ops st. eval_operands ops st = NONE ==>
    ?k. k < LENGTH ops /\ eval_operand (EL k ops) st = NONE
Proof
  Induct >> rw[eval_operands_def] >>
  Cases_on `eval_operand h st` >> gvs[]
  >- (qexists_tac `0` >> simp[])
  >- (Cases_on `eval_operands ops st` >> gvs[] >>
      first_x_assum drule >> strip_tac >>
      qexists_tac `SUC k` >> simp[])
QED

(* Helper: if some position has eval NONE, eval_operands returns NONE *)
Theorem eval_operand_none_implies_operands_none[local]:
  !ops st k. k < LENGTH ops /\ eval_operand (EL k ops) st = NONE ==>
    eval_operands ops st = NONE
Proof
  Induct >> rw[eval_operands_def] >>
  Cases_on `k`
  >- gvs[]
  >- (gvs[] >> Cases_on `eval_operand h st` >> gvs[] >>
      res_tac >> gvs[])
QED

(* Helper: running a single ASSIGN [op] [out] preserves eval of
   operands whose var names differ from out. *)
Theorem single_assign_preserves_eval[local]:
  !fuel ctx op out id st st'.
    step_inst fuel ctx
      <| inst_opcode := ASSIGN; inst_operands := [op];
         inst_outputs := [out]; inst_id := id |> st = OK st' ==>
    !op'. (!x. op' = Var x ==> x <> out) ==>
          eval_operand op' st' = eval_operand op' st
Proof
  rw[step_inst_non_invoke, step_inst_base_def, is_alloca_op_def] >>
  Cases_on `eval_operand op st` >> gvs[] >>
  Cases_on `op'` >> gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

(* Helper: run_insts of assigns from sue_expand_ops errors
   only if some original operand evals to NONE. *)
(* Helper: sue_needs_assign is F for Label operands *)
Theorem sue_needs_assign_label[local]:
  !dfg inst idx l. ~sue_needs_assign dfg inst idx \/
    idx < LENGTH inst.inst_operands /\
    (!l. EL idx inst.inst_operands <> Label l) ==>
    (!l. EL idx inst.inst_operands <> Label l) \/ ~sue_needs_assign dfg inst idx
Proof
  metis_tac[]
QED

(* Helper: run_insts of assigns from sue_expand_ops errors only if some
   original operand evals to NONE. Also: that operand is not a Label.
   Needs no-Label precondition since ops is independent from inst.inst_operands;
   trivially satisfied when ops = inst.inst_operands (sue_needs_assign F for Label). *)
local
val sue_assigns_error_implies_operand_none_thm = prove(``
  !ops dfg inst idx assigns new_ops fuel ctx st.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    (!v k. MEM (Var v) ops /\ idx <= k /\ k < idx + LENGTH ops ==>
           v <> sue_fresh_var inst.inst_id k) /\
    (!k l. k < LENGTH ops /\ sue_needs_assign dfg inst (idx + k) ==>
           EL k ops <> Label l) /\
    (?e. run_insts fuel ctx assigns st = Error e) ==>
    ?k. k < LENGTH ops /\ eval_operand (EL k ops) st = NONE /\
        (!l. EL k ops <> Label l)``,
  Induct
  >- rw[sue_expand_ops_def, run_insts_def]
  >> rpt gen_tac >> strip_tac >>
  (* Pop bounded freshness before rw/gvs mangle it *)
  qpat_x_assum `!v k. MEM (Var v) (h::ops) /\ _ ==> _`
    (fn th => let
      val th' = CONV_RULE (DEPTH_CONV
        (REWR_CONV (CONJUNCT2 listTheory.LENGTH))) th
    in
      assume_tac (MATCH_MP fresh_cons_tail th') >>
      assume_tac (MATCH_MP fresh_cons_elem th')
    end) >>
  (* Now rewrite definitions *)
  gvs[sue_expand_ops_def] >>
  `?a2 n2. sue_expand_ops dfg inst ops (idx + 1) = (a2, n2)` by
    metis_tac[pairTheory.pair_CASES] >>
  gvs[] >>
  (* Propagate no-Label precondition for IH *)
  `!k' l'. k' < LENGTH ops /\ sue_needs_assign dfg inst (idx + 1 + k') ==>
           EL k' ops <> Label l'` by (
    rw[] >> first_x_assum (qspecl_then [`SUC k'`, `l'`] mp_tac) >>
    simp[arithmeticTheory.ADD1]) >>
  Cases_on `sue_needs_assign dfg inst idx` >> gvs[]
  >- (
    Cases_on `h` >> gvs[]
    >- (
      (* h = Lit c — ASSIGN [Lit c] always succeeds, error in tail *)
      gvs[run_insts_def, step_inst_non_invoke, step_inst_base_def,
          is_alloca_op_def, eval_operand_def, update_var_def] >>
      first_x_assum (qspecl_then
        [`dfg`, `inst`, `idx + 1`, `a2`, `n2`, `fuel`, `ctx`,
         `st with vs_vars := st.vs_vars |+ (sue_fresh_var inst.inst_id idx, c)`]
        mp_tac) >>
      impl_tac >- simp[] >> strip_tac >>
      qexists_tac `SUC k` >> simp[] >>
      Cases_on `EL k ops` >>
        gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
      rename1 `Var vn2` >>
      `MEM (Var vn2) ops` by metis_tac[MEM_EL] >>
      `vn2 <> sue_fresh_var inst.inst_id idx` by metis_tac[] >>
      gvs[])
    >- (
      (* h = Var vn *)
      rename1 `Var vn` >>
      Cases_on `LENGTH (dfg_get_uses dfg vn) = 1 /\
                sue_count_remaining (Var vn) ops = 0` >> gvs[]
      >- (
        (* Last-occurrence skip: assigns = a2 *)
        first_x_assum (qspecl_then
          [`dfg`, `inst`, `idx + 1`, `a2`, `n2`,
           `fuel`, `ctx`, `st`]
          mp_tac) >>
        impl_tac >- simp[] >> strip_tac >>
        qexists_tac `SUC k` >> simp[])
      >- (
        (* Assign prepended *)
        gvs[run_insts_def] >>
        Cases_on `step_inst fuel ctx
          <| inst_opcode := ASSIGN; inst_operands := [Var vn];
             inst_outputs := [sue_fresh_var inst.inst_id idx];
             inst_id := inst.inst_id * 1000 + idx |> st` >> gvs[]
        >- (
          rename1 `_ = OK st1` >>
          `?val. FLOOKUP st.vs_vars vn = SOME val /\
                 st1 = st with vs_vars := st.vs_vars |+
                   (sue_fresh_var inst.inst_id idx, val)` by (
            pop_assum mp_tac >> pop_assum mp_tac >>
            simp[step_inst_non_invoke, step_inst_base_def,
                 is_alloca_op_def, eval_operand_def, update_var_def,
                 lookup_var_def] >>
            Cases_on `FLOOKUP st.vs_vars vn` >> simp[]) >>
          gvs[] >>
          first_x_assum (qspecl_then
            [`dfg`, `inst`, `idx + 1`, `a2`, `n2`,
             `fuel`, `ctx`,
             `st with vs_vars := st.vs_vars |+
                (sue_fresh_var inst.inst_id idx, val)`]
            mp_tac) >>
          impl_tac >- simp[] >> strip_tac >>
          qexists_tac `SUC k` >> simp[] >>
          Cases_on `EL k ops` >>
            gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
          rename1 `Var vn2` >>
          `MEM (Var vn2) ops` by metis_tac[MEM_EL] >>
          `vn2 <> sue_fresh_var inst.inst_id idx` by metis_tac[] >>
          gvs[])
        >- (
          `eval_operand (Var vn) st = NONE` by (
            gvs[step_inst_non_invoke, step_inst_base_def, is_alloca_op_def] >>
            Cases_on `eval_operand (Var vn) st` >> gvs[]) >>
          qexists_tac `0` >> simp[])))
    >- (
      (* h = Label — contradicts no-Label precondition *)
      rename1 `Label lab` >>
      qpat_x_assum `!k l. k < SUC _ /\ _ ==> _`
        (qspecl_then [`0`, `lab`] mp_tac) >>
      simp[]))
  >- (
    (* sue_needs_assign = F: no assign prepended, assigns = a2 *)
    first_x_assum (qspecl_then
      [`dfg`, `inst`, `idx + 1`, `a2`, `n2`,
       `fuel`, `ctx`, `st`]
      mp_tac) >>
    impl_tac >- simp[] >> strip_tac >>
    qexists_tac `SUC k` >> simp[]));
in
val sue_assigns_error_implies_operand_none =
  sue_assigns_error_implies_operand_none_thm;
end;

(* step_inst errors when a non-Label operand evaluates to NONE.
   Proved per-opcode at ML level to avoid case-split timeout on the
   ~90-opcode step_inst_base/inst_wf definitions.

   Note: FALSE for 0-operand exec_read0 opcodes (CALLER, MEMTOP, etc.)
   where step_inst_base ignores operands. These are handled vacuously in
   sue_assigns_error_implies_inst_error because sue_expand_ops produces
   no assigns for 0-operand instructions. *)
local
  (* Pre-expand inst_wf and step_inst_base for each opcode *)
  val inst_wf_expanded = REWRITE_CONV [inst_wf_def] ``inst_wf inst``;
  val step_inst_base_expanded =
    REWRITE_CONV [step_inst_base_def] ``step_inst_base inst st``;

  fun inst_wf_for_opc opc = let
    val asm = ASSUME (mk_eq(``inst.inst_opcode``, opc))
  in SIMP_RULE (srw_ss()) [asm] inst_wf_expanded end;

  fun step_inst_base_for_opc opc = let
    val asm = ASSUME (mk_eq(``inst.inst_opcode``, opc))
  in SIMP_RULE (srw_ss()) [asm] step_inst_base_expanded end;

  val inst_wf_log_extract = prove(
    ``inst_wf inst /\ inst.inst_opcode = LOG ==>
      ?tc rest. inst.inst_operands = Lit tc :: rest /\
                LENGTH rest = w2n tc + 2``,
    strip_tac >> fs[inst_wf_def] >> metis_tac[]);

  (* Standard per-opcode prover for fixed-operand-count opcodes *)
  fun prove_opcode_errors opc = let
    val iw = inst_wf_for_opc opc
    val sb = step_inst_base_for_opc opc
    val goal = ``!fuel ctx inst (st:venom_state) k.
      inst_wf inst /\ inst.inst_opcode = ^opc /\
      k < LENGTH inst.inst_operands /\
      (!l. EL k inst.inst_operands <> Label l) /\
      eval_operand (EL k inst.inst_operands) st = NONE ==>
      ?e. step_inst fuel ctx inst st = Error e``
  in prove(goal,
    rpt strip_tac >>
    `eval_operands inst.inst_operands st = NONE` by
      metis_tac[eval_operand_none_implies_operands_none] >>
    simp[step_inst_non_invoke] >>
    ONCE_ASM_REWRITE_TAC [sb] >>
    FULL_SIMP_TAC (srw_ss()) [iw, exec_pure1_def, exec_pure2_def,
        exec_pure3_def, exec_read0_def, exec_read1_def, exec_write2_def,
        eval_operands_def, eval_operand_def] >>
    BasicProvers.EVERY_CASE_TAC >>
      gvs[eval_operand_def, eval_operands_def] >>
    BasicProvers.EVERY_CASE_TAC >> gvs[eval_operands_def])
  end;

  (* LOG needs special handling: variable-length operand list *)
  val sb_log = step_inst_base_for_opc ``LOG``;
  val prove_log_errors = prove(``
    !fuel ctx inst (st:venom_state) k.
      inst_wf inst /\ inst.inst_opcode = LOG /\
      k < LENGTH inst.inst_operands /\
      (!l. EL k inst.inst_operands <> Label l) /\
      eval_operand (EL k inst.inst_operands) st = NONE ==>
      ?e. step_inst fuel ctx inst st = Error e``,
    rpt strip_tac >>
    `eval_operands inst.inst_operands st = NONE` by
      metis_tac[eval_operand_none_implies_operands_none] >>
    `?tc rest. inst.inst_operands = Lit tc :: rest /\
               LENGTH rest = w2n tc + 2` by
      metis_tac[inst_wf_log_extract] >>
    gvs[step_inst_non_invoke, step_inst_base_def] >>
    Cases_on `k` >- gvs[eval_operand_def] >>
    `eval_operand (EL n rest) st = NONE` by gvs[] >>
    `eval_operands rest st = NONE` by
      (fs[eval_operands_def, eval_operand_def] >>
       Cases_on `eval_operands rest st` >> fs[]) >>
    Cases_on `eval_operand (HD rest) st` >> simp[] >>
    Cases_on `eval_operand (EL 1 rest) st` >> simp[] >>
    Cases_on `eval_operands (DROP 2 rest) st` >> simp[] >>
    `LENGTH rest >= 2` by simp[] >>
    Cases_on `rest` >> fs[eval_operands_def] >>
    Cases_on `t` >> fs[eval_operands_def]);

  (* INVOKE needs special handling: step_inst handles INVOKE directly,
     not through step_inst_base. *)
  val prove_invoke_errors = prove(``
    !fuel ctx inst (st:venom_state) k.
      inst_wf inst /\ inst.inst_opcode = INVOKE /\
      k < LENGTH inst.inst_operands /\
      (!l. EL k inst.inst_operands <> Label l) /\
      eval_operand (EL k inst.inst_operands) st = NONE ==>
      ?e. step_inst fuel ctx inst st = Error e``,
    rpt strip_tac >>
    simp[Once step_inst_def, decode_invoke_def] >>
    Cases_on `inst.inst_operands` >- fs[] >>
    rename1 `hd :: tl` >>
    reverse (Cases_on `hd`) >> simp[]
    >- ((* Label case: decode_invoke succeeds, need eval_operands tl = NONE *)
      rename1 `Label callee :: tl` >>
      Cases_on `lookup_function callee ctx.ctx_functions` >> simp[] >>
      (* k=0 contradicts no-Label; so k > 0 and EL (k-1) tl = NONE *)
      Cases_on `k` >- fs[] >>
      rename1 `SUC n` >>
      fs[] >>
      `n < LENGTH tl` by fs[] >>
      `eval_operands tl st = NONE` by
        metis_tac[eval_operand_none_implies_operands_none] >>
      simp[]));

  (* JNZ: inst_wf gives [c; Label l1; Label l2], so k must be 0 *)
  val iw_jnz = inst_wf_for_opc ``JNZ``;
  val sb_jnz = step_inst_base_for_opc ``JNZ``;
  val prove_jnz_errors = prove(``
    !fuel ctx inst (st:venom_state) k.
      inst_wf inst /\ inst.inst_opcode = JNZ /\
      k < LENGTH inst.inst_operands /\
      (!l. EL k inst.inst_operands <> Label l) /\
      eval_operand (EL k inst.inst_operands) st = NONE ==>
      ?e. step_inst fuel ctx inst st = Error e``,
    rpt strip_tac >>
    `?c l1 l2. inst.inst_operands = [c; Label l1; Label l2]` by
      fs[iw_jnz] >>
    gvs[] >>
    simp[step_inst_non_invoke] >>
    ONCE_ASM_REWRITE_TAC [sb_jnz] >> simp[] >>
    `k = 0 \/ k = 1 \/ k = 2` by simp[] >>
    gvs[eval_operand_def]);

  (* DJMP: all non-first operands are Labels, so k must be 0 *)
  val iw_djmp = inst_wf_for_opc ``DJMP``;
  val sb_djmp = step_inst_base_for_opc ``DJMP``;
  val prove_djmp_errors = prove(``
    !fuel ctx inst (st:venom_state) k.
      inst_wf inst /\ inst.inst_opcode = DJMP /\
      k < LENGTH inst.inst_operands /\
      (!l. EL k inst.inst_operands <> Label l) /\
      eval_operand (EL k inst.inst_operands) st = NONE ==>
      ?e. step_inst fuel ctx inst st = Error e``,
    rpt strip_tac >>
    `?sel label_ops. inst.inst_operands = sel :: label_ops /\
      EVERY (\op. IS_SOME (get_label op)) label_ops` by fs[iw_djmp] >>
    gvs[] >>
    `k = 0` by (
      CCONTR_TAC >> fs[] >>
      `k - 1 < LENGTH label_ops` by simp[] >>
      `IS_SOME (get_label (EL (k-1) label_ops))` by
        (fs[listTheory.EVERY_EL] >> res_tac) >>
      Cases_on `EL (k-1) label_ops` >> fs[get_label_def] >>
      Cases_on `k` >> fs[]) >>
    gvs[] >>
    simp[step_inst_non_invoke] >>
    ONCE_ASM_REWRITE_TAC [sb_djmp] >> simp[] >>
    fs[eval_operand_def]);

  (* Collect per-opcode theorems indexed by opcode constructor *)
  val all_opcodes = TypeBase.constructors_of ``:opcode``;

  fun should_skip opc =
    let val sk = rhs (concl (EVAL (mk_comb(``sue_should_skip``, opc))))
        val al = rhs (concl (EVAL (mk_comb(``is_alloca_op``, opc))))
    in not (aconv sk boolSyntax.F) orelse not (aconv al boolSyntax.F)
    end;

  (* Build (opcode, theorem) pairs. Special cases first, then standard. *)
  val special_opcodes = [
    (``INVOKE``, prove_invoke_errors),
    (``LOG``, prove_log_errors),
    (``JNZ``, prove_jnz_errors),
    (``DJMP``, prove_djmp_errors)];
  fun is_special opc = List.exists (fn (o',_) => aconv opc o') special_opcodes;

  val per_opcode_pairs =
    special_opcodes @
    List.mapPartial (fn opc =>
      if should_skip opc orelse is_special opc then NONE
      else (SOME (opc, prove_opcode_errors opc)
            handle _ => NONE)
    ) all_opcodes;

  (* Tactic: after Cases_on, find matching theorem for each subgoal *)
  fun dispatch_opcode_tac (asms, gl) = let
    (* Find which opcode is in the assumptions *)
    fun find_opc [] = NONE
      | find_opc (asm::rest) =
          (case Lib.total (fn a => let val (l,r) = dest_eq a
             in if aconv l ``inst.inst_opcode`` then SOME r else NONE end) asm
           of SOME (SOME opc) => SOME opc | _ => find_opc rest)
    val opc_opt = find_opc asms
  in case opc_opt of
       NONE => raise mk_HOL_ERR "local" "dispatch" "no opcode found"
     | SOME opc =>
         (case List.find (fn (o',_) => aconv opc o') per_opcode_pairs of
            SOME (_,thm) => metis_tac [thm] (asms, gl)
          | NONE => raise mk_HOL_ERR "local" "dispatch"
              ("no theorem for " ^ term_to_string opc))
  end;

  (* Combine: case-split on opcode, discharge trivial cases, dispatch rest *)
  val step_inst_errors_on_undef_operand_thm = prove(``
    !fuel ctx inst st k.
      inst_wf inst /\
      ~sue_should_skip inst.inst_opcode /\
      ~is_alloca_op inst.inst_opcode /\
      sue_operands_wf inst /\
      k < LENGTH inst.inst_operands /\
      (!l. EL k inst.inst_operands <> Label l) /\
      eval_operand (EL k inst.inst_operands) st = NONE ==>
      ?e. step_inst fuel ctx inst st = Error e``,
    rpt strip_tac >>
    Cases_on `inst.inst_opcode` >>
    gvs[sue_should_skip_def, is_param_opcode_def,
        is_alloca_op_def, sue_operands_wf_def] >>
    TRY dispatch_opcode_tac >>
    simp[]);

in
val step_inst_errors_on_undef_operand =
  step_inst_errors_on_undef_operand_thm;
end;

(* Main error propagation lemma *)
Theorem sue_assigns_error_implies_inst_error[local]:
  !dfg inst fuel ctx st fn bb assigns new_ops.
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ~sue_should_skip inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    sue_operands_wf inst /\
    sue_expand_ops dfg inst inst.inst_operands 0 = (assigns, new_ops) /\
    (!v k. MEM (Var v) inst.inst_operands /\
           k < LENGTH inst.inst_operands ==>
           v <> sue_fresh_var inst.inst_id k) /\
    (?e. run_insts fuel ctx assigns st = Error e) ==>
    ?e. step_inst fuel ctx inst st = Error e
Proof
  rpt strip_tac >>
  `inst_wf inst` by (gvs[fn_inst_wf_def] >> res_tac) >>
  qspecl_then [`inst.inst_operands`, `dfg`, `inst`, `0`, `assigns`,
    `new_ops`, `fuel`, `ctx`, `st`]
    mp_tac sue_assigns_error_implies_operand_none >>
  impl_tac >- (
    rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[] >>
    rw[sue_needs_assign_def] >>
    Cases_on `EL k inst.inst_operands` >> gvs[]) >>
  strip_tac >>
  irule step_inst_errors_on_undef_operand >>
  simp[] >> metis_tac[]
QED

Theorem sue_inst_sim[local]:
  !dfg inst fuel ctx st fresh fn bb.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ~sue_should_skip inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    sue_operands_wf inst /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    fresh = sue_fresh_vars_fn fn /\
    (!v k. MEM (Var v) inst.inst_operands /\
           k < LENGTH inst.inst_operands ==>
           v <> sue_fresh_var inst.inst_id k) ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (step_inst fuel ctx inst st)
      (run_insts fuel ctx (sue_expand_inst dfg inst) st)
Proof
  rpt strip_tac >>
  `inst_wf inst` by (gvs[venomWfTheory.fn_inst_wf_def] >> res_tac) >>
  (* Extract assigns and new_ops from sue_expand_inst *)
  simp[sue_expand_inst_def] >>
  `?assigns new_ops.
     sue_expand_ops dfg inst inst.inst_operands 0 = (assigns, new_ops)` by
    metis_tac[pairTheory.pair_CASES] >>
  gvs[] >>
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    metis_tac[sue_expand_ops_assigns_are_assign] >>
  `LENGTH new_ops = LENGTH inst.inst_operands` by
    metis_tac[sue_expand_ops_length] >>
  gvs[run_insts_append] >>
  (* Assigns produce OK or Error *)
  `(?st'. run_insts fuel ctx assigns st = OK st') \/
   (?e. run_insts fuel ctx assigns st = Error e)` by
    metis_tac[run_insts_assigns_ok_or_error] >>
  gvs[]
  >- (
    (* OK st': assigns succeeded — main proof chain *)
    simp[analysisSimProofsBaseTheory.run_insts_singleton] >>
    (* state_equiv fresh st st' *)
    `state_equiv (sue_fresh_vars_fn fn) st st'` by (
      qspecl_then [`assigns`, `fuel`, `ctx`, `st`, `st'`,
                    `sue_fresh_vars_fn fn`]
        mp_tac run_effect_free_state_equiv >>
      impl_tac >- (
        rpt conj_tac
        >- metis_tac[sue_assigns_are_effect_free]
        >- metis_tac[sue_expand_assigns_in_fresh]
        >- first_assum ACCEPT_TAC) >>
      simp[]) >>
    (* not PARAM, not PHI *)
    `inst.inst_opcode <> PARAM /\ inst.inst_opcode <> PHI` by
      (Cases_on `inst.inst_opcode` >> gvs[sue_should_skip_def, is_param_opcode_def]) >>
    (* bounded freshness for sue_expand_ops_eval (idx=0) *)
    `!v j. MEM (Var v) inst.inst_operands /\ 0 <= j /\
           j < 0 + LENGTH inst.inst_operands ==>
           v <> sue_fresh_var inst.inst_id j` by
      (rpt strip_tac >> CCONTR_TAC >> gvs[] >>
       first_x_assum (qspec_then `j` mp_tac) >> simp[]) >>
    (* eval agreement — new_ops in st' = original in st *)
    `!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) st' =
         eval_operand (EL i inst.inst_operands) st` by
      metis_tac[sue_expand_ops_eval] >>
    (* eval agreement — original in st' = original in st *)
    `!op. (!x. op = Var x ==>
               !j. j < LENGTH inst.inst_operands ==>
               x <> sue_fresh_var inst.inst_id j) ==>
         eval_operand op st' = eval_operand op st` by (
      rpt strip_tac >>
      qspecl_then [`inst.inst_operands`, `dfg`, `inst`, `0`,
                    `assigns`, `new_ops`, `fuel`, `ctx`, `st`, `st'`, `op`]
        mp_tac sue_assigns_preserve_eval_operand >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[]) >>
      simp[]) >>
    (* combine for eval at st' *)
    `!i. i < LENGTH inst.inst_operands ==>
         eval_operand (EL i new_ops) st' =
         eval_operand (EL i inst.inst_operands) st'` by (
      rpt strip_tac >>
      `eval_operand (EL i new_ops) st' =
       eval_operand (EL i inst.inst_operands) st` by metis_tac[] >>
      `(!x. EL i inst.inst_operands = Var x ==>
            !k. k < LENGTH inst.inst_operands ==>
            x <> sue_fresh_var inst.inst_id k)` by
        (rpt strip_tac >> CCONTR_TAC >> gvs[] >>
         first_x_assum (qspec_then `k` mp_tac) >> simp[] >>
         metis_tac[MEM_EL]) >>
      metis_tac[]) >>
    (* label preservation *)
    `!i. i < LENGTH inst.inst_operands ==>
         !lbl. EL i inst.inst_operands = Label lbl ==>
               EL i new_ops = Label lbl` by
      metis_tac[sue_expand_ops_label_preserved] >>
    (* LOG HD preservation *)
    `inst.inst_opcode = LOG ==> HD new_ops = HD inst.inst_operands` by (
      strip_tac >>
      `inst.inst_operands <> []` by (
        gvs[venomWfTheory.inst_wf_def] >>
        Cases_on `inst.inst_operands` >> gvs[]) >>
      metis_tac[sue_expand_ops_log_hd_preserved]) >>
    `inst.inst_opcode <> FMP_PARAM /\
     inst.inst_opcode <> RETPC_PARAM` by
      (conj_tac >> strip_tac >> gvs[sue_should_skip_def, is_param_opcode_def]) >>
    (* DRET structural parser preservation *)
    `inst.inst_opcode = DRET ==>
     parse_dret_shape (inst with inst_operands := new_ops) =
     parse_dret_shape inst` by
      metis_tac[sue_expand_ops_dret_parse_preserved] >>
    (* step_inst (modified) st' = step_inst inst st' *)
    `step_inst fuel ctx (inst with inst_operands := new_ops) st' =
     step_inst fuel ctx inst st'` by (
      qspecl_then [`fuel`, `ctx`, `inst`, `new_ops`, `st'`]
        mp_tac passSharedPropsTheory.step_inst_operands_equiv >>
      impl_tac >- gvs[] >>
      simp[]) >>
    (* lift_result from step_inst_preserves_R *)
    `lift_result (state_equiv (sue_fresh_vars_fn fn))
                 (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
       (step_inst fuel ctx inst st) (step_inst fuel ctx inst st')` by (
      irule execEquivParamProofsTheory.step_inst_preserves_R_proof >>
      simp[execEquivParamProofsTheory.state_equiv_execution_equiv_valid_state_rel_proof] >>
      rpt strip_tac >>
      `x NOTIN sue_fresh_vars_fn fn` by metis_tac[] >>
      gvs[stateEquivTheory.state_equiv_def,
          stateEquivTheory.execution_equiv_def]) >>
    metis_tac[]
  )
  >- (
    (* Error: original must also error, so lift_result (Error, Error) = T *)
    `!v k. MEM (Var v) inst.inst_operands /\
           k < LENGTH inst.inst_operands ==>
           v <> sue_fresh_var inst.inst_id k` by
      (rpt strip_tac >> CCONTR_TAC >> gvs[] >>
       first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
    `?e'. step_inst fuel ctx inst st = Error e'` by
      metis_tac[sue_assigns_error_implies_inst_error] >>
    gvs[lift_result_def]
  )
QED

(* ===== FLAT MAP indexing helpers ===== *)

Theorem EL_FLAT_MAP[local]:
  !f (xs : 'a list) i k.
    i < LENGTH xs /\ k < LENGTH (f (EL i xs)) ==>
    EL (SUM (MAP (LENGTH o f) (TAKE i xs)) + k) (FLAT (MAP f xs)) =
    EL k (f (EL i xs))
Proof
  Induct_on `xs` >> rw[] >>
  Cases_on `i` >> fs[]
  >- simp[rich_listTheory.EL_APPEND1]
  >- (simp[rich_listTheory.EL_APPEND2] >>
      first_x_assum (qspecl_then [`n`, `k`] mp_tac) >> simp[])
QED

Theorem FLAT_MAP_offset_bound[local]:
  !f (xs : 'a list) i.
    i < LENGTH xs ==>
    SUM (MAP (LENGTH o f) (TAKE i xs)) + LENGTH (f (EL i xs)) <=
    LENGTH (FLAT (MAP f xs))
Proof
  Induct_on `xs` >> rw[] >>
  Cases_on `i` >> fs[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem FLAT_MAP_offset_SUC[local]:
  !f (xs : 'a list) i.
    i < LENGTH xs ==>
    SUM (MAP (LENGTH o f) (TAKE (SUC i) xs)) =
    SUM (MAP (LENGTH o f) (TAKE i xs)) + LENGTH (f (EL i xs))
Proof
  Induct_on `xs` >> rw[] >>
  Cases_on `i` >> fs[]
QED

(* Helper: SUC jm offset computation — extracted to avoid context pollution (L304) *)
Triviality sue_suc_offset[local]:
  !f (xs : 'a list) i j jm assigns mod_inst.
    i < LENGTH xs /\
    j = SUM (MAP (LENGTH o f) (TAKE i xs)) /\
    jm = j + LENGTH assigns /\
    f (EL i xs) = assigns ++ [mod_inst]
  ==>
    SUC jm = SUM (MAP (LENGTH o f) (TAKE (SUC i) xs))
Proof
  rpt strip_tac >>
  `SUM (MAP (LENGTH o f) (TAKE (SUC i) xs)) =
   SUM (MAP (LENGTH o f) (TAKE i xs)) + LENGTH (f (EL i xs))`
    by (irule FLAT_MAP_offset_SUC >> simp[]) >>
  simp[]
QED

Theorem lift_result_exec_result_map[local]:
  !R_ok R_term g r1 r2.
    lift_result R_ok R_term R_term r1 r2 /\
    (!s1 s2. R_ok s1 s2 ==> R_ok (g s1) (g s2)) /\
    (!s1 s2. R_term s1 s2 ==> R_term (g s1) (g s2))
  ==> lift_result R_ok R_term R_term (exec_result_map g r1) (exec_result_map g r2)
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def, exec_result_map_def]
QED

(* lift_result_halt_wrap: local re-proof of analysisSimProofsBase triviality *)
Triviality lift_result_halt_wrap[local]:
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
  imp_res_tac execEquivParamBaseTheory.vsr_R_ok_fields >> gvs[] >>
  Cases_on `v.vs_halted` >> gvs[lift_result_def] >>
  metis_tac[execEquivParamBaseTheory.vsr_R_ok_R_term]
QED

(* invoke_lift_result_idx_bridge: local re-proof *)
Triviality invoke_lift_result_idx_bridge[local]:
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
    | x => x` by simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
  `step_inst fuel ctx inst2 (s with vs_inst_idx := n) =
    case step_inst fuel ctx inst2 s of
      OK s'' => OK (s'' with vs_inst_idx := n)
    | x => x` by simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
  ntac 2 (pop_assum SUBST1_TAC) >>
  Cases_on `step_inst fuel ctx inst1 s` >>
  Cases_on `step_inst fuel ctx inst2 s` >>
  gvs[lift_result_def] >>
  metis_tac[analysisSimProofsBaseTheory.R_ok_idx_change]
QED

(* Per-instruction simulation at arbitrary state *)
Triviality sue_inst_sim_at[local]:
  !dfg inst fuel ctx st fresh fn bb.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    fn_inst_wf fn /\
    ~is_alloca_op inst.inst_opcode /\
    sue_operands_wf inst /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    fresh = sue_fresh_vars_fn fn ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (step_inst fuel ctx inst st)
      (run_insts fuel ctx (sue_expand_inst dfg inst) st)
Proof
  rpt strip_tac >>
  Cases_on `sue_should_skip inst.inst_opcode`
  >- (
    simp[sue_expand_inst_def, analysisSimProofsBaseTheory.run_insts_singleton] >>
    irule lift_result_refl_proof >>
    metis_tac[execEquivParamBaseTheory.vsr_R_ok_refl,
              execEquivParamBaseTheory.vsr_R_term_refl,
              execEquivParamProofsTheory.state_equiv_execution_equiv_valid_state_rel_proof])
  >> (
    qspecl_then [`dfg`, `inst`, `fuel`, `ctx`, `st`, `fresh`, `fn`, `bb`]
      mp_tac sue_inst_sim >>
    impl_tac >- (
      simp[] >>
      rpt strip_tac >> gvs[] >>
      metis_tac[sue_fresh_var_in_fresh_set]) >>
    simp[])
QED

(* ===== Per-block simulation ===== *)

(* exec_block_skip_prefix works when run_insts was called at idx=0 *)
Triviality exec_block_skip_prefix_idx0[local]:
  !prefix fuel ctx bb s j s'.
    j + LENGTH prefix <= LENGTH bb.bb_instructions /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) prefix /\
    (!k. k < LENGTH prefix ==> EL (j + k) bb.bb_instructions = EL k prefix) /\
    run_insts fuel ctx prefix (s with vs_inst_idx := 0) = OK s' /\
    s'.vs_inst_idx = 0 ==>
    exec_block fuel ctx bb (s with vs_inst_idx := j) =
    exec_block fuel ctx bb (s' with vs_inst_idx := j + LENGTH prefix)
Proof
  rpt strip_tac >>
  qspecl_then [`prefix`, `fuel`, `ctx`, `bb`, `s`,  `j`,
               `s' with vs_inst_idx := s.vs_inst_idx`]
    mp_tac analysisSimProofsBaseTheory.exec_block_skip_prefix >>
  simp[venom_state_component_equality] >>
  disch_then irule >>
  (* Derive run_insts at the ambient state *)
  qspecl_then [`fuel`, `ctx`, `prefix`, `s`, `0`]
    mp_tac analysisSimProofsBaseTheory.run_insts_idx_indep >>
  simp[] >> strip_tac >>
  Cases_on `run_insts fuel ctx prefix s` >>
  gvs[exec_result_map_def, venom_state_component_equality] >>
  metis_tac[analysisSimProofsBaseTheory.run_insts_preserves_idx]
QED



(* Helper: when assigns error, the expanded block also errors *)
Triviality sue_assigns_error_lift[local]:
  !fuel ctx inst s assigns expanded_insts bb i j e fn.
    run_insts fuel ctx assigns (s with vs_inst_idx := 0) = Error e /\
    lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
               (step_inst fuel ctx inst (s with vs_inst_idx := 0))
               (Error e) /\
    EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE)
      assigns /\
    j + LENGTH assigns <= LENGTH expanded_insts /\
    (!k. k < LENGTH assigns ==>
       EL (j + k) expanded_insts = EL k assigns) /\
    valid_state_rel (state_equiv (sue_fresh_vars_fn fn))
                    (execution_equiv (sue_fresh_vars_fn fn)) ==>
    lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
      (case step_inst fuel ctx inst s of
         OK s'' =>
           if is_terminator inst.inst_opcode then
             if s''.vs_halted then Halt s'' else OK s''
           else exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
       | Halt s'' => Halt s''
       | Abort a s'' => Abort a s''
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (exec_block fuel ctx
         (bb with bb_instructions := expanded_insts)
         (s with vs_inst_idx := j))
Proof
  rpt strip_tac >>
  (* step_inst inst (s,0) must also error *)
  `?e'. step_inst fuel ctx inst (s with vs_inst_idx := 0) = Error e'` by (
    qpat_x_assum `lift_result _ _ _ _ (Error _)` mp_tac >>
    Cases_on `step_inst fuel ctx inst (s with vs_inst_idx := 0)` >>
    simp[lift_result_def]) >>
  `step_inst fuel ctx inst s = Error e'` by
    metis_tac[analysisSimProofsBaseTheory.step_inst_error_idx_recover] >>
  simp[] >>
  `lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
               (Error e') (Error e)` by gvs[lift_result_def] >>
  (* Expanded block errors via run_insts_lift_exec_block *)
  `lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
               (Error e)
               (exec_block fuel ctx
                  (bb with bb_instructions := expanded_insts)
                  (s with vs_inst_idx := j))` by (
    `lift_result (state_equiv (sue_fresh_vars_fn fn))
                 (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
                 (run_insts fuel ctx assigns (s with vs_inst_idx := 0))
                 (exec_block fuel ctx
                    (bb with bb_instructions := expanded_insts)
                    (s with vs_inst_idx := j))` suffices_by simp[] >>
    qspecl_then [`state_equiv (sue_fresh_vars_fn fn)`,
                 `execution_equiv (sue_fresh_vars_fn fn)`,
                 `assigns`]
      mp_tac analysisSimProofsBaseTheory.run_insts_lift_exec_block >>
    (impl_tac >- simp[]) >>
    disch_then (qspecl_then [`fuel`, `ctx`,
      `bb with bb_instructions := expanded_insts`,
      `s with vs_inst_idx := 0`, `j`] mp_tac) >>
    simp[] >> metis_tac[]) >>
  (* Chain via transitivity *)
  irule (REWRITE_RULE [AND_IMP_INTRO]
           passSimulationProofsTheory.lift_result_trans_proof) >>
  rpt conj_tac
  >- metis_tac[stateEquivProofsTheory.state_equiv_trans,
              stateEquivProofsTheory.execution_equiv_trans]
  >- metis_tac[stateEquivProofsTheory.state_equiv_trans,
              stateEquivProofsTheory.execution_equiv_trans]
  >- metis_tac[stateEquivProofsTheory.state_equiv_trans,
              stateEquivProofsTheory.execution_equiv_trans]
  >- (qexists_tac `Error e` >> simp[])
QED

(* lift_result through case with OK continuation and optional non-OK state transform *)
Triviality lift_result_case_map[local]:
  !R_ok R_term r1 r2 f g h1 h2.
    valid_state_rel R_ok R_term /\
    lift_result R_ok R_term R_term r1 r2 /\
    (!s1 s2. R_ok s1 s2 ==> lift_result R_ok R_term R_term (f s1) (g s2)) /\
    (!s1 s2. R_term s1 s2 ==> R_term (h1 s1) (h2 s2))
  ==>
    lift_result R_ok R_term R_term
      (case r1 of
         OK s => f s
       | Halt s => Halt (h1 s)
       | Abort a s => Abort a (h1 s)
       | IntRet rv ss => IntRet rv (h1 ss)
       | Error e => Error e)
      (case r2 of
         OK s => g s
       | Halt s => Halt (h2 s)
       | Abort a s => Abort a (h2 s)
       | IntRet rv ss => IntRet rv (h2 ss)
       | Error e => Error e)
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  gvs[lift_result_def]
QED

(* Bridge step_inst through idx changes + case dispatch in one shot.
   Handles both INVOKE and non-INVOKE internally. *)
Triviality sue_step_case_lift[local]:
  !R_ok R_term fuel ctx inst1 inst2 s1 s2 n1 n2 f g.
    valid_state_rel R_ok R_term /\
    lift_result R_ok R_term R_term (step_inst fuel ctx inst1 s1)
                            (step_inst fuel ctx inst2 s2) /\
    ~is_terminator inst1.inst_opcode /\ ~is_terminator inst2.inst_opcode /\
    inst2.inst_opcode = inst1.inst_opcode /\
    (!v1 v2. R_ok v1 v2 ==>
       lift_result R_ok R_term R_term (f (v1 with vs_inst_idx := n1))
                               (g (v2 with vs_inst_idx := n2))) /\
    (!v1 v2 m1 m2. R_term v1 v2 ==>
       R_term (v1 with vs_inst_idx := m1) (v2 with vs_inst_idx := m2))
  ==>
    lift_result R_ok R_term R_term
      (case step_inst fuel ctx inst1 (s1 with vs_inst_idx := n1) of
         OK s'' => f s'' | Halt s' => Halt s' | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss | Error e => Error e)
      (case step_inst fuel ctx inst2 (s2 with vs_inst_idx := n2) of
         OK s'' => g s'' | Halt s' => Halt s' | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss | Error e => Error e)
Proof
  rpt strip_tac >>
  Cases_on `inst1.inst_opcode = INVOKE`
  >- (
    `step_inst fuel ctx inst1 (s1 with vs_inst_idx := n1) =
     case step_inst fuel ctx inst1 s1 of
       OK v => OK (v with vs_inst_idx := n1) | x => x`
      by simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
    `inst2.inst_opcode = INVOKE` by fs[] >>
    `step_inst fuel ctx inst2 (s2 with vs_inst_idx := n2) =
     case step_inst fuel ctx inst2 s2 of
       OK v => OK (v with vs_inst_idx := n2) | x => x`
      by simp[analysisSimProofsBaseTheory.invoke_step_inst_idx_OK_only] >>
    ASM_REWRITE_TAC [] >>
    Cases_on `step_inst fuel ctx inst1 s1` >>
    Cases_on `step_inst fuel ctx inst2 s2` >>
    gvs[lift_result_def]
  ) >>
  `step_inst fuel ctx inst1 (s1 with vs_inst_idx := n1) =
   exec_result_map (\s'. s' with vs_inst_idx := n1)
     (step_inst fuel ctx inst1 s1)`
    by (ASM_SIMP_TAC std_ss
          [analysisSimProofsBaseTheory.step_inst_idx_indep]) >>
  `inst2.inst_opcode <> INVOKE` by fs[] >>
  `step_inst fuel ctx inst2 (s2 with vs_inst_idx := n2) =
   exec_result_map (\s'. s' with vs_inst_idx := n2)
     (step_inst fuel ctx inst2 s2)`
    by (ASM_SIMP_TAC std_ss
          [analysisSimProofsBaseTheory.step_inst_idx_indep]) >>
  ASM_REWRITE_TAC [] >>
  Cases_on `step_inst fuel ctx inst1 s1` >>
  Cases_on `step_inst fuel ctx inst2 s2` >>
  gvs[lift_result_def, exec_result_map_def]
QED

(* Reusable tactic patterns for sue_block_sim_induct *)

(* Prove state_equiv/execution_equiv transitivity conjuncts *)
val se_trans_tac =
  rpt (conj_tac >- metis_tac[stateEquivProofsTheory.state_equiv_trans,
                             stateEquivProofsTheory.execution_equiv_trans]);

(* Specialized exec_block_preserves_R_block for state_equiv/execution_equiv
   with idx change: given state_equiv s1 s2 and freshness, proves
   lift_result for exec_block at (s1 with n) and (s2 with n). *)
Triviality sue_rbp_state_equiv[local]:
  !fresh fuel ctx bb s1 s2 n.
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    state_equiv fresh s1 s2 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb (s1 with vs_inst_idx := n))
      (exec_block fuel ctx bb (s2 with vs_inst_idx := n))
Proof
  rpt strip_tac >>
  irule analysisSimProofsBaseTheory.exec_block_preserves_R_block >>
  rpt conj_tac >| [
    (* lookup_var preservation *)
    rpt strip_tac >>
    first_x_assum (qspecl_then [`inst`, `x`] mp_tac) >>
    simp[] >> strip_tac >>
    fs[stateEquivTheory.state_equiv_def, stateEquivTheory.execution_equiv_def],
    (* state_equiv trans *)
    metis_tac[stateEquivProofsTheory.state_equiv_trans],
    (* execution_equiv trans *)
    metis_tac[stateEquivProofsTheory.execution_equiv_trans],
    (* R_ok idx change *)
    irule analysisSimProofsBaseTheory.R_ok_idx_change >>
    metis_tac[execEquivParamProofsTheory.state_equiv_execution_equiv_valid_state_rel_proof],
    (* valid_state_rel *)
    metis_tac[execEquivParamProofsTheory.state_equiv_execution_equiv_valid_state_rel_proof]
  ]
QED

(* Non-terminator case of sue_block_sim_induct, extracted for navigability *)
Triviality sue_nonterm_case[local]:
  !fuel ctx bb fn exp i j jm assigns mod_inst inst s sa dfg.
    valid_state_rel (state_equiv (sue_fresh_vars_fn fn))
                    (execution_equiv (sue_fresh_vars_fn fn)) /\
    MEM bb fn.fn_blocks /\ fn_inst_wf fn /\
    (!inst' x. MEM inst' bb.bb_instructions /\
               MEM (Var x) inst'.inst_operands ==>
               x NOTIN sue_fresh_vars_fn fn) /\
    (!inst'. MEM inst' bb.bb_instructions ==>
             ~is_alloca_op inst'.inst_opcode /\ sue_operands_wf inst') /\
    Abbrev (exp = sue_expand_inst dfg) /\
    Abbrev (i = s.vs_inst_idx) /\ i < LENGTH bb.bb_instructions /\
    Abbrev (inst = EL i bb.bb_instructions) /\
    MEM inst bb.bb_instructions /\ inst_wf inst /\
    Abbrev (j = SUM (MAP (LENGTH o exp) (TAKE i bb.bb_instructions))) /\
    Abbrev (jm = j + LENGTH assigns) /\
    exp inst = assigns ++ [mod_inst] /\
    mod_inst.inst_opcode = inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    EVERY (\a. a.inst_opcode = ASSIGN) assigns /\
    EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE) assigns /\
    sa.vs_inst_idx = 0 /\
    run_insts fuel ctx assigns (s with vs_inst_idx := 0) = OK sa /\
    lift_result (state_equiv (sue_fresh_vars_fn fn))
                (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
      (step_inst fuel ctx inst (s with vs_inst_idx := 0))
      (step_inst fuel ctx mod_inst sa) /\
    jm <= LENGTH (FLAT (MAP exp bb.bb_instructions)) /\
    EL jm (FLAT (MAP exp bb.bb_instructions)) = mod_inst /\
    j + LENGTH assigns + 1 <= LENGTH (FLAT (MAP exp bb.bb_instructions)) /\
    (!m. m < LENGTH bb.bb_instructions - i ==>
      !fuel ctx s. m = LENGTH bb.bb_instructions - s.vs_inst_idx /\
        s.vs_inst_idx <= LENGTH bb.bb_instructions ==>
        lift_result (state_equiv (sue_fresh_vars_fn fn))
          (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
          (exec_block fuel ctx bb s)
          (exec_block fuel ctx
             (bb with bb_instructions := FLAT (MAP exp bb.bb_instructions))
             (s with vs_inst_idx :=
                SUM (MAP (LENGTH o exp) (TAKE s.vs_inst_idx bb.bb_instructions)))))
  ==>
    lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
      (case step_inst fuel ctx inst s of
         OK s'' => exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet rv ss => IntRet rv ss
       | Error e => Error e)
      (exec_block fuel ctx
         (bb with bb_instructions := FLAT (MAP exp bb.bb_instructions))
         (sa with vs_inst_idx := jm))
Proof
  rpt strip_tac >>
  `jm < LENGTH (FLAT (MAP exp bb.bb_instructions))` by simp[Abbr `jm`] >>
  `~is_terminator mod_inst.inst_opcode` by metis_tac[] >>
  (* Unfold RHS exec_block one step *)
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  ASM_REWRITE_TAC [] >> simp[] >>
  (* Apply sue_step_case_lift via mp_tac + match *)
  qspecl_then [`state_equiv (sue_fresh_vars_fn fn)`,
               `execution_equiv (sue_fresh_vars_fn fn)`,
               `fuel`, `ctx`, `inst`, `mod_inst`,
               `s with vs_inst_idx := 0`, `sa`, `i`, `jm`,
               `\s''. exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)`,
               `\s''. exec_block fuel ctx
                  (bb with bb_instructions := FLAT (MAP exp bb.bb_instructions))
                  (s'' with vs_inst_idx := SUC jm)`]
    mp_tac sue_step_case_lift >>
  `(s with vs_inst_idx := 0) with vs_inst_idx := i = s` by
    simp[Abbr `i`, venom_state_component_equality] >>
  ASM_REWRITE_TAC [] >> pop_assum kall_tac >>
  simp[] >> strip_tac >>
  first_x_assum irule >>
  conj_tac
  >- (
    (* R_term idx change — first conjunct *)
    rpt strip_tac >>
    fs[execEquivParamDefsTheory.valid_state_rel_def] >>
    qpat_x_assum `!s1 s2. execution_equiv (sue_fresh_vars_fn fn) s1 s2 ==> _`
      (fn fields => mp_tac (Q.SPECL [`v1`, `v2`] fields)) >>
    (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
    first_x_assum (qspecl_then [`v1`, `v2`,
        `v1 with vs_inst_idx := m1`, `v2 with vs_inst_idx := m2`] mp_tac) >>
    disch_then match_mp_tac >>
    PURE_REWRITE_TAC (CONJUNCTS venomStateTheory.venom_state_accfupds @
      [combinTheory.K_THM]) >>
    rpt conj_tac >> TRY (FIRST_ASSUM ACCEPT_TAC) >> ASM_REWRITE_TAC[])
  >>
  (* OK/OK continuation — second conjunct *)
  rpt strip_tac >>
  irule passSimulationProofsTheory.lift_result_trans_proof >>
  se_trans_tac >>
  qexists_tac `exec_block fuel ctx bb (v2 with vs_inst_idx := SUC i)` >>
  `SUC jm = SUM (MAP (LENGTH o exp)
               (TAKE (SUC i) bb.bb_instructions))` by (
    `SUM (MAP (LENGTH o exp) (TAKE (SUC i) bb.bb_instructions)) =
     SUM (MAP (LENGTH o exp) (TAKE i bb.bb_instructions)) +
     LENGTH (exp (EL i bb.bb_instructions))` by
      (irule FLAT_MAP_offset_SUC >> simp[]) >>
    simp[Abbr `jm`, Abbr `j`, Abbr `inst`]) >>
  conj_tac
  >- (irule sue_rbp_state_equiv >> metis_tac[])
  >- (
    (* IH: same state, different blocks *)
    first_x_assum (qspec_then `LENGTH bb.bb_instructions - SUC i` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qspecl_then [`fuel`, `ctx`,
                             `v2 with vs_inst_idx := SUC i`] mp_tac) >>
    simp[])
QED

Triviality sue_block_sim_induct[local]:
  !bb dfg fresh fn.
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    (!inst. MEM inst bb.bb_instructions ==>
            ~is_alloca_op inst.inst_opcode /\
            sue_operands_wf inst) /\
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    fresh = sue_fresh_vars_fn fn ==>
    !n fuel ctx s.
      n = LENGTH bb.bb_instructions - s.vs_inst_idx /\
      s.vs_inst_idx <= LENGTH bb.bb_instructions ==>
      lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
        (exec_block fuel ctx bb s)
        (exec_block fuel ctx
           (bb with bb_instructions :=
              FLAT (MAP (sue_expand_inst dfg) bb.bb_instructions))
           (s with vs_inst_idx :=
              SUM (MAP (LENGTH o (sue_expand_inst dfg))
                       (TAKE s.vs_inst_idx bb.bb_instructions))))
Proof
  rpt gen_tac >> strip_tac >>
  completeInduct_on `n` >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `exp = sue_expand_inst dfg` >>
  qabbrev_tac `i = s.vs_inst_idx` >>
  qabbrev_tac `j = SUM (MAP (LENGTH o exp)
                    (TAKE i bb.bb_instructions))` >>
  (* Establish valid_state_rel, transitivity once for reuse *)
  `valid_state_rel (state_equiv fresh) (execution_equiv fresh)` by
    metis_tac[execEquivParamProofsTheory.state_equiv_execution_equiv_valid_state_rel_proof] >>
  Cases_on `i >= LENGTH bb.bb_instructions`
  >- (
    (* Base: i >= LENGTH, both exec_block Halt *)
    `i = LENGTH bb.bb_instructions` by fs[] >>
    `j = SUM (MAP (LENGTH o exp) (TAKE i bb.bb_instructions))` by simp[Abbr `j`] >>
    pop_assum SUBST1_TAC >>
    `i = s.vs_inst_idx` by simp[Abbr `i`] >>
    pop_assum (fn th => REWRITE_TAC [th]) >>
    ONCE_REWRITE_TAC[exec_block_def] >>
    simp[get_instruction_def, rich_listTheory.LENGTH_FLAT, MAP_MAP_o,
         lift_result_def]
  ) >>
  (* Inductive step: i < LENGTH *)
  `i < LENGTH bb.bb_instructions` by fs[] >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  `MEM inst bb.bb_instructions` by metis_tac[MEM_EL] >>
  `inst_wf inst` by (fs[venomWfTheory.fn_inst_wf_def] >> res_tac >> fs[EVERY_EL]) >>
  `~is_alloca_op inst.inst_opcode` by metis_tac[] >>
  `sue_operands_wf inst` by metis_tac[] >>
  (* EL into FLAT for expanded block *)
  `!k. k < LENGTH (exp inst) ==>
     EL (j + k) (FLAT (MAP exp bb.bb_instructions)) =
     EL k (exp inst)` by (
    rpt strip_tac >>
    `j = SUM (MAP (LENGTH o exp) (TAKE i bb.bb_instructions))` by simp[Abbr `j`] >>
    pop_assum SUBST1_TAC >>
    `inst = EL i bb.bb_instructions` by simp[Abbr `inst`] >>
    pop_assum SUBST1_TAC >>
    irule EL_FLAT_MAP >> simp[]) >>
  `j + LENGTH (exp inst) <=
   LENGTH (FLAT (MAP exp bb.bb_instructions))` by (
    `j = SUM (MAP (LENGTH o exp) (TAKE i bb.bb_instructions))` by simp[Abbr `j`] >>
    pop_assum SUBST1_TAC >>
    `inst = EL i bb.bb_instructions` by simp[Abbr `inst`] >>
    pop_assum SUBST1_TAC >>
    irule FLAT_MAP_offset_bound >> simp[]) >>
  (* Unroll LHS exec_block *)
  `exec_block fuel ctx bb s =
    case step_inst fuel ctx inst s of
      OK s'' =>
        if is_terminator inst.inst_opcode then
          if s''.vs_halted then Halt s'' else OK s''
        else exec_block fuel ctx bb (s'' with vs_inst_idx := SUC i)
    | Halt s'' => Halt s''
    | Abort a s'' => Abort a s''
    | IntRet rv ss => IntRet rv ss
    | Error e => Error e` by (
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def, Abbr `inst`, Abbr `i`]) >>
  pop_assum SUBST1_TAC >>
  (* Per-instruction simulation at idx=0 *)
  `lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
     (step_inst fuel ctx inst (s with vs_inst_idx := 0))
     (run_insts fuel ctx (sue_expand_inst dfg inst) (s with vs_inst_idx := 0))` by (
    qspecl_then [`dfg`, `inst`, `fuel`, `ctx`,
                 `s with vs_inst_idx := 0`, `fresh`, `fn`, `bb`]
      mp_tac sue_inst_sim_at >>
    impl_tac >- (simp[] >> metis_tac[]) >>
    simp[]) >>
  (* Decompose exp inst = assigns ++ [modified] *)
  `?assigns mod_inst.
     sue_expand_inst dfg inst = assigns ++ [mod_inst] /\
     mod_inst.inst_opcode = inst.inst_opcode /\
     EVERY (\a. a.inst_opcode = ASSIGN) assigns` by (
    simp[sue_expand_inst_def] >>
    COND_CASES_TAC >> simp[] >>
    pairarg_tac >> simp[] >>
    metis_tac[sue_expand_ops_assigns_are_assign]) >>
  `exp inst = assigns ++ [mod_inst]` by simp[Abbr `exp`] >>
  `EVERY (\i'. ~is_terminator i'.inst_opcode /\ i'.inst_opcode <> INVOKE) assigns` by (
    irule (REWRITE_RULE [AND_IMP_INTRO] EVERY_MONOTONIC) >>
    qexists_tac `\a. a.inst_opcode = ASSIGN` >>
    simp[is_terminator_def]) >>
  `LENGTH (exp inst) = LENGTH assigns + 1` by simp[] >>
  `!k. k < LENGTH assigns ==>
     EL (j + k) (FLAT (MAP exp bb.bb_instructions)) =
     EL k assigns` by (
    rpt strip_tac >>
    `k < LENGTH (exp inst)` by simp[] >>
    `EL k assigns = EL k (assigns ++ [mod_inst])` by
      simp[rich_listTheory.EL_APPEND1] >>
    metis_tac[]) >>
  `run_insts fuel ctx (exp inst) (s with vs_inst_idx := 0) =
   case run_insts fuel ctx assigns (s with vs_inst_idx := 0) of
     OK sa => step_inst fuel ctx mod_inst sa
   | Halt v' => Halt v'
   | Abort a' v' => Abort a' v'
   | IntRet rv ss => IntRet rv ss
   | Error e => Error e` by
    simp[run_insts_append, analysisSimProofsBaseTheory.run_insts_singleton] >>
  `(?sa. run_insts fuel ctx assigns (s with vs_inst_idx := 0) = OK sa) \/
   (?e. run_insts fuel ctx assigns (s with vs_inst_idx := 0) = Error e)` by
    metis_tac[run_insts_assigns_ok_or_error] >>
  (* Establish the EL claim BEFORE gvs[] to avoid assumption corruption *)
  `EL (j + LENGTH assigns)
     (FLAT (MAP exp bb.bb_instructions)) = mod_inst` by (
    qpat_x_assum `!k. k < LENGTH (exp inst) ==> _` (qspec_then `LENGTH assigns` mp_tac) >>
    simp[rich_listTheory.EL_APPEND2]) >>
  (* Protect assumptions from gvs[] rewriting:
     - ∀k assigns-indexed, ∀k FLAT-indexed (prevent cross-rewriting)
     - EL claim (prevent mod_inst substitution) *)
  qpat_x_assum `EL _ (FLAT _) = mod_inst` (fn el_asm =>
   qpat_x_assum `!k. k < LENGTH assigns ==> _` (fn assigns_asm =>
    qpat_x_assum `!k. k < LENGTH (exp inst) ==> _` (fn flat_asm =>
     qpat_x_assum `exp inst = _` (fn exp_asm =>
      assume_tac exp_asm >>
      gvs[] >>
      MAP_EVERY assume_tac [exp_asm, flat_asm, assigns_asm, el_asm]))))
  >- (
    (* === Assigns OK === *)
    rename1 `run_insts fuel ctx assigns (s with vs_inst_idx := 0) = OK sa` >>
    `sa.vs_inst_idx = 0` by (
      qspecl_then [`fuel`, `ctx`, `assigns`, `s with vs_inst_idx := 0`, `sa`]
        mp_tac analysisSimProofsBaseTheory.run_insts_preserves_idx >>
      simp[]) >>
    `j + LENGTH assigns <= LENGTH (FLAT (MAP exp bb.bb_instructions))` by
      simp[] >>
    `exec_block fuel ctx
       (bb with bb_instructions := FLAT (MAP exp bb.bb_instructions))
       (s with vs_inst_idx := j) =
     exec_block fuel ctx
       (bb with bb_instructions := FLAT (MAP exp bb.bb_instructions))
       (sa with vs_inst_idx := j + LENGTH assigns)` by (
      irule exec_block_skip_prefix_idx0 >> simp[]) >>
    pop_assum SUBST1_TAC >>
    qabbrev_tac `jm = j + LENGTH assigns` >>
    Cases_on `is_terminator inst.inst_opcode`
    >- (
      (* === Terminator case === *)
      `jm < LENGTH (FLAT (MAP exp bb.bb_instructions))` by simp[Abbr `jm`] >>
      ASM_REWRITE_TAC [] >> simp[] >>
      CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      simp[get_instruction_def] >>
      `is_terminator mod_inst.inst_opcode` by simp[] >>
      ASM_REWRITE_TAC [] >> simp[] >>
      irule passSimulationProofsTheory.lift_result_trans_proof >>
      se_trans_tac >>
      qexists_tac
        `case step_inst fuel ctx mod_inst sa of
           OK s'' => if s''.vs_halted then Halt s'' else OK s''
         | Halt s' => Halt s'
         | Abort a s' => Abort a s'
         | IntRet rv ss => IntRet rv ss
         | Error e => Error e` >>
      conj_tac
      >- (
        (* First conjunct: LHS → halt-wrapped step_inst mod_inst sa *)
        irule passSimulationProofsTheory.lift_result_trans_proof >>
        se_trans_tac >>
        qexists_tac
          `case step_inst fuel ctx inst (s with vs_inst_idx := 0) of
             OK s'' => if s''.vs_halted then Halt s'' else OK s''
           | Halt s' => Halt s'
           | Abort a s' => Abort a s'
           | IntRet rv ss => IntRet rv ss
           | Error e => Error e` >>
        conj_tac
        >- (
          (* Sub-case A: idx change via terminator_exec_block_step_lift *)
          qspecl_then [`state_equiv (sue_fresh_vars_fn fn)`,
                       `execution_equiv (sue_fresh_vars_fn fn)`]
            mp_tac analysisSimProofsBaseTheory.terminator_exec_block_step_lift >>
          (impl_tac >- simp[]) >>
          disch_then (qspecl_then [`fuel`, `ctx`, `inst`, `s`, `0`] mp_tac) >>
          simp[]) >>
        (* Sub-case B: sue_inst_sim via lift_result_halt_wrap *)
        irule lift_result_halt_wrap >> simp[]) >>
      (* Second conjunct: halt-wrapped step_inst mod_inst sa → exec_block *)
      qspecl_then [`state_equiv (sue_fresh_vars_fn fn)`,
                   `execution_equiv (sue_fresh_vars_fn fn)`]
        mp_tac analysisSimProofsBaseTheory.terminator_exec_block_step_lift >>
      (impl_tac >- simp[]) >>
      disch_then (qspecl_then [`fuel`, `ctx`, `mod_inst`, `sa`, `jm`] mp_tac) >>
      simp[]) >>
    (* === Non-terminator case — delegated to sue_nonterm_case === *)
    ASM_REWRITE_TAC [] >> simp[] >>
    irule sue_nonterm_case >>
    rpt conj_tac >>
    TRY (simp[Abbr `jm`] >> NO_TAC) >>
    TRY (qexists_tac `dfg` >> first_assum ACCEPT_TAC) >>
    first_assum ACCEPT_TAC )
  >- (
    (* === Assigns Error === *)
    irule sue_assigns_error_lift >>
    conj_tac >- simp[] >>
    qexistsl_tac [`assigns`, `e`] >>
    simp[] >>
    rpt strip_tac >>
    `k < LENGTH (exp inst)` by simp[] >>
    `EL k assigns = EL k (assigns ++ [mod_inst])` by
      simp[rich_listTheory.EL_APPEND1] >>
    metis_tac[])
QED

Theorem sue_block_sim[local]:
  !fuel ctx bb st dfg fresh fn.
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    (!inst. MEM inst bb.bb_instructions ==>
            ~is_alloca_op inst.inst_opcode /\
            sue_operands_wf inst) /\
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    fresh = sue_fresh_vars_fn fn /\
    st.vs_inst_idx = 0 ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb st)
      (exec_block fuel ctx (sue_expand_block dfg bb) st)
Proof
  rpt strip_tac >>
  simp[sue_expand_block_def] >>
  qspecl_then [`bb`, `dfg`, `fresh`, `fn`] mp_tac sue_block_sim_induct >>
  (impl_tac >- (rpt conj_tac >> metis_tac[])) >>
  disch_then (qspecl_then [`LENGTH bb.bb_instructions`, `fuel`, `ctx`, `st`] mp_tac) >>
  `st with vs_inst_idx := 0 = st` by simp[venom_state_component_equality] >>
  simp[]
QED

(* ===== run_block bridge: SUE preserves the PHI prefix exactly ===== *)

Triviality sue_expand_inst_nonphi_prefix_append[local]:
  !dfg inst rest.
    inst.inst_opcode <> PHI ==>
    phi_prefix_length (sue_expand_inst dfg inst ++ rest) = 0
Proof
  rpt strip_tac >>
  simp[sue_expand_inst_def] >>
  Cases_on `sue_should_skip inst.inst_opcode` >>
  gvs[phi_prefix_length_def, sue_should_skip_def, is_param_opcode_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `assigns` >> gvs[phi_prefix_length_def]
  >- (drule sue_expand_ops_assigns_are_assign >> simp[phi_prefix_length_def]) >>
  Cases_on `inst.inst_opcode` >> gvs[sue_should_skip_def, is_param_opcode_def, phi_prefix_length_def]
QED

Triviality sue_expand_inst_phi[local]:
  !dfg inst.
    inst.inst_opcode = PHI ==> sue_expand_inst dfg inst = [inst]
Proof
  rw[sue_expand_inst_def, sue_should_skip_def, is_param_opcode_def]
QED

Triviality sue_expand_inst_phi_prefix_append[local]:
  !dfg inst rest.
    inst.inst_opcode = PHI ==>
    phi_prefix_length (sue_expand_inst dfg inst ++ rest) =
    SUC (phi_prefix_length rest)
Proof
  rw[sue_expand_inst_phi, phi_prefix_length_def]
QED

Triviality sue_expand_inst_prefix_length_append[local]:
  !dfg inst rest.
    phi_prefix_length (sue_expand_inst dfg inst ++ rest) =
    if inst.inst_opcode = PHI then SUC (phi_prefix_length rest) else 0
Proof
  rpt strip_tac >>
  simp[sue_expand_inst_def] >>
  Cases_on `inst.inst_opcode` >> gvs[sue_should_skip_def, is_param_opcode_def, phi_prefix_length_def] >>
  pairarg_tac >> gvs[] >>
  Cases_on `assigns` >> gvs[phi_prefix_length_def] >>
  TRY (drule sue_expand_ops_assigns_are_assign >> simp[phi_prefix_length_def])
QED

Triviality sue_expand_phi_prefix_length[local]:
  !dfg insts.
    phi_prefix_length (FLAT (MAP (sue_expand_inst dfg) insts)) =
    phi_prefix_length insts
Proof
  gen_tac >> Induct >> simp[phi_prefix_length_def, sue_expand_inst_prefix_length_append]
QED

Triviality sue_expand_phi_prefix_el[local]:
  !dfg insts i.
    i < phi_prefix_length insts ==>
    EL i (FLAT (MAP (sue_expand_inst dfg) insts)) = EL i insts
Proof
  gen_tac >> Induct >> simp[phi_prefix_length_def] >>
  rpt strip_tac >>
  Cases_on `h.inst_opcode` >>
  gvs[phi_prefix_length_def, sue_expand_inst_phi] >>
  Cases_on `i` >> gvs[]
QED

Triviality sue_expand_phi_prefix_sum[local]:
  !dfg insts i.
    i <= phi_prefix_length insts ==>
    SUM (MAP (LENGTH o sue_expand_inst dfg) (TAKE i insts)) = i
Proof
  gen_tac >> Induct >> simp[phi_prefix_length_def] >>
  rpt gen_tac >> Cases_on `i` >> simp[phi_prefix_length_def] >>
  rpt strip_tac >>
  `h.inst_opcode = PHI` by (CCONTR_TAC >> gvs[phi_prefix_length_def]) >>
  `n <= phi_prefix_length insts` by gvs[phi_prefix_length_def] >>
  `SUM (MAP (LENGTH o sue_expand_inst dfg) (TAKE n insts)) = n` by metis_tac[] >>
  gvs[sue_expand_inst_phi]
QED

Triviality sue_expand_eval_phis[local]:
  !dfg bb s.
    eval_phis s (sue_expand_block dfg bb).bb_instructions =
    eval_phis s bb.bb_instructions
Proof
  simp[sue_expand_block_def] >> rpt strip_tac >>
  irule venomExecProofsTheory.eval_phis_same_phi_prefix >>
  simp[sue_expand_phi_prefix_length] >>
  rpt strip_tac >>
  irule sue_expand_phi_prefix_el >>
  gvs[sue_expand_phi_prefix_length]
QED

Triviality sue_block_sim_from_phi_idx[local]:
  !fuel ctx bb st dfg fresh fn.
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    (!inst. MEM inst bb.bb_instructions ==>
            ~is_alloca_op inst.inst_opcode /\
            sue_operands_wf inst) /\
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    fresh = sue_fresh_vars_fn fn /\
    st.vs_inst_idx = phi_prefix_length bb.bb_instructions ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (exec_block fuel ctx bb st)
      (exec_block fuel ctx (sue_expand_block dfg bb) st)
Proof
  rpt strip_tac >>
  simp[sue_expand_block_def] >>
  qspecl_then [`bb`, `dfg`, `fresh`, `fn`] mp_tac sue_block_sim_induct >>
  (impl_tac >- (rpt conj_tac >> metis_tac[])) >>
  disch_then (qspecl_then
    [`LENGTH bb.bb_instructions - phi_prefix_length bb.bb_instructions`,
     `fuel`, `ctx`, `st`] mp_tac) >>
  `st.vs_inst_idx <= LENGTH bb.bb_instructions` by
    metis_tac[venomExecProofsTheory.phi_prefix_length_le] >>
  `SUM (MAP (LENGTH o sue_expand_inst dfg)
        (TAKE st.vs_inst_idx bb.bb_instructions)) = st.vs_inst_idx` by (
    irule sue_expand_phi_prefix_sum >> simp[]) >>
  `st with vs_inst_idx := phi_prefix_length bb.bb_instructions = st` by
    simp[venom_state_component_equality] >>
  simp[]
QED

Triviality sue_run_block_sim[local]:
  !fuel ctx bb st dfg fresh fn.
    MEM bb fn.fn_blocks /\
    fn_inst_wf fn /\
    (!inst. MEM inst bb.bb_instructions ==>
            ~is_alloca_op inst.inst_opcode /\
            sue_operands_wf inst) /\
    (!inst x. MEM inst bb.bb_instructions /\
              MEM (Var x) inst.inst_operands ==> x NOTIN fresh) /\
    fresh = sue_fresh_vars_fn fn ==>
    lift_result (state_equiv fresh) (execution_equiv fresh) (execution_equiv fresh)
      (run_block fuel ctx bb st)
      (run_block fuel ctx (sue_expand_block dfg bb) st)
Proof
  rpt strip_tac >>
  `phi_prefix_length (sue_expand_block dfg bb).bb_instructions =
   phi_prefix_length bb.bb_instructions` by
    simp[sue_expand_block_def, sue_expand_phi_prefix_length] >>
  `eval_phis st (sue_expand_block dfg bb).bb_instructions =
   eval_phis st bb.bb_instructions` by simp[sue_expand_eval_phis] >>
  ONCE_REWRITE_TAC[run_block_def] >>
  ASM_REWRITE_TAC [] >>
  DISJ_CASES_TAC (Q.SPECL [`st`, `bb.bb_instructions`] eval_phis_ok_or_error_defs)
  >- (
    first_x_assum (qx_choose_then `s_phi` strip_assume_tac) >> gvs[] >>
    qspecl_then [`fuel`, `ctx`, `bb`,
      `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
      `dfg`, `sue_fresh_vars_fn fn`, `fn`]
      mp_tac sue_block_sim_from_phi_idx >>
    impl_tac >- (simp[] >> metis_tac[]) >>
    simp[])
  >- (
    first_x_assum (qx_choose_then `e` strip_assume_tac) >>
    gvs[lift_result_def])
QED

(* ===== Semantic correctness ===== *)

(* Expansion preserves semantics: running the expanded function yields a
   state-equivalent result to running the original, provided the function
   is well-formed, its variables are fresh w.r.t. sue_fresh_vars_fn, and
   no instruction uses alloca or violates sue_operands_wf. *)
Theorem sue_expand_function_correct_proof:
  !fuel ctx fn s.
    fn_inst_wf fn /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    (!bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
       ~is_alloca_op inst.inst_opcode /\ sue_operands_wf inst) /\
    s.vs_inst_idx = 0 ==>
    lift_result (state_equiv (sue_fresh_vars_fn fn))
               (execution_equiv (sue_fresh_vars_fn fn)) (execution_equiv (sue_fresh_vars_fn fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (sue_expand_function fn) s)
Proof
  rpt strip_tac >>
  `sue_expand_function fn =
   function_map_transform (sue_expand_block (dfg_build_function fn)) fn`
    by simp[sue_expand_function_is_fmt] >>
  pop_assum SUBST1_TAC >>
  irule passSimulationPropsTheory.block_sim_function_unconditional >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `x NOTIN sue_fresh_vars_fn fn` by metis_tac[] >>
      fs[stateEquivTheory.state_equiv_def, stateEquivTheory.execution_equiv_def])
  >- simp[sue_expand_block_label]
  >- (rpt strip_tac >> metis_tac[sue_run_block_sim])
  >- metis_tac[stateEquivProofsTheory.state_equiv_trans]
  >- metis_tac[stateEquivProofsTheory.execution_equiv_trans]
  >- metis_tac[execEquivParamProofsTheory.state_equiv_execution_equiv_valid_state_rel_proof]
QED

(* ===== Structural property: helpers ===== *)

(* sue_should_skip and sue_count_exempt are equivalent *)
Triviality skip_iff_exempt[local]:
  !op. sue_should_skip op <=> sue_count_exempt op
Proof
  Cases >> simp[sue_should_skip_def, sue_count_exempt_def, is_param_opcode_def]
QED

(* Digit-string separator lemma: underscore splits uniquely *)
Triviality digit_underscore_split[local]:
  !s1 s2 t1 t2. EVERY isDigit s1 /\ EVERY isDigit s2 /\
    (s1 ++ [#"_"] ++ t1 = s2 ++ [#"_"] ++ t2) ==>
    s1 = s2 /\ t1 = t2
Proof
  Induct >- (
    Cases_on `s2` >> rw[] >> fs[] >>
    `isDigit #"_" = F` by EVAL_TAC >> fs[]
  ) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `s2` >- (
    fs[] >> `isDigit #"_" = F` by EVAL_TAC >> fs[]
  ) >>
  fs[] >> res_tac
QED

(* Full injectivity of sue_fresh_var *)
Triviality sue_fresh_var_full_inj[local]:
  !id1 idx1 id2 idx2.
    sue_fresh_var id1 idx1 = sue_fresh_var id2 idx2 ==>
    id1 = id2 /\ idx1 = idx2
Proof
  rw[sue_fresh_var_def] >>
  fs[stringTheory.STRCAT_11] >>
  `EVERY isDigit (toString id1) /\ EVERY isDigit (toString id2)` by
    simp[ASCIInumbersTheory.EVERY_isDigit_num_to_dec_string] >>
  `STRCAT (STRCAT (toString id1) "_") (toString idx1) =
   STRCAT (STRCAT (toString id2) "_") (toString idx2)` by
    metis_tac[stringTheory.STRCAT_ASSOC] >>
  drule_all digit_underscore_split >> strip_tac >>
  fs[ASCIInumbersTheory.toString_inj]
QED

(* An operand in new_ops is either kept from original or is a fresh var.
   More precisely: for each position, new_ops[j] is either ops[j] (kept)
   or Var (sue_fresh_var inst.inst_id (j+idx)) (replaced). *)
Triviality sue_expand_ops_dichotomy[local]:
  !dfg inst ops idx assigns new_ops j.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    j < LENGTH ops ==>
    EL j new_ops = EL j ops \/
    EL j new_ops = Var (sue_fresh_var inst.inst_id (j + idx))
Proof
  Induct_on `ops` >> rw[sue_expand_ops_def] >>
  pairarg_tac >> fs[] >>
  Cases_on `j`
  >- ( (* j = 0 *)
    gvs[] >>
    Cases_on `~sue_needs_assign dfg inst idx` >> gvs[] >>
    Cases_on `h` >> gvs[LET_THM] >>
    (* Var case: condition is in assumption, not goal *)
    Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
              sue_count_remaining (Var s) ops = 0` >> gvs[]
  )
  >> ( (* j = SUC n *)
    gvs[] >>
    Cases_on `~sue_needs_assign dfg inst idx` >> gvs[] >>
    TRY (
      Cases_on `h` >> gvs[LET_THM] >>
      TRY (Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
                      sue_count_remaining (Var s) ops = 0` >> gvs[])
    ) >>
    first_x_assum (qspecl_then [`dfg`, `inst`, `idx+1`] mp_tac) >>
    simp[arithmeticTheory.ADD1]
  )
QED

(* If an original var is kept in new_ops, the DFG says it has ≤ 1 uses
   OR it doesn't need assignment. Either way, there's at most one instruction
   in the function that uses it (for the single-use property). *)
Triviality sue_expand_ops_kept_var_single_use[local]:
  !dfg inst ops idx assigns new_ops v j.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    j < LENGTH ops /\
    EL j ops = Var v /\
    EL j new_ops = Var v /\
    (!k. k < LENGTH ops ==> v <> sue_fresh_var inst.inst_id (k + idx)) ==>
    ~sue_needs_assign dfg inst (j + idx) \/
    (LENGTH (dfg_get_uses dfg v) = 1 /\
     sue_count_remaining (Var v) (DROP (j + 1) ops) = 0)
Proof
  Induct_on `ops` >> rw[sue_expand_ops_def] >>
  pairarg_tac >> fs[] >>
  Cases_on `j` >- (
    (* j = 0: EL 0 ops = Var v, EL 0 new_ops = Var v *)
    fs[] >>
    Cases_on `~sue_needs_assign dfg inst idx` >> fs[] >>
    Cases_on `h` >> fs[LET_THM] >>
    (* h = Var s, s = v *)
    Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
              sue_count_remaining (Var s) ops = 0` >> gvs[] >>
    TRY (disj2_tac >> fs[DROP_def] >> NO_TAC) >>
    (* false branch: new_ops head = Var(sue_fresh_var ...) = Var v *)
    (* But freshness says v <> sue_fresh_var inst.inst_id (0 + idx) *)
    first_x_assum (qspec_then `0` mp_tac) >> simp[]
  ) >>
  (* j = SUC n: use IH on tail *)
  gvs[] >>
  (* Establish freshness for recursive call *)
  `!k. k < LENGTH ops ==> v <> sue_fresh_var inst.inst_id (k + (idx + 1))` by (
    rpt strip_tac >>
    first_x_assum (qspec_then `k + 1` mp_tac) >>
    simp[arithmeticTheory.ADD1]
  ) >>
  Cases_on `~sue_needs_assign dfg inst idx` >> gvs[] >- (
    first_x_assum (qspecl_then [`dfg`, `inst`, `idx+1`] mp_tac) >>
    simp[arithmeticTheory.ADD1, DROP_def]
  ) >>
  Cases_on `h` >> gvs[LET_THM] >>
  TRY (Cases_on `LENGTH (dfg_get_uses dfg s) = 1 /\
                  sue_count_remaining (Var s) ops = 0` >> gvs[]) >>
  first_x_assum (qspecl_then [`dfg`, `inst`, `idx+1`] mp_tac) >>
  simp[arithmeticTheory.ADD1, DROP_def]
QED

(* For non-skipped instructions, the expanded instruction list is
   assigns ++ [mod_inst] where assigns are all ASSIGN (exempt) and
   mod_inst has the original opcode. *)
(* Already have sue_expand_inst_preserves_opcode — just re-export the key fact *)

(* Count contribution from one expanded instruction to var_use_count *)
Triviality sue_expand_inst_count[local]:
  !dfg inst v.
    sue_should_skip inst.inst_opcode ==>
    LENGTH (FILTER (\i. ~sue_count_exempt i.inst_opcode /\ MEM (Var v) i.inst_operands)
                   (sue_expand_inst dfg inst)) = 0
Proof
  rw[sue_expand_inst_def, skip_iff_exempt]
QED

Triviality sue_expand_inst_nonskip_count[local]:
  !dfg inst v.
    ~sue_should_skip inst.inst_opcode ==>
    LENGTH (FILTER (\i. ~sue_count_exempt i.inst_opcode /\ MEM (Var v) i.inst_operands)
                   (sue_expand_inst dfg inst)) =
    if MEM (Var v) (SND (sue_expand_ops dfg inst inst.inst_operands 0))
    then 1 else 0
Proof
  rw[sue_expand_inst_def] >>
  pairarg_tac >> fs[] >>
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    metis_tac[sue_expand_ops_assigns_are_assign] >>
  `~sue_count_exempt inst.inst_opcode` by metis_tac[skip_iff_exempt] >>
  simp[FILTER_APPEND_DISTRIB, FILTER_EQ_NIL, EVERY_MEM] >>
  rpt strip_tac >> gvs[sue_count_exempt_def, is_param_opcode_def] >>
  fs[EVERY_MEM] >> res_tac >> gvs[sue_count_exempt_def, is_param_opcode_def]
QED

(* fn_insts_blocks = FLAT of MAP *)
Triviality fn_insts_blocks_flat[local]:
  !bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED

(* MEM in fn_insts iff MEM in some block *)
Triviality fn_insts_mem[local]:
  !fn inst.
    MEM inst (fn_insts fn) <=>
    ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions
Proof
  rw[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

(* MEM (Var v) ops ==> MEM v (operand_vars ops) — one direction suffices *)
Triviality mem_var_operand_vars[local]:
  !ops v. MEM (Var v) ops ==> MEM v (operand_vars ops)
Proof
  Induct_on `ops` >> simp[] >> rpt strip_tac >> gvs[] >>
  simp[Once dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def] >>
  Cases_on `h` >> simp[dfgDefsTheory.operand_var_def]
QED

(* var_use_count summed over blocks = LENGTH of global FILTER *)
Triviality var_use_count_global[local]:
  !v bbs. SUM (MAP (var_use_count_block v) bbs) =
    LENGTH (FILTER (\i. ~sue_count_exempt i.inst_opcode /\
                        MEM (Var v) i.inst_operands)
                   (fn_insts_blocks bbs))
Proof
  gen_tac >> Induct_on `bbs` >>
  simp[fn_insts_blocks_def, var_use_count_block_def, FILTER_APPEND_DISTRIB]
QED

(* If Var v is in the expanded ops, v is either original or fresh.
   Derived from sue_expand_ops_dichotomy — no induction needed. *)
Triviality sue_expand_ops_var_source[local]:
  !dfg inst ops idx assigns new_ops v.
    sue_expand_ops dfg inst ops idx = (assigns, new_ops) /\
    MEM (Var v) new_ops ==>
    MEM (Var v) ops \/
    ?j. j < LENGTH ops /\ v = sue_fresh_var inst.inst_id (idx + j)
Proof
  rpt strip_tac >>
  `LENGTH new_ops = LENGTH ops` by metis_tac[sue_expand_ops_length] >>
  `?n. n < LENGTH new_ops /\ Var v = EL n new_ops` by metis_tac[MEM_EL] >>
  `n < LENGTH ops` by fs[] >>
  drule_all sue_expand_ops_dichotomy >> strip_tac >> gvs[]
  >- (disj1_tac >> metis_tac[MEM_EL])
  >- (disj2_tac >> qexists_tac `n` >> simp[arithmeticTheory.ADD_COMM])
QED

(* sue_fresh_var inst.inst_id j is in sue_fresh_vars_fn fn when inst is in fn *)
Triviality sue_fresh_var_in_fn_vars[local]:
  !fn inst j.
    MEM inst (fn_insts fn) /\ j < LENGTH inst.inst_operands ==>
    sue_fresh_var inst.inst_id j IN sue_fresh_vars_fn fn
Proof
  rw[sue_fresh_vars_fn_def, fn_insts_mem] >>
  simp[MEM_FLAT, MEM_MAP, MEM_MAPi, PULL_EXISTS] >>
  metis_tac[]
QED

(* Original operand vars are not in the fresh var set *)
Triviality sue_original_not_fresh[local]:
  !fn inst v.
    (!bb i x. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
       MEM (Var x) i.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    MEM inst (fn_insts fn) /\
    MEM (Var v) inst.inst_operands ==>
    v NOTIN sue_fresh_vars_fn fn
Proof
  rw[fn_insts_mem] >> metis_tac[]
QED

(* Combined: an original operand variable != any sue_fresh_var for any
   instruction in fn. Eliminates repeated 4-line freshness contradictions. *)
Triviality sue_original_neq_fresh[local]:
  !fn inst1 inst2 v j.
    (!bb i x. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
       MEM (Var x) i.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    MEM inst1 (fn_insts fn) /\
    MEM (Var v) inst1.inst_operands /\
    MEM inst2 (fn_insts fn) /\
    j < LENGTH inst2.inst_operands ==>
    v <> sue_fresh_var inst2.inst_id j
Proof
  rpt strip_tac >>
  `v NOTIN sue_fresh_vars_fn fn` by (
    fs[fn_insts_mem] >> metis_tac[]) >>
  `sue_fresh_var inst2.inst_id j IN sue_fresh_vars_fn fn` by (
    irule sue_fresh_var_in_fn_vars >> simp[]) >>
  metis_tac[]
QED

(* ALL_DISTINCT on a MAP implies injectivity on list elements *)
Triviality all_distinct_map_eq[local]:
  !f l x y.
    ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ f x = f y ==> x = y
Proof
  rpt strip_tac >> fs[MEM_EL] >>
  `EL n (MAP f l) = f (EL n l)` by (irule EL_MAP >> simp[]) >>
  `EL n' (MAP f l) = f (EL n' l)` by (irule EL_MAP >> simp[]) >>
  `n < LENGTH (MAP f l)` by simp[] >>
  `n' < LENGTH (MAP f l)` by simp[] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

(* Core uniqueness: at most one instruction has Var v in its expanded ops.
   If two instructions both have Var v in their expanded new_ops,
   they must be the same instruction. *)
(* When sue_needs_assign is false for a Var operand (non-LOG-0), uses <= 1 *)
Triviality sue_not_needs_assign_uses_le1[local]:
  !dfg inst n v.
    ~sue_needs_assign dfg inst n /\
    n < LENGTH inst.inst_operands /\
    EL n inst.inst_operands = Var v /\
    ~((inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) /\ n = 0) ==>
    LENGTH (dfg_get_uses dfg v) <= 1
Proof
  rw[sue_needs_assign_def, LET_THM] >>
  BasicProvers.every_case_tac >> fs[] >> gvs[]
QED

(* If Var v was kept (not replaced by fresh) in sue_expand_ops and
   the LOG-pos-0-is-Lit condition holds, then v has at most 1 user. *)
Triviality sue_kept_var_at_most_one_user[local]:
  !fn dfg inst v.
    dfg = dfg_build_function fn /\
    (!bb i x. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions /\
       MEM (Var x) i.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    (!i. MEM i (fn_insts fn) /\
         (i.inst_opcode = LOG \/ i.inst_opcode = DRET) ==>
       ?n. HD i.inst_operands = Lit n) /\
    MEM inst (fn_insts fn) /\
    MEM (Var v) inst.inst_operands /\
    MEM (Var v) (SND (sue_expand_ops dfg inst inst.inst_operands 0)) ==>
    LENGTH (dfg_get_uses (dfg_build_function fn) v) <= 1
Proof
  rpt strip_tac
  \\ Cases_on `sue_expand_ops dfg inst inst.inst_operands 0`
  \\ fs[] \\ imp_res_tac sue_expand_ops_length
  \\ `?j. j < LENGTH r /\ Var v = EL j r` by metis_tac[MEM_EL]
  \\ `j < LENGTH inst.inst_operands` by fs[]
  (* The dichotomy: either EL j r was kept from original, or replaced by fresh *)
  \\ `EL j inst.inst_operands = Var v` by (
       qspecl_then [`dfg`, `inst`, `inst.inst_operands`, `0`, `q`, `r`, `j`]
         mp_tac sue_expand_ops_dichotomy >> simp[] >> strip_tac
       >- gvs[]
       >- metis_tac[sue_original_neq_fresh])
  (* Exclude parser-significant pos 0 for LOG and DRET: HD is Lit. *)
  \\ `~((inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) /\ j = 0)` by (
       strip_tac >> fs[] >>
       res_tac >> Cases_on `inst.inst_operands` >> fs[])
  (* Now use kept_var_single_use: either ~sue_needs_assign or LENGTH uses = 1 *)
  \\ `LENGTH (dfg_get_uses dfg v) <= 1` by (
       qspecl_then [`dfg`, `inst`, `inst.inst_operands`, `0`,
                    `q`, `r`, `v`, `j`]
         mp_tac sue_expand_ops_kept_var_single_use >>
       simp[] >>
       (impl_tac >- (gvs[] >> metis_tac[sue_original_neq_fresh])) >>
       strip_tac >> simp[] >>
       metis_tac[sue_not_needs_assign_uses_le1])
  \\ gvs[]
QED

(* Helper for the "both original" case of sue_expand_at_most_one.
   If both inst1 and inst2 kept Var v as original operand after expansion,
   and v has at most 1 user in the DFG, then inst1 = inst2.
   Needs LOG-pos-0-is-Lit: without it, two LOG instructions can both keep
   Var v at position 0 (sue_needs_assign hardcodes F for LOG pos 0). *)
Triviality sue_both_original_same[local]:
  !fn dfg v inst1 inst2.
    dfg = dfg_build_function fn /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    (!inst. MEM inst (fn_insts fn) /\
         (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) ==>
       ?n. HD inst.inst_operands = Lit n) /\
    MEM inst1 (fn_insts fn) /\ MEM (Var v) inst1.inst_operands /\
    MEM (Var v) (SND (sue_expand_ops dfg inst1 inst1.inst_operands 0)) /\
    MEM inst2 (fn_insts fn) /\ MEM (Var v) inst2.inst_operands ==>
    inst1 = inst2
Proof
  rpt strip_tac >>
  `LENGTH (dfg_get_uses (dfg_build_function fn) v) <= 1` by
    metis_tac[sue_kept_var_at_most_one_user] >>
  `MEM inst1 (dfg_get_uses (dfg_build_function fn) v)` by
    metis_tac[dfg_build_function_uses_complete, mem_var_operand_vars] >>
  `MEM inst2 (dfg_get_uses (dfg_build_function fn) v)` by
    metis_tac[dfg_build_function_uses_complete, mem_var_operand_vars] >>
  Cases_on `dfg_get_uses (dfg_build_function fn) v` >> fs[] >>
  Cases_on `t` >> fs[] >> gvs[]
QED

Triviality sue_expand_at_most_one[local]:
  !fn dfg v inst1 inst2.
    dfg = dfg_build_function fn /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    (!inst. MEM inst (fn_insts fn) /\
         (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) ==>
       ?n. HD inst.inst_operands = Lit n) /\
    MEM inst1 (fn_insts fn) /\ ~sue_should_skip inst1.inst_opcode /\
    MEM (Var v) (SND (sue_expand_ops dfg inst1 inst1.inst_operands 0)) /\
    MEM inst2 (fn_insts fn) /\ ~sue_should_skip inst2.inst_opcode /\
    MEM (Var v) (SND (sue_expand_ops dfg inst2 inst2.inst_operands 0)) ==>
    inst1 = inst2
Proof
  rpt strip_tac >>
  (* Get the source of v in inst1's and inst2's expanded ops *)
  `MEM (Var v) inst1.inst_operands \/
   ?j1. j1 < LENGTH inst1.inst_operands /\
        v = sue_fresh_var inst1.inst_id j1` by (
    qspecl_then [`dfg`, `inst1`, `inst1.inst_operands`, `0`,
                 `FST (sue_expand_ops dfg inst1 inst1.inst_operands 0)`,
                 `SND (sue_expand_ops dfg inst1 inst1.inst_operands 0)`, `v`]
      mp_tac sue_expand_ops_var_source >> simp[]) >>
  `MEM (Var v) inst2.inst_operands \/
   ?j2. j2 < LENGTH inst2.inst_operands /\
        v = sue_fresh_var inst2.inst_id j2` by (
    qspecl_then [`dfg`, `inst2`, `inst2.inst_operands`, `0`,
                 `FST (sue_expand_ops dfg inst2 inst2.inst_operands 0)`,
                 `SND (sue_expand_ops dfg inst2 inst2.inst_operands 0)`, `v`]
      mp_tac sue_expand_ops_var_source >> simp[])
  >- metis_tac[sue_both_original_same]
  >- metis_tac[sue_original_neq_fresh]
  >- metis_tac[sue_original_neq_fresh]
  >- (
    `sue_fresh_var inst1.inst_id j1 = sue_fresh_var inst2.inst_id j2` by
      metis_tac[] >>
    drule sue_fresh_var_full_inj >> strip_tac >>
    `inst1.inst_id = inst2.inst_id` by fs[] >>
    metis_tac[all_distinct_map_eq])
QED

(* Requires sue_count_exempt (ASSIGN, PHI, PARAM, OFFSET — matching
   sue_should_skip) in var_use_count_block so that inserted ASSIGNs don't
   inflate the use count.
   Also requires freshness: original operand vars must not collide with
   sue_fresh_var names.  Without freshness, an original Var "sue_3_0" kept
   by last-occurrence opt can collide with a fresh var "sue_3_0" generated
   for instruction id=3 pos=0 (e.g. two ADD instructions, one with Lit
   operands id=3 and one with Var "sue_3_0" operand id=7). *)
(* If at most one element of a list satisfies P, FILTER has length <= 1 *)
Triviality filter_flat_at_most_one[local]:
  !P f l.
    ALL_DISTINCT l /\
    (!x. MEM x l ==> LENGTH (FILTER P (f x)) <= 1) /\
    (!x y. MEM x l /\ MEM y l /\
           FILTER P (f x) <> [] /\ FILTER P (f y) <> [] ==> x = y) ==>
    LENGTH (FILTER P (FLAT (MAP f l))) <= 1
Proof
  gen_tac >> gen_tac >> Induct >- simp[] >>
  rpt strip_tac >>
  qpat_x_assum `ALL_DISTINCT (h::l)` mp_tac >>
  simp[ALL_DISTINCT] >> strip_tac >>
  `(!x. MEM x l ==> LENGTH (FILTER P (f x)) <= 1)` by metis_tac[MEM] >>
  `(!x y. MEM x l /\ MEM y l /\
          FILTER P (f x) <> [] /\ FILTER P (f y) <> [] ==> x = y)`
    by metis_tac[MEM] >>
  simp[FILTER_APPEND_DISTRIB, LENGTH_APPEND] >>
  `LENGTH (FILTER P (f h)) <= 1` by metis_tac[MEM] >>
  Cases_on `FILTER P (f h)`
  >- (qpat_x_assum `ALL_DISTINCT l /\ _ ==>
          LENGTH (FILTER P (FLAT (MAP f l))) <= 1` mp_tac >> simp[]) >>
  Cases_on `t` >- (
    simp[] >>
    `FILTER P (FLAT (MAP f l)) = []` suffices_by simp[] >>
    rw[FILTER_EQ_NIL, EVERY_MEM, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
    spose_not_then strip_assume_tac >>
    `FILTER P (f y) <> []` by
      (simp[FILTER_NEQ_NIL, EXISTS_MEM] >> metis_tac[]) >>
    `h = y` by (
      qpat_x_assum `!a b. _ /\ _ /\ FILTER _ _ <> [] /\ _ ==> _`
        (qspecl_then [`h`, `y`] mp_tac) >> simp[]) >>
    metis_tac[]) >>
  gvs[]
QED

(* If Var v passes the filter in sue_expand_inst, the inst must be non-skipped
   and Var v must be in the expanded ops *)
Triviality sue_expand_inst_filter_mem[local]:
  !dfg inst v ei.
    MEM ei (sue_expand_inst dfg inst) /\
    ~sue_count_exempt ei.inst_opcode /\
    MEM (Var v) ei.inst_operands ==>
    ~sue_should_skip inst.inst_opcode /\
    MEM (Var v) (SND (sue_expand_ops dfg inst inst.inst_operands 0)) /\
    ei = inst with inst_operands :=
           SND (sue_expand_ops dfg inst inst.inst_operands 0)
Proof
  rpt gen_tac >> strip_tac >>
  fs[sue_expand_inst_def] >>
  Cases_on `sue_should_skip inst.inst_opcode` >> gvs[]
  >- (gvs[skip_iff_exempt]) >>
  pairarg_tac >> gvs[MEM_APPEND] >>
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    metis_tac[sue_expand_ops_assigns_are_assign] >>
  fs[EVERY_MEM] >> res_tac >> gvs[sue_count_exempt_def, is_param_opcode_def]
QED

(* The FLAT expanded instruction list = FLAT MAP sue_expand_inst over fn_insts *)
Triviality sue_expand_fn_insts[local]:
  !dfg bbs.
    fn_insts_blocks (MAP (sue_expand_block dfg) bbs) =
    FLAT (MAP (sue_expand_inst dfg) (fn_insts_blocks bbs))
Proof
  gen_tac >> Induct >>
  simp[fn_insts_blocks_def, sue_expand_block_def, MAP_FLAT]
QED

(* Each expansion has at most 1 non-exempt instruction (the assigns are ASSIGN) *)
Triviality sue_expand_inst_filter_le1[local]:
  !P dfg inst.
    (!ei. P ei ==> ~sue_count_exempt ei.inst_opcode) ==>
    LENGTH (FILTER P (sue_expand_inst dfg inst)) <= 1
Proof
  rpt strip_tac >>
  simp[sue_expand_inst_def] >>
  Cases_on `sue_should_skip inst.inst_opcode` >> simp[]
  >- (Cases_on `P inst` >> simp[])
  >> pairarg_tac >> simp[FILTER_APPEND_DISTRIB, LENGTH_APPEND] >>
  `FILTER P assigns = []` suffices_by (
    strip_tac >> simp[] >> Cases_on `P (inst with inst_operands := new_ops)` >> simp[]
  ) >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >> rpt strip_tac >>
  `x.inst_opcode = ASSIGN` by (
    `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
      metis_tac[sue_expand_ops_assigns_are_assign] >>
    fs[EVERY_MEM] >> res_tac
  ) >>
  `sue_count_exempt ASSIGN` by EVAL_TAC >>
  metis_tac[]
QED

(* If filter is nonempty, inst is non-skipped and contributes Var v *)
Triviality sue_expand_inst_filter_nonempty[local]:
  !dfg inst v.
    FILTER (\ei. ~sue_count_exempt ei.inst_opcode /\
                 MEM (Var v) ei.inst_operands)
           (sue_expand_inst dfg inst) <> [] ==>
    ~sue_should_skip inst.inst_opcode /\
    MEM (Var v) (SND (sue_expand_ops dfg inst inst.inst_operands 0))
Proof
  rpt gen_tac >> strip_tac >>
  fs[FILTER_NEQ_NIL, EXISTS_MEM] >>
  drule_all sue_expand_inst_filter_mem >> simp[]
QED

(* The single-use expansion pass establishes single-use form: after expansion,
   each non-exempt variable appears in at most one instruction's operands.
   Requires distinct instruction IDs, fresh variable separation, and LOG
   instructions having a literal as their first operand. *)
Theorem sue_establishes_single_use_form:
  !fn.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    (!bb inst x. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==> x NOTIN sue_fresh_vars_fn fn) /\
    (!inst. MEM inst (fn_insts fn) /\
         (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) ==>
       ?n. HD inst.inst_operands = Lit n) ==>
    single_use_form (sue_expand_function fn)
Proof
  rw[single_use_form_def, sue_expand_function_def, LET_THM] >>
  rw[var_use_count_global, sue_expand_fn_insts] >>
  qabbrev_tac `dfg = dfg_build_function fn` >>
  irule filter_flat_at_most_one >>
  simp[GSYM fn_insts_def] >>
  conj_tac >- (
    rpt strip_tac >>
    imp_res_tac sue_expand_inst_filter_nonempty >>
    irule sue_expand_at_most_one >>
    simp[Abbr `dfg`] >>
    qexists_tac `fn` >> qexists_tac `v` >>
    rpt conj_tac >> first_assum ACCEPT_TAC
  ) >>
  conj_tac >- (
    rpt strip_tac >> irule sue_expand_inst_filter_le1 >> simp[]
  ) >>
  metis_tac[ALL_DISTINCT_MAP]
QED
