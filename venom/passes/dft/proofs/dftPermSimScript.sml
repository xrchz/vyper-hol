(*
 * DFT Permutation Simulation
 *
 * If all instructions are pairwise bilaterally independent and all
 * succeed (OK), then any permutation produces the same final state.
 * Uses independent_commute_eq (from dftBlockSimTheory) for adjacent swaps,
 * then extends to arbitrary permutations via PERM induction.
 *
 * TOP-LEVEL: run_insts_perm_ok, run_insts_perm_ok_ext,
 *   run_insts_topo_equiv, run_insts_append, run_insts_bubble_to_front,
 *   run_insts_bubble_to_front_ext, flip_operands_step_inst,
 *   flip_operands_step_inst_base, step_inst_nofail_not_halt_abort
 * Helper: bi_independent, bi_independent_iff_ext, ext_bi_independent,
 *   ext_bi_independent_sym, bi_independent_imp_ext,
 *   step_swap_ok_ext, el_delete_map, topo_sorted_delete,
 *   topo_sorted_tail, perm_cons_delete,
 *   pairwise_bi_independent, pairwise_ext_bi_independent, topo_sorted
 *)

Theory dftPermSim
Ancestors
  dftBlockSim dftCommutation dftDefs
  analysisSimDefs analysisSimProofsBase
  passSharedDefs passSharedProps passSharedTransfer passSharedField
  passSimulationDefs stateEquiv
  venomExecSemantics venomExecProps venomEffects
  venomState venomInst venomInstProps
  sorting pred_set list rich_list

(* ===== Symmetry helpers ===== *)

Triviality effects_independent_sym:
  !op1 op2. effects_independent op1 op2 ==> effects_independent op2 op1
Proof
  rw[effects_independent_def] >> metis_tac[DISJOINT_SYM]
QED


(* ===== run_insts append decomposition ===== *)

(* run_insts distributes over append: run the first list to get an
   intermediate state, then continue with the second list. *)
Theorem run_insts_append:
  !fuel ctx l1 l2 s.
    run_insts fuel ctx (l1 ++ l2) s =
    case run_insts fuel ctx l1 s of
      OK s' => run_insts fuel ctx l2 s'
    | other => other
Proof
  Induct_on `l1` >> rpt strip_tac >>
  simp[run_insts_def] >>
  Cases_on `step_inst fuel ctx h s` >> simp[run_insts_def]
QED

(* ===== Bilateral independence ===== *)

Definition bi_independent_def:
  bi_independent i1 i2 <=>
    DISJOINT (set (inst_defs i1)) (set (inst_uses i2)) /\
    DISJOINT (set (inst_defs i2)) (set (inst_uses i1)) /\
    DISJOINT (set (inst_defs i1)) (set (inst_defs i2)) /\
    effects_independent i1.inst_opcode i2.inst_opcode /\
    abort_compatible i1.inst_opcode i2.inst_opcode /\
    ~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode /\
    ~is_alloca_op i1.inst_opcode /\ ~is_alloca_op i2.inst_opcode /\
    ~is_ext_call_op i1.inst_opcode /\ ~is_ext_call_op i2.inst_opcode /\
    i1.inst_opcode <> INVOKE /\ i2.inst_opcode <> INVOKE
End

Triviality bi_independent_sym:
  !i1 i2. bi_independent i1 i2 <=> bi_independent i2 i1
Proof
  rw[bi_independent_def, effects_independent_def, abort_compatible_def] >>
  metis_tac[DISJOINT_SYM]
QED

(* bi_independent implies the preconditions of effects_independent_commute *)
Triviality bi_independent_commute_pre:
  !i1 i2.
    bi_independent i1 i2 ==>
    DISJOINT (set (inst_defs i1)) (set (inst_uses i2)) /\
    DISJOINT (set (inst_defs i2)) (set (inst_uses i1)) /\
    DISJOINT (set (inst_defs i1)) (set (inst_defs i2)) /\
    effects_independent i1.inst_opcode i2.inst_opcode /\
    ~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode /\
    ~is_alloca_op i1.inst_opcode /\ ~is_alloca_op i2.inst_opcode
Proof
  simp[bi_independent_def]
QED

(* ===== Extended bilateral independence (allows INVOKE) ===== *)

(* Like bi_independent but without the ~INVOKE restriction.
   INVOKE can be reordered past pure ops because effects_independent INVOKE ADD = T.
   The swap proof for ext uses step_inst_ok_frame (all opcodes) instead of
   step_inst_base. *)
Definition ext_bi_independent_def:
  ext_bi_independent i1 i2 <=>
    DISJOINT (set (inst_defs i1)) (set (inst_uses i2)) /\
    DISJOINT (set (inst_defs i2)) (set (inst_uses i1)) /\
    DISJOINT (set (inst_defs i1)) (set (inst_defs i2)) /\
    effects_independent i1.inst_opcode i2.inst_opcode /\
    abort_compatible i1.inst_opcode i2.inst_opcode /\
    ~is_terminator i1.inst_opcode /\ ~is_terminator i2.inst_opcode /\
    ~is_alloca_op i1.inst_opcode /\ ~is_alloca_op i2.inst_opcode /\
    ~is_ext_call_op i1.inst_opcode /\ ~is_ext_call_op i2.inst_opcode
End

(* Extended bilateral independence is symmetric. *)
Theorem ext_bi_independent_sym:
  !i1 i2. ext_bi_independent i1 i2 <=> ext_bi_independent i2 i1
Proof
  rw[ext_bi_independent_def, effects_independent_def,
     abort_compatible_def] >>
  metis_tac[DISJOINT_SYM]
QED

(* Bilateral independence implies extended bilateral independence
   (drops the INVOKE restriction). *)
Theorem bi_independent_imp_ext:
  !i1 i2. bi_independent i1 i2 ==> ext_bi_independent i1 i2
Proof
  simp[bi_independent_def, ext_bi_independent_def]
QED

(* bi_independent is exactly ext_bi_independent plus the no-INVOKE restriction.
   Makes explicit the relationship between the two definitions. *)
Theorem bi_independent_iff_ext:
  !i1 i2. bi_independent i1 i2 <=>
    ext_bi_independent i1 i2 /\
    i1.inst_opcode <> INVOKE /\ i2.inst_opcode <> INVOKE
Proof
  rw[bi_independent_def, ext_bi_independent_def] >> metis_tac[]
QED

(* ===== Helpers for adjacent swap ===== *)

(* Var membership implies operand_vars membership *)
Triviality var_mem_operand_vars:
  !y ops. MEM (Var y) ops ==> MEM y (operand_vars ops)
Proof
  Induct_on `ops` >> simp[operand_vars_def] >>
  rpt strip_tac >> gvs[operand_var_def] >>
  Cases_on `operand_var h` >> simp[]
QED

(* ===== Adjacent swap: OK case ===== *)

(* The 5 conditions for step_inst_base_ok_transfer follow from
   step_inst a s = OK sa + disjointness + effects_independence.
   Extract as a reusable tactic for both directions. *)
(* Shared tactic for the 5 conditions of step_inst_base_ok_transfer.
   Expects: step_inst fuel ctx a s = OK sa, DISJOINT outputs/operands,
   effects_independent in assumptions. Variable names must match. *)
val ok_transfer_field_tac =
  let val pres_tac =
    qspecl_then [`fuel`, `ctx`, `a`, `s`, `sa`] mp_tac
      step_inst_preserves_all >> simp[]
  in
  rpt conj_tac
  >- (rpt strip_tac >>
      Cases_on `op` >> simp[eval_operand_def] >>
      FIRST [
        (rename1 `Var n` >>
         qspecl_then [`fuel`, `ctx`, `a`, `s`, `sa`] mp_tac
           step_preserves_non_output_vars >> simp[] >>
         disch_then (qspec_then `n` mp_tac) >>
         impl_tac >- (gvs[DISJOINT_DEF, EXTENSION] >>
           metis_tac[var_mem_operand_vars, MEM]) >>
         simp[]),
        metis_tac[step_preserves_labels]
      ])
  >- pres_tac >- pres_tac
  >> (pres_tac >> strip_tac >>
      spose_not_then strip_assume_tac >>
      gvs[effects_independent_def] >>
      `Eff_RETURNDATA IN read_effects RETURNDATACOPY` by EVAL_TAC >>
      metis_tac[IN_DISJOINT])
  end;

(* Backward: b succeeds on sa ==> b succeeds on s *)
Triviality step_ok_transfer_backward:
  !fuel ctx a b s sa sab.
    step_inst fuel ctx a s = OK sa /\
    step_inst_base b sa = OK sab /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    ~is_alloca_op a.inst_opcode /\ ~is_ext_call_op a.inst_opcode /\
    ~is_alloca_op b.inst_opcode /\ ~is_ext_call_op b.inst_opcode /\
    a.inst_opcode <> INVOKE /\
    DISJOINT (set a.inst_outputs) (set (operand_vars b.inst_operands)) /\
    effects_independent a.inst_opcode b.inst_opcode ==>
    ?sb. step_inst_base b s = OK sb
Proof
  rpt strip_tac >>
  irule step_inst_base_ok_transfer >>
  simp[] >> qexistsl_tac [`sa`, `sab`] >> simp[] >>
  ok_transfer_field_tac
QED

(* Forward: b succeeds on s ==> b succeeds on sa *)
Triviality step_ok_transfer_forward:
  !fuel ctx a b s sa sb.
    step_inst fuel ctx a s = OK sa /\
    step_inst_base b s = OK sb /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    ~is_alloca_op a.inst_opcode /\ ~is_ext_call_op a.inst_opcode /\
    ~is_alloca_op b.inst_opcode /\ ~is_ext_call_op b.inst_opcode /\
    a.inst_opcode <> INVOKE /\
    DISJOINT (set a.inst_outputs) (set (operand_vars b.inst_operands)) /\
    effects_independent a.inst_opcode b.inst_opcode ==>
    ?sab. step_inst_base b sa = OK sab
Proof
  rpt strip_tac >>
  irule step_inst_base_ok_transfer >>
  simp[] >> qexistsl_tac [`s`, `sb`] >> simp[] >>
  ok_transfer_field_tac
QED

Triviality step_swap_ok:
  !fuel ctx a b s sa sab.
    bi_independent a b /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rpt strip_tac >>
  gvs[bi_independent_def, inst_defs_def, inst_uses_def] >>
  (* step_inst_base versions *)
  (sg `step_inst_base a s = OK sa` >- gvs[step_inst_non_invoke]) >>
  (sg `step_inst_base b sa = OK sab` >- gvs[step_inst_non_invoke]) >>
  (* b succeeds on s (backward transfer: sa -> s) *)
  (sg `?sb. step_inst_base b s = OK sb`
   >- (irule step_ok_transfer_backward >>
       simp[] >> qexistsl_tac [`a`, `ctx`, `fuel`, `sa`, `sab`] >>
       gvs[])) >>
  (* a succeeds on sb (forward transfer: s -> sb, with b as modifier) *)
  (sg `?sa'. step_inst_base a sb = OK sa'`
   >- (qspecl_then [`fuel`, `ctx`, `b`, `a`, `s`, `sb`, `sa`] mp_tac
         step_ok_transfer_forward >>
       simp[step_inst_non_invoke] >>
       impl_tac >- metis_tac[effects_independent_sym] >>
       simp[])) >>
  qexists_tac `sb` >>
  (conj_tac >- gvs[step_inst_non_invoke]) >>
  (* convert to step_inst *)
  (sg `step_inst fuel ctx b s = OK sb`
   >- gvs[step_inst_non_invoke]) >>
  (sg `step_inst fuel ctx a sb = OK sa'`
   >- gvs[step_inst_non_invoke]) >>
  (* sa' = sab by independent_commute_eq *)
  `sab = sa'` suffices_by simp[] >>
  irule independent_commute_eq >>
  qexistsl_tac [`ctx`, `fuel`, `a`, `b`, `s`, `sa`, `sb`] >>
  gvs[inst_defs_def, inst_uses_def]
QED

(* Adjacent swap in run_insts context *)
Triviality run_insts_swap_adjacent_ok:
  !fuel ctx prefix a b suffix s s_result.
    bi_independent a b /\
    run_insts fuel ctx (prefix ++ [a; b] ++ suffix) s = OK s_result ==>
    run_insts fuel ctx (prefix ++ [b; a] ++ suffix) s = OK s_result
Proof
  rpt strip_tac >>
  gvs[run_insts_append] >>
  Cases_on `run_insts fuel ctx prefix s` >>
  gvs[run_insts_def, AllCaseEqs()] >>
  Cases_on `step_inst fuel ctx a v` >>
  gvs[run_insts_def, AllCaseEqs()] >>
  Cases_on `step_inst fuel ctx b v'` >>
  gvs[run_insts_def, AllCaseEqs()] >>
  drule_all step_swap_ok >> strip_tac >>
  simp[]
QED

(* If every element in prefix is bi_independent with x, bubble x
   from after the prefix to the front, preserving the OK result. *)
Theorem run_insts_bubble_to_front:
  !prefix fuel ctx x suffix s r.
    EVERY (bi_independent x) prefix /\
    run_insts fuel ctx (prefix ++ [x] ++ suffix) s = OK r ==>
    run_insts fuel ctx ([x] ++ prefix ++ suffix) s = OK r
Proof
  Induct_on `prefix` >> simp[] >>
  rpt strip_tac >> gvs[EVERY_DEF] >>
  (* h :: prefix ++ [x] ++ suffix executed OK.
     Decompose: step h then run (prefix ++ [x] ++ suffix). *)
  gvs[run_insts_def, AllCaseEqs()] >>
  (* IH: bubble x past prefix after stepping h *)
  first_x_assum drule >> disch_then drule >> strip_tac >>
  (* Now: run_insts (x :: prefix ++ suffix) after step h = OK r *)
  gvs[run_insts_def, AllCaseEqs()] >>
  (* Swap x and h: bi_independent x h, step h s = OK, step x (step h s) = OK
     ==> step x s = OK sx, step h sx = same final state *)
  `bi_independent h x` by metis_tac[bi_independent_sym] >>
  drule_all step_swap_ok >> strip_tac >>
  simp[run_insts_def]
QED

(* ===== Pure step characterization ===== *)

(* effects_independent with INVOKE implies the other op has empty effects *)
Triviality effects_independent_invoke_empty:
  !op. effects_independent INVOKE op ==>
       write_effects op = {} /\ read_effects op = {} /\ op <> INVOKE
Proof
  Cases >> EVAL_TAC
QED

(* Given effects_independent between INVOKE and op, derive all useful facts:
   op is not INVOKE, has empty effects, and is not an ext_call_op.
   Eliminates ~30 lines of boilerplate per use site. *)
Triviality invoke_implies_pure:
  !op. effects_independent INVOKE op ==>
    op <> INVOKE /\
    write_effects op = {} /\
    read_effects op = {} /\
    ~is_ext_call_op op
Proof
  Cases >>
  simp[effects_independent_def, write_effects_def, read_effects_def,
       is_ext_call_op_def, all_effects_def] >> EVAL_TAC
QED

(* A non-INVOKE, non-terminator, non-alloca, non-ext_call instruction with
   empty write+read_effects, inst_wf, and one output: OK result is update_var.
   Thin wrapper around pure_step_structure (from dftBlockSim). *)
Triviality pure_step_is_update_var:
  !fuel ctx b s sb.
    step_inst fuel ctx b s = OK sb /\
    b.inst_opcode <> INVOKE /\
    ~is_terminator b.inst_opcode /\
    ~is_alloca_op b.inst_opcode /\
    ~is_ext_call_op b.inst_opcode /\
    write_effects b.inst_opcode = {} /\
    read_effects b.inst_opcode = {} /\
    inst_wf b /\
    LENGTH b.inst_outputs = 1 ==>
    ?v. sb = update_var (HD b.inst_outputs) v s
Proof
  rpt strip_tac >>
  `step_inst_base b s = OK sb` by gvs[step_inst_non_invoke] >>
  drule pure_step_structure >> simp[] >>
  strip_tac >> gvs[] >>
  `LENGTH pairs = 1` by metis_tac[LENGTH_MAP] >>
  Cases_on `pairs` >> gvs[] >>
  PairCases_on `h` >>
  qexists_tac `h1` >> simp[] >>
  qpat_x_assum `_ = b.inst_outputs`
    (fn th => rewrite_tac[GSYM th]) >> simp[]
QED

(* Transfer a non-INVOKE, empty-effects instruction across any non-terminator
   OK step. If step_inst_base a s = OK sa and step_inst b s = OK sb
   with a's operands disjoint from b's outputs, then step_inst_base a sb = OK.
   Handles PHI/PARAM/RETURNDATACOPY by using step_preserves_* on b. *)
Triviality pure_inst_transfer_across:
  !fuel ctx a b s sa sb.
    step_inst_base a s = OK sa /\
    step_inst fuel ctx b s = OK sb /\
    a.inst_opcode <> INVOKE /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    ~is_alloca_op a.inst_opcode /\
    write_effects a.inst_opcode = {} /\
    read_effects a.inst_opcode = {} /\
    DISJOINT (set b.inst_outputs) (set (operand_vars a.inst_operands)) ==>
    ?sba. step_inst_base a sb = OK sba
Proof
  rpt strip_tac >>
  qspecl_then [`a`, `s`, `sa`, `sb`] mp_tac step_inst_base_ok_transfer >>
  (* Discharge side conditions *)
  `~is_ext_call_op a.inst_opcode` by (
    spose_not_then strip_assume_tac >>
    Cases_on `a.inst_opcode` >>
    gvs[is_ext_call_op_def, write_effects_def, all_effects_def]) >>
  `!op. MEM op a.inst_operands ==>
        eval_operand op s = eval_operand op sb` by (
    rpt strip_tac >> Cases_on `op` >> simp[eval_operand_def]
    >- (rename1 `Var n` >>
        qspecl_then [`fuel`, `ctx`, `b`, `s`, `sb`] mp_tac
          step_preserves_non_output_vars >> simp[] >>
        disch_then (qspec_then `n` mp_tac) >>
        impl_tac
        >- (gvs[DISJOINT_DEF, EXTENSION] >>
            metis_tac[var_mem_operand_vars, MEM])
        >> simp[])
    >> (qspecl_then [`fuel`, `ctx`, `b`, `s`, `sb`] mp_tac
          step_preserves_labels >> simp[])) >>
  `a.inst_opcode = PHI ==> s.vs_prev_bb = sb.vs_prev_bb` by (
    strip_tac >>
    qspecl_then [`fuel`, `ctx`, `b`, `s`, `sb`] mp_tac
      step_preserves_control_flow >> simp[]) >>
  `a.inst_opcode = PARAM ==> s.vs_params = sb.vs_params` by (
    strip_tac >>
    qspecl_then [`fuel`, `ctx`, `b`, `s`, `sb`] mp_tac
      step_preserves_params >> simp[]) >>
  `a.inst_opcode = FMP_PARAM ==> s.vs_params = sb.vs_params` by (
    strip_tac >>
    qspecl_then [`fuel`, `ctx`, `b`, `s`, `sb`] mp_tac
      step_preserves_params >> simp[]) >>
  `a.inst_opcode = RETPC_PARAM ==> s.vs_params = sb.vs_params` by (
    strip_tac >>
    qspecl_then [`fuel`, `ctx`, `b`, `s`, `sb`] mp_tac
      step_preserves_params >> simp[]) >>
  `a.inst_opcode = RETURNDATACOPY ==> s.vs_returndata = sb.vs_returndata` by (
    strip_tac >> gvs[read_effects_def]) >>
  simp[]
QED

(* ===== Extended swap: allows INVOKE ===== *)

(* Backward transfer for ext: b (non-INVOKE) succeeds on s given b succeeded
   on sa, where a modified s to sa but a's outputs are disjoint from b's
   operands. Works even when a is INVOKE. *)
Triviality step_ok_transfer_backward_ext:
  !fuel ctx a b s sa sab.
    step_inst fuel ctx a s = OK sa /\
    step_inst_base b sa = OK sab /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    ~is_alloca_op b.inst_opcode /\ ~is_ext_call_op b.inst_opcode /\
    DISJOINT (set a.inst_outputs) (set (operand_vars b.inst_operands)) /\
    effects_independent a.inst_opcode b.inst_opcode ==>
    ?sb. step_inst_base b s = OK sb
Proof
  rpt strip_tac >>
  qspecl_then [`b`, `sa`, `sab`, `s`] mp_tac step_inst_base_ok_transfer >>
  simp[] >> disch_then irule >>
  (* operand values preserved: sa -> s *)
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `op` >> simp[eval_operand_def]
      >- (rename1 `Var n` >>
          qspecl_then [`fuel`, `ctx`, `a`, `s`, `sa`] mp_tac
            step_preserves_non_output_vars >> simp[] >>
          disch_then (qspec_then `n` mp_tac) >>
          impl_tac >- (gvs[DISJOINT_DEF, EXTENSION] >>
            metis_tac[var_mem_operand_vars, MEM]) >>
          simp[])
      >> (qspecl_then [`fuel`, `ctx`, `a`, `s`, `sa`] mp_tac
            step_preserves_labels >> simp[])) >>
  `sa.vs_prev_bb = s.vs_prev_bb` by
    (qspecl_then [`fuel`, `ctx`, `a`, `s`, `sa`] mp_tac
       step_preserves_control_flow >> simp[]) >>
  `sa.vs_params = s.vs_params` by
    (qspecl_then [`fuel`, `ctx`, `a`, `s`, `sa`] mp_tac
       step_preserves_params >> simp[]) >>
  simp[] >>
  (* RETURNDATACOPY: vs_returndata preserved *)
  strip_tac >>
  Cases_on `is_alloca_op a.inst_opcode`
  >- (drule_all step_alloca_preserves >> simp[])
  >>
  (qspecl_then [`fuel`, `ctx`, `a`, `s`, `sa`] mp_tac
        write_effects_sound_returndata >> simp[] >>
      disch_then irule >>
      gvs[effects_independent_def] >>
      `Eff_RETURNDATA IN read_effects RETURNDATACOPY` by EVAL_TAC >>
      metis_tac[IN_DISJOINT])
QED

(* Forward transfer for ext: a succeeds on sb given a succeeded on s,
   where b modified s to sb but b's outputs are disjoint from a's operands.
   Works even when a is INVOKE (uses step_inst_ok_frame).

   Case 1 (a=INVOKE): b is pure (empty effects), so sb = s or sb = update_var.
     Use step_inst_ok_frame to transfer INVOKE across the update.
   Case 2 (a≠INVOKE, b=INVOKE): a is pure, use pure_inst_transfer_across.
   Case 3 (a≠INVOKE, b≠INVOKE): delegate to non-ext step_ok_transfer_forward. *)

Theorem step_inst_ok_frame_fold[local]:
  !pairs fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    DISJOINT (set (MAP FST pairs)) (set (operand_vars inst.inst_operands)) /\
    DISJOINT (set (inst_defs inst)) (set (MAP FST pairs)) ==>
    step_inst fuel ctx inst
      (FOLDL (\st (out,value). update_var out value st) s pairs) =
    OK (FOLDL (\st (out,value). update_var out value st) s' pairs)
Proof
  Induct_on `pairs` >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum irule >>
  conj_tac
  >- (irule step_inst_ok_frame >> simp[] >>
      gvs[DISJOINT_DEF, EXTENSION, inst_defs_def] >>
      metis_tac[var_mem_operand_vars, MEM]) >>
  gvs[DISJOINT_DEF, EXTENSION]
QED

(* Helper: a_invoke case *)
Triviality step_ok_transfer_forward_ext_invoke:
  !fuel ctx a b s sa sb.
    a.inst_opcode = INVOKE /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b s = OK sb /\
    ~is_terminator b.inst_opcode /\
    ~is_alloca_op b.inst_opcode /\
    ~is_ext_call_op b.inst_opcode /\
    DISJOINT (set b.inst_outputs) (set (operand_vars a.inst_operands)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b)) /\
    effects_independent a.inst_opcode b.inst_opcode /\
    inst_wf b ==>
    ?sba. step_inst fuel ctx a sb = OK sba
Proof
  rpt strip_tac >>
  `b.inst_opcode <> INVOKE` by (
    spose_not_then strip_assume_tac >>
    gvs[EVAL ``effects_independent INVOKE INVOKE``]) >>
  `write_effects b.inst_opcode = {} /\ read_effects b.inst_opcode = {}` by
    metis_tac[effects_independent_invoke_empty] >>
  fs[step_inst_non_invoke] >>
  qspecl_then [`b`, `s`, `sb`] mp_tac pure_step_structure >> simp[] >>
  strip_tac >> gvs[] >>
  qexists_tac `FOLDL (\st (out,value). update_var out value st) sa pairs` >>
  irule step_inst_ok_frame_fold >> simp[] >>
  gvs[inst_defs_def, DISJOINT_DEF, EXTENSION]
QED

(* Helper: a_not_invoke case *)
Triviality step_ok_transfer_forward_ext_non_invoke:
  !fuel ctx a b s sa sb.
    a.inst_opcode <> INVOKE /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b s = OK sb /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    ~is_alloca_op a.inst_opcode /\ ~is_alloca_op b.inst_opcode /\
    ~is_ext_call_op a.inst_opcode /\
    ~is_ext_call_op b.inst_opcode /\
    DISJOINT (set b.inst_outputs) (set (operand_vars a.inst_operands)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b)) /\
    effects_independent a.inst_opcode b.inst_opcode /\
    inst_wf b ==>
    ?sba. step_inst fuel ctx a sb = OK sba
Proof
  rpt strip_tac >>
  Cases_on `b.inst_opcode = INVOKE`
  >- (
    `effects_independent INVOKE a.inst_opcode` by
      metis_tac[effects_independent_sym] >>
    `write_effects a.inst_opcode = {} /\ read_effects a.inst_opcode = {}` by
      metis_tac[effects_independent_invoke_empty] >>
    `step_inst_base a s = OK sa` by gvs[step_inst_non_invoke] >>
    qspecl_then [`fuel`, `ctx`, `a`, `b`, `s`, `sa`, `sb`] mp_tac
      pure_inst_transfer_across >> simp[] >>
    strip_tac >> qexists `sba` >> gvs[step_inst_non_invoke])
  >> (
    `step_inst_base a s = OK sa` by gvs[step_inst_non_invoke] >>
    `step_inst_base b s = OK sb` by gvs[step_inst_non_invoke] >>
    qspecl_then [`fuel`, `ctx`, `b`, `a`, `s`, `sb`, `sa`] mp_tac
      step_ok_transfer_forward >>
    simp[] >>
    (impl_tac >- metis_tac[effects_independent_sym]) >>
    strip_tac >>
    qexists `sab` >> gvs[step_inst_non_invoke])
QED

(* Main theorem: combines both cases *)
Triviality step_ok_transfer_forward_ext:
  !fuel ctx a b s sa sb.
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b s = OK sb /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    ~is_alloca_op a.inst_opcode /\ ~is_alloca_op b.inst_opcode /\
    ~is_ext_call_op a.inst_opcode /\
    ~is_ext_call_op b.inst_opcode /\
    DISJOINT (set b.inst_outputs) (set (operand_vars a.inst_operands)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b)) /\
    effects_independent a.inst_opcode b.inst_opcode /\
    inst_wf b ==>
    ?sba. step_inst fuel ctx a sb = OK sba
Proof
  rpt strip_tac >>
  Cases_on `a.inst_opcode = INVOKE`
  >- (irule step_ok_transfer_forward_ext_invoke >> metis_tac[])
  >> (irule step_ok_transfer_forward_ext_non_invoke >> metis_tac[])
QED

(* The ext swap: given ext_bi_independent, inst_wf, and a;b succeeds OK,
   then b;a also succeeds OK with the same final state.
   Split into non-INVOKE and INVOKE helpers to keep each proof manageable. *)

(* Helper: non-INVOKE b case *)
Triviality step_swap_ok_ext_non_invoke:
  !fuel ctx a b s sa sab.
    ext_bi_independent a b /\ inst_wf a /\ inst_wf b /\
    b.inst_opcode <> INVOKE /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rpt strip_tac >>
  gvs[ext_bi_independent_def] >>
  `step_inst_base b sa = OK sab` by gvs[step_inst_non_invoke] >>
  (* Backward: b succeeds on s *)
  qspecl_then [`fuel`,`ctx`,`a`,`b`,`s`,`sa`,`sab`] mp_tac
    step_ok_transfer_backward_ext >>
  (impl_tac >- gvs[inst_defs_def, inst_uses_def]) >> strip_tac >>
  `step_inst fuel ctx b s = OK sb` by gvs[step_inst_non_invoke] >>
  (* Forward: a succeeds on sb *)
  qspecl_then [`fuel`,`ctx`,`a`,`b`,`s`,`sa`,`sb`] mp_tac
    step_ok_transfer_forward_ext >>
  (impl_tac >- gvs[inst_defs_def, inst_uses_def]) >> strip_tac >>
  qexists_tac `sb` >> simp[] >>
  (* Equality: sab = sba *)
  `sab = sba` suffices_by simp[] >>
  qspecl_then [`fuel`,`ctx`,`a`,`b`,`s`,`sa`,`sb`,`sab`,`sba`] mp_tac
    independent_commute_eq_ext >>
  (impl_tac >- gvs[inst_defs_def, inst_uses_def]) >> simp[]
QED

(* Helper: invert INVOKE framing through an arbitrary finite sequence of
   fresh output updates.  This is the inverse boundary needed by
   pure_step_structure consumers. *)
Theorem step_inst_invoke_unframe_fold[local]:
  !pairs fuel ctx b s sab.
    b.inst_opcode = INVOKE /\
    DISJOINT (set (MAP FST pairs))
             (set (operand_vars b.inst_operands)) /\
    DISJOINT (set (MAP FST pairs)) (set b.inst_outputs) /\
    step_inst fuel ctx b
      (FOLDL (\st (out,value). update_var out value st) s pairs) = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         sab = FOLDL (\st (out,value). update_var out value st) sb pairs
Proof
  Induct_on `pairs` >- simp[] >>
  rpt gen_tac >> PairCases_on `h` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then
    [`fuel`, `ctx`, `b`, `update_var h0 h1 s`, `sab`] mp_tac) >>
  (impl_tac >- gvs[DISJOINT_DEF, EXTENSION]) >>
  strip_tac >>
  qspecl_then [`fuel`, `ctx`, `b`, `s`, `h0`, `h1`] mp_tac
    step_inst_invoke_frame >>
  (impl_tac
   >- (simp[] >> gvs[DISJOINT_DEF, EXTENSION] >>
       metis_tac[var_mem_operand_vars, MEM])) >>
  Cases_on `step_inst fuel ctx b s` >> gvs[] >>
  metis_tac[]
QED

(* Fold-level INVOKE swap.  The hypotheses deliberately match the witness
   supplied by pure_step_structure, so callers never reason about output
   cardinality. *)
Triviality step_swap_ok_ext_invoke_fold:
  !pairs fuel ctx a b s sab.
    MAP FST pairs = a.inst_outputs /\
    step_inst_base a s =
      OK (FOLDL (\st (out,value). update_var out value st) s pairs) /\
    a.inst_opcode <> INVOKE /\
    write_effects a.inst_opcode = {} /\
    read_effects a.inst_opcode = {} /\
    inst_wf a /\ inst_wf b /\
    b.inst_opcode = INVOKE /\
    ~is_terminator a.inst_opcode /\ ~is_terminator b.inst_opcode /\
    ~is_alloca_op a.inst_opcode /\ ~is_alloca_op b.inst_opcode /\
    ~is_ext_call_op a.inst_opcode /\ ~is_ext_call_op b.inst_opcode /\
    DISJOINT (set (inst_defs a)) (set (inst_uses b)) /\
    DISJOINT (set (inst_defs b)) (set (inst_uses a)) /\
    DISJOINT (set (inst_defs a)) (set (inst_defs b)) /\
    effects_independent a.inst_opcode b.inst_opcode /\
    abort_compatible a.inst_opcode b.inst_opcode /\
    step_inst fuel ctx a s =
      OK (FOLDL (\st (out,value). update_var out value st) s pairs) /\
    step_inst fuel ctx b
      (FOLDL (\st (out,value). update_var out value st) s pairs) = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rpt strip_tac >>
  qspecl_then [`pairs`, `fuel`, `ctx`, `b`, `s`, `sab`] mp_tac
    step_inst_invoke_unframe_fold >>
  (impl_tac
   >- (simp[] >> gvs[inst_defs_def, inst_uses_def, DISJOINT_DEF, EXTENSION])) >>
  strip_tac >>
  qspecl_then [`fuel`, `ctx`, `a`, `b`, `s`,
               `FOLDL (\st (out,value). update_var out value st) s pairs`,
               `sb`] mp_tac pure_inst_transfer_across >>
  (impl_tac
   >- gvs[inst_defs_def, inst_uses_def, is_terminator_def]) >>
  strip_tac >>
  `step_inst fuel ctx a sb = OK sba` by gvs[step_inst_non_invoke] >>
  qexists_tac `sb` >> simp[] >>
  `sab = sba` suffices_by simp[] >>
  irule independent_commute_eq_ext >>
  qexistsl_tac
    [`ctx`, `fuel`, `a`, `b`, `s`,
     `FOLDL (\st (out,value). update_var out value st) s pairs`, `sb`] >>
  gvs[]
QED

(* Helper: INVOKE b case. a must be pure (invoke_implies_pure). *)
Triviality step_swap_ok_ext_invoke:
  !fuel ctx a b s sa sab.
    ext_bi_independent a b /\ inst_wf a /\ inst_wf b /\
    b.inst_opcode = INVOKE /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rpt strip_tac >>
  gvs[ext_bi_independent_def] >>
  `effects_independent INVOKE a.inst_opcode` by
    metis_tac[effects_independent_sym] >>
  drule invoke_implies_pure >> strip_tac >>
  `step_inst_base a s = OK sa` by gvs[step_inst_non_invoke] >>
  qspecl_then [`a`, `s`, `sa`] mp_tac pure_step_structure >>
  simp[] >> strip_tac >> gvs[] >>
  qspecl_then [`pairs`, `fuel`, `ctx`, `a`, `b`, `s`, `sab`] mp_tac
    step_swap_ok_ext_invoke_fold >>
  gvs[inst_defs_def, inst_uses_def]
QED

(* Under ext bilateral independence and well-formedness, swapping the
   order of two consecutive OK steps produces the same final state. *)
Theorem step_swap_ok_ext:
  !fuel ctx a b s sa sab.
    ext_bi_independent a b /\
    inst_wf a /\ inst_wf b /\
    step_inst fuel ctx a s = OK sa /\
    step_inst fuel ctx b sa = OK sab ==>
    ?sb. step_inst fuel ctx b s = OK sb /\
         step_inst fuel ctx a sb = OK sab
Proof
  rpt strip_tac >>
  Cases_on `b.inst_opcode = INVOKE`
  >- (drule_all step_swap_ok_ext_invoke >> simp[])
  >> (drule_all step_swap_ok_ext_non_invoke >> simp[])
QED

(* Adjacent swap in run_insts context, ext version *)
Triviality run_insts_swap_adjacent_ok_ext:
  !fuel ctx prefix a b suffix s s_result.
    ext_bi_independent a b /\ inst_wf a /\ inst_wf b /\
    run_insts fuel ctx (prefix ++ [a; b] ++ suffix) s = OK s_result ==>
    run_insts fuel ctx (prefix ++ [b; a] ++ suffix) s = OK s_result
Proof
  rpt strip_tac >>
  gvs[run_insts_append] >>
  Cases_on `run_insts fuel ctx prefix s` >>
  gvs[run_insts_def, AllCaseEqs()] >>
  Cases_on `step_inst fuel ctx a v` >>
  gvs[run_insts_def, AllCaseEqs()] >>
  Cases_on `step_inst fuel ctx b v'` >>
  gvs[run_insts_def, AllCaseEqs()] >>
  drule_all step_swap_ok_ext >> strip_tac >>
  simp[]
QED

(* If every element in prefix is ext-bi-independent with x and all are
   well-formed, bubble x from after the prefix to the front,
   preserving the OK result. Allows INVOKE. *)
Theorem run_insts_bubble_to_front_ext:
  !prefix fuel ctx x suffix s r.
    EVERY (ext_bi_independent x) prefix /\
    EVERY inst_wf (x :: prefix) /\
    run_insts fuel ctx (prefix ++ [x] ++ suffix) s = OK r ==>
    run_insts fuel ctx ([x] ++ prefix ++ suffix) s = OK r
Proof
  Induct_on `prefix` >> simp[] >>
  rpt strip_tac >> gvs[EVERY_DEF] >>
  gvs[run_insts_def, AllCaseEqs()] >>
  rename1 `step_inst fuel ctx h s = OK sh` >>
  (* Apply IH to sh *)
  first_x_assum (qspecl_then [`fuel`, `ctx`, `x`, `suffix`, `sh`, `r`] mp_tac) >>
  simp[] >> strip_tac >>
  rename1 `step_inst fuel ctx x sh = OK sx` >>
  (* Swap h and x: step_inst h s = OK sh, step_inst x sh = OK sx *)
  `ext_bi_independent h x` by metis_tac[ext_bi_independent_sym] >>
  qspecl_then [`fuel`, `ctx`, `h`, `x`, `s`, `sh`, `sx`] mp_tac
    step_swap_ok_ext >> simp[] >> strip_tac >>
  qexists `sb` >> simp[]
QED

(* ===== Pairwise ext independence ===== *)

Definition pairwise_ext_bi_independent_def:
  pairwise_ext_bi_independent [] = T /\
  pairwise_ext_bi_independent (x :: rest) =
    (EVERY (ext_bi_independent x) rest /\ pairwise_ext_bi_independent rest)
End

Triviality pairwise_ext_bi_independent_perm:
  !l1 l2. PERM l1 l2 ==>
    (pairwise_ext_bi_independent l1 ==> pairwise_ext_bi_independent l2) /\
    (!x. EVERY (ext_bi_independent x) l1 ==> EVERY (ext_bi_independent x) l2)
Proof
  ho_match_mp_tac PERM_IND >>
  rw[pairwise_ext_bi_independent_def, EVERY_DEF] >>
  gvs[pairwise_ext_bi_independent_def, EVERY_DEF] >>
  metis_tac[ext_bi_independent_sym]
QED

Triviality run_insts_perm_ok_ext_strong:
  !l1 l2.
    PERM l1 l2 ==>
    (pairwise_ext_bi_independent l1 ==> pairwise_ext_bi_independent l2) /\
    (!x. EVERY (ext_bi_independent x) l1 ==> EVERY (ext_bi_independent x) l2) /\
    (EVERY inst_wf l1 ==> EVERY inst_wf l2) /\
    (!fuel ctx s s_result.
       pairwise_ext_bi_independent l1 /\
       EVERY inst_wf l1 /\
       run_insts fuel ctx l1 s = OK s_result ==>
       run_insts fuel ctx l2 s = OK s_result)
Proof
  ho_match_mp_tac PERM_IND >>
  rw[pairwise_ext_bi_independent_def, EVERY_DEF] >>
  gvs[pairwise_ext_bi_independent_def, EVERY_DEF] >|
  [gvs[run_insts_def] >>
     Cases_on `step_inst fuel ctx x s` >> gvs[] >>
     res_tac >> gvs[],
   metis_tac[ext_bi_independent_sym],
   gvs[run_insts_def, AllCaseEqs()] >>
     rename1 `step_inst _ _ x s = OK sx` >>
     rename1 `step_inst _ _ y sx = OK sy` >>
     qspecl_then [`fuel`, `ctx`, `x`, `y`, `s`, `sx`, `sy`] mp_tac
       step_swap_ok_ext >> simp[] >> strip_tac >>
     qexists `sb` >> simp[] >> res_tac]
QED

(* Extended pairwise independence version: pairwise ext-bi-independent
   and well-formed instructions produce the same OK result under any
   permutation (allows INVOKE). *)
Theorem run_insts_perm_ok_ext:
  !l1 l2.
    PERM l1 l2 ==>
    !fuel ctx s s_result.
      pairwise_ext_bi_independent l1 /\
      EVERY inst_wf l1 /\
      run_insts fuel ctx l1 s = OK s_result ==>
      run_insts fuel ctx l2 s = OK s_result
Proof
  metis_tac[run_insts_perm_ok_ext_strong]
QED

(* ===== Pairwise independence ===== *)

(* All pairs in a list are bi-independent *)
Definition pairwise_bi_independent_def:
  pairwise_bi_independent [] = T /\
  pairwise_bi_independent (x :: rest) =
    (EVERY (bi_independent x) rest /\ pairwise_bi_independent rest)
End

Triviality pairwise_bi_independent_cons:
  !x rest.
    pairwise_bi_independent (x :: rest) <=>
    EVERY (bi_independent x) rest /\ pairwise_bi_independent rest
Proof
  simp[pairwise_bi_independent_def]
QED

Triviality pairwise_bi_independent_swap:
  !x y rest.
    pairwise_bi_independent (x :: y :: rest) ==>
    pairwise_bi_independent (y :: x :: rest)
Proof
  rw[pairwise_bi_independent_def, EVERY_MEM] >>
  metis_tac[bi_independent_sym]
QED

(* Key: pairwise bi-independence is preserved by PERM.
   Proved by PERM induction on the strengthened property
   that also preserves EVERY (bi_independent x) for all x. *)
Triviality pairwise_bi_independent_perm:
  !l1 l2. PERM l1 l2 ==>
    pairwise_bi_independent l1 ==> pairwise_bi_independent l2
Proof
  `!l1 l2. PERM l1 l2 ==>
     (pairwise_bi_independent l1 ==> pairwise_bi_independent l2) /\
     (!x. EVERY (bi_independent x) l1 ==> EVERY (bi_independent x) l2)`
    suffices_by metis_tac[] >>
  ho_match_mp_tac PERM_IND >> rpt conj_tac >>
  simp[pairwise_bi_independent_def, EVERY_DEF] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[bi_independent_sym]
QED

(* ===== Main OK-case permutation theorem ===== *)

(* Strengthened version carrying pairwise preservation for the trans case *)
Triviality run_insts_perm_ok_strong:
  !l1 l2.
    PERM l1 l2 ==>
    (pairwise_bi_independent l1 ==> pairwise_bi_independent l2) /\
    (!x. EVERY (bi_independent x) l1 ==> EVERY (bi_independent x) l2) /\
    (!fuel ctx s s_result.
       pairwise_bi_independent l1 /\
       run_insts fuel ctx l1 s = OK s_result ==>
       run_insts fuel ctx l2 s = OK s_result)
Proof
  ho_match_mp_tac PERM_IND >>
  rw[pairwise_bi_independent_def, EVERY_DEF] >>
  gvs[pairwise_bi_independent_def, EVERY_DEF]
  >- (gvs[run_insts_def] >>
      Cases_on `step_inst fuel ctx x s` >> gvs[] >>
      res_tac >> gvs[])
  >- metis_tac[bi_independent_sym]
  >> gvs[run_insts_def, AllCaseEqs()] >>
  drule_all step_swap_ok >> strip_tac >> simp[]
QED

(* Pairwise bi-independent instructions produce the same OK result
   under any permutation. *)
Theorem run_insts_perm_ok:
  !l1 l2.
    PERM l1 l2 ==>
    !fuel ctx s s_result.
      pairwise_bi_independent l1 /\
      run_insts fuel ctx l1 s = OK s_result ==>
      run_insts fuel ctx l2 s = OK s_result
Proof
  metis_tac[run_insts_perm_ok_strong]
QED

(* ===== Topological ordering equivalence ===== *)

(* Two permutations that are both topologically sorted w.r.t. a relation
   dep (where incomparable elements are bi_independent) produce the same
   run_insts OK result.

   Proof by strong induction on LENGTH l2. The first element x of l2
   has no deps (topo_sorted), and nothing in l1's prefix before x
   depends on x (topo_sorted l1) or is depended on by x (topo_sorted l2
   with x first). So x is bi_independent with the entire prefix.
   bubble_to_front moves x to the front. Then IH on the tails. *)

Definition topo_sorted_def:
  topo_sorted dep l <=>
    !i j. i < j /\ j < LENGTH l ==> ~dep (EL i l) (EL j l)
End

(* Two topologically sorted permutations of the same instruction list
   (w.r.t. dep, where incomparable elements are bi_independent)
   produce the same run_insts OK result, provided all elements are distinct. *)
(* EL in the list without x matches EL at a shifted index in the
   list with x inserted, for indices before the insertion point. *)
Theorem el_delete_map:
  !n prefix x suffix.
    n < LENGTH prefix + LENGTH suffix ==>
    EL n (prefix ++ suffix) =
    EL (if n < LENGTH prefix then n else SUC n)
       (prefix ++ [x] ++ suffix)
Proof
  rpt strip_tac >> Cases_on `n < LENGTH prefix`
  >- simp[EL_APPEND1]
  >> `LENGTH prefix <= n` by simp[] >>
     simp[EL_APPEND2] >>
     `LENGTH prefix <= SUC n` by simp[] >>
     simp[EL_APPEND2] >>
     `SUC n - LENGTH prefix = SUC (n - LENGTH prefix)` by simp[] >>
     `SUC n - (LENGTH prefix + 1) = n - LENGTH prefix` by simp[] >>
     simp[]
QED

(* Removing an element from a topologically sorted list preserves
   the topological ordering. *)
Theorem topo_sorted_delete:
  !dep prefix x suffix.
    topo_sorted dep (prefix ++ [x] ++ suffix) ==>
    topo_sorted dep (prefix ++ suffix)
Proof
  rw[topo_sorted_def] >> rpt strip_tac >>
  `i < LENGTH prefix + LENGTH suffix` by simp[] >>
  `j < LENGTH prefix + LENGTH suffix` by simp[] >>
  `EL i (prefix ++ suffix) =
     EL (if i < LENGTH prefix then i else SUC i)
        (prefix ++ [x] ++ suffix)` by
    (irule el_delete_map >> simp[]) >>
  `EL j (prefix ++ suffix) =
     EL (if j < LENGTH prefix then j else SUC j)
        (prefix ++ [x] ++ suffix)` by
    (irule el_delete_map >> simp[]) >>
  first_x_assum (qspecl_then
    [`if i < LENGTH prefix then i else SUC i`,
     `if j < LENGTH prefix then j else SUC j`] mp_tac) >>
  rpt (COND_CASES_TAC >> gvs[])
QED

(* The tail of a topologically sorted list is also topologically sorted. *)
Theorem topo_sorted_tail:
  !dep x rest. topo_sorted dep (x :: rest) ==> topo_sorted dep rest
Proof
  rw[topo_sorted_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]
QED

(* If prefix++[x]++suffix is a permutation of x::rest, then
   prefix++suffix is a permutation of rest. *)
Theorem perm_cons_delete:
  !x rest prefix suffix.
    PERM (prefix ++ [x] ++ suffix) (x :: rest) ==>
    PERM (prefix ++ suffix) rest
Proof
  rpt strip_tac >>
  `prefix ++ [x] ++ suffix = prefix ++ x :: suffix` by simp[] >>
  gvs[] >>
  full_simp_tac std_ss [PERM_FUN_APPEND_CONS] >>
  gvs[PERM_CONS_IFF]
QED

Triviality prefix_bi_independent:
  !prefix x suffix rest dep.
    PERM (prefix ++ [x] ++ suffix) (x :: rest) /\
    ALL_DISTINCT (prefix ++ [x] ++ suffix) /\
    topo_sorted dep (prefix ++ [x] ++ suffix) /\
    topo_sorted dep (x :: rest) /\
    (!x' y. MEM x' (prefix ++ [x] ++ suffix) /\
            MEM y (prefix ++ [x] ++ suffix) /\
            x' <> y /\ ~dep x' y /\ ~dep y x' ==>
            bi_independent x' y) ==>
    EVERY (bi_independent x) prefix
Proof
  rw[EVERY_MEM] >>
  `?k. k < LENGTH prefix /\ e = EL k prefix` by metis_tac[MEM_EL] >> gvs[] >>
  `ALL_DISTINCT (x :: rest)` by metis_tac[ALL_DISTINCT_PERM] >>
  `~dep (EL k prefix) x` by
    (qpat_x_assum `topo_sorted _ (prefix ++ _ ++ _)` mp_tac >>
     rw[topo_sorted_def] >>
     first_x_assum (qspecl_then [`k`, `LENGTH prefix`] mp_tac) >>
     simp[EL_APPEND1, EL_APPEND2]) >>
  `MEM (EL k prefix) (x :: rest)` by
    (irule (iffLR PERM_MEM_EQ) >>
     qexists_tac `prefix ++ [x] ++ suffix` >>
     simp[MEM_APPEND, MEM_EL]) >>
  `EL k prefix <> x` by
    (gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_EL]) >>
  `MEM (EL k prefix) rest` by gvs[MEM] >>
  `~dep x (EL k prefix)` by
    (qpat_x_assum `topo_sorted _ (x :: rest)` mp_tac >>
     rw[topo_sorted_def] >>
     `?m. m < LENGTH rest /\ EL k prefix = EL m rest` by metis_tac[MEM_EL] >>
     first_x_assum (qspecl_then [`0`, `SUC m`] mp_tac) >> simp[]) >>
  first_x_assum irule >>
  simp[MEM_APPEND]
QED

Triviality run_insts_topo_equiv_aux:
  !n l1 l2 dep fuel ctx s r.
    LENGTH l2 = n /\
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> bi_independent x y) /\
    run_insts fuel ctx l1 s = OK r ==>
    run_insts fuel ctx l2 s = OK r
Proof
  Induct_on `n` >> rpt strip_tac
  >- gvs[PERM_NIL, run_insts_def]
  >> Cases_on `l2` >- gvs[]
  >> rename1 `PERM l1 (x :: rest)` >>
  `LENGTH rest = n` by gvs[] >>
  (* Find x in l1 *)
  `MEM x l1` by metis_tac[PERM_MEM_EQ, MEM] >>
  `?prefix suffix. l1 = prefix ++ [x] ++ suffix /\ ~MEM x prefix`
    by metis_tac[MEM_SPLIT_APPEND_first] >>
  qpat_x_assum `_ = _ ++ [_] ++ _` SUBST_ALL_TAC >>
  (* Now l1 is substituted but universal hypothesis keeps MEM _ (prefix ++ [x] ++ suffix) form *)
  `ALL_DISTINCT (x :: rest)` by metis_tac[ALL_DISTINCT_PERM] >>
  (* x is bi_independent with all prefix elements *)
  `EVERY (bi_independent x) prefix` by
    metis_tac[prefix_bi_independent] >>
  (* Bubble x to front *)
  drule run_insts_bubble_to_front >>
  disch_then (qspecl_then [`fuel`, `ctx`, `suffix`, `s`, `r`] mp_tac) >>
  simp[] >> strip_tac >>
  (* Now: run_insts (x :: prefix ++ suffix) = OK r *)
  qpat_x_assum `!x' y. MEM x' _ /\ _ ==> _`
    (fn th => gvs[run_insts_def, AllCaseEqs()] >> assume_tac th) >>
  rename1 `step_inst fuel ctx x s = OK s'` >>
  (* Apply IH to tails *)
  first_x_assum irule >>
  simp[] >>
  qexistsl_tac [`dep`, `prefix ++ suffix`] >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[MEM_APPEND])
  >- gvs[ALL_DISTINCT_APPEND]
  >- simp[]
  >- metis_tac[perm_cons_delete]
  >- metis_tac[topo_sorted_delete]
  >- metis_tac[topo_sorted_tail]
QED

Theorem run_insts_topo_equiv:
  !l1 l2 dep fuel ctx s r.
    PERM l1 l2 /\ ALL_DISTINCT l1 /\
    topo_sorted dep l1 /\ topo_sorted dep l2 /\
    (!x y. MEM x l1 /\ MEM y l1 /\ x <> y /\
           ~dep x y /\ ~dep y x ==> bi_independent x y) /\
    run_insts fuel ctx l1 s = OK r ==>
    run_insts fuel ctx l2 s = OK r
Proof
  rpt strip_tac >> irule run_insts_topo_equiv_aux >>
  simp[] >> qexistsl_tac [`dep`, `l1`] >> simp[]
QED

(* ===== flip_operands preserves step_inst semantics ===== *)

(*
 * For commutative ops (ADD,MUL,EQ,AND,OR,XOR): swapping operands
 * applies the commutative binary function to swapped args — same result.
 * For comparators (GT<->LT, SGT<->SLT): swapping operands AND
 * flipping opcode: f(a,b) = g(b,a) where g is the flipped comparison.
 *)

(* exec_pure2 with swapped operands: f(op2,op1) = g(op1,op2) *)
Triviality exec_pure2_swap:
  !f g (i:instruction) st op1 op2.
    (!x y. f y x = g x y) /\ i.inst_operands = [op1; op2] ==>
    exec_pure2 f (i with inst_operands := [op2; op1]) st =
    exec_pure2 g i st
Proof
  rw[exec_pure2_def] >>
  Cases_on `eval_operand op1 st` >> Cases_on `eval_operand op2 st` >> gvs[]
QED

(* exec_pure2 ignores inst_opcode and inst_id *)
Triviality exec_pure2_opcode_irrel[simp]:
  exec_pure2 f (i with inst_opcode := op) st = exec_pure2 f i st
Proof rw[exec_pure2_def]
QED

(* Helpers to avoid 92-way case splits *)
Triviality commutative_not_comparator:
  !op. is_commutative op ==> ~is_comparator op
Proof Cases >> EVAL_TAC
QED

Triviality commutative_cases:
  !op. is_commutative op ==>
    op = ADD \/ op = MUL \/ op = EQ \/ op = AND \/ op = OR \/ op = XOR
Proof Cases >> EVAL_TAC
QED

Triviality comparator_cases:
  !op. is_comparator op ==> op = GT \/ op = LT \/ op = SGT \/ op = SLT
Proof Cases >> EVAL_TAC
QED

val comm_lemmas =
  [wordsTheory.WORD_ADD_COMM, wordsTheory.WORD_MULT_COMM,
   wordsTheory.WORD_AND_COMM, wordsTheory.WORD_OR_COMM,
   wordsTheory.WORD_XOR_COMM,
   arithmeticTheory.GREATER_DEF, wordsTheory.WORD_GREATER];

fun flip_commutative_finish_tac () =
  simp[] >> irule exec_pure2_swap >> rw comm_lemmas >> rw[EQ_SYM_EQ]

(*
 * flip_operands preserves step_inst_base.
 * For commutative ops: operands swapped, opcode same -> exec_pure2_swap.
 * For comparators: operands swapped AND opcode flipped -> case-by-case.
 *)
Triviality flip_commutative:
  !i st op1 op2.
    is_commutative i.inst_opcode /\ i.inst_operands = [op1; op2] ==>
    step_inst_base (flip_operands i) st = step_inst_base i st
Proof
  rpt strip_tac >>
  drule commutative_cases >> drule commutative_not_comparator >>
  strip_tac >> strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[flip_operands_def] >>
  ASM_REWRITE_TAC[step_inst_base_def] >|
  [flip_commutative_finish_tac (), flip_commutative_finish_tac (),
   flip_commutative_finish_tac (), flip_commutative_finish_tac (),
   flip_commutative_finish_tac (), flip_commutative_finish_tac ()]
QED

Triviality flip_comparator:
  !i st op1 op2.
    is_comparator i.inst_opcode /\ i.inst_operands = [op1; op2] ==>
    step_inst_base (flip_operands i) st = step_inst_base i st
Proof
  rpt strip_tac >>
  drule comparator_cases >> strip_tac >> gvs[] >>
  ASM_REWRITE_TAC[flip_operands_def, is_comparator_def,
                  flip_comparison_opcode_def] >>
  simp[LET_THM] >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  PURE_REWRITE_TAC[venomInstTheory.instruction_accfupds,
                   combinTheory.K_THM] >>
  BETA_TAC >> ASM_REWRITE_TAC[] >>
  PURE_REWRITE_TAC[venomInstTheory.opcode_case_def,
                   exec_pure2_opcode_irrel] >>
  irule exec_pure2_swap >> rw comm_lemmas
QED

(* Flipping operand order (and comparison opcode) preserves step_inst_base
   for flippable (commutative arithmetic and comparison) opcodes. *)
Theorem flip_operands_step_inst_base:
  !i st. is_flippable i.inst_opcode ==>
    step_inst_base (flip_operands i) st = step_inst_base i st
Proof
  rpt strip_tac >>
  Cases_on `i.inst_operands` >- simp[flip_operands_def] >>
  Cases_on `t` >- simp[flip_operands_def] >>
  Cases_on `t'`
  >- (rename1 `i.inst_operands = [op1; op2]` >>
      gvs[is_flippable_def] >>
      metis_tac[flip_commutative, flip_comparator])
  >> simp[flip_operands_def]
QED

Triviality flippable_not_invoke:
  !op. is_flippable op ==> op <> INVOKE
Proof Cases >> EVAL_TAC
QED

Triviality flip_opcode_not_invoke:
  !i. is_flippable i.inst_opcode ==>
    (flip_operands i).inst_opcode <> INVOKE
Proof
  rpt strip_tac >>
  imp_res_tac flippable_not_invoke >>
  `?ops. i.inst_operands = ops` by simp[] >>
  Cases_on `ops` >> fs[flip_operands_def] >>
  Cases_on `t` >> fs[flip_operands_def] >>
  Cases_on `t'` >> fs[flip_operands_def] >>
  gvs[is_flippable_def] >>
  imp_res_tac commutative_not_comparator >> gvs[] >>
  gvs[is_comparator_def, flip_comparison_opcode_def]
QED

(* flip_operands preserves step_inst semantics for flippable opcodes. *)
Theorem flip_operands_step_inst:
  !fuel ctx i st. is_flippable i.inst_opcode ==>
    step_inst fuel ctx (flip_operands i) st = step_inst fuel ctx i st
Proof
  rpt strip_tac >>
  imp_res_tac flippable_not_invoke >>
  imp_res_tac flip_opcode_not_invoke >>
  simp[step_inst_non_invoke] >>
  irule flip_operands_step_inst_base >> simp[]
QED

(* ===== NoFail + non-terminator: step_inst_base never Halt/Abort ===== *)

(* Pre-compute per-opcode step_inst_base clauses and no-halt-abort theorems.
   Each exec helper (pure1/2/3, read0/1, write2, alloca, ext_call, create,
   delegatecall) only returns OK or Error — never Halt or Abort. *)

val nf_nt_ops = List.filter (fn op_tm =>
  let val nf = EVAL ``opcode_fail_class ^op_tm = NoFail``
      val nt = EVAL ``~is_terminator ^op_tm``
  in aconv (rhs (concl nf)) T andalso aconv (rhs (concl nt)) T end
) (TypeBase.constructors_of ``:opcode``);

val nfnt_clauses = map (fn op_tm =>
  SIMP_CONV (srw_ss()) [step_inst_base_def]
    (mk_comb(mk_comb(``step_inst_base``,
      ``inst with inst_opcode := ^op_tm``), ``st:venom_state``))
) nf_nt_ops;

val exec_helper_defs = [
  exec_pure1_def, exec_pure2_def, exec_pure3_def,
  exec_read0_def, exec_read1_def, exec_write2_def,
  exec_alloca_def, exec_ext_call_def, exec_create_def,
  exec_delegatecall_def, LET_THM, AllCaseEqs()];

val per_op_no_halt_abort = map (fn (op_tm, clause) =>
  prove(
    ``inst.inst_opcode = ^op_tm ==>
      (!h. step_inst_base inst st <> Halt h) /\
      (!a es. step_inst_base inst st <> Abort a es)``,
    strip_tac >>
    `inst with inst_opcode := ^op_tm = inst`
      by simp[instruction_component_equality] >>
    pop_assum (fn eq => ONCE_REWRITE_TAC [GSYM eq]) >>
    ONCE_REWRITE_TAC [clause] >> simp exec_helper_defs)
) (ListPair.zip(nf_nt_ops, nfnt_clauses));

val per_op_combined = LIST_CONJ per_op_no_halt_abort;

(* A NoFail non-terminator step_inst_base never produces Halt or Abort
   — only OK or Error outcomes remain. *)
Theorem step_inst_nofail_not_halt_abort:
  !inst s.
    opcode_fail_class inst.inst_opcode = NoFail /\
    ~is_terminator inst.inst_opcode ==>
    (!h. step_inst_base inst s <> Halt h) /\
    (!a es. step_inst_base inst s <> Abort a es)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode` >>
  simp[opcode_fail_class_def, is_terminator_def, per_op_combined]
QED


