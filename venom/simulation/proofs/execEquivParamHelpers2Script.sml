(*
 * Parameterized Execution Equivalence — Step Inst Helpers (Part 2)
 *
 * Remaining opcodes: selfdestruct, invalid, ext_call, delegatecall, create, alloca.
 * Depends on execEquivParamBase for core helpers.
 *)

Theory execEquivParamHelpers2
Ancestors
  execEquivParamBase
  execEquivParamDefs passSimulationDefs stateEquivProps execEquivProps
  stateEquiv venomInst venomExecSemantics venomState
Libs
  finite_mapTheory listTheory rich_listTheory

open execEquivParamLib

(* ML tactics (same as Helpers1) *)

fun vsr_eval_ops_tac () =
  `!op. MEM op inst.inst_operands ==>
     eval_operand op s1 = eval_operand op s2` by (
    rw[] >> vsr_irule vsr_eval_operand >> simp[] >> metis_tac[])

fun vsr_eval_rewrite_tac () =
  imp_res_tac vsr_R_ok_fields >> vsr_eval_ops_tac () >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >> ASM_REWRITE_TAC[] >> simp[]

(* ==========================================================================
   step_inst_base helpers — Part 2
   ========================================================================== *)

Theorem vsr_step_inst_selfdestruct:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = SELFDESTRUCT /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  rpt (CASE_TAC >> gvs[lift_result_def, halt_state_def]) >>
  vsr_terminal_tac ()
QED

Theorem vsr_step_inst_invalid:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = INVALID ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >>
  simp[step_inst_base_def, lift_result_def, halt_state_def, set_returndata_def] >>
  vsr_terminal_tac ()
QED

Theorem vsr_step_inst_call:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = CALL /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  fs[lift_result_def] >>
  vsr_irule vsr_exec_ext_call >> simp[]
QED

Theorem vsr_step_inst_staticcall:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = STATICCALL /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  Cases_on `t'` >> fs[lift_result_def] >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  fs[lift_result_def] >>
  vsr_irule vsr_exec_ext_call >> simp[]
QED

Theorem vsr_step_inst_ext_call:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [CALL;STATICCALL] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >- (irule vsr_step_inst_call >> simp[]) >>
  irule vsr_step_inst_staticcall >> simp[]
QED

Theorem vsr_step_inst_delegatecall:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = DELEGATECALL /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  Cases_on `t'` >> fs[lift_result_def] >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  fs[lift_result_def] >>
  vsr_irule vsr_exec_delegatecall >> simp[]
QED

Theorem vsr_step_inst_create1:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = CREATE /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  Cases_on `t` >> fs[lift_result_def] >>
  vsr_irule vsr_exec_create >> simp[]
QED

Theorem vsr_step_inst_create2:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = CREATE2 /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  TRY (CASE_TAC >> fs[lift_result_def]) >>
  Cases_on `t'` >> fs[lift_result_def] >>
  vsr_irule vsr_exec_create >> simp[]
QED

Theorem vsr_step_inst_create:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode [CREATE;CREATE2] /\
    (!x. MEM (Var x) inst.inst_operands ==> lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rw[] >- (irule vsr_step_inst_create1 >> simp[]) >>
  irule vsr_step_inst_create2 >> simp[]
QED

Theorem vsr_step_inst_alloca:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = ALLOCA ==>
    lift_result R_ok R_term R_term (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[step_inst_base_def] >>
  rpt (CASE_TAC >> gvs[lift_result_def]) >>
  vsr_irule vsr_exec_alloca >> simp[]
QED


Theorem vsr_step_inst_bump:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = BUMP /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term
      (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[] >> vsr_eval_rewrite_tac () >>
  Cases_on `inst.inst_operands` >- simp[lift_result_def] >>
  Cases_on `t` >- simp[lift_result_def] >>
  reverse (Cases_on `t'`) >-
    (rpt (BasicProvers.TOP_CASE_TAC >> gvs[lift_result_def])) >>
  Cases_on `inst.inst_outputs` >- simp[lift_result_def] >>
  Cases_on `t` >- simp[lift_result_def] >>
  reverse (Cases_on `t'`) >- simp[lift_result_def] >>
  Cases_on `eval_operand h s2` >> gvs[lift_result_def] >>
  Cases_on `eval_operand h' s2` >> gvs[lift_result_def] >>
  metis_tac[vsr_update_var_R_ok]
QED

(* Raw-FMP and hidden-parameter opcodes introduced with the extended state. *)
Theorem vsr_step_inst_fmp_opcode:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    MEM inst.inst_opcode
      [DALLOCA; GETFMP; SETFMP; INITIAL_FMP; BUMP; FMP_PARAM; RETPC_PARAM] /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term
      (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >> gvs[]
  >- (vsr_eval_rewrite_tac () >>
      rpt (CASE_TAC >> gvs[lift_result_def]) >>
      metis_tac[vsr_fmp_R_ok, vsr_update_var_R_ok])
  >- (vsr_eval_rewrite_tac () >>
      rpt (CASE_TAC >> gvs[lift_result_def]) >>
      metis_tac[vsr_update_var_R_ok])
  >- (vsr_eval_rewrite_tac () >>
      rpt (CASE_TAC >> gvs[lift_result_def]) >>
      metis_tac[vsr_fmp_R_ok])
  >- (vsr_eval_rewrite_tac () >>
      rpt (CASE_TAC >> gvs[lift_result_def]) >>
      metis_tac[vsr_update_var_R_ok])
  >- (irule vsr_step_inst_bump >> simp[])
  >- (vsr_eval_rewrite_tac () >>
      rpt (CASE_TAC >> gvs[lift_result_def]) >>
      metis_tac[vsr_update_var_R_ok])
  >- (vsr_eval_rewrite_tac () >>
      rpt (CASE_TAC >> gvs[lift_result_def]) >>
      metis_tac[vsr_update_var_R_ok])
QED


Theorem vsr_pack_dret_dynamic:
  !R_ok R_term cursor pairs s1 s2 p1 c1 t1 p2 c2 t2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    pack_dret_dynamic cursor pairs s1 = (p1,c1,t1) /\
    pack_dret_dynamic cursor pairs s2 = (p2,c2,t2) ==>
    p1 = p2 /\ c1 = c2 /\ R_ok t1 t2
Proof
  rpt gen_tac >>
  map_every qid_spec_tac
    [`cursor`, `s1`, `s2`, `p1`, `c1`, `t1`, `p2`, `c2`, `t2`] >>
  Induct_on `pairs`
  >- simp[pack_dret_dynamic_def]
  >> Cases_on `h` >> rpt strip_tac >>
  gvs[pack_dret_dynamic_def] >>
  qabbrev_tac
    `res1 = pack_dret_dynamic (cursor + n2w (ceil32 (w2n r))) pairs
       (mcopy (w2n cursor) (w2n q) (w2n r) s1)` >>
  qabbrev_tac
    `res2 = pack_dret_dynamic (cursor + n2w (ceil32 (w2n r))) pairs
       (mcopy (w2n cursor) (w2n q) (w2n r) s2)` >>
  PairCases_on `res1` >> PairCases_on `res2` >> gvs[] >>
  `R_ok (mcopy (w2n cursor) (w2n q) (w2n r) s1)
        (mcopy (w2n cursor) (w2n q) (w2n r) s2)` by
    (vsr_irule vsr_mcopy >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem vsr_step_inst_retfmp:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = RETFMP /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term
      (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `eval_operands inst.inst_operands s1 =
   eval_operands inst.inst_operands s2` by
    (vsr_irule vsr_eval_operands >> simp[]) >>
  imp_res_tac vsr_R_ok_fields >>
  imp_res_tac vsr_R_ok_R_term >>
  Cases_on `eval_operands inst.inst_operands s2`
  >- gvs[step_inst_base_RETFMP, lift_result_def]
  >> Cases_on `x` >> gvs[step_inst_base_RETFMP, lift_result_def]
QED

Theorem vsr_step_inst_dret:
  !R_ok R_term inst s1 s2.
    valid_state_rel R_ok R_term /\ R_ok s1 s2 /\
    inst.inst_opcode = DRET /\
    (!x. MEM (Var x) inst.inst_operands ==>
         lookup_var x s1 = lookup_var x s2) ==>
    lift_result R_ok R_term R_term
      (step_inst_base inst s1) (step_inst_base inst s2)
Proof
  rpt strip_tac >>
  `eval_operands inst.inst_operands s1 =
   eval_operands inst.inst_operands s2` by
    (vsr_irule vsr_eval_operands >> simp[]) >>
  imp_res_tac vsr_R_ok_fields >>
  reverse (Cases_on `inst.inst_outputs`)
  >- gvs[step_inst_base_DRET, lift_result_def]
  >> Cases_on `parse_dret_shape inst`
  >- gvs[step_inst_base_DRET, lift_result_def]
  >> Cases_on `x` >>
  Cases_on `eval_operands inst.inst_operands s2`
  >- gvs[step_inst_base_DRET, lift_result_def]
  >> Cases_on
       `pair_dret_words (TAKE (2 * r) (DROP (q + 1) x))`
  >- gvs[step_inst_base_DRET, lift_result_def]
  >> qabbrev_tac
       `res1 = pack_dret_dynamic s1.vs_call_entry_fmp x'
          s1` >>
  qabbrev_tac
       `res2 = pack_dret_dynamic s2.vs_call_entry_fmp x'
          s2` >>
  PairCases_on `res1` >> PairCases_on `res2` >>
  gvs[step_inst_base_DRET, lift_result_def] >>
  `R_ok res12 res22 /\ res10 = res20 /\ res11 = res21` by
    (drule_all vsr_pack_dret_dynamic >> simp[]) >>
  gvs[] >>
  `R_ok (res12 with vs_fmp := res11)
        (res22 with vs_fmp := res11)` by
    (vsr_irule vsr_fmp_R_ok >> simp[]) >>
  imp_res_tac vsr_R_ok_R_term
QED

val _ = export_theory()
