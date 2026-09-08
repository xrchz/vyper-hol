(*
 * Step simulation: two instructions with same opcode, matching eval_operand
 * results, and execution_equiv UNIV states produce sim-related results
 *
 * Architecture: category theorems + per-opcode dispatch
 * Category theorems (exec_pure1/2/3, exec_read0/1, exec_write2) handle 59
 * opcodes at ~0.02s each; remaining 23 inline opcodes use direct tactics
 *)

Theory tailMergeStep
Ancestors
  stateEquiv venomExecSemantics execEquivProofs
Libs
  stateEquivTheory stateEquivProofsTheory
  venomExecSemanticsTheory venomInstTheory venomStateTheory
  execEquivProofsTheory

Theorem update_var_ee_UNIV:
  !x1 x2 v1 v2 s1 s2.
    execution_equiv UNIV s1 s2 ==>
    execution_equiv UNIV (update_var x1 v1 s1) (update_var x2 v2 s2)
Proof
  rw[execution_equiv_def, update_var_def]
QED

Theorem eval_operands_match:
  !ops1 ops2 s1 s2.
    LENGTH ops1 = LENGTH ops2 /\
    (!i. i < LENGTH ops1 ==>
         eval_operand (EL i ops1) s1 = eval_operand (EL i ops2) s2) ==>
    eval_operands ops1 s1 = eval_operands ops2 s2
Proof
  Induct >> rpt strip_tac >>
  Cases_on `ops2` >> gvs[eval_operands_def] >>
  `eval_operand h s1 = eval_operand h' s2`
    by (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  simp[] >>
  Cases_on `eval_operand h' s2` >> simp[] >>
  `eval_operands ops1 s1 = eval_operands t s2`
    suffices_by (strip_tac >> simp[]) >>
  first_x_assum (qspecl_then [`t`, `s1`, `s2`] mp_tac) >> simp[] >>
  disch_then irule >> rpt strip_tac >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]
QED

Theorem eval_operands_DROP:
  !ops1 ops2 s1 s2 n.
    LENGTH ops1 = LENGTH ops2 /\
    (!i. i < LENGTH ops1 ==>
         eval_operand (EL i ops1) s1 = eval_operand (EL i ops2) s2) ==>
    eval_operands (DROP n ops1) s1 = eval_operands (DROP n ops2) s2
Proof
  rpt strip_tac >> irule eval_operands_match >>
  simp[listTheory.LENGTH_DROP] >> rpt strip_tac >>
  `i + n < LENGTH ops1` by DECIDE_TAC >>
  drule listTheory.EL_DROP >> disch_then (fn th => simp[th]) >>
  `i + n < LENGTH ops2` by DECIDE_TAC >>
  drule listTheory.EL_DROP >> disch_then (fn th => simp[th])
QED

(* ================================================================
   ee UNIV helpers for external call infrastructure
   ================================================================ *)

Theorem ee_UNIV_read_memory:
  !s1 s2 off sz.
    execution_equiv UNIV s1 s2 ==>
    read_memory off sz s1 = read_memory off sz s2
Proof
  rw[execution_equiv_def, read_memory_def]
QED

Theorem ee_UNIV_lookup_account:
  !s1 s2 addr.
    execution_equiv UNIV s1 s2 ==>
    lookup_account addr s1.vs_accounts = lookup_account addr s2.vs_accounts
Proof
  rw[execution_equiv_def]
QED

Theorem ee_UNIV_make_venom_call_state:
  !s1 s2 target gas value calldata code is_static.
    execution_equiv UNIV s1 s2 ==>
    make_venom_call_state s1 target gas value calldata code is_static =
    make_venom_call_state s2 target gas value calldata code is_static
Proof
  rw[execution_equiv_def, make_venom_call_state_def,
     make_sub_tx_def, venom_to_tx_params_def]
QED

Theorem ee_UNIV_make_venom_delegatecall_state:
  !s1 s2 target gas calldata code is_static.
    execution_equiv UNIV s1 s2 ==>
    make_venom_delegatecall_state s1 target gas calldata code is_static =
    make_venom_delegatecall_state s2 target gas calldata code is_static
Proof
  rw[execution_equiv_def, make_venom_delegatecall_state_def,
     make_sub_tx_def, venom_to_tx_params_def]
QED

Theorem ee_UNIV_make_venom_create_state:
  !s1 s2 new_address gas value init_code.
    execution_equiv UNIV s1 s2 ==>
    make_venom_create_state s1 new_address gas value init_code =
    make_venom_create_state s2 new_address gas value init_code
Proof
  rw[execution_equiv_def, make_venom_create_state_def,
     make_sub_tx_def, venom_to_tx_params_def]
QED

Theorem ee_UNIV_extract_none:
  !s1 s2 ov ro rs rr.
    execution_equiv UNIV s1 s2 ==>
    (extract_venom_result s1 ov ro rs rr = NONE <=>
     extract_venom_result s2 ov ro rs rr = NONE)
Proof
  rw[extract_venom_result_def, LET_THM] >>
  Cases_on `rr` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  Cases_on `r.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  ntac 3 (CASE_TAC >> gvs[execution_equiv_def, write_memory_with_expansion_def])
QED

Theorem ee_UNIV_extract_some:
  !s1 s2 ov ro rs rr v1 st1.
    execution_equiv UNIV s1 s2 /\
    extract_venom_result s1 ov ro rs rr = SOME (v1, st1) ==>
    ?st2. extract_venom_result s2 ov ro rs rr = SOME (v1, st2) /\
          execution_equiv UNIV st1 st2
Proof
  rw[execution_equiv_def, extract_venom_result_def] >>
  Cases_on `rr` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  Cases_on `r.contexts` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  Cases_on `h` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  gvs[write_memory_with_expansion_def] >>
  ntac 2 (CASE_TAC >> gvs[write_memory_with_expansion_def]) >>
  qexists_tac
    `s2 with
     <|vs_returndata := q'.returnData;
       vs_accounts := if q = INR NONE then r.rollback.accounts else s2.vs_accounts;
       vs_logs := s2.vs_logs ++ if q = INR NONE then q'.logs else [];
       vs_memory :=
         (write_memory_with_expansion ro (TAKE rs q'.returnData) s2).vs_memory;
       vs_transient :=
         if q = INR NONE then r.rollback.tStorage else s2.vs_transient|>` >>
  gvs[write_memory_with_expansion_def]
QED

(* ================================================================
   Simulation definitions
   ================================================================ *)

Definition step_sim_def:
  step_sim inst1 inst2 s1 s2 <=>
    case (step_inst_base inst1 s1, step_inst_base inst2 s2) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F
End

Definition sim_pre_def:
  sim_pre inst1 inst2 s1 s2 <=>
    inst1.inst_opcode = inst2.inst_opcode /\
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    (!i. i < LENGTH inst1.inst_operands ==>
         !l. EL i inst1.inst_operands = Label l ==>
             EL i inst2.inst_operands = Label l) /\
    (!i. i < LENGTH inst1.inst_operands ==>
         !w. EL i inst1.inst_operands = Lit w ==>
             EL i inst2.inst_operands = Lit w) /\
    (!i. i < LENGTH inst1.inst_operands ==>
         !l. EL i inst2.inst_operands = Label l ==>
             EL i inst1.inst_operands = Label l) /\
    (!i. i < LENGTH inst1.inst_operands ==>
         !w. EL i inst2.inst_operands = Lit w ==>
             EL i inst1.inst_operands = Lit w) /\
    execution_equiv UNIV s1 s2
End

(* sim_pre extraction lemmas for imp_res_tac *)
val sim_pre_lit12 = prove(
  ``sim_pre inst1 inst2 s1 s2 /\
    EL i inst1.inst_operands = Lit w /\ i < LENGTH inst1.inst_operands ==>
    EL i inst2.inst_operands = Lit w``,
  rw[sim_pre_def]);

val sim_pre_lit21 = prove(
  ``sim_pre inst1 inst2 s1 s2 /\
    EL i inst2.inst_operands = Lit w /\ i < LENGTH inst1.inst_operands ==>
    EL i inst1.inst_operands = Lit w``,
  rw[sim_pre_def]);

val sim_pre_label12 = prove(
  ``sim_pre inst1 inst2 s1 s2 /\
    EL i inst1.inst_operands = Label l /\ i < LENGTH inst1.inst_operands ==>
    EL i inst2.inst_operands = Label l``,
  rw[sim_pre_def]);

val sim_pre_label21 = prove(
  ``sim_pre inst1 inst2 s1 s2 /\
    EL i inst2.inst_operands = Label l /\ i < LENGTH inst1.inst_operands ==>
    EL i inst1.inst_operands = Label l``,
  rw[sim_pre_def]);

val sim_pre_ee = prove(
  ``sim_pre inst1 inst2 s1 s2 ==> execution_equiv UNIV s1 s2``,
  rw[sim_pre_def]);

(* ================================================================
   Category simulation theorems
   Each exec_* helper preserves the simulation relation
   ================================================================ *)

val pair_case_simp = pairTheory.pair_CASE_def;

val cat_close_defs = [execution_equiv_def, update_var_def,
  write_memory_with_expansion_def, read_memory_def,
  mload_def, mstore_def, mstore8_def, sload_def, sstore_def,
  tload_def, tstore_def, mcopy_def,
  contract_storage_def, contract_transient_def];

val exec_pure2_sim = prove(``
  !f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 ==>
    case (exec_pure2 f inst1 s1, exec_pure2 f inst2 s2) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  rpt gen_tac >> strip_tac >> simp[exec_pure2_def] >>
  qpat_x_assum `!i. _ ==> _`
    (fn th =>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``0n`` th)) >>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``1n`` th))) >>
  Cases_on `inst1.inst_operands` >> gvs[listTheory.LENGTH_CONS] >>
  TRY (Cases_on `t` >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t'` >> gvs[listTheory.LENGTH_CONS]) >>
  rpt (CASE_TAC >> gvs[]) >> gvs cat_close_defs);

val exec_pure1_sim = prove(``
  !f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 ==>
    case (exec_pure1 f inst1 s1, exec_pure1 f inst2 s2) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  rpt gen_tac >> strip_tac >> simp[exec_pure1_def] >>
  qpat_x_assum `!i. _ ==> _`
    (fn th => ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``0n`` th))) >>
  Cases_on `inst1.inst_operands` >> gvs[listTheory.LENGTH_CONS] >>
  TRY (Cases_on `t` >> gvs[listTheory.LENGTH_CONS]) >>
  rpt (CASE_TAC >> gvs[]) >> gvs cat_close_defs);

val exec_pure3_sim = prove(``
  !f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 ==>
    case (exec_pure3 f inst1 s1, exec_pure3 f inst2 s2) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  rpt gen_tac >> strip_tac >> simp[exec_pure3_def] >>
  qpat_x_assum `!i. _ ==> _`
    (fn th =>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``0n`` th)) >>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``1n`` th)) >>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``2n`` th))) >>
  Cases_on `inst1.inst_operands` >> gvs[listTheory.LENGTH_CONS] >>
  TRY (Cases_on `t` >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t'` >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t` >> gvs[listTheory.LENGTH_CONS]) >>
  rpt (CASE_TAC >> gvs[]) >> gvs cat_close_defs);

val exec_read0_sim = prove(``
  !f inst1 inst2 s1 s2.
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    execution_equiv UNIV s1 s2 /\
    f s1 = f s2 ==>
    case (exec_read0 f inst1 s1, exec_read0 f inst2 s2) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  rpt gen_tac >> strip_tac >> simp[exec_read0_def] >>
  rpt (CASE_TAC >> gvs[]) >> gvs cat_close_defs);

val exec_read1_sim = prove(``
  !f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 /\
    (!v. f v s1 = f v s2) ==>
    case (exec_read1 f inst1 s1, exec_read1 f inst2 s2) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  rpt gen_tac >> strip_tac >> simp[exec_read1_def] >>
  qpat_x_assum `!i. _ ==> _`
    (fn th => ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``0n`` th))) >>
  Cases_on `inst1.inst_operands` >> gvs[listTheory.LENGTH_CONS] >>
  TRY (Cases_on `t` >> gvs[listTheory.LENGTH_CONS]) >>
  rpt (CASE_TAC >> gvs[]) >> gvs cat_close_defs);

val exec_write2_sim = prove(``
  !f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 /\
    (!v1 v2. execution_equiv UNIV (f v1 v2 s1) (f v1 v2 s2)) ==>
    case (exec_write2 f inst1 s1, exec_write2 f inst2 s2) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  rpt gen_tac >> strip_tac >> simp[exec_write2_def] >>
  qpat_x_assum `!i. _ ==> _`
    (fn th =>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``0n`` th)) >>
      ASSUME_TAC (SIMP_RULE (srw_ss()) [] (SPEC ``1n`` th))) >>
  Cases_on `inst1.inst_operands` >> gvs[listTheory.LENGTH_CONS] >>
  TRY (Cases_on `t` >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t'` >> gvs[listTheory.LENGTH_CONS]) >>
  rpt (CASE_TAC >> gvs[]));

(* ================================================================
   Category-to-step_sim bridge theorems
   ================================================================ *)

fun mk_cat_bridge cat_sim =
  prove(``!f inst1 inst2 s1 s2. ^(concl cat_sim |> dest_forall |> snd |> dest_forall |> snd
    |> dest_forall |> snd |> dest_forall |> snd |> dest_forall |> snd |> dest_imp |> fst) /\
    step_inst_base inst1 s1 = ^(concl cat_sim |> dest_forall |> snd |> dest_forall |> snd
      |> dest_forall |> snd |> dest_forall |> snd |> dest_forall |> snd |> dest_imp |> snd
      |> dest_comb |> snd |> pairSyntax.dest_pair |> fst) /\
    step_inst_base inst2 s2 = ^(concl cat_sim |> dest_forall |> snd |> dest_forall |> snd
      |> dest_forall |> snd |> dest_forall |> snd |> dest_forall |> snd |> dest_imp |> snd
      |> dest_comb |> snd |> pairSyntax.dest_pair |> snd) ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all cat_sim >> strip_tac >> fs[pair_case_simp]);

(* Build bridge theorems programmatically *)
val exec_pure2_step_sim = prove(
  ``!f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 /\
    step_inst_base inst1 s1 = exec_pure2 f inst1 s1 /\
    step_inst_base inst2 s2 = exec_pure2 f inst2 s2 ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all exec_pure2_sim >> strip_tac >> fs[pair_case_simp]);

val exec_pure1_step_sim = prove(
  ``!f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 /\
    step_inst_base inst1 s1 = exec_pure1 f inst1 s1 /\
    step_inst_base inst2 s2 = exec_pure1 f inst2 s2 ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all exec_pure1_sim >> strip_tac >> fs[pair_case_simp]);

val exec_pure3_step_sim = prove(
  ``!f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 /\
    step_inst_base inst1 s1 = exec_pure3 f inst1 s1 /\
    step_inst_base inst2 s2 = exec_pure3 f inst2 s2 ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all exec_pure3_sim >> strip_tac >> fs[pair_case_simp]);

val exec_read0_step_sim = prove(
  ``!f inst1 inst2 s1 s2.
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    execution_equiv UNIV s1 s2 /\
    f s1 = f s2 /\
    step_inst_base inst1 s1 = exec_read0 f inst1 s1 /\
    step_inst_base inst2 s2 = exec_read0 f inst2 s2 ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all exec_read0_sim >> strip_tac >> fs[pair_case_simp]);

val exec_read1_step_sim = prove(
  ``!f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 /\
    (!v. f v s1 = f v s2) /\
    step_inst_base inst1 s1 = exec_read1 f inst1 s1 /\
    step_inst_base inst2 s2 = exec_read1 f inst2 s2 ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all exec_read1_sim >> strip_tac >> fs[pair_case_simp]);

val exec_write2_step_sim = prove(
  ``!f inst1 inst2 s1 s2.
    LENGTH inst1.inst_operands = LENGTH inst2.inst_operands /\
    (!i. i < LENGTH inst1.inst_operands ==>
         eval_operand (EL i inst1.inst_operands) s1 =
         eval_operand (EL i inst2.inst_operands) s2) /\
    execution_equiv UNIV s1 s2 /\
    (!v1 v2. execution_equiv UNIV (f v1 v2 s1) (f v1 v2 s2)) /\
    step_inst_base inst1 s1 = exec_write2 f inst1 s1 /\
    step_inst_base inst2 s2 = exec_write2 f inst2 s2 ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all exec_write2_sim >> strip_tac >> fs[pair_case_simp]);

(* ================================================================
   Pre-computed conditional rewrites
   step_base_expanded: generic 88-way case expansion (computed once)
   mk_cond_rewrite_fast: per-opcode specialization via SUBS + REWRITE
   ================================================================ *)

val step_base_expanded = PURE_ONCE_REWRITE_CONV [step_inst_base_def]
  ``step_inst_base inst s``;

fun mk_cond_rewrite_fast opc = let
  val eq_asm = ASSUME (mk_eq(``inst.inst_opcode``, opc))
  val subst_th = SUBS [eq_asm] step_base_expanded
  val resolved = CONV_RULE (RAND_CONV
    (REWRITE_CONV [TypeBase.case_def_of ``:opcode``])) subst_th
  in DISCH (concl eq_asm) resolved end;

(* Classify each opcode by its exec category *)
val all_opcodes = TypeBase.constructors_of ``:opcode``;
val excluded = [``JMP``, ``JNZ``, ``DJMP``, ``RET``, ``DRET``, ``RETFMP``,
  ``RETURN``, ``REVERT``, ``STOP``, ``SINK``, ``SELFDESTRUCT``, ``INVALID``,
  ``PHI``, ``PARAM``];
val target_opcodes = filter (fn t => not (exists (aconv t) excluded)) all_opcodes;

val fast_crs = map mk_cond_rewrite_fast target_opcodes;

fun find_index _ [] _ = NONE
  | find_index x (y::ys) n = if aconv x y then SOME n
                              else find_index x ys (n+1);
fun get_cr opc = List.nth(fast_crs,
  valOf (find_index opc target_opcodes 0));

fun get_rhs_head cr = let
  val (_, eq) = dest_imp (concl cr)
  val (_, rhs) = dest_eq eq
  val (f, _) = strip_comb rhs
  in fst (dest_const f) handle _ => "INLINE"
  end handle _ => "INLINE";

fun get_exec_fn cr = let
  val (_, eq) = dest_imp (concl cr)
  val (_, rhs) = dest_eq eq
  val (f_app, _) = dest_comb rhs
  val (f_app2, _) = dest_comb f_app
  val (_, fn_arg) = dest_comb f_app2
  in fn_arg end;

(* ================================================================
   Category dispatch: one prover per exec_* family
   ================================================================ *)

val solve_f_eq = BETA_TAC >> rpt gen_tac >> simp[LET_THM] >>
  gvs[execution_equiv_def, mload_def, sload_def, tload_def,
      mstore_def, mstore8_def, sstore_def, tstore_def,
      contract_storage_def, contract_transient_def,
      write_memory_with_expansion_def];

fun prove_cat cat_thm opc cr = let
  val fn_arg = get_exec_fn cr
  val goal = ``!inst1 inst2 s1 s2.
    sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = ^opc ==>
    step_sim inst1 inst2 s1 s2``
  in prove(goal,
    rpt gen_tac >> strip_tac >> fs[sim_pre_def] >>
    match_mp_tac cat_thm >> EXISTS_TAC fn_arg >>
    imp_res_tac cr >>
    rpt conj_tac >>
    TRY (first_assum ACCEPT_TAC) >>
    TRY (asm_rewrite_tac[]) >>
    solve_f_eq)
  end;

(* ================================================================
   Shared tactic infrastructure for inline opcodes
   ================================================================ *)

val spec_evals =
  qpat_x_assum `!i. i < LENGTH inst1.inst_operands ==>
    eval_operand _ _ = eval_operand _ _`
    (fn th => MAP_EVERY (fn i =>
      TRY (ASSUME_TAC (SIMP_RULE (srw_ss()) []
        (SPEC (numSyntax.term_of_int i) th)))) [0,1,2,3,4,5,6]);

val decompose_ops =
  Cases_on `inst1.inst_operands` >> gvs[listTheory.LENGTH_CONS] >>
  TRY (Cases_on `t`  >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t'` >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t`  >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t'` >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t`  >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t'` >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (Cases_on `t`  >> gvs[listTheory.LENGTH_CONS]) >>
  TRY (gvs[listTheory.LENGTH_EQ_NUM_compute, listTheory.LENGTH_NIL_SYM]);

val inline_close_defs = [execution_equiv_def, update_var_def,
  write_memory_with_expansion_def, read_memory_def,
  halt_state_def, revert_state_def, set_returndata_def,
  mcopy_def, istore_def, mstore_def, lookup_var_def,
  finite_mapTheory.FLOOKUP_UPDATE];

(* Standard inline tactic: imp_res_tac cr, unfold step_sim,
   spec evals, decompose operands to sync lengths, then close *)
fun prove_inline cr opc =
  prove(``!inst1 inst2 s1 s2.
    sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = ^opc ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> fs[sim_pre_def] >>
  imp_res_tac cr >> simp[step_sim_def] >>
  spec_evals >> decompose_ops >>
  rpt (CASE_TAC >> gvs[]) >> gvs inline_close_defs);

(* Fetch Theorem-block helpers as SML vals for use in val proofs *)
val update_var_ee_UNIV = DB.fetch "-" "update_var_ee_UNIV";
val ee_UNIV_make_venom_call_state =
  DB.fetch "-" "ee_UNIV_make_venom_call_state";
val ee_UNIV_make_venom_delegatecall_state =
  DB.fetch "-" "ee_UNIV_make_venom_delegatecall_state";
val ee_UNIV_make_venom_create_state =
  DB.fetch "-" "ee_UNIV_make_venom_create_state";
val ee_UNIV_extract_none = DB.fetch "-" "ee_UNIV_extract_none";
val ee_UNIV_extract_some = DB.fetch "-" "ee_UNIV_extract_some";
val eval_operands_match = DB.fetch "-" "eval_operands_match";

(* Derive s2 field = s1 field equalities from ee UNIV, KEEPING ee UNIV *)
val ee_field_eqs :tactic =
  `s2.vs_memory = s1.vs_memory` by gvs[execution_equiv_def] >>
  `s2.vs_accounts = s1.vs_accounts` by gvs[execution_equiv_def] >>
  `s2.vs_call_ctx = s1.vs_call_ctx` by gvs[execution_equiv_def] >>
  `s2.vs_tx_ctx = s1.vs_tx_ctx` by gvs[execution_equiv_def] >>
  `s2.vs_block_ctx = s1.vs_block_ctx` by gvs[execution_equiv_def] >>
  `s2.vs_transient = s1.vs_transient` by gvs[execution_equiv_def] >>
  `s2.vs_prev_hashes = s1.vs_prev_hashes` by gvs[execution_equiv_def] >>
  `s2.vs_allocas = s1.vs_allocas` by gvs[execution_equiv_def] >>
  `s2.vs_labels = s1.vs_labels` by gvs[execution_equiv_def];

(* Rewrite make_venom_*_state s2 -> s1 using DEPTH_CONV *)
val rewrite_make_venom_s2 :tactic = fn (asms, g) => let
  val ee_asm = List.find (fn t =>
    can (match_term ``execution_equiv UNIV s1 s2``) t) asms
  in case ee_asm of
    NONE => ALL_TAC (asms, g)
  | SOME ea => let
      val (s1t, s2t) = let val (_, args) = strip_comb ea
        in (List.nth(args, 1), List.nth(args, 2)) end
      val mk_rev = fn th => let
        val spec = UNDISCH_ALL (SPEC_ALL (SPECL [s1t, s2t] th))
        in SYM spec end handle _ => TRUTH
      val call_rev = mk_rev ee_UNIV_make_venom_call_state
      val deleg_rev = mk_rev ee_UNIV_make_venom_delegatecall_state
      val create_rev = mk_rev ee_UNIV_make_venom_create_state
      val rewrs = List.filter (fn th => not (concl th ~~ T))
                    [call_rev, deleg_rev, create_rev]
      in if null rewrs then ALL_TAC (asms, g)
         else TRY (CONV_TAC (DEPTH_CONV (FIRST_CONV
                (map REWR_CONV rewrs)))) (asms, g)
      end
  end;

(* Close extract_venom_result case: abbreviate ov+ro_+rs_+rr so both sides
   use the same names, then NONE/SOME via ee_extract lemmas *)
val close_extract :tactic =
  qmatch_goalsub_abbrev_tac `extract_venom_result s1 ov ro_ rs_ rr` >>
  Cases_on `extract_venom_result s1 ov ro_ rs_ rr` >- (
    imp_res_tac ee_UNIV_extract_none >> gvs[]
  ) >>
  rename1 `SOME p` >> Cases_on `p` >>
  drule_all ee_UNIV_extract_some >> strip_tac >> gvs[] >>
  Cases_on `inst1.inst_outputs` >> Cases_on `inst2.inst_outputs` >>
  gvs[listTheory.LENGTH_CONS] >>
  rpt (CASE_TAC >> gvs[]) >>
  metis_tac[update_var_ee_UNIV];

(* Shared wrapper: unfold exec def, substitute s2 fields and make_venom,
   leaving only extract_venom_result s1/s2 difference, then close *)
fun prove_exec_wrapper exec_def :tactic =
  rpt gen_tac >> strip_tac >> ee_field_eqs >>
  simp[exec_def, LET_THM, read_memory_def] >> fs[] >>
  rewrite_make_venom_s2 >> close_extract;

val ee_UNIV_exec_ext_call = prove(``
  !inst1 inst2 s1 s2 gas addr value ao as_ ro rs is_static.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs ==>
    case (exec_ext_call inst1 s1 gas addr value ao as_ ro rs is_static,
          exec_ext_call inst2 s2 gas addr value ao as_ ro rs is_static) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  prove_exec_wrapper exec_ext_call_def);

val ee_UNIV_exec_delegatecall = prove(``
  !inst1 inst2 s1 s2 gas addr ao as_ ro rs.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs ==>
    case (exec_delegatecall inst1 s1 gas addr ao as_ ro rs,
          exec_delegatecall inst2 s2 gas addr ao as_ ro rs) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  prove_exec_wrapper exec_delegatecall_def);

val ee_UNIV_exec_create = prove(``
  !inst1 inst2 s1 s2 value offset sz salt_opt.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs ==>
    case (exec_create inst1 s1 value offset sz salt_opt,
          exec_create inst2 s2 value offset sz salt_opt) of
      (OK s1', OK s2') => execution_equiv UNIV s1' s2'
    | (Error _, Error _) => T
    | (Abort a1 s1', Abort a2 s2') => a1 = a2 /\ execution_equiv UNIV s1' s2'
    | _ => F``,
  prove_exec_wrapper exec_create_def);

(* Flat-form extraction lemmas: exec result equations in hypotheses.
   Derived from case-form wrappers via qspecl_then + gvs.
   Usable by imp_res_tac after CASE_TAC has split exec_result branches. *)
fun prove_flat wrapper args :tactic =
  rpt strip_tac >>
  qspecl_then args mp_tac wrapper >>
  (impl_tac >- gvs[]) >> gvs[];

val _ = print "Starting flat lemma proofs...\n";
val ext_call_args =
  [`inst1`,`inst2`,`s1`,`s2`,`g`,`a`,`v`,`ao`,`as_`,`ro`,`rs`,`st`];
val deleg_args =
  [`inst1`,`inst2`,`s1`,`s2`,`g`,`a`,`ao`,`as_`,`ro`,`rs`];
val create_args =
  [`inst1`,`inst2`,`s1`,`s2`,`v`,`off`,`sz`,`salt`];

val exec_ext_call_OK_ee = prove(``
  !inst1 inst2 s1 s2 g a v ao as_ ro rs st v1 v2.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_ext_call inst1 s1 g a v ao as_ ro rs st = OK v1 /\
    exec_ext_call inst2 s2 g a v ao as_ ro rs st = OK v2 ==>
    execution_equiv UNIV v1 v2``,
  prove_flat ee_UNIV_exec_ext_call ext_call_args);

val exec_ext_call_Abort_ee = prove(``
  !inst1 inst2 s1 s2 g a v ao as_ ro rs st a1 v1 a2 v2.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_ext_call inst1 s1 g a v ao as_ ro rs st = Abort a1 v1 /\
    exec_ext_call inst2 s2 g a v ao as_ ro rs st = Abort a2 v2 ==>
    a1 = a2 /\ execution_equiv UNIV v1 v2``,
  prove_flat ee_UNIV_exec_ext_call ext_call_args);

val exec_delegatecall_OK_ee = prove(``
  !inst1 inst2 s1 s2 g a ao as_ ro rs v1 v2.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_delegatecall inst1 s1 g a ao as_ ro rs = OK v1 /\
    exec_delegatecall inst2 s2 g a ao as_ ro rs = OK v2 ==>
    execution_equiv UNIV v1 v2``,
  prove_flat ee_UNIV_exec_delegatecall deleg_args);

val exec_delegatecall_Abort_ee = prove(``
  !inst1 inst2 s1 s2 g a ao as_ ro rs a1 v1 a2 v2.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_delegatecall inst1 s1 g a ao as_ ro rs = Abort a1 v1 /\
    exec_delegatecall inst2 s2 g a ao as_ ro rs = Abort a2 v2 ==>
    a1 = a2 /\ execution_equiv UNIV v1 v2``,
  prove_flat ee_UNIV_exec_delegatecall deleg_args);

val exec_create_OK_ee = prove(``
  !inst1 inst2 s1 s2 v off sz salt v1 v2.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_create inst1 s1 v off sz salt = OK v1 /\
    exec_create inst2 s2 v off sz salt = OK v2 ==>
    execution_equiv UNIV v1 v2``,
  prove_flat ee_UNIV_exec_create create_args);

val exec_create_Abort_ee = prove(``
  !inst1 inst2 s1 s2 v off sz salt a1 v1 a2 v2.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_create inst1 s1 v off sz salt = Abort a1 v1 /\
    exec_create inst2 s2 v off sz salt = Abort a2 v2 ==>
    a1 = a2 /\ execution_equiv UNIV v1 v2``,
  prove_flat ee_UNIV_exec_create create_args);

val _ = print "Flat lemmas done. Starting bridges...\n";
(* Bridge theorems: step_inst_base = exec_* ==> step_sim
   Same pattern as category bridges (exec_pure2_step_sim etc.) *)
val exec_ext_call_step_sim = prove(``
  !inst1 inst2 s1 s2 gas addr value ao as_ ro rs is_static.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    step_inst_base inst1 s1 =
      exec_ext_call inst1 s1 gas addr value ao as_ ro rs is_static /\
    step_inst_base inst2 s2 =
      exec_ext_call inst2 s2 gas addr value ao as_ ro rs is_static ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all ee_UNIV_exec_ext_call >> strip_tac >> fs[pair_case_simp]);

val exec_delegatecall_step_sim = prove(``
  !inst1 inst2 s1 s2 gas addr ao as_ ro rs.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    step_inst_base inst1 s1 =
      exec_delegatecall inst1 s1 gas addr ao as_ ro rs /\
    step_inst_base inst2 s2 =
      exec_delegatecall inst2 s2 gas addr ao as_ ro rs ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all ee_UNIV_exec_delegatecall >> strip_tac >> fs[pair_case_simp]);

val exec_create_step_sim = prove(``
  !inst1 inst2 s1 s2 value offset sz salt_opt.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    step_inst_base inst1 s1 =
      exec_create inst1 s1 value offset sz salt_opt /\
    step_inst_base inst2 s2 =
      exec_create inst2 s2 value offset sz salt_opt ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> simp[step_sim_def] >>
  drule_all ee_UNIV_exec_create >> strip_tac >> fs[pair_case_simp]);

(* LOG bridge: sim_pre for LOG ==> step_sim.
   Proved as a Theorem so we can debug with hol_state_at.
   LOG only returns OK or Error (no Abort), so mismatch = F branches
   can only arise if inst1 takes a different code path than inst2.
   With sim_pre (same operand constructors + eval values + ee UNIV),
   both sides follow the same path. *)
(* Helper: extract head-element Lit preservation from indexed quantifier.
   After fs[sim_pre_def] + Cases_on operand list, the Lit12/Lit21 assumptions
   have form !i. i < SUC n ==> !w. EL i (a::xs) = Lit w ==> EL i (b::ys) = Lit w.
   This extracts: !w. a = Lit w ==> b = Lit w. *)
val head_ops_lit = prove(``
  (!i. i < SUC n ==>
       !w. EL i (a::xs) = Lit w ==> EL i (b::ys) = Lit w) ==>
  !w. a = Lit w ==> b = Lit w``,
  strip_tac >> first_x_assum (qspec_then `0` mp_tac) >> simp[]);

(* LOG step sim: prove step_sim from sim_pre + LOG opcode.
   Strategy: case split on head operand constructor.
   Lit: case split LENGTH to separate Error path, then establish reverse-direction
        eval equalities so fs[] unifies case scrutinees. See FOCUS for details.
   Var/Label: inst1 Error, inst2 must also Error (from head Lit preservation). *)
val log_cr = get_cr ``LOG``;

Theorem log_step_sim:
  !inst1 inst2 s1 s2.
    sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = LOG ==>
    step_sim inst1 inst2 s1 s2
Proof
  rpt gen_tac >> strip_tac >>
  fs[sim_pre_def] >> ee_field_eqs >>
  imp_res_tac log_cr >>
  qpat_x_assum `!st. step_inst_base inst1 st = _`
    (fn th => ASSUME_TAC (SPEC ``s1:venom_state`` th)) >>
  qpat_x_assum `!st. step_inst_base inst2 st = _`
    (fn th => ASSUME_TAC (SPEC ``s2:venom_state`` th)) >>
  Cases_on `inst1.inst_operands`
  >- (`inst2.inst_operands = []` by gvs[listTheory.LENGTH_NIL_SYM] >>
      gvs[step_sim_def, execution_equiv_refl])
  >> `?h' t'. inst2.inst_operands = h'::t'` by
    (Cases_on `inst2.inst_operands` >> gvs[]) >> gvs[] >>
  imp_res_tac head_ops_lit >>
  Cases_on `h` >> gvs[]
  >- ((* Lit c *)
    Cases_on `LENGTH t' <> w2n c + 2`
    >- (fs[] >> gvs[step_sim_def])
    >> gvs[] >>
    (* Both cr equations now have same structure. Extract concrete eval equalities
       from the indexed quantifier, rewrite, then close via step_sim_def. *)
    qpat_x_assum `!i. i < _ ==> (eval_operand (EL i _) _ = eval_operand (EL i _) _)`
      (fn eval_th => let
        fun spec_fwd n = let
          val sp = SPEC (numSyntax.term_of_int n) eval_th
          val (guard, _) = dest_imp (concl sp)
          in MP sp (DECIDE guard) end
        val e1 = SIMP_RULE (srw_ss()) [] (spec_fwd 1)
        val e2 = SIMP_RULE (srw_ss()) [] (spec_fwd 2)
        in ASSUME_TAC e1 >> ASSUME_TAC e2 >> ASSUME_TAC eval_th end) >>
    `eval_operands (DROP 2 t) s1 = eval_operands (DROP 2 t') s2` by (
      match_mp_tac eval_operands_DROP >> conj_tac >- simp[] >>
      rpt strip_tac >>
      first_x_assum (qspec_then `SUC i` mp_tac) >> simp[]) >>
    (* Now fs[] rewrites eval_operand (HD t') s2 => eval_operand (HD t) s1 etc.
       in the inst2 cr equation, unifying both case scrutinees. *)
    fs[] >>
    simp[step_sim_def] >>
    Cases_on `eval_operand (HD t') s2` >> gvs[] >>
    Cases_on `eval_operand (EL 1 t') s2` >> gvs[] >>
    Cases_on `eval_operands (DROP 2 t') s2` >> gvs[execution_equiv_def])
  >- (Cases_on `h'` >> gvs[step_sim_def])
  >> Cases_on `h'` >> gvs[step_sim_def]
QED

(* ================================================================
   External call and special opcode handlers
   ================================================================ *)

(* EVAL_CASE_TAC: find first eval_operand term in outermost case
   scrutinee and split on it. Used for ext_call opcodes to avoid
   CASE_TAC cross-product explosion on shared scrutinees. *)
fun find_eval_operand_in_case tm = let
  val eval_pat = ``eval_operand (op:operand) (s:venom_state)``
  fun is_eval t = can (match_term eval_pat) t
  fun find_in t =
    if is_eval t then SOME t
    else if is_comb t then let
      val r = find_in (rator t)
      in if isSome r then r else find_in (rand t) end
    else NONE
  val (_, scrut, _) = TypeBase.dest_case tm
  in find_in scrut end handle _ => NONE;

fun EVAL_CASE_TAC (asl, g) = let
  val eval_tm = valOf (find_eval_operand_in_case g)
  in tmCases_on eval_tm [] (asl, g)
  end handle _ => NO_TAC (asl, g);

(* For ext_call opcodes (CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2):
   After simp[step_sim_def], both sides have nested option cases with
   shared scrutinees (eval equalities substituted by gvs). Split each
   eval_operand option one at a time: NONE => both Error => T (gvs closes);
   SOME => continue. After all options resolved, match_mp_tac wrapper. *)
(* LIST_CASE_TAC: find a list-typed variable in a case scrutinee
   anywhere in the goal and do Cases_on it *)
fun find_list_case_var tm = let
  fun find t =
    if can TypeBase.dest_case t then let
      val (_, scrut, _) = TypeBase.dest_case t
      val (tyname, _) = dest_type (type_of scrut)
      in if tyname = "list" andalso is_var scrut
         then SOME scrut
         else find_deeper t
      end
    else find_deeper t
  and find_deeper t =
    if is_comb t then let
      val r = find (rator t)
      in if isSome r then r else find (rand t) end
    else if is_abs t then find (body t)
    else NONE
  in find tm end;

fun LIST_CASE_TAC (asl, g) = let
  val v = valOf (find_list_case_var g)
  in tmCases_on v [] (asl, g)
  end handle _ => NO_TAC (asl, g);

(* EVAL_CASE_TAC: find first eval_operand term in a case scrutinee
   in assumptions or goal, then Cases_on it *)
fun find_eval_in_case tm = let
  val eval_pat = ``eval_operand (op:operand) (s:venom_state)``
  fun is_eval t = can (match_term eval_pat) t
  fun find_in t =
    if is_eval t then SOME t
    else if is_comb t then let
      val r = find_in (rator t)
      in if isSome r then r else find_in (rand t) end
    else if is_abs t then find_in (body t)
    else NONE
  fun from_case t =
    if can TypeBase.dest_case t then let
      val (_, scrut, _) = TypeBase.dest_case t
      in find_in scrut end
    else NONE
  fun search t =
    case from_case t of SOME e => SOME e
    | NONE => if is_comb t then
        (case search (rator t) of SOME e => SOME e | NONE => search (rand t))
      else NONE
  in search tm end;

fun EVAL_CASE_TAC_ASM (asl, g) = let
  fun try_asms [] = NONE
    | try_asms (a::rest) = (case find_eval_in_case a of
        SOME e => SOME e | NONE => try_asms rest)
  val eval_tm = case find_eval_in_case g of
      SOME e => e
    | NONE => valOf (try_asms asl)
  in tmCases_on eval_tm [] (asl, g)
  end handle _ => NO_TAC (asl, g);

(* For ext_call opcodes (CALL, STATICCALL, DELEGATECALL, CREATE, CREATE2):
   After decompose_ops (8 rounds + LENGTH_NIL_SYM), both operand lists are
   fully concrete. imp_res_tac cr gives step_inst_base equations.
   fs[] resolves the list case. Then case-split each eval_operand option
   via EVAL_CASE_TAC_ASM. NONE: both sides Error, step_sim T.
   All SOME: irule bridge closes. *)
fun prove_ext_call bridge_thm cr opc =
  prove(``!inst1 inst2 s1 s2.
    sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = ^opc ==>
    step_sim inst1 inst2 s1 s2``,
  rpt gen_tac >> strip_tac >> fs[sim_pre_def] >>
  (* Get cr equations BEFORE decompose: Cases_on will substitute
     inst1/inst2.inst_operands in the cr assumptions too *)
  imp_res_tac cr >>
  qpat_x_assum `!st. step_inst_base inst1 st = _`
    (fn th => ASSUME_TAC (SPEC ``s1:venom_state`` th)) >>
  qpat_x_assum `!st. step_inst_base inst2 st = _`
    (fn th => ASSUME_TAC (SPEC ``s2:venom_state`` th)) >>
  spec_evals >> decompose_ops >>
  (* Wrong-length subgoals: cr gives Error on both sides *)
  TRY (simp[step_sim_def] >> NO_TAC) >>
  (* Right-length: unify cc_static so both exec_* calls use same is_static arg *)
  `s2.vs_call_ctx = s1.vs_call_ctx` by gvs[execution_equiv_def] >>
  fs[] >>
  (* Split eval_operand options: NONE => both Error => step_sim T *)
  rpt (EVAL_CASE_TAC_ASM >> gvs[] >-
    (PURE_ONCE_REWRITE_TAC[step_sim_def] >> simp[])) >>
  (* cr now resolved to exec_*. drule_all bridge matches all hypotheses
     (ee, LENGTH, and both cr equations), instantiating gas/addr/etc.
     Result: step_sim inst1 inst2 s1 s2 as new assumption. *)
  drule_all bridge_thm >> simp[]);

(* LOG: 3 operands (offset, size, topic_count) + variable topics.
   topic_count must be Lit. Need eval_operands match for DROP 3.
   Use cr-before-decompose pattern. *)
(* LOG: dispatched to pre-proved log_step_sim theorem *)
fun prove_log cr opc = log_step_sim;

(* ALLOCA and OFFSET: need Lit/Label preservation.
   Strategy: resolve inst1 operands via CASE_TAC, derive inst2 operands
   from sim_pre extraction lemmas to avoid cross-product blowup. *)
fun prove_alloca cr opc =
  let val goal = ``!inst1 inst2 s1 s2.
    sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = ^opc /\
    inst1.inst_id = inst2.inst_id ==>
    step_sim inst1 inst2 s1 s2``
  in prove(goal,
  rpt gen_tac >> strip_tac >>
  `sim_pre inst1 inst2 s1 s2` by first_assum ACCEPT_TAC >>
  fs[sim_pre_def] >>
  imp_res_tac cr >> simp[step_sim_def, exec_alloca_def] >>
  spec_evals >> decompose_ops >>
  rpt (CASE_TAC >> gvs[]) >>
  gvs inline_close_defs)
  end;

(* OFFSET now uses exec_pure2, handled by category dispatch *)
(* ================================================================
   Prove all 82 per-opcode theorems
   ================================================================ *)

fun cat_thm_for "exec_pure2" = exec_pure2_step_sim
  | cat_thm_for "exec_pure1" = exec_pure1_step_sim
  | cat_thm_for "exec_pure3" = exec_pure3_step_sim
  | cat_thm_for "exec_read0" = exec_read0_step_sim
  | cat_thm_for "exec_read1" = exec_read1_step_sim
  | cat_thm_for "exec_write2" = exec_write2_step_sim
  | cat_thm_for _ = raise Fail "unknown category";

fun prove_opcode opc = let
  val cr = get_cr opc
  val cat = get_rhs_head cr
  val name = fst(dest_const opc)
  val _ = ()
  in
  if cat = "OK" then (* NOP *)
    prove(``!inst1 inst2 s1 s2.
      sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = ^opc ==>
      step_sim inst1 inst2 s1 s2``,
    rpt gen_tac >> strip_tac >> fs[sim_pre_def] >>
    imp_res_tac cr >> simp[step_sim_def] >> first_assum ACCEPT_TAC)
  else if cat = "Error" then (* INVOKE *)
    prove(``!inst1 inst2 s1 s2.
      sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = ^opc ==>
      step_sim inst1 inst2 s1 s2``,
    rpt gen_tac >> strip_tac >> fs[sim_pre_def] >>
    imp_res_tac cr >> simp[step_sim_def])
  else if mem cat ["exec_pure2","exec_pure1","exec_pure3",
                    "exec_read0","exec_read1","exec_write2"]
    then (* Category opcodes *)
    prove_cat (cat_thm_for cat) opc cr
  else if name = "LOG" then prove_log cr opc
  else if name = "ALLOCA" then prove_alloca cr opc
  else if name = "CALL" orelse name = "STATICCALL"
    then prove_ext_call exec_ext_call_step_sim cr opc
  else if name = "DELEGATECALL"
    then prove_ext_call exec_delegatecall_step_sim cr opc
  else if name = "CREATE" orelse name = "CREATE2"
    then prove_ext_call exec_create_step_sim cr opc
  else (* Generic inline *)
    prove_inline cr opc
  end;

val _ = print "Starting opcode dispatch...\n";
fun timed_prove_opcode opc = let
  val name = fst (dest_const opc)
  val _ = print ("  proving " ^ name ^ "... ")
  val t1 = Time.now()
  val th = prove_opcode opc
  val t2 = Time.now()
  val ms = LargeInt.toString (Time.toMilliseconds (Time.-(t2,t1)))
  val _ = print (ms ^ "ms\n")
  in th end;
val all_opcode_thms = map timed_prove_opcode target_opcodes;

(* ================================================================
   Main theorem: combine all per-opcode theorems
   ================================================================ *)

Theorem step_inst_base_sim:
  !inst1 inst2 s1 s2.
    sim_pre inst1 inst2 s1 s2 /\
    inst1.inst_id = inst2.inst_id /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> PHI /\ inst1.inst_opcode <> PARAM /\
    inst1.inst_opcode <> RET ==>
    step_sim inst1 inst2 s1 s2
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst1.inst_opcode` >> fs[is_terminator_def] >>
  FIRST (map (fn th =>
    irule th >> rpt conj_tac >> first_assum ACCEPT_TAC)
    all_opcode_thms)
QED

(* ================================================================
   Output value matching: when sim_pre holds and both step_inst_base
   return OK, corresponding output variable values are equal.
   ================================================================ *)

val output_close = [update_var_def, lookup_var_def,
  finite_mapTheory.FLOOKUP_UPDATE, execution_equiv_def,
  read_memory_def, mload_def, sload_def, tload_def,
  contract_storage_def, contract_transient_def,
  write_memory_with_expansion_def,
  make_venom_call_state_def, make_venom_delegatecall_state_def,
  make_venom_create_state_def, venom_to_tx_params_def,
  extract_venom_result_def, set_returndata_def, mcopy_def, LET_THM,
  exec_pure1_def, exec_pure2_def, exec_pure3_def,
  exec_read0_def, exec_read1_def, exec_write2_def,
  mstore_def, mstore8_def, sstore_def, tstore_def, exec_alloca_def];

(* Extract inst2's opcode from sim_pre so imp_res_tac cr can match both *)
val sim_pre_opcode_eq = prove(
  ``sim_pre inst1 inst2 s1 s2 ==>
    inst2.inst_opcode = inst1.inst_opcode``,
  rw[sim_pre_def]);

(* Shared tactic: specialize cr at s1, s2 and rewrite step_inst_base.
   Must derive inst2's opcode equality from sim_pre before imp_res_tac cr,
   since sim_pre hasn't been unfolded yet at this point *)
fun specialize_cr cr :tactic =
  imp_res_tac sim_pre_opcode_eq >>
  gvs[] >>
  imp_res_tac cr >>
  qpat_x_assum `!s. step_inst_base inst1 s = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SPEC ``s1:venom_state`` th])) >>
  qpat_x_assum `!s. step_inst_base inst2 s = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [SPEC ``s2:venom_state`` th]));

(* --- ext_call output-value bridges ---
   For exec_ext_call/delegatecall/create: when ee UNIV holds and both return OK,
   the output variable values are equal. Key insight: extract_venom_result
   produces the same output value (v1) for ee-UNIV-equivalent states
   (ee_UNIV_extract_some), and update_var writes that same value. *)

(* Output wrapper: unfold exec def, substitute s2 fields via ee_field_eqs,
   unify make_venom states, case-split extract_venom_result, close with
   lookup_var/update_var. Uses ee_UNIV_extract_some to get same output value. *)
(* Strategy: move exec=OK hypotheses into goal antecedents, expand exec_def,
   rewrite make_venom s2->s1 in goal, case-split extract_venom_result s1,
   use ee_UNIV_extract_some to bridge s2 with same output value, close with
   lookup_var/update_var/FLOOKUP_UPDATE *)
fun prove_exec_output_wrapper exec_def :tactic =
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `_ = OK s2'` mp_tac >>
  qpat_x_assum `_ = OK s1'` mp_tac >>
  ee_field_eqs >>
  simp[exec_def, LET_THM, read_memory_def] >>
  rewrite_make_venom_s2 >>
  qmatch_goalsub_abbrev_tac `extract_venom_result s1 ov ro_ rs_ rr` >>
  Cases_on `extract_venom_result s1 ov ro_ rs_ rr` >- gvs[] >>
  rename1 `SOME p` >> Cases_on `p` >>
  drule_all ee_UNIV_extract_some >> strip_tac >> gvs[] >>
  Cases_on `inst1.inst_outputs` >> Cases_on `inst2.inst_outputs` >>
  gvs[listTheory.LENGTH_CONS] >>
  rpt (CASE_TAC >> gvs[]) >>
  rpt strip_tac >>
  gvs[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE];

val exec_ext_call_output = prove(``
  !inst1 inst2 s1 s2 g a v ao as_ ro rs st s1' s2'.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_ext_call inst1 s1 g a v ao as_ ro rs st = OK s1' /\
    exec_ext_call inst2 s2 g a v ao as_ ro rs st = OK s2' ==>
    !k. k < LENGTH inst1.inst_outputs ==>
        lookup_var (EL k inst1.inst_outputs) s1' =
        lookup_var (EL k inst2.inst_outputs) s2'``,
  prove_exec_output_wrapper exec_ext_call_def);

val exec_delegatecall_output = prove(``
  !inst1 inst2 s1 s2 g a ao as_ ro rs s1' s2'.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_delegatecall inst1 s1 g a ao as_ ro rs = OK s1' /\
    exec_delegatecall inst2 s2 g a ao as_ ro rs = OK s2' ==>
    !k. k < LENGTH inst1.inst_outputs ==>
        lookup_var (EL k inst1.inst_outputs) s1' =
        lookup_var (EL k inst2.inst_outputs) s2'``,
  prove_exec_output_wrapper exec_delegatecall_def);

val exec_create_output = prove(``
  !inst1 inst2 s1 s2 value offset sz salt_opt s1' s2'.
    execution_equiv UNIV s1 s2 /\
    LENGTH inst1.inst_outputs = LENGTH inst2.inst_outputs /\
    exec_create inst1 s1 value offset sz salt_opt = OK s1' /\
    exec_create inst2 s2 value offset sz salt_opt = OK s2' ==>
    !k. k < LENGTH inst1.inst_outputs ==>
        lookup_var (EL k inst1.inst_outputs) s1' =
        lookup_var (EL k inst2.inst_outputs) s2'``,
  prove_exec_output_wrapper exec_create_def);

(* --- Per-category output-match provers --- *)

(* OFFSET now handled by exec_pure2 category dispatch *)

(* Inline prover: works for all opcodes where output value is a deterministic
   function of operand evals and state fields covered by ee UNIV.
   Handles: pure1/2/3, read0/1, ALLOCA, DLOAD, LOG, ASSERT, etc *)
fun prove_output_inline cr opc =
  prove(``!inst1 inst2 s1 s2 s1' s2'.
    sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = ^opc /\
    inst1.inst_id = inst2.inst_id /\
    ALL_DISTINCT inst1.inst_outputs /\
    ALL_DISTINCT inst2.inst_outputs /\
    step_inst_base inst1 s1 = OK s1' /\
    step_inst_base inst2 s2 = OK s2' ==>
    !k. k < LENGTH inst1.inst_outputs ==>
        lookup_var (EL k inst1.inst_outputs) s1' =
        lookup_var (EL k inst2.inst_outputs) s2'``,
  if aconv opc ``BUMP`` then
    (rpt gen_tac >> strip_tac >>
     specialize_cr cr >>
     fs[sim_pre_def] >>
     spec_evals >> decompose_ops >>
     Cases_on `inst1.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[] >>
     Cases_on `inst2.inst_outputs` >> gvs[] >>
     Cases_on `t` >> gvs[] >>
     Cases_on `t'` >> gvs[] >>
     qpat_x_assum `_ = OK s2'` mp_tac >>
     qpat_x_assum `_ = OK s1'` mp_tac >>
     CASE_TAC >> gvs[] >>
     CASE_TAC >> gvs[] >>
     rpt strip_tac >>
     Cases_on `k` >>
     gvs[lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
     Cases_on `n` >> gvs[])
  else
    (rpt gen_tac >> strip_tac >>
     specialize_cr cr >>
     fs[sim_pre_def] >> spec_evals >> decompose_ops >>
     gvs (AllCaseEqs() :: output_close) >>
     rpt (CASE_TAC >> gvs output_close) >>
     metis_tac[]));

(* State-mod-only opcodes: modify state but don't use update_var.
   output_match is unprovable for these from sim_pre alone (ee UNIV doesn't
   cover vs_vars). In practice they have 0 outputs, so the conclusion is
   vacuously true. We exclude them from the per-opcode dispatch and add
   has_outputs as precondition to the combined theorem *)
val state_mod_opcodes = [``MSTORE``, ``MSTORE8``, ``SSTORE``, ``TSTORE``,
  ``MCOPY``, ``CODECOPY``, ``CALLDATACOPY``, ``RETURNDATACOPY``,
  ``EXTCODECOPY``, ``DLOADBYTES``, ``LOG``, ``ISTORE``,
  ``NOP``, ``ASSERT``, ``ASSERT_UNREACHABLE``];
val output_target_opcodes =
  filter (fn t => not (exists (aconv t) state_mod_opcodes)) target_opcodes;

(* ext_call output prover: mirrors prove_ext_call but concludes with
   output value equality instead of step_sim. Uses exec_*_output bridges.
   Strategy: specialize_cr to get step_inst_base = exec_* equations,
   unfold sim_pre, resolve operands, unify call_ctx, split eval options,
   then drule_all bridge. *)
fun prove_output_ext_call bridge_thm cr opc =
  prove(``!inst1 inst2 s1 s2 s1' s2'.
    sim_pre inst1 inst2 s1 s2 /\ inst1.inst_opcode = ^opc /\
    inst1.inst_id = inst2.inst_id /\
    ALL_DISTINCT inst1.inst_outputs /\
    ALL_DISTINCT inst2.inst_outputs /\
    step_inst_base inst1 s1 = OK s1' /\
    step_inst_base inst2 s2 = OK s2' ==>
    !k. k < LENGTH inst1.inst_outputs ==>
        lookup_var (EL k inst1.inst_outputs) s1' =
        lookup_var (EL k inst2.inst_outputs) s2'``,
  rpt gen_tac >> strip_tac >>
  specialize_cr cr >>
  fs[sim_pre_def] >> spec_evals >> decompose_ops >>
  TRY (gvs[] >> NO_TAC) >>
  `s2.vs_call_ctx = s1.vs_call_ctx` by gvs[execution_equiv_def] >>
  gvs[] >>
  rpt (EVAL_CASE_TAC_ASM >> gvs[]) >>
  metis_tac[bridge_thm]);

fun prove_output_opcode opc = let
  val cr = get_cr opc
  val name = fst (dest_const opc)
  in if name = "CALL" orelse name = "STATICCALL"
       then prove_output_ext_call exec_ext_call_output cr opc
     else if name = "DELEGATECALL"
       then prove_output_ext_call exec_delegatecall_output cr opc
     else if name = "CREATE" orelse name = "CREATE2"
       then prove_output_ext_call exec_create_output cr opc
     else prove_output_inline cr opc
  end;

val _ = print "Starting output-match dispatch...\n";
fun timed_prove_output opc = let
  val name = fst (dest_const opc)
  val _ = print ("  output " ^ name ^ "... ")
  val t1 = Time.now()
  val th = prove_output_opcode opc
  val t2 = Time.now()
  val ms = LargeInt.toString (Time.toMilliseconds (Time.-(t2,t1)))
  val _ = print (ms ^ "ms\n")
  in th end;
val all_output_thms = map timed_prove_output output_target_opcodes;
val output_thm_table = ListPair.zip (output_target_opcodes, all_output_thms);

fun pick_output_opcode tm =
  case total dest_eq tm of
    SOME (lhs, rhs) =>
      List.find (fn opc => aconv lhs opc orelse aconv rhs opc) output_target_opcodes
  | NONE => NONE;

fun output_thm_for opc =
  snd (valOf (List.find (fn (opc', _) => aconv opc opc') output_thm_table));

fun output_match_dispatch_tac (asl, w) =
  case List.find (fn asm => isSome (pick_output_opcode asm)) asl of
    SOME asm =>
      let val opc = valOf (pick_output_opcode asm) in
        (qspecl_then [`inst1`, `inst2`, `s1`, `s2`, `s1'`, `s2'`] mp_tac
           (output_thm_for opc) >>
         impl_tac >- (simp[] >> metis_tac[]) >>
         disch_then (qspec_then `k` mp_tac) >>
         simp[]) (asl, w)
      end
  | NONE => failwith "output_match_dispatch_tac: no opcode assumption";

(* Define the set of output-producing opcodes for downstream use *)
Definition is_output_opcode_def:
  is_output_opcode opc <=>
    opc <> MSTORE /\ opc <> MSTORE8 /\ opc <> SSTORE /\ opc <> TSTORE /\
    opc <> MCOPY /\ opc <> CODECOPY /\ opc <> CALLDATACOPY /\
    opc <> RETURNDATACOPY /\ opc <> EXTCODECOPY /\ opc <> DLOADBYTES /\
    opc <> LOG /\ opc <> ISTORE /\ opc <> NOP /\
    opc <> ASSERT /\ opc <> ASSERT_UNREACHABLE
End

Theorem step_inst_base_output_match:
  !inst1 inst2 s1 s2 s1' s2'.
    sim_pre inst1 inst2 s1 s2 /\
    inst1.inst_id = inst2.inst_id /\
    ALL_DISTINCT inst1.inst_outputs /\
    ALL_DISTINCT inst2.inst_outputs /\
    ~is_terminator inst1.inst_opcode /\
    is_output_opcode inst1.inst_opcode /\
    inst1.inst_opcode <> PHI /\ inst1.inst_opcode <> PARAM /\
    inst1.inst_opcode <> RET /\
    step_inst_base inst1 s1 = OK s1' /\
    step_inst_base inst2 s2 = OK s2' ==>
    !k. k < LENGTH inst1.inst_outputs ==>
        lookup_var (EL k inst1.inst_outputs) s1' =
        lookup_var (EL k inst2.inst_outputs) s2'
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst1.inst_opcode` >>
  fs[is_terminator_def, is_output_opcode_def] >>
  output_match_dispatch_tac
QED

val _ = export_theory();
