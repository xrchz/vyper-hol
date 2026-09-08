(*
 * DFG Soundness Through Instruction/Block Execution
 *
 * Proves dfg_sound (+ ops_defined) is preserved through:
 * - step_inst_base (single instruction, base case)
 * - step_inst (single instruction, general)
 * - run_block (full block execution)
 *
 * These are generic infrastructure theorems, not specific to assert_elim.
 * They are used by range_successor_sound and other pass proofs.
 *)

Theory dfgSoundStep
Ancestors
  dfgDefs
  dfgAnalysisProps
  finite_map
  integer_word
  list
  pred_set
  rangeAnalysisDefs
  rangeAnalysisProofs
  stateEquiv
  venomExecProps
  venomExecSemantics
  venomInst
  venomInstProps
  venomState
  venomWf

Libs
  BasicProvers


(* ===== state_equiv {} => vs_vars equality ===== *)

(* Reusable: state_equiv with empty exclusion set implies full vs_vars equality.
   Eliminates repeated FLOOKUP_EXT + FUN_EQ_THM derivations. *)
Theorem state_equiv_empty_vars_eq:
  !s1 s2. state_equiv {} s1 s2 ==> s1.vs_vars = s2.vs_vars
Proof
  rpt strip_tac >>
  `!v. FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v` by
    fs[state_equiv_def, execution_equiv_def, lookup_var_def] >>
  metis_tac[FLOOKUP_EXT, FUN_EQ_THM]
QED

(* ===== dfg_sound preservation through execution ===== *)

(* dfg_sound is preserved when vs_vars only changes by lookup_var
   equality. The terminator step preserves all lookup_var values,
   so dfg_sound is trivially preserved through terminators. *)
Theorem dfg_sound_lookup_var_eq:
  !dfg s s'.
    dfg_sound dfg s.vs_vars /\
    (!x. lookup_var x s' = lookup_var x s)
  ==>
    dfg_sound dfg s'.vs_vars
Proof
  rpt strip_tac >>
  `s'.vs_vars = s.vs_vars` suffices_by (strip_tac >> fs[]) >>
  `!x. FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x` by
    fs[lookup_var_def] >>
  metis_tac[FLOOKUP_EXT, FUN_EQ_THM]
QED

(* Opcodes tracked by the DFG soundness predicates.
   Only these opcodes get dfg_sound sub-predicates and dfg_block_local coverage.
   PHI, NOP, JMP, etc. are NOT tracked — their operands may not all be evaluated. *)
Definition dfg_tracked_opcode_def:
  dfg_tracked_opcode opc <=>
    (opc = ASSIGN \/ opc = ISZERO \/
     opc = EQ \/ opc = LT \/ opc = GT \/ opc = SLT \/ opc = SGT \/
     opc = ADD \/ opc = SUB)
End

(* ===== Extended DFG soundness for arithmetic/compare chains ===== *)

(* eval_op_env evaluates an operand against a variable environment,
   handling Var, Lit, and Label uniformly. *)
Definition eval_op_env_def:
  eval_op_env (Var v) env = FLOOKUP env v /\
  eval_op_env (Lit w) env = SOME w /\
  eval_op_env (Label _) env = NONE
End

(* Arithmetic soundness: ADD/SUB instructions produce the correct result.
   Guarded by no-Label operands since eval_op_env cannot represent Labels. *)
Definition dfg_arith_sound_def:
  dfg_arith_sound dfg env <=>
    !v inst op1 op2.
      dfg_get_def dfg v = SOME inst /\
      (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
      inst.inst_operands = [op1; op2] /\ v IN FDOM env /\
      (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
      ?w1 w2.
        eval_op_env op1 env = SOME w1 /\
        eval_op_env op2 env = SOME w2 /\
        FLOOKUP env v = SOME (if inst.inst_opcode = ADD
                               then word_add w1 w2
                               else word_sub w1 w2)
End

(* Compare-full soundness: LT/GT with arbitrary operand types.
   Guarded by no-Label operands since eval_op_env cannot represent Labels. *)
Definition dfg_compare_full_sound_def:
  dfg_compare_full_sound dfg env <=>
    !v inst op1 op2.
      dfg_get_def dfg v = SOME inst /\
      (inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
      inst.inst_operands = [op1; op2] /\ v IN FDOM env /\
      (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
      ?w1 w2.
        eval_op_env op1 env = SOME w1 /\
        eval_op_env op2 env = SOME w2 /\
        FLOOKUP env v =
          SOME (bool_to_word
                  (if inst.inst_opcode = LT
                   then w2n w1 < w2n w2
                   else w2n w1 > w2n w2))
End

(* ===== dfg_sound FUPDATE: 4 sub-lemmas + combiner ===== *)

(* ASSIGN soundness extends to an env extended with a new key k,
   provided k was absent and nv equals the FLOOKUP of the operand variable
   for any ASSIGN [Var u] that defines k in the DFG. *)
Theorem dfg_assign_sound_fupdate:
  !dfg env k nv.
    dfg_assign_sound dfg env /\ k NOTIN FDOM env /\
    (!dinst u. dfg_get_def dfg k = SOME dinst /\
       dinst.inst_opcode = ASSIGN /\ dinst.inst_operands = [Var u] ==>
       SOME nv = FLOOKUP env u)
  ==>
    dfg_assign_sound dfg (env |+ (k, nv))
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC [dfg_assign_sound_def] >> rpt strip_tac >>
  Cases_on `v = k`
  (* v = k *)
  >- (gvs[FLOOKUP_UPDATE] >>
      `SOME nv = FLOOKUP env u` by metis_tac[] >>
      `u IN FDOM env` by (Cases_on `FLOOKUP env u` >> fs[FLOOKUP_DEF]) >>
      `u <> k` by metis_tac[] >>
      simp[FLOOKUP_UPDATE])
  (* v <> k *)
  >- (`v IN FDOM env` by fs[FDOM_FUPDATE] >>
      `FLOOKUP env v = SOME (THE (FLOOKUP (env |+ (k,nv)) v))` by
        simp[FLOOKUP_UPDATE, FLOOKUP_DEF] >>
      qpat_x_assum `dfg_assign_sound _ _` mp_tac >>
      PURE_ONCE_REWRITE_TAC [dfg_assign_sound_def] >> strip_tac >>
      `FLOOKUP env v = FLOOKUP env u` by metis_tac[] >>
      `u IN FDOM env` by
        (Cases_on `FLOOKUP env v` >> gvs[] >> fs[FLOOKUP_DEF]) >>
      `u <> k` by metis_tac[] >>
      simp[FLOOKUP_UPDATE])
QED

(* ISZERO soundness extends to an env extended with a new key k,
   provided k was absent, tracked-opcode operand vars remain defined in env,
   and nv's truthiness matches ISZERO semantics for the operand of any
   ISZERO defining k in the DFG. *)
Theorem dfg_iszero_sound_fupdate:
  !dfg env k nv.
    dfg_iszero_sound dfg env /\ k NOTIN FDOM env /\
    (* ops_defined: operand vars of defined vars (tracked opcodes) are in env *)
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       (vv IN FDOM env \/ vv = k) /\
       dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM env) /\
    (!dinst tv. dfg_get_def dfg k = SOME dinst /\
       dinst.inst_opcode = ISZERO /\ dinst.inst_operands = [Var tv] ==>
       tv IN FDOM env /\
       (nv <> 0w ==> FLOOKUP env tv = SOME 0w) /\
       (nv = 0w ==> !w'. FLOOKUP env tv = SOME w' ==> w' <> 0w))
  ==>
    dfg_iszero_sound dfg (env |+ (k, nv))
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC [dfg_iszero_sound_def] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  Cases_on `v = k`
  >- (* v = k *)
     (`tv IN FDOM env` by metis_tac[] >>
      `tv <> k` by metis_tac[] >>
      gvs[FLOOKUP_UPDATE] >> metis_tac[])
  >> (* v <> k: use old dfg_iszero_sound + FLOOKUP_UPDATE *)
     (qpat_x_assum `FLOOKUP _ v = _` mp_tac >> simp[FLOOKUP_UPDATE] >>
      strip_tac) >>
     `v IN FDOM env` by fs[flookup_thm] >>
     `tv IN FDOM env` by
       (qpat_x_assum `!vv dinst u. _ ==> u IN FDOM env`
          (qspecl_then [`v`, `inst`, `tv`] mp_tac) >>
        simp[listTheory.MEM, dfg_tracked_opcode_def]) >>
     `k <> tv` by metis_tac[] >>
     fs[] >>
     qpat_x_assum `dfg_iszero_sound _ _` mp_tac >>
     PURE_ONCE_REWRITE_TAC [dfg_iszero_sound_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >> metis_tac[]
QED

(* dfg_iszero_sound only handles [Var tv] operands.
   This handles [Lit n] operands for iszero chain truthiness at position 0. *)
Definition dfg_iszero_lit_sound_def:
  dfg_iszero_lit_sound dfg env <=>
    !v inst n. dfg_get_def dfg v = SOME inst /\ inst.inst_opcode = ISZERO /\
      inst.inst_operands = [Lit n] /\ v IN FDOM env ==>
      FLOOKUP env v = SOME (if n = 0w then 1w else 0w)
End

(* ISZERO-literal soundness extends to an env extended with a new key k,
   provided nv = bool_to_word(n = 0w) for any ISZERO [Lit n] defining k. *)
Theorem dfg_iszero_lit_sound_fupdate:
  !dfg env k nv.
    dfg_iszero_lit_sound dfg env /\
    (!dinst n. dfg_get_def dfg k = SOME dinst /\
       dinst.inst_opcode = ISZERO /\ dinst.inst_operands = [Lit n] ==>
       nv = (if n = 0w then 1w else 0w))
  ==>
    dfg_iszero_lit_sound dfg (env |+ (k, nv))
Proof
  rpt strip_tac >>
  PURE_ONCE_REWRITE_TAC [dfg_iszero_lit_sound_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `v = k`
  >- (gvs[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[])
  >- (gvs[finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FDOM_FUPDATE] >>
      qpat_x_assum `dfg_iszero_lit_sound _ _` mp_tac >>
      PURE_ONCE_REWRITE_TAC [dfg_iszero_lit_sound_def] >> strip_tac >>
      metis_tac[])
QED

(* EQ soundness extends to an env extended with a new key k,
   provided k was absent and nv's non-zero value is consistent with
   equality of the operand pair for any EQ defining k in the DFG. *)
Theorem dfg_eq_sound_fupdate:
  !dfg env k nv.
    dfg_eq_sound dfg env /\ k NOTIN FDOM env /\
    (!dinst lhs rhs. dfg_get_def dfg k = SOME dinst /\
       dinst.inst_opcode = EQ /\ dinst.inst_operands = [lhs; rhs] /\
       nv <> 0w ==>
       (!u. lhs = Var u ==> ?wu. FLOOKUP env u = SOME wu) /\
       (!u. rhs = Var u ==> ?wu. FLOOKUP env u = SOME wu) /\
       (!u wu wl. lhs = Var u /\ rhs = Lit wl /\
          FLOOKUP env u = SOME wu ==> wu = wl) /\
       (!u wu wl. rhs = Var u /\ lhs = Lit wl /\
          FLOOKUP env u = SOME wu ==> wu = wl) /\
       (!u1 u2 w1 w2. lhs = Var u1 /\ rhs = Var u2 /\
          FLOOKUP env u1 = SOME w1 /\ FLOOKUP env u2 = SOME w2 ==>
          w1 = w2))
  ==>
    dfg_eq_sound dfg (env |+ (k, nv))
Proof
  rpt strip_tac >>
  `!x. x IN FDOM env ==> FLOOKUP (env |+ (k,nv)) x = FLOOKUP env x` by
    (rpt strip_tac >> `k <> x` by metis_tac[] >> simp[FLOOKUP_UPDATE]) >>
  PURE_ONCE_REWRITE_TAC [dfg_eq_sound_def] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >> strip_tac >>
  Cases_on `v = k`
  >- (* v = k: use new-key hypothesis *)
     (`w = nv` by (qpat_x_assum `FLOOKUP _ v = _` mp_tac >>
                   PURE_REWRITE_TAC[finite_mapTheory.FLOOKUP_UPDATE] >>
                   ASM_REWRITE_TAC[] >> strip_tac >>
                   qpat_x_assum `SOME nv = SOME w`
                     (assume_tac o REWRITE_RULE[optionTheory.SOME_11]) >>
                   ASM_REWRITE_TAC[]) >>
      rw[] >> first_x_assum drule_all >> strip_tac >>
      rpt conj_tac >> rpt strip_tac >>
      res_tac >> metis_tac[flookup_thm])
  >> (* v <> k: use old dfg_eq_sound *)
     `k <> v` by metis_tac[] >>
     qpat_x_assum `FLOOKUP _ v = _` mp_tac >>
     PURE_REWRITE_TAC[finite_mapTheory.FLOOKUP_UPDATE] >>
     ASM_REWRITE_TAC[] >> strip_tac >>
     qpat_x_assum `dfg_eq_sound _ _` mp_tac >>
     PURE_ONCE_REWRITE_TAC [dfg_eq_sound_def] >> strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     rpt conj_tac >> rpt strip_tac >>
     res_tac >> metis_tac[flookup_thm]
QED

(* Compare soundness (LT/GT/SLT/SGT) extends to an env extended with
   a new key k, provided k was absent, tracked-opcode operand vars remain
   defined in env, and nv's non-zero status matches the comparison
   semantics for any compare instruction defining k in the DFG. *)
Theorem dfg_compare_sound_fupdate:
  !dfg env k nv.
    dfg_compare_sound dfg env /\ k NOTIN FDOM env /\
    (* ops_defined for tracked-opcode defined vars *)
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       (vv IN FDOM env \/ vv = k) /\
       dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM env) /\
    (!dinst lhs rhs. dfg_get_def dfg k = SOME dinst /\
       (dinst.inst_opcode = LT \/ dinst.inst_opcode = GT \/
        dinst.inst_opcode = SLT \/ dinst.inst_opcode = SGT) /\
       dinst.inst_operands = [lhs; rhs] ==>
       (!u wl wu. lhs = Var u /\ rhs = Lit wl /\
          FLOOKUP env u = SOME wu ==>
          (nv <> 0w <=>
            if dinst.inst_opcode = LT then w2n wu < w2n wl
            else if dinst.inst_opcode = GT then w2n wu > w2n wl
            else if dinst.inst_opcode = SLT then w2i wu < w2i wl
            else w2i wu > w2i wl)) /\
       (!u wl wu. rhs = Var u /\ lhs = Lit wl /\
          FLOOKUP env u = SOME wu ==>
          (nv <> 0w <=>
            if dinst.inst_opcode = LT then w2n wl < w2n wu
            else if dinst.inst_opcode = GT then w2n wl > w2n wu
            else if dinst.inst_opcode = SLT then w2i wl < w2i wu
            else w2i wl > w2i wu)))
  ==>
    dfg_compare_sound dfg (env |+ (k, nv))
Proof
  rpt gen_tac >> strip_tac >>
  PURE_ONCE_REWRITE_TAC [dfg_compare_sound_def] >>
  rpt gen_tac >> DISCH_TAC >> gen_tac >> DISCH_TAC >>
  Cases_on `v = k` >> (
    (* Derive FLOOKUP env v = SOME w *)
    qpat_x_assum `FLOOKUP _ v = _` mp_tac >>
    simp[FLOOKUP_UPDATE] >> strip_tac >>
    (* Get comparison hypothesis: from new-key hyp or old compare_sound *)
    (first_x_assum (qspecl_then [`inst`, `lhs`, `rhs`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> strip_tac
     ORELSE
     (qpat_x_assum `dfg_compare_sound _ _` mp_tac >>
      PURE_ONCE_REWRITE_TAC [dfg_compare_sound_def] >> DISCH_TAC >>
      pop_assum (mp_tac o Q.SPECL [`v`, `inst`, `lhs`, `rhs`]) >>
      (impl_tac >- metis_tac[]) >> DISCH_TAC >>
      pop_assum (mp_tac o Q.SPEC `w`) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac)) >>
    (* Close: derive u IN FDOM env, simplify FLOOKUP, apply hyp *)
    rpt conj_tac >> rpt gen_tac >> strip_tac >>
    qpat_x_assum `!vv' dinst' u'. _` (qspecl_then [`v`, `inst`, `u`] mp_tac) >>
    (impl_tac >- (
      qpat_x_assum `dfg_get_def dfg v = SOME inst /\ _ /\ _` strip_assume_tac >>
      fs[flookup_thm, listTheory.MEM, dfg_tracked_opcode_def])) >>
    strip_tac >>
    qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
    `k <> u` by metis_tac[] >>
    simp[] >> strip_tac >>
    res_tac >> gvs[])
QED

(* Combined dfg_sound extends to an env extended with a new key k,
   provided all sub-soundness preconditions hold for each tracked opcode
   (ASSIGN, ISZERO, EQ, LT/GT/SLT/SGT) that may define k in the DFG. *)
Theorem dfg_sound_fupdate:
  !dfg env k nv.
    dfg_sound dfg env /\ k NOTIN FDOM env /\
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       (vv IN FDOM env \/ vv = k) /\
       dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM env) /\
    (!dinst. dfg_get_def dfg k = SOME dinst ==>
       (dinst.inst_opcode = ASSIGN ==>
         !u. dinst.inst_operands = [Var u] ==> SOME nv = FLOOKUP env u) /\
       (dinst.inst_opcode = ISZERO ==>
         !tv. dinst.inst_operands = [Var tv] ==> tv IN FDOM env /\
           (nv <> 0w ==> FLOOKUP env tv = SOME 0w) /\
           (nv = 0w ==> !w'. FLOOKUP env tv = SOME w' ==> w' <> 0w)) /\
       (dinst.inst_opcode = EQ ==>
         !lhs rhs. dinst.inst_operands = [lhs; rhs] ==> nv <> 0w ==>
           (!u. lhs = Var u ==> ?wu. FLOOKUP env u = SOME wu) /\
           (!u. rhs = Var u ==> ?wu. FLOOKUP env u = SOME wu) /\
           (!u wu wl. lhs = Var u /\ rhs = Lit wl /\
              FLOOKUP env u = SOME wu ==> wu = wl) /\
           (!u wu wl. rhs = Var u /\ lhs = Lit wl /\
              FLOOKUP env u = SOME wu ==> wu = wl) /\
           (!u1 u2 w1 w2. lhs = Var u1 /\ rhs = Var u2 /\
              FLOOKUP env u1 = SOME w1 /\ FLOOKUP env u2 = SOME w2 ==>
              w1 = w2)) /\
       ((dinst.inst_opcode = LT \/ dinst.inst_opcode = GT \/
         dinst.inst_opcode = SLT \/ dinst.inst_opcode = SGT) ==>
         !lhs rhs. dinst.inst_operands = [lhs; rhs] ==>
           (!u wl wu. lhs = Var u /\ rhs = Lit wl /\
              FLOOKUP env u = SOME wu ==>
              (nv <> 0w <=>
                if dinst.inst_opcode = LT then w2n wu < w2n wl
                else if dinst.inst_opcode = GT then w2n wu > w2n wl
                else if dinst.inst_opcode = SLT then w2i wu < w2i wl
                else w2i wu > w2i wl)) /\
           (!u wl wu. rhs = Var u /\ lhs = Lit wl /\
              FLOOKUP env u = SOME wu ==>
              (nv <> 0w <=>
                if dinst.inst_opcode = LT then w2n wl < w2n wu
                else if dinst.inst_opcode = GT then w2n wl > w2n wu
                else if dinst.inst_opcode = SLT then w2i wl < w2i wu
                else w2i wl > w2i wu))))
  ==>
    dfg_sound dfg (env |+ (k, nv))
Proof
  rpt strip_tac >> fs[dfg_sound_def] >> rpt conj_tac >>
  (irule dfg_assign_sound_fupdate ORELSE
   irule dfg_iszero_sound_fupdate ORELSE
   irule dfg_eq_sound_fupdate ORELSE
   irule dfg_compare_sound_fupdate) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])
QED


(* Extending an environment preserves DFG soundness when old values are
   unchanged and every tracked definition present afterwards was already
   present before the extension.  Operand closure keeps all variable operands
   of those old tracked definitions in the unchanged part of the environment. *)
Theorem dfg_sound_fresh_untracked_extension:
  !dfg env env'.
    dfg_sound dfg env /\
    (!x. x IN FDOM env ==> FLOOKUP env' x = FLOOKUP env x) /\
    (!v dinst. dfg_get_def dfg v = SOME dinst /\
       v IN FDOM env' /\ dfg_tracked_opcode dinst.inst_opcode ==>
       v IN FDOM env) /\
    (!v dinst u. dfg_get_def dfg v = SOME dinst /\
       v IN FDOM env /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM env)
    ==>
    dfg_sound dfg env'
Proof
  rpt strip_tac >> fs[dfg_sound_def] >> rpt conj_tac
  >- (PURE_ONCE_REWRITE_TAC[dfg_assign_sound_def] >> rpt strip_tac >>
      `v IN FDOM env` by metis_tac[dfg_tracked_opcode_def] >>
      `u IN FDOM env` by
        metis_tac[dfg_tracked_opcode_def, listTheory.MEM] >>
      qpat_x_assum `dfg_assign_sound dfg env` mp_tac >>
      PURE_ONCE_REWRITE_TAC[dfg_assign_sound_def] >> strip_tac >>
      first_x_assum drule_all >> metis_tac[])
  >- (PURE_ONCE_REWRITE_TAC[dfg_iszero_sound_def] >> rpt strip_tac >>
      `v IN FDOM env'` by fs[flookup_thm] >>
      `v IN FDOM env` by metis_tac[dfg_tracked_opcode_def] >>
      `tv IN FDOM env` by
        metis_tac[dfg_tracked_opcode_def, listTheory.MEM] >>
      `FLOOKUP env v = SOME w` by metis_tac[] >>
      `FLOOKUP env' tv = FLOOKUP env tv` by metis_tac[] >>
      qpat_x_assum `dfg_iszero_sound dfg env` mp_tac >>
      PURE_ONCE_REWRITE_TAC[dfg_iszero_sound_def] >> strip_tac >>
      first_x_assum drule_all >> metis_tac[])
  >- (PURE_ONCE_REWRITE_TAC[dfg_eq_sound_def] >> rpt strip_tac >>
      `v IN FDOM env'` by fs[flookup_thm] >>
      `v IN FDOM env` by metis_tac[dfg_tracked_opcode_def] >>
      `FLOOKUP env v = SOME w` by metis_tac[] >>
      `!u. MEM (Var u) [lhs; rhs] ==>
           u IN FDOM env /\ FLOOKUP env' u = FLOOKUP env u` by
        (rpt gen_tac >> strip_tac >> conj_tac >>
         metis_tac[dfg_tracked_opcode_def, listTheory.MEM]) >>
      qpat_x_assum `dfg_eq_sound dfg env` mp_tac >>
      PURE_ONCE_REWRITE_TAC[dfg_eq_sound_def] >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      rpt conj_tac >> rpt strip_tac >>
      metis_tac[listTheory.MEM])
  >- (PURE_ONCE_REWRITE_TAC[dfg_compare_sound_def] >> rpt strip_tac >>
      `v IN FDOM env'` by fs[flookup_thm] >>
      `v IN FDOM env` by metis_tac[dfg_tracked_opcode_def] >>
      `FLOOKUP env v = SOME w` by metis_tac[] >>
      `!u. MEM (Var u) [lhs; rhs] ==>
           u IN FDOM env /\ FLOOKUP env' u = FLOOKUP env u` by
        (rpt gen_tac >> strip_tac >> conj_tac >>
         metis_tac[dfg_tracked_opcode_def, listTheory.MEM]) >>
      qpat_x_assum `dfg_compare_sound dfg env` mp_tac >>
      PURE_ONCE_REWRITE_TAC[dfg_compare_sound_def] >> strip_tac >>
      first_x_assum drule_all >> strip_tac >>
      rpt conj_tac >> rpt strip_tac >>
      metis_tac[listTheory.MEM])
QED
(* Every instruction in a well-formed function's flat instruction list
   satisfies inst_wf. *)
Theorem fn_insts_inst_wf:
  !fn i. fn_inst_wf fn /\ MEM i (fn_insts fn) ==> inst_wf i
Proof
  rpt strip_tac >> fs[fn_inst_wf_def, fn_insts_def] >>
  `?bb. MEM bb fn.fn_blocks /\ MEM i bb.bb_instructions` suffices_by
    metis_tac[] >>
  pop_assum mp_tac >> qspec_tac (`fn.fn_blocks`, `bbs`) >>
  Induct >> simp[fn_insts_blocks_def, MEM_APPEND] >> metis_tac[]
QED

(* A well-formed instruction other than INVOKE or BUMP has at most one output. *)
fun inst_wf_output_tac () = rpt strip_tac >> gvs[]

fun dfg_eq_condition_tac () =
  simp[exec_pure2_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_DEF, bool_to_word_def] >>
  rpt strip_tac >> gvs[FUPD11_SAME_KEY_AND_BASE, AllCaseEqs()]

fun step_vars_fupdate_finish_tac () =
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
     exec_read0_def, exec_read1_def, exec_write2_def,
     exec_ext_call_def, exec_delegatecall_def,
     exec_create_def, exec_alloca_def,
     extract_venom_result_def] >>
  gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
     write_memory_with_expansion_def, mcopy_def,
     revert_state_def, eval_operands_def,
     lookup_var_def, FLOOKUP_UPDATE, FDOM_FUPDATE]

Theorem inst_wf_noninvoke_outputs_at_most_one:
  !inst. inst_wf inst /\ inst.inst_opcode <> INVOKE /\
         inst.inst_opcode <> BUMP ==>
    LENGTH inst.inst_outputs <= 1
Proof
  PURE_ONCE_REWRITE_TAC[inst_wf_def] >>
  Cases_on `inst.inst_opcode` >>
  inst_wf_output_tac ()
QED

(* Helper: if a well-formed step_inst_base adds a new variable to vs_vars,
   it must be the single output. Key link for SSA derivation. *)
Theorem step_inst_base_new_var_singleton:
  !inst s s' v.
    step_inst_base inst s = OK s' /\ inst_wf inst /\
    ~is_terminator inst.inst_opcode /\ inst.inst_opcode <> BUMP /\
    v NOTIN FDOM s.vs_vars /\ v IN FDOM s'.vs_vars ==>
    inst.inst_outputs = [v]
Proof
  rpt strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    (CCONTR_TAC >> gvs[step_inst_base_def]) >>
  `inst.inst_opcode <> PHI` by
    (CCONTR_TAC >> gvs[step_inst_base_def]) >>
  `FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs` by
    (irule venomExecPropsTheory.step_inst_base_fdom >> simp[]) >>
  `v IN FDOM s.vs_vars UNION set inst.inst_outputs` by
    (qpat_x_assum `FDOM s'.vs_vars = _` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `v IN set inst.inst_outputs` by
    (qpat_x_assum `v NOTIN FDOM s.vs_vars` mp_tac >>
     qpat_x_assum `v IN FDOM s.vs_vars UNION _` mp_tac >>
     simp[] >> metis_tac[]) >>
  `LENGTH inst.inst_outputs <= 1` by
    metis_tac[inst_wf_noninvoke_outputs_at_most_one] >>
  Cases_on `inst.inst_outputs` >> gvs[] >>
  Cases_on `t` >> gvs[]
QED

(* Helper: if step_inst_base adds a new output to FDOM, the resulting
   vs_vars is exactly the old one with the output FUPDATEd. *)
Theorem step_inst_base_vars_fupdate:
  !inst s s' out.
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    out NOTIN FDOM s.vs_vars /\ out IN FDOM s'.vs_vars /\
    inst.inst_outputs = [out]
  ==>
    s'.vs_vars = s.vs_vars |+ (out, THE (FLOOKUP s'.vs_vars out))
Proof
  rpt strip_tac >>
  `!v. v <> out ==> lookup_var v s' = lookup_var v s` by
    (drule_all venomInstProofs1Theory.step_inst_base_preserves_all >>
     simp[]) >>
  `!v. FLOOKUP s'.vs_vars v =
       FLOOKUP (s.vs_vars |+ (out, THE (FLOOKUP s'.vs_vars out))) v` by
    (gen_tac >> Cases_on `v = out`
     >- (gvs[FLOOKUP_UPDATE] >>
         Cases_on `FLOOKUP s'.vs_vars out` >> gvs[flookup_thm])
     >> `FLOOKUP s'.vs_vars v = FLOOKUP s.vs_vars v` by
          (qpat_x_assum `!v. v <> out ==> _` (qspec_then `v` mp_tac) >>
           simp[lookup_var_def]) >>
        simp[FLOOKUP_UPDATE]) >>
  metis_tac[FLOOKUP_EXT, FUN_EQ_THM]
QED

(* SSA uniqueness: DFG entry for a variable maps to the unique instruction
   that outputs it, given the DFG entry has singleton outputs. *)
Theorem dfg_ssa_unique:
  !fn v inst dinst.
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    LENGTH dinst.inst_outputs = 1 /\
    inst.inst_outputs = [v] /\ MEM inst (fn_insts fn) /\
    ssa_form fn ==>
    dinst = inst
Proof
  rpt strip_tac >>
  `MEM v dinst.inst_outputs /\ MEM dinst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `dinst.inst_outputs = [v]` by
    (Cases_on `dinst.inst_outputs` >> gvs[MEM] >>
     Cases_on `t` >> gvs[]) >>
  CCONTR_TAC >>
  `MEM v dinst.inst_outputs /\ MEM v inst.inst_outputs` by simp[] >>
  fs[ssa_form_def] >>
  qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[] >>
  simp[MEM_FLAT, MEM_MAP] >>
  `?pfx sfx. fn_insts fn = pfx ++ [dinst] ++ sfx /\ ~MEM dinst pfx` by
    metis_tac[MEM_SPLIT_APPEND_first] >>
  `MEM inst (pfx ++ sfx)` by
    (fs[MEM_APPEND, MEM] >> metis_tac[]) >>
  simp[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND] >>
  `MEM inst pfx \/ MEM inst sfx` by fs[MEM_APPEND] >|
  [(* inst in pfx: v in prefix outputs *)
   disj1_tac >> disj2_tac >>
   simp[MEM_FLAT, MEM_MAP] >> metis_tac[],
   (* inst in sfx: v in both middle and suffix *)
   disj2_tac >> disj2_tac >>
   qexists_tac `v` >> simp[MEM_FLAT, MEM_MAP] >> metis_tac[]]
QED

(* For DFG-tracked opcodes (ASSIGN, ISZERO, EQ, LT, GT, SLT, SGT),
   inst_wf gives LENGTH inst_outputs = 1. *)
Theorem inst_wf_tracked_singleton:
  !i v. inst_wf i /\ MEM v i.inst_outputs /\
    dfg_tracked_opcode i.inst_opcode ==>
    LENGTH i.inst_outputs = 1
Proof
  rpt strip_tac >> gvs[inst_wf_def, dfg_tracked_opcode_def]
QED

(* Per-opcode DFG conditions follow from step_inst_base execution.
   If inst produces output out with value nv = THE(FLOOKUP s'.vs_vars out),
   then nv satisfies the per-opcode conditions w.r.t. s.vs_vars. *)
Theorem step_inst_base_dfg_conditions:
  !inst s s' out nv.
    step_inst_base inst s = OK s' /\ inst_wf inst /\
    inst.inst_outputs = [out] /\ out NOTIN FDOM s.vs_vars /\
    s'.vs_vars = s.vs_vars |+ (out, nv) /\
    (!v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars) ==>
    (inst.inst_opcode = ASSIGN ==>
      !u. inst.inst_operands = [Var u] ==> SOME nv = FLOOKUP s.vs_vars u) /\
    (inst.inst_opcode = ISZERO ==>
      !tv. inst.inst_operands = [Var tv] ==> tv IN FDOM s.vs_vars /\
        (nv <> 0w ==> FLOOKUP s.vs_vars tv = SOME 0w) /\
        (nv = 0w ==> !w'. FLOOKUP s.vs_vars tv = SOME w' ==> w' <> 0w)) /\
    (inst.inst_opcode = EQ ==>
      !lhs rhs. inst.inst_operands = [lhs; rhs] ==> nv <> 0w ==>
        (!u. lhs = Var u ==> ?wu. FLOOKUP s.vs_vars u = SOME wu) /\
        (!u. rhs = Var u ==> ?wu. FLOOKUP s.vs_vars u = SOME wu) /\
        (!u wu wl. lhs = Var u /\ rhs = Lit wl /\
           FLOOKUP s.vs_vars u = SOME wu ==> wu = wl) /\
        (!u wu wl. rhs = Var u /\ lhs = Lit wl /\
           FLOOKUP s.vs_vars u = SOME wu ==> wu = wl) /\
        (!u1 u2 w1 w2. lhs = Var u1 /\ rhs = Var u2 /\
           FLOOKUP s.vs_vars u1 = SOME w1 /\ FLOOKUP s.vs_vars u2 = SOME w2 ==>
           w1 = w2)) /\
    ((inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
      inst.inst_opcode = SLT \/ inst.inst_opcode = SGT) ==>
      !lhs rhs. inst.inst_operands = [lhs; rhs] ==>
        (!u wl wu. lhs = Var u /\ rhs = Lit wl /\
           FLOOKUP s.vs_vars u = SOME wu ==>
           (nv <> 0w <=>
             if inst.inst_opcode = LT then w2n wu < w2n wl
             else if inst.inst_opcode = GT then w2n wu > w2n wl
             else if inst.inst_opcode = SLT then w2i wu < w2i wl
             else w2i wu > w2i wl)) /\
        (!u wl wu. rhs = Var u /\ lhs = Lit wl /\
           FLOOKUP s.vs_vars u = SOME wu ==>
           (nv <> 0w <=>
             if inst.inst_opcode = LT then w2n wl < w2n wu
             else if inst.inst_opcode = GT then w2n wl > w2n wu
             else if inst.inst_opcode = SLT then w2i wl < w2i wu
             else w2i wl > w2i wu)))
Proof
  rpt gen_tac >> strip_tac >>
  `!b. bool_to_word b <> 0w <=> b` by (Cases >> simp[bool_to_word_def]) >>
  `!v. MEM (Var v) inst.inst_operands ==>
     FLOOKUP s.vs_vars v = SOME (s.vs_vars ' v)` by (
    rpt strip_tac >>
    `v IN FDOM s.vs_vars` by metis_tac[] >>
    simp[FLOOKUP_DEF]) >>
  conj_tac
  >- ((* ASSIGN *)
      rpt strip_tac >> gvs[MEM] >>
      qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[step_inst_base_def, exec_pure1_def, eval_operand_def,
           lookup_var_def, update_var_def, FLOOKUP_DEF] >>
      strip_tac >> gvs[FUPD11_SAME_KEY_AND_BASE]) >>
  conj_tac
  >- ((* ISZERO *)
      rpt strip_tac >> gvs[MEM] >>
      qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      simp[step_inst_base_def, exec_pure1_def, eval_operand_def,
           lookup_var_def, update_var_def, FLOOKUP_DEF,
           bool_to_word_def] >>
      rpt strip_tac >> gvs[FUPD11_SAME_KEY_AND_BASE, AllCaseEqs()]) >>
  conj_tac
  >- ((* EQ *)
      rpt strip_tac >> gvs[MEM] >>
      qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      ASM_REWRITE_TAC[] >|
      [dfg_eq_condition_tac (), dfg_eq_condition_tac (),
       dfg_eq_condition_tac ()]) >>
  (* LT/GT/SLT/SGT *)
  rpt strip_tac >> gvs[MEM] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  simp[exec_pure2_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_DEF,
       bool_to_word_def] >>
  rpt strip_tac >> gvs[FUPD11_SAME_KEY_AND_BASE, AllCaseEqs(),
       integer_wordTheory.WORD_LTi, integer_wordTheory.WORD_GTi]
QED

(* Combined: dfg_sound preserved through step_inst_base for new output. *)
Theorem dfg_sound_step_inst_base:
  !fn inst s out nv.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       (vv IN FDOM s.vs_vars \/ vv = out) /\
       dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==> u IN FDOM s.vs_vars) /\
    out NOTIN FDOM s.vs_vars /\
    (!dinst. dfg_get_def (dfg_build_function fn) out = SOME dinst ==>
       dinst = inst) /\
    (inst.inst_opcode = ASSIGN ==>
       !u. inst.inst_operands = [Var u] ==> SOME nv = FLOOKUP s.vs_vars u) /\
    (inst.inst_opcode = ISZERO ==>
       !tv. inst.inst_operands = [Var tv] ==> tv IN FDOM s.vs_vars /\
         (nv <> 0w ==> FLOOKUP s.vs_vars tv = SOME 0w) /\
         (nv = 0w ==> !w'. FLOOKUP s.vs_vars tv = SOME w' ==> w' <> 0w)) /\
    (inst.inst_opcode = EQ ==>
       !lhs rhs. inst.inst_operands = [lhs; rhs] ==> nv <> 0w ==>
         (!u. lhs = Var u ==> ?wu. FLOOKUP s.vs_vars u = SOME wu) /\
         (!u. rhs = Var u ==> ?wu. FLOOKUP s.vs_vars u = SOME wu) /\
         (!u wu wl. lhs = Var u /\ rhs = Lit wl /\
            FLOOKUP s.vs_vars u = SOME wu ==> wu = wl) /\
         (!u wu wl. rhs = Var u /\ lhs = Lit wl /\
            FLOOKUP s.vs_vars u = SOME wu ==> wu = wl) /\
         (!u1 u2 w1 w2. lhs = Var u1 /\ rhs = Var u2 /\
            FLOOKUP s.vs_vars u1 = SOME w1 /\ FLOOKUP s.vs_vars u2 = SOME w2 ==>
            w1 = w2)) /\
    ((inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
      inst.inst_opcode = SLT \/ inst.inst_opcode = SGT) ==>
       !lhs rhs. inst.inst_operands = [lhs; rhs] ==>
         (!u wl wu. lhs = Var u /\ rhs = Lit wl /\
            FLOOKUP s.vs_vars u = SOME wu ==>
            (nv <> 0w <=>
              if inst.inst_opcode = LT then w2n wu < w2n wl
              else if inst.inst_opcode = GT then w2n wu > w2n wl
              else if inst.inst_opcode = SLT then w2i wu < w2i wl
              else w2i wu > w2i wl)) /\
         (!u wl wu. rhs = Var u /\ lhs = Lit wl /\
            FLOOKUP s.vs_vars u = SOME wu ==>
            (nv <> 0w <=>
              if inst.inst_opcode = LT then w2n wl < w2n wu
              else if inst.inst_opcode = GT then w2n wl > w2n wu
              else if inst.inst_opcode = SLT then w2i wl < w2i wu
              else w2i wl > w2i wu)))
  ==>
    dfg_sound (dfg_build_function fn) (s.vs_vars |+ (out, nv))
Proof
  rpt strip_tac >>
  irule dfg_sound_fupdate >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `!d. dfg_get_def _ out = SOME d ==> _` drule >>
      strip_tac >> BasicProvers.VAR_EQ_TAC >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
QED

(* Helper: when step_inst produces no new variables, vs_vars is unchanged *)
Theorem step_inst_vars_unchanged:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (!out. MEM out inst.inst_outputs ==> out NOTIN FDOM s.vs_vars) /\
    (~?out. out NOTIN FDOM s.vs_vars /\ out IN FDOM s'.vs_vars)
  ==>
    s'.vs_vars = s.vs_vars
Proof
  rpt strip_tac >>
  simp[FLOOKUP_EXT, FUN_EQ_THM] >>
  gen_tac >> Cases_on `x IN FDOM s.vs_vars`
  >- (`~MEM x inst.inst_outputs` by metis_tac[] >>
      `lookup_var x s' = lookup_var x s` by
        metis_tac[step_preserves_non_output_vars] >>
      fs[lookup_var_def])
  >- (`x NOTIN FDOM s'.vs_vars` by metis_tac[] >>
      fs[FLOOKUP_DEF])
QED

(* Helper: new-variable case of dfg_sound preservation *)
Theorem dfg_sound_step_inst_new_var:
  !fn fuel ctx inst s s' out.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!v dinst u. dfg_get_def (dfg_build_function fn) v = SOME dinst /\
       v IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s.vs_vars) /\
    step_inst fuel ctx inst s = OK s' /\
    step_inst_base inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    MEM inst (fn_insts fn) /\
    fn_inst_wf fn /\
    (!w (i1:instruction) i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    inst.inst_opcode <> INVOKE /\
    (!o'. MEM o' inst.inst_outputs ==> o' NOTIN FDOM s.vs_vars) /\
    (!v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars) /\
    out NOTIN FDOM s.vs_vars /\ out IN FDOM s'.vs_vars
  ==>
    dfg_sound (dfg_build_function fn) s'.vs_vars /\
    (!v dinst u. dfg_get_def (dfg_build_function fn) v = SOME dinst /\
       v IN FDOM s'.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s'.vs_vars)
Proof
  rpt gen_tac >> DISCH_TAC >> fs[] >>
  (* Derive key facts *)
  `inst_wf inst` by metis_tac[fn_insts_inst_wf] >>
  Cases_on `inst.inst_opcode = BUMP`
  >- (`FDOM s'.vs_vars = FDOM s.vs_vars UNION set inst.inst_outputs` by
        (irule venomExecPropsTheory.step_inst_base_fdom >> simp[]) >>
      `!x. x IN FDOM s.vs_vars ==>
           FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x` by
        (rpt strip_tac >>
         `~MEM x inst.inst_outputs` by metis_tac[] >>
         `lookup_var x s' = lookup_var x s` by
           metis_tac[step_preserves_non_output_vars] >>
         fs[lookup_var_def]) >>
      `!v dinst. dfg_get_def (dfg_build_function fn) v = SOME dinst /\
         v IN FDOM s'.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode ==>
         v IN FDOM s.vs_vars` by
        (rpt strip_tac >> CCONTR_TAC >>
         `MEM v inst.inst_outputs` by
           (qpat_x_assum `v IN FDOM s'.vs_vars` mp_tac >>
            ASM_REWRITE_TAC[] >> simp[]) >>
         `MEM v dinst.inst_outputs /\ MEM dinst (fn_insts fn)` by
           metis_tac[dfg_build_function_correct] >>
         `dinst = inst` by metis_tac[] >>
         `~dfg_tracked_opcode BUMP` by simp[dfg_tracked_opcode_def] >>
         metis_tac[]) >>
      conj_tac
      >- (mp_tac (Q.SPECL [`dfg_build_function fn`, `s.vs_vars`,
                            `s'.vs_vars`]
                           dfg_sound_fresh_untracked_extension) >>
          impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
          simp[])
      >- (rpt strip_tac >>
          `v IN FDOM s.vs_vars` by metis_tac[] >>
          `u IN FDOM s.vs_vars` by metis_tac[] >>
          fs[])) >>
  `inst.inst_outputs = [out]` by
    (mp_tac (Q.SPECL [`inst`, `s`, `s'`, `out`]
       step_inst_base_new_var_singleton) >>
     impl_tac >- simp[] >> simp[]) >>
  `s'.vs_vars = s.vs_vars |+ (out, THE (FLOOKUP s'.vs_vars out))` by
    metis_tac[step_inst_base_vars_fupdate] >>
  qabbrev_tac `nv = THE (FLOOKUP s'.vs_vars out)` >>
  (* SSA uniqueness: dfg entry for out maps to inst *)
  `!dinst0. dfg_get_def (dfg_build_function fn) out = SOME dinst0 ==>
     dinst0 = inst` by (
    rpt strip_tac >>
    imp_res_tac (dfg_build_function_correct
      |> Q.SPECL [`fn`, `v`, `dinst0`] |> GEN_ALL) >>
    `MEM out inst.inst_outputs` by simp[] >>
    metis_tac[]) >>
  (* ops_defined extended to include out *)
  `!vv dinst' u'. dfg_get_def (dfg_build_function fn) vv = SOME dinst' /\
     (vv IN FDOM s.vs_vars \/ vv = out) /\
     dfg_tracked_opcode dinst'.inst_opcode /\
     MEM (Var u') dinst'.inst_operands ==>
     u' IN FDOM s.vs_vars` by (
    rpt strip_tac
    >- metis_tac[]
    >- (BasicProvers.VAR_EQ_TAC >>
        `dinst' = inst` by metis_tac[] >>
        BasicProvers.VAR_EQ_TAC >>
        metis_tac[])) >>
  (* Apply dfg_sound_step_inst_base for dfg_sound *)
  `dfg_sound (dfg_build_function fn) (s.vs_vars |+ (out, nv))` by (
    mp_tac step_inst_base_dfg_conditions >>
    disch_then (qspecl_then [`inst`, `s`, `s'`, `out`, `nv`] mp_tac) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    strip_tac >>
    mp_tac (Q.SPECL [`fn`, `inst`, `s`, `out`, `nv`]
      dfg_sound_step_inst_base) >>
    impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    simp[]) >>
  (* ops_defined at updated env *)
  conj_tac >- fs[] >>
  rpt strip_tac >>
  Cases_on `v = out`
  >- (BasicProvers.VAR_EQ_TAC >>
      `dinst = inst` by metis_tac[] >>
      BasicProvers.VAR_EQ_TAC >>
      simp[FDOM_FUPDATE] >> metis_tac[])
  >- (qpat_x_assum `s'.vs_vars = _` (SUBST_ALL_TAC) >>
      fs[FDOM_FUPDATE] >> metis_tac[])
QED

(* dfg_sound + ops_defined preserved by step_inst.
   Uses dfg_sound_step_inst_base for the new-output case. *)
Theorem dfg_sound_step_inst:
  !fn fuel ctx inst s s'.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!v dinst u. dfg_get_def (dfg_build_function fn) v = SOME dinst /\
       v IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s.vs_vars) /\
    step_inst fuel ctx inst s = OK s' /\
    MEM inst (fn_insts fn) /\
    fn_inst_wf fn /\
    (!w (i1:instruction) i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    inst.inst_opcode <> INVOKE /\
    (!out. MEM out inst.inst_outputs ==> out NOTIN FDOM s.vs_vars) /\
    (!v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars)
  ==>
    dfg_sound (dfg_build_function fn) s'.vs_vars /\
    (!v dinst u. dfg_get_def (dfg_build_function fn) v = SOME dinst /\
       v IN FDOM s'.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s'.vs_vars)
Proof
  rpt gen_tac >> DISCH_TAC >> fs[] >>
  (* Case 1: Terminator — vars unchanged *)
  Cases_on `is_terminator inst.inst_opcode`
  >- (
    `s'.vs_vars = s.vs_vars` by
      (`!x. lookup_var x s' = lookup_var x s` suffices_by
         (strip_tac >> fs[fmap_eq_flookup, lookup_var_def]) >>
       metis_tac[step_terminator_preserves_vars]) >>
    ASM_REWRITE_TAC[]) >>
  (* Non-terminator, derive step_inst_base *)
  `step_inst_base inst s = OK s'` by
    (fs[step_inst_def] >> gvs[]) >>
  (* Case split: new variable or not *)
  Cases_on `?out. out NOTIN FDOM s.vs_vars /\ out IN FDOM s'.vs_vars`
  >- (fs[] >>
      mp_tac dfg_sound_step_inst_new_var >>
      disch_then (qspecl_then [`fn`, `fuel`, `ctx`, `inst`, `s`, `s'`, `out`]
        mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[])
  >- (`s'.vs_vars = s.vs_vars` by metis_tac[step_inst_vars_unchanged] >>
      ASM_REWRITE_TAC[])
QED

(* Block-local DFG property: for DFG-tracked opcodes, the defining
   instruction and the defining instructions of its Var operands are
   all in the same basic block, and the operand definer appears no
   later than the using instruction. This prevents cross-block
   staleness and ensures operand values are stable after the tracked
   instruction executes. *)
Definition dfg_block_local_def:
  dfg_block_local fn <=>
    !v inst u inst_u.
      dfg_get_def (dfg_build_function fn) v = SOME inst /\
      MEM (Var u) inst.inst_operands /\
      dfg_tracked_opcode inst.inst_opcode /\
      dfg_get_def (dfg_build_function fn) u = SOME inst_u ==>
      !bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
        MEM inst_u bb.bb_instructions /\
        !i j. i < LENGTH bb.bb_instructions /\
              j < LENGTH bb.bb_instructions /\
              EL i bb.bb_instructions = inst_u /\
              EL j bb.bb_instructions = inst ==>
              i < j
End

(* Variables not written by any instruction in a block have unchanged
   lookup_var after exec_block. *)
Theorem exec_block_non_output_lookup_var:
  !bb fuel ctx s r v.
    exec_block fuel ctx bb s = OK r /\
    (!inst. MEM inst bb.bb_instructions ==> ~MEM v inst.inst_outputs) ==>
    lookup_var v r = lookup_var v s
Proof
  rpt strip_tac >>
  `!n fuel' ctx' s'.
     n = LENGTH bb.bb_instructions - s'.vs_inst_idx /\
     exec_block fuel' ctx' bb s' = OK r ==>
     lookup_var v r = lookup_var v s'`
    suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  Cases_on `s'.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[]
  >- (
    qabbrev_tac `cur = EL s'.vs_inst_idx bb.bb_instructions` >>
    `MEM cur bb.bb_instructions` by
      metis_tac[MEM_EL, Abbr `cur`] >>
    `~MEM v cur.inst_outputs` by metis_tac[] >>
    Cases_on `step_inst fuel' ctx' cur s'`
    >> simp[] >> TRY (rpt strip_tac >> gvs[AllCaseEqs()] >> NO_TAC) >>
    rename1 `OK s''` >>
    Cases_on `is_terminator cur.inst_opcode` >> simp[]
    >- (Cases_on `s''.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
        metis_tac[step_terminator_preserves_vars])
    >- (
      strip_tac >>
      `lookup_var v s'' = lookup_var v s'` by
        metis_tac[step_preserves_non_output_vars] >>
      first_x_assum (qspec_then
        `LENGTH bb.bb_instructions - SUC s'.vs_inst_idx` mp_tac) >>
      impl_tac >- simp[] >>
      disch_then (qspecl_then [`fuel'`, `ctx'`,
        `s'' with vs_inst_idx := SUC s'.vs_inst_idx`] mp_tac) >>
      simp[] >>
      `(s'' with vs_inst_idx := SUC s'.vs_inst_idx).vs_vars = s''.vs_vars`
        by simp[] >>
      fs[lookup_var_def]))
QED

(* Variables not written by any instruction in a block have unchanged
   lookup_var after run_block. *)
Theorem run_block_non_output_lookup_var:
  !bb fuel ctx s r v.
    run_block fuel ctx bb s = OK r /\
    (!inst. MEM inst bb.bb_instructions ==> ~MEM v inst.inst_outputs) ==>
    lookup_var v r = lookup_var v s
Proof
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_THEN STRIP_ASSUME_TAC
    (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  gvs[] >>
  rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
  strip_tac >>
  `lookup_var v r = lookup_var v s_phi` by
    (mp_tac (Q.SPECL [`bb`, `fuel`, `ctx`,
       `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
       `r`, `v`] exec_block_non_output_lookup_var) >>
     simp[lookup_var_def]) >>
  `FLOOKUP s_phi.vs_vars v = FLOOKUP s.vs_vars v` by
    (irule venomExecProofsTheory.eval_phis_flookup_not_phi_output >>
     simp[] >> metis_tac[]) >>
  fs[lookup_var_def]
QED

(* Corollary: FLOOKUP is preserved for non-output variables *)
Theorem run_block_non_output_flookup:
  !fuel ctx bb s r v.
    run_block fuel ctx bb s = OK r /\
    (!inst. MEM inst bb.bb_instructions ==> ~MEM v inst.inst_outputs) ==>
    FLOOKUP r.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt strip_tac >>
  `lookup_var v r = lookup_var v s` by
    metis_tac[run_block_non_output_lookup_var] >>
  fs[lookup_var_def]
QED

(* Suffix version: lookup_var preserved when no instruction from current
   index onward writes the variable. Generalizes exec_block_non_output_lookup_var. *)
Theorem exec_block_suffix_non_output_lookup_var:
  !bb fuel ctx s r v.
    exec_block fuel ctx bb s = OK r /\
    (!k. s.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
       ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
    lookup_var v r = lookup_var v s
Proof
  rpt strip_tac >>
  `!n f c t.
     n = LENGTH bb.bb_instructions - t.vs_inst_idx /\
     exec_block f c bb t = OK r /\
     (!k. t.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
       ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
     lookup_var v r = lookup_var v t`
    suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  Cases_on `t.vs_inst_idx < LENGTH bb.bb_instructions` >> simp[]
  >- (
    qabbrev_tac `cur = EL t.vs_inst_idx bb.bb_instructions` >>
    `~MEM v cur.inst_outputs` by
      (fs[Abbr `cur`] >> first_x_assum (qspec_then `t.vs_inst_idx` mp_tac) >>
       simp[]) >>
    Cases_on `step_inst f c cur t` >> simp[] >>
    rename1 `step_inst _ _ _ _ = OK t1` >>
    Cases_on `is_terminator cur.inst_opcode` >> simp[]
    >- (Cases_on `t1.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
        metis_tac[step_terminator_preserves_vars])
    >- (
      strip_tac >>
      `lookup_var v t1 = lookup_var v t` by
        (mp_tac (Q.SPECL [`f`,`c`,`cur`,`t`,`t1`]
           step_preserves_non_output_vars) >>
         (impl_tac >- simp[]) >>
         disch_then (qspec_then `v` mp_tac) >> simp[]) >>
      qpat_x_assum `!m. m < n ==> _` (qspec_then
        `LENGTH bb.bb_instructions - SUC t.vs_inst_idx` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspecl_then [`f`, `c`,
        `t1 with vs_inst_idx := SUC t.vs_inst_idx`] mp_tac) >>
      simp[] >>
      `(t1 with vs_inst_idx := SUC t.vs_inst_idx).vs_vars = t1.vs_vars`
        by simp[] >>
      fs[lookup_var_def]))
QED

Theorem run_block_suffix_non_output_lookup_var:
  !bb fuel ctx s r v.
    run_block fuel ctx bb s = OK r /\
    s.vs_inst_idx = 0 /\
    (!k. s.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
       ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
    lookup_var v r = lookup_var v s
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`bb`, `fuel`, `ctx`, `s`, `r`, `v`]
    run_block_non_output_lookup_var) >>
  impl_tac >- (
    simp[] >> rpt strip_tac >>
    `?i. i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions`
      by metis_tac[MEM_EL] >>
    gvs[] >>
    first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  simp[]
QED

(* Corollary: FLOOKUP suffix preservation (exec_block) *)
Theorem exec_block_suffix_non_output_flookup:
  !fuel ctx bb s r v.
    exec_block fuel ctx bb s = OK r /\
    (!k. s.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
       ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
    FLOOKUP r.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt strip_tac >>
  `lookup_var v r = lookup_var v s` by
    metis_tac[exec_block_suffix_non_output_lookup_var] >>
  fs[lookup_var_def]
QED

(* Corollary: FLOOKUP suffix preservation (run_block) *)
Theorem run_block_suffix_non_output_flookup:
  !fuel ctx bb s r v.
    run_block fuel ctx bb s = OK r /\
    s.vs_inst_idx = 0 /\
    (!k. s.vs_inst_idx <= k /\ k < LENGTH bb.bb_instructions ==>
       ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
    FLOOKUP r.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt strip_tac >>
  `lookup_var v r = lookup_var v s` by
    metis_tac[run_block_suffix_non_output_lookup_var] >>
  fs[lookup_var_def]
QED

(* Block membership implies function membership *)
Theorem mem_bb_fn_insts[local]:
  !fn bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  rw[fn_insts_def] >>
  `!bbs. MEM bb bbs ==> MEM inst (fn_insts_blocks bbs)` suffices_by
    metis_tac[] >>
  Induct >> rw[fn_insts_blocks_def] >> metis_tac[MEM_APPEND]
QED

(* If dfg_get_def v = SOME inst and inst not in bb, then
   no instruction in bb outputs v (by SSA uniqueness + DFG correctness) *)
Theorem no_output_in_block_from_ssa[local]:
  !fn bb v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    ~MEM inst bb.bb_instructions /\
    MEM bb fn.fn_blocks /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) ==>
    !inst'. MEM inst' bb.bb_instructions ==> ~MEM v inst'.inst_outputs
Proof
  rpt strip_tac >>
  `MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `MEM inst' (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
  `inst' = inst` by metis_tac[] >>
  gvs[]
QED

(* Case A: For variables whose defining instruction is NOT in bb,
   FLOOKUP is unchanged for v and all its operands, so dfg conditions
   are inherited from entry. The operands' definers are also outside bb
   by dfg_block_local. If dfg_get_def u = NONE, then no instruction
   outputs u at all, so it's also unchanged. *)

(* Sublist of a flat all-distinct list is all-distinct *)
Theorem ALL_DISTINCT_FLAT_IMP[local]:
  !l x:'a list. ALL_DISTINCT (FLAT l) /\ MEM x l ==> ALL_DISTINCT x
Proof
  Induct >> simp[] >> rpt strip_tac >> fs[ALL_DISTINCT_APPEND]
QED

(* Convenience: extract dfg_block_local consequence for a specific (v, inst, u, inst_u).
   Avoids expanding dfg_block_local_def in contexts with 7-way opcode disjunction. *)
Theorem dfg_block_local_elim:
  !fn v inst u inst_u bb.
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    MEM (Var u) inst.inst_operands /\
    dfg_tracked_opcode inst.inst_opcode /\
    dfg_get_def (dfg_build_function fn) u = SOME inst_u /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst_u bb.bb_instructions /\
    !i j. i < LENGTH bb.bb_instructions /\
          j < LENGTH bb.bb_instructions /\
          EL i bb.bb_instructions = inst_u /\
          EL j bb.bb_instructions = inst ==>
          i < j
Proof
  REWRITE_TAC[dfg_block_local_def] >> metis_tac[]
QED

(* dfg_block_local (strict ordering) implies no self-referential operands.
   If inst outputs v and reads Var v, then the defining inst for v (which IS inst
   by SSA) would need to be at a strictly earlier position, contradicting j < j. *)
Theorem dfg_block_local_no_self_ref[local]:
  !fn v inst bb.
    dfg_block_local fn /\
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    MEM (Var v) inst.inst_operands /\
    dfg_tracked_opcode inst.inst_opcode /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    wf_function fn /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) ==>
    F
Proof
  rpt strip_tac >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  mp_tac (Q.SPECL [`fn`, `v`, `inst`, `v`, `inst`, `bb`]
    dfg_block_local_elim) >>
  (impl_tac >- (simp[] >> metis_tac[dfg_build_function_correct])) >>
  strip_tac >>
  `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst` by
    metis_tac[MEM_EL] >>
  `i < j` by metis_tac[] >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  `ALL_DISTINCT (MAP (\i'. i'.inst_id) bb.bb_instructions)` by
    (gvs[fn_inst_ids_distinct_def] >>
     irule ALL_DISTINCT_FLAT_IMP >>
     qexists_tac `MAP (\bb'. MAP (\i'. i'.inst_id) bb'.bb_instructions)
       fn.fn_blocks` >>
     simp[MEM_MAP] >> metis_tac[]) >>
  `EL i (MAP (\i'. i'.inst_id) bb.bb_instructions) =
   EL j (MAP (\i'. i'.inst_id) bb.bb_instructions)` by
    simp[EL_MAP] >>
  `i = j` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
  gvs[]
QED

(* Case B helper: If inst at position j in bb is tracked and has
   operand Var u, then no instruction at position k > j outputs u.
   Key for showing operand values are stable after inst executes. *)
Theorem tracked_operand_no_later_output[local]:
  !fn bb v dinst u j k.
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    MEM (Var u) dinst.inst_operands /\
    dfg_tracked_opcode dinst.inst_opcode /\
    dfg_block_local fn /\
    MEM bb fn.fn_blocks /\
    j < LENGTH bb.bb_instructions /\
    EL j bb.bb_instructions = dinst /\
    j < k /\ k < LENGTH bb.bb_instructions /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) /\
    wf_function fn ==>
    ~MEM u (EL k bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  (* Get the defining instruction for u *)
  `MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (irule mem_bb_fn_insts >> qexists_tac `bb` >>
     simp[MEM_EL] >> qexists_tac `k` >> simp[]) >>
  `?inst_u. dfg_get_def (dfg_build_function fn) u = SOME inst_u` by
    metis_tac[dfg_build_function_defs_complete] >>
  `MEM u inst_u.inst_outputs /\ MEM inst_u (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `EL k bb.bb_instructions = inst_u` by metis_tac[] >>
  `MEM dinst bb.bb_instructions` by metis_tac[MEM_EL] >>
  (* By dfg_block_local_elim: inst_u in bb, with ordering *)
  `MEM inst_u bb.bb_instructions /\
   !i' j'. i' < LENGTH bb.bb_instructions /\
           j' < LENGTH bb.bb_instructions /\
           EL i' bb.bb_instructions = inst_u /\
           EL j' bb.bb_instructions = dinst ==>
           i' < j'` by
    (mp_tac (Q.SPECL [`fn`, `v`, `dinst`, `u`, `inst_u`, `bb`]
       dfg_block_local_elim) >> simp[]) >>
  `?i. i < LENGTH bb.bb_instructions /\ EL i bb.bb_instructions = inst_u` by
    metis_tac[MEM_EL] >>
  `i < j` by metis_tac[] >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  `ALL_DISTINCT (MAP (\i'. i'.inst_id) bb.bb_instructions)` by
    (gvs[fn_inst_ids_distinct_def] >>
     irule ALL_DISTINCT_FLAT_IMP >>
     qexists_tac `MAP (\bb'. MAP (\i'. i'.inst_id) bb'.bb_instructions)
       fn.fn_blocks` >>
     simp[MEM_MAP] >> metis_tac[]) >>
  `EL i (MAP (\i'. i'.inst_id) bb.bb_instructions) =
   EL k (MAP (\i'. i'.inst_id) bb.bb_instructions)` by
    simp[EL_MAP] >>
  `i = k` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
  gvs[]
QED

(* Decompose exec_block: if exec_block succeeds and j is in range,
   we can access the intermediate state at position j and the step result.
   Also provides the suffix run from j+1 when j is not the last terminator. *)
Theorem exec_block_decompose:
  !bb fuel ctx s r j.
    exec_block fuel ctx bb s = OK r /\
    s.vs_inst_idx <= j /\ j < LENGTH bb.bb_instructions /\
    (!i. s.vs_inst_idx <= i /\ i < j ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    ?s_j s_j1.
      s_j.vs_inst_idx = j /\
      exec_block fuel ctx bb s_j = OK r /\
      step_inst fuel ctx (EL j bb.bb_instructions) s_j = OK s_j1 /\
      (!v. (!k. s.vs_inst_idx <= k /\ k < j ==>
         ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
        FLOOKUP s_j.vs_vars v = FLOOKUP s.vs_vars v)
Proof
  rpt strip_tac >>
  `!n f c t.
     n = j - t.vs_inst_idx /\
     exec_block f c bb t = OK r /\
     t.vs_inst_idx <= j /\ j < LENGTH bb.bb_instructions /\
     (!i. t.vs_inst_idx <= i /\ i < j ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
     ?s_j s_j1. s_j.vs_inst_idx = j /\
           exec_block f c bb s_j = OK r /\
           step_inst f c (EL j bb.bb_instructions) s_j = OK s_j1 /\
           (!v. (!k. t.vs_inst_idx <= k /\ k < j ==>
             ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
            FLOOKUP s_j.vs_vars v = FLOOKUP t.vs_vars v)`
    suffices_by metis_tac[] >>
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `t.vs_inst_idx = j`
  >- (
    (* Base: t is already at position j. Extract step from exec_block. *)
    `?s_j1. step_inst f c (EL j bb.bb_instructions) t = OK s_j1` by
      (qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
       CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
       simp[get_instruction_def] >>
       Cases_on `step_inst f c (EL j bb.bb_instructions) t` >> simp[]) >>
    qexistsl_tac [`t`, `s_j1`] >> simp[])
  >- (
    `t.vs_inst_idx < j` by simp[] >>
    qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
    CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
    simp[get_instruction_def] >>
    `t.vs_inst_idx < LENGTH bb.bb_instructions` by simp[] >>
    simp[] >>
    Cases_on `step_inst f c (EL t.vs_inst_idx bb.bb_instructions) t` >>
    simp[] >>
    rename1 `step_inst _ _ _ _ = OK t1` >>
    `~is_terminator (EL t.vs_inst_idx bb.bb_instructions).inst_opcode` by
      (first_x_assum match_mp_tac >> simp[]) >>
    simp[] >> strip_tac >>
    qpat_x_assum `!m. m < n ==> _` (qspec_then `j - SUC t.vs_inst_idx` mp_tac) >>
    (impl_tac >- simp[]) >>
    disch_then (qspecl_then [`f`, `c`,
      `t1 with vs_inst_idx := SUC t.vs_inst_idx`] mp_tac) >>
    simp[] >> strip_tac >>
    qexistsl_tac [`s_j`, `s_j1`] >> simp[] >>
    rpt strip_tac >>
    `FLOOKUP s_j.vs_vars v = FLOOKUP t1.vs_vars v` by
      (first_x_assum irule >> rpt strip_tac >>
       first_x_assum (qspec_then `k` mp_tac) >> simp[]) >>
    `~MEM v (EL t.vs_inst_idx bb.bb_instructions).inst_outputs` by
      (first_x_assum (qspec_then `t.vs_inst_idx` mp_tac) >> simp[]) >>
    `lookup_var v t1 = lookup_var v t` by
      (irule (SRULE [] step_preserves_non_output_vars) >>
       simp[] >> metis_tac[]) >>
    gvs[lookup_var_def])
QED

Theorem phi_prefix_length_le_non_phi_el[local]:
  !insts j.
    j < LENGTH insts /\ (EL j insts).inst_opcode <> PHI ==>
    phi_prefix_length insts <= j
Proof
  Induct_on `insts` >> simp[] >>
  rpt strip_tac >>
  Cases_on `j` >> gvs[phi_prefix_length_def] >>
  Cases_on `h.inst_opcode = PHI` >> gvs[phi_prefix_length_def] >>
  first_x_assum drule_all >> simp[]
QED

Theorem eval_phis_flookup_not_prefix_output[local]:
  !insts s s' x.
    eval_phis s insts = OK s' /\
    (!k. k < phi_prefix_length insts ==>
       ~MEM x (EL k insts).inst_outputs) ==>
    FLOOKUP s'.vs_vars x = FLOOKUP s.vs_vars x
Proof
  Induct_on `insts` >> simp[eval_phis_def, phi_prefix_length_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> gvs[eval_phis_def, phi_prefix_length_def] >>
  Cases_on `eval_one_phi s h` >> gvs[] >>
  PairCases_on `x'` >> gvs[] >>
  Cases_on `eval_phis s insts` >> gvs[update_var_def] >>
  rename1 `eval_phis s insts = OK s_rest` >>
  `FLOOKUP s_rest.vs_vars x = FLOOKUP s.vs_vars x` by
    (first_x_assum irule >> rpt strip_tac >>
     first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]) >>
  `x'0 <> x` by
    (spose_not_then strip_assume_tac >> gvs[] >>
     `MEM x h.inst_outputs` by
       (drule venomExecProofsTheory.eval_one_phi_output_mem >> simp[]) >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  fs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem run_block_decompose:
  !bb fuel ctx s r j.
    run_block fuel ctx bb s = OK r /\
    s.vs_inst_idx = 0 /\
    phi_prefix_length bb.bb_instructions <= j /\
    j < LENGTH bb.bb_instructions /\
    (!i. i < j ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    ?s_j s_j1.
      s_j.vs_inst_idx = j /\
      exec_block fuel ctx bb s_j = OK r /\
      step_inst fuel ctx (EL j bb.bb_instructions) s_j = OK s_j1 /\
      (!v. (!k. k < j ==>
         ~MEM v (EL k bb.bb_instructions).inst_outputs) ==>
        FLOOKUP s_j.vs_vars v = FLOOKUP s.vs_vars v)
Proof
  rpt strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = OK _` mp_tac >>
  ONCE_REWRITE_TAC[run_block_def] >>
  DISJ_CASES_THEN STRIP_ASSUME_TAC
    (Q.SPECL [`s`, `bb.bb_instructions`] eval_phis_ok_or_error_defs) >>
  gvs[] >>
  rename1 `eval_phis s bb.bb_instructions = OK s_phi` >>
  strip_tac >>
  mp_tac (Q.SPECL [`bb`, `fuel`, `ctx`,
    `s_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions`,
    `r`, `j`] exec_block_decompose) >>
  impl_tac >- simp[] >>
  strip_tac >> qexistsl_tac [`s_j`, `s_j1`] >> simp[] >>
  rpt strip_tac >>
  `FLOOKUP s_j.vs_vars v = FLOOKUP s_phi.vs_vars v` by
    (qpat_x_assum `!v. _ ==> FLOOKUP s_j.vs_vars v = _`
       (qspec_then `v` mp_tac) >>
     simp[] >> disch_then irule >> rpt strip_tac >>
     qpat_x_assum `!k. k < j ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  `FLOOKUP s_phi.vs_vars v = FLOOKUP s.vs_vars v` by
    (mp_tac (Q.SPECL [`bb.bb_instructions`, `s`, `s_phi`, `v`]
       eval_phis_flookup_not_prefix_output) >>
     impl_tac >- (simp[] >> rpt strip_tac >>
       qpat_x_assum `!k. k < j ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
     simp[]) >>
  simp[]
QED

(* Generic list lemma: if FLAT xss is ALL_DISTINCT and x appears in two
   member lists of xss, they must be the same list. *)
Theorem ALL_DISTINCT_FLAT_unique[local]:
  !xss xs1 xs2 (x:'a).
    ALL_DISTINCT (FLAT xss) /\
    MEM xs1 xss /\ MEM xs2 xss /\
    MEM x xs1 /\ MEM x xs2 ==>
    xs1 = xs2
Proof
  Induct >> rw[FLAT] >>
  gvs[ALL_DISTINCT_APPEND, MEM_FLAT]
  >- metis_tac[]
  >- (CCONTR_TAC >> metis_tac[])
  >- (CCONTR_TAC >> metis_tac[])
QED

(* Operand's defining instruction is in the same block as the tracked inst.
   Contrapositive: if dinst not in bb, then inst_u not in bb. *)
Theorem operand_inst_same_block[local]:
  !fn bb v dinst u inst_u.
    dfg_block_local fn /\ wf_function fn /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    MEM (Var u) dinst.inst_operands /\
    dfg_tracked_opcode dinst.inst_opcode /\
    dfg_get_def (dfg_build_function fn) u = SOME inst_u /\
    MEM dinst bb.bb_instructions ==>
    MEM inst_u bb.bb_instructions
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fn`,`v`,`dinst`,`u`,`inst_u`,`bb`] dfg_block_local_elim) >>
  simp[]
QED

(* An instruction cannot be in two different blocks. *)
Theorem inst_in_unique_block[local]:
  !fn bb1 bb2 inst.
    fn_inst_ids_distinct fn /\
    MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    MEM inst bb1.bb_instructions /\ MEM inst bb2.bb_instructions ==>
    MAP (\i. i.inst_id) bb1.bb_instructions =
    MAP (\i. i.inst_id) bb2.bb_instructions
Proof
  rpt strip_tac >>
  gvs[fn_inst_ids_distinct_def] >>
  `MEM inst.inst_id (MAP (\i. i.inst_id) bb1.bb_instructions)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  `MEM inst.inst_id (MAP (\i. i.inst_id) bb2.bb_instructions)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  `MEM (MAP (\i. i.inst_id) bb1.bb_instructions)
    (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  `MEM (MAP (\i. i.inst_id) bb2.bb_instructions)
    (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) fn.fn_blocks)` by
    (simp[MEM_MAP] >> metis_tac[]) >>
  metis_tac[ALL_DISTINCT_FLAT_unique]
QED

(* If two instructions have the same ID and are in the same block,
   they are at the same position, hence equal. *)
Theorem inst_id_determines_inst_in_block[local]:
  !fn bb i1 i2.
    fn_inst_ids_distinct fn /\
    MEM bb fn.fn_blocks /\
    MEM i1 bb.bb_instructions /\ MEM i2 bb.bb_instructions /\
    i1.inst_id = i2.inst_id ==>
    i1 = i2
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (gvs[fn_inst_ids_distinct_def] >>
     irule ALL_DISTINCT_FLAT_IMP >>
     qexists_tac `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
       fn.fn_blocks` >>
     simp[MEM_MAP] >> metis_tac[]) >>
  `?k1. k1 < LENGTH bb.bb_instructions /\ EL k1 bb.bb_instructions = i1` by
    metis_tac[MEM_EL] >>
  `?k2. k2 < LENGTH bb.bb_instructions /\ EL k2 bb.bb_instructions = i2` by
    metis_tac[MEM_EL] >>
  `EL k1 (MAP (\i. i.inst_id) bb.bb_instructions) =
   EL k2 (MAP (\i. i.inst_id) bb.bb_instructions)` by
    simp[EL_MAP] >>
  `k1 = k2` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
  gvs[]
QED

(* Reverse of mem_bb_fn_insts: MEM in fn_insts implies MEM in some block *)
Theorem fn_insts_mem_block:
  !fn inst. MEM inst (fn_insts fn) ==>
    ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions
Proof
  rw[fn_insts_def] >>
  `!bbs. MEM inst (fn_insts_blocks bbs) ==>
    ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions` suffices_by
    metis_tac[] >>
  Induct >> rw[fn_insts_blocks_def] >> gvs[MEM_APPEND] >> metis_tac[]
QED

(* Tracked DFG instruction always has singleton output list.
   Combines dfg_build_function_correct + fn_inst_wf + inst_wf. *)
Theorem dfg_tracked_inst_outputs:
  !fn v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    dfg_tracked_opcode inst.inst_opcode /\
    fn_inst_wf fn ==>
    inst.inst_outputs = [v]
Proof
  rpt strip_tac >>
  `MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions` by
    metis_tac[fn_insts_mem_block] >>
  `inst_wf inst` by metis_tac[fn_inst_wf_def] >>
  gvs[dfg_tracked_opcode_def, inst_wf_def] >>
  Cases_on `inst.inst_outputs` >> gvs[LENGTH_NIL]
QED

(* MAP inst_id over fn_insts_blocks = FLAT of per-block ID maps *)
Theorem fn_insts_blocks_map_id[local]:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> rw[fn_insts_blocks_def, MAP_APPEND]
QED

(* fn_inst_ids_distinct implies ALL_DISTINCT on the inst_id map of fn_insts *)
Theorem fn_inst_ids_distinct_all_distinct[local]:
  !fn. fn_inst_ids_distinct fn ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  rw[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_map_id]
QED

(* Global ID uniqueness: same inst_id in fn_insts => same instruction *)
Theorem fn_insts_id_unique[local]:
  !fn i1 i2. fn_inst_ids_distinct fn /\
    MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
    i1.inst_id = i2.inst_id ==> (i1 = i2)
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    metis_tac[fn_inst_ids_distinct_all_distinct] >>
  `?n1. n1 < LENGTH (fn_insts fn) /\ (EL n1 (fn_insts fn) = i1)` by
    metis_tac[MEM_EL] >>
  `?n2. n2 < LENGTH (fn_insts fn) /\ (EL n2 (fn_insts fn) = i2)` by
    metis_tac[MEM_EL] >>
  `EL n1 (MAP (\i. i.inst_id) (fn_insts fn)) =
   EL n2 (MAP (\i. i.inst_id) (fn_insts fn))` by
    simp[EL_MAP] >>
  `n1 = n2` by metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP] >>
  gvs[]
QED

(* If dinst not in bb, then inst_u (operand's defining inst) not in bb either.
   Uses dfg_block_local (same block) + fn_inst_ids_distinct (unique IDs). *)
Theorem operand_not_in_block[local]:
  !fn bb v dinst u inst_u.
    dfg_block_local fn /\ wf_function fn /\
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    ~MEM dinst bb.bb_instructions /\
    MEM (Var u) dinst.inst_operands /\
    dfg_tracked_opcode dinst.inst_opcode /\
    dfg_get_def (dfg_build_function fn) u = SOME inst_u ==>
    ~MEM inst_u bb.bb_instructions
Proof
  rpt strip_tac >>
  `MEM dinst (fn_insts fn)` by metis_tac[dfg_build_function_correct] >>
  `?bb_d. MEM bb_d fn.fn_blocks /\ MEM dinst bb_d.bb_instructions` by
    metis_tac[fn_insts_mem_block] >>
  `MEM inst_u bb_d.bb_instructions` by
    metis_tac[operand_inst_same_block] >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  (* inst_u is in both bb and bb_d => same ID maps *)
  `MAP (\i. i.inst_id) bb.bb_instructions =
   MAP (\i. i.inst_id) bb_d.bb_instructions` by
    metis_tac[inst_in_unique_block] >>
  (* dinst in bb_d => dinst.inst_id in bb's ID map => some dinst' in bb *)
  `MEM dinst.inst_id (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[MEM_MAP_f] >>
  `?dinst'. (dinst.inst_id = dinst'.inst_id) /\ MEM dinst' bb.bb_instructions` by
    metis_tac[MEM_MAP] >>
  (* dinst' and dinst have same ID in fn_insts => equal => contradiction *)
  `MEM dinst' (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
  `dinst' = dinst` by metis_tac[fn_insts_id_unique] >>
  metis_tac[]
QED

(* For a tracked variable whose defining inst is NOT in bb,
   FLOOKUP is preserved through run_block for both v and its operands. *)
Theorem run_block_tracked_not_in_bb[local]:
  !fn bb fuel ctx s r v dinst.
    run_block fuel ctx bb s = OK r /\
    s.vs_inst_idx = 0 /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    ~MEM dinst bb.bb_instructions /\
    wf_function fn /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) ==>
    FLOOKUP r.vs_vars v = FLOOKUP s.vs_vars v
Proof
  rpt strip_tac >>
  irule run_block_non_output_flookup >>
  qexistsl_tac [`bb`, `ctx`, `fuel`] >> simp[] >>
  rpt strip_tac >>
  `MEM v dinst.inst_outputs /\ MEM dinst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `MEM inst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
  `inst = dinst` by metis_tac[] >>
  gvs[]
QED

(* For a variable where dfg_get_def = NONE (untracked),
   no instruction in fn_insts outputs it, so FLOOKUP preserved. *)
Theorem run_block_untracked_flookup[local]:
  !fn bb fuel ctx s r u.
    run_block fuel ctx bb s = OK r /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) u = NONE ==>
    FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u
Proof
  rpt strip_tac >>
  irule run_block_non_output_flookup >>
  qexistsl_tac [`bb`, `ctx`, `fuel`] >> simp[] >>
  rpt strip_tac >>
  CCONTR_TAC >> gvs[] >>
  `MEM inst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
  `?inst'. dfg_get_def (dfg_build_function fn) u = SOME inst'` by
    metis_tac[dfg_build_function_defs_complete] >>
  gvs[]
QED

(* If dinst not in bb and u is a Var operand of dinst (tracked opcode),
   then FLOOKUP u is preserved through run_block. *)
Theorem operand_flookup_preserved_not_in_bb[local]:
  !fn bb fuel ctx s r v dinst u.
    run_block fuel ctx bb s = OK r /\
    MEM bb fn.fn_blocks /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    ~MEM dinst bb.bb_instructions /\
    MEM (Var u) dinst.inst_operands /\
    dfg_tracked_opcode dinst.inst_opcode /\
    dfg_block_local fn /\ wf_function fn /\ fn_inst_wf fn /\
    (!w i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM w i1.inst_outputs /\ MEM w i2.inst_outputs ==> (i1 = i2)) ==>
    FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u
Proof
  rpt gen_tac >> strip_tac >>
  (Cases_on `dfg_get_def (dfg_build_function fn) u`
   >- (irule run_block_untracked_flookup >> metis_tac[])) >>
  rename1 `dfg_get_def _ u = SOME inst_u` >>
  `~MEM inst_u bb.bb_instructions` by
    metis_tac[operand_not_in_block] >>
  irule run_block_non_output_flookup >>
  qexistsl_tac [`bb`, `ctx`, `fuel`] >> simp[] >>
  rpt strip_tac >>
  `MEM u inst_u.inst_outputs /\ MEM inst_u (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `MEM inst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
  `inst = inst_u` by metis_tac[] >>
  metis_tac[]
QED

(* Within a block of a well-formed function, instructions are all distinct *)
Theorem block_insts_all_distinct[local]:
  !fn bb.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks ==>
    ALL_DISTINCT bb.bb_instructions
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    (gvs[fn_inst_ids_distinct_def] >>
     irule ALL_DISTINCT_FLAT_IMP >>
     qexists_tac `MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions)
       fn.fn_blocks` >>
     simp[MEM_MAP] >> qexists_tac `bb` >> simp[]) >>
  metis_tac[ALL_DISTINCT_MAP]
QED

(* SSA + distinct IDs: no OTHER instruction in the same block outputs v *)
Theorem no_other_output_v[local]:
  !fn bb j v dinst.
    fn_inst_ids_distinct fn /\ MEM bb fn.fn_blocks /\
    j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = dinst /\
    MEM v dinst.inst_outputs /\ MEM dinst (fn_insts fn) /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) ==>
    !k. k <> j /\ k < LENGTH bb.bb_instructions ==>
      ~MEM v (EL k bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `MEM (EL k bb.bb_instructions) (fn_insts fn)` by
    (irule mem_bb_fn_insts >> qexists_tac `bb` >>
     simp[MEM_EL] >> qexists_tac `k` >> simp[]) >>
  `EL k bb.bb_instructions = dinst` by metis_tac[] >>
  `ALL_DISTINCT bb.bb_instructions` by
    metis_tac[block_insts_all_distinct] >>
  metis_tac[ALL_DISTINCT_EL_IMP]
QED

(* Helper: unrolling one step of exec_block when the instruction is not
   a terminator. If exec_block succeeds from s at position j, and EL j
   is not a terminator, then step succeeds and exec_block continues from
   the next position with the same final result. *)
Theorem exec_block_step_continuation:
  !fuel ctx bb s r.
    exec_block fuel ctx bb s = OK r /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    ~is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode ==>
    ?s1.
      step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s = OK s1 /\
      exec_block fuel ctx bb (s1 with vs_inst_idx := SUC s.vs_inst_idx) = OK r
Proof
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  simp[get_instruction_def] >>
  Cases_on `step_inst fuel ctx (EL s.vs_inst_idx bb.bb_instructions) s` >>
  simp[]
QED

Triviality dfg_tracked_not_terminator[local]:
  !opc. dfg_tracked_opcode opc ==> ~is_terminator opc
Proof
  simp[dfg_tracked_opcode_def] >> rpt strip_tac >> gvs[is_terminator_def]
QED

(* Case B setup: when dinst is at position j in bb, extract intermediate
   states and show that v and operand FLOOKUPs at exit relate to step j.
   Tracked opcodes are not terminators, so suffix preservation applies. *)
Theorem case_b_setup[local]:
  !fn bb fuel ctx s r v dinst.
    run_block fuel ctx bb s = OK r /\
    s.vs_inst_idx = 0 /\
    MEM bb fn.fn_blocks /\
    MEM dinst bb.bb_instructions /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    dinst.inst_outputs = [v] /\
    dfg_tracked_opcode dinst.inst_opcode /\
    wf_function fn /\ fn_inst_wf fn /\
    dfg_block_local fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    ?s_j s_j1.
      step_inst fuel ctx dinst s_j = OK s_j1 /\
      FLOOKUP r.vs_vars v = FLOOKUP s_j1.vs_vars v /\
      FLOOKUP s_j.vs_vars v = FLOOKUP s.vs_vars v /\
      (!u. MEM (Var u) dinst.inst_operands /\
           ~MEM u dinst.inst_outputs ==>
        FLOOKUP r.vs_vars u = FLOOKUP s_j.vs_vars u)
Proof
  rpt gen_tac >> strip_tac >>
  `~is_terminator dinst.inst_opcode` by
    metis_tac[dfg_tracked_not_terminator] >>
  `MEM dinst (fn_insts fn)` by metis_tac[mem_bb_fn_insts] >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  `?j. j < LENGTH bb.bb_instructions /\ EL j bb.bb_instructions = dinst` by
    metis_tac[MEM_EL] >>
  `!i. i < j ==> ~is_terminator (EL i bb.bb_instructions).inst_opcode` by
    (rpt strip_tac >> `i < LENGTH bb.bb_instructions - 1` by simp[] >>
     metis_tac[]) >>
  `phi_prefix_length bb.bb_instructions <= j` by
    (irule phi_prefix_length_le_non_phi_el >> simp[] >>
     gvs[dfg_tracked_opcode_def]) >>
  mp_tac (Q.SPECL [`bb`,`fuel`,`ctx`,`s`,`r`,`j`] run_block_decompose) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`s_j`, `s_j1`] >> simp[] >>
  (* Establish continuation: exec_block from SUC j gives r *)
  qspecl_then [`fuel`,`ctx`,`bb`,`s_j`] mp_tac exec_block_step_continuation >>
  simp[] >> strip_tac >>
  (* SSA: v not output at other positions *)
  qspecl_then [`fn`,`bb`,`j`,`v`,`dinst`] mp_tac no_other_output_v >>
  simp[] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  (* Conjunct 1: FLOOKUP r v = FLOOKUP s_j1 v (suffix) *)
  conj_tac
  >- (
    qspecl_then [`fuel`,`ctx`,`bb`,
      `s_j1 with vs_inst_idx := SUC j`,`r`,`v`]
      mp_tac exec_block_suffix_non_output_flookup >>
    simp[] >> (impl_tac >- (rpt strip_tac >> first_x_assum irule >> simp[])) >>
    simp[]) >>
  (* Conjunct 2: FLOOKUP s_j v = FLOOKUP s v (prefix) *)
  conj_tac
  >- (first_x_assum irule >> simp[]) >>
  (* Conjunct 3: operands preserved.
     u <> v and outputs=[v], so step j preserves u.
     No later instruction writes u (tracked_operand_no_later_output). *)
  rpt strip_tac >>
  (* Step 1: step j preserves u *)
  qspecl_then [`fuel`, `ctx`, `dinst`, `s_j`, `s_j1`]
    mp_tac step_preserves_non_output_vars >>
  (impl_tac >- simp[]) >> disch_then (qspec_then `u` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  (* Step 2: no later instruction outputs u *)
  `!k. SUC j <= k /\ k < LENGTH bb.bb_instructions ==>
       ~MEM u (EL k bb.bb_instructions).inst_outputs` by
    (rpt gen_tac >> strip_tac >>
     `j < k` by simp[] >>
     match_mp_tac tracked_operand_no_later_output >>
     MAP_EVERY qexists_tac [`fn`,`v`,`dinst`,`j`] >>
     simp[] >> metis_tac[]) >>
  (* Step 3: suffix preserves u *)
  qspecl_then [`fuel`,`ctx`,`bb`,
     `s_j1 with vs_inst_idx := SUC j`,`r`,`u`]
     mp_tac exec_block_suffix_non_output_flookup >>
  simp[] >> strip_tac >> gvs[lookup_var_def]
QED

(* Derive inst_outputs = [v] from dfg_get_def + opcode + fn_inst_wf.
   Wraps dfg_tracked_inst_outputs with better tactic interface. *)
Theorem derive_inst_outputs[local]:
  !fn v inst.
    dfg_get_def (dfg_build_function fn) v = SOME inst /\
    fn_inst_wf fn /\ dfg_tracked_opcode inst.inst_opcode ==>
    inst.inst_outputs = [v]
Proof
  metis_tac[dfg_tracked_inst_outputs]
QED

(* bool_to_word b ≠ 0w ⟺ b.
   Used by EQ/COMPARE/ISZERO Case B to extract the boolean condition. *)
Theorem bool_to_word_neq_0w[local]:
  !b. bool_to_word b <> 0w <=> b
Proof
  Cases >> simp[bool_to_word_def]
QED

val compare_step_output_opcode_tac =
  rpt strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = OK _` mp_tac >>
  simp[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
       update_var_def, FLOOKUP_UPDATE, bool_to_word_neq_0w,
       WORD_LTi, WORD_GTi] >>
  strip_tac >>
  gvs[FLOOKUP_UPDATE, bool_to_word_neq_0w]

Theorem compare_step_output_lt[local]:
  !fuel ctx inst s s1 v lhs rhs w x y.
    inst.inst_opcode = LT /\ inst.inst_operands = [lhs; rhs] /\
    inst.inst_outputs = [v] /\ step_inst fuel ctx inst s = OK s1 /\
    eval_operand lhs s = SOME x /\ eval_operand rhs s = SOME y /\
    FLOOKUP s1.vs_vars v = SOME w ==>
    (w <> 0w <=> w2n x < w2n y)
Proof
  compare_step_output_opcode_tac
QED

Theorem compare_step_output_gt[local]:
  !fuel ctx inst s s1 v lhs rhs w x y.
    inst.inst_opcode = GT /\ inst.inst_operands = [lhs; rhs] /\
    inst.inst_outputs = [v] /\ step_inst fuel ctx inst s = OK s1 /\
    eval_operand lhs s = SOME x /\ eval_operand rhs s = SOME y /\
    FLOOKUP s1.vs_vars v = SOME w ==>
    (w <> 0w <=> w2n x > w2n y)
Proof
  compare_step_output_opcode_tac
QED

Theorem compare_step_output_slt[local]:
  !fuel ctx inst s s1 v lhs rhs w x y.
    inst.inst_opcode = SLT /\ inst.inst_operands = [lhs; rhs] /\
    inst.inst_outputs = [v] /\ step_inst fuel ctx inst s = OK s1 /\
    eval_operand lhs s = SOME x /\ eval_operand rhs s = SOME y /\
    FLOOKUP s1.vs_vars v = SOME w ==>
    (w <> 0w <=> w2i x < w2i y)
Proof
  compare_step_output_opcode_tac
QED

Theorem compare_step_output_sgt[local]:
  !fuel ctx inst s s1 v lhs rhs w x y.
    inst.inst_opcode = SGT /\ inst.inst_operands = [lhs; rhs] /\
    inst.inst_outputs = [v] /\ step_inst fuel ctx inst s = OK s1 /\
    eval_operand lhs s = SOME x /\ eval_operand rhs s = SOME y /\
    FLOOKUP s1.vs_vars v = SOME w ==>
    (w <> 0w <=> w2i x > w2i y)
Proof
  compare_step_output_opcode_tac
QED

Theorem compare_step_output[local]:
  !fuel ctx inst s s1 v lhs rhs w x y.
    (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
     inst.inst_opcode = SLT \/ inst.inst_opcode = SGT) /\
    inst.inst_operands = [lhs; rhs] /\
    inst.inst_outputs = [v] /\
    step_inst fuel ctx inst s = OK s1 /\
    eval_operand lhs s = SOME x /\
    eval_operand rhs s = SOME y /\
    FLOOKUP s1.vs_vars v = SOME w ==>
    (w <> 0w <=>
     if inst.inst_opcode = LT then w2n x < w2n y
     else if inst.inst_opcode = GT then w2n x > w2n y
     else if inst.inst_opcode = SLT then w2i x < w2i y
     else w2i x > w2i y)
Proof
  rpt strip_tac >> gvs[] >| [
    qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s1`, `v`, `lhs`, `rhs`,
                 `w`, `x`, `y`] mp_tac compare_step_output_lt >> simp[],
    qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s1`, `v`, `lhs`, `rhs`,
                 `w`, `x`, `y`] mp_tac compare_step_output_gt >> simp[],
    qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s1`, `v`, `lhs`, `rhs`,
                 `w`, `x`, `y`] mp_tac compare_step_output_slt >> simp[],
    qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s1`, `v`, `lhs`, `rhs`,
                 `w`, `x`, `y`] mp_tac compare_step_output_sgt >> simp[]]
QED

Theorem compare_case_b_from_step[local]:
  !fuel ctx inst s s1 r v lhs rhs.
    (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
     inst.inst_opcode = SLT \/ inst.inst_opcode = SGT) /\
    inst.inst_operands = [lhs; rhs] /\
    inst.inst_outputs = [v] /\
    step_inst fuel ctx inst s = OK s1 /\
    FLOOKUP r.vs_vars v = FLOOKUP s1.vs_vars v /\
    (!u. MEM (Var u) inst.inst_operands /\ ~MEM u inst.inst_outputs ==>
         FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u) /\
    ~MEM (Var v) inst.inst_operands ==>
    !w. FLOOKUP r.vs_vars v = SOME w ==>
      (!u wl wu. lhs = Var u /\ rhs = Lit wl /\
         FLOOKUP r.vs_vars u = SOME wu ==>
         (w <> 0w <=>
          if inst.inst_opcode = LT then w2n wu < w2n wl
          else if inst.inst_opcode = GT then w2n wu > w2n wl
          else if inst.inst_opcode = SLT then w2i wu < w2i wl
          else w2i wu > w2i wl)) /\
      (!u wl wu. rhs = Var u /\ lhs = Lit wl /\
         FLOOKUP r.vs_vars u = SOME wu ==>
         (w <> 0w <=>
          if inst.inst_opcode = LT then w2n wl < w2n wu
          else if inst.inst_opcode = GT then w2n wl > w2n wu
          else if inst.inst_opcode = SLT then w2i wl < w2i wu
          else w2i wl > w2i wu))
Proof
  rpt strip_tac >> gvs[] >>
  `FLOOKUP s1.vs_vars v = SOME w` by metis_tac[] >>
  `FLOOKUP s.vs_vars u = SOME wu` by metis_tac[] >>
  FIRST [
    qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s1`, `v`, `Var u`, `Lit wl`,
                 `w`, `wu`, `wl`] mp_tac compare_step_output >>
    (impl_tac >- gvs[eval_operand_def, lookup_var_def]) >> simp[],
    qspecl_then [`fuel`, `ctx`, `inst`, `s`, `s1`, `v`, `Lit wl`, `Var u`,
                 `w`, `wl`, `wu`] mp_tac compare_step_output >>
    (impl_tac >- gvs[eval_operand_def, lookup_var_def]) >> simp[]]
QED

(* Case A setup: if dinst not in bb, then v and all operand vars preserved.
   Combines run_block_tracked_not_in_bb + operand_flookup_preserved_not_in_bb. *)
Theorem case_a_setup[local]:
  !fn bb fuel ctx s r v dinst.
    run_block fuel ctx bb s = OK r /\
    s.vs_inst_idx = 0 /\
    MEM bb fn.fn_blocks /\
    ~MEM dinst bb.bb_instructions /\
    dfg_get_def (dfg_build_function fn) v = SOME dinst /\
    dinst.inst_outputs = [v] /\
    dfg_tracked_opcode dinst.inst_opcode /\
    wf_function fn /\ fn_inst_wf fn /\
    dfg_block_local fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) ==>
    FLOOKUP r.vs_vars v = FLOOKUP s.vs_vars v /\
    (!u. MEM (Var u) dinst.inst_operands ==>
         FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u)
Proof
  metis_tac[run_block_tracked_not_in_bb,
            operand_flookup_preserved_not_in_bb]
QED

(* Helper: dfg_assign_sound preserved through run_block *)
Theorem dfg_assign_sound_run_block[local]:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_assign_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt strip_tac >>
  simp[dfg_assign_sound_def] >> rpt strip_tac >>
  `dfg_tracked_opcode inst.inst_opcode` by (simp[dfg_tracked_opcode_def]) >>
  imp_res_tac derive_inst_outputs >>
  Cases_on `MEM inst bb.bb_instructions`
  >- ( (* Case B: inst is in this block, executed and wrote v *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_b_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >>
    strip_tac >>
    gvs[step_inst_non_invoke, step_inst_base_def, update_var_def,
        eval_operand_def, lookup_var_def, AllCaseEqs()] >>
    gvs[FLOOKUP_UPDATE] >>
    Cases_on `u = v` >> gvs[FLOOKUP_UPDATE])
  >- ( (* Case A: inst is not in this block, FLOOKUP preserved *)
    EVERY [
      (mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
        case_a_setup) >> (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac),
      gvs[dfg_sound_def, dfg_assign_sound_def, TO_FLOOKUP, MEM]
    ])
QED

(* Helper: dfg_iszero_sound preserved through run_block *)
Theorem dfg_iszero_sound_run_block[local]:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_iszero_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt strip_tac >>
  simp[dfg_iszero_sound_def] >> rpt gen_tac >> strip_tac >>
  `dfg_tracked_opcode inst.inst_opcode` by (simp[dfg_tracked_opcode_def]) >>
  imp_res_tac derive_inst_outputs >>
  Cases_on `MEM inst bb.bb_instructions`
  >- ( (* Case B *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_b_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    gvs[step_inst_non_invoke, step_inst_base_def, exec_pure1_def,
        update_var_def, eval_operand_def, lookup_var_def,
        AllCaseEqs(), FLOOKUP_UPDATE] >>
    Cases_on `tv = v`
    >- ( (* Self-referential: derive contradiction from dfg_iszero_sound *)
      gvs[] >>
      EVERY [
        (`dfg_iszero_sound (dfg_build_function fn) s.vs_vars` by
          gvs[dfg_sound_def]),
        qpat_x_assum `dfg_iszero_sound _ _` mp_tac,
        simp[dfg_iszero_sound_def],
        qexistsl_tac [`tv`, `inst`, `tv`],
        simp[],
        Cases_on `x = 0w` >> simp[bool_to_word_def]
      ])
    >- ( (* tv <> v: use FLOOKUP preservation *)
      gvs[FLOOKUP_UPDATE] >>
      Cases_on `x = 0w` >> gvs[bool_to_word_def]))
  >- ( (* Case A *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_a_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    gvs[dfg_sound_def, dfg_iszero_sound_def, MEM] >>
    metis_tac[])
QED

(* Helper: dfg_iszero_lit_sound preserved through run_block *)
Theorem dfg_iszero_lit_sound_run_block:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    dfg_iszero_lit_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_iszero_lit_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt strip_tac >>
  simp[dfg_iszero_lit_sound_def] >> rpt gen_tac >> strip_tac >>
  `dfg_tracked_opcode inst.inst_opcode` by (simp[dfg_tracked_opcode_def]) >>
  imp_res_tac derive_inst_outputs >>
  Cases_on `MEM inst bb.bb_instructions`
  >- ( (* Case B: inst in block *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_b_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    gvs[step_inst_non_invoke, step_inst_base_def, exec_pure1_def,
        update_var_def, eval_operand_def, lookup_var_def,
        AllCaseEqs(), FLOOKUP_UPDATE] >>
    Cases_on `n = 0w` >> gvs[bool_to_word_def])
  >- ( (* Case A: inst not in block — FLOOKUP preserved *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_a_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    `v IN FDOM s.vs_vars` by
      (Cases_on `FLOOKUP s.vs_vars v` >> gvs[flookup_thm]) >>
    qpat_x_assum `dfg_iszero_lit_sound _ s.vs_vars` mp_tac >>
    PURE_ONCE_REWRITE_TAC [dfg_iszero_lit_sound_def] >> strip_tac >>
    res_tac >> gvs[])
QED

(* Helper: dfg_eq_sound preserved through run_block *)
Theorem dfg_eq_sound_run_block[local]:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_eq_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt strip_tac >>
  simp[dfg_eq_sound_def] >> rpt gen_tac >> strip_tac >>
  `dfg_tracked_opcode inst.inst_opcode` by (simp[dfg_tracked_opcode_def]) >>
  imp_res_tac derive_inst_outputs >>
  Cases_on `MEM inst bb.bb_instructions`
  >- ( (* Case B: inst in block — use case_b_setup *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_b_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    `~MEM (Var v) inst.inst_operands` by
      metis_tac[dfg_block_local_no_self_ref] >>
    gvs[step_inst_non_invoke, step_inst_base_def, exec_pure2_def,
        update_var_def, eval_operand_def, lookup_var_def,
        AllCaseEqs(), FLOOKUP_UPDATE, bool_to_word_neq_0w] >>
    rpt strip_tac >>
    gvs[FLOOKUP_UPDATE, MEM, eval_operand_def, lookup_var_def])
  >- ( (* Case A: inst not in block — FLOOKUP preserved *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_a_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    `dfg_eq_sound (dfg_build_function fn) s.vs_vars` by
      gvs[dfg_sound_def] >>
    qpat_x_assum `dfg_eq_sound _ s.vs_vars` mp_tac >>
    PURE_ONCE_REWRITE_TAC [dfg_eq_sound_def] >>
    disch_tac >> rpt strip_tac >>
    first_x_assum (qspecl_then [`v`, `inst`, `lhs`, `rhs`] mp_tac) >>
    simp[] >> gvs[MEM] >> metis_tac[])
QED

(* Helper: dfg_compare_sound preserved through run_block *)
Theorem dfg_compare_sound_run_block[local]:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_compare_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt strip_tac >>
  simp[dfg_compare_sound_def] >> rpt gen_tac >> DISCH_TAC >>
  `dfg_tracked_opcode inst.inst_opcode` by (metis_tac[dfg_tracked_opcode_def]) >>
  `inst.inst_outputs = [v]` by metis_tac[derive_inst_outputs] >>
  Cases_on `MEM inst bb.bb_instructions`
  >- ( (* Case B: inst in block *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_b_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    qspecl_then [`fuel`, `ctx`, `inst`, `s_j`, `s_j1`, `r`, `v`, `lhs`, `rhs`]
      mp_tac compare_case_b_from_step >>
    (impl_tac >- (rpt conj_tac >>
      (first_assum ACCEPT_TAC ORELSE metis_tac[dfg_block_local_no_self_ref]))) >>
    simp[])
  >- ( (* Case A: inst not in block *)
    sg `FLOOKUP r.vs_vars v = FLOOKUP s.vs_vars v /\
        (!u. MEM (Var u) inst.inst_operands ==>
             FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u)`
    >- (irule case_a_setup >> simp[dfg_tracked_opcode_def] >> metis_tac[]) >>
    `dfg_compare_sound (dfg_build_function fn) s.vs_vars` by
      gvs[dfg_sound_def] >>
    qpat_x_assum `dfg_compare_sound _ s.vs_vars` mp_tac >>
    PURE_ONCE_REWRITE_TAC [dfg_compare_sound_def] >>
    disch_tac >>
    first_x_assum (qspecl_then [`v`, `inst`, `lhs`, `rhs`] mp_tac) >>
    (impl_tac >- metis_tac[]) >>
    gvs[MEM] >> rpt strip_tac >>
    qpat_x_assum `!u. _ ==> FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u`
      (qspec_then `u` mp_tac) >>
    simp[] >> strip_tac >> gvs[] >>
    FIRST [
      qpat_x_assum `!u wl wu. lhs = Var u /\ rhs = Lit wl /\
          FLOOKUP s.vs_vars u = SOME wu ==> _`
        (qspecl_then [`u`, `wl`, `wu`] mp_tac),
      qpat_x_assum `!u wl wu. rhs = Var u /\ lhs = Lit wl /\
          FLOOKUP s.vs_vars u = SOME wu ==> _`
        (qspecl_then [`u`, `wl`, `wu`] mp_tac)] >>
    simp[])
QED

Theorem exec_pure1_var_operand_defined[local]:
  !f inst s s' u.
    exec_pure1 f inst s = OK s' /\
    MEM (Var u) inst.inst_operands ==>
    ?w. FLOOKUP s.vs_vars u = SOME w
Proof
  rpt strip_tac >>
  gvs[exec_pure1_def, AllCaseEqs(), eval_operand_def, lookup_var_def]
QED

Theorem exec_pure2_var_operand_defined[local]:
  !f inst s s' u.
    exec_pure2 f inst s = OK s' /\
    MEM (Var u) inst.inst_operands ==>
    ?w. FLOOKUP s.vs_vars u = SOME w
Proof
  rpt strip_tac >>
  gvs[exec_pure2_def, AllCaseEqs(), eval_operand_def, lookup_var_def]
QED

Theorem step_inst_base_assign_operand_defined[local]:
  !inst s s' u.
    inst.inst_opcode = ASSIGN /\ step_inst_base inst s = OK s' /\
    MEM (Var u) inst.inst_operands ==>
    ?w. FLOOKUP s.vs_vars u = SOME w
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  simp[AllCaseEqs(), eval_operand_def, lookup_var_def] >>
  strip_tac >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem step_inst_base_iszero_operand_defined[local]:
  !inst s s' u.
    inst.inst_opcode = ISZERO /\ step_inst_base inst s = OK s' /\
    MEM (Var u) inst.inst_operands ==>
    ?w. FLOOKUP s.vs_vars u = SOME w
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def] >> strip_tac >>
  drule_all exec_pure1_var_operand_defined >> simp[]
QED

val pure2_tracked_operand_defined_tac =
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >> simp[] >> strip_tac >>
  drule_all exec_pure2_var_operand_defined >> simp[];

Theorem step_inst_base_pure2_tracked_operand_defined[local]:
  !inst s s' u.
    (inst.inst_opcode = EQ \/ inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
     inst.inst_opcode = SLT \/ inst.inst_opcode = SGT \/
     inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    step_inst_base inst s = OK s' /\ MEM (Var u) inst.inst_operands ==>
    ?w. FLOOKUP s.vs_vars u = SOME w
Proof
  rpt strip_tac >> gvs[]
  >- pure2_tracked_operand_defined_tac
  >- pure2_tracked_operand_defined_tac
  >- pure2_tracked_operand_defined_tac
  >- pure2_tracked_operand_defined_tac
  >- pure2_tracked_operand_defined_tac
  >- pure2_tracked_operand_defined_tac
  >- pure2_tracked_operand_defined_tac
QED

val tracked_operand_defined_tac =
  metis_tac[step_inst_base_assign_operand_defined,
            step_inst_base_iszero_operand_defined,
            step_inst_base_pure2_tracked_operand_defined]

(* Helper: if a tracked-opcode instruction succeeds via step_inst_base,
   all Var operands were defined in the input state. *)
Theorem step_inst_base_tracked_operand_defined[local]:
  !inst s s' u.
    dfg_tracked_opcode inst.inst_opcode /\
    step_inst_base inst s = OK s' /\
    MEM (Var u) inst.inst_operands ==>
    ?w. FLOOKUP s.vs_vars u = SOME w
Proof
  rpt strip_tac >>
  gvs[dfg_tracked_opcode_def] >>
  tracked_operand_defined_tac
QED

(* Helper: ops_defined preserved through run_block *)
Theorem dfg_ops_defined_run_block[local]:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s.vs_vars) /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    !vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM r.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM r.vs_vars
Proof
  rpt strip_tac >>
  `dinst.inst_outputs = [vv]` by
    (mp_tac (Q.SPECL [`fn`, `vv`, `dinst`] dfg_tracked_inst_outputs) >>
     simp[]) >>
  Cases_on `MEM dinst bb.bb_instructions`
  >- ( (* Case B: dinst in bb — operand u was defined at s_j *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `vv`, `dinst`]
      case_b_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >>
    strip_tac >>
    EVERY [
      (`dinst.inst_opcode <> INVOKE` by
        gvs[dfg_tracked_opcode_def]),
      (`step_inst_base dinst s_j = OK s_j1` by
        metis_tac[step_inst_non_invoke]),
      (`~MEM (Var vv) dinst.inst_operands` by
        (CCONTR_TAC >> gvs[] >>
         metis_tac[dfg_block_local_no_self_ref])),
      (`~MEM u dinst.inst_outputs` by (gvs[MEM] >> metis_tac[])),
      (`FLOOKUP r.vs_vars u = FLOOKUP s_j.vs_vars u` by
        (first_x_assum irule >> simp[])),
      (`?w. FLOOKUP s_j.vs_vars u = SOME w` by
        metis_tac[step_inst_base_tracked_operand_defined]),
      gvs[TO_FLOOKUP]
    ])
  >- ( (* Case A: dinst not in bb *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `vv`, `dinst`]
      case_a_setup) >>
    (impl_tac >- (gvs[dfg_tracked_opcode_def] >> metis_tac[])) >>
    strip_tac >>
    EVERY [
      (`vv IN FDOM s.vs_vars` by gvs[TO_FLOOKUP]),
      (`u IN FDOM s.vs_vars` by metis_tac[]),
      (`FLOOKUP r.vs_vars u = FLOOKUP s.vs_vars u` by
        (first_x_assum irule >> simp[])),
      gvs[TO_FLOOKUP]
    ])
QED

(* eval_op_env op env = eval_operand op s when env = s.vs_vars,
   for non-Label operands. Label operands disagree:
   eval_op_env returns NONE, eval_operand uses vs_labels. *)
Theorem eval_op_env_eval_operand:
  !op s. (!lbl. op <> Label lbl) ==>
         eval_op_env op s.vs_vars = eval_operand op s
Proof
  Cases >> simp[eval_op_env_def, eval_operand_def, lookup_var_def]
QED

(* If eval_op_env returns SOME, the operand is not a Label *)
Theorem eval_op_env_some_not_label:
  !op env w. eval_op_env op env = SOME w ==> (!lbl. op <> Label lbl)
Proof
  Cases >> simp[eval_op_env_def]
QED

(* eval_op_env is determined by FLOOKUP at variable positions *)
Theorem eval_op_env_flookup_eq[local]:
  !op env1 env2.
    (!u. op = Var u ==> FLOOKUP env1 u = FLOOKUP env2 u) ==>
    eval_op_env op env1 = eval_op_env op env2
Proof
  Cases >> simp[eval_op_env_def]
QED

Theorem arith_step_outputs[local]:
  !inst s s1 v op1 op2.
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    inst.inst_operands = [op1; op2] /\ inst.inst_outputs = [v] /\
    (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) /\
    step_inst_base inst s = OK s1 ==>
    ?w1 w2.
      eval_op_env op1 s.vs_vars = SOME w1 /\
      eval_op_env op2 s.vs_vars = SOME w2 /\
      FLOOKUP s1.vs_vars v = SOME (if inst.inst_opcode = ADD then w1 + w2 else w1 - w2)
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  gvs[] >| [
    simp[step_inst_base_def, exec_pure2_def, update_var_def, FLOOKUP_UPDATE] >>
    strip_tac >>
    `eval_op_env op1 s.vs_vars = eval_operand op1 s` by
      metis_tac[eval_op_env_eval_operand] >>
    `eval_op_env op2 s.vs_vars = eval_operand op2 s` by
      metis_tac[eval_op_env_eval_operand] >>
    Cases_on `eval_operand op1 s` >> gvs[] >>
    rename1 `eval_operand op1 s = SOME w1` >>
    Cases_on `eval_operand op2 s` >> gvs[] >>
    rename1 `eval_operand op2 s = SOME w2` >>
    gvs[FLOOKUP_UPDATE],
    simp[step_inst_base_def, exec_pure2_def, update_var_def, FLOOKUP_UPDATE] >>
    strip_tac >>
    `eval_op_env op1 s.vs_vars = eval_operand op1 s` by
      metis_tac[eval_op_env_eval_operand] >>
    `eval_op_env op2 s.vs_vars = eval_operand op2 s` by
      metis_tac[eval_op_env_eval_operand] >>
    Cases_on `eval_operand op1 s` >> gvs[] >>
    rename1 `eval_operand op1 s = SOME w1` >>
    Cases_on `eval_operand op2 s` >> gvs[] >>
    rename1 `eval_operand op2 s = SOME w2` >>
    gvs[FLOOKUP_UPDATE]]
QED

(* dfg_arith_sound preserved through run_block.
   Uses case_a/case_b infrastructure with ADD/SUB. *)
Theorem dfg_arith_sound_run_block:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    dfg_arith_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_arith_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt strip_tac >>
  simp[dfg_arith_sound_def] >> rpt gen_tac >> DISCH_TAC >>
  `MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `?bb'. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions` by
    metis_tac[fn_insts_mem_block] >>
  `dfg_tracked_opcode inst.inst_opcode` by
    (gvs[dfg_tracked_opcode_def]) >>
  `inst.inst_outputs = [v]` by metis_tac[derive_inst_outputs] >>
  Cases_on `MEM inst bb.bb_instructions`
  >- ( (* Case B: inst in this block *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_b_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >>
    strip_tac >>
    `~MEM (Var v) inst.inst_operands` by
      metis_tac[dfg_block_local_no_self_ref] >>
    `step_inst_base inst s_j = OK s_j1` by
      (gvs[step_inst_non_invoke]) >>
    `eval_op_env op1 r.vs_vars = eval_op_env op1 s_j.vs_vars` by
      (irule eval_op_env_flookup_eq >> rpt strip_tac >>
       qpat_x_assum `!u. MEM (Var u) inst.inst_operands /\ _ ==> _`
         (qspec_then `u` mp_tac) >>
       (impl_tac >- (gvs[MEM] >> metis_tac[])) >> simp[]) >>
    `eval_op_env op2 r.vs_vars = eval_op_env op2 s_j.vs_vars` by
      (irule eval_op_env_flookup_eq >> rpt strip_tac >>
       qpat_x_assum `!u. MEM (Var u) inst.inst_operands /\ _ ==> _`
         (qspec_then `u` mp_tac) >>
       (impl_tac >- (gvs[MEM] >> metis_tac[])) >> simp[]) >>
    qspecl_then [`inst`, `s_j`, `s_j1`, `v`, `op1`, `op2`]
      mp_tac arith_step_outputs >>
    (impl_tac >- metis_tac[]) >>
    strip_tac >>
    qexistsl_tac [`w1`, `w2`] >> gvs[])
  >- ( (* Case A: inst not in this block *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_a_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    `v IN FDOM s.vs_vars` by
      (gvs[TO_FLOOKUP] >> metis_tac[]) >>
    `eval_op_env op1 r.vs_vars = eval_op_env op1 s.vs_vars` by
      (irule eval_op_env_flookup_eq >> rpt strip_tac >>
       qpat_x_assum `!u. MEM (Var u) inst.inst_operands ==> _`
         (qspec_then `u` mp_tac) >>
       (impl_tac >- gvs[MEM]) >> simp[]) >>
    `eval_op_env op2 r.vs_vars = eval_op_env op2 s.vs_vars` by
      (irule eval_op_env_flookup_eq >> rpt strip_tac >>
       qpat_x_assum `!u. MEM (Var u) inst.inst_operands ==> _`
         (qspec_then `u` mp_tac) >>
       (impl_tac >- gvs[MEM]) >> simp[]) >>
    qpat_x_assum `dfg_arith_sound _ s.vs_vars` mp_tac >>
    simp[dfg_arith_sound_def] >> disch_tac >>
    first_x_assum (qspecl_then [`v`, `inst`, `op1`, `op2`] mp_tac) >>
    (impl_tac >- metis_tac[]) >>
    simp[])
QED

Theorem compare_full_step_outputs[local]:
  !inst s s1 v op1 op2.
    (inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
    inst.inst_operands = [op1; op2] /\ inst.inst_outputs = [v] /\
    (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) /\
    step_inst_base inst s = OK s1 ==>
    ?w1 w2.
      eval_op_env op1 s.vs_vars = SOME w1 /\
      eval_op_env op2 s.vs_vars = SOME w2 /\
      FLOOKUP s1.vs_vars v =
        SOME (bool_to_word (if inst.inst_opcode = LT then w2n w1 < w2n w2 else w2n w1 > w2n w2))
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  gvs[] >| [
    simp[step_inst_base_def, exec_pure2_def, update_var_def, FLOOKUP_UPDATE] >>
    strip_tac >>
    `eval_op_env op1 s.vs_vars = eval_operand op1 s` by
      metis_tac[eval_op_env_eval_operand] >>
    `eval_op_env op2 s.vs_vars = eval_operand op2 s` by
      metis_tac[eval_op_env_eval_operand] >>
    Cases_on `eval_operand op1 s` >> gvs[] >>
    rename1 `eval_operand op1 s = SOME w1` >>
    Cases_on `eval_operand op2 s` >> gvs[] >>
    rename1 `eval_operand op2 s = SOME w2` >>
    gvs[FLOOKUP_UPDATE],
    simp[step_inst_base_def, exec_pure2_def, update_var_def, FLOOKUP_UPDATE] >>
    strip_tac >>
    `eval_op_env op1 s.vs_vars = eval_operand op1 s` by
      metis_tac[eval_op_env_eval_operand] >>
    `eval_op_env op2 s.vs_vars = eval_operand op2 s` by
      metis_tac[eval_op_env_eval_operand] >>
    Cases_on `eval_operand op1 s` >> gvs[] >>
    rename1 `eval_operand op1 s = SOME w1` >>
    Cases_on `eval_operand op2 s` >> gvs[] >>
    rename1 `eval_operand op2 s = SOME w2` >>
    gvs[FLOOKUP_UPDATE]]
QED

(* dfg_compare_full_sound preserved through run_block.
   Uses case_a/case_b infrastructure with LT/GT (arbitrary operands). *)
Theorem dfg_compare_full_sound_run_block:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    dfg_compare_full_sound (dfg_build_function fn) s.vs_vars /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_compare_full_sound (dfg_build_function fn) r.vs_vars
Proof
  rpt strip_tac >>
  simp[dfg_compare_full_sound_def] >> rpt gen_tac >> DISCH_TAC >>
  `MEM v inst.inst_outputs /\ MEM inst (fn_insts fn)` by
    metis_tac[dfg_build_function_correct] >>
  `?bb'. MEM bb' fn.fn_blocks /\ MEM inst bb'.bb_instructions` by
    metis_tac[fn_insts_mem_block] >>
  `dfg_tracked_opcode inst.inst_opcode` by
    (gvs[dfg_tracked_opcode_def]) >>
  `inst.inst_outputs = [v]` by metis_tac[derive_inst_outputs] >>
  Cases_on `MEM inst bb.bb_instructions`
  >- ( (* Case B: inst in this block *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_b_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >>
    strip_tac >>
    `~MEM (Var v) inst.inst_operands` by
      metis_tac[dfg_block_local_no_self_ref] >>
    `step_inst_base inst s_j = OK s_j1` by
      (gvs[step_inst_non_invoke]) >>
    `eval_op_env op1 r.vs_vars = eval_op_env op1 s_j.vs_vars` by
      (irule eval_op_env_flookup_eq >> rpt strip_tac >>
       qpat_x_assum `!u. MEM (Var u) inst.inst_operands /\ _ ==> _`
         (qspec_then `u` mp_tac) >>
       (impl_tac >- (gvs[MEM] >> metis_tac[])) >> simp[]) >>
    `eval_op_env op2 r.vs_vars = eval_op_env op2 s_j.vs_vars` by
      (irule eval_op_env_flookup_eq >> rpt strip_tac >>
       qpat_x_assum `!u. MEM (Var u) inst.inst_operands /\ _ ==> _`
         (qspec_then `u` mp_tac) >>
       (impl_tac >- (gvs[MEM] >> metis_tac[])) >> simp[]) >>
    qspecl_then [`inst`, `s_j`, `s_j1`, `v`, `op1`, `op2`]
      mp_tac compare_full_step_outputs >>
    (impl_tac >- metis_tac[]) >>
    strip_tac >>
    qexistsl_tac [`w1`, `w2`] >> gvs[])
  >- ( (* Case A: inst not in this block *)
    mp_tac (Q.SPECL [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`, `v`, `inst`]
      case_a_setup) >>
    (impl_tac >- (simp[dfg_tracked_opcode_def] >> metis_tac[])) >> strip_tac >>
    `v IN FDOM s.vs_vars` by
      (gvs[TO_FLOOKUP] >> metis_tac[]) >>
    `eval_op_env op1 r.vs_vars = eval_op_env op1 s.vs_vars` by
      (irule eval_op_env_flookup_eq >> rpt strip_tac >>
       qpat_x_assum `!u. MEM (Var u) inst.inst_operands ==> _`
         (qspec_then `u` mp_tac) >>
       (impl_tac >- gvs[MEM]) >> simp[]) >>
    `eval_op_env op2 r.vs_vars = eval_op_env op2 s.vs_vars` by
      (irule eval_op_env_flookup_eq >> rpt strip_tac >>
       qpat_x_assum `!u. MEM (Var u) inst.inst_operands ==> _`
         (qspec_then `u` mp_tac) >>
       (impl_tac >- gvs[MEM]) >> simp[]) >>
    qpat_x_assum `dfg_compare_full_sound _ s.vs_vars` mp_tac >>
    simp[dfg_compare_full_sound_def] >> disch_tac >>
    first_x_assum (qspecl_then [`v`, `inst`, `op1`, `op2`] mp_tac) >>
    (impl_tac >- metis_tac[]) >>
    simp[])
QED

(* dfg_sound + ops_defined preserved through run_block.
   Requires dfg_block_local to handle the overwrite case in loops. *)
Theorem dfg_sound_run_block:
  !fn bb fuel ctx s r.
    dfg_sound (dfg_build_function fn) s.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM s.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM s.vs_vars) /\
    wf_function fn /\ fn_inst_wf fn /\
    (!v i1 i2. MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
       MEM v i1.inst_outputs /\ MEM v i2.inst_outputs ==> (i1 = i2)) /\
    ALL_DISTINCT (fn_labels fn) /\
    dfg_block_local fn /\
    (!bb. MEM bb fn.fn_blocks ==>
      !i. i < LENGTH bb.bb_instructions - 1 ==>
        ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    MEM bb fn.fn_blocks /\
    s.vs_inst_idx = 0 /\
    run_block fuel ctx bb s = OK r ==>
    dfg_sound (dfg_build_function fn) r.vs_vars /\
    (!vv dinst u. dfg_get_def (dfg_build_function fn) vv = SOME dinst /\
       vv IN FDOM r.vs_vars /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM r.vs_vars)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[dfg_sound_def] >> rpt conj_tac >> (
      irule dfg_assign_sound_run_block ORELSE
      irule dfg_iszero_sound_run_block ORELSE
      irule dfg_eq_sound_run_block ORELSE
      irule dfg_compare_sound_run_block) >>
      metis_tac[])
  >- (rpt strip_tac >> qspecl_then [`fn`, `bb`, `fuel`, `ctx`, `s`, `r`]
      mp_tac dfg_ops_defined_run_block >>
      simp[] >> disch_then drule_all >> simp[])
QED

(* Like step_jnz_behavior but without constraining inst_outputs *)
Theorem step_jnz_behavior_gen[local]:
  !s cond_op if_nonzero if_zero id outputs cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst_base
      <|inst_id := id; inst_opcode := JNZ;
        inst_operands := [cond_op; Label if_nonzero; Label if_zero];
        inst_outputs := outputs|> s =
    if cond <> 0w then OK (jump_to if_nonzero s)
    else OK (jump_to if_zero s)
Proof
  rw[step_inst_base_def]
QED

(* After running a block ending with JNZ [Var var; Label t; Label f],
   the condition variable exists in the output state with the right polarity. *)
Theorem run_block_jnz_condition:
  !fuel ctx bb s v var true_lbl false_lbl.
    run_block fuel ctx bb s = OK v /\
    s.vs_inst_idx = 0 /\
    EVERY inst_wf bb.bb_instructions /\
    bb.bb_instructions <> [] /\
    (!i. i < LENGTH bb.bb_instructions - 1 ==>
       ~is_terminator (EL i bb.bb_instructions).inst_opcode) /\
    (LAST bb.bb_instructions).inst_opcode = JNZ /\
    (LAST bb.bb_instructions).inst_operands =
      [Var var; Label true_lbl; Label false_lbl] /\
    true_lbl <> false_lbl ==>
    ?w. FLOOKUP v.vs_vars var = SOME w /\
        (v.vs_current_bb = true_lbl ==> w <> 0w) /\
        (v.vs_current_bb = false_lbl ==> w = 0w)
Proof
  rpt strip_tac >>
  qabbrev_tac `ti = PRE (LENGTH bb.bb_instructions)` >>
  `ti < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[Abbr `ti`]) >>
  `EL ti bb.bb_instructions = LAST bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> fs[Abbr `ti`, LAST_EL]) >>
  `phi_prefix_length bb.bb_instructions <= ti` by
    (irule phi_prefix_length_le_non_phi_el >> simp[] >>
     qpat_x_assum `EL ti _ = LAST _` SUBST1_TAC >> simp[]) >>
  (* Decompose run_block to get state just before JNZ *)
  mp_tac run_block_decompose >>
  disch_then (qspecl_then [`bb`, `fuel`, `ctx`, `s`, `v`, `ti`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >> rename1 `step_inst _ _ _ s_j = OK s_j1` >>
  (* Extract eval_operand from step_inst success *)
  `?cond. eval_operand (Var var) s_j = SOME cond` by (
    qpat_x_assum `step_inst _ _ (EL ti _) _ = OK _` mp_tac >>
    simp[step_inst_def, step_inst_base_def] >>
    Cases_on `eval_operand (Var var) s_j` >> simp[]) >>
  `FLOOKUP s_j.vs_vars var = SOME cond` by
    fs[eval_operand_def, lookup_var_def] >>
  (* v = s_j1: unfold exec_block at position ti, JNZ is a terminator *)
  qpat_x_assum `exec_block _ _ _ s_j = OK v` mp_tac >>
  CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  fs[venomInstTheory.get_instruction_def] >>
  simp[is_terminator_def] >>
  strip_tac >>
  pop_assum mp_tac >> gvs[] >> strip_tac >> gvs[] >>
  (* s_j1 has the right branch and variable *)
  qexists_tac `cond` >>
  qpat_x_assum `step_inst _ _ _ s_j = OK s_j1` mp_tac >>
  rw[step_inst_def, step_inst_base_def] >>
  BasicProvers.EVERY_CASE_TAC >> gvs[jump_to_def]
QED
