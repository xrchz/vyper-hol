(*
 * Assert Combiner Pass — Chain Proofs (Part 1)
 *
 * Preconditions:
 *   - wf_ssa fn: SSA with def-dominates-use
 *   - Freshness: original operands don't reference ac_or_*/ac_iz_* fresh vars
 *   - s.vs_inst_idx = 0: the transform inserts OR/ISZERO (1:N expansion)
 *   - ac_inv: DFG relationships hold at runtime + all operands evaluable
 *
 * R_ok = state_equiv (ac_fresh_vars_fn fn)
 * R_term = execution_equiv UNIV
 *   (UNIV because NOP'd first assert changes abort point; middle instructions
 *    may modify non-fresh variables before the combined assert aborts)
 *
 * Strategy: block_sim_function_inv_cross, direct per-block sim (no reversed
 * triangle needed since R_term = UNIV tolerates all variable differences).
 *)

Theory acChainProofs
Ancestors
  acBaseProofs assertCombinerDefs passSimulationDefs passSimulationProps
  stateEquiv stateEquivProps execEquivParamProps venomInstProps venomExecProps
  dfgAnalysisProps venomState venomWf venomExecSemantics venomExecProofs
  analysisSimDefs analysisSimProofsBase
Libs
  pred_setTheory arithmeticTheory listTheory rich_listTheory alistTheory

(* Quotation-free tactic helpers.
   Workaround for HOL4 QTY_TAC type inference bug in prove(...) where
   qexists_tac/qexistsl_tac/qspecl_then cause "Type constraint failure:
   s :venom_state Constraint: :operand" when existential witnesses of
   different types appear in the same composed tactic. *)
fun find_free_var name (asl, w) =
  let val vs = free_varsl (w::asl)
  in valOf (List.find (fn v => fst (dest_var v) = name) vs) end;

fun exists_var_tac name (g as (asl, w)) =
  Tactic.EXISTS_TAC (find_free_var name g) g;

fun exists_vars_tac names = Tactical.EVERY (map exists_var_tac names);

(* Apply a function to a free variable by name, producing a tactic *)
fun with_var name (f : term -> tactic) (g as (asl, w)) : goal list * validation =
  f (find_free_var name g) g;

(* specl_then with variable names instead of quotations *)
fun specl_vars_then names ttac thm (g as (asl, w)) =
  let val tms = map (fn n => find_free_var n g) names
  in ttac (SPECL tms thm) g end;

(* exists_tac with a term-building function applied to free vars *)
fun exists_term_tac f names (g as (asl, w)) =
  let val tms = map (fn n => find_free_var n g) names
  in Tactic.EXISTS_TAC (f tms) g end;

(* Normalize record constructor to record literal form.
   HOL4 treats instruction n o l l0 and <|inst_id:=n;...|> as
   syntactically different terms. This bridges them. *)
Theorem instruction_to_literal[simp]:
  instruction n op ops outs =
    <|inst_id := n; inst_opcode := op;
      inst_operands := ops; inst_outputs := outs|>
Proof
  simp[venomInstTheory.instruction_component_equality]
QED

(* ===== Rewrite as function_map_transform ===== *)

Theorem ac_transform_as_fmt:
  !fn.
    ac_transform_function fn =
    function_map_transform (ac_transform_block (dfg_build_function fn)) fn
Proof
  rw[ac_transform_function_def, function_map_transform_def, LET_THM]
QED

Theorem ac_transform_block_label:
  !dfg bb. (ac_transform_block dfg bb).bb_label = bb.bb_label
Proof
  rw[ac_transform_block_def, LET_THM]
QED

(* ===== Runtime Invariant ===== *)

Definition ac_dfg_inv_def:
  ac_dfg_inv dfg s <=>
    (!v inst input_op.
       dfg_get_def dfg v = SOME inst /\
       inst.inst_opcode = ISZERO /\
       inst.inst_operands = [input_op] /\
       IS_SOME (lookup_var v s) ==>
       ?input_val.
         eval_operand input_op s = SOME input_val /\
         lookup_var v s = SOME (bool_to_word (input_val = 0w))) /\
    (!v inst src_op.
       dfg_get_def dfg v = SOME inst /\
       inst.inst_opcode = ASSIGN /\
       inst.inst_operands = [src_op] /\
       IS_SOME (lookup_var v s) ==>
       lookup_var v s = eval_operand src_op s)
End

(* Bridge: ac_get_iszero_operand + ac_dfg_inv ==> lookup_var relates to pred value.
   Traces through ASSIGN chains in the DFG to find the ISZERO source, using
   ac_dfg_inv to maintain the relationship at each step. *)
Theorem ac_dfg_iszero_bridge:
  !dfg visited op s pred.
    ac_dfg_inv dfg s /\
    ac_get_iszero_operand dfg visited op = SOME pred /\
    IS_SOME (eval_operand op s) ==>
    ?pred_val. eval_operand pred s = SOME pred_val /\
               eval_operand op s = SOME (bool_to_word (pred_val = 0w))
Proof
  recInduct ac_get_iszero_operand_ind >> rpt strip_tac >>
  qpat_x_assum `ac_get_iszero_operand _ _ _ = _` mp_tac >>
  simp[Once ac_get_iszero_operand_def] >>
  Cases_on `op` >> simp[] >>
  Cases_on `dfg_get_def dfg s'` >> simp[] >>
  strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  Cases_on `x.inst_opcode = ISZERO` >> simp[] >>
  Cases_on `x.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> strip_tac
  >- (
    (* ISZERO case: x is ISZERO [pred], use ac_dfg_inv directly *)
    fs[ac_dfg_inv_def, eval_operand_def] >> metis_tac[]
  )
  >- (
    (* ASSIGN case: x is ASSIGN [h], ac_get_iszero_operand recurses on h *)
    fs[ac_dfg_inv_def] >>
    (* Use ASSIGN clause: lookup_var s' s = eval_operand h s *)
    `lookup_var s' s = eval_operand h s` by (
      first_x_assum match_mp_tac >> simp[] >>
      fs[eval_operand_def]) >>
    (* Apply IH: ac_dfg_inv + IS_SOME(eval h s) ==> bridge for h *)
    first_x_assum (qspec_then `s` mp_tac) >> impl_tac
    >- (simp[ac_dfg_inv_def] >> fs[eval_operand_def] >> gvs[])
    >- (strip_tac >> fs[eval_operand_def] >> gvs[])
  )
QED

(* Corollary: when ASSERT passes (nonzero), the underlying pred is 0w *)
Theorem ac_assert_pass_pred_zero:
  !dfg s v pred val.
    ac_dfg_inv dfg s /\
    ac_get_iszero_operand dfg {} (Var v) = SOME pred /\
    eval_operand (Var v) s = SOME val /\ val <> 0w ==>
    eval_operand pred s = SOME 0w
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand (Var v) s)` by simp[optionTheory.IS_SOME_DEF] >>
  drule_all ac_dfg_iszero_bridge >> strip_tac >> gvs[] >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED

(* Dual: when ASSERT aborts (operand is 0w), the underlying pred is nonzero *)
Theorem ac_assert_abort_pred_nonzero:
  !dfg s v pred.
    ac_dfg_inv dfg s /\
    ac_get_iszero_operand dfg {} (Var v) = SOME pred /\
    eval_operand (Var v) s = SOME 0w ==>
    ?pred_val. eval_operand pred s = SOME pred_val /\ pred_val <> 0w
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand (Var v) s)` by simp[optionTheory.IS_SOME_DEF] >>
  drule_all ac_dfg_iszero_bridge >> strip_tac >>
  qexists_tac `pred_val` >> simp[] >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED

(* ===== Local (prefix-restricted) DFG invariant =====
   Same as ac_dfg_inv but restricted to DFG entries whose defining instruction
   satisfies predicate P. Used to handle loops where cross-block DFG entries
   may temporarily violate ac_dfg_inv. *)

Definition ac_dfg_inv_local_def:
  ac_dfg_inv_local dfg P s <=>
    (!v inst input_op.
       dfg_get_def dfg v = SOME inst /\
       P inst /\
       inst.inst_opcode = ISZERO /\
       inst.inst_operands = [input_op] /\
       IS_SOME (lookup_var v s) ==>
       ?input_val.
         eval_operand input_op s = SOME input_val /\
         lookup_var v s = SOME (bool_to_word (input_val = 0w))) /\
    (!v inst src_op.
       dfg_get_def dfg v = SOME inst /\
       P inst /\
       inst.inst_opcode = ASSIGN /\
       inst.inst_operands = [src_op] /\
       IS_SOME (lookup_var v s) ==>
       lookup_var v s = eval_operand src_op s)
End

(* ac_dfg_inv implies ac_dfg_inv_local for any P *)
Theorem ac_dfg_inv_implies_local:
  !dfg P s. ac_dfg_inv dfg s ==> ac_dfg_inv_local dfg P s
Proof
  simp[ac_dfg_inv_def, ac_dfg_inv_local_def] >> metis_tac[]
QED

(* ac_dfg_inv_local with P = \i. T is equivalent to ac_dfg_inv *)
Theorem ac_dfg_inv_local_T:
  !dfg s. ac_dfg_inv_local dfg (\i. T) s <=> ac_dfg_inv dfg s
Proof
  simp[ac_dfg_inv_def, ac_dfg_inv_local_def]
QED

(* Antitonicity: restricting P preserves the invariant *)
Theorem ac_dfg_inv_local_restrict:
  !dfg P Q s. ac_dfg_inv_local dfg P s /\ (!i. Q i ==> P i) ==>
    ac_dfg_inv_local dfg Q s
Proof
  rw[ac_dfg_inv_local_def] >> res_tac >> metis_tac[]
QED

(* Bridge for local invariant: same as ac_dfg_iszero_bridge but uses
   ac_dfg_inv_local. Requires that all DFG entries with defined outputs
   satisfy P. *)
Theorem ac_dfg_iszero_bridge_local:
  !dfg visited op s pred P.
    ac_dfg_inv_local dfg P s /\
    ac_get_iszero_operand dfg visited op = SOME pred /\
    IS_SOME (eval_operand op s) /\
    (!v inst. dfg_get_def dfg v = SOME inst /\ IS_SOME (lookup_var v s) ==>
       P inst) ==>
    ?pred_val. eval_operand pred s = SOME pred_val /\
               eval_operand op s = SOME (bool_to_word (pred_val = 0w))
Proof
  recInduct ac_get_iszero_operand_ind >> rpt strip_tac >>
  qpat_x_assum `ac_get_iszero_operand _ _ _ = _` mp_tac >>
  simp[Once ac_get_iszero_operand_def] >>
  Cases_on `op` >> simp[] >>
  Cases_on `dfg_get_def dfg s'` >> simp[] >>
  strip_tac >>
  qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
  Cases_on `x.inst_opcode = ISZERO` >> simp[] >>
  Cases_on `x.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> strip_tac >>
  Cases_on `x.inst_opcode = ASSIGN` >> gvs[]
  >- (
    (* ISZERO case: use ISZERO clause of ac_dfg_inv_local *)
    qpat_x_assum `ac_dfg_inv_local _ _ _` mp_tac >>
    simp[ac_dfg_inv_local_def] >> strip_tac >>
    qpat_x_assum `!v inst input_op. _ /\ _ /\ _.inst_opcode = ISZERO /\ _ ==> _`
      (qspecl_then [`s'`, `x`, `h`] mp_tac) >>
    simp[] >> (impl_tac >- (fs[eval_operand_def] >> res_tac)) >>
    strip_tac >> simp[eval_operand_def] >> metis_tac[]
  )
  (* ASSIGN case: derive eval h from inv, then apply IH *)
  >>
  (Q.SUBGOAL_THEN `IS_SOME (lookup_var s' s)` ASSUME_TAC >-
    fs[eval_operand_def])
  >>
  (Q.SUBGOAL_THEN `P (x:instruction)` ASSUME_TAC >- res_tac)
  >>
  (Q.SUBGOAL_THEN `lookup_var s' s = eval_operand h s` ASSUME_TAC >- (
    qpat_x_assum `ac_dfg_inv_local _ _ _` mp_tac >>
    simp[ac_dfg_inv_local_def] >> strip_tac >>
    qpat_x_assum `!v inst src_op. _ /\ _ /\ _.inst_opcode = ASSIGN /\ _ ==> _`
      (qspecl_then [`s'`, `x`, `h`] mp_tac) >> simp[]))
  >>
  (Q.SUBGOAL_THEN `IS_SOME (eval_operand h s)` ASSUME_TAC >- gvs[]) >>
  qpat_x_assum `!s'' P'. _` (qspecl_then [`s`, `P`] mp_tac) >>
  strip_tac >> first_x_assum mp_tac >> (impl_tac >- metis_tac[]) >> strip_tac >> gvs[eval_operand_def]
QED

(* Corollary: ASSERT passes => pred = 0w (local version) *)
Theorem ac_assert_pass_pred_zero_local:
  !dfg s v pred val P.
    ac_dfg_inv_local dfg P s /\
    ac_get_iszero_operand dfg {} (Var v) = SOME pred /\
    eval_operand (Var v) s = SOME val /\ val <> 0w /\
    (!v' inst. dfg_get_def dfg v' = SOME inst /\ IS_SOME (lookup_var v' s) ==>
       P inst) ==>
    eval_operand pred s = SOME 0w
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand (Var v) s)` by simp[optionTheory.IS_SOME_DEF] >>
  drule_all ac_dfg_iszero_bridge_local >> strip_tac >> gvs[] >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED

(* Corollary: ASSERT aborts => pred nonzero (local version) *)
Theorem ac_assert_abort_pred_nonzero_local:
  !dfg s v pred P.
    ac_dfg_inv_local dfg P s /\
    ac_get_iszero_operand dfg {} (Var v) = SOME pred /\
    eval_operand (Var v) s = SOME 0w /\
    (!v' inst. dfg_get_def dfg v' = SOME inst /\ IS_SOME (lookup_var v' s) ==>
       P inst) ==>
    ?pred_val. eval_operand pred s = SOME pred_val /\ pred_val <> 0w
Proof
  rpt strip_tac >>
  `IS_SOME (eval_operand (Var v) s)` by simp[optionTheory.IS_SOME_DEF] >>
  drule_all ac_dfg_iszero_bridge_local >> strip_tac >>
  qexists_tac `pred_val` >> simp[] >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED


Definition ac_inv_def:
  ac_inv fn dfg s <=>
    ac_dfg_inv dfg s /\
    (!bb inst op.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    (* SSA freshness: defined vars are instruction outputs *)
    (!x. lookup_var x s <> NONE ==>
       ?bb inst. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
                 MEM x inst.inst_outputs)
End

(* ===== valid_state_rel for state_equiv/execution_equiv UNIV ===== *)

Theorem valid_state_rel_UNIV:
  !vars. valid_state_rel (state_equiv vars) (execution_equiv UNIV)
Proof
  simp[execEquivParamDefsTheory.valid_state_rel_def,
       stateEquivTheory.state_equiv_def,
       stateEquivTheory.execution_equiv_def,
       venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def,
       venomStateTheory.eval_operand_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `op` >> fs[venomStateTheory.eval_operand_def,
                       venomStateTheory.lookup_var_def]
QED

(* ===== Lift result helpers ===== *)

Theorem execution_equiv_weaken_UNIV[local]:
  !vars s1 s2. execution_equiv vars s1 s2 ==> execution_equiv UNIV s1 s2
Proof
  rw[stateEquivTheory.execution_equiv_def]
QED

Theorem lift_result_weaken_UNIV:
  !R vars r1 r2.
    lift_result R (execution_equiv vars) (execution_equiv vars) r1 r2 ==>
    lift_result R (execution_equiv UNIV) (execution_equiv UNIV) r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  fs[lift_result_def, execution_equiv_weaken_UNIV] >>
  metis_tac[execution_equiv_weaken_UNIV]
QED

(* ===== run_insts infrastructure ===== *)

Theorem run_insts_append:
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

(* Appending a NOP instruction to a successful run_insts is still OK *)
Theorem run_insts_snoc_nop[local]:
  !insts nop fuel ctx s s'.
    run_insts fuel ctx insts s = OK s' /\
    nop.inst_opcode = NOP ==>
    run_insts fuel ctx (insts ++ [nop]) s = OK s'
Proof
  rw[run_insts_append, run_insts_singleton, step_nop_identity]
QED

(* Specialized: appending NOP to a 2-element run_insts *)
Theorem run_insts_two_snoc_nop:
  !a b nop fuel ctx s s'.
    run_insts fuel ctx [a; b] s = OK s' /\
    nop.inst_opcode = NOP ==>
    run_insts fuel ctx [a; b; nop] s = OK s'
Proof
  rpt strip_tac >>
  `[a; b; nop] = [a; b] ++ [nop]` by simp[] >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  irule run_insts_snoc_nop >> simp[]
QED

(* General: composing [a;b] with [c] when both succeed *)
Theorem run_insts_two_snoc:
  !a b c fuel ctx s s' s''.
    run_insts fuel ctx [a; b] s = OK s' /\
    step_inst fuel ctx c s' = OK s'' ==>
    run_insts fuel ctx [a; b; c] s = OK s''
Proof
  rpt strip_tac >>
  `[a; b; c] = [a; b] ++ [c]` by simp[] >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  simp[run_insts_append, run_insts_def]
QED

(* Rewrite [a;b;c] as [a;b] ++ [c] for run_insts decomposition *)
Theorem run_insts_three:
  !a b c fuel ctx s.
    run_insts fuel ctx [a; b; c] s =
    case run_insts fuel ctx [a; b] s of
      OK s' => run_insts fuel ctx [c] s'
    | Halt s' => Halt s'
    | Abort a' s' => Abort a' s'
    | IntRet v' s' => IntRet v' s'
    | Error e => Error e
Proof
  rpt gen_tac >>
  `[a; b; c] = [a; b] ++ [c]` by simp[] >>
  pop_assum (fn th => ONCE_REWRITE_TAC[th]) >>
  simp[run_insts_append]
QED

(* ===== Per-Block Simulation helpers ===== *)

Theorem run_insts_execution_equiv_UNIV[local]:
  !insts fuel ctx s s'.
    run_insts fuel ctx insts s = OK s' /\
    EVERY (\i. is_effect_free_op i.inst_opcode) insts ==>
    execution_equiv UNIV s s'
Proof
  Induct >> rw[run_insts_def] >- simp[execution_equiv_refl] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[] >>
  rename1 `step_inst _ _ h s = OK s1` >>
  `state_equiv (set h.inst_outputs) s s1` by
    metis_tac[step_effect_free_state_equiv] >>
  `execution_equiv UNIV s s1` by
    fs[state_equiv_def, execution_equiv_def] >>
  `execution_equiv UNIV s1 s'` by metis_tac[] >>
  metis_tac[execution_equiv_trans]
QED

Theorem step_eval_operand_preserved:
  !fuel ctx inst s s' op.
    step_inst fuel ctx inst s = OK s' /\
    ~is_terminator inst.inst_opcode /\
    (!x. op = Var x ==> ~MEM x inst.inst_outputs) ==>
    eval_operand op s' = eval_operand op s
Proof
  rpt strip_tac >> Cases_on `op` >>
  gvs[eval_operand_def] >>
  metis_tac[step_preserves_non_output_vars, step_preserves_labels]
QED

(* ac_safe_between_effect_free and safe_between_wf_step_ok are in acBaseProofsTheory *)

(* ===== FOLDL characterization ===== *)

(* When candidates = [], FOLDL produces the original list *)
Triviality FIND_nil[local,simp]:
  FIND P [] = NONE
Proof
  EVAL_TAC
QED

Triviality EXISTS_nil[local,simp]:
  EXISTS P [] <=> F
Proof
  EVAL_TAC
QED

Theorem ac_foldl_no_candidates[local]:
  !insts mp acc.
    SND (FOLDL (ac_apply_merge_step []) (mp, acc) insts) = acc ++ insts
Proof
  Induct >> simp[ac_apply_merge_step_def, LET_THM]
QED

(* ===== FOLDL decomposition infrastructure ===== *)

(* Helper: ac_apply_merge_step appends to acc *)
Theorem ac_step_appends[local]:
  !cands mp acc i.
    ?mp' stuff.
      ac_apply_merge_step cands (mp, acc) i = (mp', acc ++ stuff) /\
      ac_apply_merge_step cands (mp, []) i = (mp', stuff)
Proof
  rpt gen_tac >>
  simp[ac_apply_merge_step_def, LET_THM] >>
  Cases_on `FIND (\mc. mc.mc_second_id = i.inst_id) cands` >>
  simp[] >- (
    Cases_on `EXISTS (\mc. mc.mc_first_id = i.inst_id) cands` >>
    simp[]
  ) >>
  rename1 `FIND _ _ = SOME mc` >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> simp[] >- (
    IF_CASES_TAC >> simp[] >>
    Cases_on `EXISTS (\mc'. mc'.mc_first_id = i.inst_id) cands` >>
    simp[]
  ) >>
  IF_CASES_TAC >> simp[] >>
  Cases_on `EXISTS (\mc'. mc'.mc_first_id = i.inst_id) cands` >>
  simp[]
QED

(* The accumulator prefix passes through the FOLDL *)
Theorem ac_foldl_acc_prefix[local]:
  !insts cands mp acc.
    SND (FOLDL (ac_apply_merge_step cands) (mp, acc) insts) =
    acc ++ SND (FOLDL (ac_apply_merge_step cands) (mp, []) insts)
Proof
  Induct >> simp[] >>
  rpt gen_tac >>
  qspecl_then [`cands`, `mp`, `acc`, `h`] strip_assume_tac ac_step_appends >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  pop_assum (fn th => REWRITE_TAC[th]) >>
  first_assum (qspecl_then [`cands`, `mp'`, `stuff`] mp_tac) >>
  first_x_assum (qspecl_then [`cands`, `mp'`, `acc ++ stuff`] mp_tac) >>
  simp[]
QED

(* Decompose FOLDL on i::rest *)
Theorem ac_foldl_cons:
  !i rest cands mp.
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) i in
    SND (FOLDL (ac_apply_merge_step cands) (mp, []) (i :: rest)) =
    contrib ++ SND (FOLDL (ac_apply_merge_step cands) (mp', []) rest)
Proof
  simp[] >> rpt gen_tac >>
  qabbrev_tac `result = ac_apply_merge_step cands (mp, []) i` >>
  Cases_on `result` >>
  simp[] >>
  qspecl_then [`rest`, `cands`, `q`, `r`] mp_tac ac_foldl_acc_prefix >>
  simp[]
QED

(* ===== Core: run_insts simulation for assert combiner ===== *)

(* When no candidates, transform is identity *)
Theorem ac_block_sim_same_no_cands:
  !dfg bb.
    ac_scan_block dfg bb.bb_instructions NONE = [] ==>
    ac_transform_block dfg bb = bb
Proof
  rw[ac_transform_block_def, LET_THM] >>
  qspecl_then [`bb.bb_instructions`, `[]`, `[]`]
    mp_tac ac_foldl_no_candidates >>
  simp[] >> strip_tac >>
  Cases_on `bb` >> gvs[venomInstTheory.basic_block_fn_updates, combinTheory.K_THM]
QED

(* word_or a b = 0w iff both zero *)
Theorem word_or_eq_0w:
  !(a:'a word) b. (word_or a b = 0w) <=> (a = 0w /\ b = 0w)
Proof
  rw[wordsTheory.word_or_def, wordsTheory.word_0,
     fcpTheory.CART_EQ, fcpTheory.FCP_BETA] >> metis_tac[]
QED

(* effect-free step preserves execution_equiv UNIV *)
Theorem step_effect_free_exec_equiv_UNIV[local]:
  !fuel ctx inst s s'.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode ==>
    execution_equiv UNIV s s'
Proof
  rpt strip_tac >>
  `state_equiv (set inst.inst_outputs) s s'` by
    metis_tac[step_effect_free_state_equiv] >>
  fs[state_equiv_def, execution_equiv_def]
QED

(* revert/set_returndata preserves execution_equiv UNIV *)
Theorem revert_returndata_exec_equiv_UNIV:
  !s s'. execution_equiv UNIV s s' ==>
    execution_equiv UNIV
      (revert_state (set_returndata [] s))
      (revert_state (set_returndata [] s'))
Proof
  rw[execution_equiv_def, revert_state_def, set_returndata_def]
QED

(* ===== Toolkit: ac_dfg_inv preservation ===== *)

(* effect-free step preserves revert-state execution_equiv *)
Theorem effect_free_preserves_revert_equiv[local]:
  !fuel ctx inst s s' abort_st.
    step_inst fuel ctx inst s = OK s' /\
    is_effect_free_op inst.inst_opcode /\
    execution_equiv UNIV abort_st (revert_state (set_returndata [] s))
  ==>
    execution_equiv UNIV abort_st (revert_state (set_returndata [] s'))
Proof
  rpt strip_tac >>
  `execution_equiv UNIV s s'` by metis_tac[step_effect_free_exec_equiv_UNIV] >>
  `execution_equiv UNIV (revert_state (set_returndata [] s))
                        (revert_state (set_returndata [] s'))` by
    metis_tac[revert_returndata_exec_equiv_UNIV] >>
  fs[execution_equiv_def]
QED
(* run_insts of effect-free instructions preserves execution_equiv UNIV *)
Triviality run_insts_effect_free_exec_equiv_UNIV[local]:
  !insts fuel ctx s s'.
    EVERY (\i. is_effect_free_op i.inst_opcode) insts /\
    run_insts fuel ctx insts s = OK s' ==>
    execution_equiv UNIV s s'
Proof
  Induct >> rw[run_insts_def]
  >- simp[execution_equiv_refl] >>
  gvs[EVERY_DEF] >>
  Cases_on `step_inst fuel ctx h s` >> gvs[] >>
  `execution_equiv UNIV s v` by
    metis_tac[step_effect_free_exec_equiv_UNIV] >>
  `execution_equiv UNIV v s'` by metis_tac[] >>
  metis_tac[execution_equiv_trans]
QED

(* Constructor-form step lemmas (avoiding literal form requirement) *)
Triviality step_iszero_con[local]:
  !s input_op out iid v.
    eval_operand input_op s = SOME v ==>
    step_inst_base (instruction iid ISZERO [input_op] [out]) s =
    OK (update_var out (bool_to_word (v = 0w)) s)
Proof
  rw[step_inst_base_def, exec_pure1_def, update_var_def]
QED

Triviality step_assign_con[local]:
  !s src_op out iid v.
    eval_operand src_op s = SOME v ==>
    step_inst_base (instruction iid ASSIGN [src_op] [out]) s =
    OK (update_var out v s)
Proof
  rw[step_inst_base_def, exec_pure1_def, update_var_def]
QED

(*
 * Shared tactic for the ~MEM branch of ac_dfg_inv_step:
 * variable not in step's outputs, so lookup_var and eval_operand preserved.
 *)
val ac_dfg_inv_preserved_tac =
  `lookup_var v s' = lookup_var v s` by
    metis_tac[step_preserves_non_output_vars] >>
  qpat_x_assum `ac_dfg_inv dfg s` mp_tac >>
  simp[ac_dfg_inv_def] >> strip_tac;

(* Shared tactic for establishing eval_operand preservation *)
val eval_op_preserved_tac =
  `!op. (!x. op = Var x ==> ~MEM x h.inst_outputs) ==>
        eval_operand op s' = eval_operand op s` by (
    rpt strip_tac >> Cases_on `op` >> gvs[eval_operand_def] >>
    metis_tac[step_preserves_non_output_vars, step_preserves_labels]);

Theorem ac_dfg_inv_step:
  !fuel ctx h s s' dfg.
    step_inst fuel ctx h s = OK s' /\
    ~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE /\
    inst_wf h /\
    ac_dfg_inv dfg s /\
    (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s)) /\
    (!v. MEM v h.inst_outputs /\ dfg_get_def dfg v <> NONE ==>
       dfg_get_def dfg v = SOME h) /\
    (* Self: h's operand vars not among h's outputs *)
    (!op x. MEM op h.inst_operands /\ op = Var x ==>
       ~MEM x h.inst_outputs) /\
    (* No-redefine: h doesn't redefine already-defined variables *)
    (!x. MEM x h.inst_outputs ==> ~IS_SOME (lookup_var x s))
  ==>
    ac_dfg_inv dfg s'
Proof
  rpt gen_tac >> strip_tac >>
  simp[ac_dfg_inv_def] >> rpt conj_tac
  >- (
    (* ISZERO conjunct *)
    rpt gen_tac >> strip_tac >>
    eval_op_preserved_tac >>
    Cases_on `MEM v h.inst_outputs`
    >- (
      (* Case 1: v in h's outputs => dfg entry IS h, use self-property *)
      (Q.SUBGOAL_THEN `dfg_get_def dfg v = SOME h` ASSUME_TAC >-
        (res_tac >> simp[])) >>
      gvs[] >>
      fs[optionTheory.IS_SOME_EXISTS] >>
      (Q.SUBGOAL_THEN `eval_operand input_op s' = eval_operand input_op s`
        ASSUME_TAC >-
        (first_x_assum match_mp_tac >> rpt strip_tac >> metis_tac[MEM])) >>
      Cases_on `h` >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[step_inst_non_invoke] >>
      imp_res_tac step_iszero_con >>
      gvs[update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE])
    >- (
      (* Case 2: v not in h's outputs.
         ac_dfg_inv gives eval_operand input_op s = SOME val.
         No-redefine contrapositive: ~MEM x h.inst_outputs.
         So eval_operand input_op is preserved s->s'. *)
      ac_dfg_inv_preserved_tac >>
      (Q.SUBGOAL_THEN `IS_SOME (lookup_var v s)` ASSUME_TAC >- gvs[]) >>
      qpat_x_assum `!v inst input_op. _ /\ inst.inst_opcode = ISZERO /\ _ ==> _`
        (qspecl_then [`v`, `inst`, `input_op`] mp_tac) >>
      simp[] >> strip_tac >>
      (Q.SUBGOAL_THEN `eval_operand input_op s' = eval_operand input_op s`
        ASSUME_TAC >-
        (first_x_assum match_mp_tac >> rpt strip_tac >> gvs[] >>
         gvs[eval_operand_def, optionTheory.IS_SOME_EXISTS] >>
         metis_tac[optionTheory.NOT_IS_SOME_EQ_NONE])) >>
      gvs[])
  )
  >- (
    (* ASSIGN conjunct *)
    rpt gen_tac >> strip_tac >>
    eval_op_preserved_tac >>
    Cases_on `MEM v h.inst_outputs`
    >- (
      (Q.SUBGOAL_THEN `dfg_get_def dfg v = SOME h` ASSUME_TAC >-
        (res_tac >> simp[])) >>
      gvs[] >>
      fs[optionTheory.IS_SOME_EXISTS] >>
      (Q.SUBGOAL_THEN `eval_operand src_op s' = eval_operand src_op s`
        ASSUME_TAC >-
        (first_x_assum match_mp_tac >> rpt strip_tac >> metis_tac[MEM])) >>
      Cases_on `h` >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[step_inst_non_invoke] >>
      imp_res_tac step_assign_con >>
      gvs[update_var_def, lookup_var_def, eval_operand_def,
          finite_mapTheory.FLOOKUP_UPDATE])
    >- (
      ac_dfg_inv_preserved_tac >>
      (Q.SUBGOAL_THEN `IS_SOME (lookup_var v s)` ASSUME_TAC >- gvs[]) >>
      qpat_x_assum `!v inst src_op. _ /\ inst.inst_opcode = ASSIGN /\ _ ==> _`
        (qspecl_then [`v`, `inst`, `src_op`] mp_tac) >>
      simp[] >> strip_tac >>
      (Q.SUBGOAL_THEN `eval_operand src_op s' = eval_operand src_op s`
        ASSUME_TAC >-
        (first_x_assum match_mp_tac >> rpt strip_tac >> gvs[] >>
         gvs[eval_operand_def, optionTheory.IS_SOME_EXISTS] >>
         metis_tac[optionTheory.NOT_IS_SOME_EQ_NONE])) >>
      gvs[])
  )
QED

(* Shared helper tactic for the non-output cases of ac_dfg_inv_step_ssa. *)
fun ac_ssa_case2_tac op_name =
  (Q.SUBGOAL_THEN `lookup_var v s' = lookup_var v s` ASSUME_TAC >-
    metis_tac[step_preserves_non_output_vars]) >>
  (Q.SUBGOAL_THEN `IS_SOME (lookup_var v s)` ASSUME_TAC >- gvs[]) >>
  (Q.SUBGOAL_THEN `!op'. MEM op' inst.inst_operands ==>
     eval_operand op' s' = eval_operand op' s` ASSUME_TAC >-
    (rpt strip_tac >>
     first_x_assum (qspecl_then [`v`, `inst`, `op'`] mp_tac) >>
     simp[])) >>
  qpat_x_assum `ac_dfg_inv dfg s` mp_tac >>
  simp[ac_dfg_inv_def] >> strip_tac >>
  first_x_assum (qspecl_then [`v`, `inst`, op_name] mp_tac) >>
  simp[] >> strip_tac >>
  first_x_assum (qspecl_then [op_name] mp_tac) >>
  simp[MEM] >> strip_tac >> gvs[]

(* SSA-friendly variant: replaces no-redefine with a weaker condition
   that DFG-tracked operand variables are not among h's outputs.
   This is derivable from SSA ordering (def_dominates_uses). *)
Theorem ac_dfg_inv_step_ssa:
  !fuel ctx h s s' dfg.
    step_inst fuel ctx h s = OK s' /\
    ~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE /\
    inst_wf h /\
    ac_dfg_inv dfg s /\
    (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s)) /\
    (!v. MEM v h.inst_outputs /\ dfg_get_def dfg v <> NONE ==>
       dfg_get_def dfg v = SOME h) /\
    (!op x. MEM op h.inst_operands /\ op = Var x ==>
       ~MEM x h.inst_outputs) /\
    (* Weaker than no-redefine: for DFG entries whose output is defined
       and not overwritten by h, operand variables are not in h's outputs *)
    (!v di op x.
       dfg_get_def dfg v = SOME di /\ IS_SOME (lookup_var v s) /\
       ~MEM v h.inst_outputs /\
       MEM op di.inst_operands /\ op = Var x ==>
       ~MEM x h.inst_outputs)
  ==>
    ac_dfg_inv dfg s'
Proof
  rpt gen_tac >> strip_tac >>
  (* Establish a helper: for DFG entries not overwritten by h,
     their operand evals are preserved *)
  (Q.SUBGOAL_THEN
    `!v di op. dfg_get_def dfg v = SOME di /\
       IS_SOME (lookup_var v s) /\ ~MEM v h.inst_outputs /\
       MEM op di.inst_operands ==>
       eval_operand op s' = eval_operand op s`
    ASSUME_TAC >- (
      rpt strip_tac >>
      Cases_on `op` >> gvs[eval_operand_def]
      >- metis_tac[step_preserves_non_output_vars]
      >- metis_tac[step_preserves_labels, ac_is_safe_between_def,
                   venomInstPropsTheory.step_preserves_labels])) >>
  simp[ac_dfg_inv_def] >> rpt conj_tac
  >- (
    (* ISZERO conjunct *)
    rpt gen_tac >> strip_tac >>
    Cases_on `MEM v h.inst_outputs`
    >- (
      (Q.SUBGOAL_THEN `dfg_get_def dfg v = SOME h` ASSUME_TAC >-
        (res_tac >> simp[])) >>
      gvs[] >>
      fs[optionTheory.IS_SOME_EXISTS] >>
      eval_op_preserved_tac >>
      (Q.SUBGOAL_THEN `eval_operand input_op s' = eval_operand input_op s`
        ASSUME_TAC >-
        (first_x_assum match_mp_tac >> rpt strip_tac >> metis_tac[MEM])) >>
      Cases_on `h` >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[step_inst_non_invoke] >>
      imp_res_tac step_iszero_con >>
      gvs[update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE])
    >- ac_ssa_case2_tac `input_op`)
  >- (
    (* ASSIGN conjunct *)
    rpt gen_tac >> strip_tac >>
    Cases_on `MEM v h.inst_outputs`
    >- (
      (Q.SUBGOAL_THEN `dfg_get_def dfg v = SOME h` ASSUME_TAC >-
        (res_tac >> simp[])) >>
      gvs[] >>
      fs[optionTheory.IS_SOME_EXISTS] >>
      eval_op_preserved_tac >>
      (Q.SUBGOAL_THEN `eval_operand src_op s' = eval_operand src_op s`
        ASSUME_TAC >-
        (first_x_assum match_mp_tac >> rpt strip_tac >> metis_tac[MEM])) >>
      Cases_on `h` >> gvs[inst_wf_def, LENGTH_EQ_NUM_compute] >>
      gvs[step_inst_non_invoke] >>
      imp_res_tac step_assign_con >>
      gvs[update_var_def, lookup_var_def, eval_operand_def,
          finite_mapTheory.FLOOKUP_UPDATE])
    >- ac_ssa_case2_tac `src_op`)
QED



(* ac_dfg_inv preserved through update_var on a fresh variable.
   Fresh means: not in the DFG (neither as a definition nor as an operand). *)
Theorem ac_dfg_inv_update_fresh:
  !dfg s v val.
    ac_dfg_inv dfg s /\
    dfg_get_def dfg v = NONE /\
    (!di x. dfg_get_def dfg x = SOME di ==> ~MEM (Var v) di.inst_operands)
  ==>
    ac_dfg_inv dfg (update_var v val s)
Proof
  rpt strip_tac >> simp[ac_dfg_inv_def] >> rpt conj_tac >> rpt gen_tac >>
  strip_tac >>
  Cases_on `v' = v` >> gvs[] (* v'=v contradicts dfg_get_def v = NONE *)
  (* Remaining: ISZERO and ASSIGN with v' <> v.
     Key: operand op of dfg entry inst can't be Var v (from hyp), so
     eval_operand op (update_var v val s) = eval_operand op s *)
  >- (
    `~MEM (Var v) inst.inst_operands` by res_tac >>
    `eval_operand input_op (update_var v val s) = eval_operand input_op s` by (
      Cases_on `input_op` >>
      gvs[eval_operand_def, update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
    gvs[ac_dfg_inv_def, update_var_def, lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE]
  )
  >- (
    `~MEM (Var v) inst.inst_operands` by res_tac >>
    `eval_operand src_op (update_var v val s) = eval_operand src_op s` by (
      Cases_on `src_op` >>
      gvs[eval_operand_def, update_var_def, lookup_var_def,
          finite_mapTheory.FLOOKUP_UPDATE]) >>
    gvs[ac_dfg_inv_def, update_var_def, lookup_var_def,
        finite_mapTheory.FLOOKUP_UPDATE]
  )
QED

(* eval_operand preserved through update_var when operand doesn't reference v *)
Theorem eval_operand_update_var_neq:
  !op v val s.
    (!x. op = Var x ==> x <> v) ==>
    eval_operand op (update_var v val s) = eval_operand op s
Proof
  Cases >> simp[eval_operand_def, update_var_def, lookup_var_def,
                finite_mapTheory.FLOOKUP_UPDATE]
QED

(* OR step in constructor form *)
Triviality step_or_con[local]:
  !s op1 op2 out iid v1 v2.
    eval_operand op1 s = SOME v1 /\
    eval_operand op2 s = SOME v2 ==>
    step_inst_base (instruction iid OR [op1; op2] [out]) s =
    OK (update_var out (word_or v1 v2) s)
Proof
  rw[step_inst_base_def, exec_pure2_def, update_var_def]
QED

(* IS_SOME(eval_operand) is preserved by safe_between steps *)
Theorem safe_between_step_eval_is_some:
  !inst s s' fuel ctx op.
    ac_is_safe_between inst /\ inst_wf inst /\
    step_inst fuel ctx inst s = OK s' /\
    (!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)) /\
    IS_SOME (eval_operand op s) ==>
    IS_SOME (eval_operand op s')
Proof
  rpt strip_tac >> Cases_on `op` >- simp[eval_operand_def]
  >- (
    rename1 `Var v` >>
    fs[eval_operand_def] >>
    irule safe_between_step_is_some_mono >>
    metis_tac[])
  >- (fs[eval_operand_def] >>
      `s'.vs_labels = s.vs_labels` by
        metis_tac[step_preserves_labels, ac_is_safe_between_def] >>
      gvs[])
QED

(* run_insts on safe_between instructions: succeeds, preserves non-output
   eval_operand, and maintains execution_equiv UNIV. *)
Theorem run_insts_safe_between_ok[local]:
  !insts fuel ctx s.
    EVERY (\i. ac_is_safe_between i /\ inst_wf i) insts /\
    (!inst op. MEM inst insts /\ MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) ==>
    ?s'. run_insts fuel ctx insts s = OK s' /\
         (!op. (!i x. MEM i insts /\ op = Var x ==> ~MEM x i.inst_outputs) ==>
               eval_operand op s' = eval_operand op s) /\
         execution_equiv UNIV s s'
Proof
  Induct >- rw[run_insts_def, execution_equiv_refl] >>
  rpt strip_tac >>
  fs[EVERY_DEF] >>
  `!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s)` by
    (rpt strip_tac >> first_x_assum (qspecl_then [`h`, `op`] mp_tac) >>
     simp[]) >>
  drule_all safe_between_wf_step_ok >> strip_tac >>
  first_x_assum (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  rename1 `step_inst fuel ctx h s = OK s1` >>
  simp[run_insts_def] >>
  (* Apply IH *)
  first_x_assum (qspecl_then [`fuel`, `ctx`, `s1`] mp_tac) >>
  impl_tac >- (
    rpt strip_tac >>
    match_mp_tac safe_between_step_eval_is_some >>
    MAP_EVERY qexists_tac [`h`, `s`, `fuel`, `ctx`] >> simp[] >>
    first_x_assum (qspecl_then [`inst`, `op`] mp_tac) >> simp[]) >>
  strip_tac >> simp[] >>
  `~is_terminator h.inst_opcode` by fs[ac_is_safe_between_def] >>
  conj_tac
  >- (
    rpt strip_tac >>
    irule step_eval_operand_preserved >>
    MAP_EVERY qexists_tac [`ctx`, `fuel`, `h`] >> simp[] >>
    rpt strip_tac >> first_x_assum (qspecl_then [`h`, `Var x`] mp_tac) >>
    simp[])
  >- (
    `is_effect_free_op h.inst_opcode` by
      metis_tac[ac_safe_between_effect_free] >>
    `execution_equiv UNIV s s1` by
      metis_tac[step_effect_free_exec_equiv_UNIV] >>
    metis_tac[execution_equiv_trans])
QED

(* ===== Merge segment equivalence ===== *)

(*
 * Core helper: a single merge segment with different predicates.
 *
 * Original:  ASSERT(iz1) ; safe_middle ; ASSERT(iz2)
 * Transform: NOP         ; safe_middle ; OR(p1,p2); ISZERO(or_v); ASSERT(iz_v)
 *
 * where iz1 = bool_to_word(p1=0w), iz2 = bool_to_word(p2=0w)
 * by ac_dfg_inv.
 *
 * Both abort iff p1≠0 ∨ p2≠0.
 * On success (p1=p2=0), state_equiv V (only fresh vars differ).
 * On abort, execution_equiv UNIV (all intermediate steps effect-free).
 *)

(* Step 1: NOP always succeeds, preserving state exactly *)
(* Already have step_nop_identity from venomInstPropsTheory *)

(* Step 2: ASSERT succeeds iff condition is nonzero, state unchanged *)
Theorem step_assert_ok:
  !fuel ctx inst s cond_op cond.
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [cond_op] /\
    eval_operand cond_op s = SOME cond /\ cond <> 0w ==>
    step_inst fuel ctx inst s = OK s
Proof
  rpt strip_tac >> gvs[] >>
  Cases_on `inst` >> gvs[step_inst_non_invoke, step_inst_base_def]
QED

Theorem step_assert_abort:
  !fuel ctx inst s cond_op.
    inst.inst_opcode = ASSERT /\ inst.inst_operands = [cond_op] /\
    eval_operand cond_op s = SOME 0w ==>
    step_inst fuel ctx inst s =
      Abort Revert_abort (revert_state (set_returndata [] s))
Proof
  rpt strip_tac >> gvs[] >>
  Cases_on `inst` >> gvs[step_inst_non_invoke, step_inst_base_def]
QED

(* ===== run_insts FOLDL equivalence ===== *)

(*
 * Core equivalence: run_insts on original instructions vs FOLDL-transformed.
 *
 * Proof by Induct on instruction list. At each step, ac_foldl_cons
 * decomposes the FOLDL output as contrib_h ++ FOLDL(...rest).
 *
 * Cases for each instruction h:
 *   - Pass-through: contrib_h = [h], same step, recurse
 *   - NOP'd first: contrib_h = [nop_h], original ASSERT may abort
 *     - If ASSERT succeeds: state unchanged, NOP succeeds, recurse
 *     - If ASSERT aborts: need rest of transform to also abort
 *   - Second (diff preds): contrib_h = [OR; ISZERO; modified_assert]
 *     - Both check iszero(pred) — same abort behavior
 *   - Second (same preds): contrib_h = [h], same step, recurse
 *)

(* Helper: when first assert aborts (pred ≠ 0), running safe_middle
   then OR+ISZERO+ASSERT also aborts with execution_equiv UNIV.
   This handles the deferred-abort case. *)
Triviality ac_deferred_abort_segment[local]:
  !safe_middle or_inst iz_inst assert_inst fuel ctx s
   pred1 pred2 or_v iz_v abort_st.
    (* safe_middle instructions all succeed *)
    EVERY (\i. ac_is_safe_between i /\ inst_wf i) safe_middle /\
    (!inst op. MEM inst safe_middle /\ MEM op inst.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    (* OR, ISZERO, ASSERT structure *)
    or_inst.inst_opcode = OR /\
    or_inst.inst_operands = [pred1; pred2] /\
    or_inst.inst_outputs = [or_v] /\
    iz_inst.inst_opcode = ISZERO /\
    iz_inst.inst_operands = [Var or_v] /\
    iz_inst.inst_outputs = [iz_v] /\
    assert_inst.inst_opcode = ASSERT /\
    assert_inst.inst_operands = [Var iz_v] /\
    (* pred1 evaluates to nonzero *)
    eval_operand pred1 s = SOME v1 /\ v1 <> 0w /\
    eval_operand pred2 s = SOME v2 /\
    (* safe_between doesn't write to fresh or pred variables *)
    (!i. MEM i safe_middle ==> ~MEM or_v i.inst_outputs /\
                                ~MEM iz_v i.inst_outputs) /\
    (!i x. MEM i safe_middle /\ (pred1 = Var x \/ pred2 = Var x) ==>
       ~MEM x i.inst_outputs) /\
    (* abort_st is the revert state *)
    abort_st = revert_state (set_returndata [] s) ==>
    ?sa. run_insts fuel ctx
           (safe_middle ++ [or_inst; iz_inst; assert_inst]) s =
         Abort Revert_abort sa /\
         execution_equiv UNIV abort_st sa
Proof
  rpt strip_tac >>
  (* Step 1: safe_middle succeeds *)
  drule_all run_insts_safe_between_ok >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  rename1 `run_insts fuel ctx safe_middle s = OK s_mid` >>
  (* Step 2: split computation via run_insts_append *)
  simp[run_insts_append] >>
  (* Step 3: pred1/pred2 preserved through safe_middle *)
  `eval_operand pred1 s_mid = SOME v1` by (
    first_x_assum (qspec_then `pred1` mp_tac) >>
    impl_tac >- (rpt strip_tac >> Cases_on `pred1` >> gvs[] >> metis_tac[]) >>
    simp[]) >>
  `eval_operand pred2 s_mid = SOME v2` by (
    first_x_assum (qspec_then `pred2` mp_tac) >>
    impl_tac >- (rpt strip_tac >> Cases_on `pred2` >> gvs[] >> metis_tac[]) >>
    simp[]) >>
  (* Step 4: Compute the OR+ISZERO+ASSERT chain directly *)
  `step_inst fuel ctx or_inst s_mid =
   OK (update_var or_v (word_or v1 v2) s_mid)` by (
    Cases_on `or_inst` >> gvs[step_inst_non_invoke, step_inst_base_def,
                                exec_pure2_def, update_var_def]) >>
  qabbrev_tac `s_or = update_var or_v (word_or v1 v2) s_mid` >>
  `eval_operand (Var or_v) s_or = SOME (word_or v1 v2)` by
    simp[Abbr `s_or`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst fuel ctx iz_inst s_or =
   OK (update_var iz_v (bool_to_word (word_or v1 v2 = 0w)) s_or)` by (
    Cases_on `iz_inst` >> gvs[step_inst_non_invoke, step_inst_base_def,
                                exec_pure1_def, update_var_def]) >>
  `word_or v1 v2 <> 0w` by (CCONTR_TAC >> gvs[word_or_eq_0w]) >>
  `bool_to_word (word_or v1 v2 = 0w) = 0w` by
    simp[venomExecSemanticsTheory.bool_to_word_def] >>
  qabbrev_tac `s_iz = update_var iz_v 0w s_or` >>
  `eval_operand (Var iz_v) s_iz = SOME 0w` by
    simp[Abbr `s_iz`, eval_operand_def, lookup_var_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst fuel ctx assert_inst s_iz =
   Abort Revert_abort (revert_state (set_returndata [] s_iz))` by (
    irule step_assert_abort >> simp[]) >>
  (* Step 5: Combine into run_insts *)
  simp[run_insts_append, run_insts_def] >>
  (* Step 6: execution_equiv UNIV between abort states *)
  irule revert_returndata_exec_equiv_UNIV >>
  `execution_equiv UNIV s_mid s_or` by
    simp[Abbr `s_or`, execution_equiv_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  `execution_equiv UNIV s_or s_iz` by
    simp[Abbr `s_iz`, execution_equiv_def, update_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[execution_equiv_trans]
QED

(* ===== Core: run_insts FOLDL simulation ===== *)

(* ac_scan_block only produces candidates whose ids come from ASSERT instructions *)
Theorem ac_scan_second_is_assert:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    ?inst. MEM inst insts /\ inst.inst_opcode = ASSERT /\
           inst.inst_id = mc.mc_second_id
Proof
  Induct_on `insts` >> rw[ac_scan_block_def] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem ac_scan_first_is_assert:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    (?inst. MEM inst insts /\ inst.inst_opcode = ASSERT /\
            inst.inst_id = mc.mc_first_id) \/
    (?prev_pred. pending = SOME (mc.mc_first_id, prev_pred))
Proof
  Induct_on `insts` >> rw[ac_scan_block_def] >>
  BasicProvers.every_case_tac >> gvs[] >> res_tac >> gvs[] >> metis_tac[]
QED

(* If inst is not a first and not a second, it passes through FOLDL unchanged *)
Theorem ac_step_passthrough:
  !cands mp inst.
    FIND (\mc. mc.mc_second_id = inst.inst_id) cands = NONE /\
    ~EXISTS (\mc. mc.mc_first_id = inst.inst_id) cands ==>
    ac_apply_merge_step cands (mp, []) inst = (mp, [inst])
Proof
  simp[ac_apply_merge_step_def, LET_THM] >> rpt strip_tac >>
  `~EXISTS (\mc. mc.mc_first_id = inst.inst_id) cands` by fs[] >> simp[]
QED

(* Case 1: FIND=NONE, fid → NOP *)
Theorem ac_step_fid_none:
  !cands mp inst.
    FIND (\mc. mc.mc_second_id = inst.inst_id) cands = NONE /\
    EXISTS (\mc. mc.mc_first_id = inst.inst_id) cands ==>
    ac_apply_merge_step cands (mp, []) inst =
      (mp, [inst with <| inst_opcode := NOP;
                          inst_operands := [];
                          inst_outputs := [] |>])
Proof
  simp[ac_apply_merge_step_def, LET_THM]
QED

(* Case 4: FIND=SOME mc, same preds, nofid → (extended mp, [h]) *)
Theorem ac_step_same_nofid:
  !cands mp inst mc.
    FIND (\mc. mc.mc_second_id = inst.inst_id) cands = SOME mc /\
    ~EXISTS (\mc'. mc'.mc_first_id = inst.inst_id) cands /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) = mc.mc_second_pred ==>
    ac_apply_merge_step cands (mp, []) inst =
      ((mc.mc_second_id,
        case ALOOKUP mp mc.mc_first_id of
          SOME p => p | NONE => mc.mc_first_pred)::mp, [inst])
Proof
  rpt strip_tac >> simp[ac_apply_merge_step_def, LET_THM] >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> fs[]
QED

(* Case 6: FIND=SOME mc, diff preds, nofid → (extended mp, [OR;IZ;h']) *)
Theorem ac_step_diff_nofid:
  !cands mp inst mc.
    FIND (\mc. mc.mc_second_id = inst.inst_id) cands = SOME mc /\
    ~EXISTS (\mc'. mc'.mc_first_id = inst.inst_id) cands /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) <> mc.mc_second_pred ==>
    let afp = case ALOOKUP mp mc.mc_first_id of
                NONE => mc.mc_first_pred | SOME p => p in
    let or_v = ac_or_var inst.inst_id in
    let iz_v = ac_iz_var inst.inst_id in
    ac_apply_merge_step cands (mp, []) inst =
      ((mc.mc_second_id, Var or_v)::mp,
       [<| inst_id := inst.inst_id; inst_opcode := OR;
           inst_operands := [afp; mc.mc_second_pred];
           inst_outputs := [or_v] |>;
        <| inst_id := inst.inst_id + 1; inst_opcode := ISZERO;
           inst_operands := [Var or_v];
           inst_outputs := [iz_v] |>;
        inst with inst_operands := [Var iz_v]])
Proof
  rpt strip_tac >> simp[ac_apply_merge_step_def, LET_THM] >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> fs[]
QED

(* Case 3: FIND=SOME mc, same preds, fid → (extended mp, [NOP]) *)
Theorem ac_step_same_fid:
  !cands mp inst mc.
    FIND (\mc. mc.mc_second_id = inst.inst_id) cands = SOME mc /\
    EXISTS (\mc'. mc'.mc_first_id = inst.inst_id) cands /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) = mc.mc_second_pred ==>
    ac_apply_merge_step cands (mp, []) inst =
      ((mc.mc_second_id,
        case ALOOKUP mp mc.mc_first_id of
          SOME p => p | NONE => mc.mc_first_pred)::mp,
       [inst with <| inst_opcode := NOP;
                     inst_operands := [];
                     inst_outputs := [] |>])
Proof
  rpt strip_tac >> simp[ac_apply_merge_step_def, LET_THM] >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> fs[]
QED

(* Case 5: FIND=SOME mc, diff preds, fid → (extended mp, [OR;IZ;NOP]) *)
Theorem ac_step_diff_fid:
  !cands mp inst mc.
    FIND (\mc. mc.mc_second_id = inst.inst_id) cands = SOME mc /\
    EXISTS (\mc'. mc'.mc_first_id = inst.inst_id) cands /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) <> mc.mc_second_pred ==>
    let afp = case ALOOKUP mp mc.mc_first_id of
                NONE => mc.mc_first_pred | SOME p => p in
    let or_v = ac_or_var inst.inst_id in
    let iz_v = ac_iz_var inst.inst_id in
    ac_apply_merge_step cands (mp, []) inst =
      ((mc.mc_second_id, Var or_v)::mp,
       [<| inst_id := inst.inst_id; inst_opcode := OR;
           inst_operands := [afp; mc.mc_second_pred];
           inst_outputs := [or_v] |>;
        <| inst_id := inst.inst_id + 1; inst_opcode := ISZERO;
           inst_operands := [Var or_v];
           inst_outputs := [iz_v] |>;
        inst with <| inst_opcode := NOP;
                     inst_operands := [];
                     inst_outputs := [] |>])
Proof
  rpt strip_tac >> simp[ac_apply_merge_step_def, LET_THM] >>
  Cases_on `ALOOKUP mp mc.mc_first_id` >> fs[]
QED

(* A single FOLDL step always produces at least one instruction *)
Triviality ac_step_nonempty[local]:
  !cands mp inst. SND (ac_apply_merge_step cands (mp, []) inst) <> []
Proof
  rw[ac_apply_merge_step_def, LET_THM] >>
  BasicProvers.every_case_tac >> simp[]
QED

(* The FOLDL always appends: result is non-empty if input is non-empty *)
Triviality ac_foldl_nonempty[local]:
  !insts cands mp acc.
    insts <> [] ==>
    SND (FOLDL (ac_apply_merge_step cands) (mp, acc) insts) <> []
Proof
  Induct >> rw[] >>
  qspecl_then [`cands`, `mp`, `acc`, `h`] strip_assume_tac ac_step_appends >>
  Cases_on `insts`
  >- (
    gvs[] >>
    `stuff <> []` suffices_by simp[] >>
    `SND (ac_apply_merge_step cands (mp, []) h) = stuff` by simp[] >>
    metis_tac[ac_step_nonempty])
  >- (first_x_assum (qspecl_then [`cands`, `mp'`, `acc ++ stuff`] mp_tac) >> simp[])
QED

(* LAST of FOLDL output = LAST of input when last inst passes through *)
Theorem ac_foldl_last[local]:
  !insts cands mp.
    insts <> [] /\
    ~EXISTS (\mc. mc.mc_first_id = (LAST insts).inst_id) cands /\
    FIND (\mc. mc.mc_second_id = (LAST insts).inst_id) cands = NONE
  ==>
    LAST (SND (FOLDL (ac_apply_merge_step cands) (mp, []) insts)) =
    LAST insts
Proof
  Induct >> rw[] >>
  Cases_on `insts` >> gvs[]
  >- (
    (* Base: [h] *)
    `ac_apply_merge_step cands (mp, []) h = (mp, [h])` by
      (irule ac_step_passthrough >> gvs[LAST_DEF]) >>
    simp[])
  >- (
    (* Inductive: h :: h' :: t *)
    `LAST (h :: h' :: t) = LAST (h' :: t)` by simp[LAST_DEF] >>
    qspecl_then [`h`, `h' :: t`, `cands`, `mp`]
      mp_tac ac_foldl_cons >> simp[LET_THM] >>
    Cases_on `ac_apply_merge_step cands (mp,[]) h` >> simp[] >>
    strip_tac >>
    `SND (FOLDL (ac_apply_merge_step cands) (q,[]) (h'::t)) <> []` by
      simp[ac_foldl_nonempty] >>
    simp[LAST_APPEND_NOT_NIL] >>
    first_x_assum (qspecl_then [`cands`, `q`] mp_tac) >> gvs[LAST_DEF] >>
    strip_tac >> simp[LAST_APPEND_NOT_NIL])
QED

(* FOLDL split: FOLDL on (front ++ [last]) = FOLDL on front ++ [last]
   when last is not a candidate *)
Theorem ac_foldl_split_last[local]:
  !front last_inst cands mp.
    FIND (\mc. mc.mc_second_id = last_inst.inst_id) cands = NONE /\
    ~EXISTS (\mc. mc.mc_first_id = last_inst.inst_id) cands ==>
    SND (FOLDL (ac_apply_merge_step cands) (mp, []) (front ++ [last_inst])) =
    SND (FOLDL (ac_apply_merge_step cands) (mp, []) front) ++ [last_inst]
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FOLDL (ac_apply_merge_step cands) (mp, []) front` >>
  rename1 `_ = (mp_f, out_f)` >>
  `SND (FOLDL (ac_apply_merge_step cands) (mp, []) front) = out_f` by simp[] >>
  simp[FOLDL_APPEND] >>
  qspecl_then [`cands`, `mp_f`, `out_f`, `last_inst`]
    strip_assume_tac ac_step_appends >>
  `ac_apply_merge_step cands (mp_f, []) last_inst = (mp_f, [last_inst])` by
    metis_tac[ac_step_passthrough] >>
  gvs[]
QED

(* Fresh variable injectivity and distinctness *)
Theorem ac_or_var_inj[simp]:
  !a b. (ac_or_var a = ac_or_var b) = (a = b)
Proof
  rw[ac_or_var_def]
QED

Triviality ac_iz_var_inj[local,simp]:
  !a b. (ac_iz_var a = ac_iz_var b) = (a = b)
Proof
  rw[ac_iz_var_def]
QED

Theorem ac_or_iz_distinct[simp]:
  (!a b. ac_or_var a <> ac_iz_var b) /\
  (!a b. ac_iz_var a <> ac_or_var b)
Proof
  rw[ac_or_var_def, ac_iz_var_def]
QED

(* IH application tactic for ac_scan_block_ordered_gen *)
fun scan_ordered_ih pend =
  first_x_assum (qspecl_then [`prefix ++ [h]`, pend, `mc`] mp_tac) >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND] >>
  simp[ADD1, LENGTH_APPEND] >>
  disch_then match_mp_tac >>
  REWRITE_TAC[GSYM APPEND_ASSOC, APPEND, MAP_APPEND, MAP] >>
  ASM_REWRITE_TAC[];

(* Generalized: for ac_scan_block dfg rest pending, where the full list is
   prefix ++ rest, and pending's id (if SOME) appeared before LENGTH prefix,
   every emitted candidate has first_id < second_id in the full list. *)
Triviality ac_scan_block_ordered_gen[local]:
  !dfg rest prefix pending mc.
    MEM mc (ac_scan_block dfg rest pending) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (prefix ++ rest)) /\
    (!prev_id prev_pred. pending = SOME (prev_id, prev_pred) ==>
       ?idx. idx < LENGTH prefix /\
             (EL idx (prefix ++ rest)).inst_id = prev_id) ==>
    ?idx_f idx_s.
      idx_f < idx_s /\ idx_s < LENGTH (prefix ++ rest) /\
      (EL idx_f (prefix ++ rest)).inst_id = mc.mc_first_id /\
      (EL idx_s (prefix ++ rest)).inst_id = mc.mc_second_id
Proof
  gen_tac >> Induct >> simp[ac_scan_block_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = ASSERT` >> fs[]
  >- (
    Cases_on `h.inst_operands` >> fs[]
    >- scan_ordered_ih `NONE`
    >- (
      Cases_on `ac_get_iszero_operand dfg {} h'` >> fs[]
      >- scan_ordered_ih `NONE`
      >- (
        Cases_on `t` >> fs[]
        >- (
          Cases_on `pending` >> fs[LET_THM]
          >- (
            scan_ordered_ih `SOME (h.inst_id, x)` >>
            rpt strip_tac >> gvs[] >>
            qexists_tac `LENGTH prefix` >> simp[EL_APPEND_EQN]
          )
          >- (
            Cases_on `x'` >> fs[MEM]
            >- (
              (* emit case: mc is the record, witnesses are idx and LENGTH prefix *)
              qexists_tac `idx` >> qexists_tac `LENGTH prefix` >>
              simp[EL_APPEND_EQN]
            )
            >- (
              (* tail recursive case *)
              scan_ordered_ih `SOME (h.inst_id, x)` >>
              rpt strip_tac >> gvs[] >>
              qexists_tac `LENGTH prefix` >> simp[EL_APPEND_EQN]
            )
          )
        )
        >- scan_ordered_ih `NONE`
      )
    )
  )
  >- (
    Cases_on `ac_is_safe_between h` >> fs[]
    >- (
      scan_ordered_ih `pending` >>
      rpt strip_tac >>
      first_x_assum drule >> strip_tac >>
      qexists_tac `idx` >> simp[]
    )
    >- scan_ordered_ih `NONE`
  )
QED

(* Specialization: ac_scan_block with NONE gives ordered indices *)
Theorem ac_scan_block_ordered_indices:
  !dfg insts mc.
    MEM mc (ac_scan_block dfg insts NONE) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ?idx_f idx_s.
      idx_f < idx_s /\ idx_s < LENGTH insts /\
      (EL idx_f insts).inst_id = mc.mc_first_id /\
      (EL idx_s insts).inst_id = mc.mc_second_id
Proof
  rpt strip_tac >>
  qspecl_then [`dfg`, `insts`, `[]`, `NONE`, `mc`] mp_tac
    ac_scan_block_ordered_gen >>
  simp[]
QED

(* Candidates are well-formed w.r.t. insts: for any candidate whose first
   appears in insts, both first and second appear with second after first.
   This property passes to tails (unlike the stronger version). *)
Definition ac_cands_ordered_def:
  ac_cands_ordered cands insts <=>
    (!mc. MEM mc cands /\
       (?i. MEM i insts /\ i.inst_id = mc.mc_first_id) ==>
       ?idx_f idx_s.
         idx_f < idx_s /\ idx_s < LENGTH insts /\
         (EL idx_f insts).inst_id = mc.mc_first_id /\
         (EL idx_s insts).inst_id = mc.mc_second_id) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts)
End

(* Stronger version: every candidate has both endpoints in insts *)
Theorem ac_cands_ordered_full:
  !cands insts.
    (!mc. MEM mc cands ==>
       ?idx_f idx_s.
         idx_f < idx_s /\ idx_s < LENGTH insts /\
         (EL idx_f insts).inst_id = mc.mc_first_id /\
         (EL idx_s insts).inst_id = mc.mc_second_id) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) insts)
  ==>
    ac_cands_ordered cands insts
Proof
  rw[ac_cands_ordered_def] >> metis_tac[]
QED

(* From ac_cands_ordered, if h is the first of mc, mc's second is in rest *)
Triviality ac_cands_first_at_head[local]:
  !cands h rest mc.
    ac_cands_ordered cands (h :: rest) /\ MEM mc cands /\
    mc.mc_first_id = h.inst_id ==>
    ?idx_s. idx_s < LENGTH rest /\ (EL idx_s rest).inst_id = mc.mc_second_id
Proof
  rw[ac_cands_ordered_def] >>
  first_x_assum (qspec_then `mc` mp_tac) >> simp[] >>
  impl_tac >- (qexists_tac `h` >> simp[]) >>
  strip_tac >>
  `idx_f = 0` by (
    spose_not_then assume_tac >>
    Cases_on `idx_f` >> gvs[] >>
    `MEM ((EL n rest).inst_id) (MAP (\i. i.inst_id) rest)` by
      (rw[MEM_MAP] >> qexists_tac `EL n rest` >> simp[MEM_EL] >>
       qexists_tac `n` >> simp[]) >>
    gvs[ALL_DISTINCT]) >>
  gvs[] >>
  qexists_tac `idx_s - 1` >>
  Cases_on `idx_s` >> gvs[]
QED

(* When mc.mc_second_id = h.inst_id (head), mc.mc_first_id is not in rest.
   Proof: if first_id were in (h::rest), cands_ordered gives idx_f < idx_s.
   Since second_id = h.inst_id, ALL_DISTINCT forces idx_s = 0 (only h has that id).
   But idx_f < 0 is impossible. So first_id is not in (h::rest), hence not in rest. *)
Theorem ac_cands_second_at_head:
  !cands h rest mc.
    ac_cands_ordered cands (h :: rest) /\ MEM mc cands /\
    mc.mc_second_id = h.inst_id ==>
    !i. MEM i rest ==> i.inst_id <> mc.mc_first_id
Proof
  rw[ac_cands_ordered_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `mc` mp_tac) >>
  impl_tac >- (simp[] >> qexists_tac `i` >> simp[]) >>
  strip_tac >>
  (* idx_s must be 0 since (EL idx_s (h::rest)).inst_id = mc.mc_second_id = h.inst_id *)
  `idx_s = 0` by (
    spose_not_then assume_tac >>
    `0 < LENGTH (h::rest)` by simp[] >>
    `EL idx_s (MAP (\i'. i'.inst_id) (h::rest)) = mc.mc_second_id` by
      simp[EL_MAP] >>
    `EL 0 (MAP (\i'. i'.inst_id) (h::rest)) = h.inst_id` by
      simp[EL_MAP] >>
    `idx_s < LENGTH (MAP (\i'. i'.inst_id) (h::rest))` by simp[] >>
    `0 < LENGTH (MAP (\i'. i'.inst_id) (h::rest))` by simp[] >>
    `ALL_DISTINCT (MAP (\i'. i'.inst_id) (h::rest))` by
      simp[ALL_DISTINCT] >>
    metis_tac[ALL_DISTINCT_EL_IMP]) >>
  gvs[]
QED

(* ac_cands_ordered passes to tail unconditionally *)
Theorem ac_cands_ordered_tail:
  !cands h rest.
    ac_cands_ordered cands (h :: rest) ==>
    ac_cands_ordered cands rest
Proof
  rw[ac_cands_ordered_def] >>
  first_x_assum (qspec_then `mc` mp_tac) >> simp[] >>
  impl_tac >- (qexists_tac `i` >> simp[]) >>
  strip_tac >>
  `mc.mc_first_id <> h.inst_id` by (
    spose_not_then assume_tac >> gvs[ALL_DISTINCT, MEM_MAP] >>
    metis_tac[]) >>
  `idx_f <> 0` by (spose_not_then strip_assume_tac >> gvs[]) >>
  `idx_s <> 0` by (Cases_on `idx_s` >> gvs[]) >>
  MAP_EVERY qexists_tac [`idx_f - 1`, `idx_s - 1`] >>
  Cases_on `idx_f` >> Cases_on `idx_s` >> gvs[]
QED

(*
 * ac_deferred_chain_abort: When a nonzero pred enters the chain,
 * the FOLDL-transformed code eventually aborts.
 *
 * Proof by complete induction on LENGTH insts.
 * At each step, the head instruction's FOLDL contribution either:
 *   (a) aborts directly (done)
 *   (b) succeeds, preserving pred_op nonzero — apply IH to rest
 *)
(*
 * Helper: safe_between step succeeds and preserves eval_operand + exec_equiv.
 *)
Theorem ac_safe_step_preserves[local]:
  !fuel ctx inst s.
    ac_is_safe_between inst /\ inst_wf inst /\
    (!op. MEM op inst.inst_operands ==> IS_SOME (eval_operand op s)) ==>
    ?s'. step_inst fuel ctx inst s = OK s' /\
         execution_equiv UNIV s s' /\
         (!op. (!x. op = Var x ==> ~MEM x inst.inst_outputs) ==>
               eval_operand op s' = eval_operand op s)
Proof
  rpt strip_tac >>
  drule_all safe_between_wf_step_ok >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexists_tac `s'` >> simp[] >>
  conj_tac
  >- (`is_effect_free_op inst.inst_opcode` by
        metis_tac[ac_safe_between_effect_free] >>
      metis_tac[step_effect_free_exec_equiv_UNIV]) >>
  rpt strip_tac >>
  `~is_terminator inst.inst_opcode` by
    fs[ac_is_safe_between_def] >>
  irule step_eval_operand_preserved >>
  metis_tac[]
QED

Triviality INDEX_FIND_P[local]:
  !l i P n x. INDEX_FIND i P l = SOME (n, x) ==> P x
Proof
  Induct >> simp[INDEX_FIND_def] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[] >> metis_tac[]
QED

Theorem FIND_P:
  !P l x. FIND P l = SOME x ==> P x
Proof
  rpt strip_tac >>
  fs[FIND_def] >>
  Cases_on `INDEX_FIND 0 P l` >> gvs[] >>
  Cases_on `x'` >> gvs[] >> metis_tac[INDEX_FIND_P]
QED

Triviality INDEX_FIND_MEM[local]:
  !l i P n x. INDEX_FIND i P l = SOME (n, x) ==> MEM x l
Proof
  Induct >> simp[INDEX_FIND_def] >> rpt strip_tac >>
  Cases_on `P h` >> gvs[] >> metis_tac[]
QED

Theorem FIND_MEM:
  !P l x. FIND P l = SOME x ==> MEM x l
Proof
  rpt strip_tac >> fs[FIND_def] >>
  Cases_on `INDEX_FIND 0 P l` >> gvs[] >>
  Cases_on `x'` >> gvs[] >> metis_tac[INDEX_FIND_MEM]
QED

(* If P holds for some member of l, then FIND P l returns SOME *)
Triviality FIND_MEM_EXISTS[local]:
  !P l x. MEM x l /\ P x ==> ?y. FIND P l = SOME y
Proof
  Induct_on `l` >> rw[FIND_thm] >>
  Cases_on `P h` >> simp[] >> metis_tac[]
QED

(* mc_second_id values in scan result come from instruction IDs *)
Theorem ac_scan_second_id_mem:
  !dfg insts pending mc.
    MEM mc (ac_scan_block dfg insts pending) ==>
    ?i. MEM i insts /\ mc.mc_second_id = i.inst_id
Proof
  Induct_on `insts` >> simp[ac_scan_block_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = ASSERT` >> fs[]
  >- (Cases_on `h.inst_operands` >> fs[]
      >- (res_tac >> qexists_tac `i` >> simp[])
      >- (Cases_on `t` >> fs[]
          >- (Cases_on `ac_get_iszero_operand dfg {} h'` >> fs[]
              >- (res_tac >> qexists_tac `i` >> simp[])
              >- (Cases_on `pending` >> fs[]
                  >- (res_tac >> qexists_tac `i` >> simp[])
                  >- (Cases_on `x'` >> fs[LET_THM] >>
                      gvs[MEM] >> res_tac >>
                      metis_tac[])))
          >- (Cases_on `ac_get_iszero_operand dfg {} h'` >> fs[]
              >- (res_tac >> qexists_tac `i` >> simp[])
              >- (res_tac >> qexists_tac `i` >> simp[]))))
  >- (Cases_on `ac_is_safe_between h` >> fs[] >>
      res_tac >> qexists_tac `i` >> simp[])
QED

(* mc_second_id values are unique when instruction IDs are distinct *)
Theorem ac_scan_unique_second_id:
  !dfg insts pending.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) ==>
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) (ac_scan_block dfg insts pending))
Proof
  Induct_on `insts` >> simp[ac_scan_block_def] >>
  rpt gen_tac >> strip_tac >>
  `!dfg' p'. ALL_DISTINCT (MAP (\mc. mc.mc_second_id)
     (ac_scan_block dfg' insts p'))` by metis_tac[] >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  TRY (BasicProvers.TOP_CASE_TAC >>
       gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP]) >>
  gvs[LET_THM, ALL_DISTINCT, MAP, MEM_MAP] >>
  spose_not_then strip_assume_tac >>
  drule ac_scan_second_id_mem >> strip_tac >>
  gvs[ALL_DISTINCT, MEM_MAP]
QED

(* Corollary: FIND on mc_second_id gives a unique result *)
Triviality ac_scan_find_unique[local]:
  !dfg insts pending mc1 mc2 id.
    ALL_DISTINCT (MAP (\i. i.inst_id) insts) /\
    MEM mc1 (ac_scan_block dfg insts pending) /\
    MEM mc2 (ac_scan_block dfg insts pending) /\
    mc1.mc_second_id = id /\ mc2.mc_second_id = id ==>
    mc1 = mc2
Proof
  rpt strip_tac >>
  drule ac_scan_unique_second_id >>
  strip_tac >>
  qabbrev_tac `cands = ac_scan_block dfg insts pending` >>
  `?n1. n1 < LENGTH cands /\ EL n1 cands = mc1` by
    metis_tac[MEM_EL] >>
  `?n2. n2 < LENGTH cands /\ EL n2 cands = mc2` by
    metis_tac[MEM_EL] >>
  `ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands)` by
    metis_tac[] >>
  `n1 < LENGTH (MAP (\mc. mc.mc_second_id) cands) /\
   n2 < LENGTH (MAP (\mc. mc.mc_second_id) cands)` by
    simp[] >>
  `EL n1 (MAP (\mc. mc.mc_second_id) cands) =
   EL n2 (MAP (\mc. mc.mc_second_id) cands)` by
    simp[EL_MAP] >>
  `n1 = n2` by metis_tac[ALL_DISTINCT_EL_IMP] >>
  gvs[]
QED

(*
 * Chain invariant: packages all preconditions for the deferred abort proof.
 * This keeps the induction goal manageable.
 *)
Definition ac_chain_inv_def:
  ac_chain_inv cands insts mp s pred_op v <=>
    EVERY inst_wf insts /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) insts /\
    (!i op. MEM i insts /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    (!mc. MEM mc cands ==> IS_SOME (eval_operand mc.mc_second_pred s) /\
                            IS_SOME (eval_operand mc.mc_first_pred s)) /\
    eval_operand pred_op s = SOME v /\ v <> 0w /\
    (!i x. MEM i insts /\ pred_op = Var x ==> ~MEM x i.inst_outputs) /\
    (!mc x. MEM mc cands /\ pred_op = Var x /\
       (?i. MEM i insts /\ mc.mc_second_id = i.inst_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!i x mc. MEM i insts /\ MEM (Var x) i.inst_operands /\ MEM mc cands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!i x mc. MEM i insts /\ MEM x i.inst_outputs /\ MEM mc cands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!mc mc' x. MEM mc cands /\ MEM mc' cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==>
       x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id) /\
    (* SSA-like: remaining instruction outputs don't clobber cand or mp preds *)
    (!i x mc. MEM i insts /\ MEM x i.inst_outputs /\ MEM mc cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==> F) /\
    (!i x id. MEM i insts /\ MEM x i.inst_outputs /\
       ALOOKUP mp id = SOME (Var x) ==> F) /\
    (* mp pred values are evaluable *)
    (!id p. ALOOKUP mp id = SOME p ==> IS_SOME (eval_operand p s)) /\
    (* mp keys are disjoint from remaining instruction IDs *)
    (!i. MEM i insts ==> ALOOKUP mp i.inst_id = NONE) /\
    (* merge targets are ASSERTs *)
    (!i mc. MEM i insts /\
       FIND (\mc'. mc'.mc_second_id = i.inst_id) cands = SOME mc ==>
       i.inst_opcode = ASSERT) /\
    (* chaining: consecutive candidates share predicates *)
    (!mc1 mc2. MEM mc1 cands /\ MEM mc2 cands /\
       mc1.mc_second_id = mc2.mc_first_id ==>
       mc1.mc_second_pred = mc2.mc_first_pred) /\
    ac_cands_ordered cands insts /\
    (?inst_s mc_s. MEM inst_s insts /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
End

(* ================================================================
 * Chain invariant accessor lemmas.
 * These avoid the need to expand ac_chain_inv_def repeatedly.
 * ================================================================ *)

Theorem ci_eval_pred[local]:
  ac_chain_inv cands insts mp s pred_op v ==>
  eval_operand pred_op s = SOME v /\ v <> 0w
Proof rw[ac_chain_inv_def]
QED

Theorem ci_cand_preds_eval[local]:
  ac_chain_inv cands insts mp s pred_op v /\ MEM mc cands ==>
  IS_SOME (eval_operand mc.mc_second_pred s) /\
  IS_SOME (eval_operand mc.mc_first_pred s)
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_operand_eval[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM i insts /\ MEM op i.inst_operands ==>
  IS_SOME (eval_operand op s)
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_mp_eval[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  ALOOKUP mp id = SOME p ==>
  IS_SOME (eval_operand p s)
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_mp_disjoint[local]:
  ac_chain_inv cands insts mp s pred_op v /\ MEM i insts ==>
  ALOOKUP mp i.inst_id = NONE
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_pred_fresh_outputs[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM i insts /\ pred_op = Var x ==>
  ~MEM x i.inst_outputs
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_pred_fresh_ac[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM mc cands /\ pred_op = Var x /\
  (?i. MEM i insts /\ mc.mc_second_id = i.inst_id) ==>
  x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_operand_fresh_ac[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM i insts /\ MEM (Var x) i.inst_operands /\ MEM mc cands ==>
  x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_output_fresh_ac[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM i insts /\ MEM x i.inst_outputs /\ MEM mc cands ==>
  x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_cand_pred_fresh_ac[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM mc cands /\ MEM mc' cands /\
  (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==>
  x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_output_no_clobber_cand[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM i insts /\ MEM x i.inst_outputs /\ MEM mc cands /\
  (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==> F
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_output_no_clobber_mp[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM i insts /\ MEM x i.inst_outputs /\
  ALOOKUP mp id = SOME (Var x) ==> F
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_chaining[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM mc1 cands /\ MEM mc2 cands /\
  mc1.mc_second_id = mc2.mc_first_id ==>
  mc1.mc_second_pred = mc2.mc_first_pred
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_cands_ordered[local]:
  ac_chain_inv cands insts mp s pred_op v ==>
  ac_cands_ordered cands insts
Proof rw[ac_chain_inv_def]
QED

Theorem ci_every_wf[local]:
  ac_chain_inv cands insts mp s pred_op v ==>
  EVERY inst_wf insts
Proof rw[ac_chain_inv_def]
QED

Theorem ci_every_non_term[local]:
  ac_chain_inv cands insts mp s pred_op v ==>
  EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts
Proof rw[ac_chain_inv_def]
QED

Theorem ci_every_safe_or_assert[local]:
  ac_chain_inv cands insts mp s pred_op v ==>
  EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) insts
Proof rw[ac_chain_inv_def]
QED

Theorem ci_merge_target_assert[local]:
  ac_chain_inv cands insts mp s pred_op v /\
  MEM i insts /\
  FIND (\mc'. mc'.mc_second_id = i.inst_id) cands = SOME mc ==>
  i.inst_opcode = ASSERT
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

Theorem ci_witness[local]:
  ac_chain_inv cands insts mp s pred_op v ==>
  ?inst_s mc_s. MEM inst_s insts /\
    FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
    (case ALOOKUP mp mc_s.mc_first_id of
       SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
    (case ALOOKUP mp mc_s.mc_first_id of
       SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
Proof rw[ac_chain_inv_def] >> metis_tac[]
QED

(* Consolidated head-element accessor: extract ALL head properties at once.
   Use: drule ci_head_props >> strip_tac
   Then case-split on the disjunction with Cases_on `ac_is_safe_between h` *)
Theorem ci_head_props[local]:
  ac_chain_inv cands (h::rest) mp s pred_op v ==>
  inst_wf h /\
  (ac_is_safe_between h \/ h.inst_opcode = ASSERT) /\
  (~is_terminator h.inst_opcode /\ h.inst_opcode <> INVOKE) /\
  (!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s))
Proof rw[ac_chain_inv_def] >> fs[EVERY_MEM] >> metis_tac[MEM]
QED

(* ASSERT operand extraction: avoids inst_wf_def explosion in large goals *)
Theorem assert_single_operand:
  inst_wf h /\ h.inst_opcode = ASSERT ==> ?op. h.inst_operands = [op]
Proof
  rw[inst_wf_def] >> Cases_on `h.inst_operands` >> fs[] >>
  Cases_on `t` >> fs[]
QED

(* Combined: chain_inv head is ASSERT => single evaluable operand *)
Theorem ci_head_assert_operand[local]:
  ac_chain_inv cands (h::rest) mp s pred_op v ==>
  h.inst_opcode = ASSERT ==>
  ?op. h.inst_operands = [op] /\ IS_SOME (eval_operand op s)
Proof
  rpt strip_tac >>
  drule ci_head_props >>
  disch_then (fn th =>
    let val wf = CONJUNCT1 th
        val ops = CONJUNCT2 (CONJUNCT2 (CONJUNCT2 th))
    in ASSUME_TAC wf >> ASSUME_TAC ops end) >>
  `LENGTH h.inst_operands = 1` by
    (qpat_x_assum `inst_wf _` mp_tac >> simp[inst_wf_def]) >>
  Cases_on `h.inst_operands` >> fs[]
QED

(*
 * Chain step: process head instruction's FOLDL contribution.
 * Either aborts (done) or succeeds and chain_inv passes to rest.
 *)
(*
 * Helper: chain_inv structural conjuncts pass from h::rest to rest.
 * This covers the conjuncts that don't depend on runtime state or mp.
 *)
Theorem ac_chain_inv_tail_structural[local]:
  !cands h rest mp s pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v ==>
    EVERY inst_wf rest /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) rest /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) rest /\
    (!i x mc. MEM i rest /\ MEM (Var x) i.inst_operands /\ MEM mc cands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!i x mc. MEM i rest /\ MEM x i.inst_outputs /\ MEM mc cands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!mc mc' x. MEM mc cands /\ MEM mc' cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==>
       x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id) /\
    (!i x mc. MEM i rest /\ MEM x i.inst_outputs /\ MEM mc cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==> F) /\
    ac_cands_ordered cands rest
Proof
  rw[ac_chain_inv_def, EVERY_DEF] >>
  metis_tac[ac_cands_ordered_tail]
QED

Theorem ac_chain_inv_transfer[local]:
  !cands h rest mp mp' s s' pred_op pred_op' v v'.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    (* Operand/pred evaluability in new state *)
    (!i op. MEM i rest /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s')) /\
    (!mc. MEM mc cands ==> IS_SOME (eval_operand mc.mc_second_pred s') /\
                            IS_SOME (eval_operand mc.mc_first_pred s')) /\
    eval_operand pred_op' s' = SOME v' /\ v' <> 0w /\
    (?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp' mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp' mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op') /\
    (!x. pred_op' = Var x ==>
       (!i. MEM i rest ==> ~MEM x i.inst_outputs) /\
       (!mc. MEM mc cands /\
          (?j. MEM j rest /\ mc.mc_second_id = j.inst_id) ==>
          x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id)) /\
    (* SSA-like: rest outputs don't clobber cand preds or mp' pred vars *)
    (!i x mc. MEM i rest /\ MEM x i.inst_outputs /\ MEM mc cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==> F) /\
    (!i x id. MEM i rest /\ MEM x i.inst_outputs /\
       ALOOKUP mp' id = SOME (Var x) ==> F) /\
    (!id p. ALOOKUP mp' id = SOME p ==> IS_SOME (eval_operand p s')) /\
    (!i. MEM i rest ==> ALOOKUP mp' i.inst_id = NONE)
  ==>
    ac_chain_inv cands rest mp' s' pred_op' v'
Proof
  simp[ac_chain_inv_def] >>
  rpt strip_tac >> TRY (metis_tac[ac_cands_ordered_tail])
QED

(*
 * Simplified transfer for the common case: state unchanged or only outputs changed,
 * mp unchanged, same pred_op. Covers: NOP, ASSERT(nonzero), safe_between passthrough.
 *)
Theorem ac_chain_inv_transfer_unchanged[local]:
  !cands h rest mp s s' pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    (* eval preservation: for all ops, either preserved or ops vars in outs get IS_SOME *)
    (!i op. MEM i rest /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s')) /\
    (!mc. MEM mc cands ==> IS_SOME (eval_operand mc.mc_second_pred s') /\
                            IS_SOME (eval_operand mc.mc_first_pred s')) /\
    (!id p. ALOOKUP mp id = SOME p ==> IS_SOME (eval_operand p s')) /\
    eval_operand pred_op s' = SOME v /\
    (* Witness is in rest *)
    (?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
  ==>
    ac_chain_inv cands rest mp s' pred_op v
Proof
  rpt strip_tac >>
  fs[ac_chain_inv_def] >>
  simp[ac_chain_inv_def] >> rpt strip_tac >>
  TRY (metis_tac[ac_cands_ordered_tail]) >>
  metis_tac[MEM]
QED

(*
 * Derive the IS_SOME/eval conditions from safe_between step or identity step.
 * For safe_between: ac_safe_step_preserves gives eval preservation for non-outputs,
 * and safe_between_step_eval_is_some gives IS_SOME for all previously-IS_SOME ops.
 * For identity (ASSERT OK, NOP): state unchanged, everything trivially preserved.
 *)
Theorem ac_chain_inv_safe_step[local]:
  !cands h rest mp s s' fuel ctx pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    ac_is_safe_between h /\ inst_wf h /\
    step_inst fuel ctx h s = OK s' /\
    (* Witness is in rest *)
    (?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
  ==>
    execution_equiv UNIV s s' /\
    ac_chain_inv cands rest mp s' pred_op v
Proof
  rpt strip_tac
  >- metis_tac[ac_safe_between_effect_free, step_effect_free_exec_equiv_UNIV]
  >- (
    (* Expand chain_inv in BOTH hypothesis and conclusion *)
    fs[ac_chain_inv_def] >>
    simp[ac_chain_inv_def] >> rpt strip_tac >>
    TRY (metis_tac[ac_cands_ordered_tail]) >>
    TRY (metis_tac[MEM]) >>
    (* IS_SOME subgoals: use safe_between_step_eval_is_some *)
    TRY (irule safe_between_step_eval_is_some >>
         qexistsl_tac [`ctx`, `fuel`, `h`, `s`] >> simp[] >>
         (metis_tac[MEM] ORELSE metis_tac[])) >>
    (* Value-preservation subgoals: step_eval_operand_preserved *)
    metis_tac[step_eval_operand_preserved, MEM]
  )
QED

(*
 * MP extension: if chain_inv holds with mp, we can add a "redundant" entry
 * (one whose key is not in rest and whose value is already evaluable)
 * provided the witness is unaffected by the extension.
 *)
Theorem ac_chain_inv_mp_extend[local]:
  !cands rest mp s pred_op v key val.
    ac_chain_inv cands rest mp s pred_op v /\
    (!i. MEM i rest ==> key <> i.inst_id) /\
    IS_SOME (eval_operand val s) /\
    (!i x. MEM i rest /\ MEM x i.inst_outputs /\ val = Var x ==> F) /\
    (* Witness ALOOKUP unaffected by new entry *)
    (!inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
       ==>
       (case ALOOKUP ((key,val)::mp) mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP ((key,val)::mp) mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
  ==>
    ac_chain_inv cands rest ((key,val)::mp) s pred_op v
Proof
  rw[ac_chain_inv_def] >> rpt strip_tac >>
  Cases_on `key = id` >> fs[] >> metis_tac[]
QED

(* ac_chain_inv_safe_step_same_preds is unnecessary:
   FIND=SOME → ASSERT (ci_merge_target_assert), but safe_between requires ¬volatile,
   and ASSERT is volatile, so the case is vacuous. *)
(* Helper: running [or_inst; iz_inst] succeeds and produces a predictable state *)
Theorem ac_or_iz_step:
  !fuel ctx s pred1 pred2 or_v iz_v iid v1 v2.
    eval_operand pred1 s = SOME v1 /\
    eval_operand pred2 s = SOME v2 /\
    or_v <> iz_v ==>
    let or_inst = instruction iid OR [pred1; pred2] [or_v] in
    let iz_inst = instruction (iid + 1) ISZERO [Var or_v] [iz_v] in
    let iz_val = bool_to_word (word_or v1 v2 = 0w) in
    let s_iz = update_var iz_v iz_val (update_var or_v (word_or v1 v2) s) in
    run_insts fuel ctx [or_inst; iz_inst] s = OK s_iz /\
    eval_operand (Var iz_v) s_iz = SOME iz_val /\
    eval_operand (Var or_v) s_iz = SOME (word_or v1 v2) /\
    execution_equiv UNIV s s_iz /\
    (!op. (!x. op = Var x ==> x <> or_v /\ x <> iz_v) ==>
       eval_operand op s_iz = eval_operand op s)
Proof
  rpt strip_tac >>
  simp[LET_THM] >>
  simp[run_insts_def] >>
  simp[step_inst_non_invoke] >>
  PURE_REWRITE_TAC[step_inst_base_def] >>
  simp[venomInstTheory.opcode_case_def] >>
  simp[exec_pure2_def, exec_pure1_def] >>
  simp[update_var_def, eval_operand_def, lookup_var_def] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, execution_equiv_def] >>
  rpt strip_tac >> Cases_on `op` >>
  fs[eval_operand_def, lookup_var_def, update_var_def,
     finite_mapTheory.FLOOKUP_UPDATE]
QED

(* Identity transfer: state unchanged, mp unchanged, same pred_op.
   All eval-preservation conditions are trivially satisfied. *)
Theorem ac_chain_inv_identity_transfer[local]:
  !cands h rest mp s pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    (?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
  ==>
    ac_chain_inv cands rest mp s pred_op v
Proof
  rpt strip_tac >>
  fs[ac_chain_inv_def] >>
  simp[ac_chain_inv_def] >> rpt strip_tac >>
  TRY (metis_tac[ac_cands_ordered_tail]) >>
  metis_tac[MEM]
QED

(* Same-preds mp update: when FIND=SOME mc with same effective preds,
   updating mp with (h.inst_id, mc.mc_second_pred) preserves chain_inv.
   Works with arbitrary new state s' (for composing with safe_step). *)
Theorem ac_chain_inv_same_preds_mp_step[local]:
  !cands h rest mp s s' pred_op v mc.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) = mc.mc_second_pred /\
    (!i op. MEM i rest /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s')) /\
    (!mc'. MEM mc' cands ==> IS_SOME (eval_operand mc'.mc_second_pred s') /\
                              IS_SOME (eval_operand mc'.mc_first_pred s')) /\
    (!id p. ALOOKUP mp id = SOME p ==> IS_SOME (eval_operand p s')) /\
    eval_operand pred_op s' = SOME v
  ==>
    ac_chain_inv cands rest ((h.inst_id, mc.mc_second_pred)::mp) s' pred_op v
Proof
  rpt strip_tac >>
  `mc.mc_second_id = h.inst_id` by (drule FIND_P >> simp[]) >>
  `MEM mc cands` by (drule FIND_MEM >> simp[]) >>
  `v <> 0w` by fs[ac_chain_inv_def] >>
  `ALOOKUP mp h.inst_id = NONE` by
    (fs[ac_chain_inv_def] >> metis_tac[MEM]) >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (h::rest))` by
    fs[ac_chain_inv_def, ac_cands_ordered_def] >>
  `mc.mc_second_id = h.inst_id` by (drule FIND_P >> simp[]) >>
  `MEM mc cands` by (drule FIND_MEM >> simp[]) >>
  (* Extract witness from chain_inv before irule *)
  `?inst_s mc_s. MEM inst_s (h::rest) /\
     FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
     (case ALOOKUP mp mc_s.mc_first_id of
        SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
     (case ALOOKUP mp mc_s.mc_first_id of
        SOME p => p | NONE => mc_s.mc_first_pred) = pred_op` by
    metis_tac[ac_chain_inv_def] >>
  `inst_s <> h` by (
    CCONTR_TAC >> gvs[] >>
    `FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc_s` by
      metis_tac[] >> gvs[]) >>
  `MEM inst_s rest` by metis_tac[MEM] >>
  irule ac_chain_inv_transfer >> simp[] >>
  rpt conj_tac
  (* 1: SSA cand preds vs rest outputs *)
  >- (fs[ac_chain_inv_def] >> metis_tac[MEM])
  (* 2: SSA mp' pred vars vs rest outputs *)
  >- (rpt strip_tac >> Cases_on `h.inst_id = id` >> gvs[]
      >- (fs[ac_chain_inv_def] >> metis_tac[MEM])
      >- (fs[ac_chain_inv_def] >> metis_tac[MEM]))
  (* 3: operand evaluability — direct hyp *)
  >- first_assum ACCEPT_TAC
  (* 4: ALOOKUP mp' disjoint from rest *)
  >- (rpt strip_tac >>
      `ALOOKUP mp i.inst_id = NONE` by (fs[ac_chain_inv_def] >> metis_tac[MEM]) >>
      simp[] >>
      fs[ac_chain_inv_def, ac_cands_ordered_def, ALL_DISTINCT, MAP, MEM_MAP] >>
      metis_tac[])
  (* 5: pred_op freshness *)
  >- (fs[ac_chain_inv_def] >> metis_tac[MEM])
  (* 6: IS_SOME eval for mp' preds *)
  >- (rpt strip_tac >> Cases_on `h.inst_id = id` >> gvs[] >> metis_tac[])
  (* 7: Witness in rest with mp' *)
  >- (
    `MEM mc_s cands` by (
      `FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s` by
        first_assum ACCEPT_TAC >>
      drule FIND_MEM >> simp[]) >>
    qexistsl_tac [`inst_s`, `mc_s`] >> simp[] >>
    Cases_on `h.inst_id = mc_s.mc_first_id` >> simp[]
    >- (
      (* Simplify case expressions using ALOOKUP = NONE *)
      `ALOOKUP mp mc_s.mc_first_id = NONE` by gvs[] >>
      fs[] >>
      (* mc.mc_second_pred = mc_s.mc_first_pred via chaining *)
      `mc.mc_second_pred = mc_s.mc_first_pred` by
        (qpat_x_assum `ac_chain_inv _ _ _ _ _ _` mp_tac >>
         simp[ac_chain_inv_def] >> metis_tac[]) >>
      gvs[]
    )
    >- (fs[] >> metis_tac[])
  )
  (* 8: Old chain_inv *)
  >- metis_tac[]
QED

(* Corollary: same_preds mp_step when state unchanged (s' = s).
   All eval conditions are derivable from ac_chain_inv itself. *)
Theorem ac_chain_inv_same_preds_mp_step_id[local]:
  !cands h rest mp s pred_op v mc.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) = mc.mc_second_pred
  ==>
    ac_chain_inv cands rest ((h.inst_id, mc.mc_second_pred)::mp) s pred_op v
Proof
  rpt strip_tac >>
  irule ac_chain_inv_same_preds_mp_step >>
  rpt conj_tac >>
  metis_tac[ci_operand_eval, ci_cand_preds_eval, ci_mp_eval,
            ci_eval_pred, MEM]
QED

(* When FIND=NONE for h, chain_inv's witness is in rest (not h). *)
Theorem ac_chain_inv_witness_in_rest[local]:
  !cands h rest mp s pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = NONE ==>
    ?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
Proof
  rpt strip_tac >> fs[ac_chain_inv_def] >>
  qexistsl_tac [`inst_s`, `mc_s`] >> simp[] >>
  `inst_s <> h` suffices_by (strip_tac >> gvs[MEM]) >>
  CCONTR_TAC >> gvs[] >>
  `FIND (\mc. mc.mc_second_id = h.inst_id) cands = SOME mc_s` by
    metis_tac[] >>
  fs[]
QED

(* When FIND=SOME mc with same-preds for h, h is not the diff-preds witness. *)
Theorem ac_chain_inv_witness_in_rest_same[local]:
  !cands h rest mp s pred_op v mc.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       SOME p => p | NONE => mc.mc_first_pred) = mc.mc_second_pred ==>
    ?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
Proof
  rpt strip_tac >> fs[ac_chain_inv_def] >>
  qexistsl_tac [`inst_s`, `mc_s`] >> simp[] >>
  `inst_s <> h` suffices_by (strip_tac >> gvs[MEM]) >>
  CCONTR_TAC >> gvs[] >>
  `FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc_s` by
    metis_tac[] >>
  `mc_s = mc` by fs[] >>
  gvs[]
QED

(* When diff-preds h has word_or(v1,v2)=0w, h cannot be the chain_inv witness.
   Proof: if h were the witness, pred_op = afp and v = v1, or pred_op chains
   through mc.mc_second_pred and v = v2. Either way v = 0w, contradicting v<>0w. *)
Theorem ac_diff_preds_not_witness[local]:
  !cands h rest mp s pred_op v mc afp v1 v2.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    afp = (case ALOOKUP mp mc.mc_first_id of
             SOME p => p | NONE => mc.mc_first_pred) /\
    afp <> mc.mc_second_pred /\
    eval_operand afp s = SOME v1 /\
    eval_operand mc.mc_second_pred s = SOME v2 /\
    word_or v1 v2 = 0w ==>
    ?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op /\
       mc_s.mc_first_id <> h.inst_id
Proof
  rpt strip_tac >>
  `v1 = 0w /\ v2 = 0w` by metis_tac[word_or_eq_0w] >>
  (* Extract all needed facts from ac_chain_inv_def in one go *)
  `eval_operand pred_op s = SOME v /\ v <> 0w` by
    metis_tac[ac_chain_inv_def] >>
  `!i. MEM i (h::rest) ==> ALOOKUP mp i.inst_id = NONE` by
    metis_tac[ac_chain_inv_def] >>
  `!mc1 mc2. MEM mc1 cands /\ MEM mc2 cands /\
     mc1.mc_second_id = mc2.mc_first_id ==>
     mc1.mc_second_pred = mc2.mc_first_pred` by
    metis_tac[ac_chain_inv_def] >>
  `?inst_s0 mc_s0. MEM inst_s0 (h::rest) /\
     FIND (\mc'. mc'.mc_second_id = inst_s0.inst_id) cands = SOME mc_s0 /\
     (case ALOOKUP mp mc_s0.mc_first_id of
        SOME p => p | NONE => mc_s0.mc_first_pred) <> mc_s0.mc_second_pred /\
     (case ALOOKUP mp mc_s0.mc_first_id of
        SOME p => p | NONE => mc_s0.mc_first_pred) = pred_op` by
    metis_tac[ac_chain_inv_def] >>
  `MEM mc cands /\ MEM mc_s0 cands` by metis_tac[FIND_MEM] >>
  `inst_s0 <> h` by (
    CCONTR_TAC >>
    `mc_s0 = mc` by (
      `FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc_s0` by
        metis_tac[] >>
      fs[]) >>
    `afp = pred_op` by fs[] >>
    fs[]) >>
  `MEM inst_s0 rest` by metis_tac[MEM] >>
  `mc_s0.mc_first_id <> h.inst_id` by (
    strip_tac >>
    `ALOOKUP mp h.inst_id = NONE` by simp[] >>
    `mc_s0.mc_first_pred = pred_op` by
      (qpat_x_assum `(case ALOOKUP mp mc_s0.mc_first_id of
          SOME p => p | NONE => mc_s0.mc_first_pred) = pred_op` mp_tac >>
       asm_simp_tac (srw_ss()) []) >>
    `mc.mc_second_pred = mc_s0.mc_first_pred` by
      (first_x_assum (qspecl_then [`mc`, `mc_s0`] mp_tac) >>
       imp_res_tac FIND_P >> gvs[]) >>
    gvs[]) >>
  metis_tac[]
QED

Theorem eval_operand_update_var_is_some[local]:
  !op s x v. IS_SOME (eval_operand op s) ==>
    IS_SOME (eval_operand op (update_var x v s))
Proof
  Cases >> rw[eval_operand_def, update_var_def, lookup_var_def,
              finite_mapTheory.FLOOKUP_UPDATE] >> rw[]
QED

Theorem ac_diff_preds_downstream_witness[local]:
  !cands h rest mp mc or_v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    MEM mc cands /\ mc.mc_second_id = h.inst_id /\
    or_v = ac_or_var h.inst_id /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands ==>
    ?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP ((h.inst_id, Var or_v)::mp) mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP ((h.inst_id, Var or_v)::mp) mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = Var or_v
Proof
  rpt strip_tac >>
  (* Extract needed facts from chain_inv without expanding *)
  `ac_cands_ordered cands (h::rest)` by
    metis_tac[ac_chain_inv_def] >>
  `!mc1 mc2 x. MEM mc1 cands /\ MEM mc2 cands /\
     (mc1.mc_second_pred = Var x \/ mc1.mc_first_pred = Var x) ==>
     x <> ac_or_var mc2.mc_second_id /\ x <> ac_iz_var mc2.mc_second_id` by
    metis_tac[ac_chain_inv_def] >>
  (* Get the downstream instruction *)
  fs[listTheory.EXISTS_MEM] >>
  rename1 `MEM mc_down cands` >>
  `?idx_s. idx_s < LENGTH rest /\
     (EL idx_s rest).inst_id = mc_down.mc_second_id` by
    metis_tac[ac_cands_first_at_head] >>
  qabbrev_tac `inst_next = EL idx_s rest` >>
  `MEM inst_next rest` by
    (simp[Abbr `inst_next`] >> metis_tac[MEM_EL]) >>
  `inst_next.inst_id = mc_down.mc_second_id` by simp[Abbr `inst_next`] >>
  (* FIND for inst_next returns some mc_found *)
  `?mc_found. FIND (\mc''. mc''.mc_second_id = inst_next.inst_id)
               cands = SOME mc_found` by (
    irule FIND_MEM_EXISTS >>
    qexists_tac `mc_down` >> simp[]) >>
  `mc_found.mc_second_id = inst_next.inst_id` by
    (drule FIND_P >> simp[]) >>
  `MEM mc_found cands` by (drule FIND_MEM >> simp[]) >>
  (* mc_found = mc_down by uniqueness of mc_second_id *)
  `mc_found = mc_down` by (
    `mc_found.mc_second_id = mc_down.mc_second_id` by simp[] >>
    `?n1. n1 < LENGTH cands /\ EL n1 cands = mc_found` by
      metis_tac[MEM_EL] >>
    `?n2. n2 < LENGTH cands /\ EL n2 cands = mc_down` by
      metis_tac[MEM_EL] >>
    `n1 < LENGTH (MAP (\mc. mc.mc_second_id) cands) /\
     n2 < LENGTH (MAP (\mc. mc.mc_second_id) cands)` by simp[] >>
    `EL n1 (MAP (\mc. mc.mc_second_id) cands) =
     EL n2 (MAP (\mc. mc.mc_second_id) cands)` by simp[EL_MAP] >>
    `n1 = n2` by metis_tac[ALL_DISTINCT_EL_IMP] >>
    gvs[]) >>
  (* Now mc_found = mc_down; use mc_down directly *)
  qexistsl_tac [`inst_next`, `mc_down`] >> gvs[] >>
  (* mc_down.mc_first_id = h.inst_id, so ALOOKUP gives SOME (Var or_v) *)
  simp[] >>
  (* Var or_v ≠ mc_down.mc_second_pred: freshness *)
  Cases_on `mc_down.mc_second_pred` >> simp[] >>
  spose_not_then strip_assume_tac >> gvs[] >>
  first_x_assum (qspecl_then [`mc_down`, `mc`, `ac_or_var h.inst_id`] mp_tac) >>
  gvs[]
QED

(* When FIND(h)=NONE, the chain_inv witness must be in rest, not h. *)
Theorem ci_witness_in_rest[local]:
  !cands h rest mp s pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = NONE ==>
    ?inst_s mc_s. MEM inst_s rest /\
      FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
      (case ALOOKUP mp mc_s.mc_first_id of
         SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
      (case ALOOKUP mp mc_s.mc_first_id of
         SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
Proof
  rpt strip_tac >>
  `?inst_s mc_s. MEM inst_s (h::rest) /\
     FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
     (case ALOOKUP mp mc_s.mc_first_id of
        SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
     (case ALOOKUP mp mc_s.mc_first_id of
        SOME p => p | NONE => mc_s.mc_first_pred) = pred_op` by
    metis_tac[ac_chain_inv_def] >>
  Cases_on `inst_s = h` >> gvs[MEM] >> metis_tac[]
QED

(*
 * Diff-preds transfer: common boilerplate for all diff-preds cases (5a,5b,6a).
 * Given the OR/IZ setup, transfers chain_inv to rest with mp' = (h.id, Var or_v)::mp.
 * Caller only provides: eval of pred_op', witness, and eval preservation.
 *)
Theorem ac_chain_inv_diff_preds_transfer[local]:
  !cands h rest mp s s' pred_op pred_op' v v' mc.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (* Eval preservation: s' agrees with s on all operands that avoid or_v/iz_v *)
    (!op. (!x. op = Var x ==>
       x <> ac_or_var h.inst_id /\ x <> ac_iz_var h.inst_id) ==>
       eval_operand op s' = eval_operand op s) /\
    (* New pred evaluates to nonzero *)
    eval_operand pred_op' s' = SOME v' /\ v' <> 0w /\
    (* New pred freshness — only for candidates still active in rest *)
    (!x. pred_op' = Var x ==>
       (!i. MEM i rest ==> ~MEM x i.inst_outputs) /\
       (!mc'. MEM mc' cands /\
          (?j. MEM j rest /\ mc'.mc_second_id = j.inst_id) ==>
          x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id)) /\
    (* or_v and iz_v evaluable in s' *)
    IS_SOME (eval_operand (Var (ac_or_var h.inst_id)) s') /\
    IS_SOME (eval_operand (Var (ac_iz_var h.inst_id)) s') /\
    (* Witness in rest *)
    (?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP ((h.inst_id, Var (ac_or_var h.inst_id))::mp) mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
       (case ALOOKUP ((h.inst_id, Var (ac_or_var h.inst_id))::mp) mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op')
  ==>
    ac_chain_inv cands rest
      ((h.inst_id, Var (ac_or_var h.inst_id))::mp)
      s' pred_op' v'
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac FIND_P >> imp_res_tac FIND_MEM >> gvs[] >>
  irule ac_chain_inv_transfer >> simp[] >>
  rpt conj_tac
  (* 1. SSA cand preds *)
  >- (fs[ac_chain_inv_def] >> metis_tac[MEM])
  (* 2. output no clobber mp' *)
  >- (rpt strip_tac >> Cases_on `h.inst_id = id` >> gvs[]
      >- (fs[ac_chain_inv_def] >> metis_tac[MEM])
      >- (fs[ac_chain_inv_def] >> metis_tac[MEM]))
  (* 3. operand evaluability in s' *)
  >- (rpt strip_tac >>
      `eval_operand op s' = eval_operand op s` by (
        first_x_assum irule >> rpt strip_tac >>
        fs[ac_chain_inv_def] >> metis_tac[MEM]) >>
      fs[ac_chain_inv_def] >> metis_tac[MEM])
  (* 4. mp' disjoint from rest *)
  >- (rpt strip_tac >>
      fs[ac_chain_inv_def, ac_cands_ordered_def, ALL_DISTINCT, MAP, MEM_MAP] >>
      metis_tac[])
  (* 5. cand pred evaluability in s' *)
  >- (rpt strip_tac >>
      `eval_operand mc'.mc_second_pred s' = eval_operand mc'.mc_second_pred s` by (
        first_x_assum irule >> rpt strip_tac >>
        fs[ac_chain_inv_def] >> metis_tac[MEM]) >>
      `eval_operand mc'.mc_first_pred s' = eval_operand mc'.mc_first_pred s` by (
        first_x_assum irule >> rpt strip_tac >>
        fs[ac_chain_inv_def] >> metis_tac[MEM]) >>
      fs[ac_chain_inv_def] >> metis_tac[])
  (* 6. mp' pred evaluability *)
  >- (rpt strip_tac >> reverse (Cases_on `h.inst_id = id`) >> gvs[] >>
      `IS_SOME (eval_operand p s)` by
        (imp_res_tac ci_mp_eval >> gvs[]) >>
      Cases_on `p` >> gvs[eval_operand_def, optionTheory.IS_SOME_DEF]
      >- (rename1 `ALOOKUP mp id = SOME (Var vn)` >>
          Cases_on `vn = ac_or_var h.inst_id` >> gvs[] >>
          Cases_on `vn = ac_iz_var h.inst_id` >> gvs[] >>
          `eval_operand (Var vn) s' = eval_operand (Var vn) s` by
            (first_x_assum irule >> simp[]) >>
          gvs[eval_operand_def])
      >- (`eval_operand (Label s'') s' = eval_operand (Label s'') s` by
            (first_x_assum irule >> simp[]) >>
          gvs[eval_operand_def]))
  (* 7. witness *)
  >- metis_tac[]
  (* 8. old chain_inv *)
  >- metis_tac[]
QED

(*
 * Combined diff-preds transfer lemmas.
 * Internalize witness derivation so callers don't need exists_vars_tac after irule.
 *)

(* word_or = 0w: original witness stays in rest (not h, since h's pred evals to 0w) *)
Theorem ac_chain_inv_diff_preds_zero[local]:
  !cands h rest mp s s' mc v1 v2 pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of NONE => mc.mc_first_pred | SOME p => p)
      <> mc.mc_second_pred /\
    eval_operand (case ALOOKUP mp mc.mc_first_id of
                    NONE => mc.mc_first_pred | SOME p => p) s = SOME v1 /\
    eval_operand mc.mc_second_pred s = SOME v2 /\
    word_or v1 v2 = 0w /\
    (!op. (!x. op = Var x ==> x <> ac_or_var h.inst_id /\ x <> ac_iz_var h.inst_id)
      ==> eval_operand op s' = eval_operand op s) /\
    IS_SOME (eval_operand (Var (ac_or_var h.inst_id)) s') /\
    IS_SOME (eval_operand (Var (ac_iz_var h.inst_id)) s')
  ==>
    ac_chain_inv cands rest ((h.inst_id, Var (ac_or_var h.inst_id))::mp)
      s' pred_op v
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `afp = case ALOOKUP mp mc.mc_first_id of
                        NONE => mc.mc_first_pred | SOME p => p` >>
  (* Get witness from ac_diff_preds_not_witness (includes mc_s.mc_first_id <> h.inst_id) *)
  `?inst_s mc_s. MEM inst_s rest /\
     FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
     (case ALOOKUP mp mc_s.mc_first_id of
        SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
     (case ALOOKUP mp mc_s.mc_first_id of
        SOME p => p | NONE => mc_s.mc_first_pred) = pred_op /\
     mc_s.mc_first_id <> h.inst_id` by (
    simp[Abbr `afp`] >>
    match_mp_tac ac_diff_preds_not_witness >>
    qexistsl_tac [`s`, `v`, `mc`] >> simp[]) >>
  (* Now transfer chain_inv to rest *)
  match_mp_tac ac_chain_inv_diff_preds_transfer >>
  qexistsl_tac [`s`, `pred_op`, `v`, `mc`] >>
  simp[Abbr `afp`] >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  `mc.mc_second_id = h.inst_id` by (imp_res_tac FIND_P >> fs[]) >>
  rpt conj_tac
  (* eval_operand pred_op s' = SOME v *)
  >- (`eval_operand pred_op s' = eval_operand pred_op s` by (
        first_x_assum irule >> rpt strip_tac >>
        `?i. MEM i (h::rest) /\ mc.mc_second_id = i.inst_id` by
          (qexists_tac `h` >> simp[]) >>
        metis_tac[ci_pred_fresh_ac]) >>
      metis_tac[ci_eval_pred])
  (* v <> 0w *)
  >- metis_tac[ci_eval_pred]
  (* pred_op freshness *)
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (rpt gen_tac >> strip_tac >>
          `MEM i (h::rest)` by simp[] >>
          metis_tac[ci_pred_fresh_outputs])
      >- (rpt gen_tac >> strip_tac >>
          `?i. MEM i (h::rest) /\ mc'.mc_second_id = i.inst_id` by
            (qexists_tac `j` >> simp[]) >>
          metis_tac[ci_pred_fresh_ac]))
  (* witness in rest with extended mp *)
  >- (qexistsl_tac [`inst_s`, `mc_s`] >> simp[] >>
      Cases_on `h.inst_id = mc_s.mc_first_id` >> gvs[])
QED

(* word_or <> 0w with EXISTS: downstream candidate provides new witness *)
Theorem ac_chain_inv_diff_preds_nonzero[local]:
  !cands h rest mp s s' mc v1 v2.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of NONE => mc.mc_first_pred | SOME p => p)
      <> mc.mc_second_pred /\
    eval_operand (case ALOOKUP mp mc.mc_first_id of
                    NONE => mc.mc_first_pred | SOME p => p) s = SOME v1 /\
    eval_operand mc.mc_second_pred s = SOME v2 /\
    word_or v1 v2 <> 0w /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands /\
    (!op. (!x. op = Var x ==> x <> ac_or_var h.inst_id /\ x <> ac_iz_var h.inst_id)
      ==> eval_operand op s' = eval_operand op s) /\
    IS_SOME (eval_operand (Var (ac_or_var h.inst_id)) s') /\
    IS_SOME (eval_operand (Var (ac_iz_var h.inst_id)) s') /\
    eval_operand (Var (ac_or_var h.inst_id)) s' = SOME (word_or v1 v2)
  ==>
    ac_chain_inv cands rest ((h.inst_id, Var (ac_or_var h.inst_id))::mp)
      s' (Var (ac_or_var h.inst_id)) (word_or v1 v2)
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac FIND_P >> imp_res_tac FIND_MEM >> gvs[] >>
  (* Get downstream witness from ac_diff_preds_downstream_witness *)
  `?inst_s mc_s. MEM inst_s rest /\
     FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
     (case ALOOKUP ((h.inst_id, Var (ac_or_var h.inst_id))::mp) mc_s.mc_first_id of
        SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
     (case ALOOKUP ((h.inst_id, Var (ac_or_var h.inst_id))::mp) mc_s.mc_first_id of
        SOME p => p | NONE => mc_s.mc_first_pred) =
       Var (ac_or_var h.inst_id)` by (
    match_mp_tac ac_diff_preds_downstream_witness >>
    qexists_tac `mc` >> simp[]) >>
  (* Extract ALL_DISTINCT inst_ids for freshness argument *)
  `ALL_DISTINCT (MAP (\i. i.inst_id) (h::rest))` by (
    imp_res_tac ci_cands_ordered >> fs[ac_cands_ordered_def]) >>
  match_mp_tac ac_chain_inv_diff_preds_transfer >>
  qexistsl_tac [`s`, `pred_op`, `v`, `mc`] >> simp[] >>
  rpt conj_tac
  (* Part A: outputs don't contain ac_or_var h.inst_id *)
  >- (rpt gen_tac >> strip_tac >>
      `MEM i (h::rest)` by simp[] >>
      metis_tac[ci_output_fresh_ac])
  (* Part B: h.inst_id <> mc'.mc_second_id for active candidates in rest *)
  >- (rpt gen_tac >> strip_tac >>
      fs[ALL_DISTINCT, MAP, MEM_MAP] >> metis_tac[])
  (* witness *)
  >- (qexistsl_tac [`inst_s`, `mc_s`] >> simp[] >>
      Cases_on `h.inst_id = mc_s.mc_first_id` >> gvs[])
QED

(*
 * ac_chain_step: one-step chain progress, split into 3 sub-lemmas.
 * Process h through ac_apply_merge_step. The contribution either:
 *   - aborts (ASSERT with zero condition), or
 *   - succeeds, preserving exec_equiv and transferring chain_inv to rest.
 *)

(* Sub-lemma 1: FIND = NONE — h is not a merge target *)
Theorem ac_chain_step_find_none[local]:
  !h rest cands mp fuel ctx s pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = NONE ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    (?sa. run_insts fuel ctx contrib s = Abort Revert_abort sa /\
          execution_equiv UNIV (revert_state (set_returndata [] s)) sa) \/
    (?s' pred_op' v'. run_insts fuel ctx contrib s = OK s' /\
          execution_equiv UNIV (revert_state (set_returndata [] s))
                               (revert_state (set_returndata [] s')) /\
          ac_chain_inv cands rest mp' s' pred_op' v')
Proof
  rpt gen_tac >> strip_tac >>
  simp[ac_apply_merge_step_def, LET_THM] >>
  Cases_on `EXISTS (\mc. mc.mc_first_id = h.inst_id) cands`
  >- (
    simp[pairTheory.LAMBDA_PROD] >>
    DISJ2_TAC >>
    simp[run_insts_def, step_nop_identity] >>
    drule_all ci_witness_in_rest >> strip_tac >>
    exists_vars_tac ["pred_op", "v"] >>
    simp[revert_returndata_exec_equiv_UNIV, execution_equiv_refl] >>
    irule ac_chain_inv_identity_transfer >>
    conj_tac >- (exists_vars_tac ["inst_s", "mc_s"] >> simp[]) >>
    exists_var_tac "h" >> first_assum ACCEPT_TAC
  )
  >- (
    simp[pairTheory.LAMBDA_PROD] >>
    qpat_x_assum `ac_chain_inv _ _ _ _ _ _`
      (fn ci => ASSUME_TAC ci >>
        let val th = MATCH_MP ci_head_props ci
            val (wf, rest1) = CONJ_PAIR th
            val (safe_or_assert, rest2) = CONJ_PAIR rest1
            val (non_term, ops_eval) = CONJ_PAIR rest2
        in
          ASSUME_TAC wf >> ASSUME_TAC safe_or_assert >>
          ASSUME_TAC non_term >> ASSUME_TAC ops_eval
        end) >>
    `?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of NONE => mc_s.mc_first_pred | SOME p => p) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of NONE => mc_s.mc_first_pred | SOME p => p) = pred_op`
      by metis_tac[ci_witness_in_rest] >>
    Cases_on `ac_is_safe_between h`
    >- ((* safe_between case *)
      DISJ2_TAC >>
      drule_all safe_between_wf_step_ok >>
      disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
      simp[run_insts_def] >>
      drule ac_chain_inv_safe_step >>
      disch_then (qspecl_then [`s'`, `fuel`, `ctx`] mp_tac) >>
      simp[] >> (impl_tac >- (simp[] >> metis_tac[])) >>
      strip_tac >>
      exists_vars_tac ["pred_op", "v"] >> simp[] >>
      irule revert_returndata_exec_equiv_UNIV >> simp[]
    )
    >- ((* ASSERT case *)
      `h.inst_opcode = ASSERT` by fs[] >>
      `?op. h.inst_operands = [op]` by metis_tac[assert_single_operand] >>
      `IS_SOME (eval_operand op s)` by (first_assum irule >> simp[]) >>
      Cases_on `eval_operand op s` >- fs[] >>
      Cases_on `x = 0w`
      >- (DISJ1_TAC >>
          simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
               execution_equiv_refl])
      >- (DISJ2_TAC >>
          simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
               revert_returndata_exec_equiv_UNIV, execution_equiv_refl] >>
          metis_tac[ac_chain_inv_identity_transfer])
    )
  )
QED
Theorem ac_chain_step_same_preds[local]:
  !h rest cands mp mc fuel ctx st pred_op v.
    ac_chain_inv cands (h::rest) mp st pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) = mc.mc_second_pred ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    (?sa. run_insts fuel ctx contrib st = Abort Revert_abort sa /\
          execution_equiv UNIV (revert_state (set_returndata [] st)) sa) \/
    (?st' pred_op' v'. run_insts fuel ctx contrib st = OK st' /\
          execution_equiv UNIV (revert_state (set_returndata [] st))
                               (revert_state (set_returndata [] st')) /\
          ac_chain_inv cands rest mp' st' pred_op' v')
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac FIND_P >> gvs[] >>
  qabbrev_tac `actual_fp = case ALOOKUP mp mc.mc_first_id of
                              NONE => mc.mc_first_pred | SOME p => p` >>
  simp[ac_apply_merge_step_def, LET_THM] >>
  Cases_on `EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands`
  >- (
    simp[pairTheory.LAMBDA_PROD] >>
    DISJ2_TAC >>
    simp[run_insts_def, step_nop_identity] >>
    exists_vars_tac ["pred_op", "v"] >>
    simp[revert_returndata_exec_equiv_UNIV, execution_equiv_refl] >>
    irule ac_chain_inv_same_preds_mp_step_id >>
    simp[Abbr `actual_fp`] >> metis_tac[]
  )
  >- (
    simp[pairTheory.LAMBDA_PROD] >>
    (* Extract head properties while preserving ac_chain_inv *)
    qpat_x_assum `ac_chain_inv _ _ _ _ _ _`
      (fn ci => ASSUME_TAC ci >>
        let val th = MATCH_MP ci_head_props ci
            val (wf, rest1) = CONJ_PAIR th
            val (safe_or_assert, rest2) = CONJ_PAIR rest1
            val (non_term, ops_eval) = CONJ_PAIR rest2
        in
          ASSUME_TAC wf >> ASSUME_TAC safe_or_assert >>
          ASSUME_TAC non_term >> ASSUME_TAC ops_eval
        end) >>
    (* Establish witness (unfold Abbrev so metis_tac can see the CASE expr) *)
    `?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of NONE => mc_s.mc_first_pred | SOME p => p) <> mc_s.mc_second_pred /\
       (case ALOOKUP mp mc_s.mc_first_id of NONE => mc_s.mc_first_pred | SOME p => p) = pred_op`
      by (fs[Abbr `actual_fp`] >> metis_tac[ac_chain_inv_witness_in_rest_same]) >>
    Cases_on `ac_is_safe_between h`
    >- ((* safe_between + FIND=SOME is vacuously false:
           FIND=SOME → ASSERT (ci_merge_target_assert), ASSERT is volatile *)
      `h.inst_opcode = ASSERT` by metis_tac[ci_merge_target_assert, MEM] >>
      fs[ac_is_safe_between_def, ac_is_volatile_def]
    )
    >- ((* ASSERT case *)
      `h.inst_opcode = ASSERT` by fs[] >>
      `?cond_op. h.inst_operands = [cond_op]` by metis_tac[assert_single_operand] >>
      `IS_SOME (eval_operand cond_op st)` by metis_tac[ci_operand_eval, MEM] >>
      Cases_on `eval_operand cond_op st` >- fs[] >>
      rename1 `eval_operand cond_op st = SOME cval` >>
      Cases_on `cval = 0w`
      >- (
        DISJ1_TAC >>
        simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
             execution_equiv_refl]
      )
      >- (
        DISJ2_TAC >>
        simp[run_insts_def, step_inst_non_invoke, step_inst_base_def,
             revert_returndata_exec_equiv_UNIV, execution_equiv_refl] >>
        metis_tac[ac_chain_inv_same_preds_mp_step_id]
      )
    )
  )
QED

Theorem ac_chain_step_diff_preds[local]:
  !h rest cands mp mc fuel ctx s pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) <> mc.mc_second_pred ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    (?sa. run_insts fuel ctx contrib s = Abort Revert_abort sa /\
          execution_equiv UNIV (revert_state (set_returndata [] s)) sa) \/
    (?s' pred_op' v'. run_insts fuel ctx contrib s = OK s' /\
          execution_equiv UNIV (revert_state (set_returndata [] s))
                               (revert_state (set_returndata [] s')) /\
          ac_chain_inv cands rest mp' s' pred_op' v')
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac FIND_P >> gvs[] >>
  qabbrev_tac `actual_fp = case ALOOKUP mp mc.mc_first_id of
                              NONE => mc.mc_first_pred | SOME p => p` >>
  simp[ac_apply_merge_step_def, LET_THM] >>
  `inst_wf h` by metis_tac[ci_every_wf, EVERY_MEM, MEM] >>
  `h.inst_opcode = ASSERT` by metis_tac[ci_merge_target_assert, MEM] >>
  `eval_operand pred_op s = SOME v /\ v <> 0w` by metis_tac[ci_eval_pred] >>
  `IS_SOME (eval_operand actual_fp s)` by (
    simp[Abbr `actual_fp`] >>
    Cases_on `ALOOKUP mp mc.mc_first_id` >> simp[]
    >- (fs[ac_chain_inv_def] >> metis_tac[FIND_MEM])
    >- (fs[ac_chain_inv_def] >> metis_tac[])) >>
  `IS_SOME (eval_operand mc.mc_second_pred s)` by
    (fs[ac_chain_inv_def] >> metis_tac[FIND_MEM]) >>
  Cases_on `eval_operand actual_fp s` >>
  Cases_on `eval_operand mc.mc_second_pred s` >>
    gvs[optionTheory.IS_SOME_DEF] >>
  rename1 `eval_operand actual_fp s = SOME v1` >>
  rename1 `eval_operand mc.mc_second_pred s = SOME v2` >>
  qabbrev_tac `or_v = ac_or_var h.inst_id` >>
  qabbrev_tac `iz_v = ac_iz_var h.inst_id` >>
  qabbrev_tac `s_iz = update_var iz_v (bool_to_word (word_or v1 v2 = 0w))
                        (update_var or_v (word_or v1 v2) s)` >>
  `or_v <> iz_v` by
    simp[Abbr `or_v`, Abbr `iz_v`, ac_or_var_def, ac_iz_var_def] >>
  qabbrev_tac `or_inst = instruction h.inst_id OR
    [actual_fp; mc.mc_second_pred] [or_v]` >>
  qabbrev_tac `iz_inst = instruction (h.inst_id + 1) ISZERO
    [Var or_v] [iz_v]` >>
  `run_insts fuel ctx [or_inst; iz_inst] s = OK s_iz /\
   eval_operand (Var iz_v) s_iz =
     SOME (bool_to_word (word_or v1 v2 = 0w)) /\
   eval_operand (Var or_v) s_iz = SOME (word_or v1 v2) /\
   execution_equiv UNIV s s_iz /\
   (!opr. (!x. opr = Var x ==> x <> or_v /\ x <> iz_v) ==>
      eval_operand opr s_iz = eval_operand opr s)` by (
    qspecl_then [`fuel`, `ctx`, `s`, `actual_fp`, `mc.mc_second_pred`,
                 `or_v`, `iz_v`, `h.inst_id`, `v1`, `v2`]
      mp_tac ac_or_iz_step >>
    simp[Abbr `or_inst`, Abbr `iz_inst`, Abbr `s_iz`, LET_THM]) >>
  `?cond_op. h.inst_operands = [cond_op]` by
    (gvs[inst_wf_def] >> Cases_on `h.inst_operands` >> gvs[] >>
     Cases_on `t` >> gvs[]) >>
  (* Reduce the lambda-pair applied to the if-then-else *)
  simp[COND_RAND, COND_RATOR, pairTheory.LAMBDA_PROD,
       Abbr `or_inst`, Abbr `iz_inst`, run_insts_append] >>
  (* Normalize constructor→literal BEFORE COND_CASES_TAC *)
  RULE_ASSUM_TAC (REWRITE_RULE [instruction_to_literal]) >>
  (* Use run_insts_three to decompose the 3-element list *)
  simp[run_insts_three] >>
  COND_CASES_TAC
  >- (
    simp[Abbr `or_v`] >>
    DISJ2_TAC >>
    simp[run_insts_def, step_nop_identity] >>
    Cases_on `word_or v1 v2 = 0w`
    >- suspend "exists_zero"
    >- suspend "exists_nonzero"
  )
  >- (
    simp[Abbr `or_v`] >>
    Cases_on `word_or v1 v2 = 0w`
    >- suspend "not_exists_zero"
    >- suspend "not_exists_nonzero"
  )
QED

Resume ac_chain_step_diff_preds[exists_zero]:
  (* word_or = 0w: chain_inv transfers with original pred *)
  exists_vars_tac ["pred_op", "v"] >>
  conj_tac >- (irule revert_returndata_exec_equiv_UNIV >> simp[]) >>
  match_mp_tac ac_chain_inv_diff_preds_zero >>
  exists_vars_tac ["s", "mc", "v1", "v2"] >>
  simp[Abbr `actual_fp`, Abbr `iz_v`,
       Abbr `s_iz`, update_var_def, eval_operand_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       optionTheory.IS_SOME_DEF]
QED

Resume ac_chain_step_diff_preds[exists_nonzero]:
  (* word_or ≠ 0w: chain_inv transfers with new pred *)
  irule_at Any ac_chain_inv_diff_preds_nonzero >>
  exists_vars_tac ["v2", "v1", "v", "s", "pred_op", "mc"] >>
  simp[Abbr `actual_fp`, Abbr `iz_v`,
       Abbr `s_iz`, update_var_def, eval_operand_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       optionTheory.IS_SOME_DEF] >>
  irule revert_returndata_exec_equiv_UNIV >>
  fs[update_var_def]
QED

Resume ac_chain_step_diff_preds[not_exists_zero]:
  (* word_or = 0w: bool_to_word T = 1w ≠ 0w → ASSERT succeeds *)
  DISJ2_TAC >>
  `step_inst fuel ctx (h with inst_operands := [Var iz_v]) s_iz = OK s_iz` by (
    irule step_assert_ok >> simp[bool_to_word_def]) >>
  `run_insts fuel ctx [h with inst_operands := [Var iz_v]] s_iz = OK s_iz` by
    simp[run_insts_def] >>
  simp[] >>
  exists_vars_tac ["pred_op", "v"] >>
  conj_tac >- (irule revert_returndata_exec_equiv_UNIV >> simp[]) >>
  match_mp_tac ac_chain_inv_diff_preds_zero >>
  exists_vars_tac ["s", "mc", "v1", "v2"] >>
  simp[Abbr `actual_fp`, Abbr `iz_v`,
       Abbr `s_iz`, update_var_def, eval_operand_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       optionTheory.IS_SOME_DEF]
QED

Resume ac_chain_step_diff_preds[not_exists_nonzero]:
  (* word_or ≠ 0w: ASSERT with 0w → Abort *)
  DISJ1_TAC >>
  `step_inst fuel ctx (h with inst_operands := [Var iz_v]) s_iz =
    Abort Revert_abort (revert_state (set_returndata [] s_iz))` by (
    irule step_assert_abort >> simp[bool_to_word_def]) >>
  `run_insts fuel ctx [h with inst_operands := [Var iz_v]] s_iz =
    Abort Revert_abort (revert_state (set_returndata [] s_iz))` by
    simp[run_insts_def] >>
  simp[] >>
  irule revert_returndata_exec_equiv_UNIV >> simp[]
QED

Finalise ac_chain_step_diff_preds;
Theorem ac_chain_step[local]:
  !h rest cands mp fuel ctx s pred_op v.
    ac_chain_inv cands (h::rest) mp s pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    (?sa. run_insts fuel ctx contrib s = Abort Revert_abort sa /\
          execution_equiv UNIV (revert_state (set_returndata [] s)) sa) \/
    (?s' pred_op' v'. run_insts fuel ctx contrib s = OK s' /\
          execution_equiv UNIV (revert_state (set_returndata [] s))
                               (revert_state (set_returndata [] s')) /\
          ac_chain_inv cands rest mp' s' pred_op' v')
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `FIND (\mc. mc.mc_second_id = h.inst_id) cands`
  >- metis_tac[ac_chain_step_find_none]
  >- (rename1 `FIND _ _ = SOME mc` >>
      Cases_on `(case ALOOKUP mp mc.mc_first_id of
                   NONE => mc.mc_first_pred | SOME p => p) = mc.mc_second_pred`
      >- metis_tac[ac_chain_step_same_preds]
      >- metis_tac[ac_chain_step_diff_preds])
QED

Theorem ac_deferred_chain_abort:
  !insts cands mp fuel ctx s pred_op v.
    ac_chain_inv cands insts mp s pred_op v /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) ==>
    ?sa. run_insts fuel ctx
           (SND (FOLDL (ac_apply_merge_step cands) (mp, []) insts)) s =
         Abort Revert_abort sa /\
         execution_equiv UNIV (revert_state (set_returndata [] s)) sa
Proof
  Induct >- simp[ac_chain_inv_def] >>
  rpt strip_tac >>
  drule ac_chain_step >> simp[] >>
  Cases_on `ac_apply_merge_step cands (mp,[]) h` >>
  simp[LET_THM] >> strip_tac >>
  (* Now hypothesis: ∀fuel ctx. abort ∨ ok *)
  first_x_assum (qspecl_then [`fuel`, `ctx`] strip_assume_tac)
  >- (
    (* Contribution aborts *)
    qspecl_then [`h`, `insts`, `cands`, `mp`] mp_tac ac_foldl_cons >>
    simp[LET_THM] >> strip_tac >> simp[run_insts_append] >>
    metis_tac[]
  )
  >- (
    (* Contribution succeeds, chain_inv for rest *)
    qspecl_then [`h`, `insts`, `cands`, `mp`] mp_tac ac_foldl_cons >>
    simp[LET_THM] >> strip_tac >> simp[run_insts_append] >>
    (* Use IH: first universally-quantified assumption *)
    first_x_assum drule >> simp[] >> strip_tac >>
    metis_tac[execution_equiv_trans]
  )
QED

(* ================================================================
 * Weak chain invariant: like ac_chain_inv but without the diff-preds
 * requirement on the witness. Instead, includes DFG invariant so the
 * same-preds+not-fid case terminates with a direct abort (the ASSERT's
 * ISZERO operand is 0w because the underlying predicate is nonzero).
 * ================================================================ *)

Definition ac_chain_inv_w_def:
  ac_chain_inv_w cands insts mp dfg s pred_op v <=>
    (* Structural: same as ac_chain_inv *)
    EVERY inst_wf insts /\
    EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE) insts /\
    EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) insts /\
    (!i op. MEM i insts /\ MEM op i.inst_operands ==>
       IS_SOME (eval_operand op s)) /\
    (!mc. MEM mc cands ==> IS_SOME (eval_operand mc.mc_second_pred s) /\
                            IS_SOME (eval_operand mc.mc_first_pred s)) /\
    eval_operand pred_op s = SOME v /\ v <> 0w /\
    (!i x. MEM i insts /\ pred_op = Var x ==> ~MEM x i.inst_outputs) /\
    (!mc x. MEM mc cands /\ pred_op = Var x /\
       (?i. MEM i insts /\ mc.mc_second_id = i.inst_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!i x mc. MEM i insts /\ MEM (Var x) i.inst_operands /\ MEM mc cands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!i x mc. MEM i insts /\ MEM x i.inst_outputs /\ MEM mc cands ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (!mc mc' x. MEM mc cands /\ MEM mc' cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==>
       x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id) /\
    (!i x mc. MEM i insts /\ MEM x i.inst_outputs /\ MEM mc cands /\
       (mc.mc_second_pred = Var x \/ mc.mc_first_pred = Var x) ==> F) /\
    (!i x id. MEM i insts /\ MEM x i.inst_outputs /\
       ALOOKUP mp id = SOME (Var x) ==> F) /\
    (!id p. ALOOKUP mp id = SOME p ==> IS_SOME (eval_operand p s)) /\
    (!i. MEM i insts ==> ALOOKUP mp i.inst_id = NONE) /\
    (!i mc. MEM i insts /\
       FIND (\mc'. mc'.mc_second_id = i.inst_id) cands = SOME mc ==>
       i.inst_opcode = ASSERT) /\
    (!mc1 mc2. MEM mc1 cands /\ MEM mc2 cands /\
       mc1.mc_second_id = mc2.mc_first_id ==>
       mc1.mc_second_pred = mc2.mc_first_pred) /\
    ac_cands_ordered cands insts /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    (* DFG invariant + structural *)
    ac_dfg_inv dfg s /\
    (!i mc. MEM i insts /\ MEM mc cands /\ mc.mc_second_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred) /\
    (!i v. MEM i insts /\ MEM v i.inst_outputs /\ dfg_get_def dfg v <> NONE ==>
       dfg_get_def dfg v = SOME i) /\
    (* Self: each instruction's operand vars not among its own outputs *)
    (!i op x. MEM i insts /\ MEM op i.inst_operands /\ op = Var x ==>
       ~MEM x i.inst_outputs) /\
    (!mc. MEM mc cands ==>
       dfg_get_def dfg (ac_or_var mc.mc_second_id) = NONE /\
       dfg_get_def dfg (ac_iz_var mc.mc_second_id) = NONE) /\
    (!mc di v. MEM mc cands /\ dfg_get_def dfg v = SOME di ==>
       ~MEM (Var (ac_or_var mc.mc_second_id)) di.inst_operands /\
       ~MEM (Var (ac_iz_var mc.mc_second_id)) di.inst_operands) /\
    (* Weak witness: efp = pred_op, but no diff-preds requirement *)
    (?inst_s mc_s. MEM inst_s insts /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op)
End

(* ================================================================
 * ciw_maintain: The core helper for maintaining ac_chain_inv_w
 * through one step. Factors out the 27 conjuncts that are common
 * to all cases, requiring only the varying parts as hypotheses.
 * ================================================================ *)
Triviality ciw_maintain[local]:
  !cands h rest mp mp' dfg s s' pred_op pred_op' v v'.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    (* State preservation: all operand evals transfer to s' *)
    (!op. IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op s')) /\
    ac_dfg_inv dfg s' /\
    (* Pred preservation *)
    eval_operand pred_op' s' = SOME v' /\ v' <> 0w /\
    (!i x. MEM i rest /\ pred_op' = Var x ==> ~MEM x i.inst_outputs) /\
    (!mc x. MEM mc cands /\ pred_op' = Var x /\
       (?i. MEM i rest /\ mc.mc_second_id = i.inst_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (* MP conditions for mp' *)
    (!i. MEM i rest ==> ALOOKUP mp' i.inst_id = NONE) /\
    (!i x id. MEM i rest /\ MEM x i.inst_outputs /\
       ALOOKUP mp' id = SOME (Var x) ==> F) /\
    (!id p. ALOOKUP mp' id = SOME p ==> IS_SOME (eval_operand p s')) /\
    (* Witness *)
    (?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp' mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op') ==>
    ac_chain_inv_w cands rest mp' dfg s' pred_op' v'
Proof
  simp[ac_chain_inv_w_def] >>
  metis_tac[EVERY_DEF, MEM, ac_cands_ordered_tail]
QED

(* One-step progress for the weak chain invariant.
   Three outcomes: (1) contribution aborts, (2) contribution OK + weak inv for rest,
   (3) contribution OK + STRONG inv for rest (diff-preds case with word_or=0w). *)
(*
 * To reuse existing chain_step_diff_preds, we need to upgrade weak→strong
 * when there's a diff-preds witness at the head.
 * ac_chain_inv_w has all structural fields of ac_chain_inv plus extra.
 * The only missing piece is the diff-preds part of the witness.
 *)
Theorem ciw_to_ci[local]:
  !cands insts mp dfg s pred_op v inst_s mc_s.
    ac_chain_inv_w cands insts mp dfg s pred_op v /\
    MEM inst_s insts /\
    FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
    (case ALOOKUP mp mc_s.mc_first_id of
       SOME p => p | NONE => mc_s.mc_first_pred) <> mc_s.mc_second_pred /\
    (case ALOOKUP mp mc_s.mc_first_id of
       SOME p => p | NONE => mc_s.mc_first_pred) = pred_op ==>
    ac_chain_inv cands insts mp s pred_op v
Proof
  rw[ac_chain_inv_w_def, ac_chain_inv_def] >> metis_tac[]
QED

(* Weaken strong back to weak *)
Theorem ci_to_ciw[local]:
  !cands insts mp dfg s pred_op v.
    ac_chain_inv cands insts mp s pred_op v /\
    ac_dfg_inv dfg s /\
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    (!i mc. MEM i insts /\ MEM mc cands /\ mc.mc_second_id = i.inst_id ==>
       ?v. i.inst_operands = [Var v] /\
           ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred) /\
    (!i v. MEM i insts /\ MEM v i.inst_outputs /\ dfg_get_def dfg v <> NONE ==>
       dfg_get_def dfg v = SOME i) /\
    (* Self: each instruction's operand vars not among its own outputs *)
    (!i op x. MEM i insts /\ MEM op i.inst_operands /\ op = Var x ==>
       ~MEM x i.inst_outputs) /\
    (!mc. MEM mc cands ==>
       dfg_get_def dfg (ac_or_var mc.mc_second_id) = NONE /\
       dfg_get_def dfg (ac_iz_var mc.mc_second_id) = NONE) /\
    (!mc di v. MEM mc cands /\ dfg_get_def dfg v = SOME di ==>
       ~MEM (Var (ac_or_var mc.mc_second_id)) di.inst_operands /\
       ~MEM (Var (ac_iz_var mc.mc_second_id)) di.inst_operands) ==>
    ac_chain_inv_w cands insts mp dfg s pred_op v
Proof
  rw[ac_chain_inv_def, ac_chain_inv_w_def] >> metis_tac[]
QED

(* Accessors for ac_chain_inv_w *)
Theorem ciw_eval_pred[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v ==>
  eval_operand pred_op s = SOME v /\ v <> 0w
Proof rw[ac_chain_inv_w_def]
QED

Theorem ciw_dfg_inv[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v ==> ac_dfg_inv dfg s
Proof rw[ac_chain_inv_w_def]
QED

Theorem ciw_every_wf[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v ==> EVERY inst_wf insts
Proof rw[ac_chain_inv_w_def]
QED

Theorem ciw_every_safe_assert[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v ==>
  EVERY (\i. ac_is_safe_between i \/ i.inst_opcode = ASSERT) insts
Proof rw[ac_chain_inv_w_def]
QED

Theorem ciw_operand_eval[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM i insts /\ MEM op i.inst_operands ==>
  IS_SOME (eval_operand op s)
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

Theorem ciw_merge_target_assert[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM i insts /\
  FIND (\mc'. mc'.mc_second_id = i.inst_id) cands = SOME mc ==>
  i.inst_opcode = ASSERT
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

Theorem ciw_iszero_connection[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM i insts /\ MEM mc cands /\ mc.mc_second_id = i.inst_id ==>
  ?v. i.inst_operands = [Var v] /\
      ac_get_iszero_operand dfg {} (Var v) = SOME mc.mc_second_pred
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

Theorem ciw_all_distinct_second[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v ==>
  ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands)
Proof rw[ac_chain_inv_w_def]
QED

Theorem ciw_cand_preds_eval[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\ MEM mc cands ==>
  IS_SOME (eval_operand mc.mc_second_pred s) /\
  IS_SOME (eval_operand mc.mc_first_pred s)
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

Theorem ciw_mp_eval[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  ALOOKUP mp id = SOME p ==>
  IS_SOME (eval_operand p s)
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract the witness from ciw without case-splitting *)
Theorem ciw_witness[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v ==>
  ?inst_s mc_s. MEM inst_s insts /\
    FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
    (case ALOOKUP mp mc_s.mc_first_id of
       SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract: all inst_ids in insts have ALOOKUP mp = NONE *)
Theorem ciw_mp_none[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM i insts ==> ALOOKUP mp i.inst_id = NONE
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract: ALOOKUP Var output clash is impossible *)
Theorem ciw_mp_var_no_output[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM i insts /\ MEM x i.inst_outputs /\
  ALOOKUP mp id = SOME (Var x) ==> F
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract: h.inst_id ≠ i.inst_id for distinct insts *)
Theorem ciw_distinct_ids[local]:
  ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
  MEM i rest ==> h.inst_id <> i.inst_id
Proof
  rw[ac_chain_inv_w_def, ac_cands_ordered_def, ALL_DISTINCT, MEM_MAP] >>
  metis_tac[]
QED

(* Extract: output/cand-pred clash is impossible *)
Theorem ciw_output_pred_clash[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM i insts /\ MEM x i.inst_outputs /\ MEM mc' cands /\
  (mc'.mc_second_pred = Var x \/ mc'.mc_first_pred = Var x) ==> F
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract: pred_op Var doesn't clash with inst outputs *)
Theorem ciw_pred_op_no_output[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM i insts /\ pred_op = Var x ==> ~MEM x i.inst_outputs
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract: pred_op Var doesn't clash with or/iz vars *)
Theorem ciw_pred_op_no_oriz[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM mc' cands /\ pred_op = Var x /\
  (?i. MEM i insts /\ mc'.mc_second_id = i.inst_id) ==>
  x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract: cand pred Var doesn't clash with or/iz vars *)
Theorem ciw_cand_pred_no_oriz[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM mc1 cands /\ MEM mc2 cands /\
  (mc1.mc_second_pred = Var x \/ mc1.mc_first_pred = Var x) ==>
  x <> ac_or_var mc2.mc_second_id /\ x <> ac_iz_var mc2.mc_second_id
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract: chaining — consecutive cands share pred *)
Theorem ciw_cands_chain[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM mc1 cands /\ MEM mc2 cands /\
  mc1.mc_second_id = mc2.mc_first_id ==>
  mc1.mc_second_pred = mc2.mc_first_pred
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(* Extract: ac_cands_ordered *)
Theorem ciw_cands_ordered[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v ==>
  ac_cands_ordered cands insts
Proof rw[ac_chain_inv_w_def]
QED

(* Extract: inst output doesn't clash with or/iz vars *)
Theorem ciw_output_no_oriz[local]:
  ac_chain_inv_w cands insts mp dfg s pred_op v /\
  MEM i insts /\ MEM x i.inst_outputs /\ MEM mc' cands ==>
  x <> ac_or_var mc'.mc_second_id /\ x <> ac_iz_var mc'.mc_second_id
Proof rw[ac_chain_inv_w_def] >> metis_tac[]
QED

(*
 * ciw_witness_not_head: when FIND=NONE for h, the ciw witness is in rest.
 * (Because FIND=NONE means h is not a mc_second_id, so h can't be the witness.)
 *)
Triviality ciw_witness_not_head[local]:
  !cands h rest mp dfg s pred_op v.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = NONE ==>
    ?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
Proof
  rpt strip_tac >>
  imp_res_tac ciw_witness >>
  `inst_s <> h` by (
    strip_tac >> gvs[] >>
    imp_res_tac FIND_P >> gvs[]) >>
  `MEM inst_s rest` by (gvs[MEM] >> metis_tac[]) >>
  metis_tac[]
QED

(* Helper: FIND returns mc for an instruction when ALL_DISTINCT mc_second_ids
   and mc is MEM cands with matching second_id *)
Triviality FIND_first_match[local]:
  !cands mc i.
    ALL_DISTINCT (MAP (\mc'. mc'.mc_second_id) cands) /\
    MEM mc cands /\ mc.mc_second_id = i.inst_id ==>
    FIND (\mc'. mc'.mc_second_id = i.inst_id) cands = SOME mc
Proof
  Induct >> simp[FIND_thm] >> rpt strip_tac >> gvs[] >>
  `h.mc_second_id <> mc.mc_second_id` by (
    gvs[ALL_DISTINCT, MAP, MEM_MAP] >> metis_tac[]) >>
  gvs[]
QED

(* Helper: FIND is unique when ALL_DISTINCT *)
Triviality FIND_unique[local]:
  !cands mc1 mc2 id.
    FIND (\mc. mc.mc_second_id = id) cands = SOME mc1 /\
    FIND (\mc. mc.mc_second_id = id) cands = SOME mc2 ==>
    mc1 = mc2
Proof
  rpt strip_tac >> gvs[]
QED

(*
 * ciw_witness_fid: GENERALIZED witness helper for fid merge targets.
 * When h is a fid merge target (EXISTS mc'.mc_first_id = h.inst_id),
 * finds a witness in rest after extending mp with (mc.mc_second_id, val)::mp.
 *
 * Case A (witness was h): follows chain link to mc'.mc_second_id in rest.
 *   The new witness's pred is val (from ALOOKUP mp').
 * Case B (witness was not h): witness stays in rest.
 *   The pred is either val (if mc_s.mc_first_id = mc.mc_second_id) or pred_op.
 *
 * Used for BOTH same-preds (val = mc.mc_second_pred) and diff-preds
 * (val = Var (ac_or_var h.inst_id)) cases.
 *)
Triviality ciw_witness_fid[local]:
  !cands h rest mp dfg s pred_op v mc val.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands ==>
    let mp' = (mc.mc_second_id, val)::mp in
    ?inst_s mc_s pred_op'.
      MEM inst_s rest /\
      FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
      (case ALOOKUP mp' mc_s.mc_first_id of
         SOME p => p | NONE => mc_s.mc_first_pred) = pred_op' /\
      (pred_op' = val \/ pred_op' = pred_op)
Proof
  simp[LET_THM] >> rpt strip_tac >>
  imp_res_tac ciw_witness >>
  imp_res_tac ciw_cands_ordered >>
  imp_res_tac ciw_all_distinct_second >>
  Cases_on `inst_s = h` >> gvs[]
  >- (
    (* Case A: witness was h → follow chain link *)
    gvs[listTheory.EXISTS_MEM] >>
    rename1 `MEM mc_fid cands` >>
    `?idx_s. idx_s < LENGTH rest /\
       (EL idx_s rest).inst_id = mc_fid.mc_second_id` by
      metis_tac[ac_cands_first_at_head] >>
    `mc_fid.mc_first_id = mc.mc_second_id` by (
      imp_res_tac FIND_P >> gvs[]) >>
    qexistsl_tac [`EL idx_s rest`, `mc_fid`] >>
    conj_tac >- metis_tac[MEM_EL] >>
    conj_tac >- (irule FIND_first_match >> metis_tac[FIND_MEM]) >>
    simp[ALOOKUP_def]
  )
  >- (
    (* Case B: witness ≠ h → already in rest *)
    `MEM inst_s rest` by metis_tac[MEM] >>
    qexistsl_tac [`inst_s`, `mc_s`] >> simp[ALOOKUP_def] >>
    Cases_on `mc.mc_second_id = mc_s.mc_first_id` >> simp[]
  )
QED

(* When word_or v1 v2 = 0w and mc_s.mc_first_id = mc.mc_second_id,
   chaining gives mc.mc_second_pred = pred_op, so v2 = v ≠ 0w,
   contradicting word_or = 0w (requires both args = 0w). *)
Triviality ciw_word_or_zero_witness[local]:
  !cands h rest mp dfg s pred_op v mc actual_fp v1 v2.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    actual_fp = (case ALOOKUP mp mc.mc_first_id of
                   NONE => mc.mc_first_pred | SOME p => p) /\
    eval_operand actual_fp s = SOME v1 /\
    eval_operand mc.mc_second_pred s = SOME v2 /\
    word_or v1 v2 = 0w ==>
    let mp' = (mc.mc_second_id, Var (ac_or_var h.inst_id))::mp in
    ?inst_s mc_s. MEM inst_s rest /\
      FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
      (case ALOOKUP mp' mc_s.mc_first_id of
         SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
Proof
  simp[LET_THM] >> rpt strip_tac >>
  imp_res_tac ciw_witness >>
  imp_res_tac ciw_all_distinct_second >>
  (* Show witness ≠ h: if witness = h, actual_fp = pred_op, so v1 = v ≠ 0w,
     but word_or=0w requires v1=0w (since word_or v1 v2 = 0w ⟹ v1 = 0w). *)
  `v1 = 0w /\ v2 = 0w` by metis_tac[word_or_eq_0w] >>
  imp_res_tac ciw_eval_pred >>
  `inst_s <> h` by (
    strip_tac >> gvs[] >>
    imp_res_tac FIND_unique >> gvs[] >>
    `ALOOKUP mp h.inst_id = NONE` by metis_tac[ciw_mp_none, MEM] >>
    imp_res_tac FIND_P >> gvs[] >>
    `v1 = v` by metis_tac[optionTheory.SOME_11] >>
    gvs[]) >>
  `MEM inst_s rest` by metis_tac[MEM] >>
  qexistsl_tac [`inst_s`, `mc_s`] >> simp[] >>
  simp[ALOOKUP_def] >>
  Cases_on `mc.mc_second_id = mc_s.mc_first_id` >> simp[]
  >- (
    (* mc_s.mc_first_id = mc.mc_second_id: contradiction —
       chaining gives mc.mc_second_pred = pred_op, so v2 = v ≠ 0w *)
    `mc.mc_second_pred = mc_s.mc_first_pred`
      by metis_tac[ciw_cands_chain, FIND_MEM] >>
    imp_res_tac FIND_P >> gvs[] >>
    `ALOOKUP mp h.inst_id = NONE` by metis_tac[ciw_mp_none, MEM] >>
    (* eval(actual_fp, s) = SOME v, actual_fp = mc_s.mc_first_pred
       (since ALOOKUP mp h.inst_id = NONE). But eval(mc_s.mc_first_pred, s) =
       SOME 0w (= v2). So v = 0w, contradicting v ≠ 0w. *)
    fs[] >> metis_tac[optionTheory.SOME_11]
  )
QED

(* When h is a fid merge target, the chain link provides a witness
   in rest with effective pred = val = Var(ac_or_var h.inst_id). *)
Triviality ciw_fid_witness_val[local]:
  !cands h rest mp dfg s pred_op v mc.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands ==>
    let mp' = (mc.mc_second_id, Var (ac_or_var h.inst_id))::mp in
    ?inst_s mc_s. MEM inst_s rest /\
      FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
      (case ALOOKUP mp' mc_s.mc_first_id of
         SOME p => p | NONE => mc_s.mc_first_pred) = Var (ac_or_var h.inst_id)
Proof
  simp[LET_THM, listTheory.EXISTS_MEM] >> rpt strip_tac >>
  rename1 `MEM mc_fid cands` >>
  imp_res_tac ciw_cands_ordered >>
  imp_res_tac ciw_all_distinct_second >>
  imp_res_tac FIND_P >> gvs[] >>
  `?idx_s. idx_s < LENGTH rest /\
     (EL idx_s rest).inst_id = mc_fid.mc_second_id` by
    metis_tac[ac_cands_first_at_head] >>
  `mc_fid.mc_first_id = mc.mc_second_id` by gvs[] >>
  qexistsl_tac [`EL idx_s rest`, `mc_fid`] >>
  conj_tac >- metis_tac[MEM_EL] >>
  conj_tac >- (irule FIND_first_match >> metis_tac[FIND_MEM]) >>
  simp[ALOOKUP_def]
QED

(* Local copy — cannot import from acSimPrecondProofs (circular dependency) *)
Triviality safe_assert_step_preserves_eval[local]:
  !fuel ctx h s s' op.
    step_inst fuel ctx h s = OK s' /\
    (ac_is_safe_between h \/ h.inst_opcode = ASSERT) /\
    inst_wf h /\
    (!op'. MEM op' h.inst_operands ==> IS_SOME (eval_operand op' s)) /\
    IS_SOME (eval_operand op s) ==>
    IS_SOME (eval_operand op s')
Proof
  rpt gen_tac >> strip_tac >> (
    TRY (`s' = s` by metis_tac[step_assert_identity] >> gvs[]) >>
    Cases_on `op` >> gvs[eval_operand_def] >>
    TRY (irule safe_between_step_is_some_mono >>
         MAP_EVERY qexists_tac [`ctx`, `fuel`, `h`, `s`] >> simp[] >> NO_TAC) >>
    `s'.vs_labels = s.vs_labels` by
      metis_tac[step_preserves_labels, ac_is_safe_between_def] >>
    gvs[]
  )
QED

(* When FIND=NONE and state/mp unchanged, ciw for h::rest implies ciw for rest *)
Triviality ciw_tail_unchanged[local]:
  !cands h rest mp dfg s pred_op v.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = NONE ==>
    ac_chain_inv_w cands rest mp dfg s pred_op v
Proof
  rw[ac_chain_inv_w_def, DISJ_IMP_THM, FORALL_AND_THM] >>
  imp_res_tac ac_cands_ordered_tail >> simp[] >>
  metis_tac[FIND_thm, optionTheory.NOT_NONE_SOME, optionTheory.SOME_11]
QED

(* When h is safe_between and FIND=NONE, ciw transfers to rest with same mp/pred/v.
   Collapses ciw_maintain's 10 subgoals into one theorem. *)
Triviality ciw_maintain_safe_between[local]:
  !cands h rest mp dfg s s' pred_op v fuel ctx.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    ac_is_safe_between h /\
    step_inst fuel ctx h s = OK s' /\
    FIND (\mc. mc.mc_second_id = h.inst_id) cands = NONE /\
    (!x. MEM x h.inst_outputs ==> ~IS_SOME (lookup_var x s)) ==>
    ac_chain_inv_w cands rest mp dfg s' pred_op v
Proof
  rpt strip_tac >>
  `inst_wf h` by fs[ac_chain_inv_w_def, EVERY_DEF] >>
  `~is_terminator h.inst_opcode` by fs[ac_is_safe_between_def] >>
  `!x. ~MEM x h.inst_outputs ==> lookup_var x s' = lookup_var x s` by
    metis_tac[step_preserves_non_output_vars] >>
  `!op. IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op s')` by
    (rpt strip_tac >>
     qspecl_then [`h`, `s`, `s'`, `fuel`, `ctx`, `op`]
       mp_tac (GEN_ALL safe_between_step_eval_is_some) >>
     fs[ac_chain_inv_w_def, EVERY_DEF] >> metis_tac[MEM]) >>
  `ac_dfg_inv dfg s'` by
    (qspecl_then [`fuel`, `ctx`, `h`, `s`, `s'`, `dfg`]
       mp_tac (GEN_ALL ac_dfg_inv_step) >>
     simp[] >> disch_then irule >>
     fs[ac_chain_inv_w_def, EVERY_DEF] >> metis_tac[MEM]) >>
  `!x. pred_op = Var x ==> ~MEM x h.inst_outputs` by
    (fs[ac_chain_inv_w_def] >> metis_tac[MEM]) >>
  imp_res_tac (GEN_ALL ciw_eval_pred) >>
  `eval_operand pred_op s' = SOME v` by (
    Cases_on `pred_op` >> fs[eval_operand_def] >>
    TRY (`lookup_var s'' s' = lookup_var s'' s` by
           (first_x_assum irule >> res_tac) >> fs[] >> NO_TAC) >>
    `s'.vs_labels = s.vs_labels` by
      metis_tac[step_preserves_labels, ac_is_safe_between_def] >>
    gvs[]) >>
  imp_res_tac (GEN_ALL ciw_witness_not_head) >>
  simp[ac_chain_inv_w_def] >>
  fs[ac_chain_inv_w_def] >>
  metis_tac[MEM, EVERY_DEF, ac_cands_ordered_tail]
QED

(* No-redefine maintenance: after a step that only modifies h's outputs,
   remaining instructions' outputs are still undefined.
   Abstract version: caller provides the state-preservation property.
   Conclusion uses = NONE (simp-normal form). *)
Triviality no_redefine_maintain_abs[local]:
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (h::rest))) /\
  (!i x. MEM i (h::rest) /\ MEM x i.inst_outputs ==>
     ~IS_SOME (lookup_var x s)) /\
  (!x. ~MEM x h.inst_outputs ==> lookup_var x s' = lookup_var x s) ==>
  (!i x. MEM i rest /\ MEM x i.inst_outputs ==>
     lookup_var x s' = NONE)
Proof
  rpt strip_tac >>
  (Q.SUBGOAL_THEN `~MEM x h.inst_outputs` ASSUME_TAC >-
    (fs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >> metis_tac[])) >>
  (Q.SUBGOAL_THEN `lookup_var x s' = lookup_var x s` SUBST1_TAC >-
    res_tac) >>
  (Q.SUBGOAL_THEN `~IS_SOME (lookup_var x s)` mp_tac >-
    metis_tac[MEM]) >>
  simp[]
QED

(* Concrete version for step_inst: combines step_preserves_non_output_vars *)
Triviality no_redefine_step_maintain[local]:
  step_inst fuel ctx h s = OK s' /\
  ~is_terminator h.inst_opcode /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (h::rest))) /\
  (!i x. MEM i (h::rest) /\ MEM x i.inst_outputs ==>
     ~IS_SOME (lookup_var x s)) ==>
  (!i x. MEM i rest /\ MEM x i.inst_outputs ==>
     lookup_var x s' = NONE)
Proof
  strip_tac >> match_mp_tac (GEN_ALL no_redefine_maintain_abs) >>
  qexistsl_tac [`s`, `h`] >> rpt conj_tac
  >- simp[]
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >>
      mp_tac step_preserves_non_output_vars >>
      disch_then (qspecl_then [`fuel`, `ctx`, `h`, `s`, `s'`] mp_tac) >>
      simp[] >> disch_then irule >> simp[])
QED

Theorem ac_chain_step_w[local]:
  !h rest cands mp dfg fuel ctx s pred_op v.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    (!i x. MEM i (h::rest) /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (h::rest))) ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    (?sa. run_insts fuel ctx contrib s = Abort Revert_abort sa /\
          execution_equiv UNIV (revert_state (set_returndata [] s)) sa) \/
    (?s' pred_op' v'. run_insts fuel ctx contrib s = OK s' /\
          execution_equiv UNIV (revert_state (set_returndata [] s))
                               (revert_state (set_returndata [] s')) /\
          ac_chain_inv_w cands rest mp' dfg s' pred_op' v' /\
          (!i x. MEM i rest /\ MEM x i.inst_outputs ==>
             ~IS_SOME (lookup_var x s')) /\
          ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) rest)))
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac ciw_eval_pred >>
  `inst_wf h` by (imp_res_tac ciw_every_wf >> fs[EVERY_DEF]) >>
  `ac_dfg_inv dfg s` by metis_tac[ciw_dfg_inv] >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) rest))` by
    gvs[ALL_DISTINCT_APPEND] >>
  Cases_on `FIND (\mc. mc.mc_second_id = h.inst_id) cands`
  >- suspend "find_none"
  >- suspend "find_some"
QED

Resume ac_chain_step_w[find_none]:
  simp[ac_apply_merge_step_def, LET_THM] >>
  imp_res_tac ciw_witness_not_head >>
  `!op. MEM op h.inst_operands ==> IS_SOME (eval_operand op s)` by
    (fs[ac_chain_inv_w_def] >> metis_tac[MEM]) >>
  Cases_on `EXISTS (\mc. mc.mc_first_id = h.inst_id) cands`
  >- (
    (* FIND=NONE + fid: NOP, s'=s *)
    simp[pairTheory.LAMBDA_PROD, run_insts_singleton,
         step_nop_identity, execution_equiv_refl] >>
    qexistsl_tac [`pred_op`, `v`] >> simp[] >>
    conj_tac >- (irule ciw_tail_unchanged >> metis_tac[]) >>
    rpt strip_tac >> res_tac >> fs[MEM]
  )
  >- (
    (* FIND=NONE + not-fid *)
    simp[pairTheory.LAMBDA_PROD] >>
    Cases_on `ac_is_safe_between h`
    >- suspend "fn_safe"
    >- suspend "fn_assert"
  )
QED

Resume ac_chain_step_w[fn_safe]:
  (* safe_between: step succeeds, preserves everything, ciw transfers to rest *)
  (Q.SUBGOAL_THEN `?s'. step_inst fuel ctx h s = OK s'` STRIP_ASSUME_TAC >-
    metis_tac[safe_between_wf_step_ok]) >>
  (Q.SUBGOAL_THEN `~is_terminator h.inst_opcode` ASSUME_TAC >-
    fs[ac_is_safe_between_def]) >>
  DISJ2_TAC >> simp[run_insts_singleton] >>
  qexistsl_tac [`pred_op`, `v`] >> rpt conj_tac
  >- (irule revert_returndata_exec_equiv_UNIV >>
      irule execution_equiv_weaken_UNIV >>
      qexists_tac `set h.inst_outputs` >>
      (Q.SUBGOAL_THEN `state_equiv (set h.inst_outputs) s s'` ASSUME_TAC >-
        (irule step_effect_free_state_equiv >> simp[] >>
         metis_tac[ac_safe_between_effect_free])) >>
      fs[stateEquivTheory.state_equiv_def])
  >- (irule (GEN_ALL ciw_maintain_safe_between) >> metis_tac[MEM])
  >- (rpt strip_tac >>
      (Q.SUBGOAL_THEN `~MEM x (h:instruction).inst_outputs` ASSUME_TAC >-
        (fs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >> metis_tac[])) >>
      (Q.SUBGOAL_THEN `lookup_var x s' = lookup_var x (s:venom_state)`
        SUBST1_TAC >-
        (mp_tac step_preserves_non_output_vars >>
         disch_then (qspecl_then [`fuel`, `ctx`, `h`, `s`, `s'`] mp_tac) >>
         simp[])) >>
      (Q.SUBGOAL_THEN `~IS_SOME (lookup_var x s)` mp_tac >-
        metis_tac[MEM]) >>
      simp[])
QED

Resume ac_chain_step_w[fn_assert]:
  (* h is ASSERT, FIND=NONE, not safe_between *)
  (Q.SUBGOAL_THEN `h.inst_opcode = ASSERT` ASSUME_TAC >-
    (fs[ac_chain_inv_w_def, EVERY_DEF] >> metis_tac[])) >>
  (Q.SUBGOAL_THEN `?cond_op. h.inst_operands = [cond_op]` STRIP_ASSUME_TAC >-
    (fs[inst_wf_def] >> Cases_on `h.inst_operands` >> fs[] >>
     Cases_on `t` >> fs[])) >>
  (Q.SUBGOAL_THEN `IS_SOME (eval_operand cond_op s)` ASSUME_TAC >-
    (res_tac >> fs[])) >>
  (Q.SUBGOAL_THEN `?cond. eval_operand cond_op s = SOME cond` STRIP_ASSUME_TAC >-
    (Cases_on `eval_operand cond_op s` >> fs[])) >>
  simp[run_insts_singleton] >>
  Cases_on `cond = 0w`
  >- (DISJ1_TAC >>
      qspecl_then [`fuel`, `ctx`, `h`, `s`, `cond_op`]
        mp_tac step_assert_abort >> simp[execution_equiv_refl])
  >- suspend "assert_ok"
QED

Resume ac_chain_step_w[assert_ok]:
  DISJ2_TAC >>
  (Q.SUBGOAL_THEN `step_inst fuel ctx h s = OK s` ASSUME_TAC >-
    (qspecl_then [`fuel`, `ctx`, `h`, `s`, `cond_op`, `cond`]
       mp_tac step_assert_ok >> simp[])) >>
  qexistsl_tac [`s`, `pred_op`, `v`] >> simp[] >>
  rpt conj_tac
  >- simp[execution_equiv_refl]
  >- (irule (GEN_ALL ciw_tail_unchanged) >> metis_tac[])
  >- (rpt strip_tac >>
      first_x_assum (qspecl_then [`i`, `x`] mp_tac) >>
      simp[MEM])
QED

(* ================================================================
 * ALOOKUP helpers for extended maps: (k,v)::mp
 * Self-contained — no ciw dependency, clean proof contexts.
 * ================================================================ *)
Triviality alookup_extend_none[local]:
  (!i. MEM i rest ==> k <> i.inst_id) /\
  (!i. MEM i rest ==> ALOOKUP mp i.inst_id = NONE) /\
  MEM i rest ==>
  ALOOKUP ((k,v)::mp) i.inst_id = NONE
Proof simp[ALOOKUP_def] >> metis_tac[]
QED

Triviality alookup_extend_var_no_output[local]:
  (!i x. MEM i rest /\ MEM x i.inst_outputs /\ new_pred = Var x ==> F) /\
  (!i x id. MEM i insts /\ MEM x i.inst_outputs /\
     ALOOKUP mp id = SOME (Var x) ==> F) /\
  MEM i rest /\ MEM x i.inst_outputs /\ MEM i insts /\
  ALOOKUP ((k,new_pred)::mp) id = SOME (Var x) ==>
  F
Proof
  simp[ALOOKUP_def] >> rpt strip_tac >>
  Cases_on `k = id` >> gvs[] >> metis_tac[]
QED

Triviality alookup_extend_eval[local]:
  IS_SOME (eval_operand new_pred s') /\
  (!id p. ALOOKUP mp id = SOME p ==> IS_SOME (eval_operand p s)) /\
  (!op. IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op s')) /\
  ALOOKUP ((k,new_pred)::mp) id = SOME p ==>
  IS_SOME (eval_operand p s')
Proof
  simp[ALOOKUP_def] >> rpt strip_tac >>
  Cases_on `k = id` >> gvs[] >> res_tac >> res_tac
QED

(* ================================================================
 * ciw_maintain_mp_extend: Specialized ciw_maintain for mp extension.
 * When mp' = (h.inst_id, new_pred)::mp, resolves ALOOKUP internally.
 * Used by all same_preds and diff_preds transfer helpers.
 * ================================================================ *)
Triviality ciw_maintain_mp_extend[local]:
  !cands h rest mp new_pred dfg s s' pred_op pred_op' v v'.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    (* State preservation *)
    (!op. IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op s')) /\
    ac_dfg_inv dfg s' /\
    (* Pred preservation *)
    eval_operand pred_op' s' = SOME v' /\ v' <> 0w /\
    (!i x. MEM i rest /\ pred_op' = Var x ==> ~MEM x i.inst_outputs) /\
    (!mc x. MEM mc cands /\ pred_op' = Var x /\
       (?i. MEM i rest /\ mc.mc_second_id = i.inst_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (* new_pred safety *)
    IS_SOME (eval_operand new_pred s') /\
    (!i x. MEM i rest /\ MEM x i.inst_outputs /\ new_pred = Var x ==> F) /\
    (!x mc. new_pred = Var x /\ MEM mc cands /\
       (?i. MEM i rest /\ i.inst_id = mc.mc_second_id) ==>
       x <> ac_or_var mc.mc_second_id /\ x <> ac_iz_var mc.mc_second_id) /\
    (* Witness for extended mp *)
    (?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       (case ALOOKUP ((h.inst_id, new_pred)::mp) mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op') ==>
    ac_chain_inv_w cands rest ((h.inst_id, new_pred)::mp) dfg s' pred_op' v'
Proof
  rpt strip_tac >>
  irule (GEN_ALL ciw_maintain) >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC)
  (* 1. var_no_output *)
  >- (rpt strip_tac >>
      pop_assum mp_tac >> simp[ALOOKUP_def] >>
      Cases_on `h.inst_id = id` >> simp[] >>
      metis_tac[ciw_mp_var_no_output, MEM])
  (* 2. none: ∀i. MEM i rest ⇒ ALOOKUP ((h.inst_id,new_pred)::mp) i.inst_id = NONE *)
  >- (rpt strip_tac >>
      irule (GEN_ALL alookup_extend_none) >>
      metis_tac[ciw_distinct_ids, ciw_mp_none, MEM])
  (* 3. eval: ∀id p. ALOOKUP (...) id = SOME p ⇒ IS_SOME (eval_operand p s') *)
  >- (rpt strip_tac >>
      pop_assum mp_tac >> simp[ALOOKUP_def] >>
      Cases_on `h.inst_id = id` >> simp[] >>
      metis_tac[ciw_mp_eval])
  (* 4. witness *)
  >- (qexistsl_tac [`inst_s`, `mc_s`] >> simp[])
  (* 5. old ciw *)
  >- (qexistsl_tac [`h`, `mp`, `pred_op`, `s`, `v`] >> simp[])
QED

(* Dispatch tactic for ciw_maintain_mp_extend:
   After irule (GEN_ALL ciw_maintain_mp_extend), there are 10 conjunctive
   subgoals. This tactic solves the 8 standard ones (output clash, or/iz,
   eval, dfg_inv), leaving only the witness subgoal and the old ciw subgoal. *)
(* Fast dispatch for ciw_maintain_mp_extend standard subgoals. *)
local
  val forall_tac = rpt strip_tac >> metis_tac[ciw_output_pred_clash,
    ciw_pred_op_no_output, ciw_cand_pred_no_oriz,
    ciw_pred_op_no_oriz, MEM]
  val atomic_tac = metis_tac[ciw_eval_pred, ciw_dfg_inv, ciw_cand_preds_eval]
in
  val ciw_mp_extend_tac =
    irule (GEN_ALL ciw_maintain_mp_extend) >>
    (rpt conj_tac THEN_LT
     TRYALL (fn (asl, g) =>
       if is_exists g then NO_TAC (asl, g)
       else if is_forall g then forall_tac (asl, g)
       else atomic_tac (asl, g)))
end;

(* Case 2 of fid_transfer: inst_s ≠ h, witness is in rest *)
Triviality ciw_same_preds_fid_transfer_case2[local]:
  !cands h rest mp dfg s pred_op v mc inst_s mc_s.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    mc.mc_second_id = h.inst_id /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) = mc.mc_second_pred /\
    MEM mc cands /\
    inst_s <> h /\
    MEM inst_s rest /\
    FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
    (case ALOOKUP mp mc_s.mc_first_id of
       NONE => mc_s.mc_first_pred | SOME p => p) = pred_op ==>
    ac_chain_inv_w cands rest ((h.inst_id, mc.mc_second_pred)::mp) dfg s
      pred_op v
Proof
  rpt strip_tac >>
  sg `ALOOKUP mp h.inst_id = NONE`
  >- metis_tac[ciw_mp_none, MEM] >>
  sg `MEM mc_s cands`
  >- metis_tac[FIND_MEM] >>
  Cases_on `h.inst_id = mc_s.mc_first_id`
  >- (
    sg `mc.mc_second_pred = mc_s.mc_first_pred`
    >- metis_tac[ciw_cands_chain] >>
    ciw_mp_extend_tac
    >- (qexistsl_tac [`inst_s`, `mc_s`] >> simp[ALOOKUP_def] >> gvs[])
    >- (qexistsl_tac [`pred_op`, `s`, `v`] >> simp[])
  )
  >- (
    ciw_mp_extend_tac
    >- (qexistsl_tac [`inst_s`, `mc_s`] >> simp[ALOOKUP_def])
    >- (qexistsl_tac [`pred_op`, `s`, `v`] >> simp[])
  )
QED

(* ciw transfer: same_preds + fid, state unchanged.
   Wraps ciw_maintain, proving all 12 hypotheses. *)
Triviality ciw_same_preds_fid_transfer[local]:
  !cands h rest mp dfg s pred_op v mc.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) = mc.mc_second_pred /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands ==>
    ac_chain_inv_w cands rest ((h.inst_id, mc.mc_second_pred)::mp) dfg s
      pred_op v
Proof
  rpt strip_tac >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  imp_res_tac FIND_P >>
  (* Get old witness from ciw *)
  imp_res_tac (GEN_ALL ciw_witness) >>
  Cases_on `inst_s = h` >> gvs[]
  >- (
    imp_res_tac (SIMP_RULE (srw_ss()) [LET_THM] (GEN_ALL ciw_witness_fid)) >>
    pop_assum (qspec_then `mc.mc_second_pred` mp_tac) >>
    simp[LET_THM] >> strip_tac >>
    ciw_mp_extend_tac
    >- (qexistsl_tac [`inst_s`, `mc_s`] >> simp[ALOOKUP_def])
    >- (qexistsl_tac [`mc.mc_second_pred`, `s`, `v`] >> simp[])
  )
  >- metis_tac[GEN_ALL ciw_same_preds_fid_transfer_case2]
QED


(*
 * Standalone helper for find_some + same_preds case.
 * When actual_fp = mc.mc_second_pred, no OR/IZ instructions are generated.
 * The contributed instructions are either [nop] (fid) or [h] (ASSERT).
 *)
(* Helper: inst_s (ciw witness) cannot be h when same preds and cond <> 0w. *)
Triviality same_preds_inst_s_neq_h[local]:
  !cands h rest mp mc dfg s pred_op v inst_s mc_s cond_op cond.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) = mc.mc_second_pred /\
    MEM inst_s (h::rest) /\
    FIND (\mc. mc.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
    (case ALOOKUP mp mc_s.mc_first_id of
       NONE => mc_s.mc_first_pred | SOME p => p) = pred_op /\
    h.inst_operands = [cond_op] /\ eval_operand cond_op s = SOME cond /\
    cond <> 0w ==>
    inst_s <> h
Proof
  rpt strip_tac >> gvs[] >>
  imp_res_tac (GEN_ALL FIND_unique) >> gvs[] >>
  (* mc_s = mc, so pred_op = mc.mc_second_pred *)
  (Q.SUBGOAL_THEN `MEM mc cands` ASSUME_TAC >- metis_tac[FIND_MEM]) >>
  (Q.SUBGOAL_THEN `mc.mc_second_id = h.inst_id` ASSUME_TAC >-
    (imp_res_tac FIND_P >> gvs[])) >>
  (* Get iszero connection for h and mc specifically *)
  (Q.SUBGOAL_THEN
    `?vv. h.inst_operands = [Var vv] /\
          ac_get_iszero_operand dfg {} (Var vv) = SOME mc.mc_second_pred`
    STRIP_ASSUME_TAC >-
    (mp_tac (GEN_ALL ciw_iszero_connection) >>
     disch_then (qspecl_then [`v`, `s`, `mc.mc_second_pred`, `mp`, `mc`,
       `h::rest`, `h`, `dfg`, `cands`] mp_tac) >>
     simp[])) >>
  (* So cond_op = Var vv *)
  gvs[] >>
  (* Now: ac_get_iszero_operand dfg {} (Var vv) = SOME mc.mc_second_pred *)
  (Q.SUBGOAL_THEN `ac_dfg_inv dfg s` ASSUME_TAC >-
    metis_tac[GEN_ALL ciw_dfg_inv]) >>
  qspecl_then [`dfg`, `{}`, `Var vv`, `s`, `mc.mc_second_pred`]
    mp_tac ac_dfg_iszero_bridge >> simp[] >>
  imp_res_tac (GEN_ALL ciw_eval_pred) >>
  rpt strip_tac >>
  Cases_on `pred_val = 0w` >> gvs[bool_to_word_def]
QED

(* Helper: same_preds ASSERT-ok case (cond <> 0w, no fid, s'=s) *)
Triviality same_preds_assert_ok_case[local]:
  !h rest cands mp mc dfg fuel ctx s pred_op v cond_op cond.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) = mc.mc_second_pred /\
    (!i x. MEM i rest /\ MEM x i.inst_outputs ==> ~IS_SOME (lookup_var x s)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) rest)) /\
    h.inst_opcode = ASSERT /\ MEM mc cands /\ inst_wf h /\
    h.inst_operands = [cond_op] /\ eval_operand cond_op s = SOME cond /\
    cond <> 0w /\ ~EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands ==>
    ?s' pred_op' v'.
      step_inst fuel ctx h s = OK s' /\
      execution_equiv UNIV (revert_state (set_returndata [] s))
                           (revert_state (set_returndata [] s')) /\
      ac_chain_inv_w cands rest ((h.inst_id, mc.mc_second_pred)::mp)
        dfg s' pred_op' v' /\
      (!i x. MEM i rest /\ MEM x i.inst_outputs ==>
         ~IS_SOME (lookup_var x s')) /\
      ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) rest))
Proof
  rpt gen_tac >> strip_tac >>
  (Q.SUBGOAL_THEN `step_inst fuel ctx h s = OK s` ASSUME_TAC >-
    (qspecl_then [`fuel`, `ctx`, `h`, `s`, `cond_op`, `cond`]
       mp_tac step_assert_ok >> simp[])) >>
  qexistsl_tac [`s`, `pred_op`, `v`] >> ASM_REWRITE_TAC[] >>
  conj_tac >- simp[execution_equiv_refl] >>
  imp_res_tac (GEN_ALL ciw_witness) >>
  (Q.SUBGOAL_THEN `inst_s <> h` ASSUME_TAC >-
    metis_tac[GEN_ALL same_preds_inst_s_neq_h]) >>
  (Q.SUBGOAL_THEN `MEM inst_s rest` ASSUME_TAC >-
    (gvs[MEM] >> metis_tac[])) >>
  (Q.SUBGOAL_THEN `mc.mc_second_id = h.inst_id` ASSUME_TAC >-
    (imp_res_tac FIND_P >> gvs[])) >>
  metis_tac[GEN_ALL ciw_same_preds_fid_transfer_case2]
QED

Triviality ac_chain_step_w_same_preds[local]:
  !h rest cands mp mc dfg fuel ctx s pred_op v.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) = mc.mc_second_pred /\
    (!i x. MEM i rest /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) rest)) ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    (?sa. run_insts fuel ctx contrib s = Abort Revert_abort sa /\
          execution_equiv UNIV (revert_state (set_returndata [] s)) sa) \/
    (?s' pred_op' v'. run_insts fuel ctx contrib s = OK s' /\
          execution_equiv UNIV (revert_state (set_returndata [] s))
                               (revert_state (set_returndata [] s')) /\
          ac_chain_inv_w cands rest mp' dfg s' pred_op' v' /\
          (!i x. MEM i rest /\ MEM x i.inst_outputs ==>
             ~IS_SOME (lookup_var x s')) /\
          ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) rest)))
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac FIND_P >> gvs[] >>
  (Q.SUBGOAL_THEN `h.inst_opcode = ASSERT` ASSUME_TAC >-
    (imp_res_tac (GEN_ALL ciw_merge_target_assert) >> metis_tac[MEM])) >>
  (Q.SUBGOAL_THEN `MEM mc cands` ASSUME_TAC >- metis_tac[FIND_MEM]) >>
  (Q.SUBGOAL_THEN `inst_wf h` ASSUME_TAC >-
    (imp_res_tac ciw_every_wf >> fs[EVERY_DEF])) >>
  (Q.SUBGOAL_THEN `?cond_op. h.inst_operands = [cond_op]` STRIP_ASSUME_TAC >-
    metis_tac[assert_single_operand]) >>
  (Q.SUBGOAL_THEN `IS_SOME (eval_operand cond_op s)` ASSUME_TAC >-
    (fs[ac_chain_inv_w_def] >> metis_tac[MEM])) >>
  (Q.SUBGOAL_THEN `?cond. eval_operand cond_op s = SOME cond` STRIP_ASSUME_TAC >-
    (Cases_on `eval_operand cond_op s` >> fs[])) >>
  simp[ac_apply_merge_step_def, LET_THM, pairTheory.LAMBDA_PROD] >>
  IF_CASES_TAC >>
  simp[pairTheory.LAMBDA_PROD, run_insts_singleton,
       step_nop_identity, execution_equiv_refl]
  >- (
    mp_tac (GEN_ALL ciw_same_preds_fid_transfer) >>
    disch_then (qspecl_then [`cands`, `h`, `rest`, `mp`, `dfg`, `s`,
                             `pred_op`, `v`, `mc`] mp_tac) >>
    ASM_REWRITE_TAC[] >> strip_tac >>
    qexistsl_tac [`pred_op`, `v`] >> ASM_REWRITE_TAC[] >>
    rpt strip_tac >> res_tac
  )
  >> (
    Cases_on `cond = 0w`
    >- (
      DISJ1_TAC >>
      qspecl_then [`fuel`, `ctx`, `h`, `s`, `cond_op`]
        mp_tac step_assert_abort >> simp[execution_equiv_refl]
    )
    >> (
      DISJ2_TAC >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM optionTheory.NOT_IS_SOME_EQ_NONE]) >>
      mp_tac (GEN_ALL same_preds_assert_ok_case) >>
      disch_then (qspecl_then [`h`, `rest`, `cands`, `mp`, `mc`, `dfg`,
                               `fuel`, `ctx`, `s`, `pred_op`, `v`,
                               `cond_op`, `cond`] mp_tac) >>
      ASM_REWRITE_TAC[] >> simp[optionTheory.NOT_IS_SOME_EQ_NONE]
    )
  )
QED

(*
 * Standalone helper for find_some + diff_preds case.
 * When actual_fp ≠ mc.mc_second_pred, OR+IZ instructions are generated.
 *)
(* Given ALL_DISTINCT on mc_second_id and MEM mc cands with mc.mc_second_id = id,
   FIND returns SOME mc. *)
Triviality FIND_all_distinct_second[local]:
  !cands mc id.
    ALL_DISTINCT (MAP (\mc. mc.mc_second_id) cands) /\
    MEM mc cands /\ mc.mc_second_id = id ==>
    FIND (\mc'. mc'.mc_second_id = id) cands = SOME mc
Proof
  Induct >> rw[FIND_thm]
  >- (Cases_on `h.mc_second_id = mc.mc_second_id` >> simp[] >>
      fs[MEM_MAP] >> metis_tac[])
  >- (first_x_assum irule >> simp[])
QED

(*
 * Helper: downstream witness for EXISTS + nonzero case.
 * When h has EXISTS (fid), there's a downstream instruction in rest
 * whose mc_first_id = h.inst_id, giving effective_fp = Var or_v.
 *)
Triviality ciw_diff_preds_downstream_witness[local]:
  !cands h rest mp dfg s pred_op v mc.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands ==>
    ?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       mc_s.mc_first_id = h.inst_id
Proof
  rpt strip_tac >>
  imp_res_tac (GEN_ALL ciw_cands_ordered) >>
  imp_res_tac (GEN_ALL ciw_all_distinct_second) >>
  fs[listTheory.EXISTS_MEM] >>
  rename1 `MEM mc_down cands` >>
  drule_all ac_cands_first_at_head >> strip_tac >>
  qexistsl_tac [`EL idx_s rest`, `mc_down`] >>
  conj_tac >- metis_tac[MEM_EL] >>
  conj_tac >- (irule FIND_all_distinct_second >> simp[]) >>
  simp[]
QED

(*
 * Helper: zero-case ciw witness transfer.
 * When word_or = 0, the original ciw witness (inst_s ≠ h) is preserved
 * because its effective_fp doesn't change (mc_s.mc_first_id ≠ h.inst_id
 * since word_or=0 means v1=v2=0 but the witness pred_op has v≠0).
 *)
Triviality ciw_diff_preds_zero_witness[local]:
  !cands h rest mp dfg s pred_op v mc.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) <> mc.mc_second_pred /\
    eval_operand (case ALOOKUP mp mc.mc_first_id of
                    NONE => mc.mc_first_pred | SOME p => p) s = SOME v1 /\
    eval_operand mc.mc_second_pred s = SOME v2 /\
    word_or v1 v2 = 0w ==>
    ?inst_s mc_s. MEM inst_s rest /\
       FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
       mc_s.mc_first_id <> h.inst_id /\
       (case ALOOKUP mp mc_s.mc_first_id of
          SOME p => p | NONE => mc_s.mc_first_pred) = pred_op
Proof
  rpt strip_tac >>
  imp_res_tac (GEN_ALL ciw_witness) >>
  `MEM mc cands` by metis_tac[FIND_MEM] >>
  imp_res_tac FIND_P >>
  (* word_or v1 v2 = 0 means v1 = 0 and v2 = 0 *)
  `v1 = 0w /\ v2 = 0w` by metis_tac[word_or_eq_0w] >>
  (* The witness inst_s can't be h *)
  sg `inst_s <> h`
  >- (
    strip_tac >> gvs[] >>
    (* If inst_s = h, then effective_fp(h) = pred_op and eval pred_op s = SOME v, v≠0 *)
    imp_res_tac (GEN_ALL ciw_eval_pred) >>
    (* But effective_fp(h) = actual_fp.
       Actually, mc_s = the mc matched to h, so mc_s.mc_first_id might be different.
       Let's think: inst_s = h means FIND for h gives mc_s. But we also have
       FIND for h gives mc. By FIND uniqueness, mc_s = mc. *)
    imp_res_tac (GEN_ALL FIND_unique) >> gvs[] >>
    (* Now effective_fp(mc_s) = effective_fp(mc) = actual_fp.
       actual_fp evaluates to v1 = 0w. But pred_op = actual_fp, so
       eval pred_op s = SOME 0w. But v ≠ 0w. Contradiction. *)
    gvs[]) >>
  sg `MEM inst_s rest`
  >- (gvs[MEM] >> metis_tac[]) >>
  qexistsl_tac [`inst_s`, `mc_s`] >> simp[] >>
  (* mc_s.mc_first_id ≠ h.inst_id: if equal, then
     effective_fp(mc_s) = ALOOKUP mp h.inst_id which is NONE (since h ∈ h::rest),
     so effective_fp(mc_s) = mc_s.mc_first_pred = pred_op.
     But mc_s.mc_first_id = h.inst_id = mc.mc_second_id,
     and by ciw cands_chain: mc.mc_second_pred = mc_s.mc_first_pred.
     So pred_op = mc_s.mc_first_pred = mc.mc_second_pred.
     eval pred_op s = SOME v, v ≠ 0, but eval mc.mc_second_pred s = SOME v2 = 0w.
     Contradiction since pred_op = mc.mc_second_pred. *)
  spose_not_then strip_assume_tac >> gvs[] >>
  sg `ALOOKUP mp h.inst_id = NONE`
  >- metis_tac[ciw_mp_none, MEM] >>
  sg `MEM mc_s cands`
  >- metis_tac[FIND_MEM] >>
  imp_res_tac (GEN_ALL ciw_cands_chain) >>
  imp_res_tac (GEN_ALL ciw_eval_pred) >>
  gvs[]
QED

(* ================================================================
 * Transfer helpers for diff_preds dispatch.
 * These wrap ciw_maintain_mp_extend, proving all obligations for the
 * diff_preds case where new_pred = Var (ac_or_var h.inst_id) and
 * state changes from s to s'.
 * ================================================================ *)

(* Zero case: word_or = 0, chain continues with original pred_op/v *)
Triviality ciw_diff_preds_zero_transfer[local]:
  !cands h rest mp dfg s s' pred_op v mc inst_s mc_s.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    MEM mc cands /\
    (* State preservation *)
    (!op. IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op s')) /\
    ac_dfg_inv dfg s' /\
    eval_operand pred_op s' = SOME v /\
    IS_SOME (eval_operand (Var (ac_or_var h.inst_id)) s') /\
    (* Witness: mc_s.mc_first_id <> h.inst_id *)
    MEM inst_s rest /\
    FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
    mc_s.mc_first_id <> h.inst_id /\
    (case ALOOKUP mp mc_s.mc_first_id of
       SOME p => p | NONE => mc_s.mc_first_pred) = pred_op ==>
    ac_chain_inv_w cands rest
      ((h.inst_id, Var (ac_or_var h.inst_id))::mp) dfg s' pred_op v
Proof
  rpt strip_tac >>
  irule (GEN_ALL ciw_maintain_mp_extend) >>
  imp_res_tac FIND_P >> gvs[] >>
  rpt conj_tac
  (* G1: new_pred output clash *)
  >- metis_tac[ciw_output_no_oriz, MEM]
  (* G2: pred_op output *)
  >- metis_tac[ciw_pred_op_no_output, MEM]
  (* G3: new_pred or_var distinct: h.inst_id <> mc'.mc_second_id *)
  >- (rpt strip_tac >>
      imp_res_tac ciw_distinct_ids >> metis_tac[MEM])
  (* G4: pred_op or_iz fresh *)
  >- metis_tac[ciw_pred_op_no_oriz, MEM]
  (* G5: witness *)
  >- (qexistsl_tac [`inst_s`, `mc_s`] >> simp[ALOOKUP_def])
  (* G6: v <> 0w *)
  >- metis_tac[ciw_eval_pred]
  (* G7: old ciw *)
  >- metis_tac[]
QED

(* Nonzero case: chain continues with Var (ac_or_var h.inst_id) / word_or v1 v2 *)
Triviality ciw_diff_preds_nonzero_transfer[local]:
  !cands h rest mp dfg s s' pred_op v mc or_val inst_s mc_s.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    MEM mc cands /\
    EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands /\
    (* State preservation *)
    (!op. IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op s')) /\
    ac_dfg_inv dfg s' /\
    eval_operand (Var (ac_or_var h.inst_id)) s' = SOME or_val /\
    or_val <> 0w /\
    (* Witness: mc_s.mc_first_id = h.inst_id *)
    MEM inst_s rest /\
    FIND (\mc'. mc'.mc_second_id = inst_s.inst_id) cands = SOME mc_s /\
    mc_s.mc_first_id = h.inst_id ==>
    ac_chain_inv_w cands rest
      ((h.inst_id, Var (ac_or_var h.inst_id))::mp) dfg s'
      (Var (ac_or_var h.inst_id)) or_val
Proof
  rpt strip_tac >>
  irule (GEN_ALL ciw_maintain_mp_extend) >>
  imp_res_tac FIND_P >> gvs[] >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC)
  (* G1: new_pred output clash *)
  >- metis_tac[ciw_output_no_oriz, MEM]
  (* G2: new_pred=pred_op, output clash *)
  >- metis_tac[ciw_output_no_oriz, MEM]
  (* G3: new_pred or_var distinct *)
  >- (rpt strip_tac >>
      imp_res_tac ciw_distinct_ids >> metis_tac[MEM])
  (* G4: same as G3 with eq flipped *)
  >- (rpt strip_tac >>
      imp_res_tac ciw_distinct_ids >> metis_tac[MEM])
  (* G5: witness *)
  >- (qexistsl_tac [`inst_s`, `mc_s`] >> simp[ALOOKUP_def])
  (* G6: old ciw *)
  >- metis_tac[]
QED

Triviality ac_chain_step_w_diff_preds[local]:
  !h rest cands mp mc dfg fuel ctx s pred_op v.
    ac_chain_inv_w cands (h::rest) mp dfg s pred_op v /\
    FIND (\mc'. mc'.mc_second_id = h.inst_id) cands = SOME mc /\
    (case ALOOKUP mp mc.mc_first_id of
       NONE => mc.mc_first_pred | SOME p => p) <> mc.mc_second_pred /\
    (!i x. MEM i rest /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) rest)) ==>
    let (mp', contrib) = ac_apply_merge_step cands (mp, []) h in
    (?sa. run_insts fuel ctx contrib s = Abort Revert_abort sa /\
          execution_equiv UNIV (revert_state (set_returndata [] s)) sa) \/
    (?s' pred_op' v'. run_insts fuel ctx contrib s = OK s' /\
          execution_equiv UNIV (revert_state (set_returndata [] s))
                               (revert_state (set_returndata [] s')) /\
          ac_chain_inv_w cands rest mp' dfg s' pred_op' v' /\
          (!i x. MEM i rest /\ MEM x i.inst_outputs ==>
             ~IS_SOME (lookup_var x s')) /\
          ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) rest)))
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac FIND_P >> gvs[] >>
  qabbrev_tac `actual_fp = case ALOOKUP mp mc.mc_first_id of
                              NONE => mc.mc_first_pred | SOME p => p` >>
  simp[ac_apply_merge_step_def, LET_THM] >>
  (sg `MEM mc cands` >- metis_tac[FIND_MEM]) >>
  (sg `inst_wf h` >- (imp_res_tac ciw_every_wf >> fs[EVERY_DEF])) >>
  (sg `h.inst_opcode = ASSERT`
   >- (imp_res_tac (GEN_ALL ciw_merge_target_assert) >> metis_tac[MEM])) >>
  (sg `ac_dfg_inv dfg s` >- metis_tac[ciw_dfg_inv]) >>
  imp_res_tac (GEN_ALL ciw_eval_pred) >>
  (sg `IS_SOME (eval_operand actual_fp s)`
   >- (simp[Abbr `actual_fp`] >>
       Cases_on `ALOOKUP mp mc.mc_first_id` >> simp[]
       >- (fs[ac_chain_inv_w_def] >> metis_tac[FIND_MEM])
       >- (fs[ac_chain_inv_w_def] >> metis_tac[]))) >>
  (sg `IS_SOME (eval_operand mc.mc_second_pred s)`
   >- (fs[ac_chain_inv_w_def] >> metis_tac[FIND_MEM])) >>
  Cases_on `eval_operand actual_fp s` >>
  Cases_on `eval_operand mc.mc_second_pred s` >>
    gvs[optionTheory.IS_SOME_DEF] >>
  rename1 `eval_operand actual_fp s = SOME v1` >>
  rename1 `eval_operand mc.mc_second_pred s = SOME v2` >>
  qabbrev_tac `or_v = ac_or_var h.inst_id` >>
  qabbrev_tac `iz_v = ac_iz_var h.inst_id` >>
  qabbrev_tac `s_iz = update_var iz_v (bool_to_word (word_or v1 v2 = 0w))
                        (update_var or_v (word_or v1 v2) s)` >>
  (sg `or_v <> iz_v`
   >- simp[Abbr `or_v`, Abbr `iz_v`, ac_or_var_def, ac_iz_var_def]) >>
  qabbrev_tac `or_inst = instruction h.inst_id OR
    [actual_fp; mc.mc_second_pred] [or_v]` >>
  qabbrev_tac `iz_inst = instruction (h.inst_id + 1) ISZERO
    [Var or_v] [iz_v]` >>
  (sg `run_insts fuel ctx [or_inst; iz_inst] s = OK s_iz /\
   eval_operand (Var iz_v) s_iz =
     SOME (bool_to_word (word_or v1 v2 = 0w)) /\
   eval_operand (Var or_v) s_iz = SOME (word_or v1 v2) /\
   execution_equiv UNIV s s_iz /\
   (!opr. (!x. opr = Var x ==> x <> or_v /\ x <> iz_v) ==>
      eval_operand opr s_iz = eval_operand opr s)`
   >- (qspecl_then [`fuel`, `ctx`, `s`, `actual_fp`, `mc.mc_second_pred`,
                    `or_v`, `iz_v`, `h.inst_id`, `v1`, `v2`]
         mp_tac ac_or_iz_step >>
       simp[Abbr `or_inst`, Abbr `iz_inst`, Abbr `s_iz`, LET_THM])) >>
  (* Establish dfg freshness for or_v and iz_v *)
  (sg `dfg_get_def dfg or_v = NONE /\ dfg_get_def dfg iz_v = NONE`
   >- (simp[Abbr `or_v`, Abbr `iz_v`] >>
       fs[ac_chain_inv_w_def] >> metis_tac[])) >>
  (sg `(!di x. dfg_get_def dfg x = SOME di ==>
       ~MEM (Var or_v) di.inst_operands /\
       ~MEM (Var iz_v) di.inst_operands)`
   >- (simp[Abbr `or_v`, Abbr `iz_v`] >>
       fs[ac_chain_inv_w_def] >> metis_tac[])) >>
  (sg `ac_dfg_inv dfg s_iz`
   >- metis_tac[ac_dfg_inv_update_fresh]) >>
  (* State preservation: IS_SOME transfers from s to s_iz *)
  (sg `!op. IS_SOME (eval_operand op s) ==> IS_SOME (eval_operand op s_iz)`
   >- (simp[Abbr `s_iz`] >>
       metis_tac[eval_operand_update_var_is_some])) >>
  (* Pred_op eval transfers to s_iz (pred_op doesn't use or_v/iz_v) *)
  (sg `eval_operand pred_op s_iz = SOME v`
   >- (sg `!x. pred_op = Var x ==> x <> or_v /\ x <> iz_v`
       >- (simp[Abbr `or_v`, Abbr `iz_v`] >>
           metis_tac[ciw_pred_op_no_oriz, MEM]) >>
       metis_tac[])) >>
  (* No-redefine maintenance: rest outputs fresh in s_iz *)
  (Q.SUBGOAL_THEN `!i' x'. MEM i' rest /\ MEM x' i'.inst_outputs ==>
         ~IS_SOME (lookup_var x' s_iz)` ASSUME_TAC
   >- (rpt strip_tac >>
       (Q.SUBGOAL_THEN `x' <> or_v /\ x' <> iz_v` STRIP_ASSUME_TAC >-
         (simp[Abbr `or_v`, Abbr `iz_v`] >>
          mp_tac (Q.SPECL [`x'`, `v`, `s`, `pred_op`, `mp`, `mc`,
            `h::rest`, `i'`, `dfg`, `cands`] (GEN_ALL ciw_output_no_oriz)) >>
          simp[MEM])) >>
       PURE_REWRITE_TAC [optionTheory.NOT_IS_SOME_EQ_NONE] >>
       res_tac >>
       gvs[Abbr `s_iz`, update_var_def, lookup_var_def,
           finite_mapTheory.FLOOKUP_UPDATE])) >>
  (* Reduce the lambda-pair applied to the if-then-else *)
  simp[COND_RAND, COND_RATOR, pairTheory.LAMBDA_PROD,
       Abbr `or_inst`, Abbr `iz_inst`, run_insts_append] >>
  RULE_ASSUM_TAC (REWRITE_RULE [instruction_to_literal]) >>
  simp[run_insts_three] >>
  Cases_on `EXISTS (\mc'. mc'.mc_first_id = h.inst_id) cands` >>
  simp[Abbr `or_v`] >>
  Cases_on `word_or v1 v2 = 0w`
  (* Now 4 subgoals:
     G1: fid + zero   G2: fid + nonzero   G3: ~fid + zero   G4: ~fid + nonzero *)
  (* G1: fid + zero => NOP OK, chain continues with pred_op *)
  >- (
    DISJ2_TAC >>
    simp[Once run_insts_def, step_nop_identity, Once run_insts_def] >>
    (Q.SUBGOAL_THEN `v1 = 0w /\ v2 = 0w` STRIP_ASSUME_TAC >-
      metis_tac[word_or_eq_0w]) >>
    qunabbrev_tac `actual_fp` >>
    drule_all ciw_diff_preds_zero_witness >> strip_tac >>
    qexistsl_tac [`pred_op`, `v`] >>
    (conj_tac >- (irule revert_returndata_exec_equiv_UNIV >> simp[])) >>
    conj_tac >- (irule (GEN_ALL ciw_diff_preds_zero_transfer) >>
      simp[optionTheory.IS_SOME_DEF] >> metis_tac[FIND_MEM]) >>
    rpt strip_tac >> res_tac >>
    gvs[optionTheory.NOT_IS_SOME_EQ_NONE]
  )
  (* G2: fid + nonzero => NOP OK, chain continues with Var or_v *)
  >- (
    DISJ2_TAC >>
    simp[Once run_insts_def, step_nop_identity, Once run_insts_def] >>
    drule_all ciw_diff_preds_downstream_witness >> strip_tac >>
    qexistsl_tac [`Var (ac_or_var h.inst_id)`, `word_or v1 v2`] >>
    (conj_tac >- (irule revert_returndata_exec_equiv_UNIV >> simp[])) >>
    conj_tac >- (irule (GEN_ALL ciw_diff_preds_nonzero_transfer) >>
      simp[] >> metis_tac[FIND_MEM]) >>
    rpt strip_tac >> res_tac >>
    gvs[optionTheory.NOT_IS_SOME_EQ_NONE]
  )
  (* G3: ~fid + zero => ASSERT OK (iz=1w, s'=s_iz), chain continues *)
  >- (
    DISJ2_TAC >>
    (Q.SUBGOAL_THEN `bool_to_word (v1 || v2 = 0w) = 1w` ASSUME_TAC >-
      simp[bool_to_word_def]) >>
    (Q.SUBGOAL_THEN `step_inst fuel ctx (h with inst_operands := [Var iz_v]) s_iz = OK s_iz`
      ASSUME_TAC >-
      (match_mp_tac step_assert_ok >>
       qexistsl_tac [`Var iz_v`, `1w`] >> simp[])) >>
    simp[Once run_insts_def, Once run_insts_def] >>
    (Q.SUBGOAL_THEN `v1 = 0w /\ v2 = 0w` STRIP_ASSUME_TAC >-
      metis_tac[word_or_eq_0w]) >>
    qunabbrev_tac `actual_fp` >>
    drule_all ciw_diff_preds_zero_witness >> strip_tac >>
    qexistsl_tac [`pred_op`, `v`] >>
    (conj_tac >- (irule revert_returndata_exec_equiv_UNIV >> simp[])) >>
    conj_tac >- (irule (GEN_ALL ciw_diff_preds_zero_transfer) >>
      simp[optionTheory.IS_SOME_DEF] >> metis_tac[FIND_MEM]) >>
    rpt strip_tac >> res_tac >>
    gvs[optionTheory.NOT_IS_SOME_EQ_NONE]
  )
  (* G4: ~fid + nonzero => ASSERT aborts (iz=0w) *)
  >- (
    DISJ1_TAC >>
    (Q.SUBGOAL_THEN `bool_to_word (v1 || v2 = 0w) = 0w` ASSUME_TAC >-
      simp[bool_to_word_def]) >>
    (Q.SUBGOAL_THEN `step_inst fuel ctx (h with inst_operands := [Var iz_v]) s_iz =
          Abort Revert_abort (revert_state (set_returndata [] s_iz))`
      ASSUME_TAC >-
      (match_mp_tac step_assert_abort >>
       qexistsl_tac [`Var iz_v`] >> simp[])) >>
    simp[Once run_insts_def] >>
    irule revert_returndata_exec_equiv_UNIV >> simp[]
  )
QED

Resume ac_chain_step_w[find_some]:
  rename1 `FIND _ _ = SOME mc` >>
  Cases_on `(case ALOOKUP mp mc.mc_first_id of
               NONE => mc.mc_first_pred | SOME p => p) = mc.mc_second_pred`
  >- (irule (GEN_ALL ac_chain_step_w_same_preds) >> metis_tac[MEM])
  >- (irule (GEN_ALL ac_chain_step_w_diff_preds) >> metis_tac[MEM])
QED

Finalise ac_chain_step_w;

(* Weak chain abort: the FOLDL output aborts *)
Theorem ac_deferred_chain_abort_w:
  !insts cands mp dfg fuel ctx s pred_op v.
    ac_chain_inv_w cands insts mp dfg s pred_op v /\
    (!i x. MEM i insts /\ MEM x i.inst_outputs ==>
       ~IS_SOME (lookup_var x s)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) ==>
    ?sa. run_insts fuel ctx
           (SND (FOLDL (ac_apply_merge_step cands) (mp, []) insts)) s =
         Abort Revert_abort sa /\
         execution_equiv UNIV (revert_state (set_returndata [] s)) sa
Proof
  Induct >- simp[ac_chain_inv_w_def] >>
  rpt strip_tac >>
  qspecl_then [`h`, `insts`, `cands`, `mp`, `dfg`, `fuel`, `ctx`,
               `s`, `pred_op`, `v`] mp_tac ac_chain_step_w >>
  simp[] >> (impl_tac >- (rpt strip_tac >> res_tac >>
    gvs[optionTheory.NOT_IS_SOME_EQ_NONE])) >> simp[LET_THM] >>
  Cases_on `ac_apply_merge_step cands (mp,[]) h` >>
  simp[] >> strip_tac
  >- (
    (* Abort case: run_insts on r already aborts *)
    qspecl_then [`h`, `insts`, `cands`, `mp`] mp_tac ac_foldl_cons >>
    simp[LET_THM] >> strip_tac >> simp[run_insts_append] >>
    metis_tac[]
  )
  >- (
    (* OK case: run_insts on r succeeds, use IH on tail *)
    qspecl_then [`h`, `insts`, `cands`, `mp`] mp_tac ac_foldl_cons >>
    simp[LET_THM] >> strip_tac >> simp[run_insts_append] >>
    first_x_assum drule >>
    (impl_tac >- (
      conj_tac >- (rpt strip_tac >> res_tac >> gvs[]) >>
      first_assum ACCEPT_TAC)) >>
    strip_tac >>
    metis_tac[execution_equiv_trans]
  )
QED
