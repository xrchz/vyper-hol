(*
 * Expression Lowering Properties
 *
 * TOP-LEVEL:
 *   run_inst_seq             — run instruction sequence on Venom state
 *   emitted_insts            — extract new instructions from compile state
 *   compile_expr_correct     — main expression lowering correctness
 *   compile_literal_vv_correct  — word literal case
 *   compile_name_correct     — variable lookup case
 *   compile_binop_correct    — binary operation case
 *
 * Helper:
 *
 * Mirrors correctness of: exprLoweringScript.sml (compile_expr)
 * Source semantics: vyperInterpreterScript.sml (eval_expr)
 * Target semantics: venomExecSemanticsScript.sml (step_inst_base)
 *)

Theory exprLoweringProps
Ancestors
  exprLowering emitHelper compileEnv
  venomExecSemantics venomState venomInst venomInstProps
  vyperInterpreter vyperContext
  vyperState vyperValueOperation
  valueEncoding valueEncodingProofs
  vyperAST vyperTyping
Libs
  pairLib BasicProvers

(* ===== Instruction Sequence Execution ===== *)

(* Run a list of instructions sequentially via step_inst_base.
   Returns OK if all succeed, or the first non-OK result. *)
Definition run_inst_seq_def:
  run_inst_seq [] ss = OK ss ∧
  run_inst_seq (i::is) ss =
    case step_inst_base i ss of
      OK ss' => run_inst_seq is ss'
    | other => other
End

(* ===== Compile State Helpers ===== *)

(* Instructions emitted between two compile states (within same block) *)
Definition emitted_insts_def:
  emitted_insts (st:compile_state) (st':compile_state) =
    DROP (LENGTH st.cs_current_insts) st'.cs_current_insts
End

(* No new blocks were created *)
Definition same_blocks_def:
  same_blocks (st:compile_state) (st':compile_state) ⇔
    st'.cs_blocks = st.cs_blocks ∧
    st'.cs_current_bb = st.cs_current_bb
End

(* ===== Main Correctness Theorem ===== *)

(* For a "simple" (single-block) expression:
   - The emitted instructions run successfully on the Venom state
   - The returned operand evaluates to the encoded Vyper value
   - State relation is preserved

   NOTE: This covers Literal, Name, BinOp, Compare, UnaryOp, Env vars.
   IfExp (multi-block) needs a separate theorem using run_block. *)
(* Supported expressions: single-block compilation forms.
   Handles: Literal, Name, Env vars, Not, Neg, BinOp.
   IfExp is multi-block (separate theorem needed).
   Other forms are not yet implemented in compile_expr. *)
Definition supported_expr_def:
  supported_expr (Literal _ _) = T ∧
  supported_expr (Name _ _) = T ∧
  supported_expr (Builtin _ (Env _) _) = T ∧
  supported_expr (Builtin _ Not (e::_)) = supported_expr e ∧
  supported_expr (Builtin _ Neg (e::_)) = supported_expr e ∧
  supported_expr (Builtin _ (Bop _) (e1::e2::_)) =
    (supported_expr e1 ∧ supported_expr e2) ∧
  supported_expr _ = F
End

(* well_annotated: annotation types in the AST agree with operand types
   where the evaluator uses them for bounds checking.
   - BoolV Not: evaluator ignores annotation, compiler dispatches on expr_type
   - IntV Not: evaluator uses type_to_int_bound ann for bounds
   - Neg: evaluator uses type_to_int_bound ann for bounds
   - BinOp: evaluator uses type_to_int_bound ann for arithmetic bounds;
     for comparisons type_to_int_bound ann = NONE (vacuously true). *)
Definition well_annotated_def:
  well_annotated (Literal ann l) = T ∧
  well_annotated (Name ann id) = T ∧
  well_annotated (Builtin ann (Env item) args) = T ∧
  well_annotated (Builtin ann Not (e::rest)) =
    ((expr_type e ≠ BaseT BoolT ⇒
      type_to_int_bound ann = type_to_int_bound (expr_type e)) ∧
     well_annotated e) ∧
  well_annotated (Builtin ann Neg (e::rest)) =
    (type_to_int_bound ann = type_to_int_bound (expr_type e) ∧
     well_annotated e) ∧
  well_annotated (Builtin ann (Bop bop) (e1::e2::rest)) =
    ((∀u. type_to_int_bound ann = SOME u ⇒
          type_to_int_bound (expr_type e1) = SOME u) ∧
     well_annotated e1 ∧ well_annotated e2) ∧
  well_annotated _ = T
End

Theorem compile_expr_correct:
  ∀ cenv cx ty e es ss st op st' v es'.
    state_rel cenv cx es ss ∧
    fresh_vars_wrt st ss ∧
    supported_expr e ∧
    well_annotated e ∧
    eval_expr cx e es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty e st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      state_rel cenv cx es' ss' ∧
      same_blocks st st' ∧
      st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
      ¬ss'.vs_halted ∧
      EVERY (λi. ¬is_terminator i.inst_opcode ∧ i.inst_opcode ≠ INVOKE)
        (emitted_insts st st') ∧
      fresh_vars_wrt st' ss' ∧
      (∀ op w. eval_operand op ss = SOME w ⇒ eval_operand op ss' = SOME w)
Proof
  cheat
QED

(* ===== Infrastructure Lemmas ===== *)

(* Helper: if xs = ys ++ zs then DROP (LENGTH ys) xs = zs *)
Theorem DROP_PREFIX:
  ∀ ys zs. DROP (LENGTH ys) (ys ++ zs) = zs
Proof
  Induct >> simp[]
QED

(* run_inst_seq concatenation: OK prefix *)
Theorem run_inst_seq_append:
  ∀ is1 is2 ss ss'.
    run_inst_seq is1 ss = OK ss' ⇒
    run_inst_seq (is1 ++ is2) ss = run_inst_seq is2 ss'
Proof
  Induct_on `is1` >> rw[run_inst_seq_def, comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `step_inst_base h ss` >> gvs[]
QED

(* run_inst_seq concatenation: non-OK prefix *)
Theorem run_inst_seq_append_err:
  ∀ is1 is2 ss.
    (∀s. run_inst_seq is1 ss ≠ OK s) ⇒
    run_inst_seq (is1 ++ is2) ss = run_inst_seq is1 ss
Proof
  Induct_on `is1` >> rw[run_inst_seq_def, comp_return_def, comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `step_inst_base h ss` >> gvs[]
QED

(* emit_op emits exactly one instruction and returns Var of the fresh output *)
Theorem emitted_insts_emit_op_local:
  ∀ opc ops st v st'.
    emit_op opc ops st = (v, st') ⇒
    emitted_insts st st' =
      [mk_inst st.cs_next_id opc ops
               [STRING #"%" (toString st.cs_next_var)]] ∧
    v = Var (STRING #"%" (toString st.cs_next_var)) ∧
    st'.cs_next_id = st.cs_next_id + 1 ∧
    st'.cs_next_var = st.cs_next_var + 1 ∧
    st'.cs_current_insts = st.cs_current_insts ++
      [mk_inst st.cs_next_id opc ops
               [STRING #"%" (toString st.cs_next_var)]]
Proof
  rw[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
     comp_ignore_bind_def, comp_return_def, emit_def, emitted_insts_def] >>
  gvs[rich_listTheory.DROP_LENGTH_APPEND]
QED

(* emit_op extends instructions: appends exactly one instruction *)
Theorem emit_op_extends:
  ∀ opc ops st v st'.
    emit_op opc ops st = (v, st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def]
  >> simp[emitted_insts_def, same_blocks_def,
          rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_LENGTH_NIL, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* emit_void extends instructions: appends exactly one instruction *)
Theorem emit_void_extends:
  ∀ opc ops st st'.
    emit_void opc ops st = ((), st') ⇒
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' ∧
    same_blocks st st'
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[emitted_insts_def, same_blocks_def,
          rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_LENGTH_NIL, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* emitted_insts composition through intermediate state *)
Theorem emitted_insts_append:
  ∀ st st1 st2.
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st2.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st2
    ⇒
    emitted_insts st st2 =
      emitted_insts st st1 ++ emitted_insts st1 st2
Proof
  rw[emitted_insts_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> pop_assum (fn th => SUBST_ALL_TAC th)
  >> pop_assum (fn th =>
       `LENGTH st.cs_current_insts ≤ LENGTH st1.cs_current_insts` by
         (SUBST1_TAC th >> simp[]) >>
       assume_tac th)
  >> simp[rich_listTheory.DROP_APPEND1, DROP_PREFIX]
QED

(* Chain run_inst_seq across two instruction-emitting steps.
   Also produces the accumulated cs_current_insts fact for further chaining.
   Replaces the manual emitted_insts_append + run_inst_seq_append pattern. *)
Theorem run_inst_seq_chain:
  ∀ st st1 st' ss ss1.
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st'.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st' ∧
    run_inst_seq (emitted_insts st st1) ss = OK ss1
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      run_inst_seq (emitted_insts st1 st') ss1 ∧
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rw[]
  >- (`emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
        by (irule emitted_insts_append >> gvs[]) >>
      gvs[] >> irule run_inst_seq_append >> gvs[])
  >> `emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
       by (irule emitted_insts_append >> gvs[]) >>
     gvs[]
QED

(* Error version of run_inst_seq_chain: if prefix errors, total also errors.
   Also produces the accumulated cs_current_insts fact. *)
Theorem run_inst_seq_chain_err:
  ∀ st st1 st' ss.
    st1.cs_current_insts = st.cs_current_insts ++ emitted_insts st st1 ∧
    st'.cs_current_insts = st1.cs_current_insts ++ emitted_insts st1 st' ∧
    (∀s. run_inst_seq (emitted_insts st st1) ss ≠ OK s)
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      run_inst_seq (emitted_insts st st1) ss ∧
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st'
Proof
  rw[]
  >- (`emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
        by (irule emitted_insts_append >> gvs[]) >>
      gvs[] >> irule run_inst_seq_append_err >> gvs[])
  >> `emitted_insts st st' = emitted_insts st st1 ++ emitted_insts st1 st'`
       by (irule emitted_insts_append >> gvs[]) >>
     gvs[]
QED

(* ===== Utility Lemmas (local, avoid emitHelperProps dependency) ===== *)

(* eval_operand for a Var just written by update_var *)
Theorem eval_operand_update_var_local:
  !x w ss. eval_operand (Var x) (update_var x w ss) = SOME w
Proof
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* eval_operand for a Lit is always SOME *)
Theorem eval_operand_lit_local:
  !w ss. eval_operand (Lit w) ss = SOME w
Proof
  simp[eval_operand_def]
QED

(* state_rel is preserved by update_var (only changes vs_vars) *)
Theorem state_rel_update_var_local:
  !cenv cx es ss name w.
    state_rel cenv cx es ss ==> state_rel cenv cx es (update_var name w ss)
Proof
  rw[state_rel_def, update_var_def, vars_rel_def, storage_rel_def,
     transient_rel_def, immutables_rel_def, logs_rel_def, call_ctx_rel_def,
     contract_storage_def, contract_transient_def]
QED

(* step_inst_base for MLOAD: reads 32 bytes from memory *)
Theorem step_MLOAD_local:
  !op1 out id ss v.
    eval_operand op1 ss = SOME v ==>
    step_inst_base (mk_inst id MLOAD [op1] [out]) ss =
      OK (update_var out (mload (w2n v) ss) ss)
Proof
  rw[step_inst_base_def, venomInstTheory.mk_inst_def,
     comp_return_def, comp_bind_def, comp_ignore_bind_def,
     mload_def, update_var_def, LET_THM, exec_read1_def]
QED

(* eval_operand preserved by update_var on a different variable *)
Theorem eval_operand_update_other_local:
  !op ss name w v.
    eval_operand op ss = SOME v /\
    (!x. op = Var x ==> x <> name) ==>
    eval_operand op (update_var name w ss) = SOME v
Proof
  Cases_on `op` >>
  simp[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

(* ===== Per-Expression Lemmas ===== *)

(* --- Literal --- *)
(* Covers word-type literals only. Bytestring/string literals allocate buffers. *)
Theorem compile_literal_vv_correct:
  ∀ cenv cx ty l es ss st vv st'.
    state_rel cenv cx es ss ∧
    compile_literal_vv ty l st = (vv, st') ∧
    (* Word literals only — dynamic bytes/strings allocate buffers *)
    (* Word literals only — exclude bytestring/string types that allocate buffers *)
    (∀ bs. l = BytesL bs ⇒ ∃ m. ty = BaseT (BytesT (Fixed m))) ∧
    (∀ s. l ≠ StringL s)
    ⇒
    emitted_insts st st' = [] ∧
    same_blocks st st'
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `l`
  >- (Cases_on `b` >>
      gvs[compile_literal_vv_def, comp_return_def,
          emitted_insts_def, same_blocks_def, listTheory.DROP_LENGTH_NIL])
  >- gvs[]
  >- (res_tac >>
      gvs[compile_literal_vv_def, comp_return_def,
          emitted_insts_def, same_blocks_def, listTheory.DROP_LENGTH_NIL])
  >- gvs[compile_literal_vv_def, comp_return_def,
         emitted_insts_def, same_blocks_def, listTheory.DROP_LENGTH_NIL]
  >> gvs[compile_literal_vv_def, comp_return_def,
         emitted_insts_def, same_blocks_def, listTheory.DROP_LENGTH_NIL]
QED

(* --- Name (local variable load) --- *)
(* v must be a primitive (word-sized) value,
   and offset must fit in a word (offset < dimword(:256)).
   Uses typed_val_to_w256 (not val_to_w256) to avoid BytesV address heuristic.
   The type_value tv from the scope correctly distinguishes address from bytesN. *)
(* NOTE: original statement was FALSE for v = NoneV and for
   type/value mismatches like entry.type=BaseTV BoolT with v=BytesV [1w]
   (ruled out by value_has_type). val_in_memory (BaseTV (UintT n)) NoneV
   offset mem = T (vacuously true) but mload offset ss is unconstrained,
   while typed_val_to_w256 NoneV = 0w.
   Fix: added v ≠ NoneV and value_has_type entry.type v. *)
Theorem compile_name_correct:
  ∀ cenv cx ty ann id es ss st op st' v es' offset size entry.
    state_rel cenv cx es ss ∧
    eval_expr cx (Name ann id) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Name ann id) st = (op, st') ∧
    FLOOKUP cenv.ce_vars id = SOME (MemLoc offset size) ∧
    offset < dimword (:256) ∧
    lookup_scopes (string_to_num id) es.scopes = SOME entry ∧
    entry.value = v ∧
    v ≠ NoneV ∧
    value_has_type entry.type v ∧
    (∃ bt. entry.type = BaseTV bt ∧ is_word_type (BaseT bt))
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (typed_val_to_w256 entry.type v) ∧
      es' = es ∧
      same_blocks st st'
Proof
  cheat
QED

(* --- BinOp (safe arithmetic) --- *)
(* For compile_binop: the emitted instructions compute the correct
   result and any overflow checks correctly abort on invalid inputs *)
(* NOTE: original statement was FALSE when annotation type has different
   bounds than expr_type e1. Evaluator uses type_to_int_bound ann for
   bounds checking, compiler uses type_bounds(expr_type e1).
   Fix: added type consistency + fresh_vars_wrt + named annotation. *)
Theorem compile_binop_correct:
  ∀ cenv cx ty ann bop e1 e2 es ss st op st' v es'.
    state_rel cenv cx es ss ∧
    fresh_vars_wrt st ss ∧
    (∀u. type_to_int_bound ann = SOME u ⇒
         type_to_int_bound (expr_type e1) = SOME u) ∧
    eval_expr cx (Builtin ann (Bop bop) [e1; e2]) es = (INL (Value v), es') ∧
    lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1; e2]) st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- Not (boolean negation) --- *)
(* The ISZERO instruction correctly computes boolean NOT.
   Sub-expression correctness is handled by the main induction. *)
Theorem iszero_bool_correct:
  ∀ op b ss inst_id out_var.
    eval_operand op ss = SOME (val_to_w256 (BoolV b)) ⇒
    step_inst_base (mk_inst inst_id ISZERO [op] [out_var]) ss =
      OK (update_var out_var (val_to_w256 (BoolV (¬b))) ss)
Proof
  Cases_on `b` >> rpt strip_tac >>
  `(mk_inst inst_id ISZERO [op] [out_var]).inst_opcode = ISZERO`
    by simp[venomInstTheory.mk_inst_def] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pop_assum (fn th => PURE_REWRITE_TAC[th]) >>
  simp[exec_pure1_def, venomInstTheory.mk_inst_def, val_to_w256_def,
       venomExecSemanticsTheory.bool_to_word_def]
QED

(* ASSERT instruction: non-zero → OK (no-op), zero → Abort *)
Theorem assert_true_correct:
  ∀ op v ss inst_id.
    eval_operand op ss = SOME v ∧ v ≠ 0w ⇒
    step_inst_base (mk_inst inst_id ASSERT [op] []) ss = OK ss
Proof
  simp[step_inst_base_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

Theorem assert_false_correct:
  ∀ op ss inst_id.
    eval_operand op ss = SOME 0w ⇒
    step_inst_base (mk_inst inst_id ASSERT [op] []) ss =
      Abort Revert_abort (revert_state (set_returndata [] ss))
Proof
  simp[step_inst_base_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* emit_void ASSERT: emits one ASSERT instruction *)
Theorem emit_void_assert_inst:
  ∀ op st.
    emit_void ASSERT [op] st =
      ((), st with <| cs_next_id := st.cs_next_id + 1;
                       cs_current_insts := st.cs_current_insts ++
                         [mk_inst st.cs_next_id ASSERT [op] []] |>)
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       emit_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* NOTE: original statement was FALSE when annotation type has different
   bounds than expr_type e. Compiler uses type_bounds(expr_type e) but
   evaluator uses type_to_int_bound(annotation type). Additionally, Neg
   is only defined for signed integers — unsigned annotation (e.g.
   UintT 256 with IntV 0) gave a spurious counterexample.
   Fix: named annotation, added type_to_int_bound constraint, and
   restricted ann to signed IntT. *)
Theorem compile_neg_correct:
  ∀ cenv cx ty ann e es ss st op st' v es' n.
    state_rel cenv cx es ss ∧
    eval_expr cx (Builtin ann Neg [e]) es = (INL (Value v), es') ∧
    ann = BaseT (IntT n) ∧
    type_to_int_bound ann = type_to_int_bound (expr_type e) ∧
    lower_value compile_expr cenv ty (Builtin ann Neg [e]) st = (op, st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      eval_operand op ss' = SOME (val_to_w256 v) ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- Environment variables (CALLER, TIMESTAMP, etc.) --- *)

(* ===== Prefix / same_blocks Infrastructure ===== *)

(* isPREFIX ↔ append-DROP identity *)
Theorem prefix_drop_equiv:
  !xs (l:'a list). isPREFIX xs l <=> (l = xs ++ DROP (LENGTH xs) l)
Proof
  rw[rich_listTheory.IS_PREFIX_APPEND, EQ_IMP_THM]
  >- simp[rich_listTheory.DROP_LENGTH_APPEND]
  >> qexists_tac `DROP (LENGTH xs) l` >> simp[]
QED

(* same_blocks: reflexive, symmetric, transitive *)
Theorem same_blocks_refl:
  same_blocks st st
Proof
  simp[same_blocks_def]
QED

Theorem same_blocks_sym:
  same_blocks st st1 ==> same_blocks st1 st
Proof
  simp[same_blocks_def]
QED

Theorem same_blocks_trans:
  same_blocks st st1 /\ same_blocks st1 st2 ==> same_blocks st st2
Proof
  simp[same_blocks_def]
QED

(* emit_op / emit_void / emit_inst: prefix + same_blocks *)
Theorem emit_op_prefix:
  !opc ops st v st'.
    emit_op opc ops st = (v, st') ==>
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem emit_op_same_blocks:
  !opc ops st v st'.
    emit_op opc ops st = (v, st') ==> same_blocks st st'
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def] >>
  simp[same_blocks_def]
QED

Theorem emit_void_prefix:
  !opc ops st v st'.
    emit_void opc ops st = (v, st') ==>
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem emit_void_same_blocks:
  !opc ops st v st'.
    emit_void opc ops st = (v, st') ==> same_blocks st st'
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def] >>
  simp[same_blocks_def]
QED

(* compile_ptr_load: all cases are emit_op *)
Theorem compile_ptr_load_prefix:
  !is_ctor loc op st v st'.
    compile_ptr_load is_ctor loc op st = (v, st') ==>
    isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  Cases_on `loc` >>
  simp[contextTheory.compile_ptr_load_def] >>
  rw[] >> imp_res_tac emit_op_prefix
QED

Theorem compile_ptr_load_same_blocks:
  !is_ctor loc op st v st'.
    compile_ptr_load is_ctor loc op st = (v, st') ==>
    same_blocks st st'
Proof
  Cases_on `loc` >>
  simp[contextTheory.compile_ptr_load_def] >>
  rw[] >> imp_res_tac emit_op_same_blocks
QED

(* new_block: always breaks same_blocks *)
Theorem new_block_breaks_same_blocks:
  ~same_blocks st (SND (new_block label st))
Proof
  simp[new_block_def, same_blocks_def, LET_THM]
QED

(* run_inst_seq nil *)
Theorem run_inst_seq_nil:
  run_inst_seq [] ss = OK ss
Proof
  simp[run_inst_seq_def]
QED

(* emitted_insts reflexive *)
Theorem emitted_insts_refl:
  emitted_insts st st = []
Proof
  simp[emitted_insts_def]
QED

(* ===== isPREFIX Composition Toolkit ===== *)

(* Monad composition preserves isPREFIX on cs_current_insts *)
Theorem comp_bind_isPREFIX:
  !(mf : compile_state -> 'a # compile_state)
   (mg : 'a -> compile_state -> 'b # compile_state) s0 bval s2.
    comp_bind mf mg s0 = (bval, s2) /\
    (!sa av sb. mf sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts) /\
    (!av sa bv sb. mg av sa = (bv, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts)
    ==>
    isPREFIX s0.cs_current_insts s2.cs_current_insts
Proof
  rw[comp_bind_def, pairTheory.UNCURRY] >>
  `?av s1. mf s0 = (av, s1)` by metis_tac[pairTheory.PAIR] >>
  gvs[] >>
  irule rich_listTheory.IS_PREFIX_TRANS >>
  qexists_tac `s1.cs_current_insts` >>
  metis_tac[]
QED

Theorem comp_ignore_bind_isPREFIX:
  !(mf : compile_state -> 'a # compile_state)
   (mg : compile_state -> 'b # compile_state) s0 bval s2.
    comp_ignore_bind mf mg s0 = (bval, s2) /\
    (!sa av sb. mf sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts) /\
    (!sa bv sb. mg sa = (bv, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts)
    ==>
    isPREFIX s0.cs_current_insts s2.cs_current_insts
Proof
  rw[comp_ignore_bind_def, comp_bind_def, pairTheory.UNCURRY] >>
  `?av s1. mf s0 = (av, s1)` by metis_tac[pairTheory.PAIR] >>
  gvs[] >>
  irule rich_listTheory.IS_PREFIX_TRANS >>
  qexists_tac `s1.cs_current_insts` >>
  metis_tac[]
QED

(* Primitive isPREFIX lemmas *)
Theorem comp_return_isPREFIX[local]:
  !x sa av sb. comp_return x sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[comp_return_def]
QED

Theorem emit_isPREFIX[local]:
  !inst sa av sb. emit inst sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[emit_def] >> simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem fresh_var_ci_eq[local]:
  !sa av sb. fresh_var sa = (av, sb) ==> sa.cs_current_insts = sb.cs_current_insts
Proof
  rw[fresh_var_def] >> simp[]
QED

Theorem fresh_id_ci_eq[local]:
  !sa av sb. fresh_id sa = (av, sb) ==> sa.cs_current_insts = sb.cs_current_insts
Proof
  rw[fresh_id_def] >> simp[]
QED

Theorem fresh_label_ci_eq[local]:
  !pfx sa av sb. fresh_label pfx sa = (av, sb) ==> sa.cs_current_insts = sb.cs_current_insts
Proof
  rw[fresh_label_def] >> simp[]
QED

Theorem emit_op_isPREFIX[local]:
  !opc ops sa av sb. emit_op opc ops sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def, pairTheory.UNCURRY] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem emit_void_isPREFIX[local]:
  !opc ops sa av sb. emit_void opc ops sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def, pairTheory.UNCURRY] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem emit_inst_isPREFIX[local]:
  !opc ops outs sa av sb. emit_inst opc ops outs sa = (av, sb) ==> isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  rw[emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
     emit_def, comp_return_def, venomInstTheory.mk_inst_def, pairTheory.UNCURRY] >>
  simp[rich_listTheory.IS_PREFIX_APPEND3]
QED

(* new_block changes cs_blocks (needed for vacuous cases) *)
Theorem new_block_changes_blocks[local]:
  !label st. (SND (new_block label st)).cs_blocks <> st.cs_blocks
Proof
  rw[new_block_def, LET_THM]
QED

(* ===== ci_mono: Compile monad monotonicity ===== *)

(* ci_mono st st' holds when the compile state transition from st to st'
   either (1) appends to cs_current_insts without changing cs_blocks, or
   (2) cs_blocks grew (meaning new_block was called, which resets ci).
   This is the key invariant for all compile monad operations. *)
Definition ci_mono_def:
  ci_mono (st:compile_state) (st':compile_state) ⇔
    (isPREFIX st.cs_current_insts st'.cs_current_insts ∧
     st'.cs_blocks = st.cs_blocks) ∨
    LENGTH st'.cs_blocks > LENGTH st.cs_blocks
End

Theorem ci_mono_refl[local]:
  ci_mono st st
Proof
  simp[ci_mono_def]
QED

Theorem ci_mono_trans[local]:
  ci_mono a b ∧ ci_mono b c ⇒ ci_mono a c
Proof
  simp[ci_mono_def] >> rpt strip_tac >> gvs[] >>
  irule rich_listTheory.IS_PREFIX_TRANS >>
  qexists `b.cs_current_insts` >> simp[]
QED

(* ci_mono composes through monad_bind (= comp_bind) *)
Theorem ci_mono_bind[local]:
  ∀ (mf : compile_state -> 'a # compile_state)
    (mg : 'a -> compile_state -> 'b # compile_state) s0.
    (∀ sa. ci_mono sa (SND (mf sa))) ∧
    (∀ av sa. ci_mono sa (SND (mg av sa)))
    ⇒
    ci_mono s0 (SND (comp_bind mf mg s0))
Proof
  rw[comp_bind_def, pairTheory.UNCURRY] >>
  Cases_on `mf s0` >> gvs[] >>
  irule ci_mono_trans >>
  qexists `r` >> conj_tac
  >- (first_x_assum (qspec_then `s0` mp_tac) >> simp[])
  >> first_x_assum (qspecl_then [`q`, `r`] mp_tac) >> simp[]
QED

(* ci_mono composes through comp_ignore_bind *)
Theorem ci_mono_ignore_bind[local]:
  ∀ (mf : compile_state -> 'a # compile_state)
    (mg : compile_state -> 'b # compile_state) s0.
    (∀ sa. ci_mono sa (SND (mf sa))) ∧
    (∀ sa. ci_mono sa (SND (mg sa)))
    ⇒
    ci_mono s0 (SND (comp_ignore_bind mf mg s0))
Proof
  rw[comp_ignore_bind_def, comp_bind_def, pairTheory.UNCURRY] >>
  Cases_on `mf s0` >> gvs[] >>
  irule ci_mono_trans >>
  qexists `r` >> conj_tac
  >- (qpat_x_assum `!sa. ci_mono sa (SND (mf sa))` (qspec_then `s0` mp_tac) >> simp[])
  >> qpat_x_assum `!sa. ci_mono sa (SND (mg sa))` (qspec_then `r` mp_tac) >> simp[]
QED

(* ci_mono + same_blocks → isPREFIX *)
Theorem ci_mono_same_blocks_isPREFIX[local]:
  ci_mono st st' ∧ same_blocks st st' ⇒
  isPREFIX st.cs_current_insts st'.cs_current_insts
Proof
  rw[ci_mono_def, same_blocks_def] >> gvs[]
QED

(* ci_mono for primitives *)
Theorem ci_mono_comp_return[local]:
  ∀ x sa. ci_mono sa (SND (comp_return x sa))
Proof
  simp[comp_return_def, ci_mono_def]
QED

Theorem ci_mono_emit[local]:
  ∀ inst sa. ci_mono sa (SND (emit inst sa))
Proof
  simp[emit_def, ci_mono_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem ci_mono_fresh_var[local]:
  ∀ sa. ci_mono sa (SND (fresh_var sa))
Proof
  simp[fresh_var_def, ci_mono_def]
QED

Theorem ci_mono_fresh_id[local]:
  ∀ sa. ci_mono sa (SND (fresh_id sa))
Proof
  simp[fresh_id_def, ci_mono_def]
QED

Theorem ci_mono_fresh_label[local]:
  ∀ pfx sa. ci_mono sa (SND (fresh_label pfx sa))
Proof
  simp[fresh_label_def, ci_mono_def]
QED

Theorem ci_mono_new_block[local]:
  ∀ label sa. ci_mono sa (SND (new_block label sa))
Proof
  simp[new_block_def, LET_THM, ci_mono_def]
QED

Theorem ci_mono_emit_op[local]:
  ∀ opc ops sa. ci_mono sa (SND (emit_op opc ops sa))
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, fresh_var_def, emit_def, comp_return_def,
       venomInstTheory.mk_inst_def, pairTheory.UNCURRY,
       ci_mono_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem ci_mono_emit_void[local]:
  ∀ opc ops sa. ci_mono sa (SND (emit_void opc ops sa))
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def,
       venomInstTheory.mk_inst_def, pairTheory.UNCURRY,
       ci_mono_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

Theorem ci_mono_emit_inst[local]:
  ∀ opc ops outs sa. ci_mono sa (SND (emit_inst opc ops outs sa))
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       fresh_id_def, emit_def, comp_return_def,
       venomInstTheory.mk_inst_def, pairTheory.UNCURRY,
       ci_mono_def, rich_listTheory.IS_PREFIX_APPEND3]
QED

(* ci_mono for compile_ptr_load (used by unwrap_value) *)
Theorem ci_mono_compile_ptr_load[local]:
  ∀ is_ctor loc op sa. ci_mono sa (SND (compile_ptr_load is_ctor loc op sa))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[contextTheory.compile_ptr_load_def] >>
  rw[] >> simp[ci_mono_emit_op]
QED

(* ===== blocks_len toolkit for ci_mono proofs ===== *)

(* LENGTH cs_blocks is preserved by all primitives except new_block *)
Theorem blocks_len_bind[local]:
  ∀ (m : compile_state -> 'a # compile_state)
    (g : 'a -> compile_state -> 'b # compile_state) sa.
    LENGTH (SND (monad_bind m g sa)).cs_blocks =
    LENGTH (SND (g (FST (m sa)) (SND (m sa)))).cs_blocks
Proof
  rw[comp_bind_def, LET_THM, pairTheory.UNCURRY]
QED

Theorem blocks_pres_emit_op[local]:
  ∀ opc ops sa.
    LENGTH (SND (emit_op opc ops sa)).cs_blocks = LENGTH sa.cs_blocks
Proof
  rw[emit_op_def, comp_bind_def, comp_ignore_bind_def, LET_THM,
     pairTheory.UNCURRY, fresh_id_def, fresh_var_def, emit_def,
     venomInstTheory.mk_inst_def, comp_return_def]
QED

Theorem blocks_pres_emit_void[local]:
  ∀ opc ops sa.
    LENGTH (SND (emit_void opc ops sa)).cs_blocks = LENGTH sa.cs_blocks
Proof
  rw[emit_void_def, comp_bind_def, comp_ignore_bind_def, LET_THM,
     pairTheory.UNCURRY, fresh_id_def, emit_def,
     venomInstTheory.mk_inst_def, comp_return_def]
QED

Theorem blocks_pres_emit_inst[local]:
  ∀ opc ops outs sa.
    LENGTH (SND (emit_inst opc ops outs sa)).cs_blocks = LENGTH sa.cs_blocks
Proof
  rw[emit_inst_def, comp_bind_def, comp_ignore_bind_def, LET_THM,
     pairTheory.UNCURRY, fresh_id_def, emit_def,
     venomInstTheory.mk_inst_def, comp_return_def]
QED

Theorem blocks_pres_compile_ptr_load[local]:
  ∀ ic loc op sa.
    LENGTH (SND (compile_ptr_load ic loc op sa)).cs_blocks =
    LENGTH sa.cs_blocks
Proof
  rpt gen_tac >> Cases_on `loc` >>
  rw[contextTheory.compile_ptr_load_def] >>
  rw[blocks_pres_emit_op]
QED

Theorem blocks_pres_compile_ptr_store[local]:
  ∀ ic loc op v sa.
    LENGTH (SND (compile_ptr_store ic loc op v sa)).cs_blocks =
    LENGTH sa.cs_blocks
Proof
  rpt gen_tac >> Cases_on `loc` >>
  rw[contextTheory.compile_ptr_store_def] >>
  rw[blocks_pres_emit_void]
QED

Theorem blocks_grow_new_block[local]:
  ∀ lbl sa.
    LENGTH (SND (new_block lbl sa)).cs_blocks =
    SUC (LENGTH sa.cs_blocks)
Proof
  rw[new_block_def]
QED

Theorem blocks_pres_scaled_offset[local]:
  ∀ scale base ctr sa.
    LENGTH (SND
      ((if scale = 1 then emit_op ADD [base; ctr]
        else do scaled <- emit_op MUL [ctr; Lit (n2w scale)];
                emit_op ADD [base; scaled]
             od) sa)).cs_blocks =
    LENGTH sa.cs_blocks
Proof
  rw[] >>
  simp[comp_bind_def, LET_THM, pairTheory.UNCURRY, blocks_pres_emit_op]
QED

(* compile_word_copy_loop grows blocks by exactly 3 *)
val blocks_len_rws = [blocks_len_bind,
  SIMP_RULE bool_ss [] (Q.SPECL [`i`,`sa`] (INST_TYPE [alpha |-> ``:unit``] blocks_pres_emit_op)),
  blocks_pres_emit_op, blocks_pres_emit_void, blocks_pres_emit_inst,
  blocks_pres_compile_ptr_load, blocks_pres_compile_ptr_store,
  blocks_pres_scaled_offset, blocks_grow_new_block,
  SIMP_RULE bool_ss [LET_THM] fresh_var_def,
  SIMP_RULE bool_ss [LET_THM] fresh_id_def,
  SIMP_RULE bool_ss [LET_THM] fresh_label_def,
  SIMP_RULE bool_ss [] emit_def,
  comp_return_def];

Theorem blocks_grow_compile_word_copy_loop[local]:
  ∀ src dst wc ll sl ic sa.
    LENGTH sa.cs_blocks + 3 =
    LENGTH (SND (compile_word_copy_loop src dst wc ll sl ic sa)).cs_blocks
Proof
  rw[contextTheory.compile_word_copy_loop_def, LET_THM] >>
  simp[comp_bind_def, comp_ignore_bind_def, pairTheory.UNCURRY,
       fresh_label_def, fresh_var_def, comp_return_def,
       blocks_pres_emit_inst, blocks_pres_emit_op,
       blocks_pres_compile_ptr_load, blocks_pres_compile_ptr_store,
       blocks_pres_scaled_offset, blocks_grow_new_block]
QED

(* ci_mono for compile_word_copy_loop *)
Theorem ci_mono_compile_word_copy_loop[local]:
  ∀ src dst wc ll sl ic sa.
    ci_mono sa (SND (compile_word_copy_loop src dst wc ll sl ic sa))
Proof
  rw[ci_mono_def] >> disj2_tac >>
  `LENGTH sa.cs_blocks + 3 =
   LENGTH (SND (compile_word_copy_loop src dst wc ll sl ic sa)).cs_blocks`
    by rw[blocks_grow_compile_word_copy_loop] >>
  simp[]
QED

(* ci_mono for compile_alloc_buffer *)
Theorem ci_mono_compile_alloc_buffer[local]:
  ∀ size sa. ci_mono sa (SND (compile_alloc_buffer size sa))
Proof
  rw[contextTheory.compile_alloc_buffer_def,
     comp_bind_def, comp_return_def, LET_THM, pairTheory.UNCURRY] >>
  simp[ci_mono_emit_op]
QED

(* ci_mono for storage/transient/code_to_memory *)
Theorem ci_mono_compile_storage_to_memory[local]:
  ∀ slot buf wc sa.
    ci_mono sa (SND (compile_storage_to_memory slot buf wc sa))
Proof
  rw[contextTheory.compile_storage_to_memory_def,
     ci_mono_compile_word_copy_loop]
QED

Theorem ci_mono_compile_transient_to_memory[local]:
  ∀ slot buf wc sa.
    ci_mono sa (SND (compile_transient_to_memory slot buf wc sa))
Proof
  rw[contextTheory.compile_transient_to_memory_def,
     ci_mono_compile_word_copy_loop]
QED

Theorem ci_mono_compile_code_to_memory[local]:
  ∀ off dst wc sa.
    ci_mono sa (SND (compile_code_to_memory off dst wc sa))
Proof
  rw[contextTheory.compile_code_to_memory_def] >>
  rw[ci_mono_def]
  >- simp[comp_return_def]
  >> disj2_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, pairTheory.UNCURRY, LET_THM,
       comp_return_def] >>
  `LENGTH sa.cs_blocks + 3 =
   LENGTH (SND (compile_word_copy_loop off dst wc LocCode LocMemory F sa)).cs_blocks`
    by rw[blocks_grow_compile_word_copy_loop] >>
  simp[]
QED

(* ci_mono for compile_ensure_in_memory:
   Storage/Transient → blocks grow via compile_word_copy_loop (always)
   Code → blocks grow when word_count > 0, isPREFIX when word_count = 0
   Calldata → blocks preserved, isPREFIX via emit chain
   Memory → trivial via comp_return *)

(* Shared tactic abbreviation for blocks-grew cases *)
val blocks_grew_tac =
  simp[ci_mono_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, pairTheory.UNCURRY] >> disj2_tac;

val blocks_grew_rws =
  [contextTheory.compile_alloc_buffer_def,
   comp_bind_def, comp_ignore_bind_def, comp_return_def,
   pairTheory.UNCURRY, LET_THM,
   GSYM blocks_grow_compile_word_copy_loop,
   blocks_pres_emit_op];

(* Shared tactic for isPREFIX cases *)
val isPREFIX_prim_rws =
  [contextTheory.compile_alloc_buffer_def,
   emit_op_def, emit_void_def, comp_bind_def,
   comp_ignore_bind_def, comp_return_def,
   fresh_id_def, fresh_var_def, emit_def,
   venomInstTheory.mk_inst_def, pairTheory.UNCURRY, LET_THM];

Theorem ci_mono_compile_ensure_in_memory[local]:
  ∀ ptr_op loc mem_bytes word_count is_ctor sa.
    ci_mono sa
      (SND (compile_ensure_in_memory ptr_op loc mem_bytes word_count is_ctor sa))
Proof
  rpt gen_tac >> Cases_on `loc` >>
  simp[contextTheory.compile_ensure_in_memory_def, LET_THM]
  (* LocMemory *)
  >- simp[comp_return_def, ci_mono_def]
  (* LocStorage: blocks grow *)
  >- (blocks_grew_tac >>
      simp (contextTheory.compile_storage_to_memory_def :: blocks_grew_rws))
  (* LocTransient: blocks grow *)
  >- (blocks_grew_tac >>
      simp (contextTheory.compile_transient_to_memory_def :: blocks_grew_rws))
  (* LocCode: case split on word_count *)
  >- (simp[ci_mono_def, comp_bind_def, comp_ignore_bind_def,
           comp_return_def, pairTheory.UNCURRY] >>
      Cases_on `word_count = 0`
      >- (disj1_tac >>
          simp (contextTheory.compile_code_to_memory_def :: isPREFIX_prim_rws) >>
          rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
          simp[rich_listTheory.IS_PREFIX_APPEND3])
      >> disj2_tac >>
      simp (contextTheory.compile_code_to_memory_def :: blocks_grew_rws))
  (* LocCalldata: compose the monotonicity interfaces of each primitive.
     Avoid unfolding the emit chain into a very large isPREFIX goal. *)
  >> irule ci_mono_bind
  >> simp[ci_mono_emit_op]
  >> rpt gen_tac
  >> irule ci_mono_bind
  >> simp[ci_mono_compile_alloc_buffer]
  >> rpt gen_tac >> PURE_REWRITE_TAC[LET_THM]
  >> irule ci_mono_ignore_bind
  >> simp[ci_mono_emit_void]
  >> gen_tac
  >> irule ci_mono_bind
  >> simp[ci_mono_emit_op]
  >> rpt gen_tac
  >> irule ci_mono_bind
  >> simp[ci_mono_emit_op]
  >> rpt gen_tac
  >> irule ci_mono_ignore_bind
  >> simp[ci_mono_emit_void]
  >> gen_tac >> simp[ci_mono_comp_return]
QED

(* ci_mono for unwrap_value *)
Theorem ci_mono_unwrap_value[local]:
  ∀ cenv vv sa. ci_mono sa (SND (unwrap_value cenv vv sa))
Proof
  rpt gen_tac >> Cases_on `vv` >>
  simp[unwrap_value_def]
  (* StackValue: comp_return *)
  >- simp[comp_return_def, ci_mono_def]
  (* LocatedValue: split on is_word_type *)
  >> rw[]
  (* word type: compile_ptr_load *)
  >- simp[ci_mono_compile_ptr_load]
  (* non-word type: case on ptr_location *)
  >> Cases_on `p.ptr_location` >>
  simp[LET_THM]
  >- simp[comp_return_def, ci_mono_def]
  >> simp[ci_mono_compile_ensure_in_memory]
QED

Theorem ci_mono_lower_value_cfn[local]:
  ∀ cfn cenv ty e sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (lower_value cfn cenv ty e sa))
Proof
  rpt strip_tac >> simp[lower_value_def] >> irule ci_mono_bind >> simp[ci_mono_unwrap_value]
QED

Theorem ci_mono_compile_dynarray_pop[local]:
  ∀ base_op ws es load_opc store_opc sa.
    ci_mono sa (SND (compile_dynarray_pop base_op ws es load_opc store_opc sa))
Proof
  simp[compile_dynarray_pop_def, LET_THM] >>
  rpt (CHANGED_TAC (rpt gen_tac >>
    (TRY (irule ci_mono_bind >> conj_tac) >>
     TRY (irule ci_mono_ignore_bind >> conj_tac) >>
     simp[ci_mono_emit_op, ci_mono_emit_void])))
QED

(* ===== compile_expr ci_mono by induction ===== *)

(*
 * ci_mono for compile_expr: every call either appends to cs_current_insts
 * (keeping cs_blocks) or increases LENGTH cs_blocks (via new_block).
 * Proved by unfolding definitions and composing ci_mono lemmas.
 *)

Theorem ci_mono_compile_store_bytestring[local]:
  ∀ val_op dst_op sa.
    ci_mono sa (SND (compile_store_bytestring val_op dst_op sa))
Proof
  simp[contextTheory.compile_store_bytestring_def, LET_THM] >>
  rpt (CHANGED_TAC (rpt gen_tac >>
    (TRY (irule ci_mono_bind >> conj_tac) >>
     TRY (irule ci_mono_ignore_bind >> conj_tac) >>
     simp[ci_mono_emit_op, ci_mono_emit_void])))
QED

Theorem ci_mono_compile_struct_lit_cfn[local]:
  ∀ cfn cenv ty fields buf_op cur_offset sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_struct_lit cfn cenv ty fields buf_op cur_offset sa))
Proof
  Induct_on `fields` >> simp[compile_struct_lit_def, ci_mono_comp_return] >>
  rpt gen_tac >> Cases_on `h` >> strip_tac >> simp[Once compile_struct_lit_def, LET_THM] >> rpt (CHANGED_TAC (rpt gen_tac >> TRY (irule ci_mono_bind >> conj_tac) >> TRY (irule ci_mono_ignore_bind >> conj_tac) >> TRY IF_CASES_TAC >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_store_bytestring] >> TRY (irule ci_mono_lower_value_cfn >> metis_tac[]) >> TRY (rpt strip_tac >> first_x_assum irule >> metis_tac[])))
QED

Theorem ci_mono_compile_concat_cfn[local]:
  ∀ cfn cenv es data_ptr infos offset_op sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_concat cfn cenv es data_ptr infos offset_op sa))
Proof
  recInduct compile_concat_ind >> rpt strip_tac >> gvs[compile_concat_def, ci_mono_comp_return] >>
Cases_on `is_bs` >> gvs[] >>
irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void] >>
TRY (irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_ignore_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_bind >> rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void]) >>
TRY (irule ci_mono_lower_value_cfn >> simp[])
QED

Theorem ci_mono_compile_make_array_cfn[local]:
  ∀ cfn cenv es elem_size has_lw alloca_size buf_op cur_idx sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_make_array cfn cenv es elem_size has_lw alloca_size buf_op cur_idx sa))
Proof
  Induct_on `es` >> rpt strip_tac
  >- (simp[compile_make_array_def, LET_THM] >> rw[] >>
      simp[ci_mono_comp_return] >>
      irule ci_mono_ignore_bind >> simp[ci_mono_emit_void, ci_mono_comp_return])
  >> simp[Once compile_make_array_def, LET_THM]
  >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> irule ci_mono_lower_value_cfn >> simp[]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_emit_op]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[ci_mono_emit_void] >> IF_CASES_TAC >> simp[ci_mono_compile_store_bytestring, ci_mono_emit_void]) >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

(* Reusable tactic for ci_mono composition through monadic expressions *)
val ci_mono_base_thms =
  [ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
   ci_mono_fresh_var, ci_mono_fresh_id, ci_mono_fresh_label,
   ci_mono_new_block, ci_mono_comp_return, ci_mono_emit,
   ci_mono_compile_ptr_load, ci_mono_unwrap_value,
   ci_mono_compile_ensure_in_memory, ci_mono_compile_alloc_buffer,
   ci_mono_compile_word_copy_loop, ci_mono_compile_storage_to_memory,
   ci_mono_compile_transient_to_memory, ci_mono_compile_code_to_memory,
   ci_mono_compile_dynarray_pop,
   ci_mono_compile_store_bytestring,
   ci_mono_refl];

Theorem ci_mono_compile_multi_exprs[local]:
  ∀ cfn cenv es sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_multi_exprs cfn cenv es sa))
Proof
  Induct_on `es` >> rpt strip_tac
  >- simp[compile_multi_exprs_def, ci_mono_comp_return]
  >> simp[Once compile_multi_exprs_def, LET_THM]
  >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> ho_match_mp_tac ci_mono_lower_value_cfn >> metis_tac[])
  >> rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> first_x_assum ho_match_mp_tac >> metis_tac[])
  >> rpt strip_tac >> simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_keccak256_key[local]:
  ∀ key_op is_bytes32 sa.
    ci_mono sa (SND (compile_keccak256_key key_op is_bytes32 sa))
Proof
  rpt gen_tac >> simp[compile_keccak256_key_def, LET_THM] >> IF_CASES_TAC >> rpt gen_tac >> rpt (irule ci_mono_ignore_bind ORELSE irule ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_compile_alloc_buffer, ci_mono_comp_return] >> rpt gen_tac >> rpt (irule ci_mono_ignore_bind ORELSE irule ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_compile_alloc_buffer, ci_mono_comp_return]
QED

Theorem ci_mono_compile_mapping_subscript[local]:
  ∀ base_slot key_op sa.
    ci_mono sa (SND (compile_mapping_subscript base_slot key_op sa))
Proof
  simp[compile_mapping_subscript_def, LET_THM] >>
  rpt (CHANGED_TAC (rpt gen_tac >>
    (TRY (irule ci_mono_bind >> conj_tac) >>
     TRY (irule ci_mono_ignore_bind >> conj_tac) >>
     simp[ci_mono_emit_op, ci_mono_emit_void,
          ci_mono_compile_alloc_buffer, ci_mono_comp_return])))
QED

Theorem ci_mono_compile_tuple_subscript[local]:
  ∀ base_op offset sa.
    ci_mono sa (SND (compile_tuple_subscript base_op offset sa))
Proof
  rpt gen_tac >> Cases_on `offset` >> simp[compile_tuple_subscript_def, ci_mono_emit_op, ci_mono_comp_return]
QED

Theorem ci_mono_compile_array_subscript[local]:
  ∀ base_op idx_op is_dyn sc ws es is_signed load_opc sa.
    ci_mono sa (SND (compile_array_subscript base_op idx_op is_dyn sc ws es is_signed load_opc sa))
Proof
  rpt gen_tac >>
  simp[compile_array_subscript_def, LET_THM] >>
  rpt (CHANGED_TAC (rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind) >>
    rpt strip_tac >>
    simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
         ci_mono_compile_alloc_buffer, ci_mono_refl] >>
    TRY (IF_CASES_TAC >>
         simp[ci_mono_emit_op, ci_mono_comp_return, LET_THM])))
QED

Theorem ci_mono_compile_subscript_cfn[local]:
  ∀ cfn cenv ret_ty ty base_e idx_e sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_subscript cfn cenv ret_ty ty base_e idx_e sa))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_subscript_def] >> BETA_TAC >>
  PURE_REWRITE_TAC[LET_THM] >> BETA_TAC >>
  IF_CASES_TAC >-
  (* hashmap case *)
  (irule ci_mono_bind >> conj_tac >-
   (rpt strip_tac >> BETA_TAC >>
    irule ci_mono_bind >> conj_tac >-
    (rpt strip_tac >> BETA_TAC >>
     irule ci_mono_bind >> conj_tac >-
     (rpt strip_tac >> simp[ci_mono_comp_return]) >>
     simp[ci_mono_compile_mapping_subscript]) >>
    IF_CASES_TAC >>
    simp[ci_mono_compile_keccak256_key, ci_mono_comp_return]) >>
   irule ci_mono_lower_value_cfn >> metis_tac[]) >>
  (* non-hashmap: case on ce_var_type *)
  qmatch_asmsub_abbrev_tac`¬_(cbe)` >>
  BasicProvers.TOP_CASE_TAC >> gvs[] >- (
    irule ci_mono_bind >> gvs[] >> rpt strip_tac >>
    irule ci_mono_bind >> gvs[ci_mono_comp_return] >> rpt strip_tac >>
    irule ci_mono_bind >> gvs[] >> rpt gen_tac >>
    reverse conj_tac >- (
      rpt gen_tac >>
      irule ci_mono_lower_value_cfn >>
      rpt strip_tac >> first_x_assum irule) >>
    rpt gen_tac >>
    irule ci_mono_bind >> gvs[ci_mono_compile_array_subscript] >> rpt gen_tac >>
    simp[ci_mono_comp_return] ) >>
  BasicProvers.CASE_TAC >> gvs[] >>
  irule ci_mono_bind >> gvs[] >> rpt strip_tac >>
  irule ci_mono_bind >> gvs[ci_mono_comp_return] >> rpt strip_tac >>
  irule ci_mono_bind >> gvs[] >> rpt strip_tac >>
  TRY (
    rpt gen_tac >>
    irule ci_mono_lower_value_cfn >>
    rpt strip_tac >> first_x_assum irule) >>
  TRY (
    irule ci_mono_bind >>
    gvs[ci_mono_compile_array_subscript] >>
    rpt gen_tac ) >>
  simp[ci_mono_comp_return, ci_mono_compile_tuple_subscript]
QED

Theorem ci_mono_compile_acc_cfn[local]:
  ∀ cfn cenv addr_e item sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_acc cfn cenv addr_e item sa))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `item`
  >- (rewrite_tac[Once compile_acc_def] >> irule ci_mono_lower_value_cfn >> metis_tac[]) >>
  simp[compile_acc_def, LET_THM, pairTheory.UNCURRY] >>
  rpt strip_tac >>
  TRY (irule ci_mono_emit_inst >> NO_TAC) >>
  TRY (irule ci_mono_trans >>
       qexists_tac `SND (lower_value cfn cenv (BaseT AddressT) addr_e sa)` >>
       conj_tac >- (irule ci_mono_lower_value_cfn >> metis_tac[]) >>
       simp[ci_mono_emit_op] >> NO_TAC) >>
  irule ci_mono_trans >>
  qexists_tac `SND (emit_op EXTCODESIZE
    [FST (lower_value cfn cenv (BaseT AddressT) addr_e sa)]
    (SND (lower_value cfn cenv (BaseT AddressT) addr_e sa)))` >>
  conj_tac >- (
    irule ci_mono_trans >>
    qexists_tac `SND (lower_value cfn cenv (BaseT AddressT) addr_e sa)` >>
    conj_tac >- (irule ci_mono_lower_value_cfn >> metis_tac[]) >>
    simp[ci_mono_emit_op]) >>
  simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_attribute_cfn[local]:
  ∀ cfn cenv ret_ty ty base_e field sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_attribute cfn cenv ret_ty ty base_e field sa))
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[compile_attribute_def] >> BETA_TAC >>
  irule ci_mono_bind >> conj_tac
  >- (rpt gen_tac >>
      Cases_on `FLOOKUP (compile_env_ce_vars cenv) field'` >>
      simp[LET_THM, ci_mono_comp_return] >>
      BasicProvers.every_case_tac >> simp[ci_mono_comp_return] >>
      irule ci_mono_bind >> conj_tac >>
      simp[ci_mono_emit_op, ci_mono_comp_return] >>
      rpt gen_tac >> simp[ci_mono_comp_return])
  >> metis_tac[]
QED

Theorem ci_mono_as_stack_val[local]:
  ∀ ty p sa. SND (as_stack_val ty p) = SND p
Proof
  rpt gen_tac >> Cases_on `p` >> simp[as_stack_val_def]
QED

Theorem ci_mono_as_ptr_val[local]:
  ∀ ty loc p sa. SND (as_ptr_val ty loc p) = SND p
Proof
  rpt gen_tac >> Cases_on `p` >> simp[as_ptr_val_def]
QED

Theorem ci_mono_compile_clamp[local]:
  ∀ val_op ty sa. ci_mono sa (SND (compile_clamp val_op ty sa))
Proof
  rpt gen_tac >> simp[compile_clamp_def, LET_THM, pairTheory.UNCURRY] >> IF_CASES_TAC >> gvs[] >> rpt (rpt gen_tac >> (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind) >> (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void])) >> simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem ci_mono_compile_select[local]:
  ∀ cmp a b sa. ci_mono sa (SND (compile_select cmp a b sa))
Proof
  rpt gen_tac >> simp[builtinSimpleTheory.compile_select_def, LET_THM, pairTheory.UNCURRY_DEF] >> irule ci_mono_bind >> simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_bind >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_env_var[local]:
  ∀ item sa. ci_mono sa (SND (compile_env_var item sa))
Proof
  rpt gen_tac >> Cases_on `item` >> simp[compile_env_var_def] >> TRY (simp[ci_mono_emit_op] >> NO_TAC) >> irule ci_mono_bind >> simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_bind >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_invert[local]:
  ∀ v ty cenv sa. ci_mono sa (SND (compile_invert v ty cenv sa))
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[compile_invert_def, ci_mono_emit_op]
QED

Theorem ci_mono_emit_multi_op[local]:
  ∀ opc ops n sa. ci_mono sa (SND (emit_multi_op opc ops n sa))
Proof
  rpt gen_tac >>
`!n sa. ci_mono sa (SND (fresh_vars n sa))` by (
  Induct >> simp[fresh_vars_def, ci_mono_comp_return] >>
  rpt gen_tac >>
  irule ci_mono_bind >>
  simp[ci_mono_fresh_var] >>
  rpt strip_tac >>
  irule ci_mono_bind >>
  simp[ci_mono_comp_return]
) >>
simp[emit_multi_op_def] >>
irule ci_mono_bind >>
simp[] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >>
simp[ci_mono_emit_inst, ci_mono_comp_return]
QED

Theorem ci_mono_store_multi_results[local]:
  ∀ buf_op results offset sa. ci_mono sa (SND (store_multi_results buf_op results offset sa))
Proof
  Induct_on `results` >- simp[store_multi_results_def, ci_mono_comp_return] >> rpt strip_tac >> once_rewrite_tac[store_multi_results_def] >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_emit_op]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >> simp[]
QED

Theorem ci_mono_compile_store_byte_chunks[local]:
  ∀ data_ptr bs offset sa. ci_mono sa (SND (compile_store_byte_chunks data_ptr bs offset sa))
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> rpt strip_tac >- simp[compile_store_byte_chunks_def, ci_mono_comp_return] >> simp[Once compile_store_byte_chunks_def, LET_THM] >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >> first_x_assum (qspecl_then [`TAKE 32 (v4::v5 ++ REPLICATE 31 0w)`, `word_of_bytes T 0w (TAKE 32 (v4::v5 ++ REPLICATE 31 0w))`] mp_tac) >> simp[]
QED

Theorem ci_mono_compile_store_words[local]:
  ∀ buf_op vs offset sa. ci_mono sa (SND (compile_store_words buf_op vs offset sa))
Proof
  Induct_on `vs` >- simp[compile_store_words_def, ci_mono_comp_return] >> rpt strip_tac >> once_rewrite_tac[compile_store_words_def] >> simp_tac std_ss [LET_THM] >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_emit_op]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> simp[ci_mono_emit_void]
QED

Theorem ci_mono_clamp_and_return[local]:
  ∀ res ty sa. ci_mono sa (SND (clamp_and_return res ty sa))
Proof
  simp[clamp_and_return_def] >> metis_tac[ci_mono_ignore_bind, ci_mono_compile_clamp, ci_mono_comp_return]
QED

Theorem ci_mono_wrap_truncate[local]:
  ∀ res ty sa. ci_mono sa (SND (wrap_truncate res ty sa))
Proof
  rpt gen_tac >> simp[Once wrap_truncate_def] >> IF_CASES_TAC >> simp[ci_mono_comp_return] >> IF_CASES_TAC >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_safe_add[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_add x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_add_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_sub[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_sub x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_sub_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_mul_overflow_check[local]:
  ∀ x y res is_signed bits sa. ci_mono sa (SND (compile_mul_overflow_check x y res is_signed bits sa))
Proof
  rpt gen_tac >> simp[Once compile_mul_overflow_check_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_mul[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_mul x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_mul_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_compile_mul_overflow_check ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_div[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_div x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_div_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_mod[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_mod x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_mod_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_decimal_div[local]:
  ∀ x y d ty sa. ci_mono sa (SND (compile_safe_decimal_div x y d ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_decimal_div_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_safe_pow[local]:
  ∀ x y ty sa. ci_mono sa (SND (compile_safe_pow x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_safe_pow_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_clamp_and_return ORELSE irule ci_mono_compile_clamp ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_compare[local]:
  ∀ op x y ty sa. ci_mono sa (SND (compile_compare op x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_compare_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_inst ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_neg_helper[local]:
  ∀ v ty sa. ci_mono sa (SND (compile_neg v ty sa))
Proof
  rpt gen_tac >> simp[Once compile_neg_def, LET_THM, pairTheory.UNCURRY] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_builtin_abs[local]:
  ∀ val_op sa. ci_mono sa (SND (compile_builtin_abs val_op sa))
Proof
  rpt gen_tac >> simp[Once builtinSimpleTheory.compile_builtin_abs_def, LET_THM] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE irule ci_mono_compile_select ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_binop[local]:
  ∀ op x y ty sa. ci_mono sa (SND (compile_binop op x y ty sa))
Proof
  rpt gen_tac >> simp[Once compile_binop_def, LET_THM] >>
  BasicProvers.every_case_tac >>
  simp[ci_mono_compile_safe_add, ci_mono_compile_safe_sub, ci_mono_compile_safe_mul, ci_mono_compile_safe_div, ci_mono_compile_safe_mod, ci_mono_compile_safe_decimal_div, ci_mono_compile_safe_pow, ci_mono_compile_compare, ci_mono_emit_op] >>
  rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE irule ci_mono_wrap_truncate ORELSE irule ci_mono_compile_select ORELSE irule ci_mono_emit_op ORELSE irule ci_mono_emit_inst ORELSE irule ci_mono_emit_void ORELSE irule ci_mono_comp_return ORELSE (conj_tac >> all_tac) ORELSE gen_tac ORELSE strip_tac ORELSE BETA_TAC)
QED

Theorem ci_mono_compile_bytelike_literal[local]:
  ∀ bs max_len sa. ci_mono sa (SND (compile_bytelike_literal bs max_len sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.compile_bytelike_literal_def, LET_THM] >>
  BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_alloc_buffer] >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_compile_store_byte_chunks] >> rpt strip_tac >> simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_literal_vv[local]:
  ∀ ty l sa. ci_mono sa (SND (compile_literal_vv ty l sa))
Proof
  rpt gen_tac >> Cases_on `l` >>
  rewrite_tac[exprLoweringTheory.compile_literal_vv_def, LET_THM] >> BETA_TAC >>
  BasicProvers.every_case_tac >>
  simp[ci_mono_comp_return] >>
  TRY (ho_match_mp_tac ci_mono_bind >> simp[ci_mono_comp_return, ci_mono_compile_bytelike_literal] >> NO_TAC) >>
  Cases_on `b` >> simp[exprLoweringTheory.compile_literal_vv_def, ci_mono_comp_return]
QED

Theorem ci_mono_compile_name_vv[local]:
  ∀ cenv ty id sa. ci_mono sa (SND (compile_name_vv cenv ty id sa))
Proof
  rpt gen_tac >>
  simp[exprLoweringTheory.compile_name_vv_def] >>
  BasicProvers.every_case_tac >>
  simp[ci_mono_comp_return] >>
  ho_match_mp_tac ci_mono_ignore_bind >> simp[ci_mono_comp_return, ci_mono_emit_inst]
QED

Theorem ci_mono_compile_blockhash[local]:
  ∀ n_op sa. ci_mono sa (SND (compile_blockhash n_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_blockhash_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem ci_mono_compile_blobhash[local]:
  ∀ n_op sa. ci_mono sa (SND (compile_blobhash n_op sa))
Proof
  simp[builtinMiscTheory.compile_blobhash_def, ci_mono_emit_op]
QED

Theorem ci_mono_compile_addmod[local]:
  ∀ a b c sa. ci_mono sa (SND (compile_addmod a b c sa))
Proof
  rpt gen_tac >>
  simp[builtinMathTheory.compile_addmod_def] >>
  irule ci_mono_ignore_bind >> simp[ci_mono_emit_void, ci_mono_emit_op]
QED

Theorem ci_mono_compile_mulmod[local]:
  ∀ a b c sa. ci_mono sa (SND (compile_mulmod a b c sa))
Proof
  rpt gen_tac >>
  simp[builtinMathTheory.compile_mulmod_def] >>
  irule ci_mono_ignore_bind >> simp[ci_mono_emit_void, ci_mono_emit_op]
QED

Theorem ci_mono_compile_pow_mod256[local]:
  ∀ x y sa. ci_mono sa (SND (compile_pow_mod256 x y sa))
Proof
  simp[builtinMathTheory.compile_pow_mod256_def, ci_mono_emit_op]
QED


Theorem ci_mono_compile_ceil[local]:
  ∀ v d sa. ci_mono sa (SND (compile_ceil v d sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_ceil_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_compile_select]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_compile_select]
QED

Theorem ci_mono_compile_floor[local]:
  ∀ v d sa. ci_mono sa (SND (compile_floor v d sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_floor_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_compile_select]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_compile_select]
QED

Theorem ci_mono_compile_builtin_calldatasize[local]:
  ∀ sa. ci_mono sa (SND (compile_builtin_calldatasize sa))
Proof
  simp[builtinSimpleTheory.compile_builtin_calldatasize_def, ci_mono_emit_op]
QED

Theorem ci_mono_compile_builtin_len[local]:
  ∀ ic v loc sa. ci_mono sa (SND (compile_builtin_len ic v loc sa))
Proof
  simp[builtinSimpleTheory.compile_builtin_len_def, ci_mono_compile_ptr_load]
QED

Theorem ci_mono_compile_bytestring_hash[local]:
  ∀ ptr_op sa. ci_mono sa (SND (compile_bytestring_hash ptr_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.compile_bytestring_hash_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_list_membership_in[local]:
  ∀ needle ops sa. ci_mono sa (SND (compile_list_membership_in needle ops sa))
Proof
  recInduct exprLoweringTheory.compile_list_membership_in_ind >>
  rpt strip_tac >>
  simp[exprLoweringTheory.compile_list_membership_in_def, ci_mono_comp_return, ci_mono_emit_op] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[] >>
  rpt strip_tac >> simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_list_membership_notin[local]:
  ∀ needle ops sa. ci_mono sa (SND (compile_list_membership_notin needle ops sa))
Proof
  recInduct exprLoweringTheory.compile_list_membership_notin_ind >>
  rpt strip_tac >>
  simp[exprLoweringTheory.compile_list_membership_notin_def, ci_mono_comp_return] >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op]
QED

Theorem ci_mono_compile_array_membership_loop[local]:
  ∀ needle arr_op len_op elem_size offset_base load_opc is_in sa.
    ci_mono sa (SND (compile_array_membership_loop needle arr_op len_op elem_size offset_base load_opc is_in sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.compile_array_membership_loop_def, LET_THM] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
                          ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block,
                          ci_mono_comp_return]) ORELSE
       IF_CASES_TAC ORELSE gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
       ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block,
       ci_mono_comp_return]
QED

Theorem ci_mono_compile_var_array_membership[local]:
  ∀ cenv needle arr_vv rhs_ty is_in sa. ci_mono sa (SND (compile_var_array_membership cenv needle arr_vv rhs_ty is_in sa))
Proof
  rpt gen_tac >>
  simp[exprLoweringTheory.compile_var_array_membership_def, LET_THM] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[] >- simp[ci_mono_emit_op] >> Cases_on `rhs_ty` >> simp[ci_mono_comp_return] >> rename1 `ArrayT _ sz` >> Cases_on `sz` >> simp[ci_mono_comp_return]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (rpt strip_tac >> IF_CASES_TAC >> simp[] >- (Cases_on `rhs_ty` >> simp[ci_mono_comp_return] >> rename1 `ArrayT _ sz` >> Cases_on `sz` >> simp[ci_mono_comp_return] >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> simp[ci_mono_emit_op]) >> rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (rpt strip_tac >> simp[ci_mono_emit_op]) >> rpt strip_tac >> simp[ci_mono_emit_inst]) >> simp[ci_mono_comp_return]) >> rpt strip_tac >> simp[ci_mono_compile_array_membership_loop]
QED

Theorem ci_mono_compile_keccak256_bytes[local]:
  ∀ ptr_op sa. ci_mono sa (SND (compile_keccak256_bytes ptr_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_keccak256_bytes_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_keccak256_bytesm[local]:
  ∀ val_op m sa. ci_mono sa (SND (compile_keccak256_bytesm val_op m sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_keccak256_bytesm_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_keccak256_word[local]:
  ∀ val_op sa. ci_mono sa (SND (compile_keccak256_word val_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_keccak256_word_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_sha256_bytes[local]:
  ∀ ptr_op sa. ci_mono sa (SND (compile_sha256_bytes ptr_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_sha256_bytes_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_sha256_bytesm[local]:
  ∀ val_op m sa. ci_mono sa (SND (compile_sha256_bytesm val_op m sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_sha256_bytesm_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_sha256_word[local]:
  ∀ val_op sa. ci_mono sa (SND (compile_sha256_word val_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinHashingTheory.compile_sha256_word_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_ecrecover[local]:
  ∀ hash_op v_op r_op s_op sa. ci_mono sa (SND (compile_ecrecover hash_op v_op r_op s_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_ecrecover_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_ecadd[local]:
  ∀ x1 y1 x2 y2 sa. ci_mono sa (SND (compile_ecadd x1 y1 x2 y2 sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_ecadd_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_ecmul[local]:
  ∀ x y scalar sa. ci_mono sa (SND (compile_ecmul x y scalar sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_ecmul_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer]
QED

Theorem ci_mono_compile_assert_slice_bounds[local]:
  ∀ start_op len_op src_len sa. ci_mono sa (SND (compile_assert_slice_bounds start_op len_op src_len sa))
Proof
  rpt gen_tac >> simp[builtinBytesTheory.compile_assert_slice_bounds_def] >> rpt (CHANGED_TAC (rpt (irule ci_mono_bind ORELSE irule ci_mono_ignore_bind ORELSE conj_tac ORELSE gen_tac) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]))
QED

Theorem ci_mono_compile_slice_calldata[local]:
  ∀ start_op len_op out_size sa. ci_mono sa (SND (compile_slice_calldata start_op len_op out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_calldata_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]
QED

Theorem ci_mono_compile_slice_code[local]:
  ∀ start_op len_op out_size sa. ci_mono sa (SND (compile_slice_code start_op len_op out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_code_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]
QED

Theorem ci_mono_compile_slice_extcode[local]:
  ∀ addr_op start_op len_op out_size sa. ci_mono sa (SND (compile_slice_extcode addr_op start_op len_op out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_extcode_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]
QED

Theorem ci_mono_compile_slice_memory[local]:
  ∀ src_ptr start_op len_op out_size sa. ci_mono sa (SND (compile_slice_memory src_ptr start_op len_op out_size sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_slice_memory_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_compile_assert_slice_bounds]
QED

Theorem ci_mono_compile_uint2str[local]:
  ∀ val_op n_digits sa. ci_mono sa (SND (compile_uint2str val_op n_digits sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinStringsTheory.compile_uint2str_def, LET_THM] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block, ci_mono_compile_select]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst, ci_mono_comp_return, ci_mono_compile_alloc_buffer, ci_mono_fresh_var, ci_mono_fresh_label, ci_mono_new_block, ci_mono_compile_select]
QED

Theorem ci_mono_compile_as_wei_value_decimal[local]:
  ∀ val_op scale decimal_divisor sa. ci_mono sa (SND (compile_as_wei_value_decimal val_op scale decimal_divisor sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_as_wei_value_decimal_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_as_wei_value_int[local]:
  ∀ val_op scale is_signed sa. ci_mono sa (SND (compile_as_wei_value_int val_op scale is_signed sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinMiscTheory.compile_as_wei_value_int_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_load_bytestring_as_word[local]:
  ∀ v shift_opc sa. ci_mono sa (SND (load_bytestring_as_word v shift_opc sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.load_bytestring_as_word_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_type_convert[local]:
  ∀ v conv_op sa. ci_mono sa (SND (compile_type_convert v conv_op sa))
Proof
  rpt gen_tac >> Cases_on `conv_op` >>
  rewrite_tac[exprLoweringTheory.compile_type_convert_def, LET_THM] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE IF_CASES_TAC ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
                          ci_mono_compile_alloc_buffer, ci_mono_load_bytestring_as_word]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
       ci_mono_compile_alloc_buffer, ci_mono_load_bytestring_as_word] >>
  TRY (pairarg_tac >> simp[] >> IF_CASES_TAC >> simp[] >>
       rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
            (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
            gen_tac ORELSE strip_tac) >>
       simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> NO_TAC) >>
  TRY (pairarg_tac >> simp[] >>
       rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
            (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
            gen_tac ORELSE strip_tac) >>
       simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> NO_TAC) >>
  rpt (ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt gen_tac >> rpt strip_tac) >> TRY (ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac) >> simp[ci_mono_comp_return, ci_mono_emit_void]
QED

Theorem ci_mono_compile_extract32[local]:
  ∀ src_ptr start_op sa. ci_mono sa (SND (compile_extract32 src_ptr start_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[builtinBytesTheory.compile_extract32_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_clamp_extract32[local]:
  ∀ val_op clamp sa. ci_mono sa (SND (compile_clamp_extract32 val_op clamp sa))
Proof
  rpt gen_tac >> Cases_on `clamp` >>
  rewrite_tac[builtinBytesTheory.compile_clamp_extract32_def, LET_THM] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_encode_static[local]:
  ∀ dst src sa. ci_mono sa (SND (compile_abi_encode_static dst src sa))
Proof
  rpt gen_tac >>
  rewrite_tac[abiEncoderTheory.compile_abi_encode_static_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_zero_pad[local]:
  ∀ ptr length count sa. ci_mono sa (SND (compile_abi_zero_pad ptr length count sa))
Proof
  rpt gen_tac >>
  rewrite_tac[abiEncoderTheory.compile_abi_zero_pad_def] >> BETA_TAC >>
  rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
       (conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) ORELSE
       gen_tac ORELSE strip_tac) >>
  simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_int_clamp[local]:
  ∀ val_op bits is_signed sa. ci_mono sa (SND (compile_abi_int_clamp val_op bits is_signed sa))
Proof
  rpt gen_tac >> simp[abiEncoderTheory.compile_abi_int_clamp_def, LET_THM] >> BETA_TAC >> IF_CASES_TAC >> (ho_match_mp_tac ci_mono_ignore_bind ORELSE ho_match_mp_tac ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_bind, ci_mono_ignore_bind]
QED

Theorem ci_mono_compile_abi_bytes_clamp[local]:
  ∀ val_op m sa. ci_mono sa (SND (compile_abi_bytes_clamp val_op m sa))
Proof
  rpt gen_tac >> simp[abiEncoderTheory.compile_abi_bytes_clamp_def, LET_THM] >> BETA_TAC >> rpt (rpt gen_tac >> (ho_match_mp_tac ci_mono_ignore_bind ORELSE ho_match_mp_tac ci_mono_bind) >> conj_tac >- simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_clamp_basetype[local]:
  ∀ val_op clamp sa. ci_mono sa (SND (compile_abi_clamp_basetype val_op clamp sa))
Proof
  Cases_on `clamp` >> simp[abiEncoderTheory.compile_abi_clamp_basetype_def, ci_mono_comp_return, ci_mono_compile_abi_int_clamp, ci_mono_compile_abi_bytes_clamp] >> rpt gen_tac >> TRY (irule ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_ignore_bind >> simp[ci_mono_emit_op, ci_mono_emit_void] >> NO_TAC) >> TRY (irule ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_ignore_bind >> simp[ci_mono_emit_op, ci_mono_emit_void] >> NO_TAC) >> TRY (irule ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> rpt strip_tac >> FIRST [irule ci_mono_ignore_bind, irule ci_mono_bind] >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> rpt strip_tac >> FIRST [irule ci_mono_ignore_bind, irule ci_mono_bind] >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return])
QED

Theorem ci_mono_compile_abi_decode_static[local]:
  ∀ src_op dst_op load_opc clamp_fn sa.
    (∀ v sa'. ci_mono sa' (SND (clamp_fn v sa'))) ⇒
    ci_mono sa (SND (compile_abi_decode_static src_op dst_op load_opc clamp_fn sa))
Proof
  rpt strip_tac >> simp[abiEncoderTheory.compile_abi_decode_static_def] >> BETA_TAC >> ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (first_x_assum irule) >> simp[ci_mono_emit_void]
QED

Theorem ci_mono_compile_getelemptr_abi[local]:
  ∀ src_op is_dyn abi_offset load_opc sa.
    ci_mono sa (SND (compile_getelemptr_abi src_op is_dyn abi_offset load_opc sa))
Proof
  rpt gen_tac >> simp[abiEncoderTheory.compile_getelemptr_abi_def] >> BETA_TAC >> rpt IF_CASES_TAC >> gvs[] >> rpt ((irule ci_mono_ignore_bind ORELSE irule ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> rpt strip_tac) >> TRY (IF_CASES_TAC >> gvs[] >> rpt ((irule ci_mono_ignore_bind ORELSE irule ci_mono_bind) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return] >> rpt strip_tac)) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem ci_mono_compile_abi_decode_dyn_elem_ptr[local]:
  ∀ load_opc elem_src src_data hi_op elem_abi_sz sa.
    ci_mono sa (SND (compile_abi_decode_dyn_elem_ptr load_opc elem_src src_data hi_op elem_abi_sz sa))
Proof
  rpt gen_tac >>
  rewrite_tac[abiEncoderTheory.compile_abi_decode_dyn_elem_ptr_def] >> BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_create_tuple_in_memory[local]:
  ∀ buf_op elems offset sa.
    ci_mono sa (SND (compile_create_tuple_in_memory buf_op elems offset sa))
Proof
  ho_match_mp_tac builtinAbiTheory.compile_create_tuple_in_memory_ind >>
  rpt strip_tac
  >- simp[builtinAbiTheory.compile_create_tuple_in_memory_def, ci_mono_comp_return]
  >> rewrite_tac[builtinAbiTheory.compile_create_tuple_in_memory_def] >> BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_emit_op])
  >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- (IF_CASES_TAC >> simp[ci_mono_emit_void])
  >> rpt strip_tac >> first_x_assum irule
QED

Theorem ci_mono_compile_extcodesize_check[local]:
  ∀ addr_op sa. ci_mono sa (SND (compile_extcodesize_check addr_op sa))
Proof
  rpt gen_tac >> simp[exprLoweringTheory.compile_extcodesize_check_def] >> BETA_TAC >> irule ci_mono_bind >> simp[ci_mono_emit_op, ci_mono_emit_void]
QED

Theorem ci_mono_compile_return_value_decode[local]:
  ∀ buf_op min_sz max_sz sa.
    ci_mono sa (SND (compile_return_value_decode buf_op min_sz max_sz sa))
Proof
  rpt gen_tac >> once_rewrite_tac[exprLoweringTheory.compile_return_value_decode_def] >> BETA_TAC >> rpt (FIRST [irule ci_mono_bind, irule ci_mono_ignore_bind] >> conj_tac >| [rpt strip_tac >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_select], all_tac]) >> simp[ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return, ci_mono_compile_select]
QED

Theorem ci_mono_compile_copy_memory[local]:
  ∀ dst src sz sa. ci_mono sa (SND (compile_copy_memory dst src sz sa))
Proof
  rpt gen_tac >> Cases_on `sz` >>
  rewrite_tac[contextTheory.compile_copy_memory_def] >>
  simp[ci_mono_comp_return, ci_mono_emit_void]
QED

Theorem ci_mono_compile_copy_memory_dynamic[local]:
  ∀ dst src len_op sa. ci_mono sa (SND (compile_copy_memory_dynamic dst src len_op sa))
Proof
  rpt gen_tac >>
  rewrite_tac[contextTheory.compile_copy_memory_dynamic_def] >>
  simp[ci_mono_emit_void]
QED

Theorem ci_mono_compile_with_byte_offset[local]:
  ∀ base offset sa. ci_mono sa (SND (compile_with_byte_offset base offset sa))
Proof
  rpt gen_tac >> Cases_on `offset` >>
  rewrite_tac[contextTheory.compile_with_byte_offset_def] >>
  simp[ci_mono_comp_return, ci_mono_emit_op]
QED

Theorem ci_mono_compile_abi_encode[local]:
  (∀ dst child_ptr child_info is_dyn static_ofst dyn_ofst_ptr sa.
    ci_mono sa (SND (compile_abi_encode_child dst child_ptr child_info is_dyn static_ofst dyn_ofst_ptr sa))) ∧
  (∀ dst src info sa.
    ci_mono sa (SND (compile_abi_encode_to_buf dst src info sa))) ∧
  (∀ dst src elems src_offset head_offset dyn_ptr sa.
    ci_mono sa (SND (compile_abi_encode_complex_elems dst src elems src_offset head_offset dyn_ptr sa))) ∧
  (∀ dst src elem_info elem_abi_sz elem_mem_sz len_op sa.
    ci_mono sa (SND (compile_abi_encode_dyn_loop dst src elem_info elem_abi_sz elem_mem_sz len_op sa)))
Proof
  ho_match_mp_tac abiEncoderTheory.compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac) >>
  simp[Once abiEncoderTheory.compile_abi_encode_child_def, LET_THM] >>
  let
    val base = [ci_mono_emit_op, ci_mono_emit_void, ci_mono_comp_return,
                ci_mono_compile_alloc_buffer, ci_mono_compile_abi_encode_static,
                ci_mono_compile_abi_zero_pad, ci_mono_fresh_label, ci_mono_new_block,
                ci_mono_emit_inst, ci_mono_fresh_var]
    val solve1 = rpt strip_tac >> simp base >> TRY (first_x_assum irule >> simp[])
    val decomp =
      rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
           (conj_tac >- solve1) ORELSE gen_tac ORELSE strip_tac)
    val finish = simp base >> TRY (first_x_assum irule >> simp[])
  in
    rpt strip_tac >>
    (* First try: decompose directly *)
    TRY (decomp >> finish >> NO_TAC) >>
    (* Second try: IF_CASES_TAC then decompose each branch *)
    TRY (IF_CASES_TAC >> gvs[] >> decomp >> finish >> NO_TAC) >>
    (* Third try: nested IF_CASES_TAC *)
    TRY (IF_CASES_TAC >> gvs[] >> IF_CASES_TAC >> gvs[] >> decomp >> finish >> NO_TAC) >>
    (* compile_abi_encode_complex_elems cons case: goal is
       do elem_src <- ..; <compile_abi_encode_child inlined>; complex_elems od
       Decompose as bind(elem_src, ignore_bind(child, complex_elems)) *)
    TRY (
      ho_match_mp_tac ci_mono_bind >> conj_tac >-
        (IF_CASES_TAC >> gvs[] >> simp base) >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (
        (* The inner do..od is compile_abi_encode_child with args inlined.
           We have IH: ∀child_ptr sa. ci_mono sa (SND (compile_abi_encode_child ...))
           But the goal is the inlined body, not the opaque call.
           Rewrite backwards with compile_abi_encode_child_def to fold it back. *)
        IF_CASES_TAC >> gvs[] >> decomp >> finish) >>
      rpt strip_tac >> first_x_assum irule >> NO_TAC) >>
    (* compile_abi_encode_to_buf DynArray case:
       The definition ALREADY has compile_abi_encode_dyn_loop as a call in the
       else-branch, NOT expanded. But rewrite_tac expanded ALL definitions.
       So the dyn_loop body is fully expanded in the goal.
       Solution: DON'T expand this case at all - use simp[Once def] instead.
       Or: fold back the dyn_loop body using GSYM conjunct 10. *)
    TRY (
      ho_match_mp_tac ci_mono_bind >> conj_tac >- simp base >>
      rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp base >>
      rpt strip_tac >>
      IF_CASES_TAC >> gvs[] >-
        (* ¬elem_is_dyn case: all primitives *)
        (decomp >> finish) >>
      (* elem_is_dyn case: goal has expanded compile_abi_encode_dyn_loop.
         Fold it back, then use IH. *)
      ho_match_mp_tac ci_mono_bind >> conj_tac >- simp base >>
      rpt strip_tac >>
      rewrite_tac[GSYM (List.nth (CONJUNCTS abiEncoderTheory.compile_abi_encode_child_def, 9))] >>
      first_x_assum irule >> simp[] >> NO_TAC) >>
    (* compile_abi_encode_complex_elems cons case:
       bind(elem_src, ignore_bind(child_inlined, complex_elems))
       The child call is inlined (compile_abi_encode_child expanded).
       We fold it back using once_rewrite_tac then use IH. *)
    TRY (
      ho_match_mp_tac ci_mono_bind >> conj_tac >-
        (IF_CASES_TAC >> gvs[] >> simp base) >>
      rpt strip_tac >>
      once_rewrite_tac[GSYM abiEncoderTheory.compile_abi_encode_child_def] >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >-
        (first_x_assum irule) >>
      rpt strip_tac >> first_x_assum irule >> NO_TAC) >>
    finish
  end
QED

Theorem ci_mono_compile_abi_decode[local]:
  (∀ dst src_op load_opc hi_op info sa.
    ci_mono sa (SND (compile_abi_decode_to_buf dst src_op load_opc hi_op info sa))) ∧
  (∀ dst src_op load_opc hi_op elems abi_offset vyper_offset sa.
    ci_mono sa (SND (compile_abi_decode_complex_elems dst src_op load_opc hi_op elems abi_offset vyper_offset sa))) ∧
  (∀ dst src_op load_opc hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt sa.
    ci_mono sa (SND (compile_abi_decode_dyn_loop dst src_op load_opc hi_op elem_info elem_abi_sz elem_mem_sz i_ptr cnt sa)))
Proof
  let
    val [c0,c1,c2,c3,c4,c5,c6] = CONJUNCTS abiEncoderTheory.compile_abi_decode_to_buf_def
    val db = fn t => ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[t] >> rpt strip_tac
    val dib = fn t => ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[t] >> rpt strip_tac
  in
  ho_match_mp_tac abiEncoderTheory.compile_abi_decode_to_buf_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt (disch_then strip_assume_tac)
  (* DecPrimWord *)
  >- (rewrite_tac[c0] >> BETA_TAC >>
      irule ci_mono_compile_abi_decode_static >> simp[ci_mono_compile_abi_clamp_basetype])
  (* DecBytestring *)
  >- (rewrite_tac[c1] >>
      ntac 3 (db ci_mono_emit_op) >> dib ci_mono_emit_void >>
      ntac 4 (db ci_mono_emit_op) >> dib ci_mono_emit_void >> dib ci_mono_emit_void >>
      db ci_mono_emit_op >> Cases_on `load_opc` >> simp[ci_mono_emit_void])
  (* DecDynArray *)
  >- (rpt strip_tac >> rewrite_tac[c2] >> BETA_TAC >>
      ntac 3 (db ci_mono_emit_op) >> dib ci_mono_emit_void >>
      ntac 5 (db ci_mono_emit_op) >> dib ci_mono_emit_void >> dib ci_mono_emit_void >>
      simp_tac pure_ss [LET_THM] >> BETA_TAC >> IF_CASES_TAC >> gvs[]
      >- (ntac 3 (db ci_mono_emit_op) >> Cases_on `load_opc` >> simp[ci_mono_emit_void])
      >> db ci_mono_compile_alloc_buffer >> dib ci_mono_emit_void >>
      first_x_assum irule >> simp[])
  (* DecComplex *)
  >- (rpt strip_tac >> rewrite_tac[c3] >> simp_tac pure_ss [LET_THM] >> BETA_TAC >>
      ntac 3 (db ci_mono_emit_op) >> dib ci_mono_emit_void >>
      first_x_assum irule >> simp[])
  (* complex_elems nil *)
  >- (rewrite_tac[c4] >> simp[ci_mono_comp_return])
  (* complex_elems cons *)
  >- (rpt strip_tac >> rewrite_tac[c5] >> BETA_TAC >> simp_tac pure_ss [LET_THM] >> BETA_TAC >>
      db ci_mono_compile_getelemptr_abi >>
      ho_match_mp_tac ci_mono_bind >> conj_tac >- (IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_emit_op]) >> rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (first_x_assum (irule o SRULE[]) >> simp[]) >> rpt strip_tac >>
      first_x_assum (irule o SRULE[]) >> simp[])
  (* dyn_loop *)
  >> rpt strip_tac >> rewrite_tac[c6] >> BETA_TAC >> simp_tac pure_ss [LET_THM] >> BETA_TAC >>
  ntac 3 (db ci_mono_fresh_label) >> dib ci_mono_emit_inst >> dib ci_mono_new_block >>
  ntac 3 (db ci_mono_emit_op) >> dib ci_mono_emit_inst >> dib ci_mono_new_block >>
  ntac 4 (db ci_mono_emit_op) >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- (
    IF_CASES_TAC >> simp[ci_mono_compile_abi_decode_dyn_elem_ptr, ci_mono_comp_return]) >> rpt strip_tac >>
  ntac 3 (db ci_mono_emit_op) >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (first_x_assum (irule o SRULE[]) >> simp[]) >> rpt strip_tac >>
  db ci_mono_emit_op >> dib ci_mono_emit_void >> dib ci_mono_emit_inst >> dib ci_mono_new_block >>
  simp[ci_mono_comp_return]
  end
QED

Theorem ci_mono_compile_default_return_path[local]:
  ∀ buf_op result_op default_op addr_op skip_check min_return_size
    max_return_size ret_mem_bytes ret_dec_info is_prim_return sa.
    ci_mono sa (SND (compile_default_return_path buf_op result_op default_op addr_op
                      skip_check min_return_size max_return_size ret_mem_bytes
                      ret_dec_info is_prim_return sa))
Proof
  rpt gen_tac >>
  rewrite_tac[exprLoweringTheory.compile_default_return_path_def, LET_THM] >> BETA_TAC >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_fresh_label] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_inst] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >-
    (IF_CASES_TAC >> simp[ci_mono_emit_void]) >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >-
    (IF_CASES_TAC >> simp[ci_mono_comp_return, ci_mono_compile_extcodesize_check]) >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_inst] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_compile_return_value_decode] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >-
    simp[cj 1 ci_mono_compile_abi_decode] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_inst] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_new_block] >> rpt strip_tac >>
  simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_stage_intcall_args[local]:
  ∀ cenv vals flags tys sa.
    ci_mono sa (SND (compile_stage_intcall_args cenv vals flags tys sa))
Proof
  ho_match_mp_tac compile_stage_intcall_args_ind >>
  rpt conj_tac >>
  simp[Once compile_stage_intcall_args_def, ci_mono_comp_return] >>
  TRY (rpt gen_tac >> strip_tac >> gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- first_x_assum ACCEPT_TAC >> rpt strip_tac >> simp[ci_mono_comp_return] >> NO_TAC) >>
  rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >> rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- (IF_CASES_TAC >> simp[ci_mono_emit_void] >> IF_CASES_TAC >> simp[ci_mono_emit_void] >- (rpt strip_tac >> ho_match_mp_tac ci_mono_ignore_bind >> simp[ci_mono_compile_store_bytestring, ci_mono_comp_return])) >> rpt strip_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (first_x_assum (fn ih => irule (SRULE [] ih))) >> rpt strip_tac >> simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_extcall_store_args[local]:
  ∀ cfn cenv es tys buf_op offset sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_extcall_store_args cfn cenv es tys buf_op offset sa))
Proof
  ntac 7 gen_tac >> strip_tac >>
  MAP_EVERY qid_spec_tac [`sa`, `offset`, `buf_op`, `tys`, `es`, `cenv`] >>
  Induct_on `es`
  >- simp[compile_extcall_store_args_def, ci_mono_comp_return]
  >> rpt gen_tac >> Cases_on `tys`
  >> simp[Once compile_extcall_store_args_def, LET_THM]
  >> (ho_match_mp_tac ci_mono_bind >> conj_tac
      >- (rpt strip_tac >> irule ci_mono_lower_value_cfn >> metis_tac[])
      >> rpt strip_tac >>
      ho_match_mp_tac ci_mono_bind >> conj_tac
      >- (rpt strip_tac >> IF_CASES_TAC >>
          simp[ci_mono_comp_return, ci_mono_emit_op])
      >> rpt strip_tac >>
      ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
      >- (rpt strip_tac >> TRY IF_CASES_TAC >>
          simp[ci_mono_emit_void] >>
          TRY IF_CASES_TAC >>
          simp[ci_mono_compile_store_bytestring, ci_mono_emit_void])
      >> rpt strip_tac >> first_x_assum irule)
QED

Theorem ci_mono_compile_external_call_kwargs[local]:
  ∀ addr_op args_op args_abi_size method_id_val
    return_abi_size min_return_size ret_mem_bytes
    use_staticcall call_value gas_op
    skip_check has_default default_op
    is_prim_return
    args_enc_info ret_dec_info sa.
    ci_mono sa (SND (compile_external_call_kwargs addr_op args_op args_abi_size method_id_val
                      return_abi_size min_return_size ret_mem_bytes
                      use_staticcall call_value gas_op
                      skip_check has_default default_op
                      is_prim_return
                      args_enc_info ret_dec_info sa))
Proof
  rpt gen_tac >> simp[compile_external_call_kwargs_def, LET_THM] >> BETA_TAC >> irule ci_mono_bind >> reverse conj_tac >- simp[ci_mono_compile_alloc_buffer] >> rpt strip_tac >> BETA_TAC >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac >- simp[ci_mono_emit_void] >> rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_emit_op] >> rpt strip_tac >>
  irule ci_mono_ignore_bind >> conj_tac >- simp[cj 2 ci_mono_compile_abi_encode] >>
  rpt strip_tac >> irule ci_mono_bind >> simp[ci_mono_emit_op] >> rpt strip_tac >> irule ci_mono_ignore_bind >> conj_tac >- (IF_CASES_TAC >> simp[ci_mono_compile_extcodesize_check, ci_mono_comp_return]) >>
  gen_tac >> ho_match_mp_tac ci_mono_bind >> conj_tac >- (gen_tac >> IF_CASES_TAC >> simp[ci_mono_emit_op]) >>
  rpt gen_tac >> ho_match_mp_tac ci_mono_bind >>
  conj_tac >- simp[ci_mono_fresh_label] >>
rpt strip_tac >>
irule ci_mono_bind >> simp[ci_mono_fresh_label] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> simp[ci_mono_emit_inst] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> simp[ci_mono_new_block] >>
rpt strip_tac >>
irule ci_mono_bind >> simp[ci_mono_emit_op] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> simp[ci_mono_emit_void] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> simp[ci_mono_emit_inst] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> simp[ci_mono_new_block] >>
rpt strip_tac >>
IF_CASES_TAC >> gvs[]
>- simp[ci_mono_comp_return]
>> IF_CASES_TAC >> gvs[]
>- (irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
    rpt strip_tac >> simp[ci_mono_compile_default_return_path])
>> irule ci_mono_bind >> simp[ci_mono_compile_alloc_buffer] >>
rpt strip_tac >>
irule ci_mono_bind >> simp[ci_mono_compile_return_value_decode] >>
rpt strip_tac >>
irule ci_mono_ignore_bind >> conj_tac
>- simp[ci_mono_compile_abi_decode]
>> simp[ci_mono_comp_return]
QED

Theorem ci_mono_compile_call[local]:
  ∀ cfn cenv ret_ty ty target args default_ret sa.
    (∀ cenv' ty' e' sa'. ci_mono sa' (SND (cfn cenv' ty' e' sa'))) ⇒
    ci_mono sa (SND (compile_call cfn cenv ret_ty ty target args default_ret sa))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `target` >>
  TRY (simp[compile_call_def, LET_THM, pairTheory.UNCURRY, ci_mono_emit_inst] >> NO_TAC)
  >- ( (* IntCall *)
    simp[compile_call_def, LET_THM, pairTheory.UNCURRY] >>
rpt IF_CASES_TAC >> gvs[] >>
rpt (CHANGED_TAC (
  (irule ci_mono_trans >>
   first_assum (irule_at (Pos last)) >>
   simp[ci_mono_store_multi_results, ci_mono_emit_multi_op, ci_mono_emit_op,
        ci_mono_emit_void, ci_mono_compile_stage_intcall_args,
        ci_mono_compile_alloc_buffer]) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_store_multi_results) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_emit_multi_op) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_emit_op) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_emit_void) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_compile_stage_intcall_args) ORELSE
  (irule ci_mono_trans >>
   irule_at (Pos last) ci_mono_compile_alloc_buffer) ORELSE
  (irule ci_mono_compile_multi_exprs)
)) >>
rpt strip_tac >> first_assum irule)
  >- ( (* ExtCall *)
    PairCases_on `p` >> simp[compile_call_def, LET_THM, pairTheory.UNCURRY] >>
    Cases_on `args` >> simp[ci_mono_emit_inst] >>
    rpt IF_CASES_TAC >> gvs[] >>
    Cases_on `default_ret` >> gvs[] >>
    Cases_on `t` >> gvs[] >>
    rpt (CHANGED_TAC (
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_lower_value_cfn >> simp[]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_emit_op >> simp[]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_compile_extcall_store_args >> simp[]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_compile_alloc_buffer >> simp[]) ORELSE
      (irule ci_mono_trans >>
       first_assum (irule_at (Pos last)) >>
       simp[ci_mono_compile_alloc_buffer, ci_mono_emit_op,
            ci_mono_compile_external_call_kwargs, ci_mono_comp_return]) ORELSE
      (irule ci_mono_trans >>
       irule_at (Pos last) ci_mono_compile_external_call_kwargs) ORELSE
      (irule ci_mono_lower_value_cfn >> simp[]) ORELSE
      (irule ci_mono_compile_extcall_store_args >> simp[])
    )) >>
    gvs[] >> rpt strip_tac >>
    TRY (first_assum irule >> NO_TAC) >>
    TRY (irule ci_mono_refl >> NO_TAC) >>
    simp[ci_mono_emit_inst, ci_mono_comp_return, ci_mono_refl])
  >> (* Send *)
  simp[Once compile_call_def, LET_THM] >>
  Cases_on `args` >> simp[pairTheory.UNCURRY, ci_mono_emit_inst] >>
  Cases_on `t` >> simp[pairTheory.UNCURRY, ci_mono_emit_inst] >>
  Cases_on `t'` >> simp[pairTheory.UNCURRY, ci_mono_emit_inst] >>
  irule ci_mono_trans >> irule_at (Pos last) ci_mono_emit_void >> irule ci_mono_trans >> irule_at (Pos last) ci_mono_emit_op >> irule ci_mono_trans >> irule_at (Pos last) ci_mono_lower_value_cfn >> (conj_tac >- simp[]) >> irule ci_mono_lower_value_cfn >> simp[]
QED

Theorem compile_expr_ci_mono[local]:
  (∀ cenv ty e st. ci_mono st (SND (compile_expr cenv ty e st))) ∧
  (∀ cenv ret_ty ty bi args st.
    ci_mono st (SND (compile_builtin_dispatch cenv ret_ty ty bi args st))) ∧
  (∀ cenv vv_ty ty tb ret_ty args st.
    ci_mono st (SND (compile_type_builtin_dispatch cenv vv_ty ty tb ret_ty args st)))
Proof
  cheat
QED

(* Derive: lower_value compile_expr preserves ci_mono *)
Theorem ci_mono_lower_value_compile_expr[local]:
  ∀ cenv ty e st.
    ci_mono st (SND (lower_value compile_expr cenv ty e st))
Proof
  rw[lower_value_def] >>
  irule ci_mono_bind >> conj_tac
  >- (rpt strip_tac >> simp[ci_mono_unwrap_value])
  >> simp[cj 1 compile_expr_ci_mono]
QED

(* ===== run_inst_seq preserves venom_state fields ===== *)

(* Generic: if every instruction in a list preserves some projection,
   then run_inst_seq preserves it *)
Theorem run_inst_seq_preserves_field:
  !(proj : venom_state -> 'a) is ss ss'.
    run_inst_seq is ss = OK ss' /\
    (!i ss1 ss2. MEM i is /\ step_inst_base i ss1 = OK ss2 ==> proj ss2 = proj ss1)
    ==>
    proj ss' = proj ss
Proof
  gen_tac >> Induct_on `is`
  >- simp[run_inst_seq_def]
  >> rpt gen_tac >> strip_tac >>
  gvs[run_inst_seq_def] >>
  Cases_on `step_inst_base h ss` >> gvs[] >>
  `proj v = proj ss` by
    (first_x_assum (qspecl_then [`h`, `ss`, `v`] mp_tac) >> simp[]) >>
  `proj ss' = proj v` by
    (first_x_assum (qspecl_then [`v`, `ss'`] mp_tac) >> simp[] >>
     disch_then irule >>
     rpt strip_tac >>
     first_x_assum (qspecl_then [`i`, `ss1`, `ss2`] mp_tac) >> simp[]) >>
  simp[]
QED

(* ===== Structural Properties ===== *)

(* Helper: step_inst_base preserves call/tx/block context for ANY instruction
   that returns OK. Unlike step_inst_base_preserves_inst_idx, we don't need
   ~is_terminator because jump_to only modifies vs_prev_bb/vs_current_bb/vs_inst_idx. *)
Theorem step_inst_base_ok_terminator_jump[local]:
  !inst s s'.
    is_terminator inst.inst_opcode /\
    step_inst_base inst s = OK s' ==>
    inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
    inst.inst_opcode = DJMP
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  simp_tac(srw_ss())[] >>
  gvs[AllCaseEqs()]
QED

Theorem step_inst_base_ok_jmp_ctxs[local]:
  !inst s s'.
    inst.inst_opcode = JMP /\ step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >>
  gvs[jump_to_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem step_inst_base_ok_jnz_ctxs[local]:
  !inst s s'.
    inst.inst_opcode = JNZ /\ step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >>
  gvs[jump_to_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem step_inst_base_ok_djmp_ctxs[local]:
  !inst s s'.
    inst.inst_opcode = DJMP /\ step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base inst s = OK s'` mp_tac >>
  ASM_REWRITE_TAC[step_inst_base_def] >>
  CONV_TAC (LAND_CONV (LAND_CONV EVAL)) >>
  gvs[jump_to_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem step_inst_base_ok_jump_ctxs[local]:
  !inst s s'.
    (inst.inst_opcode = JMP \/ inst.inst_opcode = JNZ \/
     inst.inst_opcode = DJMP) /\
    step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  metis_tac[step_inst_base_ok_jmp_ctxs,
            step_inst_base_ok_jnz_ctxs,
            step_inst_base_ok_djmp_ctxs]
QED

Theorem step_inst_base_ok_terminator_ctxs[local]:
  !inst s s'.
    step_inst_base inst s = OK s' /\ is_terminator inst.inst_opcode ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  drule_all step_inst_base_ok_terminator_jump >> strip_tac >>
  metis_tac[step_inst_base_ok_jump_ctxs]
QED

Theorem step_inst_base_preserves_call_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_ok_terminator_ctxs] >>
  Cases_on `inst.inst_opcode = INVOKE` >- gvs[step_inst_base_def] >>
  qspecl_then [`0`, `ARB`, `inst`, `s`, `s'`] mp_tac
    step_preserves_call_ctx >>
  ASM_SIMP_TAC bool_ss [step_inst_non_invoke]
QED

Theorem step_inst_base_preserves_tx_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    s'.vs_tx_ctx = s.vs_tx_ctx
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_ok_terminator_ctxs] >>
  Cases_on `inst.inst_opcode = INVOKE` >- gvs[step_inst_base_def] >>
  qspecl_then [`0`, `ARB`, `inst`, `s`, `s'`] mp_tac
    step_preserves_tx_ctx >>
  ASM_SIMP_TAC bool_ss [step_inst_non_invoke]
QED

Theorem step_inst_base_preserves_block_ctx[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  rpt strip_tac >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[step_inst_base_ok_terminator_ctxs] >>
  Cases_on `inst.inst_opcode = INVOKE` >- gvs[step_inst_base_def] >>
  qspecl_then [`0`, `ARB`, `inst`, `s`, `s'`] mp_tac
    step_preserves_block_ctx >>
  ASM_SIMP_TAC bool_ss [step_inst_non_invoke]
QED

Theorem step_inst_base_preserves_ctxs[local]:
  !inst s s'.
    step_inst_base inst s = OK s' ==>
    s'.vs_call_ctx = s.vs_call_ctx /\
    s'.vs_tx_ctx = s.vs_tx_ctx /\
    s'.vs_block_ctx = s.vs_block_ctx
Proof
  metis_tac[step_inst_base_preserves_call_ctx,
            step_inst_base_preserves_tx_ctx,
            step_inst_base_preserves_block_ctx]
QED

(* compile_expr preserves external-facing state components.
   Memory MAY be modified (keccak256, struct literals, mapping access, etc.
   all emit MSTORE/ALLOCA). Only call/tx/block context and accounts are
   guaranteed unchanged. *)
(* NOTE: original statement was FALSE: vs_accounts is modified by CALL/SEND
   which compile_expr can emit for non-supported expressions.
   Fix: restrict to supported_expr + drop vs_accounts.
   For supported_expr, all emitted opcodes are pure/MLOAD — they preserve contexts. *)
Theorem compile_expr_preserves_contexts:
  ∀ cenv ty e st op st' ss ss'.
    lower_value compile_expr cenv ty e st = (op, st') ∧
    supported_expr e ∧
    same_blocks st st' ∧
    run_inst_seq (emitted_insts st st') ss = OK ss'
    ⇒
    ss'.vs_call_ctx = ss.vs_call_ctx ∧
    ss'.vs_tx_ctx = ss.vs_tx_ctx ∧
    ss'.vs_block_ctx = ss.vs_block_ctx
Proof
  rpt gen_tac >> strip_tac >> rpt conj_tac >> irule (SRULE [] run_inst_seq_preserves_field) >> qexists `emitted_insts st st'` >> rpt strip_tac >> gvs[] >> drule step_inst_base_preserves_ctxs >> simp[]
QED

(* Emitted instructions extend the current block.
   This is a prefix property of the compile monad:
   every operation only appends to cs_current_insts. *)
Theorem compile_expr_extends_insts:
  ∀ cenv ty e st op st'.
    lower_value compile_expr cenv ty e st = (op, st') ∧
    same_blocks st st'
    ⇒
    st'.cs_current_insts =
      st.cs_current_insts ++ emitted_insts st st'
Proof
  rpt strip_tac >>
  `ci_mono st st'` by (
    `ci_mono st (SND (lower_value compile_expr cenv ty e st))`
      by simp[ci_mono_lower_value_compile_expr] >>
    Cases_on `lower_value compile_expr cenv ty e st` >> gvs[]) >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts`
    by (irule ci_mono_same_blocks_isPREFIX >> simp[]) >>
  gvs[GSYM prefix_drop_equiv, emitted_insts_def]
QED
