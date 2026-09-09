(*
 * Statement Lowering Properties
 *
 * TOP-LEVEL:
 *   compile_stmt_correct    — single statement lowering preserves state_rel
 *   compile_stmts_correct   — statement list lowering preserves state_rel
 *   compile_assign_name_correct — NameTarget assignment preserves state_rel
 *   compile_if_correct      — if/else preserves state_rel
 *   compile_for_correct     — for-range preserves state_rel
 *   compile_assert_correct  — assert: OK if true, Abort if false
 *   compile_return_some_external_correct  — external return: Halt
 *   compile_return_some_internal_correct  — internal return: IntRet
 *
 * Helper:
 *   run_compiled_blocks    — run multi-block compiled code
 *
 * Source: vyperInterpreterScript.sml (eval_stmt/eval_stmts)
 * Target: venomExecSemanticsScript.sml (run_block/run_function)
 * Lowering: stmtLoweringScript.sml (compile_stmt/compile_stmts)
 *)

Theory stmtLoweringProps
Ancestors
  list
  stmtLowering exprLoweringProps exprLowering emitHelper emitHelperProps
  compileEnv venomExecSemantics venomExecProps venomInst venomState

(* ===== Multi-Block Execution ===== *)

(* Assemble all blocks from a compile state into a block list.
   Includes all finalized blocks (cs_blocks) plus the current
   still-open block (cs_current_bb / cs_current_insts). *)
Definition assemble_blocks_def:
  assemble_blocks (st':compile_state) =
    let current_bb = <| bb_label := st'.cs_current_bb;
                        bb_instructions := st'.cs_current_insts |> in
    let finalized = st'.cs_blocks in
    finalized ++ [current_bb]
End

(* Build an ir_function from the blocks assembled between two compile states.
   Entry block is the block that was current at the start of compilation. *)
Definition assemble_function_def:
  assemble_function (st:compile_state) (st':compile_state) =
    mk_raw_function st.cs_current_bb (assemble_blocks st')
End

(* Run multi-block compiled code.
   The first block starts at entry_idx (mid-block, after pre-existing
   instructions). Subsequent blocks start at idx 0 via run_blocks.
   Used for statements that create multi-block CFGs (If, For, Assert).
   The ctx parameter supplies the function-call context (for INVOKE). *)
Definition run_compiled_blocks_def:
  run_compiled_blocks (ctx:venom_context) (st:compile_state) (st':compile_state)
                      (ss:venom_state) fuel =
    let fn = assemble_function st st' in
    let entry_lbl = st.cs_current_bb in
    let entry_idx = LENGTH st.cs_current_insts in
    case lookup_block entry_lbl fn.fn_blocks of
      NONE => Error "entry block not found"
    | SOME bb =>
        case exec_block fuel ctx bb
               (ss with <| vs_current_bb := entry_lbl;
                            vs_inst_idx := entry_idx |>) of
          OK ss' =>
            if ss'.vs_halted then Halt ss'
            else run_blocks fuel ctx fn ss'
        | IntRet vals ss' => IntRet vals ss'
        | Halt ss' => Halt ss'
        | Abort a ss' => Abort a ss'
        | Error e => Error e
End

(* ===== Main Statement Correctness ===== *)

(* ===== lookup_block on assembled blocks ===== *)

(* Find the current (last) block in assembled blocks *)
Theorem lookup_block_assemble_current:
  ∀ st' lbl.
    st'.cs_current_bb = lbl ∧
    ¬MEM lbl (MAP (λbb. bb.bb_label) st'.cs_blocks) ⇒
    lookup_block lbl (assemble_blocks st') =
      SOME <| bb_label := lbl; bb_instructions := st'.cs_current_insts |>
Proof
  rw[assemble_blocks_def, lookup_block_def] >>
  pop_assum mp_tac >>
  qspec_tac(`st'.cs_current_bb`,`v`) >>
  qspec_tac(`st'.cs_current_insts`,`insts`) >>
  qspec_tac(`st'.cs_blocks`,`ls`) >>
  Induct >> rw[FIND_thm]
QED

(* Find a finalized block in assembled blocks *)
Theorem lookup_block_assemble_in_blocks:
  ∀ st' bb lbl.
    FIND (λb. b.bb_label = lbl) st'.cs_blocks = SOME bb ⇒
    lookup_block lbl (assemble_blocks st') = SOME bb
Proof
  rw[assemble_blocks_def, lookup_block_def] >>
  qspec_tac(`st'.cs_current_bb`,`v`) >>
  qspec_tac(`st'.cs_current_insts`,`insts`) >>
  pop_assum mp_tac >>
  qspec_tac(`st'.cs_blocks`,`ls`) >>
  Induct >> rw[FIND_thm] >> gvs[FIND_thm]
QED

(* ===== Main Statement Correctness ===== *)

(* compile_stmt preserves state_rel: if the Vyper statement
   evaluates successfully, the compiled Venom code produces
   a related state. *)
Theorem compile_stmt_correct:
  ∀ cenv cx lctx ty s es ss st es' ctx.
    state_rel cenv cx es ss ∧
    eval_stmt cx s es = (INL (), es') ∧
    compile_stmt cenv lctx ty s st = ((), st')
    ⇒
    ∃ ss' fuel.
      run_compiled_blocks ctx st st' ss fuel = OK ss' ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* compile_stmts preserves state_rel *)
Theorem compile_stmts_correct:
  ∀ cenv cx lctx ty stmts es vss st es' ctx.
    state_rel cenv cx es vss ∧
    eval_stmts cx stmts es = (INL (), es') ∧
    compile_stmts cenv lctx ty stmts st = ((), st')
    ⇒
    ∃ vss' fuel.
      run_compiled_blocks ctx st st' vss fuel = OK vss' ∧
      state_rel cenv cx es' vss'
Proof
  cheat
QED

(* ===== Per-Statement Lemmas ===== *)

(* --- Pass: no-op --- *)
Theorem compile_pass_correct:
  ∀ cenv cx lctx ty es ss st.
    state_rel cenv cx es ss ∧
    compile_stmt cenv lctx ty Pass st = ((), st')
    ⇒
    st' = st ∧
    state_rel cenv cx es ss
Proof
  rw[compile_stmt_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* --- Expr statement: side-effect expression --- *)
Theorem compile_expr_stmt_correct:
  ∀ cenv cx lctx ty e es ss st es'.
    state_rel cenv cx es ss ∧
    eval_stmt cx (Expr e) es = (INL (), es') ∧
    compile_stmt cenv lctx ty (Expr e) st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- AnnAssign: variable declaration with init --- *)
Theorem compile_annassign_correct:
  ∀ cenv cx lctx ty id vtyp e es ss st st' es'.
    state_rel cenv cx es ss ∧
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') ∧
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- Assign: store to simple (Name) target --- *)
(* Restricted to NameTarget which has no sub-expression evaluation.
   SubscriptTarget and AttributeTarget evaluate index/field sub-expressions
   which may change compile state, requiring a multi-block argument. *)
Theorem compile_assign_name_correct:
  ∀ cenv cx lctx ty id e es ss st st' v es'.
    state_rel cenv cx es ss ∧
    eval_expr cx e es = (INL (Value v), es') ∧
    compile_stmt cenv lctx ty (Assign (BaseTarget (NameTarget id)) e) st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- Assert: abort on false, continue on true --- *)
(* NOTE: Assert creates multiple blocks (fail_block, ok_block) via new_block.
   Must use run_compiled_blocks, not run_inst_seq. *)
Theorem compile_assert_correct_true:
  ∀ cenv cx lctx ty cond_e msg es ss st st' es'.
    state_rel cenv cx es ss ∧
    eval_expr cx cond_e es = (INL (Value (BoolV T)), es') ∧
    compile_stmt cenv lctx ty (Assert cond_e msg) st = ((), st')
    ⇒
    ∃ ss' fuel ctx.
      run_compiled_blocks ctx st st' ss fuel = OK ss' ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* Assert bare + false condition: revert with empty returndata.
   Only for AssertBare — AssertReason has non-empty Error(string) data,
   AssertUnreachable uses INVALID (not REVERT). *)
Theorem compile_assert_bare_correct_false:
  ∀ cenv cx lctx ty cond_e es ss st st' es'.
    state_rel cenv cx es ss ∧
    fresh_vars_wrt st ss ∧
    supported_expr cond_e ∧
    well_annotated cond_e ∧
    eval_expr cx cond_e es = (INL (Value (BoolV F)), es') ∧
    compile_stmt cenv lctx ty (Assert cond_e AssertBare) st = ((), st')
    ⇒
    ∃ fuel ctx.
      run_compiled_blocks ctx st st' ss fuel =
        Abort Revert_abort (revert_state (set_returndata [] ss))
Proof
  rw[compile_stmt_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[comp_return_def] >>
  drule_all compile_expr_correct >> strip_tac >>
  qspec_then`"assert_ok"`drule fresh_label_props >>
  qspec_then`"assert_fail"`drule fresh_label_props >>
  qspec_then`REVERT`drule emit_inst_extends >>
  qspec_then`JNZ`drule emit_inst_extends >>
  qspec_then`fail_lbl`drule new_block_props >>
  qspec_then`ok_lbl`drule new_block_props >>
  rpt strip_tac >>
  simp[run_compiled_blocks_def, assemble_function_def, assemble_blocks_def] >>
  cheat
QED

(* Assert with reason + false condition: revert with Error(string) encoded data *)
Theorem compile_assert_reason_correct_false:
  ∀ cenv cx lctx ty cond_e reason_e es ss st st' es'.
    state_rel cenv cx es ss ∧
    eval_expr cx cond_e es = (INL (Value (BoolV F)), es') ∧
    compile_stmt cenv lctx ty (Assert cond_e (AssertReason reason_e)) st = ((), st')
    ⇒
    ∃ fuel ctx rd.
      run_compiled_blocks ctx st st' ss fuel =
        Abort Revert_abort (revert_state (set_returndata rd ss))
Proof
  cheat
QED

(* --- Return NONE (external): unlock + STOP → Halt --- *)
Theorem compile_return_none_external_correct:
  ∀ cenv lctx ty ss st st'.
    compile_stmt cenv lctx ty (Return NONE) st = ((), st') ∧
    FLOOKUP cenv.ce_vars "__return_pc__" = NONE
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Halt ss'
Proof
  cheat
QED

(* --- Return NONE (internal): load return_pc + RET → IntRet --- *)
(* NOTE: RET produces IntRet, not OK. The callee's INVOKE handler
   catches IntRet and continues as OK at the call site. *)
Theorem compile_return_none_internal_correct:
  ∀ cenv lctx ty ss st st' rpc_off sz.
    compile_stmt cenv lctx ty (Return NONE) st = ((), st') ∧
    FLOOKUP cenv.ce_vars "__return_pc__" = SOME (MemLoc rpc_off sz)
    ⇒
    ∃ ss' vals.
      run_inst_seq (emitted_insts st st') ss = IntRet vals ss'
Proof
  cheat
QED

(* --- Return (SOME e) external: ABI-encode + RETURN → Halt --- *)
Theorem compile_return_some_external_correct:
  ∀ cenv cx lctx ty e es ss st st' v es'.
    state_rel cenv cx es ss ∧
    cenv.ce_is_external ∧
    eval_expr cx e es = (INL (Value v), es') ∧
    compile_stmt cenv lctx ty (Return (SOME e)) st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Halt (halt_state ss')
Proof
  cheat
QED

(* --- Return (SOME e) internal: push to stack + RET → IntRet --- *)
Theorem compile_return_some_internal_correct:
  ∀ cenv cx lctx ty e es ss st st' v es' rpc_off sz.
    state_rel cenv cx es ss ∧
    ¬cenv.ce_is_external ∧
    FLOOKUP cenv.ce_vars "__return_pc__" = SOME (MemLoc rpc_off sz) ∧
    eval_expr cx e es = (INL (Value v), es') ∧
    compile_stmt cenv lctx ty (Return (SOME e)) st = ((), st')
    ⇒
    ∃ ss' vals.
      run_inst_seq (emitted_insts st st') ss = IntRet vals ss'
Proof
  cheat
QED

(* --- If: multi-block correctness --- *)
Theorem compile_if_correct:
  ∀ cenv cx lctx ty cond_e then_body else_body es ss st es' ctx.
    state_rel cenv cx es ss ∧
    eval_stmt cx (If cond_e then_body else_body) es = (INL (), es') ∧
    compile_stmt cenv lctx ty (If cond_e then_body else_body) st = ((), st')
    ⇒
    ∃ ss' fuel.
      run_compiled_blocks ctx st st' ss fuel = OK ss' ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- For range: multi-block loop correctness --- *)
Theorem compile_for_range_correct:
  ∀ cenv cx lctx ty id fty start_e end_e bound body es ss st es' ctx.
    state_rel cenv cx es ss ∧
    eval_stmt cx (For id fty (Range start_e end_e) bound body) es =
      (INL (), es') ∧
    compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound body) st =
      ((), st')
    ⇒
    ∃ ss' fuel.
      run_compiled_blocks ctx st st' ss fuel = OK ss' ∧
      state_rel cenv cx es' ss'
Proof
  cheat
QED

(* --- Break: jumps to exit label --- *)
Theorem compile_break_correct:
  ∀ cenv exit_lbl incr_lbl ty ss st st'.
    compile_stmt cenv (InLoop exit_lbl incr_lbl) ty Break st = ((), st')
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      OK (jump_to exit_lbl ss)
Proof
  rw[compile_stmt_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
     fresh_id_def, emit_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
          rich_listTheory.DROP_LENGTH_NIL, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[run_inst_seq_def, step_inst_base_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* --- Continue: jumps to increment label --- *)
Theorem compile_continue_correct:
  ∀ cenv exit_lbl incr_lbl ty ss st st'.
    compile_stmt cenv (InLoop exit_lbl incr_lbl) ty Continue st = ((), st')
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      OK (jump_to incr_lbl ss)
Proof
  rw[compile_stmt_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
     fresh_id_def, emit_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
          rich_listTheory.DROP_LENGTH_NIL, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[run_inst_seq_def, step_inst_base_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED
